import it.unisa.dia.gas.jpbc.Element;
import it.unisa.dia.gas.jpbc.Pairing;
import it.unisa.dia.gas.plaf.jpbc.pairing.PairingFactory;

import java.io.*;
import java.security.NoSuchAlgorithmException;
import java.util.*;
import java.util.stream.Collectors;

import static java.lang.Integer.valueOf;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.io.FileWriter;
import java.io.IOException;
import java.math.BigInteger;



public class KPABE {

    /**
     * 初始化
     * @param pairingParametersFileName
     * @param U
     * @param pkFileName
     * @param mskFileName
     */
    public static void setup(String pairingParametersFileName, int U, String pkFileName, String mskFileName) {
        //输入为 < 相关初始化参数文件名，属性全集U（整数），公钥集文件名，主密钥集文件名 >
        Pairing bp = PairingFactory.getPairing(pairingParametersFileName);  //从文件导入椭圆曲线参数，生成Pairing实例
        Element g = bp.getG1().newRandomElement().getImmutable();   //基于基本参数，从G1乘法循环群中随机选取Element整数生成元g（阶数）

        Properties mskProp = new Properties();  //新建Properties类以便生成对应主密钥msk封装文件
        Properties pkProp = new Properties();  //新建Properties类以便生成对应公钥pk封装文件
        //属性表示为1，2，3，...，U
        //对每个属性i，选取一个随机数ti作为该属性对应的主密钥，并计算相应公钥g^ti
        for (int i = 1; i <= U; i++){
            Element t = bp.getZr().newRandomElement().getImmutable();  //Element整数ti需要从加法循环群Zp中随机选取
            Element T = g.powZn(t).getImmutable();    //Element整数Ti=g^ti
            mskProp.setProperty("t"+i, Base64.getEncoder().withoutPadding().encodeToString(t.toBytes()));
            pkProp.setProperty("T"+i, Base64.getEncoder().withoutPadding().encodeToString(T.toBytes()));
            //将所得ti、Ti转换为字符串形式并进行Base64编码，并存入对应主密钥、公钥文件中
        }
        //另外选取一个随机数y，计算e(g,g)^y
        Element y = bp.getZr().newRandomElement().getImmutable();   //Element整数y需要从加法循环群Zp中随机选取
        Element egg_y = bp.pairing(g, g).powZn(y).getImmutable();  //基于椭圆曲线基本参数计算Y=egg_y=e(g,g)^y

        //将msk和pk存储到相应的文件中
        mskProp.setProperty("y", Base64.getEncoder().withoutPadding().encodeToString(y.toBytes()));
        pkProp.setProperty("egg_y", Base64.getEncoder().withoutPadding().encodeToString(egg_y.toBytes()));
        pkProp.setProperty("g", Base64.getEncoder().withoutPadding().encodeToString(g.toBytes()));
        //将所得y、Y=egg_y=e(g,g)^y、g转换为字符串形式并进行Base64编码，并存入对应主密钥、公钥、公钥文件中
        //注意区分数据类型。上面写的数据类型群元素，因此使用了Base64编码。

        storePropToFile(mskProp, mskFileName);  //封装进对应文件
        storePropToFile(pkProp, pkFileName);  //封装进对应文件

        //输出：系统主密钥文件 msk = { t1, t2, ..., t|U|, y }，公钥文件 pk = { T1, T2, ..., T|U|, Y, g }
    }

    /**
     * 密钥生成 -- 与访问控制树相关联
     * @param pairingParametersFileName
     * @param accessTree
     * @param pkFileName
     * @param mskFileName
     * @param skFileName
     * @throws NoSuchAlgorithmException
     */
    public static void keygen(String pairingParametersFileName, Node[] accessTree, String pkFileName, String mskFileName, String skFileName) throws NoSuchAlgorithmException {
        //输入为 < 相关初始化参数文件名，访问控制树，公钥文件名，主密钥文件名，私钥文件名 >
        Pairing bp = PairingFactory.getPairing(pairingParametersFileName);  //从文件导入椭圆曲线参数，生成Pairing实例

        Properties pkProp = loadPropFromFile(pkFileName);  //从对应公钥pk封装文件载入公钥Properties实例
        String gString = pkProp.getProperty("g");  //从对应公钥pk文件中获取生成元g
        Element g = bp.getG1().newElementFromBytes(Base64.getDecoder().decode(gString)).getImmutable();
        //将Base64编码后的字符串g解码转换成Element类整数

        Properties mskProp = loadPropFromFile(mskFileName);  //从对应主密钥msk封装文件载入主密钥Properties实例
        String yString = mskProp.getProperty("y");  //从对应主密钥msk文件中获取随机数密钥y值
        Element y = bp.getZr().newElementFromBytes(Base64.getDecoder().decode(yString)).getImmutable();
        //将Base64编码后的字符串y解码转换成Element类整数

        //先设置根节点要共享的秘密值
        accessTree[0].secretShare = y;
        //进行共享，使得每个叶子节点获得响应的秘密分片，使用编写的节点共享函数nodeShare()
        nodeShare(accessTree, accessTree[0], bp);
        //输入为 < 访问控制树的所有节点，根节点or要分享秘密的节点，Pairing实例 >
        //实质上是利用拉格朗日差值算法计算每个子节点的q(i)即秘密值，qi(0)=q(0)=y，并输出 < 分享秘密后的访问控制树的所有节点 >
        //解密时最后求出首项y=q(0)

        Properties skProp = new Properties();  //新建Properties类以便生成对应私钥sk封装文件

        //计算用户属性中每个属性对应的私钥Dx=g^(qx(i)/ti)，qx(i)是多项式在该属性i位置的值，ti是属性对应的主密钥
        for (Node node : accessTree) {
            if (node.isLeaf()) {
                // 对于每个叶子节点，先获取对应的主秘钥组件t，然后计算秘钥组件。
                String tString = mskProp.getProperty("t"+node.att);  //从对应主密钥msk文件中获取对应ti的字符串
                Element t = bp.getZr().newElementFromBytes(Base64.getDecoder().decode(tString)).getImmutable();
                //将Base64编码后的字符串t解码转换成Element类整数
                Element q = node.secretShare;  //获取该节点的共享的秘密值
                Element D = g.powZn(q.div(t)).getImmutable();  //计算Element类整数值Di=g^(q(i)/ti)
                skProp.setProperty("D"+node.att, Base64.getEncoder().withoutPadding().encodeToString(D.toBytes()));
                //将所得Di转换为字符串形式并进行Base64编码，并存入对应私钥文件中
            }
        }
        //将用户访问树也添加在私钥中
        //如何进行序列化和反序列化
        //skProp.setProperty("userAttList", Arrays.toString(accessTree));
        storePropToFile(skProp, skFileName);  //封装进对应文件

        //输出：私钥文件 sk = { Di } (i∈userAttList)
    }

    /**
     * 加密 -- 与属性集相关联
     * @param pairingParametersFileName
     * @param message
     * @param messageAttList
     * @param pkFileName
     * @param ctFileName
     */
    public static void encrypt(String pairingParametersFileName, Element message, int[] messageAttList, String pkFileName, String ctFileName) {
        //输入为 < 相关初始化参数文件名，Element类明文信息（GT上一点），明文属性集，公钥文件名，密文文件名 >
        Pairing bp = PairingFactory.getPairing(pairingParametersFileName);  //从文件导入椭圆曲线参数，生成Pairing实例

        Properties pkProp = loadPropFromFile(pkFileName);  //从对应公钥pk封装文件载入公钥Properties实例
        String eggString = pkProp.getProperty("egg_y");  //从对应公钥pk文件中获取公钥egg_y=Y=e(g,g)^y
        Element egg_y = bp.getGT().newElementFromBytes(Base64.getDecoder().decode(eggString)).getImmutable();
        //将Base64编码后的字符串egg_y解码转换成Element类整数

        //计算密文组件 E'=EP=Me(g,g)^(ys)
        Element s = bp.getZr().newRandomElement().getImmutable();  //选取随机Element类整数s∈Zp
        Element EP = message.duplicate().mul(egg_y.powZn(s)).getImmutable();
        //计算Element类整数E'=EP=M(Y^s)=Me(g,g)^(ys)（M点进行双线性映射得到整数）

        Properties ctProp = new Properties();  //新建Properties类以便生成对应密文ct封装文件
        //针对每个密文属性，计算密文组件 Ei=Ti^s
        for (int att : messageAttList) {
            String TString = pkProp.getProperty("T"+att);  //从对应公钥pk文件中获取对应Ti的字符串
            Element T = bp.getG1().newElementFromBytes(Base64.getDecoder().decode(TString)).getImmutable();
            //将Base64编码后的字符串Ti解码转换成Element类整数
            Element E = T.powZn(s).getImmutable();
            //针对每个明文属性，计算密文组件Element类整数 Ei=Ti^s

            ctProp.setProperty("E"+att, Base64.getEncoder().withoutPadding().encodeToString(E.toBytes()));
            //将所得密文组件Ei转换为字符串形式并进行Base64编码，并存入对应密文文件中
        }
        ctProp.setProperty("EP", Base64.getEncoder().withoutPadding().encodeToString(EP.toBytes()));
        //将Element类整数EP=M(Y^s)=Me(g,g)^(ys)也转换为字符串形式并进行Base64编码，并存入对应密文文件中

        //明文属性列表messageAttList也添加至密文文件中
        ctProp.setProperty("messageAttList", Arrays.toString(messageAttList));
        storePropToFile(ctProp, ctFileName);//封装进对应文件

        //输出：密文文件 ct = < E'=EP, {Ei}(i∈messageAttList) , messageAttList >
    }

    /**
     * 解密
     * @param pairingParametersFileName
     * @param accessTree
     * @param pkFileName
     * @param ctFileName
     * @param skFileName
     * @return
     */
    public static Element decrypt(String pairingParametersFileName, Node[] accessTree, String pkFileName, String ctFileName, String skFileName) {
        //输入为 < 相关初始化参数文件名，访问控制树，公钥文件名，密文文件名，私钥文件名 >
        Pairing bp = PairingFactory.getPairing(pairingParametersFileName);  //从文件导入椭圆曲线参数，生成Pairing实例

        Properties pkProp = loadPropFromFile(pkFileName);  //从对应公钥pk封装文件载入公钥Properties实例

        Properties ctProp = loadPropFromFile(ctFileName);  //从对应密文ct封装文件载入密文Properties实例
        String messageAttListString = ctProp.getProperty("messageAttList");  //从对应密文ct文件中获取明文属性列表
        //恢复明文消息的属性列表 int[]类型
        int[] messageAttList = Arrays.stream(messageAttListString.substring(1, messageAttListString.length()-1).split(",")).map(String::trim).mapToInt(Integer::parseInt).toArray();

        Properties skProp = loadPropFromFile(skFileName);  //从对应私钥sk封装文件载入私钥Properties实例
        for (Node node : accessTree) {
            if (node.isLeaf()) {
                // 如果叶子节点的属性值属于属性列表，则将属性对应的密文组件和秘钥组件配对的结果作为秘密值
                if (Arrays.stream(messageAttList).boxed().collect(Collectors.toList()).contains(node.att)){
                    String EString = ctProp.getProperty("E"+node.att);  //从对应密文ct文件中获取密文组件Ei
                    Element E = bp.getG1().newElementFromBytes(Base64.getDecoder().decode(EString)).getImmutable();
                    //将Base64编码后的字符串Ei解码转换成Element类整数
                    String DString = skProp.getProperty("D"+node.att);  //从对应私钥sk文件中获取用户每个属性对应的私钥Di
                    Element D = bp.getG1().newElementFromBytes(Base64.getDecoder().decode(DString)).getImmutable();
                    //将Base64编码后的字符串Di解码转换成Element类整数

                    // 这儿存在于密文属性列表中的叶子节点的秘密值是配对后的结果
                    //secretShare=e(Ei,Di)=e(g^( (ti)*s ),g^( qx(0)/(ti) )=e(g,g)^( qx(0)*s )=e(g,g)^sy
                    node.secretShare = bp.pairing(E,D).getImmutable();
                }
            }
        }
        // 进行秘密恢复
        boolean treeOK = nodeRecover(accessTree, accessTree[0], messageAttList, bp);
        //
        if (treeOK) {
            String EPString = ctProp.getProperty("EP");  //从对应密文ct文件中获取EP=M(Y^s)=Me(g,g)^(ys)
            Element EP = bp.getGT().newElementFromBytes(Base64.getDecoder().decode(EPString)).getImmutable();
            //将Base64编码后的字符串Di解码转换成Element类整数

            //恢复M=EP÷上述连乘结果  //恢复M=EP/denominator=M*e(g,g)^(ys)/e(g,g)^sy=M
            Element res = EP.div(accessTree[0].secretShare);
            return res;
        }
        else{
            System.out.println("The access tree is not satisfied.");
            return  null;
        }
    }


    //随机选取多项式参数randomP(d, a0, bp)→{ai}
    //d-1次多项式表示为q(x)=coef[0] + coef[1]*x^1 + coef[2]*x^2 + coef[d-1]*x^(d-1)
    //多项式的系数的数据类型为Zr Element，从而是的后续相关计算全部在Zr群上进行
    //通过随机选取coef参数，来构造d-1次多项式q(x)。约束条件为q(0)=s。
    public static Element[] randomP(int d, Element s, Pairing bp) {
        Element[] coef = new Element[d];
        coef[0] = s;
        for (int i = 1; i < d; i++){
            coef[i] = bp.getZr().newRandomElement().getImmutable();
        }
        return  coef;
    }

    //计算多项式函数qx(x, {ai}, bp)→q(x)
    //计算由coef为系数确定的多项式qx在序号为index点处的值，注意多项式计算在群Zr上进行
    public static Element qx(Element index, Element[] coef, Pairing bp){
        Element res = coef[0].getImmutable();
        for (int i = 1; i < coef.length; i++){
            Element exp = bp.getZr().newElement(i).getImmutable();
            //index一定要使用duplicate复制使用，因为index在每一次循环中都要使用，如果不加duplicte，index的值会发生变化
            res = res.add(coef[i].mul(index.duplicate().powZn(exp)));
            //q(x)=a[0]+a[1]x+a[2]x^2+...+a[n-1]x^(n-1)
        }
        return res;
    }

    //计算拉格朗日因子lagrange(i, S, x, bp)→δi
    //拉格朗日因子计算 i是集合S中的某个元素，x是目标点的x值
    public static Element lagrange(int i, int[] S, int x, Pairing bp) {
        Element res = bp.getZr().newOneElement().getImmutable();
        Element iElement = bp.getZr().newElement(i).getImmutable();
        Element xElement = bp.getZr().newElement(x).getImmutable();
        for (int j : S) {
            if (i != j) {
                //注意：在循环中重复使用的项一定要用duplicate复制出来使用
                //这儿xElement和iElement重复使用，但因为前面已经getImmutable所以可以不用duplicate
                Element numerator = xElement.sub(bp.getZr().newElement(j)); //x-xj
                Element denominator = iElement.sub(bp.getZr().newElement(j));  //xi-xj
                res = res.mul(numerator.div(denominator));  //(x-xj)/(xi-xj)的乘积（i≠j)
            }
        }
        return res;
    }

    // 共享秘密
    // nodes是整颗树的所有节点，n是要分享秘密的节点
    //输入为 < 访问控制树的所有节点，根节点or要分享秘密的节点，Pairing实例 >
    //根节点的q(0)=y
    public static void nodeShare(Node[] nodes, Node n, Pairing bp){
        // 如果是叶子节点，则不需要再分享
        if (!n.isLeaf()){
            // 如果不是叶子节点，则先生成一个随机多项式，多项式的常数项为当前节点的秘密值（这个值将被用于分享）
            // 多项式的次数，由节点的gate对应的threshold即门限值t决定
            Element[] coef = randomP(n.gate[0], n.secretShare, bp);
            //即：由n节点的门限值为多项式阶数、n节点的秘密值为首项系数a0（=根节点的q(0)=y），随机选取多项式参数{ai}

            for (int j=0; j<n.children.length; j++ ){
                Node childNode = nodes[n.children[j]];

                // 对于每一个子节点，以子节点的索引i为参数在整数域加法循环群Zp里随机新建对应的x，计算子节点的多项式值q(x)（也就是其对应的秘密分片）
                // 编写了函数qx来计算由coef为系数确定的多项式qx在子节点处的值，注意多项式计算在群Zr上进行
                childNode.secretShare = qx(bp.getZr().newElement(n.children[j]), coef, bp);
                //q(x)=a[0]+a[1]x+a[2]x^2+...+a[n-1]x^(n-1)
                // 递归，将该子节点的秘密继续共享下去
                nodeShare(nodes, childNode, bp);
            }
        }
        //输出为 < 访问分享了秘密后的控制树的所有节点>
    }

    // 恢复秘密
    //nodeRecover(Nodes, n,  atts, Pairing bp)→ 节点n是否可以恢复标志，恢复秘密值变为e(g,g)^sy
    //输入为< 访问控制树，要恢复秘密的节点，明文属性集，Pairing实例 >
    public static boolean nodeRecover(Node[] nodes, Node n,  int[] atts, Pairing bp) {
        //对于非叶子节点来说
        if (!n.isLeaf()) {
            // 对于内部节点，维护一个子节点索引列表，用于秘密恢复。
            List<Integer> validChildrenList = new ArrayList<Integer>();
            int[] validChildren;  //临时列表用来装满足条件的子节点
            // 遍历每一个子节点看
            for (int j=0; j<n.children.length; j++){
                Node childNode = nodes[n.children[j]];  //子节点
                // 存在子节点且可递归恢复，则递归所有子节点索引列表调用，恢复子节点的秘密值
                if (nodeRecover(nodes, childNode, atts, bp)){
                    System.out.println("The node with index " + n.children[j] + " is sarisfied!");
                    validChildrenList.add(valueOf(n.children[j]));
                    // 如果满足条件的子节点个数已经达到门限值，则跳出循环，不再计算剩余的节点
                    if (validChildrenList.size() == n.gate[0]) {
                        n.valid = true;  //表示此节点可以恢复
                        break;
                    }
                }
                else {
                    System.out.println("The node with index " + n.children[j] + " is not sarisfied!");
                }
            }
            // 如果可恢复的子节点个数等于门限值，则利用子节点的秘密分片恢复当前节点的秘密。
            if (validChildrenList.size() == n.gate[0]){
                validChildren = validChildrenList.stream().mapToInt(i->i).toArray();
                // 利用拉格朗日差值恢复秘密
                // 注意，此处是在指数因子上做拉格朗日差值
                Element secret = bp.getGT().newOneElement().getImmutable();
                for (int i : validChildren) {
                    Element delta = lagrange(i, validChildren, 0, bp);  //计算对应指数因子的拉格朗日因子，作为指数。目标值x为0，即qi(0)的拉格朗日因子。
                    secret = secret.mul(nodes[i].secretShare.duplicate().powZn(delta)); //基于拉格朗日因子进行指数运算，然后连乘
                    //计算Pi=e(Di,Ei)^deltai(0)=e(g,g)^sq(i)deltai(0)，并将结果连乘
                    //实际上得到denominator=连乘Pi=e(g,g)^(s·(求和q(i)deltai(0)))===e(g,g)^sq(0)=e(g,g)^sy
                }
                n.secretShare = secret;  //=e(g,g)^sy
            }
        }
        else {
            // 判断叶子节点的属性值是否属于属性列表
            // 判断一个元素是否属于数组，注意String类型和int类型的判断方式不同
            if (Arrays.stream(atts).boxed().collect(Collectors.toList()).contains(n.att)){
                n.valid = true;
            }
        }
        return n.valid;
    }

    public static void storePropToFile(Properties prop, String fileName){
        try(FileOutputStream out = new FileOutputStream(fileName)){
            prop.store(out, null);
        }
        catch (IOException e) {
            e.printStackTrace();
            System.out.println(fileName + " save failed!");
            System.exit(-1);
        }
    }

    public static Properties loadPropFromFile(String fileName) {
        Properties prop = new Properties();
        try (FileInputStream in = new FileInputStream(fileName)){
            prop.load(in);
        }
        catch (IOException e){
            e.printStackTrace();
            System.out.println(fileName + " load failed!");
            System.exit(-1);
        }
        return prop;
    }


    // 从文件中读取明文字符串消息
    private static String readPlaintextFromFile(String fileName) {
        StringBuilder plaintext = new StringBuilder();
        try (BufferedReader reader = new BufferedReader(new FileReader(fileName))) {
            String line;
            while ((line = reader.readLine()) != null) {
                plaintext.append(line);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
        return plaintext.toString();
    }

    // 将明文字符串写入文件的方法
    public static void writePlainTextToFile(String plainText, String filePath) {
        try {
            // 创建一个文件写入器
            FileWriter writer = new FileWriter(filePath);
            // 写入明文字符串到文件
            writer.write(plainText);
            // 关闭写入器
            writer.close();
            System.out.println("PlainText successfully written to file: " + filePath);
        } catch (IOException e) {
            // 捕获异常并打印错误信息
            System.err.println("Error writing to file: " + e.getMessage());
        }
    }




    public static void main(String[] args) throws Exception {
        int U = 20;
        int[] messageAttList = {1, 2, 4, 5};
        //int[] messageAttList = {1, 2};
        Node[] accessTree = new Node[7];  //访问树大小
        accessTree[0] = new Node(new int[]{2,3}, new int[]{1,2,3});  //构造内部根节点：gate:{门限值2，子节点个数为3};子节点索引列表：{1,2,3}
        accessTree[1] = new Node(1);  // 索引1，叶子节点，属性值1
        accessTree[2] = new Node(new int[]{2,3}, new int[]{4,5,6});  //索引2，内部节点，gate:{门限值2，子节点个数为3};子节点索引列表：{4,5,6}
        accessTree[3] = new Node(5);  // 索引3，叶子节点，属性值5
        accessTree[4] = new Node(2);  // 索引4，叶子节点，属性值2
        accessTree[5] = new Node(3);  // 索引5，叶子节点，属性值3
        accessTree[6] = new Node(4);  // 索引6，叶子节点，属性值4

//        int[] messageAttList = {1};
//        Node[] accessTree = new Node[3];
//        accessTree[0] = new Node(new int[]{2,2}, new int[]{1,2});
//        accessTree[1] = new Node(1);
//        accessTree[2] = new Node(2);

        String dir = "data/";
        String pairingParametersFileName = "a.properties";
        String pkFileName = dir + "pk.properties";
        String mskFileName = dir + "msk.properties";
        String skFileName = dir + "sk.properties";
        String ctFileName = dir + "ct.properties";

        String inputFileName = dir + "input.txt"; // 输入文件名
        String outputFileName = dir + "output.txt"; // 输入文件名


        setup(pairingParametersFileName, U, pkFileName, mskFileName);

        keygen(pairingParametersFileName, accessTree, pkFileName, mskFileName, skFileName);


    //    Element message = PairingFactory.getPairing(pairingParametersFileName).getGT().newRandomElement().getImmutable();

    //    System.out.println("明文消息:" + message);
    //    encrypt(pairingParametersFileName, message, messageAttList, pkFileName, ctFileName);

    //    Element res = decrypt(pairingParametersFileName, accessTree, pkFileName, ctFileName, skFileName);
    //            System.out.println("解密结果:" + res);
    //            if (message.isEqual(res)) {
    //                System.out.println("成功解密！");
    //            }

        // 读取明文字符串消息
        String plaintext = readPlaintextFromFile(inputFileName);
        System.out.println("明文消息: " + plaintext);

        // 将明文字符串转换为字节数组
        byte[] plaintextBytes = plaintext.getBytes(StandardCharsets.UTF_8);
        // 使用GT群的元素来表示明文
        Element plaintextElement = PairingFactory.getPairing(pairingParametersFileName).getGT().newElementFromBytes(plaintextBytes).getImmutable();
        // 在加密操作中，你可以将plaintextElement与属性相关联并进行加密
        encrypt(pairingParametersFileName, plaintextElement, messageAttList, pkFileName, ctFileName);


        // 模拟实际情况，将所有的节点的secretShare置为null
        //for (Node node : accessTree) {
            //node.secretShare = null;
        //}

        Element res = decrypt(pairingParametersFileName, accessTree, pkFileName, ctFileName, skFileName);
        System.out.println("解密结果:" + res);

        if (res!=null) {
            byte[] decryptedBytes = res.toBytes();
            String decryptedPlaintext = new String(decryptedBytes, StandardCharsets.UTF_8);

            // 打印解密后的明文字符串
            System.out.println("Decrypted plaintext: " + decryptedPlaintext);
            // 调用方法将明文字符串写入文件
            writePlainTextToFile(decryptedPlaintext, outputFileName);

        }

        if (plaintextElement.isEqual(res)) {
            System.out.println("成功解密！");
            // 在解密操作中，你可以从GT群上的点中获取字节数组，并将其转换回明文字符串
        }
    }
}
