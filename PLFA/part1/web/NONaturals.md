# 自然数

```txt
本章使用的 Unicode 符号：
    ℕ  U+2115  双线体大写 N (\bN)
    →  U+2192  右箭头 (\to, \r, \->)
    ∸  U+2238  点减 (\.-)
    ≡  U+2261  等价于 (\==)
    ⟨  U+27E8  数学左尖括号 (\<)
    ⟩  U+27E9  数学右尖括号 (\>)
    ∎  U+220E  证毕 (\qed)
```

## 自然数 -- 归纳数据类型 (Inductive Datatype)

自然数可以通过以下两条推倒规则(Inference Rules)定义：

    --------
    zero : ℕ 

    m : ℕ 
    -------- 
    suc m : ℕ

以上推导规则描述了：

- 起始步骤(Base Case): `zero` 是一个自然数
- 归纳步骤(Inductive Case): 如果`m`是一个自然数，那么`suc m`也是自然数

推导规则包含写在水平线上的零条或者多条判断(Judgement)，称为假设(Hypothesis);以及写在直线下的一条判断，称为结论(Conclusion).

推导规则可以使用Agda写出。

<pre class="Agda"> 
<a id="579" class="Keyword">data</a> <a id="ℕ"></a><a id="584" href="NONaturals.html#584" class="Datatype">ℕ</a> <a id="586" class="Symbol">:</a> <a id="588" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="592" class="Keyword">where</a> 
    <a id="ℕ.zero"></a><a id="603" href="NONaturals.html#603" class="InductiveConstructor">zero</a> <a id="608" class="Symbol">:</a> <a id="610" href="NONaturals.html#584" class="Datatype">ℕ</a>
    <a id="ℕ.suc"></a><a id="616" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="620" class="Symbol">:</a> <a id="622" href="NONaturals.html#584" class="Datatype">ℕ</a> <a id="624" class="Symbol">→</a> <a id="626" href="NONaturals.html#584" class="Datatype">ℕ</a> 
</pre>
其中关键字`data`用于声明归纳定义，`ℕ`是定义的新数据类型的名称，它是一个`Set`(类型)，关键字`where`用于分隔数据类型声明和构造子声明。

`zero`和`suc`是`ℕ`的两个构造子(Successor)，其中`zero`表示零，`suc`表示(任意自然数的)后继。

每个构造子后都由冒号以及相应的类型签名(Signature)跟随，`zero`作为自然数零，类型为`ℕ`，而`suc`表示后继，接受一个自然数作为参数，并返回另一个自然数，因此类型签名为`ℕ → ℕ`。

以上两条推导规则给出了产生自然数的唯一方法，实际上可以验证它满足皮亚诺公理，后续将使用Agda对其进行验证。

> 皮亚诺公理：
> 若三元组$(A,x_0,f)$满足以下条件，则称为一个戴德金-皮亚诺结构：
> 1. $A$是一个集合，$x_0 \in A$，$f : A \rightarrow A$ 
> 2. 不存在一个$t \in A$，使得$f(t) = x_0$
> 3. $f$ 是一个单射，即$\forall s \forall t : f(s) = f(t) \Leftrightarrow s = t$
> 4. 若$B \subset A$，$x_0 \in B$,且$\forall t \in B : f(t) \in B$， 则 $A = B$ 

使用Agda的自然数定义，可以生成自然数的实例，以`7`为例：

<pre class="Agda"><a id="seven"></a><a id="1264" href="NONaturals.html#1264" class="Function">seven</a> <a id="1270" class="Symbol">:</a> <a id="1272" href="NONaturals.html#584" class="Datatype">ℕ</a> 
<a id="1275" href="NONaturals.html#1264" class="Function">seven</a> <a id="1281" class="Symbol">=</a> <a id="1283" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="1287" class="Symbol">(</a><a id="1288" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="1292" class="Symbol">(</a><a id="1293" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="1297" class="Symbol">(</a><a id="1298" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="1302" class="Symbol">(</a><a id="1303" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="1307" class="Symbol">(</a><a id="1308" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="1312" class="Symbol">(</a><a id="1313" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="1317" href="NONaturals.html#603" class="InductiveConstructor">zero</a><a id="1321" class="Symbol">))))))</a>
</pre>
## 编译指令

在Agda中的注释(Comment)方法与Haskell相同， 即`--`作为单行注释，`{- ... -}`作为多行注释。在多行注释中，一种例外的注释形式会被识别为编译指令(Pragma) -- `{-# ... #-}`。 

<pre class="Agda"> 
<a id="1469" class="Symbol">{-#</a> <a id="1473" class="Keyword">BUILTIN</a> <a id="1481" class="Keyword">NATURAL</a> <a id="1489" href="NONaturals.html#584" class="Datatype">ℕ</a> <a id="1491" class="Symbol">#-}</a>
</pre>
该指令指示Agda数据类型`ℕ`与自然数对应，因此用户可以将`ℕ`类型简写为`0,1,2,3, ...`。 

## 模块导入

在引入自然数定义之后，就可以进行一些有关自然数事实的推理。在此之前，需要从Agda标准库中导入相等性(Equality)的定义以及用于等式推理的记法：

<pre class="Agda"> 
<a id="1653" class="Keyword">import</a> <a id="1660" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="1698" class="Symbol">as</a> <a id="1701" class="Module">Eq</a> 
<a id="1705" class="Keyword">open</a> <a id="1710" href="Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="1713" class="Keyword">using</a> <a id="1719" class="Symbol">(</a><a id="1720" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">_≡_</a><a id="1723" class="Symbol">;</a><a id="1724" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a><a id="1728" class="Symbol">)</a>
<a id="1730" class="Keyword">open</a> <a id="1735" href="Relation.Binary.PropositionalEquality.Core.html#2717" class="Module">Eq.≡-Reasoning</a> <a id="1750" class="Keyword">using</a> <a id="1756" class="Symbol">(</a><a id="1757" href="Relation.Binary.PropositionalEquality.Core.html#2815" class="Function Operator">begin_</a><a id="1763" class="Symbol">;</a><a id="1764" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">_≡⟨⟩_</a><a id="1769" class="Symbol">;</a><a id="1770" href="Relation.Binary.PropositionalEquality.Core.html#3114" class="Function Operator">_∎</a><a id="1772" class="Symbol">)</a>
</pre>
上述代码中，首行将标准库中定义了相等性的模块导入到了当前作用域(Scope),并命名为`Eq`。第二行打开了`Eq`模块，并使用`using`从句将相等运算符`_≡_`和两个项相等的证据`refl`添加到当前作用域。第三行打开了`Eq`的子模块`≡-Reasoning`(用于等价关系推理)，并将`begin_`，`_≡⟨⟩_`,`_∎`添加到当前作用域，它们分别表示“证明开始”，“等价于”，“证明结束”。

应当注意到，导入的名称中大量使用了下划线。在Agda中，使用下划线标注项(Term)相对于运算符的位置。例如`_≡_`为中缀运算符，而`begin_`为前缀运算符(运算符写在前),`_∎`为后缀运算符(运算符写在后)。

> 注意：括号与分号不允许出现在名称中，因此我们在`using`列表中无需额外空格消除歧义。


## 自然数的运算 -- 递归函数

使用递归(Recursion)可以很容易定义自然数的相关运算。

### 加法

加法使用递归可以定义为两个规则：

    0 + n ≡ n 
    (1 + m) ≡ 1 + (m + n)

使用Agda编写如下：

<pre class="Agda"> 
<a id="_+_"></a><a id="2290" href="NONaturals.html#2290" class="Function Operator">_+_</a> <a id="2294" class="Symbol">:</a> <a id="2296" href="NONaturals.html#584" class="Datatype">ℕ</a> <a id="2298" class="Symbol">→</a> <a id="2300" href="NONaturals.html#584" class="Datatype">ℕ</a> <a id="2302" class="Symbol">→</a> <a id="2304" href="NONaturals.html#584" class="Datatype">ℕ</a> 
<a id="2307" href="NONaturals.html#603" class="InductiveConstructor">zero</a> <a id="2312" href="NONaturals.html#2290" class="Function Operator">+</a> <a id="2314" href="NONaturals.html#2314" class="Bound">n</a> <a id="2316" class="Symbol">=</a> <a id="2318" href="NONaturals.html#2314" class="Bound">n</a>
<a id="2320" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2324" href="NONaturals.html#2324" class="Bound">m</a> <a id="2326" href="NONaturals.html#2290" class="Function Operator">+</a> <a id="2328" href="NONaturals.html#2328" class="Bound">n</a> <a id="2330" class="Symbol">=</a> <a id="2332" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2336" class="Symbol">(</a><a id="2337" href="NONaturals.html#2324" class="Bound">m</a> <a id="2339" href="NONaturals.html#2290" class="Function Operator">+</a> <a id="2341" href="NONaturals.html#2328" class="Bound">n</a><a id="2342" class="Symbol">)</a> 
</pre>
> 注意: 我们使用等号`=`表示定义，用`≡`表示相等。

加法作为一个中缀运算符，接受两个自然数并返回运算结果，因此类型签名为`ℕ → ℕ → ℕ`。上述定义包含了两个步骤 -- 起始步骤和归纳步骤，与自然数的定义相对应。

起始步骤表明零加任意自然数结果仍然为这个自然数；归纳步骤表明一个数的后继与另一个数相加，结果为这两个数的和的后继。

在加法定义中，构造子出现在等号左侧，我们称为模式匹配(Pattern Matching)。

另外虽然加法定义是递归的，但是较大的数相加是用较小的数相加定义的，这样的定义被称为***良基的(Well founded)***。

下面我们选择加法的实例进行证明，以二加三为例:

<pre class="Agda">  
<a id="2675" href="NONaturals.html#2675" class="Function">_</a> <a id="2677" class="Symbol">:</a> <a id="2679" class="Number">2</a> <a id="2681" href="NONaturals.html#2290" class="Function Operator">+</a> <a id="2683" class="Number">3</a> <a id="2685" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="2687" class="Number">5</a> 
<a id="2690" class="Symbol">_</a> <a id="2692" class="Symbol">=</a> <a id="2694" class="Comment">-- 根据编译指令，证明过程的等价式子可以替换为注释内容</a>
    <a id="2727" href="Relation.Binary.PropositionalEquality.Core.html#2815" class="Function Operator">begin</a> 
        <a id="2742" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2746" class="Symbol">(</a><a id="2747" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2751" href="NONaturals.html#603" class="InductiveConstructor">zero</a><a id="2755" class="Symbol">)</a> <a id="2757" href="NONaturals.html#2290" class="Function Operator">+</a> <a id="2759" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2763" class="Symbol">(</a><a id="2764" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2768" class="Symbol">(</a><a id="2769" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2773" href="NONaturals.html#603" class="InductiveConstructor">zero</a><a id="2777" class="Symbol">))</a> <a id="2780" class="Comment">-- 2 + 3 </a>
    <a id="2794" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="2807" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2811" href="NONaturals.html#603" class="InductiveConstructor">zero</a> <a id="2816" href="NONaturals.html#2290" class="Function Operator">+</a> <a id="2818" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2822" class="Symbol">(</a><a id="2823" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2827" class="Symbol">(</a><a id="2828" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2832" class="Symbol">(</a><a id="2833" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2837" href="NONaturals.html#603" class="InductiveConstructor">zero</a><a id="2841" class="Symbol">)))</a> <a id="2845" class="Comment">-- 1 + 4</a>
    <a id="2858" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="2871" href="NONaturals.html#603" class="InductiveConstructor">zero</a> <a id="2876" href="NONaturals.html#2290" class="Function Operator">+</a> <a id="2878" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2882" class="Symbol">(</a><a id="2883" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2887" class="Symbol">(</a><a id="2888" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2892" class="Symbol">(</a><a id="2893" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2897" class="Symbol">(</a><a id="2898" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2902" href="NONaturals.html#603" class="InductiveConstructor">zero</a><a id="2906" class="Symbol">))))</a> <a id="2911" class="Comment">-- 0 + 5</a>
    <a id="2924" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="2937" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2941" class="Symbol">(</a><a id="2942" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2946" class="Symbol">(</a><a id="2947" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2951" class="Symbol">(</a><a id="2952" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2956" class="Symbol">(</a><a id="2957" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="2961" href="NONaturals.html#603" class="InductiveConstructor">zero</a><a id="2965" class="Symbol">))))</a> <a id="2970" class="Comment">-- 5</a>
    <a id="2979" href="Relation.Binary.PropositionalEquality.Core.html#3114" class="Function Operator">∎</a> 
</pre>
整个证明由一个类型签名（首行）和一个提供对应类型的项的绑定(Binding)组成。

在这个证明过程中，首行使用了虚设名称`_`,虚设名称允许用户重复使用，在举例时很便利，除此之外所有名称都只能在模块中定义一次。虚设名称后面为类型签名，亦待证明的命题`2 + 3 ≡ 5`(这是柯里-霍华德同构，后面章节会阐述)。

在给出类型签名（待证明的命题）后，程序给出了相应类型的项进行绑定，亦命题的证明或***证据(Evidence)***(这也是柯里-霍华德同构)。

以数学证明的视角，该证明由等式链组成，等式链由`begin`开始，以`∎`结束，中间由一系列`≡⟨⟩`分隔的向组成。

> 实际上, `begin_`，`_∎`，`≡⟨⟩`只是作为运算符的存在，后面的章节将会详细解析这部分内容。

回到加法的定义，不难看出，不断使用递归定义，可以直接计算出`2 + 3`的结果，因此实际上Agda可以直接化简`2 + 3`为`5`,即命题变成了`5 ≡ 5`。我们可以使用`refl`立刻得出这个显然的结果。

<pre class="Agda"> 
<a id="3454" href="NONaturals.html#3454" class="Function">_</a> <a id="3456" class="Symbol">:</a> <a id="3458" class="Number">2</a> <a id="3460" href="NONaturals.html#2290" class="Function Operator">+</a> <a id="3462" class="Number">3</a> <a id="3464" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3466" class="Number">5</a> 
<a id="3469" class="Symbol">_</a> <a id="3471" class="Symbol">=</a> <a id="3473" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> 
</pre>
一个值等于其自身的证据写作`refl`。

> 注意: 这里提到的证据等同于证明。

### 乘法

一旦定义了加法，就可以使用递归定义乘法为重复的加法。

    0 * n ≡ 0 
    (1 + m) * n = n + (m * n) 

使用Agda编写如下：

<pre class="Agda"> 
<a id="_*_"></a><a id="3635" href="NONaturals.html#3635" class="Function Operator">_*_</a> <a id="3639" class="Symbol">:</a> <a id="3641" href="NONaturals.html#584" class="Datatype">ℕ</a> <a id="3643" class="Symbol">→</a> <a id="3645" href="NONaturals.html#584" class="Datatype">ℕ</a> <a id="3647" class="Symbol">→</a> <a id="3649" href="NONaturals.html#584" class="Datatype">ℕ</a> 
<a id="3652" href="NONaturals.html#603" class="InductiveConstructor">zero</a> <a id="3657" href="NONaturals.html#3635" class="Function Operator">*</a> <a id="3659" href="NONaturals.html#3659" class="Bound">n</a> <a id="3661" class="Symbol">=</a> <a id="3663" href="NONaturals.html#603" class="InductiveConstructor">zero</a> 
<a id="3669" class="Symbol">(</a><a id="3670" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="3674" href="NONaturals.html#3674" class="Bound">m</a><a id="3675" class="Symbol">)</a> <a id="3677" href="NONaturals.html#3635" class="Function Operator">*</a> <a id="3679" href="NONaturals.html#3679" class="Bound">n</a> <a id="3681" class="Symbol">=</a> <a id="3683" href="NONaturals.html#3679" class="Bound">n</a> <a id="3685" href="NONaturals.html#2290" class="Function Operator">+</a> <a id="3687" class="Symbol">(</a><a id="3688" href="NONaturals.html#3674" class="Bound">m</a> <a id="3690" href="NONaturals.html#3635" class="Function Operator">*</a> <a id="3692" href="NONaturals.html#3679" class="Bound">n</a><a id="3693" class="Symbol">)</a>
</pre>
不难看出，这个定义也是良基的，因为较大的数的相乘是用较小的数相乘定义的。

以二乘三为示例：

<pre class="Agda"> 
<a id="3760" href="NONaturals.html#3760" class="Function">_</a> <a id="3762" class="Symbol">=</a> <a id="3764" class="Number">2</a> <a id="3766" href="NONaturals.html#3635" class="Function Operator">*</a> <a id="3768" class="Number">3</a> <a id="3770" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3772" class="Number">6</a> 
<a id="3775" href="NONaturals.html#3775" class="Function">_</a> <a id="3777" class="Symbol">=</a> 
    <a id="3784" href="Relation.Binary.PropositionalEquality.Core.html#2815" class="Function Operator">begin</a> 
        <a id="3799" class="Number">2</a> <a id="3801" href="NONaturals.html#3635" class="Function Operator">*</a> <a id="3803" class="Number">3</a> 
    <a id="3810" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="3823" class="Number">3</a> <a id="3825" href="NONaturals.html#2290" class="Function Operator">+</a> <a id="3827" class="Symbol">(</a><a id="3828" class="Number">1</a> <a id="3830" href="NONaturals.html#3635" class="Function Operator">*</a> <a id="3832" class="Number">3</a><a id="3833" class="Symbol">)</a> 
    <a id="3840" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="3853" class="Number">3</a> <a id="3855" href="NONaturals.html#2290" class="Function Operator">+</a> <a id="3857" class="Symbol">(</a><a id="3858" class="Number">3</a> <a id="3860" href="NONaturals.html#2290" class="Function Operator">+</a> <a id="3862" class="Symbol">(</a><a id="3863" class="Number">0</a> <a id="3865" href="NONaturals.html#3635" class="Function Operator">*</a> <a id="3867" class="Number">3</a><a id="3868" class="Symbol">))</a> 
    <a id="3876" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="3889" class="Number">3</a> <a id="3891" href="NONaturals.html#2290" class="Function Operator">+</a> <a id="3893" class="Symbol">(</a><a id="3894" class="Number">3</a> <a id="3896" href="NONaturals.html#2290" class="Function Operator">+</a> <a id="3898" class="Number">0</a><a id="3899" class="Symbol">)</a>
    <a id="3905" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="3918" class="Number">3</a> <a id="3920" href="NONaturals.html#2290" class="Function Operator">+</a> <a id="3922" class="Number">3</a> 
    <a id="3929" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="3942" class="Number">6</a>
    <a id="3948" href="Relation.Binary.PropositionalEquality.Core.html#3114" class="Function Operator">∎</a>
</pre>
### 乘方

类似地，可以根据乘法递归定义乘方运算。

    m ^ 0 ≡ 1 
    m ^ (1 + n) ≡ m * (m ^ n)

使用Agda定义： 

<pre class="Agda"> 
<a id="_^_"></a><a id="4054" href="NONaturals.html#4054" class="Function Operator">_^_</a> <a id="4058" class="Symbol">:</a> <a id="4060" href="NONaturals.html#584" class="Datatype">ℕ</a> <a id="4062" class="Symbol">→</a> <a id="4064" href="NONaturals.html#584" class="Datatype">ℕ</a> <a id="4066" class="Symbol">→</a> <a id="4068" href="NONaturals.html#584" class="Datatype">ℕ</a> 
<a id="4071" href="NONaturals.html#4071" class="Bound">m</a> <a id="4073" href="NONaturals.html#4054" class="Function Operator">^</a> <a id="4075" href="NONaturals.html#603" class="InductiveConstructor">zero</a> <a id="4080" class="Symbol">=</a> <a id="4082" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="4086" href="NONaturals.html#603" class="InductiveConstructor">zero</a> 
<a id="4092" href="NONaturals.html#4092" class="Bound">m</a> <a id="4094" href="NONaturals.html#4054" class="Function Operator">^</a> <a id="4096" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="4100" href="NONaturals.html#4100" class="Bound">n</a> <a id="4102" class="Symbol">=</a> <a id="4104" href="NONaturals.html#4092" class="Bound">m</a> <a id="4106" href="NONaturals.html#3635" class="Function Operator">*</a> <a id="4108" class="Symbol">(</a><a id="4109" href="NONaturals.html#4092" class="Bound">m</a> <a id="4111" href="NONaturals.html#4054" class="Function Operator">^</a> <a id="4113" href="NONaturals.html#4100" class="Bound">n</a><a id="4114" class="Symbol">)</a>
</pre>
### 饱和减法

自然数中不包含负数，因此如果被减数比减数小，为了保证运算的封闭性，我们将其取零。这种针对自然数的减法变种称为***饱和减法(Monus)***。

<pre class="Agda"> 
<a id="_∸_"></a><a id="4216" href="NONaturals.html#4216" class="Function Operator">_∸_</a> <a id="4220" class="Symbol">:</a> <a id="4222" href="NONaturals.html#584" class="Datatype">ℕ</a> <a id="4224" class="Symbol">→</a> <a id="4226" href="NONaturals.html#584" class="Datatype">ℕ</a> <a id="4228" class="Symbol">→</a> <a id="4230" href="NONaturals.html#584" class="Datatype">ℕ</a> 
<a id="4233" href="NONaturals.html#4233" class="Bound">m</a> <a id="4235" href="NONaturals.html#4216" class="Function Operator">∸</a> <a id="4237" href="NONaturals.html#603" class="InductiveConstructor">zero</a> <a id="4242" class="Symbol">=</a> <a id="4244" href="NONaturals.html#4233" class="Bound">m</a> 
<a id="4247" href="NONaturals.html#603" class="InductiveConstructor">zero</a> <a id="4252" href="NONaturals.html#4216" class="Function Operator">∸</a> <a id="4254" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="4258" href="NONaturals.html#4258" class="Bound">n</a> <a id="4260" class="Symbol">=</a> <a id="4262" href="NONaturals.html#603" class="InductiveConstructor">zero</a> 
<a id="4268" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="4272" href="NONaturals.html#4272" class="Bound">m</a> <a id="4274" href="NONaturals.html#4216" class="Function Operator">∸</a> <a id="4276" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="4280" href="NONaturals.html#4280" class="Bound">n</a> <a id="4282" class="Symbol">=</a> <a id="4284" href="NONaturals.html#4272" class="Bound">m</a> <a id="4286" href="NONaturals.html#4216" class="Function Operator">∸</a> <a id="4288" href="NONaturals.html#4280" class="Bound">n</a> 
</pre>
饱和减法首次对两个参数使用了模式匹配：

- 考虑第二个参数
    + 如果它是`zero`，结果为第一个参数`m`
    + 如果它是`suc n`，考虑第一个参数
        * 如果它是`zero`，结果为`zero` 
        * 如果它是`suc m`，结果为两个参数的前继的饱和减法，即`m ∸ n`

> 注意： 在定义运算符过程中，应当确保“不重不漏”。

### 优先级

使用***优先级(Precedence)***可以避免书写大量括号，函数运算比任意运算符结合更紧密，拥有最高优先级，因此在运算符和函数混合的表达式中可以去除包裹在函数外的括号，例如`suc m + n`。

在Agda中，中缀运算符的优先级和结合性需要被声明：

<pre class="Agda"> 
<a id="4644" class="Keyword">infixl</a> <a id="4651" class="Number">6</a> <a id="4653" href="NONaturals.html#2290" class="Primitive Operator">_+_</a> <a id="4657" href="NONaturals.html#4216" class="Primitive Operator">_∸_</a>
<a id="4661" class="Keyword">infixl</a> <a id="4668" class="Number">7</a> <a id="4670" href="NONaturals.html#3635" class="Primitive Operator">_*_</a>
<a id="4674" class="Keyword">infixr</a> <a id="4681" class="Number">8</a> <a id="4683" href="NONaturals.html#4054" class="Function Operator">_^_</a>
</pre>
这里加法，饱和减法，乘法都是左结合的，且加法和饱和减法优先级更低；乘方是右结合的，且优先级高于其余三个运算符。

除此之外，用户也可以使用`infix`表示总是需要括号来消除歧义。

## 柯里化

柯里化以Haskell Curry的名字命名，对于接受多参数的函数来说，柯里化视角下允许其接受一个参数，并返回一个接受剩余参数的函数。

在Agda以及Haskell类似的函数式编成语言中，函数箭头是右结合的，而函数应用则是左结合的。

以加法为例：

`ℕ → ℕ → ℕ` 表示 `ℕ → (ℕ → ℕ)`

而

`_+_ a b` 表示 `(_+_ a) b`。

## 更多编译指令

<pre class="Agda"> 
<a id="5002" class="Symbol">{-#</a> <a id="5006" class="Keyword">BUILTIN</a> <a id="5014" class="Keyword">NATPLUS</a> <a id="5022" href="NONaturals.html#2290" class="Primitive Operator">_+_</a> <a id="5026" class="Symbol">#-}</a>
<a id="5030" class="Symbol">{-#</a> <a id="5034" class="Keyword">BUILTIN</a> <a id="5042" class="Keyword">NATTIMES</a> <a id="5051" href="NONaturals.html#3635" class="Primitive Operator">_*_</a> <a id="5055" class="Symbol">#-}</a>
<a id="5059" class="Symbol">{-#</a> <a id="5063" class="Keyword">BUILTIN</a> <a id="5071" class="Keyword">NATMINUS</a> <a id="5080" href="NONaturals.html#4216" class="Primitive Operator">_∸_</a> <a id="5084" class="Symbol">#-}</a>
</pre>
## 标准库

<pre class="Agda"><a id="5111" class="Comment">-- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)</a>
</pre>
---------------------------------------------------

## 习题参考

### 练习`seven`(实践)

<pre class="Agda"><a id="5267" href="NONaturals.html#5267" class="Function">_</a> <a id="5269" class="Symbol">:</a> <a id="5271" href="NONaturals.html#584" class="Datatype">ℕ</a> 
<a id="5274" class="Symbol">_</a> <a id="5276" class="Symbol">=</a> <a id="5278" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="5282" class="Symbol">(</a><a id="5283" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="5287" class="Symbol">(</a><a id="5288" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="5292" class="Symbol">(</a><a id="5293" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="5297" class="Symbol">(</a><a id="5298" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="5302" class="Symbol">(</a><a id="5303" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="5307" href="NONaturals.html#603" class="InductiveConstructor">zero</a><a id="5311" class="Symbol">)))))</a>
</pre>
### 练习`+-example`(实践)

计算`3 + 4`,将你的推导国策划嗯写成等式链，为`+`使用等式。

<pre class="Agda"><a id="5390" href="NONaturals.html#5390" class="Function">_</a> <a id="5392" class="Symbol">:</a> <a id="5394" class="Number">3</a> <a id="5396" href="NONaturals.html#2290" class="Primitive Operator">+</a> <a id="5398" class="Number">4</a> <a id="5400" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="5402" class="Number">7</a> 
<a id="5405" class="Symbol">_</a> <a id="5407" class="Symbol">=</a> 
    <a id="5414" href="Relation.Binary.PropositionalEquality.Core.html#2815" class="Function Operator">begin</a> 
        <a id="5429" class="Number">3</a> <a id="5431" href="NONaturals.html#2290" class="Primitive Operator">+</a> <a id="5433" class="Number">4</a> 
    <a id="5440" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="5453" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="5457" class="Symbol">(</a><a id="5458" class="Number">2</a> <a id="5460" href="NONaturals.html#2290" class="Primitive Operator">+</a> <a id="5462" class="Number">4</a><a id="5463" class="Symbol">)</a>
    <a id="5469" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="5482" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="5486" class="Symbol">(</a><a id="5487" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="5491" class="Symbol">(</a><a id="5492" class="Number">1</a> <a id="5494" href="NONaturals.html#2290" class="Primitive Operator">+</a> <a id="5496" class="Number">4</a><a id="5497" class="Symbol">))</a>
    <a id="5504" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="5517" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="5521" class="Symbol">(</a><a id="5522" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="5526" class="Symbol">(</a><a id="5527" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="5531" class="Symbol">(</a><a id="5532" class="Number">0</a> <a id="5534" href="NONaturals.html#2290" class="Primitive Operator">+</a> <a id="5536" class="Number">4</a><a id="5537" class="Symbol">)))</a>
    <a id="5545" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="5558" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="5562" class="Symbol">(</a><a id="5563" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="5567" class="Symbol">(</a><a id="5568" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="5572" class="Number">4</a><a id="5573" class="Symbol">))</a>
    <a id="5580" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="5593" class="Number">7</a>
    <a id="5599" href="Relation.Binary.PropositionalEquality.Core.html#3114" class="Function Operator">∎</a>
</pre>
### 练习`*-example`(实践)

计算`3 * 4`，将你的推导过程写成等式链，为`*`使用等式(不必对加法过程详细描述)。

<pre class="Agda"><a id="5686" href="NONaturals.html#5686" class="Function">_</a> <a id="5688" class="Symbol">:</a> <a id="5690" class="Number">3</a> <a id="5692" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="5694" class="Number">4</a> <a id="5696" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="5698" class="Number">12</a> 
<a id="5702" class="Symbol">_</a> <a id="5704" class="Symbol">=</a> 
    <a id="5711" href="Relation.Binary.PropositionalEquality.Core.html#2815" class="Function Operator">begin</a> 
        <a id="5726" class="Number">3</a> <a id="5728" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="5730" class="Number">4</a> 
    <a id="5737" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="5750" class="Number">4</a> <a id="5752" href="NONaturals.html#2290" class="Primitive Operator">+</a> <a id="5754" class="Number">2</a> <a id="5756" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="5758" class="Number">4</a> 
    <a id="5765" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="5778" class="Number">4</a> <a id="5780" href="NONaturals.html#2290" class="Primitive Operator">+</a> <a id="5782" class="Symbol">(</a><a id="5783" class="Number">4</a> <a id="5785" href="NONaturals.html#2290" class="Primitive Operator">+</a> <a id="5787" class="Number">1</a> <a id="5789" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="5791" class="Number">4</a><a id="5792" class="Symbol">)</a> 
    <a id="5799" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="5812" class="Number">4</a> <a id="5814" href="NONaturals.html#2290" class="Primitive Operator">+</a> <a id="5816" class="Symbol">(</a><a id="5817" class="Number">4</a> <a id="5819" href="NONaturals.html#2290" class="Primitive Operator">+</a> <a id="5821" class="Symbol">(</a><a id="5822" class="Number">4</a> <a id="5824" href="NONaturals.html#2290" class="Primitive Operator">+</a> <a id="5826" class="Number">0</a> <a id="5828" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="5830" class="Number">4</a><a id="5831" class="Symbol">))</a> 
    <a id="5839" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="5852" class="Number">4</a> <a id="5854" href="NONaturals.html#2290" class="Primitive Operator">+</a> <a id="5856" class="Symbol">(</a><a id="5857" class="Number">4</a> <a id="5859" href="NONaturals.html#2290" class="Primitive Operator">+</a> <a id="5861" class="Symbol">(</a><a id="5862" class="Number">4</a> <a id="5864" href="NONaturals.html#2290" class="Primitive Operator">+</a> <a id="5866" class="Number">0</a><a id="5867" class="Symbol">))</a>
    <a id="5874" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="5887" class="Number">12</a>
    <a id="5894" href="Relation.Binary.PropositionalEquality.Core.html#3114" class="Function Operator">∎</a>
</pre>
### 练习`_^_`(推荐)

检查`3 ^ 4`是否等于`81`。

<pre class="Agda"><a id="5948" href="NONaturals.html#5948" class="Function">_</a> <a id="5950" class="Symbol">:</a> <a id="5952" class="Number">3</a> <a id="5954" href="NONaturals.html#4054" class="Function Operator">^</a> <a id="5956" class="Number">4</a> <a id="5958" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="5960" class="Number">81</a>
<a id="5963" class="Symbol">_</a> <a id="5965" class="Symbol">=</a> 
    <a id="5972" href="Relation.Binary.PropositionalEquality.Core.html#2815" class="Function Operator">begin</a> 
        <a id="5987" class="Number">3</a> <a id="5989" href="NONaturals.html#4054" class="Function Operator">^</a> <a id="5991" class="Number">4</a> 
    <a id="5998" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="6011" class="Number">3</a> <a id="6013" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="6015" class="Number">3</a> <a id="6017" href="NONaturals.html#4054" class="Function Operator">^</a> <a id="6019" class="Number">3</a> 
    <a id="6026" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="6039" class="Number">3</a> <a id="6041" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="6043" class="Symbol">(</a><a id="6044" class="Number">3</a> <a id="6046" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="6048" class="Number">3</a> <a id="6050" href="NONaturals.html#4054" class="Function Operator">^</a> <a id="6052" class="Number">2</a><a id="6053" class="Symbol">)</a>
    <a id="6059" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="6072" class="Number">3</a> <a id="6074" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="6076" class="Symbol">(</a><a id="6077" class="Number">3</a> <a id="6079" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="6081" class="Symbol">(</a><a id="6082" class="Number">3</a> <a id="6084" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="6086" class="Number">3</a> <a id="6088" href="NONaturals.html#4054" class="Function Operator">^</a> <a id="6090" class="Number">1</a><a id="6091" class="Symbol">))</a>
    <a id="6098" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="6111" class="Number">3</a> <a id="6113" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="6115" class="Symbol">(</a><a id="6116" class="Number">3</a> <a id="6118" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="6120" class="Symbol">(</a><a id="6121" class="Number">3</a> <a id="6123" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="6125" class="Symbol">(</a><a id="6126" class="Number">3</a> <a id="6128" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="6130" class="Number">3</a> <a id="6132" href="NONaturals.html#4054" class="Function Operator">^</a> <a id="6134" class="Number">0</a><a id="6135" class="Symbol">)))</a>
    <a id="6143" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="6156" class="Number">3</a> <a id="6158" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="6160" class="Symbol">(</a><a id="6161" class="Number">3</a> <a id="6163" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="6165" class="Symbol">(</a><a id="6166" class="Number">3</a> <a id="6168" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="6170" class="Symbol">(</a><a id="6171" class="Number">3</a> <a id="6173" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="6175" class="Number">1</a><a id="6176" class="Symbol">)))</a>
    <a id="6184" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="6197" class="Number">81</a>
    <a id="6204" href="Relation.Binary.PropositionalEquality.Core.html#3114" class="Function Operator">∎</a>
</pre>
### 练习`∸-example₁`和`∸-example₂`(推荐)

计算`5 ∸ 3`和`3 ∸ 5`，将你的推荐过程写成等式链。

<pre class="Agda"><a id="∸-example₁"></a><a id="6291" href="NONaturals.html#6291" class="Function">∸-example₁</a> <a id="6302" class="Symbol">:</a> <a id="6304" class="Number">5</a> <a id="6306" href="NONaturals.html#4216" class="Primitive Operator">∸</a> <a id="6308" class="Number">3</a> <a id="6310" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="6312" class="Number">2</a> 
<a id="6315" href="NONaturals.html#6291" class="Function">∸-example₁</a> <a id="6326" class="Symbol">=</a> 
    <a id="6333" href="Relation.Binary.PropositionalEquality.Core.html#2815" class="Function Operator">begin</a> 
        <a id="6348" class="Number">5</a> <a id="6350" href="NONaturals.html#4216" class="Primitive Operator">∸</a> <a id="6352" class="Number">3</a> 
    <a id="6359" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="6372" class="Number">4</a> <a id="6374" href="NONaturals.html#4216" class="Primitive Operator">∸</a> <a id="6376" class="Number">2</a> 
    <a id="6383" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="6396" class="Number">3</a> <a id="6398" href="NONaturals.html#4216" class="Primitive Operator">∸</a> <a id="6400" class="Number">1</a> 
    <a id="6407" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="6420" class="Number">2</a> <a id="6422" href="NONaturals.html#4216" class="Primitive Operator">∸</a> <a id="6424" class="Number">0</a>
    <a id="6430" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="6443" class="Number">2</a>
    <a id="6449" href="Relation.Binary.PropositionalEquality.Core.html#3114" class="Function Operator">∎</a>

<a id="∸-example₂"></a><a id="6452" href="NONaturals.html#6452" class="Function">∸-example₂</a> <a id="6463" class="Symbol">:</a> <a id="6465" class="Number">3</a> <a id="6467" href="NONaturals.html#4216" class="Primitive Operator">∸</a> <a id="6469" class="Number">5</a> <a id="6471" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="6473" class="Number">0</a> 
<a id="6476" href="NONaturals.html#6452" class="Function">∸-example₂</a> <a id="6487" class="Symbol">=</a> 
    <a id="6494" href="Relation.Binary.PropositionalEquality.Core.html#2815" class="Function Operator">begin</a> 
        <a id="6509" class="Number">3</a> <a id="6511" href="NONaturals.html#4216" class="Primitive Operator">∸</a> <a id="6513" class="Number">5</a> 
    <a id="6520" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="6533" class="Number">2</a> <a id="6535" href="NONaturals.html#4216" class="Primitive Operator">∸</a> <a id="6537" class="Number">4</a> 
    <a id="6544" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="6557" class="Number">1</a> <a id="6559" href="NONaturals.html#4216" class="Primitive Operator">∸</a> <a id="6561" class="Number">3</a> 
    <a id="6568" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="6581" class="Number">0</a> <a id="6583" href="NONaturals.html#4216" class="Primitive Operator">∸</a> <a id="6585" class="Number">2</a> 
    <a id="6592" href="Relation.Binary.PropositionalEquality.Core.html#2873" class="Function Operator">≡⟨⟩</a> 
        <a id="6605" class="Number">0</a>
    <a id="6611" href="Relation.Binary.PropositionalEquality.Core.html#3114" class="Function Operator">∎</a> 
</pre>
### 练习`Bin`(拓展)

使用二进制系统能提供比一进制系统更高效的自然数表示，我们可以用一个比特串来表示一个数：

<pre class="Agda"><a id="6691" class="Keyword">data</a> <a id="Bin"></a><a id="6696" href="NONaturals.html#6696" class="Datatype">Bin</a> <a id="6700" class="Symbol">:</a> <a id="6702" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="6706" class="Keyword">where</a> 
    <a id="Bin.⟨⟩"></a><a id="6717" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="6720" class="Symbol">:</a> <a id="6722" href="NONaturals.html#6696" class="Datatype">Bin</a> 
    <a id="Bin._O"></a><a id="6731" href="NONaturals.html#6731" class="InductiveConstructor Operator">_O</a> <a id="6734" class="Symbol">:</a> <a id="6736" href="NONaturals.html#6696" class="Datatype">Bin</a> <a id="6740" class="Symbol">→</a> <a id="6742" href="NONaturals.html#6696" class="Datatype">Bin</a> 
    <a id="Bin._I"></a><a id="6751" href="NONaturals.html#6751" class="InductiveConstructor Operator">_I</a> <a id="6754" class="Symbol">:</a> <a id="6756" href="NONaturals.html#6696" class="Datatype">Bin</a> <a id="6760" class="Symbol">→</a> <a id="6762" href="NONaturals.html#6696" class="Datatype">Bin</a> 
</pre>
例如，以下比特串：

    1011

代表数字十一被编码为了

    ⟨⟩ I O I I 

由于前导零的存在，表示并不是唯一的。因此十一同样可以表示成`001011`，编码为:

    ⟨⟩ O O I O I I 

定义这样一个函数

    inc : Bin → Bin 

将一个比特串转换成下一个数的比特串。比如`1100`编码了十二，我们就应该有：

    inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O 

实现这个函数，并验证它对于表示零到四的比特串都能给出正确结果。

<pre class="Agda"><a id="inc"></a><a id="7040" href="NONaturals.html#7040" class="Function">inc</a> <a id="7044" class="Symbol">:</a> <a id="7046" href="NONaturals.html#6696" class="Datatype">Bin</a> <a id="7050" class="Symbol">→</a> <a id="7052" href="NONaturals.html#6696" class="Datatype">Bin</a> 
<a id="7057" href="NONaturals.html#7040" class="Function">inc</a> <a id="7061" class="Symbol">(</a><a id="7062" href="NONaturals.html#7062" class="Bound">pre</a> <a id="7066" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a><a id="7067" class="Symbol">)</a> <a id="7069" class="Symbol">=</a> <a id="7071" class="Symbol">(</a><a id="7072" href="NONaturals.html#7040" class="Function">inc</a> <a id="7076" href="NONaturals.html#7062" class="Bound">pre</a><a id="7079" class="Symbol">)</a> <a id="7081" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a>
<a id="7083" href="NONaturals.html#7040" class="Function">inc</a> <a id="7087" class="Symbol">(</a><a id="7088" href="NONaturals.html#7088" class="Bound">pre</a> <a id="7092" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a><a id="7093" class="Symbol">)</a> <a id="7095" class="Symbol">=</a> <a id="7097" href="NONaturals.html#7088" class="Bound">pre</a> <a id="7101" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> 
<a id="7104" href="NONaturals.html#7040" class="Function">inc</a> <a id="7108" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7111" class="Symbol">=</a> <a id="7113" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7116" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> 

<a id="7120" href="NONaturals.html#7120" class="Function">_</a> <a id="7122" class="Symbol">:</a> <a id="7124" href="NONaturals.html#7040" class="Function">inc</a> <a id="7128" class="Symbol">(</a><a id="7129" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7132" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a><a id="7133" class="Symbol">)</a> <a id="7135" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="7137" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7140" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> 
<a id="7143" class="Symbol">_</a> <a id="7145" class="Symbol">=</a> <a id="7147" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> 

<a id="7154" href="NONaturals.html#7154" class="Function">_</a> <a id="7156" class="Symbol">:</a> <a id="7158" href="NONaturals.html#7040" class="Function">inc</a> <a id="7162" class="Symbol">(</a><a id="7163" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7166" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a><a id="7167" class="Symbol">)</a> <a id="7169" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="7171" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7174" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> <a id="7176" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a> 
<a id="7179" class="Symbol">_</a> <a id="7181" class="Symbol">=</a> <a id="7183" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> 

<a id="7190" href="NONaturals.html#7190" class="Function">_</a> <a id="7192" class="Symbol">:</a> <a id="7194" href="NONaturals.html#7040" class="Function">inc</a> <a id="7198" class="Symbol">(</a><a id="7199" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7202" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> <a id="7204" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a><a id="7205" class="Symbol">)</a> <a id="7207" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="7209" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7212" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> <a id="7214" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> 
<a id="7217" class="Symbol">_</a> <a id="7219" class="Symbol">=</a> <a id="7221" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> 

<a id="7228" href="NONaturals.html#7228" class="Function">_</a> <a id="7230" class="Symbol">:</a> <a id="7232" href="NONaturals.html#7040" class="Function">inc</a> <a id="7236" class="Symbol">(</a><a id="7237" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7240" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> <a id="7242" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a><a id="7243" class="Symbol">)</a> <a id="7245" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="7247" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7250" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> <a id="7252" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a> <a id="7254" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a> 
<a id="7257" class="Symbol">_</a> <a id="7259" class="Symbol">=</a> <a id="7261" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> 

<a id="7268" href="NONaturals.html#7268" class="Function">_</a> <a id="7270" class="Symbol">:</a> <a id="7272" href="NONaturals.html#7040" class="Function">inc</a> <a id="7276" class="Symbol">(</a><a id="7277" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7280" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> <a id="7282" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a> <a id="7284" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a><a id="7285" class="Symbol">)</a> <a id="7287" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="7289" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7292" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> <a id="7294" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a> <a id="7296" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> 
<a id="7299" class="Symbol">_</a> <a id="7301" class="Symbol">=</a> <a id="7303" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> 
</pre>
使用以上定义，再定义一对函数用于在两种表示间的转换：

    to : ℕ → Bin 
    from : Bin → ℕ 

对于前者，用没有前导零的比特串来表示正数，并用`⟨⟩ O`表示零。验证这两个函数都能对零到四给出正确结果。

<pre class="Agda"><a id="to"></a><a id="7446" href="NONaturals.html#7446" class="Function">to</a> <a id="7449" class="Symbol">:</a> <a id="7451" href="NONaturals.html#584" class="Datatype">ℕ</a> <a id="7453" class="Symbol">→</a> <a id="7455" href="NONaturals.html#6696" class="Datatype">Bin</a> 
<a id="7460" href="NONaturals.html#7446" class="Function">to</a> <a id="7463" href="NONaturals.html#603" class="InductiveConstructor">zero</a> <a id="7468" class="Symbol">=</a> <a id="7470" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7473" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a> 
<a id="7476" href="NONaturals.html#7446" class="Function">to</a> <a id="7479" class="Symbol">(</a><a id="7480" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="7484" href="NONaturals.html#7484" class="Bound">n</a><a id="7485" class="Symbol">)</a> <a id="7487" class="Symbol">=</a> <a id="7489" href="NONaturals.html#7040" class="Function">inc</a> <a id="7493" class="Symbol">(</a><a id="7494" href="NONaturals.html#7446" class="Function">to</a> <a id="7497" href="NONaturals.html#7484" class="Bound">n</a><a id="7498" class="Symbol">)</a>

<a id="from"></a><a id="7501" href="NONaturals.html#7501" class="Function">from</a> <a id="7506" class="Symbol">:</a> <a id="7508" href="NONaturals.html#6696" class="Datatype">Bin</a> <a id="7512" class="Symbol">→</a> <a id="7514" href="NONaturals.html#584" class="Datatype">ℕ</a> 
<a id="7517" href="NONaturals.html#7501" class="Function">from</a> <a id="7522" class="Symbol">(</a><a id="7523" href="NONaturals.html#7523" class="Bound">pre</a> <a id="7527" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a><a id="7528" class="Symbol">)</a> <a id="7530" class="Symbol">=</a> <a id="7532" href="NONaturals.html#616" class="InductiveConstructor">suc</a> <a id="7536" class="Symbol">(</a><a id="7537" class="Number">2</a> <a id="7539" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="7541" href="NONaturals.html#7501" class="Function">from</a> <a id="7546" href="NONaturals.html#7523" class="Bound">pre</a><a id="7549" class="Symbol">)</a>
<a id="7551" href="NONaturals.html#7501" class="Function">from</a> <a id="7556" class="Symbol">(</a><a id="7557" href="NONaturals.html#7557" class="Bound">pre</a> <a id="7561" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a><a id="7562" class="Symbol">)</a> <a id="7564" class="Symbol">=</a> <a id="7566" class="Number">2</a> <a id="7568" href="NONaturals.html#3635" class="Primitive Operator">*</a> <a id="7570" href="NONaturals.html#7501" class="Function">from</a> <a id="7575" href="NONaturals.html#7557" class="Bound">pre</a> 
<a id="7580" href="NONaturals.html#7501" class="Function">from</a> <a id="7585" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7588" class="Symbol">=</a> <a id="7590" href="NONaturals.html#603" class="InductiveConstructor">zero</a> 

<a id="7597" href="NONaturals.html#7597" class="Function">_</a> <a id="7599" class="Symbol">:</a> <a id="7601" href="NONaturals.html#7446" class="Function">to</a> <a id="7604" class="Number">0</a> <a id="7606" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="7608" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7611" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a> 
<a id="7614" class="Symbol">_</a> <a id="7616" class="Symbol">=</a> <a id="7618" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> 

<a id="7625" href="NONaturals.html#7625" class="Function">_</a> <a id="7627" class="Symbol">:</a> <a id="7629" href="NONaturals.html#7446" class="Function">to</a> <a id="7632" class="Number">1</a> <a id="7634" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="7636" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7639" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> 
<a id="7642" class="Symbol">_</a> <a id="7644" class="Symbol">=</a> <a id="7646" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> 

<a id="7653" href="NONaturals.html#7653" class="Function">_</a> <a id="7655" class="Symbol">:</a> <a id="7657" href="NONaturals.html#7446" class="Function">to</a> <a id="7660" class="Number">2</a> <a id="7662" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="7664" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7667" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> <a id="7669" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a> 
<a id="7672" class="Symbol">_</a> <a id="7674" class="Symbol">=</a> <a id="7676" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> 

<a id="7683" href="NONaturals.html#7683" class="Function">_</a> <a id="7685" class="Symbol">:</a> <a id="7687" href="NONaturals.html#7446" class="Function">to</a> <a id="7690" class="Number">3</a> <a id="7692" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="7694" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7697" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> <a id="7699" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> 
<a id="7702" class="Symbol">_</a> <a id="7704" class="Symbol">=</a> <a id="7706" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> 

<a id="7713" href="NONaturals.html#7713" class="Function">_</a> <a id="7715" class="Symbol">:</a> <a id="7717" href="NONaturals.html#7446" class="Function">to</a> <a id="7720" class="Number">4</a> <a id="7722" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="7724" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7727" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> <a id="7729" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a> <a id="7731" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a> 
<a id="7734" class="Symbol">_</a> <a id="7736" class="Symbol">=</a> <a id="7738" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> 

<a id="7745" href="NONaturals.html#7745" class="Function">_</a> <a id="7747" class="Symbol">:</a> <a id="7749" href="NONaturals.html#7501" class="Function">from</a> <a id="7754" class="Symbol">(</a><a id="7755" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7758" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a><a id="7759" class="Symbol">)</a> <a id="7761" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="7763" class="Number">0</a>
<a id="7765" class="Symbol">_</a> <a id="7767" class="Symbol">=</a> <a id="7769" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> 

<a id="7776" href="NONaturals.html#7776" class="Function">_</a> <a id="7778" class="Symbol">:</a> <a id="7780" href="NONaturals.html#7501" class="Function">from</a> <a id="7785" class="Symbol">(</a><a id="7786" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7789" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a><a id="7790" class="Symbol">)</a> <a id="7792" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="7794" class="Number">1</a>
<a id="7796" class="Symbol">_</a> <a id="7798" class="Symbol">=</a> <a id="7800" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> 

<a id="7807" href="NONaturals.html#7807" class="Function">_</a> <a id="7809" class="Symbol">:</a> <a id="7811" href="NONaturals.html#7501" class="Function">from</a> <a id="7816" class="Symbol">(</a><a id="7817" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7820" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> <a id="7822" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a><a id="7823" class="Symbol">)</a> <a id="7825" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="7827" class="Number">2</a>
<a id="7829" class="Symbol">_</a> <a id="7831" class="Symbol">=</a> <a id="7833" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> 

<a id="7840" href="NONaturals.html#7840" class="Function">_</a> <a id="7842" class="Symbol">:</a> <a id="7844" href="NONaturals.html#7501" class="Function">from</a> <a id="7849" class="Symbol">(</a><a id="7850" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7853" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> <a id="7855" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a><a id="7856" class="Symbol">)</a> <a id="7858" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="7860" class="Number">3</a> 
<a id="7863" class="Symbol">_</a> <a id="7865" class="Symbol">=</a> <a id="7867" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> 

<a id="7874" href="NONaturals.html#7874" class="Function">_</a> <a id="7876" class="Symbol">:</a> <a id="7878" href="NONaturals.html#7501" class="Function">from</a> <a id="7883" class="Symbol">(</a><a id="7884" href="NONaturals.html#6717" class="InductiveConstructor">⟨⟩</a> <a id="7887" href="NONaturals.html#6751" class="InductiveConstructor Operator">I</a> <a id="7889" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a> <a id="7891" href="NONaturals.html#6731" class="InductiveConstructor Operator">O</a><a id="7892" class="Symbol">)</a> <a id="7894" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="7896" class="Number">4</a> 
<a id="7899" class="Symbol">_</a> <a id="7901" class="Symbol">=</a> <a id="7903" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> 
</pre>

