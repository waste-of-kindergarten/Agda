# 归纳证明

[TOC]

```txt
本章使用的 Unicode 符号：
    ∀  U+2200  对于所有 (\forall, \all)
    ʳ  U+02B3  修饰符小写字母 r (\^r)
    ′  U+2032  撇号 (\')
    ″  U+2033  双撇号 (\')
    ‴  U+2034  三撇号 (\')
    ⁗  U+2057  四撇号 (\')
``` 

上一章我们已经介绍了自然数的定义及其运算，但对自然数的性质仍然一无所获，本章将使用  ***归纳(Induction)*** 证明自然数满足哪些性质。

本章需要导入的库：

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
-- 导入 step-≡ 定义了 _≡⟨_⟩_ 
```

## 运算符的性质

常见的运算符性质如下：

- ***幺元(Identity)***: 对任意的`n`，若`𝟙 ∙ n ≡ n`，则`∙`有左幺元`𝟙`；若`n ∙ 𝟙 ≡ n`，则`∙`有右幺元`𝟙`。同时为左幺元和右幺元的值简称为幺元。幺元也称为 ***单位元(Unit)*** 。
- ***结合律(Associativity)***： 若括号的位置对于运算结果无影响，即对于任意的`m`，`n`和`p`，有`(m ∙ n) ∙ p ≡ m ∙ (n ∙ p)`,则称运算符满足结合律。
- ***交换律(Commutativity)***： 若参数顺序对于运算结果无影响，即对任意的`m`和`n`，有`m ∙ n ≡ n ∙ m`,则称运算符满足交换律。
- ***分配律(Distributivity)***： 对于所有的`m`，`n`和`p`，如果`m ∙₁ (n ∙₂ m) ≡ (m ∙₁ n) ∙₂ (m ∙₁ p)`，则运算符`∙₁`对运算符`∙₂`满足左分配律；类似地，如果`(m ∙₂ n) ∙₁ p ≡ (m ∙₁ p) ∙₂ (n ∙₁ p)`，则运算符`∙₁`对运算符`•₂`满足右分配律。

下面我们将讲解加法的结合律，交换律，分配律等被放入习题中。

## 结合律

加法满足结合律，将上面的结合律中的运算符`∙`替换为加法`+`即得：

    (m + n) + p ≡ m + (n + p)

注意这里的`m`，`n`和`p`取值范围为全体自然数。

可以很容易地验证实例(m = 3, n = 4, p = 5)：

```agda 
_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ = 
    begin 
        (3 + 4) + 5 
    ≡⟨⟩ 
        7 + 5 
    ≡⟨⟩ 
        12
    ≡⟨⟩ 
        3 + 9
    ≡⟨⟩ 
        3 + (4 + 5)
    ∎
``` 

但是由于自然数是无限多的，显然不能通过穷举的方式验证加法结合律对全部自然数成立，此时我们引入 ***归纳证明(Proof by Inducton)*** 。

根据自然数的定义，考虑自然数的性质`P`，自然数的归纳证明如下：

    ------ 
    P zero 

    P m 
    ----------
    P (suc m)

自然数的归纳证明描述了两个步骤：

- 起始步骤： 证明性质P对zero成立
- 归纳步骤： 如果性质P对任意自然数m成立，则证明性质P对m的后继成立

将`P`替换为加法结合律，就得到了：

    -------------------------------
    (zero + n) + p ≡ zero + (n + p)

    (m + n) + p ≡ m + (n + p)
    --------------------------------- 
    (suc m + n) + p ≡ suc m + (n + p)

有了明确的加法结合律归纳证明的推导规则，我们就可以使用Agda写出：

```agda 
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = 
    begin 
        (zero + n) + p 
    ≡⟨⟩ 
        n + p 
    ≡⟨⟩ 
        zero + (n + p)
    ∎ 
+-assoc (suc m) n p = 
    begin 
        (suc m + n) + p 
    ≡⟨⟩ 
        suc (m + n) + p 
    ≡⟨⟩ 
        suc ((m + n) + p)
    ≡⟨ cong suc (+-assoc m n p) ⟩
        suc (m + (n + p))
    ≡⟨⟩
        suc m + (n + p)
    ∎ 
```

在Agda中，标识符可以由除了空格和`@.(){};_`外的任何字符序列组成。
我们将加法结合律的标识符命名为`+-assoc`。

这段代码的首行，声明了标识符并给出了 ***类型签名(Signature)*** ， 即`+-assoc`所证明的命题：

    ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

该命题断言了对于所有的自然数`m`，`n`和`p`，等式`(m + n) + p ≡ m + (n + p)`成立。该命题的证据是一个接受三个自然数的函数，将自然数绑定到`m`，`n`和`p`上，就会返回等式对应的实例证据。

起始步骤的证明是平凡的，我们将注意力放在归纳步骤上。

对于归纳步骤需要证明：

    (suc m + n) + p ≡ suc m + (n + p)

使用加法定义进行逐步化简，得到：

    suc ((m + n) + p) ≡ suc (m + (n + p))

这个等式可以通过归纳假设`(m + n) + p ≡ m + (n + p)`两边加上`suc`得到，此时归纳步骤得证。

归纳步骤的等式链中，最初和最后的式子分贝匹配待证等式的两边，由于`_≡⟨⟩`是双向的，我们可以从上到下或从下到上阅读证明过程，直到遇到上述化简的等式。此时等式已经无法继续化简，需要使用一个附加运算符`_≡⟨_⟩_`，并将等式的依据放入尖括号内（依据应与尖括号用空格隔开）。

    ⟨ cong suc (+-assoc m n p) ⟩

其中`cong`表示 ***合同性(Congruence)*** ，即某个关系在应用了某个函数后仍然保持不变的性质。在此依据中，则为归纳假设`+-assoc m n p`在应用了`suc`后等式关系仍然保持不变。

对于加法来说，由于更大的自然数满足的结合律可以基于小的自然数的结合律证明，因此递归调用函数`+-assoc m n p`来证明归纳假设是 ***良基的(well-founded)***。 

## 交换律

在证明交换律前，我们需要先证明两条引理。

**引理1**  0是加法的一个右幺元。

    m + zero ≡ m

证明程序如下：

```agda 
+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m 
+-identityʳ zero = 
    begin 
        zero + zero 
    ≡⟨⟩ 
        zero 
    ∎
+-identityʳ (suc m) = 
    begin 
        suc m + zero 
    ≡⟨⟩ 
        suc (m + zero)
    ≡⟨ cong suc (+-identityʳ m) ⟩
        suc (zero + m)
    ≡⟨⟩ 
        suc m 
    ∎  
```

证明过程使用到的技巧与加法结合律类似，此处不再赘述。

**引理2** 对任意的自然数m,n，有`m + suc n ≡ suc (m + n)`

证明程序如下：

```agda 
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n) 
+-suc zero n = 
    begin 
        zero + suc n 
    ≡⟨⟩ 
        suc n 
    ≡⟨⟩ 
        suc (zero + n)
    ∎
+-suc (suc m) n = 
    begin 
        suc m + suc n 
    ≡⟨⟩ 
        suc (m + suc n)
    ≡⟨ cong suc (+-suc m n) ⟩
        suc (suc (m + n)) 
    ≡⟨⟩ 
        suc (suc m + n)
    ∎
``` 

下面利用这两条引理辅助证明加法的交换律。

```agda 
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m 
+-comm zero n = 
    begin 
        zero + n 
    ≡⟨⟩ 
        n 
    ≡⟨ sym (+-identityʳ n) ⟩
        n + zero 
    ∎ 
+-comm (suc m) n = 
    begin 
        (suc m) + n 
    ≡⟨⟩ 
        suc (m + n) 
    ≡⟨ cong suc (+-comm m n) ⟩
        suc (n + m)
    ≡⟨ sym (+-suc n m) ⟩
        n + suc m 
    ∎
``` 

上述代码中，使用了`sym`来交换两个引理等式两边的内容，从而使得等式链正常推导下去。

实际上，不使用`sym`也可以完成证明，只需要对`n`进行归纳即可。

```agda 
+-assoc-simple : ∀ (m n : ℕ) → m + n ≡ n + m 
+-assoc-simple m zero = 
    begin 
        m + zero 
    ≡⟨ +-identityʳ m ⟩
        m 
    ≡⟨⟩ 
        zero + m 
    ∎ 
+-assoc-simple m (suc n) = 
    begin 
        m + (suc n)
    ≡⟨ +-suc m n ⟩
        suc (m + n) 
    ≡⟨ cong suc (+-assoc-simple m n) ⟩
        suc (n + m)
    ≡⟨⟩ 
        suc n + m 
    ∎    
``` 

## 更深入的证明： 重排定理

根据加法的结合律我们可以得到推论，即重排定理：

```agda 
+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q 
+-rearrange m n p q = 
    begin 
        (m + n) + (p + q)
    ≡⟨ sym (+-assoc (m + n) p q) ⟩
        ((m + n) + p) + q  
    ≡⟨ cong (_+ q) (+-assoc m n p) ⟩
        (m + (n + p)) + q 
    ≡⟨⟩ 
        m + (n + p) + q 
    ∎  
``` 

重排定理允许我们任意应用结合律重排括号而不会改变结果。在上述代码中，使用的证明技巧与前面无异，唯一需要注意的是Agda支持的Richard Bird引入的 ***片段(Section)*** 记法`_+ q` -- 这种记法代表了函数`f(x) = x + q`。

## 改写技巧

除了使用等式链，我们还可以使用改写`rewrite`的方法对原定理的证明重新书写。

```agda 
+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)  
+-assoc′ zero n p = refl 
+-assoc′ (suc m) n p rewrite  +-assoc′ m n p = refl

+-identityʳ′ : ∀ (n : ℕ) → n + zero ≡ n 
+-identityʳ′ zero = refl 
+-identityʳ′ (suc n) rewrite +-identityʳ′ n = refl 

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n) 
+-suc′ zero n = refl 
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m 
+-comm′ zero n rewrite +-identityʳ′ n = refl
+-comm′ (suc m) n rewrite +-comm′ m n | +-suc′ n m = refl
-- 使用竖线分隔多个改写，依次执行

+-comm-simple′ : ∀ (m n : ℕ) → m + n ≡ n + m 
+-comm-simple′ m zero rewrite +-identityʳ′ m = refl
+-comm-simple′ m (suc n) rewrite +-suc′ m n | +-comm-simple′ m n = refl
``` 

在使用改写过程中，我们发现`rewrite`似乎更加智能，以`+-comm′`的证明为例，考虑起始步骤，`+-identityʳ n`对应的实例是`n + zero ≡ n`，而`+-comm′ zero n`所对应的实例为`zero + n ≡ n + zero`,在使用交互证明过程中，发现这样改写是完全没有问题的，改写后得到`n ≡ n`,这将使用`refl`立即得到。

在实际的操作过程中，看起来`rewrite`与`_≡⟨_⟩_`是类似的，但两者有明显的区别。因为如果两者作用相同，那么对于`+-comm′ zero n`的证明来说，完全可以对其进行如下改写`+-comm' zero n rewrite sym (+-identityʳ n) = refl`，但这是行不通的，在使用交互证明过程中，提示告诉我们这样重写得到的是`n + zero ≡ n + zero + zero`，这显然不能用`refl`证明，究其原因是`rewrite`将原式`zero + n ≡ n + zero`(根据定义自动化简为`n ≡ n + zero`)中匹配`n ≡ n + zero`左侧的部分全部替换成了右侧的部分，因此才有`n + zero ≡ n + zero + zero`。

另外，不难发现上述程序中也省去了`cong`，因此使用`rewrite`可以大大简化证明过程。

## 标准库

本章涉及的定义在标准库的对应：

```agda 
-- import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
``` 

## 习题参考


### 练习`operators`(实践)

请给出另一对运算符，它们拥有一个幺元，满足结合律和交换律，且其中一个对另一个满足分配律。（不必证明）

```txt
考虑一个集合A的幂集，以及两个运算符∪(并集),∩(交集)

它们满足题设基本条件：

∅ ∪ A₁ ≡ A₁ 
(A₁ ∪ A₂) ∪ A₃ ≡ A₁ ∪ (A₂ ∪ A₃)
A₁ ∪ A₂ ≡ A₂ ∪ A₁ 

A ∩ A₁ ≡ A₁ 
(A₁ ∩ A₂) ∩ A₃ ≡ A₁ ∩ (A₂ ∩ A₃)
A₁ ∩ A₂ ≡ A₂ ∩ A₁ 

且交集对并集满足分配律：
A₁ ∩ (A₂ ∪ A₃) ≡ A₁ ∩ A₂ ∪ A₁ ∩ A₃
-- 因为满足交换律，因此左分配律自然可以推出右分配律
```

请给出一个运算符的例子，它拥有幺元，满足结合律但不满足交换律（不必证明）。

```txt 
例如对称群S₃（所有索引集合为{1,2,3}的排列组合的群），

根据群的定义，S₃一定有幺元，且排列的复合满足结合律。

但它不满足交换律，它是最小的不满足交换律的对称群。
```

### 练习`finite-+-asoc`(延伸)

略

### 练习`+-swap`（推荐）

请证明对于所有自然数`m`,`n`和`p`，

    m + (n + p) ≡ n + (m + p)

成立。使用前面的结论，无需归纳证明。

```agda 
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p) 
    | +-comm m n 
    | +-assoc n m p = refl  
``` 

### 练习`*-distrib-+`(推荐)

请证明乘法对加法满足分配律，即对于所有的自然数`m`,`n`和`p`，

    (m + n) * p ≡ m * p + n * p 

成立。

```agda 
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p 
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p 
    | +-assoc p (m * p) (n * p) = refl 
``` 

### 练习`*-assoc`(推荐)

请证明乘法满足结合律，即对于所有自然数`m`,`n`和`p`，

    (m * n) * p ≡ m * (n * p)

成立。

```agda 
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p 
    | *-assoc m n p = refl 
``` 

### 练习`*-comm`(推荐)

请证明乘法满足交换律，即对于所有的自然数`m`和`n`，

    m * n ≡ n * m 

成立。和加法交换律一样，您需要先证明相应的引理。

```agda 
*-zeroʳ : ∀ (n : ℕ) → n * zero ≡ zero 
*-zeroʳ zero = refl
*-zeroʳ (suc n) rewrite *-zeroʳ n = refl 

*-suc : ∀ (m n : ℕ) → m * (suc n) ≡ m + m * n 
*-suc zero n = refl
*-suc (suc m) n rewrite *-suc m n 
    | sym (+-assoc n m (m * n)) 
    | +-comm n m 
    | +-assoc m n (m * n) = refl 

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m 
*-comm zero n rewrite *-zeroʳ n = refl
*-comm (suc m) n rewrite *-comm m n 
    | *-suc n m = refl  
``` 

### 练习`0∸n≡0`(实践)

请证明对于所有自然数`n`，

    zero ∸ n ≡ zero

成立。你的证明需要归纳法吗？

```agda 
-- 需要，因为饱和减法的定义中，将n按照自然数的两种推导规则分开
0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero 
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl
```

### 练习`∸-+-assoc`(实践)

请证明饱和减法与加法满足结合律，即对于所有的自然数`m`,`n`和`p`，

    m ∸ n ∸ p ≡ m ∸ (n + p)

成立。

```agda 
∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc m (suc n) zero rewrite +-identityʳ n = refl
∸-+-assoc zero (suc n) (suc p) = refl
∸-+-assoc (suc m) (suc n) (suc p) rewrite ∸-+-assoc m n (suc p) = refl 
``` 

### 练习`+*^`(延伸)

证明下列三条定律：

    m ^ (n + p) ≡ (m ^ n) * (m ^ p) (^-distribˡ-+-*)
    (m * n) ^ p ≡ (m ^ p) * (n ^ p) (^-distribʳ-*)
    (m ^ n) ^ p ≡ m ^ (n * p) (^-*-assoc)

对于所有`m`，`n`和`p`成立。

```agda 
^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p rewrite +-identityʳ (m ^ p) = refl
^-distribˡ-+-* m (suc n) p rewrite ^-distribˡ-+-* m n p 
    | *-assoc m (m ^ n) (m ^ p) = refl

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) rewrite ^-distribʳ-* m n p 
    | *-assoc m n ((m ^ p) * (n ^ p))
    | sym (*-assoc n (m ^ p) (n ^ p))
    | *-comm n (m ^ p)
    | *-assoc (m ^ p) n (n ^ p)
    | *-assoc m (m ^ p) (n * (n ^ p)) = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero rewrite *-zeroʳ n = refl
^-*-assoc m n (suc p) rewrite ^-*-assoc m n p
    | *-suc n p 
    | ^-distribˡ-+-* m n (n * p) = refl 
``` 

### 练习`Bin-laws`（延伸）

回想练习Bin中定义的一种表示自然数的比特串数据类型`Bin`以及要求你定义的函数:

    inc : Bin → Bin 
    to : ℕ → Bin 
    from : Bin → ℕ 

考虑以下定律，其中`n`表示自然数，`b`表示比特串：

    from (inc b) ≡ suc (from b)
    to (from b) ≡ b
    from (to n) ≡ n

对于每一条定律：若它成立，请证明；若不成立，请给出一个反例。

```agda 
data Bin : Set where 
    ⟨⟩ : Bin 
    _O : Bin → Bin 
    _I : Bin → Bin 

inc : Bin → Bin 
inc (pre I) = (inc pre) O
inc (pre O) = pre I 
inc ⟨⟩ = ⟨⟩ I

to : ℕ → Bin 
to zero = ⟨⟩ O 
to (suc n) = inc (to n)

from : Bin → ℕ 
from (pre I) = suc (2 * from pre)
from (pre O) = 2 * from pre 
from ⟨⟩ = zero 

Bin-laws₁ : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
Bin-laws₁ ⟨⟩ = refl
Bin-laws₁ (b O) = refl 
Bin-laws₁ (b I) rewrite Bin-laws₁ b 
    | +-identityʳ (from b)
    | +-suc (from b) (from b)  = refl

-- Bin-laws₂ : ∀ (b : Bin) → to (from b) ≡ b 
-- 不成立，因为对于相同的自然数，可以有许多Bin的对应，但to (from b)只是其中之一,
-- 例如 to (from ⟨⟩ O O) ≡ ⟨⟩ O

Bin-laws₃ : ∀ (n : ℕ) → from (to n) ≡ n 
Bin-laws₃ zero = refl
Bin-laws₃ (suc n) rewrite Bin-laws₁ (to n) 
    | Bin-laws₃ n = refl
```