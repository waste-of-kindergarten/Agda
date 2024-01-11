# 关系

[TOC]

```txt
本章使用的 Unicode 符号：
    ≤  U+2264  小于等于 (\<=, \le)
    ≥  U+2265  大于等于 (\>=, \ge)
    ˡ  U+02E1  小写字母 L 标识符 (\^l)
    ʳ  U+02B3  小写字母 R 标识符 (\^r)
``` 

本章针对自然数继续深入，讨论有关自然数的 ***关系(Relation)*** 及其性质。

本章需要导入的库:

```agda 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)
``` 

## 小于等于 

小于等于是自然数中最常见的关系之一，推导规则如下：

    z≤n -------- 
        zero ≤ n 

        m ≤ n 
    s≤s ---------------- 
        suc m ≤ suc n 

它描述了：

- 起始步骤： 对于所有的自然数`n`，命题`zero ≤ n`成立
- 归纳步骤： 对于所有自然数`m`和`n`，如果命题`m ≤ n`成立，那么命题`suc m ≤ suc n`成立。

根据推导规则，写出对应的Agda定义：

```agda 
data _≤_ : ℕ → ℕ → Set where 

    z≤n : ∀ {n : ℕ}
        ----------- 
        → zero ≤ n 

    s≤s : ∀ {m n : ℕ}
        → m ≤ n  
        -------------
        → suc m ≤ suc n 
``` 

这里我们归纳定义了`_≤_`类型，它要接受两个自然数作为参数；在定义中有两个构造子`z≤n`和`s≤s`，分别对应上面的两个推导规则。两个构造子的签名中还使用了隐式参数，将在本章后面详细阐述。

> 注意区分无空格与有空格的区别，无空格写法作为方便阅读的构造子名称，而有空格的则表示一种类型

下面通过一个实例来说明如何使用构造子构造不等关系(`2 ≤ 4`)：

```agda 
_ : 2 ≤ 4 
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))
``` 

这个实例告诉我们`2 ≤ 4`的证明过程。

    z≤n --------
        0 ≤ 2 
    s≤s -------- 
        1 ≤ 3 
    s≤s -------- 
        2 ≤ 4 

### 优先级

小于等于的优先级应当比自然数的运算符低，加法运算符的优先级为6,我们设置小于等于的优先级为4,以便将`a + b ≤ c`解析为`(a + b) ≤ c`;另外连续的小于等于链是无意义的，从而它既不是左结合的又不是右结合的。

```agda 
infix 4 _≤_
``` 

## 关于隐式参数

`_≤_`的定义中，构造子的类型签名使用了`{ }`包裹参数，这表明被包裹的参数是 ***隐式的(Implicit)*** 。 当使用带有隐式参数的构造子时，我们可以同样使用花括号包裹住参数（如前面实例中的演示）或者直接省略掉隐式参数。

仍然以`2 ≤ 4`的实例为例,其他等效的写法还有：

```agda 
-- 完全省略隐式参数
_ : 2 ≤ 4 
_ = s≤s (s≤s z≤n)

-- 带有隐式参数名称的完整声明
_ : 2 ≤ 4
_ = s≤s {m = 1} {n = 3} (s≤s {m = 0} {n = 2} (z≤n {n = 2}))

-- 带有隐式参数名称的部分声明
_ : 2 ≤ 4 
_ = s≤s {n = 3} (s≤s {m = 0} z≤n)

```

> 值得注意的是，即使带有隐式参数名称的声明似乎是无关参数顺序的，我们仍然不能改变隐式参数的顺序。



## 反演

通过定义，我们从更小的不等式得到更大的不等式，但有时我们还需要从更大的不等式获取更小的不等式。

对于任意的`m`和`n`，证明`suc m ≤ suc n`的方式是唯一的（只能通过`s≤s m≤n`，其中`m≤n`类型为`m ≤ n`），这使得我们能够反演之前的规则。

```agda 
inv-s≤s : ∀ {m n : ℕ} 
    → suc m ≤ suc n 
    ---------------- 
    → m ≤ n 
inv-s≤s (s≤s m≤n) = m≤n 
``` 

并不是所有的规则都可以反演，`z≤n`规则由于没有显式假设，因此没有可以被反演的规则，然而这种反演通常是成立的。

```agda 
inv-z≤n : ∀ {m : ℕ} 
    → m ≤ zero 
    ------------ 
    → m ≡ zero 
inv-z≤n z≤n = refl 
``` 

## 序关系的性质

对于二元关系`≤`(注意这里不是小于等于而是泛指二元关系)，有一些常见的性质。

- ***自反性(Reflexive)*** ： 对所有的`n`，关系`n ≤ n`成立 
- ***传递性(Transitive)*** ： 对于所有的`m`,`n`和`p`，如果`m ≤ n`和`n ≤ p`成立，那么`m ≤ n`也成立
- ***反对称性(Anti-symmetric)*** ： 对于所有的`m`和`n`，如果`m ≤ n`和`n ≤ m`同时成立，那么`m ≡ n`成立
- ***完全性(Total)*** ： 对于所有的`m`和`n`，`m ≤ n`或者`n ≤ m`成立

后面将证明小于等于满足以上四条性质。

上述性质特定的组合也有相应的名称。

- ***预序(Preorder)*** ： 满足自反性和传递性的关系
- ***偏序(Partial Order)*** ： 满足反对称性的预序
- ***全序(Total Order)*** ： 满足完全性的偏序

### 自反性的证明

```agda 
≤-refl : ∀ {n : ℕ} 
    ------ 
    → n ≤ n 
≤-refl {zero} = z≤n 
≤-refl {suc n} = s≤s ≤-refl
``` 

自反性证明对`n`进行归纳，注意归纳步骤中等号右侧的`≤-refl`隐藏了隐式参数，表示`≤-refl {n}`，为归纳假设的内容。

### 传递性的证明

```agda 
≤-trans : ∀ {m n p : ℕ} 
    → m ≤ n 
    → n ≤ p 
    -------- 
    → m ≤ p 
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)
``` 

传递性证明在`m ≤ n`的证据上进行归纳，起始步骤中,`m ≤ n`因为`z≤n`成立（实际为`z≤n {n}`），那么结论也可以通过`z≤n`得到(实际为`z≤n {p}`)，这里`n ≤ p`的证明是不必要的，因此使用`_`表示该证明并未被使用；归纳步骤中，`suc m ≤ suc n`(第一个不等式)因为`s≤s m≤n`成立，`suc n ≤ suc p`(第二个不等式)因为`s≤s n≤p`成立，通过反演操作，我们能够使用归纳假设`≤-trans m≤n n≤p`得到`m ≤ p`成立，再使用`s≤s`推导规则即可得到`suc m ≤ suc p`，即归纳步骤得证。

程序中实际上隐藏了一种不可能的情况`≤-trans (s≤s m≤n) z≤n`，这实际上可以被Agda推断出来，因此我们无需列举。由于函数的第一个显式参数`s≤s m≤n`表明隐式参数`n`的模式是`suc _`，而第二个显示参数`z≤n`表明隐式参数`n`的模式是`zero`，显然这是不可能的。

### 反对称性的证明

```agda 
≤-antisym : ∀ {m n : ℕ} 
    → m ≤ n 
    → n ≤ m 
    ------- 
    → m ≡ n 
≤-antisym z≤n z≤n = refl 
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)
```  

证明技巧与前面类似，不再赘述。

### 完全性的证明

由于暂时没有学习使用逻辑连接词，我们定义一个数据类型来表示完全性。

```agda 
data Total (m n : ℕ) : Set where 

    forward :
        m ≤ n 
        -------- 
        → Total m n 

    flipped : 
        n ≤ m 
        --------
        → Total m n 
``` 

`Total m n`成立的证明有两种形式：`forward m≤n`或者`flipped n≤m`，其中`m≤n`和`n≤m`分别是`m ≤ n`和`n ≤ m`的证明。

下面进行完全性证明:

```agda 
≤-total : ∀ (m n : ℕ) → Total m n 
≤-total zero n = forward z≤n 
≤-total (suc m) zero = flipped z≤n 
≤-total (suc m) (suc n) with ≤-total m n 
...                        | forward m≤n = forward (s≤s m≤n)
...                        | flipped n≤m = flipped (s≤s n≤m)
``` 

这里我们对两个参数分别进行归纳。

- 初始步骤1： 如果第一个参数`zero`，第二个参数`n`，那么forward条件成立，我们使用`z≤n`作为`zero ≤ n`的证明
- 初始步骤2： 如果第一个参数`suc m`，第二个参数`m`,那么flipped条件成立，使用`z≤n`作为`suc m ≤ suc n`的证明
- 归纳步骤： 如果两个参数分别为`suc m`和`suc n`，那么归纳假设`≤-total m n`可以给出如下推断：
    + 归纳假设的forward条件成立，用`m≤n`作为`m ≤ n`的证明，以此我们可以使用`s≤s m≤n`作为`suc m ≤ suc n`来证明forward条件成立
    + 归纳假设的flipped条件成立，用`n≤m`作为`n ≤ m`的证明，以此可以使用`s≤s n≤m`作为`suc n ≤ suc m`来证明flipped条件成立

在完全性的证明中，我们使用了`with`语句：`with`关键字后面有一个表达式和若干行，每行以省略号和一个竖线开头，后面跟着用来匹配表达式的模式，以及等式右边绑定的项。

这等同于定义一个辅助函数：

```agda 
≤-total′ : ∀ (m n : ℕ) → Total m n 
≤-total′ zero n = forward z≤n
≤-total′ (suc m) zero = flipped z≤n
≤-total′ (suc m) (suc n) = helper (≤-total′ m n)
    where 
    helper : Total m n → Total (suc m) (suc n) 
    helper (forward m≤n) = forward (s≤s m≤n)
    helper (flipped n≤m) = flipped (s≤s n≤m)
``` 

> 熟悉haskell的读者会发现这类似haskell中的where用法


## 单调性

给定一个运算符和一个（全）序，那么就可以考虑该运算符对于这个序是否 ***单调(Monotonic)*** 。

加法对于小于等于就是单调的，这表明：

    ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q 

我们将整个证明分为三部分：

首先，我们证明加法对于小于等于在（加法）右侧是单调的。

```agda 
+-monoʳ-≤ : ∀ (n p q : ℕ) 
    → p ≤ q 
    -------------- 
    → n + p ≤ n + q 
+-monoʳ-≤ zero p q p≤q = p≤q 
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)
``` 

其次，证明加法对于小于等于在（加法）左侧是单调的。

```agda 
+-monoˡ-≤ : ∀ (m n p : ℕ) 
    → m ≤ n 
    → m + p ≤ n + p 
+-monoˡ-≤ m n p m≤n rewrite +-comm m p 
                    | +-comm n p = +-monoʳ-≤ p m n m≤n 
```

最后，将前两步的结论结合起来，得到加法关于小于等于是单调的：

```agda 
+-mono-≤ : ∀ (m n p q : ℕ) 
    → m ≤ n 
    → p ≤ q 
    → m + p ≤ n + q 
+-mono-≤ m n p q m≤n p≤q 
    = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q) 
``` 

通过前两个步骤，很容易得到`m + p ≤ n + p`和`n + p ≤ n + q`两个结论，再使用传递性得到`m + p ≤ n + p ≤ n + q`，即满足单调性`m + p ≤ n + q`。

## 严格不等关系

使用类似的定义可以定义严格不等关系，以小于关系为例。

```agda 
infix 4 _<_ 

data _<_ : ℕ → ℕ → Set where 

    z<s : ∀ {n : ℕ} 
        ------------ 
        → zero < suc n 

    s<s : ∀ {m n : ℕ} 
        → m < n 
        ------------ 
        → suc m < suc n 
```

小于关系不是自反的，但满足传递性，另外严格不等关系满足类似完全性的性质 -- ***三分律(Trichotomy)***， 即对于任意的`m`和`n`，`m < n`，`m ≡ n`或者`n < m`三者有且仅有一个成立。除此之外，小于关系对于加法也满足单调性。

## 奇偶性

前面提到的小于等于（不等关系）和小于（严格不等关系）属于二元关系，而奇和偶两种性质是一元关系，也称为 ***谓词(Predicate)*** 。

```agda
data even : ℕ → Set 
data odd : ℕ → Set 

data even where 
    
    zero : 
        ----------- 
        even zero 

    suc : ∀ {n : ℕ} 
        → odd n 
        ------------- 
        → even (suc n)

data odd where 

    suc : ∀ {n : ℕ}
        → even n 
        ------------ 
        → odd (suc n)
``` 

关于奇偶性的定义有两个有趣的点：

**1.使用重载的(Overloaded)构造子**

可以看到，奇偶性的定义中的构造子沿用了自然数中定义时使用的构造子，由于类型推导的机制，Agda可以自动推断重载的构造子的归属。

> 然而，也正是因为类型推断的限制，Agda不允许重载已定义的名字

**2.相互递归的数据类型**

由于在使用标识符前必须要先声明，因此在前两行首先声明了两种类型`even`和`odd`，然后再声明两种类型包含的构造子，在两个数据类型的`suc`构造子中，他们的签名函数都调用了对方数据类型作为构造子证据的前提条件。

接下来我们使用相互递归的函数，证明两个有关的性质。

```agda 
e+e≡e : ∀ {m n : ℕ} 
    → even m 
    → even n 
    --------------- 
    → even (m + n)

o+e≡o : ∀ {m n : ℕ} 
    → odd m 
    → even n 
    ---------------- 
    → odd (m + n)

e+e≡e zero en = en 
e+e≡e (suc om) en = suc (o+e≡o om en)
o+e≡o (suc em) en = suc (e+e≡e em en)
``` 

上述程序证明了使用两个相互递归的函数，证明了“两个偶数之和仍为偶数”和“奇数和偶数之和为奇数”，声明过程与相互递归的数据类型类似（先声明函数类型，再声明函数绑定的项）。

## 标准库

本章涉及的定义在标准库的对应：

```agda 
-- import Data.Nat using (_≤_; z≤n; s≤s)
-- import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total;
--                                   +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
``` 

## 附记： 参数化数据类型(Parametrized datatypes)与索引数据类型(Indexed datatypes)

本章中使用了带参数的数据类型（如`Total`，`even`，`odd`）和索引数据类型（如`_≤_`，`_<_`），我们以`Total`为例，对比参数化数据类型和索引数据类型。

前面已经给出了`Total`的定义，为了方便这里用`Totalₚ`表示参数化数据类型的`Total`定义；并用`Totalᵢ`表示索引数据类型的定义。

```agda 
data Totalᵣ (m n : ℕ) : Set where 

    forwardᵣ : 
        m ≤ n 
        ----------- 
        → Totalᵣ m n 

    flippedᵣ : 
        n ≤ m 
        ----------- 
        → Totalᵣ m n  

data Totalᵢ : ℕ → ℕ → Set where 

    forwardᵢ : ∀ {m n : ℕ}
        → m ≤ n 
        -------------
        → Totalᵢ m n 

    flippedᵢ : ∀ {m n : ℕ}
        → m ≤ n 
        ------------- 
        → Totalᵢ m n  
```

参数化数据类型在声明数据类型时就已经确定这个数据类型的参数是什么（在`Totalᵣ`中的`m n : ℕ`）；而索引数据类型在声明数据类型时只给出类型的参数类型（在`Totalᵢ`中的`ℕ → ℕ → Set`），这些参数需要进一步在构造子中明确。因此相比于参数化数据类型，索引数据类型允许不同的构造子返回类型中的参数类型不同，而参数化数据类型却不能做到这一点。如`_≤_`的定义中，`z≤n`构造子的返回类型为`zero ≤ n`而`s≤s`构造子的返回类型则为`suc m ≤ suc n`，因此只能定义成索引数据类型。

然而当使用参数化数据类型与索引数据类型均可以定义时（例如`Total`的定义），应当尽可能地使用参数化数据类型。一方面参数化数据类型书写更短，便于阅读；另一方面，参数化数据类型有利于帮助Agda停机的检查器。

实际上，可以将参数和索引混合起来使用进行数据类型的定义，一个总的形式如下：

    data D (x₁ : P₁) ... (xₖ : Pₖ) : (y₁ : Q₁) → ... → (yₗ : Qₗ) → Set ℓ where
    c₁ : A₁
    ...
    cₙ : Aₙ

其中`A₁`,...,`Aₙ`类型为：

    (z₁ : B₁) → ... → (zₘ : Bₘ) → D x₁ ... xₖ t₁ ... tₗ

后续章节我们会看到混合使用的场景。


## 习题参考

### 练习`orderings`(实践)

给出一个不是偏序的预序的例子。

```txt
复数域ℂ上模长的不等关系满足预序但不满足偏序。

（满足）自反性： 实数上的不等关系满足自反性，因此模长的不等关系也满足自反性
（满足）传递性： 实数上的不等关系满足传递性，因此模长的不等关系也满足传递性
（不满足）反对称性： 模长相同的复数有无穷多个，它们在复平面上形成一个圆，从而不成立
``` 

给出一个不是全序的偏序的例子。

```txt 
集合上的子集关系⊂。

（满足）自反性：一个集合必然是自己的子集。
（满足）传递性：包含关系的传递性。
（满足）反对称性：互相包含的集合是相等的。
（不满足）完全性：差集不为空的情况，不存在包含关系。
``` 

### 练习`≤-antisym-cases`(实践)

上面的证明中省略了一个参数是`z≤n`，另一个参数是`s≤s`的情况。为什么可以省略这种情况呢？

```txt 
z≤n 表明m的模式为zero，而 s≤s 表明n的模式为suc _，但这个情况是不可能的，Agda可以自动排除这种情况。
``` 

### 练习`*-mono-≤`(延伸)

证明乘法对于小于等于是单调的。

```agda 
open import Data.Nat using (_*_)
open import Data.Nat.Properties using (*-comm)

*-monoʳ-≤ : ∀ (n p q : ℕ)
    → p ≤ q 
    ----------------
    → n * p ≤ n * q 
*-monoʳ-≤ zero p q _ = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q ((*-monoʳ-≤ n p q p≤q)) 

*-monoˡ-≤ : ∀ (m n p : ℕ) 
    → m ≤ n 
    ----------------
    → m * p ≤ n * p 
*-monoˡ-≤ m n p m≤n rewrite *-comm m p 
    | *-comm n p = *-monoʳ-≤ p m n m≤n 

*-mono-≤ : ∀ (m n p q : ℕ)
    → m ≤ n 
    → p ≤ q 
    ----------------
    → m * p ≤ n * q 
*-mono-≤ m n p q m≤n p≤q = 
    ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q) 
```

### 练习`<-trans`(推荐)

证明严格不等式是传递的。请直接证明。

```agda 
<-trans : ∀ {m n p : ℕ}
    → m < n 
    → n < p 
    --------
    → m < p 
<-trans  z<s (s<s n<p) = z<s
<-trans  (s<s m<n) (s<s n<p) = 
    s<s (<-trans m<n n<p) 
``` 

### 练习`trichotomy`(实践)

证明严格不等关系满足弱化的三元律，证明对于任意`m`和`n`，下列命题有一条成立（不必证明互斥）：

- `m < n`
- `m ≡ n`
- `n < m`

（请类比完全性的证明）

```agda 
data Trichotomy (m n : ℕ) : Set where 

    forward : 
        m < n 
        ----------------- 
        → Trichotomy m n 
    
    refl : 
        m ≡ n 
        -----------------
        → Trichotomy m n 

    flipped : 
        n < m 
        -----------------
        → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n 
<-trichotomy zero zero = refl refl
<-trichotomy zero (suc n) = forward z<s
<-trichotomy (suc m) zero = flipped z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n 
...                             | forward m<n = forward (s<s m<n)  
...                             | refl m≡n = refl (cong suc m≡n) 
...                             | flipped n<m = flipped (s<s n<m) 
``` 

### 练习`+-mono-<`实践

证明加法对于严格不等关系是单调的。正如不等关系中那样，你可以需要额外的定义。

```agda 
+-monoʳ-< : ∀ (n p q : ℕ)
        → p < q 
        ----------------
        → n + p < n + q 
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ)
        → m < n 
        ----------------
        → m + p < n + p 
+-monoˡ-< m n p m<n rewrite +-comm m p 
                    | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ) 
        → m < n 
        → p < q 
        ----------------
        → m + p < n + q 
+-mono-< m n p q m<n p<q = 
    <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q) 
``` 

### 练习`+-iff-<`(实践)

证明`suc m ≤ n`蕴含了`m < n`，及其逆命题。

```agda 
+-iff-<→ : ∀ (m n : ℕ) 
        → suc m ≤ n 
        ------------
        → m < n 
+-iff-<→ zero (suc n) (s≤s sm≤n) = z<s
+-iff-<→ (suc m) (suc n) (s≤s sm≤n) = s<s (+-iff-<→ m n sm≤n) 

+-iff-<← : ∀ (m n : ℕ) 
        → m < n 
        ------------
        → suc m ≤ n 
+-iff-<← zero (suc n) m<n = s≤s z≤n
+-iff-<← (suc m) (suc n) (s<s m<n) = s≤s (+-iff-<← m n m<n) 
``` 

### 练习`<-trans-revisited`(实践)

用另外一种方法证明严格不等是传递的，使用之前证明的不等关系和严格不等关系的练习，以及不等关系的传递性。

```agda 
<-trans-revisited : ∀ {m n p : ℕ} 
                → m < n 
                → n < p 
                -------- 
                → m < p 
<-trans-revisited {m} {n} {p} m<n n<p = 
    +-iff-<→ m p (≤-trans 
    (≤-trans (+-iff-<← m n m<n) (+-monoˡ-≤ 0 1 n z≤n)) 
    (+-iff-<← n p n<p)) 
``` 

> 提示： 对于复杂的程序，应当充分利用交互证明的编成技巧

### 练习`o+o≡e`(延伸)

证明两个奇数之和为偶数。

```agda 
o+o≡e : ∀ {m n : ℕ}
    → odd m 
    → odd n 
    → even (m + n)
o+o≡e {suc m} {n} (suc em) on rewrite +-comm m n = suc (o+e≡o on em) 
``` 


### 练习`Bin-predicates`(延伸)

回忆我们在练习Bin中定义了一个数据类型`Bin`来用二进制字符串表示自然数，这个表达方式不是唯一的，因为我们在开头加任意个0。因此11可以由以下方法表示：

    ⟨⟩ I O I I 
    ⟨⟩ O O I O I I 

定义一个谓词

    Can : Bin → Set 

其在一个二进制字符串的表示是标准的(Canonical)时成立，表示它没有开头的0.在两个11的表达方式中，第一个是标准的，而第二个不是。在定义这个谓词时，你需要一个辅助谓词：

    One : Bin → Set 

其仅在一个二进制字符串开头为1时成立。一个二进制字符串是标准的，如果它开头是1（表示一个正数），或者它仅是一个0（表示0）。

证明递增可以保持标准性。

    Can b 
    --------------- 
    Can (inc b)

证明从自然数转换成的二进制字符串是标准的。

    ------------ 
    Can (to n)

证明将一个标准的二进制字符串转换成自然数之后，再转换回二进制字符串与原二进制字符串相同。

    Can b 
    -------------- 
    to (from b) ≡ b 

（提示： 对于每一条习题，先从`One`的性质开始。此外，你或许还需要证明若`One b`成立，则`1`小于或等于`from b`的结果。）

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

data One : Bin → Set where 
    one₀ : One (⟨⟩ I) 
    one₁₀ : ∀ {b : Bin}
        →  One b  
        → One (b O)
    one₁₁ : ∀ {b : Bin}
        → One b 
        → One (b I)

data Can : Bin → Set where 
    zero : Can (⟨⟩ O) 
    one : ∀ {b : Bin}
        → One b 
        → Can b 

inc-one : ∀ {b : Bin} → One b → One (inc b)
inc-one one₀ = one₁₀ one₀
inc-one (one₁₀ o) = one₁₁ o
inc-one (one₁₁ o) = one₁₀ (inc-one o) 

inc-can : ∀ {b : Bin} → Can b → Can (inc b)
inc-can zero = one one₀
inc-can (one o) = one (inc-one o)

to-can : ∀ (n : ℕ) → Can (to n)
to-can zero = zero
to-can (suc n) = inc-can (to-can n)

helper : ∀ {b : Bin} → One b → 1 ≤ from b 
helper one₀ = s≤s z≤n
helper {b O} (one₁₀ o) rewrite +-identityʳ (from b) = 
    +-mono-≤ 0 (from b) 1 (from b) (≤-trans z≤n (helper o)) (helper o)
helper {b I} (one₁₁ o) rewrite +-identityʳ (from b) = s≤s z≤n 

{-
to-from-can : ∀ {b : Bin} → Can b → to (from b) ≡ b 
to-from-can zero = refl
to-from-can {b} (one o) = {!   !}
-}
-- 尚未做出
```   