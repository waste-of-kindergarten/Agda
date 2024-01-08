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

- ***自反性(Reflexive)*** : 对所有的`n`，关系`n ≤ n`成立 
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

小于关系不是自反的，但满足传递性，另外严格不等关系满足类似完全性的性质 -- ***三分律(Trichotomy)***， 即对于任意的`m`和`n`，`m < n`，`m ≡ n`或者`m > n`三者有且仅有一个成立。除此之外，小于关系对于加法也满足单调性。

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

## 附记： 参数化数据类型与索引数据类型

## 习题参考




