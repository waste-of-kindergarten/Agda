# 相等性与等式推理

[TOC]

```txt 
本章使用的 Unicode 符号：
    ≡  U+2261  等同于 (\==, \equiv)
    ⟨  U+27E8  数学左尖括号 (\<)
    ⟩  U+27E9  数学右尖括号 (\>)
    ∎  U+220E  证毕 (\qed)
    ≐  U+2250  趋近于极限 (\.=)
    ℓ  U+2113  手写小写 L (\ell)
    ⊔  U+2294  正方形向上开口 (\lub)
    ₀  U+2080  下标 0 (\_0)
    ₁  U+2081  下标 1 (\_1)
    ₂  U+2082  下标 2 (\_2)
``` 

本章将讨论前面使用过的相等性，此前我们将其作为基本的运算，下面会说明如何将其定义为一个归纳数据类型。

## 相等性

下面进行相等性的定义：

```agda 
data _≡_ {A : Set} (x : A) : A → Set where 
    refl : x ≡ x 
``` 

对于任意类型`A`和任意类型为`A`的值`x`，构造子`refl`提供了`x ≡ x`的证明。

这里使用了混合参数化和索引的数据类型（如上一章所说），一方面，应当尽量使用 ***参数(Parameter)*** 而非索引；另一方面，由于必须保证第二个 ***参数(Argument)*** 与第一个 ***参数(Argument)*** 一致，因此必须使用索引。

> 这里Parameter指数据类型声明的形参，而Argument指实际传入的参数（实参）

类似小于等于`_≤_`，相等性关系的优先级也应当不如其他算术运算符紧密，且相等性也不是结合的，因此定义优先级如下：

```agda 
infix 4 _≡_
``` 

## 相等性是等价关系

一个等价关系应当满足自反性，对称性与传递性，关于自反性和传递性的定义于上一章已经给出，下面给出对称性的数学定义：

- ***对称性(symmetric)*** : 对于所有的`m`和`n`，以及关系`R`，如果`mRn`成立，则`nRm`成立。

因此要想证明相等性是等价关系，只需要证明它满足以上三种性质。

对于自反性，已经在相等性定义中由构造子`refl`给出，无需证明。

对于对称性的证明如下：

```agda 
sym : ∀ {A : Set} {x y : A} 
    → x ≡ y 
    -------- 
    → y ≡ x 
sym refl = refl 
``` 

`y ≡ x`成立的条件是`x ≡ y`，而它成立的证据只能由`refl`给出（或者说`_≡_`在进行模式匹配时只有一种模式），此时`y`被限制与`x`相等，因此待证明的结论就化为了`x ≡ x`，我们只需要绑定一个为此提供证据的项(即`refl`)即可。

下面证明传递性：

```agda
trans : ∀ {A : Set} {x y z : A} 
    → x ≡ y 
    → y ≡ z 
    ------- 
    → x ≡ z 
trans refl refl = refl 
```

传递性的证明也比较直接，结论成立的条件`x ≡ y`和`y ≡ z`只能由`refl`给出，因此`y`和`z`被限制为了`x`，结论化为`x ≡ x`可由`refl`给出。

## 合同性和替换性

相等性还满足 ***合同性(Congruence)***，即： 对任意的`x`和`y`，以及函数`f`，如果`x ≡ y`，则`f x ≡ f y`。

下面证明合同性：

```agda 
cong : ∀ {A B : Set} (f : A → B) {x y : A} 
    → x ≡ y 
    -------- 
    → f x ≡ f y 
cong f refl = refl
```

合同性还可以延伸到二元函数或者多元函数，以二元函数为例：

```agda 
cong₂ : ∀ {A B C : Set} (f : A → B → C) {x y : A} {u v : B}
    → x ≡ y 
    → u ≡ v 
    --------------- 
    → f x u ≡ f y v
cong₂ f refl refl = refl 
``` 

对于相等的函数而言，也满足合同性：

```agda 
cong-app : ∀ {A B : Set} {f g : A → B}
    → f ≡ g 
    -----------------------------
    → ∀ (x : A) → f x ≡ g x 
cong-app refl x = refl
``` 

相等性也满足 ***替换性(Substitution)***，如果两个值相等，其中一个满足某个谓词，那么另一个值也满足该谓词。

```agda 
subst : ∀ {A : Set} {x y : A} (P : A → Set)
    → x ≡ y 
    → P x 
    -------
    → P y 
subst P refl px = px
``` 

谓词`P`是对于类型（亦命题）`A`参数化的一个类型，可以参考上一章中关于奇偶性的定义。

## 等式链

完成了有关相等性及其性质的定义后，我们可以开始讨论如何定义等式链。由于等式链涉及一系列的运算符号，可以将其封装到一个 ***模块(module)*** 中，这里为了方便对应标准库，将模块命名为`≡-Reasoning`。

```agda 
module ≡-Reasoning {A : Set} where 

    infix 1 begin_ 
    infixr 2 _≡⟨⟩_ _≡⟨_⟩_
    infix 3 _∎

    begin_ : ∀ {x y : A}
        → x ≡ y 
        -------- 
        → x ≡ y 
    begin x≡y = x≡y 

    _≡⟨⟩_ : ∀ (x : A) {y : A} 
        → x ≡ y 
        --------- 
        → x ≡ y 
    x ≡⟨⟩ x≡y = x≡y 

    _≡⟨_⟩_ : ∀ (x : A) {y z : A} 
        → x ≡ y 
        → y ≡ z 
        --------- 
        → x ≡ z 
    x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z 

    _∎ : ∀ (x : A)
        ----- 
        → x ≡ x 
    x ∎ = refl 

open ≡-Reasoning
``` 

一个嵌套模块包括了关键字`module`和后续的模块名（可包含隐式参数或显式参数），以及关键字`where`和模块中的内容（缩进的部分）。模块中可以包含任何形式声明，也可以包含其他模块。结束模块后，可通过`open`将嵌套模块中的全部定义导入当前的环境中。

上面的`≡-Reasoning`模块中的定义对应了前几章使用的标准库中的定义，根据定义不难发现：

- 四个有关等式链推导的符号优先级不如相等性，因此均小于4
- 整个等式链从末端开始计算(`_∎`优先级最高)，然后从后向前依次计算(`_⟨⟩_`和`_⟨_⟩_`优先级次于`_∎`，且右结合)，直到等式链的初端(`begin_`优先级最低)
- 等式链的推导实际上是不断使用传递性的过程，最终使用相等性（即相等的自反性）证明的过程
- `_⟨⟩_`与`_⟨ refl ⟩_`效果相同

最后值的一提的是，Agda总会认为化简结果相同的项是等同的，从而不对它们进行区分，这也是我们使用`_⟨⟩_`将不同式子串联起来的原因，我们可以根据自身需要对串联的式子进行合理的排列，以便符合人类阅读。



## 莱布尼兹(Leibniz)相等性与层级

> 我们使用的相等性断言的形式源于 Martin-Löf，于 1975 年发表。一个更早的形式源于莱布尼兹， 于 1686 年发表。莱布尼兹断言的相等性表示不可分辨的实体（Identity of Indiscernibles）： 两个对象相等当且仅当它们满足完全相同的性质。这条原理有时被称作莱布尼兹定律（Leibniz’ Law）， 与史波克定律紧密相关：「一个不造成区别的区别不是区别」。我们在这里定义莱布尼兹相等性， 并证明两个项满足莱布尼兹相等性当且仅当其满足 Martin-Löf 相等性。

拉布尼兹相等性定义如下：

每个对于`x`成立的性质`P`对于`y`也成立，则认为`x`和`y`莱布尼兹相等，记作`x ≐ y`。

其Agda的定义如下：

```agda 
_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y  
``` 

> 由于需要提供隐式参数`A`，我们无法将等号左边写成`x ≐ y`的形式。

注意类型签名中返回类型使用了`Set₁`而非`Set`，这是因为我们无法将`Set`赋予类型`Set`，否则会导致矛盾（例如Russell悖论或Girard悖论）。为了避免矛盾，我们引入了 ***层级(Level)*** ：`Setᵢ : Setᵢ₊₁`,其中`i`属于自然数。特别地，使用`Set`作为`Set₀`的简写。

莱布尼兹相等性也是等价关系，满足自反性，对称性和传递性。

```agda 
refl-≐ : ∀ {A : Set} {x : A}
    → x ≐ x 
refl-≐ P Px = Px 

trans-≐ : ∀ {A : Set} {x y z : A}
    → x ≐ y 
    → y ≐ z 
    --------
    → x ≐ z 
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

sym-≐ : ∀ {A : Set} {x y : A}
    → x ≐ y 
    -------- 
    → y ≐ x 
sym-≐ {A} {x} {y} x≐y P = Qy 
    where 
        Q : A → Set 
        Q z = P z → P x 
        Qx : Q x 
        Qx = refl-≐ P 
        Qy : Q y 
        Qy = x≐y Q Qx

``` 

对称性的证明相对比较复杂，但其根本实际上是构造一个新的谓词`Q`，以便能够得到`P y → P x`的证据。

下面证明“莱布尼兹相等性当且仅当其满足 Martin-Löf 相等性”，我们将两个方向的证明拆分。

首先证明 *Martin-Löf 相等性 蕴含 莱布尼兹相等性*。

```agda 
-- 我认为更简洁的方式
≡-implies-≐ : ∀ {A : Set} {x y : A} 
        → x ≡ y 
        -------- 
        → x ≐ y 
≡-implies-≐ refl P Px = Px

-- plfa 中给出的证明使用了替换性
≡-implies-≐′ : ∀ {A : Set} {x y : A}
        → x ≡ y 
        -------- 
        → x ≐ y 
≡-implies-≐′ x≡y P = subst P x≡y 
``` 

接着证明其逆命题。

```agda 
≐-implies-≡ : ∀ {A : Set} {x y : A}
        → x ≐ y 
        → x ≡ y 
≐-implies-≡ {A} {x} {y} x≐y = Qy 
    where 
        Q : A → Set 
        Q z = x ≡ z 
        Qx : Q x 
        Qx = refl 
        Qy : Q y 
        Qy = x≐y Q Qx
``` 

匿命题的证明与对称性的证法如出一辙，使用的相同的技巧，核心都在于谓词`Q`的合理构造。

## 全体多态

前面已经提到，我们无法让每个类型都属于`Set`，否则就会引发矛盾，因此我们引入了类型层级`Setᵢ : Setᵢ₊₁`，并认为每个类型都属于类型层级的某处`Setᵢ`，其中`i`是自然数。

为了使用层级，需要首先导入如下内容：

```agda 
open import Level using (Level;_⊔_) renaming (zero to lzero; suc to lsuc)
``` 

为了避免层级与自然数混淆，通过重命名将其构造子与自然数构造子区分。

实际上，层级与自然数是同构的：

    lzero : Level
    lsuc : Level → Level 

设同构映射为`f : ℕ → Level`（双射且对构造子保运算），则定义`Setᵢ`为`Set f(i)`，其中`i`为自然数。

另外，我们还有一个运算符：

    _⊔_ : Level → Level → Level 

这个运算符接受两个层级，返回较大的一个。该运算符用于计算涉及多个层级的类型属于哪个层级。

本章前面涉及到的定义为了便于说明原理，都是局限于比较`Set`层次的类型的值，并不适用于其他层级。在实际的标准库中，通过使用 ***全体多态(Universe Polymorphism)*** ，可以将这些定义推广至任何层级。

下面给出相等性和对称性推广的定义。

```agda 
data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
    refl′ : x ≡′ x 

sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A}
    → x ≡′ y 
    -------- 
    → y ≡′ x 
sym′ refl′ = refl′
```

以及莱布尼兹相等性的推广定义：

```agda 
_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y 
``` 

前面定义的未推广的莱布尼兹相等性定义是上述推广的特例(ℓ = lzero)。

## 标准库

本章涉及的定义在标准库的对应：

```agda 
-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
``` 

## 习题参考

### 练习`≤-Reasoning`(延伸)

章节Relations中的单调性证明也可以用类似`≡-Reasoning`这种更容易理解的形式给出，请仿照定义`≤-Reasoning`，并用其重新给出加法对于不等式是单调的证明，重写`+-monoˡ-≤`，`+-monoʳ-≤`和`+-mono-≤`的定义。

```agda 
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)

-- 公设：不加证明地给出
-- 从标准库导出会导致奇怪的问题，因此这里声明了自定义的版本
postulate
    +-identityʳ : ∀ (m : ℕ) → m + zero ≡ m 
    +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)


module ≤-Reasoning where

    infix 1 ≤-begin_  
    infixr 2 _≤⟨⟩_  _≤⟨_⟩_ _≡→≤⟨_⟩_
    infix 3 _≤-∎  

    ≤-begin_ : ∀ {x y : ℕ}
        → x ≤ y 
        --------- 
        → x ≤ y
    ≤-begin x≤y = x≤y

    _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ} 
        → x ≤ y 
        ----------
        → x ≤ y     
    x ≤⟨⟩ x≤y = x≤y

    _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
        → x ≤ y 
        → y ≤ z 
        -------- 
        → x ≤ z 
    x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z  

    _≡→≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
        → x ≡ y 
        → y ≤ z 
        -------- 
        → x ≤ z 
    x ≡→≤⟨ refl ⟩ y≤z = y≤z  

    _≤-∎ : ∀ (x : ℕ)
        -------- 
        → x ≤ x 
    x ≤-∎ = ≤-refl

open ≤-Reasoning

+-monoʳ-≤ : ∀ (n p q : ℕ) 
    → p ≤ q 
    ---------------- 
    → n + p ≤ n + q 
+-monoʳ-≤ zero p q p≤q = 
    ≤-begin 
        zero + p 
    ≤⟨⟩ 
        p 
    ≤⟨ p≤q ⟩
        q 
    ≤⟨⟩ 
        zero + q  
    ≤-∎
+-monoʳ-≤ (suc n) p q p≤q = 
    ≤-begin 
        (suc n) + p 
    ≤⟨⟩
        suc (n + p) 
    ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
        suc (n + q)
    ≤⟨⟩ 
        suc n + q 
    ≤-∎ 


+-monoˡ-≤ : ∀ (m n p : ℕ) 
    → m ≤ n 
    ------------------
    → m + p ≤ n + p 
+-monoˡ-≤ m n zero m≤n = 
    ≤-begin 
        m + zero
    ≡→≤⟨ +-identityʳ m ⟩
        m 
    ≤⟨ m≤n ⟩
        n 
    ≡→≤⟨ sym (+-identityʳ n) ⟩
        n + zero 
    ≤-∎    
+-monoˡ-≤ m n (suc p) m≤n = 
    ≤-begin
        m + suc p 
    ≡→≤⟨ +-suc m p ⟩
        suc (m + p) 
    ≤⟨ s≤s (+-monoˡ-≤ m n p m≤n) ⟩
        suc (n + p)
    ≡→≤⟨ sym (+-suc n p) ⟩
        n + suc p
    ≤-∎

+-mono-≤ : ∀ (m n p q : ℕ)
    → m ≤ n 
    → p ≤ q 
    ----------------  
    → m + p ≤ n + q 
+-mono-≤ m n p q m≤n p≤q = 
    ≤-begin
        m + p 
    ≤⟨ +-monoˡ-≤ m n p m≤n ⟩
        n + p 
    ≤⟨ +-monoʳ-≤ n p q p≤q ⟩
        n + q 
    ≤-∎  
``` 





 
 