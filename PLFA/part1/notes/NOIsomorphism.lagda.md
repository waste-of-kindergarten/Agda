# 同构与嵌入

[TOC]

```txt 
本章使用的 Unicode 符号：
    ∘  U+2218  环运算符 (\o, \circ, \comp)
    λ  U+03BB  小写希腊字母 LAMBDA (\lambda, \Gl)
    ≃  U+2243  渐进相等 (\~-)
    ≲  U+2272  小于或等价于 (\<~)
    ⇔  U+21D4  左右双箭头 (\<=>)
``` 

本章介绍 ***同构(Isomorphism)*** 与 ***嵌入(Embedding)*** 。

本章需要导入的库：

```agda 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
``` 

## Lambda表达式，函数复合，外延性

在介绍同构与嵌入之前，需要引入一些基础知识，首先介绍Lambda 表达式，Lambda 表达式提供了一种简洁的定义函数的方法。

对于一个函数`f`，定义了如下等式：

    f P₁ = N₁ 
    ... 
    f Pₙ = Nₙ 

其中`Pᵢ`为模式，`Nᵢ`为表达式。

使用Lambda表达式可以表示为：

    λ{ P₁ → N₁; ... ; Pₙ → Nₙ }

当`n`为`1`时，且模式是一个变量时，可以继续简写为：

    λ x → N 
    或
    λ (x : A) → N 

使用Lambda表达式避免了提供函数名以及冗长的类型签名，其定义处即为使用的位置。

下面我们讨论 ***函数复合(Function Composition)***，其Agda定义如下。

```agda 
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C) 
(g ∘ f) x = g (f x) 
``` 

以上定义也可以立即用Lambda 表达式改写。

```agda 
_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f = λ x → g (f x)
``` 

最后我们介绍外延性。外延性给出了区分函数的唯一方法，如果两个函数作用在相同的参数时永远返回相同的值，那么外延性会断言两个函数相同。这实际上是`cong-app`的逆命题。

在Agda中并没有预设外延性，因此我们可以以 ***公设(postulate)*** 的方式直接声明其成立：

```agda 
postulate
    extensionality : ∀ {A B : Set} → {f g : A → B} 
        → (∀ (x : A) → f x ≡ g x)
        -------------------------- 
        → f ≡ g 
``` 

添加外延性不仅不会导致Agda产生矛盾，而且在某些情况下会更便利，例如定义另一个加法`_+′_`。

```agda 
_+′_ : ℕ → ℕ → ℕ 
m +′ zero = m 
m +′ suc n = suc (m +′ n)
``` 

我们希望判断两个加法是不可区分的，在不使用外延性公设的情况下，我们只能证明命题：`∀ (m n : ℕ) → m +′ n ≡ m + n`成立:

```agda 
same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n 
same-app m n rewrite +-comm m n = helper m n 
    where 
    helper : ∀ (m n : ℕ) → m +′ n ≡ n + m 
    helper m zero = refl 
    helper m (suc n) = cong suc (helper m n)
``` 

而使用外延性公设，我们可以更进一步证明：

```agda 
_ : _+′_ ≡ _+_ 
_  = extensionality (λ m → extensionality (λ n  → same-app m n))
```

最后，为了能够将外延性使用在依赖函数上，可以将外延性推广如下：

```agda 
postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
``` 

> 关于依赖函数或依赖类型读者可以自行查看相关文档，这里给出一个简短的说明
>依赖函数空间(dependent function space) (a : A) → (B a) 是接受一个类型为A的参数a,产生类型为B a的结果的函数类型.其中,'A'是一个类型,B是一个以A中的元素为索引的类型族.

## 同构

如果两个集合有一一对应关系，那么说这两个集合同构。

> 实际上对于更复杂的数学结构，同构还需要保证其他数学结构，例如对于序同构需要保证映射后序结构不变，群同构需要保运算。

其Agda的定义如下：

```agda 
infix 0 _≃_
record _≃_ (A B : Set) : Set where 
    field
        to : A → B 
        from : B → A 
        from∘to : ∀ (x : A) → from (to x) ≡ x 
        to∘from : ∀ (y : B) → to (from y) ≡ y 
``` 

这里第一次使用了 ***记录(record)*** 语法，记录类型主要由一个构造子和若干域组成，构造子和域的使用都是可选的；除此之外，域的顺序可变，且后声明的域可以使用先声明的域。

    record <recordname> <parameters> : Set <level> where
    <directives>
    constructor <constructorname>
    field
        <fieldname1> : <type1>
        <fieldname2> : <type2>
        -- ...
    <declarations>

在同构类型的声明中，有四个域（亦证明同构的四个条件），分别为：

- `to` : 从 `A` 到 `B` 的函数
- `from` : 从 `B` 到 `A` 的函数
- `from∘to` : `from`是`to`的 ***左逆(left-inverse)***
- `from∘to` : `from`是`to`的 ***右逆(right-inverse)***

> 值得注意的是，当我们脱离了声明作用域但希望在当前作用域中使用记录中函数时，需要使用前缀来给出这个函数的所属，例如`_≃_.to`；当然也可以直接将其打开到当前作用域中`open _≃_`

## 同构是等价关系

同构是一个等价关系，满足自反性，对称性和传递性。

对于自反性，不难发现只需构造的恒等函数即可。

```agda 
≃-refl : ∀ {A : Set}
    -------- 
    → A ≃ A 
≃-refl = 
    record
        {   to = λ{x → x} 
        ;   from = λ{y → y} 
        ;   from∘to = λ{ x → refl} 
        ;   to∘from = λ{y → refl} 
        }
``` 

对于对称性，我们只需要将`to`和`from`，‵from∘to`和`to∘from`调换即可。

```agda 
open _≃_

≃-sym : ∀ {A B : Set}
    → A ≃ B 
    --------- 
    → B ≃ A 
≃-sym A≃B = 
    record 
        {   to = from A≃B
        ;   from = to A≃B
        ; from∘to  = to∘from A≃B
        ; to∘from = from∘to A≃B
        } 
```  

最后我们需要证明传递性，证明传递性只需要对相应函数进行复合（并化简）即可。

```agda 
≃-trans : ∀ {A B C : Set} 
    → A ≃ B 
    → B ≃ C 
    -------- 
    → A ≃ C 
≃-trans A≃B B≃C = 
    record 
        {   to = to B≃C ∘ to A≃B
        ;   from = from A≃B ∘ from B≃C
        ;   from∘to = λ{x → 
                begin 
                    ((from A≃B ∘ from B≃C) ∘ (to B≃C ∘ to A≃B)) x 
                ≡⟨⟩ 
                    from A≃B (from B≃C (to B≃C (to A≃B x)))
                ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
                    from A≃B (to A≃B x)
                ≡⟨ from∘to A≃B x ⟩
                    x 
                ∎}
        ;   to∘from = λ{y → 
                begin
                    ((to B≃C ∘ to A≃B) ∘ (from A≃B ∘ from B≃C)) y 
                ≡⟨⟩
                    to B≃C (to A≃B (from A≃B (from B≃C y)))
                ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
                    to B≃C (from B≃C y)
                ≡⟨ to∘from B≃C y ⟩
                    y
                ∎}
        }     
``` 

## 同构的相等性论证

类似等式的相等性论证（等式链），我们可以定义同构的相等性论证。

```agda 
module ≃-Reasoning where 
    
    infix  1 ≃-begin_
    infixr 2 _≃⟨_⟩_
    infix  3 _≃-∎

    ≃-begin_ : ∀ {A B : Set}
        → A ≃ B 
        -------- 
        → A ≃ B 
    ≃-begin A≃B = A≃B 

    _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
        → A ≃ B 
        → B ≃ C 
        --------
        → A ≃ C
    A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

    _≃-∎ : ∀ (A : Set)
        ------- 
        → A ≃ A 
    A ≃-∎ = ≃-refl 

open ≃-Reasoning
``` 

## 嵌入

嵌入是同构的弱化概念，同构要求证明两个类型之间的一一对应关系，而嵌入则要求证明两个类型之间有一对多的对应关系。

```agda 
infix 0 _≲_ 
record _≲_ (A B : Set) : Set where 
    field 
        to : A → B 
        from : B → A 
        from∘to : ∀ (x : A) → from (to x) ≡ x 

open _≲_
``` 

显然，嵌入关系的要求更为宽泛，缺少了`to∘from`的条件，也就是说嵌入关系的`from`未必是`to`的右逆（如果是，则该嵌入也是同构）。

嵌入关系满足自反性和传递性，但不满足对称性。

```agda 
≲-refl : ∀ {A : Set} 
    ---------
    → A ≲ A 
≲-refl = 
    record 
        {   to = λ{x → x}
        ;   from = λ{y → y}
        ;   from∘to = λ{x → refl}
        }

≲-trans : ∀ {A B C : Set} 
        → A ≲ B 
        → B ≲ C 
        -------- 
        → A ≲ C 
≲-trans A≲B B≲C = 
    record 
        {   to = to B≲C ∘ to A≲B
        ;   from = from A≲B ∘ from B≲C
        ;   from∘to = λ{x →
                    begin
                        ((from A≲B ∘ from B≲C) ∘ (to B≲C ∘ to A≲B)) x
                    ≡⟨⟩
                        from A≲B (from B≲C (to B≲C (to A≲B x)))
                    ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
                        from A≲B (to A≲B x)
                    ≡⟨ from∘to A≲B x ⟩
                        x
                    ∎}
        }
``` 

另外，如果两个类型相互嵌入，且嵌入函数对应，则它们是同构的，这是反对称性的一种弱化形式。

```agda 
≲-antisym : ∀ {A B : Set} 
    → (A≲B : A ≲ B)
    → (B≲A : B ≲ A)
    → (to A≲B ≡ from B≲A)
    → (from A≲B ≡ to B≲A)
    ---------------------- 
    → A ≃ B 
≲-antisym A≲B B≲A to≡from from≡to = 
    record 
        {   to = to A≲B
        ;   from = from A≲B
        ;   from∘to = from∘to A≲B
        ;   to∘from = λ{y → 
                begin 
                    to A≲B (from A≲B y)
                ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
                    to A≲B (to B≲A y)
                ≡⟨ cong-app to≡from (to B≲A y) ⟩
                    from B≲A (to B≲A y)
                ≡⟨ from∘to B≲A y ⟩
                    y  
                ∎}    
        }
``` 

## 嵌入的相等性证明

最后我们给出关于嵌入的相等性证明。

```agda 
module ≲-Reasoning where 

    infix 1 ≲-begin_ 
    infixr 2 _≲⟨_⟩_ 
    infix 3 _≲-∎

    ≲-begin_ : ∀ {A B : Set} 
        → A ≲ B 
        -------- 
        → A ≲ B 
    ≲-begin A≲B = A≲B 

    _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
        → A ≲ B 
        → B ≲ C 
        -------- 
        → A ≲ C 
    A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

    _≲-∎ : ∀ (A : Set)
        -----
        → A ≲ A
    A ≲-∎ = ≲-refl

open ≲-Reasoning
``` 

## 标准库

本章涉及的定义在标准库的对应：

```agda 
-- import Function using (_∘_)
-- import Function.Inverse using (_↔_)
-- import Function.LeftInverse using (_↞_)
``` 

其中`↔`和`↞`分别对应同构和嵌入

## 习题参考

### 练习`≃-implies-≲`(实践)

证明每个同构蕴含一个嵌入。

```agda 
≃-implies-≲ : ∀ {A B : Set} 
    → A ≃ B 
    -------- 
    → A ≲ B 
≃-implies-≲ A≃B = 
    record
        {   to = to A≃B
        ;   from = from A≃B
        ;   from∘to = from∘to A≃B
        }
``` 

### 练习`_⇔_`(实践)

按照下列形式定义命题的等价性（当且仅当）：

```agda 
record _⇔_ (A B : Set) : Set where 
    field
        to : A → B 
        from : B → A 
``` 

证明等价性是自反，对称和传递的。

```agda 
open _⇔_

⇔-refl : ∀ {A : Set}
    --------- 
    → A ⇔ A 
⇔-refl = 
    record 
        {   to = λ x → x 
        ;   from = λ y → y 
        }

⇔-trans : ∀ {A B C : Set}
    → A ⇔ B 
    → B ⇔ C 
    -------- 
    → A ⇔ C 
⇔-trans A⇔B B⇔C = 
    record 
        {   to = to B⇔C ∘ to A⇔B  
        ;   from = from A⇔B ∘ from B⇔C
        }

⇔-sym : ∀ {A B : Set}
    → A ⇔ B 
    -------- 
    → B ⇔ A 
⇔-sym A⇔B = 
    record 
        {   to = from A⇔B
        ;   from = to A⇔B
        }
``` 

### 练习`Bin-embedding`(延伸)

回忆练习Bin和Bin-laws，我们定义了比特串数据类型`Bin`来表示自然数，并要求你来定义下列函数：

    to : ℕ → Bin 
    from : Bin → ℕ 

它们满足如下性质：

    from (to n) ≡ n 

使用上述条件，证明存在一个从`ℕ`到`Bin`的嵌入。

```agda 
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
data Bin : Set where 
    ⟨⟩ : Bin 
    _O : Bin → Bin 
    _I : Bin → Bin 

inc : Bin → Bin 
inc (pre I) = (inc pre) O
inc (pre O) = pre I 
inc ⟨⟩ = ⟨⟩ I

toᵇ : ℕ → Bin 
toᵇ zero = ⟨⟩ O 
toᵇ (suc n) = inc (toᵇ n)

fromᵇ : Bin → ℕ 
fromᵇ (pre I) = suc (2 * fromᵇ pre)
fromᵇ (pre O) = 2 * fromᵇ pre 
fromᵇ ⟨⟩ = zero 

Bin-laws₁ : ∀ (b : Bin) → fromᵇ (inc b) ≡ suc (fromᵇ b)
Bin-laws₁ ⟨⟩ = refl
Bin-laws₁ (b O) = refl 
Bin-laws₁ (b I) rewrite Bin-laws₁ b 
    | +-identityʳ (fromᵇ b)
    | +-suc (fromᵇ b) (fromᵇ b)  = refl

Bin-laws₃ : ∀ (n : ℕ) → fromᵇ (toᵇ n) ≡ n 
Bin-laws₃ zero = refl
Bin-laws₃ (suc n) rewrite Bin-laws₁ (toᵇ n) 
    | Bin-laws₃ n = refl

ℕ≲Bin : ℕ ≲ Bin 
ℕ≲Bin = 
    record
        {   to = toᵇ
        ;   from = fromᵇ
        ;   from∘to = Bin-laws₃
        }  
``` 