# 布尔值与判定过程

[TOC]

```txt
本章使用的 Unicode 符号：
    ∧  U+2227  逻辑和 (\and, \wedge)
    ∨  U+2228  逻辑或 (\or, \vee)
    ⊃  U+2283  超集 (\sup)
    ᵇ  U+1D47  修饰符小写 B  (\^b)
    ⌊  U+230A  左向下取整 (\clL)
    ⌋  U+230B  右向下取整 (\clR)
``` 

有两种方式表示关系：

- 计算关系是否成立的函数

- 由关系成立的证明构成的数据类型

本章引入新的布尔值记法表达关系，并最后将两者结合起来得到一种新的 ***可判定性(Decidable)*** 记法。

先导入必要的库：

```agda 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.part1.Relations using (_<_; z<s; s<s)
open import plfa.part1.Isomorphism using (_⇔_)
``` 

## 证据与计算

在之前的章节我们已经使用归纳数据类型了小于等于关系，接下来我们使用布尔类型定义这个关系。

```agda 
data Bool : Set where 
    true : Bool 
    false : Bool 

infix 4 _≤ᵇ_
_≤ᵇ_ : ℕ → ℕ → Bool 
zero ≤ᵇ n = true
suc m ≤ᵇ zero = false 
suc m ≤ᵇ suc n = m ≤ᵇ n 
```

以`2 ≤ᵇ 4`为例，证明过程如下：

```agda 
_ : (2 ≤ᵇ 4) ≡ true 
_ = 
    begin 
        2 ≤ᵇ 4 
    ≡⟨⟩
        1 ≤ᵇ 3 
    ≡⟨⟩ 
        0 ≤ᵇ 2 
    ≡⟨⟩ 
        true 
    ∎
``` 

类似地，也可以证明`4 ≤ᵇ 2`不成立，使用不等式链最后推导出`false`。

实际上这种使用"布尔类型计算命题成立与否的方法"与"使用证明的方法"是有明确联系的。

我们先定义函数将计算映射到证明上。

```agda 
T : Bool → Set 
T true = ⊤
T false = ⊥
``` 

容易证明命题成立当且仅当相应的计算为`true`.

```agda 
T↔≡ : ∀ (b : Bool) → (T b) ⇔ (b ≡ true)
T↔≡ b with b 
...     | true = 
                record 
                    {   to = λ _ → refl 
                    ;   from = λ _ → tt
                    }
...     | false = 
                record
                    {   to = λ () 
                    ;   from = λ ()
                    }
``` 

据此，就可以证明`_≤ᵇ_`和`≤`的对应关系：

```agda 
infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

open _⇔_

≤ᵇ↔≤ : ∀ (m n : ℕ) → (T (m ≤ᵇ n)) ⇔ (m ≤ n) 
≤ᵇ↔≤ m n with m | n 
...         | zero | _ = 
                        record 
                            {   to = λ _ →  z≤n 
                            ;   from = λ _ → tt 
                            }
...         | suc m | zero = 
                        record 
                            {   to = λ ()
                            ;   from = λ () 
                            } 
...         | suc m | suc n = 
                        record 
                            {   to = λ x → s≤s (to (≤ᵇ↔≤ m n) x)
                            ;   from = λ { (s≤s x) → from (≤ᵇ↔≤ m n) x}
                            }  
``` 


当使用证明时，我们可以忽略掉不成立的情况，而只考虑成立的情况，这样可以简化许多工作；但对于复杂的关系的证明，有时我们更需要使用计算机直接计算出答案。幸运地是，我们有一种新的方法来兼取其优。

## 可判定性记法 -- 兼取其优

对于返回布尔值的函数，其表达了某个关系是否成立；而证据则表达了某个关系为什么成立，但需要我们手动给出证明过程。使用可判定性记法，我们可以兼取其优。

```agda 
data Dec (A : Set) : Set where 
    yes : A → Dec A 
    no : ¬ A → Dec A 
``` 

可判定类型有两个构造子，对于一个`Dec A`类型，其要么由`yes x`的形式呈现，要么以`no ¬x`形式呈现，其中`x`和`¬x`分别提供了`A`成立和无法成立的证明。

下面定义判定类型版本的不等关系：

```agda 
-- 不等式不成立的证明: 起始
¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z () 
-- 不等式不成立的证明： 归纳 
¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤? n = yes z≤n
suc m ≤? zero = no ¬s≤z
suc m ≤? suc n with m ≤? n 
...             | yes m≤n = yes (s≤s m≤n) 
...             | no ¬m≤n = no (¬s≤s ¬m≤n)
``` 

我们来使用新的函数计算实例`2 ≤? 4`成立和`4 ≤? 2`不成立:

``` 
_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl 

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_ = refl

``` 

可以看到，可判定类型的版本中，我们明确地表明某个关系是否成立，同时也给出了关系成立的原因。当我们分别使用计算和证明的方法来表达同一种关系时，我们将不得不提供它们之间的对应关系，使用可判定类型，则无需如此，因此可判定类型的版本更为简洁。

当然对于某些情况可能产生的特殊需求，我们仍然可以从这个版本中派生出来`_≤ᵇ_`。


***擦出(Erasure)*** 将一个可判定的值转换为一个布尔值：

```agda 
⌊_⌋ : ∀ {A : Set} → Dec A → Bool 
⌊ yes x ⌋ = true 
⌊ no ¬x ⌋ = false 
``` 

使用此函数可以派生出`_≤ᵇ_`:

```agda 
_≤ᵇ′_ : ℕ → ℕ → Bool 
m ≤ᵇ′ n = ⌊ m ≤? n ⌋
``` 

进一步地，对于类型为`Dec A`的值`D`，`A`成立当且今当`T ⌊ D ⌋`成立：

```agda 
toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A 
toWitness {A} {yes x} tt = x 
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _ = tt 
fromWitness {A} {no ¬x} x = ¬x x  
``` 

上面合起来就是`_≤ᵇ_`和`_≤_`的对应关系，即`≤ᵇ↔≤`。

## 逻辑连接符

我们直接给出布尔值合取和析取的定义：

```agda 
infixr 6 _∧_
infixr 5 _∨_ 

_∧_ : Bool → Bool → Bool 
true ∧ true = true 
false ∧ _ = false 
_ ∧ false = false 

_∨_ : Bool → Bool → Bool 
true ∨ _ = true 
_ ∨ true = true 
false ∨ false = false
``` 

相应地，给定两个可判定的命题，可以判定它们的合取和析取：

```agda 
infixr 6 _×-dec_
infixr 5 _⊎-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ{ ⟨ x , y ⟩ → ¬x x }
_     ×-dec no ¬y = no λ{ ⟨ x , y ⟩ → ¬y y }

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
_     ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }
``` 

接着我们给出布尔值的否定以及可判定命题的否定：

```agda 
not : Bool → Bool 
not true = false 
not false = true 

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x) = no (¬¬-intro x)
¬? (no ¬x) = yes ¬x 
``` 

最后还有一个比较陌生的运算符，这个运算符与蕴涵相对应：

```agda 
_⊃_ : Bool → Bool → Bool 
_ ⊃ true = true 
false ⊃ _ = true 
true ⊃ false = false 

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B) 
_ →-dec yes y = yes (λ _ → y) 
no ¬x →-dec _ = yes (λ x → ⊥-elim (¬x x))
yes x →-dec no ¬y = no (λ f → ¬y (f x))
``` 

## 互映证明

回顾第一章定义的自然数`monus`，对于一个较小的数减去较大的数，结果只能为零，因为对于任何的情况我们必须给出一个值，然而我们可以使用带有 ***守卫(guarded)*** 版本的减法，将这种不合理的情况剔除。

```agda 
minus : (m n : ℕ) (n≤m : n ≤ m) → ℕ 
minus m zero _ = m 
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m
``` 

这种定义虽然保证了对于不合理情况的限制，但难以使用：

```agda 
_ : minus 5 3 (s≤s (s≤s (s≤s z≤n))) ≡ 2
_ = refl
``` 

虽然这个问题目前没有通用解决方案，但上述情形下我们可以得到两个数的具体值，因此
我们的解决方案是，使用 ***互映证明(proof by reflection)*** 技术，在类型检查时同时让Agda自动判定`n ≤ m`。

```agda 
_-_ : (m n : ℕ) {n≤m : T ⌊ n ≤? m ⌋} → ℕ 
_-_ m n {n≤m} = minus m n (toWitness n≤m)
``` 

通过设置一个类型为`T ⌊ n ≤? m ⌋`的隐式参数，当我们传入参数时，如果最终规约为`⊤`，则Agda会提供相应的隐式参数；否则类型规约为`⊥`，Agda无法为此类型提供任何值，因此会报错。另外通过`toWitness`可以将自动计算完成的判定类型转化为`n ≤ m`的证据，避免了手动提供限制不等式的证据。至此我们就可以安全地使用自然数上的减法了（当然前提是满足已知两个数的具体值的情形）。

## 标准库

```agda 
-- import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
-- import Data.Nat using (_≤?_)
-- import Relation.Nullary using (Dec; yes; no)
-- import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
-- import Relation.Nullary.Negation using (¬?)
-- import Relation.Nullary.Product using (_×-dec_)
-- import Relation.Nullary.Sum using (_⊎-dec_)
-- import Relation.Binary using (Decidable)
```  

## 习题参考

### 练习`_<?_`(推荐)

与上面的函数相似，定义一个判定严格不等性的函数：

```agda 
_<?_ : ∀ (m n : ℕ) → Dec (m < n) 
``` 

```agda 
-- 不等式不成立的证明: 起始
¬n<z : ∀ {m : ℕ} → ¬ (m < zero)
¬n<z () 
-- 不等式不成立的证明： 归纳 
¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n

zero <? (suc n) = yes z<s
m <? zero = no ¬n<z
suc m <? suc n with m <? n 
...             | yes m<n = yes (s<s m<n) 
...             | no ¬m<n = no (¬s<s ¬m<n)
``` 

### 练习`_≡ℕ?_`(实践)

定义一个函数来判定两个自然数是否相等。

```agda 
open import Data.Nat using (_∸_)
open Eq using (cong)

¬s≡z : ∀ {m : ℕ} → ¬ (suc m ≡ zero)
¬s≡z = λ() 

¬z≡s : ∀ {n : ℕ} → ¬ (zero ≡ suc n)
¬z≡s = λ() 

¬s≡s : ∀ {m n : ℕ} → ¬ (m ≡ n) → ¬ (suc m ≡ suc n)
¬s≡s = λ ¬m≡n sm≡sn → ¬m≡n (cong (_∸ 1) sm≡sn)


_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n) 
zero ≡ℕ? zero = yes refl 
zero ≡ℕ? suc _ = no ¬z≡s
suc _ ≡ℕ? zero = no ¬s≡z
suc m ≡ℕ? suc n with m ≡ℕ? n 
...             |   yes m≡n = yes (cong suc m≡n) 
...             |   no ¬m≡n = no (¬s≡s ¬m≡n)
``` 

### 练习`erasure`(实践)

证明擦出将对应的布尔值和可判定的值的操作联系起来：

```agda 
∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
``` 

```agda 
∧-× (yes a) (yes b) = refl 
∧-× (no ¬a) (yes b) = refl 
∧-× (yes a) (no ¬b) = refl 
∧-× (no ¬a) (no ¬b) = refl

∨-⊎ (yes a) (yes b) = refl 
∨-⊎ (no ¬a) (yes b) = refl 
∨-⊎ (yes a) (no ¬b) = refl 
∨-⊎ (no ¬a) (no ¬b) = refl

not-¬ (yes a) = refl 
not-¬ (no ¬a) = refl
``` 

### 练习`iff-erasure`(推荐)

给出等价`_↔_`对应的布尔与可判定值的操作，并证明对应的擦除：

```agda 
_iff_ : Bool → Bool → Bool
_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
``` 

```agda 
true iff true = true 
false iff false = true 
_ iff _ = false  

(yes a) ⇔-dec (yes b) = yes (record 
                {   to = λ _ → b 
                ;   from = λ _ → a }) 
(no ¬a) ⇔-dec (yes b) = no (λ a⇔b → ¬a (from a⇔b b)) 
(yes a) ⇔-dec (no ¬b) = no (λ a⇔b → ¬b (to a⇔b a)) 
(no ¬a) ⇔-dec (no ¬b) = yes (record 
                { to = λ a → ¬¬-intro a ¬a 
                ; from = λ b → ¬¬-intro b ¬b }) 
-- 注意此处的¬¬-intro来自标准库，它类似于plfa版本的¬¬-intro加上⊥-elim的效果
-- 最终返回的结果为任意类型

iff-⇔ (yes a) (yes b) = refl 
iff-⇔ (yes a) (no ¬b) = refl 
iff-⇔ (no ¬a) (yes b) = refl 
iff-⇔ (no ¬a) (no ¬b) = refl 
``` 
   
### 练习`False`(实践)

给出`True`，`toWitness`和`fromWitness`的相反定义。分别为`False`，`toWitnessFalse`和`fromWitnessFalse`。

其中，`True`是标准库中与`T ⌊ ? ⌋`同义的函数，定义如下：

```agda
True : ∀ {Q} → Dec Q → Set 
True Q = T ⌊ Q ⌋
``` 

```agda 
False : ∀ {Q} → Dec Q → Set 
False Q = T (not ⌊ Q ⌋)

toWitnessFalse : ∀ {A : Set} {D : Dec A} → False D → ¬ A 
toWitnessFalse {D = no ¬a} tt = ¬a

fromWitnessFalse : ∀ {A : Set} {D : Dec A} → ¬ A → False D
fromWitnessFalse {D = no ¬a} _ = tt
fromWitnessFalse {D = yes a} ¬a = ¬a a 
``` 

