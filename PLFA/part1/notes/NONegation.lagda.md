# 命题的否定

[TOC]

```txt 
本章使用的 Unicode 符号：
    ¬  U+00AC  否定符号 (\neg)
    ≢  U+2262  不等价于 (\==n)
``` 

本章主要介绍否定的性质。首先导入必要的库：

```agda 
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import plfa.part1.Isomorphism using (_≃_; extensionality)
``` 

## 否定

给定命题`A`，当`A`不成立时，它的否定形式`¬ A`成立。

```agda 
¬_ : Set → Set 
¬ A = A → ⊥ 
``` 

我们将否定阐述为“蕴涵假”的形式，如果从`A`可以推出`⊥`，则`¬ A`必然成立。这是 ***归谬法(Reductio ad Absurdum)*** 的一种形式。

给定`A`和`¬ A`均成立的证据，可以得到`⊥`成立，也就是通常说的矛盾。

```agda 
¬-elim : ∀ {A : Set} 
    → ¬ A 
    → A 
    ----- 
    → ⊥ 
¬-elim ¬x x = ¬x x 
``` 

> 应当注意到，这个命题是`→-elim`的特例

如果一个命题`A`成立，那么双重否定后的命题`¬ ¬ A`也成立。

```agda 
¬¬-intro : ∀ {A : Set}
    → A 
    ----- 
    → ¬ ¬ A 
¬¬-intro x = λ{¬x → ¬x x}
``` 

由于在Agda中使用的是直觉逻辑，因此我们并不能像经典逻辑那样得到逆命题成立，本章后面将补充讨论直觉逻辑和经典逻辑的区别。

尽管如此，我们仍然可以证明一个类似的命题：

```agda 
¬¬¬-elim : ∀ {A : Set}
    → ¬ ¬ ¬ A 
    ---------- 
    → ¬ A 
¬¬¬-elim ¬¬¬x = λ{x → ¬¬¬x (¬¬-intro x)}
``` 

除此之外，另一个重要的命题是 ***换质换位律(contraposition)*** ，这有点类似逆否命题与原命题的关系，但注意在直觉逻辑中原命题和双重否定命题并不是等价的。

```agda 
contraposition : ∀ {A B : Set}
    → (A → B) 
    --------- 
    → (¬ B → ¬ A)
contraposition f ¬y = λ x → ¬y (f x)
``` 

定义完否定，我们就可以继续定义不等性：

```agda 
_≢_ : ∀ {A : Set} → A → A → Set 
x ≢ y = ¬ (x ≡ y) 
``` 

皮亚诺公理中的一条假设"0不是任何数的后继数"，可以用不等性很容易地证出:

```agda 
peano : ∀ {m : ℕ} → zero ≢ suc m 
peano = λ()
``` 

这里我们首次在λ表达式中使用了 ***谬模式(Absurd Pattern)***，这等同于：

```agda 
peano′ : ∀ {m : ℕ} → zero ≢ suc m 
peano′ ()
``` 

最后我们可以证明任意两个否定的证明都是相等的：

```agda 
assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′ 
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))
``` 

注意这里证明目标是函数相等，因此需要使用外延性。

### 优先级

我们将否定优先级设定为高于析取和合取，但低于其他运算：

```agda 
infix 3 ¬_
``` 

## 直觉逻辑与经典逻辑

直觉逻辑与经典逻辑的显著区别之一是，直觉主义者关注于某些逻辑学家对无限性本质的假设，坚持真理的构造主义的概念，例如`A ⊎ B`的证明必须确定为`A`或`B`中的哪一个成立。

直觉主义者拒绝 ***排中律(Law of Exclued Middle)*** ，其断言对于所有的`A`，`A ⊎ ¬ A`必定成立 -- 这是因为它没有给出`A`或`¬ B`的证明必须确定为`A`或`B`中的哪一个成立。海廷(Heyting)形式化了希尔伯特(Hilbert)经典逻辑的一个变种，抓住了直觉主义中可证明性的概念。在海廷逻辑中，排中律是不可证的，如果向其中添加了排中律作为公理，此时它会等价希尔伯特逻辑。

科尔莫哥洛夫(Kolmogorov)证明了两种逻辑紧密相关，即一个式子在经典逻辑中可证明，当且仅当它的双重否定式在直觉逻辑中可证。

> 摘自 Philip Wadler < < Propositions as Types > >

## 排中律不可辩驳

排中律定义如下：

```agda 
postulate  
    em : ∀ {A : Set} → A ⊎ ¬ A 
```

虽然排中律在直觉逻辑中是不成立的，但我们可以证明其是 ***不可辩驳的(Irrefutable)*** 的，即其双重否定可证明（从而其否定式无法证明）：

```agda 
em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k (inj₂ (λ x → k (inj₁ x)))
``` 

## 标准库

本章涉及的定义在标准库的对应：

```agda 
-- import Relation.Nullary using (¬_)
-- import Relation.Nullary.Negation using (contraposition)
``` 

## 习题参考

### 练习`<-irreflexive`(推荐)

利用否定证明严格不等性满足非自反性，即`n < n`对任何`n`都不成立。

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

<-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
<-irreflexive zero ()
<-irreflexive (suc n) (s<s n<n) = <-irreflexive n n<n 
```

### 练习`trichotomy`(实践)

请证明严格不等性满足三分律，即对于任何自然数`m`和`n`，以下三条刚好只有一条成立：

- `m < n`
- `m ≡ n`
- `n < m`

```agda 
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (cong; sym)
open import plfa.part1.Isomorphism using (_∘_)


trichotomy : ∀ (m n : ℕ) → 
    (m < n) × ¬ (m ≡ n) × ¬ (n < m) ⊎
    ¬ (m < n) × (m ≡ n) × ¬ (n < m) ⊎ 
    ¬ (m < n) × ¬ (m ≡ n) × (n < m)
trichotomy zero zero = (inj₂ ∘ inj₁) ⟨ <-irreflexive zero , ⟨ refl , <-irreflexive zero ⟩ ⟩
trichotomy zero (suc n) = inj₁ ⟨ z<s , ⟨ peano , (λ()) ⟩ ⟩
trichotomy (suc m) zero = (inj₂ ∘ inj₂) ⟨ (λ()) , ⟨ (λ x → peano (sym x)) , z<s ⟩ ⟩
trichotomy (suc m) (suc n) with trichotomy m n 
...                         | inj₁ x = inj₁ ⟨ (s<s (proj₁ x)) , 
                                        ⟨ (λ{refl → ((proj₁ ∘ proj₂) x) refl }) , 
                                    (λ{(s<s n<m) → ((proj₂ ∘ proj₂) x) n<m}) ⟩ ⟩
...                         | inj₂ (inj₁ x) = (inj₂ ∘ inj₁) ⟨ (λ{(s<s m<n) → (proj₁ x) m<n}) , 
                                        ⟨ (cong suc ((proj₁ ∘ proj₂) x)) , 
                                    (λ{(s<s n<m) → ((proj₂ ∘ proj₂) x) n<m}) ⟩ ⟩
...                         | inj₂ (inj₂ x) = (inj₂ ∘ inj₂) ⟨ (λ{(s<s m<n) → (proj₁ x) m<n}) , 
                                        ⟨ (λ{refl → ((proj₁ ∘ proj₂) x) refl }) , 
                                    s<s (((proj₂ ∘ proj₂) x)) ⟩ ⟩
``` 

## 练习`⊎-dual-×`(推荐)

请证明合取，析取和否定可通过以下版本的德摩根定律(De Morgan's Law)关联在一起。

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

此结果是我们之前证明的定理的简单推论。

```agda 
-- 由于导入的是标准库中的合取和析取，需要重新声明之前的结论
→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ (A → C) × (B → C)
→-distrib-⊎ = 
    record 
        {   to = λ{f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
        ;   from = λ{⟨ g , h ⟩ → λ{(inj₁ x) → g x ; (inj₂ y) → h y}}
        ;   from∘to = λ{f → extensionality λ{(inj₁ x) → refl ; (inj₂ y) → refl}}
        ;   to∘from = λ{⟨ _ , _ ⟩ → refl}
        }

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = →-distrib-⊎ 
``` 

以下命题也成立吗？

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

若成立，请证明；若不成立，你能给出一个比同构更若的关系将两边关联起来吗？

```agda 
-- 只能证明 (¬ A) ⊎ (¬ B) → ¬ (A × B)

×-dual-⊎ : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
×-dual-⊎ = λ{(inj₁ ¬a) → λ{⟨ a , b ⟩ → ¬a a} ; 
              (inj₂ ¬b) → λ{⟨ a , b ⟩ → ¬b b}}
``` 

## 练习`Classical`延伸

考虑以下定律：

- 排中律：对于所有`A`，`A ⊎ ¬ A`
- 双重否定消去律：对于所有的`A`，`¬ ¬ A → A`
- 皮尔士定律：对于所有的`A`和`B`，`((A → B) → A) → A`
- 蕴涵表示为析取：对于所有的`A`和`B`，`(A → B) → ¬ A ⊎ B` 
- 德摩根定律： 对于所有的`A`和`B`，`¬ (¬ A × ¬ B) → A ⊎ B`

请证明其中任意一条定律都蕴涵其他所有定律：

```agda 
-- 我的证明顺序 排中律 ↔ 双重否定消去律 ↔ 皮尔士定义
--            排中律 ↔ 蕴涵表示为析取  
--            排中律 ↔ 德摩根定律
-- 证明方法不唯一

Classical₀₁ : ∀ {A : Set} → A ⊎ ¬ A → (¬ ¬ A → A)
Classical₀₁ a⊎¬a with a⊎¬a 
...                 | inj₁ a = λ x → a 
...                 | inj₂ ¬a = λ x → ⊥-elim (x ¬a)  

Classical₁₀ : (∀ {A : Set} → (¬ ¬ A → A)) → {A : Set} →  A ⊎ ¬ A 
Classical₁₀ ¬¬a→a = ¬¬a→a em-irrefutable  

Classical₁₂ : ∀ {A B : Set} → (¬ ¬ A → A) → (((A → B) → A) → A)
Classical₁₂ ¬¬a→a = λ ′a→b′→a → ¬¬a→a (λ ¬a → ¬a (′a→b′→a (λ a → ⊥-elim (¬a a))))

Classical₂₁ : ∀ {A : Set} → ({B : Set} → (((A → B) → A) → A)) → (¬ ¬ A → A) 
Classical₂₁ ′′a→b′→a′→a  = λ ¬¬a → ′′a→b′→a′→a {⊥}  λ ¬a → ⊥-elim (¬¬a ¬a)

Classical₀₃ : ∀ {A B : Set} → A ⊎ ¬ A → ((A → B) → ¬ A ⊎ B)
Classical₀₃ a⊎¬a with a⊎¬a 
...                 | inj₁ a = λ a→b → inj₂ (a→b a) 
...                 | inj₂ ¬a = λ a→b → inj₁ ¬a

-- 这里临时添加了公设以便使用，这实际上是⊎-comm 的 to 映射
postulate
    ⊎→comm : ∀ {A B : Set} → A ⊎ B → B ⊎ A

Classical₃₀ : ∀ {A : Set} → ({B : Set} → (A → B) → ¬ A ⊎ B) → A ⊎ ¬ A 
Classical₃₀ {A} ′a→b′→¬a⊎b = ⊎→comm {¬ A} {A} (′a→b′→¬a⊎b {A} →id)
    where 
    →id : ∀ {A : Set} → A → A 
    →id = λ x → x 


open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

Classical₀₄ : (∀ {A : Set} → A ⊎ ¬ A) → (∀ {A B : Set} → (¬ (¬ A × ¬ B) → A ⊎ B)) 
Classical₀₄ a⊎¬a {A} {B} ¬′¬a×¬b′ with a⊎¬a {A} | a⊎¬a {B}
...                                 |  inj₁ a   | _      = inj₁ a 
...                                 |  inj₂ ¬a  | inj₁ b = inj₂ b 
...                                 |  inj₂ ¬a  | inj₂ ¬b = ⊥-elim (¬′¬a×¬b′ ⟨ ¬a , ¬b ⟩) 

Classical₄₀ : ∀ {A : Set} → ({B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B) →  A ⊎ ¬ A 
Classical₄₀ ¬′¬a⊎¬b′→a⊎b = ¬′¬a⊎¬b′→a⊎b λ{ ⟨ ¬a , ¬¬a ⟩ → ¬¬a ¬a}
``` 

## 练习`Stable`(延伸)

若双重否定消去对某个式子成立，我们就说它是 ***稳定(Stable)*** 的方式直接声明其成立：

```agda 
Stable : Set → Set 
Stable A = ¬ ¬ A → A 
``` 

请证明任何否定式都是稳定的，并且两个稳定式的合取也是稳定的。

```agda 
¬-Stable : ∀ {A : Set} → Stable (¬ A)
¬-Stable = λ ¬¬¬a → ¬¬¬-elim ¬¬¬a 

⊎-Stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
⊎-Stable ¬¬a→a ¬¬b→b = λ ¬¬a×b → 
        ⟨ (¬¬a→a λ ¬a → ¬¬a×b (λ a×b → ¬a (proj₁ a×b))) ,
         (¬¬b→b λ ¬b → ¬¬a×b (λ a×b → ¬b (proj₂ a×b))) ⟩
``` 
 