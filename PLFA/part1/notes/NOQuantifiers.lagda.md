# 全程量词与存在量词

[TOC]

```txt
本章使用的 Unicode 符号： 
    Π  U+03A0  大写希腊字母 PI (\Pi)
    Σ  U+03A3  大写希腊字母 SIGMA (\Sigma)
    ∃  U+2203  存在 (\ex, \exists)
``` 

本章介绍 ***全称量化(Universal Quantification)*** 和 ***存在量化(Existential Quantification)*** 。

需要导入的库如下：

```agda 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality)
open import Function using (_∘_)
``` 

## 全称量化

我们使用依赖函数类型形式化全称量化。给定一个`A`类型的变量`x`和一个带有`x`自由变量的命题`B x`，全称量化的命题`∀ (x : A) → B x`当对于所有类型为`A`的项`M`，命题`B M`成立时成立。

如果`A`是一个有限的数据类型，有值`x₁, ... , xₙ`，且每个类型`B x₁ , ... , B xₙ`分别有`m₁ , ... , mₙ`个不同的成员，那么`∀ (x : A) → B x`有`m₁ * ... * mₙ`个成员。

基于此，依赖函数类型也被称为 ***依赖积(Dependent Product)***，记为`Π[x ∈ A] (B x)`。


## 存在量化

定义如下归纳类型来形式化存在量词：

```agda 
data Σ (A : Set) (B : A → Set) : Set where 
    ⟨_,_⟩ : (x : A) → B x → Σ A B 
``` 

也可以定义记录类型版本：

```agda 
record Σ′ (A : Set) (B : A → Set) : Set where 
    field 
        proj₁′ : A 
        proj₂′ : B proj₁′
``` 

为了简便，我们定义一个语法：

```agda 
Σ-syntax = Σ 
infix 2 Σ-syntax 
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B 
``` 

给定一个`A`类型的变量`x`和一个带有`x`自由变量的命题`B x`，存在量化的命题`Σ[ x ∈ A ] B x`当对于一些类型为`A`的项`M`，命题`B M`成立时成立。

如果`A`是一个有限的数据类型，有值`x₁, ... , xₙ`，如果每个类型`B x₁, ... , B xₙ`有`m₁, ... ,mₙ`个不同成员，那么`Σ[ x ∈ A ] B x`有`m₁ + ... + mₙ`个成员。

基于此，存在量化也被称为 ***依赖和(Dependent Sum)***。

> 积是存在量词的一种特殊形式，其第二个分量不取决于第一个分量中的变量，因此存在量化有时有被称为依赖积，但这与全称量化的依赖积发生了重复，因此应当避免使用依赖积这个名称

定义如下存在量词`∃`:

```agda 
∃ : ∀ {A : Set} (B : A → Set) → Set 
∃ {A} B = Σ A B  

∃-syntax = ∃ 
syntax ∃-syntax (λ x → B) = ∃[ x ] B 
``` 

推广柯里化的结论，可以得到有关存在量化和全称量化之间的同构关系：

```agda 
∀∃-curring : ∀ {A : Set} {B : A → Set} {C : Set} 
    → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-curring = 
    record
        {   to = λ f → λ { ⟨ x , y ⟩ → f x y}
        ;   from = λ g → λ{x → λ{y → g ⟨ x , y ⟩ } }
        ;   from∘to = λ f → refl 
        ;   to∘from = λ g → extensionality λ{ ⟨ x , y ⟩ → refl }
        }
``` 

## 存在量化，全称量化和否定

注意到存在量化是析取的推广，而全称量化是合取的推广，存在量化的否定与否定的全称量化可以看作前面提到的德摩根定律`¬ (A ⊎ B) ≃ (¬ A) × (¬ B)`的一个推广。

```agda 
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set} 
    → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x 
¬∃≃∀¬ = 
    record 
        {   to = λ ¬∃xBx → λ x → λ Bx → ¬∃xBx ⟨ x , Bx ⟩
        ;   from = λ ∀x¬Bx → λ {⟨ x , Bx ⟩ → ∀x¬Bx x Bx}
        ;   from∘to = λ ¬∃xBx → extensionality (λ {⟨ _ , _ ⟩ → refl})
        ;   to∘from = λ ∀x¬Bx → refl 
        }
``` 

## 标准库

```agda 
-- import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
``` 

## 习题参考

### 练习`∀-distrib-×`(推荐)

证明全称量词对于合取满足分配律：

```agda 
∀-distrib-× : ∀ {A : Set} {B C : A → Set} → 
    (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
``` 

将结果与Connectives章节中的`→-distrib-×`结果对比。

```agda 
∀-distrib-× = 
    record 
        {   to = λ f → ⟨ (λ x₁ → proj₁ (f x₁)) , (λ x₁ → proj₂ (f x₁)) ⟩
        ;   from = λ {⟨ f₁ , f₂ ⟩ → λ x → ⟨ f₁ x , f₂ x ⟩}
        ;   from∘to = λ f → refl
        ;   to∘from = λ {⟨ f₁ , f₂ ⟩ → refl }
        }
``` 

### 练习`⊎∀-implies-∀⊎`(实践)

证明全称命题的析取蕴涵了析取的全称命题：

```agda 
⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} → 
    (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x 
``` 

逆命题成立吗？如果成立给出证明，如果不成立解释原因。

```agda 
⊎∀-implies-∀⊎ (inj₁ f₁) = λ x → inj₁ (f₁ x) 
⊎∀-implies-∀⊎ (inj₂ f₂) = λ x → inj₂ (f₂ x)  

-- 逆命题不成立，在尝试证明时，必须确定`B x ⊎ C x`中的x，但待证明部分中却保留全称量词，我们无法通过一个常值`B x`或`C x`证明带有全称量词的命题
```

### 练习`∀-×`(实践)

参考下面的类型：

```agda 
data Tri : Set where 
    aa : Tri 
    bb : Tri 
    cc : Tri 
``` 

令`B`作为由`Tri`索引的一个类型，也就是说`B : Tri → Set`。证明`∀ (x : Tri) → B x`和`B aa × B bb × B cc`是同构的。

```agda 
open import plfa.part1.Isomorphism using (∀-extensionality)
∀-× : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc  
∀-× = 
    record 
        {   to = λ f → ⟨ (f aa) , ⟨ (f bb) , (f cc) ⟩ ⟩
        ;   from = λ{ ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ → λ { aa → Baa ; bb → Bbb ; cc → Bcc } }  
        ;   from∘to = λ f → ∀-extensionality (λ {aa → refl ; bb → refl ; cc → refl})
        ;   to∘from = λ{ ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ → refl }
        }
``` 

### 练习`∃-distrib-⊎`(推荐)

证明存在量词对于析取满足分配律：

```agda 
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} → 
    ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
```

```agda 
∃-distrib-⊎ = 
    record 
        {   to = λ { ⟨ x , inj₁ Bx ⟩ → inj₁ ⟨ x , Bx ⟩;
                     ⟨ x , inj₂ Cx ⟩ → inj₂ ⟨ x , Cx ⟩ } 
        ;   from = λ{ (inj₁ ⟨ x , Bx ⟩) → ⟨ x , inj₁ Bx ⟩ ;
                      (inj₂ ⟨ x , Cx ⟩) → ⟨ x , (inj₂ Cx) ⟩ }
        ;   from∘to = λ { ⟨ x , inj₁ Bx ⟩ → refl ;
                          ⟨ x , inj₂ Cx ⟩ → refl }
        ;   to∘from =  λ{ (inj₁ ⟨ x , Bx ⟩) → refl ;
                      (inj₂ ⟨ x , Cx ⟩) → refl }
        }
``` 

### 练习`∃×-implies-×∃`(实践)

证明合取的存在命题蕴涵了存在命题的合取：

```agda 
∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} → 
    ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
``` 

逆命题成立吗？如果成立给出证明，否则给出解释。

```agda 
∃×-implies-×∃ ⟨ x , Bx×Cx ⟩ = ⟨ ⟨ x , proj₁ Bx×Cx ⟩ , ⟨ x , proj₂ Bx×Cx ⟩ ⟩ 

-- 逆命题不成立，参数模式匹配时合取的两个存在命题中的x可能为不同的x
``` 

### 练习`∃-⊎`(实践)

沿用练习`∀-×`中的`Tri`和`B`。证明`∃[ x ] B x`与`B aa ⊎ B bb ⊎ B cc`是同构的。

```agda 
∃-⊎ : ∀ {B : Tri → Set} → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc 
∃-⊎ = 
    record
        {   to = λ{ ⟨ aa , Baa ⟩ → inj₁ Baa ;
                    ⟨ bb , Bbb ⟩ → (inj₂ ∘ inj₁) Bbb ; 
                    ⟨ cc , Bcc ⟩ → (inj₂ ∘ inj₂) Bcc } 
        ;   from =  λ { (inj₁ Baa) → ⟨ aa , Baa ⟩ ; 
                        (inj₂ (inj₁ Bbb)) → ⟨ bb , Bbb ⟩ ;
                        (inj₂ (inj₂ Bcc)) → ⟨ cc , Bcc ⟩ }
        ;   from∘to = λ{ ⟨ aa , Baa ⟩ → refl ;
                         ⟨ bb , Bbb ⟩ → refl ; 
                         ⟨ cc , Bcc ⟩ → refl } 
        ;   to∘from = λ{ (inj₁ Baa) → refl ; 
                         (inj₂ (inj₁ Bbb)) → refl ;
                         (inj₂ (inj₂ Bcc)) → refl }
        }
``` 

### 练习`∃-even-odd`(实践)

略

### 练习`∃-+-≤`(实践)

略

### 练习`∃¬-implies-¬∀`(推荐)

证明否定的存在量化蕴涵了全称量化的否定：

```agda 
∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set} 
    → ∃[ x ] (¬ B x) 
    -----------------
    → ¬ (∀ x → B x)
``` 

逆命题成立吗？如果成立给出证明，如果不成立解释原因。

```agda 
∃¬-implies-¬∀ ⟨ x , ¬Bx ⟩ = λ ∀xBx → ¬Bx (∀xBx x) 
 
-- 逆命题不成立,甚至无法给出x 
```






