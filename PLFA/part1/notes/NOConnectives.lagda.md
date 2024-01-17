# 合取，析取与蕴涵

[TOC]

```txt
本章使用的 Unicode 符号：
    ×  U+00D7  乘法符号 (\x)
    ⊎  U+228E  多重集并集 (\u+)
    ⊤  U+22A4  向下图钉 (\top)
    ⊥  U+22A5  向上图钉 (\bot)
    η  U+03B7  希腊小写字母 ETA (\eta)
    ₁  U+2081  下标 1 (\_1)
    ₂  U+2082  下标 2 (\_2)
    ⇔  U+21D4  左右双箭头 (\<=>)
```

本章介绍基础的逻辑运算符，需要导入的库如下：

```agda 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality)
```

## 柯里-霍华德同构

> 这里引用Philip Wadler的文章 << Propositions as Types >>

柯里-霍华德同构将逻辑与程序语言联系起来：

- ***命题即类型(propositions as types)***
- ***证明即程序(proofs as programs)***

第一点表明任何一个逻辑上的命题都有一个编程语言中的类型与之对应，反之亦然；第二点表明任何一个命题的给定证明，都有一个相应类型的程序与之对应，反之亦然。进一步地对于每个化简证明过程都有一个计算程序的方法与之对应，反之亦然，即

- ***简化证明即计算程序(simplification of proofs as evaluation of programs)***

这三点保证了证明与程序，化简与计算深层次的对应关系，从而形成真正的同构，而非简单的双射关系。

在了解完柯里-霍华德同构后，我们就容易将各种逻辑运算符转化为程序语言中相应的类型：

- 合取(Conjunction) → 积(Product)
- 析取(Disjunction) → 和(Sum)
- 真(True) → 单元类型（Unit Type）
- 假(False) → 空类型(Empty Type)
- 蕴含(Implication) → 函数空间(Function Space) 

## 合取 ⇔ 积

给定两个命题`A`和`B`，其合取`A × B`成立当`A`和`B`都成立。

```agda 
data _×_ (A B : Set) : Set where 
    
    ⟨_,_⟩ : 
        A 
        → B
        --------  
        → A × B 
``` 

`A × B`成立使用`⟨ M , N ⟩`的形式表现，其中`M`是`A`成立的证明，`N`是`B`成立的证明。

反过来，当已知`A × B`成立时，我们可以得出`A`成立以及`B`成立。

```agda 
proj₁ : ∀ {A B : Set} 
    → A × B 
    -------- 
    → A 
proj₁ ⟨ x , y ⟩ = x 

proj₂ : ∀ {A B : Set} 
    → A × B 
    -------- 
    → B 
proj₂ ⟨ x , y ⟩ = y  
``` 

当`⟨_,_⟩`位于等号右侧时，我们称其为构造子；当其出现在等号左侧时，则用作模式匹配，此时称为析构器。

> 也可以称`proj₁`和`proj₂`为析构器，两者作用类似

其他术语将`⟨_,_⟩`称为 ***引入(Introduce)*** 合取,记为`×-I`;将`proj₁`和`proj₂`称为 ***消去(Eliminate)*** 合取，记为`×-E₁`和`×-E₂`。正如名称所述，引入规则描述运算符成立的前提条件；而消去规则则描述了当运算符成立时，可以得出什么结论。

可以看出引入规则和消去规则是两个互逆的过程，因而有：

```agda 
η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w 
η-× ⟨ _ , _ ⟩ = refl 

-- 模式匹配是必要的，否则无法使用析构进行化简
``` 

> 此类命题统一名称为η-Equality

上述合取运算符的定义和析构器`projᵢ`是分离的，使用记录语法可以将其整合到一起：

```agda 
record _×′_ (A B : Set) : Set where 
    constructor ⟨_,_⟩′
    field
        proj₁′ : A 
        proj₂′ : B 

open _×′_
```

当使用记录类型版本的合取构造时，会得到更多信息`⟨ proj₁′ = M ， proj₂′ = N ⟩`，因此在重写`η-x`时我们无需显式给出模式：

```agda 
η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w 
η-×′ _ = refl 
``` 

在编程语言视角下，给定两个类型`A`和`B`，我们将`A × B`称为`A`与`B`的积。如果类型`A`有`m`个成员，`B`有`n`个不同的成员，那么类型`A × B`有`m * n`个不同的成员。

### 性质

类型上的积在同构意义上满足交换律和结合律。

```agda 
×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc = 
    record 
        {   to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
        ;   from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
        ;   from∘to = λ{ ⟨ ⟨ _ , _ ⟩ , _ ⟩ → refl }
        ;   to∘from = λ{ ⟨ _ , ⟨ _ , _ ⟩ ⟩ → refl }
        }

×-comm : ∀ {A B : Set} → A × B ≃ B × A 
×-comm = 
    record 
        {   to = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
        ;   from = λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
        ;   from∘to = λ{ ⟨ _ , _ ⟩ → refl }
        ;   to∘from = λ{ ⟨ _ , _ ⟩ → refl }
        }
``` 

### 优先级

我们设置合取的优先级以便使其与析取之外的运算符结合的都不紧密。

```agda 
infixr 2 _×_
``` 


### 真 ⇔ 单元类型

恒真`⊤`恒成立。

```agda 
data ⊤ : Set where 

    tt : 
        --- 
        ⊤
``` 

恒真有引入规则但没有消去规则，当我们有恒真成立的证明时，我们不能得到任何有意义的结论。

`η-×`的零元形式为`η-⊤`，断言了任何的`⊤`类型的值都等于`tt`。

```agda 
η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl  
``` 

恒真定义也可以使用记录语法写。

```agda 
record ⊤′ : Set where 
    constructor tt′
``` 

相应的，`η-⊤`重写也无需显式给出模式：

```agda 
η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w 
η-⊤′ _ = refl 
``` 

恒真`⊤`对应了单元类型，单元类型只有一个成员`tt`。

### 性质

单位类型在同构意义下是积的幺元，我们将证明拆分为左右幺元分别证明。

```agda 
⊤′-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A 
⊤′-identityˡ = 
    record
        {   to = λ{⟨ tt , x ⟩ → x}
        ;   from = λ{x → ⟨ tt , x ⟩}
        ;   from∘to = λ{ ⟨ tt , _ ⟩ → refl}
        ;   to∘from = λ{_ → refl}
        }

⊤′-identityʳ : ∀ {A : Set} → A × ⊤ ≃ A 
⊤′-identityʳ = 
    record
        {   to = λ{⟨ x , tt ⟩ → x}
        ;   from = λ{x → ⟨ x , tt ⟩}
        ;   from∘to = λ{ ⟨ _ , tt ⟩ → refl }
        ;   to∘from = λ{_ → refl}
        }
``` 

## 析取 ⇔ 和

给定两个命题`A`和`B`，析取`A ⊎ B`当`A`或者`B`成立时成立。

```agda 
data _⊎_ (A B : Set) : Set where 

    inj₁ : 
        A 
        ------- 
        → A ⊎ B 

    inj₂ : 
        B 
        ------- 
        → A ⊎ B 
``` 

`A ⊎ B`成立有两种情况：`inj₁ M`或者`inj₂ N`，其中`M`是`A`成立的证据，`N`是`B`成立的证据。

反过来，当我们已知`A ⊎ B`成立时，可通过`A → C`和`B → C`得到`C`成立：

```agda 
case-⊎ : ∀ {A B C : Set} 
    → (A → C)
    → (B → C)
    → A ⊎ B
    --------- 
    → C
case-⊎ f₁ f₂ (inj₁ x) = f₁ x 
case-⊎ f₁ f₂ (inj₂ y) = f₂ y 
``` 

与合取类似，当`inj₁`和`inj₂`在等式左侧时，我们称其为构造子；而当其出现在右侧时，我们称其为析构器（也可以称`case-⊎`为析构器）。其他属于将`inj₁`和`inj₂`称为引入析取，记为`⊎-I₁`和`⊎-I₂`；将`case-⊎`称为消去析取，记为`⊎-E`。

相应的η-Equality命题为：

```agda 
η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w 
η-⊎ (inj₁ _) = refl 
η-⊎ (inj₂ _) = refl 
``` 

更普遍地，我们可以对析构使用一个任意函数：

```agda 
uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) → 
    case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w 
uniq-⊎ h (inj₁ _) = refl 
uniq-⊎ h (inj₂ _) = refl
``` 

> 类似也可以使用记录语法重写，此处不再赘述

在编程语言视角下，析取类型对应了和类型，对于给定的两个类型`A`和`B`,我们将`A ⊎ B`称为`A`和`B`的和。如果类型`A`有`m`个不同的成员，类型`B`有`n`个不同的成员，那么类型`A ⊎ B`有`m + n`个不同的成员。

> 注意这里的和对应集合论中的不交并(Disjoint Union)

### 性质

类型上的和在同构意义下也满足交换律和结合律（留作习题）。

### 优先级

析取的优先级应当比任意定义的运算符都结合得不紧密：

```agda 
infixr 1 _⊎_
``` 
## 假 ⇔ 空类型

恒假`⊥`从来不成立。

```agda 
data ⊥ : Set where 
    -- 什么都没有 
``` 

上述代码表明，没有任何可以证明`⊥`成立的证据。

恒假`⊥`与恒真`⊤`时对偶的，因此它只有引入规则但没有消去规则。我们没有任何理由让恒假成立；但如果假定恒假成立，我们可以得到任何结论。

```agda 
⊥-elim : ∀ {A : Set}
    → ⊥ 
    ----  
    → A 
⊥-elim ()
``` 

在上述代码中，我们首次使用了 ***荒谬模式(Absurd Pattern)*** `()`。荒谬模式用来表示没有任何模式能够匹配此处。

`uniq-⊎`的零元形式为`uniq-⊥`,断言了`⊥-elim`和任何`⊥`的函数是等价的。

```agda 
uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w 
uniq-⊥ _ ()
``` 

恒假`⊥`对应了空类型，空类型没有任何成员。

### 性质

空在同构意义下是和的幺元（留作习题）。


## 蕴涵 ⇔ 函数

给定两个命题`A`和`B`，其蕴涵`A → B`在当`A`成立使得`B`成立时成立。其对应的类型就是函数类型，因此我们无需再创建新的类型表示蕴涵。

`A → B`成立的证据由`λ (x : A) → N`给出；给定一个`A → B`成立的证明`L`，以及一个`A`成立的证明，那么`L M`是`B`成立的证明，或者说`L`将`A`的证明转化为了`B`的证明。

```agda 
→-elim : ∀ {A B : Set}
    → (A → B) 
    → A 
    --------- 
    → B 
→-elim L M = L M 
``` 

当我们定义一个函数时，称之为引入一个函数；反过来当我们应用函数时，称之为消去一个函数。

蕴涵对应的η-Equality版本为`η-→`:

```agda 
η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f 
η-→ _ = refl
``` 

## 性质

常规函数柯里化前后是同构的。

```agda 
currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    {   to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ;   from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ;   from∘to =  λ{ f → refl }
    ;   to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }
``` 

注意由于`to∘from`的证明目标是两个函数相等，因此需要使用外延性公设。

函数类型对和类型和积类型都满足分配律。

```agda 
→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ (A → C) × (B → C)
→-distrib-⊎ = 
    record 
        {   to = λ{f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
        ;   from = λ{⟨ g , h ⟩ → λ{(inj₁ x) → g x ; (inj₂ y) → h y}}
        ;   from∘to = λ{f → extensionality λ{(inj₁ x) → refl ; (inj₂ y) → refl}}
        ;   to∘from = λ{⟨ _ , _ ⟩ → refl}
        }


→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× = 
    record
        {   to = λ{f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩}
        ;   from = λ{ ⟨ g , h ⟩ → λ{x → ⟨ g x , h x ⟩ }}
        ;   from∘to = λ{f → extensionality λ{x → η-× (f x) } }
        ;   to∘from = λ{ ⟨ _ , _ ⟩ → refl}
        }
``` 

同样地，两个分配律的左逆证明目标是两个函数相等，从而需要外延性公设。

## 分配律

在同构意义下，积对和满足分配律。

```agda 
×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ = 
    record
        {   to = λ{ ⟨ inj₁ x , z ⟩ → inj₁ ⟨ x , z ⟩;
                    ⟨ inj₂ y , z ⟩ → inj₂ ⟨ y , z ⟩ }
        ;   from = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x  , z ⟩;
                      (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩ }
        ;   from∘to = λ{ ⟨ inj₁ _ , _ ⟩ → refl ;
                         ⟨ inj₂ _ , _ ⟩ → refl }
        ;   to∘from = λ{ (inj₁ ⟨ _ , _ ⟩) → refl ; 
                         (inj₂ ⟨ _ , _ ⟩) → refl }
        }
```

和对积不满足同构意义上分配律，但满足嵌入关系。

```agda 
⊎-distrib-x : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-x = 
    record
        {   to = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩;
                    (inj₂ z) → ⟨ inj₂ z , inj₂ z ⟩}
        ;   from = λ{ ⟨ inj₁ x , inj₁ y ⟩ → inj₁ ⟨ x , y ⟩;
                      ⟨ _ , inj₂ z ⟩ → inj₂ z;
                      ⟨ inj₂ z , _ ⟩ → inj₂ z}
        ;   from∘to = λ{ (inj₁ ⟨ _ , _ ⟩) → refl;
                         (inj₂ _) → refl}
        }
``` 

## 标准库

本章涉及的定义在标准库的对应：

```agda 
-- import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
-- import Data.Unit using (⊤; tt)
-- import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
-- import Data.Empty using (⊥; ⊥-elim)
-- import Function.Equivalence using (_⇔_)
``` 

## 习题参考

### 练习`⇔≃×`(推荐)

证明之前定义的`A ⇔ B`与`(A → B) x (B → A)`同构。

```agda 
record _⇔_ (A B : Set) : Set where 
    field
        to : A → B 
        from : B → A 
open _⇔_

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A) 
⇔≃× = 
    record 
        {   to = λ{A⇔B → ⟨ to A⇔B , from A⇔B ⟩}
        ;   from = λ{ ⟨ A→B , B→A ⟩ → record { to = A→B ; from = B→A}}
        ;   from∘to = λ{_ → refl }
        ;   to∘from = λ{⟨ _ , _ ⟩ → refl }
        }
```

### 练习`⊎-comm`(推荐)

证明和类型在同构意义下满足交换律。

```agda 
⊎-comm : ∀ {A B : Set} 
    → A ⊎ B ≃ B ⊎ A
⊎-comm = 
    record 
        {   to = λ{(inj₁ x) → inj₂ x ; (inj₂ y) → inj₁ y}
        ;   from = λ{(inj₁ y) → inj₂ y ; (inj₂ x) → inj₁ x}
        ;   from∘to = λ{(inj₁ _) → refl ; (inj₂ _) → refl }
        ;   to∘from = λ{(inj₂ _) → refl ; (inj₁ _) → refl }
        }
``` 

### 练习`⊎-assoc`(实践)

证明和类型在同构以以下满足结合律.

```agda 
⊎-assoc : ∀ {A B C : Set}
    → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc = 
    record 
        {   to = λ{ (inj₁ (inj₁ a)) → inj₁ a ; 
                    (inj₁ (inj₂ b)) → inj₂ (inj₁ b);
                    (inj₂ c) → inj₂ (inj₂ c)}
        ;   from = λ{ (inj₁ a) → inj₁ (inj₁ a); 
                      (inj₂ (inj₁ b)) → inj₁ (inj₂ b);
                      (inj₂ (inj₂ c)) → inj₂ c}
        ;   from∘to = λ{ (inj₁ (inj₁ _)) → refl; 
                         (inj₁ (inj₂ _)) → refl; 
                         (inj₂ _) → refl}
        ;   to∘from = λ{ (inj₁ _) → refl;
                         (inj₂ (inj₁ _)) → refl; 
                         (inj₂ (inj₂ _)) → refl}
        }
``` 

### 练习`⊥-identityˡ`(推荐)

证明空在同构意义下是和的左幺元。

```agda 
⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A 
⊥-identityˡ = 
    record 
        {   to = λ{(inj₂ a) → a}
        ;   from = λ{a → inj₂ a}
        ;   from∘to = λ{(inj₂ _) → refl}
        ;   to∘from = λ{_ → refl}
        }
``` 

### 练习`⊥-identityʳ`(推荐)

证明空在同构意义下是和的右幺元。

```agda 
⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A 
⊥-identityʳ = 
    record 
        {   to = λ{(inj₁ a) →  a}
        ;   from = λ{a → inj₁ a}
        ;   from∘to = λ{(inj₁ _) → refl}
        ;   to∘from = λ{_ → refl}
        } 
``` 

### 练习`⊎-weak-×`(推荐)

证明如下性质成立：

```agda
⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
```

这被称为***弱分配律(Weak Distributive Law)***。

```agda 
⊎-weak-× ⟨ (inj₁ a) , c ⟩ = inj₁ a 
⊎-weak-× ⟨ (inj₂ b) , c ⟩ = inj₂ ⟨ b , c ⟩ 
``` 

### 练习`⊎×-implies-×⊎`(实践)

证明合取的析取蕴涵了析取的合取：

```agda 
⊎-implies-×⊎ : ∀ {A B C D  : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D) 
``` 

反命题成立吗？如果成立，给出证明；如果不成立，给出反例。

```agda 
⊎-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩ 
⊎-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩

-- 反命题不成立，在证明反命题时，只有当模式为
-- ⟨ inj₁ _ , inj₁ _ ⟩ 和 ⟨ inj₂ _ , inj₂ _ ⟩
-- 才能证明， 另外两种模式无法给出相应的证明
-- 令 A,D = ⊥ , B,C = ⊤
-- 左侧同构为 ⊥ , 右侧同构为 ⊤ , 恒真蕴涵恒假这显然是不对的（恒假没有成员，根本无法构造）
```


