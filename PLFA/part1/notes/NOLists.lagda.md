# 列表与高阶函数

[TOC]

```txt
本章使用的 Unicode 符号：
    ∷  U+2237  比例  (\::)
    ⊗  U+2297  带圈的乘号  (\otimes, \ox)
    ∈  U+2208  元素属于  (\in)
    ∉  U+2209  元素不属于  (\inn, \notin)
``` 

本章通过列表类型为例，对前面的学习进行巩固，同时讨论 ***多态类型(Polymorphic Types)*** 和 ***高阶函数(Higher-order Functions)*** 。

先导入必要的库：

```agda 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_)
``` 


## 列表

```agda 
data List (A : Set) : Set where 
    [] : List A 
    _∷_ : A → List A → List A 

infixr 5 _∷_ 
``` 

列表类型由两个构造子组成，`[]`表示空列表，而`_∷_`接受一个类型为`A`的值和一个类型为`List A`的列表，表示将一个元素拼接到一个列表的头部以生成新的列表。

一个构造列表的实例如下：

```agda 
_ : List ℕ 
_ = 0 ∷ 1 ∷ 2 ∷ [] 
-- 0 ∷ (1 ∷ (2 ∷ []))
``` 

在列表中，我们约定`_∷_`首个参数为其构造得到列表的 ***头(Head)***，第二个参数为列表的 ***尾(Tail)***，例如上面的`0`是整个列表的头，其余部分是整个列表的尾。 

上面的列表定义使用了参数化类型，这可以等价为索引类型：

```agda 
data List′ : Set → Set₁ where
  []′  : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A
``` 

> 注意：每做一次全称量化后就需要提升一次宇宙层级，plfa原文此处似乎有书写失误

使用索引类型改写前面的实例：

```agda 
_ : List′ ℕ
_ = 0 ∷′ (1 ∷′ (2 ∷′ []′))
``` 

### 编译指令

```agda 
{-# BUILTIN LIST List #-}
``` 

### 列表语法

```agda 
pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []
``` 

## 附加

我们对于列表的第一个函数写作`_++_`，读作 ***附加(Append)***:

```agda 
infixr 5 _++_ 
_++_ : ∀ {A : Set} → List A → List A → List A  
[] ++ ys = ys 
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
``` 

这里`A`类型是附加的隐式参数，返回类型根据这个参数发生变化，这使得函数变为一个 ***多态(Polymorphic)*** 函数。

下面是一个实例：

```agda 
_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ = 
  begin
    0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
  ≡⟨⟩
    0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ∎
``` 

附加两个列表需要对于第一个列表元素个数线性的时间。

### 性质

一个重要的性质是附加满足结合律。

```agda 
++-assoc : ∀ {A : Set} (xs ys zs : List A)
    → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs) 
++-assoc [] ys zs = refl 
++-assoc (x ∷ xs) ys zs rewrite ++-assoc xs ys zs = refl 
``` 

另外我们还可以证明`[]`是`_++_`运算的幺元。

```agda 
++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs 
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs 
++-identityʳ [] = refl 
++-identityʳ (x ∷ xs) rewrite ++-identityʳ xs = refl 
``` 

由以上性质可知`_++_`和`[]`在列表上构成了 ***幺半群(Monoid)***。 

## 长度

```agda 
length : ∀ {A : Set} → List A → ℕ
length [] = zero 
length (x ∷ xs) = suc (length xs)
``` 

类似地，长度函数也使用了隐式参数`A`（但不是多态函数）。

下面是一个实例：

```agda 
_ : length [ 0 , 1 , 2 ] ≡ 3 
_ = 
    begin 
        length (0 ∷ 1 ∷ 2 ∷ [])
    ≡⟨⟩ 
        suc (length (1 ∷ 2 ∷ []))
    ≡⟨⟩
        suc (suc (length (2 ∷ [])))
    ≡⟨⟩ 
        suc (suc (suc (length {ℕ} [])))
    ≡⟨⟩ 
        suc (suc (suc zero))
    ∎
``` 

计算列表长度需要关于列表元素个数的线性时间。

### 性质

长度与列表拼接满足线性性质，即两个附加的列表长度等于它们各自长度的和。

```agda 
length-++ : ∀ {A : Set} (xs ys : List A)
    → length (xs ++ ys) ≡ length xs + length ys 
length-++ [] ys = refl 
length-++ (x ∷ xs) ys rewrite length-++ xs ys = refl 
``` 

## 反转

反转可以简单地使用附加来构造：

```agda 
reverse : ∀ {A : Set} → List A → List A 
reverse [] = [] 
reverse (x ∷ xs) = reverse xs ++ [ x ] 
``` 

下面是一个实例：

```agda 
_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    reverse (1 ∷ 2 ∷ []) ++ [ 0 ]
  ≡⟨⟩
    (reverse (2 ∷ []) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    ((reverse [] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ 2 ∷ []) ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ [] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ ([] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ (1 ∷ [] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ ([] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ≡⟨⟩
    [ 2 , 1 , 0 ]
  ∎
```

由于附加是关于第一个列表的线性时间，而反转一个长度为`n`的列表，需要不断将长度为`1`,`2`, ... , `n - 1`的列表附加起来，因此这样的反转需要列表长度二次的时间。

虽然上面定义符合直觉，但效率却比较低下，我们可以实现一个线性实践的反转，关键就在于“顺从`_∷_`的右结合”。

首先定义一个辅助函数,它是反转函数的推广：

```agda 
shunt : ∀ {A : Set} → List A → List A → List A 
shunt [] ys = ys 
shunt (x ∷ xs) ys = shunt xs (x ∷ ys) 
``` 

转移(Shunt)与反转的关系如下：

```agda 
shunt-reverse : ∀ {A : Set} (xs ys : List A) 
    → shunt xs ys ≡ reverse xs ++ ys 
shunt-reverse [] ys = refl 
shunt-reverse (x ∷ xs) ys rewrite ++-assoc (reverse xs) [ x ] ys 
                            | shunt-reverse xs (x ∷ ys) = refl 
``` 

从上面的关系可以看出，当`ys`为空时，恰好就是反转函数：

```agda 
reverse′ : ∀ {A : Set} → List A → List A 
reverse′ xs = shunt xs [] 
``` 

我们也可以直接证明它与`reverse`是等价的：

```agda 
reverses : ∀ {A : Set} (xs : List A)
    → reverse′ xs ≡ reverse xs 
reverses xs rewrite shunt-reverse xs [] 
                | ++-identityʳ (reverse xs) = refl
``` 

使用`reverse′`重写上面的实例：

```agda 
_ : reverse′ [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse′ (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    shunt (0 ∷ 1 ∷ 2 ∷ []) []
  ≡⟨⟩
    shunt (1 ∷ 2 ∷ []) (0 ∷ [])
  ≡⟨⟩
    shunt (2 ∷ []) (1 ∷ 0 ∷ [])
  ≡⟨⟩
    shunt [] (2 ∷ 1 ∷ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ∎
```

## 映射

映射将一个函数应用于列表中的所有元素，生成一个对应的列表。

```agda 
map : ∀ {A B : Set} → (A → B) → List A → List B 
map f [] = [] 
map f (x ∷ xs) = f x ∷ map f xs 
``` 

实际上，映射是一个高阶函数的例子。根据柯里化，`map`函数接受一个函数作为参数，并返回一个函数作为结果。

例如：

```agda 
sucs : List ℕ → List ℕ 
sucs = map suc 

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ = refl
``` 

`sucs`作为`map`的高阶函数，对列表中的所有元素增加一。

更一般地，对于有n个类型参数化的类型，常常会有一个对于n个函数参数化的映射。

## 折叠

折叠取一个运算符和一个值，并使用运算符将列表中的元素逐个应用最终合并为一个值；折叠提供一个默认值，以供空列表的情况返回。

```agda 
foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B 
foldr _⊗_ e [] = e 
foldr _⊗_ e (x ∷ xs) = x ⊗ foldr _⊗_ e xs 
``` 

下面是一个实例：

```agda 
_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎
``` 

折叠需要关于列表长度的线性时间。

类似地，折叠也可以用来生成高阶函数。

```agda 
sum : List ℕ → ℕ 
sum = foldr _+_ 0 

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    sum [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    10
  ∎
``` 

更一般地，对于一个有n个构造子的数据类型，会有对应的取n个参数的折叠（将返回类型视为`List _ → List _`）。

## 幺半群

一般地，我们会对折叠函数使用一个满足结合律的运算符以及该运算符的幺元，这个运算符和幺元形成了一个幺半群。

我们使用记录语法定义幺半群：

```agda 
record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where 
    field 
        assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
        identityˡ : ∀ (x : A) → e ⊗ x ≡ x 
        identityʳ : ∀ (x : A) → x ⊗ e ≡ x  

open IsMonoid
``` 

有很多幺半群的例子，如加法和零，乘法和一，以及前面提到的附加和空列表。

如果运算符`_⊗_`和幺元`e`构成一个幺半群，那么可以用相同的运算符和一个任意的值来表示折叠。

```agda 
foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e → 
    ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y rewrite identityˡ ⊗-monoid y = refl 
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y rewrite foldr-monoid _⊗_ e ⊗-monoid xs y 
                                        | assoc ⊗-monoid x (foldr _⊗_ e xs) y = refl 
```

## 全部

有两个重要的关于列表的谓词`All`和`Any`。

谓词`All P`表示列表元素对P都成立，即：

```agda 
data All {A : Set} (P : A → Set) : List A → Set where 
    [] : All P [] 
    _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs) 
``` 

两个构造子与列表对应，第一个`[]`表示`P`对空列表的任何元素成立；第二个`_∷_`表示如果`P`对列表的头元素和尾部的所有元素成立，则`P`对这个列表的任何元素成立。

例如，`All (_≤ 2)`对含有的元素都小于2的列表成立，如下：

```agda 
_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []
``` 

当一个谓词对列表的全部元素都成立，则这个谓词对这两个列表的全部元素分别成立，反之亦然，可以使用等价符号表示这个命题。

```agda 
All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) → 
    All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩
``` 

最后，正如上一章提到的，我们可以用布尔类型版本表达`All`，同时也可以使用可判定类型兼取其优。

布尔计算版本的`All`如下，我们使用高阶函数的复合更简洁地表达这个函数：

```agda 
all : ∀ {A : Set} → (A → Bool) → List A → Bool 
all p = foldr _∧_ true ∘ map p 
-- all p xs = foldr _∧_ true (map p xs)
```

可判定类型版本的`All`如下：

```agda 
Decidable : ∀ {A : Set} → (A → Set) → Set 
Decidable {A} P = ∀ (x : A) → Dec (P x)

All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P) 
All? P [] = yes []  
All? P? (x ∷ xs) with P? x | All? P? xs 
...                 | yes Px | yes Pxs = yes (Px ∷ Pxs)
...                 | no ¬Px | _ = no (λ{ (Px ∷ Pxs) → ¬Px Px}) 
...                 | _      | no ¬Pxs = no λ{ (Px ∷ Pxs) → ¬Pxs Pxs} 
``` 

## 任意

谓词`Any P`表示列表里的一些元素满足`P`：

```agda 
data Any {A : Set} (P : A → Set) : List A → Set where 
    here : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs) 
    there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)
```

任意类型也有两个构造子，它们表明，对于一个列表满足`Any P`，要么列表头部元素满足`P`，要么尾部存在一些元素满足`P`。

例如，元素与列表的存在关系就可以表示为任意类型：

```agda 
infix 4 _∈_ _∉_ 

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set 
x ∈ xs = Any (x ≡_) xs 

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set 
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl 

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))

not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (here ())
not-in (there (here ()))
not-in (there (there (here ())))
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))
``` 

## 标准库

```agda 
-- import Data.List using (List; _++_; length; reverse; map; foldr; downFrom)
-- import Data.List.Relation.Unary.All using (All; []; _∷_)
-- import Data.List.Relation.Unary.Any using (Any; here; there)
-- import Data.List.Membership.Propositional using (_∈_)
-- import Data.List.Properties
--   using (reverse-++-commute; map-compose; map-++-commute; foldr-++)
--   renaming (mapIsFold to map-is-foldr)
-- import Algebra.Structures using (IsMonoid)
-- import Relation.Unary using (Decidable)
-- import Relation.Binary using (Decidable)
``` 

> 注意： 标准库中与plfa中的定义给出有些不同，其中`IsMonoid`可以针对特定的等价关系参数化；`Relation.Unary`和`Relation.Binary`分别定义了单元关系（即谓词版本）的可判定类型和二元关系的可判定类型（如`_≤_`）

## 习题参考












 