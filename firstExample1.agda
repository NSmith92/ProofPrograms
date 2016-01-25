module firstExample1 where

{-Natural Numbers Formation and Introduction-}
data ℕ : Set where
  zero : ℕ 
  suc  : ℕ → ℕ 

{-Natural Numbers Elimination and Equality-}

ℕElim : {C : ℕ → Set}
         → (c : ℕ) 
         → (d : C zero)
         → (e : (a : ℕ) → (b : C a) → C (suc a))
         → C c 
ℕElim zero d e = d
ℕElim (suc y) d e = e y (ℕElim y d e)

{-# BUILTIN NATURAL  ℕ    #-}
{-# BUILTIN ZERO     zero #-}
{-# BUILTIN SUC      suc  #-}

data ⊤ : Set where
  triv : ⊤ 

{-No elements of falsity-}

data ⊥ : Set where
   

_==_ : ℕ → ℕ → Set 
0     == 0     = ⊤
0     == suc m = ⊥  
suc n == 0     = ⊥ 
suc n == suc m = n == m
 
{-Addition takes in a Nat, and another Nat, and returns a Nat-}
_+_ : ℕ → ℕ → ℕ 
n + 0       = n
n + (suc m) = suc (n + m)


{-# BUILTIN NATPLUS  _+_ #-}


infixr 3 _+_
infix  2 _==_

{- 
0 + 3 + 5
could mean
0 + (3 + 5)
or
(0 + 3) + 5

infixr says it should be read as
0 + (3 + 5)

and 3 is the priority

if * has priority 4 and + has 3
then 2 * 3 + 5 is parsed as
(2 * 3) + 5 and not
2 * (3 + 5)

-}

{-Reflexivity-}
refl : (n : ℕ) → n == n
refl 0       = triv
refl (suc n) = refl n

{-
refl 3  (which is of type 3 == 3
reduces 

refl 3 = refl 2 = refl 1 = refl 0 = triv

Actually refl n reduces for each concrete n to triv
-}

assoc+ : (n m k : ℕ) → n + (m + k ) == (n + m) + k
assoc+ n m 0       = refl (n + m)
assoc+ n m (suc k) = assoc+ n m k

{- assume goal expression of the form 
   g n == g n
   easy to see :  use refl
   but if it is evaluated it might becone

   ((h n) + (k n) ) * (l n )

  or something huge
   difficult to see that it's just refl

  there is no good theory of how much to reduce the right hand side
-}

{-p(_,_) : a → b → (a,b)-}

postulate A : Set
postulate B : Set


data _×_ (A B : Set) : Set where
  p : A → B → A × B

{-p0' : AxB → A
p0' (p a b) = a

p1' : AxB → B
p1' (p a b) = b -}

R0 : {A B : Set} → A × B → A
R0 (p a b)  = a

R1 : {A B : Set} → A × B → B
R1 (p a b) = b

{- 
p0 {A} {B} (p a b) = a
-}

data Bool : Set where 
  true  : Bool
  false : Bool

¬ : Bool → Bool
¬ true = false
¬ false = true


data _or_ (A B : Set) : Set where
  inl : A → A or B
  inr : B → A or B

LemIntroA : {B A : Set} → (a : A) → A or B
LemIntroA a = inl a 

LemIntroB : {A B : Set} → (b : B) → A or B
LemIntroB b = inr b

{-Symmetry-}
{-Transivity-}
{-Equality of Sets-}
{-Hypothetical Judgements and Substitution Rules-}

{-or elimination version 1-}

D : {A B : Set} 
    → {C : A or B → Set}
    → ((x : A) → C (inl x))
    → ((y : B) → C (inr y))
    → (c : A or B)
    → C c
D d e (inl x) = d x
D d e (inr y) = e y

{-OR elimination version 2-}
D' : {A B C : Set}
     → (d : (A → C))
     → (e : (B → C))
     → (A or B → C)
D' d e (inl x) = d x
D' d e (inr y) = e y 


{-PiFormation and Intro -}
data Π (A : Set) (B : A → Set) : Set where
 λ' : (b : (x  : A) → B x) → Π A B 

{-Pi Elim and Equal-}
Ap : {A : Set}
     → {B : A → Set}
     → (c : Π A B)
     → (a : A)
     → B a
Ap (λ' b) a = b a

{-ForAll Formation and Intro-}
data ∀' (A : Set) (B : A → Set) : Set where
  λ' : ((x  : A) → B x) → ∀' A B

{-forAll Elim and Equal-}
Ap' : {A : Set}
     → {B : A → Set}
     → (c : ∀' A B)
     → (a : A)
     → B a
Ap' (λ' b) a = b a

{- supsett Formation and Intro-}

data _⊃_ (A : Set) (B : Set) : Set where
 λ' : (A → B) → A ⊃ B

{-supsett Elim and Equal-}

⊃Elim : {A B : Set}
         → (A ⊃ B)
         → A
         → B
⊃Elim (λ' y) a = y a

{-Sigma formation and Introduction-}

data Σ' (A : Set) (B : A → Set) : Set where
 _,_ : (x  : A) → B x → Σ' A B

{-Sigma Elimination and Equality-}

Σ'Elim :{A : Set}
         {B : A → Set}
         {C : (Σ' A B) → Set}
         → (c : Σ' A B)
         → (d : (a : A) → (b : B a) → C( a , b))
         → C c 
Σ'Elim (x , y) d = d x y

{-Exists Formation and Introduction-}

data ∃' (A : Set) (B : A → Set) : Set where
 _,_ : (x : A) → B x → ∃' A B

{-Exists Elimination and Equality-}

∃'Elim : {A : Set}
          {B : A → Set}
          {C : Set}
          → (c : ∃' A B)
          → (d : (x : A) →  (b : B x) → C)
          → C
∃'Elim (x , y) d = d x y

{-ampersand Formation and Introduction-}

data _&'_ (A : Set) (B : Set) : Set where
  _,_ : A → B → A &' B

{-ampersand Elimination and Equality-}

&'Elim : {A : Set}
         {B : Set}
         {C : Set}
         → (A &' B)
         → (A → B → C)
         → C 
&'Elim (x , y) d = d x y

{-Plus Formation and Introduction-}

data _plus_ (A B : Set) : Set where
  inl : A → A plus B
  inr : B → A plus B

LemPlusIntroA : {B A : Set} → (a : A) → A or B
LemPlusIntroA a = inl a 

LemPlusIntroB : {A B : Set} → (b : B) → A or B
LemPlusIntroB b = inr b

{-Plus Elimination and Equality-}

PlusElim : {A B : Set} 
    → {C : A plus B → Set}
    → ((x : A) → C (inl x))
    → ((y : B) → C (inr y))
    → (c : A plus B)
    → C c
PlusElim d e (inl x) = d x
PlusElim d e (inr y) = e y

{-I Formation and Introduction-}

data I {A : Set} : A → A → Set where
 id : (a : A) → I a a

{-I Elimination and I Equality-}

IElim : {A : Set} 
       → {C : (x : A) → (y : A) → (z : I x y) → Set}
       → (a : A)
       → (b : A)
       → (c : I a b)
       → (d : (x : A) → C x x (id x))
       → C a b c
IElim .a a (id .a) d = d a

{-Finite Sets Rules-}

{-Finite Formation and Introduction-}
data ℕ0 : Set where

data ℕ1 : Set where
 m0 : ℕ1

data ℕ2 : Set where
 m0 : ℕ2
 m1 : ℕ2 

{-Finite Elimination and Equality-}

FiniteElim0 : {C : ℕ0 → Set}
            → (c : ℕ0)
            → C c
FiniteElim0 () {-Empty case distinction-}

FiniteElim1 : {C : ℕ1 → Set}
           → (c : ℕ1)
           → (c0 : C m0)
           → C c
FiniteElim1 m0 c0 = c0

FiniteElim2 : {C : ℕ2 → Set}
           → (c : ℕ2)
           → (c0 : C m0)
           → (c1 : C m1)
           → C c
FiniteElim2 m0 c0 c1 = c0
FiniteElim2 m1 c0 c1 = c1


{-Lists Rules-}
data List (A : Set) : Set where
  nil : List A
  cons  : (a : A) (b : List A) → List A

{-List Elimination and Equality-}

ListElim : {A : Set}
        → {C : List A → Set}
        → (c : List A)
        → (d : C nil)
        → (e : (x : A) → (y : List A) → (z : C y) → C (cons x y))
        → C c
ListElim nil d e = d
ListElim (cons a b) d e = e a b (ListElim b d e)

{-the above is defined by list recursion-}

{-Well Ordering Formation and Introduction-}

data W (A : Set) (B : A → Set) : Set where
 sup : (x  : A) → (b : B x → W A B) → W A B

{-Well Ordering Elimination and Equality-}


WElim : {A : Set}
     → {B : A → Set}
     → {C : W A B → Set}
     → (c : W A B)
     → (step : (a : A) 
                → (f : B a → W A B) 
                → (c : (b : B a) → C (f b))
                → C (sup a f))
     
     → C c
WElim {A} {B} {C} (sup a f) step = step a f (λ b → WElim {A} {B} {C} (f b) step)


{-Ordinal Formation and Introduction-}

data Ord : Set where
  zero : Ord
  suc : Ord → Ord 
  sup : (ℕ → Ord) → Ord

{-Ordinal Elimination and Equality-}

OrdElim : {C : Ord → Set}
        → (c : Ord)
        → (step0 : C zero) 
        → (step1 : (a : Ord)
                    → (C a)
                    → C (suc a))
        → (step2 : (a : ℕ → Ord)
                    → (ih : (n : ℕ) → C (a n)) 
                    → C (sup a))
        → C c   
OrdElim zero step0 step1 step2 = step0
OrdElim (suc y) step0 step1 step2 = step1 y (OrdElim y step0 step1 step2)
OrdElim (sup y) step0 step1 step2 = step2 y (λ n → OrdElim (y n)  step0 step1 step2 ) 

{-Recursively calling the functions (above)-}

{-Universe Rules-}

{-Universe Formation and Introduction-}

mutual 
 data U : Set where
  ℕhat : U
  ℕ0hat : U
  ℕ1hat : U
  ℕ2hat : U
  _&hat_ : U → U → U
  Σhat : (a : U) → (b : T a → U) → U
  Πhat : (a : U) → (b : T a → U) → U 
  What  : (a : U) → (b : T a → U) → U
  Ihat : (u : U) → (a : T u) → (b : T u) → U 
 
 T : U → Set
 T ℕhat = ℕ
 T ℕ0hat = ℕ0
 T ℕ1hat = ℕ1
 T ℕ2hat = ℕ2  
 T (x &hat y) = (T x &' T y)
 T (Σhat a b) = Σ' (T a) (λ x → T (b x))
 T (Πhat a b) = Π (T a) (λ x → T (b x))
 T (What a b) = W (T a) (λ x → T (b x))
 T (Ihat u a b) = I {T u} a b 
  {-Tarski-}
  {-a la Russell is NON PROVABLE-}

