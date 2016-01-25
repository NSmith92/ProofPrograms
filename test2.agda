module test2 where


{-

New additions
- I introduced an equality on bool
  _==Bool_
- Proved lemmata 
  eqBoolLemma1
  eqBoolLemma2
  refl==Bool
  orderedLemma1
  ∧BoolLemma1
  ∧BoolLemma2 
  ∧BoolLemmaIntro 

Finishing of proofs of
   Correctness-insert
   Correctness-insert-aux

Everything
starting with
Proof that insertion-sort l is a permutation  of l

-}

infixr 5 _::_  
infixl 5 _+_ 
{- means 2 + 3 + 5   is parsed as (2 + 3) + 5 and not as 
   2 + (3 + 5)

   5 priority
-}

infixl 6 _*_ 

{- .....  * binds more than + because 6 h> 5 
  2 + 3 * 5  is parsed as 2 + (3 * 5) and not (2 + 3) * 5  ....

-}

data _∧_  (A B : Set) : Set  where
  and : A -> B -> A ∧ B

{- elements of A ∧ B are of there form
   and a b
   where a : A and b : B 

  A ∧ B = { and a b  |  a : A and b : B }
-}
  
data _∨_  (A B : Set) : Set  where
  inl : A → A ∨ B
  inr : B → A ∨ B


{- elements of A ∨ B are of form
        inl a where a : A
    or  inr b where b : B

so
  A ∨ B = { inl a | a : A} ∪  { inr b  | b : B}
-}

data ∃ (A : Set)(B : A -> Set) : Set where
  exists : (a : A) -> B a -> ∃ A B

{- we write ∃ x : A. B means  ∃ A (λ x -> B)
            ∃ x : ℕ. x == 0   means ∃ ℕ (λ x -> x == 0)

    elements of ∃ A B are of form
        exists a b
          where a : A and b : B a

so
  ∃ x A B = { exists a b |  a : A and b : B a }
-}




data ⊥ : Set where

{- ⊥ has no proofs 

   ⊥ = {} = ∅   (the set containing no elements, or the empty set)

  -}


data ⊤ : Set where
  triv : ⊤ 


{- ⊤ has exactly one proof, namely triv (for tivial)
   or
   ⊤ = { triv }

-}



-- infix 3 _≤_
infix 2 _∧Bool_
infix 1 _∨Bool_

data ℕ : Set  where 
  zero : ℕ 
  suc  : ℕ → ℕ 

{- Haskell:

data Nat = zero | suc Nat

-}




{- standard library is located at{
   ~/agda/standardlib/lib-0.7/src/ -}


{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}



a : ℕ 
a = 356

{-
if_then_else_ : Bool -> ℕ → ℕ → ℕ 

if true then 5 else 7
-}

_+_ : ℕ → ℕ → ℕ 
n + 0      = n
n + suc m = suc (n + m)

{- in pure agda it would be:

_+_ : ℕ → ℕ → ℕ 
n + zero  = n
n + suc m = suc (n + m)

Builtin natural numbers you can consider as abbreviations

0 = zero
1 = suc zero
2 = suc (suc zero)
...

However, agda will actually internally use 
1 as suc 0
2 as suc 1
for efficiency reasons

-}


{- 
n + (suc m) = n + (m + 1) = (n + m) + 1 = suc (n + m )


after having introduced + we know

n + 1 = n + (suc 0) = suc (n + 0) = suc n

-}



{- 

n + suc (suc zero) = suc ( n + suc zero) = suc ( suc (n + zero))
= suc (suc 0)

-}


_*_ : ℕ → ℕ → ℕ 
n * 0 = 0
n * (suc m) = (n * m)  + n

{- n * (m + 1) = n * m + n * 1 = n * m + n
-}

data ℕ+ : Set where
  suc' : ℕ → ℕ+

sucℕ+ : ℕ+ → ℕ+ 
sucℕ+ (suc' y) = suc' (y + 1)


ℕ+->ℕ  : ℕ+ → ℕ 
ℕ+->ℕ (suc' n) = suc n

data ℤ : Set where
  plus : ℕ+ -> ℤ
  zero : ℤ 
  minus : ℕ+ -> ℤ 


exZ2 : ℤ 
exZ2 = minus (suc' 353)

{- - 354 -}


sucℤ  : ℤ   → ℤ 
sucℤ (plus (suc' n)) = plus (suc' (suc n))
   {-  plus (suc n) requires suc n to be of type ℕ+
                    because plus : ℕ+ -> ℤ 
       suc n : ℕ+   requires n to be of type ℕ 
                    because suc : ℕ → ℕ+
    plus (suc (suc n)) requires (suc (suc n)) to be of type ℕ+
                    because plus : ℕ+ -> ℤ 
     (suc (suc n) : ℕ+   requires n to be of type ℕ 
                    because suc : ℕ → ℕ+

If we had written 

data ℕ+ : Set where
  suc' : ℕ → ℕ+


then the definition would be


sucℤ  : ℤ   → ℤ 
sucℤ (plus (suc' n)) = plus (suc' (suc n))
sucℤ zero     = plus (suc' 0)
sucℤ (minus (suc' zero)) = zero
sucℤ (minus (suc' (suc n))) = minus (suc' n)


       in plus (suc n)  suc is constructor for ℕ+
      in plus (suc (suc n))  first suc is constructor for ℕ+,
                             second suc is constructor for ℕ 
-}
sucℤ zero     = plus (suc' 0)
sucℤ (minus (suc' zero)) = zero
sucℤ (minus (suc' (suc n))) = minus (suc' n)


sucℤ'  : ℤ   → ℤ 
sucℤ' (plus (suc' n)) = plus (suc' (suc n))
sucℤ' zero       = plus (suc' 0)
sucℤ' (minus (suc' zero)) = zero
sucℤ' (minus (suc' (suc n))) = minus (suc' n) 


{- abbreviation mode: M-x abbrev-mode -}

suc'' : ℕ+ → ℕ+
suc''( suc' n) = suc'( suc n)

exZ1 : ℤ 
exZ1 = plus (suc' 353)

{- + 354 -}

exZ3 : ℤ 
exZ3 = minus (suc' 353)

{- - 354 -}


sucℤ3  : ℤ   → ℤ 
sucℤ3 (plus (suc' n)) = plus (suc' (suc n))
   {-  plus (suc n) requires suc n to be of type ℕ+
                    because plus : ℕ+ -> ℤ 
       suc n : ℕ+   requires n to be of type ℕ 
                    because suc : ℕ → ℕ+
    plus (suc (suc n)) requires (suc (suc n)) to be of type ℕ+
                    because plus : ℕ+ -> ℤ 
     (suc (suc n) : ℕ+   requires n to be of type ℕ 
                    because suc : ℕ → ℕ+

If we had written 

data ℕ+ : Set where
  suc' : ℕ → ℕ+


then the definition would be


sucℤ  : ℤ   → ℤ 
sucℤ (plus (suc' n)) = plus (suc' (suc n))
sucℤ zero     = plus (suc' 0)
sucℤ (minus (suc' zero)) = zero
sucℤ (minus (suc' (suc n))) = minus (suc' n)


       in plus (suc n)  suc is constructor for ℕ+
      in plus (suc (suc n))  first suc is constructor for ℕ+,
                             second suc is constructor for ℕ 
-}
sucℤ3 zero     = plus (suc' 0)
sucℤ3 (minus (suc' zero)) = zero
sucℤ3 (minus (suc' (suc n))) = minus (suc' n)


sucℤ''  : ℤ   → ℤ 
sucℤ'' (plus (suc' n)) = plus (suc' (suc n))
sucℤ'' zero       = plus (suc' 0)
sucℤ'' (minus (suc' zero)) = zero
sucℤ'' (minus (suc' (suc n))) = minus (suc' n) 


{- abbreviation mode: M-x abbrev-mode -}

suc''' : ℕ+ → ℕ+
suc''' ( suc' n) = suc'( suc n)

predℤ  : ℤ   → ℤ 
predℤ (plus (suc' zero)) = zero
predℤ (plus (suc' (suc n))) = plus(suc' n)
predℤ zero = minus(suc' zero)
predℤ (minus (suc' n)) = minus (suc' (n + 1))

predℤ'  : ℤ   → ℤ 
predℤ' (plus (suc' zero)) = zero
predℤ' (plus (suc' (suc y))) = plus (suc' y)
predℤ' zero = minus (suc' zero)
predℤ' (minus y) = minus (sucℕ+ y )


{- application is left associative which means
   f a b
   is to be read
   (f a) b
   and not
   f (a b)

   N -> N -> N is read as
   N -> (N -> N)

   if f : N -> N -> N   and n : N
   f n  : N -> N   and if m : N
   f n m : N
-}

{-predℤ (minus (suc' n)) = minus (suc'(suc n))-}


ℕ→ℤ : ℕ → ℤ 
ℕ→ℤ zero = zero
ℕ→ℤ (suc n) = sucℤ (ℕ→ℤ n)

data Maybe (A : Set) : Set where
  nothing  : Maybe A
  just     : A → Maybe A

data Q : Set where
  _/_ : ℤ → ℕ+ → Q

{- (plus 3) / 5   should be equal to 
   (plus 6) / 10 
-}




{-
_/_ : ℤ → ℤ → Maybe Q
z / pos y = just {!!}
z / zero = nothing
z / neg y = {!!}

-}

data Bool : Set where
 true : Bool
 false : Bool  

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then a else b = a
if false then a else b = b

{- and  ∧ = \wedge 
   or   ∨  = \vee 

   

-}


{- negation on booleans
-}   

¬Bool : Bool → Bool
¬Bool true = false
¬Bool false = true

_∧Bool_ : Bool → Bool → Bool
true  ∧Bool b     = b
false ∧Bool _     = false


_∧Bool'_ : Bool → Bool → Bool
true  ∧Bool' true  = true
_     ∧Bool' _     = false


_∨Bool_ : Bool → Bool → Bool
true  ∨Bool _ = true
false ∨Bool b = b


_∨Bool'_ : Bool → Bool → Bool
true ∨Bool' true = true
true ∨Bool' false = true
false ∨Bool' true = true
false ∨Bool' false = false


_∨Bool''_ : Bool → Bool → Bool
false ∨Bool'' false = false
_     ∨Bool'' _     = true


{- We define an equality on boolens
   b ==Bool b'    is 
   true if b and b' are equal boolean values
   false otherwise

   if b is true then it is true if and only if b' is true, so the result is b'
   if b is false then it is false if and only if b' is false
     so the result is ¬Bool b'
-}

_==Bool_ : Bool → Bool → Bool
true  ==Bool b' = b'
false ==Bool b' = ¬Bool b'

{- we have the type Bool or Booleans (containing true and false)
   and formulas  (which might have an element, in which case they
              are valid, or might not have an element, in which case
              they are invalid )

   We assign to every Boolean value a formula
    such that:
     if the value is true, then the formula should be provable
                           e.g. could be ⊤
     if the value is false, then the formula is not provable\
                           e.g. could be ⊥




-}



True : (b : Bool) -> Set
True true  = ⊤ 
True false = ⊥ 


False : (b : Bool) -> Set
False b = True (¬Bool b)





_<ℕbool_ : ℕ → ℕ → Bool
_     <ℕbool 0     = false
0     <ℕbool suc _ = true
suc n <ℕbool suc m = n <ℕbool m


_==ℕbool_ : ℕ → ℕ → Bool
0     ==ℕbool 0     = true
0     ==ℕbool suc _ = false
suc _ ==ℕbool 0     = false
suc n ==ℕbool suc m = n ==ℕbool m

{- We prove that True (b ∧Bool b') implies True b and True b' -}

∧BoolLemma1 : (b b' : Bool) → True (b ∧Bool b') → True b
∧BoolLemma1 true  b' p = triv
∧BoolLemma1 false b' ()

∧BoolLemma2 : (b b' : Bool) → True (b ∧Bool b') → True b'
∧BoolLemma2 true  b' p = p
∧BoolLemma2 false b' ()

{- We prove the introduction principle for ∧Bool namely
   that True b and True b' imply True (b ∧Bool b') 
-}

∧BoolLemmaIntro : (b b' : Bool) → True b → True b' → True (b ∧Bool b')
∧BoolLemmaIntro true  b' trueb trueb' = trueb'
∧BoolLemmaIntro false b' ()    trueb'


{- We introduce some general lemmata on Booleanss -}

ifthenelseLemma1 : {D : Set}
                  → (C : D → Set)
                  → (b : Bool)
                  → (d d' : D)
                  → C d
                  → C d'
                  → C (if b then d else d')
ifthenelseLemma1 C true d d' c c' = c
ifthenelseLemma1 C false d d' c c' = c'

{- We show that if  True(b ==Bool b') and b is true then True b' holds -}

eqBoolLemma1 : (b : Bool)
               → True (true ==Bool b)
               → True b
eqBoolLemma1 b p = p


{- We show that if  True(b ==Bool b') and b is false then False b' holds 
   It holds since (false ==Bool b) is equal to (¬Bool b)
   so we can use neqBoolLemma1
  
-}

eqBoolLemma2 : (b : Bool)
               → True (false ==Bool b)
               → False b
eqBoolLemma2 b p = p


{- We show that ==Bool is reflexive, i.e.
   True (b ==Bool b) holds  always 
-}

refl==Bool : (b : Bool) → True (b ==Bool b)
refl==Bool true  = triv
refl==Bool false = triv



{- Original definition of List, when Agda didn't have special symbols was:

data List (A : Set) : Set where
  nil  : List A
  cons : A -> List A -> List A

2 :: 3 :: []  was 

cons 2 (cons 3 nil)

-}


{- Data types

data A : Set where
  C1 : A -> A
  C2 : A
  C3 : ℕ → A -> A -> A


means:

A consists of everything I can obtain by using constructors
C1 C2 C3

so the elements are

C2
C1 C2
C3 5 C2 (C1 C2)


Elements starting with different constructors are different

(we write /=  for not equal)

C2 /= C1 C2  (because the constructors C2 and C1 are different)
C1 /= C3 5 C2 (C1 C2)
             (because the constructors C1 and C3 are different)

Elements starting with the same constructors are equal
  if their arguments are equal.


C3 5 C2 C2  /= C3 6 C2 C2
   because 5 /= 6

C3 5 C2 C2 = C3 (2 + 3) C2 C2
  because 2 +3 is equal to 5


2 + 3 doesn't start with a constructor
it's a defined function (_+_) applied to 2 and 3


Elements of a data type starting with a constructor are called 
  canonical elements
  So
      suc (2 + 3) is canonical
      (It is not fully reduced, because we can reduce 2 + 3 to 
       5 which is suc( suc (... zero))
       however it starts with a constructor
       and therefore allows to do the first step in a comparison
       with another element, namely checking wether their constructors
       are the same or not

       2 + 3 I don't know yet what the constructor is
         (which could be suc or zero)

Elements of a data type not starting with a constructor are called
  non-canonical elements.

In order to compare any non-canonical elements, we reduce
them until they start with a constructor


To compare 
2 + 2  and 2 + 1
both sides are non-canonocial, so we need in order to compare them
first reduce both sides until they are canonical:


2 + 2
=
(suc 1) + (suc 1)   (homework: check it)
                    ( n + suc m = suc (n + m)
-->
suc ( (suc 1) + 1)

(we can reduce it further:
 = 
 suc ( (suc 1) + (suc 0))
 -->
 suc ( suc ( (suc 1) + 0 ) )
 -->
 suc ( suc ( (suc 1)))
)

For comparing
2 + 2  and 2 + 1

in a first step all we need is to reduce
left side to 
suc ( (suc 1) + 1)
because then it is already canonical

right hand side
2 + 1
=
(suc 1) + (suc 0)
->
suc ( (suc 1) + 0 )
->
suc ( (suc 1) 

but we can stop at
suc ( (suc 1) + 0 )
because that's canonical

For comparing 
2 + 2 and 2 + 1
we need to compare
suc ( (suc 1) + 1)   and   ( suc ( (suc 1) + 0 ))
they start with the same constructor
so we need to compare the arguments
(there is only one)

(suc 1) + 1   and    (suc 1) + 0


(suc 1) + 1  is non-canoncial

(suc 1) + 1
= 
(suc 1) + (suc 0)
->
suc ((suc 1)  + 0)


suc ( (suc 1) + 0 )
is canoncial

so in order to compare
(suc 1) + 1   and    suc ( (suc 1) + 0 )

we need to compare
suc ( (suc 1) + 0 ) and suc ( (suc 1) + 0 )
and therefore to cpare
(suc 1) + 0  and (suc 1) + 0 

*** Homework: find the mistake

Agda's reduction system is confluent,
which means the order in which you reduce terms
doesn't matter.
(So above we could have fully evaluated the left and right side
and then compared it and it would have given the same result)

So in order to compare 

2 + 2 and 2 + 1
you can just 
evaluate
2 + 2 -->   4  (or suc(...(suc zero)
2 + 1 -->   3

4  equals  3
is
suc 3  equals suc 2
which is 
3 equals 2
which is
suc 2 equals suc 1
which is
2 equals 1
which  is
1 equals 0
which is 
suc 0 equals 0
which is false because they start with a different constructor.









To compare 
2 and 2 + 1
Left side is just an abbreviation for 
   suc 2
   which is canonical (because it starts with a constructor)



-}


data List (A : Set) : Set where
  []  : List A
  _::_ : A -> List A -> List A

l : List ℕ 
l = 2 :: 3 :: []  


{- not in final code, just example for usage-}

postulate l0 : List ℕ 


{-
we usually don't use postulate, because it allows
us to prove everything.
We use it here only to solve the next goal so that we
can print it out -}

f : List ℕ → List ℕ 
f l = l0

{- less : A -> A -> Bool

less a b = true means a is less than b
less a b = false means a is not less than b
-}


≤Head : {A : Set} → (A → A → Bool) → A → List A → Bool
≤Head _≤_ a [] = true
≤Head _≤_ a (b :: l') = a ≤ b



ordered : {A : Set} → (A → A → Bool) → List A -> Bool
ordered _≤_ []              = true
ordered _≤_(a :: l)        = ≤Head _≤_ a l  ∧Bool ordered _≤_ l

Ordered : {A : Set} → (A → A → Bool) → List A -> Set
Ordered _≤_ l = True (ordered _≤_ l)




ordered'' : {A : Set} → (A → A → Bool) → List A -> Bool
ordered'' _≤_ []              = true
ordered'' _≤_ (a :: [])       = true
ordered'' _≤_ (a :: a' :: l') = a ≤ a' ∧Bool ordered'' _≤_ (a' :: l')



ordered' : {A : Set} → (_≤_ : A → A → Bool) → List A -> Bool
ordered' _≤_ [] = true
ordered' _≤_(a :: []) = true
ordered' _≤_ (a :: a' :: l ) = a ≤ a' ∧Bool ordered' _≤_(a' :: l)


{- Since ordered _≤_ (a :: l) is equal to 
   ≤Head _≤_ a l  ∧Bool ordered _≤_ l
   and    True(b ∧Bool b') implies  True b' 
   by ∧BoolLemma2
   we get that
   True (ordered (a :: l)) implies  True ordered l
-}
   
orderedLemma1 : {A : Set} 
                → (_≤_ : A → A → Bool) 
                → (a : A) 
                → (l : List A) 
                → Ordered _≤_ (a :: l) 
                → Ordered _≤_ l
orderedLemma1 _≤_ a l p = ∧BoolLemma2 (≤Head _≤_ a l) (ordered _≤_ l) p

 

{- Example 

A = ℕ 
less = _<ℕbool_  : ℕ → ℕ → Bool
list =  2 :: 3 :: []    : List ℕ 
-}


f27 : ℕ → ℕ 
f27 n = suc n

_>ℕbool_ : ℕ → ℕ → Bool
n >ℕbool m = m <ℕbool n
{- _>ℕbool_ n m = _<ℕbool_ m n -}

{- 3 >ℕbool 2
   reduces to  ( we write --> )
   2 <ℕbool 3
   =
   (suc 1) <ℕbool (suc 2)
   -->   (we use   suc n <ℕbool suc m = n <ℕbool m  
                   n = 1 and m = 2)
   1 <ℕbool 2
   =
   (suc 0) <ℕbool (suc 1)
   -->
   0 <ℕbool 1
   = 
   zero <ℕbool (suc zero)
   -->
   true

   2 <ℕbool 1
   = 
   suc 1 <ℕbool suc zero
   -->
   1 <ℕbool 0
   =
   suc 0 <ℕbool 0
   -->
   false
-}


{- Homework:
run through some other reductions:

 2 >ℕbool 5

 5 >ℕbool 2

 2 <ℕbool 5
  
 some example
-}

  

{- normal mathematics
n >ℕbool m  if and only if m <ℕbool n

n >ℕbool m  is defined as   m <ℕbool n
-}

test27 : Bool
test27 = ordered  _<ℕbool_ (2 :: 3 :: [])

test28 : Bool
test28 = ordered  _<ℕbool_ (3 :: 2 :: [])

{-
If we run compute to normal form on test27
the following happens:

test27
-->
ordered  _<ℕbool_ (2 :: 3 :: [])
    {-    2 :: 3 :: []   =  _::_ 2 (_::_ 3 [] )
          _::_   and [] 
          are the constructors for List A
    -}
        
-->
(_<ℕbool_ 2 3) ∧Bool (ordered _<ℕbool_ (3 :: []))


-}

mutual
 f0 : ℕ → ℕ 
 f0 0 = 0
 f0 (suc n) = f1 n

 f1 : ℕ → ℕ 
 f1 0 = 3
 f1 (suc n) = f0 n
 


p0 : Bool
p0 = ordered _<ℕbool_ (2 :: 5 :: 3 :: [])



{- 

ordered _<ℕbool_ (2 :: 5 :: 3 :: [])
= (2 <ℕbool 3) ∧Bool (ordered _<ℕbool_ (5 :: 3 :: []))
= (2 <ℕbool 3) ∧Bool (5 <ℕbool 3 ∧Bool (ordered _<ℕBool_ (3 :: [])))
  = (2 <ℕbool 3) ∧Bool (5 <ℕbool 3 ∧Bool true)
= (2 <ℕbool 3) ∧Bool (false ∧Bool true)\
= (2 <ℕbool 3) ∧Bool false 
= true ∧Bool false 
= false 

-}

{- insert less a l 
   assumes that l is sorted
   and returns the result of inserting a into l
   so that we obtain a sorted list
-}


insert' : { A : Set } -> (A → A → Bool) → A -> List A → List A
insert' _≤_ a []        = a :: []
insert' _≤_ a (a' :: l) = if    a ≤ a' 
                          then  a :: a' :: l 
                          else (a' :: insert' _≤_ a l)



mutual
  insert : { A : Set } -> (A → A → Bool) → A -> List A → List A
  insert _≤_ x []        = x :: []
  insert _≤_ x (a :: l) =  insert-aux _≤_ x a l (x ≤ a)

  insert-aux : { A : Set } -> (A → A → Bool) → A -> A → List A → Bool → List A
  insert-aux _≤_ x a l true  = x :: a :: l 
  insert-aux _≤_ x a l false = a :: insert _≤_ x l

{- insert-aux _≤_ a a' l b = if b then a :: a' :: l else (a' :: insert _≤_ a l) 

   insert-aux inserts a into (a' :: l) provided b = (a ≤ a')
-}

insertion-sort : { A : Set } → (A → A → Bool) → List A → List A
insertion-sort _≤_ []        = []
insertion-sort _≤_ (a :: l)  = insert _≤_ a (insertion-sort _≤_ l)


{- BHK interpretation of logical connectives
   Brouwer-Heyting-Kolmogorov interpretation of the logical connectives

   What is a proof of a formula A


   A proof of A ∧ B     is a pair <p,q> s.t. p is a proof of A
    and q is a proof of B
  A proof of A ∨ B      is either inl p for a proof p of A
                        or        inr p for a proof p of B
     inr reads in-right
     inl reads in-left 

  A proof of A -> B is a function which takes a proof of A
      and computes from it a proof of B
      so it's just the function type A -> B

  A proof of ∀ x : A.B(x)
    is a function which takes an x: A and computes a proof of B(x)
    this is just 
        (x : A) -> B x

  A proof of (∃ x : A. B(x)
    is a pair consisting of an a : A and a proof of B(a)

  
  A proof of ⊥    (falsity)
    doesn't exist

    \bot

  A proof of ⊤   (true formula)
   is    triv 



   propositions as types 
-}











{- Lemma:  ∀ A : Set.∀ less : A -> A -> Bool.∀ l : List A. 
                     Ordered less (insertion-sort less l)

-}



f25 : ℕ → ℕ 
f25 = λ x → x

f26 : ℕ → ℕ 
f26 = \ x -> x

f28 : ℕ 
f28 = (λ x -> x) 3


 


Lemma∧Bool1 : (a b : Bool) → True a → True b → True (a ∧Bool b)
Lemma∧Bool1 true b p q = q
Lemma∧Bool1 false b () q


{- or
Lemma∧Bool1 false b p q = p 
-}


Lemma1 : {A : Set} 
         → (_≤_  : A → A → Bool) 
         → (a : A)
         → (l : List A)
         →  True (ordered _≤_ l)
         →  True (≤Head _≤_ a l)
         →  True (ordered _≤_ ( a :: l))
Lemma1 _≤_ a []        p q  = triv 
   {- goal is True (ordered _≤_ ( a :: []))
      ordered _≤_ ( a :: []) evaluates to true
      True true evaluates to ⊤ 
      which has one element triv
   -}
Lemma1 _≤_ a (a' :: l') p q = Lemma∧Bool1 
                              (≤Head _≤_ a (a' :: l')) 
                              (ordered _≤_ (a' :: l')) 
                              q p

{- Goal is 
      True ((a ≤ a') ∧Bool ordered _≤_ (a' :: l'))
      q : True (≤Head _≤_ a (a' :: l')) = True (a ≤Bool a')
      p : True (ordered _≤_ (a' :: l'))
   so q proves left and p the right hand side of the boolean conjunction
   
   Lemma∧Bool1  shows that essentially
      True b  ∧ True b' -> True (b ∧Bool b')
      so with Lemma∧Bool1  we obtain from q and p  the goal
   However Lemma∧Bool has as well arguments b and b'

   in our case  b =  (≤Head _≤_ a (a' :: l'))  (which is = a ≤Bool a'
                b' = ordered _≤_ (a' :: l')
   so the goal is solved by taking 
     Lemma∧Bool1 (≤Head _≤_ a (a' :: l')) 
                 (ordered _≤_ (a' :: l')) 
                 q p
-}


mutual
  lemmaInsert≤Head : {A : Set} →  (_≤_ : A → A → Bool) → (x a : A) → (l : List A)
           → True ( a ≤ x )
           → True (≤Head _≤_ a l)  
           → True (≤Head _≤_ a (insert _≤_ x  l))
  lemmaInsert≤Head _≤_ x a []        p q = p
  lemmaInsert≤Head _≤_ x a (a' :: l) p q = lemmaInsertaux≤Head _≤_ x a a' l (x ≤ a') p q


  lemmaInsertaux≤Head : {A : Set} →  (_≤_ : A → A → Bool) → (x a a' : A) → (l : List A) → (b : Bool)
              → True ( a ≤ x )
              → True ( a ≤ a' )
              → True (≤Head _≤_ a (insert-aux _≤_ x a' l b))
  lemmaInsertaux≤Head _≤_ x a a' l true p q  = p
  lemmaInsertaux≤Head _≤_ x a a' l false p q = q


{- 
   theorem  main statement to be proved
   lemma    is auxiliary theorem (so statement is not so important
               but it is used to prove a theorem
   corollary  easy conclusion of a theorem or lemma.
      (e.g. you show for all n some property
       corollary: property holds for 5

   when we prove a theorem or lemma, we often need to prove something
     more general.

   roughly:
      you want to show    all n : Nat. phi(n) 
       phi(n) refers to a parameter, but k=5
       phi(n) = psi(n,5)
       but in order to prove phi(n+1) we need psi(n, 17)
       so phi(n) doesn't help
       So instead we prove
       all n, m.psi(n,m)
       
-}



Linear : {A : Set} → (_≤_ : A → A → Bool) → Set
Linear {A} _≤_ = (a a' : A) → False (a ≤ a') → True(a' ≤ a)


mutual
  Correctness-insert : {A : Set} 
                       → (_≤_ : A → A → Bool) 
                       → Linear _≤_
                       → (x : A)
                       → (l : List A)
                       → True (ordered _≤_ l)
                       → True (ordered _≤_ (insert _≤_ x l))
  Correctness-insert _≤_ islinear x []       orderedl = triv
  Correctness-insert _≤_ islinear x (a :: l) orderedl = Correctness-insert-aux _≤_ islinear x a l (x ≤ a) 
                                                      (refl==Bool (x ≤ a)) 
                                                      orderedl


  Correctness-insert-aux : {A : Set} 
                       → (_≤_ : A → A → Bool) 
                       → Linear _≤_
                       → (x : A)
                       → (a : A)
                       → (l : List A)
                       → (b : Bool)
                       → True (b ==Bool (x ≤ a))
                       → True (ordered _≤_ (a :: l))
                       → True (ordered _≤_ (insert-aux _≤_ x a l b))
  Correctness-insert-aux _≤_ islinear x a l true  b==x≤a orderedl = ∧BoolLemmaIntro 
                                                                    (x ≤ a) 
                                                                    (ordered _≤_ (a :: l)) 
                                                                    b==x≤a 
                                                                    orderedl
  Correctness-insert-aux _≤_ islinear x a l false b==x≤a orderedl = ∧BoolLemmaIntro 
                                                                      (≤Head _≤_ a (insert _≤_ x l))
                                                                      (ordered _≤_ (insert _≤_ x l)) 
                                                                      (lemmaInsert≤Head _≤_ x a l  
                                                                       (islinear x a b==x≤a) 
                                                                       (∧BoolLemma1 
                                                                          (≤Head _≤_ a l) 
                                                                          (ordered _≤_ l) 
                                                                          orderedl)) 
                                                                      (Correctness-insert 
                                                                       _≤_ islinear x l 
                                                                       (orderedLemma1 _≤_ a l orderedl)) 


{- Homework:
   look up on the internet cons and nil and list

  _::_ is a name for cons
  []   is a name for nil


  Original definition of list:


  data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A


So the list

[1,6,3,2] is

cons 1 (cons 6 (cons 3 (cons 2 nil)))
because:


nil : List A

[2] = cons 2 nil : List A
[3,2] = cons 3 (cons 2 nil) : List A

In order to make it more readable
we write _::_ for  cons
         []   for  nil


[1,6,3,2] = 1 :: ( 6 :: (3 :: (2 :: [])))

and with infixr 7 _::_
this read 

1 :: 6 :: 3 :: 2 :: []


Two ways of parsing
1 :: 6 :: 3 :: 2 :: []


1 :: (6 :: (3 ::(2 :: [])))
or


(((1 :: 6) :: 3) :: 2) :: []



2 + 3 + 5 can be parsed as 

(2 + 3) + 5
or
2 + (3 + 5)

for natural numbers they are equivalent
for _::_ not

and in theorems it makes a difference to talk about


x + (y + z)
and
(x + y) + z


infixr 7 _::_
tells 

to parse 

1 :: 6 :: 3 :: 2 :: []

as

1 :: (6 :: (3 ::(2 :: [])))

(infix-r for infix-right

and the number is priority

in 2 + 3 * 5 
should be parsed as

  2 + (3 * 5) and not (2 + 3) * 5

so * needs to get a higher number than +

-}

 
Correctness-Insertion-Sort : {A : Set}
                          →  (_≤_ : A → A → Bool)
                          → Linear _≤_
                          → (l : List A)
                          → True (ordered _≤_ (insertion-sort _≤_ l))
Correctness-Insertion-Sort _≤_ islinear [] = triv
Correctness-Insertion-Sort _≤_ islinear ( a :: l) = Correctness-insert _≤_ islinear a 
                                                    (insertion-sort _≤_ l) 
                                                    (Correctness-Insertion-Sort _≤_ islinear l)


{- Second line:
Goal is
 True (ordered _≤_ (insert _≤_ a (insertion-sort _≤_ l)))

we want to use 
Correctness-insert : {A : Set} 
                       → (_≤_ : A → A → Bool) 
                       → Linear _≤_
                       → (l : List A)
                       → (x : A)
                       → True (ordered _≤_ l)
                       → True (ordered _≤_ (insert _≤_ x l))
  

-}

{- Proof that insertion-sort l is a permutation  of l -}

{- We want to show that insertion-sort l is a permutation of l
   A permutation of l is a reordering of the elements in l
-}

{- We first introduce the set of positions in a  list:
   the empty list has no positions
   the list a :: l
   has as positions head
          and       tail p 
                    where p is a position in l

   We first define an operation which from a set of positions P creates the set
       { head } ∪ { tail p  }
-}

data PositionEmptylist : Set where
  head : PositionEmptylist

data CreatePositionCons (P : Set) : Set where
   head  : CreatePositionCons P
   tail  : P → CreatePositionCons P

Position : {A : Set} → List A → Set
Position [] = PositionEmptylist
Position (x :: l) = CreatePositionCons (Position l)



{- When we consider insert a l 
   it doesn't simply exchange in l an element for a.
   it rotates the elements:
   
   the result of
   
   insert a (a1 :: a2 :: a3 :: ... an :: [])

   is
   
   a1 :: a2 :: ... :: ak-1 :: a :: ak :: ... :: an ::  []


   i.e.

   we move a into the list and rotate all the elements in the list to the front


   therefore we define a rotate operation which takes a position in
   a :: l
   inserts a into the list after this position 
-}


insertAtPosition : {A  : Set}  → (x : A) → (l : List A) → (Position l) → List A
insertAtPosition x []       head     = x :: []
insertAtPosition x (a :: l) head     = x :: a :: l
insertAtPosition x (a :: l) (tail p) = a :: insertAtPosition x l p
  
   






{- a permutation of a list l are:
   in case of [] there is only one permutation which gives you []
   in case of a :: l we obtain a permutation by first
     taking a permutation of l
     applying it to l (we obtain l')
     and then taking a position in a :: l'
     and applying a full exchange to it.

  we define first a set consisting of the identity permutation (for the list l)
  and one which forms from 
  the permutations in case of a :: l
     which  consists of a permutation of list l (an element of a set Per)
            and a position in a :: l'           (an element of a set of positions Pos : Per → Set
                                                 i.e. a set depending on per : Per
-}


{- the only permutation of [] -}

data IdentityPermutation : Set where
  id : IdentityPermutation 

{- the permutations for a :: l
   are formed from permutations for list l and if the result is l'
   a position in  a :: l'
-}

data ConsPermutation (Perm : Set) (Pos : Perm → Set) : Set where
  consPermute  : (p : Perm) → Pos p → ConsPermutation Perm Pos


{- we define now simultaneously (mutually) 
   the set of permutations
   and the result of applying a permutation to a list l
       i.e. a list obtained by applying the permutaiton to it
-}

mutual
  Permutation : {A : Set} → List A → Set
  Permutation []       = IdentityPermutation
  Permutation (a :: l) = ConsPermutation (Permutation l) (λ perm → Position (permute l perm))

  permute : {A : Set} → (l : List A) → Permutation l → List A
  permute {A} [] perm = []
  permute {A} (a :: l) (consPermute perm pos) = let
                                                    l'  : List A
                                                    l'  = permute l perm
                                                  in
                                                    insertAtPosition a l' pos


                                                  
{- we define the identity type:
   it has only a proof refl of a == a   for any a
-}

data _==_ {A : Set} (a : A) : A → Set where
  refl : a == a


lemmaEqList : {A : Set} → (a : A) → (l l' : List A) → l == l' → (a :: l) == (a :: l')
lemmaEqList a .l l refl = refl  {- goal is  (a :: l) == (a :: l) -}


lemmaEqfun : {A B : Set} → (f : A → B) → (a  a' : A) → a == a' → f a == f a'
lemmaEqfun f .a' a' refl = refl  {- goal  f a' == f a' -}


{- proof of transitivity -}

lemmaTransEq : {A : Set} → (a a' a''  : A) → a == a' → a' == a'' → a == a''
lemmaTransEq .a .a a refl refl = refl  {- goal a == a -}

{- we show now that for every List l there exist a Permutation per of l
   such that   insertion-sort l is the result of applying this Permutation to l

   first we need a lemma about insert
   
   the result of insert a l
   is the result of applying of taking a position in a :: l
   and applying fullexchange to it for that position.
-}

{- first we define a function which determines the position -}


{-  insert x l 
    inserts x at some position in l
    
    positionInsert   _≤_ x l     determines this position
-}

  

mutual
   positionInsert : {A : Set} → (A → A → Bool) → (x : A) → (l : List A) → Position l
   positionInsert _≤_ x [] = head
   positionInsert _≤_ x (a :: l) = positionInsertAux _≤_ x a l (x ≤ a)

   positionInsertAux : {A : Set} 
                       → (A → A → Bool) 
                       → (x a : A) 
                       → (l : List A) 
                       → (b : Bool) 
                       → Position (a :: l)   {- x :: a :: l -}
   positionInsertAux _≤_ x a l true  = head
   positionInsertAux _≤_ x a l false = tail (positionInsert _≤_ x l)


mutual
   lemmaInsert : {A : Set} → (_≤_ : A → A → Bool) 
                 → (x : A) → (l : List A)
                 → (insert _≤_ x l) == (insertAtPosition x l (positionInsert _≤_ x l))
   lemmaInsert _≤_ x []        = refl   {- goal type is    [ x ]  == [ x ] -}
   lemmaInsert _≤_ x (a :: l) = lemmaInsertaux _≤_ x a l (x ≤ a)
         

{- insert x (a :: l)    =  insertaux x a l (x ≤ a)  -}

   lemmaInsertaux : {A : Set} → (_≤_ : A → A → Bool) 
                    → (x a : A) → (l : List A) → (b : Bool)
                    → (insert-aux _≤_ x a l b) 
                      == (insertAtPosition x (a :: l) (positionInsertAux _≤_ x a l b))
   lemmaInsertaux _≤_ x a l true  = refl   {- type of goal is
                                              (x :: a :: l)     ==  (x :: a :: l) -}
   lemmaInsertaux _≤_ x a l false = lemmaEqList a (insert _≤_ x l)
                                      (insertAtPosition x l (positionInsert _≤_ x l))
                                      (lemmaInsert _≤_ x l)

                                           {- type of goal is 

Goal: (a :: insert _≤_ x l) ==
      (a :: insertAtPosition x l (positionInsert _≤_ x l))

lemmaInsert x l : (  insert _≤_ x l == insertAtPosition x l (positionInsert _≤_ x l) )
LemmaEqList ....
                : ( a :: insert _≤_ x l == a :: insertAtPosition x l (positionInsert _≤_ x l) )



which is the result of evaluating

insert-aux _≤_ x a l false ==
insertAtPosition x (a :: l) (positionInsertAux _≤_ x a l false)insert-aux _≤_ x a l false ==
insertAtPosition x (a :: l) (positionInsertAux _≤_ x a l false)


You can make something a goal by putting {! ! } around it

 -}
                   



{- insertionSortPermutation
  determines for a list the permutation applied to this list to obtain the 
  which is the result of applying insertionsort to it
-}
insertionSortPermutation : {A : Set} → (_≤_ : A → A → Bool) → (l : List A ) → Permutation l
insertionSortPermutation _≤_ []       = id
insertionSortPermutation _≤_ (x :: l) = consPermute 
                                          (insertionSortPermutation _≤_ l) 
                                          (positionInsert _≤_ x (permute l (insertionSortPermutation _≤_ l)))


theoremInsertionSort : {A : Set} → (_≤_ : A → A → Bool) → (l : List A)
                       → (insertion-sort _≤_ l) == (permute l  (insertionSortPermutation _≤_ l))
theoremInsertionSort {A} _≤_ []       = refl   {- goal is [] == [] -}
{- Reminder: 
   insertion-sort _≤_ (a :: l)  = insert _≤_ a (insertion-sort _≤_ l)
   Goal of this theorm is

insert _≤_ x (insertion-sort _≤_ l) ==
      insertAtPosition x (permute l (insertionSortPermutation _≤_ l))
      (positionInsert _≤_ x (permute l (insertionSortPermutation _≤_ l)))
-}
theoremInsertionSort {A} _≤_ (x :: l) = let 
                                      l1 : List A
                                      l1 = insertion-sort _≤_ l

                                      l2 : List A
                                      l2 = permute l (insertionSortPermutation _≤_ l)

                                      p : l1 == l2
                                      p = theoremInsertionSort _≤_ l
                                           {- l1 and l2 are equal by induction  hypothesis -}

                                      q : insert _≤_ x l1
                                          == insert _≤_ x l2
                                      q = lemmaEqfun (insert _≤_ x) l1 l2 p

                                      r : insert _≤_ x l2
                                          == insertAtPosition x l2 (positionInsert _≤_ x l2)
                                      r = lemmaInsert _≤_ x l2

                                      s : insert _≤_ x l1 == 
                                          insertAtPosition x l2 (positionInsert _≤_ x l2)
                                      s = lemmaTransEq 
                                            (insert _≤_ x l1)
                                            (insert _≤_ x l2)
                                            (insertAtPosition x l2 (positionInsert _≤_ x l2))
                                            q
                                            r
                                    in s



{-  example of let -}


a0  : ℕ 
a0  = let
        x : ℕ
        x = 3
         
        y : ℕ
        y = x + x
     in
        y + y


                    
   



{- Old code, no longer relevant -}

lemma2' : {A : Set} →  (_≤_ : A → A → Bool) → (x a : A) → (l : List A)
         → True ( x ≤ a )
         → True (≤Head _≤_ x l)  
         → True (≤Head _≤_ x (insert' _≤_ a  l))
lemma2' _≤_ x a [] p q = p
lemma2' _≤_ x a (a' :: l) p q = ifthenelseLemma1 
                                   (λ l' → True (≤Head _≤_ x l')) 
                                   (a ≤ a') 
                                   (a :: a' :: l) 
                                   (a' :: insert' _≤_ a l)   
                                   p 
                                   q
                        

{- goal of second line is
(≤Head _≤_ x
 (if a ≤ a' then a :: a' :: l else (a' :: insert' _≤_ a l))) 
-}

{-
ifthenelseLemma1 {!λ l → (≤Head _≤_ x l)!} (a ≤ a') (a :: a' :: l) (a' :: insert' _≤_ a l) {!!} {!!}
-}


Lemma2 : (n : ℕ) →  True (n ==ℕbool n)
Lemma2 zero    = triv
Lemma2 (suc n) = Lemma2 n


{- position to element takes a list and a position and returns the element at that 
   position 

   in case of the empty list we have no position, therefore the ()
   in case of a :: l  we have position head, for which we return a
                          and position (tail p) where p is a position of l
                                and return the element at position p in lx 
                
-}


Nonempty : {A : Set} → List A → Set
Nonempty [] = ⊥ 
Nonempty (a :: l) = ⊤ 

positionToElement : {A : Set} → (l : List A) → Position l → Maybe A
positionToElement [] p  = nothing
positionToElement (a :: l) head     = just a
positionToElement (a :: l) (tail q) = positionToElement l q


{- exchange takes an element of A and an element of List A
  and a position of l
  and creates a new list, where the new element is put at position l
  and the remaining elements stay unchanged
-}

exchange : {A : Set} → A → (l : List A) → Position l → List A
exchange a []       p = a :: []
exchange a (a' :: l) head     = a :: l
exchange a (a' :: l) (tail p) = a :: exchange a l p




