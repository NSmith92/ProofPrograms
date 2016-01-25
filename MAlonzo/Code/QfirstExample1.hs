{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction #-}
module MAlonzo.Code.QfirstExample1 where
import qualified MAlonzo.RTE
name1 = "firstExample1.\8469"
d1 = ()
 
data T1 a0 = C2
           | C3 a0
name2 = "firstExample1.\8469.zero"
name3 = "firstExample1.\8469.suc"
name4 = "firstExample1.\8868"
d4 = ()
 
data T4 = C5
name5 = "firstExample1.\8868.triv"
name6 = "firstExample1.\8869"
d6 = ()
 
data T6
name7 = "firstExample1._==_"
d7 (C2) (C2) = MAlonzo.RTE.mazCoerce d4
d7 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d_1_7 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
  where d_1_7 (C2) (C3 v0) = MAlonzo.RTE.mazCoerce d6
        d_1_7 v0 v1
          = MAlonzo.RTE.mazCoerce
              (d_2_7 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
        d_2_7 (C3 v0) (C2) = MAlonzo.RTE.mazCoerce d6
        d_2_7 v0 v1
          = MAlonzo.RTE.mazCoerce
              (d_3_7 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
        d_3_7 (C3 v0) (C3 v1)
          = MAlonzo.RTE.mazCoerce
              (d7 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
        d_3_7 v0 v1 = MAlonzo.RTE.mazIncompleteMatch name7
name12 = "firstExample1._+_"
d12 v0 (C2) = MAlonzo.RTE.mazCoerce v0
d12 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d_1_12 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
  where d_1_12 v0 (C3 v1)
          = MAlonzo.RTE.mazCoerce
              (C3
                 (MAlonzo.RTE.mazCoerce
                    (d12 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
        d_1_12 v0 v1 = MAlonzo.RTE.mazIncompleteMatch name12
name17 = "firstExample1.refl"
d17 (C2) = MAlonzo.RTE.mazCoerce C5
d17 v0 = MAlonzo.RTE.mazCoerce (d_1_17 (MAlonzo.RTE.mazCoerce v0))
  where d_1_17 (C3 v0)
          = MAlonzo.RTE.mazCoerce (d17 (MAlonzo.RTE.mazCoerce v0))
        d_1_17 v0 = MAlonzo.RTE.mazIncompleteMatch name17
name22 = "firstExample1.assoc+"
d22 v0 v1 (C2)
  = MAlonzo.RTE.mazCoerce
      (d17
         (MAlonzo.RTE.mazCoerce
            (d12 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
d22 v0 v1 v2
  = MAlonzo.RTE.mazCoerce
      (d_1_22 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2))
  where d_1_22 v0 v1 (C3 v2)
          = MAlonzo.RTE.mazCoerce
              (d22 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
                 (MAlonzo.RTE.mazCoerce v2))
        d_1_22 v0 v1 v2 = MAlonzo.RTE.mazIncompleteMatch name22
name28 = "firstExample1.A"
d28
  = error
      "MAlonzo Runtime Error: postulate evaluated: firstExample1.A"
name29 = "firstExample1.B"
d29
  = error
      "MAlonzo Runtime Error: postulate evaluated: firstExample1.B"
name32 = "firstExample1._\215_"
d32 a0 a1 = ()
 
data T32 a0 a1 = C35 a0 a1
name35 = "firstExample1._\215_.p"
name36 = "firstExample1.AxB"
d36 = ()
 
data T36 a0 a1 = C37 a0 a1
name37 = "firstExample1.AxB.p"
name38 = "firstExample1.p0'"
d38 (C37 v0 v1) = MAlonzo.RTE.mazCoerce v0
d38 v0 = MAlonzo.RTE.mazIncompleteMatch name38
name41 = "firstExample1.p1'"
d41 (C37 v0 v1) = MAlonzo.RTE.mazCoerce v1
d41 v0 = MAlonzo.RTE.mazIncompleteMatch name41
name46 = "firstExample1.p0"
d46 (C35 v0 v1) = MAlonzo.RTE.mazCoerce v0
d46 v0 = MAlonzo.RTE.mazIncompleteMatch name46
name49 = "firstExample1.Bool"
d49 = ()
 
data T49 = C50
         | C51
name50 = "firstExample1.Bool.true"
name51 = "firstExample1.Bool.false"
name52 = "firstExample1.\172"
d52 (C50) = MAlonzo.RTE.mazCoerce C51
d52 v0 = MAlonzo.RTE.mazCoerce (d_1_52 (MAlonzo.RTE.mazCoerce v0))
  where d_1_52 (C51) = MAlonzo.RTE.mazCoerce C50
        d_1_52 v0 = MAlonzo.RTE.mazIncompleteMatch name52
name55 = "firstExample1._or_"
d55 a0 a1 = ()
 
data T55 a0 = C58 a0
            | C59 a0
name58 = "firstExample1._or_.inl"
name59 = "firstExample1._or_.inr"
name63 = "firstExample1.LemIntroA"
d63 v0 v1 v2
  = MAlonzo.RTE.mazCoerce (C58 (MAlonzo.RTE.mazCoerce v2))
name68 = "firstExample1.LemIntroB"
d68 v0 v1 v2
  = MAlonzo.RTE.mazCoerce (C59 (MAlonzo.RTE.mazCoerce v2))
name76 = "firstExample1.D"
d76 v0 v1 v2 v3 v4 (C58 v5)
  = MAlonzo.RTE.mazCoerce (v3 (MAlonzo.RTE.mazCoerce v5))
d76 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (d_1_76 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5))
  where d_1_76 v0 v1 v2 v3 v4 (C59 v5)
          = MAlonzo.RTE.mazCoerce (v4 (MAlonzo.RTE.mazCoerce v5))
        d_1_76 v0 v1 v2 v3 v4 v5 = MAlonzo.RTE.mazIncompleteMatch name76
name88 = "firstExample1.D'"
d88 v0 v1 v2 v3 v4 (C58 v5)
  = MAlonzo.RTE.mazCoerce (v3 (MAlonzo.RTE.mazCoerce v5))
d88 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (d_1_88 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v4)
         (MAlonzo.RTE.mazCoerce v5))
  where d_1_88 v0 v1 v2 v3 v4 (C59 v5)
          = MAlonzo.RTE.mazCoerce (v4 (MAlonzo.RTE.mazCoerce v5))
        d_1_88 v0 v1 v2 v3 v4 v5 = MAlonzo.RTE.mazIncompleteMatch name88
name97 = "firstExample1.\928"
d97 a0 a1 = ()
 
newtype T97 a0 = C102 a0
name102 = "firstExample1.\928.\955'"
name107 = "firstExample1.Ap"
d107 (C102 v0) v1
  = MAlonzo.RTE.mazCoerce (v0 (MAlonzo.RTE.mazCoerce v1))
d107 v0 v1 = MAlonzo.RTE.mazIncompleteMatch name107
name112 = "firstExample1.\8704'"
d112 a0 a1 = ()
 
newtype T112 a0 = C116 a0
name116 = "firstExample1.\8704'.\955'"
name121 = "firstExample1.Ap'"
d121 (C116 v0) v1
  = MAlonzo.RTE.mazCoerce (v0 (MAlonzo.RTE.mazCoerce v1))
d121 v0 v1 = MAlonzo.RTE.mazIncompleteMatch name121
name126 = "firstExample1._\8835_"
d126 a0 a1 = ()
 
newtype T126 a0 = C129 a0
name129 = "firstExample1._\8835_.\955'"
name132 = "firstExample1.\8835Elim"
d132 (C129 v0) v1
  = MAlonzo.RTE.mazCoerce (v0 (MAlonzo.RTE.mazCoerce v1))
d132 v0 v1 = MAlonzo.RTE.mazIncompleteMatch name132
name137 = "firstExample1.\931'"
d137 a0 a1 = ()
 
data T137 a0 a1 = C141 a0 a1
name141 = "firstExample1.\931'._,_"
name149 = "firstExample1.\931'Elim"
d149 v0 v1 v2 (C141 v3 v4) v5
  = MAlonzo.RTE.mazCoerce
      (v5 (MAlonzo.RTE.mazCoerce v3) (MAlonzo.RTE.mazCoerce v4))
d149 v0 v1 v2 v3 v4 = MAlonzo.RTE.mazIncompleteMatch name149
name155 = "firstExample1.\8707'"
d155 a0 a1 = ()
 
data T155 a0 a1 = C159 a0 a1
name159 = "firstExample1.\8707'.\955'"
 
{-# RULES
"mazNatToInteger-mazIntegerToNat" forall x .
                                  mazNatToInteger (mazIntegerToNat x) = x
"mazIntegerToNat-mazNatToInteger" forall x .
                                  mazIntegerToNat (mazNatToInteger x) = x
 #-}
mazNatToInteger
  = \ x -> case x of { C2 -> 0 :: Integer; C3 x -> 1 + (mazNatToInteger (MAlonzo.RTE.mazCoerce x)) }
mazIntegerToNat
  = \ x -> if x <= (0 :: Integer) then C2 else C3 (MAlonzo.RTE.mazCoerce (mazIntegerToNat (x - 1)))
 
{-# RULES
"mazNatToInt-mazIntToNat" forall x . mazNatToInt (mazIntToNat x) =
                          x
"mazIntToNat-mazNatToInt" forall x . mazIntToNat (mazNatToInt x) =
                          x
 #-}
mazNatToInt
  = \ x -> case x of { C2 -> 0 :: Int; C3 x -> 1 + (mazNatToInt (MAlonzo.RTE.mazCoerce x)) }
mazIntToNat
  = \ x -> if x <= (0 :: Int) then C2 else C3 (MAlonzo.RTE.mazCoerce (mazIntToNat (x - 1)))