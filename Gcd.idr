module Gcd

import Syntax.PreorderReasoning

%default total

infix 6 .|.
data (.|.) : (d, n : Nat) -> Type where
  MkDivisor : (d, n, dn : Nat) -> (prf : d * dn = n) -> d .|. n

divSelf : (n : Nat) -> n .|. n
divSelf n = MkDivisor n n 1 $ multOneRightNeutral n

divZero : (n : Nat) -> n .|. 0
divZero n = MkDivisor n 0 0 $ multZeroRightZero n

plusMinusCancel : (m, n : Nat) -> (smaller : m `LTE` n) -> m + (n `minus` m) = n
plusMinusCancel Z n LTEZero = minusZeroRight n
plusMinusCancel (S m) (S n) (LTESucc prev) = cong $ plusMinusCancel m n prev

divCombine : (smaller : m `LTE` n) -> (prf_dm : d .|. m) -> (prf_d_n_minus_m : d .|. (n `minus` m)) -> d .|. n
divCombine smaller (MkDivisor d m dm prf_dm) (MkDivisor d (minus n m) dnm prf_d_n_minus_m) =
  let prf_dn = (d * (dm + dnm))       ={ multDistributesOverPlusRight d dm dnm }=
               (d * dm + d * dnm)     ={ cong {f = \t => t + d * dnm} prf_dm }=
               (m + d * dnm)          ={ cong prf_d_n_minus_m }=
               (m + (n `minus` m))    ={ plusMinusCancel m n smaller }=
               n
               QED
  in MkDivisor d n (dm + dnm) prf_dn

data CommonDivisor : (d, m, n : Nat) -> Type where
  MkCommonDivisor : (d, m, n : Nat) -> (prf_m : d .|. m) -> (prf_n : d .|. n) -> CommonDivisor d m n

commonDivRightZ : (n : Nat) -> CommonDivisor n 0 n
commonDivRightZ n = MkCommonDivisor n 0 n (divZero n) (divSelf n)

commonDivSym : CommonDivisor d m n -> CommonDivisor d n m
commonDivSym (MkCommonDivisor d m n prf_m prf_n) = MkCommonDivisor d n m prf_n prf_m

data NoGreaterDivisor : (d, n, m : Nat) -> Type where
  MkNgd : (d, n, m : Nat) ->
          (contra : (d' : Nat) -> (d `LT` d') -> CommonDivisor d' n m -> Void) ->
          NoGreaterDivisor d n m

data Gcd : (d, n, m : Nat) -> Type where
  MkGcd : (d, n, m : Nat) ->
          (commonDivPrf : CommonDivisor d n m) ->
          (noGreater : NoGreaterDivisor d n m) ->
          Gcd d n m

notLte : (x, y : Nat) -> (contra : LTE x y -> Void) -> LTE y x
notLte Z Z contra = LTEZero
notLte Z (S k) contra = absurd $ contra LTEZero
notLte (S k) Z contra = LTEZero
notLte (S k) (S j) contra = LTESucc $ notLte k j (\pi_arg => contra $ LTESucc pi_arg)

record EuclidState where
  constructor MkES
  mES, nES : Nat
  mLess : mES `LTE` nES

Sized EuclidState where
  size (MkES m n _) = m + n

sumDecreasing : (m, n : Nat) -> m `LT` n -> S m + (n `minus` (S m)) `LT` S m + n
sumDecreasing Z (S n) (LTESucc _) = rewrite minusZeroRight n in lteRefl
sumDecreasing (S m) (S n) (LTESucc prf) = let rec = sumDecreasing m n prf
                                          in rewrite sym $ plusSuccRightSucc m n in LTESucc (LTESucc $ lteSuccLeft rec)

data ProvenEuclidStep : EuclidState -> Type where
  MkPE : (es : EuclidState) -> (d : Nat) -> (prf : CommonDivisor d (mES es) (nES es)) -> ProvenEuclidStep es

inductCommonDiv : (prf : m `LTE` n) -> CommonDivisor d m (n `minus` m) -> CommonDivisor d m n
inductCommonDiv prf (MkCommonDivisor d m (minus n m) prf_m prf_n) = MkCommonDivisor d m n prf_m $ divCombine prf prf_m prf_n

inductPERight : ProvenEuclidStep (MkES m (n `minus` m) prf) -> ProvenEuclidStep (MkES m n prf')
inductPERight {prf'} (MkPE (MkES m (n `minus` m) prf) d cdPrf) = MkPE (MkES m n _) d $ inductCommonDiv prf' cdPrf

inductPELeft : ProvenEuclidStep (MkES (n `minus` m) m prf) -> ProvenEuclidStep (MkES m n prf')
inductPELeft {prf'} (MkPE (MkES (n `minus` m) m prf) d cdPrf) = MkPE (MkES m n _) d $ inductCommonDiv prf' $ commonDivSym cdPrf

euclidStep : (es : EuclidState) -> (cont : (es' : EuclidState) -> es' `Smaller` es -> ProvenEuclidStep es') -> ProvenEuclidStep es
euclidStep (MkES Z n mLess) cont = MkPE (MkES Z n mLess) n (commonDivRightZ n)
euclidStep (MkES (S m) n mLess) cont =
  case isLTE (S m) (n `minus` S m) of
       Yes prf    => inductPERight $ cont (MkES _ _ prf) $ sumDecreasing _ _ mLess
       No contra  => let prf = notLte _ _ contra
                         smallerPrf = sumDecreasing _ _ mLess
                         rec = cont (MkES _ _ prf) (rewrite plusCommutative (n `minus` S m) (S m) in smallerPrf)
                     in inductPELeft rec

euclid' : (es : EuclidState) -> ProvenEuclidStep es
euclid' = sizeInd euclidStep

{-
euclid : (m, n : Nat) -> ProvenEuclidStep m n
euclid m n = case isLTE m n of
                  Yes prf   => euclid' m n $ MkES m n prf
                  No contra => euclid' m n $ MkES n m $ notLte _ _ contra
                  -}
