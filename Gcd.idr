module Gcd

%default total

infix 6 .|.
data (.|.) : (d, n : Nat) -> Type where
  MkDivisor : (d, n, dn : Nat) -> (prf : d * dn = n) -> d .|. n

data CommonDivisor : (d, n, m : Nat) -> Type where
  MkCommonDivisor : (d, n, m : Nat) -> (prf_n : d .|. n) -> (prf_m : d .|. m) -> CommonDivisor d n m

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

data EuclidState : Type where
  MkES : (m, n : Nat) -> (mLess : m `LTE` n) -> EuclidState

Sized EuclidState where
  size (MkES m n _) = m + n

sumDecreasing : (m, n : Nat) -> m `LT` n -> S m + (n `minus` (S m)) `LT` S m + n
sumDecreasing Z (S n) (LTESucc _) = rewrite minusZeroRight n in lteRefl
sumDecreasing (S m) (S n) (LTESucc prf) = let rec = sumDecreasing m n prf
                                          in rewrite sym $ plusSuccRightSucc m n in LTESucc (LTESucc $ lteSuccLeft rec)

euclidStep : (es : EuclidState) -> (cont : (es' : EuclidState) -> es' `Smaller` es -> Nat) -> Nat
euclidStep (MkES Z n _) cont = n
euclidStep (MkES (S m) n mLess) cont with (isLTE (S m) (n `minus` (S m)))
  | Yes prf = cont (MkES _ _ prf) $ sumDecreasing _ _ mLess
  | No contra = let prf = notLte _ _ contra
                    smallerPrf = sumDecreasing _ _ mLess
                in cont (MkES _ _ prf) (rewrite plusCommutative (n - S m) (S m) in smallerPrf)

euclid' : EuclidState -> Nat
euclid' = sizeRec euclidStep

euclid : (m, n : Nat) -> Nat
euclid m n with (isLTE m n)
  | Yes prf = euclid' $ MkES m n prf
  | No contra = euclid' $ MkES n m $ notLte _ _ contra
