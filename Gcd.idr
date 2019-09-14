module Gcd

import Syntax.PreorderReasoning

%default total

notLte : (x, y : Nat) -> (contra : LTE x y -> Void) -> y `LT` x
notLte Z Z contra = void $ contra LTEZero
notLte Z (S k) contra = absurd $ contra LTEZero
notLte (S k) Z contra = LTESucc LTEZero
notLte (S k) (S j) contra = LTESucc $ notLte k j (\pi_arg => contra $ LTESucc pi_arg)

ltWeaken : (x `LT` y) -> x `LTE` y
ltWeaken (LTESucc prev) = lteSuccRight prev

infix 6 .|.
data (.|.) : (d, n : Nat) -> Type where
  MkDivisor : (d, n, dn : Nat) -> (prf : d * dn = n) -> d .|. n

divSelf : (n : Nat) -> n .|. n
divSelf n = MkDivisor n n 1 $ multOneRightNeutral n

divZero : (n : Nat) -> n .|. 0
divZero n = MkDivisor n 0 0 $ multZeroRightZero n

multLtePlusOneLeft : (b, c : Nat) -> b * c `LTE` b * (1 + c)
multLtePlusOneLeft b c = rewrite multRightSuccPlus b c in
                         rewrite plusCommutative b (b * c) in
                         lteAddRight (b * c)

multPreservesLtRight : (a, b, c : Nat) -> (prf : a `LT` b) -> a `LT` (b * S c)
multPreservesLtRight a b Z prf = rewrite multOneRightNeutral b in prf
multPreservesLtRight a b (S c) prf = let rec = multPreservesLtRight a b c prf
                                         prf' = multLtePlusOneLeft b (S c)
                                     in rec `lteTransitive` prf'

Uninhabited (n `LT` n) where
  uninhabited (LTESucc prev) = uninhabited prev

divIsSmaller : (divPrf : d .|. S n) -> d `LTE` S n
divIsSmaller (MkDivisor d (S n) Z prf) = let sn_is_0 = sym (multZeroRightZero d) `trans` prf in absurd sn_is_0
divIsSmaller (MkDivisor d (S n) (S dn) prf) = case isLTE d (S n) of
                                                   Yes prf => prf
                                                   No contra => let sn_lt_d = notLte _ _ contra
                                                                    absPrf = multPreservesLtRight (S n) d dn sn_lt_d
                                                                    absPrf' = replace prf absPrf
                                                                in absurd absPrf'

plusMinusCancel : (m, n : Nat) -> (smaller : m `LTE` n) -> m + (n `minus` m) = n
plusMinusCancel Z n LTEZero = minusZeroRight n
plusMinusCancel (S m) (S n) (LTESucc prev) = cong $ plusMinusCancel m n prev

divCombine : (smaller : m `LTE` n) -> (prf_dm : d .|. m) -> (prf_d_n_minus_m : d .|. (n `minus` m)) -> d .|. n
divCombine smaller (MkDivisor d m dm prf_dm) (MkDivisor d (minus n m) dnm prf_d_n_minus_m) =
  let prf_dn = (d * (dm + dnm))       ={ multDistributesOverPlusRight d dm dnm }=
               (d * dm + d * dnm)     ={ cong {f = (+ d * dnm)} prf_dm }=
               (m + d * dnm)          ={ cong prf_d_n_minus_m }=
               (m + (n `minus` m))    ={ plusMinusCancel m n smaller }=
               n
               QED
  in MkDivisor d n (dm + dnm) prf_dn

divSubtract : (prf_dm : d .|. m) -> (prf_dn : d .|. n) -> d .|. (n `minus` m)
divSubtract (MkDivisor d m dm prf_dm) (MkDivisor d n dn prf_dn) =
  let prf_dn_dm = (d * (dn `minus` dm))       ={ multDistributesOverMinusRight d dn dm }=
                  ((d * dn) `minus` (d * dm)) ={ cong prf_dm }=
                  ((d * dn) `minus` m)        ={ cong {f = (`minus` m)} prf_dn }=
                  (n `minus` m)
                  QED
  in MkDivisor d (n `minus` m) (dn `minus` dm) prf_dn_dm

data CommonDivisor : (d, m, n : Nat) -> Type where
  MkCommonDivisor : (d, m, n : Nat) -> (prf_m : d .|. m) -> (prf_n : d .|. n) -> CommonDivisor d m n

commonDivRightZ : (n : Nat) -> CommonDivisor n 0 n
commonDivRightZ n = MkCommonDivisor n 0 n (divZero n) (divSelf n)

commonDivSym : CommonDivisor d m n -> CommonDivisor d n m
commonDivSym (MkCommonDivisor d m n prf_m prf_n) = MkCommonDivisor d n m prf_n prf_m

data GreatestDivisor : (d, m, n : Nat) -> Type where
  MkGD : (d, m, n : Nat) ->
         ((d' : Nat) -> CommonDivisor d' m n -> d' `LTE` d) ->
         GreatestDivisor d m n

greatestDivRightZ : (n : Nat) -> GreatestDivisor (S n) 0 (S n)
greatestDivRightZ n = MkGD (S n) 0 (S n) (prfFun n)
  where
    prfFun : (n, d' : Nat) -> CommonDivisor d' 0 (S n) -> LTE d' (S n)
    prfFun n d' (MkCommonDivisor d' Z (S n) _ prf_n) = divIsSmaller prf_n

greatestDivSym : GreatestDivisor d m n -> GreatestDivisor d n m
greatestDivSym (MkGD d m n f) = MkGD d n m $ \d', cd => f d' $ commonDivSym cd

record EuclidState where
  constructor MkES
  mES, nES : Nat
  mLess : mES `LTE` nES
  zeroLTnES : 0 `LT` nES

Sized EuclidState where
  size (MkES m n _ _) = m + n

sumDecreasing : (m, n : Nat) -> m `LT` n -> S m + (n `minus` (S m)) `LT` S m + n
sumDecreasing Z (S n) (LTESucc _) = rewrite minusZeroRight n in lteRefl
sumDecreasing (S m) (S n) (LTESucc prf) = let rec = sumDecreasing m n prf
                                          in rewrite sym $ plusSuccRightSucc m n in LTESucc (LTESucc $ lteSuccLeft rec)

data VerifiedEuclidStep : EuclidState -> Type where
  MkVES : (es : EuclidState) -> (d : Nat) ->
          (cdPrf : CommonDivisor d (mES es) (nES es)) ->
          (gPrf : GreatestDivisor d (mES es) (nES es)) ->
          VerifiedEuclidStep es

inductCommonDiv : (prf : m `LTE` n) -> CommonDivisor d m (n `minus` m) -> CommonDivisor d m n
inductCommonDiv prf (MkCommonDivisor d m (minus n m) prf_m prf_n) = MkCommonDivisor d m n prf_m $ divCombine prf prf_m prf_n

deductCommonDiv : CommonDivisor d m n -> CommonDivisor d m (n `minus` m)
deductCommonDiv (MkCommonDivisor d m n prf_m prf_n) = MkCommonDivisor d m (n `minus` m) prf_m $ divSubtract prf_m prf_n

inductGreatestDiv : GreatestDivisor d m (n `minus` m) -> GreatestDivisor d m n
inductGreatestDiv (MkGD d m (minus n m) f) = MkGD d m n f'
  where
    f' : (d' : Nat) -> CommonDivisor d' m n -> LTE d' d
    f' d' divPrf = f d' $ deductCommonDiv divPrf

inductPERight : VerifiedEuclidStep (MkES m (n `minus` m) _ _) -> VerifiedEuclidStep (MkES m n prf' _)
inductPERight {prf'} (MkVES (MkES m (n `minus` m) _ _) d cdPrf gPrf) = MkVES (MkES m n _ _) d (inductCommonDiv prf' cdPrf) (inductGreatestDiv gPrf)

inductPELeft : VerifiedEuclidStep (MkES (n `minus` m) m _ _) -> VerifiedEuclidStep (MkES m n prf' _)
inductPELeft {prf'} (MkVES (MkES (n `minus` m) m _ _) d cdPrf gPrf) = MkVES (MkES m n _ _) d (inductCommonDiv prf' $ commonDivSym cdPrf) (inductGreatestDiv $ greatestDivSym gPrf)

ltImpliesLtZero : (a `LT` b) -> 0 `LT` b
ltImpliesLtZero (LTESucc _) = LTESucc LTEZero

euclidStep : (es : EuclidState) -> (cont : (es' : EuclidState) -> es' `Smaller` es -> VerifiedEuclidStep es') -> VerifiedEuclidStep es
euclidStep (MkES Z (S n) mLess zeroLTnES) cont = MkVES (MkES Z (S n) mLess zeroLTnES) (S n) (commonDivRightZ (S n)) (greatestDivRightZ n)
euclidStep (MkES (S m) n mLess _) cont =
  case isLTE (S (S m)) (n `minus` S m) of
       Yes prf    => inductPERight $ cont (MkES _ _ (ltWeaken prf) (ltImpliesLtZero prf)) $ sumDecreasing _ _ mLess
       No contra  => let LTESucc prf = notLte _ _ contra
                         smallerPrf = sumDecreasing _ _ mLess
                         rec = cont (MkES _ _ prf (LTESucc LTEZero)) (rewrite plusCommutative (n `minus` S m) (S m) in smallerPrf)
                     in inductPELeft rec

euclid' : (es : EuclidState) -> VerifiedEuclidStep es
euclid' = sizeInd euclidStep

data Gcd : (d, m, n : Nat) -> Type where
  MkGcd : (d, m, n : Nat) ->
          (commonDivPrf : CommonDivisor d m n) ->
          (greatestPrf : GreatestDivisor d m n) ->
          Gcd d m n

gcdSym : Gcd d m n -> Gcd d n m
gcdSym (MkGcd d m n commonDivPrf greatestPrf) = MkGcd d n m (commonDivSym commonDivPrf) (greatestDivSym greatestPrf)

verifiedGcdSym : (d ** Gcd d m n) -> (d ** Gcd d n m)
verifiedGcdSym (d ** gcdPrf) = (d ** gcdSym gcdPrf)

deduceLte : Either (0 `LT` m) (0 `LT` n) -> m `LTE` n -> 0 `LT` n
deduceLte (Left l) m_lte_n = l `lteTransitive` m_lte_n
deduceLte (Right r) _ = r

euclid : (m, n : Nat) -> Either (0 `LT` m) (0 `LT` n) -> (d ** Gcd d m n)
euclid m n eitherNonZero =
  case isLTE m n of
       Yes prf   => let es = MkES m n prf (deduceLte eitherNonZero prf)
                        eqPrf = the (m = mES es) Refl
                    in unwrap es $ euclid' es
       No contra => let prf = ltWeaken $ notLte _ _ contra
                        es = MkES n m prf (deduceLte (mirror eitherNonZero) prf)
                    in verifiedGcdSym $ unwrap es $ euclid' es
  where
    unwrap : (es : EuclidState) -> VerifiedEuclidStep es -> (d ** Gcd d (mES es) (nES es))
    unwrap es (MkVES es d cdPrf gPrf) = (d ** MkGcd d (mES es) (nES es) cdPrf gPrf)
