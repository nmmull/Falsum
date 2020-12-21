module Falsum

%default total

isNonempty : (a -> Type) -> Type
isNonempty {a} p = (x : a ** p x)

isUnboundedBelow : (a -> a -> Type) -> (a -> Type) -> Type
isUnboundedBelow {a} lessThan p = (x : a) -> p x -> (y : a ** (p y, lessThan y x))

isWellFounded : (a -> a -> Type) -> Type
isWellFounded {a} lessThan =
    -- Given a predicate for a subset,
    (p : a -> Type) ->
    -- a proof that the given subset is nonempty, and
    isNonempty p ->
    -- a proof that the given subset has no smallest element
    isUnboundedBelow lessThan p ->
    -- return a proof of void.
    Void

isTransitive : (a -> a -> Type) -> Type
isTransitive {a} lessThan =
    (x, y, z : a) ->
    lessThan x y ->
    lessThan y z ->
    lessThan x z

-- A type for well-quasi-orderings
--
-- A quasi-ordering is a set together with a transitive, irreflexive, binary
-- relation (https://ncatlab.org/nlab/show/quasiorder). Irreflexivity is a
-- consequence of well-foundedness.
Omega : Type
Omega =
    (  a : Type
    ** lessThan : (a -> a -> Type)
    ** (isWellFounded lessThan, isTransitive lessThan)
    )

-- A small interface for well-quasi-orderings. I don't fully understand why,
-- but this program doesn't work when Omega is a record type.
Set : Omega -> Type
Set (a ** _) = a

order : (wqo : Omega) -> Set wqo -> Set wqo -> Type
order (_ ** lessThan ** _) = lessThan

wfPrf : (wqo : Omega) -> isWellFounded (order wqo)
wfPrf (_ ** _ ** (prf, _)) = prf

transPrf : (wqo : Omega) -> isTransitive (order wqo)
transPrf (_ ** _ ** (_, prf)) = prf

-- A well-quasi-ordering restricted to the strict down set of one of its
-- elements
parameters (wqo : Omega, x : Set wqo)
    StrictDownSet : Type
    StrictDownSet = (y : Set wqo ** order wqo y x)

    ltSDS : StrictDownSet -> StrictDownSet -> Type
    ltSDS y z = order wqo (fst y) (fst z)

    transSDS : isTransitive ltSDS
    transSDS (u ** _) (v ** _) (w ** _) uLTv vLTw = transPrf wqo u v w uLTv vLTw

    parameters (p : StrictDownSet -> Type)
        liftP : Set wqo -> Type
        liftP y = (yLTx : order wqo y x ** p (y ** yLTx))

        liftNonempty : isNonempty p -> isNonempty liftP
        liftNonempty ((y ** yLTx) ** py) = (y ** (yLTx ** py))

        liftGetSmaller : isUnboundedBelow ltSDS p -> isUnboundedBelow (order wqo) liftP
        liftGetSmaller getSmaller y (yLTx ** py) with (getSmaller (y ** yLTx) py)
            | ((z ** zLTx) ** (pz, zLTx')) = (z ** ((zLTx ** pz), zLTx'))

        wfSDS_ : isNonempty p -> isUnboundedBelow ltSDS p -> Void
        wfSDS_ p1 p2 = wfPrf wqo liftP (liftNonempty p1) (liftGetSmaller p2)

    wfSDS : isWellFounded ltSDS
    wfSDS = wfSDS_ wqo x

    sdsAsOmega : Omega
    sdsAsOmega = (StrictDownSet ** ltSDS ** (wfSDS, transSDS))

record WqoMapping (wqo1 : Omega) (wqo2 : Omega) where
    constructor MkWqoMapping
    mapping : Set wqo1 -> Set wqo2
    upperBound : Set wqo2
    orderPreserved : (x, y : Set wqo1) -> order wqo1 x y -> order wqo2 (mapping x) (mapping y)
    bounded : (x : Set wqo1) -> order wqo2 (mapping x) upperBound

-- A binary relation for well-quasi-orderings
--
-- (a, <_a) < (b, <_b) if there is an order preserving function from a to b
-- whose image is contained in a strict down set of (b, <_b)
LTOmega : Omega -> Omega -> Type
LTOmega (a ** lta ** _) (b ** ltb ** _) =
    (  f : (a -> b)
    ** z : b
         -- f is order preserving
    ** ( (x : a) -> (y : a) -> lta x y -> ltb (f x) (f y)
         -- the image of f is in the strict down set of z
       , (x : a) -> ltb (f x) z
       )
    )

LTOmega2 : Omega -> Omega -> Type
LTOmega2 = WqoMapping

parameters (p : Omega -> Type, prf1 : isNonempty p, prf2 : isUnboundedBelow LTOmega2 p)
    wqo : Omega
    wqo = fst prf1

    wqo_is_in_P : p wqo
    wqo_is_in_P = snd prf1

    restrictPred : Set wqo -> Type
    -- there is a well-quasi-ordering in the given subset which is less than the
    -- strict down set of x
    restrictPred x = (wqo' : Omega ** (p wqo', LTOmega2 wqo' (sdsAsOmega wqo x)))

    below_wqo : Omega
    below_wqo = fst (prf2 wqo wqo_is_in_P)

    below_wqo_is_in_P : p below_wqo
    below_wqo_is_in_P = fst (snd (prf2 wqo wqo_is_in_P))

    below_wqo_is_less_than_wqo : LTOmega2 below_wqo wqo
    below_wqo_is_less_than_wqo = snd (snd (prf2 wqo wqo_is_in_P))

    mapping_below_wqo_to_wqo : Set below_wqo -> Set wqo
    mapping_below_wqo_to_wqo = mapping below_wqo_is_less_than_wqo

    below_below_wqo : Omega
    below_below_wqo = fst (prf2 below_wqo below_wqo_is_in_P)

    below_below_wqo_is_in_P : p below_below_wqo
    below_below_wqo_is_in_P = fst (snd (prf2 below_wqo below_wqo_is_in_P))

    below_below_wqo_is_less_than_below_wqo : LTOmega2 below_below_wqo below_wqo
    below_below_wqo_is_less_than_below_wqo = snd (snd (prf2 below_wqo below_wqo_is_in_P))

    mapping_below_below_wqo_to_below_wqo : Set below_below_wqo -> Set below_wqo
    mapping_below_below_wqo_to_below_wqo = mapping below_below_wqo_is_less_than_below_wqo

    upper_bound_in_wqo : Set wqo
    upper_bound_in_wqo = upperBound below_wqo_is_less_than_wqo

    upper_bound_for_below_below_wqo : Omega
    upper_bound_for_below_below_wqo = sdsAsOmega wqo upper_bound_in_wqo

    mapping_below_below_wqo_to_wqo : Set below_below_wqo -> Set wqo
    mapping_below_below_wqo_to_wqo = mapping_below_wqo_to_wqo . mapping_below_below_wqo_to_below_wqo

    less_than_upper_bound_in_wqo : (x : Set below_below_wqo) -> order wqo (mapping_below_below_wqo_to_wqo x) upper_bound_in_wqo
    less_than_upper_bound_in_wqo x = bounded below_wqo_is_less_than_wqo (mapping_below_below_wqo_to_below_wqo x)

    mapping_below_below_wqo_to_upper_bound : Set below_below_wqo -> Set upper_bound_for_below_below_wqo
    mapping_below_below_wqo_to_upper_bound x = (mapping_below_below_wqo_to_wqo x ** less_than_upper_bound_in_wqo x)

    upper_bound_in_upper_bound_for_below_below_wqo : Set upper_bound_for_below_below_wqo
    upper_bound_in_upper_bound_for_below_below_wqo =
        (mapping_below_wqo_to_wqo (upperBound below_below_wqo_is_less_than_below_wqo) ** bounded below_wqo_is_less_than_wqo (upperBound below_below_wqo_is_less_than_below_wqo))





    --embedding : Set wqo -> Set upper_bound_for_below_below_wqo
    --embedding =



    --below_below_wqoLTSDSofX : LTOmega2 below_below_wqo (sdsAsOmega wf

    -- (wqo1 ** (wqo1 is in P, wqo1 < wqo))
    -- (wqo2 ** (wqo2 is in P, wqo2 < wqo1))
    -- (y ** (wqo2 ** (wqo2 is in P, wqo2 < down set of y)))

LTOmegaIsWellFounded : isWellFounded LTOmega
LTOmegaIsWellFounded p ((a ** ltA ** (wfA, tA)) ** pwf) getSmaller =
    wfA p' nonTrivial' getSmaller' where
        wf : Omega
        wf = (a ** ltA ** (wfA, tA))
        p' : a -> Type
        p' x = (wf' : Omega ** (p wf', LTOmega wf' (sdsAsOmega wf x)))
        nonTrivial' with (getSmaller wf pwf)
            | ((b ** ltB ** (wfB, tB)) ** (pwf', (m ** ubInA ** (ordPrM, ubM)))) with (getSmaller (b ** ltB ** (wfB, tB)) pwf')
                | ((c ** ltC ** (wfC, tC)) ** (pwf'', (m' ** ubInB ** (ordPrM', ubM')))) =
                    (ubInA ** ((c ** ltC ** (wfC, tC)) ** (pwf'', cLTbelow))) where
                        cLTbelow : LTOmega (c ** ltC ** (wfC, tC)) (sdsAsOmega wf ubInA)
                        cLTbelow = (g ** ub ** (ordPrG, ubG)) where
                            g : c -> (q : a ** ltA q ubInA)
                            g v = (m (m' v) ** ubM (m' v))
                            ub : (q : a ** ltA q ubInA)
                            ub = (m ubInB ** ubM ubInB)
                            ordPrG u v uLTv = ordPrM (m' u) (m' v) (ordPrM' u v uLTv)
                            ubG u = ordPrM (m' u) ubInB (ubM' u)
        getSmaller' q ((b ** ltB ** (wfB, tB)) ** (pwf', (m ** (ub ** ubLTq) ** (ordPrM, ubM)))) with (getSmaller (b ** ltB ** (wfB, tB)) pwf')
            | ((c ** ltC ** (wfC, tC)) ** (pwf'', (m' ** ubInB ** (ordPrM', ubM')))) =
                (ub ** (((c ** ltC ** (wfC, tC)) ** (pwf'', cLTbelow)), ubLTq)) where
                    cLTbelow : LTOmega (c ** ltC ** (wfC, tC)) (sdsAsOmega wf ub)
                    cLTbelow = (g ** newUB ** (ordPrG, ubG)) where
                        g : c -> (q' : a ** ltA q' ub)
                        g v = (fst (m (m' v)) ** ubM (m' v))
                        newUB : (q' : a ** ltA q' ub)
                        newUB = (fst (m ubInB) ** ubM ubInB)
                        ordPrG u v uLTv = ordPrM (m' u) (m' v) (ordPrM' u v uLTv)
                        ubG u = ordPrM (m' u) ubInB (ubM' u)

LTOmegaIsTransitive : isTransitive LTOmega
LTOmegaIsTransitive
    (a ** ltA ** _)
    (b ** ltB ** _)
    (c ** ltC ** _)
    (fAB ** _ ** (ordPresAB, _))
    (fBC ** z ** (ordPresBC, uppBndBC)) =
        ((fBC . fAB) ** z ** (ordPresAC, uppBndAC)) where
            ordPresAC x y xLTy = ordPresBC (fAB x) (fAB y) (ordPresAB x y xLTy)
            uppBndAC x = uppBndBC (fAB x)

OmegaAsOmega : Omega
OmegaAsOmega = (Omega ** LTOmega ** (LTOmegaIsWellFounded, LTOmegaIsTransitive))

OmegaAsOmega2 : Omega
OmegaAsOmega2 = (Omega ** LTOmega2 ** (prf1, prf2)) where
    prf1 : isWellFounded LTOmega2
    prf1 = ?h1
    prf2 : isTransitive LTOmega2
    prf2 = ?h2

any_omega_less_than_Omega : (wqo : Omega) -> LTOmega2 wqo OmegaAsOmega2
any_omega_less_than_Omega wqo = MkWqoMapping (sdsAsOmega wqo) wqo order_preserved_prf bounded_by_wqo where
    order_preserved_prf x y xLTy = MkWqoMapping g (x ** xLTy) order_preserved_by_g bounded_by_x where
        g : StrictDownSet wqo x -> StrictDownSet wqo y
        g (z ** zLTx) = (z ** transPrf wqo z x y zLTx xLTy)
        order_preserved_by_g (u ** _) (v ** _) p = p
        bounded_by_x (u ** uLTx) = uLTx
    bounded_by_wqo x = MkWqoMapping g x order_preserved_by_g bounded_by_x where
        g : StrictDownSet wqo x -> Set wqo
        g (y ** _) = y
        order_preserved_by_g (y ** _) (z ** _) p = p
        bounded_by_x (y ** yLTx) = yLTx


anyLTOmega : (wf : Omega) -> LTOmega wf OmegaAsOmega
anyLTOmega (a ** ltA ** (wfA, transA)) = (sdsAsOmega wf ** wf ** (ordPreserved, ltWF)) where
        wf : Omega
        wf = (a ** ltA ** (wfA, transA))
        ordPreserved x y xLTy = (embed ** (x ** xLTy) ** (ordPres, ltX)) where
            embed : StrictDownSet wf x -> StrictDownSet wf y
            embed (z ** zLTx) = (z ** (transPrf wf z x y zLTx xLTy))
            ordPres (u ** _) (v ** _) p = p
            ltX (u ** uLTx) = uLTx
        ltWF x = (embed ** x ** (ordP, ltX)) where
            embed : StrictDownSet wf x -> a
            embed (y ** _) = y
            ordP (y ** _) (z ** _) p = p
            ltX (y ** yLTx) = yLTx

OmegaLTOmega : LTOmega OmegaAsOmega OmegaAsOmega
OmegaLTOmega = anyLTOmega OmegaAsOmega

falsum : Void
falsum =
    LTOmegaIsWellFounded
        (LTOmega OmegaAsOmega)
        (OmegaAsOmega ** OmegaLTOmega)
        (\_, oLTx => (OmegaAsOmega ** (OmegaLTOmega, oLTx)))
