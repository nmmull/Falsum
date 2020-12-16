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
    -- we get a proof of void.
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
