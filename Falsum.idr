module Falsum

%default total

isWellFounded : (a -> a -> Type) -> Type
isWellFounded {a} lessThan =
    (p : a -> Type) ->
    (x : a ** p x) ->
    ((x : a) -> p x -> (y : a ** (p y, lessThan y x))) ->
    Void

isTransitive : (a -> a -> Type) -> Type
isTransitive {a} lessThan =
    (x, y, z : a) ->
    lessThan x y ->
    lessThan y z ->
    lessThan x z

Omega : Type
Omega =
    (  a : Type
    ** lessThan : (a -> a -> Type)
    ** (isWellFounded lessThan, isTransitive lessThan)
    )

LTOmega : Omega -> Omega -> Type
LTOmega (a ** lta ** _) (b ** ltb ** _) =
    (  f : (a -> b)
    ** z : b
    ** ( (x : a) -> (y : a) -> lta x y -> ltb (f x) (f y)
       , (x : a) -> ltb (f x) z
       )
    )

below : (wf : Omega) -> fst wf -> Omega
below (a ** ltA ** (wfA, transA)) x = (BelowX ** lessThan ** (wfPrf, transPrf)) where
    BelowX : Type
    BelowX = (y : a ** ltA y x)
    lessThan : BelowX -> BelowX -> Type
    lessThan y z = ltA (fst y) (fst z)
    wfPrf p nonTrivial getSmaller = wfA p' nonTrivial' getSmaller' where
        p' : a -> Type
        p' y = (yLTx : (ltA y x) ** p (y ** yLTx))
        nonTrivial' with (nonTrivial)
            | ((u ** uLTx) ** pu) = (u ** (uLTx ** pu))
        getSmaller' v (vLTx ** pv) with (getSmaller (v ** vLTx) pv)
            | ((w ** wLTx) ** (pw, wLTx')) = (w ** ((wLTx ** pw), wLTx'))
    transPrf (u ** _) (v ** _) (w ** _) uLTv vLTw = transA u v w uLTv vLTw

OmegaWellFounded : isWellFounded LTOmega
OmegaWellFounded p ((a ** ltA ** (wfA, tA)) ** pwf) getSmaller =
    wfA p' nonTrivial' getSmaller' where
        wf : Omega
        wf = (a ** ltA ** (wfA, tA))
        p' : a -> Type
        p' x = (wf' : Omega ** (p wf', LTOmega wf' (below wf x)))
        nonTrivial' with (getSmaller wf pwf)
            | ((b ** ltB ** (wfB, tB)) ** (pwf', (m ** ubInA ** (ordPrM, ubM)))) with (getSmaller (b ** ltB ** (wfB, tB)) pwf')
                | ((c ** ltC ** (wfC, tC)) ** (pwf'', (m' ** ubInB ** (ordPrM', ubM')))) =
                    (ubInA ** ((c ** ltC ** (wfC, tC)) ** (pwf'', cLTbelow))) where
                        cLTbelow : LTOmega (c ** ltC ** (wfC, tC)) (below wf ubInA)
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
                    cLTbelow : LTOmega (c ** ltC ** (wfC, tC)) (below wf ub)
                    cLTbelow = (g ** newUB ** (ordPrG, ubG)) where
                        g : c -> (q' : a ** ltA q' ub)
                        g v = (fst (m (m' v)) ** ubM (m' v))
                        newUB : (q' : a ** ltA q' ub)
                        newUB = (fst (m ubInB) ** ubM ubInB)
                        ordPrG u v uLTv = ordPrM (m' u) (m' v) (ordPrM' u v uLTv)
                        ubG u = ordPrM (m' u) ubInB (ubM' u)

OmegaTransitive : isTransitive LTOmega
OmegaTransitive
    (a ** ltA ** _)
    (b ** ltB ** _)
    (c ** ltC ** _)
    (fab ** _ ** (prf1ab, prf2ab))
    (fbc ** z ** (prf1bc, prf2bc)) =
        ((fbc . fab) ** z ** (prf1, prf2)) where
            prf1 x y xLTy = prf1bc (fab x) (fab y) (prf1ab x y xLTy)
            prf2 x = prf2bc (fab x)

OmegaAsOmega : Omega
OmegaAsOmega = (Omega ** LTOmega ** (OmegaWellFounded, OmegaTransitive))

anyLTOmega : (wf : Omega) -> LTOmega wf OmegaAsOmega
anyLTOmega (a ** ltA ** (wfA, transA)) = (below wf ** wf ** (ordPreserved, upperBound)) where
        wf : Omega
        wf = (a ** ltA ** (wfA, transA))
        ordPreserved x y xLTy = (g ** (x ** xLTy) ** (ordP, uB)) where
            g : (z : a ** ltA z x) -> (z : a ** ltA z y)
            g (z ** zLTx) = (z ** (transA z x y zLTx xLTy))
            ordP (u ** _) (v ** _) p = p
            uB (u ** uLTx) = uLTx
        upperBound x = (g ** x ** (ordP, uB)) where
            g : (z : a ** ltA z x) -> a
            g (z ** _) = z
            ordP (u ** _) (v ** _) p = p
            uB (u ** uLTx) = uLTx

OmegaLTOmega : LTOmega OmegaAsOmega OmegaAsOmega
OmegaLTOmega = anyLTOmega OmegaAsOmega

falsum : Void
falsum =
    OmegaWellFounded
        (LTOmega OmegaAsOmega)
        (OmegaAsOmega ** OmegaLTOmega)
        (\_, oLTx => (OmegaAsOmega ** (OmegaLTOmega, oLTx)))
