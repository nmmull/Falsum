module Falsum2

%default total

-- Some generally useful predicates

tran : (a -> a -> Type) -> Type
tran {a} f = (x, y, z : a) -> f x y -> f y z -> f x z

nempty : (a -> Type) -> Type
nempty {a} p = (x : a ** p x)

no_lb : (a -> a -> Type) -> (a -> Type) -> Type
no_lb {a} f p = (x : a) -> p x -> (y : a ** (p y, f y x))

wf : (a -> a -> Type) -> Type
wf {a} f = (p : a -> Type) -> nempty p -> no_lb f p -> Void

-- A type for well-quasi-orderings with a small interface
--
-- I don't fully understand why, but this program doesn't work when Omega is a
-- record type.
--
-- A quasi-ordering is a set together with a transitive, irreflexive, binary
-- relation (https://ncatlab.org/nlab/show/quasiorder). Irreflexivity is a
-- consequence of well-foundedness.

Omega : Type
Omega = (a : Type ** f : (a -> a -> Type) ** (tran f, wf f))

Set : Omega -> Type
Set (a ** _) = a

ltn : (wqo : Omega) -> Set wqo -> Set wqo -> Type
ltn (_ ** f ** _) = f

tran_prf : (wqo : Omega) -> tran (ltn wqo)
tran_prf (_ ** _ ** (prf, _)) = prf

wf_prf : (wqo : Omega) -> wf (ltn wqo)
wf_prf (_ ** _ ** (_, prf)) = prf

-- A binary relation for well-quasi-orderings with a small interface.
--
-- (a, <_a) < (b, <_b) if there is an order preserving function from a to b
-- whose image is contained in a strict down set of (b, <_b)

LTN : Omega -> Omega -> Type
LTN (a ** ltn_a ** _) (b ** ltn_b ** _) =
    (  f : (a -> b)
    ** z : b
         -- f is order preserving
    ** ( (x, y : a) -> ltn_a x y -> ltn_b (f x) (f y)
         -- the image of f is in the strict down set of z
       , (x : a) -> ltn_b (f x) z
       )
    )

m : LTN a b -> Set a -> Set b
m (f ** z ** _) = ?h
--
-- ub : LTN a b -> Set b
-- ub (_ ** z ** _) = z
--
-- ord_pres : (l : LTN a b) -> (x, y : Set a) -> ltn a x y -> ltn b (m l x) (m l y)
-- ord_pres (_ ** _ ** (prf, _)) = prf
--
-- bnd : (l: LTN a b) -> (x : Set a) -> ltn b (m l x) (ub l)
-- bnd (_ ** _ ** (_, prf)) = prf
--
-- tran_LTN : tran LTN
-- tran_LTN a b c a_ltn_b b_ltn_c = (m_ac ** ub_ac ** (ord_pres_ac, bnd_ac)) where
--     m_ac : Set a -> Set c
--     m_ac = (m b_ltn_c) . (m a_ltn_b)
--     ub_ac : Set c
--     ub_ac = ub b_ltn_c
--     ord_pres_ac x y x_ltn_y =
--         ord_pres b_ltn_c (m a_ltn_b x) (m a_ltn_b y)
--             (ord_pres a_ltn_b x y x_ltn_y)
--     bnd_ac x = bnd b_ltn_c (m a_ltn_b x)

-- A well-quasi-ordering restricted to the strict down set of one of its
-- elements
sds : (wqo : Omega) -> Set wqo -> Omega
sds wqo x = (SDS ** ltn_sds ** (tran_sds, wf_sds)) where
    SDS : Type
    SDS = (y : Set wqo ** ltn wqo y x)
    ltn_sds : SDS -> SDS -> Type
    ltn_sds y z = ltn wqo (fst y) (fst z)
    tran_sds (u ** _) (v ** _) (w ** _) u_ltn_v v_ltn_w =
        tran_prf wqo u v w u_ltn_v v_ltn_w
    wf_sds p nempty_prf no_lb_prf =
        wf_prf wqo lift_p lift_nempty lift_no_lb where
            lift_p : Set wqo -> Type
            lift_p u = (u_ltn_x : ltn wqo u x ** p (u ** u_ltn_x))
            lift_nempty with (nempty_prf)
                | ((u ** u_ltn_x) ** pu') = (u ** (u_ltn_x ** pu'))
            lift_no_lb u (u_ltn_x ** pu') with (no_lb_prf (u ** u_ltn_x) pu')
                | ((v ** v_ltn_x) ** (pv', v_ltn_u)) =
                    (v ** ((v_ltn_x ** pv'), v_ltn_u))

-- namespace wf_LTN_prf
--     parameters (p : Omega -> Type, nempty_prf : nempty p, no_lb_prf : no_lb LTN p)
--         c : Omega
--         c = fst nempty_prf
--
--         p' : Set c -> Type
--         p' x = (wqo : Omega ** (p wqo, LTN wqo (sds c x)))
--
--         c_in_p : p c
--         c_in_p = snd nempty_prf
--
--         b : Omega
--         b = fst (no_lb_prf c c_in_p)
--
--         b_in_p : p b
--         b_in_p = fst (snd (no_lb_prf c c_in_p))
--
--         b_ltn_c : LTN b c
--         b_ltn_c = snd (snd (no_lb_prf c c_in_p))
--
--         ub_c : Set c
--         ub_c = ub b_ltn_c
--
--         nempty_prf' : nempty p'
--         nempty_prf' with (no_lb_prf b b_in_p)
--             | ((set_a ** ltn_a ** (tran_prf_a, wf_prf_a)) ** (a_in_p, a_ltn_b)) = ?h

{-

        f : Set a -> Set (sds c ub_c)
        f u = (m b_ltn_c (m a_ltn_b u) ** bnd b_ltn_c (m a_ltn_b u))

        upp : Set (sds c ub_c)
        upp = (m b_ltn_c (ub a_ltn_b) ** bnd b_ltn_c (ub a_ltn_b))

        ord_pres_f : (u, v : Set a) -> ltn a u v -> ltn (sds c ub_c) (f u) (f v)
        ord_pres_f u v u_ltn_v = ord_pres b_ltn_c (m a_ltn_b u) (m a_ltn_b v) (ord_pres a_ltn_b u v u_ltn_v)

        bnd_upp : (u : Set a) -> ltn (sds c ub_c) (f u) upp
        bnd_upp u = ord_pres b_ltn_c (m a_ltn_b u) (ub a_ltn_b) (bnd a_ltn_b u)

        a_ltn_sds_ub_c : LTN a (sds c ub_c)
        a_ltn_sds_ub_c = ?h

        -- nempty_prf' : nempty p'
        -- nempty_prf' = (ub_c ** (a ** (a_in_p, a_ltn_sds_ub_c))) where
        --     a_ltn_sds_ub_c : LTN a (sds c ub_c)
        --     a_ltn_sds_ub_c = LTN_prf g upp ord_pres_g bnd_upp where
        --         g : Set a -> Set (sds c ub_c)
        --         g u = (m b_ltn_c (m a_ltn_b u) ** bnd b_ltn_c (m a_ltn_b u))
        --         upp : Set (sds c ub_c)
        --         upp = (m b_ltn_c (ub a_ltn_b) ** bnd b_ltn_c (ub a_ltn_b))
        --         ord_pres_g u v u_ltn_v = ord_pres b_ltn_c (m a_ltn_b u) (m a_ltn_b v) (ord_pres a_ltn_b u v u_ltn_v)
        --         bnd_upp u = ord_pres b_ltn_c (m a_ltn_b u) (ub a_ltn_b) (bnd a_ltn_b u)
        -}
