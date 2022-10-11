module Falsum

%default total

--
-- Some generally useful predicates: transitivity, nonemptiness, nonexistence of
-- a lower bound, well-foundedness
--
tran : (a -> a -> Type) -> Type
tran {a} f = (x, y, z : a) -> f x y -> f y z -> f x z

nempty : (a -> Type) -> Type
nempty {a} p = (x : a ** p x)

no_lb : (a -> a -> Type) -> (a -> Type) -> Type
no_lb {a} f p = (x : a) -> p x -> (y : a ** (p y, f y x))

wf : (a -> a -> Type) -> Type
wf {a} f = (p : a -> Type) -> nempty p -> no_lb f p -> Void

--
-- A type for well-quasi-orderings with a small interface
--
-- I don't fully understand why, but this program doesn't work when `Omega` is a
-- record type.
--
-- A quasi-ordering is a set together with a transitive, irreflexive, binary
-- relation (https://ncatlab.org/nlab/show/quasiorder). Irreflexivity is a
-- consequence of well-foundedness.
--
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

--
-- A binary relation for well-quasi-orderings
--
-- (a, <_a) < (b, <_b) if there is an order preserving function from a to b
-- whose image is contained in a strict down set
--
-- NOTE: this program, as in this particular case, seems to depend heavily on
-- the ability to pattern match of elements of `Omega`. I don't fully understand
-- this, but as an example, this definition does not work without pattern matching
-- and the ways it breaks are quite strange.
--
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

--
-- A simple proof that `LTN` is transitive
--
-- The first three pattern matches are bizzare, I don't know why they're
-- necessary (beyond that they are required by the type checker). These sorts of
-- matches appear throughout the program
--
tran_prf_LTN : tran LTN
tran_prf_LTN (_ ** _ ** _) (_ ** _ ** _) (_ ** _ ** _)
    (f_ab ** _ ** (ord_ab, _))
    (f_bc ** z ** (ord_bc, ub_bc)) =
        ((f_bc . f_ab) ** z ** (ord_ac, ub_ac)) where
            -- the composition of order preserving functions is order preserving
            ord_ac x y x_ltn_y = ord_bc (f_ab x) (f_ab y) (ord_ab x y x_ltn_y)

            -- upper bound in third argument remains an upper bound for the
            -- composition
            ub_ac x = ub_bc (f_ab x)

--
-- A well-quasi-ordering restricted to the strict down set of one of its
-- elements
--
sds : (wqo : Omega) -> Set wqo -> Omega
sds wqo x = (SDS ** ltn_sds ** (tran_sds, wf_sds)) where
    -- the elements less than `x`
    SDS : Type
    SDS = (y : Set wqo ** ltn wqo y x)

    -- the order for `wqo` restricted to the strict down set of `x`
    ltn_sds : SDS -> SDS -> Type
    ltn_sds y z = ltn wqo (fst y) (fst z)

    -- by construction, the transitivity proof is pretty much the one for `wqo`
    tran_sds (u ** _) (v ** _) (w ** _) u_ltn_v v_ltn_w =
        tran_prf wqo u v w u_ltn_v v_ltn_w

    -- we get a term of type `Void` by lifting `p` to `wqo` and using the
    -- well-foundedness proof for `wqo`
    wf_sds p nempty_prf no_lb_prf =
        wf_prf wqo lift_p lift_nempty lift_no_lb where
            -- `u` is in `lift_p` if it is in `p` (and the strict down set of `x`)
            lift_p : Set wqo -> Type
            lift_p u = (u_ltn_x : ltn wqo u x ** p (u ** u_ltn_x))

            -- naturally these proofs just move around parentheses
            lift_nempty with (nempty_prf)
                | ((u ** u_ltn_x) ** pu') = (u ** (u_ltn_x ** pu'))
            lift_no_lb u (u_ltn_x ** pu') with (no_lb_prf (u ** u_ltn_x) pu')
                | ((v ** v_ltn_x) ** (pv', v_ltn_u)) =
                    (v ** ((v_ltn_x ** pv'), v_ltn_u))
--
-- A proof that `LTN` is well-founded
--
wf_prf_LTN : wf LTN
wf_prf_LTN p ((set_a ** ltn_a ** (tran_prf_a, wf_prf_a)) ** p_a) no_lb_prf =
    wf_prf a p' nempty_prf' no_lb_prf' where
        -- a convenient renaming of the nonemptiness proof witness
        a : Omega
        a = (set_a ** ltn_a ** (tran_prf_a, wf_prf_a))

        -- `x` is in `p'`` if there is a well-quasi-ordering in `p` that is less
        -- than the strict down set of `x` (as a well-quasi-ordering)
        p' : Set a -> Type
        p' x = (wqo : Omega ** (p wqo, LTN wqo (sds a x)))

        --
        -- PROOF:
        -- By the no-lower-bound proof (`no_lb_prf`), there is a sequence of
        -- orderings in `p` of the form (c, <_c) < (b, <_b) < (a, <_a).
        -- Specifically, there is a an order preserving function f from c to b
        -- and an element z of b such that f maps c into the strict down set of
        -- z and, likewise, an order preserving function f' from b to a and an
        -- element z' of a such that f' maps b into the strict down set of z'.
        --
        -- So (c, <_c) embeds into a strict down set in the strict down set of
        -- z' via the composition (f' . f). In other words, (c, <_c) is less than
        -- the strict down set of z' in (a, <_a). Therefore, z' is in p'.
        --
        nempty_prf' with (no_lb_prf a p_a)
                 -- the ordering (call it b) in `p`, less than `a`, guaranteed
                 --by the no-lower-bound proof
            | (  (set_b ** ltn_b ** (tran_prf_b, wf_prf_b))
              ** (p_b, (m_ba ** ub_ba ** (ord_pres_prf_ba, ub_prf_ba)))
              )
              with (no_lb_prf (set_b ** ltn_b ** (tran_prf_b, wf_prf_b)) p_b)
                     -- the ordering `c` in `p`, less than `b`, guaranteed by
                     -- the no-lower-bound proof
                | (  (set_c ** ltn_c ** (trans_prf_c, wf_prf_c))
                  ** (p_c, (m_cb ** ub_cb ** (ord_pres_prf_cb, ub_prf_cb)))
                  )
                    -- `c` is in `p` and is less than the strict down set of
                    -- `ub_ba`
                  = (ub_ba ** c ** (p_c, c_ltn_sds_ub_ba)) where
                      -- a convenient renaming of the last ordering
                      c : Omega
                      c = (set_c ** ltn_c ** (trans_prf_c, wf_prf_c))

                      -- `c` is less than the strict down set of `ub_ba`
                      c_ltn_sds_ub_ba : LTN c (sds a ub_ba)
                      c_ltn_sds_ub_ba = (g ** ub ** (ord_pres_prf, ub_prf)) where
                          -- composition of embeddings with auxiliary bound proof
                          g : Set c -> Set (sds a ub_ba)
                          g v = (m_ba (m_cb v) ** ub_prf_ba (m_cb v))

                          -- upper bound on image of `g` is the image of `ub_cb`
                          -- under `m_ba`
                          ub : Set (sds a ub_ba)
                          ub = (m_ba ub_cb ** ub_prf_ba ub_cb)

                          -- essentially the same as the order-preservation
                          -- proof for `tran_prf_LTN`
                          ord_pres_prf u v u_ltn_v =
                              ord_pres_prf_ba
                                  (m_cb u)
                                  (m_cb v)
                                  (ord_pres_prf_cb u v u_ltn_v)

                          -- `m_cb u` <_b `ub_cb` by the upper bound proof
                          -- `m_ba (m_bc u)` <_a `m_ba ub_cb` by order preservation
                          ub_prf u = ord_pres_prf_ba (m_cb u) ub_cb (ub_prf_cb u)

        --
        -- PROOF:
        -- Suppose that v is an element of (a, <_a) in p', i.e., there is a
        -- well-quasi-ordering (b, <_b) in p which is less than the strict
        -- down set of v. Then there is an order preserving function f from b
        -- to the strict down set of v, and an element w in the strict down
        -- set of v (also in a) so that f embeds b in the strict down set of
        -- w. By the no-lower bound condition, there is another ordering (c, <_c)
        -- in p that is less than (b, <_b). The composition of order preserving
        -- functions maps (c, <_c) into the strict down set of w. Therefore, w
        -- is in p', and w <_a v since w is in the strict down set of v.
        --
        no_lb_prf' v
               -- the ordering (call it b) less than the strict down set of `v`
            (  (set_b ** ltn_b ** (tran_prf_b, wf_prf_b))
            ** (p_b, (m ** (ub ** ub_ltn_v) ** (ord_pres_prf, ub_prf)))
            )
            with (no_lb_prf (set_b ** ltn_b ** (tran_prf_b, wf_prf_b)) p_b)
                     -- the ordering `c` less than b, guaranteed by the
                     -- no-lower-bound proof
                | (  (set_c ** ltn_c ** (tran_prf_c, wf_prf_c))
                  ** (p_c, (m_cb ** ub_cb ** (ord_pres_prf_cb, ub_prf_cb)))
                  )
                    -- `ub` is less than `v` and `c`, which is in `p`, is less
                    -- than the strict down set of `ub`, making `ub` an element
                    -- of `p'`
                  = (ub ** ((c ** (p_c, c_ltn_sds_ub)), ub_ltn_v)) where
                      -- a convenient renaming
                      c : Omega
                      c = (set_c ** ltn_c ** (tran_prf_c, wf_prf_c))

                      -- `c` is less than the strict down set of `ub`
                      c_ltn_sds_ub : LTN c (sds a ub)
                      c_ltn_sds_ub = (g ** z ** (ord_pres_prf_g, ub_prf_g)) where
                          -- the composition of order preserving functions with
                          -- the auxiliary bound proof for SDS's
                          g : Set c -> Set (sds a ub)
                          g w = (fst (m (m_cb w)) ** ub_prf (m_cb w))

                          -- the upper bound is the image of the upper bound
                          -- `ub_cb` in `b`, along with the auxiliary bound
                          -- proof
                          z : Set (sds a ub)
                          z = (fst (m ub_cb) ** ub_prf ub_cb)

                          -- both are essentially the same as those in the
                          -- previous lemma
                          ord_pres_prf_g u w u_ltn_w =
                              ord_pres_prf
                                  (m_cb u)
                                  (m_cb w)
                                  (ord_pres_prf_cb u w u_ltn_w)
                          ub_prf_g w = ord_pres_prf (m_cb w) ub_cb (ub_prf_cb w)

--
-- The well-quasi-ordering of well-quasi-orderings
--
Omega_as_Omega : Omega
Omega_as_Omega = (Omega ** LTN ** (tran_prf_LTN, wf_prf_LTN))

--
-- A proof that all well-quasi-orderings are less than `Omega_as_Omega`, as
-- expected
--
LTN_Omega : (wqo : Omega) -> LTN wqo Omega_as_Omega
LTN_Omega (set_a ** ltn_a ** (tran_prf_a, wf_prf_a)) =
    -- `sds a` maps an element of `a` to its strict down set, and any strict down
    -- set is less than a itself
    (sds a ** a ** (ord_pres_prf, ub_prf)) where
        a : Omega
        a = (set_a ** ltn_a ** (tran_prf_a, wf_prf_a))

        -- if x <_a y, then the strict down set of `x` is less than the strict
        -- down set of `y` (with respect to `LTN`)
        ord_pres_prf x y x_ltn_y =
            (g ** (x ** x_ltn_y) ** (ord_pres_prf_g, ub_prf_g)) where
                -- `g` is the inclusion of the strict down set of `x` in the strict
                -- down set of `y`.
                g : Set (sds a x) -> Set (sds a y)
                g (z ** z_ltn_x) = (z ** (tran_prf a z x y z_ltn_x x_ltn_y))

                -- these proofs are simple because the order in a strict down set
                -- is essentially the same as that of `a`
                ord_pres_prf_g (_ ** _) (_ ** _) u_ltn_v = u_ltn_v
                ub_prf_g (_ ** u_ltn_x) = u_ltn_x

        -- every strict down set is less than `a` itself
        ub_prf x = (g ** x ** (ord_pres_prf_g, ub_prf_g)) where
            -- `g` is the inclusion of the strict down set of `x` into `a`
            g : Set (sds a x) -> Set a
            g (y ** _) = y

            ord_pres_prf_g (_ ** _) (_ ** _) y_ltn_z = y_ltn_z
            ub_prf_g (_ ** y_ltn_x) = y_ltn_x

--
-- A natural lemma, and where we take advantage of the fact that the system
-- does not see the non-well-foundedness.
--
-- I believe what's going on here is that the Omega on the right side is at
-- a higher level than the one on the left side. I don't think there are
-- any issues with the proof up to this point. The issue I think comes from
-- the fact that, they get collapsed again in falsum.
--
Omega_LTN_Omega : LTN Omega_as_Omega Omega_as_Omega
Omega_LTN_Omega = LTN_Omega Omega_as_Omega

--
-- Apply the well-foundedness proof for `LTN` to the set of well-quasi orderings
-- that are greater than `Omega_as_Omega`. This has no lower bound, so we get
-- `falsum`.
--
falsum : Void
falsum =
    wf_prf_LTN
        (LTN Omega_as_Omega)
        (Omega_as_Omega ** Omega_LTN_Omega)
        (\_, omega_ltn_x => (Omega_as_Omega ** (Omega_LTN_Omega, omega_ltn_x)))
