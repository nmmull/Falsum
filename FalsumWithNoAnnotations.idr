module FalsumWithNoAnnotations

%default total

tran : (a -> a -> Type) -> Type
tran {a} f = (x, y, z : a) -> f x y -> f y z -> f x z

nempty : (a -> Type) -> Type
nempty {a} p = (x : a ** p x)

no_lb : (a -> a -> Type) -> (a -> Type) -> Type
no_lb {a} f p = (x : a) -> p x -> (y : a ** (p y, f y x))

wf : (a -> a -> Type) -> Type
wf {a} f = (p : a -> Type) -> nempty p -> no_lb f p -> Void

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

LTN : Omega -> Omega -> Type
LTN (a ** ltn_a ** _) (b ** ltn_b ** _) =
    (  f : (a -> b)
    ** z : b
    ** ( (x, y : a) -> ltn_a x y -> ltn_b (f x) (f y)
       , (x : a) -> ltn_b (f x) z
       )
    )

tran_prf_LTN : tran LTN
tran_prf_LTN (_ ** _ ** _) (_ ** _ ** _) (_ ** _ ** _)
    (f_ab ** _ ** (ord_ab, _))
    (f_bc ** z ** (ord_bc, ub_bc)) =
        ((f_bc . f_ab) ** z ** (ord_ac, ub_ac)) where
            ord_ac x y x_ltn_y = ord_bc (f_ab x) (f_ab y) (ord_ab x y x_ltn_y)
            ub_ac x = ub_bc (f_ab x)

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

wf_prf_LTN : wf LTN
wf_prf_LTN p ((set_a ** ltn_a ** (tran_prf_a, wf_prf_a)) ** p_a) no_lb_prf =
    wf_prf a p' nempty_prf' no_lb_prf' where
        a : Omega
        a = (set_a ** ltn_a ** (tran_prf_a, wf_prf_a))
        p' : Set a -> Type
        p' x = (wqo : Omega ** (p wqo, LTN wqo (sds a x)))
        nempty_prf' with (no_lb_prf a p_a)
            | (  (set_b ** ltn_b ** (tran_prf_b, wf_prf_b))
              ** (p_b, (m_ba ** ub_ba ** (ord_pres_prf_ba, ub_prf_ba)))
              )
              with (no_lb_prf (set_b ** ltn_b ** (tran_prf_b, wf_prf_b)) p_b)
                | (  (set_c ** ltn_c ** (trans_prf_c, wf_prf_c))
                  ** (p_c, (m_cb ** ub_cb ** (ord_pres_prf_cb, ub_prf_cb)))
                  )
                  = (ub_ba ** c ** (p_c, c_ltn_sds_ub_ba)) where
                      c : Omega
                      c = (set_c ** ltn_c ** (trans_prf_c, wf_prf_c))
                      c_ltn_sds_ub_ba : LTN c (sds a ub_ba)
                      c_ltn_sds_ub_ba = (g ** ub ** (ord_pres_prf, ub_prf)) where
                          g : Set c -> Set (sds a ub_ba)
                          g v = (m_ba (m_cb v) ** ub_prf_ba (m_cb v))
                          ub : Set (sds a ub_ba)
                          ub = (m_ba ub_cb ** ub_prf_ba ub_cb)
                          ord_pres_prf u v u_ltn_v =
                              ord_pres_prf_ba
                                  (m_cb u)
                                  (m_cb v)
                                  (ord_pres_prf_cb u v u_ltn_v)
                          ub_prf u = ord_pres_prf_ba (m_cb u) ub_cb (ub_prf_cb u)
        no_lb_prf' v
            (  (set_b ** ltn_b ** (tran_prf_b, wf_prf_b))
            ** (p_b, (m ** (ub ** ub_ltn_v) ** (ord_pres_prf, ub_prf)))
            )
            with (no_lb_prf (set_b ** ltn_b ** (tran_prf_b, wf_prf_b)) p_b)
                | (  (set_c ** ltn_c ** (tran_prf_c, wf_prf_c))
                  ** (p_c, (m_cb ** ub_cb ** (ord_pres_prf_cb, ub_prf_cb)))
                  )
                  = (ub ** ((c ** (p_c, c_ltn_sds_ub)), ub_ltn_v)) where
                      c : Omega
                      c = (set_c ** ltn_c ** (tran_prf_c, wf_prf_c))
                      c_ltn_sds_ub : LTN c (sds a ub)
                      c_ltn_sds_ub = (g ** z ** (ord_pres_prf_g, ub_prf_g)) where
                          g : Set c -> Set (sds a ub)
                          g w = (fst (m (m_cb w)) ** ub_prf (m_cb w))
                          z : Set (sds a ub)
                          z = (fst (m ub_cb) ** ub_prf ub_cb)
                          ord_pres_prf_g u w u_ltn_w =
                              ord_pres_prf
                                  (m_cb u)
                                  (m_cb w)
                                  (ord_pres_prf_cb u w u_ltn_w)
                          ub_prf_g w = ord_pres_prf (m_cb w) ub_cb (ub_prf_cb w)

Omega_as_Omega : Omega
Omega_as_Omega = (Omega ** LTN ** (tran_prf_LTN, wf_prf_LTN))

LTN_Omega : (wqo : Omega) -> LTN wqo Omega_as_Omega
LTN_Omega (set_a ** ltn_a ** (tran_prf_a, wf_prf_a)) =
    (sds a ** a ** (ord_pres_prf, ub_prf)) where
        a : Omega
        a = (set_a ** ltn_a ** (tran_prf_a, wf_prf_a))
        ord_pres_prf x y x_ltn_y =
            (g ** (x ** x_ltn_y) ** (ord_pres_prf_g, ub_prf_g)) where
                g : Set (sds a x) -> Set (sds a y)
                g (z ** z_ltn_x) = (z ** (tran_prf a z x y z_ltn_x x_ltn_y))
                ord_pres_prf_g (_ ** _) (_ ** _) u_ltn_v = u_ltn_v
                ub_prf_g (_ ** u_ltn_x) = u_ltn_x
        ub_prf x = (g ** x ** (ord_pres_prf_g, ub_prf_g)) where
            g : Set (sds a x) -> Set a
            g (y ** _) = y
            ord_pres_prf_g (_ ** _) (_ ** _) y_ltn_z = y_ltn_z
            ub_prf_g (_ ** y_ltn_x) = y_ltn_x

Omega_LTN_Omega : LTN Omega_as_Omega Omega_as_Omega
Omega_LTN_Omega = LTN_Omega Omega_as_Omega

falsum : Void
falsum =
    wf_prf_LTN
        (LTN Omega_as_Omega)
        (Omega_as_Omega ** Omega_LTN_Omega)
        (\_, omega_ltn_x => (Omega_as_Omega ** (Omega_LTN_Omega, omega_ltn_x)))
