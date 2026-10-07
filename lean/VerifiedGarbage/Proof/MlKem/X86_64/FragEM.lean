import VerifiedGarbage.Proof.MlKem.X86_64.FragDM

/-!
# ML-KEM on x86-64: the call of `vg_mlkem*_encrypt_mul`

As the call of `vg_mlkem*_decrypt_mul` (`FragDM.lean`): what a call of
`vg_mlkem*_encrypt_mul` writing the `k + 1` polynomials from `u` from the
`k²` from `a` and the `k` from `t` and from `y`, with the working space `z`,
needs of the state (`EncMulH`), of a layout (`emChk`, `EncMulH.of`), what it
computes (`encMulAt_ok`) and that two runs leak the same (`encMulAt_tr`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- What a call of `vg_mlkem*_encrypt_mul` of rank `k` needs. -/
structure EncMulH (k : Nat) (u a t y z : Ptr) (st : State) : Prop where
  off : u.2 < 2 ^ 31 ∧ a.2 < 2 ^ 31 ∧ t.2 < 2 ^ 31 ∧ y.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31
  redA : VecReduced st.mem (pa st a) (k * k)
  redT : VecReduced st.mem (pa st t) k
  redY : VecReduced st.mem (pa st y) k
  ua : (vR (pa st u) (k + 1)).Disjoint (vR (pa st a) (k * k))
  ut : (vR (pa st u) (k + 1)).Disjoint (vR (pa st t) k)
  uy : (vR (pa st u) (k + 1)).Disjoint (vR (pa st y) k)
  uz : (vR (pa st u) (k + 1)).Disjoint (cR (pa st z))
  az : (vR (pa st a) (k * k)).Disjoint (cR (pa st z))
  tz : (vR (pa st t) k).Disjoint (cR (pa st z))
  yz : (vR (pa st y) k).Disjoint (cR (pa st z))
  kU : (below (st.gpr .rsp) 32).Disjoint (vR (pa st u) (k + 1))
  kA : (below (st.gpr .rsp) 32).Disjoint (vR (pa st a) (k * k))
  kT : (below (st.gpr .rsp) 32).Disjoint (vR (pa st t) k)
  kY : (below (st.gpr .rsp) 32).Disjoint (vR (pa st y) k)
  kZ : (below (st.gpr .rsp) 32).Disjoint (cR (pa st z))
  c : Covers ([vR (pa st a) (k * k), vR (pa st t) k, vR (pa st y) k] ++ [vR (pa st u) (k + 1), cR (pa st z)])
    (st.rd ++ st.wr)
  wc : Covers [vR (pa st u) (k + 1), cR (pa st z)] st.wr

theorem emGlue_ok (u a t y z : Ptr) (ho : u.2 < 2 ^ 31 ∧ a.2 < 2 ^ 31 ∧ t.2 < 2 ^ 31 ∧ y.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31)
    (ha : NA a) (ht : NA t) (hy : NA y) (hz : NA z) (st : State) :
    WP isa (.block (lea .rdi u ++ lea .rsi a ++ lea .rdx t ++ lea .rcx y ++ lea .r8 z)) st fun s1 =>
      ((s1.gpr .rdi = pa st u ∧ s1.gpr .rsi = pa st a ∧ s1.gpr .rdx = pa st t ∧ s1.gpr .rcx = pa st y ∧
        s1.gpr .r8 = pa st z) ∧ s1.mem = st.mem) ∧ Keep argRegs st s1 := by
  have a1 : a.1 ≠ .rdi := fun e => ha (by rw [e]; decide)
  have t1 : t.1 ≠ .rdi := fun e => ht (by rw [e]; decide)
  have t2 : t.1 ≠ .rsi := fun e => ht (by rw [e]; decide)
  have y1 : y.1 ≠ .rdi := fun e => hy (by rw [e]; decide)
  have y2 : y.1 ≠ .rsi := fun e => hy (by rw [e]; decide)
  have y3 : y.1 ≠ .rdx := fun e => hy (by rw [e]; decide)
  have z1 : z.1 ≠ .rdi := fun e => hz (by rw [e]; decide)
  have z2 : z.1 ≠ .rsi := fun e => hz (by rw [e]; decide)
  have z3 : z.1 ≠ .rdx := fun e => hz (by rw [e]; decide)
  have z4 : z.1 ≠ .rcx := fun e => hz (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho.1, sx_ofNat ho.2.1, sx_ofNat ho.2.2.1, sx_ofNat ho.2.2.2.1, sx_ofNat ho.2.2.2.2, a1, t1, t2,
    y1, y2, y3, z1, z2, z3, z4, List.cons_append, List.nil_append]

/-- The matrix at `p` reads the same on entry to a callee. -/
theorem ce_matAt (st : State) {p : Addr} {k : Nat} (h : (below (st.gpr .rsp) 32).Disjoint (vR p (k * k))) :
    matAt st.callEntry.mem p k = matAt st.mem p k := by
  simp only [matAt, vecAt]
  refine List.map_congr_left fun i hi => List.map_congr_left fun j hj => ?_
  have hi := List.mem_range.mp hi
  have hj := List.mem_range.mp hj
  have e : k * i + j < k * k := by
    have := Nat.mul_le_mul_left k (show i + 1 ≤ k by omega); rw [Nat.mul_succ] at this; omega
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add]
  exact ce_polyAt st (h.sub_right (DecMul.sub_v p e))

theorem emPre {k : Nat} {u a t y z : Ptr} {st s1 : State} (H : EncMulH k u a t y z st)
    (hv : s1.gpr .rdi = pa st u ∧ s1.gpr .rsi = pa st a ∧ s1.gpr .rdx = pa st t ∧ s1.gpr .rcx = pa st y ∧
      s1.gpr .r8 = pa st z)
    (hm : s1.mem = st.mem) (k1 : Keep argRegs st s1) :
    (encMulK k).pre (s1.callEntry.withRegions [vR (pa st a) (k * k), vR (pa st t) k, vR (pa st y) k]
      [vR (pa st u) (k + 1), cR (pa st z)]) := by
  have hsp : s1.gpr .rsp = st.gpr .rsp := k1.gpr (by decide)
  simp only [encMulK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.r8 ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2]
  refine ⟨trivial, trivial, H.ua, H.ut, H.uy, H.uz, H.az, H.tz, H.yz, ret_disj s1 (by rw [hsp]; exact H.kU),
    ret_disj s1 (by rw [hsp]; exact H.kA), ret_disj s1 (by rw [hsp]; exact H.kT),
    ret_disj s1 (by rw [hsp]; exact H.kY), ret_disj s1 (by rw [hsp]; exact H.kZ), fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_⟩
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kA.sub_right (DecMul.sub_v _ hi)), hm]; exact H.redA i hi
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kT.sub_right (DecMul.sub_v _ hi)), hm]; exact H.redT i hi
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kY.sub_right (DecMul.sub_v _ hi)), hm]; exact H.redY i hi

section
variable {A : Arith} (hA : ArithOk A) {L : Kem} (hk : L.k = 3 ∨ L.k = 4)
include hA hk

theorem encMulAt_ok {u a t y z : Ptr} (ha : NA a) (ht : NA t) (hy : NA y) (hz : NA z) {st : State}
    (H : EncMulH L.k u a t y z st) :
    WP isa (L.encMulAt A u a t y z) st fun s' => Post st s' [vR (pa st u) (L.k + 1), cR (pa st z)] ∧
      VecIs s'.mem (pa st u) (L.k + 1)
        (((mulMatTVec L.k (matAt st.mem (pa st a) L.k) ((vecAt st.mem (pa st y) L.k).map ntt)).map nttInv) ++
          [nttInv (dot (vecAt st.mem (pa st t) L.k) ((vecAt st.mem (pa st y) L.k).map ntt))]) := by
  have hC := hA.em L.k hk
  refine WP.mono (glueCall_ok hC.ok hC.nosp (by rw [hC.depth]; decide) (emGlue_ok u a t y z H.off ha ht hy hz st)
    (fun s1 hv hm k => emPre H hv hm k) H.c H.wc) fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = st.gpr .rsp := k.gpr (by decide)
  simp only [encMulK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, hm₂,
    ce_matAt s1 (by rw [hsp]; exact H.kA), ce_vecAt s1 (by rw [hsp]; exact H.kT),
    ce_vecAt s1 (by rw [hsp]; exact H.kY), hm] at hq
  exact hq

theorem encMulAt_tr {u a t y z : Ptr} (ha : NA a) (ht : NA t) (hy : NA y) (hz : NA z) :
    RelCT isa (fun x y' => EncMulH L.k u a t y z x ∧ EncMulH L.k u a t y z y' ∧ x.gpr u.1 = y'.gpr u.1 ∧
      x.gpr a.1 = y'.gpr a.1 ∧ x.gpr t.1 = y'.gpr t.1 ∧ x.gpr y.1 = y'.gpr y.1 ∧ x.gpr z.1 = y'.gpr z.1 ∧
      x.gpr .rsp = y'.gpr .rsp)
      (L.encMulAt A u a t y z) fun _ _ => True :=
  glueCall_tr (hA.em L.k hk).ok (hA.em L.k hk).ct (V := fun x x1 => ((x1.gpr .rdi = pa x u ∧
      x1.gpr .rsi = pa x a ∧ x1.gpr .rdx = pa x t ∧ x1.gpr .rcx = pa x y ∧ x1.gpr .r8 = pa x z) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _))
      (lea_nomem _ _)) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y' ⟨hx, hy', _⟩ => ⟨emGlue_ok u a t y z hx.off ha ht hy hz x, emGlue_ok u a t y z hy'.off ha ht hy hz y'⟩)
    fun x y' x1 y1 ⟨hx, hy', e1, e2, e3, e4, e5, e6⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, emPre hx hv1 hm1 k1, emPre hy' hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.wc, by rw [k2.2.1, k2.2.2]; exact hy'.c, by rw [k2.2.2]; exact hy'.wc,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e6]⟩
      simp only [encMulK, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), ce_gpr' _ (by decide : Reg.rdx ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), ce_gpr' _ (by decide : Reg.r8 ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
        hv1.2.2.2.1, hv1.2.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2.1, hv2.2.2.2.2, pa, e1, e2, e3, e4, e5,
        k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e6, and_self]

end

/-! ## In a layout -/

def emChk (bs wbs : List (Reg × Nat)) (k : Nat) (u a t y z : Ptr) : Bool :=
  wrOk bs wbs u (1024 * (k + 1)) && rdOk bs a (1024 * (k * k)) && rdOk bs t (1024 * k) && rdOk bs y (1024 * k) &&
    wrOk bs wbs z 4096 && sepB bs u (1024 * (k + 1)) a (1024 * (k * k)) && sepB bs u (1024 * (k + 1)) t (1024 * k) &&
    sepB bs u (1024 * (k + 1)) y (1024 * k) && sepB bs u (1024 * (k + 1)) z 4096 && sepB bs a (1024 * (k * k)) z 4096 &&
    sepB bs t (1024 * k) z 4096 && sepB bs y (1024 * k) z 4096

section
variable {rbs wbs : List (Reg × Nat)} {st : State} (L : Lay rbs wbs st)
include L

theorem EncMulH.of {k : Nat} {u a t y z : Ptr} (hc : emChk (rbs ++ wbs) wbs k u a t y z = true)
    (redA : VecReduced st.mem (pa st a) (k * k)) (redT : VecReduced st.mem (pa st t) k)
    (redY : VecReduced st.mem (pa st y) k) : EncMulH k u a t y z st := by
  simp only [emChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hou, hru⟩, hwu⟩, hoa, hra⟩, hot, hrt⟩, hoy, hry⟩, ⟨hoz, hrz⟩, hwz⟩, s1⟩, s2⟩, s3⟩, s4⟩, s5⟩,
    s6⟩, s7⟩ := hc
  exact ⟨⟨hou, hoa, hot, hoy, hoz⟩, redA, redT, redY, L.disj s1, L.disj s2, L.disj s3, L.disj s4, L.disj s5,
    L.disj s6, L.disj s7, L.stkD hru, L.stkD hra, L.stkD hrt, L.stkD hry, L.stkD hrz,
    covers_append (covers_cons (L.cR hra) (covers_cons (L.cR hrt) (covers_cons (L.cR hry) covers_nil)))
      (covers_cons (L.cR hru) (covers_cons (L.cR hrz) covers_nil)),
    covers_cons (L.cW hwu) (covers_cons (L.cW hwz) covers_nil)⟩

end

theorem emChk_in {bs wbs : List (Reg × Nat)} {k : Nat} {u a t y z : Ptr} (hc : emChk bs wbs k u a t y z = true) :
    inB bs u (1024 * (k + 1)) = true ∧ inB bs a (1024 * (k * k)) = true ∧ inB bs t (1024 * k) = true ∧
      inB bs y (1024 * k) = true ∧ inB bs z 4096 = true := by
  simp only [emChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨wrOk_in h1, rdOk_in h2, rdOk_in h3, rdOk_in h4, wrOk_in h5⟩

section
variable {A : Arith} (hA : ArithOk A) {L : Kem} (hk : L.k = 3 ∨ L.k = 4) {rbs wbs : List (Reg × Nat)}
include hA hk

theorem encMulAt_okL {st : State} (La : Lay rbs wbs st) {u a t y z : Ptr} (ha : NA a) (ht : NA t) (hy : NA y)
    (hz : NA z) (hc : emChk (rbs ++ wbs) wbs L.k u a t y z = true) (redA : VecReduced st.mem (pa st a) (L.k * L.k))
    (redT : VecReduced st.mem (pa st t) L.k) (redY : VecReduced st.mem (pa st y) L.k) :
    WP isa (L.encMulAt A u a t y z) st fun s' => PPost st s' [(u, 1024 * (L.k + 1)), (z, 4096)] ∧
      VecIs s'.mem (pa st u) (L.k + 1)
        (((mulMatTVec L.k (matAt st.mem (pa st a) L.k) ((vecAt st.mem (pa st y) L.k).map ntt)).map nttInv) ++
          [nttInv (dot (vecAt st.mem (pa st t) L.k) ((vecAt st.mem (pa st y) L.k).map ntt))]) :=
  encMulAt_ok hA hk ha ht hy hz (EncMulH.of La hc redA redT redY)

theorem encMulAt_trL {u a t y z : Ptr} (ha : NA a) (ht : NA t) (hy : NA y) (hz : NA z)
    (hc : emChk (rbs ++ wbs) wbs L.k u a t y z = true) :
    RelCT isa (fun x y' => LRel rbs wbs x y' ∧
      (VecReduced x.mem (pa x a) (L.k * L.k) ∧ VecReduced x.mem (pa x t) L.k ∧ VecReduced x.mem (pa x y) L.k) ∧
      (VecReduced y'.mem (pa y' a) (L.k * L.k) ∧ VecReduced y'.mem (pa y' t) L.k ∧ VecReduced y'.mem (pa y' y) L.k))
      (L.encMulAt A u a t y z) fun _ _ => True :=
  RelCT.mono (encMulAt_tr hA hk ha ht hy hz) (fun _ _ ⟨e, ⟨r1, r2, r3⟩, r4, r5, r6⟩ =>
    ⟨EncMulH.of e.1 hc r1 r2 r3, EncMulH.of e.2.1 hc r4 r5 r6, e.eq (emChk_in hc).1, e.eq (emChk_in hc).2.1,
      e.eq (emChk_in hc).2.2.1, e.eq (emChk_in hc).2.2.2.1, e.eq (emChk_in hc).2.2.2.2, e.2.2.2⟩) fun _ _ _ => trivial

end

end VG.Proof.MlKem.X86_64
