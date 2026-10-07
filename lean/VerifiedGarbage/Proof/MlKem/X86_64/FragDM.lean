import VerifiedGarbage.Proof.MlKem.X86_64.FragL
import VerifiedGarbage.Impl.MlKem.X86_64.Kem

/-!
# ML-KEM on x86-64: the call of `vg_mlkem*_decrypt_mul`

As the calls of the polynomial primitives (`FragPrim.lean`, `FragOf.lean`,
`FragL.lean`): what a call of `vg_mlkem*_decrypt_mul` writing `w` from the
`k` polynomials from `s` and from `u`, with the working space `z`, needs of
the state (`DecMulH`), of a layout (`dmChk`, `DecMulH.of`), what it
computes (`decMulAt_ok`) and that two runs leak the same (`decMulAt_tr`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- What a call of `vg_mlkem*_decrypt_mul` of rank `k` needs. -/
structure DecMulH (k : Nat) (w s u z : Ptr) (st : State) : Prop where
  off : w.2 < 2 ^ 31 ∧ s.2 < 2 ^ 31 ∧ u.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31
  redS : VecReduced st.mem (pa st s) k
  redU : VecReduced st.mem (pa st u) k
  ws : (pR (pa st w)).Disjoint (vR (pa st s) k)
  wu : (pR (pa st w)).Disjoint (vR (pa st u) k)
  wz : (pR (pa st w)).Disjoint (cR (pa st z))
  sz : (vR (pa st s) k).Disjoint (cR (pa st z))
  uz : (vR (pa st u) k).Disjoint (cR (pa st z))
  kW : (below (st.gpr .rsp) 32).Disjoint (pR (pa st w))
  kS : (below (st.gpr .rsp) 32).Disjoint (vR (pa st s) k)
  kU : (below (st.gpr .rsp) 32).Disjoint (vR (pa st u) k)
  kZ : (below (st.gpr .rsp) 32).Disjoint (cR (pa st z))
  c : Covers ([vR (pa st s) k, vR (pa st u) k] ++ [pR (pa st w), cR (pa st z)]) (st.rd ++ st.wr)
  wc : Covers [pR (pa st w), cR (pa st z)] st.wr

theorem dmGlue_ok (w s u z : Ptr) (ho : w.2 < 2 ^ 31 ∧ s.2 < 2 ^ 31 ∧ u.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31) (hs : NA s)
    (hu : NA u) (hz : NA z) (st : State) :
    WP isa (.block (lea .rdi w ++ lea .rsi s ++ lea .rdx u ++ lea .rcx z)) st fun s1 =>
      ((s1.gpr .rdi = pa st w ∧ s1.gpr .rsi = pa st s ∧ s1.gpr .rdx = pa st u ∧ s1.gpr .rcx = pa st z) ∧
        s1.mem = st.mem) ∧ Keep argRegs st s1 := by
  have s1 : s.1 ≠ .rdi := fun e => hs (by rw [e]; decide)
  have u1 : u.1 ≠ .rdi := fun e => hu (by rw [e]; decide)
  have u2 : u.1 ≠ .rsi := fun e => hu (by rw [e]; decide)
  have z1 : z.1 ≠ .rdi := fun e => hz (by rw [e]; decide)
  have z2 : z.1 ≠ .rsi := fun e => hz (by rw [e]; decide)
  have z3 : z.1 ≠ .rdx := fun e => hz (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho.1, sx_ofNat ho.2.1, sx_ofNat ho.2.2.1, sx_ofNat ho.2.2.2, s1, u1, u2, z1, z2, z3,
    List.cons_append, List.nil_append]

/-- The vector at `p` reads the same on entry to a callee. -/
theorem ce_vecAt (st : State) {p : Addr} {k : Nat} (h : (below (st.gpr .rsp) 32).Disjoint (vR p k)) :
    vecAt st.callEntry.mem p k = vecAt st.mem p k := by
  simp only [vecAt]
  exact List.map_congr_left fun i hi => ce_polyAt st (h.sub_right (DecMul.sub_v p (List.mem_range.mp hi)))

theorem dmPre {k : Nat} {w s u z : Ptr} {st s1 : State} (H : DecMulH k w s u z st)
    (hv : s1.gpr .rdi = pa st w ∧ s1.gpr .rsi = pa st s ∧ s1.gpr .rdx = pa st u ∧ s1.gpr .rcx = pa st z)
    (hm : s1.mem = st.mem) (k1 : Keep argRegs st s1) :
    (decMulK k).pre (s1.callEntry.withRegions [vR (pa st s) k, vR (pa st u) k] [pR (pa st w), cR (pa st z)]) := by
  have hsp : s1.gpr .rsp = st.gpr .rsp := k1.gpr (by decide)
  simp only [decMulK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2]
  refine ⟨trivial, trivial, H.ws, H.wu, H.wz, H.sz, H.uz, ret_disj s1 (by rw [hsp]; exact H.kW),
    ret_disj s1 (by rw [hsp]; exact H.kS), ret_disj s1 (by rw [hsp]; exact H.kU),
    ret_disj s1 (by rw [hsp]; exact H.kZ), fun i hi => ?_, fun i hi => ?_⟩
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kS.sub_right (DecMul.sub_v _ hi)), hm]; exact H.redS i hi
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kU.sub_right (DecMul.sub_v _ hi)), hm]; exact H.redU i hi

section
variable {A : Arith} (hA : ArithOk A) {L : Kem} (hk : L.k = 3 ∨ L.k = 4)
include hA hk

theorem decMulAt_ok {w s u z : Ptr} (hs : NA s) (hu : NA u) (hz : NA z) {st : State} (H : DecMulH L.k w s u z st) :
    WP isa (L.decMulAt A w s u z) st fun s' => Post st s' [pR (pa st w), cR (pa st z)] ∧
      PolyIs s'.mem (pa st w) (nttInv (dot (vecAt st.mem (pa st s) L.k) ((vecAt st.mem (pa st u) L.k).map ntt))) := by
  have hC := hA.dm L.k hk
  refine WP.mono (glueCall_ok hC.ok hC.nosp (by rw [hC.depth]; decide) (dmGlue_ok w s u z H.off hs hu hz st)
    (fun s1 hv hm k => dmPre H hv hm k) H.c H.wc) fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = st.gpr .rsp := k.gpr (by decide)
  simp only [decMulK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1, hm₂,
    ce_vecAt s1 (by rw [hsp]; exact H.kS), ce_vecAt s1 (by rw [hsp]; exact H.kU), hm] at hq
  exact hq

theorem decMulAt_tr {w s u z : Ptr} (hs : NA s) (hu : NA u) (hz : NA z) :
    RelCT isa (fun x y => DecMulH L.k w s u z x ∧ DecMulH L.k w s u z y ∧ x.gpr w.1 = y.gpr w.1 ∧
      x.gpr s.1 = y.gpr s.1 ∧ x.gpr u.1 = y.gpr u.1 ∧ x.gpr z.1 = y.gpr z.1 ∧ x.gpr .rsp = y.gpr .rsp)
      (L.decMulAt A w s u z) fun _ _ => True :=
  glueCall_tr (hA.dm L.k hk).ok (hA.dm L.k hk).ct (V := fun x x1 => ((x1.gpr .rdi = pa x w ∧ x1.gpr .rsi = pa x s ∧
      x1.gpr .rdx = pa x u ∧ x1.gpr .rcx = pa x z) ∧ x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _))
      (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨dmGlue_ok w s u z hx.off hs hu hz x, dmGlue_ok w s u z hy.off hs hu hz y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3, e4, e5⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, dmPre hx hv1 hm1 k1, dmPre hy hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.wc, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.wc,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e5]⟩
      simp only [decMulK, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), ce_gpr' _ (by decide : Reg.rdx ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1, hv1.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1,
        hv2.2.2.2, pa, e1, e2, e3, e4, k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e5, and_self]

end

/-! ## In a layout -/

def dmChk (bs wbs : List (Reg × Nat)) (k : Nat) (w s u z : Ptr) : Bool :=
  wrOk bs wbs w 1024 && rdOk bs s (1024 * k) && rdOk bs u (1024 * k) && wrOk bs wbs z 4096 &&
    sepB bs w 1024 s (1024 * k) && sepB bs w 1024 u (1024 * k) && sepB bs w 1024 z 4096 &&
    sepB bs s (1024 * k) z 4096 && sepB bs u (1024 * k) z 4096

section
variable {rbs wbs : List (Reg × Nat)} {st : State} (L : Lay rbs wbs st)
include L

theorem DecMulH.of {k : Nat} {w s u z : Ptr} (hc : dmChk (rbs ++ wbs) wbs k w s u z = true)
    (redS : VecReduced st.mem (pa st s) k) (redU : VecReduced st.mem (pa st u) k) : DecMulH k w s u z st := by
  simp only [dmChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨how, hrw⟩, hww⟩, hos, hrs⟩, hou, hru⟩, ⟨hoz, hrz⟩, hwz⟩, s1⟩, s2⟩, s3⟩, s4⟩, s5⟩ := hc
  exact ⟨⟨how, hos, hou, hoz⟩, redS, redU, L.disj s1, L.disj s2, L.disj s3, L.disj s4, L.disj s5, L.stkD hrw,
    L.stkD hrs, L.stkD hru, L.stkD hrz,
    covers_append (covers_cons (L.cR hrs) (covers_cons (L.cR hru) covers_nil))
      (covers_cons (L.cR hrw) (covers_cons (L.cR hrz) covers_nil)),
    covers_cons (L.cW hww) (covers_cons (L.cW hwz) covers_nil)⟩

end

theorem dmChk_in {bs wbs : List (Reg × Nat)} {k : Nat} {w s u z : Ptr} (hc : dmChk bs wbs k w s u z = true) :
    inB bs w 1024 = true ∧ inB bs s (1024 * k) = true ∧ inB bs u (1024 * k) = true ∧ inB bs z 4096 = true := by
  simp only [dmChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨wrOk_in h1, rdOk_in h2, rdOk_in h3, wrOk_in h4⟩

section
variable {A : Arith} (hA : ArithOk A) {L : Kem} (hk : L.k = 3 ∨ L.k = 4) {rbs wbs : List (Reg × Nat)}
include hA hk

theorem decMulAt_okL {st : State} (La : Lay rbs wbs st) {w s u z : Ptr} (hs : NA s) (hu : NA u) (hz : NA z)
    (hc : dmChk (rbs ++ wbs) wbs L.k w s u z = true) (redS : VecReduced st.mem (pa st s) L.k)
    (redU : VecReduced st.mem (pa st u) L.k) :
    WP isa (L.decMulAt A w s u z) st fun s' => PPost st s' [(w, 1024), (z, 4096)] ∧
      PolyIs s'.mem (pa st w) (nttInv (dot (vecAt st.mem (pa st s) L.k) ((vecAt st.mem (pa st u) L.k).map ntt))) :=
  decMulAt_ok hA hk hs hu hz (DecMulH.of La hc redS redU)

theorem decMulAt_trL {w s u z : Ptr} (hs : NA s) (hu : NA u) (hz : NA z)
    (hc : dmChk (rbs ++ wbs) wbs L.k w s u z = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧
      (VecReduced x.mem (pa x s) L.k ∧ VecReduced x.mem (pa x u) L.k) ∧
      (VecReduced y.mem (pa y s) L.k ∧ VecReduced y.mem (pa y u) L.k)) (L.decMulAt A w s u z) fun _ _ => True :=
  RelCT.mono (decMulAt_tr hA hk hs hu hz) (fun _ _ ⟨e, ⟨r1, r2⟩, r3, r4⟩ => ⟨DecMulH.of e.1 hc r1 r2,
    DecMulH.of e.2.1 hc r3 r4, e.eq (dmChk_in hc).1, e.eq (dmChk_in hc).2.1, e.eq (dmChk_in hc).2.2.1,
    e.eq (dmChk_in hc).2.2.2, e.2.2.2⟩) fun _ _ _ => trivial

end

/-- The `k` polynomials from polynomial `b` of the working space. -/
theorem pa_pS (st : State) (b i : Nat) : pa st (pS (b + i)) = pa st (pS b) + BitVec.ofNat 64 (1024 * i) := by
  simp only [pa, oP]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add, Nat.add_assoc]

theorem vecReduced_pS {m : Mem} {st : State} {b k : Nat} (h : ∀ i < k, Reduced m (pa st (pS (b + i)))) :
    VecReduced m (pa st (pS b)) k := fun i hi => by rw [← pa_pS]; exact h i hi

theorem vecAt_pS (m : Mem) (st : State) (b k : Nat) :
    vecAt m (pa st (pS b)) k = (List.range k).map fun i => polyAt m (pa st (pS (b + i))) := by
  simp only [vecAt, pa_pS]

end VG.Proof.MlKem.X86_64
