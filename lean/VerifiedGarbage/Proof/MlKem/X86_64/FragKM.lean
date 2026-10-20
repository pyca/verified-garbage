module
public import VerifiedGarbage.Impl.MlKem.X86_64.Kem
public import VerifiedGarbage.Proof.MlKem.X86_64.FragOf

import VerifiedGarbage.Proof.MlKem.X86_64.FragEM
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.FragDM
import VerifiedGarbage.Proof.MlKem.X86_64.FragL

/-!
# ML-KEM on x86-64: the call of `vg_mlkem*_keygen_mul`

As the call of `vg_mlkem*_encrypt_mul` (`FragEM.lean`): what a call of
`vg_mlkem*_keygen_mul` writing the `k` polynomials from `t` and from `s`,
from those from `s`, the `k²` from `a` and the `k` from `e`, with the
working space `z`, needs of the state (`KgMulH`), of a layout (`kmChk`,
`KgMulH.of`), what it computes (`kgMulAt_ok`) and that two runs leak the
same (`kgMulAt_tr`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- What a call of `vg_mlkem*_keygen_mul` of rank `k` needs. -/
structure KgMulH (k : Nat) (t s a e z : Ptr) (st : State) : Prop where
  off : t.2 < 2 ^ 31 ∧ s.2 < 2 ^ 31 ∧ a.2 < 2 ^ 31 ∧ e.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31
  redS : VecReduced st.mem (pa st s) k
  redA : VecReduced st.mem (pa st a) (k * k)
  redE : VecReduced st.mem (pa st e) k
  ts : (vR (pa st t) k).Disjoint (vR (pa st s) k)
  ta : (vR (pa st t) k).Disjoint (vR (pa st a) (k * k))
  te : (vR (pa st t) k).Disjoint (vR (pa st e) k)
  tz : (vR (pa st t) k).Disjoint (cR (pa st z))
  sa : (vR (pa st s) k).Disjoint (vR (pa st a) (k * k))
  se : (vR (pa st s) k).Disjoint (vR (pa st e) k)
  sz : (vR (pa st s) k).Disjoint (cR (pa st z))
  az : (vR (pa st a) (k * k)).Disjoint (cR (pa st z))
  ez : (vR (pa st e) k).Disjoint (cR (pa st z))
  kT : (below (st.gpr .rsp) 32).Disjoint (vR (pa st t) k)
  kS : (below (st.gpr .rsp) 32).Disjoint (vR (pa st s) k)
  kA : (below (st.gpr .rsp) 32).Disjoint (vR (pa st a) (k * k))
  kE : (below (st.gpr .rsp) 32).Disjoint (vR (pa st e) k)
  kZ : (below (st.gpr .rsp) 32).Disjoint (cR (pa st z))
  c : Covers ([vR (pa st a) (k * k), vR (pa st e) k] ++ [vR (pa st t) k, vR (pa st s) k, cR (pa st z)])
    (st.rd ++ st.wr)
  wc : Covers [vR (pa st t) k, vR (pa st s) k, cR (pa st z)] st.wr

theorem kmGlue_ok (t s a e z : Ptr) (ho : t.2 < 2 ^ 31 ∧ s.2 < 2 ^ 31 ∧ a.2 < 2 ^ 31 ∧ e.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31)
    (hs : NA s) (ha : NA a) (he : NA e) (hz : NA z) (st : State) :
    WP isa (.block (lea .rdi t ++ lea .rsi s ++ lea .rdx a ++ lea .rcx e ++ lea .r8 z)) st fun s1 =>
      ((s1.gpr .rdi = pa st t ∧ s1.gpr .rsi = pa st s ∧ s1.gpr .rdx = pa st a ∧ s1.gpr .rcx = pa st e ∧
        s1.gpr .r8 = pa st z) ∧ s1.mem = st.mem) ∧ Keep argRegs st s1 := by
  have s1 : s.1 ≠ .rdi := fun h => hs (by rw [h]; decide)
  have a1 : a.1 ≠ .rdi := fun h => ha (by rw [h]; decide)
  have a2 : a.1 ≠ .rsi := fun h => ha (by rw [h]; decide)
  have e1 : e.1 ≠ .rdi := fun h => he (by rw [h]; decide)
  have e2 : e.1 ≠ .rsi := fun h => he (by rw [h]; decide)
  have e3 : e.1 ≠ .rdx := fun h => he (by rw [h]; decide)
  have z1 : z.1 ≠ .rdi := fun h => hz (by rw [h]; decide)
  have z2 : z.1 ≠ .rsi := fun h => hz (by rw [h]; decide)
  have z3 : z.1 ≠ .rdx := fun h => hz (by rw [h]; decide)
  have z4 : z.1 ≠ .rcx := fun h => hz (by rw [h]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho.1, sx_ofNat ho.2.1, sx_ofNat ho.2.2.1, sx_ofNat ho.2.2.2.1, sx_ofNat ho.2.2.2.2, s1, a1, a2,
    e1, e2, e3, z1, z2, z3, z4, List.cons_append, List.nil_append]

theorem kmPre {k : Nat} {t s a e z : Ptr} {st s1 : State} (H : KgMulH k t s a e z st)
    (hv : s1.gpr .rdi = pa st t ∧ s1.gpr .rsi = pa st s ∧ s1.gpr .rdx = pa st a ∧ s1.gpr .rcx = pa st e ∧
      s1.gpr .r8 = pa st z)
    (hm : s1.mem = st.mem) (k1 : Keep argRegs st s1) :
    (kgMulK k).pre (s1.callEntry.withRegions [vR (pa st a) (k * k), vR (pa st e) k]
      [vR (pa st t) k, vR (pa st s) k, cR (pa st z)]) := by
  have hsp : s1.gpr .rsp = st.gpr .rsp := k1.gpr (by decide)
  simp only [kgMulK, kgMulKA, kgMulKG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.r8 ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2]
  refine ⟨trivial, trivial, H.ts, H.ta, H.te, H.tz, H.sa, H.se, H.sz, H.az, H.ez,
    ret_disj s1 (by rw [hsp]; exact H.kT), ret_disj s1 (by rw [hsp]; exact H.kS),
    ret_disj s1 (by rw [hsp]; exact H.kA), ret_disj s1 (by rw [hsp]; exact H.kE),
    ret_disj s1 (by rw [hsp]; exact H.kZ), fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kS.sub_right (DecMul.sub_v _ hi)), hm]; exact H.redS i hi
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kA.sub_right (DecMul.sub_v _ hi)), hm]; exact H.redA i hi
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kE.sub_right (DecMul.sub_v _ hi)), hm]; exact H.redE i hi

section
variable {A : Arith} (hA : ArithOk A) {L : Kem} (hk : L.k = 3 ∨ L.k = 4)
include hA hk

theorem kgMulAt_ok {t s a e z : Ptr} (hs : NA s) (ha : NA a) (he : NA e) (hz : NA z) {st : State}
    (H : KgMulH L.k t s a e z st) :
    WP isa (L.kgMulAt A t s a e z) st fun s' => Post st s' [vR (pa st t) L.k, vR (pa st s) L.k, cR (pa st z)] ∧
      VecIs s'.mem (pa st s) L.k ((vecAt st.mem (pa st s) L.k).map ntt) ∧
      VecIs s'.mem (pa st t) L.k (addVec (mulMatVec (matAt st.mem (pa st a) L.k)
        ((vecAt st.mem (pa st s) L.k).map ntt)) ((vecAt st.mem (pa st e) L.k).map ntt)) := by
  have hC := hA.km L.k hk
  refine WP.mono (glueCall_ok hC.ok hC.nosp (by rw [hC.depth]; decide) (kmGlue_ok t s a e z H.off hs ha he hz st)
    (fun s1 hv hm k => kmPre H hv hm k) H.c H.wc) fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = st.gpr .rsp := k.gpr (by decide)
  simp only [kgMulK, kgMulKA, kgMulKG, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, hm₂,
    ce_matAt s1 (by rw [hsp]; exact H.kA), ce_vecAt s1 (by rw [hsp]; exact H.kS),
    ce_vecAt s1 (by rw [hsp]; exact H.kE), hm] at hq
  exact hq

theorem kgMulAt_tr {t s a e z : Ptr} (hs : NA s) (ha : NA a) (he : NA e) (hz : NA z) :
    RelCT isa (fun x y' => KgMulH L.k t s a e z x ∧ KgMulH L.k t s a e z y' ∧ x.gpr t.1 = y'.gpr t.1 ∧
      x.gpr s.1 = y'.gpr s.1 ∧ x.gpr a.1 = y'.gpr a.1 ∧ x.gpr e.1 = y'.gpr e.1 ∧ x.gpr z.1 = y'.gpr z.1 ∧
      x.gpr .rsp = y'.gpr .rsp)
      (L.kgMulAt A t s a e z) fun _ _ => True :=
  glueCall_tr (hA.km L.k hk).ok (hA.km L.k hk).ct (V := fun x x1 => ((x1.gpr .rdi = pa x t ∧
      x1.gpr .rsi = pa x s ∧ x1.gpr .rdx = pa x a ∧ x1.gpr .rcx = pa x e ∧ x1.gpr .r8 = pa x z) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _))
      (lea_nomem _ _)) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y' ⟨hx, hy', _⟩ => ⟨kmGlue_ok t s a e z hx.off hs ha he hz x, kmGlue_ok t s a e z hy'.off hs ha he hz y'⟩)
    fun x y' x1 y1 ⟨hx, hy', e1, e2, e3, e4, e5, e6⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, kmPre hx hv1 hm1 k1, kmPre hy' hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.wc, by rw [k2.2.1, k2.2.2]; exact hy'.c, by rw [k2.2.2]; exact hy'.wc,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e6]⟩
      simp only [kgMulK, kgMulKA, kgMulKG, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), ce_gpr' _ (by decide : Reg.rdx ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), ce_gpr' _ (by decide : Reg.r8 ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
        hv1.2.2.2.1, hv1.2.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2.1, hv2.2.2.2.2, pa, e1, e2, e3, e4, e5,
        k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e6, and_self]

end

/-! ## In a layout -/

def kmChk (bs wbs : List (Reg × Nat)) (k : Nat) (t s a e z : Ptr) : Bool :=
  wrOk bs wbs t (1024 * k) && wrOk bs wbs s (1024 * k) && rdOk bs a (1024 * (k * k)) && rdOk bs e (1024 * k) &&
    wrOk bs wbs z 4096 && sepB bs t (1024 * k) s (1024 * k) && sepB bs t (1024 * k) a (1024 * (k * k)) &&
    sepB bs t (1024 * k) e (1024 * k) && sepB bs t (1024 * k) z 4096 && sepB bs s (1024 * k) a (1024 * (k * k)) &&
    sepB bs s (1024 * k) e (1024 * k) && sepB bs s (1024 * k) z 4096 && sepB bs a (1024 * (k * k)) z 4096 &&
    sepB bs e (1024 * k) z 4096

section
variable {rbs wbs : List (Reg × Nat)} {st : State} (L : Lay rbs wbs st)
include L

theorem KgMulH.of {k : Nat} {t s a e z : Ptr} (hc : kmChk (rbs ++ wbs) wbs k t s a e z = true)
    (redS : VecReduced st.mem (pa st s) k) (redA : VecReduced st.mem (pa st a) (k * k))
    (redE : VecReduced st.mem (pa st e) k) : KgMulH k t s a e z st := by
  simp only [kmChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hot, hrt⟩, hwt⟩, ⟨hos, hrs⟩, hws⟩, hoa, hra⟩, hoe, hre⟩, ⟨hoz, hrz⟩, hwz⟩, s1⟩, s2⟩, s3⟩,
    s4⟩, s5⟩, s6⟩, s7⟩, s8⟩, s9⟩ := hc
  exact ⟨⟨hot, hos, hoa, hoe, hoz⟩, redS, redA, redE, L.disj s1, L.disj s2, L.disj s3, L.disj s4, L.disj s5,
    L.disj s6, L.disj s7, L.disj s8, L.disj s9, L.stkD hrt, L.stkD hrs, L.stkD hra, L.stkD hre, L.stkD hrz,
    covers_append (covers_cons (L.cR hra) (covers_cons (L.cR hre) covers_nil))
      (covers_cons (L.cR hrt) (covers_cons (L.cR hrs) (covers_cons (L.cR hrz) covers_nil))),
    covers_cons (L.cW hwt) (covers_cons (L.cW hws) (covers_cons (L.cW hwz) covers_nil))⟩

end

theorem kmChk_in {bs wbs : List (Reg × Nat)} {k : Nat} {t s a e z : Ptr} (hc : kmChk bs wbs k t s a e z = true) :
    inB bs t (1024 * k) = true ∧ inB bs s (1024 * k) = true ∧ inB bs a (1024 * (k * k)) = true ∧
      inB bs e (1024 * k) = true ∧ inB bs z 4096 = true := by
  simp only [kmChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨wrOk_in h1, wrOk_in h2, rdOk_in h3, rdOk_in h4, wrOk_in h5⟩

section
variable {A : Arith} (hA : ArithOk A) {L : Kem} (hk : L.k = 3 ∨ L.k = 4) {rbs wbs : List (Reg × Nat)}
include hA hk

theorem kgMulAt_okL {st : State} (La : Lay rbs wbs st) {t s a e z : Ptr} (hs : NA s) (ha : NA a) (he : NA e)
    (hz : NA z) (hc : kmChk (rbs ++ wbs) wbs L.k t s a e z = true) (redS : VecReduced st.mem (pa st s) L.k)
    (redA : VecReduced st.mem (pa st a) (L.k * L.k)) (redE : VecReduced st.mem (pa st e) L.k) :
    WP isa (L.kgMulAt A t s a e z) st fun s' => PPost st s' [(t, 1024 * L.k), (s, 1024 * L.k), (z, 4096)] ∧
      VecIs s'.mem (pa st s) L.k ((vecAt st.mem (pa st s) L.k).map ntt) ∧
      VecIs s'.mem (pa st t) L.k (addVec (mulMatVec (matAt st.mem (pa st a) L.k)
        ((vecAt st.mem (pa st s) L.k).map ntt)) ((vecAt st.mem (pa st e) L.k).map ntt)) :=
  kgMulAt_ok hA hk hs ha he hz (KgMulH.of La hc redS redA redE)

theorem kgMulAt_trL {t s a e z : Ptr} (hs : NA s) (ha : NA a) (he : NA e) (hz : NA z)
    (hc : kmChk (rbs ++ wbs) wbs L.k t s a e z = true) :
    RelCT isa (fun x y' => LRel rbs wbs x y' ∧
      (VecReduced x.mem (pa x s) L.k ∧ VecReduced x.mem (pa x a) (L.k * L.k) ∧ VecReduced x.mem (pa x e) L.k) ∧
      (VecReduced y'.mem (pa y' s) L.k ∧ VecReduced y'.mem (pa y' a) (L.k * L.k) ∧ VecReduced y'.mem (pa y' e) L.k))
      (L.kgMulAt A t s a e z) fun _ _ => True :=
  RelCT.mono (kgMulAt_tr hA hk hs ha he hz) (fun _ _ ⟨e, ⟨r1, r2, r3⟩, r4, r5, r6⟩ =>
    ⟨KgMulH.of e.1 hc r1 r2 r3, KgMulH.of e.2.1 hc r4 r5 r6, e.eq (kmChk_in hc).1, e.eq (kmChk_in hc).2.1,
      e.eq (kmChk_in hc).2.2.1, e.eq (kmChk_in hc).2.2.2.1, e.eq (kmChk_in hc).2.2.2.2, e.2.2.2⟩) fun _ _ _ => trivial

end

end VG.Proof.MlKem.X86_64
