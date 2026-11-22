module

public import VerifiedGarbage.Proof.Ecdsa.X86.CombLays
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Points
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86
public import VerifiedGarbage.Proof.Ecdsa.X86.Main
import VerifiedGarbage.Proof.Ecdh.X86.Peer
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Final
import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowPoints
import VerifiedGarbage.Proof.Ecdh.X86.Main
import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Spec.Ecdsa.Verify
import VerifiedGarbage.Proof.Weierstrass.X86.Rep

/-! ### `Ecdsa.Verify.X86.Main`, which this module and modules that import it used -/

section

/-!
# ECDSA verification on x86 (32-bit): the whole function

As on AArch64 (`Proof/Ecdsa/Verify/AArch64/Main.lean`).

`verify_ok`: `Cfg.verify` returns 1 exactly if the specification's
verification of the signature holds, for any curve the proof of the code
supports (`CfgOk`) whose group law the proofs support (`Law`), restores the
callee-saved registers, keeps `esp` and writes only the working space.
`front_ok`, `mid_ok`, `points_ok` (with the invariants of the group law for
the two ladders, `step_rep'`) and `vtail_ok` compute what
`Proof.Ecdsa.verify_eq` connects to the specification.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdh.X86
open VG.Impl.Ecdh.X86 (PX PY)
open VG.Impl.Ecdsa.Verify.X86 (U V)

variable {c : Cfg}

/-- The result the contract asks for: 1 exactly if the specification's
verification holds. -/
def VPost (c : Cfg) (s₀ s' : State) : Prop :=
  s'.gpr .eax =
    if Spec.Ecdsa.verify c.C (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 0) (1 + 2 * c.C.len))
      (Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 1) c.C.len))
      (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) (2 * c.C.len)) then 1 else 0

/-- What the function keeps: the callee-saved registers, `esp`, and memory
but the working space and the stack below `esp` the calls use. -/
structure VKeep (c : Cfg) (s₀ s' : State) : Prop where
  saved : ∀ rd ∈ Cfg.saved, s'.gpr rd.1 = s₀.gpr rd.1
  esp : s'.gpr .esp = s₀.gpr .esp
  frame : Frame (s₀.wr ++ [below (s₀.gpr .esp) c.stk]) s₀.mem s'.mem

/-- The return address is kept. -/
theorem VKeep.ret {s₀ s' : State} {extra : List Region} (hp : VPre c s₀ extra) (K : VKeep c s₀ s') :
    s'.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 := by
  refine K.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rw [hp.wr] at hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.ret_sc
  · exact (below_disjoint_ret hp.sp_lo).symm

/-- The stack the parts of `verify` use. -/
structure VSp (c : Cfg) : Prop where
  validate : SpOk (Impl.Ecdh.X86.Cfg.validate c) c.stk
  scalars : SpOk (Impl.Ecdsa.Verify.X86.Cfg.scalars c) c.stk
  nPow : SpOk c.nPow c.stk
  uv : SpOk (Impl.Ecdsa.Verify.X86.Cfg.uv c) c.stk
  points : SpOk (Impl.Ecdsa.Verify.X86.Cfg.points c) c.stk
  pPow : SpOk c.pPow c.stk
  final : SpOk (Impl.Ecdsa.Verify.X86.Cfg.final c) c.stk

theorem VSp.of (h : SpOk (Impl.Ecdsa.Verify.X86.Cfg.verify c) c.stk) : VSp c := by
  have h₁ := h.right.right.right
  have h₂ := h₁.right
  exact ⟨h₁.left, h₂.left, h₂.right.left, h₂.right.right.left, h₂.right.right.right.left,
    h₂.right.right.right.right.left, h₂.right.right.right.right.right⟩

/-- What the slots of `a`, `3b` and `G` stand for. -/
theorem consts_tmv (hc : CfgOk c) {base : Addr} {g : Reg → BitVec 32} {s : State}
    (F : Fixed c base g s.mem) :
    tmv c.C c.n base s (c.sl AP) = Fin.ofNat c.C.p c.C.a ∧
      tmv c.C c.n base s (c.sl B3P) = Fin.ofNat c.C.p (3 * c.C.b) ∧
      tmv c.C c.n base s (c.sl ONEP) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · show toM _ _ (wordsVal s.mem base (c.sl AP) c.n) = _
    rw [F.ap]; exact toM_cmont hc _
  · show toM _ _ (wordsVal s.mem base (c.sl B3P) c.n) = _
    rw [F.b3p]; exact toM_cmont hc _
  · show toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n) = _
    rw [F.onep]; exact toM_one (unitMod_pow_two hc.p_odd _)

/-- `vg_ecdsa_<curve>_verify` returns whether the specification's
verification holds, and restores the callee-saved registers. -/
theorem verify_ok (hc : CfgOk c) (hC : Law c.C) (hcomb : c.comb = none)
    (hsp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.verify c) c.stk)
    {s₀ : State} (hp : VPre c s₀) :
    WP isa (Impl.Ecdsa.Verify.X86.Cfg.verify c) s₀ fun s' => VKeep c s₀ s' ∧ VPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have H := VSp.of hsp
  refine front_ok hc hp H.validate fun s₁ hF => mid_ok hc hF H.scalars H.nPow H.uv fun s₂ hM => ?_
  have F₂ := hM.fixed
  obtain ⟨ha, hb, h1⟩ := consts_tmv hc F₂
  -- The point the second ladder multiplies.
  let P := peerPt c (s₀.mem (ptr s₀ 0) = 4) (keyX c s₀) (keyY c s₀)
  have hPc : onCurve c.C P = true := peerPt_onCurve hc _ _ _
  have hG : Rep c.C (tmv c.C c.n (ptr s₀ 3) s₂ (c.sl GX)) (tmv c.C c.n (ptr s₀ 3) s₂ (c.sl GY))
      (tmv c.C c.n (ptr s₀ 3) s₂ (c.sl ONEP)) (G c.C) := by
    show Rep c.C (toM _ _ (wordsVal s₂.mem _ (c.sl GX) c.n)) (toM _ _ (wordsVal s₂.mem _ (c.sl GY) c.n))
      (toM _ _ (wordsVal s₂.mem _ (c.sl ONEP) c.n)) (G c.C)
    rw [F₂.gx, F₂.gy, toM_cmont hc, toM_cmont hc, show toM c.C.p (2 ^ (64 * c.n))
      (wordsVal s₂.mem (ptr s₀ 3) (c.sl ONEP) c.n) = 1 from h1]
    exact rep_affine' hC _ _
  have hQ : Rep c.C (tmv c.C c.n (ptr s₀ 3) s₂ (c.sl PX)) (tmv c.C c.n (ptr s₀ 3) s₂ (c.sl PY))
      (tmv c.C c.n (ptr s₀ 3) s₂ (c.sl ONEP)) P := by
    rw [h1]
    exact peerPt_rep hC _ _ _ hM.px hM.py
  have hu : sv c (ptr s₀ 3) s₂ U < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  have hv : sv c (ptr s₀ 3) s₂ V < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  have hA : c.mul.isSome ∨ 3 ≤ c.n ∧ c.n ≤ 6 → Point.LadArg s₂ (ptr s₀ 3) Impl.Ecdsa.Verify.X86.Args.verify.ao :=
    fun h => hM.keep.ladArg (A := Impl.Ecdsa.Verify.X86.Args.verify) hp.setup (vArgs_disjI hp (i := 3) (by decide))
      (Cfg.stk_28q hcomb h)
  have h0 : c.qA0 = true → (Fin.ofNat c.C.p c.C.a : Fe c.C) = 0 ∧
      tmv c.C c.n (ptr s₀ 3) s₂ (c.sl ONEP) = 1 := fun h =>
    ⟨by simp only [Impl.Ecdsa.X86.Cfg.qA0, Bool.and_eq_true, beq_iff_eq] at h; rw [h.2.1]; rfl, h1⟩
  refine points_ok hc hM hA
    (Q₁ := fun j X Y Z => Rep c.C X Y Z (mul (sv c (ptr s₀ 3) s₂ U >>> j) (G c.C)))
    (Q₂ := fun j X Y Z => Rep c.C X Y Z (mul (sv c (ptr s₀ 3) s₂ V >>> j) P))
    (step_rep' (L := c.ladderCfg) (base := ptr s₀ 3) (s := s₂) hC hc.onG ha hb hG h0)
    (by rw [shiftRight_eq_zero hu, mul_zero_pt]; exact rep_infinity' hC)
    (step_rep' (L := Impl.Ecdh.X86.Cfg.ladderQ c) (base := ptr s₀ 3) (s := s₂) hC hPc ha hb hQ h0)
    (by rw [shiftRight_eq_zero hv, mul_zero_pt]; exact rep_infinity' hC) H.points
    fun s₃ hP => ?_
  refine WP.mono (vtail_ok hc hP H.pPow H.final) fun s' ⟨saved, esp, frame, xo, hxo, hx, ret⟩ =>
    ⟨⟨saved, esp, frame⟩, ?_⟩
  obtain ⟨X1, Y1, Z1, X2, Y2, Z2, q1, q2, hsum⟩ := hP.pt
  have q1' : Rep c.C X1 Y1 Z1 (mul (sv c (ptr s₀ 3) s₂ U) (G c.C)) := by
    have := q1; simp only [Nat.shiftRight_zero] at this; exact this
  have q2' : Rep c.C X2 Y2 Z2 (mul (sv c (ptr s₀ 3) s₂ V) P) := by
    have := q2; simp only [Nat.shiftRight_zero] at this; exact this
  have hR := Rep.add hC (hC.onCurve_mul hc.onG _) (hC.onCurve_mul hPc _) q1' q2' hsum.symm
  -- The arguments as the specification reads them.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 0) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega_using []
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 0) (1 + 2 * c.C.len)).head? = some (s₀.mem (ptr s₀ 0)) := by
    rw [peer_bytes]; rfl
  have hxv : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 0) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s₀ := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
  have hyv : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 0) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s₀ := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (ptr s₀ 0)) (keyX c s₀) (keyY c s₀),
      P = .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    show peerPt c _ _ _ = _
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have h16 : 2 * c.C.len = c.C.len + c.C.len := by omega_using []
  have hr : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) (2 * c.C.len)).take c.C.len) = sigR c s₀ := by
    rw [h16, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]
  have hs : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) (2 * c.C.len)).drop c.C.len) = sigS c s₀ := by
    rw [h16, bytesAt_add, List.drop_left' (length_bytesAt _ _ _)]
  have hspec := Proof.Ecdsa.verify_eq hC hlen hb0 hxv hyv hP' hr hs hM.u_lt hM.v_lt hM.u hM.v hR hxo hx
  -- The conditions.
  have hz := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
  have hiff : (Ecdh.Valid c.C (s₀.mem (ptr s₀ 0)) (keyX c s₀) (keyY c s₀) ∧
      (1 ≤ sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (1 ≤ sigS c s₀ ∧ sigS c s₀ < c.C.n) ∧
      tmv c.C c.n (ptr s₀ 3) s₃ (c.sl RZ) ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) ↔
      ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
        sv c (ptr s₀ 3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
    constructor
    · rintro ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hZ, he⟩
      exact ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hz.mp hZ, he⟩
    · rintro ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hZ, he⟩
      exact ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hz.mpr hZ, he⟩
  unfold VPost
  rw [hashToInt_eq c, hspec, ret]
  by_cases h : (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
      sv c (ptr s₀ 3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)
  · rw [ite_eq_left (decide_eq_true (hiff.mpr h)), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp (of_decide_eq_true h'))), ite_eq_right h]

end VG.Proof.Ecdsa.Verify.X86

end

end

/-! ### `Ecdsa.Verify.X86.ProjectiveFinal`, which only this module used -/

section

/-! ### `Ecdsa.Verify.X86.ProjectiveArithmetic`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdh.X86
open VG.Impl.Ecdsa.Verify.X86.Cfg (projectiveOps)
variable {c : VG.Impl.Ecdsa.X86.Cfg}

abbrev projectiveSlots : List Nat := [X, XM, RZ, W, RX, ACC, XN]
abbrev projectiveReads : List Nat := [XM, RZ, RX, ACC]
abbrev projectiveWrites : List Nat := [X, W, XM, X, XN, TMP]

theorem projectiveOps_rename (sl : Nat → Nat) :
    projectiveOps sl = (projectiveOps id).map (FOp.rename sl) := rfl

theorem projectiveOps_run (hc : CfgOk c) (e : Nat → Fe c.C) :
    runOps (projectiveOps c.sl) e (c.sl W) = e (c.sl RX) - e (c.sl XM) * e (c.sl RZ) ∧
    runOps (projectiveOps c.sl) e (c.sl XN) =
      e (c.sl RX) - (e (c.sl XM) + e (c.sl ACC)) * e (c.sl RZ) := by
  obtain H := runOps_rename c.sl (projectiveOps id) e (fun _ _ _ h => sl_inj c hc.n0 h)
  rw [← projectiveOps_rename] at H
  exact ⟨congrFun H W, congrFun H XN⟩

/-- The five field operations compute both projective differences. -/
theorem projectiveOps_ok (hc : CfgOk c) {s : State} {base : Addr}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ projectiveReads, sv c base s i < c.C.p) :
    WP isa (fprog c.SP (projectiveOps c.sl)) s fun t =>
      Scr t base size ∧ t.gpr .esp = s.gpr .esp ∧ Unch base (slWk c projectiveWrites) s.mem t.mem ∧
      sv c base t W < c.C.p ∧ sv c base t XN < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t W) =
        tmv c.C c.n base s (c.sl RX) - tmv c.C c.n base s (c.sl XM) * tmv c.C c.n base s (c.sl RZ) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t XN) =
        tmv c.C c.n base s (c.sl RX) -
          (tmv c.C c.n base s (c.sl XM) + tmv c.C c.n base s (c.sl ACC)) * tmv c.C c.n base s (c.sl RZ) := by
  obtain hL : Lay c.MP' size (· ∈ projectiveSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain hW : WkOk c.SP c.MP' c.C.p size c.wk (· ∈ projectiveSlots.map c.sl) :=
    wkOk_map hc hc.fp (MP'_n c) (jm := MP) (by decide) rfl rfl (by decide)
  obtain I : Inv c.MP' base size c.C.p (· ∈ projectiveSlots.map c.sl) (projectiveReads.map c.sl)
      (tmv c.C c.n base s) s := by
    refine ⟨hs, hM, ?_, ?_, fun _ _ => rfl⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      obtain sub : ∀ i ∈ projectiveReads, i ∈ projectiveSlots := by decide
      exact List.mem_map_of_mem (sub i hi)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact hlt i hi
  obtain reads : readsOk (projectiveOps c.sl) (projectiveReads.map c.sl) = true := by
    rw [projectiveOps_rename]
    exact readsOk_rename c.sl (by decide)
  refine WP.mono (fprog_ok hL hW (unitMod_pow_two hc.p_odd _) _ I ?_ reads)
    fun t ⟨keep, It⟩ => ?_
  · intro op hop x hx
    simp only [projectiveOps, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> exact List.mem_map_of_mem (by decide)
  obtain w : c.sl W ∈ validAfter (projectiveOps c.sl) (projectiveReads.map c.sl) := by
    simp [mem_validAfter, projectiveOps, FOp.out]
  obtain xn : c.sl XN ∈ validAfter (projectiveOps c.sl) (projectiveReads.map c.sl) := by
    simp [mem_validAfter, projectiveOps, FOp.out]
  obtain run := projectiveOps_run hc (tmv c.C c.n base s)
  exact ⟨It.scr, keep.gpr _ (by decide), (by simpa only [progW, projectiveOps, List.map_cons, List.map_nil, FOp.out, List.append_assoc, slWk, slW, projectiveWrites, accLen_MP', MP'_n, show c.MP'.tmp = c.sl TMP from rfl, List.cons_append, List.nil_append] using keep.unch), It.lt _ w, It.lt _ xn, (It.val _ w).trans run.1, (It.val _ xn).trans run.2⟩


abbrev projectivePrepareW : List Nat := [XM, ACC, MN]
abbrev projectiveAllW : List Nat := [XM, ACC, MN, X, W, XN, TMP]

theorem projectivePrepare_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) :
    WP isa (.block (Impl.Ecdsa.Verify.X86.Cfg.projectivePrepare c)) s fun t =>
      Scr t base size ∧ t.gpr .esp = s.gpr .esp ∧ Unch base (slW c projectivePrepareW) s.mem t.mem ∧
      sv c base t XM = c.R * c.R % c.C.p ∧ sv c base t ACC = c.mont c.C.n ∧
      sv c base t MN = c.C.p - c.C.n := by
  have hp := hc.p_ge
  have hpR := hc.p_lt
  obtain r2 : c.R * c.R % c.C.p < 2 ^ (64 * c.n) :=
    Nat.lt_trans (Nat.mod_lt _ (by omega_using [hp])) hpR
  obtain mont : c.mont c.C.n < 2 ^ (64 * c.n) :=
    Nat.lt_trans (Nat.mod_lt _ (by omega_using [hp])) hpR
  obtain sub : c.C.p - c.C.n < 2 ^ (64 * c.n) := by omega_using [hpR]
  rw [Impl.Ecdsa.Verify.X86.Cfg.projectivePrepare, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setConst_ok hs (sl_le c hc.n10 (i := XM) (by decide)) r2) fun s₁ ⟨e₁,k₁,O₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₁ (sl_le c hc.n10 (i := ACC) (by decide)) mont) fun s₂ ⟨e₂,k₂,O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (setConst_ok hs₂ (sl_le c hc.n10 (i := MN) (by decide)) sub) fun s₃ ⟨e₃,k₃,O₃⟩ => ?_
  obtain o : ∀ {s t : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem t.mem → i < 45 → i ≠ j →
      sv c base t i = sv c base s i := fun O hi hij => sv_out O hc.n10 hs.nowrap hi hij
  exact ⟨hs₂.of_keeps k₃ (by decide), by rw [k₃.1 _ (by decide), k₂.1 _ (by decide), k₁.1 _ (by decide)], O₁.unch.trans (O₂.unch.trans O₃.unch),
    by rw [o O₃ (by decide) (by decide), o O₂ (by decide) (by decide)]; exact e₁,
    by rw [o O₃ (by decide) (by decide)]; exact e₂, e₃⟩

/-- Prepare constants, convert `r`, and compute both differences. -/
theorem projectiveArithmetic_ok (hc : CfgOk c) {s : State} {base : Addr}
    (hs : Scr s base size) (hmp : sv c base s MP = c.C.p)
    (hrx : sv c base s RX < c.C.p) (hrz : sv c base s RZ < c.C.p) :
    WP isa (.seq (.block (Impl.Ecdsa.Verify.X86.Cfg.projectivePrepare c))
      (.seq (Mont.mulCall c.SP (c.sl XM) (c.sl K) (c.sl XM))
        (fprog c.SP (projectiveOps c.sl)))) s fun t =>
      Scr t base size ∧ t.gpr .esp = s.gpr .esp ∧ Unch base (slWk c projectiveAllW) s.mem t.mem ∧
      sv c base t MN = c.C.p - c.C.n ∧ sv c base t W < c.C.p ∧ sv c base t XN < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t W) =
        tmv c.C c.n base s (c.sl RX) - Fin.ofNat c.C.p (sv c base s K) * tmv c.C c.n base s (c.sl RZ) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t XN) =
        tmv c.C c.n base s (c.sl RX) -
          (Fin.ofNat c.C.p (sv c base s K) + Fin.ofNat c.C.p c.C.n) * tmv c.C c.n base s (c.sl RZ) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp := hc.p_ge
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine WP.seq (WP.mono (projectivePrepare_ok hc hs) fun s₁ ⟨hs₁,esp₁,U₁,xm₁,acc₁,mn₁⟩ => ?_)
  obtain v₁ : ∀ {i}, i < 45 → i ∉ projectivePrepareW → sv c base s₁ i = sv c base s i :=
    fun hi hl => sv_unch U₁ h7 hn hi (apart_slW hl)
  obtain M₁ : ModOkW c.MP' size c.C.p s₁.mem base := modP_of hc
    ((v₁ (i := MP) (by decide) (by decide)).trans hmp)
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) hc.fp h7 hs₁ (o := XM) (a := K) (b := XM)
    (by decide) (by decide) (by decide) (by rw [xm₁]; exact Nat.mod_lt _ (by omega_using [hrx])))
    fun s₂ ⟨k₂,lt₂,e₂⟩ => ?_)
  obtain hs₂ := k₂.scr hs₁
  obtain v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ TMP → sv c base s₂ i = sv c base s₁ i :=
    fun hi hio hit => sv_keep (MP'_n c) rfl h7 hn k₂ hi hio hit
  obtain M₂ := M₁.keepX86 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  obtain xm₂ : tmv c.C c.n base s₂ (c.sl XM) = Fin.ofNat c.C.p (sv c base s K) := by
    show toM _ _ (sv c base s₂ XM) = _
    rw [toM_r2 (A := sv c base s₁ K) hpR (by rw [e₂, xm₁]; rfl), v₁ (by decide) (by decide)]
  obtain acc₂ : tmv c.C c.n base s₂ (c.sl ACC) = Fin.ofNat c.C.p c.C.n := by
    show toM _ _ (sv c base s₂ ACC) = _
    rw [v₂ (by decide) (by decide) (by decide), acc₁]
    exact toM_cmont hc _
  obtain tv₂ : ∀ {i}, i < 45 → i ∉ projectivePrepareW → i ≠ TMP →
      tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := fun {i} hi hl ht => by
    show toM _ _ (sv c base s₂ i) = toM _ _ (sv c base s i)
    rw [v₂ hi (fun he => hl (by rw [he]; decide)) ht, v₁ hi hl]
  refine WP.mono (projectiveOps_ok hc hs₂ M₂ (fun i hi => ?_)) fun s₃ ⟨hs₃,esp₃,U₃,wlt,xnlt,wval,xnval⟩ => ?_
  · simp only [projectiveReads, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact lt₂
    · rw [v₂ (by decide) (by decide) (by decide), v₁ (by decide) (by decide)]; exact hrz
    · rw [v₂ (by decide) (by decide) (by decide), v₁ (by decide) (by decide)]; exact hrx
    · rw [v₂ (by decide) (by decide) (by decide), acc₁]; exact Nat.mod_lt _ (by omega_using [hrx])
  obtain U₂ : Unch base (slWk c [XM, TMP]) s₁.mem s₂.mem := by simpa only [accLen_MP', MP'_n, show c.MP'.tmp = c.sl TMP from rfl, slWk, slW, List.map_cons, List.map_nil, List.cons_append, List.nil_append] using k₂.unch
  obtain U : Unch base (slWk c projectiveAllW) s.mem s₃.mem :=
    ((U₁.trans U₂).trans U₃).mono (by
      intro w hw
      simp only [slWk, slW, projectivePrepareW, projectiveWrites, projectiveAllW, List.map_cons, List.map_nil,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with ((h | h | h) | ((h | h) | h)) | ((h | h | h | h | h | h) | h) <;> simp [h])
  obtain mn₃ : sv c base s₃ MN = c.C.p - c.C.n := by
    obtain kept : sv c base s₃ MN = sv c base s₂ MN :=
      sv_unch U₃ h7 hn (i := MN) (by decide) (apart_slWk (by decide) (by decide))
    rw [kept, v₂ (by decide) (by decide) (by decide), mn₁]
  refine ⟨hs₃, by rw [esp₃, k₂.gpr _ (by decide), esp₁], U,mn₃,wlt,xnlt,?_,?_⟩
  · rw [wval, xm₂, tv₂ (by decide) (by decide) (by decide), tv₂ (by decide) (by decide) (by decide)]
  · rw [xnval, xm₂, acc₂, tv₂ (by decide) (by decide) (by decide), tv₂ (by decide) (by decide) (by decide)]

end VG.Proof.Ecdsa.Verify.X86

end

end

/-! ### `Ecdsa.Verify.X86.ProjectiveFlags`, which only this module used -/

section

/-! # Masks for the inversion-free x86 ECDSA comparison -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdh.X86
open VG.Impl.Ecdsa.Verify.X86 (W XN)
variable {c : Cfg}

theorem projective_mask_or (p q : Prop) [Decidable p] [Decidable q] :
    mask32 p ||| mask32 q = mask32 (p ∨ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [mask32, hp, hq]

/-- Both equalities and the bound on the second lift, as one mask. -/
theorem projectiveMatch_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) :
    WP isa (.block (Impl.Ecdsa.Verify.X86.Cfg.projectiveMatch c)) s fun t =>
      t.gpr .edx = mask32 (sv c base s W = 0 ∨
        (sv c base s K < sv c base s MN ∧ sv c base s XN = 0)) ∧
      Keeps [.eax, .ebx, .ecx, .edx] s t ∧ t.mem = s.mem := by
  rw [Impl.Ecdsa.Verify.X86.Cfg.projectiveMatch]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (nonzero_ok c hs hc.n0 (sl_le c hc.n10 (i := W) (by decide)))
    fun s₁ ⟨e₁,k₁,m₁⟩ => ?_)
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine wp_logicS (.inr rfl) rfl fun s₂ u₂ => ?_
  refine wp_movS rfl fun s₃ u₃ _ => ?_
  obtain k₃ : Keeps [.eax, .ebx, .ecx, .edx] s s₃ := ((k₁.mono (by decide)).widen u₂.keeps).widen u₃.keeps
  refine WP.block_append (WP.mono (ltN_ok c (hs.of_keeps k₃ (by decide)) hc.n0
    (sl_le c hc.n10 (i := K) (by decide)) (sl_le c hc.n10 (i := MN) (by decide))) fun s₄ ⟨e₄,k₄,m₄⟩ => ?_)
  obtain k₄' := k₃.widen k₄
  refine WP.block_append (WP.mono (nonzero_ok c (hs.of_keeps k₄' (by decide)) hc.n0
    (sl_le c hc.n10 (i := XN) (by decide))) fun s₅ ⟨e₅,k₅,m₅⟩ => ?_)
  refine wp_logicS (.inr rfl) rfl fun s₆ u₆ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₇ u₇ => ?_
  refine wp_orS rfl fun s₈ u₈ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [u₈.gpr, u₇.gpr, u₆.gpr, e₅, u₆.other _ (by decide), k₅.1 _ (by decide), e₄,
      u₇.other _ (by decide), u₆.other _ (by decide), k₅.1 _ (by decide), k₄.1 _ (by decide),
      u₃.gpr, u₂.gpr, e₁, m₄, u₃.mem, u₂.mem, m₁]
    simp only [reduceCtorEq, ite_false, ite_true, mask_not, ne_eq, not_not, mask32_and, projective_mask_or,
      sv, and_comm, or_comm]
  · exact (((k₄'.widen k₅).widen u₆.keeps).widen u₇.keeps).widen u₈.keeps
  · rw [u₈.mem, u₇.mem, u₆.mem, m₅, m₄, u₃.mem, u₂.mem, m₁]

/-- The masks, return value, and restoration change only the flag word. -/
theorem projectiveChecks_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    {g : Reg → BitVec 32} (saved : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1)
    (A : Prop) [Decidable A] (hf : flagW c base s = mask32 A) :
    WP isa (.block (Impl.Ecdsa.Verify.X86.Cfg.projectiveChecks c)) s fun t =>
      (∀ rd ∈ Cfg.saved, t.gpr rd.1 = g rd.1) ∧ t.gpr .esp = s.gpr .esp ∧
      Unch base [(c.sl FLAG, 4)] s.mem t.mem ∧
      t.gpr .eax = if A ∧ sv c base s RZ ≠ 0 ∧
        (sv c base s W = 0 ∨ (sv c base s K < sv c base s MN ∧ sv c base s XN = 0)) then 1 else 0 := by
  have h0 := hc.n0
  have h7 := hc.n10
  obtain hflag : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_using [h0, this]
  rw [Impl.Ecdsa.Verify.X86.Cfg.projectiveChecks]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (projectiveMatch_ok hc hs) fun s₁ ⟨e₁,k₁,m₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.block_append (WP.mono (andFlag_ok c hs₁ hflag) fun s₂ ⟨e₂,k₂,O₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.block_append (WP.mono (checkNonzero_ok c hs₂ h0 (sl_le c h7 (i := RZ) (by decide)) hflag)
    fun s₃ ⟨e₃,k₃,O₃⟩ => ?_)
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  obtain U : Unch base [(c.sl FLAG, 4)] s.mem s₃.mem := by
    rw [← m₁]
    exact (O₂.unch.trans O₃.unch).mono (by intro w hw; simpa using hw)
  obtain saved₃ : ∀ rd ∈ Cfg.saved, s₃.mem.readW (off base rd.2) 32 = g rd.1 := by
    intro rd hr
    obtain bound : rd.2 + 4 ≤ 16 := by revert rd; decide
    rw [Unch.readW32 U (fun w hw => by rw [List.mem_singleton.mp hw]; left; rw [sl_eq]; omega_using [bound]) (by omega_using [bound])]
    exact saved rd hr
  obtain z₂ : wordsVal s₂.mem base (c.sl RZ) c.n = sv c base s RZ := by
    rw [show wordsVal s₂.mem base (c.sl RZ) c.n = sv c base s₁ RZ from
      sv_flag O₂ h0 h7 hs.nowrap (by decide) (by decide)]
    show wordsVal s₁.mem base (c.sl RZ) c.n = _
    rw [m₁]
  obtain flag₃ : flagW c base s₃ = mask32 (A ∧ sv c base s RZ ≠ 0 ∧
      (sv c base s W = 0 ∨ (sv c base s K < sv c base s MN ∧ sv c base s XN = 0))) := by
    rw [e₃,e₂,flagW,m₁,← flagW,hf,e₁,z₂,mask32_and,mask32_and]
    simp only [and_left_comm, and_comm]
  refine WP.mono (vfinish_ok hc hs₃ saved₃ (decide (A ∧ sv c base s RZ ≠ 0 ∧
    (sv c base s W = 0 ∨ (sv c base s K < sv c base s MN ∧ sv c base s XN = 0))))
    (by simpa only [decide_eq_true_eq] using flag₃)) fun t ⟨hm,ret,keep,esp⟩ => ?_
  refine ⟨keep, ?_, ?_, ?_⟩
  · rw [esp,k₃.1 _ (by decide),k₂.1 _ (by decide),k₁.1 _ (by decide)]
  · rw [hm]; exact U
  · simpa only [decide_eq_true_eq] using ret

end VG.Proof.Ecdsa.Verify.X86

end

end


@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdh.X86
variable {c : VG.Impl.Ecdsa.X86.Cfg}

/-- The inversion-free final check has the same result as affine conversion. -/
theorem projectiveFinal_ok (hc : CfgOk c) (hC : Law c.C) (hnp : c.C.n < c.C.p)
    (hpn : c.C.p ≤ 2 * c.C.n) (hm : c.mul = none) {s₀ : State} {base : Addr}
    {Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop} {s : State} (hP : Pts c s₀ base Q₁ Q₂ s)
    (hsp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.projectiveFinal c) c.stk) :
    WP isa (Impl.Ecdsa.Verify.X86.Cfg.projectiveFinal c) s fun s' =>
      (∀ rd ∈ VG.Impl.Ecdsa.X86.Cfg.saved, s'.gpr rd.1 = s₀.gpr rd.1) ∧ s'.gpr .esp = s₀.gpr .esp ∧
      Frame (s₀.wr ++ [below (s₀.gpr .esp) c.stk]) s₀.mem s'.mem ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        s'.gpr .eax = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hP.scr.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  let A := KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
    (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)
  let fx := tmv c.C c.n base s (c.sl RX)
  let fz := tmv c.C c.n base s (c.sl RZ)
  let xo := (fx * fz ^ (c.C.p - 2)).val
  refine hP.keep.withSp hsp ?_
  rw [Impl.Ecdsa.Verify.X86.Cfg.projectiveFinal]
  refine WP.seq (WP.mono (projectiveArithmetic_ok hc hP.scr hP.fixed.mp hP.rx_lt hP.rz_lt)
    fun t ⟨ht,esp,U,mn,wlt,xnlt,wval,xnval⟩ => ?_)
  obtain v : ∀ {i}, i < 45 → i ∉ projectiveAllW → sv c base t i = sv c base s i :=
    fun hi hl => sv_unch U h7 hn hi (apart_slWk hi hl)
  obtain saved : ∀ rd ∈ Cfg.saved, t.mem.readW (off base rd.2) 32 = s₀.gpr rd.1 := by
    intro rd hr
    obtain bound : rd.2 + 4 ≤ 16 := by revert rd; decide
    rw [Unch.readW32 U (fun w hw => ?_) (by omega_arith)]
    · exact hP.fixed.saved rd hr
    · rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        left; rw [sl_eq]; omega_arith
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        left
        have := sl_below_wk c (i := FLAG) (by decide)
        rw [sl_eq] at this
        rcases hw with rfl | rfl
        · omega_arith
        · dsimp only [Mont.outW]; omega_arith
  obtain flag : flagW c base t = mask32 A := by
    rw [flagW, flag_unch U h7 h0 hn (by decide)]
    exact hP.flag
  obtain wz : sv c base t W = 0 ↔ fx = Fin.ofNat c.C.p (sigR c s₀) * fz := by
    rw [← toM_eq_zero_iff hpR wlt, wval, hP.k hm]
    change fx - Fin.ofNat c.C.p (sigR c s₀) * fz = 0 ↔ _
    constructor <;> intro h <;> grind
  obtain xnz : sv c base t XN = 0 ↔ fx = (Fin.ofNat c.C.p (sigR c s₀) + Fin.ofNat c.C.p c.C.n) * fz := by
    rw [← toM_eq_zero_iff hpR xnlt, xnval, hP.k hm]
    change fx - (Fin.ofNat c.C.p (sigR c s₀) + Fin.ofNat c.C.p c.C.n) * fz = 0 ↔ _
    constructor <;> intro h <;> grind
  obtain z : fz ≠ 0 ↔ sv c base s RZ ≠ 0 := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
  refine WP.mono (projectiveChecks_ok hc ht saved A flag) fun s' ⟨keep,esp',U',ret⟩ fr => ?_
  refine ⟨keep, by rw [esp',esp,hP.esp], fr, xo, (fx * fz ^ (c.C.p - 2)).isLt, Fin.ofNat_val_eq_self _, ?_⟩
  simp only [v (i := RZ) (by decide) (by decide), v (i := K) (by decide) (by decide), hP.k hm, mn, wz, xnz] at ret
  obtain iff : (A ∧ sv c base s RZ ≠ 0 ∧
      (fx = Fin.ofNat c.C.p (sigR c s₀) * fz ∨
        (sigR c s₀ < c.C.p - c.C.n ∧ fx = (Fin.ofNat c.C.p (sigR c s₀) + Fin.ofNat c.C.p c.C.n) * fz))) ↔
      (A ∧ sv c base s RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
    constructor
    · rintro ⟨ha,hz,hm⟩
      exact ⟨ha,hz,(Proof.Ecdsa.projective_matches hC hnp hpn (z.mpr hz) ha.2.1.2).mpr hm⟩
    · rintro ⟨ha,hz,hm⟩
      exact ⟨ha,hz,(Proof.Ecdsa.projective_matches hC hnp hpn (z.mpr hz) ha.2.1.2).mp hm⟩
  simpa only [iff] using ret

theorem tail_dispatch_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State} {base : Addr}
    {Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop} {s : State} (hP : Pts c s₀ base Q₁ Q₂ s)
    (hsp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.tail c) c.stk) :
    WP isa (Impl.Ecdsa.Verify.X86.Cfg.tail c) s fun s' =>
      (∀ rd ∈ VG.Impl.Ecdsa.X86.Cfg.saved, s'.gpr rd.1 = s₀.gpr rd.1) ∧ s'.gpr .esp = s₀.gpr .esp ∧
      Frame (s₀.wr ++ [below (s₀.gpr .esp) c.stk]) s₀.mem s'.mem ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        s'.gpr .eax = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 := by
  unfold Impl.Ecdsa.Verify.X86.Cfg.tail at hsp ⊢
  by_cases h : c.mul.isNone ∧ c.C.len = 32 ∧ c.C.n < c.C.p ∧ c.C.p ≤ 2 * c.C.n
  · rw [ite_eq_left h] at hsp ⊢
    exact projectiveFinal_ok hc hC h.2.2.1 h.2.2.2 (Option.isNone_iff_eq_none.mp h.1) hP hsp
  · rw [ite_eq_right h] at hsp ⊢
    exact vtail_ok hc hP hsp.left hsp.right

end VG.Proof.Ecdsa.Verify.X86

end

end


@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdh.X86
open VG.Impl.Ecdh.X86 (PX PY)
open VG.Impl.Ecdsa.Verify.X86 (U V)

variable {c : Cfg}

/-- The stack the parts of `verifyCombBody` use. -/
structure VCSp (c : Cfg) : Prop where
  validate : SpOk (Impl.Ecdh.X86.Cfg.validate c) c.stk
  scalars : SpOk (Impl.Ecdsa.Verify.X86.Cfg.scalars c) c.stk
  nPow : SpOk c.nPow c.stk
  uv : SpOk (Impl.Ecdsa.Verify.X86.Cfg.uv c) c.stk
  points : SpOk (Impl.Ecdsa.Verify.X86.Cfg.pointsComb c) c.stk
  tail : SpOk (Impl.Ecdsa.Verify.X86.Cfg.tail c) c.stk

theorem VCSp.of (h : SpOk (Impl.Ecdsa.Verify.X86.Cfg.verifyCombBody c) c.stk) : VCSp c := by
  have h₁ := h.left.right.right.right.left
  have h₂ := h.right.left
  have h₃ := h.right.right
  exact ⟨h₁, h₂.left, h₂.right.left, h₂.right.right.left, h₃.left, h₃.right⟩

theorem verifyCombBody_ok (hc : CfgOk c) (hC : Law c.C) (hne : c.C.n < 2 ^ (8 * c.C.len)) (hT : CombTbls c)
    (hCo : ∀ d, c.comb = some d → CombOk c d) (ham3 : c.n = 4 ∧ c.combJac = true → AM3 c.C)
    {s₀ : State} {extra : List Region} (hp : VPre c s₀ extra)
    (hTb : ∀ d, c.comb = some d → TblMem s₀ ((s₀.gpr .eax).setWidth 64) (c.combWords d) ∧
      (∀ i < (c.combWords d).length, ∀ b < 8,
        size ≤ ofs (ptr s₀ 3) ((s₀.gpr .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) ∧
      ∀ r ∈ s₀.wr ++ [below (s₀.gpr .esp) c.stk],
        Region.Disjoint ⟨(s₀.gpr .eax).setWidth 64, 8 * (c.combWords d).length⟩ r)
    (h24 : c.stk = 24) (hspG : SpOk c.gMul c.stk) (hsp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.verifyCombBody c) c.stk) :
    WP isa (Impl.Ecdsa.Verify.X86.Cfg.verifyCombBody c) s₀ fun s' => VKeep c s₀ s' ∧ VPost c s₀ s' := by
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  obtain H := VCSp.of hsp
  refine WP.seq (WP.mono (front_ok hc hp H.validate (rest := .block []) (fun _ h => WP.block_nil h))
    fun s₁ hF => ?_)
  refine WP.seq (WP.mono (mid_ok hc hF H.scalars H.nPow H.uv (rest := .block []) (fun _ h => WP.block_nil h))
    fun s₂ hM => ?_)
  have F₂ := hM.fixed
  obtain ⟨_, _, h1⟩ := consts_tmv hc F₂
  -- The point the variable-base method multiplies.
  let P := peerPt c (s₀.mem (ptr s₀ 0) = 4) (keyX c s₀) (keyY c s₀)
  obtain hPc : onCurve c.C P = true := peerPt_onCurve hc _ _ _
  obtain hQ : Rep c.C (tmv c.C c.n (ptr s₀ 3) s₂ (c.sl PX)) (tmv c.C c.n (ptr s₀ 3) s₂ (c.sl PY))
      (tmv c.C c.n (ptr s₀ 3) s₂ (c.sl ONEP)) P := by
    rw [h1]
    exact peerPt_rep hC _ _ _ hM.px hM.py
  refine pointsComb_ok hc hC hne hT hCo ham3 hM
    (fun d hd => by
      obtain ⟨ht, ho, hap⟩ := hTb d hd
      exact ⟨ht.of_frame (by rw [hM.rd, hM.wr]) hM.whole hap, ho, hap⟩)
    hPc hQ hp.stk_wr h24 hspG H.points
    fun s₃ hP => ?_
  refine WP.mono (tail_dispatch_ok hc hC hP H.tail) fun s' ⟨saved, esp, frame, xo, hxo, hx, ret⟩ =>
    ⟨⟨saved, esp, frame⟩, ?_⟩
  obtain ⟨X1, Y1, Z1, X2, Y2, Z2, q1, q2, hsum⟩ := hP.pt
  obtain q1' : Rep c.C X1 Y1 Z1 (mul (sv c (ptr s₀ 3) s₂ U) (G c.C)) := by
    have := q1; simp only [Nat.shiftRight_zero] at this; exact this
  obtain q2' : Rep c.C X2 Y2 Z2 (mul (sv c (ptr s₀ 3) s₂ V) P) := by
    have := q2; simp only [Nat.shiftRight_zero] at this; exact this
  obtain hR := Rep.add hC (hC.onCurve_mul hc.onG _) (hC.onCurve_mul hPc _) q1' q2' hsum.symm
  -- The arguments as the specification reads them.
  obtain hlen : (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 0) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega_using []
  obtain hb0 : (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 0) (1 + 2 * c.C.len)).head? = some (s₀.mem (ptr s₀ 0)) := by
    rw [peer_bytes]; rfl
  obtain hxv : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 0) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s₀ := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
  obtain hyv : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 0) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s₀ := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  obtain hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (ptr s₀ 0)) (keyX c s₀) (keyY c s₀),
      P = .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    show peerPt c _ _ _ = _
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  obtain h16 : 2 * c.C.len = c.C.len + c.C.len := by omega_using []
  obtain hr : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) (2 * c.C.len)).take c.C.len) = sigR c s₀ := by
    rw [h16, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]
  obtain hs : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) (2 * c.C.len)).drop c.C.len) = sigS c s₀ := by
    rw [h16, bytesAt_add, List.drop_left' (length_bytesAt _ _ _)]
  obtain hspec := Proof.Ecdsa.verify_eq hC hlen hb0 hxv hyv hP' hr hs hM.u_lt hM.v_lt hM.u hM.v hR hxo hx
  -- The conditions.
  obtain hz := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
  obtain hiff : (Ecdh.Valid c.C (s₀.mem (ptr s₀ 0)) (keyX c s₀) (keyY c s₀) ∧
      (1 ≤ sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (1 ≤ sigS c s₀ ∧ sigS c s₀ < c.C.n) ∧
      tmv c.C c.n (ptr s₀ 3) s₃ (c.sl RZ) ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) ↔
      ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
        sv c (ptr s₀ 3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
    constructor
    · rintro ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hZ, he⟩
      exact ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hz.mp hZ, he⟩
    · rintro ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hZ, he⟩
      exact ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hz.mpr hZ, he⟩
  unfold VPost
  rw [hashToInt_eq c, hspec, ret]
  by_cases h : (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
      sv c (ptr s₀ 3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)
  · rw [ite_eq_left (decide_eq_true (hiff.mpr h)), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp (of_decide_eq_true h'))), ite_eq_right h]

end VG.Proof.Ecdsa.Verify.X86
