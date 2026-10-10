import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Final
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdh.X86.Main

/-!
# ECDSA verification on x86 (32-bit): the whole function

As on AArch64 (`Proof/Ecdsa/Verify/AArch64/Main.lean`).

`verify_ok`: `Cfg.verify` returns 1 exactly if the specification's
verification of the signature holds, for any curve the proof of the code
supports (`CfgOk`) whose group law the proofs support (`Law`), restores the
callee-saved registers, keeps `esp` and writes only the working space.
`front_ok`, `mid_ok`, `points_ok` (with the invariants of the group law for
the two ladders, `step_rep`) and `vtail_ok` compute what
`Proof.Ecdsa.verify_eq` connects to the specification.
-/

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
  have hA : 3 ≤ c.n ∧ c.n ≤ 6 → Point.LadArg s₂ (ptr s₀ 3) Impl.Ecdsa.Verify.X86.Args.verify.ao := fun h =>
    hM.keep.ladArg (A := Impl.Ecdsa.Verify.X86.Args.verify) hp.setup (vArgs_disjI hp (i := 3) (by decide)) (Cfg.stk_28 hcomb h.2)
  refine points_ok hc hM hA
    (Q₁ := fun j X Y Z => Rep c.C X Y Z (mul (sv c (ptr s₀ 3) s₂ U >>> j) (G c.C)))
    (Q₂ := fun j X Y Z => Rep c.C X Y Z (mul (sv c (ptr s₀ 3) s₂ V >>> j) P))
    (step_rep hC hc.onG ha hb hG)
    (by rw [shiftRight_eq_zero hu, mul_zero_pt]; exact rep_infinity' hC)
    (step_rep hC hPc ha hb hQ)
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
    rw [length_bytesAt]; omega
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
  have h16 : 2 * c.C.len = c.C.len + c.C.len := by omega
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
