import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Contract
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Lit
import VerifiedGarbage.Proof.P224.Point
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.P224.X86_64.TaintSums
import VerifiedGarbage.Proof.P224.Prime

/-!
# ECDSA over P-224 on x86-64: `Verified`

P-224 is a curve the proof supports (`p224_ok`, and `Law` for its group law
and `InvSounds` for its inversions, which the registration file supplies:
`Proof.P224.law` and the variant's `inv`), so `sign_ok` gives the contract's
postcondition; the callee-saved registers are restored, `rsp`
is never written, and every store is to `out` or `scratch`, which the return
address is apart from (`abiPreserved`). Constant time by taint tracking: the
only branches are on loop counters, and every address is an argument plus a
constant or a counter.
-/

namespace VG.Proof.Ecdsa.X86_64.P224

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

theorem p224_nBits : Spec.Ecdsa.nBits p224.C = 224 := by
  show Spec.P224.curve.n.log2 + 1 = 224
  have h1 : 223 ≤ Spec.P224.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.P224.curve.n.log2 < 224 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `28` bytes is dropped. -/
theorem p224_sh : p224.sh = 0 := by
  unfold Cfg.sh
  rw [p224_nBits]
  rfl

theorem p224_ok (hI : InvSounds) : CfgOk p224 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P224.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  red_p := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  n_len := by decide +kernel
  n_bits := by decide +kernel
  nbits_le := by decide
  mask h := absurd h (by decide)
  sh := by rw [p224_sh]; decide
  comb d h := by cases h
  inv _ := ⟨by decide, @hI _ _ (by
    show Nat.Prime Spec.P224.curve.p
    rw [show Spec.P224.curve.p = 26959946667150639794667015087019630673557916260026308143510066298881 by decide +kernel]
    exact Proof.P224.prime_26959946667150639794667015087019630673557916260026308143510066298881),
    InvOk.ofMod (by decide +kernel) (by decide)⟩
  inv_n h := absurd h (by decide)
  am3 := by unfold AM3; decide +kernel
  even _ := by decide

/-- P-224 has no comb here: `[k]G` is by the ladder, and there are no tables. -/
theorem p224_tbls : CombTbls p224 := fun d h => by cases h

theorem pre_of {s : State} (h : signX86_64.pre s) : Pre p224 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, h12, h13⟩ := h
  exact ⟨by rw [h1]; rfl, h2, h3, h4, h5, h6, h7, h8, h9, h12, h13,
    by simp [TblsHeld, Cfg.combConsts, Abi.constsHeld, Abi.constRegions, p224]⟩

theorem sign_x86 (hL : Law Spec.P224.curve) (hI : InvSounds) (s : State) (hs : signX86_64.pre s) :
    ∃ t s', Exec isa signP224 s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := sign_ok (p224_ok hI) hL p224_tbls (pre_of hs)
  have hsp : ∀ i ∈ instrs signP224, Taint.clobbers i .rsp = false := by
    have h : signP224.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide
    rw [Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he (by lit_decide)).2.2
  obtain ⟨-, hwr, -, -, -, -, -, -, -, hro, hrs, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ⟨fun r hr => ?_, ?_⟩, hpost⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact Exec.gpr hsp he
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
  · rw [hwr] at F
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hro
      · exact hrs) (by decide)

theorem sign_ct : ConstantTime isa signX86_64.pre signX86_64.pub signP224 := by
  obtain ⟨_, hc⟩ : ∃ h, (taintS.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8]) signP224 h).isSome = true := by
    taint_decide_sum [Proof.P224.X86_64.ladderGSum]
  refine VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8]) ?_ hc
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4, h5⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem sign_verified (hL : Law Spec.P224.curve) (hI : InvSounds) :
    Verified X86_64.target signP224 (Spec.Ecdsa.P224.inst.signContract X86_64.abi) :=
  Verified.of_correct (sign_x86 hL hI) sign_ct implies

end VG.Proof.Ecdsa.X86_64.P224
