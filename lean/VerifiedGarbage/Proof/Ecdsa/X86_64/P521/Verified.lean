import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Contract
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Lit
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.P521.X86_64.TaintSums

/-!
# ECDSA over P-521 on x86-64: `Verified`

P-521 is a curve the proof supports (`p521_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.P521.law`), so `sign_ok` gives
the contract's postcondition; the callee-saved registers are restored, `rsp`
is never written, and every store is to `out` or `scratch`, which the return
address is apart from (`abiPreserved`). Constant time by taint tracking: the
only branches are on loop counters, and every address is an argument plus a
constant or a counter.
-/

namespace VG.Proof.Ecdsa.X86_64.P521

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

theorem p521_nBits : Spec.Ecdsa.nBits p521.C = 521 := by
  show Spec.P521.curve.n.log2 + 1 = 521
  have h1 : 520 ≤ Spec.P521.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.P521.curve.n.log2 < 521 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- A hash of `66` bytes drops its last 7 bits. -/
theorem p521_sh : p521.sh = 7 := by
  unfold Cfg.sh
  rw [p521_nBits]
  rfl

theorem p521_ok : CfgOk p521 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P521.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  sh := by rw [p521_sh]; decide
  comb d h := by cases h
  inv h := absurd h (by decide)
  inv_n h := absurd h (by decide)

/-- P-521 has no comb: `[k]G` is by the ladder, and there are no tables. -/
theorem p521_tbls : CombTbls p521 := fun d h => by cases h

theorem pre_of {s : State} (h : signX86_64.pre s) : Pre p521 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, h12, h13⟩ := h
  exact ⟨by rw [h1]; rfl, h2, h3, h4, h5, h6, h7, h8, h9, h12, h13,
    by simp [TblsHeld, Cfg.combConsts, Abi.constsHeld, Abi.constRegions, p521]⟩

theorem sign_x86 (hL : Law Spec.P521.curve) (s : State) (hs : signX86_64.pre s) :
    ∃ t s', Exec isa signP521 s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := sign_ok p521_ok hL p521_tbls (pre_of hs)
  have hsp : ∀ i ∈ instrs signP521, Taint.clobbers i .rsp = false := by
    have h : signP521.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide
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

theorem sign_ct : ConstantTime isa signX86_64.pre signX86_64.pub signP521 := by
  obtain ⟨_, hc⟩ : ∃ h, (taintS.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8]) signP521 h).isSome = true := by
    taint_decide_sum [Proof.P521.X86_64.ladderGSum, Proof.P521.X86_64.powPSum]
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

theorem sign_verified (hL : Law Spec.P521.curve) :
    Verified X86_64.target signP521 (Spec.Ecdsa.P521.inst.signContract X86_64.abi) :=
  Verified.of_correct (sign_x86 hL) sign_ct implies

end VG.Proof.Ecdsa.X86_64.P521
