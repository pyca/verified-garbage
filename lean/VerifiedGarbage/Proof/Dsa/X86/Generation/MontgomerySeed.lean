module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.MontgomerySetup
public import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomeryMath
public import VerifiedGarbage.Proof.Mont.X86.ContextInit
import VerifiedGarbage.Proof.Mont.X86.WordConst
import VerifiedGarbage.Proof.Mont.X86.PowerLoop
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! The short doubling pass starts from a reduced, public power of two. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Impl.Mont
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem montgomery_seed {s : State} {base : Addr} {size n m bits : Nat}
    (C : Context n m base size s) (hn : 0 < n) (hn' : n ≤ 48)
    (bitsLow : 2 ≤ bits) (bitsHigh : bits ≤ 64 * n) (top : 2 ^ (bits - 1) ≤ m)
    (odd : m % 2 = 1) :
    WP isa (montgomerySeed n bits) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n 4) n = 2 ^ n * 2 ^ (64 * n) % m ∧
      wordsVal t.mem base (slot n 3) n = wordsVal s.mem base (slot n 3) n ∧
      Outs base (setupRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have b4 := slot_bound (n := n) (i := 4) (by decide)
  have s04 := slot_le (n := n) (i := 0) (j := 4) (by decide)
  have h4 := slot_header n 4
  have b3 := slot_bound (n := n) (i := 3) (by decide)
  have s34 := slot_le (n := n) (i := 3) (j := 4) (by decide)
  have reduced : 2 ^ (bits - 1) < m := by
    have even : 2 ^ (bits - 1) % 2 = 0 := by
      rw [show bits - 1 = (bits - 2) + 1 by omega, Nat.pow_succ, Nat.mul_mod_left]
    omega
  have fit : slot n 4 + 4 * (2 * n) ≤ size := by
    have := C.size_le
    unfold stride at b4
    omega
  unfold montgomerySeed
  refine WP.seq (WP.mono (setConstW_ok C.scr (by omega) fit
    (Nat.pow_lt_pow_right (by decide) (by omega))) fun u ⟨value, K, O⟩ => ?_)
  have Cu := C.outside_keep K (by decide) (by decide) O
    (.inl (by unfold stride at s04; omega)) (by omega)
  have vu : wordsVal u.mem base (slot n 4) n = 2 ^ (bits - 1) := by
    rw [wordsVal_eq_val32]; exact value
  refine WP.seq (wp_movS rfl fun v U _ => WP.block_nil ?_)
  have Cv : Context n m base size v := by
    exact Cu.outside_keep (d := slot n 4) (len := 8 * n) U.keeps (by decide) (by decide)
      (U.mem ▸ Outside.refl base (slot n 4) (8 * n) u.mem)
      (.inl (by unfold stride at s04; omega)) (by omega)
  have vv : wordsVal v.mem base (slot n 4) n = 2 ^ (bits - 1) := by rw [U.mem, vu]
  refine WP.mono (doubleLoop_ok Cv.scr Cv.modulus
    (context_opLay Cv.size_le (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide))
    (.inr (by change slot n 0 + 8 * n ≤ slot n 4; unfold stride at s04; omega))
    (by change wordsVal v.mem base (slot n 4) n < m; rw [vv]; exact reduced)
    (by omega) (by omega) U.gpr) fun t I => ?_
  obtain ⟨Ct, one, F⟩ := Cv.power_frame I.modulus I.mem I.keeps
  refine ⟨Ct, ?_, ?_, ?_, (K.mono (by decide)).trans ((U.keeps.mono (by decide)).trans I.keeps)⟩
  · have value := I.value
    simp only [contextMod] at value
    rw [value, vv, montgomery_seed_power bitsHigh]
  · rw [one, U.mem, wordsVal_eq_val32, wordsVal_eq_val32]
    exact O.val32 (.inl (by unfold stride at s34; omega))
      (by have := C.scr.nowrap; have := C.size_le; unfold stride at b3; omega)
  · have Fseed : Outs base (setupRanges n) s.mem u.mem := Outs.of_outside O (by simp [setupRanges, show 4 * (2 * n) = 8 * n by omega])
    have Fmove : Outs base (setupRanges n) u.mem v.mem := by
      rw [U.mem]; exact Outs.refl base (setupRanges n) u.mem
    exact Fseed.trans (Fmove.trans F)

end VG.Proof.Dsa.X86.Generation
