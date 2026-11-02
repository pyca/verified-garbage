module

import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerCall
public import VerifiedGarbage.Proof.MillerRabin.Keeps
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Round
public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerSave
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSq
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MillerRabin.Contract

/-! # The shared caller changes only the round and two padding words -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64.Caller

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaKeyGen.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.MillerRabin.AArch64
open VG.Impl.MillerRabin.AArch64.Caller
open VG.Proof.MlKem.AArch64 (Keep)

def callRanges (w : Nat) : List (Nat × Nat) := [(pad w, 16)] ++ mutRanges Proof.MillerRabin.Round.compact w

private theorem preserved_of_not_mm (r : Reg) (h : r ∉ mmRegs) (h0 : r ≠ .x0) : r ∈ preserved := by
  cases r <;> simp_all [mmRegs, preserved]

theorem call_frame_ok (M : Mont) (name : String) (hnf : (round M.mm).noFrames = true)
    {s : State} {B : Addr} {Z w c bm b : Nat}
    (hc : MrCtx s B Z w c bm) (he : ECtx s.mem B w c)
    (h4 : 4 ≤ w) (h128 : w ≤ 128) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (ho : c % 2 = 1) (h3 : 3 ≤ c)
    (hx : wv s.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c) :
    WP isa (call name (round M.mm)) s fun t =>
      word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round c b) ∧
      Frm B (callRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  obtain ⟨tr, t, hExec, hB, ha, hf, m, hk, hm⟩ := call_ok M name hnf hc he h4 h128 hEZ ho h3 hx
  have hn : 8 * (32 + 28 * (w + 2)) ≤ 2 ^ 64 := by omega_arith
  have hpad : pad w + 16 ≤ 2 ^ 64 := by
    simp only [pad, slot, hdrBytes, aOne]
    omega_arith
  have hsaved : Frm B [(pad w, 16)] s.mem (savedMem s B w) := by
    intro x h
    exact saved_outside s B w hpad x (h (pad w, 16) (by simp))
  have hsFrame : Frame [⟨B, 8 * (32 + 28 * (w + 2))⟩] s.mem (savedMem s B w) := by
    unfold savedMem
    refine Frame.writeW (Frame.writeW (Frame.refl _ _) (r := ⟨B, 8 * (32 + 28 * (w + 2))⟩)
      (by simp) _ ?_) (r := ⟨B, 8 * (32 + 28 * (w + 2))⟩) (by simp) _ ?_
    all_goals apply Offset.contains_base
    all_goals simp only [pad, slot, hdrBytes, aOne] <;> omega_arith
  have hsReverse : Frame [⟨B, 8 * (32 + 28 * (w + 2))⟩] (savedMem s B w) s.mem :=
    fun x h => (hsFrame x h).symm
  have hkt : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact B (32 + 28 * (w + 2)) w
      (savedMem s B w) t.mem := by
    rw [hm]
    exact keeps_write_flag hk hn (by decide) _
  have hfRound := keeps_to_frm hkt (hsReverse.trans hf)
  refine ⟨tr, t, hExec, ?_, ?_, ?_⟩
  · rw [hm, word_writeW_self]
  · exact (hsaved.mono (fun r hr => List.mem_append_left _ hr)).trans
      (hfRound.mono (fun r hr => List.mem_append_right _ hr))
  · have hrw := VG.AArch64.Exec.rdwr hExec
    refine ⟨?_, hrw.1, hrw.2.1, ha.2.1, ha.2.2⟩
    intro r hr
    by_cases h : r = .x0
    · subst r
      exact hB.trans hc.ws.x0.symm
    · exact ha.1 r (preserved_of_not_mm r hr h)

end VG.Proof.MillerRabin.AArch64.Caller
