module

import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerResult
public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerStages
public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerFrame
import VerifiedGarbage.Proof.MillerRabin.AArch64.CT
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.MillerRabin.AArch64.Prepared
import VerifiedGarbage.Proof.MillerRabin.AArch64.Correct
import VerifiedGarbage.Proof.MillerRabin.AArch64.Frame
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrRound
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `MillerRabin.AArch64.CallerCT`, which only this module used -/

section

/-! # Constant time of calling the shared prepared round -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64.Caller

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.MillerRabin.AArch64 VG.Impl.MillerRabin.AArch64.Caller

private theorem ready_base {L : VG.Proof.Bignum.AArch64.Ws} {s : State} (h : Ready L s) :
    s.gpr .x0 = L.B := by
  obtain ⟨⟨_, _, _, c, bm, b, hc, _⟩, _⟩ := h
  exact hc.ws.x0

private theorem ready_width {L : VG.Proof.Bignum.AArch64.Ws} {s : State} (h : Ready L s) :
    Proof.Rsa.Mont.wOf s.mem L.B = L.w := by
  obtain ⟨⟨_, _, _, c, bm, b, hc, _⟩, _⟩ := h
  exact ctx_width hc

private theorem ready_pub {s t : State} {L : VG.Proof.Bignum.AArch64.Ws}
    (hs : Ready L s) (ht : Ready L t) (hsp : s.sp = t.sp) :
    roundPub (narrowed s L.B L.w) (narrowed t L.B L.w) := by
  have h0s : (narrowed s L.B L.w).gpr .x0 = L.B := (s.callEntry_gpr (by decide)).trans (ready_base hs)
  have h0t : (narrowed t L.B L.w).gpr .x0 = L.B := (t.callEntry_gpr (by decide)).trans (ready_base ht)
  have h1s : (narrowed s L.B L.w).gpr .x1 = BitVec.ofNat 64 (callWords L.w) :=
    (s.callEntry_gpr (by decide)).trans hs.2.2
  have h1t : (narrowed t L.B L.w).gpr .x1 = BitVec.ofNat 64 (callWords L.w) :=
    (t.callEntry_gpr (by decide)).trans ht.2.2
  refine ⟨hsp, h0s.trans h0t.symm, h1s.trans h1t.symm, ?_⟩
  rw [h0s, h0t]
  exact (ready_width hs).trans (ready_width ht).symm

private theorem prepared_call_ct (M : Mont) (name : String) :
    RelCT isa (Two Ready) (.call name (round M.mm)) fun _ _ => True := by
  apply RelCT.callEx (round_correct M) (round_ct M)
  rintro s t ⟨L, hs, ht, hsp⟩
  have hcs := ready_covers hs
  have hct := ready_covers ht
  exact ⟨[], [⟨L.B, 8 * callWords L.w⟩], [], [⟨L.B, 8 * callWords L.w⟩],
    ready_pre hs, ready_pre ht, ready_pub hs ht hsp,
    Covers.right hcs, hcs, Covers.right hct, hct⟩

theorem call_ct (M : Mont) (name : String) (hnf : (round M.mm).noFrames = true) :
    RelCT isa (Two Before) (call name (round M.mm)) fun _ _ => True := by
  unfold VG.Impl.MillerRabin.AArch64.Caller.call
  refine RelCT.seq (two_post (Ψ := Ready) ?_ (fun _ _ h => save_ready h)) ?_
  · exact save_ct.mono (fun _ _ h => by
      obtain ⟨L, hs, ht, hsp⟩ := h
      exact ⟨L, before_good hs, before_good ht, hsp⟩) (fun _ _ h => h)
  · exact RelCT.seq (two_post (prepared_call_ct M name)
      (fun _ _ h => call_restore_pre (round_correct M) name hnf h)) restore_ct

end VG.Proof.MillerRabin.AArch64.Caller

end

end


/-! # A prepared round for generic RSA and FFDH policies -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Bignum.Public VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.MlKem.AArch64 (Keep)

structure Kernel where
  run : List (Prog isa)
  nonempty : run ≠ []
  ok : ∀ {s : State} {B : Addr} {Z w c bm b : Nat},
    MrCtx s B Z w c bm → ECtx s.mem B w c → 4 ≤ w → w ≤ 128 →
    slot w aE + 8 * (w + 2) ≤ Z → c % 2 = 1 → 3 ≤ c →
    wv s.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c →
    WP isa (seqs run) s fun t =>
      (∃ bm', MrCtx t B Z w c bm') ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round c b) ∧
      Frm B (Caller.callRanges w) s.mem t.mem ∧ Keep mmRegs s t
  ct : RelCT isa (Two Caller.Before) (seqs run) fun _ _ => True

/-- A call of the shared entry point, keeping its workspace for the policy. -/
def Kernel.called (M : Mont) (name : String) (hnf : (VG.Impl.MillerRabin.AArch64.round M.mm).noFrames = true) : Kernel where
  run := [VG.Impl.MillerRabin.AArch64.Caller.call name (VG.Impl.MillerRabin.AArch64.round M.mm)]
  nonempty := by simp
  ok := by exact Caller.call_result_ok (round_correct M) name hnf
  ct := by exact Caller.call_ct M name hnf

end VG.Proof.MillerRabin.AArch64
