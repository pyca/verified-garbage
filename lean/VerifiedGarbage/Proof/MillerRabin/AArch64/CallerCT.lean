module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerStages
import VerifiedGarbage.Proof.MillerRabin.AArch64.CT
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.MillerRabin.AArch64.Prepared
import VerifiedGarbage.Proof.MillerRabin.AArch64.Correct

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
      (fun _ _ h => call_restore_pre M name hnf h)) restore_ct

end VG.Proof.MillerRabin.AArch64.Caller
