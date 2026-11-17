module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerResult
import VerifiedGarbage.Proof.MillerRabin.AArch64.CT
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.MillerRabin.AArch64.Prepared
import VerifiedGarbage.Proof.MillerRabin.AArch64.Correct
import VerifiedGarbage.Proof.MillerRabin.AArch64.Frame
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrRound
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerBoundaryCT
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSq
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Round
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerContext
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerCall

/-! ### `MillerRabin.AArch64.CallerStages`, which only this module used -/

section

/-! ### `MillerRabin.AArch64.CallerPre`, which only this module used -/

section

/-! # Narrow a larger caller to the prepared round's required workspace -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64.Caller

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaKeyGen.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate

def callWords (w : Nat) : Nat := 32 + 28 * (w + 2)

def narrowed (s : State) (B : Addr) (w : Nat) : State :=
  s.callEntry.withRegions [] [⟨B, 8 * callWords w⟩]

theorem call_size {w Z : Nat} (h : slot w aE + 8 * (w + 2) ≤ Z) : 8 * callWords w ≤ Z := by
  simp only [slot, hdrBytes, aE, callWords] at h ⊢
  omega_arith

theorem narrow_pre {s : State} {B : Addr} {Z w c bm : Nat}
    (hc : MrCtx s B Z w c bm) (he : ECtx s.mem B w c)
    (h4 : 4 ≤ w) (h128 : w ≤ 128) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (ho : c % 2 = 1) (h3 : 3 ≤ c) (hx : wv s.mem B (slot w aXm) w < c)
    (h1 : s.gpr .x1 = BitVec.ofNat 64 (callWords w)) : roundPre (narrowed s B w) := by
  have hB : (narrowed s B w).gpr .x0 = B := (s.callEntry_gpr (by decide)).trans hc.ws.x0
  have hN : (narrowed s B w).gpr .x1 = BitVec.ofNat 64 (callWords w) := (s.callEntry_gpr (by decide)).trans h1
  have hn : callWords w < 2 ^ 64 := by unfold callWords; omega_arith
  unfold roundPre
  rw [hB, hN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · change ([⟨B, 8 * callWords w⟩] : List Region) = [⟨B, callWords w * 8⟩]
    rw [Nat.mul_comm]
  · have := hc.ws.scr.nowrap
    have := call_size hEZ
    omega_arith
  · change Proof.MillerRabin.Round.Layout Proof.MillerRabin.Round.compact s.mem B (callWords w)
    exact layout_of_ctx hc h4 h128
  · change Proof.MillerRabin.Round.Prepared Proof.MillerRabin.Round.compact s.mem B
    exact prepared_of_ctx hc he ho h3 hx

theorem narrow_covers {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) : Covers [⟨B, 8 * callWords w⟩] s.wr := by
  apply Covers.one
  have hsize := call_size hEZ
  have hr := hs.region (d := 0) (n := 8 * callWords w) (by omega_arith) (by unfold callWords; omega_arith)
  simpa only [InRegions, off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using hr

end VG.Proof.MillerRabin.AArch64.Caller

end

end


/-! # Contexts at the three boundaries of a shared-round call -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64.Caller

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.RsaKeyGen.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.MillerRabin.AArch64
open VG.Impl.MillerRabin.AArch64.Caller

def Before (L : VG.Proof.Bignum.AArch64.Ws) (s : State) : Prop :=
  4 ≤ L.w ∧ L.w ≤ 128 ∧ slot L.w aE + 8 * (L.w + 2) ≤ L.Z ∧
    ∃ c bm b : Nat, MrCtx s L.B L.Z L.w c bm ∧ ECtx s.mem L.B L.w c ∧
      c % 2 = 1 ∧ 3 ≤ c ∧ wv s.mem L.B (slot L.w aXm) L.w = b % c * 2 ^ (64 * L.w) % c

def Ready (L : VG.Proof.Bignum.AArch64.Ws) (s : State) : Prop :=
  Before L s ∧ s.gpr .x19 = L.B ∧ s.gpr .x1 = BitVec.ofNat 64 (callWords L.w)

theorem before_good {L : VG.Proof.Bignum.AArch64.Ws} {s : State} (h : Before L s) : GoodW L s := by
  obtain ⟨_, _, _, c, bm, b, hc, _⟩ := h
  exact ⟨_, hc.good⟩

theorem save_ready {L : VG.Proof.Bignum.AArch64.Ws} {s : State} (h : Before L s) :
    WP isa (.block save) s (Ready L) := by
  obtain ⟨h4, h128, hEZ, c, bm, b, hc, he, ho, h3, hx⟩ := h
  refine WP.mono (save_ok hc.good.1 hc.good.2 h128) ?_
  rintro t ⟨hm, h19, h1, hk⟩
  obtain ⟨hct, het⟩ := save_context hc he hEZ hm hk
  refine ⟨⟨h4, h128, hEZ, c, bm, b, hct, het, ho, h3, ?_⟩, h19, h1⟩
  rw [hm, (saved_outside s L.B L.w (by
    have hz : slot L.w 16 ≤ L.Z := hc.ws.hZ
    have hn := hc.ws.scr.nowrap
    simp only [pad, slot, hdrBytes, aOne] at hz ⊢
    omega_arith)).wv (Or.inl (by simp only [pad, slot, hdrBytes, aOne, aXm]; omega_arith))
      (by
        have hsX := slot_le (w := L.w) (show aXm < 8 by decide)
        have hsZ := hc.good.2
        have hsN := hc.ws.scr.nowrap
        omega_arith)]
  exact hx

theorem ready_pre {L : VG.Proof.Bignum.AArch64.Ws} {s : State} (h : Ready L s) :
    roundPre (narrowed s L.B L.w) := by
  obtain ⟨⟨h4, h128, hEZ, c, bm, b, hc, he, ho, h3, hx⟩, h19, h1⟩ := h
  apply narrow_pre hc he h4 h128 hEZ ho h3 ?_ h1
  rw [hx]
  exact Nat.mod_lt _ (by omega_arith)

theorem ready_covers {L : VG.Proof.Bignum.AArch64.Ws} {s : State} (h : Ready L s) :
    Covers [⟨L.B, 8 * callWords L.w⟩] s.wr := by
  obtain ⟨⟨_, _, hEZ, c, bm, b, hc, _⟩, _⟩ := h
  exact narrow_covers hc.ws.scr hEZ

theorem call_restore_pre {R : Prog isa} (hR : ∀ s, roundContract.pre s → ∃ tr t, Exec isa R s tr t ∧ abiPreserved s t ∧ roundContract.post s t)
    (name : String) (hnf : R.noFrames = true)
    {L : VG.Proof.Bignum.AArch64.Ws} {s : State} (h : Ready L s) :
    WP isa (.call name R) s (RestorePre L) := by
  have hp := ready_pre h
  have hw := ready_covers h
  obtain ⟨⟨h4, h128, hEZ, c, bm, b, hc, he, ho, h3, hx⟩, h19, h1⟩ := h
  refine WP.callV hR hp (Covers.right hw) hw ?_ hnf
  intro t hrd hwr hsp hf hregs hnever hvcs hpost
  change roundPost (narrowed s L.B L.w) (t.withRegions [] [⟨L.B, 8 * callWords L.w⟩]) at hpost
  unfold roundPost at hpost
  have hB : (narrowed s L.B L.w).gpr .x0 = L.B := (s.callEntry_gpr (by decide)).trans hc.ws.x0
  have hN : (narrowed s L.B L.w).gpr .x1 = BitVec.ofNat 64 (callWords L.w) := (s.callEntry_gpr (by decide)).trans h1
  rw [hB, hN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold callWords; omega_arith)] at hpost
  dsimp only at hpost
  have hWidth : Proof.Rsa.Mont.wOf (narrowed s L.B L.w).mem L.B = L.w := ctx_width (s := s) hc
  rw [hWidth] at hpost
  have hkeep : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact L.B (callWords L.w) L.w s.mem t.mem := hpost.2
  refine ⟨hc.ws.scr.congr hwr, hc.good.2,
    (hregs .x19 (by simp [preserved]) (by decide)).trans h19, ?_, ?_⟩
  · exact (kept_header hkeep (by unfold callWords; omega_arith) (by decide) (by decide)).trans hc.ws.hw
  · exact (kept_header hkeep (by unfold callWords; omega_arith) (by decide) (by decide)).trans (hc.ws.harr aOne (by decide))

end VG.Proof.MillerRabin.AArch64.Caller

end

end

/-! ### `MillerRabin.AArch64.CallerCT`, which only this module used -/

section

/-! # Constant time of calling the shared prepared round -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64.Caller

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.MillerRabin.AArch64 VG.Impl.MillerRabin.AArch64.Caller

theorem ready_base {L : VG.Proof.Bignum.AArch64.Ws} {s : State} (h : Ready L s) :
    s.gpr .x0 = L.B := by
  obtain ⟨⟨_, _, _, c, bm, b, hc, _⟩, _⟩ := h
  exact hc.ws.x0

theorem ready_width {L : VG.Proof.Bignum.AArch64.Ws} {s : State} (h : Ready L s) :
    Proof.Rsa.Mont.wOf s.mem L.B = L.w := by
  obtain ⟨⟨_, _, _, c, bm, b, hc, _⟩, _⟩ := h
  exact ctx_width hc

theorem ready_pub {s t : State} {L : VG.Proof.Bignum.AArch64.Ws}
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
