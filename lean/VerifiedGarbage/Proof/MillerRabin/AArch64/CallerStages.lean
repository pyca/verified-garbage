module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerBoundaryCT
public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerPre
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Round
import VerifiedGarbage.Proof.MillerRabin.AArch64.Correct
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerContext
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerKept
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.AArch64.Prepared

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

theorem call_restore_pre (M : Mont) (name : String) (hnf : (round M.mm).noFrames = true)
    {L : VG.Proof.Bignum.AArch64.Ws} {s : State} (h : Ready L s) :
    WP isa (.call name (round M.mm)) s (RestorePre L) := by
  have hp := ready_pre h
  have hw := ready_covers h
  obtain ⟨⟨h4, h128, hEZ, c, bm, b, hc, he, ho, h3, hx⟩, h19, h1⟩ := h
  refine WP.callV (round_correct M) hp (Covers.right hw) hw ?_ hnf
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
