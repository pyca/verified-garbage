module

import VerifiedGarbage.Proof.MillerRabin.AArch64.Prepared
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSq
import VerifiedGarbage.Proof.Framework.Omega

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
