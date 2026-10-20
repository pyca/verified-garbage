module

import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerEntry
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Contract
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSq
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.Prepared
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # The caller provides the shared round's workspace and stack -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

def callWords (w : Nat) : Nat := 32 + 28 * (w + 2)

def narrowed (s : State) (B : Addr) (w : Nat) : State :=
  s.callEntry.withRegions [] [⟨B, 8 * callWords w⟩]

structure Room (s : State) (B : Addr) (Z : Nat) : Prop where
  size : 128 ≤ (s.gpr .rsp).toNat
  disjoint : Region.Disjoint ⟨B, Z⟩ (below (s.gpr .rsp) 128)

theorem call_size {w Z : Nat} (hZ : slot w 28 ≤ Z) : 8 * callWords w ≤ Z := by
  simp only [callWords, slot, hdrBytes] at hZ ⊢
  omega_arith

theorem narrow_pre {s : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (he : ECtx s.mem B w c) (hd : MrDims B Z w)
    (hZ : slot w 28 ≤ Z) (hr : Room s B Z)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 (callWords w))
    (ho : c % 2 = 1) (h3 : 3 ≤ c) (hx : wv s.mem B (slot w aXm) w < c) :
    roundPre (narrowed s B w) := by
  have hn := hc.good.scr.nowrap
  have hsize := call_size hZ
  have hw := hd.w128
  have hN : callWords w < 2 ^ 64 := by unfold callWords; omega_arith
  obtain ⟨hce, hee⟩ := entry_context hc he hd hr.disjoint
  have heX : wv s.callEntry.mem B (slot w aXm) w < c := by
    rw [entry_wv s hn (by
      have hz := hd.x
      simp only [slot, hdrBytes, aRm1, aXm] at hz ⊢
      omega_arith) hr.disjoint]
    exact hx
  have hSub : Region.Sub ⟨B, 8 * callWords w⟩ ⟨B, Z⟩ := by
    intro x hx
    simp only [Region.Contains] at hx ⊢
    omega_arith
  have hD := (hr.disjoint.sub_left hSub).symm
  dsimp only [roundPre, narrowed, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_mem]
  rw [State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), hc.good.rdi,
    State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), hsi,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN]
  simp only [Nat.mul_comm (callWords w) 8]
  refine ⟨trivial, trivial, by omega_arith, ?_, ?_, ?_,
    layout_of_ctx hce hd.w4 hd.w128, prepared_of_ctx hce hee hd.w128 ho h3 heX⟩
  · rw [State.callEntry_rsp]
    change 120 ≤ (s.gpr .rsp - BitVec.ofNat 64 8).toNat
    rw [toNat_sub_ofNat (k := 8) (by have := hr.size; omega_arith)]
    have := hr.size
    omega_arith
  · rw [State.callEntry_rsp]
    change Region.Disjoint (below (s.gpr .rsp) 8) ⟨B, 8 * callWords w⟩
    exact hD.sub_left (below_sub (sp := s.gpr .rsp) (a := 8) (b := 128) (by decide) (by decide))
  · rw [State.callEntry_rsp]
    change Region.Disjoint (below (s.gpr .rsp - 8#64) 120) ⟨B, 8 * callWords w⟩
    exact hD.sub_left (below_callee (s.gpr .rsp) 120)

theorem narrow_covers {s : State} {B : Addr} {Z w : Nat} (h : Scr s B Z) (hZ : slot w 28 ≤ Z) :
    Covers ([] ++ [⟨B, 8 * callWords w⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨B, 8 * callWords w⟩] s.wr := by
  have hreg : InRegions s.wr B (8 * callWords w) := by
    simpa only [InRegions, off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using
      h.region (d := 0) (n := 8 * callWords w) (by have := call_size hZ; omega_arith)
        (by unfold callWords; omega_arith)
  refine ⟨Covers.one ?_, Covers.one hreg⟩
  obtain ⟨r, hm, hc⟩ := hreg
  exact ⟨r, List.mem_append_right _ hm, hc⟩

end VG.Proof.MillerRabin.X86_64.Caller
