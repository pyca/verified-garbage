module
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSq

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # A shared call's return address preserves the prepared workspace -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

theorem entry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

theorem entry_byte (s : State) {B : Addr} {Z i : Nat}
    (hn : B.toNat + Z ≤ 2 ^ 64) (hi : i < Z)
    (hs : Region.Disjoint ⟨B, Z⟩ (below (s.gpr .rsp) 128)) :
    s.callEntry.mem (off B i) = s.mem (off B i) := by
  apply (entry_frame s).bytes (R := ⟨B, Z⟩) ?_ (by change Z ≤ 2 ^ 64; omega_arith) hi
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact hs.sub_right (below_sub (by decide) (by decide))

theorem entry_word (s : State) {B : Addr} {Z d : Nat}
    (hn : B.toNat + Z ≤ 2 ^ 64) (hd : d + 8 ≤ Z)
    (hs : Region.Disjoint ⟨B, Z⟩ (below (s.gpr .rsp) 128)) :
    word s.callEntry.mem B d = word s.mem B d := by
  have hf := entry_frame s
  apply hf.readW (r := ⟨B, Z⟩)
    (Offset.contains_base B hd (by omega_arith)) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact hs.sub_right (below_sub (by decide) (by decide))

theorem entry_wv (s : State) {B : Addr} {Z d k : Nat}
    (hn : B.toNat + Z ≤ 2 ^ 64) (hd : d + 8 * k ≤ Z)
    (hs : Region.Disjoint ⟨B, Z⟩ (below (s.gpr .rsp) 128)) :
    wv s.callEntry.mem B d k = wv s.mem B d k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [wv, wv, ih (by omega_arith), entry_word s hn (by omega_arith) hs]

theorem entry_context {s : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (he : ECtx s.mem B w c) (hd : MrDims B Z w)
    (hs : Region.Disjoint ⟨B, Z⟩ (below (s.gpr .rsp) 128)) :
    MrCtx s.callEntry B Z w mi c bm ∧ ECtx s.callEntry.mem B w c := by
  have hn := hc.good.scr.nowrap
  have hz := hd.x
  have hHdr : ∀ i < 16, word s.callEntry.mem B (8 * i) = word s.mem B (8 * i) :=
    fun i hi => entry_word s hn (by
      have := hdr_lt_slot w 8 (by omega_arith : i < 32)
      have := hd.z
      omega_arith) hs
  have hArr : ∀ j < 27, wv s.callEntry.mem B (slot w j) w = wv s.mem B (slot w j) w :=
    fun j hj => entry_wv s hn (by
      have hslot := VG.Proof.Rsa.slot_lt (w := w) hj
      simp only [slot, hdrBytes, aRm1] at hz hslot ⊢
      omega_arith) hs
  refine ⟨⟨⟨hc.good.scr.congr rfl, by
      rw [State.callEntry_gpr _ (by decide)]; exact hc.good.rdi,
      ⟨(hHdr sW (by decide)).trans hc.good.hdr.hw,
        (hHdr sMinv (by decide)).trans hc.good.hdr.hminv,
        fun j hj => (hHdr (sArr j) (by unfold sArr; omega_arith)).trans (hc.good.hdr.harr j hj)⟩⟩,
    ?_, (hArr aN (by decide)).trans hc.n, (hArr aB (by decide)).trans hc.b,
    (hArr aR1 (by decide)).trans hc.r1, (hArr aRm1 (by decide)).trans hc.rm1⟩, ?_⟩
  · rw [entry_word s hn (by
      have := hd.w4
      simp only [slot, hdrBytes, aRm1, aN] at hz ⊢
      omega_arith) hs]
    exact hc.inv
  · refine ⟨(hArr aE (by decide)).trans he.e, ?_⟩
    rw [entry_word s hn (by
      simp only [slot, hdrBytes, aRm1, aE] at hz ⊢
      omega_arith) hs]
    exact he.l

end VG.Proof.MillerRabin.X86_64.Caller
