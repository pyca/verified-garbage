module

import VerifiedGarbage.Proof.MillerRabin.X86_64.Frame
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Restore
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Normalize
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Core
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeByte
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Restore bookkeeping without changing the reusable round contract -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.Proof.Bignum VG.Impl.MillerRabin.X86_64

private theorem slot_keys : restoreSlots.map (·.1) = bookkeeping.map (·.1) := rfl

theorem restored_core_keeps {B S : Addr} {n w : Nat} {m m' : Mem}
    (hn : 8 * n ≤ 2 ^ 64) (hf : Frm B (coreRanges w) (normalizedMem m B w) m')
    (hs : ∀ p ∈ restoreSlots, m'.readW (S + BitVec.ofNat 64 p.2) 64 = word m B (8 * p.1)) :
    Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.extended B n w m (restoredMem m' B S) := by
  classical
  intro i hi hh ha ht
  by_cases hb : ∃ p ∈ restoreSlots, 8 * p.1 ≤ i ∧ i < 8 * p.1 + 8
  · obtain ⟨p, hp, hlo, hhi⟩ := hb
    have hw : word (restoredMem m' B S) B (8 * p.1) = word m B (8 * p.1) :=
      (restored_values m' B S p hp).trans (hs p hp)
    have hbyte := VG.Proof.RsaKeyGen.X86_64.word_bytes hw (j := i - 8 * p.1) (by omega_arith)
    rw [off, Offset.add_ofNat_add_ofNat, show 8 * p.1 + (i - 8 * p.1) = i by omega_arith] at hbyte
    exact hbyte
  · have hslots : ∀ p ∈ restoreSlots, i < 8 * p.1 ∨ 8 * p.1 + 8 ≤ i := by
      intro p hp
      by_cases hlo : i < 8 * p.1
      · exact Or.inl hlo
      · right
        by_contra hhi
        exact hb ⟨p, hp, by omega_arith, by omega_arith⟩
    have ho : ∀ p ∈ restoreSlots, ofs B (B + BitVec.ofNat 64 i) < 8 * p.1 ∨ 8 * p.1 + 8 ≤ ofs B (B + BitVec.ofNat 64 i) := by
      simpa only [ofs, Mem.sub_ofNat_toNat B (by omega_arith : i < 2 ^ 64)] using hslots
    rw [restored_byte m' B S _ ho, core_keeps hn hf i hi hh ha ht]
    apply normalized_byte
    intro j hj
    rw [← slot_keys] at hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
    exact ho p hp

end VG.Proof.MillerRabin.X86_64
