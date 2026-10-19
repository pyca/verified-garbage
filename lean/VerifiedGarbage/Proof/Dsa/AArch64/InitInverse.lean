module
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Initializing the Montgomery inverse for each odd DSA modulus -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev initInverse : List Instr :=
  ([ldh .x3 (sArr aN), ld .x3 .x3] : List Instr) ++ minv ++
    ([sth .x15 sMinv] : List Instr)

theorem initInverse_ok {s : State} {B : Addr} {Z w : Nat} {oldMinv : BitVec 64}
    (hg : Good s B Z w oldMinv) (hZ : slot w 8 ≤ Z)
    (hodd : (word s.mem B (slot w aN)).toNat % 2 = 1) :
    WP isa (.block initInverse) s fun t => ∃ mi : BitVec 64,
      Good t B Z w mi ∧ ((word s.mem B (slot w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 ∧
      Outside B (8 * sMinv) 8 s.mem t.mem ∧ Keep [.x3, .x4, .x5, .x6, .x15] s t := by
  have hhdr : ∀ i < 32, 8 * i + 8 ≤ Z := fun i hi =>
    Nat.le_trans (hdr_lt_slot w 8 hi) hZ
  have hn : slot w aN + 8 ≤ Z := by
    have h := slot_le (w := w) (show aN < 8 by decide)
    omega
  unfold initInverse
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (Q := fun u =>
      u.gpr .x3 = word s.mem B (slot w aN) ∧ u.mem = s.mem) ?_ rfl rfl rfl)
    fun u ⟨⟨hub, hum⟩, hku⟩ => ?_
  · brun [hdr_enc (show sArr aN < 32 by decide), hg.x0, hg.hdr.harr aN (by decide),
      hg.scr.ld (hhdr (sArr aN) (by decide)), hg.scr.ld hn]
  rw [WP.block_append_iff]
  refine WP.mono (minv_ok u (by rw [hub]; exact hodd)) fun v ⟨hvi, hkv, hvm⟩ => ?_
  have hks := hku.trans hkv
  have hvdi := (hks.gpr .x0 (show Reg.x0 ∉ _ by decide)).trans hg.x0
  refine WP.mono (WP.keep [] (Q := fun t =>
      t.mem = v.mem.writeW (off B (8 * sMinv)) (v.gpr .x15)) ?_ rfl rfl rfl)
    fun t ⟨htm, hkt⟩ => ?_
  · brun [hdr_enc (show sMinv < 32 by decide), hvdi,
      (hg.scr.congr hks.wr).st (hhdr sMinv (by decide))]
  have hf : Outside B (8 * sMinv) 8 s.mem t.mem := by
    rw [htm, hvm, hum]
    exact writeW_outside _ _ _ (by decide)
  have hktotal := hks.trans hkt
  refine ⟨v.gpr .x15, ⟨hg.scr.congr hktotal.wr, (hktotal.gpr .x0 (by decide)).trans hg.x0,
    ⟨?_, ?_, ?_⟩⟩, by rw [hub] at hvi; exact hvi, hf, hktotal.mono (by decide)⟩
  · exact (hf.word (Or.inl (by decide)) (by decide)).trans hg.hdr.hw
  · rw [htm, word_writeW_self]
  · intro j hj
    exact (hf.word (Or.inr (by unfold sArr sMinv; omega)) (by unfold sArr; omega)).trans (hg.hdr.harr j hj)

end VG.Proof.Dsa.AArch64
