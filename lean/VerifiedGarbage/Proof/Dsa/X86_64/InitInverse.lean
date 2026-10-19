module
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Framework.Omega

/-! # Initializing the Montgomery inverse for each odd DSA modulus -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev initInverse : List Instr :=
  ([.mov .rbx (.mem (hdr (sArr aN))), .mov .rbx (.mem (at0 .rbx))] : List Instr) ++ minv ++
    ([.store (hdr sMinv) .r15] : List Instr)

theorem initInverse_ok {s : State} {B : Addr} {Z w : Nat} {oldMinv : BitVec 64}
    (hg : Good s B Z w oldMinv) (hZ : slot w 8 ≤ Z)
    (hodd : (word s.mem B (slot w aN)).toNat % 2 = 1) :
    WP isa (.block initInverse) s fun t => ∃ mi : BitVec 64,
      Good t B Z w mi ∧ ((word s.mem B (slot w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 ∧
      Outside B (8 * sMinv) 8 s.mem t.mem ∧ Keep [.rax, .rbx, .rcx, .rdx, .rsi, .r15] s t := by
  have hhdr : ∀ i < 32, 8 * i + 8 ≤ Z := fun i hi =>
    Nat.le_trans (hdr_lt_slot w 8 hi) hZ
  have hn : slot w aN + 8 ≤ Z := by
    have h := slot_le (w := w) (show aN < 8 by decide)
    omega
  unfold initInverse
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.rbx] (Q := fun u =>
      u.gpr .rbx = word s.mem B (slot w aN) ∧ u.mem = s.mem) ?_ rfl)
    fun u ⟨⟨hub, hum⟩, hku⟩ => ?_
  · xrun [State.ea, hdr, at0, hdrOff, hg.rdi, hg.hdr.harr aN (by decide),
      hg.scr.ld (hhdr (sArr aN) (by decide)), hg.scr.ld hn,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  rw [WP.block_append_iff]
  refine WP.mono (minv_ok u (by rw [hub]; exact hodd)) fun v ⟨hvi, hkv, hvm⟩ => ?_
  have hks := hku.trans hkv
  have hvdi := (hks.gpr (show Reg.rdi ∉ _ by decide)).trans hg.rdi
  refine WP.mono (WP.keep [] (Q := fun t =>
      t.mem = v.mem.writeW (off B (8 * sMinv)) (v.gpr .r15)) ?_ rfl)
    fun t ⟨htm, hkt⟩ => ?_
  · xrun [State.ea, hdr, hdrOff, hvdi,
      (hg.scr.congr hks.2.2).st (hhdr sMinv (by decide))]
  have hf : Outside B (8 * sMinv) 8 s.mem t.mem := by
    rw [htm, hvm, hum]
    exact writeW_outside _ _ _ (by decide)
  have hktotal := hks.trans hkt
  refine ⟨v.gpr .r15, ⟨hg.scr.congr hktotal.2.2, (hktotal.gpr (by decide)).trans hg.rdi,
    ⟨?_, ?_, ?_⟩⟩, by rw [hub] at hvi; exact hvi, hf, hktotal.mono (by decide)⟩
  · exact (hf.word (Or.inl (by decide)) (by decide)).trans hg.hdr.hw
  · rw [htm, word_writeW_self]
  · intro j hj
    exact (hf.word (Or.inr (by unfold sArr sMinv; omega)) (by unfold sArr; omega)).trans (hg.hdr.harr j hj)

end VG.Proof.Dsa.X86_64
