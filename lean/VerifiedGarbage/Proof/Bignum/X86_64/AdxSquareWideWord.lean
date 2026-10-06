import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquareWide
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBlock
import VerifiedGarbage.Proof.Framework.Omega

/-! Word-level equations retain both carry flags across stores. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareWide
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem store_ok {s : State} {B : Addr} {Z e j k : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (h14 : s.gpr .r14 = BitVec.ofNat 64 j)
    (hZ : e + 8 * j + 8 * k + 8 ≤ Z) :
    WP isa (.block [.store (ix .r8 .r14 (8 * k)) .r11]) s fun t =>
      t.mem = s.mem.writeW (off B (e + 8 * j + 8 * k)) (s.gpr .r11) ∧
      t.cf = s.cf ∧ t.of = s.of ∧ Keep [] s t := by
  refine WP.mono (WP.keep [] (Q := fun t =>
      t.mem = s.mem.writeW (off B (e + 8 * j + 8 * k)) (s.gpr .r11) ∧
      t.cf = s.cf ∧ t.of = s.of) ?_ rfl) fun t ⟨h, kt⟩ => ⟨h.1, h.2.1, h.2.2, kt⟩
  xrun [ea_ixk s h8 h14 k, hs.st hZ]

theorem word_ok {s : State} {B : Addr} {Z e eb j k : Nat} {hi prev : Reg} {c o : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j)
    (hZ : e + 8 * j + 8 * k + 8 ≤ Z) (hZb : eb + 8 * j + 8 * k + 8 ≤ Z)
    (hc : s.cf = some c) (ho : s.of = some o)
    (d1 : hi ≠ .r11) (d2 : prev ≠ hi) (d3 : prev ≠ .r11) (d4 : hi ≠ .r8) (d5 : hi ≠ .r14) :
    WP isa (.block (AdxSquareWide.word k hi prev)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      (word t.mem B (e + 8 * j + 8 * k)).toNat +
        2 ^ 64 * ((t.gpr hi).toNat + c'.toNat + o'.toNat) =
        (word s.mem B (e + 8 * j + 8 * k)).toNat +
        (s.gpr .rdx).toNat * (word s.mem B (eb + 8 * j + 8 * k)).toNat +
        (s.gpr prev).toNat + c.toNat + o.toNat ∧
      Outside B (e + 8 * j + 8 * k) 8 s.mem t.mem ∧ Keep [hi, .r11] s t := by
  have hn := hs.nowrap
  unfold AdxSquareWide.word
  rw [WP.block_append_iff]
  refine WP.mono (wordA_ok s (readSrc_word hs (ea_ixk s h9 h14 k) hZb)
    (readSrc_word hs (ea_ixk s h8 h14 k) hZ) hc ho d1 d2 d3 d4 (by decide) d5 (by decide))
    fun a ⟨c', o', ca, oa, eq, ka⟩ => ?_
  refine WP.mono (store_ok (hs.congr ka.2.2.2) ((ka.gpr (by simp [Ne.symm d4])).trans h8)
    ((ka.gpr (by simp [Ne.symm d5])).trans h14) hZ) fun t ⟨hm, ct, ot, kt⟩ => ?_
  refine ⟨c', o', ct.trans ca, ot.trans oa, ?_, ?_, (ka.keep.trans kt).mono (by simp)⟩
  · rw [kt.gpr (by simp), hm, word_writeW_self]
    omega_using [eq]
  · rw [hm, ka.2.1]; exact writeW_outside _ _ _ (by omega)
end VG.Proof.Bignum.X86_64.AdxSquareWide
