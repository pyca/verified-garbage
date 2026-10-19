module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorPower
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Data.Int.ModEq

/-! # Initialize the generator exponentiation's saved parent operands -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout

theorem generatorFields_ok {s : State} {B : Addr} {Z w len : Nat} {mi : BitVec 64}
    (h : Good s B Z w mi) (hZ : 336 ≤ Z) (hlen : len < 2 ^ 32) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.generatorFields len)) s fun t =>
      Good t B Z w mi ∧
      word t.mem B 256 = off B VG.Impl.Dsa.Generation.Layout.p ∧
      word t.mem B 288 = off B VG.Impl.Dsa.Generation.Layout.exponent ∧
      word t.mem B 328 = BitVec.ofNat 64 len ∧
      word t.mem B 272 = word s.mem B 272 ∧
      Outside B 256 80 s.mem t.mem ∧ Keep [.rax] s t := by
  have hv : (BitVec.ofNat 32 len).setWidth 64 = BitVec.ofNat 64 len := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  let m1 := s.mem.writeW (off B 256) (off B VG.Impl.Dsa.Generation.Layout.p)
  let m2 := m1.writeW (off B 288) (off B VG.Impl.Dsa.Generation.Layout.exponent)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = m2.writeW (off B 328) (BitVec.ofNat 64 len)) (by
    xrun [Impl.Dsa.X86_64.Generation.generatorFields, Core.field, Field.offset, State.ea, BitVec.ofInt_natCast, h.rdi,
      h.scr.st (d := 256) (by omega), h.scr.st (d := 288) (by omega), h.scr.st (d := 328) (by omega),
      sx_ofNat (by decide : VG.Impl.Dsa.Generation.Layout.p < 2 ^ 31),
      sx_ofNat (by decide : VG.Impl.Dsa.Generation.Layout.exponent < 2 ^ 31), hv]
    rfl) rfl) fun t ⟨hm, hk⟩ => ?_
  have f1 : Outside B 256 8 s.mem m1 := writeW_outside _ _ _ (by decide)
  have f2 : Outside B 288 8 m1 m2 := writeW_outside _ _ _ (by decide)
  have f3 : Outside B 328 8 m2 t.mem := by rw [hm]; exact writeW_outside _ _ _ (by decide)
  have ff : Outside B 256 80 s.mem t.mem :=
    ((f1.mono (by decide) (by decide)).trans (f2.mono (by decide) (by decide))).trans
      (f3.mono (by decide) (by decide))
  refine ⟨⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.rdi, ?_⟩, ?_, ?_, ?_, ?_, ff, hk⟩
  · refine ⟨?_, ?_, fun j hj => ?_⟩
    · change word t.mem B 48 = _
      rw [ff.word (d := 48) (Or.inl (by decide)) (by decide)]
      exact h.hdr.hw
    · change word t.mem B 56 = _
      rw [ff.word (d := 56) (Or.inl (by decide)) (by decide)]
      exact h.hdr.hminv
    · rw [ff.word (Or.inl (by unfold VG.Impl.Bignum.X86_64.sArr; omega))
        (by unfold VG.Impl.Bignum.X86_64.sArr; omega)]
      exact h.hdr.harr j hj
  · rw [f3.word (d := 256) (Or.inl (by decide)) (by decide),
      f2.word (d := 256) (Or.inl (by decide)) (by decide)]
    exact word_writeW_self _ _ _ _
  · rw [f3.word (d := 288) (Or.inl (by decide)) (by decide)]
    exact word_writeW_self _ _ _ _
  · rw [hm]; exact word_writeW_self _ _ _ _
  · rw [f3.word (d := 272) (Or.inl (by decide)) (by decide),
      f2.word (d := 272) (Or.inl (by decide)) (by decide),
      f1.word (d := 272) (Or.inr (by decide)) (by decide)]

end VG.Proof.Dsa.X86_64.Generation
