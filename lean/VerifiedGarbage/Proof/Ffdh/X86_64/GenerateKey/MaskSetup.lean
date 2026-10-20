module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # FFDH on x86-64: recover the scalar output's full-width pointer -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem maskSetup_ok {s : State} {B xp : Addr} {Z k ld : Nat} {c : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 256 ≤ Z) (hk : k < 2 ^ 31) (hld : ld < k)
    (hX : word s.mem B (8 * sX) = off xp ld)
    (hL : word s.mem B (8 * sXl) = BitVec.ofNat 64 (k - ld))
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hax : s.gpr .rax = BitVec.ofNat 64 c.toNat) :
    WP isa (.block maskSetup) s fun t =>
      (t.gpr .r11 = xp ∧ t.gpr .r15 = mask c ∧ t.gpr .rcx = BitVec.ofNat 64 k ∧
      word t.mem B (8 * sF) = BitVec.ofNat 64 c.toNat ∧ Frm B [(8 * sF, 8)] s.mem t.mem) ∧
      Keep [.r15, .r11, .rdx, .rcx] s t := by
  let m := s.mem.writeW (off B (8 * sF)) (BitVec.ofNat 64 c.toNat)
  have hf := writeW_outside (d := 8 * sF) s.mem B (BitVec.ofNat 64 c.toNat) (by decide)
  have hh : ∀ i < sF, word m B (8 * i) = word s.mem B (8 * i) :=
    fun i hi => hf.word (Or.inl (by omega)) (by unfold sF sFn at hi; omega)
  have hX' : word m B (8 * sX) = off xp ld := (hh _ (by decide)).trans hX
  have hL' : word m B (8 * sXl) = BitVec.ofNat 64 (k - ld) := (hh _ (by decide)).trans hL
  have hK' : word m B (8 * sK) = BitVec.ofNat 64 k := (hh _ (by decide)).trans hK
  have hsub : BitVec.ofNat 64 k - BitVec.ofNat 64 (k - ld) = BitVec.ofNat 64 ld := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hmask : 0#64 - BitVec.ofNat 64 c.toNat = mask c := by cases c <;> rfl
  refine WP.mono (WP.keep [.r15, .r11, .rdx, .rcx] (Q := fun t =>
      t.gpr .r11 = xp ∧ t.gpr .r15 = mask c ∧ t.gpr .rcx = BitVec.ofNat 64 k ∧ t.mem = m) (by
    unfold maskSetup
    xrun [State.ea, hdr, hdi, hdrOff, hax, hX', hL', hK', hsub, hmask,
      show (BitVec.setWidth 64 (0 : BitVec 32)) = 0#64 from rfl,
      hs.st (d := 8 * sF) (by change 248 ≤ Z; omega),
      hs.ld (d := 8 * sX) (by change 168 ≤ Z; omega),
      hs.ld (d := 8 * sXl) (by change 176 ≤ Z; omega),
      hs.ld (d := 8 * sK) (by change 152 ≤ Z; omega), m, off, BitVec.add_sub_cancel]) rfl)
    fun t ⟨⟨hp, hm, hcx, hmem⟩, kt⟩ => ?_
  exact ⟨⟨hp, hm, hcx, by rw [hmem]; exact word_writeW_self _ _ _ _,
    by rw [hmem]; exact Frm.of_outside hf (by simp)⟩, kt⟩

end VG.Proof.Ffdh.X86_64.GenerateKey
