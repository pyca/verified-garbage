module

public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.Words

/-! # FFDH parameter candidates on x86-64: the first shaped byte -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.ParameterCandidate

private theorem top_machine {j : Nat} (hj : j < 8) (b : Byte) :
    ((b.setWidth 64 &&& BitVec.ofNat 64 (2 ^ j - 1)) ||| BitVec.ofNat 64 (2 ^ j)).setWidth 8 = topByte j b := by
  have hb := b.isLt
  have hp : 2 ^ j ≤ 128 := show 2 ^ j ≤ 2 ^ 7 from Nat.pow_le_pow_right (by decide) (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [topByte_value hj]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 2 ^ j - 1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 2 ^ j < 2 ^ 64 by omega),
    Nat.and_two_pow_sub_one_eq_mod, Nat.or_two_pow_eq_add_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)),
    Nat.mod_eq_of_lt (show b.toNat % 2 ^ j + 2 ^ j < 2 ^ 8 by have := Nat.mod_lt b.toNat (Nat.two_pow_pos j); omega)]

theorem firstByte_ok {s : State} {rp op : Addr} {len j : Nat} {b : Byte}
    (hl : 2 ≤ len) (hk : len < 2 ^ 31) (hj : j < 8)
    (hrp : s.gpr .rsi = rp) (hop : s.gpr .rdi = op) (hn : s.gpr .rcx = BitVec.ofNat 64 len)
    (hm : s.gpr .r8 = BitVec.ofNat 64 (2 ^ j - 1)) (hh : s.gpr .r9 = BitVec.ofNat 64 (2 ^ j))
    (hrd : InRegions (s.rd ++ s.wr) rp 1) (hwr : InRegions s.wr op 1) (hb : s.mem rp = b) :
    WP isa (.block firstByte) s fun t =>
      t.mem = s.mem.writeW op (topByte j b) ∧ t.gpr .r10 = off rp 1 ∧ t.gpr .r11 = off op 1 ∧
      t.gpr .rcx = BitVec.ofNat 64 (len - 1) ∧ Keep [.rax, .r10, .r11, .rcx] s t := by
  have hsub : BitVec.ofNat 64 len - 1 = BitVec.ofNat 64 (len - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    omega
  refine WP.mono (WP.keep [.rax, .r10, .r11, .rcx] (Q := fun t =>
    t.mem = s.mem.writeW op (topByte j b) ∧ t.gpr .r10 = off rp 1 ∧ t.gpr .r11 = off op 1 ∧
      t.gpr .rcx = BitVec.ofNat 64 (len - 1))
    (by unfold firstByte; xrun [State.ea, at0, hrp, hop, hn, hm, hh,
      show rp + BitVec.ofInt 64 0 = rp from by simp,
      show op + BitVec.ofInt 64 0 = op from by simp, hrd, hwr, hb, top_machine hj b, hsub, off]
        exact ⟨rfl, rfl⟩) rfl)
    fun _ ⟨⟨hmem, hp, ho, hc⟩, k⟩ => ⟨hmem, hp, ho, hc, k⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
