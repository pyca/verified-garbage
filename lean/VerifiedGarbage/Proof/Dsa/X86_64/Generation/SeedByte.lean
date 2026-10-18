module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedAdd
public import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Omega

/-! # Carry propagation for one wrapped-seed byte -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private theorem byte_add (c : Nat) (b : Byte) :
    BitVec.ofNat 64 c + b.setWidth 64 = BitVec.ofNat 64 (b.toNat + c) := by
  have hb := b.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem seedAddByte_ok {s : State} {rp op : Addr} {i carry : Nat} {b : Byte}
    (hc : carry < 2 ^ 32) (hrp : s.gpr .rsi = rp) (hop : s.gpr .rdi = op)
    (hcarry : s.gpr .rax = BitVec.ofNat 64 carry)
    (hrd : InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : InRegions s.wr (off op i) 1) (hb : s.mem (off rp i) = b) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.seedAddByte i)) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 ((b.toNat + carry) / 256) ∧
      t.mem = s.mem.writeW (off op i) (BitVec.ofNat 8 (b.toNat + carry)) ∧ Keep [.rax, .rcx] s t := by
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 ((b.toNat + carry) / 256) ∧
      t.mem = s.mem.writeW (off op i) (BitVec.ofNat 8 (b.toNat + carry))) ?_ rfl)
    fun _ ⟨⟨hv, hm⟩, hk⟩ => ⟨hv, hm, hk⟩
  simp only [off] at hrd hwr hb
  xrun [Impl.Dsa.X86_64.Generation.seedAddByte, State.ea, hrp, hop, hcarry,
    BitVec.ofInt_natCast, off, hrd, hwr, hb, byte_add carry b]
  constructor
  · apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    omega
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega

end VG.Proof.Dsa.X86_64.Generation
