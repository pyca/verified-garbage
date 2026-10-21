module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentImport
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Bignum.X86.LoadBE
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Full-width exponent import agrees with the reviewed arbitrary-byte input -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentImport
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86

theorem code_ok {s : State} {base : Addr} {size len : Nat} {source : BitVec 32}
    (S : Scr s base size) (header : 256 ≤ size)
    (pointer : s.mem.readW (off base 12) 32 = source) (length : w32 s.mem base 16 = len)
    (positive : 0 < len) (bound : len ≤ 8) (sourceFit : source.toNat + len ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (source.setWidth 64) len)
    (separate : (⟨source.setWidth 64, len⟩ : Region).Disjoint ⟨off base 128, 8⟩) :
    WP isa VG.Impl.RsaKeyGen.X86.ExponentImport.code s fun t =>
      word t.mem base 128 = BitVec.ofNat 64 (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (source.setWidth 64) len)) ∧
      Outside base 128 8 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold VG.Impl.RsaKeyGen.X86.ExponentImport.code
  refine WP.seq (wp_movS (readSrc_sc S (by omega)) fun a A _ =>
    wp_movS (readSrc_sc (S.of_keeps A.keeps (by decide)) (d := 16) (by omega)) fun b B _ => WP.block_nil ?_)
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s b :=
    (A.keeps.mono (by decide)).widen B.keeps
  have mem : b.mem = s.mem := B.mem.trans A.mem
  have ptr : b.gpr .esi = source := by rw [B.other .esi (by decide), A.gpr, pointer]
  have count : b.gpr .ecx = BitVec.ofNat 32 len := by
    rw [B.gpr, A.mem]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← length, Nat.mod_eq_of_lt (s.mem.readW (off base 16) 32).isLt]
  refine WP.mono (VG.Proof.Bignum.X86.loadBE_ok (S.of_keeps K (by decide)) (by decide) (by omega)
    positive bound (by rw [ptr]; exact sourceFit) count
    (by rw [ptr, K.2.1, K.2.2]; exact readable) (by rw [ptr]; exact separate))
    fun t ⟨value, O, Kt⟩ => ?_
  rw [mem, ptr] at value
  rw [mem] at O
  simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at value
  change (word t.mem base 128).toNat = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (source.setWidth 64) len) at value
  exact ⟨by apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, ← value, Nat.mod_eq_of_lt (word t.mem base 128).isLt], O, K.trans Kt⟩

end VG.Proof.RsaKeyGen.X86.ExponentImport
