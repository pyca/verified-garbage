module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Encode
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.X86.PrivCompareBuffer
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Signature encodings compare byte for byte without an early exit -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.RsaPkcs1Sig.X86

theorem compare_ok (s : State) {a b : BitVec 32} {n : Nat}
    (positive : 0 < n) (bound : n < 2 ^ 32) (aFit : a.toNat + n ≤ 2 ^ 32) (bFit : b.toNat + n ≤ 2 ^ 32)
    (aRead : InRegions (s.rd ++ s.wr) (byteAddr a) n) (bRead : InRegions (s.rd ++ s.wr) (byteAddr b) n)
    (first : s.gpr .esi = a) (second : s.gpr .edi = b) (count : s.gpr .ecx = BitVec.ofNat 32 n) :
    WP isa VG.Impl.RsaPkcs1Sig.X86.compare s fun t =>
      (t.gpr .ebp = 0 ↔ Spec.Rsa.bytesAt s.mem (byteAddr a) n = Spec.Rsa.bytesAt s.mem (byteAddr b) n) ∧
      t.mem = s.mem ∧ Keeps [.esi, .edi, .ebp, .eax, .edx, .ecx] s t := by
  unfold VG.Impl.RsaPkcs1Sig.X86.compare
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  refine WP.mono (VG.Proof.Rsa.X86.PrivChecked.compareBuffer_ok u positive bound aFit bFit
    (by rw [U.rd, U.wr]; exact aRead) (by rw [U.rd, U.wr]; exact bRead)
    ((U.other .esi (by decide)).trans first) ((U.other .edi (by decide)).trans second)
    ((U.other .ecx (by decide)).trans count) U.gpr) fun t ⟨eq, mem, rest⟩ => ?_
  exact ⟨U.mem ▸ eq, mem.trans U.mem, (U.keeps.mono (by decide)).trans rest⟩

end VG.Proof.RsaPkcs1Sig.X86
