module

import VerifiedGarbage.Proof.Bignum.X86.PublicMask
import VerifiedGarbage.Proof.Bignum.X86.PublicWrite
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Bignum.MemoryFrame

/-! # Masking and export preserve saved registers while releasing accepted results -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext
open VG.Proof.Mont VG.Proof.Mont.X86

theorem exportResult_ok {s : State} {base : Addr} {bytes n len y : Nat} {out : BitVec 32}
    (hs : Scr s base bytes) (hn : 0 < n) (hz : size n ≤ bytes) (hl : 0 < len) (hlen : len ≤ 8 * n)
    (V : wordsVal s.mem base (slot n 7) n = y) (valueFit : y < 2 ^ (8 * len))
    (accept : Bool) (Mask : s.mem.readW (off base 144) 32 = if accept then BitVec.allOnes 32 else 0)
    (P : CallArgument s base bytes 0 out) (L : CallArgument s base bytes 1 (BitVec.ofNat 32 len))
    (fit : out.toNat + len ≤ 2 ^ 32) (write : InRegions s.wr (byteAddr out) len)
    (sep : Region.Disjoint ⟨base, bytes⟩ ⟨byteAddr out, len⟩) :
    WP isa (PublicFn.exportResult n) s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr out) len = Spec.Rsa.i2osp (if accept then y else 0) len ∧
      t.gpr .eax = BitVec.ofNat 32 accept.toNat ∧
      Frame [⟨off base 16, bytes - 16⟩, ⟨byteAddr out, len⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have sz := size_eq n
  have nw := hs.nowrap
  unfold PublicFn.exportResult
  refine WP.seq (WP.mono (maskResult_ok hs hn hz accept V Mask) fun u ⟨Y, A, O, K⟩ => ?_)
  have O' : Outside base 0 bytes s.mem u.mem := O.mono (by omega) (by omega)
  refine WP.mono (writeResult_ok (hs.of_keeps K (by decide)) hz hl hlen Y
    (by cases accept <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega)
    accept A ((P.keep K (by decide) O').readSrc) ((L.keep K (by decide) O').readSrc)
    fit (by rw [K.2.2]; exact write) sep) fun t ⟨R, B, F, T⟩ => ?_
  refine ⟨R, B, ?_, (K.mono (by decide)).trans (T.mono (by decide))⟩
  exact ((outside_frame O (by omega)).mono (by simp)).trans (F.mono (by simp))

end VG.Proof.Bignum.X86.PublicContext
