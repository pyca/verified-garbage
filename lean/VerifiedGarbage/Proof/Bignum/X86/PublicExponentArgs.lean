module

public import VerifiedGarbage.Proof.Bignum.X86.PublicInputs
public import VerifiedGarbage.Proof.Bignum.ExponentCheckMath
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86.ExponentCheck
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Spec.RsaKeyGen

/-! # Scan the public exponent supplied through the cdecl argument slots -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem publicExponent_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PublicInputs base bytes len args s) :
    WP isa (.seq (.block PublicFn.exponentArgs) exponentCheck) s fun t =>
      let e := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)
      t.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.exponentValid e).toNat ∧
      t.gpr .ebx = BitVec.ofNat 32 (e % 2 ^ 32) ∧ t.gpr .edx = BitVec.ofNat 32 (exponentHigh e) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.seq (WP.mono (argumentPair_ok (by decide) (by decide)
    ((h.stack 4 (by decide)).readSrc) ((h.stack 5 (by decide)).readSrc)) fun u ⟨P, C, M, K⟩ => ?_)
  refine WP.mono (exponentCheck_words_ok u (eb := Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)
    (by rw [bytesAt_length]; exact h.ePositive)
    (by rw [bytesAt_length]; exact (args 5).isLt)
    (by rw [bytesAt_length]; exact h.eFit)
    (by rw [bytesAt_length, K.2.1, K.2.2]; exact h.eRead)
    (by intro i hi; rw [M]; simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range])
    P (by rw [bytesAt_length, BitVec.ofNat_toNat]; exact C))
    fun t ⟨E, Lo, Hi, Mt, T⟩ => ?_
  exact ⟨E, Lo, Hi, Mt.trans M, (K.mono (by decide)).trans (T.mono (by decide))⟩

theorem exponentFlag_ok {s : State} (b : Bool)
    (value : s.gpr .eax = BitVec.ofNat 32 b.toNat) :
    WP isa (.block [.alu .cmp .eax (.imm 0)]) s fun t =>
      t.zf = some (!b) ∧ t.mem = s.mem ∧ Keeps [] s t := by
  refine wp_cmpS rfl fun t F Z => WP.block_nil ?_
  refine ⟨?_, F.mem, F.keeps []⟩
  rw [Z, value]
  cases b <;> rfl

end VG.Proof.Bignum.X86
