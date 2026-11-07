module

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

theorem exponentFlag_ok {s : State} (b : Bool)
    (value : s.gpr .eax = BitVec.ofNat 32 b.toNat) :
    WP isa (.block [.alu .cmp .eax (.imm 0)]) s fun t =>
      t.zf = some (!b) ∧ t.mem = s.mem ∧ Keeps [] s t := by
  refine wp_cmpS rfl fun t F Z => WP.block_nil ?_
  refine ⟨?_, F.mem, F.keeps []⟩
  rw [Z, value]
  cases b <;> rfl

end VG.Proof.Bignum.X86
