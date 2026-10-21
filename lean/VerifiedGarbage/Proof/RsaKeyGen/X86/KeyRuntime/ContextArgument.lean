module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
import VerifiedGarbage.Proof.Framework.Offset

/-! # Original cdecl arguments remain the runtime arithmetic's public widths -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (stackAddress stackValue)
open VG.Proof.Bignum.X86 (CallArgument)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context argsRegion)

theorem context_argument {B : Addr} {Z i : Nat} {p : BitVec 32} {args : Nat → BitVec 32} {s : State}
    (C : Context B Z p args s) (index : i < 18) : CallArgument s B Z (i + 4) (args i) := by
  have operand : VG.Impl.RsaKeyGen.X86.CandidateArgs.arg i =
      VG.Impl.Bignum.X86.PublicFn.argument (i + 4) := by
    unfold VG.Impl.RsaKeyGen.X86.CandidateArgs.arg VG.Impl.Bignum.X86.PublicFn.argument
    congr 1
    omega
  have R := C.read i index
  rw [operand] at R
  have read : s.load32 (stackAddress s (i + 4)) = some (args i) := R
  have access : InRegions (s.rd ++ s.wr) (stackAddress s (i + 4)) 4 := by
    unfold State.load32 at read
    split at read
    · assumption
    · contradiction
  have value : stackValue s (i + 4) = args i := by
    unfold State.load32 at read
    rw [ite_eq_left access] at read
    exact Option.some.inj read
  have address : stackAddress s (i + 4) = off (argsRegion p).base (4 * i) := by
    rw [← C.address index, operand]
    rfl
  refine ⟨⟨access, ?_⟩, value⟩
  rw [address]
  exact C.separate.sub_left (Offset.sub_base _ (by change 4 * i + 4 ≤ 72; omega))

end VG.Proof.RsaKeyGen.X86.KeyRuntime
