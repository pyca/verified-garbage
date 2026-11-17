module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Sized
public import VerifiedGarbage.Proof.Bignum.X86.PublicExponentArgs
public import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
public import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
public import VerifiedGarbage.Proof.Bignum.X86.PublicReturn
public import VerifiedGarbage.Proof.Bignum.PublicWritten
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.X86.Isa
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.X86.PublicFailure
public import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Impl.Bignum.X86.PublicContext
import VerifiedGarbage.Proof.Dsa.X86.StackArgument
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Bignum.X86.PublicEntry
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Bignum.ExponentCheckMath
public import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
public import VerifiedGarbage.Proof.Bignum.ExponentWords
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Bignum.X86.PublicControls`, which this module and modules that import it used -/

section

/-! # Save a validated exponent and derive the public limb count -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem saveExponent_ok {s : State} {base : Addr} {bytes e : Nat}
    (hs : Scr s base bytes) (hb : 136 ≤ bytes) (he : e < 2 ^ 33)
    (lo : s.gpr .ebx = BitVec.ofNat 32 (e % 2 ^ 32))
    (hi : s.gpr .edx = BitVec.ofNat 32 (exponentHigh e)) :
    WP isa (.block PublicFn.saveExponent) s fun t =>
      val32 t.mem base 128 2 = e ∧ Outside base 128 8 s.mem t.mem ∧ Keeps [] s t := by
  unfold PublicFn.saveExponent
  refine wp_storeS (hs.ea (by omega_using [hb])) (hs.write (by omega_using [hb])) fun u A => ?_
  have hu := hs.of_keeps (A.keeps []) (by decide)
  refine wp_storeS (hu.ea (by omega_using [hb])) (hu.write (by omega_using [hb])) fun t B => WP.block_nil ?_
  have Oa : Outside base 128 4 s.mem u.mem := by rw [A.mem]; exact writeW32_outside _ _ _ (by decide)
  have Ob : Outside base 132 4 u.mem t.mem := by rw [B.mem]; exact writeW32_outside _ _ _ (by decide)
  refine ⟨?_, (Oa.mono (by omega_using []) (by omega_using [])).trans (Ob.mono (by omega_using []) (by omega_using [])),
    (A.keeps []).trans (B.keeps [])⟩
  have low : w32 t.mem base 128 = e % 2 ^ 32 := by
    rw [Outside.w32 Ob (.inl (by decide)) (by decide), A.mem, w32_write_self, lo, BitVec.toNat_ofNat,
      Nat.mod_mod]
  have high : w32 t.mem base 132 = e / 2 ^ 32 := by
    rw [B.mem, w32_write_self, A.gpr, hi, BitVec.toNat_ofNat]
    unfold exponentHigh
    omega_using [he]
  simp only [val32, Nat.mul_zero, Nat.add_zero]
  change w32 t.mem base 128 + 2 ^ 32 * w32 t.mem base 132 = e
  rw [low, high]
  omega_using []

end VG.Proof.Bignum.X86

end

end

/-! # The room for the calls of public RSA at a run-time width

The room for the multiplications' calls below `esp` (`Room`), which the
contract's 96 bytes of stack give.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.PublicContext
open VG.Proof.Dsa.X86 (argumentPointer)

/-- What the calls need beyond `PublicInputs`. -/
structure Room (base : Addr) (bytes : Nat) (args : Nat → BitVec 32) (s : State) : Prop where
  hbase : (args 8).toNat = base.toNat
  hbytes : bytes = (args 9).toNat * 8
  room : CallRoom (s.gpr .esp) base bytes
  top : (s.gpr .esp).toNat + 44 ≤ 2 ^ 32

theorem Room.keep {base : Addr} {bytes : Nat} {args : Nat → BitVec 32} {s t : State} (X : Room base bytes args s)
    {regs : List Reg} (K : Keeps regs s t) (sp : .esp ∉ regs) : Room base bytes args t :=
  ⟨X.hbase, X.hbytes, by rw [K.1 _ sp]; exact X.room, by rw [K.1 _ sp]; exact X.top⟩

end VG.Proof.Bignum.X86.PublicRt
