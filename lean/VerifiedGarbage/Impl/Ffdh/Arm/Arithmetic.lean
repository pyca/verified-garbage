module

public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
public import VerifiedGarbage.Impl.Bignum.Arm.WindowExp
public import VerifiedGarbage.Impl.Bignum.Arm.ArrayCompare

/-! FFDH's native ARMv7 arithmetic uses the runtime-sized RSA workspace and
its three-bit fixed-window exponentiation. Slot zero of the local frame
holds the workspace base, as RSA's arithmetic helpers require. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm
open VG VG.Arm

/-- Initialize the modulus, its inverse, and R-squared using RSA's code.
The modulus pointer and byte length occupy local offsets 8 and 12. -/
def prepare : Prog isa :=
  .seq VG.Impl.Bignum.Arm.PublicFn.prepare VG.Impl.Bignum.Arm.precompute

/-- Full-width secret exponentiation, including a scan of every table entry.
Exponent pointer and count occupy RSA header offsets 128 and 132. -/
def pow : Prog isa := VG.Impl.Bignum.Arm.windowExpPhase

/-- Install the exponent controls before importing the base, so the import
may use every scratch register. Source pointer and count are r4 and r6;
the exponent pointer and count are r1 and r2. -/
def power : Prog isa := .seq (.block VG.Impl.Bignum.Arm.expControls)
  (.seq (VG.Impl.Bignum.Arm.importOperand 1) pow)

/-- Preserve AAPCS registers and reserve native locals without putting
secret-dependent state in the ABI argument area. -/
def framed (body : Prog isa) : Prog isa :=
  .frame (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (.seq (.frame (.alloc 72) body (.free 72)) (.block VG.Impl.Bignum.Arm.PcFn.restore))
    (.pop .r12 56)

end VG.Impl.Ffdh.Arm
