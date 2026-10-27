module

public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! # Calling the probable-prime test from the persistent generation frame

The tests are functions of their own (`vg_dsa_probable_prime_{bits}`),
called with the scratch base (frame word 5) as their working space, the
unread rest of the witness tape (words 14, 15 and 16) and frame word 19 for
the octets they read. Their status, 2 for a composite, is stored as the
generation's 3 in word 19, and the octets read are added to word 16 unless
the tape ran out. -/

@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- The test's arguments: `ws`, its words, the rest of the tape and `used`. -/
def primeCallArgs : List Instr :=
  [.ldrSp .x0 40, movi .x1 (VG.Impl.Dsa.Generation.Layout.domainCheck / 8),
   .ldrSp .x2 112, .ldrSp .x5 128, .add .x .x2 .x2 .x5,
   .ldrSp .x3 120, .sub .x .x3 .x3 .x5, .addSp .x4 152]

/-- The status, a `u32` in `w0`; the octets read added to the cursor if the
tape sufficed; then the status stored, with 2 as 3. -/
def primeCallStatus : Prog isa :=
  .seq (.block [.addImm .w .x0 .x0 0])
    (.seq (.ite (.zero .x .x0) (.block [])
        (.block [.ldrSp .x3 152, .ldrSp .x4 128, .add .x .x3 .x3 .x4, .strSp .x3 128]))
      (.block [.lsr .x .x3 .x0 1, .add .x .x0 .x0 .x3, .strSp .x0 152]))

/-- The test of a candidate of `bits` bits, called as `prime bits`. -/
def primeCall (prime : Nat → Prog isa) (bits : Nat) : Prog isa :=
  .seq (.block primeCallArgs) (.seq (prime bits) primeCallStatus)

end VG.Impl.Dsa.AArch64.Generation
