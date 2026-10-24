module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Freeze
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Layout
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Packed

/-!
# Ed25519 on PPC64LE: decoding a point

ARMv7's decoding (`Impl/Ed25519/Arm/PointDecode.lean`, `Recover.lean`,
`RecoverSign.lean`): `y` and the sign from the encoding at `r14`, `y`
canonical, the candidate `x` by the square root's power, and its checks. The
result is in `r17`: 1 if the encoding is a point, 0 otherwise.
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE
open VG.PPC64LE
open VG.Impl.X25519.PPC64LE (low31)

def recoverInitOps : List FieldOp := [
  .const 16 Spec.Ed25519.d, .const 4 1, .mulc 5 1 1, .sub 6 5 4,
  .mulc 7 16 1, .mulc 7 7 1, .add 7 7 4,
  .mulc 8 7 7, .mulc 9 8 7, .mulc 10 9 9, .mulc 10 10 7, .mulc 2 6 10]

def recoverFinishOps : List FieldOp := [
  .const 5 0, .sub 12 5 6, .mulc 0 6 9, .mulc 0 0 15, .mulc 11 7 0, .mulc 11 11 0]

def recoverCandidate : Prog isa :=
  .seq (fieldCode recoverInitOps) (.seq rootPower (fieldCode recoverFinishOps))

/-- `r5` is zero exactly when the parity of the reduced `x` at `FR` is the
sign. -/
def recoverParity : List Instr :=
  [.load .w .r7 .r6 FR, .lsl .r7 .r7 63, .lsr .d .r7 .r7 63, .load .d .r8 .r6 SIGN,
    .logic .xor .r5 .r7 .r8]

def recoverSuccessOps : List FieldOp := [.const 2 1, .mulc 3 0 1]

def recoverSuccess : Prog isa := .seq (fieldCode recoverSuccessOps) (.block [.li .r17 1])

def recoverInvalid : Prog isa := .block [.li .r17 0]

def recoverAdjustSign : Prog isa :=
  .seq (.block (freeze 0 ++ recoverParity))
    (.seq (.ite (.zero .d .r5) (.block []) (fieldCode [.const 5 0, .sub 0 5 0])) recoverSuccess)

def signTest : List Instr := [.load .d .r5 .r6 SIGN]

def recoverSign : Prog isa :=
  .seq (fieldZero 0) (.ite (.zero .d .r5)
    (.seq (.block signTest) (.ite (.nonzero .d .r5) recoverInvalid recoverAdjustSign)) recoverAdjustSign)

def recoverPoint : Prog isa :=
  .seq recoverCandidate (.seq (fieldEqual 11 6) (.ite (.zero .d .r5) recoverSign
    (.seq (fieldEqual 11 12) (.ite (.zero .d .r5)
      (.seq (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mulc 0 0 18]) recoverSign)
      recoverInvalid))))

/-- `y`'s sign bit (bit 255) to `SIGN`, and cleared. -/
def splitYSign : List Instr :=
  [.load .w .r7 .r6 (offset 1 + 28), .lsr .d .r8 .r7 31, .store .d .r8 .r6 SIGN] ++ low31 ++
    [.store .w .r7 .r6 (offset 1 + 28)]

def canonicalY : Prog isa := .seq (.block (freeze 1)) (.block (wordsEqual (offset 1) FR))

def pointDecodeLoad : Prog isa :=
  .seq (.block (unpackField (offset 1) 0 ++ splitYSign)) canonicalY

def pointDecode : Prog isa := .seq pointDecodeLoad (.ite (.zero .d .r5) recoverPoint recoverInvalid)

def pointEqualOps : List FieldOp := [.mulc 8 0 6, .mulc 9 4 2, .mulc 10 1 6, .mulc 11 5 2]

def pointEqual : Prog isa :=
  .seq (fieldCode pointEqualOps) (.seq (fieldEqual 8 9) (.ite (.zero .d .r5)
    (.seq (fieldEqual 10 11) (.ite (.zero .d .r5) (.block [.li .r17 1]) recoverInvalid)) recoverInvalid))

end VG.Impl.Ed25519.PPC64LE
