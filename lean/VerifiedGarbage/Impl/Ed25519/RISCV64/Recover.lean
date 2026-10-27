module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.Freeze
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Scalar

/-!
# Ed25519 on RISC-V: decoding a point

The PPC64LE decoding (`Impl/Ed25519/PPC64LE/Recover.lean`, ARMv7's): `y`
and the sign from the encoding at `s0`, `y` canonical, the candidate `x` by
the square root's power, and its checks. The result is in `s3`: 1 if the
encoding is a point, 0 otherwise. The sign is a word at `SIGN`.
-/

@[expose] public section

namespace VG.Impl.Ed25519.RISCV64
open VG.RISCV64
open VG.Impl.X25519.RISCV64 (low31)

/-- A decoding's sign bit. -/
def SIGN : Nat := 24

def recoverInitOps : List FieldOp := [
  .const 16 Spec.Ed25519.d, .const 4 1, .mulc 5 1 1, .sub 6 5 4,
  .mulc 7 16 1, .mulc 7 7 1, .add 7 7 4,
  .mulc 8 7 7, .mulc 9 8 7, .mulc 10 9 9, .mulc 10 10 7, .mulc 2 6 10]

def recoverFinishOps : List FieldOp := [
  .const 5 0, .sub 12 5 6, .mulc 0 6 9, .mulc 0 0 15, .mulc 11 7 0, .mulc 11 11 0]

def recoverCandidate : Prog isa :=
  .seq (fieldCode recoverInitOps) (.seq rootPower (fieldCode recoverFinishOps))

/-- `a2` is zero exactly when the parity of the reduced `x` at `FR` is the
sign. -/
def recoverParity : List Instr :=
  [.load .w .a4 .a3 FR, .shift .sll .d .a4 .a4 63, .shift .srl .d .a4 .a4 63, .load .w .a5 .a3 SIGN,
    .logic .xor .a2 .a4 .a5]

def recoverSuccessOps : List FieldOp := [.const 2 1, .mulc 3 0 1]

def recoverSuccess : Prog isa := .seq (fieldCode recoverSuccessOps) (.block [.li .s3 1])

def recoverInvalid : Prog isa := .block [.li .s3 0]

def recoverAdjustSign : Prog isa :=
  .seq (.block (freeze 0 ++ recoverParity))
    (.seq (.ite (.zero .a2) (.block []) (fieldCode [.const 5 0, .sub 0 5 0])) recoverSuccess)

def signTest : List Instr := [.load .w .a2 .a3 SIGN]

def recoverSign : Prog isa :=
  .seq (fieldZero 0) (.ite (.zero .a2)
    (.seq (.block signTest) (.ite (.nonzero .a2) recoverInvalid recoverAdjustSign)) recoverAdjustSign)

def recoverPoint : Prog isa :=
  .seq recoverCandidate (.seq (fieldEqual 11 6) (.ite (.zero .a2) recoverSign
    (.seq (fieldEqual 11 12) (.ite (.zero .a2)
      (.seq (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mulc 0 0 18]) recoverSign)
      recoverInvalid))))

/-- `y`'s sign bit (bit 255) to `SIGN`, and cleared. -/
def splitYSign : List Instr :=
  [.load .w .a4 .a3 (offset 1 + 28), .shift .srl .d .a5 .a4 31, .store .w .a5 .a3 SIGN] ++ low31 ++
    [.store .w .a4 .a3 (offset 1 + 28)]

def canonicalY : Prog isa := .seq (.block (freeze 1)) (.block (wordsEqual (offset 1) FR))

def pointDecodeLoad : Prog isa :=
  .seq (.block (unpackField .s0 (offset 1) 0 ++ splitYSign)) canonicalY

def pointDecode : Prog isa := .seq pointDecodeLoad (.ite (.zero .a2) recoverPoint recoverInvalid)

def pointEqualOps : List FieldOp := [.mulc 8 0 6, .mulc 9 4 2, .mulc 10 1 6, .mulc 11 5 2]

def pointEqual : Prog isa :=
  .seq (fieldCode pointEqualOps) (.seq (fieldEqual 8 9) (.ite (.zero .a2)
    (.seq (fieldEqual 10 11) (.ite (.zero .a2) (.block [.li .s3 1]) recoverInvalid)) recoverInvalid))

end VG.Impl.Ed25519.RISCV64
