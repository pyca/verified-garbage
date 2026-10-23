module

public import VerifiedGarbage.Impl.Aes.AArch64.AeseBlocks

/-!
# CBC decryption with resident round keys and seven independent AES states

For FEAT_AES and FEAT_SHA3. The signature and workspace are the existing
CBC decryption interface. The schedule is converted once per call. Key-size
dispatch is outside the loops; each loop decrypts seven independent blocks.
The original ciphertext is loaded before each plaintext store, retaining the
chaining value in v31. EOR3 combines the final round-key and chaining XORs.

Only caller-saved registers are written. No stack or scratch space is used.
-/

@[expose] public section

namespace VG.Impl.AesCbc.AArch64.Decrypt

open VG VG.AArch64
open VG.Impl.Aes.AArch64.Aese

/-- The equivalent inverse cipher, except for the final XOR with k₀. -/
def rounds (nr : Nat) (regs : List VReg) : Prog isa :=
  .block (drnd regs .v30 ++
    (if nr = 10 then [] else
      (if nr = 12 then [] else drnd regs .v29 ++ drnd regs .v28) ++
        drnd regs .v27 ++ drnd regs .v26) ++
    (List.range 8).flatMap (fun j => drnd regs (kreg (9-j))) ++
    regs.map (fun b => .vop (.aesd b .v17)))

/-- Finish one block and retain its original ciphertext for its successor. -/
def finish (b : VReg) (i : Nat) : List Instr :=
  [.vop (.eor3 b b .v16 .v31), .ldrq .v31 .x2 (16*i), .strq b .x2 (16*i)]

def finishData : List VReg → Nat → List Instr
  | [], _ => []
  | b :: bs, i => finish b i ++ finishData bs (i + 1)

def regs7 : List VReg := [.v0,.v1,.v2,.v3,.v4,.v5,.v6]

/-- Public underflow test: x13 is one exactly when fewer than seven blocks remain. -/
def checkEnough : List Instr :=
  [.subImm .x .x9 .x3 7, .lsr .x .x13 .x9 63]

/-- Seven blocks; x3 counts remaining blocks and x13 records the next loop guard. -/
def batch (nr : Nat) : Prog isa :=
  .seq (.block (ldData regs7 0))
    (.seq (rounds nr regs7)
      (.block (finishData regs7 0 ++
        [.addImm .x .x2 .x2 112, .subImm .x .x3 .x3 7] ++ checkEnough)))

/-- The remaining zero to six blocks, without loading the keys again. -/
def tail (nr : Nat) : Prog isa :=
  .seq (.block (ldData [.v0] 0))
    (.seq (rounds nr [.v0])
      (.block (finish .v0 0 ++ [.addImm .x .x2 .x2 16, .subImm .x .x3 .x3 1])))

def adaptArgs : List Instr :=
  [.addImm .x .x11 .x2 0, .addImm .x .x2 .x3 0,
    .addImm .x .x3 .x4 0, .addImm .x .x4 .x5 0, .ldrq .v31 .x11 0]

def loops (nr : Nat) : Prog isa :=
  .seq (.block checkEnough)
    (.seq (.ite (.nonzero .x .x13) (.block [])
        (.seq (.block [.align 4]) (.loop (batch nr) (.zero .x .x13))))
      (.ite (.zero .x .x3) (.block [])
        (.seq (.block [.align 4]) (.loop (tail nr) (.nonzero .x .x3)))))

/-- The original argument order is schedule, rounds, IV, data, n, scratch. -/
def body (nr : Nat) : Prog isa :=
  .seq (.block (adaptArgs ++ decSetup))
    (.seq (loops nr) (.block [.strq .v31 .x11 0]))

def code : Prog isa :=
  .seq (.block [.subImm .x .x9 .x1 10, .subImm .x .x10 .x1 12])
    (.ite (.zero .x .x9) (body 10) (.ite (.zero .x .x10) (body 12) (body 14)))

end VG.Impl.AesCbc.AArch64.Decrypt
