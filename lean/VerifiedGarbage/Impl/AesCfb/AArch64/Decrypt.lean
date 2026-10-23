module

public import VerifiedGarbage.Impl.Aes.AArch64.AeseBlocks

/-! # CFB128 decryption with eight independent AES states and resident round keys

Each AES input is the preceding original ciphertext (or the initial IV).
Load the group before any plaintext store. Only caller-saved registers are
written; no stack or scratch storage is used. Requires FEAT_AES only.
-/

@[expose] public section

namespace VG.Impl.AesCfb.AArch64.Decrypt

open VG VG.AArch64
open VG.Impl.Aes.AArch64.Aese

def inputs : List VReg → List Instr
  | [] => []
  | b :: bs => .vop (.logic .orr b .v31 .v31) :: ldData bs 0

def finish (b : VReg) (i : Nat) : List Instr :=
  [.ldrq .v31 .x2 (16*i), .vop (.logic .eor b b .v31), .strq b .x2 (16*i)]

def finishData : List VReg → Nat → List Instr
  | [], _ => []
  | b :: bs, i => finish b i ++ finishData bs (i+1)

def advance (k : Nat) : List Instr :=
  [.addImm .x .x2 .x2 (16*k), .subImm .x .x3 .x3 k]

def group (rs : List VReg) : Prog isa :=
  .seq (.block (inputs rs)) (.seq (aes rs)
    (.block (finishData rs 0 ++ advance rs.length)))

def checkEnough (k : Nat) : List Instr :=
  [.subImm .x .x9 .x3 k, .lsr .x .x13 .x9 63]

def batch : Prog isa := .seq (group regs8) (.block (checkEnough 8))

def adaptArgs : List Instr :=
  [.addImm .x .x11 .x2 0, .addImm .x .x2 .x3 0,
    .addImm .x .x3 .x4 0, .addImm .x .x4 .x5 0, .ldrq .v31 .x11 0]

def loops : Prog isa :=
 .seq (.block (checkEnough 8))
  (.seq (.ite (.nonzero .x .x13) (.block [])
    (.seq (.block [.align 4]) (.loop batch (.zero .x .x13))))
   (.seq (.block (checkEnough 4))
    (.seq (.ite (.nonzero .x .x13) (.block []) (group (regs8.take 4)))
     (.ite (.zero .x .x3) (.block []) (.loop (group [.v0]) (.nonzero .x .x3))))))

def code : Prog isa :=
  .seq (.block (adaptArgs ++ encSetup))
    (.seq loops (.block [.strq .v31 .x11 0]))

end VG.Impl.AesCfb.AArch64.Decrypt
