module

public import VerifiedGarbage.Impl.Aes.AArch64.AeseBlocks
public import VerifiedGarbage.Impl.AesCbc.AArch64.Decrypt

/-!
# CBC encryption with resident keys and a preloaded next-block operand

The AES state in v31 omits the final round-key XOR. The next plaintext,
pre-XORed with k₀ XOR kNr in v7, supplies AESE's first-round key operand.
AESE therefore combines the previous ciphertext, plaintext, and k₀ without
an intervening dependent XOR. The next plaintext is loaded during the current
block's rounds, guarded by the public remaining-block count.

All three key sizes are specialized outside the loop. Only caller-saved
registers are written; stack and scratch are unused.
-/

@[expose] public section
namespace VG.Impl.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Impl.Aes.AArch64.Aese

def rounds (start count : Nat) : List Instr :=
  (List.range count).flatMap fun j => rnd [.v31] (kreg (start+j))

def first : List Instr := [.vop (.aese .v31 .v0),.vop (.aesmc .v31 .v31)]

def prefetch : List Instr := [.ldrq .v0 .x2 16,.vop (.logic .eor .v0 .v0 .v7)]

def finish : List Instr :=
  [.vop (.aese .v31 .v29),.vop (.logic .eor .v1 .v31 .v30),.strq .v1 .x2 0,
    .addImm .x .x2 .x2 16]

def step (nr : Nat) : Prog isa :=
  .seq (.block (first ++ [.subImm .x .x3 .x3 1] ++ rounds 1 4)) <|
  .seq (.ite (.zero .x .x3) (.block []) (.block prefetch))
    (.block (rounds 5 (nr-6) ++ finish))

/-- Fix each key size's loop position relative to the 32-byte fetch boundary.
The public x12 writes are padding outside the loop, executed only once. -/
def enter (nr : Nat) : List Instr :=
  [.ldrq .v0 .x2 0,.vop (.logic .eor .v0 .v0 .v7),.align 5] ++
    List.replicate (if nr=10 then 0 else if nr=12 then 6 else 1) (.movz .x .x12 0 0)

def setup : List Instr :=
  Decrypt.adaptArgs ++ encSetup ++
    [.vop (.logic .eor .v7 .v16 .v30),.vop (.logic .eor .v31 .v31 .v30)]

def body (nr : Nat) : Prog isa :=
  .seq (.block setup) <|
  .seq (.ite (.zero .x .x3) (.block [])
    (.seq (.block (enter nr)) (.loop (step nr) (.nonzero .x .x3))))
    (.block [.vop (.logic .eor .v31 .v31 .v30),.strq .v31 .x11 0])

def code : Prog isa :=
  .seq (.block [.subImm .x .x9 .x1 10,.subImm .x .x10 .x1 12])
    (.ite (.zero .x .x9) (body 10) (.ite (.zero .x .x10) (body 12) (body 14)))
end VG.Impl.AesCbc.AArch64.Encrypt
