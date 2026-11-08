module

public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Common
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Feistel
public import VerifiedGarbage.Spec.TripleDes

/-!
# Scalar Triple DES blocks on PPC64LE

`encryptBlock` and `decryptBlock` (schedule = r3, data = r4, scratch = r5).
The two 32-bit Feistel halves stay in `r14` (L) and `r15` (R). Each round is
`feistel` (`Feistel.lean`), which looks the eight S-boxes up at once in the
64 lanes of a word, with words of constants that the block first stores in
slots 15–61 of the scratch buffer (`storeConsts`). The three passes share
IP and FP, and one loop runs them, with the pass's first key and its step
chosen by the passes left. `r16` counts the rounds, `r17` points at the
round key, `r18` holds the key step (8 or −8) and `r19` the passes left.
Slots 0–14 of the scratch buffer save `r14`–`r28`. `r29`–`r31` are never
written, so that a caller can keep public values (ECB's count of blocks, a
mode's pointers and count) in them across a call: the taint analysis cannot
follow a value through memory. Round counters and key addresses are public.
-/

@[expose] public section

namespace VG.Impl.TripleDes.PPC64LE

open VG.PPC64LE
open VG.Spec.TripleDes (Direction)

def savedRegs : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24,
  .r25, .r26, .r27, .r28]

def blockSave : List Instr := savedRegs.zipIdx.map fun (r, i) => .store .d r .r5 (8 * i)
def blockRestore : List Instr := savedRegs.zipIdx.map fun (r, i) => .load .d r .r5 (8 * i)

/-- Load the block big-endian, apply IP, and split it into L and R. -/
def blockLoad : List Instr :=
  ([.li .r6 0, .loadRev .d .r7 .r4 .r6] : List Instr) ++
    permuteCode Spec.TripleDes.ip 64 .r8 .r7 .r9 .r10 ++
    ([.lsr .d .r14 .r8 32, .rotr .w .r15 .r8 0] : List Instr)

def swapHalves : List Instr := [rr .r6 .r14, rr .r14 .r15, rr .r15 .r6]

def roundBody : List Instr := feistel ++ swapHalves

/-- The next round key, `r18` bytes on, and the round counted. -/
def roundAdvance : List Instr := [.add .r17 .r17 .r18, .subi .r16 .r16 1]

def passStart (component : Nat) (d : Direction) : List Instr :=
  [.addi .r17 .r3 (128 * component + if d = .encrypt then 0 else 120), imm .r16 16, imm .r18 0,
    if d = .encrypt then .addi .r18 .r18 8 else .subi .r18 .r18 8]

/-- The component and direction of the pass with `left` passes left (3, 2, 1). -/
def passOf (d : Direction) (left : Nat) : Nat × Direction :=
  match d, left with
  | .encrypt, 3 => (0, .encrypt)
  | .encrypt, 2 => (1, .decrypt)
  | .encrypt, _ => (2, .encrypt)
  | .decrypt, 3 => (2, .decrypt)
  | .decrypt, 2 => (1, .encrypt)
  | .decrypt, _ => (0, .decrypt)

/-- Choose the pass's first key and step by the passes left. -/
def passSelect (d : Direction) : Prog isa :=
  .seq (.block [.subi .r20 .r19 3])
    (.ite (.zero .d .r20) (.block (passStart (passOf d 3).1 (passOf d 3).2))
      (.seq (.block [.subi .r20 .r19 2])
        (.ite (.zero .d .r20) (.block (passStart (passOf d 2).1 (passOf d 2).2))
          (.block (passStart (passOf d 1).1 (passOf d 1).2)))))

def passCountAdvance : List Instr := [.subi .r19 .r19 1]

def pass (d : Direction) : Prog isa :=
  .seq (passSelect d)
    (.seq (.loop (.block (roundBody ++ roundAdvance)) (.nonzero .d .r16))
      (.block (swapHalves ++ passCountAdvance)))

def blockBody (d : Direction) : Prog isa :=
  .seq (.block [imm .r19 3]) (.loop (pass d) (.nonzero .d .r19))

/-- Join R and L, apply FP, and store the block big-endian. -/
def blockStore : List Instr :=
  ([.rotr .d .r6 .r14 32, .logic .xor .r6 .r6 .r15] : List Instr) ++
    permuteCode Spec.TripleDes.fp 64 .r8 .r6 .r9 .r10 ++
    ([.li .r7 0, .storeRev .d .r8 .r4 .r7] : List Instr)

def block (d : Direction) : Prog isa :=
  .seq (.block (blockSave ++ storeConsts roundConsts constOff ++ blockLoad))
    (.seq (blockBody d) (.block (blockStore ++ blockRestore)))

def encryptBlock : Prog isa := block .encrypt
def decryptBlock : Prog isa := block .decrypt

end VG.Impl.TripleDes.PPC64LE
