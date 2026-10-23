module

public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Common
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Sbox
public import VerifiedGarbage.Spec.TripleDes

/-!
# Scalar Triple DES blocks on PPC64LE

`encryptBlock` and `decryptBlock` (schedule = r3, data = r4, scratch = r5).
The two 32-bit Feistel halves stay in `r14` (L) and `r15` (R). S-box input
bits are formed with fixed shifts and XORs with the round key, passed
through Boolean circuits, and XORed directly into their P-permuted
destinations. The three passes share IP and FP, and one loop runs them, with
the pass's first key and its step chosen by the passes left. `r16` counts
the rounds, `r17` points at the round key, `r18` holds the key step (8 or
−8) and `r19` the passes left. Slots 0–14 of the scratch buffer save
`r14`–`r28`, and slots 15–63 are the S-boxes' spills. `r29`–`r31` are never
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

/-- Six inputs, least significant first, for public S-box number `i`.
The source R bit comes directly from E; the key's upper sixteen bits are
never read as cipher bits. -/
def sboxInputs (i : Nat) : List Instr :=
  ([.load .d .r20 .r17 0, imm .r22 1] : List Instr) ++ (List.range 6).flatMap fun j =>
    let k := 6 * i + 5 - j
    shrFrom (q j) .r15 (32 - Spec.TripleDes.expansion.getD k 1) ++
      shrFrom .r21 .r20 (47 - k) ++
      ([.logic .xor (q j) (q j) .r21, .logic .and (q j) (q j) .r22] : List Instr)

/-- Deposit each output's low bit directly into its destination in L.
The P table contains all 32 positions, so each destination is unique. -/
def sboxOutputs (i : Nat) : List Instr :=
  [imm .r20 1] ++ (List.range 4).flatMap fun j =>
    let position := 4 * i + 4 - j
    let dst := (Spec.TripleDes.p.toList.findIdx? (· == position)).getD 0
    ([.logic .and (q j) (q j) .r20] : List Instr) ++ placeBit (q j) (31 - dst) ++
      ([.logic .xor .r14 .r14 (q j)] : List Instr)

def box (i : Nat) : List Instr := sboxInputs i ++ sboxCode i ++ sboxOutputs i

def swapHalves : List Instr := [rr .r6 .r14, rr .r14 .r15, rr .r15 .r6]

def roundBody : List Instr := (List.range 8).flatMap box ++ swapHalves

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
  .seq (.block (blockSave ++ blockLoad))
    (.seq (blockBody d) (.block (blockStore ++ blockRestore)))

def encryptBlock : Prog isa := block .encrypt
def decryptBlock : Prog isa := block .decrypt

end VG.Impl.TripleDes.PPC64LE
