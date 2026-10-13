module

public import VerifiedGarbage.Impl.TripleDes.AArch64.Common
public import VerifiedGarbage.Impl.TripleDes.AArch64.Sbox
public import VerifiedGarbage.Spec.TripleDes

@[expose] public section

namespace VG.Impl.TripleDes.AArch64

open VG.AArch64
open VG.Spec.TripleDes (Direction)

def savedRegs : List Reg := [.x19, .x20, .x21, .x22]

def blockSave : List Instr := savedRegs.zipIdx.map fun (r, i) => .str .x r .x2 (8 * i)
def blockRestore : List Instr := savedRegs.zipIdx.map fun (r, i) => .ldr .x r .x2 (8 * i)

def blockLoad : List Instr :=
  ([.ldr .x .x3 .x1 0, .rev .x3 .x3] : List Instr) ++
    permuteCode Spec.TripleDes.ip 64 .x10 .x3 .x11 .x12 ++
    ([.lsr .x .x19 .x10 32, rr .x20 .x10] : List Instr) ++ mask .x20 32

def sboxInputs (i : Nat) : List Instr :=
  ([.ldr .x .x10 .x22 0, imm .x12 1] : List Instr) ++ (List.range 6).flatMap fun j =>
    let k := 6 * i + 5 - j
    [rr (q j) .x20] ++ shr (q j) (32 - Spec.TripleDes.expansion.getD k 1) ++
      [rr .x11 .x10] ++ shr .x11 (47 - k) ++
      ([.logic .eor .x (q j) (q j) .x11, .logic .and .x (q j) (q j) .x12] : List Instr)

def sboxOutputs (i : Nat) : List Instr :=
  [imm .x10 1] ++ (List.range 4).flatMap fun j =>
    let position := 4 * i + 4 - j
    let dst := (Spec.TripleDes.p.toList.findIdx? (· == position)).getD 0
    ([.logic .and .x (q j) (q j) .x10] : List Instr) ++ placeBit (q j) (31 - dst) ++
      ([.logic .eor .x .x19 .x19 (q j)] : List Instr)

def box (i : Nat) : List Instr := sboxInputs i ++ sboxCode i ++ sboxOutputs i

def swapHalves : List Instr := [rr .x3 .x19, rr .x19 .x20, rr .x20 .x3]

def roundBody : List Instr := (List.range 8).flatMap box ++ swapHalves

/-! One loop runs the three passes. The key step of the pass (8 or −8) is in
the low lane of `v0` and the passes left in that of `v1`, which the rounds
never touch; the pass's first key and its step are chosen by the passes
left. -/

/-- The next round key, `v0.d[0]` bytes on, and the round counted. -/
def roundAdvance : List Instr :=
  [.umov .x .x3 .v0 0, .add .x .x22 .x22 .x3, .subImm .x .x21 .x21 1]

def passStart (component : Nat) (d : Direction) : List Instr :=
  [.addImm .x .x22 .x0 (128 * component + if d = .encrypt then 0 else 120),
    imm .x21 16, .sub .x .x3 .x0 .x0,
    if d = .encrypt then .addImm .x .x3 .x3 8 else .subImm .x .x3 .x3 8,
    .vop (.dup .d2 .v0 .x3)]

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
  .seq (.block [.umov .x .x3 .v1 0, .subImm .x .x4 .x3 3])
    (.ite (.zero .x .x4) (.block (passStart (passOf d 3).1 (passOf d 3).2))
      (.seq (.block [.subImm .x .x4 .x3 2])
        (.ite (.zero .x .x4) (.block (passStart (passOf d 2).1 (passOf d 2).2))
          (.block (passStart (passOf d 1).1 (passOf d 1).2)))))

def passCountAdvance : List Instr :=
  [.umov .x .x3 .v1 0, .subImm .x .x3 .x3 1, .vop (.dup .d2 .v1 .x3)]

def pass (d : Direction) : Prog isa :=
  .seq (passSelect d)
    (.seq (.loop (.block (roundBody ++ roundAdvance)) (.nonzero .x .x21))
      (.block (swapHalves ++ passCountAdvance)))

def blockBody (d : Direction) : Prog isa :=
  .seq (.block [imm .x3 3, .vop (.dup .d2 .v1 .x3)]) (.loop (pass d) (.nonzero .x .x3))

def blockStore : List Instr :=
  ([.lsl .x .x3 .x19 32, .logic .eor .x .x3 .x3 .x20] : List Instr) ++
    permuteCode Spec.TripleDes.fp 64 .x10 .x3 .x11 .x12 ++ ([.rev .x3 .x10] : List Instr)

def block (d : Direction) : Prog isa :=
  .seq (.block (blockSave ++ blockLoad))
    (.seq (blockBody d) (.block (blockStore ++ blockRestore ++ ([.str .x .x3 .x1 0] : List Instr))))

def encryptBlock : Prog isa := block .encrypt
def decryptBlock : Prog isa := block .decrypt

end VG.Impl.TripleDes.AArch64
