module

public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Impl.Mont.X86.Words

/-! # Exponentiation by fixed 4-bit windows on 32-bit x86

`windowExponentiate` computes what `exponentiate` does, from the exponent's
top bits down: a table of the base's powers `0` to `15` in Montgomery form,
then for each four bits four squares and a multiplication by the table's
entry for them, read by a masked scan of the whole table. The exponent's
words are shifted up by four bits per window; every count and address is
public.
-/

@[expose] public section
namespace VG.Impl.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86

/-- The workspace word holding the current window. -/
def windowOffset : Nat := 4

/-- The table's entry `j`, of `n` 64-bit words, at `tab`. -/
def entry (n tab j : Nat) : Nat := tab + 8 * n * j

/-- Copy `n` 64-bit words. -/
def copyWords (n src dst : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (.imm 0)]) (selectsW (2 * n) src src dst)

/-- The `k` words at `o` shifted up by four bits, from the lowest word up:
each word's top four bits are carried in `ecx` into the word above. -/
def shiftUp (k o : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (.imm 0)]) (wordLoop k [.mov .eax (.mem (at_ .ebp o)),
    .mov .ebx (.reg .eax), .shift .shr .ebx 28, .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .ecx),
    .store (at_ .ebp o) .eax, .mov .ecx (.reg .ebx)])

/-- The top four bits of the `k`-word exponent at `exp`, into the window word. -/
def topWindow (exp k : Nat) : List Instr :=
  [.mov .eax (.mem (sc (exp + 4 * (k - 1)))), .shift .shr .eax 28, .store (sc windowOffset) .eax]

/-- ECX all ones exactly when the window is `j` (below 16). -/
def windowMask (j : Nat) : List Instr :=
  [.mov .eax (.mem (sc windowOffset)), .alu .xor .eax (.imm (BitVec.ofNat 32 j)),
   .alu .sub .eax (.imm 1), .shift .shr .eax 31, .mov .ecx (.imm 0), .alu .sub .ecx (.reg .eax)]

/-- Entry `j` into `dst` when the window is `j`. -/
def selectEntry (n tab dst j : Nat) : Prog isa :=
  .seq (.block (windowMask j)) (selectsW (2 * n) dst (entry n tab j) dst)

/-- Entries `1` to `k` over `dst`, each when the window names it. -/
def selectEntries (n tab dst : Nat) : Nat → Prog isa
  | 0 => .block []
  | k + 1 => .seq (selectEntries n tab dst k) (selectEntry n tab dst (k + 1))

/-- The window's entry into `dst`, by a scan of the whole table. -/
def selectWindow (n tab dst : Nat) : Prog isa :=
  .seq (copyWords n (entry n tab 0) dst) (selectEntries n tab dst 15)

/-- The `k` words at `src` into the words from `esi` up, `esi` past them. -/
def copyOut (k src : Nat) : Prog isa :=
  wordLoop k [.mov .eax (.mem (at_ .ebp src)), .store { base := .esi } .eax, .alu .add .esi (.imm 4)]

/-- The next entry: the one below (slot 7) times the base (slot 5), into slot 7
and the entry at `esi`; until `esi` reaches the table's end. -/
def tableStep (n tab : Nat) : Prog isa :=
  .seq (mul (contextMod n) 0 (slot n 2) (slot n 7) (slot n 7) (slot n 5)) <|
  .seq (copyOut (2 * n) (slot n 7))
    (.block [.mov .edx (.reg .edi), .alu .add .edx (.imm (BitVec.ofNat 32 (entry n tab 16))),
      .alu .cmp .esi (.reg .edx)])

/-- Entries `2` to `15`. -/
def tablePowers (n tab : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.reg .edi), .alu .add .esi (.imm (BitVec.ofNat 32 (entry n tab 2)))])
    (.loop (tableStep n tab) .ne)

/-- The table: one (slot 6) and the base (slot 5), in Montgomery form, and
their products. -/
def buildTable (n tab : Nat) : Prog isa :=
  .seq (copyWords n (slot n 6) (entry n tab 0)) <|
  .seq (copyWords n (slot n 5) (entry n tab 1)) <|
  .seq (copyWords n (slot n 5) (slot n 7)) (tablePowers n tab)

def square (n : Nat) : Prog isa := mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 6) (slot n 6)

def squares (n : Nat) : Prog isa := .seq (square n) <| .seq (square n) <| .seq (square n) (square n)

/-- The window, and the exponent shifted past it. -/
def nextWindow (n expWords : Nat) : Prog isa :=
  .seq (.block (topWindow (slot n 8) expWords)) (shiftUp expWords (slot n 8))

def windowBody (n expWords tab : Nat) : Prog isa :=
  .seq (squares n) <| .seq (nextWindow n expWords) <|
  .seq (selectWindow n tab (slot n 7))
    (mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 6) (slot n 7))

def windowStep (n expWords tab : Nat) : Prog isa :=
  .seq (windowBody n expWords tab) (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)])

/-- Input base and exponent occupy slots five and eight; the result replaces
slot six, as `exponentiate`'s. The table occupies 16 entries of `n` words at
`tab`. -/
def windowExponentiate (n expWords tab : Nat) : Prog isa :=
  .seq (mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 4) (slot n 3)) <|
  .seq (mul (contextMod n) 0 (slot n 2) (slot n 5) (slot n 5) (slot n 4)) <|
  .seq (buildTable n tab) <|
  .seq (.block [.mov .esi (.imm (BitVec.ofNat 32 (8 * expWords)))]) <|
  .seq (.loop (windowStep n expWords tab) .ne)
    (mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 6) (slot n 3))

end VG.Impl.Mont.X86.Dynamic
