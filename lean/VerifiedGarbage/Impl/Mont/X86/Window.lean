module

public import VerifiedGarbage.Impl.Mont.X86.Context

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

/-- Shift the word at `out` up by four bits (four doublings), bringing in
the top four bits of the word below it, or zeros for the lowest word. -/
def shiftUpWord (out : Nat) (lowest : Bool) : List Instr :=
  [.mov .edx (.mem (sc out)), .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx),
   .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx)] ++
  (if lowest then [] else
    [.mov .eax (.mem (sc (out - 4))), .shift .shr .eax 28, .alu .add .edx (.reg .eax)]) ++
  [.store (sc out) .edx]

/-- Shift the `k` words at `exp` up by four bits, from the top word down. -/
def shiftUp : Nat → Nat → List Instr
  | 0, _ => []
  | k + 1, exp => shiftUpWord (exp + 4 * k) (k == 0) ++ shiftUp k exp

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

/-- Entries `2` to `k + 1`: each the previous one times the base (slot 5),
in slot 7. -/
def tablePowers (n tab : Nat) : Nat → Prog isa
  | 0 => .block []
  | k + 1 => .seq (tablePowers n tab k)
      (.seq (mul (contextMod n) 0 (slot n 2) (slot n 7) (slot n 7) (slot n 5))
        (copyWords n (slot n 7) (entry n tab (k + 2))))

/-- The table: one (slot 6) and the base (slot 5), in Montgomery form, and
their products. -/
def buildTable (n tab : Nat) : Prog isa :=
  .seq (copyWords n (slot n 6) (entry n tab 0)) <|
  .seq (copyWords n (slot n 5) (entry n tab 1)) <|
  .seq (copyWords n (slot n 5) (slot n 7)) (tablePowers n tab 14)

def square (n : Nat) : Prog isa := mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 6) (slot n 6)

def squares (n : Nat) : Prog isa := .seq (square n) <| .seq (square n) <| .seq (square n) (square n)

def windowBody (n expWords tab : Nat) : Prog isa :=
  .seq (squares n) <|
  .seq (.block (topWindow (slot n 8) expWords ++ shiftUp expWords (slot n 8))) <|
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
