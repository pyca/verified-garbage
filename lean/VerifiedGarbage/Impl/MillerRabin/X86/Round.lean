module

public import VerifiedGarbage.Impl.MillerRabin.X86.Workspace

/-! # A prepared, four-bit-window Miller–Rabin round on i686

This follows the shared window algorithm used by the ARM and x86-64
rounds. Table entries are appended directly, avoiding a shift of the
partially built table after each product. All table reads scan public
addresses; the candidate and witness choose no branch or address.
-/

@[expose] public section
namespace VG.Impl.MillerRabin.X86
open VG VG.X86 VG.Impl.Mont.X86

def seqs (ps : List (Prog isa)) : Prog isa := ps.foldr .seq (.block [])

def sE1 : Nat := 184
def sE2 : Nat := 188
def sV : Nat := 212
def sF : Nat := 232
def sK : Nat := 236
def sQ : Nat := 240
def sR : Nat := 244

def aX : Nat := 5
def aY : Nat := 6
def aM1 : Nat := 8
def aT0 : Nat := 11
def aE : Nat := 27

def tabCopies : Prog isa :=
  .seq (copy aT0 9) (.seq (copy (aT0 + 1) aX) (copy aY aX))

def tabInit : Prog isa := seqs [tabCopies,
  .block (arrayPointer .eax (aT0 + 2) .edx ++ [.store (sp tableCursor) .eax,
    .mov .eax (.imm 14), .store (sc sK) .eax])]

def tabTransfer : Prog isa :=
  .seq (.block (arrayPointer .esi aY .edx ++ [.mov .ebx (.mem (sp tableCursor))] ++ width .ecx))
    VG.Impl.Bignum.X86.copyBytes

def tabEnd : List Instr :=
  [.alu .add .ebx (.imm 16), .store (sp tableCursor) .ebx,
      .mov .eax (.mem (sc sK)), .alu .sub .eax (.imm 1), .store (sc sK) .eax]

def tabStore : Prog isa := .seq tabTransfer (.block tabEnd)

def tabStep : Prog isa := .seq (product aY aY aX) tabStore

/-- Incorporate a minus-one comparison only above the threshold. -/
def sqFlag : List Instr :=
  [.mov .ecx (.mem (sc sQ)), .mov .edx (.mem (sc sR)), .alu .sub .edx (.reg .ecx),
   .shift .shr .edx 31, .alu .and .edx (.mem (sc sE2)), .mov .eax (.mem (sc sF)),
   .alu .or .eax (.reg .edx), .store (sc sF) .eax,
   .alu .sub .ecx (.imm 1), .store (sc sQ) .ecx]

def sqStep : Prog isa := seqs [product aY aY aY, equal sE2 aY aM1, .block sqFlag]
def sqLoop : Prog isa := .loop sqStep .ne

/-- `esi` is all ones exactly for the current digit's table entry. -/
def maskJ (j : Nat) : List Instr :=
  [.mov .eax (.mem (sc sV)), .shift .shr .eax 28,
   .alu .xor .eax (.imm (BitVec.ofNat 32 j)), .alu .sub .eax (.imm 1), .shift .shr .eax 31,
   .mov .esi (.imm 0), .alu .sub .esi (.reg .eax)]

def scanFrom : Nat → Nat → Prog isa
  | _, 0 => .block []
  | j, n + 1 => .seq (.block (maskJ j))
      (.seq (select aX (aT0 + j)) (scanFrom (j + 1) n))

def scan : Prog isa := .seq (copy aX aT0) (scanFrom 1 15)

def sqFour : List Instr :=
  [.mov .eax (.imm 0), .store (sc sR) .eax, .mov .eax (.imm 4), .store (sc sQ) .eax]

/-- Update the flag after a nonzero digit and advance within the word. -/
def winFlag : List Instr :=
  [.mov .eax (.mem (sc sV)), .mov .edx (.reg .eax), .shift .shr .edx 28,
   .alu .sub .edx (.imm 1), .shift .shr .edx 31,
   .mov .ecx (.reg .edx), .alu .xor .ecx (.imm 1),
   .mov .ebx (.mem (sc sE1)), .alu .or .ebx (.mem (sc sE2)), .alu .and .ebx (.reg .ecx),
   .mov .ebp (.mem (sc sF)), .alu .and .ebp (.reg .edx), .alu .or .ebx (.reg .ebp),
   .store (sc sF) .ebx]

def winAdvance : List Instr := List.replicate 4 (.alu .add .eax (.reg .eax)) ++
  [.store (sc sV) .eax, .mov .eax (.mem (sc sK)), .alu .sub .eax (.imm 1),
   .store (sc sK) .eax, .alu .and .eax (.imm 7), .alu .cmp .eax (.imm 0)]

def winEnd : List Instr := winFlag ++ winAdvance

def win : Prog isa :=
  .seq (.seq (.block sqFour) sqLoop)
    (.seq (.seq scan (product aY aY aX))
      (.seq (equal sE1 aY aT0) (.seq (equal sE2 aY aM1) (.block winEnd))))

def wordLoad : List Instr :=
  arrayPointer .ebp aE .edx ++
  [.mov .ecx (.mem (sc sK)), .shift .shr .ecx 3, .alu .sub .ecx (.imm 1),
   .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .alu .add .ebp (.reg .ecx),
   .mov .eax (.mem (at_ .ebp 0)), .store (sc sV) .eax]

def word : Prog isa := seqs [.block wordLoad, .loop win .ne,
  .block [.mov .eax (.mem (sc sK)), .alu .cmp .eax (.imm 0)]]

def winCounters : List Instr :=
  [.mov .eax (.imm 0), .store (sc sF) .eax] ++ width .eax ++
    [.alu .add .eax (.reg .eax), .store (sc sK) .eax]

def winInit : Prog isa := seqs [copy aM1 10, copy aY aT0, .block winCounters]

/-- Fold the prepared one-hot word to obtain the final threshold `4 - sigma`. -/
def foldBits : List Instr :=
  [.mov .edx (.reg .eax), .shift .shr .edx 16, .alu .or .eax (.reg .edx),
   .mov .edx (.reg .eax), .shift .shr .edx 8, .alu .or .eax (.reg .edx),
   .mov .edx (.reg .eax), .shift .shr .edx 4, .alu .or .eax (.reg .edx),
   .mov .edx (.reg .eax), .shift .shr .edx 1, .alu .and .edx (.imm 1),
   .mov .ecx (.reg .eax), .shift .shr .ecx 2, .alu .and .ecx (.imm 1),
   .shift .shr .eax 3, .alu .and .eax (.imm 1),
   .alu .add .eax (.reg .edx), .alu .add .edx (.reg .edx), .alu .add .eax (.reg .edx),
   .alu .add .ecx (.reg .ecx), .alu .add .eax (.reg .ecx)]

def lowBits : List Instr :=
  arrayPointer .ebp aE .edx ++ width .ecx ++
  [.alu .add .ebp (.reg .ecx), .mov .eax (.mem (at_ .ebp 0)), .alu .or .eax (.mem (at_ .ebp 4))] ++
  foldBits ++ [.store (sc sR) .eax, .mov .eax (.imm 3), .store (sc sQ) .eax]

def entry : List Instr :=
  savedRegisters.map (fun (r, d) => .store (sp d) r) ++
  [.mov .edi (.mem (sp (frameBytes + 4))),
   .mov .eax (.mem (sp (frameBytes + 8))), .store (sp savedLength) .eax]

def finish : List Instr :=
  [.mov .eax (.mem (sc sF))] ++
    savedRegisters.map (fun (r, d) => .mov r (.mem (sp d)))

def arithmetic : Prog isa :=
  .seq tabInit (.seq (.loop tabStep .ne) (.seq winInit (.seq (.loop word .ne)
    (.seq (.block lowBits) sqLoop))))

def body : Prog isa := seqs [.block entry, saveProtected, arithmetic, restoreProtected, .block finish]

def code : Prog isa := .frame (.alloc frameBytes) body (.free frameBytes)

end VG.Impl.MillerRabin.X86
