module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.ParameterSearch
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Validate
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Output
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TrialTable

/-! # cdecl entry for finite-tape DSA parameter generation on i686

The outer 16 bytes save callee-saved registers. The inner 148-byte frame
holds persistent search state; incoming arguments start at offset 168.
The shared arithmetic arena is initialized before any candidate search.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Pbkdf2.Stream.X86

def savedRegisters : List (Nat × Reg) := [(0, .ebx), (4, .ebp), (8, .esi), (12, .edi)]
def saveRegisters : List Instr := savedRegisters.map fun (d, r) => .store (VG.Impl.Mont.X86.at_ .esp d) r
def restoreRegisters : List Instr := savedRegisters.map fun (d, r) => .mov r (.mem (VG.Impl.Mont.X86.at_ .esp d))

def incomingSlots : List (Nat × Nat) :=
  [(0, 6), (1, 7), (2, 17), (3, 18), (4, 8), (5, 9), (6, 11), (7, 12), (8, 13), (9, 15), (10, 5)]

def entryIncoming : List Instr := incomingSlots.flatMap fun (arg, slot) =>
  [.mov .eax (.mem (VG.Impl.Mont.X86.at_ .esp (168 + 4 * arg))), .store (frameSlot slot) .eax]

def derivedSlots : List (Nat × Nat) :=
  [(3, VG.Impl.Dsa.Generation.Layout.wrappedSeed), (4, VG.Impl.Dsa.Generation.Layout.hashes),
   (14, VG.Impl.Dsa.Generation.Layout.hash)]

def entryDerived : List Instr :=
  (derivedSlots.flatMap fun (slot, offset) => bufferPointer .eax offset ++ [.store (frameSlot slot) .eax]) ++
  [.mov .eax (.imm 0), .store (frameSlot 16) .eax]

def clearScratch (plen : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.mem (frameSlot 5)),
      .mov .ecx (.imm (BitVec.ofNat 32 (VG.Impl.Dsa.Generation.Layout.usedBytes plen))), .mov .eax (.imm 0)])
    (.loop (.block [.store8 (VG.Impl.Mont.X86.at_ .esi 0) .al, .alu .add .esi (.imm 1), .alu .sub .ecx (.imm 1)]) .ne)

def initializeSearch (plen : Nat) : Prog isa :=
  .seq (clearScratch plen)
    (.seq (.block [.mov .edi (.mem (frameSlot 5))]) (trialTable 1024))

def generate (H : Hash) (name : String) (check : Prog isa) (plen qlen : Nat) : Prog isa :=
  .seq (initializeSearch plen)
    (.seq (parameterSearch H plen qlen (finishDomain name check plen qlen)) finishOutput)

def dispatch (H1 H256 : Hash) (name : String) (check : Prog isa) : Prog isa :=
  .seq (.block [.mov .eax (.mem (frameSlot 17)), .alu .cmp .eax (.imm 128)])
    (.ite .e (generate H1 name check 128 20)
      (.seq (.block [.alu .cmp .eax (.imm 256)])
        (.ite .e (generate H256 name check 256 32) (generate H256 name check 384 32))))

def entryBody (H1 H256 : Hash) (name : String) (check : Prog isa) : Prog isa :=
  .seq (.block (entryIncoming ++ entryDerived)) (dispatch H1 H256 name check)

def code (H1 H256 : Hash) (name : String) (check : Prog isa) : Prog isa :=
  .frame (.alloc 16)
    (.seq (.block saveRegisters)
      (.seq (.frame (.alloc frameBytes) (entryBody H1 H256 name check) (.free frameBytes)) (.block restoreRegisters)))
    (.free 16)
end VG.Impl.Dsa.X86.Generation
