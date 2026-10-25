module

public import VerifiedGarbage.Impl.Ffdh.VettedGroups
public import VerifiedGarbage.Impl.Ffdh.X86.Domain
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Encode

/-! Exact standard-domain recognition on i686. The prefix saves nonvolatile
registers in the existing scratch header. Only static-address formation uses
four stack bytes, within the original validator's 172-byte reservation. -/

@[expose] public section
namespace VG.Impl.Ffdh.X86.VettedValidation
open VG VG.X86 VG.Impl.Ffdh.VettedGroups

def tableSym : String := "VG_FFDH_VETTED_GROUPS_X86"
def tableConsts : List (String × List (BitVec 64)) := [(tableSym, tableWords)]
def saved : List (Reg × Nat) := [(.ebp, 36), (.esi, 40), (.edi, 44), (.ebx, 32)]
def entry : List Instr := VG.Impl.Ffdh.X86.entry VG.Impl.Ffdh.X86.CheckDomain.args ++
  [.mov .ebx (.reg .edi)]

def tableAddress : Prog isa := .frame (.symPush .eax tableSym) (.block []) (.pop .ecx 1)
def saveTable : List Instr := [.store ⟨.ebx, 16⟩ .eax]
def header (g : Group) : List Instr :=
  [.mov .eax (.mem ⟨.esp, 12⟩), .alu .cmp .eax (.imm (BitVec.ofNat 32 g.len))]
def compareArgs (offset : Nat) : List Instr :=
  [.mov .esi (.mem ⟨.esp, 4⟩), .mov .ecx (.mem ⟨.esp, 8⟩),
    .mov .edi (.mem ⟨.ebx, 16⟩), .alu .add .edi (.imm (BitVec.ofNat 32 (offset + 8)))]
def record (g : Group) (offset : Nat) : Prog isa :=
  .seq (.block (header g)) (.seq
    (.ite .e (.seq (.block (compareArgs offset)) VG.Impl.RsaPkcs1Sig.X86.compare)
      (.block [.mov .ebp (.imm 1)])) (.block [.alu .test .ebp (.reg .ebp)]))
def scan : List Group → Nat → Prog isa
  | [], _ => .block [.mov .eax (.imm 0)]
  | g :: gs, offset => .seq (record g offset)
    (.ite .e (.block [.mov .eax (.imm (BitVec.ofNat 32 g.bits))]) (scan gs (offset + 8 + 3 * g.len)))
def restore : List Instr := saved.map (fun p => .mov p.1 (.mem ⟨.ebx, p.2⟩))
def setup : Prog isa := .seq (.block entry) (.seq tableAddress (.block saveTable))
def recognize : Prog isa := .seq setup (.seq (scan groups 0) (.block restore))
def code : Prog isa := .seq recognize (.seq (.block [.alu .test .eax (.reg .eax)])
  (.ite .ne (.block [.mov .eax (.imm 1)]) VG.Impl.Ffdh.X86.CheckDomain.code))

end VG.Impl.Ffdh.X86.VettedValidation
