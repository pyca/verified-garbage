module

public import VerifiedGarbage.Impl.Ffdh.VettedGroups
public import VerifiedGarbage.Impl.MlKem.X86_64.Common
import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Encode
public import VerifiedGarbage.TCB.X86_64.Isa

/-! Exact standard-domain recognition before the selected general validator.
Only two public argument words are saved in the existing scratch header. -/

@[expose] public section
namespace VG.Impl.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Impl.Ffdh.VettedGroups

def tableSym : String := "VG_FFDH_VETTED_GROUPS_X64"
def tableConsts : List (String × List (BitVec 64)) := [(tableSym, tableWords)]

def entry : List Instr := [.mov .r9 (.reg .rcx),
  .store (at_ .r9 128) .rsi, .store (at_ .r9 136) .rdx]

def header (g : Group) : List Instr := [.mov .rax (.mem (at_ .r9 136)),
  .alu .cmp .rax (.imm (BitVec.ofNat 32 g.len)), .mov32 .rdx (.imm 1)]

def compareArgs (offset : Nat) : List Instr := [.leaSym .rsi tableSym,
  .alu .add .rsi (.imm (BitVec.ofNat 32 (offset + 8))),
  .mov .rcx (.mem (at_ .r9 128))]

def record (g : Group) (offset : Nat) : Prog isa := .seq (.block (header g))
  (.seq (.ite .e (.seq (.block (compareArgs offset)) VG.Impl.RsaPkcs1Sig.X86_64.compare) (.block []))
    (.block [.alu .test .rdx (.reg .rdx)]))

def scan : List Group → Nat → Prog isa
  | [], _ => .block [.mov32 .rax (.imm 0)]
  | g :: gs, offset => .seq (record g offset)
    (.ite .e (.block [.mov32 .rax (.imm (BitVec.ofNat 32 g.bits))])
      (scan gs (offset + 8 + 3 * g.len)))

def restore : List Instr := [.mov .rsi (.mem (at_ .r9 128)),
  .mov .rdx (.mem (at_ .r9 136)), .mov .rcx (.reg .r9)]

def code (fallback : Prog isa) : Prog isa := .seq (.seq (.block entry) (scan groups 0))
  (.seq (.block [.alu .test .rax (.reg .rax)])
    (.ite .ne (.block [.mov32 .rax (.imm 1)]) (.seq (.block restore) fallback)))

end VG.Impl.Ffdh.X86_64.VettedValidation
