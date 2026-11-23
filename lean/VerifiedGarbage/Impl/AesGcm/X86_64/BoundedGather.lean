module
public import VerifiedGarbage.Impl.AesGcm.X86_64.BoundedSeal
public import VerifiedGarbage.Impl.AesGcm.X86_64.DirectGather

/-! Feed up to two gather descriptors to the bounded seal; longer scatter lists use the streaming pieces. -/
@[expose] public section
namespace VG.Impl.AesGcm.X86_64.DirectGather
open VG.X86_64

def descriptorHead : List Instr := [.mov .rax (.mem (at_ .rsp 8))]
def descriptorData : List Instr :=
  [.mov .rbx (.mem (at_ .rax 0)), .mov .r10 (.mem (at_ .rax 8)),
   .mov .rcx (.mem (at_ .rsp 16)),.alu .cmp .rcx (imm 2)]

def gatherArgs : Prog isa := .seq (.block descriptorHead) (.seq (.block descriptorData)
  (.ite .e (.block [.mov .r11 (.mem (at_ .rax 16))]) (.block [.mov .r11 (.reg .rbx)])))

def boundedGather : Prog isa := .seq gatherArgs (.call Short.bounded.name Short.bounded.code)

def countTest : List Instr := [.mov .rax (.mem (at_ .rsp 16)),.alu .sub .rax (imm 1),
  .alu .cmp .rax (imm 2),.mov32 .rax (imm 0),.mov32 .rcx (imm 1),.cmov .b .rax (.reg .rcx),
  .alu .test .rax (.reg .rax)]

def withBounded (fallback : Prog isa) : Prog isa :=
  .seq (.seq Short.cond (.ite .e (.block []) (.block countTest))) (.ite .e fallback boundedGather)

def preparedBounded (c : Callees) (ctr toFn : Fn) : Prog isa :=
  framed (dispatch (withBounded (quick toFn)) (withBounded (general c ctr (some toFn))))

end VG.Impl.AesGcm.X86_64.DirectGather
