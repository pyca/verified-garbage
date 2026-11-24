module
public import VerifiedGarbage.Impl.AesGcm.X86_64.Fn

/-! Contiguous AES-GCM seal with separate source and destination registers.
Every payload instruction also accepts identical buffers. -/

@[expose] public section
namespace VG.Impl.AesGcm.X86_64.Contiguous
open VG.X86_64
def src := at_ .rsp 8
def regs (r : Reg) : List Instr :=
  [.mov r (.mem src), .alu .add r (.mem (at_ .r15 tlenO)), .alu .sub r (.mem (at_ .r15 lenO))]
def call (f : Fn) : Prog isa := .call f.name f.code
def fusedArgs : List Instr :=
  ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++ ptr .rdx .r14 48 ++
    ptr .rcx .r14 16 ++ [.mov .r8 (.mem src), .mov .r9 (.reg .rax), .mov .r10 (.mem (at_ .r15 dataO))] ++ ptr .rax .r15 bScrO

def fused (f : Fn) : Prog isa :=
  .seq (.block fusedArgs) (.frame (.push [.rax]) (call f) (.pop .rax 1))
def ctrArgs : List Instr :=
  ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++ ptr .rdx .r14 48 ++
    [.mov .rcx (.mem src), .mov .r8 (.reg .rax), .mov .r11 (.mem (at_ .r15 dataO))] ++ ptr .r9 .r15 bScrO

def hashArgs : List Instr :=
  ptr .rdi .r13 240 ++ ptr .rsi .r14 16 ++ [.mov .rdx (.mem (at_ .r15 dataO)),
    .mov .rcx (.mem (at_ .r15 lenO)), .shift .shr .rcx 4] ++ ptr .r8 .r15 bScrO

def separate (ctr gh : Fn) : Prog isa :=
  .seq (.block ctrArgs) (.seq (call ctr) (.seq (.block hashArgs) (call gh)))

def bulk (kernel : Prog isa) : Prog isa :=
  .seq (.block [.mov .rax (.mem (at_ .r15 lenO)), .store (at_ .r15 tlenO) .rax,
    .shift .shr .rax 4, .alu .test .rax (.reg .rax)])
    (.ite .e (.block []) (.seq kernel (.block [.mov .rax (.mem (at_ .r15 lenO)), .mov .rcx (.reg .rax),
        .alu .and .rcx (imm 15), .store (at_ .r15 lenO) .rcx, .alu .sub .rax (.reg .rcx),
        .alu .add .rax (.mem (at_ .r15 dataO)), .store (at_ .r15 dataO) .rax])))
def finishVec (prepared wide : Bool) : Prog isa :=
  .seq (.block (if prepared then Short.finPowP else Short.finPow))
  (.seq (if wide then Short.finKs else Short.finKsA)
  (.seq (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .test .rax (.reg .rax)])
    (.ite .e (.block (Short.finLens ++ Short.finGh1 ++ Short.tagK 0))
      (.seq (.block (Short.finTextArgs ++ regs .rbx))
        (.seq (Short.xorText true .rbx) (.block (Short.finLens ++ Short.finGh2 ++ Short.tagK 0)))))))
def finishScalar (c : Callees) : Prog isa :=
 .seq (.block (regs .rbx ++ [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))]))
  (.seq (cryptTailG c true) (oneTag c 0))
def boundedArgs : List Instr :=
  [.mov .rbx (.mem src), .mov .r10 (.mem (at_ .r15 lenO)), .mov .r11 (.reg .rbx)]

def bounded : Prog isa :=
  .seq (.block boundedArgs)
    (call Short.bounded)
def one (c : Callees) (vec wide prepared : Bool) (kernel : Prog isa) : Prog isa :=
 let aad := if prepared && vec then .seq (Fast.cond (!wide)) (.ite .e (oneAad c) Fast.aad) else oneAad c
 let long := .seq aad (.seq (bulk kernel) (if vec then finishVec prepared wide else finishScalar c))
 let body := if prepared && wide then .seq Short.cond (.ite .e long bounded) else long
 Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (.seq (.block (oneEntry 40 16 24))
  (.seq body (.seq (.block (tagOut (at_ .rsp 32))) (.block restore))))

end VG.Impl.AesGcm.X86_64.Contiguous
