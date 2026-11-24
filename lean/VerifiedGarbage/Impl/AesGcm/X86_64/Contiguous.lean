module
public import VerifiedGarbage.Impl.Aes.X86_64.Callee
public import VerifiedGarbage.Impl.Gcm.X86_64.Flag
public import VerifiedGarbage.Impl.Scrub.X86_64
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
/-- The scalar bitsliced AES encryptor evaluates multiple lanes even for a
single block. Share those rounds between the tag mask and the tail mask. -/
def maskAES : Fn :=
  ⟨Impl.Aes.X86_64.Blocks.encScalar.name, Impl.Aes.X86_64.Blocks.encScalar.code⟩

def copyMask (fromOff toOff : Nat) : List Instr :=
  [.movdquLoad .xmm0 (at_ .r14 fromOff), .movdquStore (at_ .r15 toOff) .xmm0]

def maskArgs (count : Nat) : List Instr :=
  [.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] ++ ptr .rdx .r15 256 ++
    [.mov32 .rcx (imm count)] ++ ptr .r8 .r15 scrO

def mixMasks : List Instr :=
  [.movdquLoad .xmm0 (at_ .r15 256), .movdquLoad .xmm1 (at_ .r14 16),
    .xop (.bin .pxor .xmm0 .xmm1), .movdquStore (at_ .r15 0) .xmm0]

def makeMasks (enc : Fn) : Prog isa :=
  .seq (.block (copyMask 0 256 ++ copyMask 48 272 ++ maskArgs 2)) (call enc)

def maskXor : Prog isa :=
  .seq (.block [.alu .test .rbp (.reg .rbp)]) (.ite .e (.block [])
    (.seq (.block ([.mov .rdi (.reg .r12), .mov .rcx (.reg .rbp)] ++ ptr .rsi .r15 272)) (xorLoopG true)))

def authReload : List Instr :=
  [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)]

def authLens : List Instr :=
  [.mov .rbx (.mem (at_ .r15 alenO)), .mov .rbp (.mem (at_ .r15 tlenO))]

def maskAuth (c : Callees) : Prog isa :=
  .seq (.block authReload) (.seq (absorbPad c 16) (.seq (.block authLens) (.seq (lens c 16) (.block mixMasks))))

def finishMasks (c : Callees) (enc : Fn) : Prog isa :=
  let args := regs .rbx ++ [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))]
  .seq (.block args) (.seq (makeMasks enc) (.seq maskXor (maskAuth c)))

def finishScalar (c : Callees) : Prog isa :=
 .seq (.block (regs .rbx ++ [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))]))
  (.seq (cryptTailG c true) (oneTag c 0))

/-- The branch depends only on the number of bytes left after the bulk loop. -/
def maskChoice (f g : Prog isa) : Prog isa :=
  .seq (.block [.mov .rax (.mem (at_ .r15 lenO)),.alu .test .rax (.reg .rax)]) (.ite .e f g)

/-- The completed bulk loop has already authenticated the aligned record. -/
def oneMask (enc : Fn) : Prog isa :=
  .seq (.block (copyMask 0 256 ++ maskArgs 1)) (call enc)

def directEcbTag (c : Callees) (enc : Fn) : Prog isa :=
  .seq (lens c 16) (.seq (oneMask enc) (.block mixMasks))

def alignedTag (c : Callees) (enc : Fn) : Prog isa := .seq (.block authLens) (directEcbTag c enc)

def maskFinish (c : Callees) (enc : Fn) : Prog isa :=
  maskChoice (alignedTag c enc) (finishMasks c enc)

def maskIndex (base index : Reg) (disp : Nat := 0) : MemOp :=
  {base, index := some index, disp := Int.ofNat disp}

def startMasks : List Instr :=
  [.movdquLoad .xmm0 (at_ .r14 0), .movdquStore (at_ .r15 256) .xmm0,
   .mov32 .r11 (.mem (at_ .r14 12)), .bswap32 .r11, .mov32 .r10 (imm 0),
   .mov .rbp (.mem (at_ .r15 lenO)), .store (at_ .r15 tlenO) .rbp]

def packOne : List Instr :=
  [.movdquStore (maskIndex .r15 .r10 272) .xmm0, .alu32 .add .r11 (imm 1),
   .mov32 .rax (.reg .r11), .bswap32 .rax, .store32 (maskIndex .r15 .r10 284) .rax]

def bumpMask : List Instr := [.alu .add .r10 (imm 16), .alu .cmp .r10 (.reg .rbp)]

def batchAESArgs : List Instr :=
  ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++
  ptr .rdx .r15 256 ++ [.mov .rcx (.reg .rbp),.shift .shr .rcx 4,.alu .add .rcx (imm 1)] ++ ptr .r8 .r15 scrO

def maskPtrs : List Instr :=
  [.mov .rdi (.mem (at_ .rsp 8)), .mov .rsi (.mem (at_ .r15 dataO)), .mov32 .r10 (imm 0)]

def xorOne : List Instr :=
  [.movdquLoad .xmm0 (maskIndex .rdi .r10), .movdquLoad .xmm1 (maskIndex .r15 .r10 272),
   .xop (.bin .pxor .xmm0 .xmm1), .movdquStore (maskIndex .rsi .r10) .xmm0]

def batchKeys (enc : Fn) : Prog isa :=
  .seq (.block startMasks) (.seq (.loop (.block (packOne++bumpMask)) .ne)
    (.seq (.block batchAESArgs) (call enc)))

def batchText : Prog isa := .seq (.block maskPtrs) (.loop (.block (xorOne++bumpMask)) .ne)

def batchAuth (c : Callees) : Prog isa :=
  .seq (.block hashArgs) (.seq (call c.gh) (.seq (.block authLens) (.seq (lens c 16) (.block mixMasks))))

def batchMasks (c : Callees) (enc : Fn) : Prog isa := .seq (batchKeys enc) (.seq batchText (batchAuth c))

/-- Rotating the byte count minus one block moves any partial byte count above
the bound. Batch up to seven payload counters with J0 in at most two four-block AES groups. -/
def chooseBatch (bounded ordinary : Prog isa) : Prog isa :=
  .seq (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .sub .rax (imm 16), .shift .ror .rax 4,
    .alu .cmp .rax (imm 7)]) (.ite .b bounded ordinary)

def softwareBody (c : Callees) (ctr enc : Fn) : Prog isa :=
  .seq (oneAad c) (chooseBatch (batchMasks c enc) (.seq (bulk (separate ctr c.gh)) (maskFinish c enc)))

/-- The AES-NI/PCLMUL profile hashes the complete ciphertext once both the
whole and partial blocks have reached their destination. -/
def deferredBody (c : Callees) (ctr : Fn) : Prog isa :=
  let crypt := bulk (.seq (.block ctrArgs) (call ctr))
  let tail := regs .rbx ++ [.mov .r12 (.mem (at_ .r15 dataO)),.mov .rbp (.mem (at_ .r15 lenO))]
  let full := [.mov .r12 (.mem (at_ .rsp 16)),.mov .rbp (.mem (at_ .r15 tlenO)),.mov32 .rbx (imm 0)]
  .seq (oneAad c) (.seq crypt (.seq (.block tail) (.seq (cryptTailG c true)
    (.seq (.block full) (tagCiphertext c 0)))))

def boundedArgs : List Instr :=
  [.mov .rbx (.mem src), .mov .r10 (.mem (at_ .r15 lenO)), .mov .r11 (.reg .rbx)]

def bounded : Prog isa :=
  .seq (.block boundedArgs)
    (call Short.bounded)
def aad (c : Callees) (vec wide prepared : Bool) : Prog isa :=
  if prepared && vec then .seq (Fast.cond (!wide)) (.ite .e (oneAad c) Fast.aad) else oneAad c

def body (c : Callees) (vec wide prepared : Bool) (kernel : Prog isa) : Prog isa :=
  let long := .seq (aad c vec wide prepared) (.seq (bulk kernel) (if vec then finishVec prepared wide else finishScalar c))
  if prepared && wide then .seq Short.cond (.ite .e long bounded) else long

def core (record : Prog isa) : Prog isa :=
  .seq (.block (oneEntry 40 16 24)) (.seq record (.seq (.block (tagOut (at_ .rsp 32))) (.block restore)))

def framed (record : Prog isa) : Prog isa :=
  Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (core record)

def one (c : Callees) (vec wide prepared : Bool) (kernel : Prog isa) : Prog isa :=
  framed (body c vec wide prepared kernel)

/-- A preallocated record using bitsliced AES for both payload and tag masks. -/
def preparedMasks (level : Impl.Scrub.X86_64.VecLevel) (c : Callees) (ctr : Fn) : Prog isa :=
  Impl.Scrub.X86_64.scrubAll level 0 2640 (framed (softwareBody c ctr maskAES))

/-- One entry per CPU variant. The prepared flag selects whether the key
already holds enough powers of the hash subkey. Buffer layout has no effect
on this choice. -/
def selected (defer wide : Bool) (threshold : Nat)
    (c : Callees) (ctr : Fn) (blocks : Option Fn) : Prog isa :=
  let plain := if defer then framed (deferredBody c ctr) else
    one c blocks.isSome wide false (separate ctr c.gh)
  match blocks with
    | some b => Impl.Gcm.X86_64.Flag.onFlag threshold (one c true wide true (fused b)) plain
    | none => plain

def prepared (level : Impl.Scrub.X86_64.VecLevel) (defer wide : Bool) (threshold : Nat)
    (c : Callees) (ctr : Fn) (blocks : Option Fn) : Prog isa :=
  Impl.Scrub.X86_64.scrubAll level 0 2640 (selected defer wide threshold c ctr blocks)

end VG.Impl.AesGcm.X86_64.Contiguous
