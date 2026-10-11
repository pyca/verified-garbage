module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZR
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZTo
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx
public import VerifiedGarbage.Impl.Aes.X86_64.VaesZH

/-!
# Prepared AVX-512 GCM with AES keys cached across batches

`encR` also takes the `r` blocks (1 to 15) after the last group of 16, so
that `vg_aes_gcm_encrypt_blocks` need not call `vg_aes_ctr32` and
`vg_ghash` for them (`rem`). After the loops, the last group is still to
hash and `r9 = 16 + r`. The counter after the last block is stored first,
and `rax` pointed at the powers of the last `r` blocks, `H'ʳ` … `H'`, at
`scratch + 256 - 16 r` (`remSetup`). Then the keystream of the `r` blocks,
`4 ⌈r / 4⌉` counters encrypted in the lanes of `zmm3` … (`ksBatch`), is
computed while the last group is hashed between its rounds, as in a body,
and stored to `scratch + 768`. Each of the `r` blocks is then encrypted
with its keystream and its product with its power added to the lane 0
products (`remBody`, with `Y` added to the first block, then cleared), which
are reduced once (`StitchAvx.reduceHash`).
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.StitchZH
open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Aes.X86_64.VaesZ (ctrsZ xorDataZ)
open VG.Impl.Gcm.X86_64.StitchZ (gq gq48 lastG adv)
open VG.Impl.Gcm.X86_64.StitchZR (setupP powP48)
open VG.Impl.Gcm.X86_64.StitchZTo (atIx)

def batch (j : Nat) (g : Nat → List Instr) : Prog isa :=
  .seq (.block (ctrsZ .xmm14 .xmm0 .xmm15 aregs))
    (.seq (Aes.X86_64.VaesZH.aes aregs g) (.block (xorDataZ .xmm13 .rdx aregs j)))

def first : Prog isa := batch 0 fun _ => []

def body : Prog isa :=
  .seq (batch 4 gq) (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 32)])

def body48 : Prog isa :=
  .seq (batch 12 (gq48 0)) (.seq (batch 16 (gq48 1)) (.seq (batch 20 (gq48 2))
    (.block [.alu .add .rdx (.imm 768), .alu .sub .r9 (.imm 48), .alu .cmp .r9 (.imm 96)])))

def dbody : Prog isa :=
  .seq (batch 0 gq) (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 16)])

def dbody48 : Prog isa :=
  .seq (batch 0 (gq48 0)) (.seq (batch 4 (gq48 1)) (.seq (batch 8 (gq48 2))
    (.block [.alu .add .rdx (.imm 768), .alu .sub .r9 (.imm 48), .alu .cmp .r9 (.imm 48)])))

def bigP : Prog isa :=
  .seq (.block powP48) (.seq (batch 4 fun _ => []) (.seq (batch 8 fun _ => [])
    (.seq (.loop body48 .ae) (.block (.vmovdqu32Load .xmm1 (at_ .r11 832) :: (lastG ++ adv ++ lastG ++ adv))))))

def bigDP : Prog isa :=
  .seq (.block powP48) (.seq (.loop dbody48 .ae) (.block [.vmovdqu32Load .xmm1 (at_ .r11 832)]))

def enc : Prog isa :=
  .seq (.seq (.block setupP) Aes.X86_64.VaesZH.loadKeys)
    (.seq first
      (.seq (.block [.alu .cmp .r9 (.imm 256)])
        (.seq (.ite .b (.block []) bigP)
          (.seq (.block [.alu .cmp .r9 (.imm 32)])
            (.seq (.ite .b (.block []) (.loop body .ae))
              (.block (storeCtr ++ lastG ++ storeY)))))))

/-! ## The blocks after the last group -/

/-- The counter after the last of the `r = r9 - 16` blocks, stored; `r10 =
16 r`, and `rax` pointed at the powers `H'ʳ` … `H'`. -/
def remSetup : List Instr :=
  [.mov .r10 (.reg .r9), .alu .sub .r10 (.imm 16), .vop (.vmovq .xmm13 .r10),
   .vop (.vbin .vpaddd .l128 .xmm13 .xmm14 .xmm13), .vop (.vbin .vpshufb .l128 .xmm13 .xmm13 .xmm0),
   .vmovdquStore .l128 (at_ .rax 0) .xmm13,
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .mov .rax (.reg .r11), .alu .add .rax (.imm 256), .alu .sub .rax (.reg .r10)]

/-- Each register of `rs` stored to `scratch + 768 + 64 i`. -/
def ksStores : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, i => .vmovdqu32Store (at_ .r11 (768 + 64 * i)) b :: ksStores bs (i + 1)

/-- The keystream of `4 k` blocks, stored to `scratch + 768`, with the
instructions `g j` after round `j`. -/
def ksBatch (k : Nat) (g : Nat → List Instr) : Prog isa :=
  .seq (.block (ctrsZ .xmm14 .xmm0 .xmm15 (aregs.take k)))
    (.seq (Aes.X86_64.VaesZH.aes (aregs.take k) g) (.block (ksStores (aregs.take k) 0)))

/-- The keystream of `4 ⌈r / 4⌉` blocks, from `r10 = 16 r`, while the group
at `rdx` is hashed. -/
def ksSel : Prog isa :=
  .seq (.block [.alu .cmp .r10 (.imm 65)])
    (.ite .b (ksBatch 1 gq)
      (.seq (.block [.alu .cmp .r10 (.imm 129)])
        (.ite .b (ksBatch 2 gq)
          (.seq (.block [.alu .cmp .r10 (.imm 193)]) (.ite .b (ksBatch 3 gq) (ksBatch 4 gq))))))

/-- Block `r10 / 16` of the last `r`, read at `src + r10`: its keystream from
`scratch + 768`, the ciphertext written to `rdx + r10`, and its product with
its power (at `rax + r10`) added to those in the lower lanes of `xmm8` …
`xmm10` (`StitchAvx.acc`), with `Y` added to it (then cleared, for the next
blocks). -/
def remBody (src : Reg) : List Instr :=
  ([.vmovdquLoad .l128 .xmm13 (atIx src .r10 0), .vmovdquLoad .l128 .xmm12 (atIx .r11 .r10 768),
   .vop (.vbin .vpxor .l128 .xmm13 .xmm13 .xmm12), .vmovdquStore .l128 (atIx .rdx .r10 0) .xmm13,
   .vop (.vbin .vpshufb .l128 .xmm13 .xmm13 .xmm0), .vop (.vbin .vpxor .l128 .xmm13 .xmm13 .xmm2),
   .vop (.vbin .vpxor .l128 .xmm2 .xmm2 .xmm2), .vmovdquLoad .l128 .xmm12 (atIx .rax .r10 0)] : List Instr) ++
  StitchAvx.acc .xmm13 .xmm12

/-- The next block, and whether it is the last. -/
def remNext : List Instr := [.alu .add .r10 (.imm 16), .alu .sub .r9 (.imm 1), .alu .cmp .r9 (.imm 16)]

/-- The `r9 - 16` blocks after the last group, the last group hashed, and
`Y` stored; the blocks are read at `src` (`pre` points it at them once `rdx`
does). -/
def remWith (pre : List Instr) (src : Reg) : Prog isa :=
  .seq (.block remSetup)
    (.seq ksSel
      (.seq (.block (([.alu .add .rdx (.imm 256), .mov32 .r10 (.imm 0)] : List Instr) ++ pre ++ StitchAvx.zero))
        (.seq (.loop (.block (remBody src ++ remNext)) .ne) (.block (StitchAvx.reduceHash ++ storeY)))))

def rem : Prog isa := remWith [] .rdx

/-- The end of `encR`: the last group, and the blocks after it if any. -/
def tailR (r : Prog isa) : Prog isa :=
  .seq (.block [.alu .cmp .r9 (.imm 16)]) (.ite .e (.block (storeCtr ++ lastG ++ storeY)) r)

/-- `enc`, for any number of blocks from 16 on. -/
def encR : Prog isa :=
  .seq (.seq (.block setupP) Aes.X86_64.VaesZH.loadKeys)
    (.seq first
      (.seq (.block [.alu .cmp .r9 (.imm 256)])
        (.seq (.ite .b (.block []) bigP)
          (.seq (.block [.alu .cmp .r9 (.imm 32)])
            (.seq (.ite .b (.block []) (.loop body .ae)) (tailR rem))))))

def dec : Prog isa :=
  .seq (.seq (.block setupP) Aes.X86_64.VaesZH.loadKeys)
    (.seq (.block [.alu .cmp .r9 (.imm 256)])
      (.seq (.ite .b (.block []) bigDP)
        (.seq (.block [.alu .cmp .r9 (.imm 16)])
          (.seq (.ite .b (.block []) (.loop dbody .ae))
            (.block (storeCtr ++ storeY))))))

end VG.Impl.Gcm.X86_64.StitchZH
