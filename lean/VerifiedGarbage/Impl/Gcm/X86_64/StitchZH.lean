module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZR
import VerifiedGarbage.Impl.Gcm.X86_64.StitchZTo
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx
public import VerifiedGarbage.Impl.Aes.X86_64.VaesZH

/-!
# Prepared AVX-512 GCM with AES keys cached across batches

`encR` also takes the `r` blocks (1 to 15) after the last group of 16, so
that `vg_aes_gcm_encrypt_blocks` need not call `vg_aes_ctr32` and
`vg_ghash` for them (`rem`). After the loops, the last group is still to
hash and `r9 = 16 + r`. The counter after the last block is stored first,
and `rax` pointed at the powers of the last `r` blocks, `H'ʳ` … `H'`, at
`scratch + 256 - 16 r` (`remSetup`). Then the `r` blocks are encrypted as one
more group of `⌈r / 4⌉` registers (`remG`): their counters are encrypted in
the lanes of `zmm3` … while the last group is hashed between their rounds,
as in a body; the data is added to them and the blocks stored, the last
register's through the mask of its blocks; and the registers are hashed
with their powers, the last one's loaded through the same mask so that its
other lanes add nothing, and the four lanes reduced once and added
(`StitchZ.fin`).

`decR` takes them as a masked group too (`remGD`), hashing the ciphertext
blocks between the rounds as they are in memory.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.StitchZH
open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Aes.X86_64.VaesZ (ctrsZ xorDataZ)
open VG.Impl.Gcm.X86_64.StitchZ (gq gq48 lastG adv fin)
open VG.Impl.Gcm.X86_64.StitchZR (setupP powP48)
open VG.Impl.Gcm.X86_64.StitchZTo (atIx)

/-! ## The counters of a batch

With a public block index (`be`), `r10d` holds the index of the batch's
first block, less one, in its top byte. Adding 16 there carries exactly when
the low byte of the sixteen indices from the batch's on may wrap around; if it
does not, the counter blocks are the first one byte-reversed (`vpshufb`) and
then 4, 8 and 12 more in its last byte, a `vpaddd` of `0x04` in the top byte
of each lane (`fastCtrs`), the constant at `scratch + 896`; the counters
advance by 16, at `scratch + 912`. Otherwise, and without an index, each
register's counters are byte-reversed (`ctrsZ`). -/

/-- The counter blocks of a batch whose low bytes do not wrap. -/
def fastCtrs : List Instr :=
  [.vbroadcasti32x4 .xmm13 (at_ .r11 896), .zop (.zbin .vpshufb .xmm3 .xmm14 .xmm0),
   .zop (.zbin .vpaddd .xmm4 .xmm3 .xmm13), .zop (.zbin .vpaddd .xmm5 .xmm4 .xmm13),
   .zop (.zbin .vpaddd .xmm6 .xmm5 .xmm13), .vbroadcasti32x4 .xmm13 (at_ .r11 912),
   .zop (.zbin .vpaddd .xmm14 .xmm14 .xmm13)]

/-- The counter blocks of a batch, through `fastCtrs` when the block index is
public (`be`) and the low bytes do not wrap. -/
def ctrs (be : Bool) : Prog isa :=
  if be then
    .seq (.block [.alu32 .add .r10 (.imm 0x10000000)])
      (.ite .ae (.block fastCtrs) (.block (ctrsZ .xmm14 .xmm0 .xmm15 aregs)))
  else .block (ctrsZ .xmm14 .xmm0 .xmm15 aregs)

/-- The constants of `fastCtrs` stored, and `r10d` set from the block index
at `[rsp + off]` (`r10` is the scratch register). -/
def beSetup (off : Nat) : List Instr :=
  [.movImm64 .r10 0x0400000000000000, .vop (.vmovq .xmm13 .r10),
   .vop (.vshift .pslldq .l128 .xmm13 .xmm13 8), .vmovdquStore .l128 (at_ .r11 896) .xmm13,
   .movImm64 .r10 16, .vop (.vmovq .xmm13 .r10), .vmovdquStore .l128 (at_ .r11 912) .xmm13,
   .mov32 .r10 (.mem (at_ .rsp off)), .alu32 .sub .r10 (.imm 1), .shift32 .shl .r10 24]

def batch (j : Nat) (g : Nat → List Instr) (be : Bool := false) : Prog isa :=
  .seq (ctrs be)
    (.seq (Aes.X86_64.VaesZH.aes aregs g) (.block (xorDataZ .xmm13 .rdx aregs j)))

def first : Prog isa := batch 0 fun _ => []

def body : Prog isa :=
  .seq (batch 4 gq) (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 32)])

def body48 : Prog isa :=
  .seq (batch 12 (gq48 0)) (.seq (batch 16 (gq48 1)) (.seq (batch 20 (gq48 2))
    (.block [.alu .add .rdx (.imm 768), .alu .sub .r9 (.imm 48), .alu .cmp .r9 (.imm 96)])))

def dbody (be : Bool := false) : Prog isa :=
  .seq (batch 0 gq be) (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 16)])

def dbody48 (be : Bool := false) : Prog isa :=
  .seq (batch 0 (gq48 0) be) (.seq (batch 4 (gq48 1) be) (.seq (batch 8 (gq48 2) be)
    (.block [.alu .add .rdx (.imm 768), .alu .sub .r9 (.imm 48), .alu .cmp .r9 (.imm 48)])))

def bigP : Prog isa :=
  .seq (.block powP48) (.seq (batch 4 fun _ => []) (.seq (batch 8 fun _ => [])
    (.seq (.loop body48 .ae) (.block (.vmovdqu32Load .xmm1 (at_ .r11 832) :: (lastG ++ adv ++ lastG ++ adv))))))

def bigDP (be : Bool := false) : Prog isa :=
  .seq (.block powP48) (.seq (.loop (dbody48 be) .ae) (.block [.vmovdqu32Load .xmm1 (at_ .r11 832)]))

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

/-- `remBody` for decryption: block `r10 / 16` of the last `r`, read at
`src + r10`, is hashed as it is read (byte-reversed, with `Y` added, times its
power at `rax + r10`), and its keystream from `scratch + 768` added to it in
`xmm12`, stored to `rdx + r10`. -/
def remBodyD (src : Reg) : List Instr :=
  ([.vmovdquLoad .l128 .xmm13 (atIx src .r10 0), .vmovdquLoad .l128 .xmm12 (atIx .r11 .r10 768),
   .vop (.vbin .vpxor .l128 .xmm12 .xmm12 .xmm13), .vmovdquStore .l128 (atIx .rdx .r10 0) .xmm12,
   .vop (.vbin .vpshufb .l128 .xmm13 .xmm13 .xmm0), .vop (.vbin .vpxor .l128 .xmm13 .xmm13 .xmm2),
   .vop (.vbin .vpxor .l128 .xmm2 .xmm2 .xmm2), .vmovdquLoad .l128 .xmm12 (atIx .rax .r10 0)] : List Instr) ++
  StitchAvx.acc .xmm13 .xmm12

/-! ## The blocks after the last group, as a masked group

`remG` encrypts the `r` blocks after the last group as one more group of
`k = ⌈r / 4⌉` registers, without storing their keystream: while the last
group is hashed between their rounds (`gq`), as in a body, their
counters are encrypted in the lanes of `zmm3` …, the data added to them
and stored, the last register's through the mask of its blocks
(`remMaskG`, in `r10`) (`xorG`), and the `k` registers hashed with the
powers `H'ʳ` … `H'` at `rax`, the last register's loaded through the same
mask, so that its lanes after the `r` blocks add nothing (`hashG`). -/

/-- The mask of the last register's blocks, `r mod 4` of them (four if
`r` is a multiple of four), in `r10`, from `r9 = 16 + r`. -/
def remMaskG : Prog isa :=
  .seq (.block [.alu .test .r9 (.imm 1)])
    (.ite .e
      (.seq (.block [.alu .test .r9 (.imm 2)])
        (.ite .e (.block [.mov32 .r10 (.imm 255)]) (.block [.mov32 .r10 (.imm 15)])))
      (.seq (.block [.alu .test .r9 (.imm 2)])
        (.ite .e (.block [.mov32 .r10 (.imm 3)]) (.block [.mov32 .r10 (.imm 63)]))))

/-- The registers `rs`, from the `j`-th, XORed with the data at `src + 64 j`
… and stored to `rdx + 64 j` …; the last through the mask in `r10`. -/
def xorG (src : Reg) : List XReg → Nat → List Instr
  | [], _ => []
  | [b], j => [.kLoad .r10 .xmm13 (at_ src (64 * j)), .zop (.zbin .vpxord b b .xmm13),
      .kStore (at_ .rdx (64 * j)) .r10 b]
  | b :: bs, j => ([.vmovdqu32Load .xmm13 (at_ src (64 * j)), .zop (.zbin .vpxord b b .xmm13),
      .vmovdqu32Store (at_ .rdx (64 * j)) b] : List Instr) ++ xorG src bs (j + 1)

/-- The lane-wise products of register `b` byte-reversed (with `Y` added if
`j = 0`) with the powers in `zmm12`, written (`j = 0`) or added. -/
def hash1 (b : XReg) (j : Nat) : List Instr :=
  ([.zop (.zbin .vpshufb .xmm7 b .xmm0)] : List Instr) ++
    (if j = 0 then [.zop (.zbin .vpxord .xmm7 .xmm7 .xmm2)] else []) ++
    (if j = 0 then StitchZ.accInit .xmm7 .xmm12 else StitchZ.acc .xmm7 .xmm12)

/-- The registers `rs`, from the `j`-th, hashed with the powers at
`rax + 64 j` …; the last's through the mask in `r10`. -/
def hashG : List XReg → Nat → List Instr
  | [], _ => []
  | [b], j => .kLoad .r10 .xmm12 (at_ .rax (64 * j)) :: hash1 b j
  | b :: bs, j => (.vmovdqu32Load .xmm12 (at_ .rax (64 * j)) :: hash1 b j) ++ hashG bs (j + 1)

/-- The `r` blocks of a group of `k` registers, while `g` runs between
their rounds: their keystream, the data at `src` (`pre` points it at the
blocks once `rdx` does) added and stored, hashed, and the four lanes'
products reduced into `Y`. -/
def ksBatchG (k : Nat) (g : Nat → List Instr) (pre : List Instr) (src : Reg) : Prog isa :=
  .seq (.block (ctrsZ .xmm14 .xmm0 .xmm15 (aregs.take k)))
    (.seq (Aes.X86_64.VaesZH.aes (aregs.take k) g)
      (.seq (.block (.alu .add .rdx (.imm 256) :: pre))
        (.seq remMaskG (.block (xorG src (aregs.take k) 0 ++ hashG (aregs.take k) 0 ++ fin)))))

/-- `ksBatchG` of `⌈r / 4⌉` registers, from `r10 = 16 r`. -/
def ksSelG (pre : List Instr) (src : Reg) : Prog isa :=
  .seq (.block [.alu .cmp .r10 (.imm 65)])
    (.ite .b (ksBatchG 1 gq pre src)
      (.seq (.block [.alu .cmp .r10 (.imm 129)])
        (.ite .b (ksBatchG 2 gq pre src)
          (.seq (.block [.alu .cmp .r10 (.imm 193)])
            (.ite .b (ksBatchG 3 gq pre src) (ksBatchG 4 gq pre src))))))

/-- The `r9 - 16` blocks after the last group, the last group hashed, and
`Y` stored, as a masked group. -/
def remG (pre : List Instr) (src : Reg) : Prog isa :=
  .seq (.block remSetup) (.seq (ksSelG pre src) (.block storeY))

/-- The blocks after the last group, in place. -/
def rem : Prog isa := remG [] .rdx

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

/-! ## Decryption: the blocks after the last group, as a masked group

`remGD` decrypts the `r` blocks after the last group as one more group of
`k = ⌈r / 4⌉` registers: their counters are encrypted in the lanes of
`zmm3` … while the ciphertext blocks are hashed between the rounds as they
are in memory, as a body hashes a group (`gD`): register `i` of them,
byte-reversed, with `Y` added to the first block, times the powers at
`rax + 64 i`, the last register's blocks and powers loaded through the mask
of its blocks (`remMaskG`, in `r10`), so that its other lanes read nothing
and add nothing; the four lanes reduced after round 5. Then the ciphertext
is added to the keystream in the registers and stored (`xorG`). -/

/-- Load `i` of the GHASH of the `r` blocks: four powers and four blocks,
through the mask if `last`, the products written (`i = 0`, with `Y` added
to the first block) or added. -/
def ldGD (last : Bool) (i : Nat) : List Instr :=
  (if last then ([.kLoad .r10 .xmm12 (at_ .rax (64 * i)), .kLoad .r10 .xmm7 (at_ .rdx (64 * i))] : List Instr)
    else [.vmovdqu32Load .xmm12 (at_ .rax (64 * i)), .vmovdqu32Load .xmm7 (at_ .rdx (64 * i))]) ++
    ([.zop (.zbin .vpshufb .xmm7 .xmm7 .xmm0)] : List Instr) ++
    (if i = 0 then [.zop (.zbin .vpxord .xmm7 .xmm7 .xmm2)] else []) ++
    (if i = 0 then StitchZ.accInit .xmm7 .xmm12 else StitchZ.acc .xmm7 .xmm12)

/-- The GHASH work between the rounds of `k` registers: the loads after
rounds 1–`k`, the reduction after round 5. -/
def gD (k j : Nat) : List Instr :=
  if 1 ≤ j ∧ j ≤ k then ldGD (j == k) (j - 1) else if j = 5 then fin else []

/-- The `r` blocks at `rdx` as a group of `k` registers, hashed between
their rounds, and decrypted in place. -/
def ksBatchGD (k : Nat) : Prog isa :=
  .seq remMaskG
    (.seq (.block (ctrsZ .xmm14 .xmm0 .xmm15 (aregs.take k)))
      (.seq (Aes.X86_64.VaesZH.aes (aregs.take k) (gD k)) (.block (xorG .rdx (aregs.take k) 0))))

/-- `ksBatchGD` of `⌈r / 4⌉` registers, from `r10 = 16 r`. -/
def ksSelGD : Prog isa :=
  .seq (.block [.alu .cmp .r10 (.imm 65)])
    (.ite .b (ksBatchGD 1)
      (.seq (.block [.alu .cmp .r10 (.imm 129)])
        (.ite .b (ksBatchGD 2)
          (.seq (.block [.alu .cmp .r10 (.imm 193)]) (.ite .b (ksBatchGD 3) (ksBatchGD 4))))))

/-- The `r9 - 16` blocks at `rdx` after the last group, which the loop has
already hashed, hashed and decrypted as a masked group, and `Y` stored. -/
def remGD : Prog isa := .seq (.block remSetup) (.seq ksSelGD (.block storeY))

/-- The setup of `decR`: the powers and the AES keys loaded. -/
def decRHead : Prog isa := .seq (.block setupP) Aes.X86_64.VaesZH.loadKeys

/-- `decR` after its setup and the comparison with 256. -/
def decRTail (be : Bool := false) : Prog isa :=
  .seq (.ite .b (.block []) (bigDP be))
    (.seq (.block [.alu .cmp .r9 (.imm 16)])
      (.seq (.ite .b (.block []) (.loop (dbody be) .ae))
        (.seq (.block [.alu .test .r9 (.reg .r9)])
          (.ite .e (.block (storeCtr ++ storeY))
            (.seq (.block [.alu .add .r9 (.imm 16)]) remGD)))))

/-- What follows the load of the block index in `decR true`. -/
def decRBeRest : Prog isa :=
  .seq (.block [.alu32 .sub .r10 (.imm 1), .shift32 .shl .r10 24, .alu .cmp .r9 (.imm 256)]) (decRTail true)

/-- `dec`, for any number of blocks from 16 on: the `r9` blocks after the
last group, if any, by `remGD`. -/
def decR (be : Bool := false) : Prog isa :=
  .seq decRHead
    (.seq (.block ((if be then beSetup 16 else []) ++ [.alu .cmp .r9 (.imm 256)])) (decRTail be))

def dec : Prog isa :=
  .seq (.seq (.block setupP) Aes.X86_64.VaesZH.loadKeys)
    (.seq (.block [.alu .cmp .r9 (.imm 256)])
      (.seq (.ite .b (.block []) bigDP)
        (.seq (.block [.alu .cmp .r9 (.imm 16)])
          (.seq (.ite .b (.block []) (.loop dbody .ae))
            (.block (storeCtr ++ storeY))))))

end VG.Impl.Gcm.X86_64.StitchZH
