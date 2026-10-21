module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZR
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
open VG.Impl.Gcm.X86_64.Stitch (aregs storeY)
open VG.Impl.Gcm.X86_64.Slot (ctrsM storeCtr)
open VG.Impl.Aes.X86_64.VaesZ (xorDataZ)
open VG.Impl.Gcm.X86_64.StitchZ (gq gq48 lastG adv fin bigMinP bigMinPE)
open VG.Impl.Gcm.X86_64.StitchZR (setupP powP48)
open VG.Impl.Gcm.X86_64.StitchZTo (atIx)

def batch (j : Nat) (g : Nat → List Instr) : Prog isa :=
  .seq (.block (ctrsM aregs))
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

/-- `remSetup` for the loops with the counter blocks in the slot: the
counter after the last of the `r = r9 - 16` blocks stored from the slot
(`Slot.storeCtrAt`); `r10 = 16 r`, and `rax` pointed at the powers `H'ʳ` …
`H'`. -/
def remSetupM : List Instr :=
  Slot.storeCtrAt ++
  ([.mov .r10 (.reg .r9), .alu .sub .r10 (.imm 16),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .mov .rax (.reg .r11), .alu .add .rax (.imm 256), .alu .sub .rax (.reg .r10)] : List Instr)

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
  .seq (.block (Slot.loads (aregs.take k) 0))
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
  .seq (.block remSetupM) (.seq (ksSelG pre src) (.block storeY))

/-- The blocks after the last group, in place. -/
def rem : Prog isa := remG [] .rdx

/-- The end of `encR`: the last group, and the blocks after it if any. -/
def tailR (r : Prog isa) : Prog isa :=
  .seq (.block [.alu .cmp .r9 (.imm 16)]) (.ite .e (.block (storeCtr ++ lastG ++ storeY)) r)

/-- `enc`, for any number of blocks from 16 on. -/
def encR : Prog isa :=
  .seq (.seq (.block setupP) Aes.X86_64.VaesZH.loadKeys)
    (.seq first
      (.seq (.block [.alu .cmp .r9 (.imm bigMinPE)])
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
    (.seq (.block (Slot.loads (aregs.take k) 0))
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
def remGD : Prog isa := .seq (.block remSetupM) (.seq ksSelGD (.block storeY))

/-- `dec`, for any number of blocks from 16 on: the `r9` blocks after the
last group, if any, by `remGD`. -/
def decR : Prog isa :=
  .seq (.seq (.block setupP) Aes.X86_64.VaesZH.loadKeys)
    (.seq (.block [.alu .cmp .r9 (.imm bigMinP)])
      (.seq (.ite .b (.block []) bigDP)
        (.seq (.block [.alu .cmp .r9 (.imm 16)])
          (.seq (.ite .b (.block []) (.loop dbody .ae))
            (.seq (.block [.alu .test .r9 (.reg .r9)])
              (.ite .e (.block (storeCtr ++ storeY))
                (.seq (.block [.alu .add .r9 (.imm 16)]) remGD)))))))

def dec : Prog isa :=
  .seq (.seq (.block setupP) Aes.X86_64.VaesZH.loadKeys)
    (.seq (.block [.alu .cmp .r9 (.imm 256)])
      (.seq (.ite .b (.block []) bigDP)
        (.seq (.block [.alu .cmp .r9 (.imm 16)])
          (.seq (.ite .b (.block []) (.loop dbody .ae))
            (.block (storeCtr ++ storeY))))))

end VG.Impl.Gcm.X86_64.StitchZH
