module

public import VerifiedGarbage.Impl.Gcm.X86_64.Stitch
public import VerifiedGarbage.Impl.AesGcmSiv.X86_64

/-!
# AES-GCM-SIV's counter mode and POLYVAL, interleaved, with VAES and VPCLMULQDQ

The loop of `vg_aes_gcm_siv_open` for CPUs with VAES, VPCLMULQDQ and AVX2, on
groups of sixteen blocks, as AES-GCM's (`Impl/Gcm/X86_64/Stitch.lean`,
`Stitch.enc`): each group is deciphered (counter mode) while the previous
group's plaintext is hashed, and the last group's plaintext then alone.
POLYVAL is GHASH with the key `H · x` on blocks in the other byte order
(`Proof.GcmSiv.Polyval`), and GHASH's loads reverse each block's bytes into
the register form, so POLYVAL's loads are the data's 32 bytes as they are,
with no byte reversal (`ldR`). The counter block of RFC 8452 §4 increments
its first 32-bit word, little-endian: `vpaddd` on the block as it is
(`ctrsR`), so the counter pair needs no byte reversal either. `Y` and `H`
are kept in GHASH's order, as AES-GCM-SIV's other code keeps them.

Registers as in `Stitch`: `ymm0` the byte-reversal mask (for `H` and `Y`),
`ymm1` the reduction constant, `xmm2` `Y`, `ymm3`–`ymm6` eight blocks being
deciphered, `ymm7` two blocks being hashed, `ymm8`–`ymm11` the products and a
temporary, `ymm12` a pair of powers, `ymm13` a round key, `ymm14` the counter
pair and `ymm15` the counter increment (2 in each lane). `rdi` points to the
key schedule, `rsi` holds `rounds`, `r10` the last round key's address;
`rdx` points to the counter block at entry, then to the group being hashed,
and `rax` to the counter block; `rcx` to
`Y`, `r8` to `H`, `r11` to the powers' working space, `r9` counts the blocks.
-/

@[expose] public section

namespace VG.Impl.AesGcmSiv.X86_64Stitch

open VG.X86_64
open VG.Impl.Aes.X86_64.Vaes (aesK xorDataK)
open VG.Impl.Gcm.X86_64.Pclmul (at_ revMask poly hInv)
open VG.Impl.Gcm.X86_64.Vpclmul (powers powers16 zero acc reduce combine)
open VG.Impl.Gcm.X86_64.Stitch (aregs storesK pregs ordE gq)

/-- The counter blocks: each block register gets the two counters (`c`) as
they are, and both counters advance by two (`i`) in their first words. -/
def ctrsR (c i : XReg) : List XReg → List Instr
  | [] => []
  | b :: bs => ([.vop (.vmovdqa .l256 b c), .vop (.vbin .vpaddd .l256 c c i)] : List Instr) ++ ctrsR c i bs

/-- Blocks `2k` and `2k + 1` into the lanes of `ymm7` as they are (POLYVAL's
order is GHASH's reversed), with `Y` added to block 0, and their products
with the powers in `p`. -/
def ldR (k : Nat) (p : XReg) : List Instr :=
  ([.vmovdquLoad .l256 .xmm7 (at_ .rdx (32 * k))] : List Instr) ++
  (if k = 0 then [.vop (.vbin .vpxor .l256 .xmm7 .xmm7 .xmm2)] else []) ++ acc .xmm7 p

/-- The powers of the `k`-th load of a body, from the working space, then
that load. -/
def ghLoad (k : Nat) : List Instr := .vmovdquLoad .l256 .xmm12 (at_ .r11 (32 * k)) :: ldR k .xmm12

/-- `H'`–`H'¹⁶` from `H` at `r8`, as `Stitch.setupG` computes them from the
hash subkey. -/
def setupG : List Instr :=
  Gcm.X86_64.Pclmul.const .xmm0 revMask ++ Gcm.X86_64.Pclmul.const .xmm1 poly ++
  ([.movdquLoad .xmm7 (at_ .r8 0), .xop (.bin .pshufb .xmm7 .xmm0)] : List Instr) ++ hInv ++
  Gcm.X86_64.Pclmul.pows ++ powers ++ powers16

/-- `Y`, the counter pair (as it is), the increment, the last round key's
address, and the hashing pointer at the data (`r12`). -/
def setupC : List Instr :=
  [.vmovdquLoad .l128 .xmm2 (at_ .rcx 0), .vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
   .movImm64 .r10 1, .vop (.vmovq .xmm15 .r10),
   .vmovdquLoad .l128 .xmm14 (at_ .rdx 0),
   .vop (.vbin .vpaddd .l128 .xmm13 .xmm14 .xmm15), .vop (.vinserti128 .xmm14 .xmm14 .xmm13 1),
   .movImm64 .r10 2, .vop (.vmovq .xmm15 .r10), .vop (.vinserti128 .xmm15 .xmm15 .xmm15 1),
   .mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi),
   .mov .rax (.reg .rdx), .mov .rdx (.reg .r12)]

def setup : List Instr := setupG ++ storesK .r11 pregs 0 ++ setupC

/-- Eight blocks deciphered at `rdx + 32 j` (the data blocks `2j`…), the
POLYVAL loads `g i` after round `i`. -/
def batch (j : Nat) (g : Nat → List Instr) : Prog isa :=
  .seq (.block (ctrsR .xmm14 .xmm15 aregs))
    (.seq (aesK .xmm13 aregs g) (.block (xorDataK .xmm13 .rdx aregs j)))

/-- The POLYVAL loads between the rounds of a batch, as `Stitch.gq` places
`Stitch.ghLoad`s. -/
def gq (base : Nat) (fin : Bool) (j : Nat) : List Instr :=
  if 1 ≤ j ∧ j ≤ 4 then ghLoad (ordE (base + j - 1))
  else if fin ∧ j = 5 then reduce .xmm7 ++ combine else []

def gA : Nat → List Instr := gq 0 false

def gB : Nat → List Instr := gq 4 true

/-- The first group, deciphered only. -/
def first : Prog isa := .seq (batch 0 fun _ => []) (batch 4 fun _ => [])

/-- A group deciphered (at `rdx + 256`) and the previous one hashed (at
`rdx`). -/
def body : Prog isa :=
  .seq (.block zero)
    (.seq (batch 8 gA)
      (.seq (batch 12 gB)
        (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 32)])))

/-- The counter block stored, as it is. -/
def storeCtr : List Instr := [.vmovdquStore .l128 (at_ .rax 0) .xmm14]

/-- The last group hashed, at `rdx`. -/
def lastG : List Instr :=
  zero ++ (List.range 8).flatMap (fun i => ghLoad (ordE i)) ++ reduce .xmm7 ++ combine

/-- `Y` stored in GHASH's order, and the upper lanes cleared. -/
def storeY : List Instr :=
  [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0), .vmovdquStore .l128 (at_ .rcx 0) .xmm2, .vop .vzeroupper]

/-- `r9` (a multiple of 16, at least 16) blocks at `r12` deciphered and their
plaintext absorbed into `Y`. -/
def dec : Prog isa :=
  .seq (.block setup)
    (.seq first
      (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.seq (.ite .b (.block []) (.loop body .ae))
          (.block (storeCtr ++ lastG ++ storeY)))))

/-! ## `vg_aes_gcm_siv_open` with the interleaved loop -/

open VG.Impl.AesGcm.X86_64 (imm ptr Callees Fn)
open VG.Impl.AesGcmSiv.X86_64 (entry recv keys absorb lens tagIn tag tagOut cmp mask restore crypt polyval cryptChunk
  cryptTail okO tagO cmO yO hO akO skO scrO ghO roundsO aadO alenO dataO lenO bO zero16)

variable (c : Callees) (e : Fn) (wide : Bool)

/-! ## POLYVAL in registers, for short messages

POLYVAL's field element of a block is its 16 bytes as they are (`ldR`), so
a short message's POLYVAL takes one block at a time in registers: `Y ← (Y ⊕
X) · H` with `vg_ghash_vpclmul`'s product of a lane (`Vpclmul.acc`,
`reduce`) and `H' = H · x⁻¹`, which is the authentication key at `W + akO`
as it is (GHASH's key `H` is its product with `x`, `hkey`). `Y` starts at
zero in a register, and the lengths block is built in registers: loading
either from where it was just stored in two halves would wait for the
stores. The last bytes of the additional data and of the data go through
`W + bO`. -/

/-- `Y ← (Y ⊕ X) · H` in lane 0 of `ymm2`, `X` in `xmm7`, with
`vg_ghash_vpclmul`'s product of each lane (`Vpclmul.acc`, `reduce`). -/
def hmul : List Instr :=
  Gcm.X86_64.Vpclmul.zero ++ ([.vop (.vbin .vpxor .l256 .xmm7 .xmm7 .xmm2)] : List Instr) ++
  Gcm.X86_64.Vpclmul.acc .xmm7 .xmm3 ++ Gcm.X86_64.Vpclmul.reduce .xmm2

/-- `hmul` of the block at `rsi`, as it is. -/
def hstep : List Instr := ([.vmovdquLoad .l128 .xmm7 (at_ .rsi 0)] : List Instr) ++ hmul

/-- One block: `hstep`, `rsi` on, `rbx` down. -/
def hrBody : List Instr := hstep ++ ([.alu .add .rsi (imm 16), .alu .sub .rbx (imm 1)] : List Instr)

/-- The last `rbp` (1 to 15) bytes at `rsi`, padded with zeros at `W + bO`,
absorbed. -/
def htail : Prog isa :=
  .seq (.block (zero16 bO ++ ptr .rdi .r15 bO ++ ([.mov .rcx (.reg .rbp)] : List Instr)))
  (.seq Impl.AesGcm.X86_64.copyLoop (.block (ptr .rsi .r15 bO ++ hstep)))

/-- The `rbp` bytes at `r12`, padded with zeros to whole blocks, absorbed. -/
def habsorb : Prog isa :=
  .seq (.block [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .and .rbp (imm 15), .mov .rsi (.reg .r12),
      .alu .test .rbx (.reg .rbx)])
  (.seq (.ite .e (.block []) (.loop (.block hrBody) .ne))
  (.seq (.block [.alu .test .rbp (.reg .rbp)])
    (.ite .e (.block []) htail)))

/-- The constants, `H'` (the authentication key at `W + akO`) in `xmm3` and
`Y` (zero) in `xmm2`. -/
def hsetup : List Instr :=
  ([.vop .vzeroupper] : List Instr) ++ Gcm.X86_64.Pclmul.const .xmm0 revMask ++ Gcm.X86_64.Pclmul.const .xmm1 poly ++
  ([.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1), .vmovdquLoad .l128 .xmm3 (at_ .r15 akO),
    .vop (.vbin .vpxor .l128 .xmm2 .xmm2 .xmm2)] : List Instr)

/-- The lengths block, `le64(8 · aad_len) ‖ le64(8 · len)`, built in `xmm7`
and absorbed, and `Y` stored in GHASH's order. -/
def hlens : List Instr :=
  [.mov .rax (.mem (at_ .r15 alenO)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .vop (.vmovq .xmm5 .rax),
    .mov .rax (.mem (at_ .r15 lenO)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .vop (.vmovq .xmm6 .rax), .vop (.vbin .vpunpcklqdq .l128 .xmm7 .xmm5 .xmm6)] ++
  hmul ++
  ([.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0), .vmovdquStore .l128 (at_ .r15 yO) .xmm2, .vop .vzeroupper] :
    List Instr)

/-- POLYVAL of the additional data, the data and the lengths, in registers,
and the tag input. -/
def polyvalR : Prog isa :=
  .seq (.block (hsetup ++ ([.mov .r12 (.mem (Impl.AesGcm.X86_64.at_ .r15 aadO)),
      .mov .rbp (.mem (Impl.AesGcm.X86_64.at_ .r15 alenO))] : List Instr)))
  (.seq habsorb
  (.seq (.block [.mov .r12 (.mem (Impl.AesGcm.X86_64.at_ .r15 dataO)), .mov .rbp (.mem (Impl.AesGcm.X86_64.at_ .r15 lenO))])
  (.seq habsorb (.block (hlens ++ tagIn)))))

/-- The whole blocks of the additional data and the data together, against
10: below it, POLYVAL in registers (`polyvalR`), whose blocks wait for each
other, else `polyval`, whose call computes powers of `H` to take eight blocks
at once. -/
def hsmall : List Instr :=
  [.mov .rax (.mem (Impl.AesGcm.X86_64.at_ .r15 alenO)), .shift .shr .rax 4, .mov .rdx (.mem (Impl.AesGcm.X86_64.at_ .r15 lenO)),
    .shift .shr .rdx 4, .alu .add .rax (.reg .rdx), .alu .cmp .rax (imm 10)]

/-- POLYVAL and the tag input: in registers for short messages. -/
def polyvalS : Prog isa := .seq (.block hsmall) (.ite .b polyvalR (polyval c wide))


/-- The data from the 256-byte groups on (`r12`, its length `rbp`): its whole
blocks and its last bytes deciphered from the counter block at `W + cmO`. -/
def cryptRest : Prog isa :=
  .seq (.block [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)])
  (.seq (.ite .e (.block []) (.loop (cryptChunk e wide) .ne))
  (.seq (.block [.alu .test .rbp (.reg .rbp)])
    (.ite .e (.block []) (cryptTail c))))

/-- The data after its 256-byte groups: its address (`r12`) and length
(`rbp`). -/
def rest : List Instr :=
  [.mov .r12 (.mem (Impl.AesGcm.X86_64.at_ .r15 dataO)), .mov .rax (.mem (Impl.AesGcm.X86_64.at_ .r15 lenO)), .shift .shr .rax 8,
    .shift .shl .rax 8, .alu .add .r12 (.reg .rax), .mov .rbp (.mem (Impl.AesGcm.X86_64.at_ .r15 lenO)), .alu .and .rbp (imm 255)]

/-- With 256 bytes of data or more: POLYVAL of the additional data, then its
groups of sixteen blocks deciphered and absorbed by the interleaved loop, the
rest deciphered and absorbed as `open` does, the lengths and the tag input. -/
def stitched : Prog isa :=
  .seq (.block [.mov .rax (.mem (Impl.AesGcm.X86_64.at_ .r15 tagO)), .store (Impl.AesGcm.X86_64.at_ .r15 cmO) .rax, .mov .rax (.mem (Impl.AesGcm.X86_64.at_ .r15 (tagO + 8))),
      .movImm64 .rcx 0x8000000000000000, .alu .or .rax (.reg .rcx), .store (Impl.AesGcm.X86_64.at_ .r15 (cmO + 8)) .rax,
      .mov .r12 (.mem (Impl.AesGcm.X86_64.at_ .r15 aadO)), .mov .rbp (.mem (Impl.AesGcm.X86_64.at_ .r15 alenO))])
  (.seq (absorb c wide)
  (.seq (.block (ptr .rdi .r15 skO ++ ([.mov .rsi (.mem (Impl.AesGcm.X86_64.at_ .r15 roundsO))] : List Instr) ++ ptr .rdx .r15 cmO ++
      ptr .rcx .r15 yO ++ ptr .r8 .r15 hO ++ ptr .r11 .r15 scrO ++
      ([.mov .r12 (.mem (Impl.AesGcm.X86_64.at_ .r15 dataO)), .mov .r9 (.mem (Impl.AesGcm.X86_64.at_ .r15 lenO)), .shift .shr .r9 8,
        .alu .add .r9 (.reg .r9), .alu .add .r9 (.reg .r9), .alu .add .r9 (.reg .r9), .alu .add .r9 (.reg .r9)] :
        List Instr)))
  (.seq dec
  (.seq (.block rest)
  (.seq (cryptRest c e wide)
  (.seq (.block rest)
  (.seq (absorb c wide)
  (.seq (lens c) (.block tagIn)))))))))

/-- `vg_aes_gcm_siv_open`, with the interleaved loop from 256 bytes of data. -/
def «open» : Prog isa :=
  .seq (.block entry) (.seq (.block recv) (.seq (keys c e)
    (.seq (.block [.mov .rax (.mem (Impl.AesGcm.X86_64.at_ .r15 lenO)), .alu .cmp .rax (imm 256)])
    (.seq (.ite .b (.seq (crypt c e wide) (polyvalS c wide)) (stitched c e wide))
    (.seq (tag c bO)
    (.seq (.block cmp) (.seq mask (.block (([.mov .rax (.mem (Impl.AesGcm.X86_64.at_ .r15 okO))] : List Instr) ++ restore)))))))))


/-! ## `vg_aes_gcm_siv_seal` with loops for the 256-byte groups

Sealing needs POLYVAL of the plaintext before counter mode, so the groups are
absorbed in one loop (`hash`, the loads of `dec`'s with no rounds between
them) and enciphered in another (`ctr`, `dec`'s batches with nothing between
their rounds), each in registers, from 256 bytes of data on. -/

/-- `Y` from `rcx`, in GHASH's order, after the setup's mask. -/
def loadY : List Instr := [.vmovdquLoad .l128 .xmm2 (at_ .rcx 0), .vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0)]

/-- A group of sixteen blocks at `rdx` absorbed; `rdx` on, `r9` down. -/
def hbody : List Instr := lastG ++ ([.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16)] : List Instr)

/-- `r9` (a multiple of 16, at least 16) blocks at `rdx` absorbed into `Y` at
`rcx`, with the powers of `H` at `r8` in the working space at `r11`. -/
def hash : Prog isa :=
  .seq (.block (setupG ++ storesK .r11 pregs 0 ++ loadY)) (.seq (.loop (.block hbody) .ne) (.block storeY))

/-- The mask (in both lanes), the counter pair from the counter block at `rdx`, the increment,
the last round key's address, the counter block's address in `rax` and the
data's in `rdx`. -/
def setupK : List Instr :=
  Gcm.X86_64.Pclmul.const .xmm0 revMask ++
  ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .movImm64 .r10 1, .vop (.vmovq .xmm15 .r10),
   .vmovdquLoad .l128 .xmm14 (at_ .rdx 0),
   .vop (.vbin .vpaddd .l128 .xmm13 .xmm14 .xmm15), .vop (.vinserti128 .xmm14 .xmm14 .xmm13 1),
   .movImm64 .r10 2, .vop (.vmovq .xmm15 .r10), .vop (.vinserti128 .xmm15 .xmm15 .xmm15 1),
   .mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi),
   .mov .rax (.reg .rdx), .mov .rdx (.reg .r12)] : List Instr)

/-- A group of sixteen blocks at `rdx` enciphered; `rdx` on, `r9` down. -/
def cbody : Prog isa :=
  .seq (batch 0 fun _ => []) (.seq (batch 4 fun _ => [])
    (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16)]))

/-- `r9` (a multiple of 16, at least 16) blocks at `r12` enciphered in counter
mode from the counter block at `rdx`, which is advanced. -/
def ctr : Prog isa :=
  .seq (.block setupK) (.seq (.loop cbody .ne) (.block (storeCtr ++ ([.vop .vzeroupper] : List Instr))))

/-- The data's length compared with 256. -/
def lenCmp : List Instr := [.mov .rax (.mem (Impl.AesGcm.X86_64.at_ .r15 lenO)), .alu .cmp .rax (imm 256)]

/-- The groups' blocks and the rest of the data. -/
def groups (d : Reg) : List Instr :=
  [.mov d (.mem (Impl.AesGcm.X86_64.at_ .r15 dataO)), .mov .r9 (.mem (Impl.AesGcm.X86_64.at_ .r15 lenO)),
    .shift .shr .r9 8, .alu .add .r9 (.reg .r9), .alu .add .r9 (.reg .r9), .alu .add .r9 (.reg .r9),
    .alu .add .r9 (.reg .r9)]

/-- With 256 bytes of data or more: POLYVAL of the additional data, the
data's groups (`hash`, its powers in `vg_ghash`'s working space, which
absorbing writes anyway), the rest of the data, the lengths and the tag
input. -/
def hashS : Prog isa :=
  .seq (.block [.mov .r12 (.mem (Impl.AesGcm.X86_64.at_ .r15 aadO)), .mov .rbp (.mem (Impl.AesGcm.X86_64.at_ .r15 alenO))])
  (.seq (absorb c wide)
  (.seq (.block (ptr .rcx .r15 yO ++ ptr .r8 .r15 hO ++ ptr .r11 .r15 ghO ++ groups .rdx))
  (.seq hash
  (.seq (.block rest)
  (.seq (absorb c wide)
  (.seq (lens c) (.block tagIn)))))))

/-- With 256 bytes of data or more: counter mode from the tag, on the data's
groups (`ctr`), then on the rest of the data. Its first two blocks are
`stitched`'s: the counter block from the tag, and the loop's arguments. -/
def cryptS : Prog isa :=
  .seq (.block [.mov .rax (.mem (Impl.AesGcm.X86_64.at_ .r15 tagO)), .store (Impl.AesGcm.X86_64.at_ .r15 cmO) .rax,
      .mov .rax (.mem (Impl.AesGcm.X86_64.at_ .r15 (tagO + 8))), .movImm64 .rcx 0x8000000000000000,
      .alu .or .rax (.reg .rcx), .store (Impl.AesGcm.X86_64.at_ .r15 (cmO + 8)) .rax,
      .mov .r12 (.mem (Impl.AesGcm.X86_64.at_ .r15 aadO)), .mov .rbp (.mem (Impl.AesGcm.X86_64.at_ .r15 alenO))])
  (.seq (.block (ptr .rdi .r15 skO ++ ([.mov .rsi (.mem (Impl.AesGcm.X86_64.at_ .r15 roundsO))] : List Instr) ++
      ptr .rdx .r15 cmO ++ ptr .rcx .r15 yO ++ ptr .r8 .r15 hO ++ ptr .r11 .r15 scrO ++ groups .r12))
  (.seq ctr
  (.seq (.block rest) (cryptRest c e wide))))

/-- `vg_aes_gcm_siv_seal`, with the loops from 256 bytes of data. -/
def «seal» : Prog isa :=
  .seq (.block entry) (.seq (keys c e)
    (.seq (.block lenCmp) (.seq (.ite .b (polyvalS c wide) (hashS c wide))
    (.seq (tag c tagO)
    (.seq (.block lenCmp) (.seq (.ite .b (crypt c e wide) (cryptS c e wide))
    (.block (tagOut ++ restore))))))))

end VG.Impl.AesGcmSiv.X86_64Stitch
