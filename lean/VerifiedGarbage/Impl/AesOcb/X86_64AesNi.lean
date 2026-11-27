module

public import VerifiedGarbage.Impl.AesOcb.X86_64
public import VerifiedGarbage.Impl.Aes.X86_64.AesNiBlocks

/-!
# AES-OCB on x86-64 in one pass, with AES-NI

`vg_aes_ocb_seal_aesni` and `vg_aes_ocb_open_aesni`, with the contracts of
`vg_aes_ocb_seal` and `vg_aes_ocb_open` and their arguments
(`X86_64.lean`), their working space `W` (`work`) a last argument, which a
frame on the stack allocates. They call no function: AES runs in their own
code (`Aes.X86_64.AesNi.aes`, `aesDec`), on up to eight blocks at once, one
in each of `xmm0`–`xmm7`, the round key in `xmm8`.

* The entry (`X86_64.entry`) saves our caller's registers and keeps the
  arguments in `W` at the offsets of `X86_64.lean`, with `L_$` and `L_0`.
  Then `L_1`, `L_2` and `L_3` (`lmore`), read back in 8-byte halves (`ldx`), and the table `C` of the XORs of
  `L_0`, `L_1` and `L_2` that the offsets of the blocks `8k + t`, for
  `t` from 1 to 7, are from `Offset_{8k}` (`ctab`): `L_{ntz(8k + t)}` is
  `L_0`, `L_1`, `L_0`, `L_2`, `L_0`, `L_1`, `L_0`, so `Offset_{8k + t}` is
  `Offset_{8k} ⊕ C[t]`. `C[8]`, for the eighth block, is `L_2 ⊕ L_j` with
  `j = 3 + ntz(k + 1)`, which each group of eight sets (`c8`): `L_j` is
  `L_3` doubled `ntz(k + 1)` times, a number of times that depends on the
  public `k` only.
* A group of `r ≤ 8` blocks (`group`), at `r11`, with the offset
  `Offset_{8k}` in `xmm12`: each block is loaded, its offset
  `xmm12 ⊕ C[t]` stored in the buffer at `W + ofO` and XORed in, AES runs
  on all of them, and each is XORed with its offset again and stored (for
  `seal` and `open`), or added to the sum in `xmm10` (for `HASH`).
  `seal` adds each block of the plaintext to the checksum, in `xmm10`,
  before, and `open` after. The offset of the group's last block is the
  next `xmm12`.
* A pass (`pass`) takes groups of eight while it can, counting them in
  `r13`, then the rest, from 1 to 7 blocks, in one group.
* `Ktop`, the nonce block enciphered (`ktop`), comes first, right after the
  entry: its block is written a byte at a time, so its load waits for those
  stores, which `lmore` and `ctab` give time to drain, and its AES then
  runs alongside `HASH`'s.
* `HASH(K, A)` is a pass over the whole blocks of the associated data from
  a zero offset, then the rest padded, XORed with `Offset ⊕ L_*`,
  enciphered and added, to `W + sumO`.
* `Offset_0` (`X86_64.offset0`, from `Ktop`) to `xmm12`, the checksum zeroed; a pass over the whole
  blocks of the data; the rest (`rest`), whose pad is `ENCIPHER` of
  `Offset_* = Offset ⊕ L_*`; and the tag, `ENCIPHER(Checksum ⊕ Offset ⊕
  L_$) ⊕ HASH`, to `W + d`. `open` deciphers with the round keys through
  `aesimc` at `W + imcO` (`Aes.X86_64.AesNi.imcKeys`).
* Then, as in `X86_64.lean`: `seal` copies the tag out (`tagOut`); `open`
  copies the received tag in (`recv`), compares (`cmp`) and masks the data
  (`mask`).

## The working space `W`

Below byte 384, as in `X86_64.lean`, but for `L_1` at 96, `L_2` at 144,
`L_3` at 320 and `L_j` at 336; `[384, 512)`: `C[1]` … `C[8]`; `[512, 640)`:
the offsets of a group; for `open`, `[640, 848)`: round keys 1 … `Nr − 1`
through `aesimc` (`imcKeys` writes round key `j` to `W + imcO + 16 j`).
`seal` uses 640 bytes, `open` 848.

`rdi` holds the key schedule (the key context) throughout, `rsi` the rounds
(reloaded from `W + rndO` where code between clobbers it) and `r10` the
last round key. Only the pointers, the lengths, `rounds` and `tag_len`
(and for `open`, whether the tag is right) affect timing.
-/

@[expose] public section

namespace VG.Impl.AesOcb.X86_64AesNi

open VG.X86_64
open VG.Impl.AesOcb.X86_64 (at_ ld st mvr addi dbl zero16 copy16 ldO l0O ofsO ckO sumO tmpO t2O ohO
  dataO lenO rndO aadO alenO entry nonceBlock offset0 padTo xorPad tagOut recv cmp mask restore tagO)
open VG.Impl.Aes.X86_64.AesNi (regs8)

/-! ## The working space -/

def l1O : Nat := 96
def l2O : Nat := ohO
def l3O : Nat := 320
def ljO : Nat := 336
def cO : Nat := 384
def ofO : Nat := 512
/-- `imcKeys` writes round key `j` (`1 ≤ j < Nr`) to `W + imcO + 16 j`. -/
def imcO : Nat := 624

/-- The bytes of `W` `seal` and `open` use. -/
def sealWork : Nat := 640
def openWork : Nat := 848

/-! ## `L_1` … `L_3` and `C` -/

/-- `x ← W + d`, through `rax`, `rdx` and `t`, in two 8-byte loads: the
block was just written in two 8-byte stores (`dbl`), whose values a
16-byte load would wait for (store forwarding fails). -/
def ldx (x t : XReg) (d : Nat) : List Instr :=
  [ld .rax .r15 d, ld .rdx .r15 (d + 8), .xop (.movq x .rax), .xop (.movq t .rdx),
   .xop (.bin .punpcklqdq x t)]

/-- `L_1`, `L_2` and `L_3`, each the double of the one before. -/
def lmore : List Instr := dbl .r15 l0O .r15 l1O ++ dbl .r15 l1O .r15 l2O ++ dbl .r15 l2O .r15 l3O

/-- `W + cO + 16 (t − 1) ← x` for `C[t]`. -/
def stC (t : Nat) (x : XReg) : Instr := .movdquStore (at_ .r15 (cO + 16 * (t - 1))) x

/-- `C[1]` … `C[7]`, from `L_0`, `L_1` and `L_2` in `xmm12`, `xmm13` and
`xmm14`, through `xmm11`: `L_0`, `L_0 ⊕ L_1`, `L_1`, `L_1 ⊕ L_2`,
`L_0 ⊕ L_1 ⊕ L_2`, `L_0 ⊕ L_2`, `L_2`. -/
def ctab : List Instr :=
  ldx .xmm12 .xmm11 l0O ++ ldx .xmm13 .xmm11 l1O ++ ldx .xmm14 .xmm11 l2O ++
  [stC 1 .xmm12, stC 3 .xmm13, stC 7 .xmm14,
   .xop (.bin .movdqa .xmm11 .xmm12), .xop (.bin .pxor .xmm11 .xmm13), stC 2 .xmm11,
   .xop (.bin .pxor .xmm11 .xmm14), stC 5 .xmm11,
   .xop (.bin .movdqa .xmm11 .xmm13), .xop (.bin .pxor .xmm11 .xmm14), stC 4 .xmm11,
   .xop (.bin .movdqa .xmm11 .xmm12), .xop (.bin .pxor .xmm11 .xmm14), stC 6 .xmm11]

/-- `r10 := rdi + 16 rsi`, the last round key. -/
def lastKey : List Instr :=
  [.mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi)]

/-- `rsi ←` the rounds, and the last round key. -/
def keys : List Instr := ld .rsi .r15 rndO :: lastKey

/-- `rsi ←` the rounds again, from the last round key: `(r10 − rdi) / 16`.
The code computes it rather than read `W + rndO` again, so that the taint
analysis, which forgets what memory holds after a store of a secret it cannot
place, still sees it as public. -/
def keysR : List Instr := [mvr .rsi .r10, .alu .sub .rsi (.reg .rdi), .shift .shr .rsi 4]

/-- `C[8] = L_2 ⊕ L_j`, `j = 3 + ntz(k + 1)` for the group `k` in `r13`:
`L_j` is `L_3` doubled while `r9`, from `k + 1`, is even, halving it. -/
def c8 : Prog isa :=
  .seq (.block (copy16 l3O ljO ++ [mvr .r9 .r13, addi .r9 1, .alu .test .r9 (.imm 1)]))
    (.seq (.ite .ne (.block [])
        (.loop (.block (dbl .r15 ljO .r15 ljO ++ [.shift .shr .r9 1, .alu .test .r9 (.imm 1)])) .e))
      (.block [ld .rax .r15 ljO, ld .rdx .r15 (ljO + 8), .alu .xor .rax (.mem (at_ .r15 l2O)),
        .alu .xor .rdx (.mem (at_ .r15 (l2O + 8))), .xop (.movq .xmm11 .rax), .xop (.movq .xmm13 .rdx),
        .xop (.bin .punpcklqdq .xmm11 .xmm13), stC 8 .xmm11]))

/-! ## Groups and passes -/

/-- What a pass does: `HASH`, `seal`'s or `open`'s. -/
inductive Mode where
  | hash
  | seal
  | «open»
  deriving DecidableEq

/-- Block `t` of the group in `b`: loaded from `r11 + 16 t` (`seal` adds it
to the checksum in `xmm10`), its offset `xmm12 ⊕ C[t + 1]` stored at
`W + ofO + 16 t` and XORed in, through `xmm11`. -/
def gPre (md : Mode) : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, t =>
    ([.movdquLoad b (at_ .r11 (16 * t))] : List Instr) ++
    (if md = .seal then [.xop (.bin .pxor .xmm10 b)] else []) ++
    ([.movdquLoad .xmm11 (at_ .r15 (cO + 16 * t)), .xop (.bin .pxor .xmm11 .xmm12),
      .movdquStore (at_ .r15 (ofO + 16 * t)) .xmm11, .xop (.bin .pxor b .xmm11)] : List Instr) ++
    gPre md bs (t + 1)

/-- Block `t` of the group in `b`, after AES: added to the sum in `xmm10`
(`HASH`), or XORed with its offset again and stored back (`open` adds it to
the checksum in `xmm10`). -/
def gPost (md : Mode) : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, t =>
    (if md = .hash then [.xop (.bin .pxor .xmm10 b)] else
      ([.movdquLoad .xmm11 (at_ .r15 (ofO + 16 * t)), .xop (.bin .pxor b .xmm11),
        .movdquStore (at_ .r11 (16 * t)) b] : List Instr) ++
      (if md = .open then [.xop (.bin .pxor .xmm10 b)] else [])) ++
    gPost md bs (t + 1)

/-- AES's cipher, or for `open` the inverse cipher, on the block
registers. -/
def cipher (md : Mode) (rs : List XReg) : Prog isa :=
  if md = .open then Aes.X86_64.AesNi.aesDec rs else Aes.X86_64.AesNi.aes rs

/-- `r8 ← W + imcO`, for `open`'s inverse cipher. -/
def imcPtr : List Instr := [mvr .r8 .r15, addi .r8 imcO]

/-- A group of `r` blocks (`1 ≤ r ≤ 8`) at `r11` (`gPre`, AES, `gPost`),
then `xmm12 ←` the offset of the last, and `r11` past them. -/
def group (md : Mode) (r : Nat) : Prog isa :=
  .seq (.block (gPre md (regs8.take r) 0 ++ (if md = .open then imcPtr else [])))
    (.seq (cipher md (regs8.take r))
      (.block (gPost md (regs8.take r) 0 ++
        ([.movdquLoad .xmm12 (at_ .r15 (ofO + 16 * (r - 1))), addi .r11 (16 * r)] : List Instr))))

/-- `r12 = t`: a group of `t`, else on to `t + 1`; from `t = 7`, or when
the fuel `f` runs out, a group of 7. -/
def tailUp (md : Mode) : Nat → Nat → Prog isa
  | _, 0 => group md 7
  | t, f + 1 =>
    if t ≥ 7 then group md 7
    else .seq (.block [.alu .cmp .r12 (.imm (BitVec.ofNat 32 t))])
      (.ite .e (group md t) (tailUp md (t + 1) f))

/-- The last `r12` blocks (`r12 < 8`): nothing if `r12` is 0, else one group
of `r12`, tried from 1 to 7. -/
def tail (md : Mode) : Prog isa :=
  .seq (.block [.alu .test .r12 (.reg .r12)]) (.ite .e (.block []) (tailUp md 1 6))

/-- A pass over the `r12` whole blocks at `r11`, the offset in `xmm12`:
groups of eight (`k` in `r13`, with `C[8]` for each), then the tail. -/
def pass (md : Mode) : Prog isa :=
  .seq (.block [.mov .r13 (.imm 0), .alu .cmp .r12 (.imm 8)])
    (.seq (.ite .b (.block [])
        (.loop (.seq c8 (.seq (group md 8)
          (.block [addi .r13 1, .alu .sub .r12 (.imm 8), .alu .cmp .r12 (.imm 8)]))) .ae))
      (tail md))

/-! ## `HASH`, the nonce, the rest and the tag -/

/-- One block in `xmm0` through AES. -/
def one : Prog isa := Aes.X86_64.AesNi.aes [.xmm0]

/-- `HASH(K, A)` to `W + sumO`. -/
def hash : Prog isa :=
  .seq (.block [ld .r11 .r15 aadO, ld .r12 .r15 alenO, .shift .shr .r12 4,
      .xop (.bin .pxor .xmm12 .xmm12), .xop (.bin .pxor .xmm10 .xmm10)])
    (.seq (pass .hash)
      (.seq (.block [mvr .rbx .r11, ld .r12 .r15 alenO, .alu .and .r12 (.imm 15)])
        (.seq (.ite .e (.block [])
            (.seq (padTo t2O)
              (.seq (.block ([.movdquLoad .xmm11 (at_ .rdi 240), .xop (.bin .pxor .xmm12 .xmm11),
                  .movdquLoad .xmm0 (at_ .r15 t2O), .xop (.bin .pxor .xmm0 .xmm12)] ++ keysR))
                (.seq one (.block [.xop (.bin .pxor .xmm10 .xmm0)])))))
          (.block [.movdquStore (at_ .r15 sumO) .xmm10]))))

/-- `Ktop`: the nonce block, its last 6 bits cleared, enciphered in place at
`W + tmpO` (`bottom` at `W + botO`). -/
def ktop : Prog isa :=
  .seq (.block keys)
    (.seq nonceBlock
      (.seq (.block (keysR ++ [.movdquLoad .xmm0 (at_ .r15 tmpO)]))
        (.seq one (.block [.movdquStore (at_ .r15 tmpO) .xmm0]))))

/-- `Offset_0` from `Ktop` and `bottom` to `xmm12`, the last round key
again (`offset0` uses `r10`), and the checksum `xmm10 ← 0`. -/
def nonce : List Instr :=
  offset0 ++ lastKey ++ ldx .xmm12 .xmm11 ofsO ++ [.xop (.bin .pxor .xmm10 .xmm10)]

/-- `Offset_* = Offset ⊕ L_*` to `xmm12`, `Pad = ENCIPHER(K, Offset_*)` to
`W + tmpO`. -/
def restHead : Prog isa :=
  .seq (.block [.movdquLoad .xmm11 (at_ .rdi 240), .xop (.bin .pxor .xmm12 .xmm11),
      .xop (.bin .movdqa .xmm0 .xmm12)])
    (.seq one (.block [.movdquStore (at_ .r15 tmpO) .xmm0]))

/-- The checksum `xmm10 ⊕=` the block at `W + t2O`. -/
def addPad : List Instr := [.movdquLoad .xmm11 (at_ .r15 t2O), .xop (.bin .pxor .xmm10 .xmm11)]

/-- The rest of the data (`r12` bytes at `rbx`, `0 < r12 < 16`): `Pad`
(`restHead`); for `seal` (`enc`) the checksum of the padded plaintext, then
the XOR; for `open`, the XOR, then the checksum. -/
def rest (enc : Bool) : Prog isa :=
  .seq restHead
    (if enc then .seq (padTo t2O) (.seq (.block addPad) xorPad)
    else .seq xorPad (.seq (padTo t2O) (.block addPad)))

/-- The data: whole blocks, then the rest (its length kept in `rbp` across
the pass, as for `keysR`). -/
def body (enc : Bool) : Prog isa :=
  .seq (.block [ld .r11 .r15 dataO, ld .r12 .r15 lenO, mvr .rbp .r12, .shift .shr .r12 4])
    (.seq (pass (if enc then .seal else .open))
      (.seq (.block [mvr .rbx .r11, mvr .r12 .rbp, .alu .and .r12 (.imm 15)])
        (.ite .e (.block []) (rest enc))))

/-- The tag, `ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ HASH(K, A)`, to `W + d`. -/
def tag (d : Nat) : Prog isa :=
  .seq (.block ([.xop (.bin .movdqa .xmm0 .xmm10), .xop (.bin .pxor .xmm0 .xmm12),
      .movdquLoad .xmm11 (at_ .r15 ldO), .xop (.bin .pxor .xmm0 .xmm11)] ++ keysR))
    (.seq one
      (.block [.movdquLoad .xmm11 (at_ .r15 sumO), .xop (.bin .pxor .xmm0 .xmm11),
        .movdquStore (at_ .r15 d) .xmm0]))

/-! ## The functions -/

/-- Between `Ktop` and the data: `L_1`, `L_2`, `L_3`, the table `C`,
`HASH`, `Offset_0` and, for `open` (not `enc`), the round keys through
`aesimc`. -/
def mid (enc : Bool) : Prog isa :=
  .seq (.block (lmore ++ ctab ++ keys))
    (.seq hash
      (.seq (.block nonce)
        (if enc then .block [] else .seq (.block imcPtr) Aes.X86_64.AesNi.imcKeys)))

/-- `seal` (`enc`) or `open` up to the tag, at `W + d`. -/
def front (enc : Bool) (d : Nat) : Prog isa :=
  .seq (.block entry) (.seq ktop (.seq (mid enc) (.seq (body enc) (tag d))))

def «seal» : Prog isa := .seq (front true tagO) (.seq tagOut (.block restore))

def «open» : Prog isa :=
  .seq (front false t2O) (.seq recv (.seq cmp (.seq mask (.block ([ld .rax .r15 tagO] ++ restore)))))

end VG.Impl.AesOcb.X86_64AesNi
