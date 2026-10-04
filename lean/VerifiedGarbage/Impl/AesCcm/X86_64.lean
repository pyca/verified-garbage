import VerifiedGarbage.Impl.AesGcm.X86_64
import VerifiedGarbage.Impl.CmacAes.X86_64

/-!
# AES-CCM: x86-64 implementation

`vg_aes_ccm_seal(schedule = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx, aad = r8, aad_len = r9, data = [rsp + 8], len = [rsp + 16], work = [rsp + 24], tag_len = [rsp + 32])`
and `vg_aes_ccm_open` with the same arguments (see `VG.Spec.Ccm.sealContract`
and `openContract`), composed of calls of the verified `vg_cmac_aes_update`,
whose chaining (`Cᵢ = CIPH_K(Cᵢ₋₁ ⊕ Mᵢ)`) from a zero block is CCM's CBC-MAC
(§6.1 steps 1–4), and `vg_aes_ctr32`. Like those, they are generic over the
implementation of AES they call (`Ctr32`, and `sfx`, the suffix of the name
of `vg_cmac_aes_update` made with it).

## The working space

`work` (`W`, 2560 bytes): `[0, 16)` the tag (the received one, for `open`),
`[32, 48)` a block `B`: `B₀`, the first block of the associated data or a
last block padded with zeros, `[48, 64)` the counter block `Ctr₀`,
`[64, 80)` the counter block passed to `vg_aes_ctr32` (`Ctr₁` first),
`[80, 96)` a keystream block, `[96, 112)` the MAC `open` computes,
`[112, 160)` our caller's `rbx, rbp, r12–r15`, `[160, 240)` the arguments
and other public values kept across calls, `[240, 272)` the two tags `open`
compares, padded with zeros (`cmp`, `recv`), and `[384, 2560)` the working
space of the functions called.

## Registers

`r15` holds `W` and `r13` the key schedule throughout; the functions called
preserve them. The pieces take their arguments in `r12` (a pointer), `rbp`
(a length) and `rbx`; the number of rounds is kept in `W` and loaded before
each call.

## The pieces

* `ctrs`: `Ctr₀ = [q − 1]₈ ‖ N ‖ 0⁸q` and `Ctr₁` (A.3), for `q = 15 − n`.
* `b0 y`: `B₀ = flags ‖ N ‖ [p]₈q` (A.2.1), from `Ctr₀`: its first byte
  replaced by the flags, and `[p]₆₄` ORed into its last 8 bytes (the bytes
  of `[p]₆₄` before the last `q` are zero, as `p < 2^(8q)`); then the MAC
  state at `W + y` zeroed and `B₀` chained into it.
* `aad y`: if there is associated data, its first block, the encoding of its
  length (A.2.2, `header`) followed by as many of its bytes as fit
  (`aadHead`), then the rest (`absorbPad`).
* `absorbPad y`: the `rbp` bytes at `r12` padded with zeros to whole blocks,
  chained: the whole blocks in one call, then the last bytes in `B`.
* `mac y`: `b0`, `aad` and the payload (`absorbPad` of the data), so that
  `W + y` holds `Yᵣ`.
* `tag y`: `Yᵣ ⊕ CIPH_K(Ctr₀)` at `W + y`, by `vg_aes_ctr32` on it.
* `ctr`: the data XORed with the keystream from `Ctr₁`: its whole blocks by
  `vg_aes_ctr32`, in chunks that stop where the low 32 bits of the counter
  wrap around (`ctrChunk`), after which the counter's next 32 bits are
  incremented, since CCM's counter (A.3) is `q` bytes, up to 8, and
  `vg_aes_ctr32` increments only the low 32 bits; then the last bytes with a
  keystream block. How many blocks a chunk has depends only on the length:
  the low 32 bits of the counter `Ctrᵢ` are `i` modulo 2³² when `q ≥ 4`, and
  never wrap when `q < 4`, as `i < 2^(8q)`.
* `mask`: every byte of the data ANDed with `0 − ok`, for `ok` the result
  of `cmp`.

`seal` computes the MAC of the payload, the tag, then encrypts the payload;
`open` decrypts it, computes the MAC of the plaintext and the tag at
`W + 96`, compares the first `tag_len` bytes of the two tags without a
branch, and masks the data.

Only the pointers, `rounds`, the lengths and `tag_len` can affect timing:
the branches are on those, and so are the numbers of calls, bytes copied and
blocks chained.
-/

namespace VG.Impl.AesCcm.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (Ctr32)
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop xorLoop minLen recv cmp)

/-! ## The working space -/

def bO : Nat := 32
def c0O : Nat := 48
def c1O : Nat := 64
def ksO : Nat := 80
def uO : Nat := 96
def nonceO : Nat := 160
def nlenO : Nat := 168
def aadO : Nat := 176
def alenO : Nat := 184
def dataO : Nat := 192
def lenO : Nat := 200
def tlO : Nat := 208
def kO : Nat := 216
def okO : Nat := 224
def roundsO : Nat := 232
def scrO : Nat := 384

def saved : List (Reg × Nat) :=
  [(.rbx, 112), (.rbp, 120), (.r12, 128), (.r13, 136), (.r14, 144), (.r15, 152)]

/-- Saves our caller's registers at `b + 112`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .store (at_ b d) r

/-- Restores them, with `r15` (restored last) holding `W`. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .r15 d))

/-- The 16 bytes at `W + d` zeroed. -/
def zero16 (d : Nat) : List Instr :=
  [.mov32 .rax (imm 0), .store (at_ .r15 d) .rax, .store (at_ .r15 (d + 8)) .rax]

variable (c : Ctr32) (sfx : String)

def callUpdate : Prog isa := .call ("vg_cmac_aes_update" ++ sfx) (Impl.CmacAes.X86_64.update c)

def callCtr : Prog isa := .call c.name c.code

/-! ## The CBC-MAC -/

/-- `vg_cmac_aes_update`'s arguments but the data and the number of blocks:
the key schedule, the rounds, the MAC state at `W + y` and the working
space. -/
def updArgs (y : Nat) : List Instr :=
  [.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] ++ ptr .rdx .r15 y ++ ptr .r9 .r15 scrO

/-- `B` chained into the MAC state at `W + y`. -/
def updBlock (y : Nat) : Prog isa :=
  .seq (.block (updArgs y ++ ptr .rcx .r15 bO ++ [.mov32 .r8 (imm 1)])) (callUpdate c sfx)

/-- The `rbp` bytes at `r12`, padded with zeros to whole blocks, chained into
the MAC state at `W + y`. -/
def absorbPad (y : Nat) : Prog isa :=
  .seq (.block [.mov .r8 (.reg .rbp), .shift .shr .r8 4, .alu .test .r8 (.reg .r8)])
  (.seq (.ite .e (.block []) (.seq (.block (updArgs y ++ [.mov .rcx (.reg .r12)])) (callUpdate c sfx)))
  (.seq (.block [.mov .rcx (.reg .rbp), .alu .and .rcx (imm 15), .alu .test .rcx (.reg .rcx)])
    (.ite .e (.block [])
      (.seq (.block (zero16 bO ++ [.mov .rsi (.reg .rbp), .alu .sub .rsi (.reg .rcx), .alu .add .rsi (.reg .r12)] ++
          ptr .rdi .r15 bO))
        (.seq copyLoop (updBlock c sfx y))))))

/-- `B` zeroed, and the encoding (A.2.2) of the length `rbp` (not 0) of the
associated data at its start, its length (2, 6 or 10) in `rbx`. -/
def header : Prog isa :=
  .seq (.block (zero16 bO ++ [.mov32 .rax (imm 0xff00), .alu .cmp .rbp (.reg .rax)]))
  (.ite .b
    (.block [.mov .rax (.reg .rbp), .bswap .rax, .shift .shr .rax 48, .store (at_ .r15 bO) .rax,
      .mov32 .rbx (imm 2)])
    (.seq (.block [.movImm64 .rax 0x100000000, .alu .cmp .rbp (.reg .rax)])
      (.ite .b
        (.block [.mov .rax (.reg .rbp), .bswap .rax, .shift .shr .rax 16, .alu .or .rax (imm 0xfeff),
          .store (at_ .r15 bO) .rax, .mov32 .rbx (imm 6)])
        (.block [.mov32 .rax (imm 0xffff), .store (at_ .r15 bO) .rax, .mov .rax (.reg .rbp), .bswap .rax,
          .store (at_ .r15 (bO + 2)) .rax, .mov32 .rbx (imm 10)]))))

/-- The first block of the associated data (`rbp` bytes at `r12`, at least
one): the encoding of its length followed by its first `min (16 − h, rbp)`
bytes, padded with zeros, chained into `W + y`; `r12` and `rbp` then the
rest. -/
def aadHead (y : Nat) : Prog isa :=
  .seq header
  (.seq minLen
  (.seq (.block [.mov .rsi (.reg .r12), .mov .rdi (.reg .r15), .alu .add .rdi (.reg .rbx),
      .alu .add .rdi (imm bO), .alu .add .r12 (.reg .rcx), .alu .sub .rbp (.reg .rcx)])
  (.seq copyLoop (updBlock c sfx y))))

/-- The associated data, formatted (A.2.2) and chained into `W + y`. -/
def aad (y : Nat) : Prog isa :=
  .seq (.block [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO)), .alu .test .rbp (.reg .rbp)])
    (.ite .e (.block []) (.seq (aadHead c sfx y) (absorbPad c sfx y)))

/-- `Ctr₀` at `W + 48` and `Ctr₁` at `W + 64`. -/
def ctrs : Prog isa :=
  .seq (.block (zero16 c0O ++ [.mov32 .rax (imm 14), .alu .sub .rax (.mem (at_ .r15 nlenO)),
      .store8 (at_ .r15 c0O) .rax, .mov .rsi (.mem (at_ .r15 nonceO)), .mov .rcx (.mem (at_ .r15 nlenO))] ++
      ptr .rdi .r15 (c0O + 1)))
  (.seq copyLoop
    (.block [.mov .rax (.mem (at_ .r15 c0O)), .store (at_ .r15 c1O) .rax, .mov .rax (.mem (at_ .r15 (c0O + 8))),
      .store (at_ .r15 (c1O + 8)) .rax, .mov32 .rax (imm 1), .store8 (at_ .r15 (c1O + 15)) .rax]))

/-- `B₀` (A.2.1) in `B`, from `Ctr₀`, and chained into the MAC state at
`W + y`, zeroed first. The flags are `64 [a > 0] + 8 ((t − 2) / 2) + q − 1`,
and `8 ((t − 2) / 2) = 4 (t − 2)` for the even `t`. -/
def b0 (y : Nat) : Prog isa :=
  .seq (.block [.mov .rax (.mem (at_ .r15 c0O)), .store (at_ .r15 bO) .rax, .mov .rax (.mem (at_ .r15 (c0O + 8))),
      .store (at_ .r15 (bO + 8)) .rax, .mov .rax (.mem (at_ .r15 tlO)), .alu .sub .rax (imm 2), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax),
      .mov32 .rcx (imm 14), .alu .sub .rcx (.mem (at_ .r15 nlenO)), .alu .add .rax (.reg .rcx),
      .mov .rcx (.mem (at_ .r15 alenO)), .alu .test .rcx (.reg .rcx)])
  (.seq (.ite .e (.block []) (.block [.alu .add .rax (imm 64)]))
  (.seq (.block ([.store8 (at_ .r15 bO) .rax, .mov .rax (.mem (at_ .r15 lenO)), .bswap .rax,
      .alu .or .rax (.mem (at_ .r15 (bO + 8))), .store (at_ .r15 (bO + 8)) .rax] ++ zero16 y))
    (updBlock c sfx y)))

/-- `Yᵣ`, the CBC-MAC of the formatted nonce, associated data and payload
(§6.1 steps 1–4), at `W + y`. -/
def mac (y : Nat) : Prog isa :=
  .seq (b0 c sfx y)
  (.seq (aad c sfx y)
  (.seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))])
    (absorbPad c sfx y)))

/-- `Yᵣ ⊕ CIPH_K(Ctr₀)` at `W + y`. -/
def tag (y : Nat) : Prog isa :=
  .seq (.block ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] ++ ptr .rdx .r15 c0O ++
      ptr .rcx .r15 y ++ [.mov32 .r8 (imm 1)] ++ ptr .r9 .r15 scrO))
    (callCtr c)

/-! ## Counter mode -/

/-- With `rbx` whole blocks left at `r12` and the low 32 bits of the counter
`r14`: `min (rbx, 2³² − r14)` of them by `vg_aes_ctr32`, after which `r12`,
`rbx` and `r14` are past them, and if the low 32 bits wrapped around, `r14`
is 0 and the counter's bytes 8–11 are incremented as a big-endian integer
(ZF set when no block is left). -/
def ctrChunk : Prog isa :=
  .seq (.block [.movImm64 .r8 0x100000000, .alu .sub .r8 (.reg .r14), .alu .cmp .rbx (.reg .r8)])
  (.seq (.ite .b (.block [.mov .r8 (.reg .rbx)]) (.block []))
  (.seq (.block ([.store (at_ .r15 kO) .r8, .mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] ++
      ptr .rdx .r15 c1O ++ [.mov .rcx (.reg .r12)] ++ ptr .r9 .r15 scrO))
  (.seq (callCtr c)
  (.seq (.block [.mov .rax (.mem (at_ .r15 kO)), .alu .sub .rbx (.reg .rax), .alu .add .r14 (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .r12 (.reg .rax), .movImm64 .rax 0x100000000, .alu .cmp .r14 (.reg .rax)])
  (.seq (.ite .e
      (.block [.mov32 .r14 (imm 0), .mov32 .rax (.mem (at_ .r15 (c1O + 8))), .bswap32 .rax,
        .alu32 .add .rax (imm 1), .bswap32 .rax, .store32 (at_ .r15 (c1O + 8)) .rax])
      (.block []))
    (.block [.alu .test .rbx (.reg .rbx)]))))))

/-- The data XORed with the keystream from `Ctr₁` (§6.1 steps 5–8, §6.2
steps 3–5): its whole blocks by `ctrChunk`, then its last `len mod 16` bytes
with a keystream block. -/
def ctr : Prog isa :=
  .seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbx (.mem (at_ .r15 lenO)), .shift .shr .rbx 4,
      .mov32 .r14 (imm 1), .alu .test .rbx (.reg .rbx)])
  (.seq (.ite .e (.block []) (.loop (ctrChunk c) .ne))
  (.seq (.block [.mov .rbp (.mem (at_ .r15 lenO)), .alu .and .rbp (imm 15), .alu .test .rbp (.reg .rbp)])
    (.ite .e (.block [])
      (.seq (.block (zero16 ksO ++ [.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] ++
          ptr .rdx .r15 c1O ++ ptr .rcx .r15 ksO ++ [.mov32 .r8 (imm 1)] ++ ptr .r9 .r15 scrO))
      (.seq (callCtr c)
        (.seq (.block ([.mov .rdi (.reg .r12)] ++ ptr .rsi .r15 ksO ++ [.mov .rcx (.reg .rbp)])) xorLoop))))))

/-! ## Masking the data -/

/-- `[r12 + r10]`. -/
def maskByte : MemOp := { base := .r12, index := some .r10 }

/-- Every byte of the data ANDed with `0 − ok`. -/
def mask : Prog isa :=
  .seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .r11 (imm 0),
      .alu .sub .r11 (.mem (at_ .r15 okO)), .mov32 .r10 (imm 0), .alu .test .rbp (.reg .rbp)])
    (.ite .e (.block [])
      (.loop (.block [.movzx8 .rax maskByte, .alu .and .rax (.reg .r11), .store8 maskByte .rax,
        .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rbp)]) .ne))

/-! ## The functions -/

/-- Saves the registers in the working space (whose address, the ninth
argument, is on the stack above the return address), keeps `W` in `r15` and
the key schedule in `r13`, and the other arguments in `W`. -/
def entry : List Instr :=
  [.mov .rax (.mem (at_ .rsp 24))] ++ save .rax ++
    [.mov .r15 (.reg .rax), .mov .r13 (.reg .rdi), .store (at_ .r15 roundsO) .rsi,
      .store (at_ .r15 nonceO) .rdx, .store (at_ .r15 nlenO) .rcx, .store (at_ .r15 aadO) .r8,
      .store (at_ .r15 alenO) .r9, .mov .rax (.mem (at_ .rsp 8)), .store (at_ .r15 dataO) .rax,
      .mov .rax (.mem (at_ .rsp 16)), .store (at_ .r15 lenO) .rax, .mov .rax (.mem (at_ .rsp 32)),
      .store (at_ .r15 tlO) .rax]

/-- `vg_aes_ccm_seal`. -/
def «seal» : Prog isa :=
  .seq (.block entry) (.seq ctrs (.seq (mac c sfx 0) (.seq (tag c 0) (.seq (ctr c) (.block restore)))))

/-- `vg_aes_ccm_open`. -/
def «open» : Prog isa :=
  .seq (.block entry)
  (.seq ctrs
  (.seq (ctr c)
  (.seq (mac c sfx uO)
  (.seq (tag c uO)
  (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))])
  (.seq recv
  (.seq (cmp uO)
  (.seq (.block [.store (at_ .r15 okO) .rax])
  (.seq mask
    (.block ([.mov .rax (.mem (at_ .r15 okO))] ++ restore)))))))))))

end VG.Impl.AesCcm.X86_64
