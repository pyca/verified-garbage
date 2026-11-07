module

public import VerifiedGarbage.Impl.AesXts.X86_64AesNi

/-!
# XTS-AES on x86-64 in one pass, out of place

`vg_aes_xts_encrypt_to_vaes_vpclmul(schedule = rdi, rounds = rsi, tweak = rdx, src = rcx, n = r8,
scratch = r9, dst = r10)` and `vg_aes_xts_decrypt_to_vaes_vpclmul`, and their
`_aesni_pclmul` counterparts: the one-pass functions of `X86_64Vaes.lean`
and `X86_64AesNi.lean`, with the blocks read from `src` and written to
`dst` (the contract `VG.Proof.AesXts.X86_64.To.xtsToX86_64`). Each block is
read once from `src`, has its tweak XORed in, is enciphered (or
deciphered), has its tweak XORed in again, and is stored to `dst`: nothing
is copied.

The code is that of the in-place functions but for two things. On entry,
`src - dst` is kept at `scratch + 248` (`dOff`, below the tweaks and above
the round keys decryption keeps there) and `dst` takes the place of the
data pointer, so `r11` walks `dst`; after the setup, `src - dst` is loaded
into `rcx`, which the loops leave alone, and every block is loaded from
`[r11 + rcx + d]` (`ix`), the block at `src` whose result goes to
`[r11 + d]`.

Every branch and every address depends only on the pointers, `rounds` and
`n`. No callee-saved register is written.
-/

@[expose] public section

namespace VG.Impl.AesXts.X86_64VaesTo

open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ regs8)
open VG.Impl.AesXts.X86_64Vaes (enter gen regs4 tws ldT stT constK postXor steps tPost finish)

/-- Where `src - dst` waits, in the scratch buffer. -/
def dOff : Nat := 248

/-- `[r11 + rcx + d]`: with `dst + d` in `r11` and `src - dst` in `rcx`, the
block at `src + d`. -/
def ix (d : Nat) : MemOp := { base := .r11, index := some .rcx, disp := d }

/-- `src - dst` into the scratch buffer, and `dst` where `enter` takes the
data pointer from. -/
def enterTo : List Instr :=
  [.alu .sub .rcx (.reg .r10), .store (at_ .r9 dOff) .rcx, .mov .rcx (.reg .r10)] ++ enter

/-- `src - dst` back into `rcx`, and `cmp r9, 8`. -/
def ldD : List Instr := [.mov .rcx (.mem (at_ .r8 dOff)), .alu .cmp .r9 (.imm 8)]

/-- `X86_64Vaes.preXor`, with the blocks loaded from `src`. -/
def preXor : List XReg → List XReg → Nat → List Instr
  | b :: bs, t :: ts, k => ([.vmovdquLoad .l256 b (ix (32 * k)), .vop (.vbin .vpxor .l256 b b t)] : List Instr) ++
      preXor bs ts (k + 1)
  | _, _, _ => []

/-- `X86_64Vaes.tPre`, with the blocks loaded from `src`. -/
def tPre : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, k => ([.movdquLoad b (ix (16 * k)), .movdquLoad .xmm9 (at_ .rax (16 * k)),
      .xop (.bin .pxor b .xmm9)] : List Instr) ++ tPre bs (k + 1)

/-- `X86_64Vaes.group`, with the blocks loaded from `src`. -/
def group (f : List XReg → Prog isa) : Prog isa :=
  .seq (.block (preXor regs4 tws 0))
    (.seq (f regs4)
      (.block (postXor regs4 tws 0 ++ steps ++ ([.alu .add .r11 (.imm 128), .alu .sub .r9 (.imm 8),
        .alu .cmp .r9 (.imm 8)] : List Instr))))

/-- `X86_64Vaes.tail1`, with the block loaded from `src`. -/
def tail1 (f : List XReg → Prog isa) : Prog isa :=
  .seq (.block (tPre [.xmm0] 0))
    (.seq (f [.xmm0])
      (.block (tPost [.xmm0] 0 ++ ([.alu .add .r11 (.imm 16), .alu .add .rax (.imm 16),
        .alu .sub .r9 (.imm 1)] : List Instr))))

/-- `X86_64Vaes.tail`, with the blocks loaded from `src`. -/
def tail (f : List XReg → Prog isa) : Prog isa :=
  .seq (.block [.mov .rax (.reg .r8), .alu .add .rax (.imm 256), .alu .test .r9 (.reg .r9)])
    (.ite .e (.block []) (.loop (tail1 f) .ne))

/-- `X86_64Vaes.loop8`, with the blocks loaded from `src`. -/
def loop8 (f8 : List XReg → Prog isa) : Prog isa :=
  .ite .b (.block [])
    (.seq (.block (constK ++ ldT tws 0))
      (.seq (.loop (group f8) .ae) (.block (stT tws 0 ++ ([.vop .vzeroupper] : List Instr)))))

/-- `X86_64AesNi.group`, with the blocks loaded from `src`. -/
def groupNi (f : List XReg → Prog isa) : Prog isa :=
  .seq (.block (tPre regs8 0))
    (.seq (f regs8)
      (.block (tPost regs8 0 ++ X86_64AesNi.steps ++ ([.alu .add .r11 (.imm 128), .alu .sub .r9 (.imm 8),
        .alu .cmp .r9 (.imm 8)] : List Instr))))

/-- `X86_64AesNi.loop8`, with the blocks loaded from `src`. -/
def loop8Ni (f : List XReg → Prog isa) : Prog isa :=
  .ite .b (.block [])
    (.seq (.block (X86_64AesNi.constK ++ ([.mov .rax (.reg .r8), .alu .add .rax (.imm 256)] : List Instr)))
      (.loop (groupNi f) .ae))

/-- All the blocks (at least one), as `X86_64Vaes.crypt`, out of place. -/
def crypt (pre loop : Prog isa) (f : List XReg → Prog isa) : Prog isa :=
  .seq (.block [.alu .test .r8 (.reg .r8)])
    (.ite .e (.block [])
      (.seq (.block (enterTo ++ gen))
        (.seq pre
          (.seq (.block ldD)
            (.seq loop (.seq (tail f) (.block finish)))))))

def encryptVaes : Prog isa := crypt (.block []) (loop8 Aes.X86_64.Vaes.aes) Aes.X86_64.AesNi.aes

def decryptVaes : Prog isa :=
  crypt Aes.X86_64.AesNi.imcKeys (loop8 Aes.X86_64.VaesBlocks.aesDec) Aes.X86_64.AesNi.aesDec

def encryptAesNi : Prog isa := crypt (.block []) (loop8Ni Aes.X86_64.AesNi.aes) Aes.X86_64.AesNi.aes

def decryptAesNi : Prog isa :=
  crypt Aes.X86_64.AesNi.imcKeys (loop8Ni Aes.X86_64.AesNi.aesDec) Aes.X86_64.AesNi.aesDec

end VG.Impl.AesXts.X86_64VaesTo
