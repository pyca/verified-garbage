import VerifiedGarbage.Impl.Gcm.X86_64.StitchZTo

/-!
# The VAES interleaved encryption loop, out of place

`Stitch.enc` for `vg_aes_gcm_encrypt_blocks_to`, which reads the plaintext
from one buffer and writes the ciphertext to another: `(ctx = rdi,
rounds = rsi, counter = rdx, y = rcx, src = r8, n = r9, dst = r10,
scratch = r11)`.

The setup ends with `StitchZTo.setupCTo` in place of `Stitch.setupC`: it
computes `r8 ← src - dst` before `r10` becomes the last round key's address,
and points `rdx` at `dst`. `r8` then stays constant: each pair of plaintext
blocks is loaded from `[rdx + r8 + 32 j]` (the plaintext at the offset of
the output blocks the pair is written to, `xorDataKTo`), and the ciphertext
stored to `[rdx + 32 j]`, where the GHASH loads read it back, as in place.
Everything else is the code of `Stitch.enc`.
-/

namespace VG.Impl.Gcm.X86_64.StitchTo

open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Aes.X86_64.Vaes (ctrsK aesK)
open VG.Impl.Gcm.X86_64.Stitch (aregs storesK pregs setupG gA gB storeCtr lastG storeY)
open VG.Impl.Gcm.X86_64.StitchZTo (atIx setupCTo)
open VG.Impl.Gcm.X86_64.Vpclmul (zero)

/-- XOR block register `i` into the two plaintext blocks at
`base + idx + 32 (j + i)`, through `t`, and store the result to
`base + 32 (j + i)` (`Vaes.xorDataK` out of place). -/
def xorDataKTo (t : XReg) (base idx : Reg) : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => [.vmovdquLoad .l256 t (atIx base idx (32 * j)), .vop (.vbin .vpxor .l256 b b t),
      .vmovdquStore .l256 (at_ base (32 * j)) b] ++ xorDataKTo t base idx bs (j + 1)

/-- `Stitch.setup`, out of place. -/
def setup : List Instr := setupG ++ storesK .r11 pregs 0 ++ setupCTo

/-- Eight plaintext blocks at `rdx + r8 + 32 j` encrypted to `rdx + 32 j`,
the GHASH loads `g i` after round `i`. -/
def batchTo (j : Nat) (g : Nat → List Instr) : Prog isa :=
  .seq (.block (ctrsK .xmm14 .xmm0 .xmm15 aregs))
    (.seq (aesK .xmm13 aregs g) (.block (xorDataKTo .xmm13 .rdx .r8 aregs j)))

/-- The first group, encrypted only. -/
def firstTo : Prog isa := .seq (batchTo 0 fun _ => []) (batchTo 4 fun _ => [])

/-- A group encrypted (to `rdx + 256`) and the previous one hashed (at
`rdx`). -/
def bodyTo : Prog isa :=
  .seq (.block zero)
    (.seq (batchTo 8 gA)
      (.seq (batchTo 12 gB)
        (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 32)])))

/-- `Stitch.enc`, out of place: `n` (a multiple of 16, at least 16) blocks. -/
def enc : Prog isa :=
  .seq (.block setup)
    (.seq firstTo
      (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.seq (.ite .b (.block []) (.loop bodyTo .ae))
          (.block (storeCtr ++ lastG ++ storeY)))))

end VG.Impl.Gcm.X86_64.StitchTo
