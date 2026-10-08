import VerifiedGarbage.Impl.Gcm.X86_64.StitchZP

/-!
# The AVX-512 interleaved encryption loop, out of place

`StitchZ.enc` and `StitchZP.enc` for `vg_aes_gcm_encrypt_blocks_to`, which
reads the plaintext from one buffer and writes the ciphertext to another:
`(ctx = rdi, rounds = rsi, counter = rdx, y = rcx, src = r8, n = r9,
dst = r10, scratch = r11)`.

The setup computes `r8 ← src - dst` before `r10` becomes the last round
key's address, and points `rdx` at `dst` (`setupCTo`, in place of
`Stitch.setupC`'s `mov rdx, r8`). `r8` then stays constant: each group of
plaintext is loaded from `[rdx + r8 + 64 j]` (the plaintext at the offset of
the output block the group is written to, `xorDataZTo`), and the ciphertext
stored to `[rdx + 64 j]`, where the GHASH loads read it back, as in place.
Everything else is the code of `StitchZ` and `StitchZP`.
-/

namespace VG.Impl.Gcm.X86_64.StitchZTo

open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY setupG storesK pregs)
open VG.Impl.Aes.X86_64.VaesZ (aesZ ctrsZ)
open VG.Impl.Gcm.X86_64.StitchZ (gq gq48 pow48 lastG adv setupZ)
open VG.Impl.Gcm.X86_64.StitchZP (setupGP powP48)

/-- `[base + idx + d]`. -/
def atIx (base idx : Reg) (d : Nat) : MemOp := { base, index := some idx, disp := d }

/-- XOR block register `i` into the four plaintext blocks at
`base + idx + 64 (j + i)`, through `t`, and store the result to
`base + 64 (j + i)` (`VaesZ.xorDataZ` out of place). -/
def xorDataZTo (t : XReg) (base idx : Reg) : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => [.vmovdqu32Load t (atIx base idx (64 * j)), .zop (.zbin .vpxord b b t),
      .vmovdqu32Store (at_ base (64 * j)) b] ++ xorDataZTo t base idx bs (j + 1)

/-- `Y`, the four counters, the increment, `src - dst` in `r8`, `dst` in
`rdx` and the last round key's address in `r10`. -/
def setupCTo : List Instr :=
  [.vmovdquLoad .l128 .xmm2 (at_ .rcx 0), .vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
   .movImm64 .rax 1, .vop (.vmovq .xmm15 .rax),
   .vmovdquLoad .l128 .xmm14 (at_ .rdx 0), .vop (.vbin .vpshufb .l128 .xmm14 .xmm14 .xmm0),
   .vop (.vbin .vpaddd .l128 .xmm13 .xmm14 .xmm15), .vop (.vinserti128 .xmm14 .xmm14 .xmm13 1),
   .movImm64 .rax 2, .vop (.vmovq .xmm15 .rax), .vop (.vinserti128 .xmm15 .xmm15 .xmm15 1),
   .alu .sub .r8 (.reg .r10), .mov .rax (.reg .rdx), .mov .rdx (.reg .r10),
   .mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi)]

/-- `StitchZ.setup`, out of place. -/
def setup : List Instr := setupG ++ storesK .r11 pregs 0 ++ setupCTo ++ setupZ

/-- `StitchZP.setupP`, out of place. -/
def setupP : List Instr := setupGP ++ storesK .r11 pregs 0 ++ setupCTo ++ setupZ

/-- Sixteen plaintext blocks at `rdx + r8 + 64 j` encrypted to `rdx + 64 j`,
the GHASH work `g i` after round `i`. -/
def batchTo (j : Nat) (g : Nat → List Instr) : Prog isa :=
  .seq (.block (ctrsZ .xmm14 .xmm0 .xmm15 aregs)) (.seq (aesZ .xmm13 aregs g) (.block (xorDataZTo .xmm13 .rdx .r8 aregs j)))

/-- The first group, encrypted only. -/
def firstTo : Prog isa := batchTo 0 fun _ => []

/-- A group encrypted (to `rdx + 256`) and the previous one hashed (at `rdx`). -/
def bodyTo : Prog isa :=
  .seq (batchTo 4 gq) (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 32)])

/-- Three groups encrypted (to `rdx + 768`) and the three before hashed (at
`rdx`). -/
def body48To : Prog isa :=
  .seq (batchTo 12 (gq48 0)) (.seq (batchTo 16 (gq48 1)) (.seq (batchTo 20 (gq48 2))
    (.block [.alu .add .rdx (.imm 768), .alu .sub .r9 (.imm 48), .alu .cmp .r9 (.imm 96)])))

/-- After the tables of 48 blocks: the next two groups, the loop, and two of
the three groups left to hash. -/
def bigRestTo : Prog isa :=
  .seq (batchTo 4 fun _ => []) (.seq (batchTo 8 fun _ => [])
    (.seq (.loop body48To .ae) (.block (.vmovdqu32Load .xmm1 (at_ .r11 832) :: (lastG ++ adv ++ lastG ++ adv)))))

/-- `StitchZ.big`, out of place. -/
def bigTo : Prog isa := .seq (.block pow48) bigRestTo

/-- `StitchZP.bigP`, out of place. -/
def bigPTo : Prog isa := .seq (.block powP48) bigRestTo

/-- `n` (a multiple of 16, at least 16) blocks, after the setup `su`, with
`bigC` from 256 blocks on. -/
def encWith (su : List Instr) (bigC : Prog isa) : Prog isa :=
  .seq (.block su)
    (.seq firstTo
      (.seq (.block [.alu .cmp .r9 (.imm 256)])
        (.seq (.ite .b (.block []) bigC)
          (.seq (.block [.alu .cmp .r9 (.imm 32)])
            (.seq (.ite .b (.block []) (.loop bodyTo .ae))
              (.block (storeCtr ++ lastG ++ storeY)))))))

/-- `StitchZ.enc`, out of place. -/
def enc : Prog isa := encWith setup bigTo

/-- `StitchZP.enc`, out of place. -/
def encP : Prog isa := encWith setupP bigPTo

end VG.Impl.Gcm.X86_64.StitchZTo
