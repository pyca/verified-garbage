module

public import VerifiedGarbage.Impl.MlKem.X86_64.Sample4

/-!
# ML-KEM on x86-64: three entries of the matrix and three blocks of `H(ek)` at once

`sampleH` is a fragment that encapsulation inlines (not a function), with
the interface of `vg_mlkem_sample_ntt4_avx2` (`Sample4.lean`): `seeds` in
`rdi`, `a` in `rsi` and `scratch` in `rdx`. It runs `SampleNTT` on the first
three seeds to the first three polynomials from `a`, as
`vg_mlkem_sample_ntt4_avx2` does, while the fourth state of the four
Keccak states, which that function uses for a fourth seed, absorbs three
blocks of the input of `H = SHA3-256` (rate 136): the state of that sponge
is at `scratch + 6720` (`oHS`, 200 bytes, as `[u64; 25]`), and the three
blocks at `scratch + 6920` (`oHB`, 408 bytes), past what the sampling uses.

The code is `vg_mlkem_sample_ntt4_avx2`'s with three changes:

1. After the padded seeds are written to the four states, the fourth state
   is overwritten with the sponge's state (`hload`).
2. Each of the three squeezes first XORs the next block (17 lanes, from
   `r8`, which the permutation keeps) into the fourth state (`hxor`), so
   that its permutation is the sponge's absorption of that block.
3. After the three squeezes, the fourth state is stored back as the
   sponge's (`hsave`), and only the first three seeds are sampled
   (`run1 0` to `run1 2`, then `tail3`): if one of them has fewer than 256
   coefficients, the two more squeezes permute all four states again (the
   fourth is no longer needed), and each of the three runs 112 more
   iterations.

The fourth state's output is copied to the fourth buffer, which nothing
reads. The XOR and the copies have fixed addresses, so the sponge's state
and blocks do not affect timing; the sampling's branches and addresses
depend on the first three seeds only.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64.Sample4

open VG.X86_64
open VG.Impl.Sha3.X86_64.X4 (rcTable)

/-- The state of the sponge of `H` (200 bytes) and its next three blocks
(408 bytes), in the scratch space. -/
def oHS : Nat := 6720
def oHB : Nat := 6920

/-- The sponge's state to the fourth state (lane `i` at byte `32 i + 24`). -/
def hload : List Instr :=
  (List.range 25).flatMap fun i => [.mov .rax (.mem (at_ .rbx (oHS + 8 * i))), .store (at_ .rbx (32 * i + 24)) .rax]

/-- The block at `r8` XORed into the fourth state, and `r8` to the next. -/
def hxor : List Instr :=
  ((List.range 17).flatMap fun i => [.mov .rax (.mem (at_ .r8 (8 * i))),
    .alu .xor .rax (.mem (at_ .rbx (32 * i + 24))), .store (at_ .rbx (32 * i + 24)) .rax]) ++
  [.alu .add .r8 (.imm 136)]

/-- A block XORed into the fourth state, then a squeeze. -/
def squeezeH (fast : Bool := false) : Prog isa := .seq (.block hxor) (squeeze fast)

/-- The three squeezes, each absorbing a block from `scratch + oHB`. -/
def squeezesH (fast : Bool := false) : Prog isa :=
  .seq (.block [.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 oHB))])
    (blocks oBuf 168 3 (squeezeH fast))

/-- The fourth state back to the sponge's. -/
def hsave : List Instr :=
  (List.range 25).flatMap fun i => [.mov .rax (.mem (at_ .rbx (32 * i + 24))), .store (at_ .rbx (oHS + 8 * i)) .rax]

/-- `r14` is 1 if each of the first three seeds has 256 coefficients, and 0 otherwise. -/
def cntFlags3 : List Instr := .mov32 .r14 (.imm 1) :: (List.range 3).flatMap fun k =>
  [.mov .rax (.mem (at_ .rbx (oCnt + 8 * k))), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax)]

/-- Two more blocks of each state, and 112 more iterations on each of the first three seeds. -/
def more3 (fast : Bool := false) (w16 : Bool := false) : Prog isa :=
  .seq (.block [.mov32 .r14 (.imm 1)]) (.seq (squeezes 0 2 fast) (.seq (.block tabAddr)
    (.seq (run2 0 w16) (.seq (run2 1 w16) (.seq (run2 2 w16) (.block cntFlags3))))))

/-- If one of the first three seeds has fewer than 256 coefficients, `more3`; then the return value. -/
def tail3 (fast : Bool := false) (w16 : Bool := false) : Prog isa :=
  .seq (.block (cntFlags3 ++ ([.alu32 .cmp .r14 (.imm 0)] : List Instr)))
    (.seq (.ite .e (more3 fast w16) (.block [])) (.block (([.vop .vzeroupper] : List Instr) ++ epi)))

/-- Three entries of the matrix and three blocks of `H`'s sponge, with
32-bit coefficients or, if `w16`, 16-bit ones. -/
def sampleH (fast : Bool := false) (w16 : Bool := false) : Prog isa :=
  .seq (.block (pro ++ rcTable .rbx (oRc / 32) ++ absorb4)) (.seq (.block hload) (.seq (squeezesH fast)
    (.seq (.block hsave) (.seq (.block tabAddr) (.seq (run1 0 w16) (.seq (run1 1 w16) (.seq (run1 2 w16) (tail3 fast w16))))))))

end VG.Impl.MlKem.X86_64.Sample4
