module

public import VerifiedGarbage.Impl.MlKem.X86_64.KpkeAccY
public import VerifiedGarbage.Impl.MlKem.X86_64.Arith

/-!
# ML-KEM on x86-64: the products of K-PKE in one call

`vg_mlkem*_decrypt_mul(w = rdi, s = rsi, u = rdx, scratch = rcx)`
(`Spec/MlKem/KpkeMul.lean`) computes `NTT⁻¹(ŝ^⊺ ∘ NTT(u'))` with the code
of `vg_mlkem_ntt`, `vg_mlkem_multiply_ntts`, `vg_mlkem_add` and
`vg_mlkem_inv_ntt` (or their AVX2 versions, `Bodies`) inlined, inside one
MXCSR region (`withMxcsr`, at `scratch + 768`) rather than one per call,
which is most of the cost of a call. It keeps `scratch` in `rbx`, `w` in
`rbp`, `ŝ[j]` in `r12`, `u'[j]` in `r13` and the count of the `k` terms
left in `r14`, and saves its caller's values of them (and of `r15`) at
`scratch + 3072`.
It sums the products in an accumulator at `w`, in the backend's own form
(`Bodies`): it sets up the table of the products (`Bodies.tab`) and zeroes
the accumulator; then for each `j`, it computes `NTT(u'[j])` to
`scratch + 1024` (`Bodies.nttO`: the NTT's code, but for the pointer its
last step stores through, `r10`) and adds its product with `ŝ[j]` to the
accumulator (`Bodies.mulAcc`); then `NTT⁻¹` of the accumulator, to `w`.
The code it inlines uses the first 1024 bytes of `scratch` as their
working space, and `scratch + 2048` and `scratch + 3328` for the products.
Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- The code of the polynomial arithmetic of one backend, without the MXCSR
prologue and epilogue of its functions, around an accumulator of a sum of
products in a form of the backend's own: `u32`s with SSE2 (`Bodies.sse`),
words with AVX2 (`KpkeAccY.lean`). -/
structure Bodies where
  /-- `NTT` of the polynomial at `rdi` to the one at `r10`, with the working
  space at `rsi`. -/
  nttO : Prog isa
  /-- `NTT⁻¹` of the accumulator at `rdi`, to the polynomial at `rdi`, with
  the working space at `rsi`. -/
  inv : Prog isa
  /-- The accumulator at `rdi` of the zero polynomial. -/
  zero : Prog isa
  /-- Whatever `mulAcc` reads from `scratch = rcx + 3328` (256 bytes). -/
  tab : List Instr
  /-- The accumulator `o` at `rdi = rbp + 1024 o` plus `f = rsi ×_T g = rdx`,
  with the working space at `rcx` (1024 bytes) and at `rcx + 2048` (1024
  bytes), what `tab` left at `rcx + 3328`, and `rbx` equal to `rcx`. -/
  mulAcc : Nat → Prog isa

/-- `vg_mlkem_ntt`'s code, storing to `r10`. -/
def nttOB : Prog isa :=
  .seq vpro (.seq (vlay vbfly 128 1 2) (.seq (vlay vbfly 64 2 2) (.seq (vlay vbfly 32 4 2)
    (.seq (vlay vbfly 16 8 2) (.seq (vlay vbfly 8 16 2) (.seq (vlay4 vbfly 32 0x50 4)
      (.seq (vlay2 vbfly 64 0xE4 8) (.seq (.block [.mov .rdi (.reg .r10)]) vepi))))))))

/-- `vg_mlkem_inv_ntt`'s code. -/
def nttInvB : Prog isa :=
  .seq vpro (.seq (vlay2 vibfly 124 0x1B (-8)) (.seq (vlay4 vibfly 62 0x05 (-4))
    (.seq (vlay vibfly 8 31 (-2)) (.seq (vlay vibfly 16 15 (-2)) (.seq (vlay vibfly 32 7 (-2))
      (.seq (vlay vibfly 64 3 (-2)) (.seq (vlay vibfly 128 1 (-2)) (.seq vscale vepi))))))))

/-- `vg_mlkem_multiply_ntts`'s code. -/
def mulB : Prog isa := .seq (.block [.mov .r10 (.reg .rcx)]) (.seq (.block mulPro) (rcxLoop 16 mulBody))

/-- The polynomial at `rdi`, zeroed, sixteen bytes at a time. -/
def zeroB : Prog isa :=
  .seq (.block [xb .pxor .xmm0 .xmm0]) (rcxLoop 64 [.movdquStore (at_ .rdi 0) .xmm0, .alu .add .rdi (.imm 16)])

/-- `rdi += rsi ×_T rdx`, for `rdi = rbp + 1024 o`: the product to `rcx + 2048`,
with `vg_mlkem_multiply_ntts`'s code, then added to `rdi` (from `rbp` again)
with `vg_mlkem_add`'s; `rbx` is `rcx` (`scratch`). -/
def mulAccB (o : Nat) : Prog isa :=
  .seq (.block (leaR .rdi .rcx 2048))
    (.seq mulB (.seq (.block ([.mov .rdi (.reg .rbp), .alu .add .rdi (.imm (BitVec.ofNat 32 (1024 * o)))] ++
      leaR .rsi .rbx 2048)) X86_64.add))

/-- `vg_mlkem_ntt_avx2`'s code, storing to `r10`. -/
def nttOBY : Prog isa := .seq (ypro zmTab) (.seq nttLazy (.seq (.block [.mov .rdi (.reg .r10)]) yepi))

def Bodies.sse : Bodies := ⟨nttOB, nttInvB, zeroB, [], mulAccB⟩

def Bodies.avx2 : Bodies := ⟨nttOBY, nttInvAccY, zeroAccY, tabAccY, fun _ => mulAccY⟩

namespace KpkeMul

/-- The callee-saved registers and where in `scratch` they are saved (`rbx`,
through which they are loaded back, last). -/
def slots : List (Reg × Nat) := [(.rbp, 3072), (.r12, 3080), (.r13, 3088), (.r14, 3096), (.r15, 3104), (.rbx, 3112)]

/-- Save them through `rcx` (`scratch`). -/
def save : List Instr := slots.map fun p => .store (at_ .rcx p.2) p.1

/-- Load them back through `rbx` (`scratch`). -/
def restore : List Instr := slots.map fun p => .mov p.1 (.mem (at_ .rbx p.2))

/-- The table of the products, and the accumulator at `rbp` zeroed. -/
def start (B : Bodies) : Prog isa :=
  .seq (.block ([.mov .rcx (.reg .rbx)] ++ B.tab ++ [.mov .rdi (.reg .rbp)])) B.zero

/-- A term of the sum: `NTT(u'[j])` to `scratch + 1024`, and its product with
`ŝ[j]` added to the accumulator; then the next `j`. -/
def term (B : Bodies) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .r13), .mov .rsi (.reg .rbx), .mov .r10 (.reg .rbx), .alu .add .r10 (.imm 1024)])
    (.seq B.nttO (.seq (.block [.mov .rdi (.reg .rbp), .mov .rsi (.reg .r12), .mov .rdx (.reg .rbx),
      .alu .add .rdx (.imm 1024), .mov .rcx (.reg .rbx)])
    (.seq (B.mulAcc 0) (.block [.alu .add .r12 (.imm 1024), .alu .add .r13 (.imm 1024), .alu .sub .r14 (.imm 1)]))))


/-! ### `vg_mlkem*_encrypt_mul` -/

/-- A term of sum `o`: `f ×_T ŷ[j]`, with `f` at `rsi` (set by `fs`) and
`ŷ[j]` at `scratch + 1024`, added to the accumulator of `u[o]` (at
`rbp + 1024 o`). -/
def prodAcc (B : Bodies) (fs : List Instr) (o : Nat) : Prog isa :=
  .seq (.block ([.mov .rdi (.reg .rbp), .alu .add .rdi (.imm (BitVec.ofNat 32 (1024 * o)))] ++ fs ++
      [.mov .rdx (.reg .rbx), .alu .add .rdx (.imm 1024), .mov .rcx (.reg .rbx)])) (B.mulAcc o)

/-- The terms `j` of the sums `i, …, i + n - 1` of `Â^⊺ ∘ ŷ`: `Â[j, i] ×_T ŷ[j]`, with row `j` of `Â`
at `r12`. -/
def innerE (B : Bodies) : Nat → Nat → Prog isa
  | _, 0 => .block []
  | i, n + 1 => .seq (prodAcc B [.mov .rsi (.reg .r12), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * i)))] i)
    (innerE B (i + 1) n)

/-- The terms `j`: `ŷ[j] = NTT(y[j])` to `scratch + 1024`, those of the `k`
sums of `Â^⊺ ∘ ŷ`, and that of `t̂^⊺ ∘ ŷ` (`t̂[j]` at `r15`); then the next `j`. -/
def termE (B : Bodies) (k : Nat) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .r13), .mov .rsi (.reg .rbx), .mov .r10 (.reg .rbx), .alu .add .r10 (.imm 1024)])
    (.seq B.nttO (.seq (innerE B 0 k) (.seq (prodAcc B [.mov .rsi (.reg .r15)] k)
      (.block [.alu .add .r12 (.imm (BitVec.ofNat 32 (1024 * k))), .alu .add .r13 (.imm 1024),
        .alu .add .r15 (.imm 1024), .alu .sub .r14 (.imm 1)]))))

/-- `NTT⁻¹` of each of the `k + 1` sums. -/
def invE (B : Bodies) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .rbp), .mov .rsi (.reg .rbx)])
    (.seq B.inv (.block [.alu .add .rbp (.imm 1024), .alu .sub .r15 (.imm 1)]))

/-- Save the callee-saved registers through `r8` (`scratch`). -/
def saveE : List Instr := slots.map fun p => .store (at_ .r8 p.2) p.1

/-- The accumulators of `u[i], …, u[i + n - 1]` (at `rbp + 1024 i`, …) zeroed. -/
def zeroE (B : Bodies) : Nat → Nat → Prog isa
  | _, 0 => .block []
  | i, n + 1 => .seq (.seq (.block [.mov .rdi (.reg .rbp), .alu .add .rdi (.imm (BitVec.ofNat 32 (1024 * i)))])
    B.zero) (zeroE B (i + 1) n)

/-- The table of the products, and the `k + 1` accumulators zeroed. -/
def startE (B : Bodies) (k : Nat) : Prog isa :=
  .seq (.block ([.mov .rcx (.reg .rbx)] ++ B.tab)) (zeroE B 0 (k + 1))

end KpkeMul

open KpkeMul in
/-- `vg_mlkem*_decrypt_mul` of rank `k`, with the code of `B`. -/
def decryptMul (B : Bodies) (k : Nat) : Prog isa :=
  .seq (.block (save ++ [.mov .rbx (.reg .rcx), .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx),
      .mov32 .r14 (.imm (BitVec.ofNat 32 k))]))
    (.seq (withMxcsr .rbx oMx (.seq (start B) (.seq (.loop (term B) .ne)
      (.seq (.block [.mov .rdi (.reg .rbp), .mov .rsi (.reg .rbx)]) B.inv))))
    (.block restore))

open KpkeMul in
/-- `vg_mlkem*_encrypt_mul` of rank `k`, with the code of `B`. -/
def encryptMul (B : Bodies) (k : Nat) : Prog isa :=
  .seq (.block (saveE ++ [.mov .rbx (.reg .r8), .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rcx),
      .mov .r15 (.reg .rdx), .mov32 .r14 (.imm (BitVec.ofNat 32 k))]))
    (.seq (withMxcsr .rbx oMx (.seq (startE B k) (.seq (.loop (termE B k) .ne)
      (.seq (.block [.mov32 .r15 (.imm (BitVec.ofNat 32 (k + 1)))]) (.loop (invE B) .ne)))))
    (.block restore))

end VG.Impl.MlKem.X86_64
