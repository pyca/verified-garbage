import VerifiedGarbage.Impl.MlKem.X86_64.NttAvx2
import VerifiedGarbage.Impl.MlKem.X86_64.MulAvx2
import VerifiedGarbage.Impl.MlKem.X86_64.Arith

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
It zeroes `w`; then for each `j`, it computes `NTT(u'[j])` to
`scratch + 1024` (`Bodies.nttO`: the NTT's code, but for the pointer its
last step stores through, `r10`), its product with `ŝ[j]` to
`scratch + 2048`, and adds that to `w`; then `NTT⁻¹(w)`. The code it
inlines uses the first 1024 bytes of `scratch` as their working space.
Every address and branch depends only on the pointers.
-/

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- The code of the polynomial arithmetic of one backend, without the MXCSR
prologue and epilogue of its functions. -/
structure Bodies where
  /-- `NTT` of the polynomial at `rdi` to the one at `r10`, with the working
  space at `rsi`. -/
  nttO : Prog isa
  /-- `NTT⁻¹` of the polynomial at `rdi`, in place, with the working space
  at `rsi`. -/
  inv : Prog isa
  /-- `h = rdi` becomes `f = rsi ×_T g = rdx`, with the working space at
  `rcx`. -/
  mul : Prog isa
  /-- `f = rdi` becomes `f + g`, `g = rsi`. -/
  add : Prog isa

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

/-- `vg_mlkem_ntt_avx2`'s code, storing to `r10`. -/
def nttOBY : Prog isa :=
  .seq (ypro zmTab) (.seq (ylay vbfly 128 1) (.seq (ylay vbfly 64 2) (.seq (ylay vbfly 32 4)
    (.seq (ylay vbfly 16 8) (.seq (ylay8 vbfly 16) (.seq (ylay4 vbfly 32) (.seq (ylay2 vbfly 64)
      (.seq (.block [.mov .rdi (.reg .r10)]) yepi))))))))

/-- `vg_mlkem_inv_ntt_avx2`'s code. -/
def nttInvBY : Prog isa :=
  .seq (ypro zmTabInv) (.seq (ylay2 vibfly 0) (.seq (ylay4 vibfly 64) (.seq (ylay8 vibfly 96)
    (.seq (ylay vibfly 16 112) (.seq (ylay vibfly 32 120) (.seq (ylay vibfly 64 124)
      (.seq (ylay vibfly 128 126) (.seq yscale yepi))))))))

/-- `vg_mlkem_multiply_ntts_avx2`'s code. -/
def mulBY : Prog isa :=
  .seq (.block [.mov .r10 (.reg .rcx)]) (.seq (.block mulProY) (.seq (rcxLoop 8 mulBodyY) (.block [.vop .vzeroupper])))

def Bodies.sse : Bodies := ⟨nttOB, nttInvB, mulB, X86_64.add⟩

def Bodies.avx2 : Bodies := ⟨nttOBY, nttInvBY, mulBY, addAvx2⟩

namespace KpkeMul

/-- The callee-saved registers and where in `scratch` they are saved (`rbx`,
through which they are loaded back, last). -/
def slots : List (Reg × Nat) := [(.rbp, 3072), (.r12, 3080), (.r13, 3088), (.r14, 3096), (.r15, 3104), (.rbx, 3112)]

/-- Save them through `rcx` (`scratch`). -/
def save : List Instr := slots.map fun p => .store (at_ .rcx p.2) p.1

/-- Load them back through `rbx` (`scratch`). -/
def restore : List Instr := slots.map fun p => .mov p.1 (.mem (at_ .rbx p.2))

/-- The polynomial at `rbp`, zeroed, sixteen bytes at a time. -/
def zeroW : Prog isa :=
  .seq (.block [xb .pxor .xmm0 .xmm0, .mov .rdi (.reg .rbp)])
    (rcxLoop 64 [.movdquStore (at_ .rdi 0) .xmm0, .alu .add .rdi (.imm 16)])

/-- A term of the sum: `NTT(u'[j])` to `scratch + 1024`, its product with
`ŝ[j]` to `scratch + 2048`, added to `w`; then the next `j`. -/
def term (B : Bodies) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .r13), .mov .rsi (.reg .rbx), .mov .r10 (.reg .rbx), .alu .add .r10 (.imm 1024)])
    (.seq B.nttO (.seq (.block [.mov .rdi (.reg .rbx), .alu .add .rdi (.imm 2048), .mov .rsi (.reg .r12),
      .mov .rdx (.reg .rbx), .alu .add .rdx (.imm 1024), .mov .rcx (.reg .rbx)])
    (.seq B.mul (.seq (.block [.mov .rdi (.reg .rbp), .mov .rsi (.reg .rbx), .alu .add .rsi (.imm 2048)])
      (.seq B.add (.block [.alu .add .r12 (.imm 1024), .alu .add .r13 (.imm 1024), .alu .sub .r14 (.imm 1)]))))))


/-! ### `vg_mlkem*_encrypt_mul` -/

/-- A term of sum `o`: `f ×_T ŷ[j]`, with `f` at `rsi` (set by `fs`) and
`ŷ[j]` at `scratch + 1024`, to `scratch + 2048`, added to `u[o]` (at
`rbp + 1024 o`). -/
def prodAdd (B : Bodies) (fs : List Instr) (o : Nat) : Prog isa :=
  .seq (.block ([.mov .rdi (.reg .rbx), .alu .add .rdi (.imm 2048)] ++ fs ++
      [.mov .rdx (.reg .rbx), .alu .add .rdx (.imm 1024), .mov .rcx (.reg .rbx)]))
    (.seq B.mul (.seq (.block [.mov .rdi (.reg .rbp), .alu .add .rdi (.imm (BitVec.ofNat 32 (1024 * o))),
      .mov .rsi (.reg .rbx), .alu .add .rsi (.imm 2048)]) B.add))

/-- The terms `j` of the sums `i, …, i + n - 1` of `Â^⊺ ∘ ŷ`: `Â[j, i] ×_T ŷ[j]`, with row `j` of `Â`
at `r12`. -/
def innerE (B : Bodies) : Nat → Nat → Prog isa
  | _, 0 => .block []
  | i, n + 1 => .seq (prodAdd B [.mov .rsi (.reg .r12), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * i)))] i)
    (innerE B (i + 1) n)

/-- The terms `j`: `ŷ[j] = NTT(y[j])` to `scratch + 1024`, those of the `k`
sums of `Â^⊺ ∘ ŷ`, and that of `t̂^⊺ ∘ ŷ` (`t̂[j]` at `r15`); then the next `j`. -/
def termE (B : Bodies) (k : Nat) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .r13), .mov .rsi (.reg .rbx), .mov .r10 (.reg .rbx), .alu .add .r10 (.imm 1024)])
    (.seq B.nttO (.seq (innerE B 0 k) (.seq (prodAdd B [.mov .rsi (.reg .r15)] k)
      (.block [.alu .add .r12 (.imm (BitVec.ofNat 32 (1024 * k))), .alu .add .r13 (.imm 1024),
        .alu .add .r15 (.imm 1024), .alu .sub .r14 (.imm 1)]))))

/-- `NTT⁻¹` of each of the `k + 1` sums. -/
def invE (B : Bodies) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .rbp), .mov .rsi (.reg .rbx)])
    (.seq B.inv (.block [.alu .add .rbp (.imm 1024), .alu .sub .r15 (.imm 1)]))

/-- Save the callee-saved registers through `r8` (`scratch`). -/
def saveE : List Instr := slots.map fun p => .store (at_ .r8 p.2) p.1

/-- The `k + 1` polynomials of `u` (at `rbp`), zeroed, sixteen bytes at a time. -/
def zeroU (k : Nat) : Prog isa :=
  .seq (.block [xb .pxor .xmm0 .xmm0, .mov .rdi (.reg .rbp)])
    (rcxLoop (64 * (k + 1)) [.movdquStore (at_ .rdi 0) .xmm0, .alu .add .rdi (.imm 16)])

end KpkeMul

open KpkeMul in
/-- `vg_mlkem*_decrypt_mul` of rank `k`, with the code of `B`. -/
def decryptMul (B : Bodies) (k : Nat) : Prog isa :=
  .seq (.block (save ++ [.mov .rbx (.reg .rcx), .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx),
      .mov32 .r14 (.imm (BitVec.ofNat 32 k))]))
    (.seq (withMxcsr .rbx oMx (.seq zeroW (.seq (.loop (term B) .ne)
      (.seq (.block [.mov .rdi (.reg .rbp), .mov .rsi (.reg .rbx)]) B.inv))))
    (.block restore))

open KpkeMul in
/-- `vg_mlkem*_encrypt_mul` of rank `k`, with the code of `B`. -/
def encryptMul (B : Bodies) (k : Nat) : Prog isa :=
  .seq (.block (saveE ++ [.mov .rbx (.reg .r8), .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rcx),
      .mov .r15 (.reg .rdx), .mov32 .r14 (.imm (BitVec.ofNat 32 k))]))
    (.seq (withMxcsr .rbx oMx (.seq (zeroU k) (.seq (.loop (termE B k) .ne)
      (.seq (.block [.mov32 .r15 (.imm (BitVec.ofNat 32 (k + 1)))]) (.loop (invE B) .ne)))))
    (.block restore))

end VG.Impl.MlKem.X86_64
