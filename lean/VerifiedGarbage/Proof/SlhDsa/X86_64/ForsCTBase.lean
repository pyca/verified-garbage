module

-- separate module: the taint checks of `forsSign`'s blocks, rebuilt only when its blocks change

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkForsCTBase
public import VerifiedGarbage.Proof.SlhDsa.X86_64.ForsFront
public meta import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkForsCTBase
public meta import VerifiedGarbage.Proof.SlhDsa.X86_64.ForsFront
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# SLH-DSA (SHAKE) on x86-64: `forsSign` is constant time, its blocks

The taint analysis checks each block of `forsSign` from the registers both
runs agree on, for each of the six parameter sets (`ForsCT.P6`). A block
that loads a variable of frame 2 that it then uses in an address is checked
in two parts: the load, then the rest with the loaded register public, which
the runs agree on by correctness (`RelCT.block_append`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Fors

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.X86_64 (Layout setField setFieldR copyWords)
open VG.Impl.SlhDsa.X86_64.Fors
open VG.Proof.SlhDsa.X86_64.ForsCT (P6)

section
variable {P : State → State → Prop}

/-- A load of a variable of frame 2. -/
theorem ct_load (r : Reg) (i : Nat) (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block [.mov r (.mem (var i))]) fun _ _ => True :=
  Levels.taintR _ h (hc := .block []) (by kernel_rfl)

/-- An empty block. -/
theorem ct_nil : RelCT isa P (.block []) fun _ _ => True :=
  Levels.taintR [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (hc := .block []) (by kernel_rfl)

/-- Variable 3 ← 0. -/
theorem ct_zero3 (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block [.mov32 .rax (.imm 0), .store (var 3) .rax]) fun _ _ => True :=
  Levels.taintR _ h (by taint_decide)

/-- The tree's index, from `rax` = the tree. -/
theorem ct_fidx (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx, .rax], x.gpr r = y.gpr r) :
    RelCT isa P (.block [.mov .r13 (.mem fidx), .mov .rsi (.mem (var 1))]) fun _ _ => True :=
  Levels.taintR _ h (hc := .block []) (by kernel_rfl)

variable {p : Params} (hp : P6 p)
include hp

/-- The lanes for the private key values. -/
theorem ct_lanesA (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (([.mov .r10 (.mem (var 4)), .alu .add .r10 (.mem (var 2)), .alu .add .r10 (.mem (var 3))] : List Instr) ++
      (List.range 4).flatMap (fun k' => leafAdrs ⟨p.n, p.len⟩ 6 k' ++
        copyWords .rbx (Layout.laneA k' + (⟨p.n, p.len⟩ : Impl.SlhDsa.X86_64.Layout).msgOff) .rbx Layout.oSkSeed
          ((⟨p.n, p.len⟩ : Impl.SlhDsa.X86_64.Layout).n / 8)))) fun _ _ => True := by
  simp only [Impl.SlhDsa.X86_64.Layout.msgOff]
  rw [show leafAdrs ⟨p.n, p.len⟩ = leafAdrs ⟨p.n, 0⟩ from rfl]
  rcases hp with ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ <;>
    rw [hn] <;> exact Levels.taintR _ h (by taint_decide)

/-- The capture of the private key values, after `rsi` = the signature. -/
theorem ct_capture (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx, .rsi], x.gpr r = y.gpr r) :
    RelCT isa P (.block (([.mov .rdx (.mem (var 2)), .alu .add .rdx (.mem (var 3))] : List Instr) ++
      (List.range 4).flatMap (captureSk ⟨p.n, p.len⟩) ++
      (List.range 4).flatMap (fun k' => setField .rbx (Layout.laneA k' +
        (⟨p.n, p.len⟩ : Impl.SlhDsa.X86_64.Layout).adrsOff + 16) 3))) fun _ _ => True := by
  simp only [Impl.SlhDsa.X86_64.Layout.adrsOff]
  rw [show captureSk ⟨p.n, p.len⟩ = captureSk ⟨p.n, 0⟩ from rfl]
  rcases hp with ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ <;>
    rw [hn] <;> exact Levels.taintR _ h (by taint_decide)

/-- The leaves to the nodes, after `rdx` = the leaf `j`. -/
theorem ct_out (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx, .rdx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.Wots.mulN (⟨p.n, p.len⟩ : Impl.SlhDsa.X86_64.Layout).n .rdx .rcx ++
      ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
      (List.range 4).flatMap (fun k' => copyWords .rdx (Layout.oN + (⟨p.n, p.len⟩ : Impl.SlhDsa.X86_64.Layout).n * k')
        .rbx (Layout.laneA k' + (⟨p.n, p.len⟩ : Impl.SlhDsa.X86_64.Layout).msgOff)
        ((⟨p.n, p.len⟩ : Impl.SlhDsa.X86_64.Layout).n / 8)) ++
      ([.mov .rax (.mem (var 3)), .alu .add .rax (.imm 4), .store (var 3) .rax,
        .alu .cmp .rax (.imm (BitVec.ofNat 32 (2 ^ s p.a)))] : List Instr))) fun _ _ => True := by
  simp only [Impl.SlhDsa.X86_64.Layout.msgOff, s]
  rcases hp with ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ <;>
    rw [hn, ha] <;> exact Levels.taintR _ h (by taint_decide)

/-- The parameters of `levels` for a subtree. -/
theorem ct_subB (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (([.mov .r10 (.mem (var 1)),
      .alu .add .r10 (.imm (BitVec.ofNat 32 (⟨p.n, p.len⟩ : Impl.SlhDsa.X86_64.Layout).n)),
      .mov .rcx (.mem (var 4)), .alu .add .rcx (.mem (var 2))] : List Instr) ++
      Impl.SlhDsa.X86_64.Tree.setParams (.mem (var 2)) (.reg .rcx) (.imm 3) (.reg .r12) ++
      ([.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 Layout.oN)),
        .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ s p.a))), .mov32 .rcx (.imm 0),
        .mov .r8 (.reg .r10), .mov .r9 (.reg .r13)] : List Instr))) fun _ _ => True := by
  simp only [s]
  rcases hp with ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ <;>
    rw [hn, ha] <;> exact Levels.taintR _ h (by taint_decide)

/-- The subtree's root to the subtree roots, after `rdx` = its first leaf. -/
theorem ct_rootCopy (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx, .rdx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (([.shift .shr .rdx (s p.a)] : List Instr) ++
      Impl.SlhDsa.X86_64.Wots.mulN (⟨p.n, p.len⟩ : Impl.SlhDsa.X86_64.Layout).n .rdx .rcx ++
      ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
      copyWords .rdx Layout.oRoots .rbx Layout.oN ((⟨p.n, p.len⟩ : Impl.SlhDsa.X86_64.Layout).n / 8)))
      fun _ _ => True := by
  simp only [s]
  rcases hp with ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ <;>
    rw [hn, ha] <;> exact Levels.taintR _ h (by taint_decide)

/-- The next subtree. -/
theorem ct_next2 (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block [.mov .rax (.mem (var 2)), .alu .add .rax (.imm (BitVec.ofNat 32 (2 ^ s p.a))),
      .store (var 2) .rax, .alu .cmp .rax (.imm (BitVec.ofNat 32 (2 ^ p.a)))]) fun _ _ => True := by
  simp only [s]
  rcases hp with ⟨-, ha, -⟩ | ⟨-, ha, -⟩ | ⟨-, ha, -⟩ | ⟨-, ha, -⟩ | ⟨-, ha, -⟩ | ⟨-, ha, -⟩ <;>
    rw [ha] <;> exact Levels.taintR _ h (hc := .block []) (by kernel_rfl)

/-- The tree's signature zeroed, after `rsi` = it. -/
theorem ct_zeroSig (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx, .rsi], x.gpr r = y.gpr r) :
    RelCT isa P (.block (([.mov32 .rax (.imm 0)] : List Instr) ++
      (List.range ((p.a + 1) * (⟨p.n, p.len⟩ : Impl.SlhDsa.X86_64.Layout).n / 8)).map
        (fun w => .store (Impl.Sha3.X86_64.at_ .rsi (8 * w)) .rax) ++ ([.store (var 2) .rax] : List Instr))) fun _ _ => True := by
  dsimp only
  rcases hp with ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ <;>
    rw [hn, ha] <;> exact Levels.taintR _ h (by taint_decide)

/-- The parameters of `levels` above the subtrees. -/
theorem ct_topB (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (copyWords .rbx Layout.oN .rbx Layout.oRoots
        (2 ^ (p.a - s p.a) * (⟨p.n, p.len⟩ : Impl.SlhDsa.X86_64.Layout).n / 8) ++
      ([.mov .r10 (.mem (var 1)), .alu .add .r10 (.imm (BitVec.ofNat 32 ((⟨p.n, p.len⟩ : Impl.SlhDsa.X86_64.Layout).n +
        s p.a * (⟨p.n, p.len⟩ : Impl.SlhDsa.X86_64.Layout).n)))] : List Instr) ++
      Impl.SlhDsa.X86_64.Tree.setParams (.imm 0) (.mem (var 4)) (.imm 3) (.reg .r12) ++
      ([.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 Layout.oN)),
        .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ (p.a - s p.a)))), .mov32 .rcx (.imm (BitVec.ofNat 32 (s p.a))),
        .mov .r8 (.reg .r10), .mov .r9 (.reg .r13)] : List Instr))) fun _ _ => True := by
  simp only [s]
  rcases hp with ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ <;>
    rw [hn, ha] <;> exact Levels.taintR _ h (by taint_decide)

/-- The tree's root to lane 0 of the lanes `B`, after `rdx` = the tree. -/
theorem ct_rootB (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx, .rdx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.Wots.mulN (⟨p.n, p.len⟩ : Impl.SlhDsa.X86_64.Layout).n .rdx .rcx ++
      ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
      copyWords .rdx (Layout.laneB 0 + (⟨p.n, p.len⟩ : Impl.SlhDsa.X86_64.Layout).msgOff) .rbx (rootOff p.a)
        ((⟨p.n, p.len⟩ : Impl.SlhDsa.X86_64.Layout).n / 8))) fun _ _ => True := by
  simp only [Impl.SlhDsa.X86_64.Layout.msgOff, rootOff, s]
  rcases hp with ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ <;>
    rw [hn, ha] <;> exact Levels.taintR _ h (by taint_decide)

/-- The next tree. -/
theorem ct_treeEnd (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block [.mov .rax (.mem (var 1)),
      .alu .add .rax (.imm (BitVec.ofNat 32 ((p.a + 1) * (⟨p.n, p.len⟩ : Impl.SlhDsa.X86_64.Layout).n))),
      .store (var 1) .rax, .mov .rax (.mem (var 4)), .alu .add .rax (.imm (BitVec.ofNat 32 (2 ^ p.a))),
      .store (var 4) .rax, .mov .rax (.mem (var 0)), .alu .add .rax (.imm 1), .store (var 0) .rax,
      .alu .cmp .rax (.imm (BitVec.ofNat 32 p.k))]) fun _ _ => True := by
  rcases hp with ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ <;>
    rw [hn, ha, hk] <;> exact Levels.taintR _ h (hc := .block []) (by kernel_rfl)

end

end VG.Proof.SlhDsa.X86_64.Fors
