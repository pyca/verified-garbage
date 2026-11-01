module

public import VerifiedGarbage.Proof.Blake2.RISCV64.Contract
public import VerifiedGarbage.Impl.Blake2.RISCV64
public import VerifiedGarbage.Spec.Blake2.Contract
public import VerifiedGarbage.Proof.Blake2.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Blake2.RISCV64.Round
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Blake2.RISCV64.Compress
import VerifiedGarbage.Proof.Blake2.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Blake2.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Blake2.RISCV64.Contract
meta import VerifiedGarbage.Impl.Blake2.RISCV64
meta import VerifiedGarbage.Spec.Blake2.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# BLAKE2 compression function on RISC-V: `Verified`

Correctness (`Compress.lean`), constant time (by taint tracking,
`taint_decide`), and a state satisfying the precondition, against
`Proof.Blake2.compressRISCV64`, then moved to the shared contracts of
`Spec/Blake2/Contract.lean`.
-/

@[expose] public section

namespace VG.Proof.Blake2.RISCV64

open VG VG.RISCV64

theorem rok_b : ROk (z := .d) Spec.Blake2.b := by unfold ROk; decide
theorem rok_s : ROk (z := .w) Spec.Blake2.s := by unfold ROk; decide

theorem compress_correct {z : Size} (P : Spec.Blake2.Params z.bits) (hR : ROk P) :
    ∀ s, (compressRISCV64 P).pre s → ∃ t s', Exec isa (Impl.Blake2.RISCV64.compress P) s t s' ∧
      abiPreserved s s' ∧ (compressRISCV64 P).post s s' := fun s hs => by
  obtain ⟨t, s', he, h₁, hra, h₂⟩ := correct P hR (pre_of P s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, hra⟩, h₂⟩

theorem agree_pub {w : Nat} (P : Spec.Blake2.Params w) :
    ∀ s₁ s₂, (compressRISCV64 P).pre s₁ → (compressRISCV64 P).pre s₂ →
      (compressRISCV64 P).pub s₁ s₂ → taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a5]) s₁ s₂ := by
  rintro s₁ s₂ - - ⟨h0, h1, h2, -, -, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h5]

theorem compressB_ct : ConstantTime isa (compressRISCV64 Spec.Blake2.b).pre
    (compressRISCV64 Spec.Blake2.b).pub (Impl.Blake2.RISCV64.compress Spec.Blake2.b) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a5]) (agree_pub _)
    (by taint_decide)

theorem compressS_ct : ConstantTime isa (compressRISCV64 Spec.Blake2.s).pre
    (compressRISCV64 Spec.Blake2.s).pub (Impl.Blake2.RISCV64.compress Spec.Blake2.s) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a5]) (agree_pub _)
    (by taint_decide)

/-- A state satisfying the precondition (with no blocks). -/
def satState (n : Nat) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a5 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, n⟩, ⟨0x3000, 512⟩]

theorem compressB_verified' :
    Verified RISCV64.target (Impl.Blake2.RISCV64.compress Spec.Blake2.b) (compressRISCV64 Spec.Blake2.b) :=
  ⟨compress_correct (z := .d) _ rok_b, compressB_ct, satState 64, rfl, rfl,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide)⟩

theorem compressS_verified' :
    Verified RISCV64.target (Impl.Blake2.RISCV64.compress Spec.Blake2.s) (compressRISCV64 Spec.Blake2.s) :=
  ⟨compress_correct (z := .w) _ rok_s, compressS_ct, satState 32, rfl, rfl,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide)⟩

theorem compressB_verified :
    Verified RISCV64.target (Impl.Blake2.RISCV64.compress Spec.Blake2.b)
      (Proof.Blake2.compressBContract RISCV64.abi) :=
  compressB_verified'.of_implies (by
    sig_implies [Proof.Blake2.compressBContract, Proof.Blake2.compressBSig, compressRISCV64,
      RISCV64.abi, RISCV64.argRegs, Spec.Blake2.blockBytes] [satState] using satState 64)

theorem compressS_verified :
    Verified RISCV64.target (Impl.Blake2.RISCV64.compress Spec.Blake2.s)
      (Proof.Blake2.compressSContract RISCV64.abi) :=
  compressS_verified'.of_implies (by
    sig_implies [Proof.Blake2.compressSContract, Proof.Blake2.compressSSig, compressRISCV64,
      RISCV64.abi, RISCV64.argRegs, Spec.Blake2.blockBytes] [satState] using satState 32)

end VG.Proof.Blake2.RISCV64
