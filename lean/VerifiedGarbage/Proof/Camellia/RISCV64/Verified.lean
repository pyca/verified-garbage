module

public import VerifiedGarbage.Proof.Camellia.RISCV64.Ecb
public import VerifiedGarbage.Proof.Camellia.Scratch
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Camellia.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Camellia.RISCV64.Ecb
meta import VerifiedGarbage.Proof.Camellia.Scratch
meta import VerifiedGarbage.Impl.StackScratch.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Camellia.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint

/-!
# Camellia ECB on RISC-V meets its contracts

`ecb_verified`: `ecb dir` is correct (`ecb_wp`) and constant time, by the
taint analysis: the pointers, `rounds`, `n` and the stack pointer are
public, and so is everything the code computes from them, which it keeps in
registers (`a0`–`a5`, the copies' pointers and counts and the loop tests).
`ecb_framed` runs it with its working space on the stack, zeroed on return:
3200 bytes, for the 400 words of the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.Impl.Camellia.RISCV64

theorem ecbTaint_agree (dir : Dir) (s₁ s₂ : State) (_ : (ecbRISCV64 dir).pre s₁) (_ : (ecbRISCV64 dir).pre s₂)
    (hp : (ecbRISCV64 dir).pub s₁ s₂) : taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ecb_ct (dir : Dir) : ConstantTime isa (ecbRISCV64 dir).pre (ecbRISCV64 dir).pub (ecb dir) := by
  cases dir
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
      (ecbTaint_agree .encrypt) (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
      (ecbTaint_agree .decrypt) (by taint_decide)

/-- The registers ECB writes. -/
def ecbWrites : List Reg :=
  [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7,
   .s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11]

theorem preserved_sreg : ∀ r ∈ preserved, ∃ i < 12, sreg i = r := by decide

theorem ecb_correct (dir : Dir) (s : State) (hs : (ecbRISCV64 dir).pre s) :
    ∃ t s', Exec isa (ecb dir) s t s' ∧ abiPreserved s s' ∧ (ecbRISCV64 dir).post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, hk⟩ := WP.keep ecbWrites (ecb_wp dir hs) (by cases dir <;> lit_decide)
    (by cases dir <;> lit_decide)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, hk.gpr (by decide)⟩, h₂⟩
  obtain ⟨i, hi, rfl⟩ := preserved_sreg r hr
  exact h₁ i hi

/-- A state satisfying the precondition (one block). -/
def ecbSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 18 | .a2 => 0x3000 | .a3 => 1 | .a4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 8 * 400⟩]

theorem ecb_verified (dir : Dir) :
    Verified target (ecb dir) (Proof.Camellia.ecbScratchContract abi (specDir dir) slots) :=
  Verified.of_correct (ecb_correct dir) (ecb_ct dir) (by
    cases dir <;>
    sig_implies [Proof.Camellia.ecbScratchContract, Proof.Camellia.ecbScratchSig, Spec.Camellia.ecbSig,
      Spec.Camellia.ecbPre, Spec.Camellia.ecbPost, ecbRISCV64, specDir, abi, argRegs, slots, tailSlot, savedSlot,
      keySlot] [ecbSat] using ecbSat)

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000`, one block at `0x3000`, 18 rounds. -/
def ecbFrameSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 18 | .a2 => 0x3000 | .a3 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x3000, 16⟩]

theorem ecbFrameSat_pre (d : Spec.Camellia.Direction) :
    ∃ s, (Spec.Camellia.ecbContract abi d 3200).pre s := by
  implies_sat [Spec.Camellia.ecbContract, Spec.Camellia.ecbSig, Spec.Camellia.ecbPre, Spec.Camellia.ecbPost, abi,
    argRegs] [ecbFrameSat] using ecbFrameSat

/-- ECB in the direction `dir`, with its working space on the stack. -/
theorem ecb_framed (dir : Dir) :
    Verified target (Impl.StackScratch.RISCV64.withStackScratchWiped 3200 .a4 400 (ecb dir))
      (Spec.Camellia.ecbContract abi (specDir dir) 3200) :=
  Verified.stackScratchWiped (sig := Spec.Camellia.ecbSig) (nm := "scratch") (e := .u64)
    (n := 400) (pre := Spec.Camellia.ecbPre abi.ptrBits)
    (post := Spec.Camellia.ecbPost (specDir dir) abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 3200) (words := 400) (by rw [← Proof.Camellia.ecbScratchContract_eq]; exact ecb_verified dir)
    (by decide) (by decide) (by decide) (Proof.Camellia.ecbPostOut_local _ _) (ecbFrameSat_pre _)

end VG.Proof.Camellia.RISCV64
