module

public import VerifiedGarbage.Proof.Sha3.RISCV64.Contract
public import VerifiedGarbage.Impl.Sha3.RISCV64.Stream
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Contract
meta import VerifiedGarbage.Impl.Sha3.RISCV64.Stream
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# The SHA-3 sponge on RISC-V: `Verified`

`absorb`, `pad` and `squeeze` (`Stream/`): correctness, constant time (by
taint tracking, `taint_decide`), and a state satisfying each precondition,
against the per-target contracts, then moved to the shared ones of
`Spec/Sha3/Contract.lean` with the stack they use: their frame and the
permutation's (608 bytes).
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Stream

open VG VG.RISCV64

/-! ## `absorb` -/

theorem absorb_ct : ConstantTime isa Proof.Sha3.absorbRISCV64.pre Proof.Sha3.absorbRISCV64.pub
    Impl.Sha3.RISCV64.Stream.absorb := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, h4, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4]

/-- A state satisfying `absorb`'s precondition, with no data. -/
def absorbSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 72 | .a3 => 0x2000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 200⟩]

theorem absorb_verified' :
    Verified RISCV64.target Impl.Sha3.RISCV64.Stream.absorb Proof.Sha3.absorbRISCV64 := by
  refine ⟨fun s hs => ?_, absorb_ct, absorbSat, rfl, rfl, ?_, by decide, by decide, ?_, ?_,
    by decide, by decide⟩
  · obtain ⟨t, s', he, h⟩ := Absorb.correct (Absorb.pre_of hs)
    exact ⟨t, s', he, h⟩
  all_goals exact Region.disjoint_of_sep (by decide)

theorem absorb_verified :
    Verified RISCV64.target Impl.Sha3.RISCV64.Stream.absorb (Spec.Sha3.absorbContract RISCV64.abi 1168) :=
  absorb_verified'.of_implies (by
    contract_implies [Spec.Sha3.absorbContract, Spec.Sha3.absorbSig, Spec.Sha3.absorbPre,
      Spec.Sha3.absorbPost, Proof.Sha3.absorbRISCV64, RISCV64.abi, RISCV64.argRegs] [absorbSat]
      using absorbSat)

/-! ## `pad` -/

theorem pad_ct : ConstantTime isa Proof.Sha3.padRISCV64.pre Proof.Sha3.padRISCV64.pub
    Impl.Sha3.RISCV64.Stream.pad := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h0, h1, h2]

/-- A state satisfying `pad`'s precondition. -/
def padSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 136 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩]

theorem pad_verified' :
    Verified RISCV64.target Impl.Sha3.RISCV64.Stream.pad Proof.Sha3.padRISCV64 := by
  refine ⟨fun s hs => ?_, pad_ct, padSat, rfl, rfl, by decide, by decide, ?_, by decide, by decide⟩
  · obtain ⟨t, s', he, h⟩ := Pad.correct (Pad.pre_of hs)
    exact ⟨t, s', he, h⟩
  · exact Region.disjoint_of_sep (by decide)

theorem pad_verified :
    Verified RISCV64.target Impl.Sha3.RISCV64.Stream.pad (Spec.Sha3.padContract RISCV64.abi 1136) :=
  pad_verified'.of_implies (by
    contract_implies [Spec.Sha3.padContract, Spec.Sha3.padSig, Spec.Sha3.padPre, Spec.Sha3.padPost,
      Proof.Sha3.padRISCV64, RISCV64.abi, RISCV64.argRegs] [padSat] using padSat)

/-! ## `squeeze` -/

theorem squeeze_ct : ConstantTime isa Proof.Sha3.squeezeRISCV64.pre Proof.Sha3.squeezeRISCV64.pub
    Impl.Sha3.RISCV64.Stream.squeeze := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, h4, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4]

/-- A state satisfying `squeeze`'s precondition, with no output. -/
def squeezeSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 72 | .a3 => 0x2000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩]

theorem squeeze_verified' :
    Verified RISCV64.target Impl.Sha3.RISCV64.Stream.squeeze Proof.Sha3.squeezeRISCV64 := by
  refine ⟨fun s hs => ?_, squeeze_ct, squeezeSat, rfl, rfl, ?_, by decide, by decide, ?_, ?_,
    by decide, by decide⟩
  · obtain ⟨t, s', he, h⟩ := Squeeze.correct (Squeeze.pre_of hs)
    exact ⟨t, s', he, h⟩
  all_goals exact Region.disjoint_of_sep (by decide)

theorem squeeze_verified :
    Verified RISCV64.target Impl.Sha3.RISCV64.Stream.squeeze
      (Spec.Sha3.squeezeContract RISCV64.abi 1168) :=
  squeeze_verified'.of_implies (by
    contract_implies [Spec.Sha3.squeezeContract, Spec.Sha3.squeezeSig, Spec.Sha3.squeezePre,
      Spec.Sha3.squeezePost, Proof.Sha3.squeezeRISCV64, RISCV64.abi, RISCV64.argRegs] [squeezeSat]
      using squeezeSat)

end VG.Proof.Sha3.RISCV64.Stream
