import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Rc4.Contract

/-!
# RC4 on ARMv7: the contracts the proofs use

`Spec.Rc4.initContract` and `Spec.Rc4.applyContract` spelled out for ARMv7:
every argument is in a register, and no stack is used.
-/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Spec.Rc4

def initC : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let ctx : Region := ⟨State.addr (s.gpr .r2), 258⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 64⟩
    s.rd = [key] ∧ s.wr = [ctx, scratch] ∧ key.Disjoint ctx ∧ key.Disjoint scratch ∧
      ctx.Disjoint scratch ∧ (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 258 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 64 ≤ 2 ^ 32
  post s s' :=
    match init (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) with
    | .ok c => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
        contextAt s'.mem (State.addr (s.gpr .r2)) = c
    | .error .invalidKeyLength => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

def applyC : Contract isa where
  pre s :=
    let ctx : Region := ⟨State.addr (s.gpr .r0), 258⟩
    let data : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 64⟩
    s.rd = [] ∧ s.wr = [ctx, data, scratch] ∧ ctx.Disjoint data ∧ ctx.Disjoint scratch ∧
      data.Disjoint scratch ∧ (s.gpr .r0).toNat + 258 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 64 ≤ 2 ^ 32
  post s s' :=
    let result := update (contextAt s.mem (State.addr (s.gpr .r0)))
      (bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
    contextAt s'.mem (State.addr (s.gpr .r0)) = result.1 ∧
      bytesAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat = result.2
  pub s₁ s₂ := (s₁.sp = s₂.sp ∧
      [(contextAt s₁.mem (State.addr (s₁.gpr .r0))).i.toNat] =
        [(contextAt s₂.mem (State.addr (s₂.gpr .r0))).i.toNat]) ∧
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3

/-- `init(0x1000, 1, 0x2000, 0x3000)`. -/
def initSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 258⟩, ⟨0x3000, 64⟩]

/-- `apply(0x1000, 0x2000, 1, 0x3000)`. -/
def applySat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 1 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 258⟩, ⟨0x2000, 1⟩, ⟨0x3000, 64⟩]

end VG.Proof.Rc4.Arm
