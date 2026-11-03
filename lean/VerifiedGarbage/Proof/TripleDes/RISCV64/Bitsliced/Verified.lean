module

import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Ecb
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.TripleDes.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Bitsliced
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Lit
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Ecb
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.TripleDes.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Impl.TripleDes.RISCV64.Bitsliced
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Lit

/-!
# Bitsliced Triple DES ECB on RISC-V meets its contract

The proof is written against `ecbC`, which states the frame of 1056 bytes
below the stack pointer, and moved to the shared contracts of
`Spec/TripleDes/Contract.lean` with `stack := 1056`.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Bitsliced

open VG VG.RISCV64 VG.Impl.TripleDes.RISCV64.Bitslice
open VG.Spec.TripleDes (Direction)

/-- The ECB contract as the code sees it. -/
def ecbC (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 384⟩
    let data : Region := ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩
    let stack : Region := ⟨s.sp - 1056, 1056⟩
    s.rd = [key] ∧ s.wr = [data] ∧ key.Disjoint data ∧
      (s.gpr .a1).toNat + 8 * (s.gpr .a2).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ 1056 ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint data
  post s s' :=
    Spec.TripleDes.blocksAt s'.mem (s.gpr .a1) (s.gpr .a2).toNat =
      Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (s.gpr .a0)) d
        (Spec.TripleDes.blocksAt s.mem (s.gpr .a1) (s.gpr .a2).toNat)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

theorem ecb_ok (d : Direction) (s : State) (hs : (ecbC d).pre s) :
    ∃ t s', Exec isa (ecb d) s t s' ∧ abiPreserved s s' ∧ (ecbC d).post s s' := by
  obtain ⟨rd, wr, kd, fit, al, sp, sk, sd⟩ := hs
  obtain ⟨t, s', he, hp, hb⟩ := ecb_wp d ⟨rd, wr, kd, fit, al, sp, sk, sd⟩
  exact ⟨t, s', he, hp, VG.Proof.TripleDes.Bitslice.ecb_blocks _ _ _ _ _ _ hb⟩

theorem ecb_agree (d : Direction) : ∀ s₁ s₂, (ecbC d).pre s₁ → (ecbC d).pre s₂ → (ecbC d).pub s₁ s₂ →
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2]) s₁ s₂ := by
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

theorem encrypt_ct : ConstantTime isa (ecbC .encrypt).pre (ecbC .encrypt).pub encrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) (ecb_agree .encrypt)
    (by taint_decide)

theorem decrypt_ct : ConstantTime isa (ecbC .decrypt).pre (ecbC .decrypt).pub decrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) (ecb_agree .decrypt)
    (by taint_decide)

def ecbSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x3000, 0⟩]

theorem encrypt_verified :
    Verified RISCV64.target encrypt (Spec.TripleDes.ecbEncryptContract RISCV64.abi 1056) := by
  refine Verified.of_correct (k := ecbC .encrypt) (ecb_ok .encrypt) encrypt_ct ?_
  contract_implies [Spec.TripleDes.ecbEncryptContract, Spec.TripleDes.ecbContract,
    Spec.TripleDes.ecbSig, Spec.TripleDes.ecbPost, RISCV64.abi, RISCV64.argRegs, ecbC] [ecbSat]
    using ecbSat

theorem decrypt_verified :
    Verified RISCV64.target decrypt (Spec.TripleDes.ecbDecryptContract RISCV64.abi 1056) := by
  refine Verified.of_correct (k := ecbC .decrypt) (ecb_ok .decrypt) decrypt_ct ?_
  contract_implies [Spec.TripleDes.ecbDecryptContract, Spec.TripleDes.ecbContract,
    Spec.TripleDes.ecbSig, Spec.TripleDes.ecbPost, RISCV64.abi, RISCV64.argRegs, ecbC] [ecbSat]
    using ecbSat

end VG.Proof.TripleDes.RISCV64.Bitsliced
