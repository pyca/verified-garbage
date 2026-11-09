module

import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Ecb
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.TripleDes.Scratch
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Bitsliced
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Lit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Ecb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.TripleDes.Scratch
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.Bitsliced
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# Bitsliced Triple DES ECB on PPC64LE meets its contract

The proof is written against `contract`, the ECB contract with the scratch
buffer as an argument (`Proof.TripleDes.ecbScratchContract`), which the
registration puts in its frame (`Proof/TripleDes/PPC64LE/Frame.lean`), as
for the block-at-a-time ECB it replaces (`Ecb/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Bitsliced

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE.Bitslice
open VG.Spec.TripleDes (Direction)

/-- The public registers: the arguments, and the stack pointer. -/
def Pub (s₁ s₂ : State) : Prop := s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r3, .r4, .r5, .r6], s₁.gpr r = s₂.gpr r

/-- The ECB contract as the code sees it. -/
def contract (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 384⟩
    let data : Region := ⟨s.gpr .r4, 8 * (s.gpr .r5).toNat⟩
    let buf : Region := ⟨s.gpr .r6, 1024⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧ (s.gpr .r4).toNat + 8 * (s.gpr .r5).toNat ≤ 2 ^ 64
  post s s' :=
    Spec.TripleDes.blocksAt s'.mem (s.gpr .r4) (s.gpr .r5).toNat =
      Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)) d
        (Spec.TripleDes.blocksAt s.mem (s.gpr .r4) (s.gpr .r5).toNat)
  pub := Pub

theorem ecb_correct (d : Direction) (s : State) (hs : (contract d).pre s) :
    ∃ t s', Exec isa (ecb d) s t s' ∧ abiPreserved s s' ∧ (contract d).post s s' := by
  obtain ⟨rd, wr, kd, kb, db, fit⟩ := hs
  have pre : EcbPre s :=
    ⟨⟨_, List.mem_append_left _ (by rw [rd]; exact List.mem_singleton_self _), Region.contains_self _ _⟩,
      covers_of_in ⟨_, by rw [wr]; exact List.mem_cons_self, Region.contains_self _ _⟩,
      ⟨_, by rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩,
      kd, kb, db, fit⟩
  obtain ⟨t, s', he, hp, hl, -, -, hb⟩ := ecb_wp d pre
  exact ⟨t, s', he, ⟨hp, Exec.sp he, hl⟩, VG.Proof.TripleDes.Bitslice.ecb_blocks _ _ _ _ _ _ hb⟩

theorem ecb_constantTime (d : Direction) (pre : State → Prop) :
    ConstantTime isa pre Pub (ecb d) := by
  cases d
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ hp
    exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ hp
    exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1024⟩]

theorem pub_iff (s₁ s₂ : State) : Pub s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
      s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 := by
  simp [Pub]

theorem encrypt_verified : Verified target encrypt (Proof.TripleDes.ecbEncryptScratchContract abi 0) := by
  refine Verified.of_correct (k := contract .encrypt) (ecb_correct .encrypt) (ecb_constantTime .encrypt _) ?_
  sig_implies [Proof.TripleDes.ecbEncryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, contract,
    pub_iff] [satState] using satState

theorem decrypt_verified : Verified target decrypt (Proof.TripleDes.ecbDecryptScratchContract abi 0) := by
  refine Verified.of_correct (k := contract .decrypt) (ecb_correct .decrypt) (ecb_constantTime .decrypt _) ?_
  sig_implies [Proof.TripleDes.ecbDecryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, contract,
    pub_iff] [satState] using satState

end VG.Proof.TripleDes.PPC64LE.Bitsliced
