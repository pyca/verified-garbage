module

import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Loop
public import VerifiedGarbage.Proof.TripleDes.AArch64.ConstantTime
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.TripleDes.Scratch
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Lit
public import VerifiedGarbage.Impl.TripleDes.AArch64.Bitsliced
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit
import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
import VerifiedGarbage.Proof.TripleDes.SboxTables

/-! ### `TripleDes.AArch64.Ecb.Contract`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.Ecb

open VG VG.AArch64

def contract (d : Spec.TripleDes.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 384⟩
    let data : Region := ⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩
    let buf : Region := ⟨s.gpr .x3, 1024⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧
      (s.gpr .x1).toNat + 8 * (s.gpr .x2).toNat ≤ 2 ^ 64
  post s s' :=
    Spec.TripleDes.blocksAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
      Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)) d
        (Spec.TripleDes.blocksAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  pub := PublicRegs [.x0, .x1, .x2, .x3]

end VG.Proof.TripleDes.AArch64.Ecb

end

end


/-! # The AdvSIMD bitsliced ECB functions meet their contracts -/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.Impl.TripleDes.AArch64.BitsliceNeon VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (blockOut wAt wAt_wAt blockAt_frame ecb_blocks)
open VG.Proof.TripleDes.AArch64.Ecb (contract)

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1024⟩]

theorem publicRegs_four (s₁ s₂ : State) :
    VG.Proof.TripleDes.AArch64.PublicRegs [.x0, .x1, .x2, .x3] s₁ s₂ ↔
      s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
        s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 := by
  simp [VG.Proof.TripleDes.AArch64.PublicRegs]

theorem ecb_contract (d : Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (ecb d) s (fun s' => (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyData, keyBuf, dataBuf, fit⟩ := hs
  exact WP.mono (ecb_correct d ⟨hrd, hwr, keyData, keyBuf, dataBuf, fit⟩) fun s' h =>
    ecb_blocks _ _ _ _ _ _ h

end VG.Proof.TripleDes.AArch64.BitslicedNeon
