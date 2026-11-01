module

public import VerifiedGarbage.Proof.Sm4.Ctr32Scratch
public import VerifiedGarbage.Proof.Sm4.AArch64.ModeCore
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Impl.Sm4.AArch64.Ctr32
public import VerifiedGarbage.Proof.Modes.Ctr32
import VerifiedGarbage.Proof.Sm4.AArch64.Link
import VerifiedGarbage.Proof.Modes.AArch64.Ctr32
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sm4.AArch64.Ctr32Lit
meta import VerifiedGarbage.Proof.Sm4.Ctr32Scratch
meta import VerifiedGarbage.Proof.Sm4.AArch64.ModeCore
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Impl.Sm4.AArch64.Ctr32
meta import VerifiedGarbage.Proof.Modes.Ctr32
meta import VerifiedGarbage.Proof.Sm4.AArch64.Link
meta import VerifiedGarbage.Proof.Modes.AArch64.Ctr32
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.AArch64.Ctr32Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.Sm4.Contract

/-!
# SM4's counter mode with `inc₃₂` on AArch64 meets its contracts

`ctr32_wp`: the modes' counter mode with `inc₃₂` over SM4's core
(`Proof.Modes.AArch64.ctr32_wp` with `modeCoreSpec`). `ctr32_verified`:
`ctr32` is correct and constant time, by the taint analysis: the pointers,
`n` and the stack pointer are public, and so is everything the code computes
from them, which it keeps in registers; the counter block is secret.
`ctr32_framed` runs it with its working space on the stack, zeroed on
return, as `ctr_framed` (`CtrVerified.lean`): 3264 bytes, the 408 words of
the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.AArch64 VG.Impl.Sm4.AArch64

/-- `vg_sm4_ctr32` on AArch64 with its working space at `x4`. -/
def ctr32AArch64 : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 128⟩
    let ctr : Region := ⟨s.gpr .x1, 16⟩
    let data : Region := ⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 8 * (slots + 12)⟩
    s.rd = [sched] ∧ s.wr = [ctr, data, scratch] ∧ sched.Disjoint ctr ∧ sched.Disjoint data ∧
      sched.Disjoint scratch ∧ ctr.Disjoint data ∧ ctr.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .x0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 16 * (s.gpr .x3).toNat ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8 * (slots + 12) ≤ 2 ^ 64
  post s s' :=
    Spec.Gcm.blocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
        Spec.Gcm.ctr32 (Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt s.mem (s.gpr .x0))) (Spec.Gcm.blockAt s.mem (s.gpr .x1))
          (Spec.Gcm.blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) ∧
      Spec.Gcm.blockAt s'.mem (s.gpr .x1) =
        Nat.repeat Spec.Gcm.inc32 (s.gpr .x3).toNat (Spec.Gcm.blockAt s.mem (s.gpr .x1))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.Impl.Sm4.AArch64
open VG.Proof.Sm4 (ctr32AArch64)

attribute [local irreducible] Spec.Sm4.cipher in
/-- The core's cipher, on GCM's blocks, is the contract's (see `cipher_eq`,
`CtrVerified.lean`). -/
theorem gcmCipher_eq (k : Spec.Sm4.Schedule) :
    Proof.Modes.onBlocks (modeCoreSpec.cipher k) = Spec.Sm4.gcmCipher k := rfl

theorem ctr32_keeps_x30 : Modes.AArch64.KeepsReg .x30 ctr32 := by sm4_keeps_x30

theorem ctr32_wp {s₀ : State} (hp : ctr32AArch64.pre s₀) :
    WP isa ctr32 s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ ctr32AArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKC, dKD, dKS, dCD, dCS, dDS, fitK, fitC, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * (slots + 12)⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.ctr32_wp modeCoreSpec (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dCS dDS dCD fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKC⟩) fun s' ⟨hcs, hdata, hctr, _, _, _⟩ => ⟨hcs, ?_, hctr⟩
  rw [gcmCipher_eq] at hdata
  exact hdata

theorem ctr32Taint_agree (s₁ s₂ : State) (_ : ctr32AArch64.pre s₁) (_ : ctr32AArch64.pre s₂)
    (hp : ctr32AArch64.pub s₁ s₂) : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ctr32_ct : ConstantTime isa ctr32AArch64.pre ctr32AArch64.pub ctr32 :=
  VG.Taint.constantTime_of_exists (A := VectorTaint.taint)
    (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun s₁ s₂ h₁ h₂ hp => ⟨ctr32Taint_agree s₁ s₂ h₁ h₂ hp, fun v hv => by
      simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hv⟩) (by taint_decide_sum [cryptSum])

theorem ctr32_correct (s : State) (hs : ctr32AArch64.pre s) :
    ∃ t s', Exec isa ctr32 s t s' ∧ abiPreserved s s' ∧ ctr32AArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' ctr32_keeps_x30 (ctr32_wp hs)
  exact ⟨t, s', he, modeAbi_of he h₁ h₃ (by lit_decide), h₂⟩

/-- A state satisfying the precondition (one block). -/
def ctr32Sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 8 * 408⟩]

theorem ctr32_verified :
    Verified AArch64.target ctr32 (Proof.Sm4.ctr32ScratchContract AArch64.abi (slots + 12)) :=
  Verified.of_correct ctr32_correct ctr32_ct (by
    sig_implies [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Post, ctr32AArch64,
      AArch64.abi, AArch64.argRegs, slots, tableEnd, tableSlot] [ctr32Sat] using ctr32Sat)

/-- A state satisfying `vg_sm4_ctr32`'s precondition: the schedule at
`0x1000`, the counter block at `0x2000`, one block at `0x3000`. -/
def ctr32FrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩]

theorem ctr32FrameSat_pre : ∃ s, (Proof.Sm4.ctr32Contract AArch64.abi 3264).pre s := by
  implies_sat [Proof.Sm4.ctr32Contract, Proof.Sm4.ctr32Sig, AArch64.abi, AArch64.argRegs] [ctr32FrameSat] using ctr32FrameSat

/-- `vg_sm4_ctr32` with its working space on the stack. -/
theorem ctr32_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 ctr32)
      (Proof.Sm4.ctr32Contract AArch64.abi 3264) :=
  AArch64.Verified.stackScratchWiped (sig := Proof.Sm4.ctr32Sig) (nm := "scratch") (e := .u64)
    (n := 408) (post := Proof.Sm4.ctr32Post AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3264) ctr32_verified
    (by decide) (by decide) (by decide) (Proof.Sm4.ctr32PostOut_local _) ctr32FrameSat_pre

end VG.Proof.Sm4.AArch64
