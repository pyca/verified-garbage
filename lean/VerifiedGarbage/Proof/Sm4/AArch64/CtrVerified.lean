module

import VerifiedGarbage.Proof.Sm4.AArch64.Link
meta import VerifiedGarbage.Proof.Sm4.AArch64.Link
public import VerifiedGarbage.Proof.Sm4.AArch64.CryptSum
meta import VerifiedGarbage.Proof.Sm4.AArch64.CryptSum
import VerifiedGarbage.Proof.Modes.AArch64.Ctr
meta import VerifiedGarbage.Proof.Modes.AArch64.Ctr
public import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sm4.AArch64.Lit
meta import VerifiedGarbage.Proof.Sm4.AArch64.Lit
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Sm4.AArch64.ModeCore
public import VerifiedGarbage.Impl.StackScratch.AArch64
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Impl.Aes.AArch64.Alloc
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.AesSiv.Words
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncLoop
import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.AArch64.Copy
import VerifiedGarbage.Proof.Modes.AArch64.Counter
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Modes.AArch64.Unchain
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Sm4.AArch64.Copy
import VerifiedGarbage.Proof.Sm4.AArch64.Crypt16
import VerifiedGarbage.Proof.Sm4.AArch64.Imm
import VerifiedGarbage.Proof.Sm4.AArch64.PreparedVerified
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Sm4.Planes
import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.AesCcm.Mac
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.AesSiv.Ctr32
meta import VerifiedGarbage.Proof.AesSiv.Words
meta import VerifiedGarbage.Proof.Cmac.Dbl32
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcEncLoop
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
meta import VerifiedGarbage.Proof.Modes.AArch64.Copy
meta import VerifiedGarbage.Proof.Modes.AArch64.Counter
meta import VerifiedGarbage.Proof.Modes.AArch64.Steps
meta import VerifiedGarbage.Proof.Modes.AArch64.Unchain
meta import VerifiedGarbage.Proof.Modes.AArch64.Words
meta import VerifiedGarbage.Proof.Modes.AArch64.Xor
meta import VerifiedGarbage.Proof.Modes.Addr
meta import VerifiedGarbage.Proof.Sm4.AArch64.Copy
meta import VerifiedGarbage.Proof.Sm4.AArch64.Crypt16
meta import VerifiedGarbage.Proof.Sm4.AArch64.Imm
meta import VerifiedGarbage.Proof.Sm4.AArch64.ModeCore
meta import VerifiedGarbage.Proof.Sm4.AArch64.PreparedVerified
meta import VerifiedGarbage.Proof.Sm4.CtrCipher
meta import VerifiedGarbage.Proof.Sm4.Layout
meta import VerifiedGarbage.Proof.Sm4.Planes
meta import VerifiedGarbage.Spec.Ctr.Contract

/-!
# SM4-CTR on AArch64 meets its contracts

`ctr_wp`: the modes' CTR over SM4's core (`Proof.Modes.AArch64.ctr_wp` with
`modeCoreSpec`). `ctr_verified`: `ctr` is correct and constant time, by
the taint analysis: the pointers, `n` and the stack pointer are public, and
so is everything the code computes from them, which it keeps in registers;
the counter block is secret. `ctr_framed` runs it with its working space on
the stack, zeroed on return: 3264 bytes, the 408 words of the scratch
buffer.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.AArch64 VG.Impl.Sm4.AArch64

/-- CTR on AArch64 with its working space at `x4`. -/
def ctrAArch64 : Contract AArch64.isa where
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
    Spec.Cbc.blocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
        Spec.Ctr.crypt (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s.mem (s.gpr .x0))) (Spec.Aes.bytesAt s.mem (s.gpr .x1) 16)
          (Spec.Cbc.blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) ∧
      Spec.Aes.bytesAt s'.mem (s.gpr .x1) 16 = Spec.Ctr.next (Spec.Aes.bytesAt s.mem (s.gpr .x1) 16) (s.gpr .x3).toNat
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.Impl.Sm4.AArch64
open VG.Proof.Sm4 (ctrAArch64)

attribute [local irreducible] Spec.Sm4.cipher in
/-- The core's cipher is SM4's, without unfolding it. -/
theorem cipher_eq (k : Spec.Sm4.Schedule) : modeCoreSpec.cipher k = Spec.Sm4.cipher k := rfl

theorem ctr_wp {s₀ : State} (hp : ctrAArch64.pre s₀) :
    WP isa ctr s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ ctrAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKC, dKD, dKS, dCD, dCS, dDS, fitK, fitC, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * (slots + 12)⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.ctr_wp modeCoreSpec (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dCS dDS dCD fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKC⟩) fun s' ⟨hcs, hdata, hctr, _, _, _⟩ => ⟨hcs, ?_, hctr⟩
  rw [cipher_eq] at hdata
  exact hdata

theorem ctrTaint_agree (s₁ s₂ : State) (_ : ctrAArch64.pre s₁) (_ : ctrAArch64.pre s₂)
    (hp : ctrAArch64.pub s₁ s₂) : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ctr_ct : ConstantTime isa ctrAArch64.pre ctrAArch64.pub ctr :=
  VG.Taint.constantTime_of_exists (A := VectorTaint.taint)
    (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun s₁ s₂ h₁ h₂ hp => ⟨ctrTaint_agree s₁ s₂ h₁ h₂ hp, fun v hv => by
      simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hv⟩) (by taint_decide_sum [cryptSum])

theorem ctr_correct (s : State) (hs : ctrAArch64.pre s) :
    ∃ t s', Exec isa ctr s t s' ∧ abiPreserved s s' ∧ ctrAArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' ctr_keeps_x30 (ctr_wp hs)
  exact ⟨t, s', he, modeAbi_of he h₁ h₃ (by lit_decide), h₂⟩

/-- A state satisfying the precondition (one block). -/
def ctrSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 8 * 408⟩]

theorem ctr_verified :
    Verified AArch64.target ctr (Proof.Sm4.ctrScratchContract AArch64.abi (slots + 12)) :=
  Verified.of_correct ctr_correct ctr_ct (by
    sig_implies [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Proof.Sm4.ctrPost, ctrAArch64,
      AArch64.abi, AArch64.argRegs, slots, tableEnd, tableSlot] [ctrSat] using ctrSat)

/-- A state satisfying `vg_sm4_ctr`'s precondition: the schedule at
`0x1000`, the counter block at `0x2000`, one block at `0x3000`. -/
def ctrFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩]

theorem ctrFrameSat_pre : ∃ s, (Spec.Sm4.ctrContract AArch64.abi 3264).pre s := by
  implies_sat [Spec.Sm4.ctrContract, Spec.Sm4.ctrSig, AArch64.abi, AArch64.argRegs] [ctrFrameSat] using ctrFrameSat

/-- CTR with its working space on the stack. -/
theorem ctr_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 ctr)
      (Spec.Sm4.ctrContract AArch64.abi 3264) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.ctrSig) (nm := "scratch") (e := .u64)
    (n := 408) (post := Proof.Sm4.ctrPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3264) ctr_verified
    (by decide) (by decide) (by decide) (Proof.Sm4.ctrPostOut_local _) ctrFrameSat_pre

end VG.Proof.Sm4.AArch64
