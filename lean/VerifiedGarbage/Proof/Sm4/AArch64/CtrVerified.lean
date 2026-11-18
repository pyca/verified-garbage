module

import VerifiedGarbage.Proof.Sm4.AArch64.Link
import VerifiedGarbage.Proof.Modes.AArch64.Ctr
import VerifiedGarbage.Proof.Modes.AArch64.Steps
public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.ModeCore
public import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Proof.Sm4.AArch64.ModeCore
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.AArch64.Link
meta import VerifiedGarbage.Proof.Modes.AArch64.Ctr
meta import VerifiedGarbage.Proof.Modes.AArch64.Steps
meta import VerifiedGarbage.Proof.Sm4.AArch64.Serial.ModeCore
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
meta import VerifiedGarbage.Proof.Sm4.AArch64.ModeCore
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# SM4-CTR on AArch64 meets its contracts

`ctr_wp`: the modes' CTR over SM4's core (`Proof.Modes.AArch64.ctr_wp` with
`modeCoreSpec`, `ctrBatch_wp`) or, for fewer than six blocks, over the
single-block core (with `Serial.coreSpec`, `ctrSerial_wp`), whichever
`few` runs (`few_wp`). `ctr_verified`: `ctr` is correct and constant time, by
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

/-- `few` runs one of its two programs, from a state that differs in `x13`. -/
theorem few_wp {short long : Prog isa} {s₀ : State} {Q : State → Prop}
    (h : ∀ s₁, (∀ r, r ≠ .x13 → s₁.gpr r = s₀.gpr r) → s₁.mem = s₀.mem → s₁.rd = s₀.rd → s₁.wr = s₀.wr →
      WP isa short s₁ Q ∧ WP isa long s₁ Q) : WP isa (few short long) s₀ Q := by
  obtain ⟨sₐ, eₐ, _, gₐ, mₐ, rdₐ, wrₐ⟩ := Modes.AArch64.addImm_ok s₀ .x13 .x3 (v := 2) (by decide)
  obtain ⟨s₁, e', _, g', m', rd', wr'⟩ := Modes.AArch64.lsr_ok sₐ .x13 .x13 (sh := 3) (by decide)
  have e₁ : runBlock isa [.addImm .x .x13 .x3 2, .lsr .x .x13 .x13 3] s₀ = some s₁ := by
    rw [show ([.addImm .x .x13 .x3 2, .lsr .x .x13 .x13 3] : List Instr) =
      [.addImm .x .x13 .x3 2] ++ [.lsr .x .x13 .x13 3] from rfl, Modes.AArch64.runBlock_app, eₐ,
      Option.bind_some, e']
  obtain ⟨hs, hl⟩ := h s₁ (fun r hr => (g' r hr).trans (gₐ r hr)) (m'.trans mₐ) (rd'.trans rdₐ)
    (wr'.trans wrₐ)
  unfold few
  exact WP.seq (WP.of_runBlock ⟨s₁, e₁, WP.ite _ rfl (fun _ => hs) (fun _ => hl)⟩)

attribute [local irreducible] Spec.Sm4.cipher in
/-- The single-block core's cipher is SM4's, without unfolding it. -/
theorem serialCipher_eq (k : Spec.Sm4.Schedule) : Serial.coreSpec.cipher k = Spec.Sm4.cipher k := rfl

/-- Six blocks or more: the modes' CTR over the bitsliced core. -/
theorem ctrBatch_wp {s₀ : State} (hp : ctrAArch64.pre s₀) :
    WP isa (modeCore.ctr ⟨.x1, .x2, .x3, .x4⟩) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
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

/-- Fewer than six blocks: the modes' CTR over the single-block core. -/
theorem ctrSerial_wp {s₀ : State} (hp : ctrAArch64.pre s₀) :
    WP isa (Impl.Sm4.AArch64.Serial.core.ctr ⟨.x1, .x2, .x3, .x4⟩) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ ctrAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKC, dKD, dKS, dCD, dCS, dDS, fitK, fitC, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * (slots + 12)⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.ctr_wp Serial.coreSpec (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dCS dDS dCD fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKC⟩) fun s' ⟨hcs, hdata, hctr, _, _, _⟩ => ⟨hcs, ?_, hctr⟩
  rw [serialCipher_eq] at hdata
  exact hdata

theorem ctr_wp {s₀ : State} (hp : ctrAArch64.pre s₀) :
    WP isa ctr s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ ctrAArch64.post s₀ s' := by
  refine few_wp fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  have hp₁ : ctrAArch64.pre s₁ := by
    simpa only [ctrAArch64, m₁, rd₁, wr₁, g₁ .x0 (by decide), g₁ .x1 (by decide), g₁ .x2 (by decide),
      g₁ .x3 (by decide), g₁ .x4 (by decide)] using hp
  have transfer {s' : State}
      (h : (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₁.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ ctrAArch64.post s₁ s') :
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ ctrAArch64.post s₀ s' := by
    refine ⟨fun i hi => (h.1 i hi).trans (g₁ _ ?_), ?_⟩
    · have : ∀ i < 10, Impl.Modes.AArch64.Core.savedRegs.getD i .x19 ≠ .x13 := by decide
      exact this i hi
    · simpa only [ctrAArch64, m₁, g₁ .x0 (by decide), g₁ .x1 (by decide), g₁ .x2 (by decide),
        g₁ .x3 (by decide), g₁ .x4 (by decide)] using h.2
  exact ⟨WP.mono (ctrSerial_wp hp₁) fun _ h => transfer h, WP.mono (ctrBatch_wp hp₁) fun _ h => transfer h⟩

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

/-- CTR with its working space on the stack, which its registration zeroes
(`ScrubAll.withScrubAll`). -/
theorem ctr_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 3264 .x4 ctr)
      (Spec.Sm4.ctrContract AArch64.abi 3264) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm4.ctrSig) (nm := "scratch") (e := .u64)
    (n := 408) (post := Proof.Sm4.ctrPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3264) ctr_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ hb h => Proof.Sm4.ctrPostOut_local _ vs m m₁ m₂ r hl hb h) ctrFrameSat_pre

end VG.Proof.Sm4.AArch64
