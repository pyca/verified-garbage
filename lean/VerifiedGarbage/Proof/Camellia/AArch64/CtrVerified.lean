import VerifiedGarbage.Proof.Camellia.AArch64.ModeCore
import VerifiedGarbage.Proof.Modes.AArch64.Ctr
import VerifiedGarbage.Proof.Camellia.CtrScratch
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Camellia.AArch64.Lit

/-!
# Camellia-CTR on AArch64 meets its contracts

`ctr_wp`: the modes' CTR over Camellia's core (`Proof.Modes.AArch64.ctr_wp`
with `modeCoreSpec`). `ctr_verified`: `ctr` is correct and constant time, by
the taint analysis: the pointers, `rounds`, `n` and the stack pointer are
public, and so is everything the code computes from them, which it keeps in
registers; the counter block is secret. `ctr_framed` runs it with its
working space on the stack, zeroed on return: 3248 bytes, the 406 words of
the scratch buffer.
-/

namespace VG.Proof.Camellia

open VG VG.AArch64 VG.Impl.Camellia.AArch64

/-- CTR on AArch64 with its working space at `x5`. -/
def ctrAArch64 : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 272⟩
    let ctr : Region := ⟨s.gpr .x2, 16⟩
    let data : Region := ⟨s.gpr .x3, 16 * (s.gpr .x4).toNat⟩
    let scratch : Region := ⟨s.gpr .x5, 8 * slots⟩
    s.rd = [sched] ∧ s.wr = [ctr, data, scratch] ∧ sched.Disjoint ctr ∧ sched.Disjoint data ∧
      sched.Disjoint scratch ∧ ctr.Disjoint data ∧ ctr.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .x0).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + 16 * (s.gpr .x4).toNat ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + 8 * slots ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 18 ∨ (s.gpr .x1).toNat = 24)
  post s s' :=
    Spec.Cbc.blocksAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat =
        Spec.Ctr.crypt (Spec.Camellia.cipher (Spec.Camellia.subkeysAt s.mem (s.gpr .x0) (s.gpr .x1).toNat))
          (Spec.Aes.bytesAt s.mem (s.gpr .x2) 16) (Spec.Cbc.blocksAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) ∧
      Spec.Aes.bytesAt s'.mem (s.gpr .x2) 16 = Spec.Ctr.next (Spec.Aes.bytesAt s.mem (s.gpr .x2) 16) (s.gpr .x4).toNat
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.sp = s₂.sp

end VG.Proof.Camellia

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.Impl.Camellia.AArch64
open VG.Proof.Camellia (ctrAArch64 schedWords)

attribute [local irreducible] Spec.Camellia.cipher in
/-- The core's cipher is Camellia's, without unfolding it. -/
theorem cipher_eq (m : Mem) (p : Addr) (R : Nat) :
    modeCoreSpec.cipher (R, schedWords m p R) = Spec.Camellia.cipher (Spec.Camellia.subkeysAt m p R) :=
  rfl

theorem ctr_wp {s₀ : State} (hp : ctrAArch64.pre s₀) :
    WP isa ctr s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ ctrAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKC, dKD, dKS, dCD, dCS, dDS, fitK, fitC, fitD, fitB, hR⟩ := hp
  have hwS : (⟨s₀.gpr .x5, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.ctr_wp modeCoreSpec (r := ⟨.x2, .x3, .x4, .x5⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x5) (P := s₀.gpr .x2) (D := s₀.gpr .x3) (n := (s₀.gpr .x4).toNat)
    (k := ((s₀.gpr .x1).toNat, schedWords s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat))
    rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dCS dDS dCD fitD
    ⟨s₀.gpr .x0, rfl, by apply BitVec.eq_of_toNat_eq; simp, hR, rfl, by rw [hrd]; simp, fitK,
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dKS
        · exact dKC⟩) fun s' ⟨hcs, hdata, hctr, _, _, _⟩ => ⟨hcs, ?_, hctr⟩
  rw [cipher_eq] at hdata
  exact hdata

theorem ctrTaint_agree (s₁ s₂ : State) (_ : ctrAArch64.pre s₁) (_ : ctrAArch64.pre s₂)
    (hp : ctrAArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ctr_ct : ConstantTime isa ctrAArch64.pre ctrAArch64.pub ctr :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) ctrTaint_agree
    (by taint_decide)

theorem ctr_correct (s : State) (hs : ctrAArch64.pre s) :
    ∃ t s', Exec isa ctr s t s' ∧ abiPreserved s s' ∧ ctrAArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (ctr_wp hs) (by lit_decide) (by lit_decide)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega)
  · exact h₁ 1 (by omega)
  · exact h₁ 2 (by omega)
  · exact h₁ 3 (by omega)
  · exact h₁ 4 (by omega)
  · exact h₁ 5 (by omega)
  · exact h₁ 6 (by omega)
  · exact h₁ 7 (by omega)
  · exact h₁ 8 (by omega)
  · exact h₁ 9 (by omega)
  · exact h₃ _ (by simp)

/-- A state satisfying the precondition (one block, 18 rounds). -/
def ctrSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 18 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 8 * 406⟩]

theorem ctr_verified :
    Verified AArch64.target ctr (Proof.Camellia.ctrScratchContract AArch64.abi slots) :=
  Verified.of_correct ctr_correct ctr_ct (by
    sig_implies [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig,
      Spec.Camellia.ctrPre, Spec.Camellia.ctrPost, ctrAArch64, AArch64.abi, AArch64.argRegs, slots,
      tailSlot, savedSlot, endSlot, keySlot] [ctrSat] using ctrSat)

/-- A state satisfying CTR's precondition: the schedule at `0x1000`, the
counter block at `0x2000`, one block at `0x3000`, 18 rounds. -/
def ctrFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 18 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩]

theorem ctrFrameSat_pre : ∃ s, (Spec.Camellia.ctrContract AArch64.abi 3248).pre s := by
  implies_sat [Spec.Camellia.ctrContract, Spec.Camellia.ctrSig, Spec.Camellia.ctrPre,
    Spec.Camellia.ctrPost, AArch64.abi, AArch64.argRegs] [ctrFrameSat] using ctrFrameSat

/-- CTR with its working space on the stack. -/
theorem ctr_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x5 406 ctr)
      (Spec.Camellia.ctrContract AArch64.abi 3248) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Camellia.ctrSig) (nm := "scratch") (e := .u64)
    (n := 406) (pre := Spec.Camellia.ctrPre AArch64.abi.ptrBits)
    (post := Spec.Camellia.ctrPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3248) (by rw [← Proof.Camellia.ctrScratchContract_eq]; exact ctr_verified)
    (by decide) (by decide) (by decide) (Proof.Camellia.ctrPostOut_local _) ctrFrameSat_pre

end VG.Proof.Camellia.AArch64
