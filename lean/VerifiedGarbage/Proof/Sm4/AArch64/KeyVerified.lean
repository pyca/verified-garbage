import VerifiedGarbage.Proof.Sm4.AArch64.KeyEk
import VerifiedGarbage.Proof.Sm4.AArch64.Verified
import VerifiedGarbage.Proof.Sm4.AArch64.Lit

/-!
# SM4 key expansion on AArch64 meets its contracts

`expandKey_verified`: `expandKey` is correct (`expandKey_wp`) and constant
time, by the taint analysis with the pointers and the stack pointer public.
`expandKey_framed` runs it with its working space on the stack, zeroed on
return, as `ecb_framed` does.
-/

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.Impl.Sm4.AArch64
open VG.Proof.Sm4 (expandKeyAArch64)

theorem expandKeyTaint_agree (s₁ s₂ : State) (_ : expandKeyAArch64.pre s₁) (_ : expandKeyAArch64.pre s₂)
    (hp : expandKeyAArch64.pub s₁ s₂) : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

theorem expandKey_ct : ConstantTime isa expandKeyAArch64.pre expandKeyAArch64.pub expandKey :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) expandKeyTaint_agree (by taint_decide)

theorem expandKey_correct (s : State) (hs : expandKeyAArch64.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyAArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (expandKey_wp hs) (by lit_decide)
    (by lit_decide)
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

/-- A state satisfying the precondition. -/
def expandKeySat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 8 * 396⟩]

theorem expandKey_verified :
    Verified AArch64.target expandKey (Proof.Sm4.expandKeyScratchContract AArch64.abi slots) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Sm4.expandKeyScratchContract, Proof.Sm4.expandKeyScratchSig, Proof.Sm4.expandKeyPost,
      expandKeyAArch64, AArch64.abi, AArch64.argRegs, slots, savedSlot, tableEnd, tableSlot]
      [expandKeySat] using expandKeySat)

/-- A state satisfying the key schedule's precondition: the key at
`0x1000`, the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Sm4.expandKeyContract AArch64.abi 3168).pre s := by
  implies_sat [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, AArch64.abi, AArch64.argRegs]
    [expandKeyFrameSat] using expandKeyFrameSat

/-- Key expansion, with its working space on the stack. -/
theorem expandKey_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3168 .x2 396 expandKey)
      (Spec.Sm4.expandKeyContract AArch64.abi 3168) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 396) (post := Proof.Sm4.expandKeyPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 3168) expandKey_verified
    (by decide) (by decide) (by decide) (Proof.Sm4.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Sm4.AArch64
