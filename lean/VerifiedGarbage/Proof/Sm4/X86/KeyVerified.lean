import VerifiedGarbage.Proof.Sm4.X86.KeyEk
import VerifiedGarbage.Proof.Sm4.X86.Verified

/-!
# The SM4 key schedule on x86 (32-bit) meets its contracts

`expandKey_verified`: `expandKey` is correct (`expandKey_wp`) and constant
time, by the taint analysis, which starts with `esp` public and knows which
argument words are the base addresses of the schedule and the scratch
buffer: only the pointers, `kp`, the loop test and the slot of the
schedule's pointer are public. `expandKey_framed` runs it with its working
space on the stack, zeroed on return: 1448 bytes, the 1432 of the scratch
buffer, the copies of the two argument slots, the buffer's address and the
return address of the call of the code.
-/

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.Impl.Sm4.X86
open VG.Proof.Sm4 (expandKeyX86)

/-- `expandKeyX86.pre`, by name. -/
structure KPre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 0).setWidth 64, 16⟩, ⟨argAddr s 0, 12⟩]
  wr : s.wr = [⟨(arg s 1).setWidth 64, 128⟩, ⟨(arg s 2).setWidth 64, 4 * Impl.Sm4.X86.slots⟩]
  dSB : Region.Disjoint ⟨(arg s 1).setWidth 64, 128⟩ ⟨(arg s 2).setWidth 64, 4 * Impl.Sm4.X86.slots⟩
  aS : Region.Disjoint ⟨argAddr s 0, 12⟩ ⟨(arg s 1).setWidth 64, 128⟩
  aB : Region.Disjoint ⟨argAddr s 0, 12⟩ ⟨(arg s 2).setWidth 64, 4 * Impl.Sm4.X86.slots⟩
  rS : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 1).setWidth 64, 128⟩
  rB : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 2).setWidth 64, 4 * Impl.Sm4.X86.slots⟩
  fS : (arg s 1).toNat + 128 ≤ 2 ^ 32
  fB : (arg s 2).toNat + 4 * Impl.Sm4.X86.slots ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32

theorem KPre.of {s : State} (h : expandKeyX86.pre s) : KPre s := by
  obtain ⟨h1, h2, -, -, h5, h6, h7, h8, h9, -, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h5, h6, h7, h8, h9, h11, h12, h13⟩

/-- The initial taint: `esp` public, and the words holding `schedule` and
`scratch` known to be the base addresses of the writable regions. -/
def expandKeyTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [128, 4 * Impl.Sm4.X86.slots], argLen := 16,
    argBases := [(8, 0), (12, 1)] }

theorem expandKeyTaint_wf {s : State} (hp : KPre s) : VG.X86.Taint.Wf expandKeyTaint s := by
  have hS := hp.fS; have hB := hp.fB; have hs := hp.fSp
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [expandKeyTaint]; omega, ?_⟩, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.dSB, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [setWidth_toNat] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega) hp.rS hp.aS
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega) hp.rB hp.aB
  · intro p hp'
    simp only [expandKeyTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem expandKeyTaint_agree {s₁ s₂ : State} (h₁ : expandKeyX86.pre s₁) (h₂ : expandKeyX86.pre s₂)
    (hpub : expandKeyX86.pub s₁ s₂) : VG.X86.Taint.Agree expandKeyTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := KPre.of h₁; have hp₂ := KPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, expandKeyTaint_wf hp₁, expandKeyTaint_wf hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [expandKeyTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr, ha 1 (by omega), ha 2 (by omega)]
  · simp only [expandKeyTaint] at hk
    rw [show VG.X86.Taint.depth expandKeyTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 16) hp₁.fSp h4 hk, VG.X86.Taint.argByte_eq (n := 16) hp₂.fSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem expandKey_ct : ConstantTime isa expandKeyX86.pre expandKeyX86.pub expandKey :=
  VG.Taint.constantTime (A := VG.X86.taint) expandKeyTaint
    (fun _ _ h₁ h₂ hp => expandKeyTaint_agree h₁ h₂ hp) (by taint_decide)

theorem expandKey_correct (s : State) (hs : expandKeyX86.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyX86.post s s' :=
  expandKey_wp hs

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000` at `0x8004`. -/
def ekSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30 else 0

/-- A state satisfying the precondition. -/
def ekSat : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ekSatMem
  rd := [⟨0x1000, 16⟩, ⟨0x8004, 12⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 1432⟩]

theorem expandKey_verified :
    Verified X86.target expandKey (Proof.Sm4.expandKeyScratchContract X86.abi 179) :=
  Verified.of_correct expandKey_correct expandKey_ct
    (by
      have a0 : arg ekSat 0 = 0x1000 := by decide
      have a1 : arg ekSat 1 = 0x2000 := by decide
      have a2 : arg ekSat 2 = 0x3000 := by decide
      have e : argAddr ekSat 0 = 0x8004 := by decide
      have esp : ekSat.gpr .esp = 0x8000 := rfl
      sig_implies [Proof.Sm4.expandKeyScratchContract, Proof.Sm4.expandKeyScratchSig, Proof.Sm4.expandKeyPost,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes, expandKeyX86, Impl.Sm4.X86.slots]
        [a0, a1, a2, e, esp] using ekSat)

/-- A state satisfying `vg_sm4_expand_key`'s precondition: the key at
`0x1000` and the schedule at `0x2000`, as stack arguments at `0x8004`. -/
def expandKeyFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else 0
  rd := [⟨0x1000, 16⟩, ⟨0x8004, 8⟩]
  wr := [⟨0x2000, 128⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Sm4.expandKeyContract X86.abi 1448).pre s := by
  implies_sat [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] [expandKeyFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using expandKeyFrameSat

/-- The key schedule, with its working space on the stack. -/
theorem expandKey_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1448 2 358 expandKey)
      (Spec.Sm4.expandKeyContract X86.abi 1448) :=
  X86.Verified.stackScratchWiped (sig := Spec.Sm4.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 179) (post := Proof.Sm4.expandKeyPost X86.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 1448) expandKey_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.expandKeyPost_local _) (Proof.Sm4.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Sm4.X86
