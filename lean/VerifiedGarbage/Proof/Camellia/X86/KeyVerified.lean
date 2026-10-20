module

public import VerifiedGarbage.Proof.Camellia.X86.ExpandKey
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Camellia.X86.Lit
public import VerifiedGarbage.Proof.Camellia.Scratch
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Camellia.X86.Verified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Camellia.X86.ExpandKey
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Camellia.X86.Lit
meta import VerifiedGarbage.Proof.Camellia.Scratch
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Impl.StackScratch.X86
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Camellia.X86.Verified
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The Camellia key schedule on x86 (32-bit) meets its contracts

`expandKey_verified`: `expandKey` is correct (`expandKey_wp`) and constant
time, by the taint analysis, which starts with `esp` public and knows which
argument words are the base addresses of the schedule and the scratch
buffer: the pointers, the key's length, `kp` and the count of pairs the code
keeps in a slot of the scratch buffer are public. `expandKey_framed` runs it
with its working space on the stack, zeroed on return: 2708 bytes, the 2688
of the scratch buffer, the copies of the three argument slots, the buffer's
address and the return address of the call of the code.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.Impl.Camellia.X86

/-- `expandKeyX86.pre`, by name. -/
structure KPre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩, ⟨argAddr s 0, 16⟩]
  wr : s.wr = [⟨(arg s 2).setWidth 64, 272⟩, ⟨(arg s 3).setWidth 64, 4 * Impl.Camellia.X86.slots⟩]
  dSB : Region.Disjoint ⟨(arg s 2).setWidth 64, 272⟩ ⟨(arg s 3).setWidth 64, 4 * Impl.Camellia.X86.slots⟩
  aS : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 2).setWidth 64, 272⟩
  aB : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 3).setWidth 64, 4 * Impl.Camellia.X86.slots⟩
  rS : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 2).setWidth 64, 272⟩
  rB : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 3).setWidth 64, 4 * Impl.Camellia.X86.slots⟩
  fS : (arg s 2).toNat + 272 ≤ 2 ^ 32
  fB : (arg s 3).toNat + 4 * Impl.Camellia.X86.slots ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32

theorem KPre.of {s : State} (h : expandKeyX86.pre s) : KPre s := by
  obtain ⟨h1, h2, -, -, h5, h6, h7, h8, h9, -, h11, h12, h13, -⟩ := h
  exact ⟨h1, h2, h5, h6, h7, h8, h9, h11, h12, h13⟩

/-- The initial taint: `esp` public, and the words holding `schedule` and
`scratch` known to be the base addresses of the writable regions. -/
def expandKeyTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [272, 4 * Impl.Camellia.X86.slots], argLen := 20,
    argBases := [(12, 0), (16, 1)] }

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
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.rS hp.aS
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.rB hp.aB
  · intro p hp'
    simp only [expandKeyTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem expandKeyTaint_agree {s₁ s₂ : State} (h₁ : expandKeyX86.pre s₁) (h₂ : expandKeyX86.pre s₂)
    (hpub : expandKeyX86.pub s₁ s₂) : VG.X86.Taint.Agree expandKeyTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := KPre.of h₁; have hp₂ := KPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, expandKeyTaint_wf hp₁, expandKeyTaint_wf hp₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [expandKeyTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr, ha 2 (by omega), ha 3 (by omega)]
  · simp only [expandKeyTaint] at hk
    rw [show VG.X86.Taint.depth expandKeyTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 20) hp₁.fSp h4 hk, VG.X86.Taint.argByte_eq (n := 20) hp₂.fSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem expandKey_ct : ConstantTime isa expandKeyX86.pre expandKeyX86.pub expandKey :=
  VG.Taint.constantTime (A := VG.X86.taint) expandKeyTaint
    (fun _ _ h₁ h₂ hp => expandKeyTaint_agree h₁ h₂ hp) (by native_taint_decide)

theorem expandKey_correct (s : State) (hs : expandKeyX86.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyX86.post s s' :=
  expandKey_wp hs

/-- Memory holding the arguments `0x1000, 16, 0x2000, 0x3000` at `0x8004`. -/
def ekSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800D then 0x20 else
    if a = 0x8011 then 0x30 else 0
  rd := [⟨0x1000, 16⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x2000, 272⟩, ⟨0x3000, 2688⟩]

theorem expandKey_verified :
    Verified X86.target expandKey (Proof.Camellia.expandKeyScratchContract X86.abi 336) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Camellia.expandKeyScratchContract, Proof.Camellia.expandKeyScratchSig,
      Spec.Camellia.expandKeySig, Spec.Camellia.expandKeyPre, Spec.Camellia.expandKeyPost, expandKeyX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Impl.Camellia.X86.slots, Impl.Camellia.X86.grpSlot,
      Impl.Camellia.X86.nSlot, Impl.Camellia.X86.dSlot, Impl.Camellia.X86.savedSlot, Impl.Camellia.X86.keySlot,
      Impl.Camellia.X86.tailSlot]
      [ekSat, arg, argAddr, Mem.readW, Mem.read] using ekSat)

/-- A state satisfying `vg_camellia_expand_key`'s precondition: a key of 16
bytes at `0x1000` and the schedule at `0x2000`, as stack arguments at
`0x8004`. -/
def expandKeyFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800D then 0x20 else 0
  rd := [⟨0x1000, 16⟩, ⟨0x8004, 12⟩]
  wr := [⟨0x2000, 272⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Camellia.expandKeyContract X86.abi 2708).pre s := by
  implies_sat [Spec.Camellia.expandKeyContract, Spec.Camellia.expandKeySig, Spec.Camellia.expandKeyPre,
    Spec.Camellia.expandKeyPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [expandKeyFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using expandKeyFrameSat

/-- The key schedule, with its working space on the stack. -/
theorem expandKey_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 2708 3 672 expandKey)
      (Spec.Camellia.expandKeyContract X86.abi 2708) :=
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 336) (pre := Spec.Camellia.expandKeyPre X86.abi.ptrBits)
    (post := Spec.Camellia.expandKeyPost X86.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2708) (by rw [← Proof.Camellia.expandKeyScratchContract_eq]; exact expandKey_verified)
    (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.Camellia.expandKeyPre_local _) (Proof.Camellia.expandKeyPost_local _)
    (Proof.Camellia.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Camellia.X86
