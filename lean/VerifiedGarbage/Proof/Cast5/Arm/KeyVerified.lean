module

public import VerifiedGarbage.Proof.Cast5.Arm.Key
meta import VerifiedGarbage.Proof.Cast5.Arm.Key
public import VerifiedGarbage.Proof.Cast5.Arm.Lit
meta import VerifiedGarbage.Proof.Cast5.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
public import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Cast5.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Cast5.Arm.Ecb
import VerifiedGarbage.Proof.Cast5.Arm.KeyHalf
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Cast5.Arm.Ecb
meta import VerifiedGarbage.Proof.Cast5.Arm.KeyHalf
meta import VerifiedGarbage.Proof.Cast5.Memory
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# CAST5 key expansion on ARMv7: verified

Constant time by the taint analysis: `r0`–`r3` (the pointers and the key's
length) and the table's address are public, `r3` the working space's base;
the step and half counts and the schedule's pointer are computed from them.
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Impl.Cast5.Arm
open VG.Impl.Cast5 (s5678Sym s5678 keyConsts)

/-- The initial taint: `r0`–`r3` public, `r3` the base of writable region 1. -/
def τKey : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [128, 256], bases := [(.r3, 1)] }

theorem τKey_wf {s : State} (h : keyArm.pre (stripConsts keyConsts s)) : VG.Arm.Taint.Wf τKey s := by
  obtain ⟨_, hwr, _, _, dKS, _, hKf, hcf, _⟩ := h
  simp only [stripConsts_gpr, stripConsts_wr] at hwr dKS hKf hcf
  refine ⟨fun _ => ⟨by simp [hwr, τKey], by simpa [hwr] using dKS, ?_⟩, fun p hp => ?_, fun h => absurd h (by decide),
    fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [toNat_addr] <;> omega
  · simp only [τKey, List.mem_singleton] at hp; subst hp
    simp only [VG.Arm.Taint.region, hwr]
    rfl

theorem τKey_agree {s₁ s₂ : State} (h₁ : keyArm.pre (stripConsts keyConsts s₁))
    (h₂ : keyArm.pre (stripConsts keyConsts s₂)) (hp : keyArm.pub s₁ s₂) : VG.Arm.Taint.Agree τKey s₁ s₂ := by
  obtain ⟨_, p0, p1, p2, p3⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, τKey_wf h₁, τKey_wf h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
    fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  · simp only [τKey, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact p0
    · exact p1
    · exact p2
    · exact p3
  · have w₁ := h₁.2.1
    have w₂ := h₂.2.1
    simp only [stripConsts_wr, stripConsts_gpr] at w₁ w₂
    rw [w₁, w₂, p2, p3]

/-- Key expansion's contract with the table, as the proof states it. -/
def keyArmC : Contract isa where
  pre s := keyArm.pre (stripConsts keyConsts s) ∧ ConstsOk keyConsts 0 s
  post := keyArm.post
  pub s₁ s₂ := keyArm.pub s₁ s₂ ∧ s₁.syms s5678Sym = s₂.syms s5678Sym

theorem expandKey_constantTime : ConstantTime isa keyArmC.pre keyArmC.pub expandKey :=
  VG.Taint.constantTime (A := taintSym [s5678Sym]) τKey (fun _ _ h₁ h₂ hp => ⟨τKey_agree h₁.1 h₂.1 hp.1,
    fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hp.2⟩) (by taint_decide)

theorem keyArmC_correct (s : State) (hs : keyArmC.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyArmC.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := key_correct s hs.1 hs.2
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

/-- A state satisfying the precondition without the table: a key of five bytes. -/
def keySat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 5 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 5⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 256⟩]

theorem key_implies : keyArm.Implies (Spec.Cast5.expandKeyContract abi) := by
  sig_implies [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre,
    Spec.Cast5.expandKeyPost, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, keyArm,
    Spec.Cast5.validKey] [keySat] using keySat

theorem keyConsts_eq : keyConsts = [(s5678Sym, s5678)] := rfl

/-- The memory of the witness with the table: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def keySatMem : Mem := constMem 0x100000 s5678

theorem keySatMem_held : ∀ i < s5678.length,
    keySatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = s5678.getD i 0 := by
  unfold keySatMem
  exact constMem_held _ _ (by rw [Impl.Cast5.s5678, table_length]; decide)

/-- A state satisfying the precondition with the table. -/
def keySatC : State :=
  { keySat with mem := keySatMem, rd := [⟨0x1000, 5⟩, ⟨0x100000, 4096⟩], syms := fun _ => 0x100000 }

theorem key_sat : (Spec.Cast5.expandKeyContract (abi.withConsts keyConsts)).pre keySatC := by
  have hl : s5678.length = 512 := by rw [Impl.Cast5.s5678, table_length]
  have held := keySatMem_held
  rw [keyConsts_eq]
  generalize s5678 = W at hl held ⊢
  generalize e : keySatC = s
  sig_pre [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    Spec.Cast5.validKey]
  subst e
  rw [hl]
  refine ⟨by decide, by decide, fun i hi => held i (by rw [hl]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 128⟩, ⟨0x3000, 256⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide)

theorem keyC_implies : keyArmC.Implies (Spec.Cast5.expandKeyContract (abi.withConsts keyConsts)) where
  pre _ hs := ⟨key_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
  post s s' hs hp := post_consts.mpr (key_implies.post (stripConsts keyConsts s) s' (pre_consts.mp hs).1 hp)
  pub s₁ s₂ h₁ h₂ hp := ⟨key_implies.pub (stripConsts keyConsts s₁) (stripConsts keyConsts s₂)
      (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
    symAddr_eq_iff.mp ((pub_consts.mp hp).2 _ List.mem_cons_self)⟩
  sat := ⟨keySatC, key_sat⟩

theorem expandKey_verified :
    Verified target expandKey (Spec.Cast5.expandKeyContract (abi.withConsts keyConsts)) :=
  Verified.of_correct keyArmC_correct expandKey_constantTime keyC_implies

end VG.Proof.Cast5.Arm
