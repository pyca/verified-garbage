module

public import VerifiedGarbage.Proof.Cast5.Arm.Ecb
meta import VerifiedGarbage.Proof.Cast5.Arm.Ecb
public import VerifiedGarbage.Proof.Cast5.Arm.Lit
meta import VerifiedGarbage.Proof.Cast5.Arm.Lit
public import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
public import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Cast5.Contract
meta import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# CAST5 ECB on ARMv7: verified

Constant time by the taint analysis: `r0`–`r3`, the stack argument (the
working space's address) and the table's address are public; the working
space's slots then hold public values (pointers, counts, the type of the
next round). The proof's contract (`ecbArmC`) is `ecbArm` for the state
without the table's region, with what the contract says of the table
(`ConstsOk`).
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Impl.Cast5.Arm
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)

/-- The initial taint: `r0`–`r3`, the 4 bytes of stack argument (the base of
writable region 1, the working space) are public. -/
def τEcb : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [0, 256], argLen := 4, argBases := [(0, 1)] }

theorem τEcb_wf {up : Bool} {s : State} (h : (ecbArm up).pre (stripConsts ecbConsts s)) :
    VG.Arm.Taint.Wf τEcb s := by
  obtain ⟨_, hwr, _, _, dDS, aD, aS, _, hdf, hcf, hsp, _⟩ := h
  simp only [stripConsts_gpr, stripConsts_wr, stackArg_strip, stackArgAddr_strip] at hwr dDS aD aS
  simp only [stripConsts_gpr, stripConsts_sp, stackArg_strip] at hdf hcf hsp
  refine ⟨fun _ => ⟨by simp [hwr, τEcb], by simpa [hwr] using dDS, ?_⟩, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hsp, ?_⟩, ?_⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [toNat_addr] <;> omega
  · have e : (⟨State.addr s.sp, 4⟩ : Region) = ⟨stackArgAddr s 0, 4⟩ := by simp [stackArgAddr]
    simp only [τEcb, e, hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact aD
    · exact aS
  · intro p hp; simp only [τEcb, List.mem_singleton] at hp; subst hp
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hwr]
    rfl

theorem τEcb_agree {up : Bool} {s₁ s₂ : State} (h₁ : (ecbArm up).pre (stripConsts ecbConsts s₁))
    (h₂ : (ecbArm up).pre (stripConsts ecbConsts s₂))
    (hp : (ecbArm up).pub s₁ s₂) : VG.Arm.Taint.Agree τEcb s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, τEcb_wf h₁, τEcb_wf h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [τEcb, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact p0
    · exact p1
    · exact p2
    · exact p3
  · have w₁ := h₁.2.1
    have w₂ := h₂.2.1
    simp only [stripConsts_wr, stripConsts_gpr, stackArg_strip] at w₁ w₂
    rw [w₁, w₂, p2, p3, a0]
  · have argByte_eq (s : State) : Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
      simp [Taint.argByte, stackArgAddr]
    simp only [τEcb] at hk
    rw [argByte_eq, argByte_eq, Mem.readW_byte s₁.mem _ hk, Mem.readW_byte s₂.mem _ hk]
    exact congrArg _ a0

/-- The ECB functions' contract with the table, as the proof states it. -/
def ecbArmC (up : Bool) : Contract isa where
  pre s := (ecbArm up).pre (stripConsts ecbConsts s) ∧ ConstsOk ecbConsts 0 s
  post := (ecbArm up).post
  pub s₁ s₂ := (ecbArm up).pub s₁ s₂ ∧ s₁.syms s1234Sym = s₂.syms s1234Sym

theorem τEcb_agreeS {up : Bool} {s₁ s₂ : State} (h₁ : (ecbArmC up).pre s₁) (h₂ : (ecbArmC up).pre s₂)
    (hp : (ecbArmC up).pub s₁ s₂) : VG.Arm.Taint.AgreeS [s1234Sym] τEcb s₁ s₂ :=
  ⟨τEcb_agree h₁.1 h₂.1 hp.1, fun n hn => by
    simp only [List.mem_singleton] at hn; subst hn; exact hp.2⟩

theorem ecbEncrypt_constantTime : ConstantTime isa (ecbArmC true).pre (ecbArmC true).pub ecbEncrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) τEcb (fun _ _ h₁ h₂ hp => τEcb_agreeS h₁ h₂ hp)
    (by taint_decide)

theorem ecbDecrypt_constantTime : ConstantTime isa (ecbArmC false).pre (ecbArmC false).pub ecbDecrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) τEcb (fun _ _ h₁ h₂ hp => τEcb_agreeS h₁ h₂ hp)
    (by taint_decide)

theorem ecbArmC_correct (up : Bool) (s : State) (hs : (ecbArmC up).pre s) :
    ∃ t s', Exec isa (ecb up) s t s' ∧ abiPreserved s s' ∧ (ecbArmC up).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_correct up s hs.1 hs.2
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

/-- A state satisfying the precondition without the table: no blocks. -/
def ecbSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 12 | .r2 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x4001 then 0x30 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x4000, 4⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 256⟩]

theorem ecbEnc_implies : (ecbArm true).Implies (Spec.Cast5.ecbEncryptContract abi) := by
  sig_implies [Spec.Cast5.ecbEncryptContract, Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPre,
    Spec.Cast5.ecbPost, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, ecbArm]
    [ecbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using ecbSat

theorem ecbDec_implies : (ecbArm false).Implies (Spec.Cast5.ecbDecryptContract abi) := by
  sig_implies [Spec.Cast5.ecbDecryptContract, Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPre,
    Spec.Cast5.ecbPost, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, ecbArm]
    [ecbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using ecbSat

theorem ecbConsts_eq : ecbConsts = [(s1234Sym, s1234)] := rfl

/-- The memory of the witness with the table: the table at `0x100000`, the
stack argument (the working space at `0x3000`) at `0x4000` (irreducible:
unfolding it in a definitional check would evaluate the table). -/
@[irreducible] def ecbSatMem : Mem := fun a =>
  if (a - 0x100000).toNat < 4096 then constMem 0x100000 s1234 a else if a = 0x4001 then 0x30 else 0

theorem ecbSatMem_held : ∀ i < s1234.length,
    ecbSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0 := by
  intro i hi
  have hl : s1234.length = 512 := by rw [Impl.Cast5.s1234, table_length]
  rw [hl] at hi
  have hm : ecbSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 =
      (constMem 0x100000 s1234).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 := by
    apply Mem.readW_congr
    intro j hj
    have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x100000).toNat = 8 * i + j := by
      rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    unfold ecbSatMem
    rw [e, ite_eq_left (show 8 * i + j < 4096 by omega)]
  exact hm.trans (constMem_held 0x100000 s1234 (by rw [hl]; decide) i (by rw [hl]; exact hi))

/-- A state satisfying the precondition with the table. -/
def ecbSatC : State :=
  { ecbSat with mem := ecbSatMem, rd := [⟨0x1000, 128⟩, ⟨0x4000, 4⟩, ⟨0x100000, 4096⟩], syms := fun _ => 0x100000 }

theorem ecbSatC_arg : stackArg ecbSatC 0 = 0x3000 := by
  have e : stackArg ecbSatC 0 = ecbSat.mem.readW (stackArgAddr ecbSatC 0) 32 := by
    unfold stackArg
    apply Mem.readW_congr
    intro b hb
    change ecbSatMem _ = _
    unfold ecbSatMem
    have : ∀ b < 4, ¬ (stackArgAddr ecbSatC 0 + BitVec.ofNat 64 b - 0x100000).toNat < 4096 := by decide
    rw [ite_eq_right (this b (by omega))]
    rfl
  rw [e]; decide

theorem ecb_sat (up : Bool) :
    (Spec.Cast5.ecbContract (abi.withConsts ecbConsts) (if up then .encrypt else .decrypt)).pre ecbSatC := by
  have a := ecbSatC_arg
  have hl : s1234.length = 512 := by rw [Impl.Cast5.s1234, table_length]
  have held := ecbSatMem_held
  rw [ecbConsts_eq]
  generalize s1234 = W at hl held ⊢
  generalize e : ecbSatC = s at a
  sig_pre [Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPre, abi, argRegs, Arm.reduceClassify,
    Arm.Loc.val, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [a, hl]
  refine ⟨by decide, by decide, fun i hi => held i (by rw [hl]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 0⟩, ⟨0x3000, 256⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide)

theorem ecbC_implies (up : Bool) :
    (ecbArmC up).Implies (Spec.Cast5.ecbContract (abi.withConsts ecbConsts) (if up then .encrypt else .decrypt)) := by
  have hI : (ecbArm up).Implies (Spec.Cast5.ecbContract abi (if up then .encrypt else .decrypt)) := by
    cases up
    · exact ecbDec_implies
    · exact ecbEnc_implies
  exact
    { pre := fun s hs => ⟨hI.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
      post := fun s s' hs hp => post_consts.mpr (hI.post (stripConsts ecbConsts s) s' (pre_consts.mp hs).1 hp)
      pub := fun s₁ s₂ h₁ h₂ hp => ⟨hI.pub (stripConsts ecbConsts s₁) (stripConsts ecbConsts s₂)
          (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
        symAddr_eq_iff.mp ((pub_consts.mp hp).2 _ List.mem_cons_self)⟩
      sat := ⟨ecbSatC, ecb_sat up⟩ }

theorem ecbEncrypt_verified :
    Verified target ecbEncrypt (Spec.Cast5.ecbEncryptContract (abi.withConsts ecbConsts)) :=
  Verified.of_correct (ecbArmC_correct true) ecbEncrypt_constantTime (ecbC_implies true)

theorem ecbDecrypt_verified :
    Verified target ecbDecrypt (Spec.Cast5.ecbDecryptContract (abi.withConsts ecbConsts)) :=
  Verified.of_correct (ecbArmC_correct false) ecbDecrypt_constantTime (ecbC_implies false)

end VG.Proof.Cast5.Arm
