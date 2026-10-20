module

import VerifiedGarbage.Proof.Blowfish.Arm.KeyMain
public import VerifiedGarbage.Proof.Blowfish.Scratch
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Blowfish.Arm.Ecb
import VerifiedGarbage.Proof.Blowfish.Arm.Lit
public import VerifiedGarbage.Impl.Blowfish.Arm
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Blowfish.Arm.KeyMain
meta import VerifiedGarbage.Proof.Blowfish.Scratch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Blowfish.Arm.Ecb
meta import VerifiedGarbage.Proof.Blowfish.Arm.Lit
meta import VerifiedGarbage.Impl.Blowfish.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Exec

/-!
# Blowfish on ARMv7: the functions meet their contracts, with the working space as an argument

Constant time is the taint analysis's: the pointers, the key's length and
the count of blocks are public, as is the address of key expansion's table
(`taintSym`), and the working space (at `r3`) is a
writable region whose public slots keep the pointer and the counter public
through memory.
-/

@[expose] public section

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

def dir (up : Bool) : Direction := if up then .encrypt else .decrypt

/-! ## ECB -/

/-- The ECB contract as the code sees it. -/
def ecbC (up : Bool) : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 4168⟩
    let data : Region := ⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩
    let buf : Region := ⟨State.addr (s.gpr .r3), 256⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧ data.Disjoint buf ∧
      (s.gpr .r0).toNat + 4168 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 8 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 256 ≤ 2 ^ 32
  post s s' :=
    blocksAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      ecb (scheduleAt s.mem (State.addr (s.gpr .r0))) (dir up)
        (blocksAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

theorem ecb_ok (up : Bool) (s : State) (hs : (ecbC up).pre s) :
    ∃ t s', Exec isa (Impl.Blowfish.Arm.ecb up) s t s' ∧ abiPreserved s s' ∧ (ecbC up).post s s' := by
  obtain ⟨rd, wr, kd, kb, db, fK, fD, fB⟩ := hs
  obtain ⟨t, s', he, hp⟩ := ecb_correct ⟨rd, wr, kd, kb, db, fK, fD, fB⟩ up
  exact ⟨t, s', he, ⟨hp.regs, Exec.sp he⟩, hp.blocks⟩

/-- The initial taint of ECB: the arguments, and the working space, the
second writable region, at `r3`. -/
def τE : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [0, 256], bases := [(.r3, 1)] }

theorem ecb_agree (up : Bool) {s₁ s₂ : State} (h₁ : (ecbC up).pre s₁) (h₂ : (ecbC up).pre s₂)
    (hp : (ecbC up).pub s₁ s₂) : VG.Arm.Taint.Agree τE s₁ s₂ := by
  have wf : ∀ s, (ecbC up).pre s → VG.Arm.Taint.Wf τE s := fun s ⟨_, wr, _, _, db, _, fD, fB⟩ => by
    refine ⟨fun _ => ⟨by simp [wr, τE], ?_, ?_⟩, ?_, fun h => absurd h (by decide),
      fun _ h => (List.not_mem_nil h).elim⟩
    · simp only [wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
        List.Pairwise.nil]
      exact ⟨db, fun _ h => h.elim, trivial⟩
    · simp only [wr, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only [State.addr, BitVec.toNat_setWidth] <;> omega
    · intro p hp'
      simp only [τE, List.mem_singleton] at hp'; subst hp'
      simp [VG.Arm.Taint.region, wr]
  obtain ⟨psp, p0, p1, p2, p3⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf _ h₁, wf _ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
    fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  · simp only [τE, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p1, p2, p3]

theorem ecb_ct (up : Bool) : ConstantTime isa (ecbC up).pre (ecbC up).pub (Impl.Blowfish.Arm.ecb up) := by
  cases up
  · exact VG.Taint.constantTime (A := VG.Arm.taint) τE (fun _ _ h₁ h₂ hp => ecb_agree false h₁ h₂ hp)
      (by taint_decide)
  · exact VG.Taint.constantTime (A := VG.Arm.taint) τE (fun _ _ h₁ h₂ hp => ecb_agree true h₁ h₂ hp)
      (by taint_decide)

/-- `ecb(0x1000, 0x3000, 0, 0x4000)`. -/
def ecbSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 256⟩]

theorem ecb_verified (up : Bool) :
    Verified target (Impl.Blowfish.Arm.ecb up) (Proof.Blowfish.ecbScratchContract abi (dir up)) := by
  refine Verified.of_correct (k := ecbC up) (ecb_ok up) (ecb_ct up) ?_
  sig_implies [Proof.Blowfish.ecbScratchContract, Proof.Blowfish.ecbScratchSig, Spec.Blowfish.ecbPost, abi,
    argRegs, Arm.reduceClassify, Arm.Loc.val, ecbC, State.addr] [ecbSat] using ecbSat

/-! ## Key expansion -/

/-- The key expansion contract as the code sees it. -/
def keyC : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let sch : Region := ⟨State.addr (s.gpr .r2), 4168⟩
    let buf : Region := ⟨State.addr (s.gpr .r3), 64⟩
    validKey (s.gpr .r1).toNat ∧ s.rd = [key] ∧ s.wr = [sch, buf] ∧ key.Disjoint sch ∧ key.Disjoint buf ∧
      sch.Disjoint buf ∧ (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 4168 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 64 ≤ 2 ^ 32
  post s s' :=
    scheduleAt s'.mem (State.addr (s.gpr .r2)) =
      expandKey (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

theorem initConsts_eq : initConsts = [(initSym, Impl.Blowfish.initWords)] := rfl

theorem initWords_length : Impl.Blowfish.initWords.length = 521 := by simp [Impl.Blowfish.initWords]

/-- What the calling convention says of the table (`ConstsOk`), as the proof
needs it: the initial schedule's image at the table's address, which does not
wrap around and is apart from the writable regions, and the table's region
last among the readable ones. -/
theorem consts_init {st : Nat} {s : State} (hc : ConstsOk initConsts st s) :
    (∀ i < 521, s.mem.readW (State.addr (s.syms initSym) + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.Blowfish.initWords.getD i 0) ∧ (s.syms initSym).toNat + 4168 ≤ 2 ^ 32 ∧
      (∀ r ∈ s.wr, (⟨State.addr (s.syms initSym), 4168⟩ : Region).Disjoint r) ∧
      s.rd.drop (s.rd.length - 1) = [⟨State.addr (s.syms initSym), 4168⟩] := by
  have hf := hc.fit (name := initSym) (ws := Impl.Blowfish.initWords) List.mem_cons_self
  obtain ⟨hd, hh, ht⟩ := hc
  have e : constRegs initConsts s = [⟨State.addr (s.syms initSym), 4168⟩] := by
    rw [constRegs, initConsts_eq, Abi.constRegions_cons, Abi.constRegions_nil, initWords_length]; rfl
  have hl : initConsts.length = 1 := rfl
  rw [e, hl] at hd
  rw [e] at ht
  rw [initWords_length] at hf
  have hm : (initSym, Impl.Blowfish.initWords) ∈ initConsts := by rw [initConsts_eq]; exact List.mem_cons_self
  have hh' := hh _ hm
  simp only at hh'
  rw [initWords_length] at hh'
  exact ⟨hh', hf,
    (List.forall_mem_singleton.mp ht).2.1, hd⟩

theorem expandKey_ok (s : State) (hs : keyC.pre (stripConsts initConsts s)) (hc : ConstsOk initConsts 0 s) :
    ∃ t s', Exec isa Impl.Blowfish.Arm.expandKey s t s' ∧ abiPreserved s s' ∧ keyC.post s s' := by
  obtain ⟨v, rd, wr, ks, kb, sb, fK, fS, fB⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr] at wr ks kb sb fK fS fB v
  obtain ⟨held, fitT, tw, td⟩ := consts_init hc
  have hrd : s.rd = [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, ⟨State.addr (s.syms initSym), 4168⟩] := by
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, td]
    have h' : s.rd.take (s.rd.length - initConsts.length) = _ := rd
    exact congrArg (· ++ _) h'
  obtain ⟨t, s', he, hp⟩ := expandKey_correct ⟨hrd, wr, ks, kb, sb, fK, fS, fB, v, held, fitT,
    tw _ (by rw [wr]; exact List.mem_cons_self), tw _ (by rw [wr]; simp)⟩
  exact ⟨t, s', he, ⟨hp.regs, Exec.sp he⟩, hp.sched⟩

/-- The initial taint of key expansion: the arguments, and the schedule and
the working space, the writable regions, at `r2` and `r3`. -/
def τK : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [4168, 64], bases := [(.r2, 0), (.r3, 1)] }

theorem expandKey_agree {s₁ s₂ : State} (h₁ : keyC.pre (stripConsts initConsts s₁))
    (h₂ : keyC.pre (stripConsts initConsts s₂)) (hp : keyC.pub s₁ s₂) : VG.Arm.Taint.Agree τK s₁ s₂ := by
  have wf : ∀ s, keyC.pre (stripConsts initConsts s) → VG.Arm.Taint.Wf τK s :=
    fun s ⟨_, _, wr, _, _, sb, _, fS, fB⟩ => by
    simp only [stripConsts_gpr, stripConsts_wr] at wr sb fS fB
    refine ⟨fun _ => ⟨by simp [wr, τK], ?_, ?_⟩, ?_, fun h => absurd h (by decide),
      fun _ h => (List.not_mem_nil h).elim⟩
    · simp only [wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
        List.Pairwise.nil]
      exact ⟨sb, fun _ h => h.elim, trivial⟩
    · simp only [wr, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only [State.addr, BitVec.toNat_setWidth] <;> omega
    · intro p hp'
      simp only [τK, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl <;> simp [VG.Arm.Taint.region, wr]
  obtain ⟨psp, p0, p1, p2, p3⟩ := hp
  have w₁ := h₁.2.2.1
  have w₂ := h₂.2.2.1
  simp only [stripConsts_wr, stripConsts_gpr] at w₁ w₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf _ h₁, wf _ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
    fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  · simp only [τK, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [w₁, w₂, p2, p3]

/-- Key expansion's contract with the table, as the proof states it. -/
def keyCC : Contract isa where
  pre s := keyC.pre (stripConsts initConsts s) ∧ ConstsOk initConsts 0 s
  post := keyC.post
  pub s₁ s₂ := keyC.pub s₁ s₂ ∧ s₁.syms initSym = s₂.syms initSym

theorem expandKey_ct : ConstantTime isa keyCC.pre keyCC.pub Impl.Blowfish.Arm.expandKey :=
  VG.Taint.constantTime (A := taintSym [initSym]) τK (fun _ _ h₁ h₂ hp => ⟨expandKey_agree h₁.1 h₂.1 hp.1,
    fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hp.2⟩) (by taint_decide)

/-- `expand_key(0x1000, 4, 0x2000, 0x4000)`. -/
def keySat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 4 | .r2 => 0x2000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 4⟩]
  wr := [⟨0x2000, 4168⟩, ⟨0x4000, 64⟩]

theorem key_implies : keyC.Implies (expandKeyScratch8Contract abi) where
  pre := by
    intro s h
    sig_pre [expandKeyScratch8Contract, expandKeyScratch8Sig, Spec.Blowfish.expandKeyPre,
      Spec.Blowfish.expandKeyPost, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, keyC, State.addr] at h
    obtain ⟨_, rd, wr, ks, kb, sb, fK, fS, fB, v⟩ := h
    exact ⟨v, rd, wr, ks, kb, sb, fK, fS, fB⟩
  post := by sig_implies_post [expandKeyScratch8Contract, expandKeyScratch8Sig, Spec.Blowfish.expandKeyPre,
      Spec.Blowfish.expandKeyPost, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, keyC, State.addr]
  pub := by sig_implies_pub [expandKeyScratch8Contract, expandKeyScratch8Sig, Spec.Blowfish.expandKeyPre,
      Spec.Blowfish.expandKeyPost, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, keyC, State.addr]
  sat := by sig_implies_sat [expandKeyScratch8Contract, expandKeyScratch8Sig, Spec.Blowfish.expandKeyPre,
      Spec.Blowfish.expandKeyPost, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, keyC, State.addr]
      [keySat, Spec.Blowfish.validKey] using keySat

/-- The memory of the witness with the table: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def keySatMem : Mem := constMem 0x100000 Impl.Blowfish.initWords

theorem keySatMem_held : ∀ i < Impl.Blowfish.initWords.length,
    keySatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = Impl.Blowfish.initWords.getD i 0 := by
  unfold keySatMem
  exact constMem_held _ _ (by rw [initWords_length]; decide)

/-- A state satisfying the precondition with the table. -/
def keySatC : State :=
  { keySat with mem := keySatMem, rd := [⟨0x1000, 4⟩, ⟨0x100000, 4168⟩], syms := fun _ => 0x100000 }

theorem key_sat : (expandKeyScratch8Contract (abi.withConsts initConsts)).pre keySatC := by
  have hl : Impl.Blowfish.initWords.length = 521 := initWords_length
  have held := keySatMem_held
  rw [initConsts_eq]
  generalize Impl.Blowfish.initWords = W at hl held ⊢
  generalize e : keySatC = s
  sig_pre [expandKeyScratch8Contract, expandKeyScratch8Sig, Spec.Blowfish.expandKeyPre, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    Spec.Blowfish.validKey]
  subst e
  rw [hl]
  refine ⟨by decide, by decide, fun i hi => held i (by rw [hl]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 4168⟩, ⟨0x4000, 64⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide)

theorem keyCC_implies : keyCC.Implies (expandKeyScratch8Contract (abi.withConsts initConsts)) where
  pre _ hs := ⟨key_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
  post s s' hs hp := post_consts.mpr (key_implies.post (stripConsts initConsts s) s' (pre_consts.mp hs).1 hp)
  pub s₁ s₂ h₁ h₂ hp := ⟨key_implies.pub (stripConsts initConsts s₁) (stripConsts initConsts s₂)
      (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
    symAddr_eq_iff.mp ((pub_consts.mp hp).2 _ List.mem_cons_self)⟩
  sat := ⟨keySatC, key_sat⟩

theorem expandKey_verified :
    Verified target Impl.Blowfish.Arm.expandKey (expandKeyScratch8Contract (abi.withConsts initConsts)) :=
  Verified.of_correct (k := keyCC) (fun s (hs : keyCC.pre s) => expandKey_ok s hs.1 hs.2) expandKey_ct keyCC_implies

end VG.Proof.Blowfish.Arm
