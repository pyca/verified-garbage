import VerifiedGarbage.Proof.Blowfish.Arm.KeyMain
import VerifiedGarbage.Proof.Blowfish.Arm.Lit
import VerifiedGarbage.Proof.Blowfish.Scratch
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Blowfish on ARMv7: the functions meet their contracts, with the working space as an argument

Constant time is the taint analysis's: the pointers, the key's length and
the count of blocks are public, and the working space (at `r3`) is a
writable region whose public slots keep the pointer and the counter public
through memory.
-/

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

/-- `vg_blowfish_expand_key` with `scratch: *mut [u64; 8]`. -/
def expandKeyScratch8Sig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("schedule", .array true .u8 4168),
    ("scratch", .array true .u64 8)]

/-- `expandKeyContract`, whatever `scratch` is. -/
def expandKeyScratch8Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandKeyScratch8Sig.contract A
    (pre := fun key keyLen schedule _scratch => expandKeyPre A.ptrBits key keyLen schedule)
    (post := fun key keyLen schedule _scratch => expandKeyPost A.ptrBits key keyLen schedule)
    (stack := stack)

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

theorem expandKey_ok (s : State) (hs : keyC.pre s) :
    ∃ t s', Exec isa Impl.Blowfish.Arm.expandKey s t s' ∧ abiPreserved s s' ∧ keyC.post s s' := by
  obtain ⟨v, rd, wr, ks, kb, sb, fK, fS, fB⟩ := hs
  obtain ⟨t, s', he, hp⟩ := expandKey_correct ⟨rd, wr, ks, kb, sb, fK, fS, fB, v⟩
  exact ⟨t, s', he, ⟨hp.regs, Exec.sp he⟩, hp.sched⟩

/-- The initial taint of key expansion: the arguments, and the schedule and
the working space, the writable regions, at `r2` and `r3`. -/
def τK : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [4168, 64], bases := [(.r2, 0), (.r3, 1)] }

theorem expandKey_agree {s₁ s₂ : State} (h₁ : keyC.pre s₁) (h₂ : keyC.pre s₂) (hp : keyC.pub s₁ s₂) :
    VG.Arm.Taint.Agree τK s₁ s₂ := by
  have wf : ∀ s, keyC.pre s → VG.Arm.Taint.Wf τK s := fun s ⟨_, _, wr, _, _, sb, _, fS, fB⟩ => by
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
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf _ h₁, wf _ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
    fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  · simp only [τK, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.2.1, h₂.2.2.1, p2, p3]

theorem expandKey_ct : ConstantTime isa keyC.pre keyC.pub Impl.Blowfish.Arm.expandKey :=
  VG.Taint.constantTime (A := VG.Arm.taint) τK (fun _ _ h₁ h₂ hp => expandKey_agree h₁ h₂ hp)
    (by taint_decide)

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

theorem expandKey_verified :
    Verified target Impl.Blowfish.Arm.expandKey (expandKeyScratch8Contract abi) := by
  refine Verified.of_correct (k := keyC) expandKey_ok expandKey_ct
    { pre := by
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
          [keySat, Spec.Blowfish.validKey] using keySat }

end VG.Proof.Blowfish.Arm
