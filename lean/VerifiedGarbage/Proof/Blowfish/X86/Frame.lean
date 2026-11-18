module

public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Impl.Blowfish.X86
import VerifiedGarbage.Proof.Blowfish.X86.Run
import VerifiedGarbage.Proof.Blowfish.X86.KeyMain
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Blowfish.X86.KeyMain
public import VerifiedGarbage.Proof.Blowfish.X86.Lit
meta import VerifiedGarbage.Proof.Blowfish.X86.Lit
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Blowfish.X86.Ecb
meta import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Blowfish.KeyTable
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Rc4.Scan32
import VerifiedGarbage.Proof.Rc4.Table
meta import VerifiedGarbage.Proof.Blowfish.Blocks
meta import VerifiedGarbage.Proof.Blowfish.KeyTable
meta import VerifiedGarbage.Proof.Blowfish.X86.Run
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.MlKem.X86.Leaf
meta import VerifiedGarbage.Proof.Rc4.Scan32
meta import VerifiedGarbage.Proof.Rc4.Table
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.SigEval
public import VerifiedGarbage.Proof.Blowfish.Scratch
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Blowfish.Scratch
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.Proof.Framework.X86.Taint

/-! ### `Blowfish.X86.Verified`, which only this module used -/

section

/-! ### `Blowfish.X86.Contract`, which this module and modules that import it used -/

section

/-!
# Blowfish on x86 (32-bit): the contracts the proofs use

`Proof.Blowfish.ecbScratchContract` and
`Proof.Blowfish.expandKeyScratch8Contract` spelled out for x86: `ecbC`,
with the arguments only read (the taint analysis follows them in memory only
while nothing that may alias them is written), and `keyC`. `wideEcb` lets
the code write the arguments, as the shared contract does, and implies it;
`Verified.lean` narrows it back.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86
open VG VG.X86 VG.Spec.Blowfish VG.Proof.Blowfish

def dir (up : Bool) : Direction := if up then .encrypt else .decrypt

def ecbC (up : Bool) : Contract isa where
  pre s :=
    let sch : Region := ⟨(arg s 0).setWidth 64, 4168⟩
    let data : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat * 8⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 256⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sch, args] ∧ s.wr = [data, scratch] ∧ sch.Disjoint data ∧ sch.Disjoint scratch ∧
      data.Disjoint scratch ∧ args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧
      ret.Disjoint scratch ∧ (arg s 0).toNat + 4168 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + (arg s 2).toNat * 8 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 256 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    blocksAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      ecb (scheduleAt s.mem ((arg s 0).setWidth 64)) (dir up)
        (blocksAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

/-- `ecbC`, with the arguments writable. -/
def wideEcb (up : Bool) : Contract isa :=
  { ecbC up with
    pre := fun s =>
      let sch : Region := ⟨(arg s 0).setWidth 64, 4168⟩
      let data : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat * 8⟩
      let scratch : Region := ⟨(arg s 3).setWidth 64, 256⟩
      let args : Region := ⟨argAddr s 0, 16⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      s.rd = [sch] ∧ s.wr = [data, scratch, args] ∧ sch.Disjoint data ∧ sch.Disjoint scratch ∧
        data.Disjoint scratch ∧ args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧
        ret.Disjoint scratch ∧ (arg s 0).toNat + 4168 ≤ 2 ^ 32 ∧
        (arg s 1).toNat + (arg s 2).toNat * 8 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 256 ≤ 2 ^ 32 ∧
        (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧ args.Disjoint sch }

def keyC : Contract isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let sch : Region := ⟨(arg s 2).setWidth 64, 4168⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 64⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, args] ∧ s.wr = [sch, scratch] ∧ key.Disjoint sch ∧ key.Disjoint scratch ∧
      sch.Disjoint scratch ∧ args.Disjoint sch ∧ args.Disjoint scratch ∧ ret.Disjoint sch ∧
      ret.Disjoint scratch ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 4168 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 64 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧ validKey (arg s 1).toNat
  post s s' :=
    scheduleAt s'.mem ((arg s 2).setWidth 64) =
      expandKey (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

/-- `ecb(0x1000, 0x2000, 0, 0x3000)`. -/
def ecbSat : State where
  gpr r := if r = .esp then 0x6000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6005 then 0x10 else if a = 0x6009 then 0x20 else if a = 0x6011 then 0x30 else 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 256⟩, ⟨0x6004, 16⟩]

/-- `expand_key(0x1000, 4, 0x2000, 0x4000)`. -/
def keySat : State where
  gpr r := if r = .esp then 0x6000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6005 then 0x10 else if a = 0x6008 then 4 else if a = 0x600d then 0x20 else
    if a = 0x6011 then 0x40 else 0
  rd := [⟨0x1000, 4⟩, ⟨0x6004, 16⟩]
  wr := [⟨0x2000, 4168⟩, ⟨0x4000, 64⟩]

tactic_template "bf_pre" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
    intro s h
    sig_pre [$ls,*] at h
    sig_split h
    sig_reduce [$ls,*]
    sig_simp [$ls,*] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega))

theorem ecb_implies (up : Bool) : (wideEcb up).Implies (ecbScratchContract abi (dir up)) where
  pre := by
    bf_pre [ecbScratchContract, ecbScratchSig, ecbPost, abi, argSlots, argVal, argBytes, wideEcb, ecbC]
  post := by
    sig_implies_post [ecbScratchContract, ecbScratchSig, ecbPost, abi, argSlots, argVal, argBytes,
      wideEcb, ecbC]
  pub := by
    sig_implies_pub [ecbScratchContract, ecbScratchSig, ecbPost, abi, argSlots, argVal, argBytes,
      wideEcb, ecbC]
  sat := by
    refine ⟨ecbSat, ?_⟩
    have h0 : (arg ecbSat 2).toNat = 0 := by decide
    sig_pre [ecbScratchContract, ecbScratchSig, ecbPost, abi, argSlots, argVal, argBytes, wideEcb, ecbC]
    sig_and_intros
    -- The data is empty.
    all_goals first
      | rfl
      | decide
      | (intro a _ h₂; simp only [Region.Contains, h0] at h₂; omega)
      | exact Region.disjoint_of_sep (by decide)

theorem key_implies : keyC.Implies (expandKeyScratch8Contract abi) where
  pre := by
    bf_pre [expandKeyScratch8Contract, expandKeyScratch8Sig, expandKeyPre, expandKeyPost, abi, argSlots,
      argVal, argBytes, keyC, validKey]
  post := by
    sig_implies_post [expandKeyScratch8Contract, expandKeyScratch8Sig, expandKeyPre, expandKeyPost, abi, argSlots,
      argVal, argBytes, keyC, validKey]
  pub := by
    sig_implies_pub [expandKeyScratch8Contract, expandKeyScratch8Sig, expandKeyPre, expandKeyPost, abi, argSlots,
      argVal, argBytes, keyC, validKey]
  sat := by
    sig_implies_sat [expandKeyScratch8Contract, expandKeyScratch8Sig, expandKeyPre, expandKeyPost, abi, argSlots,
      argVal, argBytes, keyC, validKey]
      [keySat, arg, argAddr, Mem.readW, Mem.read] using keySat

end VG.Proof.Blowfish.X86

end

end

/-!
# Blowfish on x86 (32-bit): the functions meet their contracts, with the working space as an argument

Constant time is the taint analysis's: the pointers, the key's length and
the count of blocks are public, and the working space (the fourth argument)
is a writable region whose public slots keep the pointer and the counter
public through memory. ECB meets `ecbC`, with its arguments only read; the
shared contract lets the code write them too (`wideEcb`), which
`Verified.narrowTo` allows.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86
open VG VG.X86 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-! ## ECB -/

theorem ecbPre_of {up : Bool} {s : State} (hs : (ecbC up).pre s) : EcbPre s := by
  obtain ⟨hrd, hwr, kd, kb, db, ad, ab, rd, rb, fK, fD, fB, fsp⟩ := hs
  rw [Nat.mul_comm] at hwr kd db ad rd fD
  exact ⟨hrd, hwr, kd, kb, db, ad, ab, rd, rb, fK, fD, fB, fsp⟩

theorem ecb_ok (up : Bool) (s : State) (hs : (ecbC up).pre s) :
    ∃ t s', Exec isa (Impl.Blowfish.X86.ecb up) s t s' ∧ abiPreserved s s' ∧ (ecbC up).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_correct (ecbPre_of hs) up
  exact ⟨t, s', he, ha, hp⟩

/-- The initial taint of ECB: the stack pointer, and the data and the
working space, the writable regions, at the arguments 8 and 16 bytes up. -/
def τE : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 256], argLen := 20, argBases := [(8, 0), (16, 1)] }

theorem τE_wf {up : Bool} {s : State} (hs : (ecbC up).pre s) : VG.X86.Taint.Wf τE s := by
  obtain ⟨_, hwr, _, _, db, ad, ab, rd, rb, _, fD, fB, fsp⟩ := hs
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨fsp, ?_⟩, ?_⟩
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨db, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [fsp]) rd ad
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [fsp]) rb ab
  · intro p hp
    simp only [τE, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]

theorem ecb_agree {up : Bool} {s t : State} (hs : (ecbC up).pre s) (ht : (ecbC up).pre t)
    (hp : (ecbC up).pub s t) : VG.X86.Taint.Agree τE s t := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, (ecbC up).pre s → (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 := by
    intro s hs; obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h⟩ := hs; exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, τE_wf hs, τE_wf ht,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τE, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [hs.2.1, ht.2.1, args 1 (by decide), args 2 (by decide), args 3 (by decide)]
  · simp only [τE] at hk
    rw [show VG.X86.Taint.depth τE.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (fit _ hs) h4 hk, VG.X86.Taint.argByte_eq (fit _ ht) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega_using [hk]))

theorem ecb_ct (up : Bool) : ConstantTime isa (ecbC up).pre (ecbC up).pub (Impl.Blowfish.X86.ecb up) := by
  cases up
  · exact VG.Taint.constantTime (A := taint) τE (fun _ _ h₁ h₂ hp => ecb_agree h₁ h₂ hp)
      (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) τE (fun _ _ h₁ h₂ hp => ecb_agree h₁ h₂ hp)
      (by taint_decide)

def ecbRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, 4168⟩, ⟨argAddr s 0, 16⟩]
def ecbWr (s : State) : List Region :=
  [⟨(arg s 1).setWidth 64, (arg s 2).toNat * 8⟩, ⟨(arg s 3).setWidth 64, 256⟩]

tactic_template "narrow_blowfish_x86_verified" : tactic => `(tactic| simp only [VG.Proof.Blowfish.X86.ecbC, VG.Proof.Blowfish.X86.wideEcb,
                     VG.Proof.Blowfish.X86.ecbRd, VG.Proof.Blowfish.X86.ecbWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr])
tactic_template "narrow_blowfish_x86_verified" loc:Lean.Parser.Tactic.location : tactic => `(tactic| simp only [VG.Proof.Blowfish.X86.ecbC, VG.Proof.Blowfish.X86.wideEcb,
                     VG.Proof.Blowfish.X86.ecbRd, VG.Proof.Blowfish.X86.ecbWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $loc)

theorem wideEcb_pre (up : Bool) (s : State) (h : (wideEcb up).pre s) :
    (ecbC up).pre (s.withRegions (ecbRd s) (ecbWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow_blowfish_x86_verified
  exact ⟨trivial, trivial, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1⟩

theorem ecb_verified (up : Bool) :
    Verified target (Impl.Blowfish.X86.ecb up) (ecbScratchContract abi (dir up)) := by
  have hsat := (ecb_implies up).sat_left
  have narrowSat : ∃ s, (ecbC up).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wideEcb_pre up s hs⟩
  apply Verified.of_implies _ (ecb_implies up)
  refine Verified.narrowTo (Verified.of_correct (ecb_ok up) (ecb_ct up) (.refl narrowSat))
    ecbRd ecbWr (wideEcb_pre up) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [ecbRd, ecbWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp only [h, true_or, or_true]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [ecbWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp only [h, true_or, or_true]
  · intro s s' _ h
    narrow_blowfish_x86_verified at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow_blowfish_x86_verified
    exact h

/-! ## Key expansion -/

theorem expandKey_ok (s : State) (hs : keyC.pre s) :
    ∃ t s', Exec isa Impl.Blowfish.X86.expandKey s t s' ∧ abiPreserved s s' ∧ keyC.post s s' := by
  obtain ⟨hrd, hwr, ks, kb, sb, as, ab, rs, rb, fKey, fSch, fBuf, fsp, valid⟩ := hs
  obtain ⟨t, s', he, ha, hp⟩ :=
    expandKey_correct ⟨hrd, hwr, ks, kb, sb, as, ab, rs, rb, fKey, fSch, fBuf, fsp, valid⟩
  exact ⟨t, s', he, ha, hp⟩

/-- The initial taint of key expansion: the stack pointer, and the schedule
and the working space, the writable regions, at the arguments 12 and 16
bytes up. -/
def τK : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [4168, 64], argLen := 20, argBases := [(12, 0), (16, 1)] }

theorem τK_wf {s : State} (hs : keyC.pre s) : VG.X86.Taint.Wf τK s := by
  obtain ⟨_, hwr, _, _, sb, as, ab, rs, rb, _, fS, fB, fsp, _⟩ := hs
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨fsp, ?_⟩, ?_⟩
  · rw [hwr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨sb, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [fsp]) rs as
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [fsp]) rb ab
  · intro p hp
    simp only [τK, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]

theorem expandKey_agree {s t : State} (hs : keyC.pre s) (ht : keyC.pre t) (hp : keyC.pub s t) :
    VG.X86.Taint.Agree τK s t := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, keyC.pre s → (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 := by
    intro s hs; obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := hs; exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, τK_wf hs, τK_wf ht,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τK, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [hs.2.1, ht.2.1, args 2 (by decide), args 3 (by decide)]
  · simp only [τK] at hk
    rw [show VG.X86.Taint.depth τK.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (fit _ hs) h4 hk, VG.X86.Taint.argByte_eq (fit _ ht) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega_using [hk]))

theorem expandKey_ct : ConstantTime isa keyC.pre keyC.pub Impl.Blowfish.X86.expandKey :=
  VG.Taint.constantTime (A := taint) τK (fun _ _ h₁ h₂ hp => expandKey_agree h₁ h₂ hp) (by taint_decide)

theorem expandKey_verified : Verified target Impl.Blowfish.X86.expandKey (expandKeyScratch8Contract abi) :=
  Verified.of_correct expandKey_ok expandKey_ct key_implies

end VG.Proof.Blowfish.X86

end

end

/-!
# Blowfish on x86 (32-bit), with the working space on the stack

Key expansion and ECB keep our caller's `ebx`, `esi`, `edi` and `ebp`, the
halves, F, and their pointer and counter in working space that was their
fourth argument: they run their code, proved with it as an argument
(`Verified.lean`), in a frame that allocates it and copies their three
argument slots, and zero the 40 bytes of it they use after the code
(`Verified.stackScratchWiped`): 84 bytes for key expansion (64 of working
space) and 276 for ECB (256). The code uses no other stack.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86

open VG VG.X86

/-- A state satisfying `vg_blowfish_expand_key`'s precondition: a 4-byte key
at `0x1000` and the schedule at `0x2000`, as stack arguments at `0x8004`. -/
def expandKeyFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 4 else if a = 0x800d then 0x20 else 0
  rd := [⟨0x1000, 4⟩, ⟨0x8004, 12⟩]
  wr := [⟨0x2000, 4168⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Blowfish.expandKeyContract X86.abi 84).pre s := by
  implies_sat [Spec.Blowfish.expandKeyContract, Spec.Blowfish.expandKeySig, Spec.Blowfish.expandKeyPre,
    Spec.Blowfish.expandKeyPost, Spec.Blowfish.validKey, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [expandKeyFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using expandKeyFrameSat

theorem expandKey_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 84 3 10 Impl.Blowfish.X86.expandKey)
      (Spec.Blowfish.expandKeyContract X86.abi 84) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.expandKeySig) (nm := "scratch") (e := .u64) (n := 8)
    (pre := Spec.Blowfish.expandKeyPre X86.abi.ptrBits) (post := Spec.Blowfish.expandKeyPost X86.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 84)
    expandKey_verified (by decide) (by decide +kernel) (by decide +kernel) (by decide)
    (Proof.Blowfish.expandKeyPre_local _) (Proof.Blowfish.expandKeyPost_local _)
    (Proof.Blowfish.expandKeyPostOut_local _) expandKeyFrameSat_pre

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000` and no data at `0x2000`, as stack arguments at `0x8004`, which are
writable. -/
def ecbFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x8004, 12⟩]

theorem ecbFrameSat_pre (d : Spec.Blowfish.Direction) :
    ∃ s, (Spec.Blowfish.ecbContract X86.abi d 276).pre s := by
  have h0 : (X86.arg ecbFrameSat 2).toNat = 0 := by decide
  refine ⟨ecbFrameSat, ?_⟩
  sig_pre [Spec.Blowfish.ecbContract, Spec.Blowfish.ecbSig, Spec.Blowfish.ecbPost, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
  sig_and_intros
  -- The data is empty.
  all_goals first
    | rfl
    | decide
    | (intro a _ h₂; simp only [Region.Contains, h0] at h₂; omega)
    | exact Region.disjoint_of_sep (by decide)

theorem ecb_framed (up : Bool) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 276 3 10 (Impl.Blowfish.X86.ecb up))
      (Spec.Blowfish.ecbContract X86.abi (dir up) 276) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.ecbSig) (nm := "scratch") (e := .u64) (n := 32)
    (post := Spec.Blowfish.ecbPost (dir up) X86.abi.ptrBits) (wa := true) (stack := 0) (bytes := 276)
    (ecb_verified up) (by decide) (by cases up <;> lit_decide) (by cases up <;> lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Blowfish.ecbPost_local _ (dir up))
    (Proof.Blowfish.ecbPostOut_local _ (dir up)) (ecbFrameSat_pre (dir up))

end VG.Proof.Blowfish.X86
