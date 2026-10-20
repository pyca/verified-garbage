module

import VerifiedGarbage.Proof.Blowfish.X86.KeyMain
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Blowfish.X86.KeyMain
public import VerifiedGarbage.Proof.Blowfish.X86.Contract
meta import VerifiedGarbage.Proof.Blowfish.X86.Contract
public import VerifiedGarbage.Proof.Blowfish.X86.Lit
meta import VerifiedGarbage.Proof.Blowfish.X86.Lit
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Blowfish.X86.Ecb
meta import VerifiedGarbage.Proof.Framework.X86.Inline
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Blowfish.Table
import VerifiedGarbage.Proof.Blowfish.X86.KeyEnc
import VerifiedGarbage.Proof.Blowfish.X86.KeyP
import VerifiedGarbage.Proof.Blowfish.X86.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Rc4.Scan32
import VerifiedGarbage.Proof.Rc4.Table
meta import VerifiedGarbage.Proof.Blowfish.Blocks
meta import VerifiedGarbage.Proof.Blowfish.Table
meta import VerifiedGarbage.Proof.Blowfish.X86.KeyEnc
meta import VerifiedGarbage.Proof.Blowfish.X86.KeyP
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
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) rd ad
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) rb ab
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
    exact congrArg _ (args ((k - 4) / 4) (by omega))

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
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) rs as
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) rb ab
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
    exact congrArg _ (args ((k - 4) / 4) (by omega))

theorem expandKey_ct : ConstantTime isa keyC.pre keyC.pub Impl.Blowfish.X86.expandKey :=
  VG.Taint.constantTime (A := taint) τK (fun _ _ h₁ h₂ hp => expandKey_agree h₁ h₂ hp) (by taint_decide)

theorem expandKey_verified : Verified target Impl.Blowfish.X86.expandKey (expandKeyScratch8Contract abi) :=
  Verified.of_correct expandKey_ok expandKey_ct key_implies

end VG.Proof.Blowfish.X86
