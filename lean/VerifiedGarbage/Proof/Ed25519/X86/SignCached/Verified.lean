module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Ed25519.X86.SignCached
public import VerifiedGarbage.Proof.Sha512.X86.Lit
public import VerifiedGarbage.Proof.Ed25519.X86.ScalarLit
public import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit
public import VerifiedGarbage.Proof.Ed25519.X86.MulAddLit
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
import VerifiedGarbage.Proof.Ed25519.Expanded
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.Ed25519.X86.SignCached
meta import VerifiedGarbage.Proof.Sha512.X86.Lit
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarLit
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit
meta import VerifiedGarbage.Proof.Ed25519.X86.MulAddLit
meta import VerifiedGarbage.Spec.Ed25519.ExpandedSign
meta import VerifiedGarbage.Proof.Ed25519.Expanded
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Ed25519.X86.Whole.CallCT
import VerifiedGarbage.Proof.Ed25519.X86.Whole.BlocksCT
public import VerifiedGarbage.Proof.Ed25519.X86.SignCached.MulAdd
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe
import VerifiedGarbage.Proof.Ed25519.X86.Whole.CopyDigest
public import VerifiedGarbage.Proof.Ed25519.X86.SignCached.HashUpdate
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Prune
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
public import VerifiedGarbage.Proof.Ed25519.X86.Whole.Reduce
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.CallCT
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.BlocksCT
meta import VerifiedGarbage.Proof.Ed25519.X86.SignCached.MulAdd
meta import VerifiedGarbage.Proof.Ed25519.VerifyBytes
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.CopyDigest
meta import VerifiedGarbage.Proof.Ed25519.X86.SignCached.HashUpdate
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Prune
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Ed25519.Signing
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.Reduce
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Ed25519.X86.CombLit
import VerifiedGarbage.Proof.Ed25519.X86.PointCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.NormNum.Prime
meta import Mathlib.Data.Nat.Totient
meta import Mathlib.Tactic.Positivity.Finset
meta import Mathlib.Algebra.Order.Field.Basic
meta import Mathlib.Tactic.NormNum.GCD
meta import Mathlib.Data.Sym.Sym2.Init
meta import Mathlib.Tactic.ContinuousFunctionalCalculus
meta import Mathlib.Tactic.Push
meta import VerifiedGarbage.Proof.Ed25519.X86.CombLit
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTBlocks
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import Mathlib.Data.Nat.Basic
meta import Mathlib.Order.RelClasses
import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Hash
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Count
meta import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Hash
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.Count
public import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Args
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Args
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Calls
public import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
public import VerifiedGarbage.Proof.Ed25519.X86.Whole.Hash
import VerifiedGarbage.Proof.Framework.X86.CallWith
import Mathlib.Tactic.ToAdditive
meta import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Calls
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.Hash
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import Mathlib.Tactic.ToAdditive

/-! ### `Ed25519.X86.SignCached.Base`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached
open VG.Impl.Ed25519.X86 (scalarBase combSym)
open VG.Impl.Ed25519.X86.PublicKey (callWith)

def baseRd (L : Lay) : List Region := [field L 96, ⟨L.E.setWidth 64, 12⟩, L.TB]
def baseOut (L : Lay) : Region := ⟨L.out.setWidth 64, 32⟩
def baseWr (L : Lay) : List Region := [baseOut L, L.SCR]
def BaseArgs (L : Lay) (t : State) : Prop :=
  Whole.slots L.E t 0 = L.out ∧ Whole.slots L.E t 1 = fp L 96 ∧ Whole.slots L.E t 2 = L.scr

theorem base_nosp : NoSp scalarBase := NoSp.of_all (by lit_decide)
theorem base_stack : stackUse scalarBase = 8 := by lit_decide

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem base_pre (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : BaseArgs L s) (hy : s.syms combSym = L.T)
    (ht : TblWords (L.T.setWidth 64) s.mem) :
    scalarBaseLocal.pre (s.callEntry.withRegions (baseRd L) (baseWr L)) := by
  have H := hashSpace hL
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hc.esp H.below H.frameFit hj
  have a0 := (ca (j := 0) (by decide)).trans ha.1
  have a1 := (ca (j := 1) (by decide)).trans ha.2.1
  have a2 := (ca (j := 2) (by decide)).trans ha.2.2
  have ae := Whole.arg_base hc.esp (baseRd L) (baseWr L)
  have ret : Region.Sub ⟨(L.E - 4).setWidth 64, 4⟩ L.STK := Whole.below_sub_stack H.below (by decide)
  have args : Region.Sub ⟨L.E.setWidth 64, 12⟩ L.STK :=
    fun p hp => Whole.frame_sub L.E p (Region.sub_prefix (by decide) p hp)
  have out : Region.Sub (baseOut L) L.OUT := Region.sub_prefix (by decide)
  have be := hL.below
  have stk : Region.Sub (below (L.E - BitVec.ofNat 32 4) 8) L.STK := Whole.inner_sub_stack be
  have hf : L.E.toNat + 256 ≤ 2 ^ 32 := by have := hL.top; omega_using [this]
  have tb : L.TB ∈ L.inputs := by simp [Lay.inputs]
  have tw : TblWords (L.T.setWidth 64) s.callEntry.mem :=
    ht.frame (Whole.callEntry_frame s) fun r hr => by
      rw [List.mem_singleton.mp hr, hc.esp]
      exact (hL.ks _ tb).symm.sub_right (Whole.below_sub_stack be (by decide))
  have cy : (s.callEntry.withRegions (baseRd L) (baseWr L)).syms combSym = L.T := hy
  have cs : callStk (s.callEntry.withRegions (baseRd L) (baseWr L)) = below (L.E - BitVec.ofNat 32 4) 8 := by
    simp only [callStk, State.withRegions_gpr, State.callEntry_esp, hc.esp]; rfl
  simp only [scalarBaseLocal, BaseRegions, CombHeld, cy, cs, State.withRegions_rd, State.withRegions_wr,
    arg_withRegions, State.withRegions_gpr, State.withRegions_mem, State.callEntry_esp, hc.esp, a0, a1,
    a2, ae]
  refine ⟨⟨rfl, rfl, hL.oc.sub_left out, hL.kc.sub_left (field_sub hL (by decide)),
    (hL.ko.sub_left args).sub_right out, hL.kc.sub_left args,
    (hL.ko.sub_left ret).sub_right out, hL.kc.sub_left ret,
    by have := hL.no; omega_using [this], field_fit hL (by decide), hL.nc, ?_, ?_,
    Whole.inner_frame be hf (d := 96) (n := 32) (by decide) (by decide), hL.kc.sub_left stk,
    (hL.ko.sub_left stk).sub_right out⟩,
    (hL.ko.sub_left stk).sub_right out, tw, hL.nt, ?_⟩
  · change (L.E - BitVec.ofNat 32 4).toNat + 16 ≤ 2 ^ 32
    rw [sub_toNat (k := 4) (by omega_using [be])]
    have := hL.top; omega_using [hf]
  · change 8 ≤ (L.E - BitVec.ofNat 32 4).toNat
    rw [sub_toNat (k := 4) (by omega_using [be])]
    omega_using [be]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact (hL.os _ tb).symm.sub_right out
    · exact hL.sc _ tb
    · exact (hL.ks _ tb).symm.sub_right stk

theorem base_call (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : BaseArgs L s) (hy : s.syms combSym = L.T)
    (ht : TblWords (L.T.setWidth 64) s.mem) :
    WP isa (.call "vg_ed25519_scalar_base" scalarBase) s fun t => Ctx L g m₀ t ∧
      Frame (baseWr L ++ [below L.E 24]) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem ((fp L 96).setWidth 64) 32) := by
  have cov := hash_covers (L := L) (rs := baseRd L ++ baseWr L) (by
    simp only [baseRd, baseWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact .inl (fieldWithin hL (by decide))
    · exact .inl (argsWithin L (by decide))
    · exact .inr ⟨L.TB, by simp [Lay.inputs], 0, by simp, by simp⟩
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], 0, by simp [baseOut], by change 0 + 32 ≤ 64; decide⟩
    · exact scratch_covered ⟨0, by simp, by simp⟩)
  have ws : ∀ r ∈ baseWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    simp only [baseWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], 0, by simp [baseOut], by change 0 + 32 ≤ 64; decide⟩
    · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, by simp, by simp⟩
  with_reducible
    refine Whole.call_ok hc hL.below scalarBase_ok base_nosp (by rw [base_stack]; decide)
      (base_pre hc hL ha hy ht) cov ws fun t ht hf _ post => ⟨ht, hf, ?_⟩
  obtain ⟨s₂, hm, _, hp⟩ := post
  have H := hashSpace hL
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hc.esp H.below H.frameFit hj
  change Spec.Ed25519.bytesAt s₂.mem ((arg s.callEntry 0).setWidth 64) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 1).setWidth 64) 32) at hp
  rw [hm, (ca (by decide)).trans ha.1, (ca (by decide)).trans ha.2.1] at hp
  rw [hp, field_ce hc hL (by decide)]

theorem base_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (hy : s.syms combSym = L.T) :
    WP isa (callWith baseArgs "vg_ed25519_scalar_base" scalarBase) s fun t => Ctx L g m₀ t ∧
      Frame (primitiveWrites L (baseOut L)) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem ((fp L 96).setWidth 64) 32) := by
  refine WP.seq (WP.mono_syms (args_ok hc hL ha (vs := [.caller 0 0, .frame 96, .caller 5 0])
    (by decide) (Whole.valid_all (by decide))) fun u ⟨hu, hf, hs⟩ yu => ?_)
  have a0 := hs.slot hL (j := 0) (by decide) (by decide)
  have a1 := hs.slot hL (j := 1) (by decide) (by decide)
  have a2 := hs.slot hL (j := 2) (by decide) (by decide)
  change Whole.slots L.E u 0 = L.out + 0#32 at a0
  change Whole.slots L.E u 2 = L.scr + 0#32 at a2
  rw [BitVec.add_zero] at a0 a2
  refine WP.mono (base_call hu hL ⟨a0, a1, a2⟩ ((congrFun yu combSym).trans hy) (hu.tbl hL ha))
    fun t ⟨ht, hft, hp⟩ =>
    ⟨ht, primitive_frame hf hft, ?_⟩
  rw [hp, field_setup hL hf (by decide) (by decide)]

end VG.Proof.Ed25519.X86.SignCached

end

end

/-! ### `Ed25519.X86.SignCached.Entry`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86
open VG.Impl.Ed25519.X86 (combSym)

def signRd (n : Nat) (s : State) : List Region :=
  [⟨(arg s 1).setWidth 64, n⟩, ⟨(arg s 2).setWidth 64, 32⟩,
    ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩, ⟨argAddr s 0, 24⟩, TBL ((s.syms combSym).setWidth 64)]
def signWr (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 64⟩, ⟨(arg s 5).setWidth 64, 8192⟩]

/-- What the two runs of a signature share: the stack pointer, the arguments and the
comb's tables. -/
def signPub (s t : State) : Prop :=
  s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧
    arg s 2 = arg t 2 ∧ arg s 3 = arg t 3 ∧ arg s 4 = arg t 4 ∧ arg s 5 = arg t 5 ∧
    s.syms combSym = t.syms combSym

/-- Signing with the `n` bytes at the second argument (the seed's SHA-512 digest, 64),
the condition `key` on them and the public key, and the postcondition `post`. -/
def signLocalWith (n : Nat) (key : State → Prop) (post : State → State → Prop) : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, n⟩
    let pk : Region := ⟨(arg s 2).setWidth 64, 32⟩
    let msg : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = signRd n s ∧ s.wr = signWr s ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint msg ∧ out.Disjoint args ∧
      out.Disjoint scr ∧ stk.Disjoint out ∧ ret.Disjoint out ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ msg.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint seed ∧ ret.Disjoint pk ∧ ret.Disjoint msg ∧ ret.Disjoint scr ∧
      stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + n ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 5).toNat + 8192 ≤ 2 ^ 32 ∧
      280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧ key s ∧
      CombHeld s [out, scr, stk, ret]
  post := post
  pub := signPub

def lay (n : Nat) (s : State) : Lay :=
  ⟨arg s 0, arg s 1, arg s 2, arg s 3, arg s 4, arg s 5, s.gpr .esp - BitVec.ofNat 32 256,
    s.syms combSym, n⟩

variable {n : Nat} {key : State → Prop} {post : State → State → Prop}

theorem entry_bounds {s : State} (h : (signLocalWith n key post).pre s) :
    280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, ht, _⟩ := h
  exact ⟨hb, ht⟩

theorem entry_key {s : State} (h : (signLocalWith n key post).pre s) : key s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, _⟩ := h
  exact hk

theorem entry_held {s : State} (h : (signLocalWith n key post).pre s) :
    CombHeld s [⟨(arg s 0).setWidth 64, 64⟩, ⟨(arg s 5).setWidth 64, 8192⟩,
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩, ⟨(s.gpr .esp).setWidth 64, 4⟩] := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht⟩ := h
  exact ht

theorem lay_base {s : State} (h : (signLocalWith n key post).pre s) :
    (lay n s).E.setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 256 :=
  Taint.sub_setWidth (by have := (entry_bounds h).1; omega_arith)

theorem lay_args {s : State} (h : (signLocalWith n key post).pre s) :
    (lay n s).ARGS = ⟨argAddr s 0, 24⟩ := by
  rw [Lay.ARGS, lay_base h]
  have ha : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    addr_eq (by have := (entry_bounds h).2; omega_arith)
  rw [ha]
  congr 1
  change _ - 256#64 + 260#64 = _ + 4#64
  rw [show BitVec.ofNat 64 260 = BitVec.ofNat 64 256 + BitVec.ofNat 64 4 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem lay_ret {s : State} (h : (signLocalWith n key post).pre s) :
    (lay n s).RET = ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
  rw [Lay.RET, lay_base h]
  change (⟨(s.gpr .esp).setWidth 64 - 256#64 + 256#64, 4⟩ : Region) = _
  rw [BitVec.sub_add_cancel]

theorem lay_stack {s : State} (h : (signLocalWith n key post).pre s) :
    (lay n s).STK = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩ := by
  rw [Lay.STK, Whole.STK, lay_base h, BitVec.sub_sub]
  rfl

theorem lay_top {s : State} (h : (signLocalWith n key post).pre s) : (lay n s).E.toNat + 284 ≤ 2 ^ 32 := by
  have hb := entry_bounds h
  change (s.gpr .esp - BitVec.ofNat 32 256).toNat + 284 ≤ _
  rw [sub_toNat (by omega_arith)]
  omega_arith

theorem lay_ok {s : State} (h : (signLocalWith n key post).pre s) (sl : 32 ≤ n) : (lay n s).Ok := by
  have held := entry_held h
  have h₀ := h
  obtain ⟨_, _, os, op, om, oa, oc, ko, ro, sc, pc, mc, ac, rs, rp, rm, rc,
    ks, kp, km, kc, no, ns, np, nm, nc, nb, na, _⟩ := h₀
  have top : (lay n s).E.toNat + 284 ≤ 2 ^ 32 := by
    change (s.gpr .esp - BitVec.ofNat 32 256).toNat + 284 ≤ _
    rw [sub_toNat (by omega_arith)]
    omega_arith
  refine ⟨?_, top, ?_, oc, ?_, ?_, no, ?_, ?_, ?_, ?_, ?_, np, nm, ns, nc, held.2.1, sl⟩
  · change 24 ≤ (s.gpr .esp - BitVec.ofNat 32 256).toNat
    rw [sub_toNat (by omega_arith)]
    omega_arith
  · intro r hr
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact os
    · exact op
    · exact om
    · rw [lay_args h]; exact oa
    · exact (held.2.2 _ List.mem_cons_self).symm
  · rw [lay_stack h]; exact ko
  · rw [lay_ret h]; exact ro
  · intro r hr
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact sc
    · exact pc
    · exact mc
    · rw [lay_args h]; exact ac
    · exact held.2.2 _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · intro r hr
    rw [lay_stack h]
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ks
    · exact kp
    · exact km
    · rw [Lay.ARGS, lay_base h]
      have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 256 + 260 =
          (s.gpr .esp).setWidth 64 + 4 := by
        change _ - 256#64 + 260#64 = _ + 4#64
        rw [show (260#64) = 256#64 + 4#64 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
      rw [e]
      exact Offset.disjoint_below_above _ (by decide)
    · exact (held.2.2 _ (by simp)).symm
  · intro r hr
    rw [lay_ret h]
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rs
    · exact rp
    · exact rm
    · rw [Lay.ARGS, lay_base h]
      have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 256 + 260 =
          (s.gpr .esp).setWidth 64 + 4 := by
        change _ - 256#64 + 260#64 = _ + 4#64
        rw [show (260#64) = 256#64 + 4#64 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
      rw [e]
      exact (Offset.disjoint_base _ (by decide) (by decide)).symm
    · exact (held.2.2 _ (by simp)).symm
  · rw [lay_stack h]; exact kc
  · rw [lay_ret h]; exact rc

theorem lay_arguments {s : State} (h : (signLocalWith n key post).pre s) : Arguments (lay n s) s.mem := by
  refine ⟨fun j hj => ?_, (entry_held h).1⟩
  have hb := lay_top h
  have e : (lay n s).E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j) = argAddr s j := by
    rw [← addr_eq (by have := hb; omega_arith)]
    simp only [addr, lay, argAddr]
    rw [show 260 + 4 * j = 256 + (4 + 4 * j) by omega_arith, BitVec.ofNat_add,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rw [e]
  change arg s j = (lay n s).value j
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega_arith
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem push_ctx {s : State} (h : (signLocalWith n key post).pre s) :
    Ctx (lay n s) s.gpr s.mem (pushed (List.replicate 64 .eax) s) := by
  have hn := (entry_bounds h).1
  have hf := pushed_frame (s := s) (rs := List.replicate 64 .eax) (by simp)
    (by simp only [List.length_replicate]; omega_arith)
  refine ⟨?_, ?_, ?_, fun r _ hn => pushed_gpr _ _ hn, ?_⟩
  · rw [pushed_rd, h.1]
    rw [Lay.inputs, lay_args h]
    rfl
  · rw [pushed_wr, h.2.1]
    simp only [List.length_replicate, Whole.FR, Lay.outputs, Lay.SCR, lay, signWr]
  · rw [pushed_esp, List.length_replicate]
    rfl
  · refine Frame.sub hf fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    refine ⟨(lay n s).STK, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    rw [lay_stack h, ← Taint.sub_setWidth hn]
    exact below_sub (by simp) hn

end VG.Proof.Ed25519.X86.SignCached

end

end

/-! ### `Ed25519.X86.SignCached.HashInputs`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

variable {L : Lay}

theorem update_args {t : State} (hL : L.Ok) (c : Nat) (p n : Value)
    (h : OutArgs L [.caller 5 0, .const c, .const 0, p, n, .caller 5 192] t) :
    UpdateArgs L (BitVec.ofNat 32 c) (value L p) (value L n) t := by
  have h0 := h.slot hL (j := 0) (by simp) (by simp)
  have h1 := h.slot hL (j := 1) (by simp) (by simp)
  have h2 := h.slot hL (j := 2) (by simp) (by simp)
  have h3 := h.slot hL (j := 3) (by simp) (by simp)
  have h4 := h.slot hL (j := 4) (by simp) (by simp)
  have h5 := h.slot hL (j := 5) (by simp) (by simp)
  change Whole.slots L.E t 0 = L.scr + 0#32 at h0
  rw [BitVec.add_zero] at h0
  exact ⟨h0, h1, h2, h3, h4, h5⟩

theorem Input.external {p n : BitVec 32}
    (hc : ∃ R ∈ L.inputs ++ L.outputs, Whole.Within ⟨p.setWidth 64, n.toNat⟩ R)
    (hs : Region.Disjoint ⟨p.setWidth 64, n.toNat⟩ L.SCR)
    (hk : L.STK.Disjoint ⟨p.setWidth 64, n.toNat⟩)
    (hL : L.Ok) (hf : p.toNat + n.toNat ≤ 2 ^ 32) : Input L p n :=
  ⟨.inr hc, hs, hk.sub_left (Whole.below_sub_stack hL.below (by decide)),
    (hk.sub_left (fun a ha => Whole.frame_sub L.E a (Region.sub_prefix (by decide : 24 ≤ 256) a ha))).symm, hf⟩

theorem key_input (hL : L.Ok) : Input L L.pk 32 :=
  Input.external ⟨L.PK, by simp [Lay.inputs], 0, by simp, by change 0 + 32 ≤ 32; decide⟩
    (hL.sc _ (by simp [Lay.inputs])) (hL.ks _ (by simp [Lay.inputs])) hL hL.np

theorem message_input (hL : L.Ok) : Input L L.msg L.len :=
  Input.external ⟨L.MSG, by simp [Lay.inputs], 0, by simp, by simp⟩
    (hL.sc _ (by simp [Lay.inputs])) (hL.ks _ (by simp [Lay.inputs])) hL hL.nm

theorem point_input (hL : L.Ok) : Input L L.out 32 :=
  Input.external ⟨L.OUT, by simp [Lay.outputs], 0, by simp, by change 0 + 32 ≤ 64; decide⟩
    (hL.oc.sub_left (Region.sub_prefix (by decide)))
    (hL.ko.sub_right (Region.sub_prefix (by decide))) hL (by change L.out.toNat + 32 ≤ 2 ^ 32; have := hL.no; omega_using [this])

theorem prefix_input (hL : L.Ok) : Input L (L.E + 64) 32 := by
  have ea : (L.E + 64).setWidth 64 = L.E.setWidth 64 + 64 :=
    addr_eq (x := L.E) (k := 64) (by have := hL.top; omega_using [this])
  have hin : Whole.Within ⟨(L.E + 64).setWidth 64, (32 : BitVec 32).toNat⟩ L.FR :=
    ⟨64, ea, by change 64 + 32 ≤ 256; decide⟩
  refine ⟨.inl hin, hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p (hin.sub p hp)), ?_, ?_, ?_⟩
  · change Region.Disjoint ⟨(L.E - BitVec.ofNat 32 24).setWidth 64, 24⟩ _
    rw [Taint.sub_setWidth hL.below, ea]
    exact (Offset.disjoint_below _ (n := 24) (d := 64) (k := 32) (by decide)).symm
  · rw [ea]
    exact Offset.disjoint_base _ (d := 64) (n := 32) (k := 24) (by decide) (by decide)
  · rw [BitVec.toNat_add, show (64 : BitVec 32).toNat = 64 from rfl,
      Nat.mod_eq_of_lt (by have := hL.top; omega_using [this])]
    have := hL.top; change L.E.toNat + 64 + 32 ≤ 2 ^ 32; omega_using [this]

end VG.Proof.Ed25519.X86.SignCached

end

end

/-! ### `Ed25519.X86.SignCached.HashFinalize`, which only this module used -/

section

/-! Merged from `Proof.Ed25519.X86.SignCached.FinalizeArgs`. -/

@[expose] public section

section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole VG.Impl.Ed25519.X86.SignCached

def FinArgs (L : Lay) (count : BitVec 64) (t : State) : Prop :=
  Whole.slots L.E t 0 = L.scr ∧ Whole.slots L.E t 3 = L.E + 192 ∧
    Whole.slots L.E t 4 = L.scr + 192 ∧
    Whole.slots L.E t 2 ++ Whole.slots L.E t 1 = count

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem count_keep {t u : State} (hf : Frame [⟨L.E.setWidth 64 + 4, 8⟩] t.mem u.mem)
    {j : Nat} (hj : j = 0 ∨ j = 3 ∨ j = 4) : Whole.slots L.E u j = Whole.slots L.E t j := by
  refine hf.readW (Region.contains_self _ _) ?_ (by decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  apply Offset.disjoint (e := 4) (k := 8)
  · rcases hj with rfl | rfl | rfl <;> decide
  · rcases hj with rfl | rfl | rfl <;> decide
  · decide

theorem count_frame {m m' : Mem} (hf : Frame [⟨L.E.setWidth 64 + 4, 8⟩] m m') :
    Frame [⟨L.E.setWidth 64, 24⟩] m m' :=
  hf.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (d := 4) (by decide)⟩

theorem finalizeArgs_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (n : Nat) (hn : n < 2 ^ 32) (b : Bool) :
    WP isa (.block (finalizeArgs n b)) s fun t => Ctx L g m₀ t ∧
      Frame [⟨L.E.setWidth 64, 24⟩] s.mem t.mem ∧
      FinArgs L (BitVec.ofNat 64 ((if b then L.len.toNat else 0) + n)) t := by
  rw [finalizeArgs, WP.block_append_iff]
  refine WP.mono (args_ok hc hL ha (vs := [.caller 5 0, .const n, .const 0, .frame 192, .caller 5 192])
    (by simp) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_
  have aa := hs.slot hL (j := 0) (by simp) (by simp)
  have ab := hs.slot hL (j := 1) (by simp) (by simp)
  have ac := hs.slot hL (j := 2) (by simp) (by simp)
  have ad := hs.slot hL (j := 3) (by simp) (by simp)
  have ae := hs.slot hL (j := 4) (by simp) (by simp)
  change Whole.slots L.E u 0 = L.scr + 0#32 at aa
  rw [BitVec.add_zero] at aa
  change Whole.slots L.E u 1 = BitVec.ofNat 32 n at ab
  change Whole.slots L.E u 2 = 0#32 at ac
  change Whole.slots L.E u 3 = L.E + 192 at ad
  change Whole.slots L.E u 4 = L.scr + 192 at ae
  cases b with
  | false =>
    refine WP.block_nil ⟨hu, hf, aa, ad, ae, ?_⟩
    rw [ac, ab]
    simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
    change (0#32) ++ BitVec.ofNat 32 n = BitVec.ofNat 64 n
    rw [count_zero_high, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  | true =>
    have hr : InRegions (u.rd ++ u.wr) (addr L.E 276) 4 := by
      refine ⟨L.ARGS, ?_, ?_⟩
      · rw [hu.rd]; simp [Lay.inputs]
      · rw [addr_eq (by have := hL.top; omega_using [this])]
        exact Offset.contains _ (e := 260) (k := 24) (d := 276) (n := 4) (by decide) (by decide) (by decide)
    have hx : u.mem.readW (addr L.E 276) 32 = L.len := by
      rw [addr_eq (by have := hL.top; omega_using [this])]
      exact (hu.arg_word hL (j := 4) (by decide)).trans (ha.1 4 (by decide))
    refine WP.mono (Whole.Ctx.count hu (index := 4) (n := n) (by have := hL.top; omega_using [this]) hr hx)
      fun t ⟨ht, hft, hlo, hhi⟩ => ⟨ht, hf.trans (count_frame hft),
        (count_keep hft (.inl rfl)).trans aa,
        (count_keep hft (.inr (.inl rfl))).trans ad,
        (count_keep hft (.inr (.inr rfl))).trans ae, ?_⟩
    change (t.mem.readW (L.E.setWidth 64 + 8#64) 32 ++ t.mem.readW (L.E.setWidth 64 + 4#64) 32 : BitVec 64) = BitVec.ofNat 64 ((if true then L.len.toNat else 0) + n)
    change t.mem.readW (L.E.setWidth 64 + 8#64) 32 = _ at hhi
    change t.mem.readW (L.E.setWidth 64 + 4#64) 32 = _ at hlo
    rw [hhi, hlo]
    exact Whole.count_pair L.len n hn

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem digest_addr (hL : L.Ok) : (L.E + 192).setWidth 64 = L.E.setWidth 64 + 192 :=
  addr_eq (x := L.E) (k := 192) (by have := hL.top; omega_using [this])

theorem digestWithin (hL : L.Ok) : Whole.Within ⟨(L.E + 192).setWidth 64, 64⟩ L.FR :=
  ⟨192, digest_addr hL, by change 192 + 64 ≤ 256; decide⟩

theorem digest_below (hL : L.Ok) : (below L.E 24).Disjoint ⟨(L.E + 192).setWidth 64, 64⟩ := by
  change Region.Disjoint ⟨(L.E - BitVec.ofNat 32 24).setWidth 64, 24⟩ _
  rw [Taint.sub_setWidth hL.below, digest_addr hL]
  exact (Offset.disjoint_below _ (n := 24) (d := 192) (k := 64) (by decide)).symm

theorem finalize_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (n : Nat) (hn : n < 2 ^ 32) (b : Bool) {msg : List Byte}
    (hlen : msg.length < 2 ^ 64) (hcount : (if b then L.len.toNat else 0) + n = msg.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) msg) :
    WP isa (finalize n b) s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 = Spec.Sha512.sha512 msg := by
  refine WP.seq (WP.mono (finalizeArgs_ok hc hL ha n hn b) fun u ⟨hu, hf, a0, a3, a4, ac⟩ => ?_)
  have H := hashSpace hL
  have fit : (L.E + 192).toNat + 64 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl,
      Nat.mod_eq_of_lt (by have := hL.top; omega_using [this])]
    have := hL.top; omega_using [this]
  have hd : Region.Disjoint ⟨(L.E + 192).setWidth 64, 64⟩ L.SCR :=
    hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p ((digestWithin hL).sub p hp))
  have hp := Whole.finalize_pre hu.esp H a0 a3 a4 hd (digest_below hL) (by
    rw [digest_addr hL]
    exact Offset.base_disjoint _ (k := 20) (e := 192) (n := 64) (by decide) (by decide)) fit
  have cov := hash_covers (L := L)
    (rs := Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeRd, Whole.finalizeWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L)
    · exact .inl (digestWithin hL)
    · exact scratch_covered (workWithin hL))
  have ws := hash_writes (L := L) (rs := Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr (shaWithin L)
    · exact .inl (digestWithin hL)
    · exact .inr (workWithin hL))
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hu.esp H.below H.frameFit hj
  have cnt : Proof.Sha512.countX86 u.callEntry = BitVec.ofNat 64 msg.length := by
    unfold Proof.Sha512.countX86
    rw [ca (j := 2) (by decide), ca (j := 1) (by decide), ac, hcount]
  have hbsha : (Whole.SHA L.scr).Disjoint (below (u.gpr .esp) 4) := by
    rw [hu.esp]; exact (H.below_sha (by decide)).symm
  refine WP.mono (Whole.finalize_call hu H.below hp cov ws (ca (by decide) |>.trans a0)
    (ca (by decide) |>.trans a3) cnt hbsha (setup_repr hL hf hr) hlen)
    fun t ⟨ht, hft, hdigest⟩ => ⟨ht, ?_, ?_⟩
  · refine (setup_frame hf).trans (hash_frame hft ?_)
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (shaWithin L)
    · exact .inr ⟨0, by rw [digest_addr hL]; simp, by change 0 + 64 ≤ 64; decide⟩
    · exact .inl (workWithin hL)
  · rw [digest_addr hL] at hdigest
    exact hdigest

end VG.Proof.Ed25519.X86.SignCached

end

end

/-! ### `Ed25519.X86.SignCached.Prefix`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey VG.Impl.Ed25519.X86.SignCached
open VG.Proof.Ed25519.X86.PublicKey (Step frame_word decode_words)

theorem copyWord_ok {s : State} {E : BitVec 32} {k : Nat} (he : s.gpr .esp = E)
    (hr : InRegions (s.rd ++ s.wr) (addr E (224 + 4 * k)) 4)
    (hw : InRegions s.wr (addr E (64 + 4 * k)) 4) :
    WP isa (.block (copyWord 224 64 k)) s fun t => Step s t ∧
      t.mem = s.mem.writeW (addr E (64 + 4 * k)) (s.mem.readW (addr E (224 + 4 * k)) 32) := by
  simp only [copyWord, at_]
  refine Wp.wp_ldm he hr fun u hu => ?_
  refine Wp.wp_stm (hu.other _ (by decide) |>.trans he) (hu.wr ▸ hw) fun t ht => WP.block_nil ?_
  refine ⟨⟨ht.rd.trans hu.rd, ht.wr.trans hu.wr, fun r h => by rw [ht.gpr]; exact hu.other r h⟩, ?_⟩
  rw [ht.mem, hu.mem, hu.gpr]

structure PrefixInv (E : BitVec 32) (s : State) (n : Nat) (t : State) : Prop where
  step : Step s t
  frame : Frame [⟨E.setWidth 64 + BitVec.ofNat 64 64, 32⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (addr E (64 + 4 * j)) 32 =
    s.mem.readW (addr E (224 + 4 * j)) 32

theorem copyPrefix_ok {s : State} {E : BitVec 32} (he : s.gpr .esp = E)
    (hf : E.toNat + 256 ≤ 2 ^ 32) (hw : (⟨E.setWidth 64, 256⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap (copyWord 224 64))) s (PrefixInv E s n)
  | 0, _ => WP.block_nil ⟨Step.refl s, Frame.refl _ _, fun _ h => by omega_using [h]⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyPrefix_ok he hf hw n (by omega_using [hn])) fun u hu => ?_
    have ur : InRegions (u.rd ++ u.wr) (addr E (224 + 4 * n)) 4 := by
      obtain ⟨r, hr, hc⟩ := frame_word hf (hu.step.wr ▸ hw) (d := 224 + 4 * n) (by omega_using [hn])
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    have uw := frame_word hf (hu.step.wr ▸ hw) (d := 64 + 4 * n) (by omega_using [hn])
    refine WP.mono (copyWord_ok (hu.step.esp.trans he) ur uw) fun t ⟨kt, mt⟩ => ?_
    have a224 : addr E (224 + 4 * n) = E.setWidth 64 + BitVec.ofNat 64 (224 + 4 * n) :=
      addr_eq (by omega_using [hf, hn])
    have a32 : addr E (64 + 4 * n) = E.setWidth 64 + BitVec.ofNat 64 (64 + 4 * n) :=
      addr_eq (by omega_using [hf, hn])
    have same : u.mem.readW (addr E (224 + 4 * n)) 32 = s.mem.readW (addr E (224 + 4 * n)) 32 := by
      rw [a224]
      apply hu.frame.readW (Region.contains_self _ _) _ (by decide)
      simp only [List.mem_singleton]
      rintro r rfl
      exact Offset.disjoint _ (by omega_using [hn]) (by omega_using [hn]) (by omega_using [hn])
    rw [same] at mt
    refine ⟨hu.step.trans kt, ?_, fun j hj => ?_⟩
    · rw [mt, a32]
      exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_using []) (by omega_using [hn]) (by decide))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (a := addr E (64 + 4 * j)) (b := addr E (64 + 4 * n)) ?_ (by decide)]
        · exact hu.words j (by omega_using [hj, hjn])
        · rw [a32, addr_eq (by omega_using [hf, hj, hn])]
          exact Offset.sep _ (by omega_using [hj, hjn]) (by omega_using [hj, hn]) (by omega_using [hn])

theorem prefix_ok {s : State} {E : BitVec 32} (he : s.gpr .esp = E)
    (hf : E.toNat + 256 ≤ 2 ^ 32) (hw : (⟨E.setWidth 64, 256⟩ : Region) ∈ s.wr) :
    WP isa (.block copyPrefix) s fun t => Step s t ∧
      Frame [⟨E.setWidth 64 + 64, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (E.setWidth 64 + 64) 32 =
        Spec.Ed25519.bytesAt s.mem (E.setWidth 64 + 224) 32 := by
  refine WP.mono (copyPrefix_ok he hf hw 8 (by decide)) fun t ht => ⟨ht.step, ht.frame, ?_⟩
  have words : ∀ j < 8, t.mem.readW (E.setWidth 64 + BitVec.ofNat 64 (64 + 4 * j)) 32 =
      s.mem.readW (E.setWidth 64 + BitVec.ofNat 64 (224 + 4 * j)) 32 := by
    intro j hj
    have h := ht.words j hj
    rw [addr_eq (by omega_using [hf, hj]), addr_eq (by omega_using [hf, hj])] at h
    exact h
  rw [Proof.Ed25519.bytesAt_encodeLE t.mem, Proof.Ed25519.bytesAt_encodeLE s.mem]
  apply congrArg (Spec.Ed25519.encodeLE 32)
  rw [decode_words, decode_words]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have w0 := words 0 (by decide)
  have w1 := words 1 (by decide)
  have w2 := words 2 (by decide)
  have w3 := words 3 (by decide)
  have w4 := words 4 (by decide)
  have w5 := words 5 (by decide)
  have w6 := words 6 (by decide)
  have w7 := words 7 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at w0 w1 w2 w3 w4 w5 w6 w7
  change t.mem.readW (E.setWidth 64 + (64 : BitVec 64)) 32 = s.mem.readW (E.setWidth 64 + (224 : BitVec 64)) 32 at w0
  rw [w0, w1, w2, w3, w4, w5, w6, w7]

end VG.Proof.Ed25519.X86.SignCached

end

end

/-! ### `Ed25519.X86.SignCached.CT`, which only this module used -/

section

/-! ### `Ed25519.X86.SignCached.CTReady`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def init_ready (hc : Ctx L g m₀ s) (hL : L.Ok)
    (a0 : Whole.slots L.E s 0 = L.scr) :
    Whole.CallReady (Proof.Sha512.initX86 Spec.Sha512.H0_512) L.E L.inputs L.outputs s := by
  have H := hashSpace hL
  have cov := hash_covers (L := L) (rs := Whole.initRd L.E ++ Whole.initWr L.scr) (by
    simp only [Whole.initRd, Whole.initWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L))
  have ws := hash_writes (L := L) (rs := Whole.initWr L.scr) (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact .inr (shaWithin L))
  exact ⟨_, _, Whole.init_pre hc.esp H a0, cov, ws⟩

def update_ready (hc : Ctx L g m₀ s) (hL : L.Ok) {c p n : BitVec 32}
    (hi : Input L p n) (ha : UpdateArgs L c p n s) :
    Whole.CallReady Proof.Sha512.updateX86 L.E L.inputs L.outputs s := by
  obtain ⟨a0, _, _, a3, a4, a5⟩ := ha
  have H := hashSpace hL
  have hp := Whole.update_pre hc.esp H a0 a3 a4 a5 hi.scratch hi.below hi.fit
  have cov := hash_covers (L := L) (rs := Whole.updateRd L.E p n ++ Whole.hashWr L.scr) (by
    simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hi.cover
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L)
    · exact scratch_covered (workWithin hL))
  have ws := hash_writes (L := L) (rs := Whole.hashWr L.scr) (by
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (shaWithin L)
    · exact .inr (workWithin hL))
  exact ⟨_, _, hp, cov, ws⟩

def finalize_ready (hc : Ctx L g m₀ s) (hL : L.Ok) {count : BitVec 64}
    (ha : FinArgs L count s) :
    Whole.CallReady Proof.Sha512.finalizeX86 L.E L.inputs L.outputs s := by
  obtain ⟨a0, a3, a4, _⟩ := ha
  have H := hashSpace hL
  have fit : (L.E + 192).toNat + 64 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl,
      Nat.mod_eq_of_lt (by have := hL.top; omega_using [this])]
    have := hL.top; omega_using [this]
  have hd : Region.Disjoint ⟨(L.E + 192).setWidth 64, 64⟩ L.SCR :=
    hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p ((digestWithin hL).sub p hp))
  have hp := Whole.finalize_pre hc.esp H a0 a3 a4 hd (digest_below hL) (by
    rw [digest_addr hL]
    exact Offset.base_disjoint _ (by decide) (by decide)) fit
  have cov := hash_covers (L := L)
    (rs := Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeRd, Whole.finalizeWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L)
    · exact .inl (digestWithin hL)
    · exact scratch_covered (workWithin hL))
  have ws := hash_writes (L := L) (rs := Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr (shaWithin L)
    · exact .inl (digestWithin hL)
    · exact .inr (workWithin hL))
  exact ⟨_, _, hp, cov, ws⟩

def reduce_ready (hc : Ctx L g m₀ s) (hL : L.Ok)
    {d : Nat} (hd : 24 ≤ d) (hd' : d + 32 ≤ 256)
    (a0 : Whole.slots L.E s 0 = L.E + BitVec.ofNat 32 d)
    (a1 : Whole.slots L.E s 1 = L.E + 192) (a2 : Whole.slots L.E s 2 = L.scr) :
    Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs s := by
  have H := hashSpace hL
  have wo : Whole.Within ⟨(L.E + BitVec.ofNat 32 d).setWidth 64, 32⟩ L.FR :=
    ⟨d, Whole.frame_addr H.frameFit (by omega_using [hd']), hd'⟩
  have cov : Covers (Whole.reduceRd L.E ++ Whole.reduceWr L.E L.scr d)
      (L.inputs ++ L.FR :: L.outputs) := by
    apply hash_covers
    simp only [Whole.reduceRd, Whole.reduceWr, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (digestWithin hL)
    · exact .inl (argsWithin L (by decide))
    · exact .inl wo
    · exact scratch_covered ⟨0, by simp, by simp⟩
  have ws : ∀ r ∈ Whole.reduceWr L.E L.scr d,
      Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply hash_writes
    simp only [Whole.reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl wo
    · exact .inr ⟨0, by simp, by simp⟩
  exact ⟨_, _, Whole.reduce_pre hc H hd hd' a0 a1 a2, cov, ws⟩

def base_ready (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : BaseArgs L s)
    (hy : s.syms Impl.Ed25519.X86.combSym = L.T) (ht : TblWords (L.T.setWidth 64) s.mem) :
    Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs s := by
  have cov := hash_covers (L := L) (rs := baseRd L ++ baseWr L) (by
    simp only [baseRd, baseWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact .inl (fieldWithin hL (by decide))
    · exact .inl (argsWithin L (by decide))
    · exact .inr ⟨L.TB, by simp [Lay.inputs], 0, by simp, by simp⟩
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], 0, by simp [baseOut], by change 0 + 32 ≤ 64; decide⟩
    · exact scratch_covered ⟨0, by simp, by simp⟩)
  have ws : ∀ r ∈ baseWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    simp only [baseWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], 0, by simp [baseOut], by change 0 + 32 ≤ 64; decide⟩
    · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, by simp, by simp⟩
  exact ⟨_, _, base_pre hc hL ha hy ht, cov, ws⟩

def mul_ready (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : MulArgs L s) :
    Whole.CallReady scalarMulAddLocal L.E L.inputs L.outputs s := by
  have cov := hash_covers (L := L) (rs := mulRd L ++ mulWr L) (by
    simp only [mulRd, mulWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact .inl (fieldWithin hL (by decide))
    · exact .inl (fieldWithin hL (by decide))
    · exact .inl (fieldWithin hL (by decide))
    · exact .inl (argsWithin L (by decide))
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], halfWithin hL⟩
    · exact scratch_covered ⟨0, by simp, by simp⟩)
  have ws : ∀ r ∈ mulWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    simp only [mulWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], halfWithin hL⟩
    · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, by simp, by simp⟩
  exact ⟨_, _, mul_pre hc hL ha, cov, ws⟩

end VG.Proof.Ed25519.X86.SignCached

end

end

/-! Merged from `Proof.Ed25519.X86.SignCached.CTCommon`. -/

@[expose] public section

section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

def Two (L : Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem) (P : State → Prop) (a b : State) : Prop :=
  Ctx L g₁ m₁ a ∧ Ctx L g₂ m₂ b ∧ P a ∧ P b

theorem two_esp {P : State → Prop} {a b : State} (h : Two L g₁ g₂ m₁ m₂ P a b) :
    a.gpr .esp = b.gpr .esp := h.1.esp.trans h.2.1.esp.symm

theorem two_wp {P Q : State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two L g₁ g₂ m₁ m₂ P) c fun _ _ => True)
    (ha : ∀ t, Ctx L g₁ m₁ t → P t → WP isa c t fun u => Ctx L g₁ m₁ u ∧ Q u)
    (hb : ∀ t, Ctx L g₂ m₂ t → P t → WP isa c t fun u => Ctx L g₂ m₂ u ∧ Q u) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ P) c (Two L g₁ g₂ m₁ m₂ Q) :=
  (hct.wp fun a b h => ⟨ha a h.1 h.2.2.1, hb b h.2.1 h.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩

theorem setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (vs : List Value) (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 6 v)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (setup 0 vs)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block (setup 0 vs))
      (Two L g₁ g₂ m₁ m₂ (OutArgs L vs)) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) ht) ?_ ?_
  · intro s hc _
    exact WP.mono (args_ok hc hL ha hn hv) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩
  · intro s hc _
    exact WP.mono (args_ok hc hL hb hn hv) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

theorem call_args_eq (hL : L.Ok) {vs : List Value} (hn : vs.length ≤ 6)
    {a b : State} (h : Two L g₁ g₂ m₁ m₂ (OutArgs L vs) a b) {j : Nat} (hj : j < vs.length) :
    arg a.callEntry j = arg b.callEntry j := by
  have H := hashSpace hL
  rw [Whole.call_arg h.1.esp H.below H.frameFit (by omega_using [hn, hj]),
    Whole.call_arg h.2.1.esp H.below H.frameFit (by omega_using [hn, hj]),
    h.2.2.1.slot hL hj hn, h.2.2.2.slot hL hj hn]

theorem call_ct (hL : L.Ok) {P : State → Prop} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (sp : NoSp c) (stack : stackUse c ≤ 20)
    (ready : ∀ {g m t}, Ctx L g m t → P t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, Two L g₁ g₂ m₁ m₂ P a b →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw)) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ P) (.call name c) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply two_wp
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready h.1 h.2.2.1
    let rb := ready h.2.1 h.2.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ h, ca, wa, cb, wb, two_esp h⟩
  · intro t hc hs
    exact WP.mono ((ready hc hs).wp hc correct sp stack hL.below) fun _ hu => ⟨hu, trivial⟩
  · intro t hc hs
    exact WP.mono ((ready hc hs).wp hc correct sp stack hL.below) fun _ hu => ⟨hu, trivial⟩

/-- The states name the comb's tables at `L.T`. -/
abbrev Named (L : Lay) (t : State) : Prop := t.syms Impl.Ed25519.X86.combSym = L.T

/-- Every run keeps the addresses of statics. -/
theorem two_syms {P Q : State → Prop} {c : Prog isa}
    (h : RelCT isa (Two L g₁ g₂ m₁ m₂ P) c (Two L g₁ g₂ m₁ m₂ Q)) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => P t ∧ Named L t) c
      (Two L g₁ g₂ m₁ m₂ fun t => Q t ∧ Named L t) := by
  intro a b ta tb a' b' ⟨ha, hb, ⟨pa, ya⟩, ⟨pb, yb⟩⟩ ea eb
  obtain ⟨e, ha', hb', qa, qb⟩ := h _ _ _ _ _ _ ⟨ha, hb, pa, pb⟩ ea eb
  exact ⟨e, ha', hb', ⟨qa, (congrFun (Exec.syms ea) _).trans ya⟩,
    ⟨qb, (congrFun (Exec.syms eb) _).trans yb⟩⟩

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.Body`. -/
section
/-! Merged from `Proof.Ed25519.X86.SignCached.Secret`. -/
section
/-! Merged from `Proof.Ed25519.X86.SignCached.Preserve`. -/
section
/-! Merged from `Proof.Ed25519.X86.SignCached.HashSteps`. -/
section
/-! Merged from `Proof.Ed25519.X86.SignCached.HashPreserve`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86

theorem bytes_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Ed25519.bytesAt m p n).length = n := by
  simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]

theorem hash_frame_bytes {L : Lay} (hL : L.Ok) {m m' : Mem} (hf : Frame (hashWrites L) m m')
    {d n : Nat} (hd : 24 ≤ d) (hn : d + n ≤ 192) :
    Spec.Ed25519.bytesAt m' (L.E.setWidth 64 + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.E.setWidth 64 + BitVec.ofNat 64 d) n := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  refine hf.bytes (R := ⟨L.E.setWidth 64 + BitVec.ofNat 64 d, n⟩) ?_ (by change n ≤ 2 ^ 64; omega_using [hn]) (List.mem_range.mp hi)
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p (Offset.sub_base _ (by omega_using [hn] : d + n ≤ 256) p hp))
  · exact Offset.disjoint_base _ (by omega_using [hd]) (by omega_using [hn])
  · change Region.Disjoint _ ⟨(L.E - BitVec.ofNat 32 24).setWidth 64, 24⟩
    rw [Taint.sub_setWidth hL.below]
    exact Offset.disjoint_below _ (n := 24) (d := d) (k := n) (by omega_using [hn])
  · exact Offset.disjoint _ (e := 192) (k := 64) (by omega_using [hn]) (by omega_using [hn]) (by decide)

theorem hash_out_bytes {L : Lay} (hL : L.Ok) {m m' : Mem} (hf : Frame (hashWrites L) m m') :
    Spec.Ed25519.bytesAt m' (L.out.setWidth 64) 32 = Spec.Ed25519.bytesAt m (L.out.setWidth 64) 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  refine hf.bytes (R := ⟨L.out.setWidth 64, 32⟩) ?_ (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  have ho : Region.Sub ⟨L.out.setWidth 64, 32⟩ L.OUT := Region.sub_prefix (by decide)
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.oc.sub_left ho
  · exact ((hL.ko.sub_left (fun p hp => Whole.frame_sub L.E p
      (Region.sub_prefix (by decide : 24 ≤ 256) p hp))).sub_right ho).symm
  · exact ((hL.ko.sub_left (Whole.below_sub_stack hL.below (by decide))).sub_right ho).symm
  · exact ((hL.ko.sub_left (fun p hp => Whole.frame_sub L.E p
      (Offset.sub_base _ (by decide : 192 + 64 ≤ 256) p hp))).sub_right ho).symm

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem update_input (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (source count : Nat) (hsource : source < 6) (hi : Input L (L.value source) 32)
    {prev : List Byte} (hcount : (BitVec.ofNat 32 count).toNat = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (update (inputArgs source count)) s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt s.mem ((L.value source).setWidth 64) 32) := by
  refine update_step hc hL ha (by simp) (by simp [Whole.valid, hsource]) ?_ hi hcount hr
  intro t ht
  have h := update_args hL count (.caller source 0) (.const 32) ht
  change UpdateArgs L (BitVec.ofNat 32 count) (L.value source) (32#32) t
  simpa only [value, BitVec.add_zero] using h

theorem update_prefix (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) []) :
    WP isa (update prefixArgs) s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 64) 32) := by
  have e : (L.E + 64).setWidth 64 = L.E.setWidth 64 + 64 :=
    addr_eq (x := L.E) (k := 64) (by have := hL.top; omega_using [this])
  refine WP.mono (update_step hc hL ha (c := 0#32) (by decide) (by exact Whole.valid_all (by decide)) ?_
    (prefix_input hL) (prev := []) (by decide) hr) fun t ⟨ht, hf, hp⟩ => ⟨ht, hf, ?_⟩
  · intro t ht
    exact update_args hL 0 (.frame 64) (.const 32) ht
  · simpa only [List.nil_append, e, show (32 : BitVec 32).toNat = 32 from rfl] using hp

theorem update_message (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (count : Nat) {prev : List Byte} (hcount : (BitVec.ofNat 32 count).toNat = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (update (messageArgs count)) s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.mono (update_step hc hL ha (by simp) (by simp [Whole.valid]) ?_
    (message_input hL) hcount hr) fun t ⟨ht, hf, hp⟩ => ⟨ht, hf, ?_⟩
  · intro t ht
    have h := update_args hL count (.caller 3 0) (.caller 4 0) ht
    simpa only [value, Lay.value, BitVec.add_zero] using h
  · rw [hc.input_bytes hL (r := L.MSG) (by simp [Lay.inputs]) (by have := L.len.isLt; change L.len.toNat ≤ 2 ^ 64; omega_using [])] at hp
    exact hp

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.Reduce`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem reduce_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (d : Nat) (hd : 24 ≤ d) (hd' : d + 32 ≤ 256) :
    WP isa (reduce d) s fun t => Ctx L g m₀ t ∧
      Frame (primitiveWrites L (field L d)) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem ((fp L d).setWidth 64) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 192) 64) := by
  refine WP.seq (WP.mono (args_ok hc hL ha (vs := [.frame d, .frame 192, .caller 5 0])
    (by simp) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs.slot hL (j := 0) (by simp) (by simp)
  have a1 := hs.slot hL (j := 1) (by simp) (by simp)
  have a2 := hs.slot hL (j := 2) (by simp) (by simp)
  change Whole.slots L.E u 0 = L.E + BitVec.ofNat 32 d at a0
  change Whole.slots L.E u 1 = L.E + 192 at a1
  change Whole.slots L.E u 2 = L.scr + 0#32 at a2
  rw [BitVec.add_zero] at a2
  refine WP.mono (Whole.reduce_call hu (hashSpace hL) (by simp [Lay.outputs]) hd hd' a0 a1 a2)
    fun t ⟨ht, hft, hp⟩ => ⟨ht, primitive_frame hf hft, ?_⟩
  change Spec.Ed25519.bytesAt t.mem ((fp L d).setWidth 64) 32 = Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt u.mem ((L.E + 192).setWidth 64) 64) at hp
  rw [hp]
  refine congrArg Spec.Ed25519.scalarReduce ?_
  have ea : (L.E + 192).setWidth 64 = L.E.setWidth 64 + 192 :=
    Whole.frame_addr (hashSpace hL).frameFit (by decide)
  rw [ea]
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (R := ⟨L.E.setWidth 64 + 192, 64⟩)
    (by
      rintro r hr
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint_base _ (d := 192) (n := 64) (k := 24) (by decide) (by decide))
    (by change 64 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.Hashes`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem hashNonce_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa hashNonce s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 64) 32 ++
          Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (update_prefix hu hL ha ru) fun v ⟨hv, fv, rv⟩ => ?_)
  have keep := hash_frame_bytes hL fu (d := 64) (n := 32) (by decide) (by decide)
  change Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + (64 : BitVec 64)) 32 = Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + (64 : BitVec 64)) 32 at keep
  rw [keep] at rv
  refine WP.seq (WP.mono (update_message hv hL ha 32 (by rw [bytes_length]; rfl) rv)
    fun w ⟨hw, fw, rw'⟩ => ?_)
  refine WP.mono (finalize_step hw hL ha 32 (by decide) true ?_ ?_ rw')
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans (fw.trans ft)), hd⟩
  · rw [List.length_append, bytes_length, bytes_length]
    have := L.len.isLt; omega_using []
  · rw [List.length_append, bytes_length, bytes_length]
    simp only [ite_true]; omega_using []

theorem hashChallenge_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa hashChallenge s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (L.out.setWidth 64) 32 ++
          Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32 ++
          Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (update_input hu hL ha 0 0 (by decide) (point_input hL)
    (by decide) ru) fun v ⟨hv, fv, rv⟩ => ?_)
  change Spec.Sha512.Repr _ v.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem (L.out.setWidth 64) 32) at rv
  rw [List.nil_append, hash_out_bytes hL fu] at rv
  refine WP.seq (WP.mono (update_input hv hL ha 2 32 (by decide) (key_input hL)
    (by rw [bytes_length]; rfl) rv) fun w ⟨hw, fw, rw'⟩ => ?_)
  have hk := hv.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  change Spec.Ed25519.bytesAt v.mem (L.pk.setWidth 64) 32 = Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32 at hk
  change Spec.Sha512.Repr _ w.mem _ (_ ++ Spec.Ed25519.bytesAt v.mem (L.pk.setWidth 64) 32) at rw'
  rw [hk] at rw'
  refine WP.seq (WP.mono (update_message hw hL ha 64 (by rw [List.length_append, bytes_length, bytes_length]; rfl)
    rw') fun z ⟨hz, fz, rz⟩ => ?_)
  refine WP.mono (finalize_step hz hL ha 64 (by decide) true ?_ ?_ rz)
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans (fw.trans (fz.trans ft))), hd⟩
  · rw [List.length_append, List.length_append, bytes_length, bytes_length, bytes_length]
    have := L.len.isLt; omega_using []
  · rw [List.length_append, List.length_append, bytes_length, bytes_length, bytes_length]
    simp only [ite_true]; omega_using []

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86
variable {L : Lay} {m m' : Mem}

theorem frame_bytes {rs : List Region} (hf : Frame rs m m') (r : Region)
    (hd : ∀ R ∈ rs, r.Disjoint R) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m' r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  exact List.map_congr_left fun i hi => hf.bytes hd hn (List.mem_range.mp hi)

theorem single_frame_bytes {d n e k : Nat} (hf : Frame [⟨L.E.setWidth 64 + BitVec.ofNat 64 e, k⟩] m m')
    (hsep : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 256) (he : e + k ≤ 256) :
    Spec.Ed25519.bytesAt m' (L.E.setWidth 64 + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.E.setWidth 64 + BitVec.ofNat 64 d) n :=
  frame_bytes hf ⟨L.E.setWidth 64 + BitVec.ofNat 64 d, n⟩
    (by rintro r hr; rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hsep (by omega_using [hd]) (by omega_using [he]))
    (by change n ≤ 2 ^ 64; omega_using [hd])

theorem primitive_field_bytes (hL : L.Ok) {out : Region}
    (hf : Frame (primitiveWrites L out) m m') {d : Nat} (hd : 24 ≤ d) (hb : d + 32 ≤ 256)
    (ho : (field L d).Disjoint out) :
    Spec.Ed25519.bytesAt m' ((fp L d).setWidth 64) 32 =
      Spec.Ed25519.bytesAt m ((fp L d).setWidth 64) 32 := by
  refine frame_bytes hf (field L d) ?_ (by change 32 ≤ 2 ^ 64; decide)
  simp only [primitiveWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ho
  · exact hL.kc.sub_left (field_sub hL hb)
  · change Region.Disjoint ⟨(fp L d).setWidth 64, 32⟩ _
    rw [fp_addr hL (by omega_using [hb])]
    exact Offset.disjoint_base _ hd (by omega_using [hb])
  · change Region.Disjoint ⟨(fp L d).setWidth 64, 32⟩ ⟨(L.E - BitVec.ofNat 32 24).setWidth 64, 24⟩
    rw [fp_addr hL (by omega_using [hb]), Taint.sub_setWidth hL.below]
    exact Offset.disjoint_below _ (n := 24) (d := d) (k := 32) (by omega_using [hb])

theorem reduce_field_bytes (hL : L.Ok) {o d : Nat}
    (hf : Frame (primitiveWrites L (field L o)) m m') (hd : 24 ≤ d) (hb : d + 32 ≤ 256)
    (ho : o + 32 ≤ 256) (hs : d + 32 ≤ o ∨ o + 32 ≤ d) :
    Spec.Ed25519.bytesAt m' ((fp L d).setWidth 64) 32 =
      Spec.Ed25519.bytesAt m ((fp L d).setWidth 64) 32 := by
  refine primitive_field_bytes hL hf hd hb ?_
  change Region.Disjoint ⟨(fp L d).setWidth 64, 32⟩ ⟨(fp L o).setWidth 64, 32⟩
  rw [fp_addr hL (by omega_using [hb]), fp_addr hL (by omega_using [ho])]
  exact Offset.disjoint _ hs (by omega_using [hb]) (by omega_using [ho])

theorem base_field_bytes (hL : L.Ok) (hf : Frame (primitiveWrites L (baseOut L)) m m')
    {d : Nat} (hd : 24 ≤ d) (hb : d + 32 ≤ 256) :
    Spec.Ed25519.bytesAt m' ((fp L d).setWidth 64) 32 =
      Spec.Ed25519.bytesAt m ((fp L d).setWidth 64) 32 :=
  primitive_field_bytes hL hf hd hb ((hL.ko.sub_left (field_sub hL hb)).sub_right (Region.sub_prefix (by decide)))

theorem primitive_out_bytes (hL : L.Ok) {out : Region}
    (hf : Frame (primitiveWrites L out) m m') (ho : (baseOut L).Disjoint out) :
    Spec.Ed25519.bytesAt m' (L.out.setWidth 64) 32 = Spec.Ed25519.bytesAt m (L.out.setWidth 64) 32 := by
  refine frame_bytes hf (baseOut L) ?_ (by change 32 ≤ 2 ^ 64; decide)
  have hs : Region.Sub (baseOut L) L.OUT := Region.sub_prefix (by decide)
  simp only [primitiveWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ho
  · exact hL.oc.sub_left hs
  · exact ((hL.ko.sub_left (fun p hp => Whole.frame_sub L.E p
      (Region.sub_prefix (by decide : 24 ≤ 256) p hp))).sub_right hs).symm
  · exact ((hL.ko.sub_left (Whole.below_sub_stack hL.below (by decide))).sub_right hs).symm

theorem reduce_out_bytes (hL : L.Ok) {d : Nat} (hf : Frame (primitiveWrites L (field L d)) m m')
    (hd : d + 32 ≤ 256) :
    Spec.Ed25519.bytesAt m' (L.out.setWidth 64) 32 = Spec.Ed25519.bytesAt m (L.out.setWidth 64) 32 :=
  primitive_out_bytes hL hf (((hL.ko.sub_left (field_sub hL hd)).sub_right (Region.sub_prefix (by decide))).symm)

theorem mul_out_bytes (hL : L.Ok) (hf : Frame (primitiveWrites L (half L)) m m') :
    Spec.Ed25519.bytesAt m' (L.out.setWidth 64) 32 = Spec.Ed25519.bytesAt m (L.out.setWidth 64) 32 := by
  refine primitive_out_bytes hL hf ?_
  change Region.Disjoint ⟨L.out.setWidth 64, 32⟩ ⟨(L.out + 32).setWidth 64, 32⟩
  rw [half_addr hL]
  exact Offset.base_disjoint _ (e := 32) (n := 32) (k := 32) (by decide) (by decide)

theorem hash_field_bytes (hL : L.Ok) (hf : Frame (hashWrites L) m m')
    {d : Nat} (hd : 24 ≤ d) (hb : d + 32 ≤ 192) :
    Spec.Ed25519.bytesAt m' ((fp L d).setWidth 64) 32 =
      Spec.Ed25519.bytesAt m ((fp L d).setWidth 64) 32 := by
  rw [fp_addr hL (by omega_using [hb])]
  exact hash_frame_bytes hL hf hd hb

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem ctx_step {t : State} (hc : Ctx L g m₀ s) (ht : PublicKey.Step s t) {d n : Nat}
    (hf : Frame [⟨L.E.setWidth 64 + BitVec.ofNat 64 d, n⟩] s.mem t.mem) (hn : d + n ≤ 256) :
    Ctx L g m₀ t := by
  refine hc.of_frame ht.rd ht.wr ht.esp ?_ hf ?_
  · intro r hr _
    apply ht.regs
    rintro rfl; simp [calleeSaved] at hr
  · intro r hr; rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ hn)

theorem saveSecret_ok (hc : Ctx L g m₀ s) (hL : L.Ok) {expanded : List Byte}
    (he : Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 192) 64 = expanded) :
    WP isa (.block saveSecret) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem ((fp L 32).setWidth 64) 32 =
        Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune expanded) ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 64) 32 = expanded.drop 32 := by
  rw [saveSecret, WP.block_append_iff]
  have fr : Whole.FR L.E ∈ s.wr := by rw [hc.wr]; exact List.mem_cons_self
  have fit := (hashSpace hL).frameFit
  refine WP.mono (PublicKey.prune_ok hc.esp fit fr he) fun u ⟨hu, hf, hs⟩ => ?_
  have hcu := ctx_step hc hu (d := 32) (n := 32) hf (by decide)
  refine WP.mono (prefix_ok hcu.esp fit (by rw [hcu.wr]; exact List.mem_cons_self))
    fun t ⟨ht, hft, hp⟩ => ⟨ctx_step hcu ht (d := 64) (n := 32) hft (by decide), ?_, ?_⟩
  · rw [fp_addr hL (by decide)]
    have keep := single_frame_bytes (L := L) hft (d := 32) (n := 32) (e := 64) (k := 32)
      (by decide) (by decide) (by decide)
    rw [keep]
    have sc := Proof.Ed25519.bytesAt_encodeLE u.mem (L.E.setWidth 64 + 32) 32
    rw [hs] at sc
    exact sc
  · rw [hp]
    have keep := single_frame_bytes (L := L) hf (d := 224) (n := 32) (e := 32) (k := 32)
      (by decide) (by decide) (by decide)
    change Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + (224 : BitVec 64)) 32 =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + (224 : BitVec 64)) 32 at keep
    rw [keep, ← he, Proof.Ed25519.signatureBytes_drop]
    rw [BitVec.add_assoc, show (192 : BitVec 64) + BitVec.ofNat 64 32 = (224 : BitVec 64) from rfl]

/-- The secret scalar of the digest `E`. -/
def scalar (E : List Byte) : List Byte := Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune E)
/-- The nonce of the digest `E` and the message. -/
def nonce (L : Lay) (m : Mem) (E : List Byte) : List Byte :=
  Spec.Ed25519.scalarReduce (Spec.Sha512.sha512
    (E.drop 32 ++ Spec.Ed25519.bytesAt m (L.msg.setWidth 64) L.len.toNat))

structure SecretReady (L : Lay) (E : List Byte) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem ((fp L 32).setWidth 64) 32 = scalar E
  prefixBytes : Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 64) 32 = E.drop 32

/-- The scalar and the prefix of the digest `E` that `first` leaves at 192. -/
theorem secretFrom_ok {first : Prog isa} {E : List Byte}
    (hh : WP isa first s fun t => Ctx L g m₀ t ∧ Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 = E)
    (hL : L.Ok) :
    WP isa (secretFrom first) s fun t => Ctx L g m₀ t ∧ SecretReady L E t :=
  WP.seq (WP.mono hh fun _ ⟨hu, hd⟩ =>
    WP.mono (saveSecret_ok hu hL hd) fun _ ⟨ht, hs, hp⟩ => ⟨ht, hs, hp⟩)

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

structure NonceReady (L : Lay) (m : Mem) (E : List Byte) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem ((fp L 32).setWidth 64) 32 = scalar E
  nonce : Spec.Ed25519.bytesAt t.mem ((fp L 96).setWidth 64) 32 = nonce L m E
  point : Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 32 = Spec.Ed25519.scalarBase (SignCached.nonce L m E)

theorem nonce_ok {E : List Byte} (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (hs : SecretReady L E s)
    (hy : s.syms Impl.Ed25519.X86.combSym = L.T) :
    WP isa nonceCode s fun t => Ctx L g m₀ t ∧ NonceReady L m₀ E t := by
  refine WP.seq (WP.mono_syms (hashNonce_ok hc hL ha) fun u ⟨hu, fu, du⟩ yu => ?_)
  rw [hs.prefixBytes] at du
  have su := (hash_field_bytes hL fu (d := 32) (by decide) (by decide)).trans hs.scalar
  refine WP.seq (WP.mono_syms (reduce_step hu hL ha 96 (by decide) (by decide))
    fun v ⟨hv, fv, nv⟩ yv => ?_)
  rw [du] at nv
  have sv := (reduce_field_bytes hL fv (d := 32) (by decide) (by decide) (by decide) (by decide)).trans su
  refine WP.mono (base_step hv hL ha (by rw [yv, yu]; exact hy)) fun t ⟨ht, ft, pt⟩ =>
    ⟨ht, ?_, ?_, ?_⟩
  · exact (base_field_bytes hL ft (d := 32) (by decide) (by decide)).trans sv
  · exact (base_field_bytes hL ft (d := 96) (by decide) (by decide)).trans nv
  · rw [nv] at pt
    exact pt

theorem challenge_ok {seed : List Byte} (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (hs : NonceReady L m₀ (Spec.Sha512.sha512 seed) s)
    (hk : Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32 = Spec.Ed25519.publicKey seed) :
    WP isa challengeCode s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 64 = Spec.Ed25519.sign seed
        (Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.seq (WP.mono (hashChallenge_ok hc hL ha) fun u ⟨hu, fu, du⟩ => ?_)
  rw [hs.point] at du
  have su := (hash_field_bytes hL fu (d := 32) (by decide) (by decide)).trans hs.scalar
  have nu := (hash_field_bytes hL fu (d := 96) (by decide) (by decide)).trans hs.nonce
  have pu := (hash_out_bytes hL fu).trans hs.point
  refine WP.seq (WP.mono (reduce_step hu hL ha 128 (by decide) (by decide)) fun v ⟨hv, fv, cv⟩ => ?_)
  rw [du] at cv
  have sv := (reduce_field_bytes hL fv (d := 32) (by decide) (by decide) (by decide) (by decide)).trans su
  have nv := (reduce_field_bytes hL fv (d := 96) (by decide) (by decide) (by decide) (by decide)).trans nu
  have pv := (reduce_out_bytes hL fv (by decide)).trans pu
  refine WP.mono (mul_step hv hL ha) fun t ⟨ht, ft, st⟩ => ⟨ht, ?_⟩
  rw [nv, cv, sv] at st
  have pt := (mul_out_bytes hL ft).trans pv
  rw [Proof.Ed25519.signatureBytes_split, pt]
  change Spec.Ed25519.scalarBase (nonce L m₀ (Spec.Sha512.sha512 seed)) ++ Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64 + (32 : BitVec 64)) 32 = _
  rw [st]
  exact Proof.Ed25519.sign_pipeline _ _ _ hk

theorem wipe_ok (hc : Ctx L g m₀ s) (hL : L.Ok) :
    WP isa (.block wipe) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 64 = Spec.Ed25519.bytesAt s.mem (L.out.setWidth 64) 64 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 8) (count := 56) (hashSpace hL).frameFit (by decide))
    fun t ⟨ht, hf, _⟩ => ⟨ht, ?_⟩
  refine frame_bytes hf L.OUT ?_ (by change 64 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (fun p hp => Whole.frame_sub L.E p
    (Offset.sub_base _ (by decide : 4 * 8 + 4 * 56 ≤ 256) p hp))).symm

/-- The signature of `seed`, after any `first` that leaves its digest at 192. -/
theorem bodyFrom_ok (hL : L.Ok) (ha : Arguments L m₀) {first : Prog isa} {seed : List Byte}
    (hh : WP isa first s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 = Spec.Sha512.sha512 seed)
    (hk : Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32 = Spec.Ed25519.publicKey seed)
    (hy : s.syms Impl.Ed25519.X86.combSym = L.T) :
    WP isa (bodyFrom first) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 64 = Spec.Ed25519.sign seed
        (Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.seq (WP.mono_syms (secretFrom_ok hh hL) fun u ⟨hu, su⟩ yu => ?_)
  refine WP.seq (WP.mono (nonce_ok hu hL ha su (by rw [yu]; exact hy)) fun v ⟨hv, nv⟩ => ?_)
  refine WP.seq (WP.mono (challenge_ok hv hL ha nv hk) fun w ⟨hw, sw⟩ => ?_)
  exact WP.mono (wipe_ok hw hL) fun t ⟨ht, same⟩ => ⟨ht, same.trans sw⟩

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.CTPrimitives`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem reduce_call_ct (hL : L.Ok) (d : Nat) (hd : 24 ≤ d) (hd' : d + 32 ≤ 256) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.frame d, .frame 192, .caller 5 0]))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.X86.scalarReduce)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL scalarReduce_ok scalarReduce_ct Whole.reduce_nosp (by rw [Whole.reduce_stack]; decide)
  · intro g m t hc hs
    exact reduce_ready hc hL hd hd' (hs.slot hL (j := 0) (by simp) (by simp))
      (hs.slot hL (j := 1) (by simp) (by simp))
      ((hs.slot hL (j := 2) (by simp) (by simp)).trans (BitVec.add_zero _))
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by simp) h (by decide : 0 < 3),
      call_args_eq hL (by simp) h (by decide : 1 < 3), call_args_eq hL (by simp) h (by decide : 2 < 3)⟩

theorem base_call_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => OutArgs L [.caller 0 0, .frame 96, .caller 5 0] t ∧ Named L t)
      (.call "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase)
      (Two L g₁ g₂ m₁ m₂ fun t => True ∧ Named L t) := by
  have args : ∀ {t : State}, OutArgs L [.caller 0 0, .frame 96, .caller 5 0] t → BaseArgs L t :=
    fun hs => ⟨((hs.slot hL (j := 0) (by decide) (by decide)).trans (BitVec.add_zero _)),
      hs.slot hL (j := 1) (by decide) (by decide),
      ((hs.slot hL (j := 2) (by decide) (by decide)).trans (BitVec.add_zero _))⟩
  have hct : RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => OutArgs L [.caller 0 0, .frame 96, .caller 5 0] t ∧
      Named L t) (.call "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase) fun _ _ => True := by
    refine Whole.callEx scalarBase_ok scalarBase_ct fun a b h => ?_
    let ra := base_ready h.1 hL (args h.2.2.1.1) h.2.2.1.2 (h.1.tbl hL ha)
    let rb := base_ready h.2.1 hL (args h.2.2.2.1) h.2.2.2.2 (h.2.1.tbl hL hb)
    obtain ⟨ca, wa⟩ := ra.covers_state h.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    have h' : Two L g₁ g₂ m₁ m₂ (OutArgs L [.caller 0 0, .frame 96, .caller 5 0]) a b :=
      ⟨h.1, h.2.1, h.2.2.1.1, h.2.2.2.1⟩
    refine ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre, ⟨congrArg (· - 4) (two_esp h),
      call_args_eq hL (by decide) h' (by decide : 0 < 3), call_args_eq hL (by decide) h' (by decide : 1 < 3),
      call_args_eq hL (by decide) h' (by decide : 2 < 3), ?_⟩, ca, wa, cb, wb, two_esp h⟩
    change a.syms _ = b.syms _
    rw [h.2.2.1.2, h.2.2.2.2]
  have fw : ∀ {g : Reg → BitVec 32} {m : Mem}, Arguments L m → ∀ u, Ctx L g m u →
      OutArgs L [.caller 0 0, .frame 96, .caller 5 0] u ∧ Named L u →
      WP isa (.call "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase) u
        (fun v => Ctx L g m v ∧ True ∧ Named L v) := fun hm u hc hs =>
    WP.mono_syms ((base_ready hc hL (args hs.1) hs.2 (hc.tbl hL hm)).wp hc scalarBase_ok base_nosp
      (by rw [base_stack]; decide) hL.below) fun _ hv yv => ⟨hv, trivial, by
        rw [Named, yv]; exact hs.2⟩
  exact two_wp hct (fw ha) (fw hb)

theorem mul_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.caller 0 32, .frame 96, .frame 128, .frame 32, .caller 5 0]))
      (.call "vg_ed25519_scalar_mul_add" Impl.Ed25519.X86.scalarMulAdd)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL scalarMulAdd_ok scalarMulAdd_ct mul_nosp (by rw [mul_stack]; decide)
  · intro g m t hc hs
    exact mul_ready hc hL ⟨hs.slot hL (j := 0) (by decide) (by decide),
      hs.slot hL (j := 1) (by decide) (by decide), hs.slot hL (j := 2) (by decide) (by decide),
      hs.slot hL (j := 3) (by decide) (by decide),
      ((hs.slot hL (j := 4) (by decide) (by decide)).trans (BitVec.add_zero _))⟩
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by decide) h (by decide : 0 < 5),
      call_args_eq hL (by decide) h (by decide : 1 < 5), call_args_eq hL (by decide) h (by decide : 2 < 5),
      call_args_eq hL (by decide) h (by decide : 3 < 5), call_args_eq hL (by decide) h (by decide : 4 < 5)⟩

theorem saveSecret_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block saveSecret)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) (by native_taint_decide)) ?_ ?_
  · intro t hc _
    exact WP.mono (saveSecret_ok hc hL rfl) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (saveSecret_ok hc hL rfl) fun _ h => ⟨h.1, trivial⟩

theorem wipe_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block wipe)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) (by native_taint_decide)) ?_ ?_
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.CTHashPipeline`. -/
section
/-! Merged from `Proof.Ed25519.X86.SignCached.CTHash`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem init_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.caller 5 0]))
      (.call (Spec.Sha512.init512Api.name ++ "_core") (Impl.Sha512.X86.Stream.init Spec.Sha512.H0_512))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL (Proof.Sha512.X86.Stream.init_verified _).1
    (Proof.Sha512.X86.Stream.init_verified _).2.1 Whole.init_nosp (by rw [Whole.init_stack]; decide)
  · intro g m t hc hs
    apply init_ready hc hL
    exact (hs.slot hL (j := 0) (by decide) (by decide)).trans (BitVec.add_zero _)
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by decide) h (by decide : 0 < 1)⟩

theorem update_call_ct (hL : L.Ok) {vs : List Value} (hn : vs.length = 6)
    {c p n : BitVec 32} (hi : Input L p n)
    (hargs : ∀ t, OutArgs L vs t → UpdateArgs L c p n t) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L vs))
      (.call "vg_sha512_update_scratch" Impl.Sha512.X86.Stream.update)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL Proof.Sha512.X86.Stream.Update.update_verified.1
    Proof.Sha512.X86.Stream.Update.update_verified.2.1 Whole.update_nosp (by rw [Whole.update_stack])
  · intro g m t hc hs
    exact update_ready hc hL hi (hargs t hs)
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), fun j hj => call_args_eq hL (by omega_using [hn]) h (by omega_using [hn, hj])⟩

theorem append_pair_eq {a b c d : BitVec 32} (h : a ++ b = c ++ d) : a = c ∧ b = d := by
  constructor
  · have e := congrArg (BitVec.extractLsb' 32 32) h
    simpa only [BitVec.extractLsb'_append_eq_left] using e
  · have e := congrArg (BitVec.extractLsb' 0 32) h
    simpa only [BitVec.extractLsb'_append_eq_right] using e

theorem finalize_call_ct (hL : L.Ok) (count : BitVec 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (FinArgs L count))
      (.call "vg_sha512_finalize_scratch" Impl.Sha512.X86.Stream.finalize)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL Proof.Sha512.X86.Stream.Finalize.finalize_verified.1
    Proof.Sha512.X86.Stream.Finalize.finalize_verified.2.1 Whole.finalize_nosp (by rw [Whole.finalize_stack])
  · intro g m t hc hs
    exact finalize_ready hc hL hs
  · intro a b ar aw br bw h
    refine ⟨congrArg (· - 4) (two_esp h), ?_⟩
    intro j hj
    have H := hashSpace hL
    rw [arg_withRegions, arg_withRegions, Whole.call_arg h.1.esp H.below H.frameFit (by omega_using [hj]),
      Whole.call_arg h.2.1.esp H.below H.frameFit (by omega_using [hj])]
    obtain ⟨a0, a3, a4, ac⟩ := h.2.2.1
    obtain ⟨b0, b3, b4, bc⟩ := h.2.2.2
    have pair := append_pair_eq (ac.trans bc.symm)
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega_using [hj]) with rfl | rfl | rfl | rfl | rfl
    · exact a0.trans b0.symm
    · exact pair.2
    · exact pair.1
    · exact a3.trans b3.symm
    · exact a4.trans b4.symm

theorem finalize_args_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (n : Nat) (hn : n < 2 ^ 32) (b : Bool)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (finalizeArgs n b)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block (finalizeArgs n b))
      (Two L g₁ g₂ m₁ m₂ (FinArgs L (BitVec.ofNat 64 ((if b then L.len.toNat else 0) + n)))) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) ht) ?_ ?_
  · intro s hc _
    exact WP.mono (finalizeArgs_ok hc hL ha n hn b) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩
  · intro s hc _
    exact WP.mono (finalizeArgs_ok hc hL hb n hn b) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem init_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) init (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [.caller 5 0] (by decide) (by exact Whole.valid_all (by decide)) (by native_taint_decide)).seq
    (init_call_ct hL)

theorem update_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (count : Nat) (p n : Value) (hp : Whole.valid 6 p) (hn : Whole.valid 6 n)
    (hi : Input L (value L p) (value L n))
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (setup 0
      [.caller 5 0, .const count, .const 0, p, n, .caller 5 192])) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True)
      (update (setup 0 [.caller 5 0, .const count, .const 0, p, n, .caller 5 192]))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb _ (by simp) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl | rfl)
    · simp [Whole.valid]
    · simp [Whole.valid]
    · simp [Whole.valid]
    · exact hp
    · exact hn
    · simp [Whole.valid]) ht).seq
    (update_call_ct hL rfl hi (fun _ hs => update_args hL count p n hs))

theorem finalize_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (n : Nat) (hn : n < 2 ^ 32) (b : Bool)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (finalizeArgs n b)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (finalize n b)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (finalize_args_ct hL ha hb n hn b ht).seq (finalize_call_ct hL _)

theorem hashNonce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) hashNonce
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hs := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 0 (.frame 64) (.const 32)
    (Whole.valid_of (by decide)) (Whole.valid_of (by decide)) (prefix_input hL) (by native_taint_decide)
  have hm := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 32 (.caller 3 0) (.caller 4 0)
    (Whole.valid_of (by decide)) (Whole.valid_of (by decide)) (by simpa only [value, Lay.value, BitVec.add_zero] using message_input hL)
    (by native_taint_decide)
  exact (init_ct hL ha hb).seq (hs.seq (hm.seq
    (finalize_ct hL ha hb 32 (by decide) true (by native_taint_decide))))

theorem hashChallenge_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) hashChallenge
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hr := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 0 (.caller 0 0) (.const 32)
    (Whole.valid_of (by decide)) (Whole.valid_of (by decide)) (by simpa [value, Lay.value] using point_input hL)
    (by native_taint_decide)
  have hp := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 32 (.caller 2 0) (.const 32)
    (Whole.valid_of (by decide)) (Whole.valid_of (by decide)) (by simpa [value, Lay.value] using key_input hL)
    (by native_taint_decide)
  have hm := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 64 (.caller 3 0) (.caller 4 0)
    (Whole.valid_of (by decide)) (Whole.valid_of (by decide)) (by simpa only [value, Lay.value, BitVec.add_zero] using message_input hL)
    (by native_taint_decide)
  exact (init_ct hL ha hb).seq (hr.seq (hp.seq (hm.seq
    (finalize_ct hL ha hb 64 (by decide) true (by native_taint_decide)))))

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.CTBody`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

/-- Signing after any `first` whose runs are related. -/
theorem bodyFrom_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) {first : Prog isa}
    (hh : RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) first (Two L g₁ g₂ m₁ m₂ fun _ => True)) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => True ∧ Named L t) (bodyFrom first)
      (Two L g₁ g₂ m₁ m₂ fun t => True ∧ Named L t) := by
  have r96 := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.frame 96, .frame 192, .caller 5 0]
    (by decide) (by exact Whole.valid_all (by decide)) (by native_taint_decide)).seq
    (reduce_call_ct hL 96 (by decide) (by decide))
  have r128 := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.frame 128, .frame 192, .caller 5 0]
    (by decide) (by exact Whole.valid_all (by decide)) (by native_taint_decide)).seq
    (reduce_call_ct hL 128 (by decide) (by decide))
  have b := (two_syms (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 0 0, .frame 96, .caller 5 0]
    (by decide) (by exact Whole.valid_all (by decide)) (by native_taint_decide))).seq (base_call_ct hL ha hb)
  have m := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 0 32, .frame 96, .frame 128, .frame 32, .caller 5 0]
    (by decide) (by exact Whole.valid_all (by decide)) (by native_taint_decide)).seq (mul_call_ct hL)
  exact (two_syms (hh.seq (saveSecret_ct hL))).seq
    (((two_syms (hashNonce_ct hL ha hb)).seq ((two_syms r96).seq b)).seq
      (two_syms (((hashChallenge_ct hL ha hb).seq (r128.seq m)).seq (wipe_ct hL))))

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.Correct`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

private theorem noSp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact ha i hi
  · exact hb i hi

private theorem noSp_update {args : List Instr} (h : NoSp (.block args)) : NoSp (update args) :=
  noSp_seq h Whole.update_nosp

private theorem noSp_finalize {n : Nat} {b : Bool} (h : NoSp (.block (finalizeArgs n b))) :
    NoSp (finalize n b) := noSp_seq h Whole.finalize_nosp

private theorem noSp_reduce {n : Nat} (h : NoSp (.block (reduceArgs n))) : NoSp (reduce n) :=
  noSp_seq h Whole.reduce_nosp

theorem bodyFrom_nosp {first : Prog isa} (hs : NoSp first) : NoSp (bodyFrom first) := by
  have ni : NoSp init := noSp_seq (NoSp.of_all (by decide +kernel)) Whole.init_nosp
  have hn : NoSp hashNonce := noSp_seq ni (noSp_seq
    (noSp_update (NoSp.of_all (by decide +kernel)))
    (noSp_seq (noSp_update (NoSp.of_all (by decide +kernel)))
      (noSp_finalize (NoSp.of_all (by decide +kernel)))))
  have hc : NoSp hashChallenge := noSp_seq ni (noSp_seq
    (noSp_update (NoSp.of_all (by decide +kernel)))
    (noSp_seq (noSp_update (NoSp.of_all (by decide +kernel)))
    (noSp_seq (noSp_update (NoSp.of_all (by decide +kernel)))
      (noSp_finalize (NoSp.of_all (by decide +kernel))))))
  exact noSp_seq (noSp_seq hs (NoSp.of_all (by decide +kernel)))
    (noSp_seq (noSp_seq hn (noSp_seq (noSp_reduce (NoSp.of_all (by decide +kernel)))
      (noSp_seq (NoSp.of_all (by decide +kernel)) base_nosp)))
    (noSp_seq (noSp_seq hc (noSp_seq (noSp_reduce (NoSp.of_all (by decide +kernel)))
      (noSp_seq (NoSp.of_all (by decide +kernel)) mul_nosp))) (NoSp.of_all (by decide +kernel))))

variable {n : Nat} {key : State → Prop} {post : State → State → Prop} in
/-- The frame around `bodyFrom first`, from the signature it leaves in `out`. -/
theorem frame_ok {first : Prog isa} {s : State} (h : (signLocalWith n key post).pre s) (sl : 32 ≤ n)
    (hn : NoSp first)
    {sig : List Byte}
    (hb : WP isa (bodyFrom first) (pushed (List.replicate 64 .eax) s) fun u => Ctx (lay n s) s.gpr s.mem u ∧
      Spec.Ed25519.bytesAt u.mem ((lay n s).out.setWidth 64) 64 = sig)
    (hp : ∀ t, Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 64 = sig → post s t) :
    WP isa (.frame (.push (List.replicate 64 .eax)) (bodyFrom first) (.pop .eax 64)) s
      fun t => abiPreserved s t ∧ post s t := by
  have hL := lay_ok h sl
  have hb' := entry_bounds h
  refine WP.frame (rs := List.replicate 64 .eax) (by simp) (by simp) (by decide)
    (by simp only [List.length_replicate]; omega_using [hb']) (bodyFrom_nosp hn)
    (WP.mono hb fun u ⟨hu, ho⟩ m v fl => ?_)
  simp only [List.length_replicate] at fl
  obtain hb256 : 256 ≤ (s.gpr .esp).toNat := by omega_using [hb']
  refine ⟨⟨fun r hr => ?_, ?_⟩, hp _ ?_⟩
  · show (popped Reg.eax (List.replicate 64 Reg.eax).length u).gpr r = s.gpr r
    by_cases he : r = .esp
    · subst r
      rw [popped_esp, hu.esp, List.length_replicate]
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ he (by intro e; subst r; simp [calleeSaved] at hr), hu.cs r hr he]
  · show m.readW _ 32 = _
    rw [fl.readW (r := (lay n s).RET) (by rw [lay_ret h]; exact Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr, lay_ret h]
      change Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩
        ⟨(s.gpr .esp - BitVec.ofNat 32 256).setWidth 64, 256⟩
      rw [Taint.sub_setWidth hb256]
      exact (Offset.below_disjoint _ (by decide)).symm) (by decide)]
    refine hu.frame.readW (r := (lay n s).RET) ?_ ?_ (by decide)
    · rw [lay_ret h]; exact Region.contains_self _ _
    · simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact hL.ro
      · exact hL.rc
      · change (lay n s).RET.Disjoint (lay n s).STK
        rw [lay_ret h, lay_stack h]
        exact (Offset.below_disjoint _ (by decide)).symm
  · show Spec.Ed25519.bytesAt m _ 64 = sig
    have hko := hL.ko
    rw [lay_stack h] at hko
    refine Eq.trans (List.map_congr_left fun _ hi => fl.bytes (R := (lay n s).OUT) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      refine (hko.sub_left ?_).symm
      change Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 256).setWidth 64, 256⟩ _
      rw [Taint.sub_setWidth hb256]
      exact Taint.below_sub (by decide) (by decide))
      (by show 64 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)) ?_
    exact ho

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

variable {n : Nat} {key : State → Prop} {post : State → State → Prop}

theorem lay_eq {s t : State} (h : signPub s t) : lay n s = lay n t := by
  obtain ⟨sp, a0, a1, a2, a3, a4, a5, sy⟩ := h
  simp only [lay, sp, a0, a1, a2, a3, a4, a5, sy]

/-- The frame around `bodyFrom first`, for any `first` whose runs are related. -/
theorem frame_ct {first : Prog isa} (sl : 32 ≤ n)
    (hh : ∀ {L : Lay} {g₁ g₂ m₁ m₂}, L.Ok → L.seedLen = n → Arguments L m₁ → Arguments L m₂ →
      RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) first (Two L g₁ g₂ m₁ m₂ fun _ => True)) :
    ConstantTime isa (signLocalWith n key post).pre signPub
      (.frame (.push (List.replicate 64 .eax)) (bodyFrom first) (.pop .eax 64)) := by
  apply RelCT.constantTime
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb a' b' ⟨s₁, s₂, ⟨p₁, p₂, hp⟩, rfl, rfl⟩ ea eb
  have he : lay n s₁ = lay n s₂ := lay_eq hp
  have h₂ : Ctx (lay n s₁) s₂.gpr s₂.mem (pushed (List.replicate 64 .eax) s₂) :=
    by rw [he]; exact push_ctx p₂
  have ha₂ : Arguments (lay n s₁) s₂.mem := by rw [he]; exact lay_arguments p₂
  have y₂ : Named (lay n s₁) (pushed (List.replicate 64 .eax) s₂) := by
    rw [he]; rfl
  exact ⟨(bodyFrom_ct (lay_ok p₁ sl) (lay_arguments p₁) ha₂ (hh (lay_ok p₁ sl) rfl (lay_arguments p₁) ha₂)
    _ _ _ _ _ _ ⟨push_ctx p₁, h₂, ⟨trivial, rfl⟩, ⟨trivial, y₂⟩⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.X86.SignCached

/-! ## The copy of the cached digest -/

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey

variable {L : Lay}

theorem seed64 (h64 : L.seedLen = 64) : L.SEED = ⟨L.seed.setWidth 64, 64⟩ := by
  rw [Lay.SEED, h64]

theorem seed64_mem (h64 : L.seedLen = 64) : (⟨L.seed.setWidth 64, 64⟩ : Region) ∈ L.inputs := by
  rw [← seed64 h64]; simp [Lay.inputs]

/-- The 64 bytes at the second argument, apart from the frame. -/
theorem seed64_disjoint (hL : L.Ok) (h64 : L.seedLen = 64) :
    Region.Disjoint ⟨L.seed.setWidth 64, 64⟩ ⟨L.E.setWidth 64 + BitVec.ofNat 64 192, 64⟩ := by
  have hk := (hL.ks _ (seed64_mem h64)).symm
  exact hk.sub_right fun p hp => Whole.frame_sub L.E p (Offset.sub_base _ (by decide) p hp)

/-- The second argument's slot, readable, holds the digest's address. -/
theorem copy_arg {g : Reg → BitVec 32} {m₀ : Mem} {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok)
    (ha : Arguments L m₀) :
    InRegions (t.rd ++ t.wr) (addr L.E 264) 4 ∧ t.mem.readW (addr L.E 264) 32 = L.seed := by
  rw [addr_eq (by have := hL.top; omega_using [this])]
  refine ⟨⟨L.ARGS, ?_, ?_⟩, (hc.arg_word hL (j := 1) (by decide)).trans (ha.1 1 (by decide))⟩
  · rw [hc.rd]; exact List.mem_append_left _ (by simp [Lay.inputs])
  · exact Offset.contains _ (e := 260) (k := 24) (by omega_using []) (by omega_using []) (by decide)

/-- `copyExpanded` leaves the caller's 64 bytes at the second argument at frame offset 192. -/
theorem copy_ok {g : Reg → BitVec 32} {m₀ : Mem} {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok)
    (ha : Arguments L m₀) (h64 : L.seedLen = 64) :
    WP isa copyExpanded t fun u => Ctx L g m₀ u ∧
      Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + 192) 64 = Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 64 := by
  obtain ⟨harg, hp⟩ := copy_arg hc hL ha
  refine WP.mono (Whole.copyExpanded_ok hc (by have := hL.top; omega_using [this]) harg hp
    (by have := hL.ns; omega_using [h64, this]) (by rw [hc.rd]; exact List.mem_append_left _ (seed64_mem h64))
    (seed64_disjoint hL h64)) fun u ⟨hu, hb⟩ => ⟨hu, hb.trans ?_⟩
  have hs := hc.input_bytes hL (r := L.SEED) (by simp [Lay.inputs]) (by change L.seedLen ≤ 2 ^ 64; omega_using [h64])
  rw [seed64 h64] at hs
  exact hs

theorem copy_nosp : NoSp copyExpanded := NoSp.of_all (by decide +kernel)

variable {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem copy_ct (hL : L.Ok) (h64 : L.seedLen = 64) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) copyExpanded (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have p : RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block copyPtr)
      (Two L g₁ g₂ m₁ m₂ fun u => u.gpr .ecx = L.seed) := by
    refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) (by native_taint_decide)) ?_ ?_
    · intro t hc _
      obtain ⟨harg, hp⟩ := copy_arg hc hL ha
      exact WP.mono (Whole.copyPtr_ok hc harg) fun _ ⟨hu, _, he⟩ => ⟨hu, he.trans hp⟩
    · intro t hc _
      obtain ⟨harg, hp⟩ := copy_arg hc hL hb
      exact WP.mono (Whole.copyPtr_ok hc harg) fun _ ⟨hu, _, he⟩ => ⟨hu, he.trans hp⟩
  have w : RelCT isa (Two L g₁ g₂ m₁ m₂ fun u => u.gpr .ecx = L.seed) (.block copyDigestWords)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
    refine two_wp (RelCT.taint (A := taint) (τr [.esp, .ecx]) (fun a b h => agree_regs fun r hr => ?_)
      (by native_taint_decide)) ?_ ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact two_esp h
      · exact h.2.2.1.trans h.2.2.2.symm
    · intro t hc he
      exact WP.mono (Whole.copyWords_ok hc (by have := hL.top; omega_using [this]) he (by have := hL.ns; omega_using [h64, this])
        (by rw [hc.rd]; exact List.mem_append_left _ (seed64_mem h64)) (seed64_disjoint hL h64))
        fun _ hu => ⟨hu.1, trivial⟩
    · intro t hc he
      exact WP.mono (Whole.copyWords_ok hc (by have := hL.top; omega_using [this]) he (by have := hL.ns; omega_using [h64, this])
        (by rw [hc.rd]; exact List.mem_append_left _ (seed64_mem h64)) (seed64_disjoint hL h64))
        fun _ hu => ⟨hu.1, trivial⟩
  exact p.seq w

end VG.Proof.Ed25519.X86.SignCached

end

end

/-! Merged from `Proof.Ed25519.X86.SignCached.Contract`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.X86.SignCached.Sat`. -/
section
/-! A seed and its public key, for the satisfiability witness below. -/
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86
open VG.Impl.Ed25519.X86 (combSym combConsts)

def satSeed : List Byte := Spec.Ed25519.bytesAt (fun _ => 0) 0x2000 32
def satKey : List Byte := Spec.Ed25519.publicKey satSeed

theorem satKey_length : satKey.length = 32 := by
  simp only [satKey, Spec.Ed25519.publicKey, Spec.Ed25519.encodePoint, Spec.Ed25519.encodeLE,
    List.length_map, List.length_range]

def satMem (a : Addr) : Byte :=
  if a.toNat < 0x3000 then 0 else if a.toNat < 0x3020 then satKey[a.toNat - 0x3000]?.getD 0
  else if a = 0x9005 then 0x10 else if a = 0x9009 then 0x20 else
    if a = 0x900d then 0x30 else if a = 0x9011 then 0x40 else if a = 0x9019 then 0x50 else 0

theorem sat_key : Spec.Ed25519.bytesAt satMem 0x3000 32 = satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satKey_length]
  · intro i hi hj
    have hi' : i < 32 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega_using [hi']
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, satMem, ha,
      show ¬ 0x3000 + i < 0x3000 from by omega_using [], ite_false, show 0x3000 + i < 0x3020 from by omega_using [hi'], ite_true, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

end VG.Proof.Ed25519.X86.SignCached
end
end

/-! ## Signing with the seed's cached digest -/

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached
open VG.Impl.Ed25519.X86 (combSym combConsts)
open VG.Proof.Ed25519 (sha512_length sign_of_sha512_eq)

/-- Some seed has the digest at the second argument and the public key at the third. -/
def keyE (s : State) : Prop := ∃ seed : List Byte, seed.length = 32 ∧
  Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64 = Spec.Sha512.sha512 seed ∧
  Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32 = Spec.Ed25519.publicKey seed

/-- The signature of every seed whose SHA-512 digest is at the second argument. -/
def postE (s t : State) : Prop := ∀ seed : List Byte, seed.length = 32 →
  Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64 = Spec.Sha512.sha512 seed →
  Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 64 =
    Spec.Ed25519.sign seed (Spec.Ed25519.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)

def signLocalE : Contract isa := signLocalWith 64 keyE postE

theorem signExpanded_ok {s : State} (h : signLocalE.pre s) :
    WP isa codeExpanded s fun t => abiPreserved s t ∧ signLocalE.post s t := by
  obtain ⟨seed, -, hE, hk⟩ := entry_key h
  have hL := lay_ok h (by decide)
  exact frame_ok h (by decide) copy_nosp
    (bodyFrom_ok hL (lay_arguments h)
      (WP.mono (copy_ok (push_ctx h) hL (lay_arguments h) rfl) fun _ ⟨hu, hb⟩ => ⟨hu, hb.trans hE⟩) hk rfl)
    fun _ ht _ _ hE' => ht.trans (sign_of_sha512_eq (hE.symm.trans hE') _)

theorem signExpanded_ct : ConstantTime isa signLocalE.pre signLocalE.pub codeExpanded :=
  frame_ct (by decide) fun hL h64 ha hb => copy_ct hL h64 ha hb

def signWideE : Contract isa := { signLocalE with
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, 64⟩
    let pk : Region := ⟨(arg s 2).setWidth 64, 32⟩
    let msg : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = [seed, pk, msg, TBL ((s.syms combSym).setWidth 64)] ∧ s.wr = [out, scr, args] ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint msg ∧ out.Disjoint args ∧
      out.Disjoint scr ∧ stk.Disjoint out ∧ ret.Disjoint out ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ msg.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint seed ∧ ret.Disjoint pk ∧ ret.Disjoint msg ∧ ret.Disjoint scr ∧
      stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 64 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 5).toNat + 8192 ≤ 2 ^ 32 ∧
      280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧ keyE s ∧
      CombHeld s [out, scr, stk, ret] }

theorem signWideE_pre (s : State) (h : signWideE.pre s) :
    signLocalE.pre (s.withRegions (signRd 64 s) (signWr s)) := by
  simp only [signLocalE, signLocalWith, signRd, signWr, keyE, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.withRegions_syms, CombHeld]
  exact ⟨True.intro, True.intro, h.2.2⟩

def satDigestE : List Byte := Spec.Sha512.sha512 satSeed

/-- `satMem`, with the seed's digest at `0x2000`. -/
def satMemE (a : Addr) : Byte :=
  if a.toNat < 0x2000 then 0 else if a.toNat < 0x2040 then satDigestE[a.toNat - 0x2000]?.getD 0
  else satMem a

def satStateE : State where
  gpr r := match r with | .esp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemWith satMemE
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 32⟩, ⟨0x4000, 0⟩, ⟨0x100000, 24576⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩, ⟨0x9004, 24⟩]
  syms _ := 0x100000

theorem satE_arg (j : Nat) (hj : j < 6) : arg satStateE j = Mem.readW satMemE (argAddr satStateE j) 32 := by
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change satMemWith satMemE _ = _
  rw [satMemWith_out]
  have : ∀ j < 6, ∀ b < 4, 8 * 32 * 96 ≤ (argAddr satStateE j + BitVec.ofNat 64 b - 0x100000).toNat := by
    decide
  exact this j hj b (by omega_using [hb])

theorem satE_digest : Spec.Ed25519.bytesAt (satMemWith satMemE) 0x2000 64 = satDigestE := by
  have out : ∀ i < 64, 8 * 32 * 96 ≤ ((0x2000 : Addr) + BitVec.ofNat 64 i - 0x100000).toNat := by
    decide
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satDigestE, sha512_length]
  · intro i hi hj
    have hi' : i < 64 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
      change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
      omega_using [hi']
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range]
    rw [satMemWith_out _ (out i hi')]
    unfold satMemE
    simp only [ha, show ¬ 0x2000 + i < 0x2000 from by omega_using [], ite_false,
      show 0x2000 + i < 0x2040 from by omega_using [hi'], ite_true, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

theorem satE_key : Spec.Ed25519.bytesAt (satMemWith satMemE) 0x3000 32 = Spec.Ed25519.publicKey satSeed := by
  have out : ∀ i < 32, 8 * 32 * 96 ≤ ((0x3000 : Addr) + BitVec.ofNat 64 i - 0x100000).toNat := by
    decide
  change _ = satKey
  rw [← sat_key]
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
    change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
    omega_using [hi']
  rw [satMemWith_out _ (out i hi')]
  unfold satMemE
  simp only [ha, show ¬ 0x3000 + i < 0x2000 from by omega_using [], ite_false,
    show ¬ 0x3000 + i < 0x2040 from by omega_using []]

theorem satE : (Spec.Ed25519.signExpandedContract (X86.abi.withConsts combConsts) 280).pre satStateE := by
  have hl := combWords_length
  have a0 : arg satStateE 0 = 0x1000 := (satE_arg 0 (by decide)).trans (by decide)
  have a1 : arg satStateE 1 = 0x2000 := (satE_arg 1 (by decide)).trans (by decide)
  have a2 : arg satStateE 2 = 0x3000 := (satE_arg 2 (by decide)).trans (by decide)
  have a3 : arg satStateE 3 = 0x4000 := (satE_arg 3 (by decide)).trans (by decide)
  have a4 : arg satStateE 4 = 0 := (satE_arg 4 (by decide)).trans (by decide)
  have a5 : arg satStateE 5 = 0x5000 := (satE_arg 5 (by decide)).trans (by decide)
  have held : TblWords ((satStateE.syms combSym).setWidth 64) satStateE.mem := satMemWith_held satMemE
  have key : ∃ seed : List Byte, seed.length = 32 ∧
      Spec.Ed25519.bytesAt satStateE.mem ((0x2000 : BitVec 32).setWidth 64) 64 = Spec.Sha512.sha512 seed ∧
      Spec.Ed25519.bytesAt satStateE.mem ((0x3000 : BitVec 32).setWidth 64) 32 = Spec.Ed25519.publicKey seed :=
    ⟨satSeed, by simp only [satSeed, Spec.Ed25519.bytesAt, List.length_map, List.length_range],
      satE_digest, satE_key⟩
  generalize e : satStateE = s
  sig_pre [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig,
    Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  refine ⟨by decide, by decide, by rw [hl]; rfl, held, by rw [hl]; decide, ?_, ?_, ?_, by decide, ?_⟩
  · rw [hl]
    intro r hr
    change r ∈ [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩, ⟨0x9004, 24⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · rw [hl]; exact Region.disjoint_of_sep (by decide)
  · rw [hl]; exact Region.disjoint_of_sep (by decide)
  · rw [a0, a1, a2, a3, a4, a5]
    refine ⟨rfl, rfl, ?_⟩
    repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | exact key | decide

theorem signWideE_implies :
    signWideE.Implies (Spec.Ed25519.signExpandedContract (X86.abi.withConsts combConsts) 280) where
  pre s h := by
    sig_pre [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨h280, hsp, hd, held, hfit, hdw, tret, tstk, -, ht, hw, os, op, om, oc, oa, sc, -, pc, -,
      mc, -, ca, ro, rs, rp, rm, rc, -, ko, ks, kp, km, kc, -, f0, f1, f2, f3, f5, hk⟩ := h
    refine ⟨?_, hw, os, op, om, oa, oc, ko, ro, sc, pc, mc, ca.symm, rs, rp, rm, rc, ks, kp, km, kc,
      f0, f1, f2, f3, f5, h280, by omega_using [hsp], hk, held, hfit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact tstk
      · exact tret
  post := by
    intro s t _ h
    sig_post [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts]
    exact h
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2, h3, h4, h5⟩ := h
    exact ⟨hsp, h0, h1, h2, h3, h4, h5, hsy⟩
  sat := ⟨satStateE, satE⟩

end VG.Proof.Ed25519.X86.SignCached

namespace VG.Impl.Ed25519.X86.SignCached
materialize_code codeExpanded
end VG.Impl.Ed25519.X86.SignCached

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached
open VG.Impl.Ed25519.X86 (combConsts)

theorem signExpanded_verified :
    Verified X86.target codeExpanded
      (Spec.Ed25519.signExpandedContract (X86.abi.withConsts combConsts) 280) := by
  have hsat := signWideE_implies.sat_left
  have satLocal : ∃ s, signLocalE.pre s := hsat.elim fun s h => ⟨_, signWideE_pre s h⟩
  have verifiedLocal : Verified X86.target codeExpanded signLocalE :=
    Verified.of_correct (fun _ h => signExpanded_ok h) signExpanded_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal (signRd 64) signWr signWideE_pre
    ?_ ?_ ?_ ?_ hsat) signWideE_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [signRd, signWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl) <;> simp
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [signWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [signWideE, signLocalE, signLocalWith, postE, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [signWideE, signLocalE, signLocalWith, signPub, arg_withRegions, State.withRegions_gpr,
      State.withRegions_syms] using h

end VG.Proof.Ed25519.X86.SignCached
