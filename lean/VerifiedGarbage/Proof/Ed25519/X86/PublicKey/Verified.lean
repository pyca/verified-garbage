module

public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe
import VerifiedGarbage.Proof.Ed25519.X86.Whole.CopyDigest
import VerifiedGarbage.Proof.Sha512.X86.Stream.Finalize
import VerifiedGarbage.Proof.Ed25519.X86.Whole.BlocksCT
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified
import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.CopyDigest
meta import VerifiedGarbage.Proof.Sha512.X86.Stream.Finalize
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.BlocksCT
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified
meta import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.Expanded
meta import VerifiedGarbage.Proof.Ed25519.Contract
meta import VerifiedGarbage.Proof.Ed25519.Expanded
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Ed25519.X86.Whole.Layout
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Proof.Ed25519.X86.CombTbl
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.AddrArith -- shake: keep
public import VerifiedGarbage.Proof.Ed25519.X86.Whole.Setup
public import VerifiedGarbage.Impl.Ed25519.X86.PublicKey
import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Prune
public import VerifiedGarbage.Proof.Ed25519.X86.Whole.HashPre
public import VerifiedGarbage.Proof.Ed25519.X86.Whole.CallCT
public import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Proof.Framework.X86.CallWith
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Ed25519.X86.CombLit
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha512.X86.Lit
-- Proofs inside exposed definitions (structure values) use these: Lean needs them public.
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.RelClasses
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.Layout
meta import VerifiedGarbage.Spec.Ed25519.Contract
meta import VerifiedGarbage.Proof.Ed25519.X86.CombTbl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.Setup
meta import VerifiedGarbage.Impl.Ed25519.X86.PublicKey
meta import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Prune
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.HashPre
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.CallCT
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Sha512.Stream
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import Mathlib.Tactic.NormNum.Prime
meta import Mathlib.Data.Nat.Totient
meta import Mathlib.Tactic.Positivity.Finset
meta import Mathlib.Algebra.Order.Field.Basic
meta import Mathlib.Tactic.NormNum.GCD
meta import Mathlib.Data.Sym.Sym2.Init
meta import Mathlib.Tactic.ContinuousFunctionalCalculus
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Tactic.Push
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Ed25519.X86.CombLit
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha512.X86.Lit
meta import Mathlib.Data.Nat.Basic
meta import Mathlib.Order.RelClasses

/-! ### `Ed25519.X86.PublicKey.CTReady`, which only this module used -/

section

/-! ### `Ed25519.X86.PublicKey.Layout`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86
open VG.Impl.Ed25519.X86 (combSym)

/-- The seed, the arguments and the comb's tables (the static `combSym`, which
`vg_ed25519_scalar_base` reads). -/
def pkRd (n : Nat) (s : State) : List Region :=
  [⟨(arg s 1).setWidth 64, n⟩, ⟨argAddr s 0, 12⟩, TBL ((s.syms combSym).setWidth 64)]
def pkWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 32⟩, ⟨(arg s 2).setWidth 64, 8192⟩]

/-- What the two runs of a derivation share: the stack pointer, the arguments and the
comb's tables. -/
def pkPub (s t : State) : Prop :=
  s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2 ∧
    s.syms combSym = t.syms combSym

/-- Public-key derivation from the `n` bytes at the second argument (the seed's SHA-512
digest, 64), with the postcondition `post`. -/
def pkLocalWith (n : Nat) (post : State → State → Prop) : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, n⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := below (s.gpr .esp) 280
    s.rd = pkRd n s ∧ s.wr = pkWr s ∧ out.Disjoint seed ∧ out.Disjoint scratch ∧
      seed.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ stack.Disjoint out ∧
      stack.Disjoint seed ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + n ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 ∧ CombHeld s [out, scratch, stack]
  post := post
  pub := pkPub

variable {n : Nat}

abbrev esp (s : State) : BitVec 32 := s.gpr .esp - BitVec.ofNat 32 256
abbrev Ctx (n : Nat) (s t : State) : Prop := Whole.Ctx (esp s) s.gpr s.mem (pkRd n s) (pkWr s) t

structure Bounds (n : Nat) (s : State) : Prop where
  out : (arg s 0).toNat + 32 ≤ 2 ^ 32
  seed : (arg s 1).toNat + n ≤ 2 ^ 32
  scratch : (arg s 2).toNat + 8192 ≤ 2 ^ 32
  below : 280 ≤ (s.gpr .esp).toNat
  above : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32

theorem bounds {post : State → State → Prop} {s : State} (h : (pkLocalWith n post).pre s) : Bounds n s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, a, b, c, d, e, _⟩ := h
  exact ⟨a, b, c, d, e⟩

theorem Bounds.frame {s : State} (h : Bounds n s) : (esp s).toNat + 272 ≤ 2 ^ 32 := by
  rw [sub_toNat (by have := h.below; omega_using [this])]
  have := h.above
  omega_using [this]

theorem Bounds.call {s : State} (h : Bounds n s) : 24 ≤ (esp s).toNat := by
  rw [sub_toNat (by have := h.below; omega_using [this])]
  have := h.below
  omega_using [this]

theorem stack_eq {s : State} (h : Bounds n s) : Whole.STK (esp s) = below (s.gpr .esp) 280 := by
  simp only [Whole.STK, below, esp]
  rw [Taint.sub_setWidth (by have := h.below; omega_using [this] : 256 ≤ (s.gpr .esp).toNat),
    Taint.sub_setWidth h.below, BitVec.sub_sub]
  rfl

/-- Pushing the caller-saved EAX allocates locals without changing callee-saved registers. -/
theorem push_ctx {post : State → State → Prop} {s : State} (h : (pkLocalWith n post).pre s) :
    Ctx n s (pushed (List.replicate 64 .eax) s) := by
  have hb := bounds h
  have hf := pushed_frame (s := s) (rs := List.replicate 64 .eax) (by simp)
    (by simp only [List.length_replicate]; have := hb.below; omega_using [this])
  refine ⟨(pushed_rd _ _).trans h.1, ?_, ?_, fun r _ hn => pushed_gpr _ _ hn, ?_⟩
  · rw [pushed_wr, h.2.1]
    simp only [List.length_replicate]
  · rw [pushed_esp, List.length_replicate]
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨Whole.STK (esp s), List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    rw [stack_eq hb]
    exact below_sub (by simp) hb.below

abbrev OUT (s : State) : Region := ⟨(arg s 0).setWidth 64, 32⟩
abbrev SEED (n : Nat) (s : State) : Region := ⟨(arg s 1).setWidth 64, n⟩
abbrev SCR (s : State) : Region := ⟨(arg s 2).setWidth 64, 8192⟩
abbrev ARGS (s : State) : Region := ⟨argAddr s 0, 12⟩
abbrev RET (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩

structure Facts (n : Nat) (s : State) : Prop extends Bounds n s where
  os : (OUT s).Disjoint (SEED n s)
  oc : (OUT s).Disjoint (SCR s)
  sc : (SEED n s).Disjoint (SCR s)
  ao : (ARGS s).Disjoint (OUT s)
  ac : (ARGS s).Disjoint (SCR s)
  ro : (RET s).Disjoint (OUT s)
  rc : (RET s).Disjoint (SCR s)
  ko : (Whole.STK (esp s)).Disjoint (OUT s)
  ks : (Whole.STK (esp s)).Disjoint (SEED n s)
  kc : (Whole.STK (esp s)).Disjoint (SCR s)
  held : CombHeld s [OUT s, SCR s, Whole.STK (esp s)]

theorem facts {post : State → State → Prop} {s : State} (h : (pkLocalWith n post).pre s) : Facts n s := by
  have hb := bounds h
  obtain ⟨_, _, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, _, _, _, _, _, held⟩ := h
  exact ⟨hb, os, oc, sc, ao, ac, ro, rc, stack_eq hb ▸ ko, stack_eq hb ▸ ks, stack_eq hb ▸ kc,
    stack_eq hb ▸ held⟩

theorem arg_address (s : State) (j : Nat) : addr (esp s) (260 + 4 * j) = argAddr s j := by
  simp only [addr, esp, argAddr]
  rw [show 260 + 4 * j = 256 + (4 + 4 * j) by omega_using [], BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem arg_address64 {s : State} (h : Bounds n s) {j : Nat} (hj : j < 3) :
    argAddr s j = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * j) :=
  addr_eq (by have := h.above; omega_using [hj, this])

theorem args_stack {s : State} (h : Bounds n s) : (ARGS s).Disjoint (Whole.STK (esp s)) := by
  rw [stack_eq h]
  change Region.Disjoint ⟨argAddr s 0, 12⟩ ⟨((s.gpr .esp) - BitVec.ofNat 32 280).setWidth 64, 280⟩
  rw [arg_address64 h (by decide), Taint.sub_setWidth h.below]
  exact (Offset.disjoint_below_above _ (m := 280) (a := 4) (l := 12) (by decide)).symm

theorem args_contains {s : State} (h : Bounds n s) {j : Nat} (hj : j < 3) :
    (ARGS s).Contains (argAddr s j) 4 := by
  change (⟨argAddr s 0, 12⟩ : Region).Contains _ _
  rw [arg_address64 h (by decide), arg_address64 h hj]
  exact Offset.contains _ (by omega_using []) (by omega_using [hj]) (by decide)

theorem original_arg {s t : State} (h : Facts n s) (hc : Ctx n s t) {j : Nat} (hj : j < 3) :
    t.mem.readW (addr (esp s) (260 + 4 * j)) 32 = arg s j := by
  rw [arg_address]
  exact hc.frame.readW (args_contains h.toBounds hj) (by
    simp only [pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact h.ao
    · exact h.ac
    · exact args_stack h.toBounds) (by decide)

theorem original_arg_readable {s t : State} (h : Facts n s) (hc : Ctx n s t) {j : Nat} (hj : j < 3) :
    InRegions (t.rd ++ t.wr) (addr (esp s) (260 + 4 * j)) 4 := by
  rw [arg_address, hc.rd]
  exact ⟨ARGS s, List.mem_append_left _ (by simp [pkRd]), args_contains h.toBounds hj⟩

end VG.Proof.Ed25519.X86.PublicKey

end

end


/-! Merged from `Proof.Ed25519.X86.PublicKey.Setup`. -/

@[expose] public section

section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86
open VG.Impl.Ed25519.X86.Whole (Value setup)
variable {n : Nat}

def argValue (s : State) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => esp s + BitVec.ofNat 32 d
  | .caller i d => arg s i + BitVec.ofNat 32 d

theorem setup_ok {s t : State} (h : Facts n s) (hc : Ctx n s t) {vs : List Value}
    (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 3 v) :
    WP isa (.block (setup 0 vs)) t fun u => Ctx n s u ∧
      Frame [⟨(esp s).setWidth 64, 24⟩] t.mem u.mem ∧
      ∀ j (hj : j < vs.length), Whole.slots (esp s) u j = argValue s (vs[j]'hj) := by
  refine WP.mono (Whole.Ctx.setup hc (n := 3) (by have := h.toBounds.frame; omega_using [this])
    (fun j hj => original_arg_readable h hc hj) (by omega_using [hn]) hv) fun u ⟨hu, hf, hs⟩ => ⟨hu, hf, ?_⟩
  intro j hj
  have e := hs j hj
  simp only [Nat.zero_add] at e
  rw [addr_eq (by have := h.toBounds.frame; omega_using [hn, hj, this])] at e
  rw [Whole.slots, e]
  generalize he : vs[j]'hj = v
  have vv := hv (vs[j]'hj) (List.getElem_mem hj)
  rw [he] at vv
  cases v with
  | const n => rfl
  | frame d => rfl
  | caller i d =>
    exact congrArg (· + BitVec.ofNat 32 d) (original_arg h hc vv)

end VG.Proof.Ed25519.X86.PublicKey
end

/-! Merged from `Proof.Ed25519.X86.PublicKey.Base`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86
open VG.Impl.Ed25519.X86 (scalarBase)
variable {n : Nat}

def scalarPtr (s : State) : BitVec 32 := esp s + BitVec.ofNat 32 32

theorem scalarPtr_addr {s : State} (h : Bounds n s) :
    (scalarPtr s).setWidth 64 = (esp s).setWidth 64 + BitVec.ofNat 64 32 :=
  addr_eq (by have := h.frame; omega_using [this])

theorem base_nosp : NoSp scalarBase := NoSp.of_all (by lit_decide)
theorem base_stack : stackUse scalarBase = 8 := by lit_decide

def BaseArgs (s t : State) : Prop :=
  Whole.slots (esp s) t 0 = arg s 0 ∧ Whole.slots (esp s) t 1 = scalarPtr s ∧
    Whole.slots (esp s) t 2 = arg s 2

def baseRd (s : State) : List Region :=
  [⟨(scalarPtr s).setWidth 64, 32⟩, ⟨(esp s).setWidth 64, 12⟩,
    TBL ((s.syms Impl.Ed25519.X86.combSym).setWidth 64)]

/-- The three cdecl argument slots of the base-point multiplication. -/
theorem base_args {s t : State} (h : Facts n s) (hc : Ctx n s t) (ha : BaseArgs s t) :
    arg t.callEntry 0 = arg s 0 ∧ arg t.callEntry 1 = scalarPtr s ∧ arg t.callEntry 2 = arg s 2 := by
  have e : ∀ j < 64, arg t.callEntry j = Whole.slots (esp s) t j :=
    fun j hj => Whole.call_arg hc.esp h.toBounds.call (by have := h.toBounds.frame; omega_using [this]) hj
  exact ⟨(e 0 (by decide)).trans ha.1, (e 1 (by decide)).trans ha.2.1,
    (e 2 (by decide)).trans ha.2.2⟩

theorem base_pre {s t : State} (h : Facts n s) (hc : Ctx n s t) (ha : BaseArgs s t)
    (hy : t.syms = s.syms) :
    scalarBaseLocal.pre (t.callEntry.withRegions (baseRd s) (pkWr s)) := by
  obtain ⟨a0, a1, a2⟩ := base_args h hc ha
  have ae : argAddr t.callEntry 0 = (esp s).setWidth 64 := by
    rw [argAddr_callEntry, hc.esp]
    simp
  have fe := h.toBounds.frame
  have be := h.toBounds.call
  have ret : Region.Sub ⟨(esp s - 4).setWidth 64, 4⟩ (Whole.STK (esp s)) :=
    Whole.below_sub_stack be (by decide)
  have args : Region.Sub ⟨(esp s).setWidth 64, 12⟩ (Whole.STK (esp s)) :=
    fun p hp => Whole.frame_sub (esp s) p (Region.sub_prefix (by decide) p hp)
  have scalar : Region.Sub ⟨(scalarPtr s).setWidth 64, 32⟩ (Whole.STK (esp s)) := by
    rw [scalarPtr_addr h.toBounds]
    exact fun p hp => Whole.frame_sub (esp s) p (Offset.sub_base _ (by decide : 32 + 32 ≤ 256) p hp)
  have stk : Region.Sub (below (esp s - BitVec.ofNat 32 4) 8) (Whole.STK (esp s)) :=
    Whole.inner_sub_stack be
  have hf : (esp s).toNat + 256 ≤ 2 ^ 32 := by omega_using [fe]
  have tw : TblWords ((s.syms Impl.Ed25519.X86.combSym).setWidth 64) t.callEntry.mem := by
    refine (h.held.1.frame hc.frame fun r hr => ?_).frame (Whole.callEntry_frame t) fun r hr => ?_
    · simp only [pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact h.held.2.2 _ (by simp)
    · rw [List.mem_singleton.mp hr, hc.esp]
      exact (h.held.2.2 _ (by simp)).sub_right (Whole.below_sub_stack be (by decide))
  have cy : (t.callEntry.withRegions (baseRd s) (pkWr s)).syms = s.syms := hy
  have cs : callStk (t.callEntry.withRegions (baseRd s) (pkWr s)) = below (esp s - BitVec.ofNat 32 4) 8 := by
    simp only [callStk, State.withRegions_gpr, State.callEntry_esp, hc.esp]; rfl
  simp only [scalarBaseLocal, BaseRegions, CombHeld, cy, cs, State.withRegions_rd, State.withRegions_wr,
    arg_withRegions, argAddr_withRegions, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_esp, hc.esp, a0, a1, a2, ae]
  refine ⟨⟨rfl, rfl, h.oc, h.kc.sub_left scalar, h.ko.sub_left args, h.kc.sub_left args,
    h.ko.sub_left ret, h.kc.sub_left ret, h.out, ?_, h.scratch, ?_, ?_,
    Whole.inner_frame be hf (d := 32) (n := 32) (by decide) (by decide), h.kc.sub_left stk,
    h.ko.sub_left stk⟩,
    h.ko.sub_left stk, tw, h.held.2.1, ?_⟩
  · change (esp s + BitVec.ofNat 32 32).toNat + 32 ≤ 2 ^ 32
    rw [BitVec.toNat_add, show (BitVec.ofNat 32 32).toNat = 32 from rfl, Nat.mod_eq_of_lt (by omega_using [fe])]
    omega_using [fe]
  · change (esp s - BitVec.ofNat 32 4).toNat + 16 ≤ 2 ^ 32
    rw [sub_toNat (by omega_using [be] : 4 ≤ (esp s).toNat)]
    omega_using [fe]
  · change 8 ≤ (esp s - BitVec.ofNat 32 4).toNat
    rw [sub_toNat (by omega_using [be] : 4 ≤ (esp s).toNat)]
    omega_using [be]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact h.held.2.2 _ (by simp)
    · exact h.held.2.2 _ (by simp)
    · exact (h.held.2.2 _ (by simp)).sub_right stk

theorem base_call {s t : State} (h : Facts n s) (hc : Ctx n s t) (ha : BaseArgs s t)
    (hy : t.syms = s.syms) :
    WP isa (.call "vg_ed25519_scalar_base" scalarBase) t fun u => Ctx n s u ∧
      Spec.Ed25519.bytesAt u.mem ((arg s 0).setWidth 64) 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem ((scalarPtr s).setWidth 64) 32) := by
  have scalarWithin : Whole.Within ⟨(scalarPtr s).setWidth 64, 32⟩ (Whole.FR (esp s)) :=
    ⟨32, scalarPtr_addr h.toBounds, by change 32 + 32 ≤ 256; decide⟩
  have cov : Covers (baseRd s ++ pkWr s) (pkRd n s ++ Whole.FR (esp s) :: pkWr s) := by
    refine Covers.of_sub ?_
    simp only [baseRd, pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨Whole.FR (esp s), by simp, scalarWithin⟩
    · exact ⟨Whole.FR (esp s), by simp, 0, by simp, by change 0 + 12 ≤ 256; decide⟩
    · exact ⟨TBL ((s.syms Impl.Ed25519.X86.combSym).setWidth 64), by simp [pkRd], 0, by simp, by simp⟩
    · exact ⟨OUT s, by simp, 0, by simp, by change 0 + 32 ≤ 32; decide⟩
    · exact ⟨SCR s, by simp, 0, by simp, by change 0 + 8192 ≤ 8192; decide⟩
  have ws : ∀ r ∈ pkWr s, Whole.Within r (Whole.FR (esp s)) ∨ ∃ R ∈ pkWr s, Whole.Within r R :=
    fun r hr => .inr ⟨r, hr, 0, by simp, by simp⟩
  with_reducible
    refine Whole.call_ok hc h.toBounds.call scalarBase_ok base_nosp (by rw [base_stack]; decide)
      (base_pre h hc ha hy) cov ws fun u hu _ _ post => ⟨hu, ?_⟩
  obtain ⟨s₂, hm, hg, hp⟩ := post
  obtain ⟨a0, a1, _⟩ := base_args h hc ha
  change Spec.Ed25519.bytesAt s₂.mem ((arg t.callEntry 0).setWidth 64) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.callEntry.mem ((arg t.callEntry 1).setWidth 64) 32) at hp
  rw [hm, a0, a1] at hp
  rw [hp]
  refine congrArg Spec.Ed25519.scalarBase ?_
  refine Whole.callEntry_bytes (r := ⟨(scalarPtr s).setWidth 64, 32⟩) ?_ (by change 32 ≤ 2 ^ 64; decide)
  rw [hc.esp, scalarPtr_addr h.toBounds]
  change Region.Disjoint ⟨(esp s).setWidth 64 + BitVec.ofNat 64 32, 32⟩
    ⟨(esp s - BitVec.ofNat 32 4).setWidth 64, 4⟩
  have e : (esp s - BitVec.ofNat 32 4).setWidth 64 = (esp s).setWidth 64 - BitVec.ofNat 64 4 :=
    Taint.sub_setWidth (m := 4) (by have := h.toBounds.call; omega_using [this])
  rw [e]
  exact (Offset.disjoint_below_above _ (m := 4) (a := 32) (l := 32) (by decide)).symm

end VG.Proof.Ed25519.X86.PublicKey
end

/-! Merged from `Proof.Ed25519.X86.PublicKey.Hash`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey
variable {n : Nat}

theorem seed_same {s t : State} (h : Facts n s) (hc : Ctx n s t) :
    Spec.Ed25519.bytesAt t.mem ((arg s 1).setWidth 64) n =
      Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) n := by
  apply List.map_congr_left
  intro i hi
  exact hc.frame.bytes (R := SEED n s) (by
    simp only [pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact h.os.symm
    · exact h.sc
    · exact h.ks.symm) (by have := h.seed; change n ≤ 2 ^ 64; omega_using [this]) (List.mem_range.mp hi)

end VG.Proof.Ed25519.X86.PublicKey
end

/-! Merged from `Proof.Ed25519.X86.PublicKey.Correct`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey
variable {n : Nat}

theorem prune_step {s t : State} (h : Facts n s) (hc : Ctx n s t) {digest : List Byte}
    (hh : Spec.Sha512.bytesAt t.mem ((esp s).setWidth 64 + 192) 64 = digest) :
    WP isa (.block prune) t fun u => Ctx n s u ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem ((scalarPtr s).setWidth 64) 32) =
        Spec.Ed25519.prune digest := by
  refine WP.mono (prune_ok hc.esp (by have := h.toBounds.frame; omega_using [this])
    (by rw [hc.wr]; exact List.mem_cons_self) hh) fun u ⟨ku, hf, hs⟩ => ⟨?_, ?_⟩
  · refine hc.of_frame ku.rd ku.wr ku.esp ?_ hf ?_
    · intro r hr _
      apply ku.regs
      rintro rfl
      simp [calleeSaved] at hr
    · rintro r hr
      rw [List.mem_singleton.mp hr]
      exact .inl (Offset.sub_base _ (by decide))
  · rw [scalarPtr_addr h.toBounds]
    exact hs

theorem base_step {s t : State} (h : Facts n s) (hc : Ctx n s t) (hy : t.syms = s.syms) {k : Nat}
    (hn : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem ((scalarPtr s).setWidth 64) 32) = k) :
    WP isa (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase) t
      fun u => Ctx n s u ∧ Spec.Ed25519.bytesAt u.mem ((arg s 0).setWidth 64) 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul k Spec.Ed25519.basePoint) := by
  refine WP.seq (WP.mono_syms (setup_ok h hc (vs := [.caller 0 0, .frame 32, .caller 2 0])
    (by decide) (Whole.valid_all (by decide))) fun u ⟨hu, hf, hs⟩ yu => ?_)
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  simp only [argValue, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2
  have he : Spec.Ed25519.bytesAt u.mem ((scalarPtr s).setWidth 64) 32 =
      Spec.Ed25519.bytesAt t.mem ((scalarPtr s).setWidth 64) 32 := by
    apply List.map_congr_left
    intro i hi
    exact hf.bytes (R := ⟨(scalarPtr s).setWidth 64, 32⟩) (by
      rintro r hr; rw [List.mem_singleton.mp hr, scalarPtr_addr h.toBounds]
      exact Offset.disjoint_base _ (by decide) (by decide)) (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  refine WP.mono (base_call h hu ⟨a0, a1, a2⟩ (yu.trans hy)) fun v ⟨hv, ho⟩ => ⟨hv, ?_⟩
  rw [ho, he, Spec.Ed25519.scalarBase, hn]

/-- The public key of the digest that `first` leaves at frame offset 192, in `out`. -/
theorem bodyFrom_ok {s t : State} (h : Facts n s) (hy : t.syms = s.syms)
    {first : Prog isa} {digest : List Byte}
    (hh : WP isa first t fun u => Ctx n s u ∧
      Spec.Sha512.bytesAt u.mem ((esp s).setWidth 64 + 192) 64 = digest) :
    WP isa (bodyFrom first) t fun u => Ctx n s u ∧ Spec.Ed25519.bytesAt u.mem ((arg s 0).setWidth 64) 32 =
      Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul (Spec.Ed25519.prune digest) Spec.Ed25519.basePoint) := by
  refine WP.seq (WP.mono_syms hh fun t₁ ⟨hc₁, hh⟩ y₁ => ?_)
  refine WP.seq (WP.mono_syms (prune_step h hc₁ hh) fun t₂ ⟨hc₂, hn⟩ y₂ => ?_)
  refine WP.seq (WP.mono (base_step h hc₂ (y₂.trans (y₁.trans hy)) hn) fun t₃ ⟨hc₃, ho⟩ => ?_)
  refine WP.mono (Whole.Ctx.zeroWords hc₃ (start := 8) (count := 56)
    (by have := h.toBounds.frame; omega_using [this]) (by decide)) fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  have he : Spec.Ed25519.bytesAt u.mem ((arg s 0).setWidth 64) 32 =
      Spec.Ed25519.bytesAt t₃.mem ((arg s 0).setWidth 64) 32 := by
    apply List.map_congr_left
    intro i hi
    exact hf.bytes (R := OUT s) (by
      rintro r hr; rw [List.mem_singleton.mp hr]
      exact (h.ko.sub_left (fun p hp => Whole.frame_sub (esp s) p
        (Offset.sub_base _ (by decide : 4 * 8 + 4 * 56 ≤ 256) p hp))).symm)
      (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rw [he, ho]

private theorem noSp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact ha i hi
  · exact hb i hi

theorem bodyFrom_nosp {first : Prog isa} (hf : NoSp first) : NoSp (bodyFrom first) := by
  have nb : NoSp (.block baseArgs) := NoSp.of_all (by decide +kernel)
  have np : NoSp (.block prune) := NoSp.of_all (by decide +kernel)
  have nw : NoSp (.block wipe) := NoSp.of_all (by decide +kernel)
  exact noSp_seq hf (noSp_seq np (noSp_seq (noSp_seq nb base_nosp) nw))

/-- The frame around `bodyFrom first`, from the public key it leaves in `out`. -/
theorem frame_ok {post : State → State → Prop} {first : Prog isa} {s : State}
    (h : (pkLocalWith n post).pre s) (hn : NoSp first) {key : List Byte}
    (hb : WP isa (bodyFrom first) (pushed (List.replicate 64 .eax) s) fun u => Ctx n s u ∧
      Spec.Ed25519.bytesAt u.mem ((arg s 0).setWidth 64) 32 = key)
    (hp : ∀ t, Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 = key → post s t) :
    WP isa (.frame (.push (List.replicate 64 .eax)) (bodyFrom first) (.pop .eax 64)) s
      fun t => abiPreserved s t ∧ post s t := by
  have hf := facts h
  refine WP.frame (rs := List.replicate 64 .eax) (by simp) (by simp) (by decide)
    (by simp only [List.length_replicate]; have := hf.below; omega_using [this]) (bodyFrom_nosp hn)
    (WP.mono hb fun u ⟨hu, ho⟩ m v fl => ?_)
  simp only [List.length_replicate] at fl
  obtain hb256 : 256 ≤ (s.gpr .esp).toNat := by have := hf.below; omega_using [this]
  refine ⟨⟨fun r hr => ?_, ?_⟩, hp _ ?_⟩
  · show (popped .eax (List.replicate 64 Reg.eax).length u).gpr r = s.gpr r
    by_cases he : r = .esp
    · subst r
      rw [popped_esp, hu.esp, List.length_replicate]
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ he (by intro e; subst r; simp [calleeSaved] at hr), hu.cs r hr he]
  · show m.readW _ 32 = _
    rw [fl.readW (r := RET s) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      change Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩
        ⟨(s.gpr .esp - BitVec.ofNat 32 256).setWidth 64, 256⟩
      rw [Taint.sub_setWidth hb256]
      exact (Offset.below_disjoint _ (by decide)).symm) (by decide)]
    refine hu.frame.readW (r := RET s) (Region.contains_self _ _) ?_ (by decide)
    simp only [pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hf.ro
    · exact hf.rc
    · rw [stack_eq hf.toBounds]
      change Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩
        ⟨(s.gpr .esp - BitVec.ofNat 32 280).setWidth 64, 280⟩
      rw [Taint.sub_setWidth hf.below]
      exact (Offset.below_disjoint _ (by decide)).symm
  · show Spec.Ed25519.bytesAt m _ 32 = key
    refine Eq.trans (List.map_congr_left fun _ hi => fl.bytes (R := OUT s) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ((stack_eq hf.toBounds ▸ hf.ko).sub_left (below_sub (by decide) hf.below)).symm)
      (by show 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)) ?_
    exact ho

end VG.Proof.Ed25519.X86.PublicKey
end

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey
open VG.Impl.Ed25519.X86.Whole (Value)
variable {n : Nat}

def Slots (vs : List Value) (s t : State) : Prop :=
  ∀ j (hj : j < vs.length), Whole.slots (esp s) t j = argValue s (vs[j]'hj)

def baseValues : List Value := [.caller 0 0, .frame 32, .caller 2 0]

def base_ready {s t : State} (h : Facts n s) (hc : Ctx n s t) (hy : t.syms = s.syms)
    (hs : Slots baseValues s t) :
    Whole.CallReady scalarBaseLocal (esp s) (pkRd n s) (pkWr s) t := by
  unfold Slots baseValues at hs
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  simp only [argValue, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2
  have ha : BaseArgs s t := ⟨a0, a1, a2⟩
  have scalarWithin : Whole.Within ⟨(scalarPtr s).setWidth 64, 32⟩ (Whole.FR (esp s)) :=
    ⟨32, scalarPtr_addr h.toBounds, by change 32 + 32 ≤ 256; decide⟩
  have cov : Covers (baseRd s ++ pkWr s) (pkRd n s ++ Whole.FR (esp s) :: pkWr s) := by
    refine Covers.of_sub ?_
    simp only [baseRd, pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨Whole.FR (esp s), by simp, scalarWithin⟩
    · exact ⟨Whole.FR (esp s), by simp, 0, by simp, by change 0 + 12 ≤ 256; decide⟩
    · exact ⟨TBL ((s.syms Impl.Ed25519.X86.combSym).setWidth 64), by simp [pkRd], 0, by simp, by simp⟩
    · exact ⟨OUT s, by simp, 0, by simp, by change 0 + 32 ≤ 32; decide⟩
    · exact ⟨SCR s, by simp, 0, by simp, by change 0 + 8192 ≤ 8192; decide⟩
  have ws : ∀ r ∈ pkWr s, Whole.Within r (Whole.FR (esp s)) ∨ ∃ R ∈ pkWr s, Whole.Within r R :=
    fun r hr => .inr ⟨r, hr, 0, by simp, by simp⟩
  exact ⟨baseRd s, pkWr s, base_pre h hc ha hy, cov, ws⟩

end VG.Proof.Ed25519.X86.PublicKey

end

end

/-! Merged from `Proof.Ed25519.X86.PublicKey.CT`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.X86.PublicKey.CTCommon`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey
open VG.Impl.Ed25519.X86.Whole (Value setup)
variable {n : Nat}

def Two (n : Nat) (s₁ s₂ : State) (P : State → State → Prop) (a b : State) : Prop :=
  Ctx n s₁ a ∧ Ctx n s₂ b ∧ P s₁ a ∧ P s₂ b

variable {s₁ s₂ : State}

theorem esp_eq (pub : pkPub s₁ s₂) : esp s₁ = esp s₂ := congrArg (· - BitVec.ofNat 32 256) pub.1

theorem argValue_eq (pub : pkPub s₁ s₂) {v : Value} (hv : Whole.valid 3 v) : argValue s₁ v = argValue s₂ v := by
  cases v with
  | const _ => rfl
  | frame d => exact congrArg (· + BitVec.ofNat 32 d) (esp_eq pub)
  | caller i d =>
    apply congrArg (· + BitVec.ofNat 32 d)
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by change i < 3 at hv; omega_using [hv]) with rfl | rfl | rfl
    · exact pub.2.1
    · exact pub.2.2.1
    · exact pub.2.2.2.1

theorem two_esp (pub : pkPub s₁ s₂) {P : State → State → Prop} {a b : State} (h : Two n s₁ s₂ P a b) :
    a.gpr .esp = b.gpr .esp := h.1.esp.trans ((esp_eq pub).trans h.2.1.esp.symm)

theorem two_wp (h₁ : Facts n s₁) (h₂ : Facts n s₂) {P Q : State → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two n s₁ s₂ P) c fun _ _ => True)
    (hw : ∀ s t, Facts n s → Ctx n s t → P s t → WP isa c t fun u => Ctx n s u ∧ Q s u) :
    RelCT isa (Two n s₁ s₂ P) c (Two n s₁ s₂ Q) :=
  (hct.wp fun a b h => ⟨hw s₁ a h₁ h.1 h.2.2.1, hw s₂ b h₂ h.2.1 h.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩

theorem setup_ct (h₁ : Facts n s₁) (h₂ : Facts n s₂) (pub : pkPub s₁ s₂) (vs : List Value) (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 3 v)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (setup 0 vs)) hint).isSome = true) :
    RelCT isa (Two n s₁ s₂ fun _ _ => True) (.block (setup 0 vs)) (Two n s₁ s₂ (Slots vs)) :=
  two_wp h₁ h₂ (Whole.block_rel (fun _ _ h => two_esp pub h) ht) fun _ _ h hc _ =>
    WP.mono (setup_ok h hc hn hv) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

theorem call_args_eq (h₁ : Facts n s₁) (h₂ : Facts n s₂) (pub : pkPub s₁ s₂) {vs : List Value} (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 3 v)
    {a b : State} (h : Two n s₁ s₂ (Slots vs) a b) {j : Nat} (hj : j < vs.length) :
    arg a.callEntry j = arg b.callEntry j := by
  rw [Whole.call_arg h.1.esp h₁.toBounds.call (by have := h₁.toBounds.frame; omega_using [this]) (by omega_using [hn, hj]),
    Whole.call_arg h.2.1.esp h₂.toBounds.call (by have := h₂.toBounds.frame; omega_using [this]) (by omega_using [hn, hj]),
    h.2.2.1 j hj, h.2.2.2 j hj]
  exact argValue_eq pub (hv _ (List.getElem_mem hj))

/-- `Two`, with each state naming the statics its entry names. -/
def TwoS (n : Nat) (s₁ s₂ : State) (P : State → State → Prop) (a b : State) : Prop :=
  Two n s₁ s₂ P a b ∧ a.syms = s₁.syms ∧ b.syms = s₂.syms

theorem two_syms {P Q : State → State → Prop} {c : Prog isa}
    (h : RelCT isa (Two n s₁ s₂ P) c (Two n s₁ s₂ Q)) : RelCT isa (TwoS n s₁ s₂ P) c (TwoS n s₁ s₂ Q) := by
  intro a b ta tb a' b' ⟨hp, ya, yb⟩ ea eb
  obtain ⟨e, q⟩ := h _ _ _ _ _ _ hp ea eb
  exact ⟨e, q, (Exec.syms ea).trans ya, (Exec.syms eb).trans yb⟩

end VG.Proof.Ed25519.X86.PublicKey
end

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey
variable {n : Nat}

variable {s₁ s₂ : State}

theorem base_ct (h₁ : Facts n s₁) (h₂ : Facts n s₂) (pub : pkPub s₁ s₂) :
    RelCT isa (TwoS n s₁ s₂ (Slots baseValues)) (.call "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase)
      (TwoS n s₁ s₂ fun _ _ => True) := by
  have hct : RelCT isa (TwoS n s₁ s₂ (Slots baseValues))
      (.call "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase) fun _ _ => True := by
    refine Whole.callEx scalarBase_ok scalarBase_ct fun a b h => ?_
    let ra := base_ready h₁ h.1.1 h.2.1 h.1.2.2.1
    let rb := base_ready h₂ h.1.2.1 h.2.2 h.1.2.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.1.2.1
    have hj := fun j (hj : j < baseValues.length) =>
      call_args_eq h₁ h₂ pub (by decide) (Whole.valid_all (by decide)) h.1 hj
    refine ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre, ⟨congrArg (· - 4) (two_esp pub h.1),
      hj 0 (by decide), hj 1 (by decide), hj 2 (by decide), ?_⟩, ca, wa, cb, wb, two_esp pub h.1⟩
    change a.syms _ = b.syms _
    rw [h.2.1, h.2.2]
    exact pub.2.2.2.2
  have fw : ∀ (u₀ u : State), Facts n u₀ → Ctx n u₀ u → u.syms = u₀.syms → Slots baseValues u₀ u →
      WP isa (.call "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase) u
        (fun v => Ctx n u₀ v ∧ v.syms = u₀.syms) := fun u₀ u hf hc hy hs =>
    WP.mono_syms ((base_ready hf hc hy hs).wp hc scalarBase_ok base_nosp (by rw [base_stack]; decide)
      hf.toBounds.call) fun _ hv yv => ⟨hv, yv.trans hy⟩
  exact (hct.wp fun a b h => ⟨fw s₁ a h₁ h.1.1 h.2.1 h.1.2.2.1, fw s₂ b h₂ h.1.2.1 h.2.2 h.1.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨⟨h.2.1.1, h.2.2.1, trivial, trivial⟩, h.2.1.2, h.2.2.2⟩

theorem prune_ct (h₁ : Facts n s₁) (h₂ : Facts n s₂) (pub : pkPub s₁ s₂) : RelCT isa (Two n s₁ s₂ fun _ _ => True) (.block prune) (Two n s₁ s₂ fun _ _ => True) := by
  refine two_wp h₁ h₂ (Whole.block_rel (fun _ _ h => two_esp pub h) (by native_taint_decide)) ?_
  intro s t h hc _
  exact WP.mono (prune_step h hc (digest := Spec.Sha512.bytesAt t.mem ((esp s).setWidth 64 + 192) 64) rfl)
    fun _ hu => ⟨hu.1, trivial⟩

theorem wipe_ct (h₁ : Facts n s₁) (h₂ : Facts n s₂) (pub : pkPub s₁ s₂) : RelCT isa (Two n s₁ s₂ fun _ _ => True) (.block wipe) (Two n s₁ s₂ fun _ _ => True) := by
  refine two_wp h₁ h₂ (Whole.block_rel (fun _ _ h => two_esp pub h) (by native_taint_decide)) ?_
  intro s t h hc _
  exact WP.mono (Whole.Ctx.zeroWords hc (start := 8) (count := 56)
    (by have := h.toBounds.frame; omega_using [this]) (by decide)) fun _ hu => ⟨hu.1, trivial⟩

/-- The frame's body after any `first` whose runs are related. -/
theorem bodyFrom_ct (h₁ : Facts n s₁) (h₂ : Facts n s₂) (pub : pkPub s₁ s₂) {first : Prog isa}
    (hh : RelCT isa (TwoS n s₁ s₂ fun _ _ => True) first (TwoS n s₁ s₂ fun _ _ => True)) :
    RelCT isa (TwoS n s₁ s₂ fun _ _ => True) (bodyFrom first) (TwoS n s₁ s₂ fun _ _ => True) := by
  have b := setup_ct h₁ h₂ pub baseValues (by decide) (Whole.valid_all (by decide)) (by native_taint_decide)
  exact hh.seq ((two_syms (prune_ct h₁ h₂ pub)).seq (((two_syms b).seq (base_ct h₁ h₂ pub)).seq
      (two_syms (wipe_ct h₁ h₂ pub))))

/-- The frame around `bodyFrom first`, for any `first` whose runs are related. -/
theorem frame_ct {post : State → State → Prop} {first : Prog isa}
    (hh : ∀ {s₁ s₂ : State}, Facts n s₁ → Facts n s₂ → pkPub s₁ s₂ →
      RelCT isa (TwoS n s₁ s₂ fun _ _ => True) first (TwoS n s₁ s₂ fun _ _ => True)) :
    ConstantTime isa (pkLocalWith n post).pre pkPub
      (.frame (.push (List.replicate 64 .eax)) (bodyFrom first) (.pop .eax 64)) := by
  apply RelCT.constantTime
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb a' b' ⟨s₁, s₂, ⟨p₁, p₂, hp⟩, rfl, rfl⟩ ea eb
  have f₁ := facts p₁
  have f₂ := facts p₂
  exact ⟨(bodyFrom_ct f₁ f₂ hp (hh f₁ f₂ hp) _ _ _ _ _ _
    ⟨⟨push_ctx p₁, push_ctx p₂, trivial, trivial⟩, rfl, rfl⟩ ea eb).1, trivial⟩

/-! ## The copy of the cached digest -/

/-- The digest's bytes: the 64 bytes at the second argument, apart from the frame. -/
theorem digest_disjoint {s : State} (h : Facts 64 s) :
    Region.Disjoint ⟨(arg s 1).setWidth 64, 64⟩ ⟨(esp s).setWidth 64 + BitVec.ofNat 64 192, 64⟩ :=
  h.ks.symm.sub_right fun p hp => Whole.frame_sub (esp s) p (Offset.sub_base _ (by decide) p hp)

/-- `copyExpanded` leaves the 64 bytes at the second argument at frame offset 192. -/
theorem copy_ok {s t : State} (h : Facts 64 s) (hc : Ctx 64 s t) :
    WP isa copyExpanded t fun u => Ctx 64 s u ∧
      Spec.Sha512.bytesAt u.mem ((esp s).setWidth 64 + 192) 64 =
        Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64 := by
  refine WP.mono (Whole.copyExpanded_ok hc (by have := h.toBounds.frame; omega_using [this])
    (original_arg_readable h hc (j := 1) (by decide)) (original_arg h hc (j := 1) (by decide)) h.seed
    (by rw [hc.rd]; exact List.mem_append_left _ List.mem_cons_self) (digest_disjoint h))
    fun u ⟨hu, hb⟩ => ⟨hu, hb.trans (seed_same h hc)⟩

theorem copy_ct (h₁ : Facts 64 s₁) (h₂ : Facts 64 s₂) (pub : pkPub s₁ s₂) :
    RelCT isa (TwoS 64 s₁ s₂ fun _ _ => True) copyExpanded (TwoS 64 s₁ s₂ fun _ _ => True) := by
  have p : RelCT isa (Two 64 s₁ s₂ fun _ _ => True) (.block copyPtr)
      (Two 64 s₁ s₂ fun s u => u.gpr .ecx = arg s 1) :=
    two_wp h₁ h₂ (Whole.block_rel (fun _ _ h => two_esp pub h) (by native_taint_decide)) fun s t h hc _ =>
      WP.mono (Whole.copyPtr_ok hc (original_arg_readable h hc (j := 1) (by decide)))
        fun _ ⟨hu, _, he⟩ => ⟨hu, he.trans (original_arg h hc (j := 1) (by decide))⟩
  have w : RelCT isa (Two 64 s₁ s₂ fun s u => u.gpr .ecx = arg s 1) (.block copyDigestWords)
      (Two 64 s₁ s₂ fun _ _ => True) := by
    refine two_wp h₁ h₂ (RelCT.taint (A := taint) (τr [.esp, .ecx]) (fun a b h => agree_regs fun r hr => ?_)
      (by native_taint_decide)) fun s t h hc he =>
        WP.mono (Whole.copyWords_ok hc (by have := h.toBounds.frame; omega_using [this]) he h.seed
          (by rw [hc.rd]; exact List.mem_append_left _ List.mem_cons_self) (digest_disjoint h))
          fun _ hu => ⟨hu.1, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact two_esp pub h
    · exact h.2.2.1.trans (pub.2.2.1.trans h.2.2.2.symm)
  exact two_syms (p.seq w)

theorem copy_nosp : NoSp copyExpanded := NoSp.of_all (by decide +kernel)

end VG.Proof.Ed25519.X86.PublicKey
end

/-! Merged from `Proof.Ed25519.X86.PublicKey.Lit`. -/
section
namespace VG.Impl.Ed25519.X86.PublicKey
materialize_code publicKeyExpanded
end VG.Impl.Ed25519.X86.PublicKey
end

/-! Merged from `Proof.Ed25519.X86.PublicKey.Contract`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86
open VG.Impl.Ed25519.X86 (combSym combConsts)
variable {n : Nat}

def pkWideWith (n : Nat) (post : State → State → Prop) : Contract isa := { pkLocalWith n post with
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, n⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = [seed, TBL ((s.syms combSym).setWidth 64)] ∧ s.wr = [out, scratch, args] ∧
      out.Disjoint seed ∧ out.Disjoint scratch ∧
      seed.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ stack.Disjoint out ∧
      stack.Disjoint seed ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + n ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 ∧ CombHeld s [out, scratch, stack]
}

def pkSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

theorem pkWide_pre {post : State → State → Prop} (s : State) (h : (pkWideWith n post).pre s) :
    (pkLocalWith n post).pre (s.withRegions (pkRd n s) (pkWr s)) := by
  obtain ⟨_, _, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, no, ns, nc, nb, na, held⟩ := h
  simp only [pkLocalWith, pkRd, pkWr, arg_withRegions, argAddr_withRegions, State.withRegions_syms,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, below,
    Taint.sub_setWidth nb, CombHeld]
  exact ⟨True.intro, True.intro, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, no, ns, nc, nb, na, held⟩

end VG.Proof.Ed25519.X86.PublicKey
end

/-! ## Derivation from the seed's cached digest -/

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey
open VG.Impl.Ed25519.X86 (combSym combConsts)
open VG.Proof.Ed25519 (sha512_length)

/-- The public key of every seed whose SHA-512 digest is at the second argument. -/
def pkPostE (s t : State) : Prop :=
  ∀ seed : List Byte, seed.length = 32 →
    Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64 = Spec.Sha512.sha512 seed →
    Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 = Spec.Ed25519.publicKey seed

def pkLocalE : Contract isa := pkLocalWith 64 pkPostE
def pkWideE : Contract isa := pkWideWith 64 pkPostE

theorem publicKeyExpanded_ok {s : State} (h : pkLocalE.pre s) :
    WP isa publicKeyExpanded s fun t => abiPreserved s t ∧ pkLocalE.post s t :=
  frame_ok h copy_nosp (bodyFrom_ok (t := pushed (List.replicate 64 .eax) s) (facts h) rfl
    (copy_ok (facts h) (push_ctx h)))
    fun _ ht _ _ hE => ht.trans (congrArg (fun d =>
      Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul (Spec.Ed25519.prune d) Spec.Ed25519.basePoint)) hE)

theorem publicKeyExpanded_ct : ConstantTime isa pkLocalE.pre pkLocalE.pub publicKeyExpanded :=
  frame_ct fun h₁ h₂ pub => copy_ct h₁ h₂ pub

def satSeedE : List Byte := Spec.Ed25519.bytesAt (fun _ => 0) 0x2000 32
def satDigestE : List Byte := Spec.Sha512.sha512 satSeedE

theorem satSeedE_length : satSeedE.length = 32 := by
  simp only [satSeedE, Spec.Ed25519.bytesAt, List.length_map, List.length_range]

/-- `pkSatMem`, with the digest at `0x2000`. -/
def pkSatMemE : Mem := fun a =>
  if a.toNat < 0x2000 then 0 else if a.toNat < 0x2040 then satDigestE[a.toNat - 0x2000]?.getD 0
  else pkSatMem a

def pkSatStateE : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemWith pkSatMemE
  rd := [⟨0x2000, 64⟩, ⟨0x100000, 24576⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 12⟩]
  syms _ := 0x100000

theorem pkSatE_arg (j : Nat) (hj : j < 3) :
    arg pkSatStateE j = pkSatMemE.readW (argAddr pkSatStateE j) 32 := by
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change satMemWith pkSatMemE _ = _
  rw [satMemWith_out]
  have : ∀ j < 3, ∀ b < 4, 8 * 32 * 96 ≤ (argAddr pkSatStateE j + BitVec.ofNat 64 b - 0x100000).toNat := by
    decide
  exact this j hj b (by omega_using [hb])

theorem satE_digest : Spec.Ed25519.bytesAt (satMemWith pkSatMemE) 0x2000 64 = satDigestE := by
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
    unfold pkSatMemE
    simp only [ha, show ¬ 0x2000 + i < 0x2000 from by omega_using [], ite_false,
      show 0x2000 + i < 0x2040 from by omega_using [hi'], ite_true, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

theorem pkE_sat :
    (Proof.Ed25519.publicKeyExpandedContract (X86.abi.withConsts combConsts) 280).pre pkSatStateE := by
  have hl := combWords_length
  have a0 : arg pkSatStateE 0 = 0x1000 := (pkSatE_arg 0 (by decide)).trans (by decide)
  have a1 : arg pkSatStateE 1 = 0x2000 := (pkSatE_arg 1 (by decide)).trans (by decide)
  have a2 : arg pkSatStateE 2 = 0x4000 := (pkSatE_arg 2 (by decide)).trans (by decide)
  have held : TblWords ((pkSatStateE.syms combSym).setWidth 64) pkSatStateE.mem :=
    satMemWith_held pkSatMemE
  have key : Spec.Ed25519.bytesAt pkSatStateE.mem ((0x2000 : BitVec 32).setWidth 64) 64 =
      Spec.Sha512.sha512 satSeedE := satE_digest
  generalize e : pkSatStateE = s
  sig_pre [Proof.Ed25519.publicKeyExpandedContract, Proof.Ed25519.publicKeyExpandedSig,
    Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  refine ⟨by decide, by decide, by rw [hl]; rfl, held, by rw [hl]; decide, ?_, ?_, ?_, by decide, ?_⟩
  · rw [hl]
    intro r hr
    change r ∈ [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 12⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · rw [hl]; exact Region.disjoint_of_sep (by decide)
  · rw [hl]; exact Region.disjoint_of_sep (by decide)
  · rw [a0, a1, a2]
    refine ⟨rfl, rfl, ?_⟩
    repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | exact ⟨satSeedE, satSeedE_length, key⟩ |
      decide

theorem pkWideE_implies :
    pkWideE.Implies (Proof.Ed25519.publicKeyExpandedContract (X86.abi.withConsts combConsts) 280) where
  pre s h := by
    sig_pre [Proof.Ed25519.publicKeyExpandedContract, Proof.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨h280, hsp, hd, held, hfit, hdw, -, hstk, -, ht, hw, os, oc, oa, sc, -, ca, ro, -, rc, -,
      ko, ks, kc, -, f0, f1, f2, -⟩ := h
    refine ⟨?_, hw, os, oc, sc, oa.symm, ca.symm, ro, rc, ko, ks, kc, f0, f1, f2, h280, by omega_using [hsp],
      held, hfit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hstk
  post := by
    intro s t _ h
    sig_post [Proof.Ed25519.publicKeyExpandedContract, Proof.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts]
    exact h
  pub s t _ _ h := by
    sig_pub [Proof.Ed25519.publicKeyExpandedContract, Proof.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨hsp, h0, h1, h2, hsy⟩
  sat := ⟨pkSatStateE, pkE_sat⟩

theorem publicKeyExpanded_verified :
    Verified X86.target publicKeyExpanded
      (Proof.Ed25519.publicKeyExpandedContract (X86.abi.withConsts combConsts) 280) := by
  have hsat := pkWideE_implies.sat_left
  have satLocal : ∃ s, pkLocalE.pre s := hsat.elim fun s h => ⟨_, pkWide_pre s h⟩
  have verifiedLocal : Verified X86.target publicKeyExpanded pkLocalE :=
    Verified.of_correct (fun _ h => publicKeyExpanded_ok h) publicKeyExpanded_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal (pkRd 64) pkWr pkWide_pre
    ?_ ?_ ?_ ?_ hsat) pkWideE_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [pkRd, pkWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with (rfl | rfl | rfl) | (rfl | rfl) <;> simp
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [pkWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [pkWideE, pkWideWith, pkLocalE, pkLocalWith, pkPostE, arg_withRegions,
      State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [pkWideE, pkWideWith, pkLocalE, pkLocalWith, pkPub, arg_withRegions, State.withRegions_gpr,
      State.withRegions_syms] using h

end VG.Proof.Ed25519.X86.PublicKey
