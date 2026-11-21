module

public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Ed25519.AArch64.Scrub
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
public import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Prune
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Expanded
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ed25519.ExpandedSign
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Prune
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
meta import VerifiedGarbage.Proof.Ed25519.Expanded
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarVerified
import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.AArch64.Ladder
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarVerified
meta import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X25519.AArch64.Ladder
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddCodec
public import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Preserve
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Ed25519.Signing
meta import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddCodec
meta import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Preserve
meta import VerifiedGarbage.Proof.Ed25519.VerifyBytes
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Mathlib.Tactic.NormNum.Prime
meta import Mathlib.Data.Nat.Totient
meta import Mathlib.Tactic.Positivity.Finset
meta import Mathlib.Algebra.Order.Field.Basic
meta import Mathlib.Tactic.NormNum.GCD
meta import Mathlib.Data.Sym.Sym2.Init
meta import Mathlib.Tactic.ContinuousFunctionalCalculus
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
import VerifiedGarbage.Spec.Weierstrass
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
meta import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
public import Mathlib.Tactic.Push
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.RelClasses
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
meta import Mathlib.Tactic.Push
meta import Mathlib.Data.Nat.Basic
meta import Mathlib.Order.RelClasses

/-! ### `Ed25519.AArch64.SignCached.Verified`, which only this module used -/

section

/-! ### `Ed25519.AArch64.SignCached.CTReady`, which only this module used -/

section

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTCommon`. -/

@[expose] public section

section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

def Two (L : Lay) (g₁ g₂ : Reg → BitVec 64) (v₁ v₂ : VReg → BitVec 128)
    (m₁ m₂ : Mem) (P : State → Prop) (a b : State) : Prop :=
  Ctx L g₁ v₁ m₁ a ∧ Ctx L g₂ v₂ m₂ b ∧ P a ∧ P b ∧
    a.syms Impl.Ed25519.AArch64.combSym = L.T ∧ b.syms Impl.Ed25519.AArch64.combSym = L.T

theorem two_sp {P : State → Prop} {a b : State} (h : Two L g₁ g₂ v₁ v₂ m₁ m₂ P a b) :
    a.sp = b.sp := h.1.sp.trans h.2.1.sp.symm

/-- `two_wp`, whose runs may use the static's address. -/
theorem two_wpS {P Q : State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ P) c fun _ _ => True)
    (ha : ∀ t, Ctx L g₁ v₁ m₁ t → t.syms Impl.Ed25519.AArch64.combSym = L.T → P t →
      WP isa c t fun u => Ctx L g₁ v₁ m₁ u ∧ Q u)
    (hb : ∀ t, Ctx L g₂ v₂ m₂ t → t.syms Impl.Ed25519.AArch64.combSym = L.T → P t →
      WP isa c t fun u => Ctx L g₂ v₂ m₂ u ∧ Q u) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ P) c (Two L g₁ g₂ v₁ v₂ m₁ m₂ Q) :=
  (hct.wp (F₁ := fun (u : State) => (Ctx L g₁ v₁ m₁ u ∧ Q u) ∧ u.syms Impl.Ed25519.AArch64.combSym = L.T)
    (F₂ := fun (u : State) => (Ctx L g₂ v₂ m₂ u ∧ Q u) ∧ u.syms Impl.Ed25519.AArch64.combSym = L.T) fun a b h =>
    ⟨WP.mono_syms (ha a h.1 h.2.2.2.2.1 h.2.2.1) fun _ hu su => ⟨hu, by rw [su]; exact h.2.2.2.2.1⟩,
      WP.mono_syms (hb b h.2.1 h.2.2.2.2.2 h.2.2.2.1) fun _ hu su => ⟨hu, by rw [su]; exact h.2.2.2.2.2⟩⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨h.2.1.1.1, h.2.2.1.1, h.2.1.1.2, h.2.2.1.2, h.2.1.2, h.2.2.2⟩

theorem two_wp {P Q : State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ P) c fun _ _ => True)
    (ha : ∀ t, Ctx L g₁ v₁ m₁ t → P t → WP isa c t fun u => Ctx L g₁ v₁ m₁ u ∧ Q u)
    (hb : ∀ t, Ctx L g₂ v₂ m₂ t → P t → WP isa c t fun u => Ctx L g₂ v₂ m₂ u ∧ Q u) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ P) c (Two L g₁ g₂ v₁ v₂ m₁ m₂ Q) :=
  two_wpS hct (fun t hc _ hp => ha t hc hp) (fun t hc _ hp => hb t hc hp)

theorem setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (args : List (Reg × Value)) (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup args)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block (setup args))
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L args)) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_sp h) ht) ?_ ?_
  · intro s hc _
    exact WP.mono (args_ok hc hL ha hn hv hr) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩
  · intro s hc _
    exact WP.mono (args_ok hc hL hb hn hv hr) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

theorem args_eq {args : List (Reg × Value)} {a b : State}
    (h : Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L args) a b) {p : Reg × Value} (hp : p ∈ args) :
    a.gpr p.1 = b.gpr p.1 := (h.2.2.1 p hp).trans (h.2.2.2.1 p hp).symm

theorem call_gpr_eq {args : List (Reg × Value)} {a b : State}
    (h : Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L args) a b) {p : Reg × Value}
    (hp : p ∈ args) (hl : p.1 ∉ linkRegs) : a.callEntry.gpr p.1 = b.callEntry.gpr p.1 := by
  rw [State.callEntry_gpr _ hl, State.callEntry_gpr _ hl]
  exact args_eq h hp

theorem call_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    {P : State → Prop} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hd : c.aarch64Depth ≤ 1)
    (ready : ∀ {g v m t}, Ctx L g v m t → t.syms Impl.Ed25519.AArch64.combSym = L.T →
      TblWords L.T t.mem → P t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, Two L g₁ g₂ v₁ v₂ m₁ m₂ P a b →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw)) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ P) (.call name c)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply two_wpS
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready h.1 h.2.2.2.2.1 (h.1.tbl hL ha.2) h.2.2.1
    let rb := ready h.2.1 h.2.2.2.2.2 (h.2.1.tbl hL hb.2) h.2.2.2.1
    obtain ⟨ca, wa⟩ := Whole.CallReady.covers_state h.1 ra
    obtain ⟨cb, wb⟩ := Whole.CallReady.covers_state h.2.1 rb
    exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ h, ca, wa, cb, wb⟩
  · intro t hc hy hs
    exact WP.mono (Whole.CallReady.wpF hc (ready hc hy (hc.tbl hL ha.2) hs) correct hd)
      fun _ hu => ⟨hu, trivial⟩
  · intro t hc hy hs
    exact WP.mono (Whole.CallReady.wpF hc (ready hc hy (hc.tbl hL hb.2) hs) correct hd)
      fun _ hu => ⟨hu, trivial⟩

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64
variable {L : Lay} {s : State}

def reduce_ready (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256) (ha : ReduceArgs L d s) : Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs s := by
  have cov : Covers (reduceRd L ++ reduceWr L d) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (digestWithin L)
    · exact .inl (fieldWithin L hd)
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ reduceWr L d, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (fieldWithin L hd)
    · exact .inr (.inr (scratchWithin L))
  exact ⟨reduceRd L, reduceWr L d, reduce_pre hL ha, cov, ws⟩

def base_ready (hL : L.Ok) (ha : BaseArgs L s) (hsy : s.syms Impl.Ed25519.AArch64.combSym = L.T)
    (hm : TblWords L.T s.mem) : Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs s := by
  have cov : Covers (baseRd L ++ baseWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [baseRd, baseWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (fieldWithin L (by decide))
    · exact .inr ⟨L.TB, by simp [Lay.inputs], 0, (BitVec.add_zero _).symm, by simp⟩
    · exact .inr (output_covered (baseWithin L))
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ baseWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [baseWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (baseWithin L))
    · exact .inr (.inr (scratchWithin L))
  exact ⟨baseRd L, baseWr L, base_pre hL ha hsy hm, cov, ws⟩

def mul_ready (hL : L.Ok) (ha : MulArgs L s) : Whole.CallReady scalarMulAddLocal L.E L.inputs L.outputs s := by
  have cov : Covers (mulRd L ++ mulWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [mulRd, mulWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact .inl (fieldWithin L (by decide))
    · exact .inl (fieldWithin L (by decide))
    · exact .inl (fieldWithin L (by decide))
    · exact .inr (output_covered (halfWithin L))
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ mulWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [mulWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (halfWithin L))
    · exact .inr (.inr (scratchWithin L))
  exact ⟨mulRd L, mulWr L, mul_pre hL ha, cov, ws⟩

def init_ready (ha : s.gpr .x0 = L.scr) :
    Whole.CallReady (Proof.Sha512.initAArch64 Spec.Sha512.H0_512) L.E L.inputs L.outputs s := by
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨[], Whole.initWr L.scr, Whole.init_pre ha, Whole.covers_writes hw, hw⟩

def UpdateArgs (L : Lay) (count p len : Addr) (s : State) : Prop :=
  s.gpr .x0 = L.scr ∧ s.gpr .x1 = count ∧ s.gpr .x2 = p ∧ s.gpr .x3 = len ∧ s.gpr .x4 = L.scr + 192

def update_ready (hL : L.Ok) (hsp : s.sp = L.E) {count p len : Addr} (hi : Input L p len)
    (ha : UpdateArgs L count p len s) :
    Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs s := by
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨Whole.updateRd p len, Whole.hashWr L.scr,
    Whole.update_pre ha.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2 hi.scratch (by rw [hsp]; exact hL.e16)
      (by rw [hsp]; exact hL.cc) (by rw [hsp]; exact hi.ck hL), update_covers hi, hw⟩

def FinalArgs (L : Lay) (count : Addr) (s : State) : Prop :=
  s.gpr .x0 = L.scr ∧ s.gpr .x1 = count ∧ s.gpr .x2 = L.E + 192 ∧ s.gpr .x3 = L.scr + 192

def finalize_ready (hL : L.Ok) (hsp : s.sp = L.E) {count : Addr} (ha : FinalArgs L count s) :
    Whole.CallReady Proof.Sha512.finalizeAArch64 L.E L.inputs L.outputs s :=
  ⟨[], Whole.finalizeWr L.scr (L.E + 192),
    Whole.finalize_pre ha.1 ha.2.2.1 ha.2.2.2 (hL.kc.sub_left (digestWithin L).sub)
      (by rw [hsp]; exact hL.e16) (by rw [hsp]; exact hL.cc)
      (by rw [hsp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304)),
    Whole.covers_writes (final_writes L), final_writes L⟩

end VG.Proof.Ed25519.AArch64.SignCached

end

end

/-! ### `Ed25519.AArch64.SignCached.Entry`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64

/-- Signing with `n` bytes read at the seed pointer (the seed, or its cached digest), `key`
relating them to the public key, and the postcondition `post`. -/
def signLocalWith (n : Nat) (key : State → Prop) (post : State → State → Prop) : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 64⟩
    let seed : Region := ⟨s.gpr .x1, n⟩
    let pk : Region := ⟨s.gpr .x2, 32⟩
    let msg : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let scr : Region := ⟨s.gpr .x5, 8192⟩
    let stk : Region := below s.sp 352
    s.rd = [seed, pk, msg, TBL (s.syms Impl.Ed25519.AArch64.combSym)] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint msg ∧ out.Disjoint scr ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ msg.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + n ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x5).toNat + 8192 ≤ 2 ^ 64 ∧ 352 ≤ s.sp.toNat ∧ key s ∧
      CombHeld s [out, scr, stk]
  post := post
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
    s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4 ∧ s.gpr .x5 = t.gpr .x5 ∧
    s.syms Impl.Ed25519.AArch64.combSym = t.syms Impl.Ed25519.AArch64.combSym

def lay (n : Nat) (s : State) : Lay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, Whole.base s,
    s.syms Impl.Ed25519.AArch64.combSym, n⟩

variable {n : Nat} {key : State → Prop} {post : State → State → Prop}

theorem entry_below {s : State} (h : (signLocalWith n key post).pre s) : 352 ≤ s.sp.toNat := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩ := h
  exact hb

theorem entry_writes {s : State} (h : (signLocalWith n key post).pre s) :
    ∀ r ∈ s.wr, (below s.sp 352).Disjoint r := by
  obtain ⟨_, hw, _, _, _, _, _, _, _, ko, _, _, _, kc, _⟩ := h
  intro r hr
  rw [hw] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ko
  · exact kc

theorem lay_ok {s : State} (h : (signLocalWith n key post).pre s) (hn : 32 ≤ n) : (lay n s).Ok := by
  obtain ⟨_, _, os, op, om, oc, sc, pc, mc, ko, ks, kp, km, kc, no, ns, np, nm, nc, hb, _, -, fit, dj⟩ := h
  have dk := dj (below s.sp 352) (by simp)
  have stk := Whole.stk_sub s
  have fr : Region.Sub (Whole.FR (Whole.base s)) (below s.sp 352) :=
    fun a h => stk a ((Region.sub_prefix (by decide) : Region.Sub (Whole.FR (Whole.base s)) ⟨Whole.base s, 336⟩) a h)
  have ar : Region.Sub (Whole.ARGS (Whole.base s)) (below s.sp 352) :=
    fun a h => stk a ((Offset.sub_base _ (by decide) : Region.Sub (Whole.ARGS (Whole.base s)) ⟨Whole.base s, 336⟩) a h)
  have ck := Whole.ck_sub s
  refine ⟨?_, ?_, oc, ko.sub_left fr, no, ?_, ?_, kc.sub_left fr, np, nm, ns, nc, Whole.base_16 hb, ?_,
    ko.sub_left ck, kc.sub_left ck, fit, hn⟩
  · change (s.sp - 336#64).toNat + 304 ≤ 2 ^ 64
    rw [BitVec.toNat_sub_of_le (by change 336 ≤ s.sp.toNat; omega_using [hb])]
    have hs := s.sp.isLt
    change s.sp.toNat - 336 + 304 ≤ 2 ^ 64
    omega_using []
  · simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact os
    · exact op
    · exact om
    · exact (dj ⟨s.gpr .x0, 64⟩ (by simp)).symm
    · exact (ko.sub_left ar).symm
  · simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact sc
    · exact pc
    · exact mc
    · exact dj ⟨s.gpr .x5, 8192⟩ (by simp)
    · exact kc.sub_left ar
  · simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact ks.sub_left fr
    · exact kp.sub_left fr
    · exact km.sub_left fr
    · exact dk.symm.sub_left fr
    · exact Offset.base_disjoint _ (by decide) (by decide)
  · simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact ks.sub_left ck
    · exact kp.sub_left ck
    · exact km.sub_left ck
    · exact dk.symm.sub_left ck
    · exact Whole.ck_frame (by decide : 256 + 48 ≤ 304)

theorem entry_ctx {s p : State} (h : (signLocalWith n key post).pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    Ctx (lay n s) s.gpr s.v p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  simpa only [Whole.bodyRd, h.1, Whole.bodyWr, h.2.1, Ctx, Lay.inputs, Lay.outputs,
    Lay.SEED, Lay.PK, Lay.MSG, Lay.OUT, Lay.SCR, Lay.ARGS, Lay.TB, Whole.ARGS, show BitVec.ofNat 64 256 = (256 : Addr) from rfl, lay, List.cons_append, List.nil_append] using hc

theorem entry_args {s p : State} (h : (signLocalWith n key post).pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    Arguments (lay n s) p.mem := by
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · have hw := Whole.saved_words hp hj
    have he : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega_using [hj]
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hw
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, held, fit, dj⟩ := h
    have hf := Whole.saved_frame hp
    rw [← held i hi]
    refine hf.readW (r := TBL (s.syms Impl.Ed25519.AArch64.combSym))
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, fit])) (fun r hr => ?_) (by decide)
    rw [List.mem_singleton.mp hr]
    exact (dj (below s.sp 352) (by simp)).sub_right (Whole.stk_sub s)

theorem entry_syms {s p : State} (hp : Whole.Saved (Whole.entered s) 6 p) :
    (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)).syms Impl.Ed25519.AArch64.combSym = (lay n s).T :=
  congrFun hp.step.syms Impl.Ed25519.AArch64.combSym

theorem entry_input {s : State} (h : (signLocalWith n key post).pre s) {m : Mem}
    (hf : Frame [below s.sp 336] s.mem m) {r : Region} (hr : r ∈ s.rd) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m r.base r.len = Spec.Ed25519.bytesAt s.mem r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes ?_ hn (List.mem_range.mp hi)
  rintro R hR
  rw [List.mem_singleton.mp hR]
  obtain ⟨hrd, _, _, _, _, _, _, _, _, _, ks, kp, km, _, _, _, _, _, _, _, _, -, -, dj⟩ := h
  rw [hrd] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have hb : Region.Sub (below s.sp 336) (below s.sp 352) := below_sub (by decide) (by decide)
  rcases hr with rfl | rfl | rfl | rfl
  · exact (ks.sub_left hb).symm
  · exact (kp.sub_left hb).symm
  · exact (km.sub_left hb).symm
  · exact (dj (below s.sp 352) (by simp)).sub_right hb

end VG.Proof.Ed25519.AArch64.SignCached

end

end

/-! ### `Ed25519.AArch64.SignCached.Body`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Ed25519.AArch64.SignCached.Secret`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.AArch64.SignCached.Prefix`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

structure PrefixStep (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  vec : t.v = s.v
  regs : ∀ r, r ≠ .x0 → r ≠ .x15 → t.gpr r = s.gpr r

theorem PrefixStep.trans {s t u : State} (h : PrefixStep s t) (h' : PrefixStep t u) : PrefixStep s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.vec.trans h.vec,
    fun r h0 h15 => (h'.regs r h0 h15).trans (h.regs r h0 h15)⟩

theorem copyWord_ok {s : State} {E : Addr} (he : s.sp = E)
    (hr : (⟨E, 256⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < 4) :
    WP isa (.block (copyWord k)) s fun t => PrefixStep s t ∧
      t.mem = s.mem.writeW (E + BitVec.ofNat 64 (64 + 8 * k))
        (s.mem.readW (E + BitVec.ofNat 64 (224 + 8 * k)) 64) := by
  have source : InRegions (s.rd ++ s.wr) (E + BitVec.ofNat 64 (224 + 8 * k)) 8 :=
    ⟨⟨E, 256⟩, List.mem_append_right _ hr, Offset.contains_base E (by omega_using [hk]) (by omega_using [hk])⟩
  have dest : InRegions s.wr (E + BitVec.ofNat 64 (64 + 8 * k)) 8 :=
    ⟨⟨E, 256⟩, hr, Offset.contains_base E (by omega_using [hk]) (by omega_using [hk])⟩
  have hl : exec (.ldrSp .x0 (224 + 8 * k)) s =
      some (s.write .x .x0 (s.mem.readW (E + BitVec.ofNat 64 (224 + 8 * k)) 64)) := by
    simp only [exec, show (224 + 8 * k) % 8 = 0 ∧ 224 + 8 * k < 32768 from by omega_using [hk],
      and_self, ite_true, State.load, he, source, Option.map_some, Mem.readW, BitVec.setWidth_eq]
  have ha {t : State} : exec (.addSp .x15 64) t = some (t.write .x .x15 (t.sp + BitVec.ofNat 64 64)) := by
    simp only [exec, show 64 < 4096 from by decide, ite_true]
  apply WP.of_runBlock
  simp only [copyWord, runBlock_cons, runStep_some, hl, ha, RegUpd.sp_write]
  rw [exec_str_x ⟨by omega_using [], by omega_using [hk]⟩ (by
    simpa only [RegUpd.wr_write, RegUpd.gpr_write_self, BitVec.setWidth_eq, he, Offset.add_add] using dest)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
  · intro r h0 h15
    simp only [RegUpd.gpr_write, h0, h15, ite_false]
  · simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
      BitVec.setWidth_eq, he, Offset.add_add]

structure PrefixInv (E : Addr) (s : State) (n : Nat) (t : State) : Prop where
  step : PrefixStep s t
  frame : Frame [⟨E + BitVec.ofNat 64 64, 32⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (E + BitVec.ofNat 64 (64 + 8 * j)) 64 =
    s.mem.readW (E + BitVec.ofNat 64 (224 + 8 * j)) 64

theorem copyPrefix_ok {s : State} {E : Addr} (he : s.sp = E)
    (hw : (⟨E, 256⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 4, WP isa (.block ((List.range n).flatMap copyWord)) s (PrefixInv E s n)
  | 0, _ => WP.block_nil ⟨⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyPrefix_ok he hw n (by omega_using [hn])) fun u hu => ?_
    refine WP.mono (copyWord_ok (hu.step.sp.trans he) (hu.step.wr ▸ hw) (by omega_using [hn] : n < 4))
      fun t ⟨kt, mt⟩ => ?_
    have same : u.mem.readW (E + BitVec.ofNat 64 (224 + 8 * n)) 64 =
        s.mem.readW (E + BitVec.ofNat 64 (224 + 8 * n)) 64 := by
      apply hu.frame.readW (Region.contains_self _ _) _ (by decide)
      simp only [List.mem_singleton]
      rintro r rfl
      exact Offset.disjoint _ (by omega_using []) (by omega_using [hn]) (by decide)
    rw [same] at mt
    refine ⟨hu.step.trans kt, ?_, fun j hj => ?_⟩
    · rw [mt]
      exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_using []) (by omega_using [hn]) (by decide))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (a := E + BitVec.ofNat 64 (64 + 8 * j))
          (b := E + BitVec.ofNat 64 (64 + 8 * n)) ?_ (by decide)]
        · exact hu.words j (by omega_using [hj, hjn])
        · exact Offset.sep _ (by omega_using [hjn]) (by omega_using [hn, hj]) (by omega_using [hn])

theorem prefix_ok {s : State} {E : Addr} (he : s.sp = E)
    (hw : (⟨E, 256⟩ : Region) ∈ s.wr) :
    WP isa (.block copyPrefix) s fun t => PrefixStep s t ∧
      Frame [⟨E + BitVec.ofNat 64 64, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (E + 64) 32 = Spec.Ed25519.bytesAt s.mem (E + 224) 32 := by
  refine WP.mono (copyPrefix_ok he hw 4 (by decide)) fun t ht => ⟨ht.step, ht.frame, ?_⟩
  rw [Proof.Ed25519.bytesAt_encodeLE t.mem, Proof.Ed25519.bytesAt_encodeLE s.mem]
  apply congrArg (Spec.Ed25519.encodeLE 32)
  change Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (off E 64) 32) =
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off E 224) 32)
  rw [decodeLE_words, decodeLE_words]
  simp only [fe, word]
  rw [ht.words 0 (by decide), ht.words 1 (by decide), ht.words 2 (by decide), ht.words 3 (by decide)]

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g : Reg → BitVec 64} {vec : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem prune_ctx {t : State} (hc : Ctx L g vec m₀ s) (ht : PublicKey.Step s t)
    (hf : Frame [⟨s.sp + 32, 32⟩] s.mem t.mem) : Ctx L g vec m₀ t := by
  refine hc.of_frame ht.rd ht.wr ht.sp ?_ ?_ hf ?_
  · intro r hr _
    apply ht.regs <;> rintro rfl <;> simp [preserved] at hr
  · intro r _; rw [ht.v]
  · intro r hr; rw [List.mem_singleton.mp hr, hc.sp]
    exact .inl (Offset.sub_base _ (by decide : 32 + 32 ≤ 256))

theorem prefix_ctx {t : State} (hc : Ctx L g vec m₀ s) (ht : PrefixStep s t)
    (hf : Frame [⟨L.E + BitVec.ofNat 64 64, 32⟩] s.mem t.mem) : Ctx L g vec m₀ t := by
  refine hc.of_frame ht.rd ht.wr ht.sp ?_ ?_ hf ?_
  · intro r hr _
    apply ht.regs <;> rintro rfl <;> simp [preserved] at hr
  · intro r _; rw [ht.vec]
  · intro r hr; rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by decide : 64 + 32 ≤ 256))

theorem saveSecret_ok (hc : Ctx L g vec m₀ s) {expanded : List Byte}
    (he : Spec.Ed25519.bytesAt s.mem (L.E + 192) 64 = expanded) :
    WP isa (.block saveSecret) s fun t => Ctx L g vec m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 32) 32 =
        Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune expanded) ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 64) 32 = expanded.drop 32 := by
  rw [saveSecret, WP.block_append_iff]
  have fr : (⟨s.sp, 256⟩ : Region) ∈ s.wr := by rw [hc.sp, hc.wr]; exact List.mem_cons_self
  have hd : Spec.Sha512.bytesAt s.mem (s.sp + 192) 64 = expanded := by rw [hc.sp]; exact he
  refine WP.mono (PublicKey.prune_ok fr hd) fun u ⟨hu, hf, hs⟩ => ?_
  have hcu := prune_ctx hc hu hf
  rw [hc.sp] at hf hs
  refine WP.mono (prefix_ok hcu.sp (by rw [hcu.wr]; exact List.mem_cons_self))
    fun t ⟨ht, hft, hp⟩ => ⟨prefix_ctx hcu ht hft, ?_, ?_⟩
  · have keep := single_frame_bytes (L := L) hft (d := 32) (by decide) (by decide) (by decide)
    change Spec.Ed25519.bytesAt t.mem (L.E + 32) 32 = Spec.Ed25519.bytesAt u.mem (L.E + 32) 32 at keep
    rw [keep]
    have sc := Proof.Ed25519.bytesAt_encodeLE u.mem (L.E + 32) 32
    rw [hs] at sc
    exact sc
  · rw [hp]
    have keep := single_frame_bytes (L := L) (e := 32) (k := 32) hf (d := 224)
      (by decide) (by decide) (by decide)
    change Spec.Ed25519.bytesAt u.mem (L.E + 224) 32 = Spec.Ed25519.bytesAt s.mem (L.E + 224) 32 at keep
    rw [keep, ← he, Proof.Ed25519.signatureBytes_drop]
    rw [BitVec.add_assoc, show (192 : BitVec 64) + BitVec.ofNat 64 32 = (224 : BitVec 64) from rfl]

def scalar (E : List Byte) : List Byte := Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune E)
def nonce (L : Lay) (E : List Byte) (m : Mem) : List Byte := Spec.Ed25519.scalarReduce (Spec.Sha512.sha512
  (E.drop 32 ++ Spec.Ed25519.bytesAt m L.msg L.len.toNat))

/-- The digest `E` left at `frame 192` by the first step of signing. -/
def DigestReady (L : Lay) (E : List Byte) (t : State) : Prop :=
  Spec.Ed25519.bytesAt t.mem (L.E + 192) 64 = E

structure SecretReady (L : Lay) (E : List Byte) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem (L.E + 32) 32 = scalar E
  prefixBytes : Spec.Ed25519.bytesAt t.mem (L.E + 64) 32 = E.drop 32

theorem secret_ok (hc : Ctx L g vec m₀ s) {E : List Byte} (hd : DigestReady L E s) :
    WP isa (.block saveSecret) s fun t => Ctx L g vec m₀ t ∧ SecretReady L E t :=
  WP.mono (saveSecret_ok hc hd) fun _ ⟨ht, hs, hp⟩ => ⟨ht, hs, hp⟩

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g : Reg → BitVec 64} {vec : VReg → BitVec 128} {m₀ : Mem} {s : State}

structure NonceReady (L : Lay) (E : List Byte) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem (L.E + 32) 32 = scalar E
  nonce : Spec.Ed25519.bytesAt t.mem (L.E + 96) 32 = nonce L E m
  point : Spec.Ed25519.bytesAt t.mem (L.out) 32 = Spec.Ed25519.scalarBase (SignCached.nonce L E m)

theorem nonce_ok [VG.Proof.Ed25519.AArch64.Divstep.Sound] (b : Backend) (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀) {E : List Byte} (hs : SecretReady L E s)
    (hsy : s.syms Impl.Ed25519.AArch64.combSym = L.T) :
    WP isa (nonceCode b.code b.suffix) s fun t => Ctx L g vec m₀ t ∧ NonceReady L E m₀ t := by
  refine WP.seq (WP.mono_syms (hashNonce_ok b hc hL ha) fun u ⟨hu, fu, du⟩ syu => ?_)
  rw [hs.prefixBytes] at du
  have su := (hash_field_bytes hL fu (d := 32) (by decide)).trans hs.scalar
  refine WP.seq (WP.mono_syms (reduce_step hu hL ha 96 (by decide)) fun v ⟨hv, fv, nv⟩ syv => ?_)
  rw [du] at nv
  have sv := (reduce_field_bytes hL fv (d := 32) (by decide) (by decide) (by decide)).trans su
  refine WP.mono (base_step hv hL ha (by rw [syv, syu]; exact hsy)) fun t ⟨ht, ft, pt⟩ => ⟨ht, ?_, ?_, ?_⟩
  · exact (base_field_bytes hL ft (d := 32) (by decide)).trans sv
  · exact (base_field_bytes hL ft (d := 96) (by decide)).trans nv
  · change Spec.Ed25519.bytesAt v.mem (L.E + 96) 32 = _ at nv
    rw [nv] at pt
    exact pt

theorem challenge_ok (b : Backend) (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {E : List Byte} (hs : NonceReady L E m₀ s) {seed : List Byte} (hE : E = Spec.Sha512.sha512 seed)
    (hk : Spec.Ed25519.bytesAt m₀ (L.pk) 32 = Spec.Ed25519.publicKey seed) :
    WP isa (challengeCode b.code b.suffix) s fun t => Ctx L g vec m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out) 64 = Spec.Ed25519.sign seed
        (Spec.Ed25519.bytesAt m₀ (L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (hashChallenge_ok b hc hL ha) fun u ⟨hu, fu, du⟩ => ?_)
  rw [hs.point] at du
  have su := (hash_field_bytes hL fu (d := 32) (by decide)).trans hs.scalar
  have nu := (hash_field_bytes hL fu (d := 96) (by decide)).trans hs.nonce
  have pu := (hash_out_bytes hL fu).trans hs.point
  refine WP.seq (WP.mono (reduce_step hu hL ha 128 (by decide)) fun v ⟨hv, fv, cv⟩ => ?_)
  rw [du] at cv
  have sv := (reduce_field_bytes hL fv (d := 32) (by decide) (by decide) (by decide)).trans su
  have nv := (reduce_field_bytes hL fv (d := 96) (by decide) (by decide) (by decide)).trans nu
  have pv := (reduce_out_bytes hL fv (by decide)).trans pu
  refine WP.mono (mul_step hv hL ha) fun t ⟨ht, ft, st⟩ => ⟨ht, ?_⟩
  change Spec.Ed25519.bytesAt v.mem (L.E + 96) 32 = _ at nv
  change Spec.Ed25519.bytesAt v.mem (L.E + 128) 32 = _ at cv
  change Spec.Ed25519.bytesAt v.mem (L.E + 32) 32 = _ at sv
  rw [nv, cv, sv] at st
  have pt := (mul_out_bytes hL ft).trans pv
  rw [Proof.Ed25519.signatureBytes_split, pt]
  change Spec.Ed25519.scalarBase (nonce L E m₀) ++ Spec.Ed25519.bytesAt t.mem (L.out + (32 : BitVec 64)) 32 = _
  rw [st]
  subst hE
  exact Proof.Ed25519.sign_pipeline _ _ _ hk

theorem wipe_ok (hc : Ctx L g vec m₀ s) (hL : L.Ok) :
    WP isa (.block wipe) s fun t => Ctx L g vec m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out) 64 = Spec.Ed25519.bytesAt s.mem (L.out) 64 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 4) (count := 28) (by decide))
    fun t ⟨ht, hf, _⟩ => ⟨ht, ?_⟩
  refine frame_bytes hf L.OUT ?_ (by change 64 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 8 * 4 + 8 * 28 ≤ 256))).symm

/-- Signing after a first step `first` that leaves the digest `E` of `seed` at `frame 192`. -/
theorem bodyFrom_ok [VG.Proof.Ed25519.AArch64.Divstep.Sound] (b : Backend) {first : Prog isa}
    {E : List Byte} (hfirst : WP isa first s fun t => Ctx L g vec m₀ t ∧ DigestReady L E t)
    (hL : L.Ok) (ha : Arguments L m₀) {seed : List Byte} (hE : E = Spec.Sha512.sha512 seed)
    (hk : Spec.Ed25519.bytesAt m₀ (L.pk) 32 = Spec.Ed25519.publicKey seed)
    (hsy : s.syms Impl.Ed25519.AArch64.combSym = L.T) :
    WP isa (bodyFrom first b.code b.suffix) s fun t => Ctx L g vec m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out) 64 = Spec.Ed25519.sign seed
        (Spec.Ed25519.bytesAt m₀ (L.msg) L.len.toNat) := by
  have hsec : WP isa (.seq first (.block saveSecret)) s fun t => Ctx L g vec m₀ t ∧ SecretReady L E t :=
    WP.seq (WP.mono hfirst fun _ ⟨hd, ed⟩ => secret_ok hd ed)
  refine WP.seq (WP.mono_syms hsec fun u ⟨hu, su⟩ syu => ?_)
  refine WP.seq (WP.mono (nonce_ok b hu hL ha su (by rw [syu]; exact hsy)) fun v ⟨hv, nv⟩ => ?_)
  refine WP.seq (WP.mono (challenge_ok b hv hL ha nv hE hk) fun w ⟨hw, sw⟩ => ?_)
  exact WP.mono (wipe_ok hw hL) fun t ⟨ht, same⟩ => ⟨ht, same.trans sw⟩

end VG.Proof.Ed25519.AArch64.SignCached

end

end

/-! # Constant time of signing after its first step (AArch64), and a witness's seed and key -/

@[expose] public section

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTBody`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTHash`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem init_call_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L [(.x0, .caller 5 0)]))
      (.call Spec.Sha512.init512Api.name (Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512))
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb (Proof.Sha512.AArch64.Stream.init_verified _).1
    (Proof.Sha512.AArch64.Stream.init_verified _).2.1 (Whole.depth_of_noFrames rfl)
  · intro g v m t _ _ _ hs
    have h := hs (.x0, .caller 5 0) (by simp)
    change t.gpr .x0 = L.scr + 0#64 at h
    rw [BitVec.add_zero] at h
    exact init_ready h
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨call_gpr_eq (p := (.x0, .caller 5 0)) h (by simp) (by decide), hsp⟩

theorem update_call_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (count : Nat) (p n : Value)
    (hi : Input L (value L p) (value L n)) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L
      [(.x0, .caller 5 0), (.x1, .const count), (.x2, p), (.x3, n), (.x4, .caller 5 192)]))
      (.call ("vg_sha512_update_scratch" ++ backend.suffix) backend.update)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb backend.update_verified.1 backend.update_verified.2.1 (Whole.update_depth backend)
  · intro g v m t hc _ _ hs
    have a0 := hs (.x0, .caller 5 0) (by simp)
    change t.gpr .x0 = L.scr + 0#64 at a0
    rw [BitVec.add_zero] at a0
    exact update_ready hL hc.sp hi ⟨a0, hs (.x1, .const count) (by simp), hs (.x2, p) (by simp),
      hs (.x3, n) (by simp), hs (.x4, .caller 5 192) (by simp)⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨call_gpr_eq (p := (.x0, .caller 5 0)) h (by simp) (by decide),
      call_gpr_eq (p := (.x1, .const count)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x2, p)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x3, n)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x4, .caller 5 192)) h (by simp) (by decide), hsp⟩

theorem finalize_call_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (n : Nat) (b : Bool) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L
      [(.x0, .caller 5 0), (.x1, if b then .caller 4 n else .const n),
        (.x2, .frame 192), (.x3, .caller 5 192)]))
      (.call ("vg_sha512_finalize_scratch" ++ backend.suffix) backend.finalize)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb backend.finalize_verified.1 backend.finalize_verified.2.1 (Whole.finalize_depth backend)
  · intro g v m t hc _ _ hs
    have a0 := hs (.x0, .caller 5 0) (by simp)
    change t.gpr .x0 = L.scr + 0#64 at a0
    rw [BitVec.add_zero] at a0
    exact finalize_ready hL hc.sp ⟨a0, hs (.x1, if b then .caller 4 n else .const n) (by simp),
      hs (.x2, .frame 192) (by simp), hs (.x3, .caller 5 192) (by simp)⟩
  · intro a c ar aw br bw h
    have hsp := two_sp h
    exact ⟨call_gpr_eq (p := (.x0, .caller 5 0)) h (by simp) (by decide),
      call_gpr_eq (p := (.x1, if b then .caller 4 n else .const n)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x2, .frame 192)) h (by simp) (by decide),
      call_gpr_eq (p := (.x3, .caller 5 192)) h (by simp) (by decide), hsp⟩

theorem init_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) init
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.x0, .caller 5 0)] (by decide) (by decide)
    (by decide) (by taint_decide)).seq (init_call_ct hL ha hb)

theorem update_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (count : Nat) (p n : Value) (hc : count < 65536) (hp : Whole.valid p) (hn : Whole.valid n)
    (hi : Input L (value L p) (value L n))
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup
      [(.x0, .caller 5 0), (.x1, .const count), (.x2, p), (.x3, n), (.x4, .caller 5 192)])) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)
      (update backend.code backend.suffix (setup
        [(.x0, .caller 5 0), (.x1, .const count), (.x2, p), (.x3, n), (.x4, .caller 5 192)]))
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hv : ∀ x : Reg × Value, x ∈ [(.x0, .caller 5 0), (.x1, .const count),
      (.x2, p), (.x3, n), (.x4, .caller 5 192)] → Whole.valid x.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl | rfl)
    · decide
    · exact hc
    · exact hp
    · exact hn
    · decide
  exact (setup_ct hL ha hb _ (by simp) hv (by simp [preserved]) ht).seq
    (update_call_ct backend hL ha hb count p n hi)

theorem finalize_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (n : Nat) (hn : n < 4096) (b : Bool)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (finalizeArgs n b)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (finalize backend.code backend.suffix n b)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hv : Whole.valid (if b then .caller 4 n else .const n) := by
    cases b <;> simp [Whole.valid] <;> omega_using [hn]
  have hvall : ∀ p : Reg × Value, p ∈ [(.x0, .caller 5 0),
      (.x1, if b then .caller 4 n else .const n), (.x2, .frame 192), (.x3, .caller 5 192)] → Whole.valid p.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl)
    · decide
    · exact hv
    · decide
    · decide
  exact (setup_ct hL ha hb _ (by simp) hvall (by simp [preserved]) ht).seq
    (finalize_call_ct backend hL ha hb n b)

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTHashPipeline`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem hashNonce_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (hashNonce backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hp : Input L (value L (.frame 64)) (value L (.const 32)) := prefix_input hL
  have hm : Input L (value L (.caller 3 0)) (value L (.caller 4 0)) := by
    change Input L (L.msg + 0#64) (L.len + 0#64)
    rw [BitVec.add_zero, BitVec.add_zero]
    exact message_input hL
  exact (init_ct hL ha hb).seq ((update_ct backend hL ha hb 0 (.frame 64) (.const 32)
    (by decide) (by decide) (by decide) hp (by taint_decide)).seq
    ((update_ct backend hL ha hb 32 (.caller 3 0) (.caller 4 0)
      (by decide) (by decide) (by decide) hm (by taint_decide)).seq
      (finalize_ct backend hL ha hb 32 (by decide) true (by taint_decide))))

theorem hashChallenge_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (hashChallenge backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have ho : Input L (value L (.caller 0 0)) (value L (.const 32)) := by
    change Input L (L.out + 0#64) 32#64
    rw [BitVec.add_zero]
    exact point_input hL
  have hk : Input L (value L (.caller 2 0)) (value L (.const 32)) := by
    change Input L (L.pk + 0#64) 32#64
    rw [BitVec.add_zero]
    exact key_input hL
  have hm : Input L (value L (.caller 3 0)) (value L (.caller 4 0)) := by
    change Input L (L.msg + 0#64) (L.len + 0#64)
    rw [BitVec.add_zero, BitVec.add_zero]
    exact message_input hL
  exact (init_ct hL ha hb).seq ((update_ct backend hL ha hb 0 (.caller 0 0) (.const 32)
    (by decide) (by decide) (by decide) ho (by taint_decide)).seq
    ((update_ct backend hL ha hb 32 (.caller 2 0) (.const 32)
      (by decide) (by decide) (by decide) hk (by taint_decide)).seq
      ((update_ct backend hL ha hb 64 (.caller 3 0) (.caller 4 0)
        (by decide) (by decide) (by decide) hm (by taint_decide)).seq
        (finalize_ct backend hL ha hb 64 (by decide) true (by taint_decide)))))

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTPrimitives`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem reduce_call_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (d : Nat) (hd : d + 32 ≤ 256) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L [(.x0, .frame d), (.x1, .frame 192), (.x2, .caller 5 0)]))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.AArch64.scalarReduce)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb scalarReduce_ok scalarReduce_ct (Whole.depth_of_noFrames reduce_noFrames)
  · intro g v m t _ _ _ hs
    have a0 := hs (.x0, .frame d) (by simp)
    have a1 := hs (.x1, .frame 192) (by simp)
    have a2 := hs (.x2, .caller 5 0) (by simp)
    change t.gpr .x2 = L.scr + 0#64 at a2
    rw [BitVec.add_zero] at a2
    exact reduce_ready hL hd ⟨a0, a1, a2⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.x0, .frame d)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x1, .frame 192)) h (by simp) (by decide),
      call_gpr_eq (p := (.x2, .caller 5 0)) h (by simp) (by decide)⟩

theorem base_call_ct [VG.Proof.Ed25519.AArch64.Divstep.Sound] (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L [(.x0, .caller 0 0), (.x1, .frame 96), (.x2, .caller 5 0)]))
      (.call "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb scalarBase_ok scalarBase_ct (Whole.depth_of_noFrames base_noFrames)
  · intro g v m t _ _ _ hs
    have a0 := hs (.x0, .caller 0 0) (by simp)
    change t.gpr .x0 = L.out + 0#64 at a0
    rw [BitVec.add_zero] at a0
    have a1 := hs (.x1, .frame 96) (by simp)
    have a2 := hs (.x2, .caller 5 0) (by simp)
    change t.gpr .x2 = L.scr + 0#64 at a2
    rw [BitVec.add_zero] at a2
    exact base_ready hL ⟨a0, a1, a2⟩ ‹_› ‹_›
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.x0, .caller 0 0)) h (by simp) (by decide),
      call_gpr_eq (p := (.x1, .frame 96)) h (by simp) (by decide),
      call_gpr_eq (p := (.x2, .caller 5 0)) h (by simp) (by decide),
      h.2.2.2.2.1.trans h.2.2.2.2.2.symm⟩

theorem mul_call_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L [(.x0, .caller 0 32), (.x1, .frame 96), (.x2, .frame 128), (.x3, .frame 32), (.x4, .caller 5 0)]))
      (.call "vg_ed25519_scalar_mul_add" Impl.Ed25519.AArch64.scalarMulAdd)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb scalarMulAdd_ok scalarMulAdd_ct (Whole.depth_of_noFrames mul_noFrames)
  · intro g v m t _ _ _ hs
    have a0 := hs (.x0, .caller 0 32) (by simp)
    have a1 := hs (.x1, .frame 96) (by simp)
    have a2 := hs (.x2, .frame 128) (by simp)
    have a3 := hs (.x3, .frame 32) (by simp)
    have a4 := hs (.x4, .caller 5 0) (by simp)
    change t.gpr .x4 = L.scr + 0#64 at a4
    rw [BitVec.add_zero] at a4
    exact mul_ready hL ⟨a0, a1, a2, a3, a4⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.x0, .caller 0 32)) h (by simp) (by decide),
      call_gpr_eq (p := (.x1, .frame 96)) h (by simp) (by decide),
      call_gpr_eq (p := (.x2, .frame 128)) h (by simp) (by decide),
      call_gpr_eq (p := (.x3, .frame 32)) h (by simp) (by decide),
      call_gpr_eq (p := (.x4, .caller 5 0)) h (by simp) (by decide)⟩

theorem saveSecret_ct :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block saveSecret)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_sp h) (by taint_decide)) ?_ ?_
  · intro t hc _
    exact WP.mono (saveSecret_ok hc rfl) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (saveSecret_ok hc rfl) fun _ h => ⟨h.1, trivial⟩

theorem wipe_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block wipe)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_sp h) (by taint_decide)) ?_ ?_
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem reduce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (d : Nat) (hd : d + 32 ≤ 256)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (reduceArgs d)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (reduce d)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hv : Whole.valid (.frame d) := by change d < 4096; omega_using [hd]
  have hvall : ∀ p : Reg × Value, p ∈ [(.x0, .frame d), (.x1, .frame 192), (.x2, .caller 5 0)] → Whole.valid p.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    · exact hv
    · decide
    · decide
  exact (setup_ct hL ha hb _ (by simp) hvall (by simp [preserved]) ht).seq
    (reduce_call_ct hL ha hb d hd)

theorem base_ct [VG.Proof.Ed25519.AArch64.Divstep.Sound] (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)
      (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.x0, .caller 0 0), (.x1, .frame 96), (.x2, .caller 5 0)]
    (by decide) (by decide) (by decide) (by taint_decide)).seq
    (base_call_ct hL ha hb)

theorem mul_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)
      (callWith mulAddArgs "vg_ed25519_scalar_mul_add" Impl.Ed25519.AArch64.scalarMulAdd)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.x0, .caller 0 32), (.x1, .frame 96), (.x2, .frame 128),
    (.x3, .frame 32), (.x4, .caller 5 0)]
    (by decide) (by decide) (by decide) (by taint_decide)).seq
    (mul_call_ct hL ha hb)

/-- Signing after a first step related to itself, as the copy of a cached digest is. -/
theorem bodyFrom_ct [VG.Proof.Ed25519.AArch64.Divstep.Sound] (backend : Backend) {first : Prog isa}
    (hfirst : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) first
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True))
    (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (bodyFrom first backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (hfirst.seq saveSecret_ct).seq
    (((hashNonce_ct backend hL ha hb).seq ((reduce_ct hL ha hb 96 (by decide) (by taint_decide)).seq
      (base_ct hL ha hb))).seq
      (((hashChallenge_ct backend hL ha hb).seq ((reduce_ct hL ha hb 128 (by decide) (by taint_decide)).seq
        (mul_ct hL ha hb))).seq (wipe_ct hL)))

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CT`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

theorem lay_eq {n : Nat} {key : State → Prop} {post : State → State → Prop} {s t : State}
    (hp : (signLocalWith n key post).pub s t) : lay n s = lay n t := by
  obtain ⟨sp, h0, h1, h2, h3, h4, h5, hsy⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2, h3, h4, h5, hsy]

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.Contract`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.SignCached.Sat`. -/
section
/-! A satisfiability witness with a matching seed and cached public key. -/
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64

def satSeed : List Byte := Spec.Ed25519.bytesAt (fun _ => 0) 0x2000 32
def satKey : List Byte := Spec.Ed25519.publicKey satSeed

theorem satKey_length : satKey.length = 32 := by
  simp only [satKey, Spec.Ed25519.publicKey, Spec.Ed25519.encodePoint, Spec.Ed25519.encodeLE,
    List.length_map, List.length_range]

end VG.Proof.Ed25519.AArch64.SignCached
end
end

end

end

/-! # Complete Ed25519 signing with the seed's cached SHA-512 digest (AArch64)

`codeExpanded` is `bodyFrom PublicKey.copyExpanded`: the digest at the second argument is
copied to `frame 192`, where `bodyFrom` reads it. The rest is proven by `bodyFrom_ok` and
`bodyFrom_ct`. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached VG.Impl.Ed25519.AArch64.Whole
open VG.Impl.Ed25519.AArch64.PublicKey (copyArgs copyWords copyExpanded)
open VG.Proof.Ed25519 (sign_of_sha512_eq sha512_length)

variable {L : Lay} {g : Reg → BitVec 64} {vec : VReg → BitVec 128} {m₀ : Mem} {s : State}

/-- The digest at `seed`, read only and outside what signing writes. -/
theorem copy_src (hL : L.Ok) (h64 : L.seedLen = 64) : Whole.CopySrc L.E L.inputs L.outputs L.seed := by
  have hs : (⟨L.seed, 64⟩ : Region) = L.SEED := by rw [Lay.SEED, h64]
  refine ⟨hs ▸ by simp [Lay.inputs], fun r hr => ?_⟩
  have hi : L.SEED ∈ L.inputs := by simp [Lay.inputs]
  rw [hs]
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hL.os _ hi).symm
  · exact hL.sc _ hi
  · exact (hL.ks _ hi).symm
  · exact (hL.ck _ hi).symm

/-- The copy's arguments: the digest in `x1`, `frame 192` in `x15`. -/
theorem copy_args {t : State} (ho : OutArgs L copyArgs t) :
    t.gpr .x1 = L.seed ∧ t.gpr .x15 = L.E + BitVec.ofNat 64 192 := by
  have a1 := ho (.x1, .caller 1 0) (by simp [copyArgs])
  change t.gpr .x1 = L.seed + 0#64 at a1
  rw [BitVec.add_zero] at a1
  exact ⟨a1, ho (.x15, .frame 192) (by simp [copyArgs])⟩

theorem copy_ok (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (h64 : L.seedLen = 64) :
    WP isa copyExpanded s fun t =>
      Ctx L g vec m₀ t ∧ DigestReady L (Spec.Ed25519.bytesAt m₀ L.seed 64) t := by
  refine WP.seq (WP.mono (args_ok hc hL ha (args := copyArgs) (by decide) (by decide)
    (by simp [copyArgs, preserved])) fun t ⟨ht, _, ho⟩ => ?_)
  have ⟨a1, a15⟩ := copy_args ho
  exact Whole.copy_digest (copy_src hL h64) ⟨ht, a1, a15, fun _ h => absurd h (Nat.not_lt_zero _)⟩

variable {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem copyWords_ct :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L copyArgs)) (.block copyWords) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.x1, .x15]) (fun a b h => ⟨two_sp h, fun r hr => by
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact args_eq h (p := (.x1, .caller 1 0)) (by simp [copyArgs])
    · exact args_eq h (p := (.x15, .frame 192)) (by simp [copyArgs])⟩) (by taint_decide)

theorem copy_ct (hL : L.Ok) (h64 : L.seedLen = 64) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) copyExpanded
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine (setup_ct hL ha hb copyArgs (by decide) (by decide) (by simp [copyArgs, preserved])
    (by taint_decide)).seq (two_wp copyWords_ct ?_ ?_)
  · intro t hc ho
    have ⟨a1, a15⟩ := copy_args ho
    exact WP.mono (Whole.copy_digest (copy_src hL h64) ⟨hc, a1, a15, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun _ h => ⟨h.1, trivial⟩
  · intro t hc ho
    have ⟨a1, a15⟩ := copy_args ho
    exact WP.mono (Whole.copy_digest (copy_src hL h64) ⟨hc, a1, a15, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun _ h => ⟨h.1, trivial⟩

/-! ## The expanded-key entry point -/

/-- Signing with the seed's digest at `x1` and its public key at `x2`. -/
def signLocalE : Contract isa := signLocalWith 64
  (fun s => ∃ seed : List Byte, seed.length = 32 ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 64 = Spec.Sha512.sha512 seed ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32 = Spec.Ed25519.publicKey seed)
  (fun s t => ∀ seed : List Byte, seed.length = 32 →
    Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 64 = Spec.Sha512.sha512 seed →
    Spec.Ed25519.bytesAt t.mem (s.gpr .x0) 64 = Spec.Ed25519.sign seed
      (Spec.Ed25519.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat))

theorem expanded_key {s : State} (h : signLocalE.pre s) :
    ∃ seed : List Byte, seed.length = 32 ∧
      Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 64 = Spec.Sha512.sha512 seed ∧
      Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32 = Spec.Ed25519.publicKey seed := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, _⟩ := h
  exact hk

theorem bodyE_depth (v : Whole.Backend) :
    (bodyFrom copyExpanded v.code v.suffix).aarch64Depth ≤ 1 := by
  have hu := Whole.update_depth v
  have hf := Whole.finalize_depth v
  change (Impl.Sha512.AArch64.Stream.updateWith v.suffix v.code).aarch64Depth ≤ 1 at hu
  change (Impl.Sha512.AArch64.Stream.finalizeWith v.suffix v.code).aarch64Depth ≤ 1 at hf
  have hr := Whole.depth_zero_of_noFrames reduce_noFrames
  have hb := Whole.depth_zero_of_noFrames base_noFrames
  have hm := Whole.depth_zero_of_noFrames mul_noFrames
  simp only [bodyFrom, copyExpanded, nonceCode, challengeCode, hashNonce, hashChallenge,
    init, update, finalize, reduce, Impl.Ed25519.AArch64.Whole.callWith, Code.aarch64Depth, Nat.max_le,
    Impl.Sha512.AArch64.Stream.init, hr, hb, hm]
  omega_using [hu, hf]

theorem signE_ok [VG.Proof.Ed25519.AArch64.Divstep.Sound] (v : Whole.Backend) {s : State}
    (h : signLocalE.pre s) :
    WP isa (codeExpanded v.code v.suffix) s fun u => abiPreserved s u ∧ signLocalE.post s u := by
  obtain ⟨seed, -, hE, hk⟩ := expanded_key h
  have hw := Whole.wrap_ok (bodyE_depth v) (entry_below h) (entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m (s.gpr .x1) 64 = Spec.Sha512.sha512 seed ∧
      Spec.Ed25519.bytesAt m' (s.gpr .x0) 64 = Spec.Ed25519.sign seed
        (Spec.Ed25519.bytesAt m (s.gpr .x3) (s.gpr .x4).toNat))
    (hP := fun _ _ _ _ f hq => ⟨hq.1, (List.map_congr_left fun i hi => VG.AArch64.lost_byte f
      ((entry_writes h ⟨s.gpr .x0, 64⟩ (by rw [h.2.1]; simp)).symm.sub_right
        (VG.AArch64.below_sub (by decide) (by decide))) (List.mem_range.mp hi)).trans hq.2⟩)
    (fun p hp => by
      have hf := Whole.saved_frame hp
      have hE' := (entry_input h hf (r := ⟨s.gpr .x1, 64⟩) (by rw [h.1]; simp)
        (by change 64 ≤ 2 ^ 64; decide)).trans hE
      have hk' := (entry_input h hf (r := ⟨s.gpr .x2, 32⟩) (by rw [h.1]; simp)
        (by change 32 ≤ 2 ^ 64; decide)).trans hk
      have hc : Ctx (lay 64 s) s.gpr s.v p.mem _ := entry_ctx h hp
      have hL : (lay 64 s).Ok := lay_ok h (by decide)
      have ha : Arguments (lay 64 s) p.mem := entry_args h hp
      exact WP.mono (bodyFrom_ok v (copy_ok hc hL ha rfl) hL ha hE' hk' (entry_syms hp))
        fun u huo => ⟨by
          simpa only [Whole.bodyRd, h.1, Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.PK, Lay.MSG,
            Lay.OUT, Lay.SCR, Lay.ARGS, Lay.TB, Whole.ARGS, show BitVec.ofNat 64 256 = (256 : Addr) from rfl,
            lay, h.2.1, List.cons_append, List.nil_append] using huo.1, hE', huo.2⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hE', hp⟩ => ⟨hu, fun seed' _ hs' => ?_⟩
  have hm := entry_input h hf (r := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩) (by rw [h.1]; simp)
    (Nat.le_of_lt (s.gpr .x4).isLt)
  change Spec.Ed25519.bytesAt u.mem (s.gpr .x0) 64 = _
  rw [hp, hm]
  exact sign_of_sha512_eq (hE.symm.trans hs') _

theorem signE_ct [VG.Proof.Ed25519.AArch64.Divstep.Sound] (v : Whole.Backend) :
    ConstantTime isa signLocalE.pre signLocalE.pub (codeExpanded v.code v.suffix) := by
  refine Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    obtain ⟨seed, -, hE, hk⟩ := expanded_key hs
    have hf := Whole.saved_frame hp
    have hE' := (entry_input hs hf (r := ⟨s.gpr .x1, 64⟩) (by rw [hs.1]; simp)
      (by change 64 ≤ 2 ^ 64; decide)).trans hE
    have hk' := (entry_input hs hf (r := ⟨s.gpr .x2, 32⟩) (by rw [hs.1]; simp)
      (by change 32 ≤ 2 ^ 64; decide)).trans hk
    have hL := lay_ok hs (by decide)
    have ha := entry_args hs hp
    exact WP.mono (bodyFrom_ok v (copy_ok (entry_ctx hs hp) hL ha rfl) hL ha hE' hk' (entry_syms hp))
      fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq (n := 64) hp
    have hq : Ctx (lay 64 s) t.gpr t.v q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay 64 s) q.mem := he ▸ entry_args ht hqb
    have hqs : (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)).syms Impl.Ed25519.AArch64.combSym =
        (lay 64 s).T := he ▸ entry_syms hqb
    have hL := lay_ok hs (by decide)
    have hpa' := entry_args hs hpa
    exact ⟨(bodyFrom_ct v (copy_ct hL rfl hpa' hqa) hL hpa' hqa _ _ _ _ _ _
      ⟨entry_ctx hs hpa, hq, trivial, trivial, entry_syms hpa, hqs⟩ ea eb).1, trivial⟩

/-! ## A witness, and the shared contract -/

open VG.Impl.Ed25519.AArch64 (combSym combWords combConsts)

def satDigest : List Byte := Spec.Sha512.sha512 satSeed

theorem satSeed_length : satSeed.length = 32 := by
  simp only [satSeed, Spec.Ed25519.bytesAt, List.length_map, List.length_range]

/-- The seed's digest at `0x2000` and its public key at `0x3000`. -/
def satMemE (a : Addr) : Byte :=
  if a.toNat < 0x2000 then 0
  else if a.toNat < 0x3000 then satDigest[a.toNat - 0x2000]?.getD 0
  else satKey[a.toNat - 0x3000]?.getD 0

theorem sat_digest : Spec.Ed25519.bytesAt satMemE 0x2000 64 = satDigest := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satDigest, sha512_length]
  · intro i hi hj
    have hi' : i < 64 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
      change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
      omega_using [hi']
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, satMemE, ha,
      show ¬ 0x2000 + i < 0x2000 from by omega_using [], show 0x2000 + i < 0x3000 from by omega_using [hi'], ite_false, ite_true,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

theorem sat_keyE : Spec.Ed25519.bytesAt satMemE 0x3000 32 = satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satKey_length]
  · intro i hi hj
    have hi' : i < 32 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega_using [hi']
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, satMemE, ha,
      show ¬ 0x3000 + i < 0x2000 from by omega_using [], show ¬ 0x3000 + i < 0x3000 from by omega_using [], ite_false,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

/-- `satMemE`, and the comb's tables at `0x100000` (irreducible: unfolding it in a definitional
check would evaluate the tables). -/
@[irreducible] def satMemTE : Mem := fun a =>
  if 0x100000 ≤ a.toNat then constMem 0x100000 combWords a else satMemE a

theorem satMemTE_bytes {p : Addr} {n : Nat} (hp : p.toNat + n ≤ 0x100000) :
    Spec.Ed25519.bytesAt satMemTE p n = Spec.Ed25519.bytesAt satMemE p n := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  unfold satMemTE
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_using [hp, hi'])]
  simp only [show ¬ 0x100000 ≤ (p.toNat + i) % 2 ^ 64 by omega_using [hp, hi'], ite_false]

theorem satMemTE_held : ∀ i < combWords.length,
    satMemTE.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  intro i hi
  have hl := combWords_length
  rw [← constMem_held 0x100000 combWords (by omega_using [hl]) i hi]
  refine Mem.readW_congr fun b hb => ?_
  have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b).toNat = 0x100000 + 8 * i + b := by
    have h0 : (0x100000 : Addr).toNat = 0x100000 := rfl
    rw [Offset.add_add, BitVec.toNat_add, BitVec.toNat_ofNat, h0,
      Nat.mod_eq_of_lt (a := 8 * i + b) (by omega_using [hi, hl, hb])]
    omega_using [hi, hl, hb]
  unfold satMemTE
  simp only [e, show 0x100000 ≤ 0x100000 + 8 * i + b by omega_using [], ↓reduceIte]

def satStateE : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x5 => 0x5000 | _ => 0
  sp := 0x9000
  mem := satMemTE
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 32⟩, ⟨0x4000, 0⟩, ⟨0x100000, 49152⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_preE {s : State} (hsp : 352 ≤ s.sp.toNat)
    (hrd : s.rd = [⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, 32⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩,
      ⟨s.syms combSym, 8 * combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 64⟩, ⟨s.gpr .x5, 8192⟩])
    (hheld : ∀ i < combWords.length,
      s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0)
    (hfit : (s.syms combSym).toNat + 8 * combWords.length ≤ 2 ^ 64)
    (hdw : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms combSym, 8 * combWords.length⟩ r)
    (hds : Region.Disjoint ⟨s.syms combSym, 8 * combWords.length⟩ ⟨s.sp - 352#64, 352⟩)
    (hal : (s.syms combSym).toNat % 64 = 0)
    (hrest : (⟨s.gpr .x0, 64⟩ : Region).Disjoint ⟨s.gpr .x1, 64⟩ ∧
      (⟨s.gpr .x0, 64⟩ : Region).Disjoint ⟨s.gpr .x2, 32⟩ ∧
      (⟨s.gpr .x0, 64⟩ : Region).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩ ∧
      (⟨s.gpr .x0, 64⟩ : Region).Disjoint ⟨s.gpr .x5, 8192⟩ ∧
      (⟨s.gpr .x1, 64⟩ : Region).Disjoint ⟨s.gpr .x5, 8192⟩ ∧
      (⟨s.gpr .x2, 32⟩ : Region).Disjoint ⟨s.gpr .x5, 8192⟩ ∧
      (⟨s.gpr .x3, (s.gpr .x4).toNat⟩ : Region).Disjoint ⟨s.gpr .x5, 8192⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x0, 64⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x1, 64⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x2, 32⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x5, 8192⟩ ∧
      (s.gpr .x0).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 64 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x5).toNat + 8192 ≤ 2 ^ 64)
    (hk : ∃ seed : List Byte, seed.length = 32 ∧
      Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 64 = Spec.Sha512.sha512 seed ∧
      Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32 = Spec.Ed25519.publicKey seed) :
    (Spec.Ed25519.signExpandedContract (AArch64.abi.withConsts combConsts) 352).pre s := by
  sig_pre [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig,
    Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs,
    combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17⟩ := hrest
  exact ⟨hsp, by rw [hrd]; rfl, hheld, hfit, hdw, hds, hal, by rw [hrd]; rfl, hw, r1, r2, r3, r4, r5, r6, r7,
    r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, hk⟩

theorem satE : ∃ s, (Spec.Ed25519.signExpandedContract (AArch64.abi.withConsts combConsts) 352).pre s := by
  have hl := combWords_length
  refine ⟨satStateE, spec_preE (by decide) (by rw [hl]; rfl) rfl satMemTE_held (by rw [hl]; decide) ?_
    (by rw [hl]; exact Region.disjoint_of_sep (by decide)) (by decide) ?_ ⟨satSeed, satSeed_length, ?_, ?_⟩⟩
  · rw [hl]
    simp only [satStateE, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide
  · change Spec.Ed25519.bytesAt satMemTE 0x2000 64 = _
    rw [satMemTE_bytes (by decide), sat_digest]
    rfl
  · change Spec.Ed25519.bytesAt satMemTE 0x3000 32 = _
    rw [satMemTE_bytes (by decide), sat_keyE]
    rfl

theorem signE_implies : signLocalE.Implies
    (Spec.Ed25519.signExpandedContract (AArch64.abi.withConsts combConsts) 352) where
  pre s h := by
    sig_pre [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hsp, hd, held, fit, hdw, hds, -, ht, hw, os, op, om, oc, sc, pc, mc, ko, ks, kp, km, kc,
      no, ns, np, nm, nc, hpk⟩ := h
    refine ⟨?_, hw, os, op, om, oc, sc, pc, mc, ko, ks, kp, km, kc, no, ns, np, nm, nc, hsp, hpk,
      held, fit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hds
  post := by
    sig_implies_post [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig,
      Spec.Ed25519.scratchWords, signLocalE, signLocalWith, below, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts]
  pub := by
    sig_implies_pub [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig,
      Spec.Ed25519.scratchWords, signLocalE, signLocalWith, below, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts]
  sat := satE

theorem signExpanded_verified [VG.Proof.Ed25519.AArch64.Divstep.Sound] (v : Whole.Backend) :
    Verified AArch64.target (codeExpanded v.code v.suffix)
      (Spec.Ed25519.signExpandedContract (AArch64.abi.withConsts combConsts) 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => signE_ok v h) (signE_ct v) (.refl signE_implies.sat_left))
    signE_implies

/-! ## The function, as emitted

`vg_ed25519_sign_expanded` over `v` with its cleanup (`Impl.Ed25519.AArch64.SignCached.Fn.signExpanded`): it meets its contract in
constant time and returns without secret residue (`VerifiedScrubbed`), which
is what its registration binds. What the cleanup needs of the code
(`Scrub.scrubSide`) is proved of the function's own instructions here,
once, with code that does nothing in the place of the compression function,
and of each compression function where it is defined (`Compress.scrub`). -/

open VG.AArch64.Scrub in
private theorem signExpanded_all {p : Instr → Bool} (c : Prog isa) (sfx : String)
    (h0 : sideAll p (Impl.Ed25519.AArch64.SignCached.codeExpanded (.block []) "") = true) (hc : sideAll p c = true) :
    sideAll p (Impl.Ed25519.AArch64.SignCached.codeExpanded c sfx) = true := by
  simp only [Impl.Ed25519.AArch64.SignCached.codeExpanded, Impl.Ed25519.AArch64.SignCached.bodyFrom, Impl.Ed25519.AArch64.SignCached.nonceCode, Impl.Ed25519.AArch64.SignCached.challengeCode, Impl.Ed25519.AArch64.SignCached.hashNonce, Impl.Ed25519.AArch64.SignCached.hashChallenge, Impl.Ed25519.AArch64.SignCached.update, Impl.Ed25519.AArch64.SignCached.finalize, Impl.Ed25519.AArch64.Whole.wrap, Impl.Ed25519.AArch64.Whole.callWith, Impl.Sha512.AArch64.Stream.updateWith, Impl.Sha512.AArch64.Stream.finalizeWith, Impl.MdStream.AArch64.update, Impl.MdStream.AArch64.updateMain, Impl.MdStream.AArch64.updateBody, Impl.MdStream.AArch64.compressN, Impl.MdStream.AArch64.compressWith, Impl.MdStream.AArch64.finalize, Impl.MdStream.AArch64.finalizeMain, Impl.MdStream.AArch64.finalizeBody, Impl.MdStream.AArch64.compressAt, sideAll, Bool.and_eq_true] at h0 ⊢
  simp only [h0, hc, and_self]

open VG.AArch64.Scrub in
private theorem signExpanded_own : calleeSide (Impl.Ed25519.AArch64.SignCached.codeExpanded (.block []) "") Impl.Ed25519.AArch64.SignCached.Fn.signExpandedOwn = true := by
  kernel_rfl

private theorem signExpanded_depth (v : Whole.Backend) : 16 * (Impl.Ed25519.AArch64.SignCached.codeExpanded v.code v.suffix).aarch64Depth ≤ 352 := by
  simp only [Impl.Ed25519.AArch64.SignCached.codeExpanded, Impl.Ed25519.AArch64.SignCached.bodyFrom, Impl.Ed25519.AArch64.SignCached.nonceCode, Impl.Ed25519.AArch64.SignCached.challengeCode, Impl.Ed25519.AArch64.SignCached.hashNonce, Impl.Ed25519.AArch64.SignCached.hashChallenge, Impl.Ed25519.AArch64.SignCached.update, Impl.Ed25519.AArch64.SignCached.finalize, Impl.Ed25519.AArch64.Whole.wrap, Impl.Ed25519.AArch64.Whole.callWith, Impl.Sha512.AArch64.Stream.updateWith, Impl.Sha512.AArch64.Stream.finalizeWith, Impl.MdStream.AArch64.update, Impl.MdStream.AArch64.finalize, Code.aarch64Depth, Instr.frameUnits, v.updateDepth, v.finalizeDepth]
  decide

open VG.AArch64.Scrub in
theorem signExpanded_side (v : Whole.Backend) :
    scrubSide (Impl.Ed25519.AArch64.SignCached.codeExpanded v.code v.suffix) 352 0 (Impl.Ed25519.AArch64.SignCached.Fn.signExpandedOwn.union v.clear) [] = true :=
  scrubSide_union (by decide) (signExpanded_depth v) (by decide)
    (signExpanded_all v.code v.suffix (sideAll_union_left signExpanded_own) (sideAll_union_right v.scrub)) (by decide)

/-- `vg_ed25519_sign_expanded` over `v` as emitted, cleanup included. -/
theorem signExpanded_scrubbed [VG.Proof.Ed25519.AArch64.Divstep.Sound] (v : Whole.Backend) :
    VerifiedScrubbed AArch64.target (Impl.Ed25519.AArch64.SignCached.Fn.signExpanded v.impl) (Spec.Ed25519.signExpandedContract (AArch64.abi.withConsts combConsts) 352) 0 :=
  VG.AArch64.Scrub.verifiedScrubbedAll (api := Spec.Ed25519.signExpandedApi)
    { suffix := v.suffix
      code := Impl.Ed25519.AArch64.SignCached.codeExpanded v.code v.suffix
      verified := signExpanded_verified v } _ Proof.Ed25519.AArch64.Scrub.signExpandedOk (signExpanded_side v)

end VG.Proof.Ed25519.AArch64.SignCached
