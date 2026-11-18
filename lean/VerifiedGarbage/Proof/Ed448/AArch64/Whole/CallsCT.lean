module

public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Sponge
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
import VerifiedGarbage.Proof.Ed448.AArch64.ScalarVerified
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Sponge
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
meta import VerifiedGarbage.Proof.Ed448.AArch64.ScalarVerified
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
meta import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Calls
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Calls
meta import VerifiedGarbage.Proof.Framework.RelCT

/-! ### `Ed448.AArch64.Whole.CT`, which this module and modules that import it used -/

section

/-!
# Ed448's complete operations on AArch64: constant time in the frame's body

Two runs whose public data agree have the same `Env`, so in the frame's body
they are related by `Two`: both satisfy `WCtx` with it (and a predicate `P`
of what the next piece needs), whatever their secrets. The facts about one
run (`M`: what the saved arguments are, from the run's initial memory) hold
in both. A block addresses only the stack (`block_ct`); a call's arguments
(`setupS_ct`) have the same values `val` in both runs, which `callS_ct`
passes to constant-time code whose public data they are (`Whole.callEx`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Whole
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK)

/-- Two runs, each in the frame's body with `V`, and `P`. -/
abbrev Two (V : Env) (g₁ g₂ : Reg → Addr) (v₁ v₂ : VReg → BitVec 128) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) : Prop :=
  (WCtx V g₁ v₁ m₁ a ∧ P a) ∧ (WCtx V g₂ v₂ m₂ b ∧ P b)

/-- The argument registers hold `val`. -/
abbrev Regs (args : List (Reg × Src)) (val : Reg → Addr) (t : State) : Prop :=
  ∀ p ∈ args, t.gpr p.1 = val p.1

variable {V : Env} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem two_sp {P : State → Prop} {a b : State} (h : Two V g₁ g₂ v₁ v₂ m₁ m₂ P a b) : a.sp = b.sp :=
  h.1.1.1.sp.trans h.2.1.1.sp.symm

/-- A block addressed through the stack pointer, with its effect in each run. -/
theorem block_ct {M : Mem → Prop} (h₁ : M m₁) (h₂ : M m₂) {P Q : State → Prop} {is : List Instr}
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block is) hint).isSome = true)
    (hok : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      WP isa (.block is) t fun u => WCtx V g vec m₀ u ∧ Q u) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (.block is) (Two V g₁ g₂ v₁ v₂ m₁ m₂ Q) :=
  VG.Proof.Ed25519.AArch64.Whole.rel_wp
    (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => two_sp h) ht)
    (fun _ h => hok h₁ h.1 h.2) (fun _ h => hok h₂ h.1 h.2)

/-- A call's arguments, the same values `val` in both runs. -/
theorem setupS_ct (hV : V.Ok) {M : Mem → Prop} (h₁ : M m₁) (h₂ : M m₂) {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, srcValid p.2) (hret : retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS args)) hint).isSome = true)
    {P : State → Prop} (val : Reg → Addr)
    (hval : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      ∀ p ∈ args, srcValue V.E t.mem (t.gpr .x0) p.2 = val p.1) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (.block (setupS args))
      (Two V g₁ g₂ v₁ v₂ m₁ m₂ (Regs args val)) :=
  block_ct h₁ h₂ ht fun hm hc hp => WP.mono (wsetup_ok hV hc hn hv hret hr) fun _ ⟨hu, _, hs⟩ =>
    ⟨hu, fun p hq => (hs p hq).trans (hval hm hc hp p hq)⟩

/-- A call, its arguments the same values in both runs, and its effect in each run. -/
theorem callS_ct (hV : V.Ok) {M : Mem → Prop} (h₁ : M m₁) (h₂ : M m₂) {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, srcValid p.2) (hret : retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS args)) hint).isSome = true)
    {P : State → Prop} (val : Reg → Addr)
    (hval : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      ∀ p ∈ args, srcValue V.E t.mem (t.gpr .x0) p.2 = val p.1)
    {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) {rd wr : List Region}
    (pre : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → Regs args val t →
      k.pre (t.callEntry.withRegions rd wr))
    (hcov : Covers (rd ++ wr) (V.ins ++ FR V.E :: V.outs)) (hw : ∀ r ∈ wr, Writable V r)
    (kp : ∀ a b : State, a.sp = b.sp → (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      a.syms V.sym = b.syms V.sym →
      k.pub (a.callEntry.withRegions rd wr) (b.callEntry.withRegions rd wr))
    {Q : State → Prop}
    (hok : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      WP isa (callS args name c) t fun u => WCtx V g vec m₀ u ∧ Q u) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (callS args name c) (Two V g₁ g₂ v₁ v₂ m₁ m₂ Q) := by
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp ?_ (fun _ h => hok h₁ h.1 h.2) (fun _ h => hok h₂ h.1 h.2)
  refine (setupS_ct hV h₁ h₂ hn hv hret hr ht val hval).seq
    (VG.Proof.Ed25519.AArch64.Whole.callEx correct ct fun a b h => ?_)
  let ready : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → Regs args val t →
      VG.Proof.Ed25519.AArch64.Whole.CallReady k V.E V.ins V.outs t := fun hm hc hs =>
    ⟨rd, wr, pre hm hc hs, hcov, fun r hr => (hw r hr).imp And.left id⟩
  obtain ⟨ca, wa⟩ := (ready h₁ h.1.1 h.1.2).covers_state h.1.1.1
  obtain ⟨cb, wb⟩ := (ready h₂ h.2.1 h.2.2).covers_state h.2.1.1
  refine ⟨rd, wr, rd, wr, pre h₁ h.1.1 h.1.2, pre h₂ h.2.1 h.2.2, kp a b (two_sp h) (fun p hp => ?_)
    (h.1.1.2.2.trans h.2.1.2.2.symm), ca, wa, cb, wb⟩
  rw [State.callEntry_gpr _ (hl p hp), State.callEntry_gpr _ (hl p hp), h.1.2 p hp, h.2.2 p hp]

end VG.Proof.Ed448.AArch64.Whole

end

end

/-!
# Ed448's complete operations on AArch64: each call in constant time

The sponge's pieces (`zeroSt_ct`, `kabs_ct`, `kpad_ct`, `ksqz_ct`) and the
calls of the Ed448 primitives (`reduce_ct`, `base_ct`, `mulAdd_ct`), related by `Two`: their arguments have values that agree in
both runs (`val`, or the sponge's positions), which are the callee's public
data, and each run has the effect its correctness lemma gives (`hok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Whole
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK)

variable {V : Env} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}
  {M : Mem → Prop} {d : Nat} {scr : Addr}

theorem regs_get {args : List (Reg × Src)} {val : Reg → Addr} {t : State} (h : Regs args val t) {r : Reg}
    (hr : r ∈ args.map Prod.fst) : t.gpr r = val r := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  exact h p hp

theorem entry_eq {args : List (Reg × Src)} {a b : State}
    (h : ∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) {r : Reg}
    (hr : r ∈ args.map Prod.fst) : a.callEntry.gpr r = b.callEntry.gpr r := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  exact h p hp

/-! ## The sponge -/

theorem zeroSt_ct (hV : V.Ok) (hs : ScrOk V d scr) (h₁ : M m₁) (h₂ : M m₂) {P : State → Prop}
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS [(.x15, .loc d 0)])) hint).isSome = true) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (zeroSt d) (Two V g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp ?_
    (fun _ h => WP.mono (zeroSt_ok hV hs h.1) fun _ hu => ⟨hu.1, trivial⟩)
    (fun _ h => WP.mono (zeroSt_ok hV hs h.1) fun _ hu => ⟨hu.1, trivial⟩)
  refine (setupS_ct hV h₁ h₂ (args := [(.x15, .loc d 0)]) (by simp) (by simp [srcValid, hd.1]; omega_using [hd]) rfl
    (by simp [preserved]) ht (fun _ => scr) fun _ hc _ p hp => ?_).seq ?_
  · rw [List.mem_singleton.mp hp, hs.loc hc, BitVec.add_zero]
  · refine RelCT.taint (A := taint) (Taint.ofRegs [.x15]) (fun a b h => ⟨two_sp h, fun r hr => ?_⟩)
      (by taint_decide)
    simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
    subst hr
    exact (h.1.2 _ List.mem_cons_self).trans (h.2.2 _ List.mem_cons_self).symm

/-- What `absArgs` puts in the registers. -/
def absVal (scr dp : Addr) (n q : Nat) : Reg → Addr
  | .x0 => scr
  | .x1 => BitVec.ofNat 64 136
  | .x2 => BitVec.ofNat 64 q
  | .x3 => dp
  | .x4 => BitVec.ofNat 64 n
  | _ => scr + BitVec.ofNat 64 256

theorem kabs_ct (v : Proof.Sha3.AArch64.Permutation) (hV : V.Ok) (hs : ScrOk V d scr)
    (h₁ : M m₁) (h₂ : M m₂) {src len pos : Src} (hvs : srcValid src) (hvl : srcValid len)
    (hvp : srcValid pos) (hrs : noRet src = true) (hrl : noRet len = true)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS (absArgs d src len pos))) hint).isSome = true)
    {P : State → Prop} {dp : Addr} {n q : Nat}
    (hdp : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t → srcValue V.E t.mem (t.gpr .x0) src = dp)
    (hn : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      srcValue V.E t.mem (t.gpr .x0) len = BitVec.ofNat 64 n)
    (hq : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      srcValue V.E t.mem (t.gpr .x0) pos = BitVec.ofNat 64 q)
    (hql : q < 136) (hnl : n < 2 ^ 64)
    (hin : Within ⟨dp, n⟩ (FR V.E) ∨ ∃ R ∈ V.ins ++ V.outs, Within ⟨dp, n⟩ R)
    (dS : Region.Disjoint ⟨dp, n⟩ (ST scr)) (dK : Region.Disjoint ⟨dp, n⟩ (KS scr))
    (kD : (CK V.E).Disjoint ⟨dp, n⟩) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (kabs v.callee d src len pos)
      (Two V g₁ g₂ v₁ v₂ m₁ m₂ fun u => u.gpr .x0 = BitVec.ofNat 64 ((q + n) % 136)) := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  refine callS_ct hV h₁ h₂ (by simp) (fun p hp => by
      simp only [absArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hvp
      · exact ⟨hd.1, hd.2, by decide⟩
      · show (136 : Nat) < 65536; decide
      · exact hvs
      · exact hvl
      · exact ⟨hd.1, hd.2, by decide⟩)
    (by simp only [retOk, List.all_cons, List.all_nil, hrs, hrl]; rfl) (by simp [preserved])
    (by simp [linkRegs]) ht (absVal scr dp n q) (fun hm hc hp p hp' => ?_)
    (Proof.Sha3.AArch64.Stream.Absorb.absorb_correct v) (Proof.Sha3.AArch64.Stream.Absorb.absorb_ct v)
    (fun _ hc hr => absorb_pre hV hs hc.1.sp (hr (.x0, .loc d 0) (by simp)) (hr (.x1, .val (.const 136)) (by simp))
      (hr (.x2, pos) (by simp)) (hr (.x3, src) (by simp)) (hr (.x4, len) (by simp)) (hr (.x5, .loc d 256) (by simp))
      hql hnl dS dK kD)
    (covers_rw (fun r hr => by rw [List.mem_singleton.mp hr]; exact hin) hs.sponge_writes) hs.sponge_writes
    (fun _ _ hsp hg _ => ⟨hg (.x0, .loc d 0) (by simp), hg (.x1, .val (.const 136)) (by simp), hg (.x2, pos) (by simp),
      hg (.x3, src) (by simp), hg (.x4, len) (by simp), hg (.x5, .loc d 256) (by simp), hsp⟩)
    (fun hm hc hp => WP.mono (kabs_ok v hV hs hc hvs hvl hvp hrs hrl (hdp hm hc hp) (hn hm hc hp)
      (hq hm hc hp) hql hnl hin dS dK kD) fun _ ⟨hu, _, _, hx⟩ =>
        ⟨hu, BitVec.eq_of_toNat_eq (by rw [hx, toNat_ofNat64 (by omega_using [])])⟩)
  simp only [absArgs, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hq hm hc hp
  · exact (hs.loc hc _ 0).trans (BitVec.add_zero _)
  · rfl
  · exact hdp hm hc hp
  · exact hn hm hc hp
  · exact hs.loc hc _ 256

/-- What `padArgs` puts in the registers. -/
def padVal (scr : Addr) (q : Nat) : Reg → Addr
  | .x0 => scr
  | .x1 => BitVec.ofNat 64 136
  | .x2 => BitVec.ofNat 64 q
  | .x3 => BitVec.ofNat 64 0x1f
  | _ => scr + BitVec.ofNat 64 256

theorem kpad_ct (v : Proof.Sha3.AArch64.Permutation) (hV : V.Ok) (hs : ScrOk V d scr)
    (h₁ : M m₁) (h₂ : M m₂) {pos : Src} (hvp : srcValid pos)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS (padArgs d pos))) hint).isSome = true)
    {P : State → Prop} {q : Nat}
    (hq : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      srcValue V.E t.mem (t.gpr .x0) pos = BitVec.ofNat 64 q)
    (hql : q < 136) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (kpad v.callee d pos) (Two V g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  refine callS_ct hV h₁ h₂ (by simp) (fun p hp => by
      simp only [padArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact hvp
      · exact ⟨hd.1, hd.2, by decide⟩
      · show (136 : Nat) < 65536; decide
      · show (0x1f : Nat) < 65536; decide
      · exact ⟨hd.1, hd.2, by decide⟩)
    (by simp only [retOk, List.all_cons, List.all_nil]; rfl) (by simp [preserved])
    (by simp [linkRegs]) ht (padVal scr q) (fun hm hc hp p hp' => ?_)
    (Proof.Sha3.AArch64.Stream.Pad.pad_correct v) (Proof.Sha3.AArch64.Stream.Pad.pad_ct v)
    (fun _ hc hr => pad_pre hV hs hc.1.sp (hr (.x0, .loc d 0) (by simp)) (hr (.x1, .val (.const 136)) (by simp))
      (hr (.x2, pos) (by simp)) (hr (.x4, .loc d 256) (by simp)) hql)
    (covers_rw (by simp) hs.sponge_writes) hs.sponge_writes
    (fun _ _ hsp hg _ => ⟨hg (.x0, .loc d 0) (by simp), hg (.x1, .val (.const 136)) (by simp), hg (.x2, pos) (by simp),
      hg (.x4, .loc d 256) (by simp), hsp⟩)
    (fun hm hc hp => WP.mono (kpad_ok v hV hs hc hvp (hq hm hc hp) hql) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩)
  simp only [padArgs, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl
  · exact hq hm hc hp
  · exact (hs.loc hc _ 0).trans (BitVec.add_zero _)
  · rfl
  · rfl
  · exact hs.loc hc _ 256

/-- What `sqzArgs` puts in the registers. -/
def sqzVal (scr op : Addr) : Reg → Addr
  | .x0 => scr
  | .x1 => BitVec.ofNat 64 136
  | .x2 => BitVec.ofNat 64 0
  | .x3 => op
  | .x4 => BitVec.ofNat 64 114
  | _ => scr + BitVec.ofNat 64 256

theorem ksqz_ct (v : Proof.Sha3.AArch64.Permutation) (hV : V.Ok) (hs : ScrOk V d scr)
    (h₁ : M m₁) (h₂ : M m₂) {out : Src} (hvo : srcValid out) (hro : noRet out = true)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS (sqzArgs d out))) hint).isSome = true)
    {P : State → Prop} {op : Addr}
    (hop : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t → srcValue V.E t.mem (t.gpr .x0) out = op)
    (hw : Apart V ⟨op, 114⟩ ∨ ∃ R ∈ V.outs, Within ⟨op, 114⟩ R)
    (dS : Region.Disjoint ⟨op, 114⟩ (ST scr)) (dK : Region.Disjoint ⟨op, 114⟩ (KS scr))
    (kD : (CK V.E).Disjoint ⟨op, 114⟩) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (ksqz v.callee d out) (Two V g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  have hws : ∀ r ∈ [ST scr, ⟨op, 114⟩, KS scr], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr ⟨_, hs.out, st_within scr⟩
    · exact hw
    · exact .inr ⟨_, hs.out, ks_within scr⟩
  refine callS_ct hV h₁ h₂ (by simp) (fun p hp => by
      simp only [sqzArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨hd.1, hd.2, by decide⟩
      · show (136 : Nat) < 65536; decide
      · show (0 : Nat) < 65536; decide
      · exact hvo
      · show (114 : Nat) < 65536; decide
      · exact ⟨hd.1, hd.2, by decide⟩)
    (by simp only [retOk, List.all_cons, List.all_nil, hro]; rfl) (by simp [preserved])
    (by simp [linkRegs]) ht (sqzVal scr op) (fun hm hc hp p hp' => ?_)
    (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_correct v) (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_ct v)
    (fun _ hc hr => squeeze_pre hV hs hc.1.sp (hr (.x0, .loc d 0) (by simp)) (hr (.x1, .val (.const 136)) (by simp))
      (hr (.x2, .val (.const 0)) (by simp)) (hr (.x3, out) (by simp)) (hr (.x4, .val (.const 114)) (by simp)) (hr (.x5, .loc d 256) (by simp))
      dS dK kD)
    (covers_rw (by simp) hws) hws
    (fun _ _ hsp hg _ => ⟨hg (.x0, .loc d 0) (by simp), hg (.x1, .val (.const 136)) (by simp), hg (.x2, .val (.const 0)) (by simp),
      hg (.x3, out) (by simp), hg (.x4, .val (.const 114)) (by simp), hg (.x5, .loc d 256) (by simp), hsp⟩)
    (fun hm hc hp => WP.mono (ksqz_ok v hV hs hc hvo hro (hop hm hc hp) hw dS dK kD)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩)
  simp only [sqzArgs, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hs.loc hc _ 0).trans (BitVec.add_zero _)
  · rfl
  · rfl
  · exact hop hm hc hp
  · rfl
  · exact hs.loc hc _ 256

/-! ## The Ed448 primitives -/

theorem reduce_ct (hV : V.Ok) (h₁ : M m₁) (h₂ : M m₂) {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, srcValid p.2) (hret : retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS args)) hint).isSome = true)
    {P : State → Prop} (val : Reg → Addr)
    (hval : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      ∀ p ∈ args, srcValue V.E t.mem (t.gpr .x0) p.2 = val p.1)
    (hm : ∀ r ∈ [Reg.x0, .x1, .x2], r ∈ args.map Prod.fst)
    (hd : Region.Disjoint ⟨val .x1, 114⟩ ⟨val .x2, 8192⟩) (hrd : Readable V ⟨val .x1, 114⟩)
    (hwo : Writable V ⟨val .x0, 57⟩) (hws : Writable V ⟨val .x2, 8192⟩) {Q : State → Prop}
    (hok : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t → WP isa
      (callS args "vg_ed448_scalar_reduce" Impl.Ed448.AArch64.scalarReduce) t
      fun u => WCtx V g vec m₀ u ∧ Q u) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P)
      (callS args "vg_ed448_scalar_reduce" Impl.Ed448.AArch64.scalarReduce) (Two V g₁ g₂ v₁ v₂ m₁ m₂ Q) := by
  have hw : ∀ r ∈ [(⟨val .x0, 57⟩ : Region), ⟨val .x2, 8192⟩], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hwo, hws]
  exact callS_ct hV h₁ h₂ hn hv hret hr hl ht val hval Proof.Ed448.AArch64.scalarReduce_ok
    Proof.Ed448.AArch64.scalarReduce_ct
    (fun _ _ hs => reduce_pre (regs_get hs (hm .x0 (by simp))) (regs_get hs (hm .x1 (by simp)))
      (regs_get hs (hm .x2 (by simp))) hd)
    (covers_rw (fun r hr => by rw [List.mem_singleton.mp hr]; exact hrd) hw) hw
    (fun _ _ hsp hg _ => ⟨hsp, entry_eq hg (hm .x0 (by simp)), entry_eq hg (hm .x1 (by simp)),
      entry_eq hg (hm .x2 (by simp))⟩) hok

theorem base_ct (hb : Proof.Ed448.AArch64.BaseOk) (hV : V.Ok) (hcfg:V.sym=Impl.X448.AArch64.Base.combSym ∧ V.words=Impl.X448.AArch64.Base.combWords) (h₁ : M m₁) (h₂ : M m₂)
    {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, srcValid p.2) (hret : retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS args)) hint).isSome = true)
    {P : State → Prop} (val : Reg → Addr)
    (hval : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      ∀ p ∈ args, srcValue V.E t.mem (t.gpr .x0) p.2 = val p.1)
    (hm : ∀ r ∈ [Reg.x0, .x1, .x2], r ∈ args.map Prod.fst)
    (hos : Region.Disjoint ⟨val .x0, 57⟩ ⟨val .x2, 8192⟩) (hss : Region.Disjoint ⟨val .x1, 57⟩ ⟨val .x2, 8192⟩)
    (hnc : (val .x2).toNat + 8192 ≤ 2 ^ 64) (hrd : Readable V ⟨val .x1, 57⟩)
    (hwo : Writable V ⟨val .x0, 57⟩) (hws : Writable V ⟨val .x2, 8192⟩)
    (hMT : ∀ {m}, M m → TblWords V.T m) {Q : State → Prop}
    (hok : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t → WP isa
      (callS args "vg_ed448_scalar_base" Impl.Ed448.AArch64.scalarBase) t
      fun u => WCtx V g vec m₀ u ∧ Q u) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P)
      (callS args "vg_ed448_scalar_base" Impl.Ed448.AArch64.scalarBase) (Two V g₁ g₂ v₁ v₂ m₁ m₂ Q) := by
  have hw : ∀ r ∈ [(⟨val .x0, 57⟩ : Region), ⟨val .x2, 8192⟩], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hwo, hws]
  exact callS_ct hV h₁ h₂ hn hv hret hr hl ht val hval hb.ok
    hb.ct
    (fun hM hc hs => base_pre (regs_get hs (hm .x0 (by simp))) (regs_get hs (hm .x1 (by simp)))
      (regs_get hs (hm .x2 (by simp))) hos hss hnc (by simpa only [hcfg.1] using hc.2.2) (combHeld_of hV hcfg hc (hMT hM) hw _ _))
    (covers_rw (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exact hrd
      · simpa only [hcfg.2] using tbl_readable hV) hw) hw
    (fun _ _ hsp hg hsy => ⟨hsp, entry_eq hg (hm .x0 (by simp)), entry_eq hg (hm .x1 (by simp)),
      entry_eq hg (hm .x2 (by simp)), by simpa only [State.withRegions,State.callEntry,VG.AArch64.call,State.write,hcfg.1] using hsy⟩) hok

theorem mulAdd_ct (hV : V.Ok) (h₁ : M m₁) (h₂ : M m₂) {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, srcValid p.2) (hret : retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS args)) hint).isSome = true)
    {P : State → Prop} (val : Reg → Addr)
    (hval : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      ∀ p ∈ args, srcValue V.E t.mem (t.gpr .x0) p.2 = val p.1)
    (hm : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4], r ∈ args.map Prod.fst)
    (hdr : Region.Disjoint ⟨val .x1, 57⟩ ⟨val .x4, 8192⟩) (hdk : Region.Disjoint ⟨val .x2, 57⟩ ⟨val .x4, 8192⟩)
    (hds : Region.Disjoint ⟨val .x3, 57⟩ ⟨val .x4, 8192⟩)
    (hrr : Readable V ⟨val .x1, 57⟩) (hrk : Readable V ⟨val .x2, 57⟩) (hrs : Readable V ⟨val .x3, 57⟩)
    (hwo : Writable V ⟨val .x0, 57⟩) (hws : Writable V ⟨val .x4, 8192⟩) {Q : State → Prop}
    (hok : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t → WP isa
      (callS args "vg_ed448_scalar_mul_add" Impl.Ed448.AArch64.scalarMulAdd) t
      fun u => WCtx V g vec m₀ u ∧ Q u) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P)
      (callS args "vg_ed448_scalar_mul_add" Impl.Ed448.AArch64.scalarMulAdd) (Two V g₁ g₂ v₁ v₂ m₁ m₂ Q) := by
  have hw : ∀ r ∈ [(⟨val .x0, 57⟩ : Region), ⟨val .x4, 8192⟩], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hwo, hws]
  have hrd : ∀ r ∈ [(⟨val .x1, 57⟩ : Region), ⟨val .x2, 57⟩, ⟨val .x3, 57⟩], Readable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [hrr, hrk, hrs]
  exact callS_ct hV h₁ h₂ hn hv hret hr hl ht val hval Proof.Ed448.AArch64.scalarMulAdd_ok
    Proof.Ed448.AArch64.scalarMulAdd_ct
    (fun _ _ hs => mulAdd_pre (regs_get hs (hm .x0 (by simp))) (regs_get hs (hm .x1 (by simp)))
      (regs_get hs (hm .x2 (by simp))) (regs_get hs (hm .x3 (by simp))) (regs_get hs (hm .x4 (by simp)))
      hdr hdk hds)
    (covers_rw hrd hw) hw
    (fun _ _ hsp hg _ => ⟨hsp, entry_eq hg (hm .x0 (by simp)), entry_eq hg (hm .x1 (by simp)),
      entry_eq hg (hm .x2 (by simp)), entry_eq hg (hm .x3 (by simp)), entry_eq hg (hm .x4 (by simp))⟩) hok

end VG.Proof.Ed448.AArch64.Whole
