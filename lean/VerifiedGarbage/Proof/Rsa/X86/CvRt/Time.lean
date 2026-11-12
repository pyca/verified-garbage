module

public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Proof.Rsa.X86.CvRt.TimeCheck
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeExp
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Rsa.X86.CvInputs
public import VerifiedGarbage.Proof.Rsa.X86.CvRt.Load
public import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.Framework.Slots
public import VerifiedGarbage.Proof.Rsa.X86.CvRt.Checks
public import VerifiedGarbage.Proof.Rsa.X86.InvTimeBase
public import VerifiedGarbage.Proof.Rsa.X86.InvDispatch
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Isa

import VerifiedGarbage.Proof.Rsa.X86.InvChoose
import VerifiedGarbage.Proof.Rsa.X86.InvTimeChoose
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Rsa.X86.CvInverseCall
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Guard
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Time
import VerifiedGarbage.Proof.Rsa.X86.CvRt.Core
import VerifiedGarbage.Proof.Rsa.X86.CvRt.Sized
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import Init.Data.List.Basic
import Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Impl.Rsa.X86.KeyRt
/-! # The trace of CRT parameter calculation at a run-time width, once the modulus is accepted

The width is read from the arguments on the stack, so the taint analysis
takes them public with `edi` and `esp` (`τV`, `sizedCheck`), from states whose
permissions are narrowed to the outputs and the working space, apart from the
arguments (`ArgsOk`); runs of `sized` from the states themselves leak the
same traces (`sizedNarrow_relCT`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.CrtValuesRt
open VG.Proof.Rsa.X86.CrtValues (CallGeometry Inputs bodyWrites inputBytes)
open VG.Proof.Bignum.X86.PublicRt (Both relCT_narrow)

/-- The return address and the arguments lie apart from every writable region. -/
def ArgsOk (s : State) : Prop :=
  (s.gpr .esp).toNat + 68 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 68⟩ r

theorem τV_wf {s : State} (A : ArgsOk s) : VG.X86.Taint.Wf τV s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => A, fun _ h => (List.not_mem_nil h).elim⟩

theorem agreeV {g : CallGeometry} {s₁ s₂ : State} (h₁ : Inputs g s₁) (h₂ : Inputs g s₂)
    (A₁ : ArgsOk s₁) (A₂ : ArgsOk s₂) (sp : s₁.gpr .esp = s₂.gpr .esp) : VG.X86.Taint.Agree τV s₁ s₂ := by
  have f₁ := A₁.1
  have f₂ := A₂.1
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τV_wf A₁, τV_wf A₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τV, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (h₁.ws.workspace.edi_toNat.trans h₂.ws.workspace.edi_toNat.symm)
    · exact sp
  · simp only [τV] at hk
    rw [show VG.X86.Taint.depth τV.stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (show arg s₁ _ = arg s₂ _ from
      (h₁.arguments _ (by omega)).value.trans (h₂.arguments _ (by omega)).value.symm)

/-- What a narrowed run of `sized` keeps: the inputs, the arguments apart and `esp`. -/
def Run (g : CallGeometry) (sp : BitVec 32) (s : State) : Prop :=
  Inputs g s ∧ ArgsOk s ∧ s.gpr .esp = sp

theorem Run.agree {g : CallGeometry} {sp : BitVec 32} {t₁ t₂ : State} (h₁ : Run g sp t₁) (h₂ : Run g sp t₂) :
    VG.X86.Taint.Agree τV t₁ t₂ :=
  agreeV h₁.1 h₂.1 h₁.2.1 h₂.2.1 (h₁.2.2.trans h₂.2.2.symm)

theorem ArgsOk.keep {s t : State} (A : ArgsOk s) {rs : List Reg} (K : Keeps rs s t) (spn : .esp ∉ rs) : ArgsOk t :=
  ⟨by rw [K.1 _ spn]; exact A.1, by rw [K.2.2, K.1 _ spn]; exact A.2⟩

theorem Run.frame {g : CallGeometry} {sp : BitVec 32} {u t : State} (h : Run g sp u) {rs : List Reg}
    (K : Keeps rs u t) (di : .edi ∉ rs) (spn : .esp ∉ rs) (O : Outside g.base 0 g.size u.mem t.mem) : Run g sp t :=
  ⟨h.1.after K di spn (scratchFrame h.1 O), h.2.1.keep K spn, (K.1 _ spn).trans h.2.2⟩

theorem Run.frameBelow {g : CallGeometry} {sp : BitVec 32} {u t : State} (h : Run g sp u) {rs : List Reg}
    (K : Keeps rs u t) (di : .edi ∉ rs) (spn : .esp ∉ rs)
    (F : Frame (g.writes ++ [below (u.gpr .esp) 52]) u.mem t.mem) : Run g sp t :=
  ⟨h.1.afterBelow K di spn F, h.2.1.keep K spn, (K.1 _ spn).trans h.2.2⟩

/-! ## The pieces -/

open VG.Impl.Rsa.X86.CrtValues (sPodd sE1 sE3 sMask aOne aQ aP aDQ aDR aDD aDT aDR2 aDR3 aD nArr)
open VG.Proof.Rsa.X86.Keys (Keep num slot arr S wp_seqs_cons)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw keep_outside)
open VG.Proof.Rsa.X86.WordRt (MLen wq mw Bal relLift RelCT.seqs_cons RelCT.seqs_append)
open VG.X86.Wp (wp_cmpi)

/-- The guard, of the arguments and `n`. -/
def GuardC (g : CallGeometry) (N : Nat) : Prop :=
  (g.args 7).toNat % 8 = 0 ∧ 2 * (g.args 9).toNat = (g.args 7).toNat ∧ 2 * (g.args 11).toNat = (g.args 7).toNat ∧
    128 ≤ (g.args 7).toNat ∧ 2 ^ (32 * kw (g.args 7).toNat - 1) ≤ N

/-- Both runs, each from its own start `x`, the two with the same `n`. -/
def Both₃ (g : CallGeometry) (P : State → State → Prop) (t₁ t₂ : State) : Prop :=
  ∃ x₁ x₂, (fun x₁ x₂ : State => inputBytes g x₁.mem 0 = inputBytes g x₂.mem 0) x₁ x₂ ∧ P x₁ t₁ ∧ P x₂ t₂

theorem taintLift {g : CallGeometry} {sp : BitVec 32} {c : Prog isa} {P Q : State → State → Prop}
    (hc : Ck τV c) (hr : ∀ x t, P x t → Run g sp t) (hw : ∀ x t, P x t → WP isa c t (Q x)) :
    RelCT isa (Both₃ g P) c (Both₃ g Q) := by
  obtain ⟨_, hc⟩ := hc
  exact relLift (Rel := fun x₁ x₂ : State => inputBytes g x₁.mem 0 = inputBytes g x₂.mem 0)
    (VG.RelCT.taint (A := sseTaint) τV (fun t₁ t₂ ⟨x₁, x₂, _, h₁, h₂⟩ => (hr x₁ t₁ h₁).agree (hr x₂ t₂ h₂)) hc) hw

/-- An argument, at its length's value. -/
theorem _root_.VG.Proof.Rsa.X86.CrtValues.Inputs.argNat {g : CallGeometry} {s : State} (h : Inputs g s) {i : Nat} (hi : i < 16) :
    VG.Proof.Bignum.X86.CallArgument s g.base g.size i (BitVec.ofNat 32 (g.args i).toNat) := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact h.arguments i hi

theorem _root_.VG.Proof.Rsa.X86.CrtValues.Inputs.lens {g : CallGeometry} {s : State} (h : Inputs g s) :
    (g.args 7).toNat ≤ 1024 ∧ (g.args 9).toNat ≤ 1024 ∧ (g.args 11).toNat ≤ 1024 := by
  have b0 : (g.args 7).toNat ≤ 8 * g.n := h.inputBound 0
  have b1 : (g.args 9).toNat ≤ 8 * g.n := h.inputBound 1
  have b2 : (g.args 11).toNat ≤ 8 * g.n := h.inputBound 2
  have up := h.upper
  omega

abbrev ar (g : CallGeometry) (x : State) : Geometry := arithmeticGeometry g x.mem

def S1 (g : CallGeometry) (sp : BitVec 32) (x t : State) : Prop :=
  Run g sp t ∧ Start (ar g x) (g.args 7).toNat t
def S2 (g : CallGeometry) (sp : BitVec 32) (x t : State) : Prop :=
  Run g sp t ∧ StC (ar g x) (g.args 7).toNat t ∧ (slot t.mem g.base sG = 0 ↔ GuardC g (ar g x).N)
def S3 (g : CallGeometry) (sp : BitVec 32) (x t : State) : Prop :=
  Run g sp t ∧ StI (ar g x) (g.args 7).toNat t ∧ (slot t.mem g.base sG = 0 ↔ GuardC g (ar g x).N)
def S4 (g : CallGeometry) (sp : BitVec 32) (x t : State) : Prop :=
  Run g sp t ∧ StD (ar g x) (g.args 7).toNat t ∧ (slot t.mem g.base sG = 0 ↔ GuardC g (ar g x).N)
def S5 (g : CallGeometry) (sp : BitVec 32) (x t : State) : Prop :=
  S4 g sp x t ∧ t.zf = some (decide (slot t.mem g.base sG = 0))

/-- Each run after the first block: its working space, and the guard. -/
def S1b (g : CallGeometry) (sp : BitVec 32) (x t : State) : Prop :=
  (RtWs lay t g.base g.size (g.args 7).toNat nArr ∧ Run g sp t) ∧ (slot t.mem g.base sG = 0 ↔ GuardC g (ar g x).N)

/-- Each run after the guard's compare. -/
def S1c (g : CallGeometry) (sp : BitVec 32) (x t : State) : Prop :=
  S1b g sp x t ∧ t.zf = some (decide (slot t.mem g.base sG = 0))

theorem firstBlock_guard {g : CallGeometry} {sp : BitVec 32} {x t : State} (h : S1 g sp x t) :
    WP isa (.block (VG.Impl.Rsa.X86.KeyRt.bitOf lay sPodd aP ++
      VG.Impl.Rsa.X86.WordModRt.balanced lay 7 9 11 aDQ sG)) t (S1b g sp x) := by
  obtain ⟨r, st⟩ := h
  have ls := r.1.lens
  have fit := fun j (hj : j < nArr) => st.ws.ws.fit64 (j := j) hj
  refine WP.block_append (WP.mono (VG.Proof.Rsa.X86.KeyRt.bitOf_ok st.ws (j := aP) (sl := sPodd) (by decide)
    (by decide)) fun v ⟨hv, kv, _, rv⟩ => ?_)
  have Ov := keep_outside st.ws.ws kv (by simp) (by decide)
  have rv' := r.frame rv (by decide) (by decide) Ov
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.balanced_ok hv (rv'.1.argNat (by decide)) (rv'.1.argNat (by decide))
    (rv'.1.argNat (by decide)) ls.1 ls.2.1 ls.2.2 (n := aDQ) (sl := sG) (by decide) (by decide))
    fun t' ⟨ht, kt, eu, rt⟩ => ⟨⟨ht, rv'.frame rt (by decide) (by decide) (keep_outside hv.ws kt (by simp) (by decide))⟩,
      ?_⟩
  have w : mw v.mem g.base (kw (g.args 7).toNat) aDQ (kw (g.args 7).toNat - 1) =
      mw t.mem g.base (kw (g.args 7).toNat) aDQ (kw (g.args 7).toNat - 1) :=
    kv.word (by unfold S; have := st.ws.kw_pos; omega) (by simp) (by decide) (fit _ (by decide))
  have top : 2 ^ 31 ≤ mw t.mem g.base (kw (g.args 7).toNat) aDQ (kw (g.args 7).toNat - 1) ↔
      2 ^ (32 * kw (g.args 7).toNat - 1) ≤ (ar g x).N := by
    rw [← st.n]; exact VG.Proof.Rsa.X86.WordRt.top_iff st.ws.kw_pos
  have eb : (ar g x).base = g.base := rfl
  rw [eb] at eu
  rw [eu, w]
  exact ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, top.mp e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, top.mpr e⟩⟩

theorem guardB_ok {g : CallGeometry} {sp : BitVec 32} {x t : State} (h : S1b g sp x t) :
    WP isa (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sG)), .alu .cmp .eax (.imm 0)]) t (S1c g sp x) := by
  obtain ⟨⟨hd, r⟩, hg⟩ := h
  refine wp_movS (readSrc_sc hd.ws.workspace (by have := hd.ws.hdr_le; unfold sG VG.Impl.Rsa.X86.Keys.hdr at *; omega))
    fun u U _ => wp_cmpi fun t' T _ z => WP.block_nil ?_
  have K : Keeps [.eax] t t' := U.keeps.trans (T.keeps [.eax])
  have M : t'.mem = t.mem := T.mem.trans U.mem
  have hw := hd.keep K (by decide) (by decide) (by rw [M]; exact Outside.refl _ _ _ _)
  have sl : slot t'.mem g.base sG = slot t.mem g.base sG := by rw [M]
  refine ⟨⟨⟨hw, r.frame K (by decide) (by decide) (by rw [M]; exact Outside.refl _ _ _ _)⟩, by rw [sl]; exact hg⟩, ?_⟩
  rw [z, U.gpr, VG.Proof.Rsa.X86.WordRt.sub0_beq, sl]

theorem firstDiv_relCT {g : CallGeometry} {sp : BitVec 32} (ck : CvCk) :
    RelCT isa (Both₃ g (S1 g sp)) firstDiv (Both₃ g (S2 g sp)) := by
  refine relLift (Rel := fun x₁ x₂ : State => inputBytes g x₁.mem 0 = inputBytes g x₂.mem 0) ?_ fun x t h => ?_
  · -- The trace: the block, the guard, then the product, over `w / 2` words where the guard holds.
    unfold firstDiv
    simp only [VG.Impl.Rsa.X86.Keys.seqs]
    obtain ⟨_, cb⟩ := ck.block
    obtain ⟨_, cg⟩ := ck.guard
    refine VG.RelCT.seq (relLift (P := S1 g sp)
      ((VG.RelCT.taint (A := sseTaint) τV (fun t₁ t₂ ⟨_, _, _, h₁, h₂⟩ => h₁.1.agree h₂.1) cb).mono
        (fun _ _ h => h) fun _ _ _ => trivial) fun _ _ h => firstBlock_guard h) ?_
    unfold VG.Impl.Rsa.X86.WordModRt.ifBalanced
    refine VG.RelCT.seq (relLift (P := S1b g sp)
      ((VG.RelCT.taint (A := sseTaint) τV (fun t₁ t₂ ⟨_, _, _, h₁, h₂⟩ => h₁.1.2.agree h₂.1.2) cg).mono
        (fun _ _ h => h) fun _ _ _ => trivial) fun _ _ h => guardB_ok h) ?_
    have zEq : ∀ {t₁ t₂ : State}, (∃ x₁ x₂, inputBytes g x₁.mem 0 = inputBytes g x₂.mem 0 ∧
        S1c g sp x₁ t₁ ∧ S1c g sp x₂ t₂) → t₁.zf = t₂.zf :=
      fun {t₁ t₂} ⟨x₁, x₂, hn, ⟨⟨_, g₁⟩, z₁⟩, ⟨⟨_, g₂⟩, z₂⟩⟩ => by
        rw [z₁, z₂]
        have hN : (ar g x₁).N = (ar g x₂).N := by
          show Spec.Rsa.os2ip (inputBytes g x₁.mem 0) = Spec.Rsa.os2ip (inputBytes g x₂.mem 0)
          rw [hn]
        have : (slot t₁.mem g.base sG = 0) ↔ (slot t₂.mem g.base sG = 0) := by
          rw [g₁, g₂, hN]
        simp only [this]
    have hτ : ∀ r ∈ [Reg.edi, .esp], τV.regs.mem r = true := by
      intro r hr; change r ∈ RegSet.ofList [Reg.edi, .esp]; simpa only [RegSet.mem_ofList] using hr
    by_cases hk : 1 ≤ kw (g.args 7).toNat
    swap
    · exact VG.RelCT.of_false fun _ _ ⟨_, _, _, ⟨⟨⟨w₁, _⟩, _⟩, _⟩, _⟩ => hk w₁.kw_pos
    refine VG.RelCT.ite (M := isa) (c := .e) (fun t₁ t₂ h => zEq h) ?_ ?_
    · exact (VG.Proof.Rsa.X86.WordRt.mulHalf_relCT (τ := τV) (Fr := Run g sp) (B := g.base) (Z := g.size)
        (fun _ _ a b => a.agree b) (fun f K d e O => f.frame K d e O) hτ hk
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ck.h₀ ck.r₁ ck.h₂).mono
        (fun _ _ ⟨⟨_, _, _, ⟨⟨f₁, _⟩, _⟩, ⟨⟨f₂, _⟩, _⟩⟩, _⟩ => ⟨f₁, f₂⟩) fun _ _ h => h
    · exact (VG.Proof.Rsa.X86.WordRt.mulRows_relCT (τ := τV) (Fr := Run g sp) (B := g.base) (Z := g.size)
        (fun _ _ a b => a.agree b) (fun f K d e O => f.frame K d e O) hτ
        (rows := none) (by show 1 ≤ kw _; exact hk) (Nat.le_refl _) (fun k hk => by cases hk)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ck.r₀ ck.r₁ ck.r₂).mono
        (fun _ _ ⟨⟨_, _, _, ⟨⟨f₁, _⟩, _⟩, ⟨⟨f₂, _⟩, _⟩⟩, _⟩ => ⟨f₁, f₂⟩) fun _ _ h => h
  · -- What each run computes.
    obtain ⟨r, st⟩ := h
    have ls := r.1.lens
    have gate := inputsGate r.1 x.mem
    have pB : (ar g x).P < 2 ^ (8 * (g.args 9).toNat) := by
      rw [← VG.Proof.Bignum.pow256_eq]; exact gate.pBound
    have qB : (ar g x).Q < 2 ^ (8 * (g.args 11).toNat) := by
      rw [← VG.Proof.Bignum.pow256_eq]; exact gate.qBound
    refine WP.mono (firstDiv_ok st (r.1.argNat (by decide)) (r.1.argNat (by decide)) ls.2.1 ls.2.2 pB qB)
      fun t' ⟨hc, k, R, an, han, cn, _, hg⟩ => ⟨r.frame R (by decide) (by decide) (keep_outside st.ws.ws k
        (by decide) (by decide)), hc, ?_⟩
    have ea : an = (g.args 7).toNat := by
      have e := cn.value.symm.trans (r.1.arguments 7 (by decide)).value
      rw [← e, BitVec.toNat_ofNat]; omega
    subst ea
    refine hg.trans ?_
    have tp : 2 ^ 31 ≤ mw x.mem g.base (kw (g.args 7).toNat) aDQ (kw (g.args 7).toNat - 1) ∨ True := .inr trivial
    have nv := st.n
    have top : 2 ^ 31 ≤ mw t.mem g.base (kw (g.args 7).toNat) aDQ (kw (g.args 7).toNat - 1) ↔
        2 ^ (32 * kw (g.args 7).toNat - 1) ≤ (ar g x).N := by
      rw [← nv]; exact VG.Proof.Rsa.X86.WordRt.top_iff st.ws.kw_pos
    exact ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, top.mp e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, top.mpr e⟩⟩

theorem checksA_relCT {g : CallGeometry} {sp : BitVec 32} (ck : CvCk) :
    RelCT isa (Both₃ g (S2 g sp)) (VG.Impl.Rsa.X86.Keys.seqs checksPrefix) (Both₃ g (S3 g sp)) :=
  taintLift ck.checksA (fun _ _ h => h.1) fun x t ⟨r, hc, hg⟩ =>
    WP.mono (checksA_ok hc) fun t' ⟨hi, k, R⟩ =>
      ⟨r.frame R (by decide) (by decide) (keep_outside hc.ws.ws k (by decide) (by decide)), hi, by
        have e : slot t'.mem g.base sG = slot t.mem g.base sG := k.slot (e := sG) (by decide) (by decide)
        rw [e]; exact hg⟩

theorem inverse_relCT [VG.Proof.Rsa.X86.BatchLaw] {g : CallGeometry} {sp : BitVec 32} :
    RelCT isa (Both₃ g (S3 g sp)) inverseChoice fun t₁ t₂ => Run g sp t₁ ∧ Run g sp t₂ := by
  refine (VG.RelCT.exists_ (P := fun (x : State × State) t₁ t₂ =>
    inputBytes g x.1.mem 0 = inputBytes g x.2.mem 0 ∧ S3 g sp x.1 t₁ ∧ S3 g sp x.2 t₂) fun ⟨x₁, x₂⟩ => ?_).mono
    (fun t₁ t₂ ⟨x₁, x₂, e, h₁, h₂⟩ => ⟨⟨x₁, x₂⟩, e, h₁, h₂⟩) fun _ _ h => h
  have inp : ∀ {x t : State}, S3 g sp x t →
      InvInput g.args g.base g.size (g.args 7).toNat (ar g x).P (ar g x).Q t ∧
        InvTiming.Public g.args g.base g.size sp t := fun {x t} ⟨r, hb, _⟩ =>
    ⟨⟨hb.ws, inputsGate r.1 x.mem, hb.u, hb.m, hb.nm, hb.zero,
      by exact Prod.ext hb.u (Prod.ext hb.v (Prod.ext hb.x₁ hb.x₂))⟩, ⟨r.2.1, r.2.2, r.1.arguments⟩⟩
  have post : ∀ {x t t' : State}, S3 g sp x t →
      InvPost g.base g.size (g.args 7).toNat (ar g x).P (ar g x).Q t t' → Run g sp t' := fun {x t t'} h p => by
    obtain ⟨r, hb, _⟩ := h
    have F : Frame (g.writes ++ [below (t.gpr .esp) 52]) t.mem t'.mem :=
      VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS.toFrame (fun _ _ o => scratchFrame r.1
        (keep_outside hb.ws.ws o (by decide) (by decide))) p.2.1
    exact r.frameBelow p.2.2.1 (by decide) (by decide) F
  exact (VG.RelCT.wp (F₁ := fun t' => ∃ t, S3 g sp x₁ t ∧ InvPost g.base g.size (g.args 7).toNat (ar g x₁).P (ar g x₁).Q t t')
    (F₂ := fun t' => ∃ t, S3 g sp x₂ t ∧ InvPost g.base g.size (g.args 7).toNat (ar g x₂).P (ar g x₂).Q t t')
    ((InvTiming.dispatch_relCT (args := g.args) (base := g.base) (size := g.size) (len := (g.args 7).toNat)
      (P := (ar g x₁).P) (Q := (ar g x₁).Q) (P' := (ar g x₂).P) (Q' := (ar g x₂).Q) (sp := sp)).mono
      (fun t₁ t₂ h => ⟨inp h.2.1, inp h.2.2⟩) fun _ _ h => h)
    fun t₁ t₂ h => ⟨WP.mono (inverseDispatch_ok (inp h.2.1).1) fun t' p => ⟨t₁, h.2.1, p⟩,
      WP.mono (inverseDispatch_ok (inp h.2.2).1) fun t' p => ⟨t₂, h.2.2, p⟩⟩).mono (fun _ _ h => h)
    fun _ _ ⟨_, ⟨_, a₁, p₁⟩, ⟨_, a₂, p₂⟩⟩ => ⟨post a₁ p₁, post a₂ p₂⟩

theorem checksB_relCT [VG.Proof.Rsa.X86.BatchLaw] {g : CallGeometry} {sp : BitVec 32} (ck : CvCk) :
    RelCT isa (Both₃ g (S3 g sp)) (VG.Impl.Rsa.X86.Keys.seqs (inverseChoice :: checksSuffix)) (Both₃ g (S4 g sp)) := by
  obtain ⟨_, cs⟩ := ck.suffix
  refine relLift (Rel := fun x₁ x₂ : State => inputBytes g x₁.mem 0 = inputBytes g x₂.mem 0)
    (RelCT.seqs_cons (by simp [checksSuffix]) inverse_relCT
      (VG.RelCT.taint (A := sseTaint) τV (fun t₁ t₂ h => h.1.agree h.2) cs)) fun x t ⟨r, hb, hg⟩ => ?_
  have gate := inputsGate r.1 x.mem
  refine WP.mono (checksB_ok hb gate) fun t' ⟨hd, K, R⟩ => ⟨?_, hd, ?_⟩
  · exact r.frameBelow R (by decide) (by decide) (VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS.toFrame
      (fun _ _ o => scratchFrame r.1 (keep_outside hb.ws.ws o (by decide) (by decide))) K)
  · have e : slot t'.mem g.base sG = slot t.mem g.base sG :=
      outsS_slot K gate.room (e := sG) (by decide) hb.ws.ws.hdr_le (by decide)
    rw [e]; exact hg

theorem guard_relCT {g : CallGeometry} {sp : BitVec 32} (ck : CvCk) :
    RelCT isa (Both₃ g (S4 g sp)) (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sG)), .alu .cmp .eax (.imm 0)])
      (Both₃ g (S5 g sp)) :=
  taintLift ck.guard (fun _ _ h => h.1) fun x t ⟨r, hd, hg⟩ => by
    refine wp_movS (readSrc_sc hd.ws.ws.workspace (by have := hd.ws.ws.hdr_le; unfold sG VG.Impl.Rsa.X86.Keys.hdr at *; omega))
      fun u U _ => wp_cmpi fun t' T _ z => WP.block_nil ?_
    have K : Keeps [.eax] t t' := U.keeps.trans (T.keeps [.eax])
    have M : t'.mem = t.mem := T.mem.trans U.mem
    have hw := hd.ws.keep K (by decide) (by decide) (by rw [M]; exact Outside.refl _ _ _ _)
    have sl : slot t'.mem g.base sG = slot t.mem g.base sG := by rw [M]
    refine ⟨⟨r.frame K (by decide) (by decide) (by rw [M]; exact Outside.refl _ _ _ _), hd.mem hw M,
      by rw [sl]; exact hg⟩, ?_⟩
    rw [z, U.gpr, VG.Proof.Rsa.X86.WordRt.sub0_beq, sl]; rfl

/-- Each run in the word steps: `p`'s length `ap`, which the guard admits. -/
def FW (g : CallGeometry) (sp : BitVec 32) (t : State) : Prop :=
  Run g sp t ∧ RtWs lay t g.base g.size (g.args 7).toNat nArr ∧
    MLen t g.base g.size 9 (g.args 9).toNat ∧ 4 ≤ wq (g.args 9).toNat ∧ wq (g.args 9).toNat ≤ kw (g.args 7).toNat

theorem fwStep {g : CallGeometry} {sp : BitVec 32} {c : Prog isa}
    (hrel : RelCT isa (fun t₁ t₂ => FW g sp t₁ ∧ FW g sp t₂) c fun _ _ => True)
    (hw : ∀ t, FW g sp t → WP isa c t (FW g sp)) :
    RelCT isa (fun t₁ t₂ => FW g sp t₁ ∧ FW g sp t₂) c (fun t₁ t₂ => FW g sp t₁ ∧ FW g sp t₂) :=
  (VG.RelCT.wp hrel fun t₁ t₂ h => ⟨hw t₁ h.1, hw t₂ h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

theorem FW.next {g : CallGeometry} {sp : BitVec 32} {t t' : State} (h : FW g sp t) {js ds : List Nat}
    {rs : List Reg} (hw : RtWs lay t' g.base g.size (g.args 7).toNat nArr)
    (k : Keep g.base (kw (g.args 7).toNat) js ds t.mem t'.mem) (hjs : ∀ j ∈ js, j < nArr)
    (hds : ∀ d ∈ ds, d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (K : Keeps rs t t') (di : .edi ∉ rs) (spn : .esp ∉ rs) :
    FW g sp t' :=
  have O := keep_outside h.2.1.ws k hjs hds
  ⟨h.1.frame K di spn O, hw, h.2.2.1.keep K spn O, h.2.2.2⟩

theorem fwTaint {g : CallGeometry} {sp : BitVec 32} {c : Prog isa} (hc : Ck τV c)
    (hw : ∀ t, FW g sp t → WP isa c t (FW g sp)) :
    RelCT isa (fun t₁ t₂ => FW g sp t₁ ∧ FW g sp t₂) c (fun t₁ t₂ => FW g sp t₁ ∧ FW g sp t₂) := by
  obtain ⟨_, hc⟩ := hc
  exact fwStep (VG.RelCT.taint (A := sseTaint) τV (fun t₁ t₂ h => h.1.1.agree h.2.1) hc) hw

theorem fwWordMod {g : CallGeometry} {sp : BitVec 32} {r : Nat} (hr : r = aDR2 ∨ r = aDR3)
    (c₀ : Ck τV (.seq (.seq (.block (VG.Impl.Rsa.X86.WordModRt.orTop lay 9 aDD)) (VG.Impl.Rsa.X86.WordModRt.recip lay))
      (VG.Impl.Rsa.X86.WordModRt.seed lay 9 aDQ r false)))
    (c₁ : Ck τV (.block (VG.Proof.Rsa.X86.WordRt.digitHead lay aDQ)))
    (c₂ : Ck τV₂ (.seq (.block VG.Proof.Rsa.X86.WordRt.digitH₂) (VG.Proof.Rsa.X86.WordRt.digitTail lay 9 aDQ r aDD aDT))) :
    RelCT isa (fun t₁ t₂ => FW g sp t₁ ∧ FW g sp t₂) (VG.Impl.Rsa.X86.WordModRt.wordMod lay 9 aDQ r aDD aDT)
      (fun t₁ t₂ => FW g sp t₁ ∧ FW g sp t₂) := by
  have hrN : r < nArr := by rcases hr with rfl | rfl <;> decide
  have d1 : r ≠ aDT := by rcases hr with rfl | rfl <;> decide
  have d2 : r ≠ aDD := by rcases hr with rfl | rfl <;> decide
  have d3 : r ≠ aDQ := by rcases hr with rfl | rfl <;> decide
  refine fwStep ?_ fun t h => WP.mono (VG.Proof.Rsa.X86.WordRt.wordMod_ok h.2.1 h.2.2.1 (x := aDQ) (r := r) (m := aDD)
    (t := aDT) (wide := false) (by decide) hrN (by decide) (by decide) d1 (by decide) d2 d3 (by decide) (by decide)
    (fun e => absurd e (by decide)) (fun e => absurd e (by decide)) (fun e => absurd e (by decide)) h.2.2.2.1
    h.2.2.2.2) fun t' ⟨hw, k, _, _, _, K⟩ => h.next hw k (by
      intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl
      · decide
      · exact hrN
      · decide) (by decide) K (by decide) (by decide)
  intro t₁ t₂ t₁' t₂' s₁ s₂ hp e₁ e₂
  exact VG.Proof.Rsa.X86.WordRt.wordMod_relCT (τ := τV) (Fr := Run g sp) (B := g.base) (Z := g.size)
    (fun _ _ a b => a.agree b) (fun f K d e O => f.frame K d e O)
    (by intro r hr; change r ∈ RegSet.ofList [Reg.edi, .esp]; simpa only [RegSet.mem_ofList] using hr)
    (by decide) hrN (by decide) (by decide) d1 (by decide) d2 d3 (by decide) (by decide)
    (fun e => absurd e (by decide)) (fun e => absurd e (by decide)) (fun e => absurd e (by decide))
    hp.1.2.2.2.1 hp.1.2.2.2.2 c₀ c₁ c₂ _ _ _ _ _ _
    ⟨⟨hp.1.2.1, hp.1.1, hp.1.2.2.1⟩, ⟨hp.2.2.1, hp.2.1, hp.2.2.2.1⟩⟩ e₁ e₂

theorem wordRems_relCT {g : CallGeometry} {sp : BitVec 32} (ck : CvCk) :
    RelCT isa (fun t₁ t₂ => FW g sp t₁ ∧ FW g sp t₂) wordRems (fun t₁ t₂ => FW g sp t₁ ∧ FW g sp t₂) := by
  unfold wordRems rems
  refine RelCT.seqs_cons (by simp) (fwWordMod (.inl rfl) ck.m₀ ck.m₁ ck.m₂) ?_
  refine RelCT.seqs_cons (by simp) (fwTaint ck.copyD fun t h => WP.mono (VG.Proof.Rsa.X86.KeyRt.copy_ok h.2.1
    (o := aDQ) (a := aD) (by decide) (by decide) (by decide)) fun t' ⟨hw, k, _, K, _⟩ =>
      h.next hw k (by decide) (by simp) K (by decide) (by decide)) ?_
  refine RelCT.seqs_cons (by simp) (fwTaint ck.copyQ fun t h => WP.mono (VG.Proof.Rsa.X86.KeyRt.copy_ok h.2.1
    (o := aDD) (a := aQ) (by decide) (by decide) (by decide)) fun t' ⟨hw, k, _, K, _⟩ =>
      h.next hw k (by decide) (by simp) K (by decide) (by decide)) ?_
  refine RelCT.seqs_cons (by simp) (fwTaint ck.clr fun t h => WP.mono (VG.Proof.Rsa.X86.KeyRt.clrLow_ok h.2.1
    (j := aDD) (by decide)) fun t' ⟨hw, k, _, K, _⟩ =>
      h.next hw k (by decide) (by simp) K (by decide) (by decide)) ?_
  exact fwWordMod (.inr rfl) ck.m₀' ck.m₁ ck.m₂'

theorem branch_relCT {g : CallGeometry} {sp : BitVec 32} (ck : CvCk) :
    RelCT isa (Both₃ g (S5 g sp)) (.ite .e wordRems divRems) fun t₁ t₂ => Run g sp t₁ ∧ Run g sp t₂ := by
  have zEq : ∀ {t₁ t₂ : State}, Both₃ g (S5 g sp) t₁ t₂ → t₁.zf = t₂.zf := fun {t₁ t₂} ⟨x₁, x₂, hn, ⟨g₁, z₁⟩, ⟨g₂, z₂⟩⟩ => by
    rw [z₁, z₂]
    have hN : (ar g x₁).N = (ar g x₂).N := by
      show Spec.Rsa.os2ip (inputBytes g x₁.mem 0) = Spec.Rsa.os2ip (inputBytes g x₂.mem 0)
      rw [hn]
    have : (slot t₁.mem g.base sG = 0) ↔ (slot t₂.mem g.base sG = 0) := by
      rw [g₁.2.2, g₂.2.2, hN]
    simp only [this]
  refine VG.RelCT.ite (M := isa) (c := .e) (fun t₁ t₂ h => zEq h) ?_ ?_
  · refine (wordRems_relCT ck).mono ?_ fun _ _ h => ⟨h.1.1, h.2.1⟩
    rintro t₁ t₂ ⟨hb, et⟩
    have et₂ : isa.eval .e t₂ = some true := (zEq hb).symm.trans et
    obtain ⟨x₁, x₂, _, ⟨g₁, z₁⟩, ⟨g₂, z₂⟩⟩ := hb
    have fw : ∀ {x t : State}, S4 g sp x t → t.zf = some (decide (slot t.mem g.base sG = 0)) →
        isa.eval .e t = some true → FW g sp t := fun {x t} ⟨r, hd, hg⟩ z e => by
      have bal : GuardC g (ar g x).N := hg.mp (by change t.zf = _ at e; rw [z] at e; simpa using e)
      obtain ⟨h8, hp, -, h128, -⟩ := bal
      refine ⟨r, hd.ws, ⟨r.1.argNat (by decide), r.1.lens.2.1⟩, ?_, ?_⟩
      · simp only [wq]; omega
      · simp only [wq, kw, Spec.Rsa.modulusWords]; omega
    exact ⟨fw g₁ z₁ et, fw g₂ z₂ et₂⟩
  · obtain ⟨_, cb⟩ := ck.bits
    refine (VG.RelCT.wp (F₁ := Run g sp) (F₂ := Run g sp)
      ((VG.RelCT.taint (A := sseTaint) τV (P := fun t₁ t₂ => Run g sp t₁ ∧ Run g sp t₂)
        (fun t₁ t₂ h => h.1.agree h.2) cb).mono
        (fun t₁ t₂ ⟨⟨_, _, _, ⟨g₁, _⟩, ⟨g₂, _⟩⟩, _⟩ => ⟨g₁.1, g₂.1⟩) fun _ _ h => h) ?_).mono (fun _ _ h => h)
      fun _ _ h => h.2
    rintro t₁ t₂ ⟨⟨x₁, x₂, _, ⟨⟨r₁, d₁, _⟩, _⟩, ⟨⟨r₂, d₂, _⟩, _⟩⟩, _⟩
    exact ⟨WP.mono (divRems_ok d₁) fun t' ⟨_, k, K⟩ =>
        r₁.frame K (by decide) (by decide) (keep_outside d₁.ws.ws k (by decide) (by decide)),
      WP.mono (divRems_ok d₂) fun t' ⟨_, k, K⟩ =>
        r₂.frame K (by decide) (by decide) (keep_outside d₂.ws.ws k (by decide) (by decide))⟩

/-- Two runs of `sized` with the same `n` leak the same trace. -/
theorem sized_relCT [VG.Proof.Rsa.X86.BatchLaw] (g : CallGeometry) (len : Lengths g) (sp : BitVec 32) :
    RelCT isa (fun s₁ s₂ => (Run g sp s₁ ∧ Run g sp s₂) ∧ inputBytes g s₁.mem 0 = inputBytes g s₂.mem 0)
      sized fun _ _ => True := by
  have ck := cvCk
  unfold sized
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine VG.RelCT.seq (R := Both₃ g (S1 g sp)) ?_ (VG.RelCT.seq (R := fun t₁ t₂ => Run g sp t₁ ∧ Run g sp t₂) ?_ ?_)
  · obtain ⟨_, hc⟩ := ck.loads
    have T := VG.RelCT.wpDep
      (P := fun (s₁ s₂ : State) => (Run g sp s₁ ∧ Run g sp s₂) ∧ inputBytes g s₁.mem 0 = inputBytes g s₂.mem 0)
      (VG.RelCT.taint (A := sseTaint) τV
      (P := fun (s₁ s₂ : State) => (Run g sp s₁ ∧ Run g sp s₂) ∧ inputBytes g s₁.mem 0 = inputBytes g s₂.mem 0)
      (fun t₁ t₂ h => h.1.1.agree h.1.2) hc)
      (F := fun (σ t : State) => S1 g sp σ t) fun s₁ s₂ h =>
        ⟨WP.mono (loads_ok h.1.1.1 len) fun t ⟨it, st, _, K⟩ => ⟨⟨it, h.1.1.2.1.keep K (by decide),
          (K.1 _ (by decide)).trans h.1.1.2.2⟩, st⟩,
          WP.mono (loads_ok h.1.2.1 len) fun t ⟨it, st, _, K⟩ => ⟨⟨it, h.1.2.2.1.keep K (by decide),
          (K.1 _ (by decide)).trans h.1.2.2.2⟩, st⟩⟩
    refine T.mono (fun _ _ h => h) ?_
    rintro t₁ t₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩
    exact ⟨σ₁, σ₂, hp.2, h₁, h₂⟩
  · unfold core
    refine VG.RelCT.seq (firstDiv_relCT ck) (VG.RelCT.seq (R := Both₃ g (S4 g sp)) ?_ ?_)
    · show RelCT isa _ (VG.Impl.Rsa.X86.Keys.seqs (checksPrefix ++ inverseChoice :: checksSuffix)) _
      exact RelCT.seqs_append (by simp [checksPrefix]) (by simp) (VG.RelCT.seq (checksA_relCT ck) (checksB_relCT ck))
    · unfold VG.Impl.Rsa.X86.WordModRt.ifBalanced
      exact VG.RelCT.seq (guard_relCT ck) (branch_relCT ck)
  · obtain ⟨_, hc⟩ := ck.stores
    exact VG.RelCT.taint (A := sseTaint) τV (fun t₁ t₂ h => h.1.agree h.2) hc

/-- What the runs of `sized` from the states themselves need: the inputs, `esp`, and the arguments apart
from what the body writes. -/
def SizedAt (g : CallGeometry) (sp : BitVec 32) (s : State) : Prop :=
  Inputs g s ∧ s.gpr .esp = sp ∧ sp.toNat + 68 ≤ 2 ^ 32 ∧
    ∀ r ∈ g.writes, Region.Disjoint ⟨sp.setWidth 64, 68⟩ r

theorem narrow_inputs {g : CallGeometry} {s : State} (h : Inputs g s) :
    Inputs g (s.withRegions (s.rd ++ s.wr) g.writes) := by
  refine ⟨⟨⟨h.ws.workspace.edi, by simp [State.withRegions, CallGeometry.writes], h.ws.workspace.nowrap,
      h.ws.workspace.stk⟩, h.ws.fits, h.ws.wpos, h.ws.wle⟩, h.lower, h.upper,
    fun i hi => ⟨⟨?_, (h.arguments i hi).stack.apart⟩, (h.arguments i hi).value⟩, h.stackApart, h.inputPositive,
    h.inputBound, h.inputFit, fun j => ?_, h.inputApart, h.outputPositive, h.outputBound, h.outputFit, fun j => ?_,
    h.outputScratch, h.outputSeparate, h.room⟩
  · obtain ⟨r, hr, hc⟩ := (h.arguments i hi).stack.read
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := h.inputRead j
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · refine ⟨g.buffer (2 * j.val), ?_, Region.contains_self _ _⟩
    have cases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
    rcases cases with e | e | e <;> simp [State.withRegions, CallGeometry.writes, e]

theorem narrow_run {g : CallGeometry} {sp : BitVec 32} {s : State} (S : SizedAt g sp s) :
    Run g sp (s.withRegions (s.rd ++ s.wr) g.writes) := by
  obtain ⟨h, esp, fit, apart⟩ := S
  refine ⟨narrow_inputs h, ⟨?_, fun r hr => ?_⟩, esp⟩
  · show (s.gpr .esp).toNat + 68 ≤ _; rw [esp]; exact fit
  · show Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 68⟩ r; rw [esp]; exact apart r hr

theorem sizedNarrow_relCT [VG.Proof.Rsa.X86.BatchLaw] (g : CallGeometry) (len : Lengths g) (sp : BitVec 32) :
    RelCT isa (fun s₁ s₂ => Both (SizedAt g sp) s₁ s₂ ∧ inputBytes g s₁.mem 0 = inputBytes g s₂.mem 0)
      sized fun _ _ => True := by
  refine relCT_narrow (Pn := fun s₁ s₂ => (Run g sp s₁ ∧ Run g sp s₂) ∧ inputBytes g s₁.mem 0 = inputBytes g s₂.mem 0)
    (fun s => s.rd ++ s.wr) (fun _ => g.writes) (fun s₁ s₂ ⟨⟨S₁, S₂⟩, hn⟩ => ?_) (sized_relCT g len sp)
  have cov : ∀ {s : State}, SizedAt g sp s → Covers g.writes s.wr := by
    intro s S
    apply Covers.of_forall
    intro r hr
    simp only [CallGeometry.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Covers.of_mem (by simpa using S.1.ws.workspace.wr)
    · exact Covers.one (S.1.outputWrite 0)
    · exact Covers.one (S.1.outputWrite 1)
    · exact Covers.one (S.1.outputWrite 2)
  have wp : ∀ {s : State}, SizedAt g sp s →
      ∃ F, WP isa sized (s.withRegions (s.rd ++ s.wr) g.writes) F :=
    fun S => ⟨_, sized_ok (narrow_inputs S.1) len⟩
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right (cov S₁)), cov S₁,
    Covers.append_left (Covers.refl _) (Covers.right (cov S₂)), cov S₂, wp S₁, wp S₂,
    ⟨narrow_run S₁, narrow_run S₂⟩, hn⟩

end VG.Proof.Rsa.X86.CrtValuesRt
