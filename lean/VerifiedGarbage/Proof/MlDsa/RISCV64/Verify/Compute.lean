module

public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Steps
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Samp
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Samp
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Good
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Steps
meta import VerifiedGarbage.Proof.MlDsa.Verify.Mem
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Site
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.CallV
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.CallV
meta import VerifiedGarbage.Proof.MlDsa.Verify.Final
public import VerifiedGarbage.Proof.MlDsa.Verify.Spec
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.StepsCT
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Verify.Lay
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Piece
public import VerifiedGarbage.Proof.MlKem.RISCV64.TopSave
import VerifiedGarbage.Proof.MlDsa.RISCV64.CacheCopy
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Verify.Lay
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Piece
meta import VerifiedGarbage.Proof.MlKem.RISCV64.TopSave
meta import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.StepsCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.CacheCopy
meta import VerifiedGarbage.Proof.MlDsa.Verify.Spec
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Site
meta import VerifiedGarbage.Proof.MlDsa.Contract

/-! ### `MlDsa.RISCV64.Verify.SampA`, which this module and modules that import it used -/

section

/-! ### `MlDsa.RISCV64.Verify.Z`, which only this module used -/

section

/-! ### `MlDsa.RISCV64.Verify.Hint`, which only this module used -/

section

/-! ### `MlDsa.RISCV64.Verify.Control`, which only this module used -/

section

/-! ### `MlDsa.RISCV64.Verify.Inv`, which only this module used -/

section

/-!
# ML-DSA verification on RISC-V: what holds throughout, and the prologue

As on PPC64LE (`Proof/MlDsa/PPC64LE/Verify/SampA.lean`): what holds of the
state throughout (`VC`: the layout, the permissions and stack pointer of the
entry state, our caller's registers saved in `scratch` (ML-KEM's
`TopSaved`), the callee-saved registers we do not save as they were, and the
inputs), which a part keeps if it writes only `scratch` and the stack, apart
from the saved registers (`vcChk`); the pieces of verification (`VPiece`);
and the prologue, key generation's (`vpro_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Verify

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece disjW disjW' reg)
open VG.Impl.MlDsa.RISCV64.Verify
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.Sha3.RISCV64.Stream (mov)

/-! ## The inputs -/

section
variable (p : Params) (σ : State)

abbrev pkOf : List Byte := bytesAt σ.mem (vPk σ) p.pkLen
abbrev muOf : List Byte := bytesAt σ.mem (vMu σ) 64
abbrev sgOf : List Byte := bytesAt σ.mem (vSg σ) p.sigLen

end

/-- The public data of `verifyContract`. -/
def vPub (p : Params) (σ₁ σ₂ : State) : Prop :=
  σ₁.sp = σ₂.sp ∧ vPk σ₁ = vPk σ₂ ∧ vMu σ₁ = vMu σ₂ ∧ vSg σ₁ = vSg σ₂ ∧ vScr σ₁ = vScr σ₂ ∧
    pkOf p σ₁ = pkOf p σ₂ ∧ muOf σ₁ = muOf σ₂ ∧ sgOf p σ₁ = sgOf p σ₂ ∧ vCache σ₁ = vCache σ₂ ∧
    σ₁.gpr .a5 = σ₂.gpr .a5

theorem vSel_pub {p : Params} {σ₁ σ₂ : State} (h : vPub p σ₁ σ₂) : vSel σ₁ = vSel σ₂ := by
  obtain ⟨-, -, -, -, -, -, -, -, e4, e5⟩ := h
  simp only [vSel, vCache] at *
  rw [e4, e5]

/-- The pieces of verification. -/
abbrev VPiece (p : Params) (STK : Nat) := Piece (VPre p STK) (vPub p)

theorem vlay_pub {p : Params} {STK : Nat} {σ₁ σ₂ : State} (h : vPub p σ₁ σ₂) : vlay p STK σ₁ = vlay p STK σ₂ := by
  obtain ⟨e0, e1, e2, e3, e4, -⟩ := h
  simp only [vlay, vPk, vMu, vSg, vScr] at *
  rw [e0, e1, e2, e3, e4]

/-! ## What holds throughout -/

/-- What holds throughout, from the entry state `σ`. -/
structure VC (p : Params) (STK : Nat) (σ s : State) : Prop where
  site : Site (vlay p STK σ) vWb STK s
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  pres : ∀ r ∈ preserved, r ∉ savedTop → s.gpr r = σ.gpr r
  sav : TopSaved s.mem (vScr σ) σ
  pk : bytesAt s.mem ((vlay p STK σ).A 2 0) p.pkLen = pkOf p σ
  mu : bytesAt s.mem ((vlay p STK σ).A 3 0) 64 = muOf σ
  sg : bytesAt s.mem ((vlay p STK σ).A 4 0) p.sigLen = sgOf p σ
  pre : VPre p STK σ
  s3 : s.gpr .s3 = vSel σ
  cache : bytesAt s.mem (vCache σ) (vCLen σ) = bytesAt σ.mem (vCache σ) (vCLen σ)

theorem inputs_eq (p : Params) (STK : Nat) (σ : State) :
    bytesAt σ.mem ((vlay p STK σ).A 2 0) p.pkLen = pkOf p σ ∧ bytesAt σ.mem ((vlay p STK σ).A 3 0) 64 = muOf σ ∧
      bytesAt σ.mem ((vlay p STK σ).A 4 0) p.sigLen = sgOf p σ := by
  simp only [Lay.A, BitVec.add_zero]; exact ⟨rfl, rfl, rfl⟩

theorem saveR_vlay (p : Params) (STK : Nat) (σ : State) : saveR (vScr σ) = (vlay p STK σ).R 0 1288 80 := rfl

/-- A part that writes the regions `W` keeps `VC`. -/
def vcChk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, 1288, 80) W && W.all (fun w => w.1 == 0 || w.1 == 1) &&
    sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (2, 0, p.pkLen) W &&
    sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (3, 0, 64) W &&
    sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (4, 0, p.sigLen) W

/-- Bytes of a buffer only read, kept by a part that writes only buffers of `vWb`. -/
theorem bytes_keepR {L : Lay} (hL : OkW L vWb) {W : List (Nat × Nat × Nat)} {m m' : Mem} (hf : Frame (L.RL W) m m')
    {i o l : Nat} (h : sepAll L.sizes (i, o, l) W = true) (hw : W.all (fun w => w.1 == 0 || w.1 == 1) = true)
    (hl : l ≤ 2 ^ 64) : bytesAt m' (L.A i o) l = bytesAt m (L.A i o) l :=
  Proof.MlKem.bytesAt_frame hf (fun r hr => by
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hr
    refine disjW hL (List.all_eq_true.mp h w hw') (.inr ?_)
    have := List.all_eq_true.mp hw w hw'
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    simp only [vWb, List.mem_cons, List.not_mem_nil, or_false]
    exact this) hl

theorem vfit {p : Params} {STK : Nat} {σ : State} (hL : OkW (vlay p STK σ) vWb) (i : Nat) (hi : i < 5) :
    (vlay p STK σ).size i ≤ 2 ^ 64 := by
  have := hL.fit i (by simp only [vlay, List.length_cons, List.length_nil]; omega_arith)
  omega_arith

theorem VC.keep {p : Params} {STK : Nat} {σ s s' : State} (h : VC p STK σ s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((vlay p STK σ).RL W) s s') (hc : vcChk p STK W = true) : VC p STK σ s' := by
  simp only [vcChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h0, hw⟩, h2⟩, h3⟩, h4⟩ := hc
  have hL := h.site.ok
  have hd : ∀ r ∈ (vlay p STK σ).RL W, ((vlay p STK σ).R 0 1288 80).Disjoint r :=
    fun r hr => by
      obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hr
      exact disjW hL (List.all_eq_true.mp h0 w hw') (.inl (by decide))
  refine ⟨h.site.kept hk, hk.rd.trans h.rd, hk.wr.trans h.wr, hk.sp.trans h.sp,
    fun r hr hs => (hk.cs r hr).trans (h.pres r hr hs), h.sav.keep hk.frame (by rw [saveR_vlay p STK σ]; exact hd),
    ?_, ?_, ?_, h.pre, by rw [hk.cs .s3 (by decide)]; exact h.s3, ?_⟩
  · rw [bytes_keepR hL hk.frame h2 hw (vfit hL 2 (by decide))]; exact h.pk
  · rw [bytes_keepR hL hk.frame h3 hw (by decide)]; exact h.mu
  · rw [bytes_keepR hL hk.frame h4 hw (vfit hL 4 (by decide))]; exact h.sg
  · refine (Proof.MlKem.bytesAt_frame hk.frame (fun r hr => ?_) (by have := h.pre.f_x; omega_arith)).trans h.cache
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hr
    have hb := List.all_eq_true.mp h0 w hw'
    simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at hb
    have e := List.all_eq_true.mp hw w hw'
    simp only [Bool.or_eq_true, beq_iff_eq] at e
    refine Region.Disjoint.symm (Region.Disjoint.sub_left ?_ (Lay.R_sub hb.1.2))
    rcases e with e | e <;> rw [e]
    · exact h.pre.d_cx
    · exact h.pre.b_x

/-! ## The prologue -/

theorem vpro_ok {p : Params} (hF : VFacts p) {STK : Nat} (hSTK : 1168 ≤ STK) {σ : State} (hp : VPre p STK σ) :
    WP isa (.block pro) σ fun s => VC p STK σ s ∧ s.gpr .s4 = 1 := by
  have hL := vlay_ok hp
  have fc := hp.f_c
  have hk := hF.k
  obtain ⟨hs1, -⟩ := hF.scr
  have w0 : (vlay p STK σ).buf 0 ∈ σ.wr := by
    rw [show (vlay p STK σ).buf 0 = reg (vScr σ) (scrLen p) from rfl, hp.wr]
    exact List.mem_singleton_self _
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions σ.wr (vScr σ + BitVec.ofNat 64 o) n := fun {o n} h =>
    Lay.covers (L := vlay p STK σ) (o := o) (l := n) w0 (by rw [vlay_size0]; omega_arith) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [pro, VG.Impl.MlDsa.RISCV64.KeyGen.pro, List.append_assoc, WP.block_append_iff]
  refine WP.mono (topSave_ok rfl hp.al_c fun o _ h₂ => wS (by omega_arith))
    fun s₁ ⟨sav, fr, g₁, rd₁, wr₁, sp₁⟩ => ?_
  have g3 : s₁.gpr .a0 = vPk σ := by rw [g₁]
  have g4 : s₁.gpr .a1 = vMu σ := by rw [g₁]
  have g5 : s₁.gpr .a2 = vSg σ := by rw [g₁]
  have g6 : s₁.gpr .a3 = vScr σ := by rw [g₁]
  have g7 : s₁.gpr .a4 = vCache σ := by rw [g₁]
  have g8 : s₁.gpr .a5 = σ.gpr .a5 := by rw [g₁]
  have hmv : WP isa (.block ([mov .s10 .a0, mov .s9 .a1, mov .s8 .a2, mov .s11 .a3, .li .s4 1] ++
      [.li .t2 0, .sltu .t0 .t2 .a5, .sub .t0 .t2 .t0, .logic .and .s3 .a4 .t0])) s₁ fun s =>
      s.gpr .s10 = vPk σ ∧ s.gpr .s9 = vMu σ ∧ s.gpr .s8 = vSg σ ∧ s.gpr .s11 = vScr σ ∧
      s.gpr .s4 = 1 ∧ s.gpr .s3 = vSel σ ∧ (∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₁.gpr r) ∧
      s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₁.sp := by
    simp only [List.cons_append, List.nil_append]
    mrun [mov, g3, g4, g5, g6, g7, g8]
    refine ⟨rfl, CacheCopy.sel_eq _ _, fun r hr hs => ?_⟩
    simp only [savedTop, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
    obtain ⟨a3, a4, -, -, -, a8, a9, a10, a11⟩ := hs
    have t0 : r ≠ .t0 := fun e => by subst e; revert hr; decide
    have t2 : r ≠ .t2 := fun e => by subst e; revert hr; decide
    simp only [a3, a4, a8, a9, a10, a11, t0, t2, ite_false]
  have hin : ∀ {i l : Nat}, i = 2 ∨ i = 3 ∨ i = 4 → l = (vlay p STK σ).size i →
      bytesAt s₁.mem ((vlay p STK σ).A i 0) l = bytesAt σ.mem ((vlay p STK σ).A i 0) l := fun {i l} hi hl => by
    refine Proof.MlKem.bytesAt_frame fr (fun r hr => ?_) (by rw [hl]; exact vfit hL i (by omega_arith))
    rw [List.mem_singleton] at hr; subst hr
    rw [saveR_vlay p STK σ]
    refine disjW' (i := i) (o := 0) (l := l) (j := 0) (o' := 1288) (l' := 80) hL ?_ (.inr (.inl (by decide)))
    subst hl
    rcases hi with rfl | rfl | rfl <;> vsep hF [vlay, Lay.size]
  obtain ⟨ep, em, es⟩ := inputs_eq p STK σ
  refine WP.mono hmv fun s ⟨g30, g29, g28, g31, g24, g19, cs, m, rd, wr, sp⟩ => ⟨⟨⟨hL, rfl, by decide, by decide,
    by rw [vlay_size0]; omega_arith, rfl, by rw [sp, sp₁]; rfl, hSTK, by rw [sp, sp₁]; exact hp.stk,
    by rw [sp, sp₁]; exact hp.al, hp.al_c, g31, g30, g29, g28,
    fun i hi hi1 => ?_, fun i hi hi1 => ?_⟩, rd.trans rd₁, wr.trans wr₁, sp.trans sp₁,
    fun r hr hs => (cs r hr hs).trans (by rw [g₁]), by rw [m]; exact sav,
    ?_, ?_, ?_, hp, g19, ?_⟩, g24⟩
  · show _ ∈ s.wr
    rw [wr, wr₁, hp.wr]
    simp only [vWb, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · simp [Lay.buf, vlay]
    · exact absurd rfl hi1
  · show _ ∈ s.rd ++ s.wr
    rw [rd, rd₁, wr, wr₁, hp.rd, hp.wr]
    rcases (by omega_arith : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;> simp [Lay.buf, vlay]
  · rw [m, hin (i := 2) (l := p.pkLen) (.inl rfl) rfl]; exact ep
  · rw [m, hin (i := 3) (l := 64) (.inr (.inl rfl)) rfl]; exact em
  · rw [m, hin (i := 4) (l := p.sigLen) (.inr (.inr rfl)) rfl]; exact es
  · rw [m]
    refine Proof.MlKem.bytesAt_frame fr (fun r hr => ?_) (by have := hp.f_x; omega_arith)
    rw [List.mem_singleton] at hr; subst hr
    rw [saveR_vlay p STK σ]
    exact (hp.d_cx.sub_left (Lay.R_sub (L := vlay p STK σ) (i := 0) (by rw [vlay_size0]; omega_arith))).symm

theorem vpro_piece {p : Params} (hF : VFacts p) {STK : Nat} (hSTK : 1168 ≤ STK) :
    VPiece p STK (fun σ s => s = σ) (fun σ s => VC p STK σ s ∧ s.gpr .s4 = 1) (.block pro) :=
  ⟨fun σ s hp hs => by subst hs; exact vpro_ok hF hSTK hp,
    Sample.taint_block [.a0, .a1, .a2, .a3] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
      subst h₁ h₂; exact pub.1)
      (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      obtain ⟨-, e0, e1, e2, e3, -⟩ := pub
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [e0, e1, e2, e3]) (by taint_decide)⟩

end VG.Proof.MlDsa.RISCV64.Verify

end

end

/-!
# ML-DSA verification on RISC-V: two runs, and the branches on the result

As on PPC64LE (`Proof/MlDsa/PPC64LE/Verify/SampA.lean`): two runs with the
same layout (`VTwo`), the constant time of a piece without calls by the
taint analysis from the pointers (`vrel31`), what holds throughout kept by
writes of `a0` and `s4` (`VC.regs2`), and `ifOk c`, a branch on the result
so far in `s4` (`ifOk_piece`), which is a function of the public data.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Verify

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv taint31 taint4
  Regs2)
open VG.Impl.MlDsa.RISCV64.Verify
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

/-- 1 if `b`, 0 if not. -/
def flag (b : Bool) : BitVec 64 := if b then 1 else 0

theorem flag_ne {b : Bool} : flag b ≠ 0 ↔ b = true := by cases b <;> simp [flag]

theorem vptr_ok {r : Reg} (hr : KeyGen.baseReg r = true) {o : Nat} (h : o < 2 ^ 31 - 2048) :
    KeyGen.argOk (.ptr (r, o)) = true := by
  simp only [KeyGen.argOk, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hr, h⟩

/-- Proves that an offset into the buffers is below `2³¹`, for any parameter
set with the facts `hF`. -/
syntax "vlt " term:max : tactic
macro_rules
  | `(tactic| vlt $hF) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).w1; have := ($hF).w1l; have := ($hF).pk
      have := ($hF).hint; have := ($hF).ct; have := ($hF).lz
      try dsimp only [VG.Impl.MlDsa.RISCV64.Verify.oP, VG.Impl.MlDsa.RISCV64.Verify.oB,
        VG.Impl.MlDsa.RISCV64.Verify.oSS, VG.Impl.MlDsa.RISCV64.Verify.oSB, VG.Impl.MlDsa.RISCV64.Verify.oCT]
      omega))

/-! ## Two runs -/

theorem vc_twoL {p : Params} {STK : Nat} {σ₁ σ₂ x y : State} (pub : vPub p σ₁ σ₂) (h₁ : VC p STK σ₁ x)
    (h₂ : VC p STK σ₂ y) : Two (vlay p STK σ₁) vWb STK x y :=
  ⟨h₁.site, vlay_pub pub ▸ h₂.site, by rw [h₁.sp, h₂.sp, pub.1]⟩

/-- Two runs whose entry states have the same layout. -/
def VTwo (p : Params) (STK : Nat) (x y : State) : Prop := ∃ σ, Two (vlay p STK σ) vWb STK x y

theorem vtaint31 {p : Params} {STK : Nat} {c : Prog isa} {hc : VG.Taint.Hint VG.RISCV64.taint.T}
    (h : (VG.RISCV64.taint.check (Taint.ofRegs [.s11]) c hc).isSome = true) :
    RelCT isa (VTwo p STK) c fun _ _ => True :=
  RelCT.exists_ fun _ => taint31 (fun _ _ h => h) h

theorem vtaint4 {p : Params} {STK : Nat} {c : Prog isa} {hc : VG.Taint.Hint VG.RISCV64.taint.T}
    (h : (VG.RISCV64.taint.check (Taint.ofRegs [.s8, .s9, .s10, .s11]) c hc).isSome = true) :
    RelCT isa (VTwo p STK) c fun _ _ => True :=
  RelCT.exists_ fun _ => taint4 (fun _ _ h => h) h

/-- A piece without calls, checked by the taint analysis from `scratch`. -/
theorem vrel31 {p : Params} {STK : Nat} {I : State → State → Prop} (hI : ∀ σ s, I σ s → VC p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.RISCV64.taint.T}
    (h : (VG.RISCV64.taint.check (Taint.ofRegs [.s11]) c hc).isSome = true) :
    RelCT isa (Rel2 (VPre p STK) (vPub p) I) c fun _ _ => True :=
  rel_of (vtaint31 h) fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, vc_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

/-! ## The state, but for `a0` and `s4` -/

theorem VC.regs2 {p : Params} {STK : Nat} {σ s s' : State} (h : VC p STK σ s) (hr : Regs2 s s') :
    VC p STK σ s' :=
  ⟨h.site.regs2 hr, hr.rd.trans h.rd, hr.wr.trans h.wr, hr.sp.trans h.sp,
    fun r hp hs => by
      have : r ≠ .a0 ∧ r ≠ .s4 := ⟨fun e => by subst e; simp [preserved] at hp,
        fun e => by subst e; simp [savedTop] at hs⟩
      rw [hr.gpr r this.1 this.2]; exact h.pres r hp hs,
    by rw [hr.mem]; exact h.sav, by rw [hr.mem]; exact h.pk, by rw [hr.mem]; exact h.mu, by rw [hr.mem]; exact h.sg,
    h.pre, by rw [hr.gpr .s3 (by decide) (by decide)]; exact h.s3, by rw [hr.mem]; exact h.cache⟩

/-! ## A branch on `s4` -/

/-- `ifOk c`: `c` if `r24 ≠ 0`, where `s4` is `v σ`, a function of the
public data. -/
theorem ifOk_piece {p : Params} {STK : Nat} {I J : State → State → Prop} {c : Prog isa} {v : State → BitVec 64}
    (hv : ∀ σ s, VPre p STK σ → I σ s → s.gpr .s4 = v σ)
    (hpub : ∀ σ₁ σ₂, VPre p STK σ₁ → VPre p STK σ₂ → vPub p σ₁ σ₂ → v σ₁ = v σ₂)
    (hc : VPiece p STK (fun σ s => I σ s ∧ v σ ≠ 0) J c)
    (he : ∀ σ s, VPre p STK σ → I σ s → v σ = 0 → J σ s) :
    VPiece p STK I J (ifOk c) := by
  refine ⟨fun σ s hp hs => ?_, ?_⟩
  · have h24 := hv σ s hp hs
    refine WP.ite _ (Steps.eval_nonzero s .s4) (fun hb => hc.ok σ _ hp ⟨hs, ?_⟩) fun hb => ?_
    · rw [← h24]; simpa using hb
    · have : v σ = 0 := by rw [← h24]; simpa using hb
      exact WP.block_nil (he σ _ hp hs this)
  · refine RelCT.ite ?_ ?_ ?_
    · rintro _ _ ⟨σ₁, σ₂, p₁, p₂, pub, hx, hy⟩
      rw [Steps.eval_nonzero, Steps.eval_nonzero, hv _ _ p₁ hx, hv _ _ p₂ hy, hpub _ _ p₁ p₂ pub]
    · refine RelCT.mono hc.tr (fun _ _ ⟨⟨σ₁, σ₂, p₁, p₂, pub, hx, hy⟩, hb⟩ =>
        ⟨σ₁, σ₂, p₁, p₂, pub, ⟨hx, ?_⟩, ⟨hy, ?_⟩⟩) fun _ _ h => h
      · rw [Steps.eval_nonzero] at hb
        rw [← hv _ _ p₁ hx]; simpa using hb
      · rw [Steps.eval_nonzero] at hb
        rw [← hpub _ _ p₁ p₂ pub, ← hv _ _ p₁ hx]; simpa using hb
    · exact RelCT.block_nil fun _ _ _ => trivial

end VG.Proof.MlDsa.RISCV64.Verify

end

end

/-!
# ML-DSA verification on RISC-V: the primitives, and the hint

As on PPC64LE (`Proof/MlDsa/PPC64LE/Verify/SampA.lean`): the primitives
verification calls, verified with at most `S` bytes of stack (`VPrimsOk`);
and the hint `h` of the signature, unpacked to polynomials `0, …, k - 1`,
with `s4` 1 if it is well formed and 0 if not (`hint_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Verify

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee HbuOk hbu_ok
  hbu_tr zx and24_ok)
open VG.Impl.MlDsa.RISCV64.Verify
open VG.Impl.MlDsa.RISCV64.KeyGen (and24)
open VG.Spec.MlDsa (Params hintBitUnpack)
open VG.Proof.MlDsa (HintIs)
open VG.Spec.Sha3 (bytesAt)

/-! ## The primitives -/

/-- The primitives, each verified against its contract with at most `S`
bytes of stack. -/
structure VPrimsOk (P : Prims) (S : Nat) : Prop where
  ntt : Callee P.ntt (fun stk => Proof.MlDsa.nttContract RISCV64.abi stk) S
  invNtt : Callee P.invNtt (fun stk => Proof.MlDsa.nttInvContract RISCV64.abi stk) S
  mul : Callee P.mul (fun stk => Proof.MlDsa.mulContract RISCV64.abi stk) S
  mulAdd : Callee P.mulAdd (fun stk => Proof.MlDsa.mulAddContract RISCV64.abi stk) S
  sub : Callee P.sub (fun stk => Proof.MlDsa.subContract RISCV64.abi stk) S
  rejNtt : Callee P.rejNtt (fun stk => Proof.MlDsa.rejNTTContract RISCV64.abi stk) S
  ball : Callee P.ball (fun stk => Proof.MlDsa.sampleInBallContract RISCV64.abi stk) S
  useHint : Callee P.useHint (fun stk => Proof.MlDsa.useHintContract RISCV64.abi stk) S
  simpleBitPack : Callee P.simpleBitPack (fun stk => Proof.MlDsa.simpleBitPackContract RISCV64.abi stk) S
  bitUnpack : Callee P.bitUnpack (fun stk => Proof.MlDsa.bitUnpackContract RISCV64.abi stk) S
  unpackT1 : Callee P.unpackT1 (fun stk => Proof.MlDsa.unpackT1Contract RISCV64.abi stk) S
  hintUnpack : Callee P.hintUnpack (fun stk => Proof.MlDsa.hintBitUnpackContract RISCV64.abi stk) S
  normLt : Callee P.normLt (fun stk => Proof.MlDsa.normLtContract RISCV64.abi stk) S

/-! ## The signature -/

/-- `h`, or `⊥`, of the signature of a run from `σ`. -/
abbrev hintOf (p : Params) (σ : State) : Option (List (Vector Bool Spec.MlDsa.n)) :=
  Proof.MlDsa.Verify.vHint p (sgOf p σ)

/-- Bytes of the signature, from its bytes in memory. -/
theorem sig_slice {p : Params} {STK : Nat} {σ s : State} (h : VC p STK σ s) {o l : Nat} (hl : o + l ≤ p.sigLen) :
    bytesAt s.mem ((vlay p STK σ).A 4 o) l = ((sgOf p σ).drop o).take l := by
  have e := h.sg
  simp only [Lay.A, BitVec.add_zero] at e ⊢
  rw [← e, Proof.MlKem.bytesAt_slice _ _ hl]

/-- Bytes of the public key, from its bytes in memory. -/
theorem pk_slice {p : Params} {STK : Nat} {σ s : State} (h : VC p STK σ s) {o l : Nat} (hl : o + l ≤ p.pkLen) :
    bytesAt s.mem ((vlay p STK σ).A 2 o) l = ((pkOf p σ).drop o).take l := by
  have e := h.pk
  simp only [Lay.A, BitVec.add_zero] at e ⊢
  rw [← e, Proof.MlKem.bytesAt_slice _ _ hl]

/-! ## The hint -/

/-- After the hint. -/
structure V1 (p : Params) (STK : Nat) (σ s : State) : Prop where
  vc : VC p STK σ s
  s4 : s.gpr .s4 = flag (hintOf p σ).isSome
  hint : ∀ h, hintOf p σ = some h → HintIs s.mem ((vlay p STK σ).A 0 (oP 0)) p.k h

/-- After the call of `HintBitUnpack`: its result in `a0`. -/
structure H1 (p : Params) (STK : Nat) (σ s : State) : Prop where
  vc : VC p STK σ s
  s4 : s.gpr .s4 = 1
  a0 : zx (s.gpr .a0) = flag (hintOf p σ).isSome
  hint : ∀ h, hintOf p σ = some h → HintIs s.mem ((vlay p STK σ).A 0 (oP 0)) p.k h

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hS in
theorem hint_m {σ : State} :
    HbuOk (vlay p STK σ) vWb (.s8, oHint p) (p.ω + p.k) p.ω (pH 0) (256 * p.k) := by
  have hk := hF.k; have hom := hF.om; have hl := hF.l
  have ho : oHint p < 2 ^ 31 - 2048 := by
    rw [hF.hint]; rcases hF.ct with h | h | h <;> rcases hF.lz with h' | h' <;> rw [h, h'] <;> omega_arith
  exact ⟨⟨vptr_ok rfl ho, by vsep hF⟩, ⟨vptr_ok rfl (by decide), by vsep hF⟩, show ix Reg.s11 ∈ vWb by decide,
    by vsep hF, by rw [Nat.add_sub_cancel_left]; exact hF.hp, by omega_arith, by rw [Nat.add_sub_cancel_left], by omega_arith, by valsep⟩

omit hP hF hS in
theorem zx_of {x : BitVec 64} {b : Bool} (h : x.setWidth 32 = if b then 1 else 0) : zx x = flag b := by
  cases b <;> simp only [zx, h, flag] <;> decide

theorem hbu_ok' {σ s : State} (h : VC p STK σ s) (h24 : s.gpr .s4 = 1) :
    WP isa (hintUnpackAt P (.s8, oHint p) (p.ω + p.k) p.ω (pH 0) (256 * p.k)) s (H1 p STK σ) := by
  have hs := h.site
  unfold hintUnpackAt
  refine hbu_ok hP.hintUnpack hs hS (hint_m hF) fun s' k' hm => ?_
  have h' := h.keep k' (by vsep hF [vcChk])
  have eb : bytesAt s.mem (lpa (vlay p STK σ) (.s8, oHint p)) (p.ω + p.k) =
      ((sgOf p σ).drop (oHint p)).take (p.ω + p.k) := sig_slice h (by rw [hF.sig])
  rw [eb, Nat.add_sub_cancel_left] at hm
  refine ⟨h', by rw [k'.cs _ (by decide)]; exact h24, ?_, fun hh e => ?_⟩
  · show zx (s'.gpr .a0) = flag (hintBitUnpack p.ω p.k (((sgOf p σ).drop (oHint p)).take (p.ω + p.k))).isSome
    refine zx_of ?_
    split at hm
    · rename_i hh e; rw [e]; exact hm.1
    · rename_i e; rw [e]; exact hm
  · show HintIs s'.mem _ p.k hh
    have e' : hintBitUnpack p.ω p.k ((sgOf p σ).drop (oHint p) |>.take (p.ω + p.k)) = some hh := e
    rw [e'] at hm
    exact hm.2

theorem hbu_piece :
    VPiece p STK (fun σ s => VC p STK σ s ∧ s.gpr .s4 = 1) (H1 p STK)
      (hintUnpackAt P (.s8, oHint p) (p.ω + p.k) p.ω (pH 0) (256 * p.k)) := by
  refine ⟨fun σ s _ h => hbu_ok' hP hF hS h.1 h.2, ?_⟩
  unfold hintUnpackAt
  refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
    bytesAt x.mem (lpa (vlay p STK σ) (.s8, oHint p)) (p.ω + p.k) =
      bytesAt y.mem (lpa (vlay p STK σ) (.s8, oHint p)) (p.ω + p.k))
    (RelCT.exists_ fun σ => hbu_tr hP.hintUnpack hS (hint_m hF)
      fun x y ⟨T, e⟩ => ⟨T.1, T.2.1, T.2.2, e⟩) ?_
  intro σ₁ _ _ _ _ _ pub h₁ h₂
  refine ⟨σ₁, vc_twoL pub h₁.1 h₂.1, ?_⟩
  show bytesAt _ ((vlay p STK σ₁).A 4 (oHint p)) _ = bytesAt _ ((vlay p STK σ₁).A 4 (oHint p)) _
  rw [sig_slice h₁.1 (by rw [hF.sig]), pub.2.2.2.2.2.2.2.1, vlay_pub pub, sig_slice h₂.1 (by rw [hF.sig])]

omit hP hF hS in
theorem and24_piece : VPiece p STK (H1 p STK) (V1 p STK) (.block and24) := by
  refine ⟨fun σ s _ h => WP.mono (and24_ok s) fun s' ⟨_, e24, hr⟩ => ⟨h.vc.regs2 hr, ?_, ?_⟩,
    vrel31 (fun _ _ h => h.vc) (by taint_decide)⟩
  · rw [e24, h.s4, h.a0]; cases (hintOf p σ).isSome <;> decide
  · intro hh e; rw [hr.mem]; exact h.hint hh e

theorem hint_piece :
    VPiece p STK (fun σ s => VC p STK σ s ∧ s.gpr .s4 = 1) (V1 p STK) (hint P p) :=
  (hbu_piece hP hF hS).seq and24_piece

end

end VG.Proof.MlDsa.RISCV64.Verify

end

end

/-!
# ML-DSA verification on RISC-V: `z`

As on PPC64LE (`Proof/MlDsa/PPC64LE/Verify/SampA.lean`): each `z[i]`, unpacked
from the signature to polynomial `8 + i`, and `r24 ← r24 ∧ (‖z[i]‖∞ < γ₁ - β)`
(`zOne_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Verify

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee BuOk bu_ok
  bu_tr nl_ok nl_tr polyIs_keepW keepD zx and24_ok)
open VG.Impl.MlDsa.RISCV64.Verify
open VG.Impl.MlDsa.RISCV64.KeyGen (and24)
open VG.Spec.MlDsa (Params toRq normRq)
open VG.Proof.MlDsa (HintIs PolyIs polyAt Reduced)
open VG.Proof.MlDsa.Verify (vZ)
open VG.Spec.Sha3 (bytesAt)

/-- `‖z[i]‖∞ < γ₁ - β` for every `i < j`. -/
abbrev zOk (p : Params) (σ : State) (j : Nat) : Bool :=
  decide (∀ i < j, normRq [toRq (vZ p (sgOf p σ) i)] < p.γ₁ - p.β)

/-- A hint kept by a part that writes apart from it. -/
theorem hintIs_keepW {L : Lay} {Wb : List Nat} (hL : OkW L Wb) {W : List (Nat × Nat × Nat)} {m m' : Mem}
    (hf : Frame (L.RL W) m m') {i o k : Nat} (h : sepAll L.sizes (i, o, 1024 * k) W = true) (hw : i ∈ Wb)
    (hk : 1024 * k ≤ 2 ^ 64) {hh : List (Vector Bool Spec.MlDsa.n)} (hi : HintIs m (L.A i o) k hh) :
    HintIs m' (L.A i o) k hh :=
  Proof.MlDsa.Verify.hintIs_frame hf hk (keepD hL h hw) hi

/-- After the hint and the first `j` of `z`. -/
structure V2 (p : Params) (STK : Nat) (j : Nat) (σ s : State) : Prop where
  vc : VC p STK σ s
  hint : ∃ h, hintOf p σ = some h ∧ HintIs s.mem ((vlay p STK σ).A 0 (oP 0)) p.k h
  z : ∀ i < j, PolyIs s.mem ((vlay p STK σ).A 0 (oP (8 + i))) (toRq (vZ p (sgOf p σ) i))
  s4 : s.gpr .s4 = flag (zOk p σ j)

theorem V2.keep {p : Params} (hF : VFacts p) {STK j : Nat} {σ s s' : State} (h : V2 p STK j σ s)
    {W : List (Nat × Nat × Nat)} (hk : Kept ((vlay p STK σ).RL W) s s') (hc : vcChk p STK W = true)
    (hh : sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP 0, 1024 * p.k) W = true)
    (hz : ∀ i < j, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP (8 + i), 1024) W = true) :
    V2 p STK j σ s' := by
  have hL := h.vc.site.ok
  obtain ⟨hh', e, hi⟩ := h.hint
  exact ⟨h.vc.keep hk hc, ⟨hh', e, hintIs_keepW hL hk.frame hh (by decide) (by have := hF.k; omega_arith) hi⟩,
    fun i hi' => polyIs_keepW hL hk.frame (hz i hi') (by decide) rfl (h.z i hi'),
    by rw [hk.cs _ (by decide)]; exact h.s4⟩

theorem flag_and (a b : Bool) : flag a &&& flag b = flag (a && b) := by
  cases a <;> cases b <;> decide

theorem zOk_succ (p : Params) (σ : State) (j : Nat) :
    zOk p σ (j + 1) = (zOk p σ j && decide (normRq [toRq (vZ p (sgOf p σ) j)] < p.γ₁ - p.β)) := by
  simp only [zOk]
  rw [← Bool.decide_and]
  refine decide_eq_decide.mpr (Iff.intro (fun h => ⟨fun i hi => h i (by omega_arith), h j (by omega_arith)⟩) fun h i hi => ?_)
  rcases (by omega_arith : i < j ∨ i = j) with hi | rfl
  exacts [h.1 i hi, h.2]

/-! ## One `z[i]` -/

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hS in
theorem bu_m {σ : State} {j : Nat} (hj : j < p.ℓ) :
    BuOk (vlay p STK σ) vWb (.s8, p.ctildeLen + lenZ p * j) (lenZ p) (p.γ₁ - 1) p.γ₁ (pZ j) := by
  have hl := hF.l
  obtain ⟨hb, hlz, hg⟩ := hF.bu
  refine ⟨⟨vptr_ok rfl ?_, ?_⟩, ⟨vptr_ok rfl (by unfold oP; omega_arith), by vsep hF⟩, show ix Reg.s11 ∈ vWb by decide,
    ?_, hb, hlz, ?_, ?_⟩
  · rcases hF.ct with e | e | e <;> rcases hF.lz with e' | e' <;> rw [e, e'] <;> omega_arith
  · rcases hF.lz with e | e <;> vsep hF [hF.sig, hF.hint, e]
  · rcases hF.lz with e | e <;> vsep hF [hF.sig, hF.hint, e]
  · rcases hF.lz with e | e <;> rw [e] <;> omega_arith
  · valsep

/-- After `z[j]` is unpacked. -/
abbrev Z1 (p : Params) (STK j : Nat) (σ s : State) : Prop :=
  V2 p STK j σ s ∧ PolyIs s.mem ((vlay p STK σ).A 0 (oP (8 + j))) (toRq (vZ p (sgOf p σ) j))

theorem bu_piece {j : Nat} (hj : j < p.ℓ) :
    VPiece p STK (V2 p STK j) (Z1 p STK j)
      (bitUnpackAt P (.s8, p.ctildeLen + lenZ p * j) (lenZ p) (p.γ₁ - 1) p.γ₁ (pZ j)) := by
  have hl := hF.l
  refine ⟨fun σ s _ h => ?_, ?_⟩
  · unfold bitUnpackAt
    refine bu_ok hP.bitUnpack h.vc.site hS (bu_m hF hj) fun s' k' hz => ⟨h.keep hF k' ?_ ?_ ?_, ?_⟩
    · rcases hF.lz with e | e <;> vsep hF [vcChk, hF.sig, hF.hint, e]
    · vsep hF
    · intro i hi; vsep hF
    · have e : bytesAt s.mem (lpa (vlay p STK σ) (.s8, p.ctildeLen + lenZ p * j)) (lenZ p) =
          ((sgOf p σ).drop (p.ctildeLen + lenZ p * j)).take (lenZ p) :=
        sig_slice h.vc (by rw [hF.sig, hF.hint]; rcases hF.lz with e | e <;> rw [e] <;> omega_arith)
      rw [e] at hz
      exact hz
  · unfold bitUnpackAt
    exact rel_of (RelCT.exists_ fun σ => bu_tr hP.bitUnpack hS (bu_m hF hj) fun x y h => h)
      fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, vc_twoL pub h₁.vc h₂.vc⟩

/-- After the norm of `z[j]`. -/
abbrev Z2 (p : Params) (STK j : Nat) (σ s : State) : Prop :=
  Z1 p STK j σ s ∧ zx (s.gpr .a0) = flag (decide (normRq [toRq (vZ p (sgOf p σ) j)] < p.γ₁ - p.β))

theorem nl_piece {j : Nat} (hj : j < p.ℓ) :
    VPiece p STK (Z1 p STK j) (Z2 p STK j) (normLtAt P (pZ j) (p.γ₁ - p.β)) := by
  have hl := hF.l
  have pf : ∀ σ, PtrIn (vlay p STK σ) (pZ j) 1024 := fun σ => ⟨vptr_ok rfl (by unfold oP; omega_arith), by vsep hF⟩
  refine ⟨fun σ s _ h => ?_, ?_⟩
  · unfold normLtAt
    have hr0 : Reduced s.mem (lpa (vlay p STK σ) (pZ j)) := h.2.1
    have hb : p.γ₁ - p.β < 2 ^ 31 - 2048 := hF.nb.1
    refine nl_ok hP.normLt h.1.vc.site hS (bd := p.γ₁ - p.β) (pf σ) (by valsep) hb hr0 fun s' k' hr => ⟨⟨h.1.keep hF k'
      (by vsep hF [vcChk]) (by vsep hF) (fun i hi => by vsep hF),
      polyIs_keepW h.1.vc.site.ok k'.frame (by vsep hF) (by decide) rfl h.2⟩, ?_⟩
    rw [show polyAt s.mem (lpa (vlay p STK σ) (pZ j)) = _ from h.2.2] at hr
    exact zx_of (by rw [hr]; simp only [decide_eq_true_eq])
  · unfold normLtAt
    refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      Reduced x.mem (lpa (vlay p STK σ) (pZ j)) ∧ Reduced y.mem (lpa (vlay p STK σ) (pZ j)))
      (RelCT.exists_ fun σ => nl_tr hP.normLt hS (bd := p.γ₁ - p.β) (pf σ) (by valsep) hF.nb.1
        fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
      fun σ₁ _ _ _ _ _ pub h₁ h₂ => ?_
    have r₂ : Reduced _ (lpa (vlay p STK _) (pZ j)) := h₂.2.1
    rw [← vlay_pub pub] at r₂
    exact ⟨σ₁, vc_twoL pub h₁.1.vc h₂.1.vc, h₁.2.1, r₂⟩

omit hP hF hS in
theorem and24z_piece {j : Nat} : VPiece p STK (Z2 p STK j) (V2 p STK (j + 1)) (.block and24) := by
  refine ⟨fun σ s _ h => WP.mono (and24_ok s) fun s' ⟨_, e24, hr⟩ => ?_,
    vrel31 (fun _ _ h => h.1.1.vc) (by taint_decide)⟩
  obtain ⟨hh, e, hi⟩ := h.1.1.hint
  refine ⟨h.1.1.vc.regs2 hr, ⟨hh, e, by rw [hr.mem]; exact hi⟩, fun i hi' => ?_, ?_⟩
  · rw [hr.mem]
    rcases (by omega_arith : i < j ∨ i = j) with hi' | rfl
    exacts [h.1.1.z i hi', h.1.2]
  · rw [e24, h.1.1.s4, h.2, flag_and, zOk_succ]

theorem zOne_piece {j : Nat} (hj : j < p.ℓ) : VPiece p STK (V2 p STK j) (V2 p STK (j + 1)) (zOne P p j) :=
  (bu_piece hP hF hS hj).seq ((nl_piece hP hF hS hj).seq and24z_piece)

end

end VG.Proof.MlDsa.RISCV64.Verify

end

end

/-!
# ML-DSA verification on RISC-V: `Â`

As on PPC64LE (`Proof/MlDsa/PPC64LE/Verify/SampA.lean`): once the signature
is checked (`VB`), `ρ` to the seed `SB`, and each `Â[r, s]` sampled to
polynomial `20 + 8r + s`, its result ANDed into `s4` and the polynomial
masked with it (`rows_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Verify

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee RnOk rn_ok
  rn_tr polyIs_keepW polyAt_keepW reduced_keepW bytes_keepW keepD setB_ok copyS andMask_ok masked_poly taint31
  zx zx_01 zx_one Regs2)
open VG.Impl.MlDsa.RISCV64.Verify
open VG.Impl.MlDsa.RISCV64.KeyGen (and24 mask setB seqR sampled)
open VG.Impl.MlKem.RISCV64 (copy)
open VG.Spec.MlDsa (Params toRq normRq rejNTTPoly minBounds Outcome)
open VG.Proof.MlDsa (HintIs PolyIs polyAt Reduced)
open VG.Proof.MlDsa.Verify (vZ vRho aSeed)
open VG.Proof.MlDsa.KeyGen (ifp ifn seedA_eq)
open VG.Spec.Sha3 (bytesAt)

/-! ## After the checks of the signature -/

/-- The hint well formed and `z` small, in memory. -/
structure VB (p : Params) (STK : Nat) (σ s : State) : Prop where
  vc : VC p STK σ s
  hint : ∃ h, hintOf p σ = some h ∧ HintIs s.mem ((vlay p STK σ).A 0 (oP 0)) p.k h
  z : ∀ i < p.ℓ, PolyIs s.mem ((vlay p STK σ).A 0 (oP (8 + i))) (toRq (vZ p (sgOf p σ) i))
  zok : zOk p σ p.ℓ = true

theorem VB.keep {p : Params} (hF : VFacts p) {STK : Nat} {σ s s' : State} (h : VB p STK σ s)
    {W : List (Nat × Nat × Nat)} (hk : Kept ((vlay p STK σ).RL W) s s') (hc : vcChk p STK W = true)
    (hh : sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP 0, 1024 * p.k) W = true)
    (hz : ∀ i < p.ℓ, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP (8 + i), 1024) W = true) :
    VB p STK σ s' := by
  have hL := h.vc.site.ok
  obtain ⟨hh', e, hi⟩ := h.hint
  exact ⟨h.vc.keep hk hc, ⟨hh', e, hintIs_keepW hL hk.frame hh (by decide) (by have := hF.k; omega_arith) hi⟩,
    fun i hi' => polyIs_keepW hL hk.frame (hz i hi') (by decide) rfl (h.z i hi'), h.zok⟩

theorem VB.regs2 {p : Params} {STK : Nat} {σ s s' : State} (h : VB p STK σ s) (hr : Regs2 s s') :
    VB p STK σ s' := by
  obtain ⟨hh, e, hi⟩ := h.hint
  exact ⟨h.vc.regs2 hr, ⟨hh, e, by rw [hr.mem]; exact hi⟩, fun i hi' => by rw [hr.mem]; exact h.z i hi', h.zok⟩

/-- The entry `(r', s')` comes before `(r, c)`. -/
abbrev Dn (r c r' s' : Nat) : Prop := r' < r ∨ (r' = r ∧ s' < c)

/-- The address of `Â[r, s]`. -/
abbrev aA (p : Params) (STK : Nat) (σ : State) (r s : Nat) : Addr := (vlay p STK σ).A 0 (oP (20 + 8 * r + s))

/-- After the entries of `Â` before `(r, c)`. -/
structure VS (p : Params) (STK : Nat) (r c : Nat) (σ s : State) : Prop where
  vb : VB p STK σ s
  rho : bytesAt s.mem ((vlay p STK σ).A 0 oSB) 32 = vRho (pkOf p σ)
  red : ∀ r' s', s' < p.ℓ → Dn r c r' s' → Reduced s.mem (aA p STK σ r' s')
  ok : ∃ q : Bool, s.gpr .s4 = flag q ∧
    (q = true → ∀ r' s', s' < p.ℓ → Dn r c r' s' →
      ∃ b : Nat, rejNTTPoly b (aSeed (pkOf p σ) r' s') = some (polyAt s.mem (aA p STK σ r' s'))) ∧
    (q = false → ∃ r' s', s' < p.ℓ ∧ Dn r c r' s' ∧ rejNTTPoly minBounds.rejNTT (aSeed (pkOf p σ) r' s') = none)

theorem Dn.lt {r c r' s' : Nat} (hd : Dn r c r' s') (hs : s' < 8) (hc : c ≤ 8) : 8 * r' + s' < 8 * r + c ∧ r' ≤ r := by
  rcases hd with h | ⟨rfl, h⟩ <;> omega_arith

theorem flag_and01 (q : Bool) {x : BitVec 64} (hx : x.setWidth 32 = 0 ∨ x.setWidth 32 = 1) :
    flag q &&& zx x = flag (q && decide (x.setWidth 32 = 1)) := by
  rcases hx with h | h <;> simp only [zx, h] <;> cases q <;> decide

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

/-! ## `ρ` to the seed -/

omit hP hS in
theorem rho_ok {σ s : State} (h : VB p STK σ s) (h24 : s.gpr .s4 = 1) :
    WP isa (copy .s10 0 .s11 oSB 32) s (VS p STK 0 0 σ) := by
  obtain hk := hF.k; have hl := hF.l
  refine WP.mono (copyS h.vc.site (sb := .s10) (so := 0) (db := .s11) (dO := oSB) (len := 32)
    ⟨vptr_ok rfl (by decide), by vsep hF⟩ ⟨vptr_ok rfl (by decide), by vsep hF⟩ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by vsep hF))
    fun s' ⟨k', b'⟩ => ⟨h.keep hF k' (by vsep hF [vcChk]) (by vsep hF) (fun i hi => by vsep hF), ?_,
      fun _ _ _ hd => absurd hd (by omega_arith), ⟨true, by rw [k'.cs .s4 (by decide), h24]; rfl,
        fun _ _ _ _ hd => absurd hd (by omega_arith), fun h => absurd h (by decide)⟩⟩
  show bytesAt s'.mem (lpa (vlay p STK σ) (.s11, oSB)) 32 = _
  rw [b', show lpa (vlay p STK σ) (.s10, 0) = (vlay p STK σ).A 2 0 from rfl, pk_slice h.vc (by rw [hF.pk]; omega_arith),
    List.drop_zero]
  rfl

/-! ## One entry -/

omit hP hS in
theorem rn_m {σ : State} {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) :
    RnOk (vlay p STK σ) vWb (sc oSB) (pS (20 + (8 * r + c))) (sc oSS) := by
  obtain hk := hF.k; have hl := hF.l
  exact ⟨⟨vptr_ok rfl (by decide), by vsep hF⟩, ⟨vptr_ok rfl (by unfold oP; omega_arith), by vsep hF⟩,
    ⟨vptr_ok rfl (by decide), by vsep hF⟩, show ix Reg.s11 ∈ vWb by decide,
    show ix Reg.s11 ∈ vWb by decide, by vsep hF, by vsep hF, by vsep hF, by valsep, by valsep⟩

theorem aOne_ok {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) {σ s : State} (h : VS p STK r c σ s) :
    WP isa (aOne P (8 * r + c)) s (VS p STK r (c + 1) σ) := by
  obtain hk := hF.k; have hl := hF.l
  have hs := h.vb.vc.site
  have hL := hs.ok
  unfold aOne sampled
  obtain e8 : (8 * r + c) % 8 = c := by omega_arith
  obtain e8' : (8 * r + c) / 8 = r := by omega_arith
  rw [e8, e8']
  -- `s` and `r` to the seed
  refine WP.seq (WP.block_append (WP.mono (setB_ok hs (q := sc (oSB + 32)) ⟨vptr_ok rfl (by decide), by vsep hF⟩
    (by decide) (by decide) (v := c) (by omega_arith)) fun s₁ ⟨k₁, b₁⟩ => WP.mono (setB_ok (hs.kept k₁)
      (q := sc (oSB + 33)) ⟨vptr_ok rfl (by decide), by vsep hF⟩ (by decide) (by decide) (v := r) (by omega_arith))
      fun s₂ ⟨k₂, b₂⟩ => ?_))
  obtain kv := (h.vb.keep hF k₁ (by vsep hF [vcChk]) (by vsep hF) (fun i hi => by vsep hF)).keep hF k₂
    (by vsep hF [vcChk]) (by vsep hF) (fun i hi => by vsep hF)
  obtain hseed : bytesAt s₂.mem ((vlay p STK σ).A 0 oSB) 34 = aSeed (pkOf p σ) r c := by
    obtain b₀ := (bytes_keepW hL k₂.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans
      ((bytes_keepW hL k₁.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans h.rho)
    obtain b₁' := bytes_keepW hL k₂.frame (i := 0) (o := oSB + 32) (l := 1) (by vsep hF) (by decide) (by decide)
    rw [show (34 : Nat) = 32 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, b₀,
      show aSeed (pkOf p σ) r c = _ from seedA_eq (vRho (pkOf p σ)) r c, List.append_assoc]
    refine congrArg _ ?_
    obtain e1 : bytesAt s₂.mem ((vlay p STK σ).A 0 (oSB + 32)) 1 = [BitVec.ofNat 8 c] := b₁'.trans b₁
    have e2 : bytesAt s₂.mem ((vlay p STK σ).A 0 (oSB + 33)) 1 = [BitVec.ofNat 8 r] := b₂
    simp only [Lay.A, BitVec.add_assoc, ← BitVec.ofNat_add] at e1 e2 ⊢
    rw [e1, e2]; rfl
  obtain kept12 : ∀ r' s', s' < p.ℓ → Dn r c r' s' → polyAt s₂.mem (aA p STK σ r' s') = polyAt s.mem (aA p STK σ r' s') ∧
      (Reduced s.mem (aA p STK σ r' s') → Reduced s₂.mem (aA p STK σ r' s')) := fun r' s' hs' hd => by
    have := hd.lt (by omega_arith) (by omega_arith)
    exact
    ⟨(polyAt_keepW hL k₂.frame (by vsep hF) (by decide) rfl).trans (polyAt_keepW hL k₁.frame (by vsep hF) (by decide) rfl),
      fun hr' => reduced_keepW hL k₂.frame (by vsep hF) (by decide) rfl (reduced_keepW hL k₁.frame (by vsep hF)
        (by decide) rfl hr')⟩
  obtain h24₂ : s₂.gpr .s4 = s.gpr .s4 := by rw [k₂.cs .s4 (by decide), k₁.cs .s4 (by decide)]
  -- the call
  refine WP.seq (rn_ok hP.rejNtt kv.vc.site hS (rn_m hF hr hc) fun s₃ k₃ hred hout => ?_)
  have hseed' : bytesAt s₂.mem (lpa (vlay p STK σ) (sc oSB)) 34 = _ := hseed
  rw [hseed'] at hout
  obtain hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  obtain kv₃ := kv.keep hF k₃ (by vsep hF [vcChk]) (by vsep hF) (fun i hi => by vsep hF)
  obtain kept3 : ∀ r' s', s' < p.ℓ → Dn r c r' s' → polyAt s₃.mem (aA p STK σ r' s') = polyAt s₂.mem (aA p STK σ r' s') ∧
      (Reduced s₂.mem (aA p STK σ r' s') → Reduced s₃.mem (aA p STK σ r' s')) := fun r' s' hs' hd => by
    have := hd.lt (by omega_arith) (by omega_arith)
    exact
    ⟨polyAt_keepW hL k₃.frame (by vsep hF) (by decide) rfl,
      fun hr' => reduced_keepW hL k₃.frame (by vsep hF) (by decide) rfl hr'⟩
  obtain rho₃ : bytesAt s₃.mem ((vlay p STK σ).A 0 oSB) 32 = vRho (pkOf p σ) :=
    (bytes_keepW hL k₃.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans
      ((bytes_keepW hL k₂.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans
        ((bytes_keepW hL k₁.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans h.rho))
  obtain h24₃ : s₃.gpr .s4 = s.gpr .s4 := by rw [k₃.cs .s4 (by decide), h24₂]
  -- the result and the mask
  refine WP.mono (andMask_ok kv₃.vc.site (a := pS (20 + (8 * r + c))) ⟨vptr_ok rfl (by unfold oP; omega_arith), by vsep hF⟩
    (by valsep) (show ix Reg.s11 ∈ vWb by decide) hr01) fun s₄ ⟨s₅, r₅, k₄, r₄, co⟩ => ?_
  obtain ⟨pi, p1, _⟩ := masked_poly hred co
  obtain kv₄ := (kv₃.regs2 r₅).keep hF k₄ (by vsep hF [vcChk]) (by vsep hF) (fun i hi => by vsep hF)
  obtain kept4 : ∀ r' s', s' < p.ℓ → Dn r c r' s' → polyAt s₄.mem (aA p STK σ r' s') = polyAt s₃.mem (aA p STK σ r' s') ∧
      (Reduced s₃.mem (aA p STK σ r' s') → Reduced s₄.mem (aA p STK σ r' s')) := fun r' s' hs' hd => by
    have := hd.lt (by omega_arith) (by omega_arith)
    rw [← r₅.mem]
    exact
    ⟨polyAt_keepW hL k₄.frame (by vsep hF) (by decide) rfl,
      fun hr' => reduced_keepW hL k₄.frame (by vsep hF) (by decide) rfl hr'⟩
  obtain ea : lpa (vlay p STK σ) (pS (20 + (8 * r + c))) = aA p STK σ r c := by
    show (vlay p STK σ).A 0 (oP (20 + (8 * r + c))) = _
    rw [← Nat.add_assoc]
  rw [ea] at pi p1 hout
  obtain ⟨q, hq, hok, hbad⟩ := h.ok
  refine ⟨kv₄, (bytes_keepW hL k₄.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans
      (by rw [r₅.mem]; exact rho₃),
    fun r' s' hs' hd => ?_, ⟨q && decide ((s₃.gpr .a0).setWidth 32 = 1), ?_, fun hq' r' s' hs' hd => ?_, fun hq' => ?_⟩⟩
  · have := hd.lt (by omega_arith) (by omega_arith)
    rcases (by omega_arith : Dn r c r' s' ∨ (r' = r ∧ s' = c)) with hd | ⟨rfl, rfl⟩
    · exact (kept4 r' s' hs' hd).2 ((kept3 r' s' hs' hd).2 ((kept12 r' s' hs' hd).2 (h.red r' s' hs' hd)))
    · exact pi.1
  · rw [r₄, h24₃, hq, flag_and01 q hr01]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
    rcases (by omega : Dn r c r' s' ∨ (r' = r ∧ s' = c)) with hd | ⟨rfl, rfl⟩
    · obtain ⟨b, hb⟩ := hok hq'.1 r' s' hs' hd
      refine ⟨b, ?_⟩
      rw [(kept4 r' s' hs' hd).1, (kept3 r' s' hs' hd).1, (kept12 r' s' hs' hd).1]
      exact hb
    · rw [p1 hq'.2]
      rcases hout with ⟨_, b, hb⟩ | ⟨h0, _⟩
      · exact ⟨b.rejNTT, hb⟩
      · rw [h0] at hq'; exact absurd hq'.2 (by decide)
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hq'
    rcases hq' with hq' | hq'
    · obtain ⟨r', s', hs', hd, hn⟩ := hbad hq'
      exact ⟨r', s', hs', by omega, hn⟩
    · rcases hout with ⟨h1, _⟩ | ⟨_, hn⟩
      · exact absurd h1 hq'
      · exact ⟨r, c, hc, by omega_arith, hn⟩

/-! ## Constant time -/

omit hP hF hS in
theorem vsetB2_taint : ∀ v < 8, ∀ w < 8, (VG.RISCV64.taint.check (Taint.ofRegs [.s11])
    (.block (setB (sc (oSB + 32)) v ++ setB (sc (oSB + 33)) w)) (.block [])).isSome = true := by decide +kernel

omit hP hF hS in
/-- The check is the same for every offset: its hint is computed once. -/
theorem vAndMask_taint : ∀ j < 128, (VG.RISCV64.taint.check (Taint.ofRegs [.s11])
    (.seq (.block and24) (mask (pS j)))
    (VG.Taint.hintOf VG.RISCV64.taint (Taint.ofRegs [.s11]) (.seq (.block and24) (mask (sc 0))))).isSome = true := by
  decide +kernel

theorem aOne_two {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) (σ : State) :
    RelCT isa (fun x y => Two (vlay p STK σ) vWb STK x y ∧
      bytesAt x.mem ((vlay p STK σ).A 0 oSB) 32 = bytesAt y.mem ((vlay p STK σ).A 0 oSB) 32) (aOne P (8 * r + c))
      fun _ _ => True := by
  obtain hk := hF.k; have hl := hF.l
  unfold aOne sampled
  obtain e8 : (8 * r + c) % 8 = c := by omega_arith
  obtain e8' : (8 * r + c) / 8 = r := by omega_arith
  rw [e8, e8']
  let F := fun (x x' : State) => (∃ rs, Kept rs x x') ∧
    bytesAt x'.mem ((vlay p STK σ).A 0 oSB) 34 = bytesAt x.mem ((vlay p STK σ).A 0 oSB) 32 ++
      [BitVec.ofNat 8 c, BitVec.ofNat 8 r]
  obtain hF1 : ∀ x, Site (vlay p STK σ) vWb STK x →
      WP isa (.block (setB (sc (oSB + 32)) c ++ setB (sc (oSB + 33)) r)) x (F x) := fun x hs =>
    WP.block_append (WP.mono (setB_ok hs (q := sc (oSB + 32)) ⟨vptr_ok rfl (by decide), by vsep hF⟩ (by decide)
      (by decide) (v := c) (by omega_arith)) fun s₁ ⟨k₁, b₁⟩ => WP.mono (setB_ok (hs.kept k₁) (q := sc (oSB + 33))
        ⟨vptr_ok rfl (by decide), by vsep hF⟩ (by decide) (by decide) (v := r) (by omega_arith)) fun s₂ ⟨k₂, b₂⟩ =>
        ⟨⟨_, (k₁.monoL (W' := [tri (sc (oSB + 32)) 1, tri (sc (oSB + 33)) 1]) (by simp)).trans (k₂.monoL (by simp))⟩,
        by
        have hL := hs.ok
        obtain b₁' := bytes_keepW hL k₂.frame (i := 0) (o := oSB + 32) (l := 1) (by vsep hF) (by decide) (by decide)
        obtain b₀ := (bytes_keepW hL k₂.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans
          (bytes_keepW hL k₁.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide))
        rw [show (34 : Nat) = 32 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, b₀,
          List.append_assoc]
        refine congrArg _ ?_
        obtain e1 : bytesAt s₂.mem ((vlay p STK σ).A 0 (oSB + 32)) 1 = [BitVec.ofNat 8 c] := b₁'.trans b₁
        have e2 : bytesAt s₂.mem ((vlay p STK σ).A 0 (oSB + 33)) 1 = [BitVec.ofNat 8 r] := b₂
        simp only [Lay.A, BitVec.add_assoc, ← BitVec.ofNat_add] at e1 e2 ⊢
        rw [e1, e2]; rfl⟩)
  refine RelCT.seq ((RelCT.wpDep (M := isa) (P := fun x y => Two (vlay p STK σ) vWb STK x y ∧
      bytesAt x.mem ((vlay p STK σ).A 0 oSB) 32 = bytesAt y.mem ((vlay p STK σ).A 0 oSB) 32)
    (taint31 (fun _ _ h => h.1) (vsetB2_taint _ (by omega_arith) _ (by omega_arith))) (F := F)
    fun x y h => ⟨hF1 x h.1.1, hF1 y h.1.2.1⟩).mono (fun _ _ h => h)
      (Q' := fun (x y : State) => Two (vlay p STK σ) vWb STK x y ∧
        bytesAt x.mem ((vlay p STK σ).A 0 oSB) 34 = bytesAt y.mem ((vlay p STK σ).A 0 oSB) 34)
      fun x' y' ⟨_, x, y, ⟨T, e32⟩, ⟨⟨_, kx⟩, bx⟩, ⟨⟨_, ky⟩, by'⟩⟩ =>
        ⟨⟨T.1.kept kx, T.2.1.kept ky, by rw [kx.sp, ky.sp]; exact T.2.2⟩, by rw [bx, by', e32]⟩) ?_
  obtain ok := fun x (hs : Site (vlay p STK σ) vWb STK x) =>
    rn_ok hP.rejNtt hs hS (name := "vg_mldsa_rej_ntt_poly") (rn_m hF (σ := σ) hr hc)
      (Q := fun x' => ∃ rs, Kept rs x x') fun _ k _ _ => ⟨_, k⟩
  refine RelCT.seq (VG.Proof.MlDsa.RISCV64.KeyGen.RelCT.two (fun _ _ h => h.1) (rn_tr hP.rejNtt hS (rn_m hF hr hc)
      fun x y h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩) fun x hs => ok x hs) ?_
  exact taint31 (fun _ _ h => h) (vAndMask_taint _ (by omega_arith))

theorem aOne_piece {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) :
    VPiece p STK (VS p STK r c) (VS p STK r (c + 1)) (aOne P (8 * r + c)) :=
  ⟨fun _ _ _ h => aOne_ok hP hF hS hr hc h,
    rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      bytesAt x.mem ((vlay p STK σ).A 0 oSB) 32 = bytesAt y.mem ((vlay p STK σ).A 0 oSB) 32)
      (RelCT.exists_ fun σ => aOne_two hP hF hS hr hc σ) fun σ₁ _ _ _ _ _ pub h₁ h₂ =>
        ⟨σ₁, vc_twoL pub h₁.vb.vc h₂.vb.vc, by rw [h₁.rho, vlay_pub pub, h₂.rho, pub.2.2.2.2.2.1]⟩⟩

/-! ## The rows -/

omit hP hF hS in
theorem VS.next {r : Nat} {σ s : State} (h : VS p STK r p.ℓ σ s) : VS p STK (r + 1) 0 σ s := by
  obtain e : ∀ r' s', s' < p.ℓ → (Dn (r + 1) 0 r' s' ↔ Dn r p.ℓ r' s') := fun r' s' hs => by
    simp only [Dn]; omega_arith
  obtain ⟨q, hq, hok, hbad⟩ := h.ok
  exact ⟨h.vb, h.rho, fun r' s' hs hd => h.red r' s' hs ((e r' s' hs).mp hd),
    ⟨q, hq, fun hq' r' s' hs hd => hok hq' r' s' hs ((e r' s' hs).mp hd),
      fun hq' => let ⟨r', s', hs, hd, hn⟩ := hbad hq'; ⟨r', s', hs, (e r' s' hs).mpr hd, hn⟩⟩⟩

theorem aRow_piece {r : Nat} (hr : r < p.k) : VPiece p STK (VS p STK r 0) (VS p STK (r + 1) 0) (aRow P p r) := by
  have hl := hF.l
  unfold aRow
  refine Piece.mono (Piece.seqR (I := fun e σ s => VS p STK r (e - 8 * r) σ s) p.ℓ (8 * r)
    fun e h1 h2 => ?_) (fun σ s _ h => by simpa using h) fun σ s _ h => VS.next (by simpa using h)
  have := aOne_piece hP hF hS hr (c := e - 8 * r) (by omega_arith)
  rw [show 8 * r + (e - 8 * r) = e by omega_arith, show e - 8 * r + 1 = e + 1 - 8 * r by omega_arith] at this
  exact this

theorem rows_piece : VPiece p STK (VS p STK 0 0) (VS p STK p.k 0) (seqR (aRow P p) 0 p.k) := by
  refine Piece.mono (Piece.seqR (I := fun r => VS p STK r 0) p.k 0 fun r _ hr => aRow_piece hP hF hS (by omega_arith))
    (fun _ _ _ h => h) fun σ s _ h => ?_
  simpa using h

end

end VG.Proof.MlDsa.RISCV64.Verify

end

end

/-!
# ML-DSA verification on RISC-V: after the samplers

As on PPC64LE (`Proof/MlDsa/PPC64LE/Verify/Cmp.lean`): once the samplers
are done, with `Â` and `c` in memory as `A'` and `cc` and `s4` as `R`, the
rest of the function computes `w′₁` from them, whatever they are (`KC5`);
which writes keep it (`K5Chk`, `k5chks`); and the NTTs of `z` and `c`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Verify

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee ip_ok ip_tr
  polyIs_keepW polyAt_keepW reduced_keepW bytes_keepW keepD)
open VG.Impl.MlDsa.RISCV64.Verify
open VG.Spec.MlDsa (Params toRq ntt simpleBitPack)
open VG.Proof.MlDsa (HintIs PolyIs polyAt Reduced)
open VG.Proof.MlDsa.Verify (vZ zHat w1Row)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-- What the samplers give, with `R` their result: `A'` and `cc` those of the
standard for some bounds if `R` is 1, and a sampler failing within the least
bounds if 0. -/
def Gd (p : Params) (σ : State) (A' : Nat → Nat → Spec.MlDsa.Poly) (cc : Spec.MlDsa.Poly) (R : BitVec 64) : Prop :=
  ∃ q : Bool, R = flag q ∧
    (q = true → (∀ r < p.k, ∀ s' < p.ℓ, ∃ b : Nat,
      Spec.MlDsa.rejNTTPoly b (Proof.MlDsa.Verify.aSeed (pkOf p σ) r s') = some (A' r s')) ∧
      ∃ b : Nat, (Spec.MlDsa.sampleInBall p.τ b (Proof.MlDsa.Verify.vCt p (sgOf p σ))).map toRq = some cc) ∧
    (q = false → (∃ r < p.k, ∃ s' < p.ℓ, Spec.MlDsa.rejNTTPoly Spec.MlDsa.minBounds.rejNTT
      (Proof.MlDsa.Verify.aSeed (pkOf p σ) r s') = none) ∨
      Spec.MlDsa.sampleInBall p.τ Spec.MlDsa.minBounds.ball (Proof.MlDsa.Verify.vCt p (sgOf p σ)) = none)

/-- After the samplers: `w′₁` from `A'` and `cc`, so far. -/
structure KC5 (p : Params) (STK : Nat) (σ : State) (A' : Nat → Nat → Spec.MlDsa.Poly) (cc : Spec.MlDsa.Poly)
    (h : List (Vector Bool Spec.MlDsa.n)) (R : BitVec 64) (nz : Nat) (nc : Bool) (nr : Nat) (s : State) : Prop where
  vc : VC p STK σ s
  hh : hintOf p σ = some h
  hint : HintIs s.mem ((vlay p STK σ).A 0 (oP 0)) p.k h
  a : ∀ r < p.k, ∀ s' < p.ℓ, PolyIs s.mem (aA p STK σ r s') (A' r s')
  z : ∀ i < p.ℓ, PolyIs s.mem ((vlay p STK σ).A 0 (oP (8 + i)))
    (if i < nz then zHat p (sgOf p σ) i else toRq (vZ p (sgOf p σ) i))
  c : PolyIs s.mem ((vlay p STK σ).A 0 (oP 15)) (if nc then ntt cc else cc)
  rows : ∀ r < nr, bytesAt s.mem ((vlay p STK σ).A 0 (oB + w1Len p * r)) (w1Len p) =
    simpleBitPack (w1Row p (pkOf p σ) (sgOf p σ) A' (ntt cc) h r) (w1Max p)
  s4 : s.gpr .s4 = R
  gd : Gd p σ A' cc R

/-- A part that writes `W` keeps what `KC5` says of the polynomials it does not write. -/
structure K5Chk (p : Params) (STK : Nat) (nr : Nat) (W : List (Nat × Nat × Nat)) : Prop where
  vc : vcChk p STK W = true
  hint : sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP 0, 1024 * p.k) W = true
  a : ∀ r < p.k, ∀ s' < p.ℓ, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP (20 + 8 * r + s'), 1024) W = true
  z : ∀ i < p.ℓ, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP (8 + i), 1024) W = true
  c : sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP 15, 1024) W = true
  rows : ∀ r < nr, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oB + w1Len p * r, w1Len p) W = true

/-- Proves a `K5Chk`, in each case of `w1Len`. -/
tactic_template "k5chk " hF:term:max : tactic => `(tactic| (
      rcases ($hF).w1l with hw1 | ⟨hw1, _⟩ <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> vsep $hF [vcChk, hw1]))

theorem sepAll_append {sz : List Nat} {a : Nat × Nat × Nat} {W₁ W₂ : List (Nat × Nat × Nat)}
    (h₁ : sepAll sz a W₁ = true) (h₂ : sepAll sz a W₂ = true) : sepAll sz a (W₁ ++ W₂) = true := by
  simp only [sepAll, List.all_append, Bool.and_eq_true] at *
  exact ⟨h₁, h₂⟩

theorem vcChk_append {p : Params} {STK : Nat} {W₁ W₂ : List (Nat × Nat × Nat)} (h₁ : vcChk p STK W₁ = true)
    (h₂ : vcChk p STK W₂ = true) : vcChk p STK (W₁ ++ W₂) = true := by
  simp only [vcChk, List.all_append, Bool.and_eq_true] at *
  exact ⟨⟨⟨⟨sepAll_append h₁.1.1.1.1 h₂.1.1.1.1, h₁.1.1.1.2, h₂.1.1.1.2⟩, sepAll_append h₁.1.1.2 h₂.1.1.2⟩,
    sepAll_append h₁.1.2 h₂.1.2⟩, sepAll_append h₁.2 h₂.2⟩

/-- The checks of two parts of writes, for both. -/
theorem K5Chk.append {p : Params} {STK nr : Nat} {W₁ W₂ : List (Nat × Nat × Nat)} (h₁ : K5Chk p STK nr W₁)
    (h₂ : K5Chk p STK nr W₂) : K5Chk p STK nr (W₁ ++ W₂) :=
  ⟨vcChk_append h₁.vc h₂.vc, sepAll_append h₁.hint h₂.hint,
    fun r hr s hs => sepAll_append (h₁.a r hr s hs) (h₂.a r hr s hs), fun i hi => sepAll_append (h₁.z i hi) (h₂.z i hi),
    sepAll_append h₁.c h₂.c, fun r hr => sepAll_append (h₁.rows r hr) (h₂.rows r hr)⟩

/-! `K5Chk` of the writes of a part, from those of each region, each proved once for
any region (`k5chk` on a literal list of writes costs seconds). -/

theorem K5Chk.nil {p : Params} (_ : VFacts p) {STK nr : Nat} (_ : nr ≤ p.k) : K5Chk p STK nr [] :=
  ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl⟩

theorem K5Chk.stk {p : Params} (hF : VFacts p) {STK nr : Nat} (hnr : nr ≤ p.k) : K5Chk p STK nr [(1, 0, STK)] := by
  k5chk hF

/-- A write to `scratch` apart from what `KC5` holds. -/
theorem K5Chk.c0 {p : Params} (hF : VFacts p) {STK nr : Nat} (hnr : nr ≤ p.k) {o n : Nat}
    (h1 : o + n ≤ 1288 ∨ 1368 ≤ o) (h2 : o + n ≤ oB ∨ oB + w1Len p * nr ≤ o) (h3 : o + n ≤ oP 0 ∨ oP 8 ≤ o)
    (h4 : o + n ≤ oP 8 ∨ oP 16 ≤ o) (h5 : o + n ≤ oP 20) : K5Chk p STK nr [(0, o, n)] := by
  simp only [oB, oP] at h2 h3 h4 h5
  rcases hF.w1l with hw1 | ⟨hw1, _⟩ <;> rw [hw1] at h2 <;>
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> vsep hF [vcChk, hw1]

theorem K5Chk.cons_c0 {p : Params} (hF : VFacts p) {STK nr : Nat} (hnr : nr ≤ p.k) {o n : Nat}
    {W : List (Nat × Nat × Nat)}
    (h1 : o + n ≤ 1288 ∨ 1368 ≤ o) (h2 : o + n ≤ oB ∨ oB + w1Len p * nr ≤ o ∨ oB + 1024 ≤ o)
    (h3 : o + n ≤ oP 0 ∨ oP 8 ≤ o) (h4 : o + n ≤ oP 8 ∨ oP 16 ≤ o) (h5 : o + n ≤ oP 20) (h : K5Chk p STK nr W) :
    K5Chk p STK nr ((0, o, n) :: W) := by
  have : w1Len p * nr ≤ 1024 := by
    have := Nat.mul_le_mul_left (w1Len p) hnr; rw [Nat.mul_comm (w1Len p) p.k] at this; have := hF.w1; omega_arith
  exact (K5Chk.c0 hF hnr h1 (by omega_using [h2, this]) h3 h4 h5).append (W₁ := [_]) h

theorem K5Chk.cons_stk {p : Params} (hF : VFacts p) {STK nr : Nat} (hnr : nr ≤ p.k) {W : List (Nat × Nat × Nat)}
    (h : K5Chk p STK nr W) : K5Chk p STK nr ((1, 0, STK) :: W) :=
  (K5Chk.stk hF hnr).append (W₁ := [_]) h

/-- Proves a `K5Chk` of writes to `scratch` and the stack, with `hnr : nr ≤ p.k`. -/
tactic_template "k5chks " hF:term:max hnr:term:max : tactic => `(tactic| (
                   repeat' (first
                     | with_reducible exact VG.Proof.MlDsa.RISCV64.Verify.K5Chk.nil $hF $hnr
                     | apply VG.Proof.MlDsa.RISCV64.Verify.K5Chk.cons_stk $hF $hnr
                     | apply VG.Proof.MlDsa.RISCV64.Verify.K5Chk.cons_c0 $hF $hnr)
                   all_goals (
                     have := ($hF).w1.1; have := ($hF).k; have := ($hF).l
                     try simp only [VG.Impl.MlDsa.RISCV64.Verify.oP, VG.Impl.MlDsa.RISCV64.Verify.oB, VG.Impl.MlDsa.RISCV64.Verify.oSS,
                       VG.Impl.MlDsa.RISCV64.Verify.oCT]
                     omega_arith)))

theorem KC5.keep {p : Params} (hF : VFacts p) {STK : Nat} {σ : State} {A' : Nat → Nat → Spec.MlDsa.Poly}
    {cc : Spec.MlDsa.Poly} {h : List (Vector Bool Spec.MlDsa.n)} {R : BitVec 64} {nz : Nat} {nc : Bool} {nr : Nat}
    {s s' : State} (hk5 : KC5 p STK σ A' cc h R nz nc nr s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((vlay p STK σ).RL W) s s') (hc : K5Chk p STK nr W) : KC5 p STK σ A' cc h R nz nc nr s' := by
  have hL := hk5.vc.site.ok
  have hle : w1Len p ≤ 2 ^ 64 := by rcases hF.w1l with e | ⟨e, _⟩ <;> omega_using [e]
  exact ⟨hk5.vc.keep hk hc.vc, hk5.hh, hintIs_keepW hL hk.frame hc.hint (by decide) (by have := hF.k; omega_using [this]) hk5.hint,
    fun r hr s' hs' => polyIs_keepW hL hk.frame (hc.a r hr s' hs') (by decide) rfl (hk5.a r hr s' hs'),
    fun i hi => polyIs_keepW hL hk.frame (hc.z i hi) (by decide) rfl (hk5.z i hi),
    polyIs_keepW hL hk.frame hc.c (by decide) rfl hk5.c,
    fun r hr => by rw [bytes_keepW hL hk.frame (hc.rows r hr) (by decide) hle]; exact hk5.rows r hr,
    (hk.cs .s4 (by decide)).trans hk5.s4, hk5.gd⟩

/-- The states of `compute` with `nz`, `nc` and `nr`, for some `A'`, `cc`, `h` and `R`. -/
abbrev KX (p : Params) (STK : Nat) (nz : Nat) (nc : Bool) (nr : Nat) (σ s : State) : Prop :=
  ∃ A' cc h R, KC5 p STK σ A' cc h R nz nc nr s

/-! ## The NTTs of `z` and `c` -/

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

theorem nttZ_ok {j : Nat} (hj : j < p.ℓ) {σ : State} {A' cc h R} {s : State}
    (hk5 : KC5 p STK σ A' cc h R j false 0 s) : WP isa (nttAt P (pZ j)) s (KC5 p STK σ A' cc h R (j + 1) false 0) := by
  have hk := hF.k; have hl := hF.l
  have hs := hk5.vc.site
  have hL := hs.ok
  have hz := hk5.z j hj
  rw [ifn (Nat.lt_irrefl j)] at hz
  unfold nttAt
  refine ip_ok (t := ntt) hP.ntt hs hS (f := pZ j) (w := sc oSS) ⟨⟨vptr_ok rfl (by unfold oP; omega_using [hj, hl]), by vsep hF⟩,
    ⟨vptr_ok rfl (by decide), by vsep hF⟩, show ix Reg.s11 ∈ vWb by decide, show ix Reg.s11 ∈ vWb by decide,
    by vsep hF, by valsep, by valsep⟩ hz.1 fun s' k' hb => ?_
  refine ⟨hk5.vc.keep k' (by vsep hF [vcChk]), hk5.hh,
    hintIs_keepW hL k'.frame (by vsep hF) (by decide) (by omega_using [hk]) hk5.hint,
    fun r hr s' hs' => polyIs_keepW hL k'.frame (by vsep hF) (by decide) rfl (hk5.a r hr s' hs'),
    fun i hi => ?_, polyIs_keepW hL k'.frame (by vsep hF) (by decide) rfl hk5.c,
    fun _ h => absurd h (Nat.not_lt_zero _), (k'.cs .s4 (by decide)).trans hk5.s4, hk5.gd⟩
  by_cases e : i = j
  · subst e
    rw [ifp (Nat.lt_succ_self _)]
    show PolyIs s'.mem (lpa (vlay p STK σ) (pZ i)) _
    have e2 : polyAt s.mem (lpa (vlay p STK σ) (pZ i)) = _ := hz.2
    rw [e2] at hb
    exact hb
  · have := polyIs_keepW hL k'.frame (i := 0) (o := oP (8 + i)) (by vsep hF) (by decide) rfl (hk5.z i hi)
    by_cases hlt : i < j
    · rwa [ifp hlt, ← ifp (show i < j + 1 by omega_using [hlt]) (zHat p (sgOf p σ) i) (toRq (vZ p (sgOf p σ) i))] at this
    · rwa [ifn hlt, ← ifn (show ¬ i < j + 1 by omega_using [e, hlt]) (zHat p (sgOf p σ) i) (toRq (vZ p (sgOf p σ) i))] at this

theorem nttZ_piece {j : Nat} (hj : j < p.ℓ) :
    VPiece p STK (KX p STK j false 0) (KX p STK (j + 1) false 0) (nttAt P (pZ j)) := by
  have hl := hF.l
  refine ⟨fun _ _ _ ⟨A', cc, h, R, hk5⟩ => WP.mono (nttZ_ok hP hF hS hj hk5) fun _ h' => ⟨A', cc, h, R, h'⟩, ?_⟩
  unfold nttAt
  refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
    Reduced x.mem (lpa (vlay p STK σ) (pZ j)) ∧ Reduced y.mem (lpa (vlay p STK σ) (pZ j)))
    (RelCT.exists_ fun σ => ip_tr (t := ntt) hP.ntt hS (f := pZ j) (w := sc oSS)
      (⟨⟨vptr_ok rfl (by unfold oP; omega_using [hj, hl]), by vsep hF⟩, ⟨vptr_ok rfl (by decide), by vsep hF⟩,
        show ix Reg.s11 ∈ vWb by decide, show ix Reg.s11 ∈ vWb by decide, by vsep hF, by valsep, by valsep⟩ : KeyGen.IpOk (vlay p STK σ) vWb _ _)
      fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
    fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ?_
  have r₂ : Reduced _ (lpa (vlay p STK _) (pZ j)) := (h₂.z j hj).1
  rw [← vlay_pub pub] at r₂
  exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, (h₁.z j hj).1, r₂⟩

theorem nttC_ok {σ : State} {A' cc h R} {s : State} (hk5 : KC5 p STK σ A' cc h R p.ℓ false 0 s) :
    WP isa (nttAt P pC) s (KC5 p STK σ A' cc h R p.ℓ true 0) := by
  have hk := hF.k; have hl := hF.l
  have hs := hk5.vc.site
  have hL := hs.ok
  unfold nttAt
  refine ip_ok (t := ntt) hP.ntt hs hS (f := pC) (w := sc oSS) ⟨⟨vptr_ok rfl (by decide), by vsep hF⟩,
    ⟨vptr_ok rfl (by decide), by vsep hF⟩, show ix Reg.s11 ∈ vWb by decide, show ix Reg.s11 ∈ vWb by decide,
    by vsep hF, by valsep, by valsep⟩ hk5.c.1 fun s' k' hb => ?_
  refine ⟨hk5.vc.keep k' (by vsep hF [vcChk]), hk5.hh,
    hintIs_keepW hL k'.frame (by vsep hF) (by decide) (by omega_using [hk]) hk5.hint,
    fun r hr s' hs' => polyIs_keepW hL k'.frame (by vsep hF) (by decide) rfl (hk5.a r hr s' hs'),
    fun i hi => polyIs_keepW hL k'.frame (by vsep hF) (by decide) rfl (hk5.z i hi), ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), (k'.cs .s4 (by decide)).trans hk5.s4, hk5.gd⟩
  show PolyIs s'.mem (lpa (vlay p STK σ) pC) _
  have e2 : polyAt s.mem (lpa (vlay p STK σ) pC) = cc := hk5.c.2
  rw [e2] at hb
  exact hb

theorem nttC_piece : VPiece p STK (KX p STK p.ℓ false 0) (KX p STK p.ℓ true 0) (nttAt P pC) := by
  refine ⟨fun _ _ _ ⟨A', cc, h, R, hk5⟩ => WP.mono (nttC_ok hP hF hS hk5) fun _ h' => ⟨A', cc, h, R, h'⟩, ?_⟩
  unfold nttAt
  refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
    Reduced x.mem (lpa (vlay p STK σ) pC) ∧ Reduced y.mem (lpa (vlay p STK σ) pC))
    (RelCT.exists_ fun σ => ip_tr (t := ntt) hP.ntt hS (f := pC) (w := sc oSS)
      (⟨⟨vptr_ok rfl (by decide), by vsep hF⟩, ⟨vptr_ok rfl (by decide), by vsep hF⟩,
        show ix Reg.s11 ∈ vWb by decide, show ix Reg.s11 ∈ vWb by decide, by vsep hF, by valsep, by valsep⟩ : KeyGen.IpOk (vlay p STK σ) vWb _ _)
      fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
    fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ?_
  have r₂ : Reduced _ (lpa (vlay p STK _) pC) := h₂.c.1
  rw [← vlay_pub pub] at r₂
  exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, h₁.c.1, r₂⟩

end

end VG.Proof.MlDsa.RISCV64.Verify
