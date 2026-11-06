module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Verify.Lay
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Piece
public import VerifiedGarbage.Proof.MlKem.RISCV64.TopSave
import VerifiedGarbage.Proof.MlDsa.RISCV64.CacheCopy
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Verify.Lay
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Piece
meta import VerifiedGarbage.Proof.MlKem.RISCV64.TopSave
meta import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun

/-!
# ML-DSA verification on RISC-V: what holds throughout, and the prologue

As on PPC64LE (`Proof/MlDsa/PPC64LE/Verify/Inv.lean`): what holds of the
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
