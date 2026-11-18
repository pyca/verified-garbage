module

public import VerifiedGarbage.Proof.MlDsa.Sign.Setup
import VerifiedGarbage.Proof.MlDsa.KeyGen.Masked
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.StepsCT
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Samp
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.CallS
public import VerifiedGarbage.Proof.MlDsa.Sign.Leak
import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.ContractsV
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.Lay
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Piece
public import VerifiedGarbage.Proof.MlKem.RISCV64.TopSave
import VerifiedGarbage.Proof.MlDsa.RISCV64.CacheCopy
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.Lay
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Piece
meta import VerifiedGarbage.Proof.MlKem.RISCV64.TopSave
meta import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.StepsCT
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Samp
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.CallS
meta import VerifiedGarbage.Proof.MlDsa.Sign.Leak
meta import VerifiedGarbage.Proof.MlDsa.Sign.Setup
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.ContractsV
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.CacheCopy
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun

/-! ### `MlDsa.RISCV64.Sign.Control`, which only this module used -/

section

/-! ### `MlDsa.RISCV64.Sign.Inv`, which only this module used -/

section

/-!
# ML-DSA signing on RISC-V: what holds throughout, and the prologue

As key generation's and verification's (`KeyGen/Inv.lean`, `Verify/Inv.lean`):
what holds of the state throughout, from the entry state: the layout, the
permissions and stack pointer of the entry state, our caller's registers
saved in `scratch` (ML-KEM's `TopSaved`), the callee-saved registers we do
not save as they were, and the inputs; until the hash of `ρ″` with `rnd` in
buffer 4 and `sig` stored at `SIG` (`SC1`), and then with `sig` in buffer 4
(`SC2`, from `SC1` by loading `sig` into `s8`, `toSC2`). Which writes keep
them (`sc1Chk`, `sc2Chk`); the pieces of signing (`SPiece`); and the
prologue (`spro_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sign

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece disjW disjW' reg)
open VG.Impl.MlDsa.RISCV64.Sign
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.Sha3.RISCV64.Stream (mov)

/-! ## The inputs -/

section
variable (p : Params) (σ : State)

abbrev skOf : List Byte := bytesAt σ.mem (sSk σ) p.skLen
abbrev muOf : List Byte := bytesAt σ.mem (sMu σ) 64
abbrev rndOf : List Byte := bytesAt σ.mem (sRnd σ) 32

end

/-- The public data of `signContract`. -/
def sPub (p : Params) (σ₁ σ₂ : State) : Prop :=
  σ₁.sp = σ₂.sp ∧ sSk σ₁ = sSk σ₂ ∧ sMu σ₁ = sMu σ₂ ∧ sRnd σ₁ = sRnd σ₂ ∧ sSig σ₁ = sSig σ₂ ∧
    sScr σ₁ = sScr σ₂ ∧ Spec.MlDsa.signLeak p (skOf p σ₁) (muOf σ₁) (rndOf σ₁) =
      Spec.MlDsa.signLeak p (skOf p σ₂) (muOf σ₂) (rndOf σ₂) ∧ sCache σ₁ = sCache σ₂ ∧
    σ₁.gpr .a6 = σ₂.gpr .a6

theorem cSel_pub {p : Params} {σ₁ σ₂ : State} (h : sPub p σ₁ σ₂) : cSel σ₁ = cSel σ₂ := by
  obtain ⟨-, -, -, -, -, -, -, e5, e6⟩ := h
  simp only [cSel, sCache] at *
  rw [e5, e6]

/-- The pieces of signing. -/
abbrev SPiece (p : Params) (STK : Nat) := Piece (SPre p STK) (sPub p)

theorem slay1_pub {p : Params} {STK : Nat} {σ₁ σ₂ : State} (h : sPub p σ₁ σ₂) : slay1 p STK σ₁ = slay1 p STK σ₂ := by
  obtain ⟨e0, e1, e2, e3, -, e5, -⟩ := h
  simp only [slay1, sSk, sMu, sRnd, sScr] at *
  rw [e0, e1, e2, e3, e5]

theorem slay2_pub {p : Params} {STK : Nat} {σ₁ σ₂ : State} (h : sPub p σ₁ σ₂) : slay2 p STK σ₁ = slay2 p STK σ₂ := by
  obtain ⟨e0, e1, e2, -, e4, e5, -⟩ := h
  simp only [slay2, sSk, sMu, sSig, sScr] at *
  rw [e0, e1, e2, e4, e5]

theorem saveR_slay1 (p : Params) (STK : Nat) (σ : State) : saveR (sScr σ) = (slay1 p STK σ).R 0 1288 80 := rfl
theorem saveR_slay2 (p : Params) (STK : Nat) (σ : State) : saveR (sScr σ) = (slay2 p STK σ).R 0 1288 80 := rfl

/-! ## What holds throughout -/

/-- What holds until the hash of `ρ″`, from the entry state `σ`. -/
structure SC1 (p : Params) (STK : Nat) (σ s : State) : Prop where
  site : Site (slay1 p STK σ) sWb1 STK s
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  pres : ∀ r ∈ preserved, r ∉ savedTop → s.gpr r = σ.gpr r
  sav : TopSaved s.mem (sScr σ) σ
  sig : s.mem.readW (sScr σ + BitVec.ofNat 64 oSIG) 64 = sSig σ
  sk : bytesAt s.mem ((slay1 p STK σ).A 2 0) p.skLen = skOf p σ
  mu : bytesAt s.mem ((slay1 p STK σ).A 3 0) 64 = muOf σ
  rnd : bytesAt s.mem ((slay1 p STK σ).A 4 0) 32 = rndOf σ
  pre : SPre p STK σ
  s3 : s.gpr .s3 = cSel σ
  cache : bytesAt s.mem (sCache σ) (sCLen σ) = bytesAt σ.mem (sCache σ) (sCLen σ)

/-- What holds from the hash of `ρ″` on, from the entry state `σ`. -/
structure SC2 (p : Params) (STK : Nat) (σ s : State) : Prop where
  site : Site (slay2 p STK σ) sWb2 STK s
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  pres : ∀ r ∈ preserved, r ∉ savedTop → s.gpr r = σ.gpr r
  sav : TopSaved s.mem (sScr σ) σ
  sk : bytesAt s.mem ((slay2 p STK σ).A 2 0) p.skLen = skOf p σ
  mu : bytesAt s.mem ((slay2 p STK σ).A 3 0) 64 = muOf σ
  pre : SPre p STK σ
  s3 : s.gpr .s3 = cSel σ
  cache : bytesAt s.mem (sCache σ) (sCLen σ) = bytesAt σ.mem (sCache σ) (sCLen σ)

/-- A part that writes the regions `W` before the hash of `ρ″` keeps `SC1`. -/
def sc1Chk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  sepAll [scrLen p, STK, p.skLen, 64, 32] (0, 1288, 80) W && W.all (fun w => w.1 == 0 || w.1 == 1) &&
    sepAll [scrLen p, STK, p.skLen, 64, 32] (0, 912, 8) W &&
    sepAll [scrLen p, STK, p.skLen, 64, 32] (2, 0, p.skLen) W &&
    sepAll [scrLen p, STK, p.skLen, 64, 32] (3, 0, 64) W &&
    sepAll [scrLen p, STK, p.skLen, 64, 32] (4, 0, 32) W

/-- A part that writes the regions `W` after the hash of `ρ″` keeps `SC2`. -/
def sc2Chk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, 1288, 80) W &&
    W.all (fun w => w.1 == 0 || w.1 == 1 || w.1 == 4) &&
    sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (2, 0, p.skLen) W &&
    sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (3, 0, 64) W

/-- Bytes of a buffer only read, kept by a part that writes only buffers of `Wb`. -/
theorem bytes_keepR {L : Lay} {Wb : List Nat} (hL : OkW L Wb) {W : List (Nat × Nat × Nat)} {m m' : Mem}
    (hf : Frame (L.RL W) m m') {i o l : Nat} (h : sepAll L.sizes (i, o, l) W = true) (hw : ∀ w ∈ W, w.1 ∈ Wb)
    (hl : l ≤ 2 ^ 64) : bytesAt m' (L.A i o) l = bytesAt m (L.A i o) l :=
  Proof.MlKem.bytesAt_frame hf (fun r hr => by
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hr
    exact disjW hL (List.all_eq_true.mp h w hw') (.inr (hw w hw'))) hl

/-- The cache, apart from the buffers that a part writes, is kept by it. -/
theorem cache_keep {L : Lay} {W : List (Nat × Nat × Nat)} {m m' : Mem} (hf : Frame (L.RL W) m m') {X : Region}
    (hl : X.len ≤ 2 ^ 64)
    (h : ∀ w ∈ W, w.2.1 + w.2.2 ≤ L.size w.1 ∧ (⟨L.ptr w.1, L.size w.1⟩ : Region).Disjoint X) :
    bytesAt m' X.base X.len = bytesAt m X.base X.len :=
  Proof.MlKem.bytesAt_frame hf (fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact ((h w hw).2.sub_left (Lay.R_sub (h w hw).1)).symm) hl

/-- The bounds of a region apart from another. -/
theorem sepAll_bound {sz : List Nat} {a : Nat × Nat × Nat} {W : List (Nat × Nat × Nat)} (h : sepAll sz a W = true)
    {w : Nat × Nat × Nat} (hw : w ∈ W) : w.2.1 + w.2.2 ≤ sz.getD w.1 0 := by
  have := List.all_eq_true.mp h w hw
  simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.2

theorem sfit1 {p : Params} {STK : Nat} {σ : State} (hL : OkW (slay1 p STK σ) sWb1) (i : Nat) (hi : i < 5) :
    (slay1 p STK σ).size i ≤ 2 ^ 64 := by
  have := hL.fit i (by simp only [slay1, List.length_cons, List.length_nil]; omega_arith)
  omega_arith

theorem sfit2 {p : Params} {STK : Nat} {σ : State} (hL : OkW (slay2 p STK σ) sWb2) (i : Nat) (hi : i < 5) :
    (slay2 p STK σ).size i ≤ 2 ^ 64 := by
  have := hL.fit i (by simp only [slay2, List.length_cons, List.length_nil]; omega_arith)
  omega_arith

theorem SC1.keep {p : Params} {STK : Nat} {σ s s' : State} (h : SC1 p STK σ s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((slay1 p STK σ).RL W) s s') (hc : sc1Chk p STK W = true) : SC1 p STK σ s' := by
  simp only [sc1Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨h0, hw⟩, h1⟩, h2⟩, h3⟩, h4⟩ := hc
  have hL := h.site.ok
  have hw' : ∀ w ∈ W, w.1 ∈ sWb1 := fun w hw'' => by
    have := List.all_eq_true.mp hw w hw''
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    simp only [sWb1, List.mem_cons, List.not_mem_nil, or_false]; exact this
  have hd : ∀ r ∈ (slay1 p STK σ).RL W, ((slay1 p STK σ).R 0 1288 80).Disjoint r :=
    fun r hr => by
      obtain ⟨w, hw'', rfl⟩ := List.mem_map.mp hr
      exact disjW hL (List.all_eq_true.mp h0 w hw'') (.inl (by decide))
  have hd8 : ∀ r ∈ (slay1 p STK σ).RL W, ((slay1 p STK σ).R 0 912 8).Disjoint r :=
    fun r hr => by
      obtain ⟨w, hw'', rfl⟩ := List.mem_map.mp hr
      exact disjW hL (List.all_eq_true.mp h1 w hw'') (.inl (by decide))
  refine ⟨h.site.kept hk, hk.rd.trans h.rd, hk.wr.trans h.wr, hk.sp.trans h.sp,
    fun r hr hs => (hk.cs r hr).trans (h.pres r hr hs), h.sav.keep hk.frame (by rw [saveR_slay1 p STK σ]; exact hd),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk.frame.readW (r := (slay1 p STK σ).R 0 912 8) (Region.contains_self _ _) hd8 (by decide)]
    exact h.sig
  · rw [bytes_keepR hL hk.frame h2 hw' (sfit1 hL 2 (by decide))]; exact h.sk
  · rw [bytes_keepR hL hk.frame h3 hw' (by decide)]; exact h.mu
  · rw [bytes_keepR hL hk.frame h4 hw' (by decide)]; exact h.rnd
  · exact h.pre
  · rw [hk.cs .s3 (by decide)]; exact h.s3
  · refine (cache_keep (X := reg (sCache σ) (sCLen σ)) hk.frame (by have := h.pre.f_x; show sCLen σ ≤ 2 ^ 64; omega_arith)
      fun w hw => ⟨sepAll_bound h0 hw, ?_⟩).trans h.cache
    have e := hw' w hw
    simp only [sWb1, List.mem_cons, List.not_mem_nil, or_false] at e
    rcases e with e | e <;> rw [e]
    · exact h.pre.d_cx
    · exact h.pre.b_x

theorem SC2.keep {p : Params} {STK : Nat} {σ s s' : State} (h : SC2 p STK σ s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((slay2 p STK σ).RL W) s s') (hc : sc2Chk p STK W = true) : SC2 p STK σ s' := by
  simp only [sc2Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h0, hw⟩, h2⟩, h3⟩ := hc
  have hL := h.site.ok
  have hw' : ∀ w ∈ W, w.1 ∈ sWb2 := fun w hw'' => by
    have := List.all_eq_true.mp hw w hw''
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    simp only [sWb2, List.mem_cons, List.not_mem_nil, or_false]; omega_arith
  have hd : ∀ r ∈ (slay2 p STK σ).RL W, ((slay2 p STK σ).R 0 1288 80).Disjoint r :=
    fun r hr => by
      obtain ⟨w, hw'', rfl⟩ := List.mem_map.mp hr
      exact disjW hL (List.all_eq_true.mp h0 w hw'') (.inl (by decide))
  refine ⟨h.site.kept hk, hk.rd.trans h.rd, hk.wr.trans h.wr, hk.sp.trans h.sp,
    fun r hr hs => (hk.cs r hr).trans (h.pres r hr hs), h.sav.keep hk.frame (by rw [saveR_slay2 p STK σ]; exact hd),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [bytes_keepR hL hk.frame h2 hw' (sfit2 hL 2 (by decide))]; exact h.sk
  · rw [bytes_keepR hL hk.frame h3 hw' (by decide)]; exact h.mu
  · exact h.pre
  · rw [hk.cs .s3 (by decide)]; exact h.s3
  · refine (cache_keep (X := reg (sCache σ) (sCLen σ)) hk.frame (by have := h.pre.f_x; show sCLen σ ≤ 2 ^ 64; omega_arith)
      fun w hw => ⟨sepAll_bound h0 hw, ?_⟩).trans h.cache
    have e := hw' w hw
    simp only [sWb2, List.mem_cons, List.not_mem_nil, or_false] at e
    rcases e with e | e | e <;> rw [e]
    · exact h.pre.d_cx
    · exact h.pre.b_x
    · exact h.pre.d_gx

theorem inputs_eq (p : Params) (STK : Nat) (σ : State) :
    bytesAt σ.mem ((slay1 p STK σ).A 2 0) p.skLen = skOf p σ ∧ bytesAt σ.mem ((slay1 p STK σ).A 3 0) 64 = muOf σ ∧
      bytesAt σ.mem ((slay1 p STK σ).A 4 0) 32 = rndOf σ := by
  simp only [Lay.A, BitVec.add_zero]; exact ⟨rfl, rfl, rfl⟩

/-! ## The prologue -/

theorem spro_ok {p : Params} (hF : SFacts p) {STK : Nat} (hSTK : 1168 ≤ STK) {σ : State} (hp : SPre p STK σ) :
    WP isa (.block pro) σ fun s => SC1 p STK σ s ∧ s.gpr .s4 = 1 := by
  have hL := slay1_ok hp
  have fc := hp.f_c
  obtain ⟨hs1, hs2, -⟩ := hF.scr
  have w0 : (slay1 p STK σ).buf 0 ∈ σ.wr := by
    rw [show (slay1 p STK σ).buf 0 = reg (sScr σ) (scrLen p) from rfl, hp.wr]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions σ.wr (sScr σ + BitVec.ofNat 64 o) n := fun {o n} h =>
    Lay.covers (L := slay1 p STK σ) (o := o) (l := n) w0 (by rw [slay1_size0]; omega_arith) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [pro, WP.block_append_iff]
  refine WP.mono (topSave_ok rfl hp.al_c fun o _ h₂ => wS (by omega_arith))
    fun s₁ ⟨sav, fr, g₁, rd₁, wr₁, sp₁⟩ => ?_
  have g3 : s₁.gpr .a0 = sSk σ := by rw [g₁]
  have g4 : s₁.gpr .a1 = sMu σ := by rw [g₁]
  have g5 : s₁.gpr .a2 = sRnd σ := by rw [g₁]
  have g6 : s₁.gpr .a3 = sSig σ := by rw [g₁]
  have g7 : s₁.gpr .a4 = sScr σ := by rw [g₁]
  have g8 : s₁.gpr .a5 = sCache σ := by rw [g₁]
  have g9 : s₁.gpr .a6 = σ.gpr .a6 := by rw [g₁]
  have a912 : (sScr σ + BitVec.ofNat 64 oSIG).toNat % 8 = 0 := by
    have := hp.al_c
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [oSIG]; omega_using [this]
  have i912 : InRegions s₁.wr (sScr σ + BitVec.ofNat 64 oSIG) 8 := by rw [wr₁]; exact wS (by decide)
  have o912 : oSIG % 8 = 0 ∧ oSIG < 32768 := by decide
  have hmv : WP isa (.block [mov .s10 .a0, mov .s9 .a1, mov .s8 .a2, mov .s11 .a4, .store .d .a3 .s11 oSIG,
      .li .s4 1, .li .t2 0, .sltu .t0 .t2 .a6, .sub .t0 .t2 .t0, .logic .and .s3 .a5 .t0]) s₁ fun s =>
      s.gpr .s10 = sSk σ ∧ s.gpr .s9 = sMu σ ∧ s.gpr .s8 = sRnd σ ∧ s.gpr .s11 = sScr σ ∧
      s.gpr .s4 = 1 ∧ s.gpr .s3 = cSel σ ∧ (∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₁.gpr r) ∧
      s.mem = s₁.mem.writeW (sScr σ + BitVec.ofNat 64 oSIG) (sSig σ) ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧
      s.sp = s₁.sp := by
    have hlt : oSIG < 2048 := by decide
    mrun [mov, g3, g4, g5, g6, g7, g8, g9, i912, a912, hlt]
    refine ⟨?_, ?_, fun r hr hs => ?_⟩
    all_goals try exact rfl
    all_goals try exact CacheCopy.sel_eq _ _
    simp only [savedTop, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
    obtain ⟨a3, a4, -, -, -, a8, a9, a10, a11⟩ := hs
    have t0 : r ≠ .t0 := fun e => by subst e; revert hr; decide
    have t2 : r ≠ .t2 := fun e => by subst e; revert hr; decide
    simp only [a3, a4, a8, a9, a10, a11, t0, t2, ite_false]
  refine WP.mono hmv fun s ⟨g30, g29, g28, g31, g24, g19, cs, m, rd, wr, sp⟩ => ?_
  have fr8 : Frame [(slay1 p STK σ).R 0 912 8] s₁.mem s.mem := by
    rw [m]
    exact (show Frame [(slay1 p STK σ).R 0 912 8] s₁.mem s₁.mem from fun _ _ => rfl).writeW
      (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hin : ∀ {i l : Nat}, i = 2 ∨ i = 3 ∨ i = 4 → l = (slay1 p STK σ).size i →
      bytesAt s.mem ((slay1 p STK σ).A i 0) l = bytesAt σ.mem ((slay1 p STK σ).A i 0) l := fun {i l} hi hl => by
    have hl' : l ≤ 2 ^ 64 := by rw [hl]; exact sfit1 hL i (by omega_arith)
    rw [Proof.MlKem.bytesAt_frame fr8 (fun r hr => ?_) hl', Proof.MlKem.bytesAt_frame fr (fun r hr => ?_) hl']
    · rw [List.mem_singleton] at hr; subst hr
      rw [saveR_slay1 p STK σ]
      refine disjW' (i := i) (o := 0) (l := l) (j := 0) (o' := 1288) (l' := 80) hL ?_ (.inr (.inl (by decide)))
      subst hl
      rcases hi with rfl | rfl | rfl <;> ssep hF [slay1, Lay.size]
    · rw [List.mem_singleton] at hr; subst hr
      refine disjW' (i := i) (o := 0) (l := l) (j := 0) (o' := 912) (l' := 8) hL ?_ (.inr (.inl (by decide)))
      subst hl
      rcases hi with rfl | rfl | rfl <;> ssep hF [slay1, Lay.size]
  obtain ⟨ek, em, er⟩ := inputs_eq p STK σ
  refine ⟨⟨⟨hL, rfl, by decide, by decide, by rw [slay1_size0]; omega_arith, rfl, by rw [sp, sp₁]; rfl, hSTK,
    by rw [sp, sp₁]; exact hp.stk, by rw [sp, sp₁]; exact hp.al, hp.al_c, g31, g30, g29, g28, fun i hi hi1 => ?_,
    fun i hi hi1 => ?_⟩,
    rd.trans rd₁, wr.trans wr₁, sp.trans sp₁,
    fun r hr hs => (cs r hr hs).trans (by rw [g₁]),
    sav.keep fr8 (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact disjW' (i := 0) (o := 1288) (l := 80) (j := 0) (o' := 912) (l' := 8) hL (by ssep hF [slay1, Lay.size])
        (.inl (by decide))), ?_, ?_, ?_, ?_, hp, g19, ?_⟩, g24⟩
  · show _ ∈ s.wr
    rw [wr, wr₁, hp.wr]
    simp only [sWb1, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · simp [Lay.buf, slay1]
    · exact absurd rfl hi1
  · show _ ∈ s.rd ++ s.wr
    rw [rd, rd₁, wr, wr₁, hp.rd, hp.wr]
    rcases (by omega_arith : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;> simp [Lay.buf, slay1]
  · rw [m]; exact Mem.readW_writeW_self64 _ _ _
  · rw [hin (i := 2) (l := p.skLen) (.inl rfl) rfl]; exact ek
  · rw [hin (i := 3) (l := 64) (.inr (.inl rfl)) rfl]; exact em
  · rw [hin (i := 4) (l := 32) (.inr (.inr rfl)) rfl]; exact er
  · have hx : (sCLen σ) ≤ 2 ^ 64 := by have := hp.f_x; omega_arith
    have hsub : ∀ {o l : Nat}, o + l ≤ scrLen p →
        (Region.Disjoint (reg (sCache σ) (sCLen σ)) ((slay1 p STK σ).R 0 o l)) := fun h =>
      (hp.d_cx.sub_left (Lay.R_sub (L := slay1 p STK σ) (i := 0) h)).symm
    rw [Proof.MlKem.bytesAt_frame fr8 (fun r hr => ?_) hx, Proof.MlKem.bytesAt_frame fr (fun r hr => ?_) hx]
    · rw [List.mem_singleton] at hr; subst hr; rw [saveR_slay1 p STK σ]; exact hsub (by omega_arith)
    · rw [List.mem_singleton] at hr; subst hr; exact hsub (by omega_arith)

theorem spro_piece {p : Params} (hF : SFacts p) {STK : Nat} (hSTK : 1168 ≤ STK) :
    SPiece p STK (fun σ s => s = σ) (fun σ s => SC1 p STK σ s ∧ s.gpr .s4 = 1) (.block pro) :=
  ⟨fun σ s hp hs => by subst hs; exact spro_ok hF hSTK hp,
    Sample.taint_block [.a0, .a1, .a2, .a3, .a4] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
      subst h₁ h₂; exact pub.1)
      (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      obtain ⟨-, e3, e4, e5, e6, e7, -⟩ := pub
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [e3, e4, e5, e6, e7]) (by taint_decide)⟩

end VG.Proof.MlDsa.RISCV64.Sign

end

end

/-!
# ML-DSA signing on RISC-V: the primitives, two runs, and the branches on the result

What the proofs need of the implementations of the primitives (`SPrimsOk`):
verified with at most `S` bytes of stack, and, as on 32-bit ARM
(`Proof/MlDsa/Arm/Sign/PhaseA.lean`), for the two samplers whose results the
function branches on, that the result is a function of their public data
(`RetPub`) and that they succeed only if the sampling finishes within
`maxBounds`. A call of such a sampler gives the same result in two runs
(`callVRet_tr`). Then: `ρ` is public (`pub_rho`); two runs with the same
layout (`STwo1`, `STwo2`) and the constant time of a piece without calls by
the taint analysis from the pointers.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sign

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv taint31 taint4
  Regs2 Callee CallRel glueOk glueSt glue_ok glueSt_rd glueSt_wr glue_noMem)
open VG.Impl.MlDsa.RISCV64.KeyGen (callAt)
open VG.Impl.MlDsa.RISCV64.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The primitives -/

/-- The result of `c` (the low word of `a0`) is the same in two runs from
states that satisfy `k.pre` and agree on `k.pub`. -/
def RetPub (k : Contract isa) (c : Prog isa) : Prop :=
  RelCT isa (fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂) c
    fun s₁ s₂ => (s₁.gpr .a0).setWidth 32 = (s₂.gpr .a0).setWidth 32

/-- What the proofs need of the implementations `P` of the primitives: each
verified against its contract with at most `S` bytes of stack, and the facts
about the two samplers the function branches on. -/
structure SPrimsOk (P : Prims) (S : Nat) : Prop where
  ntt : Callee P.ntt (fun stk => nttContract RISCV64.abi stk) S
  invNtt : Callee P.invNtt (fun stk => nttInvContract RISCV64.abi stk) S
  mul : Callee P.mul (fun stk => mulContract RISCV64.abi stk) S
  mulAdd : Callee P.mulAdd (fun stk => mulAddContract RISCV64.abi stk) S
  add : Callee P.add (fun stk => addContract RISCV64.abi stk) S
  sub : Callee P.sub (fun stk => subContract RISCV64.abi stk) S
  rejNTT : Callee P.rejNTT (fun stk => rejNTTContract RISCV64.abi stk) S
  expandMask : Callee P.expandMask (fun stk => expandMaskContract RISCV64.abi stk) S
  ball : Callee P.ball (fun stk => sampleInBallContract RISCV64.abi stk) S
  highBits : Callee P.highBits (fun stk => highBitsContract RISCV64.abi stk) S
  lowBits : Callee P.lowBits (fun stk => lowBitsContract RISCV64.abi stk) S
  normLt : Callee P.normLt (fun stk => normLtContract RISCV64.abi stk) S
  makeHint : Callee P.makeHint (fun stk => makeHintContract RISCV64.abi stk) S
  simpleBitPack : Callee P.simpleBitPack (fun stk => simpleBitPackContract RISCV64.abi stk) S
  bitPack : Callee P.bitPack (fun stk => bitPackContract RISCV64.abi stk) S
  bitUnpack : Callee P.bitUnpack (fun stk => bitUnpackContract RISCV64.abi stk) S
  hintBitPack : Callee P.hintBitPack (fun stk => hintBitPackContract RISCV64.abi stk) S
  /-- With some stack (at most `S`) it is verified with, `vg_mldsa_rej_ntt_poly`'s result depends
  only on its public data (its seed), and it succeeds only if `RejNTTPoly` finishes within
  `maxBounds`. -/
  rejX : ∃ stk, stk ≤ S ∧ Verified RISCV64.target P.rejNTT (rejNTTContract RISCV64.abi stk) ∧
    RetPub (rejNTTContract RISCV64.abi stk) P.rejNTT ∧
    ∀ s t s', (rejNTTContract RISCV64.abi stk).pre s → Exec isa P.rejNTT s t s' →
      (s'.gpr .a0).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (s.gpr .a0) 34)).isSome
  /-- Likewise, `vg_mldsa_sample_in_ball`'s result depends only on its public data (`c̃`), and it
  succeeds only if `SampleInBall` finishes within `maxBounds`. -/
  ballX : ∃ stk, stk ≤ S ∧ Verified RISCV64.target P.ball (sampleInBallContract RISCV64.abi stk) ∧
    RetPub (sampleInBallContract RISCV64.abi stk) P.ball ∧
    ∀ s t s', (sampleInBallContract RISCV64.abi stk).pre s → Exec isa P.ball s t s' →
      (s'.gpr .a0).setWidth 32 = 1 →
      (sampleInBall ((s.gpr .a2).setWidth 32).toNat maxBounds.ball
        (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)).isSome

/-! ## Calls whose results are public -/

/-- The run of a call narrowed to the regions its contract gives it: the
same trace, and the same registers. -/
theorem narrow_run {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} {t : List Leak} {s' : State}
    (hpre : k.pre (s.withRegions rd wr)) (hc : RISCV64.Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : RISCV64.Covers wr s.wr)
    (he : Exec isa c s t s') : ∃ s'', Exec isa c (s.withRegions rd wr) t s'' ∧ s''.gpr = s'.gpr := by
  obtain ⟨t', s'', he', -⟩ := hv _ hpre
  have hw' := Exec.widen he' (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at hw'
  obtain ⟨rfl, rfl⟩ := Exec.det he hw'
  exact ⟨_, he', rfl⟩

/-- A call of verified code whose result is public in its own runs gives the
same result in two runs whose narrowed entry states satisfy its precondition
and agree on its public data. -/
theorem RelCT.callRet {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ →
      k.pre (s₁.callEntry.withRegions rd wr) ∧ k.pre (s₂.callEntry.withRegions rd wr) ∧
      k.pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) ∧
      RISCV64.Covers (rd ++ wr) (s₁.rd ++ s₁.wr) ∧ RISCV64.Covers wr s₁.wr ∧
      RISCV64.Covers (rd ++ wr) (s₂.rd ++ s₂.wr) ∧ RISCV64.Covers wr s₂.wr) :
    RelCT isa P (.call n c) fun s₁ s₂ => (s₁.gpr .a0).setWidth 32 = (s₂.gpr .a0).setWidth 32 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      obtain ⟨n₁, x₁, g₁⟩ := narrow_run hv p₁ (by simpa using c₁) (by simpa using w₁) b₁
      obtain ⟨n₂, x₂, g₂⟩ := narrow_run hv p₂ (by simpa using c₂) (by simpa using w₂) b₂
      obtain ⟨ht, hrax⟩ := hr _ _ _ _ _ _ ⟨p₁, p₂, hpub⟩ x₁ x₂
      rw [ret_eq r₁, ret_eq r₂]
      exact ⟨by simp only [ht], show _ = _ by rw [← g₁, ← g₂]; exact hrax⟩

/-- `callV_tr`, with the result of a callee that is public (`RetPub`). -/
theorem callVRet_tr {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {as : List (Reg × Impl.MlDsa.RISCV64.KeyGen.Arg)} (hg : glueOk as = true)
    {P : State → State → Prop}
    (hP : ∀ x y, P x y → ∃ rd wr, CallRel k rd wr x y (glueSt x as) (glueSt y as)) :
    RelCT isa P (callAt name c as) fun x y => (x.gpr .a0).setWidth 32 = (y.gpr .a0).setWidth 32 := by
  unfold callAt
  refine RelCT.seq (RelCT.wpDep (F := fun x x1 => x1 = glueSt x as) (relct_noMem (glue_noMem as))
    fun x y _ => ⟨glue_ok hg x, glue_ok hg y⟩) ?_
  refine RelCT.mono (P := fun (a b : State) => ∃ rw : List Region × List Region, ∃ x y : State,
      CallRel k rw.1 rw.2 x y a b ∧ x.rd = a.rd ∧ x.wr = a.wr ∧ y.rd = b.rd ∧ y.wr = b.wr)
    (RelCT.exists_ fun (rw : List Region × List Region) => RelCT.callRet hv hr rw.1 rw.2
      fun a b ⟨x, y, h, e1, e2, e3, e4⟩ => by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
        exact ⟨h1, h2, h3, by rwa [← e1, ← e2], by rwa [← e2], by rwa [← e3, ← e4], by rwa [← e4]⟩) ?_
    fun _ _ h => h
  rintro a b ⟨-, x, y, hp, rfl, rfl⟩
  obtain ⟨rd, wr, h⟩ := hP x y hp
  exact ⟨(rd, wr), x, y, h, (glueSt_rd x as).symm, (glueSt_wr x as).symm, (glueSt_rd y as).symm,
    (glueSt_wr y as).symm⟩

/-! ## The samplers' calls, with their bounds -/

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {L : Lay} {Wb : List Nat} {STK : Nat}
include hP

/-- `rn_ok`, and the success of `RejNTTPoly` within `maxBounds` if the call succeeded. -/
theorem rn_okX {s : State} (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} {sd a w : Impl.MlDsa.RISCV64.KeyGen.Ptr}
    (m : KeyGen.RnOk L Wb sd a w) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri a 1024, tri w 2048, (1, 0, STK)]) s s' →
      ((s'.gpr .a0).setWidth 32 = 1 → Reduced s'.mem (lpa L a)) →
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (lpa L sd) 34)) ((s'.gpr .a0).setWidth 32)
        (polyAt s'.mem (lpa L a)) →
      ((s'.gpr .a0).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (lpa L sd) 34)).isSome) → Q s') :
    WP isa (callAt name P.rejNTT (KeyGen.rnArgs sd a w)) s Q := by
  obtain ⟨stk, hstk, hver, -, hmax⟩ := hP.rejX
  obtain ⟨c1, c2⟩ := KeyGen.rn_cov hs m
  have hv : ∀ s₀, (rejNTTContract RISCV64.abi stk).pre s₀ → ∃ t s', Exec isa P.rejNTT s₀ t s' ∧
      abiPreserved s₀ s' ∧ ((rejNTTContract RISCV64.abi stk).post s₀ s' ∧
        ((s'.gpr .a0).setWidth 32 = 1 →
          (rejNTTPoly maxBounds.rejNTT (bytesAt s₀.mem (s₀.gpr .a0) 34)).isSome)) := fun s₀ h₀ => by
    obtain ⟨t, s', e, ha, hp⟩ := hver.1 s₀ h₀
    exact ⟨t, s', e, ha, hp, hmax s₀ t s' h₀ e⟩
  refine KeyGen.callV (k := { rejNTTContract RISCV64.abi stk with
      post := fun s₀ s' => (rejNTTContract RISCV64.abi stk).post s₀ s' ∧
        ((s'.gpr .a0).setWidth 32 = 1 →
          (rejNTTPoly maxBounds.rejNTT (bytesAt s₀.mem (s₀.gpr .a0) 34)).isSome) }) hv
    (hs.depth hP.rejNTT.stack hS) m.hg (KeyGen.rn_preS hs (Nat.le_trans hstk hS) m) c1 c2
    fun s' hk ⟨hp, hx⟩ => hQ s' (hs.keptW [tri a 1024, tri w 2048] (Nat.le_trans hP.rejNTT.stack hS) hk) ?_ ?_ ?_
  all_goals
    obtain ⟨g3, g4, -⟩ := KeyGen.rn_vg hs m (KeyGen.rnRd L sd) (KeyGen.rnWr L a w)
    have := KeyGen.rejNtt_post hp
    rw [State.withRegions_mem, State.withRegions_gpr, g3, g4, KeyGen.view_glue_mem] at this
    rw [g3, KeyGen.view_glue_mem, State.withRegions_gpr] at hx
  exacts [this.1, this.2, hx]

/-- `ball_ok`, and the success of `SampleInBall` within `maxBounds` if the call succeeded. -/
theorem ball_okX {s : State} (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String}
    {ct c w : Impl.MlDsa.RISCV64.KeyGen.Ptr} {len tau : Nat} (m : KeyGen.BallOk L Wb ct len tau c w)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri c 1024, tri w 2048, (1, 0, STK)]) s s' →
      ((s'.gpr .a0).setWidth 32 = 1 → Reduced s'.mem (lpa L c)) →
      Outcome (fun b => (sampleInBall tau b.ball (bytesAt s.mem (lpa L ct) len)).map toRq)
        ((s'.gpr .a0).setWidth 32) (polyAt s'.mem (lpa L c)) →
      ((s'.gpr .a0).setWidth 32 = 1 → (sampleInBall tau maxBounds.ball (bytesAt s.mem (lpa L ct) len)).isSome) →
      Q s') :
    WP isa (callAt name P.ball (KeyGen.ballArgs ct len tau c w)) s Q := by
  obtain ⟨stk, hstk, hver, -, hmax⟩ := hP.ballX
  obtain ⟨c1, c2⟩ := KeyGen.ball_cov hs m
  obtain ⟨l0, ll, lt⟩ := m.lt
  have hv : ∀ s₀, (sampleInBallContract RISCV64.abi stk).pre s₀ → ∃ t s', Exec isa P.ball s₀ t s' ∧
      abiPreserved s₀ s' ∧ ((sampleInBallContract RISCV64.abi stk).post s₀ s' ∧
        ((s'.gpr .a0).setWidth 32 = 1 → (sampleInBall ((s₀.gpr .a2).setWidth 32).toNat maxBounds.ball
          (bytesAt s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)).isSome)) := fun s₀ h₀ => by
    obtain ⟨t, s', e, ha, hp⟩ := hver.1 s₀ h₀
    exact ⟨t, s', e, ha, hp, hmax s₀ t s' h₀ e⟩
  refine KeyGen.callV (k := { sampleInBallContract RISCV64.abi stk with
      post := fun s₀ s' => (sampleInBallContract RISCV64.abi stk).post s₀ s' ∧
        ((s'.gpr .a0).setWidth 32 = 1 → (sampleInBall ((s₀.gpr .a2).setWidth 32).toNat maxBounds.ball
          (bytesAt s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)).isSome) }) hv
    (hs.depth hP.ball.stack hS) m.hg (KeyGen.ball_preS hs (Nat.le_trans hstk hS) m) c1 c2
    fun s' hk ⟨hp, hx⟩ => hQ s' (hs.keptW [tri c 1024, tri w 2048] (Nat.le_trans hP.ball.stack hS) hk) ?_ ?_ ?_
  all_goals
    obtain ⟨g3, g4, g5, g6, -⟩ := KeyGen.ball_vg hs m (KeyGen.ballRd L ct len) (KeyGen.ballWr L c w)
    have := KeyGen.ball_post hp
    rw [State.withRegions_mem, State.withRegions_gpr, g3, g4, g5, g6, KeyGen.view_glue_mem,
      KeyGen.imm32 (by omega_arith), KeyGen.imm32_toNat (by omega_arith), KeyGen.imm_toNat (by omega_arith)] at this
    rw [g3, g4, g5, KeyGen.view_glue_mem, State.withRegions_gpr, KeyGen.imm32 (by omega_arith), KeyGen.imm32_toNat (by omega_arith),
      KeyGen.imm_toNat (by omega_arith)] at hx
  exacts [this.1, this.2, hx]

theorem rn_trRet (hS : S ≤ STK) {name : String} {sd a w : Impl.MlDsa.RISCV64.KeyGen.Ptr}
    (m : KeyGen.RnOk L Wb sd a w) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      bytesAt x.mem (lpa L sd) 34 = bytesAt y.mem (lpa L sd) 34) :
    RelCT isa Q (callAt name P.rejNTT (KeyGen.rnArgs sd a w))
      fun x y => (x.gpr .a0).setWidth 32 = (y.gpr .a0).setWidth 32 := by
  obtain ⟨stk, hstk, hver, hret, -⟩ := hP.rejX
  refine callVRet_tr hver.1 hret m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, hl⟩ := hQ x y hxy
  obtain ⟨gx3, gx4, gx5⟩ := KeyGen.rn_vg hx m (KeyGen.rnRd L sd) (KeyGen.rnWr L a w)
  obtain ⟨gy3, gy4, gy5⟩ := KeyGen.rn_vg hy m (KeyGen.rnRd L sd) (KeyGen.rnWr L a w)
  refine ⟨KeyGen.rnRd L sd, KeyGen.rnWr L a w, KeyGen.rn_preS hx (Nat.le_trans hstk hS) m,
    KeyGen.rn_preS hy (Nat.le_trans hstk hS) m,
    KeyGen.rejNtt_pub (by rw [KeyGen.view_glue_sp, KeyGen.view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4])
      (by rw [gx5, gy5]) ?_, (KeyGen.rn_cov hx m).1, (KeyGen.rn_cov hx m).2, (KeyGen.rn_cov hy m).1,
    (KeyGen.rn_cov hy m).2⟩
  rw [gx3, gy3, KeyGen.view_glue_mem, KeyGen.view_glue_mem]
  exact hl

theorem ball_trRet (hS : S ≤ STK) {name : String} {ct c w : Impl.MlDsa.RISCV64.KeyGen.Ptr} {len tau : Nat}
    (m : KeyGen.BallOk L Wb ct len tau c w) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      bytesAt x.mem (lpa L ct) len = bytesAt y.mem (lpa L ct) len) :
    RelCT isa Q (callAt name P.ball (KeyGen.ballArgs ct len tau c w))
      fun x y => (x.gpr .a0).setWidth 32 = (y.gpr .a0).setWidth 32 := by
  obtain ⟨stk, hstk, hver, hret, -⟩ := hP.ballX
  obtain ⟨l0, ll, lt⟩ := m.lt
  refine callVRet_tr hver.1 hret m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, hl⟩ := hQ x y hxy
  obtain ⟨gx3, gx4, gx5, gx6, gx7⟩ := KeyGen.ball_vg hx m (KeyGen.ballRd L ct len) (KeyGen.ballWr L c w)
  obtain ⟨gy3, gy4, gy5, gy6, gy7⟩ := KeyGen.ball_vg hy m (KeyGen.ballRd L ct len) (KeyGen.ballWr L c w)
  refine ⟨KeyGen.ballRd L ct len, KeyGen.ballWr L c w, KeyGen.ball_preS hx (Nat.le_trans hstk hS) m,
    KeyGen.ball_preS hy (Nat.le_trans hstk hS) m,
    KeyGen.ball_pub (by rw [KeyGen.view_glue_sp, KeyGen.view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4])
      (by rw [gx5, gy5]) (by rw [gx6, gy6]) (by rw [gx7, gy7]) ?_, (KeyGen.ball_cov hx m).1, (KeyGen.ball_cov hx m).2,
    (KeyGen.ball_cov hy m).1, (KeyGen.ball_cov hy m).2⟩
  rw [gx3, gy3, gx4, gy4, KeyGen.view_glue_mem, KeyGen.view_glue_mem, KeyGen.imm_toNat (by omega_arith)]
  exact hl

end

/-! ## Two runs related by more than their entry states -/

/-- Two runs, each satisfying `I` from its entry state, related by `E`. -/
def RR (p : Params) (STK : Nat) (I E : State → State → Prop) (x y : State) : Prop :=
  Rel2 (SPre p STK) (sPub p) I x y ∧ E x y

theorem WP.conj {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁) (h₂ : WP isa c s Q₂) :
    WP isa c s fun s' => Q₁ s' ∧ Q₂ s' := by
  obtain ⟨t, s', e, q₁⟩ := h₁
  obtain ⟨_, _, e', q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact ⟨t, _, e, q₁, q₂⟩

/-- A piece that takes each run from `I` to `J` and from `s` to `s'` with
`F s s'`, and leaks the same from runs related by `RR I E`, with `Q₀` of the
final states. -/
theorem stepRR {p : Params} {STK : Nat} {I J E E' Q₀ F : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, SPre p STK σ → I σ s → WP isa c s fun s' => J σ s' ∧ F s s')
    (ht : RelCT isa (RR p STK I E) c Q₀)
    (hE : ∀ x y x' y', RR p STK I E x y → F x x' → F y y' → Q₀ x' y' → E' x' y') :
    RelCT isa (RR p STK I E) c (RR p STK J E') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', hq⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, he⟩ := hr
  obtain ⟨_, u₁, f₁, g₁, k₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂, k₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', ⟨σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩, hE _ _ _ _ ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, he⟩ k₁ k₂ hq⟩

/-! ## `ρ` -/

theorem signLeak_head (p : Params) (sk μ rnd : List Byte) :
    ∃ X, signLeak p sk μ rnd = leakBytes (sk.take 32) ++ X := by
  unfold signLeak
  rcases e : skDecode p sk with ⟨ρ, K, tr, s₁, s₂, t₀⟩
  have hρ : ρ = sk.take 32 := by rw [← Proof.MlDsa.Sign.skRho_eq p sk, e]
  subst hρ
  exact ⟨_, rfl⟩

theorem leak_rho {p : Params} {sk₁ sk₂ μ₁ μ₂ r₁ r₂ : List Byte} (h1 : sk₁.length = p.skLen)
    (h2 : sk₂.length = p.skLen) (h : signLeak p sk₁ μ₁ r₁ = signLeak p sk₂ μ₂ r₂) :
    sk₁.take 32 = sk₂.take 32 := by
  obtain ⟨X₁, e₁⟩ := signLeak_head p sk₁ μ₁ r₁
  obtain ⟨X₂, e₂⟩ := signLeak_head p sk₂ μ₂ r₂
  rw [e₁, e₂] at h
  refine Proof.MlDsa.Sign.leakBytes_inj (List.append_inj h ?_).1
  rw [Proof.MlDsa.Sign.leakBytes_length, Proof.MlDsa.Sign.leakBytes_length, List.length_take, List.length_take, h1, h2]

theorem pub_rho {p : Params} {σ₁ σ₂ : State} (h : sPub p σ₁ σ₂) : (skOf p σ₁).take 32 = (skOf p σ₂).take 32 :=
  leak_rho (Proof.MlKem.bytesAt_length _ _ _) (Proof.MlKem.bytesAt_length _ _ _) h.2.2.2.2.2.2.1

/-! ## The state, but for `a0` and `s4` -/

theorem SC1.regs2 {p : Params} {STK : Nat} {σ s s' : State} (h : SC1 p STK σ s) (hr : Regs2 s s') :
    SC1 p STK σ s' :=
  ⟨h.site.regs2 hr, hr.rd.trans h.rd, hr.wr.trans h.wr, hr.sp.trans h.sp,
    fun r hp hs => by
      have : r ≠ .a0 ∧ r ≠ .s4 := ⟨fun e => by subst e; simp [preserved] at hp,
        fun e => by subst e; simp [savedTop] at hs⟩
      rw [hr.gpr r this.1 this.2]; exact h.pres r hp hs,
    by rw [hr.mem]; exact h.sav, by rw [hr.mem]; exact h.sig, by rw [hr.mem]; exact h.sk, by rw [hr.mem]; exact h.mu,
    by rw [hr.mem]; exact h.rnd, h.pre, by rw [hr.gpr .s3 (by decide) (by decide)]; exact h.s3,
    by rw [hr.mem]; exact h.cache⟩

theorem SC2.regs2 {p : Params} {STK : Nat} {σ s s' : State} (h : SC2 p STK σ s) (hr : Regs2 s s') :
    SC2 p STK σ s' :=
  ⟨h.site.regs2 hr, hr.rd.trans h.rd, hr.wr.trans h.wr, hr.sp.trans h.sp,
    fun r hp hs => by
      have : r ≠ .a0 ∧ r ≠ .s4 := ⟨fun e => by subst e; simp [preserved] at hp,
        fun e => by subst e; simp [savedTop] at hs⟩
      rw [hr.gpr r this.1 this.2]; exact h.pres r hp hs,
    by rw [hr.mem]; exact h.sav, by rw [hr.mem]; exact h.sk, by rw [hr.mem]; exact h.mu, h.pre,
    by rw [hr.gpr .s3 (by decide) (by decide)]; exact h.s3, by rw [hr.mem]; exact h.cache⟩

/-! ## Two runs -/

section
variable {p : Params} {STK : Nat}

theorem sc1_twoL {σ₁ σ₂ x y : State} (pub : sPub p σ₁ σ₂) (h₁ : SC1 p STK σ₁ x) (h₂ : SC1 p STK σ₂ y) :
    Two (slay1 p STK σ₁) sWb1 STK x y :=
  ⟨h₁.site, slay1_pub pub ▸ h₂.site, by rw [h₁.sp, h₂.sp, pub.1]⟩

theorem sc2_twoL {σ₁ σ₂ x y : State} (pub : sPub p σ₁ σ₂) (h₁ : SC2 p STK σ₁ x) (h₂ : SC2 p STK σ₂ y) :
    Two (slay2 p STK σ₁) sWb2 STK x y :=
  ⟨h₁.site, slay2_pub pub ▸ h₂.site, by rw [h₁.sp, h₂.sp, pub.1]⟩

/-- A piece without calls before the hash of `ρ″`, checked by the taint
analysis from `scratch`. -/
theorem srel1 {I : State → State → Prop} (hI : ∀ σ s, I σ s → SC1 p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.RISCV64.taint.T}
    (h : (VG.RISCV64.taint.check (Taint.ofRegs [.s11]) c hc).isSome = true) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) I) c fun _ _ => True :=
  rel_of (RelCT.exists_ fun _ => taint31 (fun _ _ h => h) h)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc1_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

/-- A piece without calls after the hash of `ρ″`, checked by the taint
analysis from `scratch`. -/
theorem srel2 {I : State → State → Prop} (hI : ∀ σ s, I σ s → SC2 p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.RISCV64.taint.T}
    (h : (VG.RISCV64.taint.check (Taint.ofRegs [.s11]) c hc).isSome = true) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) I) c fun _ _ => True :=
  rel_of (RelCT.exists_ fun _ => taint31 (fun _ _ h => h) h)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

/-- `srel1`, from all the pointers. -/
theorem srel1p {I : State → State → Prop} (hI : ∀ σ s, I σ s → SC1 p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.RISCV64.taint.T}
    (h : (VG.RISCV64.taint.check (Taint.ofRegs [.s8, .s9, .s10, .s11]) c hc).isSome = true) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) I) c fun _ _ => True :=
  rel_of (RelCT.exists_ fun _ => taint4 (fun _ _ h => h) h)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc1_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

/-- `srel2`, from all the pointers. -/
theorem srel2p {I : State → State → Prop} (hI : ∀ σ s, I σ s → SC2 p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.RISCV64.taint.T}
    (h : (VG.RISCV64.taint.check (Taint.ofRegs [.s8, .s9, .s10, .s11]) c hc).isSome = true) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) I) c fun _ _ => True :=
  rel_of (RelCT.exists_ fun _ => taint4 (fun _ _ h => h) h)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

end

end VG.Proof.MlDsa.RISCV64.Sign

end

end

/-!
# ML-DSA signing on RISC-V: `Â`

As on PPC64LE (`Proof/MlDsa/PPC64LE/Sign/PhaseA.lean`): `ρ` to the seed `RS`,
then each entry `e` of `Â`: its two bytes to the seed, `RejNTTPoly` to its
slot, and its result ANDed into `s4` (`IA`: after `e` entries, either every
sampling so far finished within `maxBounds` and the slots hold the entries,
or one did not finish within `minBounds`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sign

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv taint31
  Regs2 Callee polyIs_keepW polyAt_keepW reduced_keepW bytes_keepW setB_ok copyS zx zx_01 and24_ok)
open VG.Impl.MlDsa.RISCV64.Sign
open VG.Impl.MlDsa.RISCV64.KeyGen (and24 setB seqR callAt)
open VG.Impl.MlKem.RISCV64 (copy)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign (aSeed aF rejNTTPoly_mono)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- `ρ`. -/
abbrev rhoOf (σ : State) : List Byte := (skOf p σ).take 32

/-- The seed of entry `e`. -/
abbrev seedE (σ : State) (e : Nat) : List Byte := aSeed (rhoOf p σ) (e / p.ℓ) (e % p.ℓ)

/-- Entry `e` of `Â`, within `maxBounds`. -/
abbrev aVal (σ : State) (e : Nat) : Poly := aF maxBounds.rejNTT (rhoOf p σ) (e / p.ℓ) (e % p.ℓ)

end

theorem aP_eq (p : Params) (e : Nat) : aP p (e / p.ℓ) (e % p.ℓ) = pS (aBase p + e) := by
  show sc (oP (5 + 4 * p.k + 3 * p.ℓ + p.ℓ * (e / p.ℓ) + e % p.ℓ)) = sc (oP (5 + 4 * p.k + 3 * p.ℓ + e))
  rw [Nat.add_assoc _ (p.ℓ * _), Nat.div_add_mod]

/-- `ExpandA` after `e` entries. -/
structure IA (p : Params) (STK : Nat) (σ : State) (e : Nat) (s : State) : Prop where
  sc : SC1 p STK σ s
  rs : bytesAt s.mem ((slay1 p STK σ).A 0 oRS) 32 = rhoOf p σ
  r01 : s.gpr .s4 = 0 ∨ s.gpr .s4 = 1
  ok : s.gpr .s4 = 1 → (∀ e' < e, (rejNTTPoly maxBounds.rejNTT (seedE p σ e')).isSome) ∧
    ∀ e' < e, PolyIs s.mem ((slay1 p STK σ).A 0 (oP (aBase p + e'))) (aVal p σ e')
  bad : s.gpr .s4 = 0 → ∃ e' < e, rejNTTPoly minBounds.rejNTT (seedE p σ e') = none

/-- The result of `vg_mldsa_rej_ntt_poly`, if it succeeded within `maxBounds`. -/
theorem rej_val {x : List Byte} {r : BitVec 32} {out : Poly}
    (h : Outcome (fun b => rejNTTPoly b.rejNTT x) r out) (h1 : r = 1)
    (hm : (rejNTTPoly maxBounds.rejNTT x).isSome) : out = (rejNTTPoly maxBounds.rejNTT x).getD zero := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    have e1 := rejNTTPoly_mono (Nat.le_max_left b.rejNTT maxBounds.rejNTT) hb
    have e2 := rejNTTPoly_mono (Nat.le_max_right b.rejNTT maxBounds.rejNTT) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

theorem integerToBytes_one {x : Nat} : integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [integerToBytes]

theorem aSeed_eq (ρ : List Byte) (i j : Nat) : aSeed ρ i j = ρ ++ [BitVec.ofNat 8 j, BitVec.ofNat 8 i] := by
  simp only [aSeed, integerToBytes_one, List.append_assoc]; rfl

theorem and24_01 {a x : BitVec 64} (ha : a = 0 ∨ a = 1) (hx : x.setWidth 32 = 0 ∨ x.setWidth 32 = 1) :
    (a &&& zx x = 0 ∨ a &&& zx x = 1) ∧ (a &&& zx x = 1 ↔ a = 1 ∧ x.setWidth 32 = 1) := by
  rcases ha with rfl | rfl <;> rcases hx with h | h <;> simp only [zx, h] <;> decide

/-- `s4` is the same in two runs. -/
abbrev E24 (x y : State) : Prop := x.gpr .s4 = y.gpr .s4

theorem wp_seqR {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → ∀ s, I k s → WP isa (f k) s (I (k + 1))) →
      ∀ s, I a s → WP isa (seqR f a n) s (I (a + n))
  | 0, a, _, s, hs => by rw [seqR, Nat.add_zero]; exact WP.block_nil hs
  | n + 1, a, h, s, hs => by
    rw [seqR, show a + (n + 1) = a + 1 + n by omega_using []]
    exact WP.seq (WP.mono (h a (Nat.le_refl _) (by omega_using []) s hs) fun s' hs' =>
      wp_seqR n (a + 1) (fun k h₁ h₂ => h k (by omega_using [h₁]) (by omega_using [h₂])) s' hs')

theorem rr_seqR {f : Nat → Prog isa} {R : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → RelCT isa (R k) (f k) (R (k + 1))) →
      RelCT isa (R a) (seqR f a n) (R (a + n))
  | 0, a, _ => by
    rw [seqR, Nat.add_zero]
    intro _ _ _ _ _ _ hr e₁ e₂
    rw [Exec.block_iff] at e₁ e₂
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    obtain ⟨rfl, rfl⟩ := e₁
    obtain ⟨rfl, rfl⟩ := e₂
    exact ⟨rfl, hr⟩
  | n + 1, a, h => by
    rw [seqR, show a + (n + 1) = a + 1 + n by omega_using []]
    exact RelCT.seq (h a (Nat.le_refl _) (by omega_using [])) (rr_seqR n (a + 1) fun k h₁ h₂ => h k (by omega_using [h₁]) (by omega_using [h₂]))

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hS in
theorem rnE_m {σ : State} {e : Nat} (he : e < p.k * p.ℓ) :
    KeyGen.RnOk (slay1 p STK σ) sWb1 (sc oRS) (pS (aBase p + e)) (sc oPS) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  exact ⟨⟨sptr_ok rfl (by decide), by ssep hF⟩, ⟨sptr_ok rfl (by slt hF), by ssep hF⟩,
    ⟨sptr_ok rfl (by decide), by ssep hF⟩, show ix Reg.s11 ∈ sWb1 by decide, show ix Reg.s11 ∈ sWb1 by decide,
    by ssep hF, by ssep hF, by ssep hF, by salsep, by salsep⟩

/-- The two bytes of the seed of entry `e`. -/
abbrev blkE (p : Params) (e : Nat) : List Instr := setB (sc (oRS + 32)) (e % p.ℓ) ++ setB (sc (oRS + 33)) (e / p.ℓ)

omit hP hS in
theorem blkE_ok {e : Nat} (he : e < p.k * p.ℓ) {σ s : State} (h : IA p STK σ e s) :
    WP isa (.block (blkE p e)) s fun s' =>
      (IA p STK σ e s' ∧ bytesAt s'.mem ((slay1 p STK σ).A 0 oRS) 34 = seedE p σ e) ∧ s'.gpr .s4 = s.gpr .s4 := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hs := h.sc.site
  have hL := hs.ok
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega_using [hl])
  refine WP.block_append (WP.mono (setB_ok hs (q := sc (oRS + 32)) ⟨sptr_ok rfl (by decide), by ssep hF⟩
    (by decide) (by decide) (v := e % p.ℓ) (by omega_using [hl, hr])) fun s₁ ⟨k₁, b₁⟩ => WP.mono (setB_ok (hs.kept k₁)
      (q := sc (oRS + 33)) ⟨sptr_ok rfl (by decide), by ssep hF⟩ (by decide) (by decide) (v := e / p.ℓ) (by omega_using [hk, hq]))
      fun s₂ ⟨k₂, b₂⟩ => ?_)
  have sc₂ := (h.sc.keep k₁ (by ssep hF [sc1Chk])).keep k₂ (by ssep hF [sc1Chk])
  have rs₂ : bytesAt s₂.mem ((slay1 p STK σ).A 0 oRS) 32 = rhoOf p σ :=
    (bytes_keepW hL k₂.frame (i := 0) (o := oRS) (l := 32) (by ssep hF) (by decide) (by decide)).trans
      ((bytes_keepW hL k₁.frame (i := 0) (o := oRS) (l := 32) (by ssep hF) (by decide) (by decide)).trans h.rs)
  have h24₂ : s₂.gpr .s4 = s.gpr .s4 := by rw [k₂.cs .s4 (by decide), k₁.cs .s4 (by decide)]
  refine ⟨⟨⟨sc₂, rs₂, by rw [h24₂]; exact h.r01, fun h1 => ?_, fun h0 => h.bad (by rw [← h24₂]; exact h0)⟩, ?_⟩, h24₂⟩
  · obtain ⟨ok1, fam⟩ := h.ok (by rw [← h24₂]; exact h1)
    exact ⟨ok1, fun e' he' => polyIs_keepW hL k₂.frame (by ssep hF) (by decide) rfl
      (polyIs_keepW hL k₁.frame (by ssep hF) (by decide) rfl (fam e' he'))⟩
  · have b₁' := bytes_keepW hL k₂.frame (i := 0) (o := oRS + 32) (l := 1) (by ssep hF) (by decide) (by decide)
    rw [show (34 : Nat) = 32 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, rs₂, seedE,
      aSeed_eq, List.append_assoc]
    refine congrArg _ ?_
    have e1 : bytesAt s₂.mem ((slay1 p STK σ).A 0 (oRS + 32)) 1 = [BitVec.ofNat 8 (e % p.ℓ)] := b₁'.trans b₁
    have e2 : bytesAt s₂.mem ((slay1 p STK σ).A 0 (oRS + 33)) 1 = [BitVec.ofNat 8 (e / p.ℓ)] := b₂
    simp only [Lay.A, BitVec.add_assoc, ← BitVec.ofNat_add] at e1 e2 ⊢
    rw [e1, e2]; rfl

/-- Entry `e`'s call is done. -/
def JE (p : Params) (STK : Nat) (e : Nat) (σ s : State) : Prop :=
  ∃ s₀, IA p STK σ e s₀ ∧
    Kept ((slay1 p STK σ).RL [tri (pS (aBase p + e)) 1024, tri (sc oPS) 2048, (1, 0, STK)]) s₀ s ∧
    ((s.gpr .a0).setWidth 32 = 1 → Reduced s.mem ((slay1 p STK σ).A 0 (oP (aBase p + e)))) ∧
    Outcome (fun b => rejNTTPoly b.rejNTT (seedE p σ e)) ((s.gpr .a0).setWidth 32)
      (polyAt s.mem ((slay1 p STK σ).A 0 (oP (aBase p + e)))) ∧
    ((s.gpr .a0).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (seedE p σ e)).isSome)

theorem callE_ok {e : Nat} (he : e < p.k * p.ℓ) {σ s : State} (h : IA p STK σ e s)
    (hs : bytesAt s.mem ((slay1 p STK σ).A 0 oRS) 34 = seedE p σ e) :
    WP isa (callAt "vg_mldsa_rej_ntt_poly" P.rejNTT (KeyGen.rnArgs (sc oRS) (pS (aBase p + e)) (sc oPS))) s
      fun s' => JE p STK e σ s' ∧ s'.gpr .s4 = s.gpr .s4 :=
  rn_okX hP h.sc.site hS (rnE_m hF he) fun s' k' hred hout hmax =>
    ⟨⟨s, h, k', hred, by rw [← hs]; exact hout, by rw [← hs]; exact hmax⟩, k'.cs .s4 (by decide)⟩

omit hP hS in
theorem andE_ok {e : Nat} (he : e < p.k * p.ℓ) {σ s : State} (h : JE p STK e σ s) :
    WP isa (.block and24) s (IA p STK σ (e + 1)) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  obtain ⟨s₃₀, h, k₃, hred, hout, hmax⟩ := h
  have hL := h.sc.site.ok
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  have sc₃ := h.sc.keep k₃ (by ssep hF [sc1Chk])
  have h24₃ : s.gpr .s4 = s₃₀.gpr .s4 := k₃.cs .s4 (by decide)
  refine WP.mono (and24_ok s) fun s₄ ⟨_, e24, r₄⟩ => ?_
  obtain ⟨a01, aeq⟩ := and24_01 (a := s.gpr .s4) (by rw [h24₃]; exact h.r01) hr01
  rw [h24₃] at a01 aeq
  refine ⟨sc₃.regs2 r₄, ?_, by rw [e24, h24₃]; exact a01, fun h1 => ?_, fun h0 => ?_⟩
  · rw [r₄.mem]
    exact (bytes_keepW hL k₃.frame (i := 0) (o := oRS) (l := 32) (by ssep hF) (by decide) (by decide)).trans h.rs
  · rw [e24, h24₃] at h1
    obtain ⟨hs1, hr1⟩ := aeq.mp h1
    obtain ⟨ok1, fam⟩ := h.ok hs1
    have hm := hmax hr1
    refine ⟨fun e' he' => ?_, fun e' he' => ?_⟩
    · rcases (by omega_using [he'] : e' < e ∨ e' = e) with he' | rfl
      exacts [ok1 e' he', hm]
    · rw [r₄.mem]
      rcases (by omega_using [he'] : e' < e ∨ e' = e) with he' | rfl
      · exact polyIs_keepW hL k₃.frame (by ssep hF) (by decide) rfl (fam e' he')
      · exact ⟨hred hr1, rej_val hout hr1 hm⟩
  · rw [e24, h24₃] at h0
    rcases h.r01 with e0 | e0
    · obtain ⟨e', he', hn⟩ := h.bad e0
      exact ⟨e', by omega_using [he'], hn⟩
    · rcases hr01 with e1 | e1
      · rcases hout with ⟨h1, _⟩ | ⟨_, hn⟩
        · rw [e1] at h1; cases h1
        · exact ⟨e, by omega_using [], hn⟩
      · rw [e0] at h0; simp only [zx, e1] at h0; exact absurd h0 (by decide)

omit hP hF hS in
theorem sampleE_eq (e : Nat) : sampleE P p e = .seq (.block (blkE p e))
    (.seq (callAt "vg_mldsa_rej_ntt_poly" P.rejNTT (KeyGen.rnArgs (sc oRS) (pS (aBase p + e)) (sc oPS)))
      (.block and24)) := by
  unfold sampleE rejAt; rw [aP_eq]

theorem sampleE_ok {e : Nat} (he : e < p.k * p.ℓ) {σ s : State} (h : IA p STK σ e s) :
    WP isa (sampleE P p e) s (IA p STK σ (e + 1)) := by
  rw [sampleE_eq]
  exact WP.seq (WP.mono (blkE_ok hF he h) fun s1 ⟨⟨h1, hs1⟩, _⟩ =>
    WP.seq (WP.mono (callE_ok hP hF hS he h1 hs1) fun s2 ⟨h2, _⟩ => andE_ok hF he h2))


/-! ## `ExpandA` -/

omit hP hS in
theorem sk_rho {σ s : State} (h : SC1 p STK σ s) : bytesAt s.mem ((slay1 p STK σ).A 2 0) 32 = rhoOf p σ := by
  have := hF.sk
  rw [rhoOf, ← h.sk, Proof.MlKem.bytesAt_take _ _ (by omega_using [this])]

omit hP hS in
theorem rho_ok {σ s : State} (h : SC1 p STK σ s) (h1 : s.gpr .s4 = 1) :
    WP isa (copy .s10 0 .s11 oRS 32) s fun s' => IA p STK σ 0 s' ∧ s'.gpr .s4 = 1 := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine WP.mono (copyS h.site (sb := .s10) (so := 0) (db := .s11) (dO := oRS) (len := 32)
    ⟨sptr_ok rfl (by have := hF.sk; omega_using []), by ssep hF⟩ ⟨sptr_ok rfl (by decide), by ssep hF⟩ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by ssep hF))
    fun s' ⟨k', b'⟩ => ?_
  have h24 : s'.gpr .s4 = 1 := by rw [k'.cs .s4 (by decide), h1]
  refine ⟨⟨h.keep k' (by ssep hF [sc1Chk]), ?_, .inr h24, fun _ => ⟨fun _ hd => absurd hd (by omega_using []),
    fun _ hd => absurd hd (by omega_using [])⟩, fun h0 => absurd (h0.symm.trans h24) (by decide)⟩, h24⟩
  show bytesAt s'.mem (lpa (slay1 p STK σ) (.s11, oRS)) 32 = _
  rw [b', show lpa (slay1 p STK σ) (.s10, 0) = (slay1 p STK σ).A 2 0 from rfl, sk_rho hF h]

theorem expandA_ok {σ s : State} (h : SC1 p STK σ s) (h1 : s.gpr .s4 = 1) :
    WP isa (expandA P p) s (IA p STK σ (p.k * p.ℓ)) := by
  unfold Impl.MlDsa.RISCV64.Sign.expandA
  refine WP.seq (WP.mono (rho_ok hF h h1) fun s' h' => ?_)
  simpa using wp_seqR (I := fun e => IA p STK σ e) (p.k * p.ℓ) 0
    (fun e _ he _ hs => sampleE_ok hP hF hS (by omega_using [he]) hs) s' h'.1

omit hP hF hS in
theorem blkE_taint : ∀ v < 8, ∀ w < 8, (VG.RISCV64.taint.check (Taint.ofRegs [.s11])
    (.block (setB (sc (oRS + 32)) v ++ setB (sc (oRS + 33)) w)) (.block [])).isSome = true := by decide +kernel

omit hP hF hS in
theorem and24_taint : (VG.RISCV64.taint.check (Taint.ofRegs [.s11]) (.block and24) (.block [])).isSome = true := by
  decide +kernel

theorem sampleE_tr {e : Nat} (he : e < p.k * p.ℓ) :
    RelCT isa (RR p STK (IA p STK · e) E24) (sampleE P p e) (RR p STK (IA p STK · (e + 1)) E24) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega_using [hl])
  rw [sampleE_eq]
  refine RelCT.seq (stepRR
    (J := fun σ s => IA p STK σ e s ∧ bytesAt s.mem ((slay1 p STK σ).A 0 oRS) 34 = seedE p σ e)
    (F := fun s s' => s'.gpr .s4 = s.gpr .s4) (E' := E24)
    (fun σ s _ h => blkE_ok hF he h)
    (RelCT.mono (srel1 (fun σ s h => h.sc) (blkE_taint _ (by omega_using [hl, hr]) _ (by omega_using [hk, hq]))) (fun _ _ h => h.1) fun _ _ h => h)
    fun x y x' y' hr fx fy _ => by show _ = _; rw [fx, fy]; exact hr.2) ?_
  refine RelCT.seq (stepRR (J := JE p STK e) (F := fun s s' => s'.gpr .s4 = s.gpr .s4)
    (E' := fun x y => E24 x y ∧ (x.gpr .a0).setWidth 32 = (y.gpr .a0).setWidth 32)
    (fun σ s _ h => callE_ok hP hF hS he h.1 h.2) ?_
    fun x y x' y' hr fx fy q => ⟨by show _ = _; rw [fx, fy]; exact hr.2, q⟩) ?_
  · refine RelCT.mono (RelCT.exists_ fun σ => rn_trRet hP (L := slay1 p STK σ) (Wb := sWb1) hS
      (name := "vg_mldsa_rej_ntt_poly") (rnE_m hF he)
      (Q := fun x y => Site (slay1 p STK σ) sWb1 STK x ∧ Site (slay1 p STK σ) sWb1 STK y ∧ x.sp = y.sp ∧
        bytesAt x.mem (lpa (slay1 p STK σ) (sc oRS)) 34 = bytesAt y.mem (lpa (slay1 p STK σ) (sc oRS)) 34)
      fun _ _ h => h) ?_ fun _ _ h => h
    rintro x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, ⟨h₁, b₁⟩, ⟨h₂, b₂⟩⟩, -⟩
    have T := sc1_twoL pub h₁.sc h₂.sc
    refine ⟨σ₁, T.1, T.2.1, T.2.2, ?_⟩
    show bytesAt x.mem ((slay1 p STK σ₁).A 0 oRS) 34 = bytesAt y.mem ((slay1 p STK σ₁).A 0 oRS) 34
    rw [b₁, slay1_pub pub, b₂, seedE, seedE, rhoOf, rhoOf, pub_rho pub]
  · refine stepRR (J := fun σ s => IA p STK σ (e + 1) s)
      (F := fun s s' => s'.gpr .s4 = s.gpr .s4 &&& zx (s.gpr .a0)) (Q₀ := fun _ _ => True)
      (fun σ s _ h => WP.conj (andE_ok hF he h) (WP.mono (and24_ok s) fun _ h => h.2.1))
      (RelCT.mono (srel1 (fun σ s h => ?_) and24_taint) (fun _ _ h => h.1) fun _ _ h => h)
      fun x y x' y' hr fx fy _ => ?_
    · obtain ⟨s₀, h, k, -⟩ := h
      exact h.sc.keep k (by ssep hF [sc1Chk])
    · show _ = _
      rw [fx, fy, hr.2.1]; simp only [zx, hr.2.2]

theorem expandA_tr :
    RelCT isa (RR p STK (fun σ s => SC1 p STK σ s ∧ s.gpr .s4 = 1) fun _ _ => True) (expandA P p)
      (RR p STK (IA p STK · (p.k * p.ℓ)) E24) := by
  unfold Impl.MlDsa.RISCV64.Sign.expandA
  refine RelCT.seq (stepRR (J := fun σ s => IA p STK σ 0 s) (F := fun _ s' => s'.gpr .s4 = 1) (E' := E24)
    (fun σ s _ h => rho_ok hF h.1 h.2)
    (RelCT.mono (srel1p (fun σ s h => h.1) (by taint_decide)) (fun _ _ h => h.1) fun _ _ h => h)
    fun x y x' y' _ fx fy _ => by show _ = _; rw [fx, fy]) ?_
  simpa using rr_seqR (R := fun e => RR p STK (IA p STK · e) E24) (p.k * p.ℓ) 0
    fun e _ he => sampleE_tr hP hF hS (by omega_using [he])

end

end VG.Proof.MlDsa.RISCV64.Sign
