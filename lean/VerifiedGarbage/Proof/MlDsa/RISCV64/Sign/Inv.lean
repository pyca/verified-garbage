module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.Lay
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
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.Lay
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Piece
meta import VerifiedGarbage.Proof.MlKem.RISCV64.TopSave
meta import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

public import VerifiedGarbage.TCB.RISCV64.Target
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
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [oSIG]; omega
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
