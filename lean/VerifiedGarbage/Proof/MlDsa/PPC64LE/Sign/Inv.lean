module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Lay
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Piece
public import VerifiedGarbage.Proof.MlKem.PPC64LE.TopSave
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Lay
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Piece
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.TopSave
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# ML-DSA signing on PPC64LE: what holds throughout, and the prologue

As key generation's and verification's (`KeyGen/Inv.lean`, `Verify/Inv.lean`):
what holds of the state throughout, from the entry state: the layout, the
permissions and stack pointer of the entry state, our caller's registers
saved in `scratch` (ML-KEM's `TopSaved`), the callee-saved registers we do
not save as they were, and the inputs; until the hash of `ρ″` with `rnd` in
buffer 4 and `sig` stored at `SIG` (`SC1`), and then with `sig` in buffer 4
(`SC2`, from `SC1` by loading `sig` into `r28`, `toSC2`). Which writes keep
them (`sc1Chk`, `sc2Chk`); the pieces of signing (`SPiece`); and the
prologue (`spro_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sign

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece disjW disjW' reg)
open VG.Impl.MlDsa.PPC64LE.Sign
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.Sha3.PPC64LE.Stream (mov)

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
      Spec.MlDsa.signLeak p (skOf p σ₂) (muOf σ₂) (rndOf σ₂)

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

theorem saveR_slay1 (p : Params) (STK : Nat) (σ : State) : saveR (sScr σ) = (slay1 p STK σ).R 0 840 72 := rfl
theorem saveR_slay2 (p : Params) (STK : Nat) (σ : State) : saveR (sScr σ) = (slay2 p STK σ).R 0 840 72 := rfl

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

/-- A part that writes the regions `W` before the hash of `ρ″` keeps `SC1`. -/
def sc1Chk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  sepAll [scrLen p, STK, p.skLen, 64, 32] (0, 840, 72) W && W.all (fun w => w.1 == 0 || w.1 == 1) &&
    sepAll [scrLen p, STK, p.skLen, 64, 32] (0, 912, 8) W &&
    sepAll [scrLen p, STK, p.skLen, 64, 32] (2, 0, p.skLen) W &&
    sepAll [scrLen p, STK, p.skLen, 64, 32] (3, 0, 64) W &&
    sepAll [scrLen p, STK, p.skLen, 64, 32] (4, 0, 32) W

/-- A part that writes the regions `W` after the hash of `ρ″` keeps `SC2`. -/
def sc2Chk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, 840, 72) W &&
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
  have hd : ∀ r ∈ (slay1 p STK σ).RL W, ((slay1 p STK σ).R 0 840 72).Disjoint r :=
    fun r hr => by
      obtain ⟨w, hw'', rfl⟩ := List.mem_map.mp hr
      exact disjW hL (List.all_eq_true.mp h0 w hw'') (.inl (by decide))
  have hd8 : ∀ r ∈ (slay1 p STK σ).RL W, ((slay1 p STK σ).R 0 912 8).Disjoint r :=
    fun r hr => by
      obtain ⟨w, hw'', rfl⟩ := List.mem_map.mp hr
      exact disjW hL (List.all_eq_true.mp h1 w hw'') (.inl (by decide))
  refine ⟨h.site.kept hk, hk.rd.trans h.rd, hk.wr.trans h.wr, hk.sp.trans h.sp,
    fun r hr hs => (hk.cs r hr).trans (h.pres r hr hs), h.sav.keep hk.frame (by rw [saveR_slay1 p STK σ]; exact hd),
    ?_, ?_, ?_, ?_⟩
  · rw [hk.frame.readW (r := (slay1 p STK σ).R 0 912 8) (Region.contains_self _ _) hd8 (by decide)]
    exact h.sig
  · rw [bytes_keepR hL hk.frame h2 hw' (sfit1 hL 2 (by decide))]; exact h.sk
  · rw [bytes_keepR hL hk.frame h3 hw' (by decide)]; exact h.mu
  · rw [bytes_keepR hL hk.frame h4 hw' (by decide)]; exact h.rnd

theorem SC2.keep {p : Params} {STK : Nat} {σ s s' : State} (h : SC2 p STK σ s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((slay2 p STK σ).RL W) s s') (hc : sc2Chk p STK W = true) : SC2 p STK σ s' := by
  simp only [sc2Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h0, hw⟩, h2⟩, h3⟩ := hc
  have hL := h.site.ok
  have hw' : ∀ w ∈ W, w.1 ∈ sWb2 := fun w hw'' => by
    have := List.all_eq_true.mp hw w hw''
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    simp only [sWb2, List.mem_cons, List.not_mem_nil, or_false]; omega_arith
  have hd : ∀ r ∈ (slay2 p STK σ).RL W, ((slay2 p STK σ).R 0 840 72).Disjoint r :=
    fun r hr => by
      obtain ⟨w, hw'', rfl⟩ := List.mem_map.mp hr
      exact disjW hL (List.all_eq_true.mp h0 w hw'') (.inl (by decide))
  refine ⟨h.site.kept hk, hk.rd.trans h.rd, hk.wr.trans h.wr, hk.sp.trans h.sp,
    fun r hr hs => (hk.cs r hr).trans (h.pres r hr hs), h.sav.keep hk.frame (by rw [saveR_slay2 p STK σ]; exact hd),
    ?_, ?_⟩
  · rw [bytes_keepR hL hk.frame h2 hw' (sfit2 hL 2 (by decide))]; exact h.sk
  · rw [bytes_keepR hL hk.frame h3 hw' (by decide)]; exact h.mu

theorem inputs_eq (p : Params) (STK : Nat) (σ : State) :
    bytesAt σ.mem ((slay1 p STK σ).A 2 0) p.skLen = skOf p σ ∧ bytesAt σ.mem ((slay1 p STK σ).A 3 0) 64 = muOf σ ∧
      bytesAt σ.mem ((slay1 p STK σ).A 4 0) 32 = rndOf σ := by
  simp only [Lay.A, BitVec.add_zero]; exact ⟨rfl, rfl, rfl⟩

/-! ## The prologue -/

theorem spro_ok {p : Params} (hF : SFacts p) {STK : Nat} (hSTK : 48 ≤ STK) {σ : State} (hp : SPre p STK σ) :
    WP isa (.block pro) σ fun s => SC1 p STK σ s ∧ s.gpr .r24 = 1 := by
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
  refine WP.mono (topSave_ok (.inr rfl) rfl fun o _ h₂ => wS (by omega_arith))
    fun s₁ ⟨sav, fr, g₁, lr₁, rd₁, wr₁, sp₁⟩ => ?_
  have g3 : s₁.gpr .r3 = sSk σ := g₁ _ (by decide)
  have g4 : s₁.gpr .r4 = sMu σ := g₁ _ (by decide)
  have g5 : s₁.gpr .r5 = sRnd σ := g₁ _ (by decide)
  have g6 : s₁.gpr .r6 = sSig σ := g₁ _ (by decide)
  have g7 : s₁.gpr .r7 = sScr σ := g₁ _ (by decide)
  have i912 : InRegions s₁.wr (sScr σ + BitVec.ofNat 64 oSIG) 8 := by rw [wr₁]; exact wS (by decide)
  have o912 : oSIG % 8 = 0 ∧ oSIG < 32768 := by decide
  have hmv : WP isa (.block [mov .r30 .r3, mov .r29 .r4, mov .r28 .r5, mov .r31 .r7, .store .d .r6 .r31 oSIG,
      .li .r24 1]) s₁ fun s =>
      s.gpr .r30 = sSk σ ∧ s.gpr .r29 = sMu σ ∧ s.gpr .r28 = sRnd σ ∧ s.gpr .r31 = sScr σ ∧
      s.gpr .r24 = 1 ∧ (∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₁.gpr r) ∧
      s.mem = s₁.mem.writeW (sScr σ + BitVec.ofNat 64 oSIG) (sSig σ) ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧
      s.sp = s₁.sp := by
    prun [g3, g4, g5, g6, g7, i912, o912, exec_std]
    and_intros
    all_goals first
      | exact trivial
      | rfl
      | (intro r hr hs
         simp only [savedTop, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
         obtain ⟨a24, a25, a26, a27, a28, a29, a30, a31⟩ := hs
         simp only [RegUpd.gpr_write, a24, a28, a29, a30, a31, ite_false])
  refine WP.mono hmv fun s ⟨g30, g29, g28, g31, g24, cs, m, rd, wr, sp⟩ => ?_
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
      refine disjW' (i := i) (o := 0) (l := l) (j := 0) (o' := 840) (l' := 72) hL ?_ (.inr (.inl (by decide)))
      subst hl
      rcases hi with rfl | rfl | rfl <;> ssep hF [slay1, Lay.size]
    · rw [List.mem_singleton] at hr; subst hr
      refine disjW' (i := i) (o := 0) (l := l) (j := 0) (o' := 912) (l' := 8) hL ?_ (.inr (.inl (by decide)))
      subst hl
      rcases hi with rfl | rfl | rfl <;> ssep hF [slay1, Lay.size]
  obtain ⟨ek, em, er⟩ := inputs_eq p STK σ
  refine ⟨⟨⟨hL, rfl, by decide, by decide, by rw [slay1_size0]; omega_arith, rfl, by rw [sp, sp₁]; rfl, hSTK,
    by rw [sp, sp₁]; exact hp.stk, g31, g30, g29, g28, fun i hi hi1 => ?_, fun i hi hi1 => ?_⟩,
    rd.trans rd₁, wr.trans wr₁, sp.trans sp₁,
    fun r hr hs => (cs r hr hs).trans (g₁ r (by rintro rfl; simp [preserved] at hr)),
    sav.keep fr8 (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact disjW' (i := 0) (o := 840) (l := 72) (j := 0) (o' := 912) (l' := 8) hL (by ssep hF [slay1, Lay.size])
        (.inl (by decide))), ?_, ?_, ?_, ?_⟩, g24⟩
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

theorem spro_piece {p : Params} (hF : SFacts p) {STK : Nat} (hSTK : 48 ≤ STK) :
    SPiece p STK (fun σ s => s = σ) (fun σ s => SC1 p STK σ s ∧ s.gpr .r24 = 1) (.block pro) :=
  ⟨fun σ s hp hs => by subst hs; exact spro_ok hF hSTK hp,
    Sample.taint_block [.r3, .r4, .r5, .r6, .r7] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
      subst h₁ h₂; exact pub.1)
      (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      obtain ⟨-, e3, e4, e5, e6, e7, -⟩ := pub
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [e3, e4, e5, e6, e7]) (by taint_decide)⟩

end VG.Proof.MlDsa.PPC64LE.Sign
