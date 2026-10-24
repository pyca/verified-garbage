module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.ExpA
import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Seeds
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.ExpA
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# ML-DSA signing on PPC64LE: `ρ″` and the private key

As on 32-bit ARM (`Proof/MlDsa/Arm/Sign/PhaseD.lean`), once `Â` is sampled
(`IM`): `rnd ‖ μ` to `W1`, `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`, and `sig` to
`r28`, which takes the layout from `slay1` to `slay2` (`SC1.toSC2`); then
`ŝ₁[r]`, `ŝ₂[i]` and `t̂₀[i]`, each the `NTT` of the `BitUnpack` of its piece
of `sk`, in their slots (`ID`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sign

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of taint4 hashLay
  hashLay_ptr hashS hashS_tr pieceS ix_ne1 shake31 polyIs_keepW bytes_keepW copyS)
open VG.Impl.MlDsa.PPC64LE.Sign
open VG.Impl.MlDsa.PPC64LE.KeyGen (seqR callAt)
open VG.Impl.MlKem.PPC64LE (copy hash)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign (s1F s2F t0F)
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- The slots of `ŝ₁`, `ŝ₂` and `t̂₀`. -/
abbrev s1Base : Nat := 5 + 2 * p.k + 2 * p.ℓ
abbrev s2Base : Nat := 5 + 2 * p.k + 3 * p.ℓ
abbrev t0Base : Nat := 5 + 3 * p.k + 3 * p.ℓ

/-- `ŝ₁[r]`, `ŝ₂[i]` and `t̂₀[i]` of the function entered in `σ`. -/
abbrev S1v (σ : State) (r : Nat) : Poly := s1F p (skOf p σ) r
abbrev S2v (σ : State) (i : Nat) : Poly := s2F p (skOf p σ) i
abbrev T0v (σ : State) (i : Nat) : Poly := t0F p (skOf p σ) i

/-- `ρ″ = H(K ‖ rnd ‖ μ, 64)`. -/
abbrev rppOf (σ : State) : List Byte := H (((skOf p σ).drop 32).take 32 ++ rndOf σ ++ muOf σ) 64

end

/-! ## The layouts -/

theorem sA0 (p : Params) (STK : Nat) (σ : State) (o : Nat) : (slay1 p STK σ).A 0 o = (slay2 p STK σ).A 0 o := rfl

/-- `sig` to `r28`: from `SC1` to `SC2`. -/
theorem SC1.toSC2 {p : Params} {STK : Nat} {σ s s' : State} (hp : SPre p STK σ) (h : SC1 p STK σ s)
    (g28 : s'.gpr .r28 = sSig σ) (go : ∀ r, r ≠ .r28 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : SC2 p STK σ s' := by
  have hs := h.site
  refine ⟨⟨slay2_ok hp, rfl, by decide, by decide, hs.sz0, hs.sz1, by rw [hsp]; exact hs.p1, hs.s48,
    by rw [hsp]; exact hs.spk, by rw [go _ (by decide)]; exact hs.r31, by rw [go _ (by decide)]; exact hs.r30,
    by rw [go _ (by decide)]; exact hs.r29, g28, fun i hi hi1 => ?_, fun i hi hi1 => ?_⟩,
    hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, fun r hr hs' => ?_, by rw [hm]; exact h.sav,
    by rw [hm]; exact h.sk, by rw [hm]; exact h.mu⟩
  · show _ ∈ s'.wr
    rw [hwr, h.wr, hp.wr]
    simp only [sWb2, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · simp [Lay.buf, slay2]
    · exact absurd rfl hi1
    · simp [Lay.buf, slay2]
  · show _ ∈ s'.rd ++ s'.wr
    rw [hrd, hwr, h.rd, h.wr, hp.rd, hp.wr]
    rcases (by omega : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;> simp [Lay.buf, slay2]
  · have : r ≠ .r28 := fun e => by subst e; simp [savedTop] at hs'
    rw [go r this]; exact h.pres r hr hs'

/-! ## `Â` -/

/-- `Â` sampled within `maxBounds`, in its slots. -/
structure IM (p : Params) (STK : Nat) (σ s : State) : Prop where
  sc : SC1 p STK σ s
  r24 : s.gpr .r24 = 1
  ok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (seedE p σ e)).isSome
  A : ∀ e < p.k * p.ℓ, PolyIs s.mem ((slay1 p STK σ).A 0 (oP (aBase p + e))) (aVal p σ e)

theorem IA.im {p : Params} {STK : Nat} {σ s : State} (h : IA p STK σ (p.k * p.ℓ) s) (h1 : s.gpr .r24 = 1) :
    IM p STK σ s := ⟨h.sc, h1, (h.ok h1).1, (h.ok h1).2⟩

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hF hS in
theorem IM.keep {σ s s' : State} (h : IM p STK σ s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((slay1 p STK σ).RL W) s s') (hc : sc1Chk p STK W = true)
    (hA : ∀ e < p.k * p.ℓ, sepAll (slay1 p STK σ).sizes (0, oP (aBase p + e), 1024) W = true)
    (h24 : s'.gpr .r24 = s.gpr .r24) : IM p STK σ s' :=
  ⟨h.sc.keep hk hc, h24.trans h.r24, h.ok,
    fun e he => polyIs_keepW h.sc.site.ok hk.frame (hA e he) (by decide) rfl (h.A e he)⟩

/-! ## `ρ″` -/

/-- The buffers of the sponge: `sk` and `scratch`. -/
abbrev Ksk : Nat → Bool := fun i => i == 2

omit hP hF hS in
theorem ksk : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → Ksk i = true → Ksk j = true → i ∈ sWb1 ∨ j ∈ sWb1 :=
  fun i _ j _ hij _ _ hi hj => by
    simp only [Ksk, beq_iff_eq] at hi hj; omega

omit hP hS in
theorem rppPieces {σ s : State} (hs : Site (slay1 p STK σ) sWb1 STK s) :
    (∀ pc ∈ ([⟨.r30, 32, 32⟩, ⟨.r31, oW1, 96⟩] : List Impl.MlKem.PPC64LE.Piece),
      PieceOk (hashLay (slay1 p STK σ) s Ksk) ix s false pc) ∧
    PieceOk (hashLay (slay1 p STK σ) s Ksk) ix s true (⟨.r31, oMS, 64⟩ : Impl.MlKem.PPC64LE.Piece) := by
  refine ⟨fun pc hpc => ?_, pieceS hs rfl (show oMS < 32768 by decide) (show 64 < 32768 by decide) (by decide)
    (by ssep hF [hashLay, Lay.size]) (.inl rfl) fun _ => show ix Reg.r31 ∈ sWb1 by decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl
  · exact pieceS hs rfl (show 32 < 32768 by decide) (show 32 < 32768 by decide) (by decide)
      (by
        have := hF.sk; have := hF.scr
        dsimp only [hashLay, Lay.size, Ksk, sepAll, sepB, tri, ix, kRegs]
        set_option linter.unusedSimpArgs false in
        simp (config := { decide := true }) only [sepB, slay1_sizes, List.getD_cons_zero, List.getD_cons_succ,
          List.length_cons, List.length_nil, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.or_eq_true,
          decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.and_true, Bool.true_and, true_and, and_true, true_or, or_true,
          Nat.zero_add, ite_true, ite_false]
        omega) (.inr rfl) fun h => absurd h (by decide)
  · exact pieceS hs rfl (show oW1 < 32768 by decide) (show 96 < 32768 by decide) (by decide)
      (by ssep hF [hashLay, Lay.size]) (.inl rfl) fun h => absurd h (by decide)

/-- `rnd` in `W1`. -/
structure IW1 (p : Params) (STK : Nat) (σ s : State) : Prop where
  im : IM p STK σ s
  w : bytesAt s.mem ((slay1 p STK σ).A 0 oW1) 32 = rndOf σ

/-- `rnd ‖ μ` in `W1`. -/
structure IW (p : Params) (STK : Nat) (σ s : State) : Prop where
  im : IM p STK σ s
  w : bytesAt s.mem ((slay1 p STK σ).A 0 oW1) 96 = rndOf σ ++ muOf σ

/-- `ρ″` at `MS`. -/
structure IR (p : Params) (STK : Nat) (σ s : State) : Prop where
  im : IM p STK σ s
  rpp : bytesAt s.mem ((slay1 p STK σ).A 0 oMS) 64 = rppOf p σ

omit hP hS in
theorem copy1_ok {σ s : State} (h : IM p STK σ s) : WP isa (copy .r28 0 .r31 oW1 32) s (IW1 p STK σ) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine WP.mono (copyS h.sc.site (sb := .r28) (so := 0) (db := .r31) (dO := oW1) (len := 32)
    ⟨sptr_ok rfl (by decide), rfl⟩ ⟨sptr_ok rfl (by decide), by ssep hF⟩ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by ssep hF)) fun s₁ ⟨k₁, b₁⟩ =>
      ⟨h.keep k₁ (by ssep hF [sc1Chk]) (fun e he => by ssep hF) (k₁.cs .r24 (by decide)), ?_⟩
  show bytesAt s₁.mem (lpa (slay1 p STK σ) (.r31, oW1)) 32 = _
  rw [b₁]; exact h.sc.rnd

omit hP hS in
theorem copy2_ok {σ s : State} (h : IW1 p STK σ s) : WP isa (copy .r29 0 .r31 (oW1 + 32) 64) s (IW p STK σ) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hL := h.im.sc.site.ok
  refine WP.mono (copyS h.im.sc.site (sb := .r29) (so := 0) (db := .r31) (dO := oW1 + 32) (len := 64)
    ⟨sptr_ok rfl (by decide), rfl⟩ ⟨sptr_ok rfl (by decide), by ssep hF⟩ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by ssep hF)) fun s₂ ⟨k₂, b₂⟩ =>
      ⟨h.im.keep k₂ (by ssep hF [sc1Chk]) (fun e he => by ssep hF) (k₂.cs .r24 (by decide)), ?_⟩
  have e₁ : bytesAt s₂.mem ((slay1 p STK σ).A 0 oW1) 32 = rndOf σ := by
    rw [bytes_keepW hL k₂.frame (i := 0) (o := oW1) (l := 32) (by ssep hF) (by decide) (by decide)]; exact h.w
  have e₂ : bytesAt s₂.mem ((slay1 p STK σ).A 0 (oW1 + 32)) 64 = muOf σ := by
    show bytesAt s₂.mem (lpa (slay1 p STK σ) (.r31, oW1 + 32)) 64 = _
    rw [b₂]; exact h.im.sc.mu
  rw [show (96 : Nat) = 32 + 64 from rfl, Proof.MlKem.bytesAt_add, e₁]
  refine congrArg _ ?_
  simp only [Lay.A, BitVec.add_assoc, ← BitVec.ofNat_add] at e₂ ⊢
  exact e₂

omit hP hS in
theorem rppHash_ok {σ s : State} (h : IW p STK σ s) :
    WP isa (hash 136 0x1f [⟨.r30, 32, 32⟩, ⟨.r31, oW1, 96⟩] [⟨.r31, oMS, 64⟩]) s (IR p STK σ) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hs := h.im.sc.site
  obtain ⟨hin, hq⟩ := rppPieces hF hs
  refine WP.mono (hashS hs ksk (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by simp) hin hq)
    fun s' ⟨k', o'⟩ => ⟨h.im.keep k' (by ssep hF [sc1Chk]) (fun e he => by ssep hF) (k'.cs .r24 (by decide)), ?_⟩
  have o₃ : bytesAt s'.mem ((slay1 p STK σ).A 0 oMS) 64 = _ := o'
  rw [o₃]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
    hashLay_ptr _ _ _ (ix_ne1 _)]
  have e1 : bytesAt s.mem ((slay1 p STK σ).ptr (ix Reg.r30) + BitVec.ofNat 64 32) 32 =
      ((skOf p σ).drop 32).take 32 := by
    have := hF.sk
    rw [← h.im.sc.sk, Proof.MlKem.bytesAt_slice _ _ (by omega)]
    simp only [Lay.A, BitVec.add_zero]; rfl
  have e2 : bytesAt s.mem ((slay1 p STK σ).ptr (ix Reg.r31) + BitVec.ofNat 64 oW1) 96 = rndOf σ ++ muOf σ := h.w
  rw [e1, e2, shake31, ← List.append_assoc]
  exact (Proof.MlKem.shake256_eq _ _).symm


/-! ## The private key -/

end

/-- `Â`, `ρ″`, and the first `a` polynomials of `ŝ₁`, `b` of `ŝ₂` and `c` of `t̂₀`. -/
structure ID (p : Params) (STK : Nat) (σ : State) (a b c : Nat) (s : State) : Prop where
  sc : SC2 p STK σ s
  r24 : s.gpr .r24 = 1
  ok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (seedE p σ e)).isSome
  A : ∀ e < p.k * p.ℓ, PolyIs s.mem ((slay2 p STK σ).A 0 (oP (aBase p + e))) (aVal p σ e)
  rpp : bytesAt s.mem ((slay2 p STK σ).A 0 oMS) 64 = rppOf p σ
  s1 : ∀ r < a, PolyIs s.mem ((slay2 p STK σ).A 0 (oP (s1Base p + r))) (S1v p σ r)
  s2 : ∀ i < b, PolyIs s.mem ((slay2 p STK σ).A 0 (oP (s2Base p + i))) (S2v p σ i)
  t0 : ∀ i < c, PolyIs s.mem ((slay2 p STK σ).A 0 (oP (t0Base p + i))) (T0v p σ i)

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hS in
theorem ldSig_ok {σ s : State} (hp : SPre p STK σ) (h : IR p STK σ s) :
    WP isa (.block [.load .d .r28 .r31 oSIG]) s (ID p STK σ 0 0 0) := by
  have hs := h.im.sc.site
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r31 + BitVec.ofNat 64 oSIG) 8 := by
    rw [hs.r31]
    exact hs.crE (q := sc oSIG) (l := 8) ⟨sptr_ok rfl (by decide), by ssep hF⟩ _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.cons (exec_load_d (by decide) (by decide) hin) (WP.block_nil ?_)
  have g : s.mem.readW (s.gpr .r31 + BitVec.ofNat 64 oSIG) 64 = sSig σ := by rw [hs.r31]; exact h.im.sc.sig
  rw [g]
  exact ⟨h.im.sc.toSC2 hp (RegUpd.gpr_write_self ..) (fun r hr => RegUpd.gpr_write_of_ne _ _ hr) rfl rfl rfl rfl,
    by rw [RegUpd.gpr_write_of_ne _ _ (by decide)]; exact h.im.r24, h.im.ok, fun e he => h.im.A e he, h.rpp,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩

omit hP hS in
theorem rhoPP_piece : SPiece p STK (IM p STK) (ID p STK · 0 0 0) rhoPP := by
  unfold rhoPP
  refine Piece.seq ⟨fun σ s _ h => copy1_ok hF h, srel1p (fun σ s h => h.sc) (by taint_decide)⟩
    (Piece.seq ⟨fun σ s _ h => copy2_ok hF h, srel1p (fun σ s h => h.im.sc) (by taint_decide)⟩
    (Piece.seq ⟨fun σ s _ h => rppHash_ok hF h, ?_⟩
      ⟨fun σ s hp h => ldSig_ok hF hp h, srel1p (fun σ s h => h.im.sc) (by taint_decide)⟩))
  exact rel_of (RelCT.exists_ fun σ => hashS_tr ksk (rate := 136) (sfx := 0x1f) (by decide) (by decide)
    (by simp) (fun s hs => (rppPieces hF (σ := σ) hs).1) (fun s hs => (rppPieces hF hs).2) fun _ _ h => h)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc1_twoL pub h₁.im.sc h₂.im.sc⟩

omit hP hS in
/-- A part that writes slot `j` (not one of the polynomials done), `PS` and
the stack keeps `ID`. -/
theorem id_keep {σ s s' : State} {a b c j : Nat} (h : ID p STK σ a b c s)
    (hk : Kept ((slay2 p STK σ).RL [tri (pS j) 1024, tri (sc oPS) 1024, (1, 0, STK)]) s s')
    (h24 : s'.gpr .r24 = s.gpr .r24) (hj : s1Base p ≤ j ∧ j < aBase p) (ha : a ≤ p.ℓ) (hb : b ≤ p.k) (hc : c ≤ p.k)
    (h1 : ∀ r < a, s1Base p + r ≠ j) (h2 : ∀ i < b, s2Base p + i ≠ j) (h3 : ∀ i < c, t0Base p + i ≠ j) :
    ID p STK σ a b c s' := by
  have hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  have hL := h.sc.site.ok
  dsimp only [s1Base, s2Base, t0Base, aBase] at hj h1 h2 h3
  obtain ⟨hj1, hj2⟩ := hj
  refine ⟨h.sc.keep hk (by ssep hF [sc2Chk]), h24.trans h.r24, h.ok,
    fun e he => polyIs_keepW hL hk.frame (by ssep hF) (by decide) rfl (h.A e he),
    by rw [bytes_keepW hL hk.frame (i := 0) (o := oMS) (l := 64) (by ssep hF) (by decide) (by decide)]; exact h.rpp,
    fun r hr => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · have := h1 r hr
    exact polyIs_keepW hL hk.frame (by ssep hF [s1Base]) (by decide) rfl (h.s1 r hr)
  · have := h2 i hi
    exact polyIs_keepW hL hk.frame (by ssep hF [s2Base]) (by decide) rfl (h.s2 i hi)
  · have := h3 i hi
    exact polyIs_keepW hL hk.frame (by ssep hF [t0Base]) (by decide) rfl (h.t0 i hi)

omit hP hF hS in
theorem sk_slice2 {σ s : State} (h : SC2 p STK σ s) {o l : Nat} (hl : o + l ≤ p.skLen) :
    bytesAt s.mem ((slay2 p STK σ).A 2 o) l = ((skOf p σ).drop o).take l := by
  have e := h.sk
  simp only [Lay.A, BitVec.add_zero] at e ⊢
  rw [← e, Proof.MlKem.bytesAt_slice _ _ hl]

section
variable {a b c j o len x y : Nat} (hj : s1Base p ≤ j ∧ j < aBase p) (ha : a ≤ p.ℓ) (hb : b ≤ p.k) (hc : c ≤ p.k)
  (h1 : ∀ r < a, s1Base p + r ≠ j) (h2 : ∀ i < b, s2Base p + i ≠ j) (h3 : ∀ i < c, t0Base p + i ≠ j)

/-- The `BitUnpack` of `len` bytes of `sk` at `o` in slot `j`. -/
abbrev DU (p : Params) (STK : Nat) (a b c j o len x y : Nat) (σ s : State) : Prop :=
  ID p STK σ a b c s ∧
    PolyIs s.mem ((slay2 p STK σ).A 0 (oP j)) (toRq (bitUnpack (((skOf p σ).drop o).take len) x y))

include hj ha hb hc h1 h2 h3

omit hP hS ha hb hc h1 h2 h3 in
theorem du_m {σ : State} (hxy : (x, y) ∈ bitPackParams) (hlen : len = 32 * bitlen (x + y))
    (ho : o + len ≤ p.skLen) (hlt : 0 < len ∧ len < 2 ^ 31 ∧ x < 2 ^ 31 ∧ y < 2 ^ 31) :
    KeyGen.BuOk (slay2 p STK σ) sWb2 (.r30, o) len x y (pS j) := by
  have hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  have := hF.lens
  have hj' := hj
  dsimp only [s1Base, aBase] at hj'
  obtain ⟨hj1, hj2⟩ := hj'
  exact ⟨⟨sptr_ok rfl (by omega), by ssep hF⟩, ⟨sptr_ok rfl (by slt hF), by ssep hF⟩,
    show ix Reg.r31 ∈ sWb2 by decide, by ssep hF, hxy, hlen, hlt⟩

omit hP hS ha hb hc h1 h2 h3 in
theorem nt_m {σ : State} : KeyGen.IpOk (slay2 p STK σ) sWb2 (pS j) (sc oPS) := by
  have hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  have hj' := hj
  dsimp only [s1Base, aBase] at hj'
  obtain ⟨hj1, hj2⟩ := hj'
  exact ⟨⟨sptr_ok rfl (by slt hF), by ssep hF⟩, ⟨sptr_ok rfl (by decide), by ssep hF⟩,
    show ix Reg.r31 ∈ sWb2 by decide, show ix Reg.r31 ∈ sWb2 by decide, by ssep hF⟩

theorem du_piece (hxy : (x, y) ∈ bitPackParams) (hlen : len = 32 * bitlen (x + y))
    (ho : o + len ≤ p.skLen) (hlt : 0 < len ∧ len < 2 ^ 31 ∧ x < 2 ^ 31 ∧ y < 2 ^ 31) :
    SPiece p STK (ID p STK · a b c) (DU p STK a b c j o len x y) (bitUnpackAt P (.r30, o) len x y (pS j)) := by
  refine ⟨fun σ s _ h => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.bu_tr hP.bitUnpack hS
    (du_m hF hj (σ := σ) hxy hlen ho hlt) fun _ _ h => ⟨h.1, h.2.1, h.2.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub h₁.sc h₂.sc⟩⟩
  unfold bitUnpackAt
  refine KeyGen.bu_ok hP.bitUnpack h.sc.site hS (du_m hF hj hxy hlen ho hlt) fun s₁ k₁ hb₁ =>
    ⟨id_keep hF h (k₁.monoL (by simp)) (k₁.cs .r24 (by decide)) hj ha hb hc h1 h2 h3, ?_⟩
  have e : bytesAt s.mem (lpa (slay2 p STK σ) (.r30, o)) len = ((skOf p σ).drop o).take len := sk_slice2 h.sc ho
  rw [← e]; exact hb₁

theorem nt_piece :
    SPiece p STK (DU p STK a b c j o len x y)
      (fun σ s => ID p STK σ a b c s ∧
        PolyIs s.mem ((slay2 p STK σ).A 0 (oP j)) (ntt (toRq (bitUnpack (((skOf p σ).drop o).take len) x y))))
      (nttAt P (pS j)) := by
  refine ⟨fun σ s _ h => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.ip_tr (t := ntt) hP.ntt hS
    (nt_m hF hj (σ := σ)) (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧
      Reduced x.mem ((slay2 p STK σ).A 0 (oP j)) ∧ Reduced y.mem ((slay2 p STK σ).A 0 (oP j)))
      fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub h₁.1.sc h₂.1.sc, h₁.2.1, by rw [slay2_pub pub]; exact h₂.2.1⟩⟩
  unfold nttAt
  refine KeyGen.ip_ok (t := ntt) hP.ntt h.1.sc.site hS (nt_m hF hj) h.2.1 fun s₂ k₂ hb₂ =>
    ⟨id_keep hF h.1 k₂ (k₂.cs .r24 (by decide)) hj ha hb hc h1 h2 h3, ?_⟩
  show PolyIs s₂.mem (lpa (slay2 p STK σ) (pS j)) _
  rw [← h.2.2]
  exact hb₂

end

omit hP hS in
theorem eta_facts : (p.η, p.η) ∈ bitPackParams ∧ sLen p = 32 * bitlen (p.η + p.η) ∧
    0 < sLen p ∧ sLen p < 2 ^ 31 ∧ p.η < 2 ^ 31 := by
  refine ⟨?_, by rw [← Nat.two_mul], ?_⟩
  · rcases hF.eta with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  · rcases hF.eta with ⟨e, l⟩ | ⟨e, l⟩ <;> rw [l, e] <;> decide

theorem decS1_piece {r : Nat} (hr : r < p.ℓ) :
    SPiece p STK (ID p STK · r 0 0) (ID p STK · (r + 1) 0 0) (decS1 P p r) := by
  have hk' := hF.k; have hl := hF.l
  obtain ⟨hxy, hlen, hlt⟩ := eta_facts hF
  have ho : skS1 p r + sLen p ≤ p.skLen := by
    have hsk := hF.sk
    have hm : sLen p * (r + 1) ≤ sLen p * (p.ℓ + p.k) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_add, Nat.mul_one] at hm
    show 128 + sLen p * r + sLen p ≤ p.skLen
    omega
  have hj : s1Base p ≤ s1Base p + r ∧ s1Base p + r < aBase p := ⟨by omega, by simp only [s1Base, aBase]; omega⟩
  refine Piece.mono ((du_piece hP hF hS hj (Nat.le_of_lt hr) (Nat.zero_le _) (Nat.zero_le _) (fun _ _ => by omega)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _)) hxy hlen ho
    ⟨hlt.1, hlt.2.1, hlt.2.2, hlt.2.2⟩).seq (nt_piece hP hF hS hj (Nat.le_of_lt hr) (Nat.zero_le _) (Nat.zero_le _)
      (fun _ _ => by omega) (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))))
    (fun _ _ _ h => h) fun σ s _ ⟨I, hq⟩ => ⟨I.sc, I.r24, I.ok, I.A, I.rpp, fun r' hr' => ?_, I.s2, I.t0⟩
  rcases (by omega : r' < r ∨ r' = r) with h' | rfl
  exacts [I.s1 r' h', hq]

end

end VG.Proof.MlDsa.PPC64LE.Sign
