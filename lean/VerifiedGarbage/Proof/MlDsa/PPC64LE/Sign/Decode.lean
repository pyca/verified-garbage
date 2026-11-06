module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.ExpA
import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Seeds
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Copy
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.ExpA
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
meta import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Copy
meta import VerifiedGarbage.Proof.MlDsa.Verify.Mem
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA signing on PPC64LE: `ρ″` and the private key

As on 32-bit ARM (`Proof/MlDsa/Arm/Sign/PhaseD.lean`), once `Â` is sampled
(`IM`): `rnd ‖ μ` to `W1`, `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`, and `sig` to
`r28`, which takes the layout from `slay1` to `slay2` (`SC1.toSC2`); then
`ŝ₁[r]`, `ŝ₂[i]` and `t̂₀[i]`, each the `NTT` of the `BitUnpack` of its piece
of `sk`, in their slots (`ID`, `keys_piece`).

In a kernel (`withCache`), with the precondition `CPre` (`SCache`: `r15`
bytes at `r14` are none or the polynomials of `sk`, in a region to read apart
from the buffers written and the stack) and the public data `cPub` (with the
cache's pointer and length): if `r15 ≠ 0`, the polynomials are copied from
the cache instead (`cp_piece`), which memory outside the buffers written and
the stack still holds (`FC`, by `Exec.frameAny`: `cache_poly`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sign

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of taint4 hashLay
  hashLay_ptr hashS hashS_tr pieceS ix_ne1 shake31 polyIs_keepW bytes_keepW copyS reg relInv)
open VG.Impl.MlDsa.PPC64LE.Sign
open VG.Impl.MlDsa.PPC64LE.KeyGen (seqR callAt)
open VG.Impl.MlKem.PPC64LE (copy hash)
open VG.Impl.MlDsa.PPC64LE (copyW)
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
    obtain ⟨X, hX⟩ := hp.rd
    rw [hrd, hwr, h.rd, h.wr, hX, hp.wr]
    rcases (by omega_arith : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;> simp [Lay.buf, slay2]
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
    simp only [Ksk, beq_iff_eq] at hi hj; omega_arith

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
        omega_arith) (.inr rfl) fun h => absurd h (by decide)
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
    rw [← h.im.sc.sk, Proof.MlKem.bytesAt_slice _ _ (by omega_arith)]
    simp only [Lay.A, BitVec.add_zero]; rfl
  have e2 : bytesAt s.mem ((slay1 p STK σ).ptr (ix Reg.r31) + BitVec.ofNat 64 oW1) 96 = rndOf σ ++ muOf σ := h.w
  rw [e1, e2, shake31, ← List.append_assoc]
  exact (Proof.MlKem.shake256_eq _ _).symm


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
  exact ⟨⟨sptr_ok rfl (by omega_arith), by ssep hF⟩, ⟨sptr_ok rfl (by slt hF), by ssep hF⟩,
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
    have hm : sLen p * (r + 1) ≤ sLen p * (p.ℓ + p.k) := Nat.mul_le_mul_left _ (by omega_arith)
    rw [Nat.mul_add, Nat.mul_one] at hm
    show 128 + sLen p * r + sLen p ≤ p.skLen
    omega_arith
  have hj : s1Base p ≤ s1Base p + r ∧ s1Base p + r < aBase p := ⟨by omega_arith, by simp only [s1Base, aBase]; omega_arith⟩
  refine Piece.mono ((du_piece hP hF hS hj (Nat.le_of_lt hr) (Nat.zero_le _) (Nat.zero_le _) (fun _ _ => by omega_arith)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _)) hxy hlen ho
    ⟨hlt.1, hlt.2.1, hlt.2.2, hlt.2.2⟩).seq (nt_piece hP hF hS hj (Nat.le_of_lt hr) (Nat.zero_le _) (Nat.zero_le _)
      (fun _ _ => by omega_arith) (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))))
    (fun _ _ _ h => h) fun σ s _ ⟨I, hq⟩ => ⟨I.sc, I.r24, I.ok, I.A, I.rpp, fun r' hr' => ?_, I.s2, I.t0⟩
  rcases (by omega_arith : r' < r ∨ r' = r) with h' | rfl
  exacts [I.s1 r' h', hq]


theorem decS2_piece {i : Nat} (hi : i < p.k) :
    SPiece p STK (ID p STK · p.ℓ i 0) (ID p STK · p.ℓ (i + 1) 0) (decS2 P p i) := by
  have hk' := hF.k; have hl := hF.l
  obtain ⟨hxy, hlen, hlt⟩ := eta_facts hF
  have ho : skS2 p i + sLen p ≤ p.skLen := by
    have hsk := hF.sk
    have hm : sLen p * (i + 1) ≤ sLen p * p.k := Nat.mul_le_mul_left _ (by omega_arith)
    rw [Nat.mul_add, Nat.mul_one] at hm
    rw [Nat.mul_add] at hsk
    show 128 + sLen p * p.ℓ + sLen p * i + sLen p ≤ p.skLen
    omega_arith
  have hj : s1Base p ≤ s2Base p + i ∧ s2Base p + i < aBase p :=
    ⟨by simp only [s1Base, s2Base]; omega_arith, by simp only [s2Base, aBase]; omega_arith⟩
  have h1 : ∀ r < p.ℓ, s1Base p + r ≠ s2Base p + i := fun r hr => by simp only [s1Base, s2Base]; omega_arith
  have h2 : ∀ i' < i, s2Base p + i' ≠ s2Base p + i := fun i' hi' => by omega_arith
  refine Piece.mono ((du_piece hP hF hS hj (Nat.le_refl _) (Nat.le_of_lt hi) (Nat.zero_le _) h1 h2
    (fun _ h => absurd h (Nat.not_lt_zero _)) hxy hlen ho ⟨hlt.1, hlt.2.1, hlt.2.2, hlt.2.2⟩).seq
    (nt_piece hP hF hS hj (Nat.le_refl _) (Nat.le_of_lt hi) (Nat.zero_le _) h1 h2
      (fun _ h => absurd h (Nat.not_lt_zero _))))
    (fun _ _ _ h => h) fun σ s _ ⟨I, hq⟩ => ⟨I.sc, I.r24, I.ok, I.A, I.rpp, I.s1, fun i' hi' => ?_, I.t0⟩
  rcases (by omega_arith : i' < i ∨ i' = i) with h' | rfl
  exacts [I.s2 i' h', hq]

theorem decT0_piece {i : Nat} (hi : i < p.k) :
    SPiece p STK (ID p STK · p.ℓ p.k i) (ID p STK · p.ℓ p.k (i + 1)) (decT0 P p i) := by
  have hk' := hF.k; have hl := hF.l
  have ho : skT0 p i + 416 ≤ p.skLen := by
    have hsk := hF.sk
    show 128 + sLen p * (p.ℓ + p.k) + 416 * i + 416 ≤ p.skLen
    omega_arith
  have hj : s1Base p ≤ t0Base p + i ∧ t0Base p + i < aBase p :=
    ⟨by simp only [s1Base, t0Base]; omega_arith, by simp only [t0Base, aBase]; omega_arith⟩
  have h1 : ∀ r < p.ℓ, s1Base p + r ≠ t0Base p + i := fun r hr => by simp only [s1Base, t0Base]; omega_arith
  have h2 : ∀ i' < p.k, s2Base p + i' ≠ t0Base p + i := fun i' hi' => by simp only [s2Base, t0Base]; omega_arith
  have h3 : ∀ i' < i, t0Base p + i' ≠ t0Base p + i := fun i' hi' => by omega_arith
  refine Piece.mono ((du_piece hP hF hS hj (Nat.le_refl _) (Nat.le_refl _) (Nat.le_of_lt hi) h1 h2 h3
    (x := 4095) (y := 4096) (by decide) (by decide) ho (by decide)).seq
    (nt_piece hP hF hS hj (Nat.le_refl _) (Nat.le_refl _) (Nat.le_of_lt hi) h1 h2 h3))
    (fun _ _ _ h => h) fun σ s _ ⟨I, hq⟩ => ⟨I.sc, I.r24, I.ok, I.A, I.rpp, I.s1, I.s2, fun i' hi' => ?_⟩
  rcases (by omega_arith : i' < i ∨ i' = i) with h' | rfl
  · exact I.t0 i' h'
  · have e : skT0 p i' = 128 + Proof.MlDsa.Sign.lenS p * p.ℓ + Proof.MlDsa.Sign.lenS p * p.k + 32 * d * i' := by
      show 128 + sLen p * (p.ℓ + p.k) + 416 * i' = _
      rw [Nat.mul_add, ← Nat.add_assoc]; rfl
    rw [e] at hq
    exact hq

/-- `ŝ₁`, `ŝ₂` and `t̂₀`, decoded from `sk`. -/
theorem keys_piece : SPiece p STK (ID p STK · 0 0 0) (ID p STK · p.ℓ p.k p.k) (keys P p) := by
  unfold keys
  exact (Piece.mono (Piece.seqR (I := fun r σ s => ID p STK σ r 0 0 s) p.ℓ 0
    fun r _ hr => decS1_piece hP hF hS (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h).seq
    ((Piece.mono (Piece.seqR (I := fun i σ s => ID p STK σ p.ℓ i 0 s) p.k 0
      fun i _ hi => decS2_piece hP hF hS (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h).seq
      (Piece.mono (Piece.seqR (I := fun i σ s => ID p STK σ p.ℓ p.k i s) p.k 0
        fun i _ hi => decT0_piece hP hF hS (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h))

end

/-! ## A kernel's cache -/

/-- What a kernel's entry state holds of its cache, the `r15` bytes at `r14`:
nothing, or the `ℓ + 2k` polynomials of `sk`; a region it may read, apart
from the buffers it writes and the stack. -/
structure SCache (p : Params) (STK : Nat) (σ : State) : Prop where
  polys : σ.gpr .r15 = 0 ∨ ((σ.gpr .r15).toNat = 4 * n * (p.ℓ + 2 * p.k) ∧
    Proof.MlDsa.CachedSecretPolys p σ.mem (σ.gpr .r14) (skOf p σ))
  rd : reg (σ.gpr .r14) (σ.gpr .r15).toNat ∈ σ.rd
  d_g : (reg (σ.gpr .r14) (σ.gpr .r15).toNat).Disjoint (reg (sSig σ) p.sigLen)
  d_c : (reg (σ.gpr .r14) (σ.gpr .r15).toNat).Disjoint (reg (sScr σ) (scrLen p))
  b : (reg (σ.gpr .r14) (σ.gpr .r15).toNat).Disjoint (below σ.sp STK)

/-- The precondition of a kernel's signing. -/
abbrev CPre (p : Params) (STK : Nat) (σ : State) : Prop := SPre p STK σ ∧ SCache p STK σ

/-- Its public data: `signContract`'s, and the cache's pointer and length. -/
def cPub (p : Params) (σ₁ σ₂ : State) : Prop :=
  sPub p σ₁ σ₂ ∧ σ₁.gpr .r14 = σ₂.gpr .r14 ∧ σ₁.gpr .r15 = σ₂.gpr .r15

/-- The pieces of a kernel's signing. -/
abbrev CPiece (p : Params) (STK : Nat) := Piece (CPre p STK) (cPub p)

theorem SPiece.cache {p : Params} {STK : Nat} {I J : State → State → Prop} {c : Prog isa}
    (h : SPiece p STK I J c) : CPiece p STK I J c :=
  ⟨fun σ s hp hs => h.ok σ s hp.1 hs, RelCT.mono h.tr (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ =>
    ⟨σ₁, σ₂, p₁.1, p₂.1, pub.1, i₁, i₂⟩) fun _ _ h => h⟩

/-- Memory but the buffers written and the stack is as on entry. -/
abbrev FC (STK : Nat) (σ s : State) : Prop := Frame (σ.wr ++ [below σ.sp STK]) σ.mem s.mem

/-- A run of code, with what it changes in memory. -/
theorem wp_frame {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) (hd : sdepth c < 2 ^ 64) :
    WP isa c s fun s' => Q s' ∧ Frame (s.wr ++ [below s.sp (sdepth c)]) s.mem s'.mem := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.frameAny he hd⟩

/-- `FC` after code that changes memory only in the buffers written and its
stack. -/
theorem FC.step {STK : Nat} {σ s s' : State} (h : FC STK σ s) (hw : s.wr = σ.wr) (hsp : s.sp = σ.sp) {d : Nat}
    (hd : d ≤ STK) (hS : STK < 2 ^ 64) (hf : Frame (s.wr ++ [below s.sp d]) s.mem s'.mem) : FC STK σ s' :=
  Frame.trans h (hf.sub fun r hr => by
    rw [hw, hsp] at hr
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub hd hS⟩)

/-- Polynomial `i` of the cache, in memory with `FC`. -/
theorem cache_poly {p : Params} {STK : Nat} {σ s : State} (hp : SPre p STK σ) (hc : SCache p STK σ)
    (fc : FC STK σ s) (hne : σ.gpr .r15 ≠ 0) {i : Nat} (hi : i < p.ℓ + 2 * p.k) :
    PolyIs s.mem (σ.gpr .r14 + BitVec.ofNat 64 (1024 * i)) (preparedSecretPolys p (skOf p σ))[i]! := by
  obtain ⟨hl, hpoly⟩ := hc.polys.resolve_left hne
  have hsub : Region.Sub (Proof.MlDsa.Verify.polyRegion (σ.gpr .r14 + BitVec.ofNat 64 (1024 * i)))
      (reg (σ.gpr .r14) (σ.gpr .r15).toNat) :=
    Offset.sub_base _ (by rw [hl]; show 1024 * i + 1024 ≤ 4 * 256 * (p.ℓ + 2 * p.k); omega)
  refine Proof.MlDsa.Verify.polyIs_frame fc (fun r hr => ?_) ?_
  · rw [hp.wr] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hc.d_g.sub_left hsub
    · exact hc.d_c.sub_left hsub
    · exact hc.b.sub_left hsub
  · have := hpoly i hi
    rwa [show 4 * n * i = 1024 * i by show 4 * 256 * i = 1024 * i; omega] at this

section
variable {p : Params} (hF : SFacts p) {STK : Nat}
include hF

/-- Polynomial `i` of the cache copied to slot `j`. -/
theorem cp_piece {a b c j i : Nat} (hj : s1Base p ≤ j ∧ j < aBase p) (ha : a ≤ p.ℓ) (hb : b ≤ p.k) (hc : c ≤ p.k)
    (h1 : ∀ r < a, s1Base p + r ≠ j) (h2 : ∀ i < b, s2Base p + i ≠ j) (h3 : ∀ i < c, t0Base p + i ≠ j)
    (hi : i < p.ℓ + 2 * p.k) :
    CPiece p STK (fun σ s => (ID p STK σ a b c s ∧ FC STK σ s) ∧ σ.gpr .r15 ≠ 0)
      (fun σ s => ((ID p STK σ a b c s ∧ FC STK σ s) ∧ σ.gpr .r15 ≠ 0) ∧
        PolyIs s.mem ((slay2 p STK σ).A 0 (oP j)) (preparedSecretPolys p (skOf p σ))[i]!)
      (copyW (.r14, 1024 * i) (pS j) 128) := by
  have hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  have hscr := hF.scr
  have hj' := hj
  dsimp only [s1Base, aBase] at hj'
  have hoj : oP j + 1024 ≤ scrLen p := by simp only [oP]; omega_arith
  refine ⟨fun σ s hp ⟨⟨h, fc⟩, hne⟩ => ?_, ?_⟩
  · have hs := h.sc.site
    have g14 : s.gpr .r14 = σ.gpr .r14 := h.sc.pres .r14 (by decide) (by decide)
    have g31 : s.gpr .r31 = sScr σ := hs.r31
    obtain ⟨hlen, -⟩ := hp.2.polys.resolve_left hne
    have hsub : Region.Sub ⟨σ.gpr .r14 + BitVec.ofNat 64 (1024 * i), 8 * 128⟩
        (reg (σ.gpr .r14) (σ.gpr .r15).toNat) :=
      Offset.sub_base _ (by rw [hlen]; show 1024 * i + 1024 ≤ 4 * 256 * (p.ℓ + 2 * p.k); omega)
    have dsub : Region.Sub ⟨sScr σ + BitVec.ofNat 64 (oP j), 8 * 128⟩ (reg (sScr σ) (scrLen p)) :=
      Offset.sub_base _ (by show oP j + 1024 ≤ scrLen p; exact hoj)
    have cr : PPC64LE.Covers [⟨s.gpr .r14 + BitVec.ofNat 64 (1024 * i), 8 * 128⟩] (s.rd ++ s.wr) := by
      rw [g14, h.sc.rd]
      exact Covers.of_sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_append_left _ hp.2.rd, 1024 * i, rfl,
          by rw [hlen]; show 1024 * i + 1024 ≤ 4 * 256 * (p.ℓ + 2 * p.k); omega⟩
    have cw : PPC64LE.Covers [⟨s.gpr .r31 + BitVec.ofNat 64 (oP j), 8 * 128⟩] s.wr := by
      rw [g31, h.sc.wr, hp.1.wr]
      exact Covers.of_sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), oP j, rfl, hoj⟩
    have hd : (⟨s.gpr .r14 + BitVec.ofNat 64 (1024 * i), 8 * 128⟩ : Region).Disjoint
        ⟨s.gpr .r31 + BitVec.ofNat 64 (oP j), 8 * 128⟩ := by
      rw [g14, g31]; exact (hp.2.d_c.sub_left hsub).sub_right dsub
    refine WP.mono (copyW_ok (sb := .r14) (db := .r31) (by decide) (by decide)
      (by omega_arith) (by simp only [oP]; omega_arith) (by decide) (by decide) cr cw hd) fun s' ⟨k, hbt⟩ => ?_
    rw [g31] at k hbt
    rw [g14] at hbt
    have k' : Kept ((slay2 p STK σ).RL [tri (pS j) 1024, tri (sc oPS) 1024, (1, 0, STK)]) s s' :=
      k.mono fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact List.mem_cons_self ..
    refine ⟨⟨⟨id_keep hF h k' (k.cs .r24 (by decide)) hj ha hb hc h1 h2 h3, ?_⟩, hne⟩, ?_⟩
    · refine FC.step fc (h.sc.wr) (h.sc.sp) (Nat.zero_le STK) (by have := hs.spk; have := σ.sp.isLt; omega_arith)
        (k.frame.sub fun r hr => ?_)
      rw [List.mem_singleton] at hr; subst hr
      rw [h.sc.wr, hp.1.wr]
      exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), dsub⟩
    · exact Proof.MlDsa.PreparedKey.polyIs_of_copy hbt (cache_poly hp.1 hp.2 fc hne hi)
  · refine rel_of (copyW_tr (by decide) (by decide) (by decide) (by omega_arith) (by simp only [oP]; omega_arith)
      (by decide) (P := fun x y => x.sp = y.sp ∧ x.gpr .r14 = y.gpr .r14 ∧ x.gpr .r31 = y.gpr .r31) fun _ _ h => h)
      fun σ₁ σ₂ x y p₁ p₂ pub ⟨⟨h₁, _⟩, _⟩ ⟨⟨h₂, _⟩, _⟩ => ⟨?_, ?_, ?_⟩
    · rw [h₁.sc.sp, h₂.sc.sp, pub.1.1]
    · rw [h₁.sc.pres .r14 (by decide) (by decide), h₂.sc.pres .r14 (by decide) (by decide), pub.2.1]
    · rw [h₁.sc.site.r31, h₂.sc.site.r31]; exact pub.1.2.2.2.2.2.1

/-- `ŝ₁`, `ŝ₂` and `t̂₀`, copied from the cache. -/
theorem cached_piece :
    CPiece p STK (fun σ s => (ID p STK σ 0 0 0 s ∧ FC STK σ s) ∧ σ.gpr .r15 ≠ 0)
      (fun σ s => (ID p STK σ p.ℓ p.k p.k s ∧ FC STK σ s) ∧ σ.gpr .r15 ≠ 0) (cached p) := by
  have hk' := hF.k; have hl := hF.l
  unfold cached
  refine (Piece.mono (Piece.seqR (I := fun r σ s => (ID p STK σ r 0 0 s ∧ FC STK σ s) ∧ σ.gpr .r15 ≠ 0) p.ℓ 0
    fun r _ hr => ?_) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h).seq
    ((Piece.mono (Piece.seqR (I := fun i σ s => (ID p STK σ p.ℓ i 0 s ∧ FC STK σ s) ∧ σ.gpr .r15 ≠ 0) p.k 0
      fun i _ hi => ?_) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h).seq
      (Piece.mono (Piece.seqR (I := fun i σ s => (ID p STK σ p.ℓ p.k i s ∧ FC STK σ s) ∧ σ.gpr .r15 ≠ 0) p.k 0
        fun i _ hi => ?_) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h))
  · rw [Nat.zero_add] at hr
    refine Piece.mono (cp_piece hF (j := s1Base p + r) (i := r) ⟨by omega_arith, by simp only [s1Base, aBase]; omega_arith⟩
      (Nat.le_of_lt hr) (Nat.zero_le _) (Nat.zero_le _) (fun _ _ => by omega_arith)
      (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _)) (by omega_arith))
      (fun _ _ _ h => h) fun σ s _ ⟨⟨⟨I, fc⟩, hne⟩, hq⟩ => ⟨⟨⟨I.sc, I.r24, I.ok, I.A, I.rpp, fun r' hr' => ?_, I.s2, I.t0⟩,
        fc⟩, hne⟩
    rcases (by omega_arith : r' < r ∨ r' = r) with h' | rfl
    · exact I.s1 r' h'
    · rw [Proof.MlDsa.PreparedKey.secret_s1 p _ hr] at hq; exact hq
  · rw [Nat.zero_add] at hi
    have h1 : ∀ r < p.ℓ, s1Base p + r ≠ s2Base p + i := fun r hr => by simp only [s1Base, s2Base]; omega_arith
    refine Piece.mono (cp_piece hF (j := s2Base p + i) (i := p.ℓ + i)
      ⟨by simp only [s1Base, s2Base]; omega_arith, by simp only [s2Base, aBase]; omega_arith⟩
      (Nat.le_refl _) (Nat.le_of_lt hi) (Nat.zero_le _) h1 (fun i' hi' => by omega_arith)
      (fun _ h => absurd h (Nat.not_lt_zero _)) (by omega_arith))
      (fun _ _ _ h => h) fun σ s _ ⟨⟨⟨I, fc⟩, hne⟩, hq⟩ => ⟨⟨⟨I.sc, I.r24, I.ok, I.A, I.rpp, I.s1, fun i' hi' => ?_, I.t0⟩,
        fc⟩, hne⟩
    rcases (by omega_arith : i' < i ∨ i' = i) with h' | rfl
    · exact I.s2 i' h'
    · rw [Proof.MlDsa.PreparedKey.secret_s2 p _ hi] at hq; exact hq
  · rw [Nat.zero_add] at hi
    have h1 : ∀ r < p.ℓ, s1Base p + r ≠ t0Base p + i := fun r hr => by simp only [s1Base, t0Base]; omega_arith
    have h2 : ∀ i' < p.k, s2Base p + i' ≠ t0Base p + i := fun i' hi' => by simp only [s2Base, t0Base]; omega_arith
    refine Piece.mono (cp_piece hF (j := t0Base p + i) (i := p.ℓ + p.k + i)
      ⟨by simp only [s1Base, t0Base]; omega_arith, by simp only [t0Base, aBase]; omega_arith⟩
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_of_lt hi) h1 h2 (fun i' hi' => by omega_arith) (by omega_arith))
      (fun _ _ _ h => h) fun σ s _ ⟨⟨⟨I, fc⟩, hne⟩, hq⟩ => ⟨⟨⟨I.sc, I.r24, I.ok, I.A, I.rpp, I.s1, I.s2, fun i' hi' => ?_⟩,
        fc⟩, hne⟩
    rcases (by omega_arith : i' < i ∨ i' = i) with h' | rfl
    · exact I.t0 i' h'
    · rw [Proof.MlDsa.PreparedKey.secret_t0 p _ hi] at hq; exact hq

end

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hF hS in
/-- A branch on the cache's length, which the entry states fix. -/
theorem Piece.ite15 {I J : State → State → Prop} {t e : Prog isa}
    (h15 : ∀ σ s, CPre p STK σ → I σ s → s.gpr .r15 = σ.gpr .r15)
    (ht : CPiece p STK (fun σ s => I σ s ∧ σ.gpr .r15 ≠ 0) J t)
    (he : CPiece p STK (fun σ s => I σ s ∧ σ.gpr .r15 = 0) J e) :
    CPiece p STK I J (.ite (.nonzero .d .r15) t e) := by
  refine ⟨fun σ s hp hs => WP.ite _ (eval_nonzero s .r15) (fun hb => ht.ok σ s hp ⟨hs, ?_⟩)
    fun hb => he.ok σ s hp ⟨hs, ?_⟩, ?_⟩
  · rw [← h15 σ s hp hs]; simpa using hb
  · rw [← h15 σ s hp hs]; simpa using hb
  · refine RelCT.ite (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => by
      rw [eval_nonzero, eval_nonzero, h15 _ _ p₁ i₁, h15 _ _ p₂ i₂, pub.2.2]) ?_ ?_
    · exact RelCT.mono ht.tr (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩, hb⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, ⟨i₁, by
        rw [eval_nonzero, h15 _ _ p₁ i₁] at hb; simpa using hb⟩, ⟨i₂, by
        rw [eval_nonzero, h15 _ _ p₁ i₁] at hb; rw [← pub.2.2]; simpa using hb⟩⟩) fun _ _ h => h
    · exact RelCT.mono he.tr (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩, hb⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, ⟨i₁, by
        rw [eval_nonzero, h15 _ _ p₁ i₁] at hb; simpa using hb⟩, ⟨i₂, by
        rw [eval_nonzero, h15 _ _ p₁ i₁] at hb; rw [← pub.2.2]; simpa using hb⟩⟩) fun _ _ h => h

omit hP hF hS in
theorem sdepth_rhoPP : sdepth rhoPP ≤ 48 := by decide

omit hP hS in
/-- `ρ″`, keeping `FC`. -/
theorem rhoPPC_piece :
    CPiece p STK (fun σ s => IM p STK σ s ∧ FC STK σ s) (fun σ s => ID p STK σ 0 0 0 s ∧ FC STK σ s) rhoPP := by
  have r := (rhoPP_piece (STK := STK) hF).cache
  refine ⟨fun σ s hp ⟨h, fc⟩ => WP.mono (wp_frame (r.ok σ s hp h) (by have := sdepth_rhoPP; omega))
    fun s' ⟨h', fr⟩ => ⟨h', FC.step fc h.sc.wr h.sc.sp (Nat.le_trans sdepth_rhoPP h.sc.site.s48)
      (by have := h.sc.site.spk; have := σ.sp.isLt; rw [h.sc.sp] at *; omega_arith) fr⟩,
    RelCT.mono r.tr (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, i₁.1, i₂.1⟩) fun _ _ h => h⟩

/-- Decoding, from `Â`: `ρ″`, then `ŝ₁`, `ŝ₂` and `t̂₀`, copied from the cache
if `r15 ≠ 0` and decoded from `sk` otherwise. -/
theorem decode_piece :
    CPiece p STK (fun σ s => IM p STK σ s ∧ FC STK σ s) (ID p STK · p.ℓ p.k p.k) (decode P p) := by
  unfold decode
  refine (rhoPPC_piece hF).seq (Piece.ite15 (fun σ s _ h => h.1.sc.pres .r15 (by decide) (by decide))
    (Piece.mono (cached_piece hF) (fun _ _ _ h => ⟨h.1, h.2⟩) fun _ _ _ h => h.1.1)
    (Piece.mono (keys_piece hP hF hS).cache (fun _ _ _ h => h.1.1) fun _ _ _ h => h))

end

end VG.Proof.MlDsa.PPC64LE.Sign
