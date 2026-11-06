module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.ExpA
import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Seeds
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlDsa.RISCV64.CacheCopy
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.ExpA
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# ML-DSA signing on RISC-V: `ρ″` and the private key

As on PPC64LE (`Proof/MlDsa/PPC64LE/Sign/PhaseD.lean`), once `Â` is sampled
(`IM`): `rnd ‖ μ` to `W1`, `ρ″ = H(K ‖ rnd ‖ μ, 64)` to `MS`, and `sig` to
`s8`, which takes the layout from `slay1` to `slay2` (`SC1.toSC2`); then
`ŝ₁[r]`, `ŝ₂[i]` and `t̂₀[i]`, each the `NTT` of the `BitUnpack` of its piece
of `sk`, in their slots (`ID`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sign

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of taint4 hashLay
  hashLay_ptr hashS hashS_tr pieceS ix_ne1 shake31 polyIs_keepW bytes_keepW copyS)
open VG.Impl.MlDsa.RISCV64.Sign
open VG.Impl.MlDsa.RISCV64.KeyGen (seqR callAt)
open VG.Impl.MlKem.RISCV64 (copy hash)
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

/-- `sig` to `s8`: from `SC1` to `SC2`. -/
theorem SC1.toSC2 {p : Params} {STK : Nat} {σ s s' : State} (hp : SPre p STK σ) (h : SC1 p STK σ s)
    (g28 : s'.gpr .s8 = sSig σ) (go : ∀ r, r ≠ .s8 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : SC2 p STK σ s' := by
  have hs := h.site
  refine ⟨⟨slay2_ok hp, rfl, by decide, by decide, hs.sz0, hs.sz1, by rw [hsp]; exact hs.p1, hs.s1168,
    by rw [hsp]; exact hs.spk, by rw [hsp]; exact hs.al, hs.al0, by rw [go _ (by decide)]; exact hs.s11, by rw [go _ (by decide)]; exact hs.s10,
    by rw [go _ (by decide)]; exact hs.s9, g28, fun i hi hi1 => ?_, fun i hi hi1 => ?_⟩,
    hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, fun r hr hs' => ?_, by rw [hm]; exact h.sav,
    by rw [hm]; exact h.sk, by rw [hm]; exact h.mu, hp, by rw [go _ (by decide)]; exact h.s3,
    by rw [hm]; exact h.cache⟩
  · show _ ∈ s'.wr
    rw [hwr, h.wr, hp.wr]
    simp only [sWb2, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · simp [Lay.buf, slay2]
    · exact absurd rfl hi1
    · simp [Lay.buf, slay2]
  · show _ ∈ s'.rd ++ s'.wr
    rw [hrd, hwr, h.rd, h.wr, hp.rd, hp.wr]
    rcases (by omega_arith : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;> simp [Lay.buf, slay2]
  · have : r ≠ .s8 := fun e => by subst e; simp [savedTop] at hs'
    rw [go r this]; exact h.pres r hr hs'

/-! ## `Â` -/

/-- `Â` sampled within `maxBounds`, in its slots. -/
structure IM (p : Params) (STK : Nat) (σ s : State) : Prop where
  sc : SC1 p STK σ s
  s4 : s.gpr .s4 = 1
  ok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (seedE p σ e)).isSome
  A : ∀ e < p.k * p.ℓ, PolyIs s.mem ((slay1 p STK σ).A 0 (oP (aBase p + e))) (aVal p σ e)

theorem IA.im {p : Params} {STK : Nat} {σ s : State} (h : IA p STK σ (p.k * p.ℓ) s) (h1 : s.gpr .s4 = 1) :
    IM p STK σ s := ⟨h.sc, h1, (h.ok h1).1, (h.ok h1).2⟩

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hF hS in
theorem IM.keep {σ s s' : State} (h : IM p STK σ s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((slay1 p STK σ).RL W) s s') (hc : sc1Chk p STK W = true)
    (hA : ∀ e < p.k * p.ℓ, sepAll (slay1 p STK σ).sizes (0, oP (aBase p + e), 1024) W = true)
    (h24 : s'.gpr .s4 = s.gpr .s4) : IM p STK σ s' :=
  ⟨h.sc.keep hk hc, h24.trans h.s4, h.ok,
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
    (∀ pc ∈ ([⟨.s10, 32, 32⟩, ⟨.s11, oW1, 96⟩] : List Impl.MlKem.RISCV64.Piece),
      PieceOk (hashLay (slay1 p STK σ) s Ksk) ix s false pc) ∧
    PieceOk (hashLay (slay1 p STK σ) s Ksk) ix s true (⟨.s11, oMS, 64⟩ : Impl.MlKem.RISCV64.Piece) := by
  refine ⟨fun pc hpc => ?_, pieceS hs rfl (show oMS < 32768 by decide) (show 64 < 2048 by decide) (by decide)
    (by ssep hF [hashLay, Lay.size]) (.inl rfl) fun _ => show ix Reg.s11 ∈ sWb1 by decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl
  · exact pieceS hs rfl (show 32 < 32768 by decide) (show 32 < 2048 by decide) (by decide)
      (by
        have := hF.sk; have := hF.scr
        dsimp only [hashLay, Lay.size, Ksk, sepAll, sepB, tri, ix, kRegs]
        set_option linter.unusedSimpArgs false in
        simp (config := { decide := true }) only [sepB, slay1_sizes, List.getD_cons_zero, List.getD_cons_succ,
          List.length_cons, List.length_nil, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.or_eq_true,
          decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.and_true, Bool.true_and, true_and, and_true, true_or, or_true,
          Nat.zero_add, ite_true, ite_false]
        omega_arith) (.inr rfl) fun h => absurd h (by decide)
  · exact pieceS hs rfl (show oW1 < 32768 by decide) (show 96 < 2048 by decide) (by decide)
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
theorem copy1_ok {σ s : State} (h : IM p STK σ s) : WP isa (copy .s8 0 .s11 oW1 32) s (IW1 p STK σ) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine WP.mono (copyS h.sc.site (sb := .s8) (so := 0) (db := .s11) (dO := oW1) (len := 32)
    ⟨sptr_ok rfl (by decide), rfl⟩ ⟨sptr_ok rfl (by decide), by ssep hF⟩ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by ssep hF)) fun s₁ ⟨k₁, b₁⟩ =>
      ⟨h.keep k₁ (by ssep hF [sc1Chk]) (fun e he => by ssep hF) (k₁.cs .s4 (by decide)), ?_⟩
  show bytesAt s₁.mem (lpa (slay1 p STK σ) (.s11, oW1)) 32 = _
  rw [b₁]; exact h.sc.rnd

omit hP hS in
theorem copy2_ok {σ s : State} (h : IW1 p STK σ s) : WP isa (copy .s9 0 .s11 (oW1 + 32) 64) s (IW p STK σ) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hL := h.im.sc.site.ok
  refine WP.mono (copyS h.im.sc.site (sb := .s9) (so := 0) (db := .s11) (dO := oW1 + 32) (len := 64)
    ⟨sptr_ok rfl (by decide), rfl⟩ ⟨sptr_ok rfl (by decide), by ssep hF⟩ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by ssep hF)) fun s₂ ⟨k₂, b₂⟩ =>
      ⟨h.im.keep k₂ (by ssep hF [sc1Chk]) (fun e he => by ssep hF) (k₂.cs .s4 (by decide)), ?_⟩
  have e₁ : bytesAt s₂.mem ((slay1 p STK σ).A 0 oW1) 32 = rndOf σ := by
    rw [bytes_keepW hL k₂.frame (i := 0) (o := oW1) (l := 32) (by ssep hF) (by decide) (by decide)]; exact h.w
  have e₂ : bytesAt s₂.mem ((slay1 p STK σ).A 0 (oW1 + 32)) 64 = muOf σ := by
    show bytesAt s₂.mem (lpa (slay1 p STK σ) (.s11, oW1 + 32)) 64 = _
    rw [b₂]; exact h.im.sc.mu
  rw [show (96 : Nat) = 32 + 64 from rfl, Proof.MlKem.bytesAt_add, e₁]
  refine congrArg _ ?_
  simp only [Lay.A, BitVec.add_assoc, ← BitVec.ofNat_add] at e₂ ⊢
  exact e₂

omit hP hS in
theorem rppHash_ok {σ s : State} (h : IW p STK σ s) :
    WP isa (hash 136 0x1f [⟨.s10, 32, 32⟩, ⟨.s11, oW1, 96⟩] [⟨.s11, oMS, 64⟩]) s (IR p STK σ) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hs := h.im.sc.site
  obtain ⟨hin, hq⟩ := rppPieces hF hs
  refine WP.mono (hashS hs ksk (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by simp) hin hq)
    fun s' ⟨k', o'⟩ => ⟨h.im.keep k' (by ssep hF [sc1Chk]) (fun e he => by ssep hF) (k'.cs .s4 (by decide)), ?_⟩
  have o₃ : bytesAt s'.mem ((slay1 p STK σ).A 0 oMS) 64 = _ := o'
  rw [o₃]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
    hashLay_ptr _ _ _ (ix_ne1 _)]
  have e1 : bytesAt s.mem ((slay1 p STK σ).ptr (ix Reg.s10) + BitVec.ofNat 64 32) 32 =
      ((skOf p σ).drop 32).take 32 := by
    have := hF.sk
    rw [← h.im.sc.sk, Proof.MlKem.bytesAt_slice _ _ (by omega_arith)]
    simp only [Lay.A, BitVec.add_zero]; rfl
  have e2 : bytesAt s.mem ((slay1 p STK σ).ptr (ix Reg.s11) + BitVec.ofNat 64 oW1) 96 = rndOf σ ++ muOf σ := h.w
  rw [e1, e2, shake31, ← List.append_assoc]
  exact (Proof.MlKem.shake256_eq _ _).symm


end

/-- `Â`, `ρ″`, and the first `a` polynomials of `ŝ₁`, `b` of `ŝ₂` and `c` of `t̂₀`. -/
structure ID (p : Params) (STK : Nat) (σ : State) (a b c : Nat) (s : State) : Prop where
  sc : SC2 p STK σ s
  s4 : s.gpr .s4 = 1
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
    WP isa (.block [.load .d .s8 .s11 oSIG]) s (ID p STK σ 0 0 0) := by
  have hs := h.im.sc.site
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .s11 + BitVec.ofNat 64 oSIG) 8 := by
    rw [hs.s11]
    exact hs.crE (q := sc oSIG) (l := 8) ⟨sptr_ok rfl (by decide), by ssep hF⟩ _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine Steps.WP.cons (exec_load_d (by decide) (by rw [hs.s11]; exact hs.alS (q := sc oSIG) ⟨rfl, by decide⟩) hin)
    (WP.block_nil ?_)
  have g : s.mem.readW (s.gpr .s11 + BitVec.ofNat 64 oSIG) 64 = sSig σ := by rw [hs.s11]; exact h.im.sc.sig
  rw [g]
  exact ⟨h.im.sc.toSC2 hp (RegUpd.gpr_write_self ..) (fun r hr => RegUpd.gpr_write_of_ne _ _ hr) rfl rfl rfl rfl,
    by rw [RegUpd.gpr_write_of_ne _ _ (by decide)]; exact h.im.s4, h.im.ok, fun e he => h.im.A e he, h.rpp,
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
    (h24 : s'.gpr .s4 = s.gpr .s4) (hj : s1Base p ≤ j ∧ j < aBase p) (ha : a ≤ p.ℓ) (hb : b ≤ p.k) (hc : c ≤ p.k)
    (h1 : ∀ r < a, s1Base p + r ≠ j) (h2 : ∀ i < b, s2Base p + i ≠ j) (h3 : ∀ i < c, t0Base p + i ≠ j) :
    ID p STK σ a b c s' := by
  have hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  have hL := h.sc.site.ok
  dsimp only [s1Base, s2Base, t0Base, aBase] at hj h1 h2 h3
  obtain ⟨hj1, hj2⟩ := hj
  refine ⟨h.sc.keep hk (by ssep hF [sc2Chk]), h24.trans h.s4, h.ok,
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
    (ho : o + len ≤ p.skLen) (hlt : 0 < len ∧ len < 2 ^ 31 - 2048 ∧ x < 2 ^ 31 - 2048 ∧ y < 2 ^ 31 - 2048) :
    KeyGen.BuOk (slay2 p STK σ) sWb2 (.s10, o) len x y (pS j) := by
  have hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  have := hF.lens
  have hj' := hj
  dsimp only [s1Base, aBase] at hj'
  obtain ⟨hj1, hj2⟩ := hj'
  exact ⟨⟨sptr_ok rfl (by omega_arith), by ssep hF⟩, ⟨sptr_ok rfl (by slt hF), by ssep hF⟩,
    show ix Reg.s11 ∈ sWb2 by decide, by ssep hF, hxy, hlen, hlt, by salsep⟩

omit hP hS ha hb hc h1 h2 h3 in
theorem nt_m {σ : State} : KeyGen.IpOk (slay2 p STK σ) sWb2 (pS j) (sc oPS) := by
  have hk' := hF.k; have hl := hF.l; have hkl := hF.kl
  have hj' := hj
  dsimp only [s1Base, aBase] at hj'
  obtain ⟨hj1, hj2⟩ := hj'
  exact ⟨⟨sptr_ok rfl (by slt hF), by ssep hF⟩, ⟨sptr_ok rfl (by decide), by ssep hF⟩,
    show ix Reg.s11 ∈ sWb2 by decide, show ix Reg.s11 ∈ sWb2 by decide, by ssep hF, by salsep, by salsep⟩

theorem du_piece (hxy : (x, y) ∈ bitPackParams) (hlen : len = 32 * bitlen (x + y))
    (ho : o + len ≤ p.skLen) (hlt : 0 < len ∧ len < 2 ^ 31 - 2048 ∧ x < 2 ^ 31 - 2048 ∧ y < 2 ^ 31 - 2048) :
    SPiece p STK (ID p STK · a b c) (DU p STK a b c j o len x y) (bitUnpackAt P (.s10, o) len x y (pS j)) := by
  refine ⟨fun σ s _ h => ?_, rel_of (RelCT.exists_ fun σ => KeyGen.bu_tr hP.bitUnpack hS
    (du_m hF hj (σ := σ) hxy hlen ho hlt) fun _ _ h => ⟨h.1, h.2.1, h.2.2⟩)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub h₁.sc h₂.sc⟩⟩
  unfold bitUnpackAt
  refine KeyGen.bu_ok hP.bitUnpack h.sc.site hS (du_m hF hj hxy hlen ho hlt) fun s₁ k₁ hb₁ =>
    ⟨id_keep hF h (k₁.monoL (by simp)) (k₁.cs .s4 (by decide)) hj ha hb hc h1 h2 h3, ?_⟩
  have e : bytesAt s.mem (lpa (slay2 p STK σ) (.s10, o)) len = ((skOf p σ).drop o).take len := sk_slice2 h.sc ho
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
    ⟨id_keep hF h.1 k₂ (k₂.cs .s4 (by decide)) hj ha hb hc h1 h2 h3, ?_⟩
  show PolyIs s₂.mem (lpa (slay2 p STK σ) (pS j)) _
  rw [← h.2.2]
  exact hb₂

end

omit hP hF hS in
/-- The selection in `s3` is the cache pointer, if it is not zero. -/
theorem sel_cache {σ s : State} (h : SC2 p STK σ s) (h3 : s.gpr .s3 ≠ 0) :
    s.gpr .s3 = sCache σ ∧ sCLen σ = 1024 * (p.ℓ + 2 * p.k) ∧
      Proof.MlDsa.CachedSecretPolys p σ.mem (sCache σ) (skOf p σ) := by
  have e := h.s3
  have h6 : σ.gpr .a6 ≠ 0 := fun e6 => by
    rw [e, cSel, ite_eq_left_of_eq_true _ _ (eq_true e6)] at h3; exact h3 rfl
  obtain ⟨hl, hc⟩ := h.pre.cache.resolve_left h6
  exact ⟨by rw [e, cSel, ite_eq_right_of_eq_false _ _ (eq_false h6)],
    by rw [hl]; simp only [Spec.MlDsa.n]; try omega_arith, hc⟩

omit hP hF hS in
/-- The bytes of slot `s1Base + j` after the copy are those of polynomial `j` of the cache. -/
theorem slot_bytes {σ : State} {m : Mem} {j : Nat} (hj : j < p.ℓ + 2 * p.k)
    (hb : bytesAt m ((slay2 p STK σ).A 0 (oP (s1Base p))) (1024 * (p.ℓ + 2 * p.k)) =
      bytesAt σ.mem (sCache σ) (1024 * (p.ℓ + 2 * p.k))) :
    bytesAt m ((slay2 p STK σ).A 0 (oP (s1Base p + j))) 1024 =
      bytesAt σ.mem (sCache σ + BitVec.ofNat 64 (4 * Spec.MlDsa.n * j)) 1024 := by
  have hm : 1024 * j + 1024 ≤ 1024 * (p.ℓ + 2 * p.k) := by omega_arith
  have e1 := Proof.MlKem.bytesAt_slice m ((slay2 p STK σ).A 0 (oP (s1Base p))) hm
  have e2 := Proof.MlKem.bytesAt_slice σ.mem (sCache σ) hm
  rw [hb] at e1
  rw [show 4 * Spec.MlDsa.n * j = 1024 * j by simp only [Spec.MlDsa.n]; try omega_arith, ← e2, e1]
  simp only [Lay.A, BitVec.add_assoc, ← BitVec.ofNat_add, oP]
  congr 3; omega_arith

omit hP hS in
theorem cached_glue : KeyGen.glueOk [(.a1, .ptr (s1P p 0)), (.a2, .imm (1024 * (p.ℓ + 2 * p.k)))] = true := by
  have hk := hF.k; have hl := hF.l
  simp only [KeyGen.glueOk, KeyGen.argReg, KeyGen.argOk, List.all_cons, List.all_nil, s1P, pS, sc, oP]
  set_option linter.unusedSimpArgs false in
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_self_eq_true, Bool.true_and, Bool.and_true, Bool.or_true,
    Bool.true_or]
  constructor <;> omega_arith

omit hP hS in
theorem cached_ok {σ s : State} (h : ID p STK σ 0 0 0 s) (h3 : s.gpr .s3 ≠ 0) :
    WP isa (cached p) s (ID p STK σ p.ℓ p.k p.k) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hs := h.sc.site
  have hp := h.sc.pre
  have hL := hs.ok
  obtain ⟨hsel, hlen, hpolys⟩ := sel_cache h.sc h3
  obtain ⟨hs1, hs2, hs3⟩ := hF.scr
  have hfit : (sCache σ).toNat + 1024 * (p.ℓ + 2 * p.k) ≤ 2 ^ 64 := by have := hp.f_x; rw [hlen] at this; exact this
  have hbd : oP (s1Base p) + 1024 * (p.ℓ + 2 * p.k) ≤ (slay2 p STK σ).size 0 := by
    rw [slay2_size0]; simp only [oP, s1Base]; omega_arith
  have hgo := cached_glue hF
  have dcx : Region.Disjoint ⟨sScr σ, scrLen p⟩ ⟨sCache σ, 1024 * (p.ℓ + 2 * p.k)⟩ := by
    have := hp.d_cx; rw [hlen] at this; exact this
  have ccov : (⟨sCache σ, 1024 * (p.ℓ + 2 * p.k)⟩ : Region) ∈ σ.rd := by
    rw [hp.rd, ← hlen]; simp
  have hS : s.gpr .s3 + BitVec.ofNat 64 0 = sCache σ := by rw [hsel, BitVec.add_zero]
  have hD : s.gpr (s1P p 0).1 + BitVec.ofNat 64 (s1P p 0).2 = (slay2 p STK σ).A 0 (oP (s1Base p)) := by
    show s.gpr .s11 + _ = _
    rw [hs.s11]; simp only [Lay.A, s1Base, Nat.add_zero]
  unfold cached
  refine WP.mono (CacheCopy.cacheCopy_ok (off := 0) (dst := s1P p 0) (len := 1024 * (p.ℓ + 2 * p.k)) (s := s)
    (by decide) hgo (by omega_arith) (by omega_arith)
    (by rw [hS, hD]; exact (dcx.sub_left (Lay.R_sub (L := slay2 p STK σ) (i := 0) hbd)).symm)
    (Covers.of_mem fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hS, h.sc.rd]; exact List.mem_append_left _ ccov)
    (by rw [hD]; exact Lay.covers (hs.cw 0 (by decide) (by decide)) hbd))
    fun s' ⟨cs, rd', wr', sp', fr, hb⟩ => ?_
  rw [hS, hD] at hb
  rw [hD] at fr
  have hk : Kept ((slay2 p STK σ).RL [(0, oP (s1Base p), 1024 * (p.ℓ + 2 * p.k))]) s s' :=
    ⟨cs, sp', rd', wr', fr⟩
  have hb' : bytesAt s'.mem ((slay2 p STK σ).A 0 (oP (s1Base p))) (1024 * (p.ℓ + 2 * p.k)) =
      bytesAt σ.mem (sCache σ) (1024 * (p.ℓ + 2 * p.k)) := by
    rw [hb]; have := h.sc.cache; rw [hlen] at this; exact this
  have hpoly : ∀ j (hj : j < p.ℓ + 2 * p.k) {f : Poly},
      (Spec.MlDsa.preparedSecretPolys p (skOf p σ))[j]! = f →
        PolyIs s'.mem ((slay2 p STK σ).A 0 (oP (s1Base p + j))) f := fun j hj f hf => by
    have := hpolys j hj
    rw [hf] at this
    exact Proof.MlDsa.PreparedKey.polyIs_of_copy (slot_bytes hj hb') this
  refine ⟨h.sc.keep hk (by ssep hF [sc2Chk, s1Base]), by rw [hk.cs .s4 (by decide)]; exact h.s4, h.ok,
    fun e he => polyIs_keepW hL hk.frame (by ssep hF [s1Base]) (by decide) rfl (h.A e he),
    by rw [bytes_keepW hL hk.frame (i := 0) (o := oMS) (l := 64) (by ssep hF [s1Base]) (by decide) (by decide)]
       exact h.rpp,
    fun r hr => hpoly r (by omega_arith) (Proof.MlDsa.PreparedKey.secret_s1 p _ hr),
    fun i hi => ?_, fun i hi => ?_⟩
  · rw [show s2Base p + i = s1Base p + (p.ℓ + i) by simp only [s1Base, s2Base]; omega_arith]
    exact hpoly _ (by omega_arith) (Proof.MlDsa.PreparedKey.secret_s2 p _ hi)
  · rw [show t0Base p + i = s1Base p + (p.ℓ + p.k + i) by simp only [s1Base, t0Base]; omega_arith]
    exact hpoly _ (by omega_arith) (Proof.MlDsa.PreparedKey.secret_t0 p _ hi)

omit hP hS in
theorem cached_piece :
    SPiece p STK (fun σ s => ID p STK σ 0 0 0 s ∧ s.gpr .s3 ≠ 0) (ID p STK · p.ℓ p.k p.k) (cached p) :=
  ⟨fun σ s _ h => cached_ok hF h.1 h.2,
    rel_of (CacheCopy.cacheCopy_tr (by decide) (cached_glue hF)
      (P := fun x y => x.sp = y.sp ∧ x.gpr .s3 = y.gpr .s3 ∧ x.gpr .s11 = y.gpr .s11) fun _ _ h => h)
      fun σ₁ σ₂ x y _ _ pub h₁ h₂ => ⟨by rw [h₁.1.sc.sp, h₂.1.sc.sp, pub.1],
        by rw [h₁.1.sc.s3, h₂.1.sc.s3, cSel_pub pub],
        by rw [h₁.1.sc.site.s11, h₂.1.sc.site.s11, slay2_pub pub]⟩⟩

omit hP hS in
theorem eta_facts : (p.η, p.η) ∈ bitPackParams ∧ sLen p = 32 * bitlen (p.η + p.η) ∧
    0 < sLen p ∧ sLen p < 2 ^ 31 - 2048 ∧ p.η < 2 ^ 31 - 2048 := by
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
    (fun _ _ _ h => h) fun σ s _ ⟨I, hq⟩ => ⟨I.sc, I.s4, I.ok, I.A, I.rpp, fun r' hr' => ?_, I.s2, I.t0⟩
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
    (fun _ _ _ h => h) fun σ s _ ⟨I, hq⟩ => ⟨I.sc, I.s4, I.ok, I.A, I.rpp, I.s1, fun i' hi' => ?_, I.t0⟩
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
    (fun _ _ _ h => h) fun σ s _ ⟨I, hq⟩ => ⟨I.sc, I.s4, I.ok, I.A, I.rpp, I.s1, I.s2, fun i' hi' => ?_⟩
  rcases (by omega_arith : i' < i ∨ i' = i) with h' | rfl
  · exact I.t0 i' h'
  · have e : skT0 p i' = 128 + Proof.MlDsa.Sign.lenS p * p.ℓ + Proof.MlDsa.Sign.lenS p * p.k + 32 * d * i' := by
      show 128 + sLen p * (p.ℓ + p.k) + 416 * i' = _
      rw [Nat.mul_add, ← Nat.add_assoc]; rfl
    rw [e] at hq
    exact hq

/-- `ŝ₁`, `ŝ₂` and `t̂₀`, decoded from `sk` and transformed. -/
theorem decodeKey_piece : SPiece p STK (ID p STK · 0 0 0) (ID p STK · p.ℓ p.k p.k) (decodeKey P p) := by
  unfold decodeKey
  exact (Piece.mono (Piece.seqR (I := fun r σ s => ID p STK σ r 0 0 s) p.ℓ 0
    fun r _ hr => decS1_piece hP hF hS (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h).seq
    ((Piece.mono (Piece.seqR (I := fun i σ s => ID p STK σ p.ℓ i 0 s) p.k 0
      fun i _ hi => decS2_piece hP hF hS (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h).seq
      (Piece.mono (Piece.seqR (I := fun i σ s => ID p STK σ p.ℓ p.k i s) p.k 0
        fun i _ hi => decT0_piece hP hF hS (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h))

/-- Decoding, from `Â`: `ρ″`, `ŝ₁`, `ŝ₂` and `t̂₀`, from the cache or from `sk`. -/
theorem decode_piece : SPiece p STK (IM p STK) (ID p STK · p.ℓ p.k p.k) (decode P p) := by
  unfold decode
  exact (rhoPP_piece hF).seq (CacheCopy.pieceIte
    (fun _ _ _ _ _ _ pub h₁ h₂ => by rw [h₁.sc.s3, h₂.sc.s3, cSel_pub pub]) (cached_piece hF)
    (Piece.mono (decodeKey_piece hP hF hS) (fun _ _ _ h => h.1) fun _ _ _ h => h))
end

end VG.Proof.MlDsa.RISCV64.Sign
