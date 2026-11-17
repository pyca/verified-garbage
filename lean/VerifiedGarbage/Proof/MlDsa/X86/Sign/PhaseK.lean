module

public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Words
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Inv
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Prims
import VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimB
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Local
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimA
import VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimD
import VerifiedGarbage.Proof.MlDsa.Sample.Hash
import VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimC
import VerifiedGarbage.Proof.MlKem.X86.TopSeq
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `MlDsa.X86.Sign.Run`, which only this module used -/

section

/-! ### `MlDsa.X86.Sign.PhaseC`, which only this module used -/

section

/-! ### `MlDsa.X86.Sign.PhaseD`, which only this module used -/

section

/-! ### `MlDsa.X86.Sign.PhaseA`, which only this module used -/

section

/-!
# ML-DSA signing on x86 (32-bit): `ExpandA`

`ρ` is copied to `RS`, and entry `e` of `Â` (row `e / ℓ`, column `e % ℓ`) is
sampled into slot `aBase + e` from the seed `ρ ‖ e % ℓ ‖ e / ℓ` (`seedE`),
with `OK` the AND of the results (`okE`). After entry `e` (`IA e`): if every
entry so far succeeded, their slots hold them, within `maxBounds` (`aVal`);
otherwise one of them fails within `minBounds`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_ copyW)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params}

section
variable (p : Params)

/-- `ρ`, from the initial state. -/
abbrev rhoS (s₀ : State) : List Byte := rhoV (skOf p s₀)

/-- The seed of entry `e`. -/
abbrev seedE (s₀ : State) (e : Nat) : List Byte := aSeed (rhoS p s₀) (e / p.ℓ) (e % p.ℓ)

/-- Entry `e`, within `maxBounds`. -/
abbrev aVal (s₀ : State) (e : Nat) : Poly := Av (skOf p s₀) (e / p.ℓ) (e % p.ℓ)

/-- The values of `ŝ₁`, `ŝ₂` and `t̂₀`, from the initial state. -/
abbrev S1 (s₀ : State) : Nat → Poly := s1F p (skOf p s₀)
abbrev S2 (s₀ : State) : Nat → Poly := s2F p (skOf p s₀)
abbrev T0 (s₀ : State) : Nat → Poly := t0F p (skOf p s₀)

/-- The first `n1`, `n2` and `n0` polynomials of `ŝ₁`, `ŝ₂` and `t̂₀`. -/
structure DKs (n1 n2 n0 : Nat) (s₀ : State) (m : Mem) : Prop where
  f1 : Fam s₀ m (s1B p) n1 (S1 p s₀)
  f2 : Fam s₀ m (s2B p) n2 (S2 p s₀)
  f0 : Fam s₀ m (t0B p) n0 (T0 p s₀)

/-- The first `e` entries were sampled. -/
def okE (F : List Byte → Bool) (s₀ : State) (e : Nat) : Bool := (List.range e).all fun e' => F (seedE p s₀ e')

end

theorem okE_succ {F : List Byte → Bool} {s₀ : State} {e : Nat} :
    okE p F s₀ (e + 1) = (okE p F s₀ e && F (seedE p s₀ e)) := by
  simp only [okE, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

theorem okE_lt {F : List Byte → Bool} {s₀ : State} {e e' : Nat} (h : okE p F s₀ e = true) (he : e' < e) :
    F (seedE p s₀ e') = true :=
  List.all_eq_true.mp h e' (List.mem_range.mpr he)

theorem DKs.keep {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {n1 n2 n0 : Nat} (h1 : n1 ≤ p.ℓ) (h2 : n2 ≤ p.k)
    (h0 : n0 ≤ p.k) {bs : List Buf} {N : Nat} (hN : N ≤ 80) {m m' : Mem} (fr : Frame (FR s₀ bs N) m m')
    (h : ∀ c ∈ bs, OutS p n1 n2 n0 c) (d : DKs p n1 n2 n0 s₀ m) : DKs p n1 n2 n0 s₀ m' :=
  ⟨d.f1.keep hp ps hN fr (by simp only [nS, s1B]; omega_arith) fun c hc => (h c hc).1,
    d.f2.keep hp ps hN fr (by simp only [nS, s2B]; omega_arith) fun c hc => (h c hc).2.1,
    d.f0.keep hp ps hN fr (by simp only [nS, t0B]; omega_arith) fun c hc => (h c hc).2.2⟩

/-- After entry `e`. -/
structure IA (p : Params) (F : List Byte → Bool) (e : Nat) (s₀ s : State) : Prop where
  ctx : Ctx (Y p) s₀ s
  rs : bytesAt s.mem (Buf.addr s₀ (sc oRS 32)) 32 = rhoS p s₀
  ok : scw s₀ s oOK = if okE p F s₀ e then 1 else 0
  fam : okE p F s₀ e = true → Fam s₀ s.mem (aBase p) e (aVal p s₀)
  bad : okE p F s₀ e = false → ∃ e' < e, rejNTTPoly minBounds.rejNTT (seedE p s₀ e') = none
  dk : DKs p p.ℓ p.k p.k s₀ s.mem

/-- The result of `vg_mldsa_rej_ntt_poly`, if it succeeded within `maxBounds`. -/
theorem rej_val {x : List Byte} {r : BitVec 32} {out : Poly}
    (h : Outcome (fun b => rejNTTPoly b.rejNTT x) r out) (h1 : r = 1)
    (hm : (rejNTTPoly maxBounds.rejNTT x).isSome) : out = (rejNTTPoly maxBounds.rejNTT x).getD zero := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    obtain e1 := rejNTTPoly_mono (Nat.le_max_left b.rejNTT maxBounds.rejNTT) hb
    obtain e2 := rejNTTPoly_mono (Nat.le_max_right b.rejNTT maxBounds.rejNTT) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

theorem integerToBytes_one {x : Nat} : integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [integerToBytes]

theorem skLen_ge (ps : PS p) : 32 ≤ p.skLen := by have := ps.hskLen; omega_using [this]

theorem rhoS_eq {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') : rhoS p s₀ = rhoS p s₀' :=
  rho_of_leak (by rw [VG.Proof.MlKem.bytesAt_length]; exact skLen_ge ps)
    (by rw [VG.Proof.MlKem.bytesAt_length]; exact skLen_ge ps) hq.coarse

/-! ## An entry -/

/-- The bytes of the layout an entry needs. -/
theorem okRS (ps : PS p) : (Y p).ok (sc oRS 32) = true ∧ (Y p).okW (sc (oRS + 32) 1) = true ∧
    (Y p).okW (sc (oRS + 33) 1) = true ∧ (Y p).ok (sc oRS 33) = true ∧ (Y p).ok (sc oRS 34) = true ∧
    (Y p).ok (sc (oRS + 32) 1) = true ∧ (Y p).ok (sc (oRS + 33) 1) = true :=
  ⟨sc_ok' ps (by decide) (by decide), sc_ok ps (by decide) (by decide), sc_ok ps (by decide) (by decide),
    sc_ok' ps (by decide) (by decide), sc_ok' ps (by decide) (by decide), sc_ok' ps (by decide) (by decide),
    sc_ok' ps (by decide) (by decide)⟩

theorem seed_bytes (ps : PS p) {s₀ : State} (hp : TPre (Y p) s₀) {m : Mem} {ρ : List Byte} {i j : Nat}
    (hρ : bytesAt m (Buf.addr s₀ (sc oRS 32)) 32 = ρ)
    (hj : bytesAt m (Buf.addr s₀ (sc (oRS + 32) 1)) 1 = [BitVec.ofNat 8 j])
    (hi : bytesAt m (Buf.addr s₀ (sc (oRS + 33) 1)) 1 = [BitVec.ofNat 8 i]) :
    bytesAt m (Buf.addr s₀ (sc oRS 34)) 34 = aSeed ρ i j := by
  obtain ⟨o1, -, -, o4, o5, o6, o7⟩ := okRS ps
  rw [addr_off hp (d := 32) o5 o6] at hj
  rw [addr_off hp (d := 33) o5 o7] at hi
  rw [show Buf.addr s₀ (sc oRS 32) = Buf.addr s₀ (sc oRS 34) from rfl] at hρ
  rw [VG.Proof.MlKem.bytesAt_add _ _ 33 1, VG.Proof.MlKem.bytesAt_add _ _ 32 1, hρ, hj, hi, aSeed,
    integerToBytes_one, integerToBytes_one]

theorem rs_hi (ps : PS p) : oRS + 34 ≤ scrLen p := by
  have := scr_ge ps; simp only [oP, oRS, nS] at this ⊢; omega_using [this]

/-- The two bytes of the seed of entry `e`. -/
theorem seedBlk_piece {P : Prims} (F : PrimsOk P) (ps : PS p) (e : Nat) (he : e < p.k * p.ℓ) :
    SP p (IA p F.rejF e) (fun s₀ s => IA p F.rejF e s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ (sc oRS 34)) 34 = seedE p s₀ e)
      (.block (st8 (oRS + 32) (e % p.ℓ) ++ st8 (oRS + 33) (e / p.ℓ))) := by
  obtain ⟨o1, w2, w3, -, -, -, -⟩ := okRS ps
  refine blk_piece (fun _ _ _ h => h.ctx) (fun s₀ s hp h => ?_) rfl
  refine wp_st8 hp h.ctx w2 _ fun s₁ c₁ f₁ b₁ => ?_
  rw [← List.append_nil (st8 (oRS + 33) (e / p.ℓ))]
  refine wp_st8 hp c₁ w3 _ fun s₂ c₂ f₂ b₂ => WP.block_nil_iff.mpr ?_
  obtain fs : ∀ o, o = oRS + 32 ∨ o = oRS + 33 → ∀ c ∈ [sc o 1], c.arg = SC ∧ oRS + 32 ≤ c.off ∧ c.off + c.len ≤ oRS + 34 ∧ 0 < c.len :=
    fun o ho c hc => by rw [List.mem_singleton] at hc; subst hc; simp only [oRS, true_and] at ho ⊢; omega_using [ho]
  obtain f := (frSc hp (M := 0) (Nat.le_refl _) (by decide) (by decide) (rs_hi ps) (fs _ (.inl rfl)) f₁).trans
    (frSc hp (M := 0) (Nat.le_refl _) (by decide) (by decide) (rs_hi ps) (fs _ (.inr rfl)) f₂)
  obtain o0 : ∀ c ∈ [sc (oRS + 32) (oRS + 34 - (oRS + 32))], Out p oOK (oOK + 4) c := by
    intro c hc; rw [List.mem_singleton] at hc; subst hc; exact ⟨sc_ok' ps (by decide) (by decide), fun _ => by decide⟩
  obtain o1' : ∀ c ∈ [sc (oRS + 32) (oRS + 34 - (oRS + 32))], Out p oRS (oRS + 32) c := by
    intro c hc; rw [List.mem_singleton] at hc; subst hc; exact ⟨sc_ok' ps (by decide) (by decide), fun _ => by decide⟩
  obtain oF : ∀ c ∈ [sc (oRS + 32) (oRS + 34 - (oRS + 32))], Out p (oP (aBase p)) (oP (aBase p + e)) c := by
    intro c hc; rw [List.mem_singleton] at hc; subst hc
    exact ⟨sc_ok' ps (by decide) (by decide), fun _ => .inl (by simp only [oP, oRS]; omega_using [])⟩
  obtain hrs : bytesAt s₂.mem (Buf.addr s₀ (sc oRS 32)) 32 = rhoS p s₀ := by rw [keepB hp (by decide) f o1 o1', h.rs]
  refine ⟨⟨c₂, hrs, by rw [scw, keepW' hp (by decide) f (sc_ok' ps (by decide) (by decide)) o0]; exact h.ok,
    fun hk => (h.fam hk).keep hp ps (by decide) f (by simp only [nS, aBase]; omega_using [he]) oF, h.bad,
    h.dk.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by decide) f (by ofsd)⟩, ?_⟩
  obtain b₁' : bytesAt s₂.mem (Buf.addr s₀ (sc (oRS + 32) 1)) 1 = [BitVec.ofNat 8 (e % p.ℓ)] := by
    rw [keepB hp (by decide) f₂ (sc_ok' ps (by decide) (by decide)) fun c hc => by
      rw [List.mem_singleton] at hc; subst hc; exact ⟨sc_ok' ps (by decide) (by decide), fun _ => .inr (Nat.le_refl _)⟩, b₁]
  exact seed_bytes ps hp hrs b₁' b₂

/-- After the call of entry `e`. -/
structure RB (p : Params) (F : List Byte → Bool) (e : Nat) (s₀ s : State) : Prop where
  ia : IA p F e s₀ s
  eax : s.gpr .eax = if F (seedE p s₀ e) then 1 else 0
  yes : F (seedE p s₀ e) = true → PolyIs s.mem (Buf.addr s₀ (pS (aBase p + e))) (aVal p s₀ e)
  no : F (seedE p s₀ e) = false → rejNTTPoly minBounds.rejNTT (seedE p s₀ e) = none

theorem rej_lay (ps : PS p) {e : Nat} (he : e < p.k * p.ℓ) :
    ((Y p).ok ⟨SC, oRS, 34⟩ && (Y p).okW ⟨SC, oP (aBase p + e), 1024⟩ && (Y p).okW ⟨SC, oPS, 2048⟩ &&
      (Y p).sep ⟨SC, oRS, 34⟩ ⟨SC, oP (aBase p + e), 1024⟩ && (Y p).sep ⟨SC, oRS, 34⟩ ⟨SC, oPS, 2048⟩ &&
      (Y p).sep ⟨SC, oP (aBase p + e), 1024⟩ ⟨SC, oPS, 2048⟩) = true := by ofsd

/-- The call of entry `e`. -/
theorem rejCall_piece {P : Prims} (F : PrimsOk P) (ps : PS p) (e : Nat) (he : e < p.k * p.ℓ) :
    SP p (fun s₀ s => IA p F.rejF e s₀ s ∧ bytesAt s.mem (Buf.addr s₀ (sc oRS 34)) 34 = seedE p s₀ e)
      (RB p F.rejF e)
      (callPR "vg_mldsa_rej_ntt_poly" P.rejNTT [.buf (sc oRS 34), .buf (pS (aBase p + e)), .buf bPS]) := by
  refine rej_piece F.rejNTT (F.ok _ (by simp)) SC oRS SC (oP (aBase p + e)) SC oPS (rej_lay ps he)
    (fun _ _ _ h => h.1.ctx) (fun s₀ s₀' s s' hp hp' hq h h' => by
      rw [h.2, h'.2]; show aSeed (rhoS p s₀) _ _ = aSeed (rhoS p s₀') _ _; rw [rhoS_eq ps hq])
    fun s₀ s s' hp ⟨h, hs⟩ c' fr heax hred hout => ?_
  rw [hs] at heax hout
  obtain hj : aBase p + e < nS p := by simp only [nS, aBase]; omega_using [he]
  refine ⟨⟨c', by rw [keepB hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofsd), h.rs],
    by rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofsd)]; exact h.ok,
    fun hk => (h.fam hk).keep hp ps (by decide) fr (by omega_using [hj]) (by ofsd), h.bad,
    h.dk.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by decide) fr (by ofsd)⟩, heax, fun hy => ?_, fun hn => ?_⟩
  · rw [hy] at heax; simp only [↓reduceIte] at heax
    refine ⟨hred heax, ?_⟩
    rw [rej_val hout heax (F.rejMax _ hy)]
    rfl
  · rw [hn] at heax
    rcases hout with ⟨h1, _⟩ | ⟨_, h0⟩
    · rw [heax] at h1; cases h1
    · exact h0

/-- `OK ← OK ∧ eax` after the call of entry `e`. -/
theorem rejAnd_piece {P : Prims} (F : PrimsOk P) (ps : PS p) (e : Nat) (he : e < p.k * p.ℓ) :
    SP p (RB p F.rejF e) (IA p F.rejF (e + 1)) (.block andOK) := by
  refine blk_piece (fun _ _ _ h => h.ia.ctx) (fun s₀ s hp h => wp_andOK hp h.ia.ctx ps fun s' c' fr ok' => ?_) rfl
  obtain hj : aBase p + e < nS p := by simp only [nS, aBase]; omega_using [he]
  obtain fr' := fr0 hp (N := 80) (by decide) fr
  obtain hfam : okE p F.rejF s₀ e = true → Fam s₀ s'.mem (aBase p) e (aVal p s₀) := fun hk =>
    (h.ia.fam hk).keep hp ps (by decide) fr' (by omega_using [hj]) (by ofsd)
  refine ⟨c', by rw [keepB hp (by decide) fr' (sc_ok' ps (by decide) (by decide)) (by ofsd), h.ia.rs], ?_, fun hk => ?_, fun hk => ?_,
    h.ia.dk.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by decide) fr' (by ofsd)⟩
  · rw [ok', h.ia.ok, h.eax, and01, okE_succ]
  · rw [okE_succ, Bool.and_eq_true] at hk
    exact (hfam hk.1).snoc (keepP hp ps (by decide) fr' hj (by ofsd) (h.yes hk.2))
  · rw [okE_succ, Bool.and_eq_false_iff] at hk
    rcases hk with hk | hk
    · obtain ⟨e', he', hn⟩ := h.ia.bad hk
      exact ⟨e', by omega_using [he'], hn⟩
    · exact ⟨e, by omega_using [], h.no hk⟩

theorem aP_slot {e : Nat} : aP p (e / p.ℓ) (e % p.ℓ) = pS (aBase p + e) := by
  rw [aP_eq, Nat.div_add_mod]

/-- Entry `e` of `Â`. -/
theorem sampleE_piece {P : Prims} (F : PrimsOk P) (ps : PS p) (e : Nat) (he : e < p.k * p.ℓ) :
    SP p (IA p F.rejF e) (IA p F.rejF (e + 1)) (sampleE P p e) := by
  unfold sampleE rejAt
  rw [aP_slot]
  exact (seedBlk_piece F ps e he).seq ((rejCall_piece F ps e he).seq (rejAnd_piece F ps e he))

/-- `ρ` to `RS`, and `Â`. -/
theorem expandA_piece {P : Prims} (F : PrimsOk P) (ps : PS p) :
    SP p (fun s₀ s => Ctx (Y p) s₀ s ∧ scw s₀ s oOK = 1 ∧ DKs p p.ℓ p.k p.k s₀ s.mem) (IA p F.rejF (p.k * p.ℓ))
      (Impl.MlDsa.X86.Sign.expandA P p) := by
  unfold Impl.MlDsa.X86.Sign.expandA
  refine Piece.seq (B := IA p F.rejF 0) (copy_piece 0 0 SC oRS 8 (by decide) (by decide) (by ofsd)
    (fun _ _ _ h => h.1) fun s₀ s s' hp h c' fr hb => ?_)
    (by simpa using seqR_piece (I := IA p F.rejF) 0 (p.k * p.ℓ) fun e _ he => sampleE_piece F ps e (by omega_using [he]))
  obtain fr' : Frame (FR s₀ [sc oRS 32] 80) s.mem s'.mem := fr.mono (by simp)
  refine ⟨c', ?_, ?_, fun _ j hj => absurd hj (Nat.not_lt_zero _), fun hk => absurd hk (by simp [okE]),
    h.2.2.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by decide) fr' (by ofsd)⟩
  · show bytesAt s'.mem (Buf.addr s₀ ⟨SC, oRS, 4 * 8⟩) (4 * 8) = _
    rw [hb, h.1.roBytes hp (b := ⟨0, 0, 4 * 8⟩) (by ofsd) rfl]
    exact (VG.Proof.MlKem.bytesAt_take _ _ (skLen_ge ps)).symm
  · rw [scw, keepW' hp (by decide) fr' (sc_ok' ps (by decide) (by decide)) (by ofsd)]
    simp [okE, h.2.1]

end VG.Proof.MlDsa.X86.Sign

end

end


/-!
# ML-DSA signing on x86 (32-bit): the private key, and `ρ″`

`ŝ₁`, `ŝ₂` and `t̂₀` are the `NTT` of the `BitUnpack` of their pieces of `sk`
(`decOne_piece`), in the slots from `s1B`, `s2B` and `t0B`, next to `Â`
(`DK`); then `K ‖ rnd` is copied to `HIN`, and `ρ″ = H(K ‖ rnd ‖ μ, 64)`
hashed to `MS` (`KD`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_ copyW)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params}

section
variable (p : Params)

/-- `ρ″`, from the initial state. -/
abbrev rppS (s₀ : State) : List Byte := rppV (skOf p s₀) (muOf s₀) (rndOf s₀)

/-- `Â`, and the first `n1`, `n2` and `n0` polynomials of `ŝ₁`, `ŝ₂` and `t̂₀`. -/
structure DK (n1 n2 n0 : Nat) (s₀ : State) (m : Mem) : Prop where
  fa : Fam s₀ m (aBase p) (p.k * p.ℓ) (aVal p s₀)
  f1 : Fam s₀ m (s1B p) n1 (S1 p s₀)
  f2 : Fam s₀ m (s2B p) n2 (S2 p s₀)
  f0 : Fam s₀ m (t0B p) n0 (T0 p s₀)

/-- What the loop needs of the setup. -/
structure KD (s₀ s : State) : Prop where
  ctx : Ctx (Y p) s₀ s
  dk : DK p p.ℓ p.k p.k s₀ s.mem
  ms : bytesAt s.mem (Buf.addr s₀ (sc oMS 64)) 64 = rppS p s₀

end

theorem DK.keep {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {n1 n2 n0 : Nat} (h1 : n1 ≤ p.ℓ) (h2 : n2 ≤ p.k)
    (h0 : n0 ≤ p.k) {bs : List Buf} {N : Nat} (hN : N ≤ 80) {m m' : Mem} (fr : Frame (FR s₀ bs N) m m')
    (h : ∀ c ∈ bs, OutK p n1 n2 n0 c) (d : DK p n1 n2 n0 s₀ m) : DK p n1 n2 n0 s₀ m' :=
  ⟨d.fa.keep hp ps hN fr (by simp only [nS, aBase]; omega_arith) fun c hc => (h c hc).1,
    d.f1.keep hp ps hN fr (by simp only [nS, s1B]; omega_arith) fun c hc => (h c hc).2.1,
    d.f2.keep hp ps hN fr (by simp only [nS, s2B]; omega_arith) fun c hc => (h c hc).2.2.1,
    d.f0.keep hp ps hN fr (by simp only [nS, t0B]; omega_arith) fun c hc => (h c hc).2.2.2⟩

/-! ## A polynomial of the private key -/

/-- The bytes `sk[o : o + l]`. -/
theorem sk_slice {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {o l : Nat} (hol : o + l ≤ p.skLen)
    (hl : 0 < l) : bytesAt s.mem (Buf.addr s₀ (bSk o l)) l = ((skOf p s₀).drop o).take l := by
  obtain ok : (Y p).ok (bSk o l) = true :=
    Lay.ok_iff.mpr ⟨by rw [Y_n]; exact (by decide : 0 < 5), hl, by rw [Y_alen0]; exact hol⟩
  obtain ok0 : (Y p).ok (bSk 0 p.skLen) = true :=
    Lay.ok_iff.mpr ⟨by rw [Y_n]; exact (by decide : 0 < 5), by show 0 < p.skLen; omega_arith,
      by rw [Y_alen0]; show 0 + p.skLen ≤ p.skLen; omega_arith⟩
  rw [h.roBytes hp ok rfl, VG.Proof.MlKem.bytesAt_slice _ _ hol, Buf.addr_eq hp ok, Buf.addr_eq hp ok0]
  simp only [BitVec.add_zero]

/-- `f ← NTT(BitUnpack(sk[o : o + len], a, b))`, in slot `j`. -/
theorem decOne_piece {P : Prims} (F : PrimsOk P) (ps : PS p) {A B : State → State → Prop} (j o len a b : Nat)
    (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hs : a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ len < 2 ^ 32)
    (hj : j < nS p) (hol : o + len ≤ p.skLen) (hlen : 0 < len)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s)
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' →
      Frame (FR s₀ [pS j, sc oPS 1024] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ (pS j)) (ntt (toRq (bitUnpack (((skOf p s₀).drop o).take len) a b))) → B s₀ s') :
    SP p A B (.seq (bitUnpackAt P (bSk o len) a b (pS j)) (nttAt P (pS j))) := by
  obtain hc : ((Y p).ok ⟨0, o, len⟩ && (Y p).okW ⟨SC, oP j, 1024⟩ && (Y p).sep ⟨0, o, len⟩ ⟨SC, oP j, 1024⟩) = true := by
    have := slot_ok ps hj
    simp only [Bool.and_eq_true, this, and_true]
    exact ⟨Lay.ok_iff.mpr ⟨by rw [Y_n]; exact (by decide : 0 < 5), hlen, by rw [Y_alen0]; exact hol⟩, Lay.sep_iff.mpr (.inr ⟨by simp, .inr rfl⟩)⟩
  refine Piece.seq (B := fun s₀ s₁ => ∃ s, A s₀ s ∧ Ctx (Y p) s₀ s₁ ∧ Frame (FR s₀ [pS j, sc oPS 1024] 80) s.mem s₁.mem ∧
      PolyIs s₁.mem (Buf.addr s₀ (pS j)) (toRq (bitUnpack (((skOf p s₀).drop o).take len) a b)))
    (bu_piece F.bitUnpack (F.ok _ (by simp)) a b len hab hl hs 0 o SC (oP j) hc hA
      fun s₀ s s' hp ha c' fr hq => ⟨s, ha, c', fr.mono (by simp), by rw [← sk_slice hp (hA _ _ hp ha) hol hlen]; exact hq⟩) ?_
  refine inPlace_piece (t := ntt) F.ntt (F.ok _ (by simp)) (pS j) rfl (by
      have := slot_ok ps hj; have := sc_ok ps (o := oPS) (n := 1024) (by decide) (by decide)
      simp only [Bool.and_eq_true, *, true_and]; ofsd)
    (fun s₀ s₁ hp ⟨_, _, c, _, hq⟩ => ⟨c, hq.1⟩) fun s₀ s₁ s' hp ⟨s, ha, c, fr, hq⟩ c' fr' post => ?_
  rw [hq.2] at post
  exact hQ s₀ s s' hp ha c' (fr.trans fr') post

/-! ## The private key -/

theorem ps_sk (ps : PS p) : sLen p * p.ℓ + sLen p * p.k + 416 * p.k + 128 = p.skLen := by
  rw [ps.hskLen, Nat.mul_add]; omega_arith

theorem ps_sLen (ps : PS p) : 0 < sLen p ∧ sLen p < 2 ^ 32 := by rcases ps.hsLen with h | h <;> omega_arith

/-- `ŝ₁`. -/
theorem decS1s_piece {P : Prims} (F : PrimsOk P) (ps : PS p) :
    SP p (fun s₀ s => Ctx (Y p) s₀ s ∧ DKs p 0 0 0 s₀ s.mem) (fun s₀ s => Ctx (Y p) s₀ s ∧ DKs p p.ℓ 0 0 s₀ s.mem)
      (seqR (decS1 P p) 0 p.ℓ) := by
  have := seqR_piece (p := p) (f := decS1 P p) (I := fun r s₀ s => Ctx (Y p) s₀ s ∧ DKs p r 0 0 s₀ s.mem) 0 p.ℓ
    fun r _ hr => by
      obtain hl := ps_sLen ps
      obtain hk := ps_sk ps
      obtain hr' : r < p.ℓ := by omega_arith
      obtain hmul : sLen p * r + sLen p ≤ sLen p * p.ℓ := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr'
      exact decOne_piece F ps (s1B p + r) (skS1 p r) (sLen p) p.η p.η ps.hη.1 ps.hη.2.1
        ⟨ps.hη.2.2, ps.hη.2.2, hl.2⟩ (by simp only [nS, s1B]; omega_arith) (by simp only [skS1]; omega_arith) hl.1
        (fun _ _ _ h => h.1) fun s₀ s s' hp h c' fr hq => ⟨c',
          { (h.2.keep hp ps (by omega_arith) (by omega_arith) (by omega_arith) (by decide) fr (by ofsd)) with
            f1 := (h.2.f1.keep hp ps (by decide) fr (by simp only [nS, s1B]; omega_arith) (by ofsd)).snoc hq }⟩
  simpa using this

/-- `ŝ₂`. -/
theorem decS2s_piece {P : Prims} (F : PrimsOk P) (ps : PS p) :
    SP p (fun s₀ s => Ctx (Y p) s₀ s ∧ DKs p p.ℓ 0 0 s₀ s.mem) (fun s₀ s => Ctx (Y p) s₀ s ∧ DKs p p.ℓ p.k 0 s₀ s.mem)
      (seqR (decS2 P p) 0 p.k) := by
  have := seqR_piece (p := p) (f := decS2 P p) (I := fun r s₀ s => Ctx (Y p) s₀ s ∧ DKs p p.ℓ r 0 s₀ s.mem) 0 p.k
    fun r _ hr => by
      obtain hl := ps_sLen ps
      obtain hk := ps_sk ps
      obtain hr' : r < p.k := by omega_arith
      obtain hmul : sLen p * r + sLen p ≤ sLen p * p.k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr'
      exact decOne_piece F ps (s2B p + r) (skS2 p r) (sLen p) p.η p.η ps.hη.1 ps.hη.2.1
        ⟨ps.hη.2.2, ps.hη.2.2, hl.2⟩ (by simp only [nS, s2B]; omega_arith) (by simp only [skS2]; omega_arith) hl.1
        (fun _ _ _ h => h.1) fun s₀ s s' hp h c' fr hq => ⟨c',
          { (h.2.keep hp ps (Nat.le_refl _) (by omega_arith) (by omega_arith) (by decide) fr (by ofsd)) with
            f2 := (h.2.f2.keep hp ps (by decide) fr (by simp only [nS, s2B]; omega_arith) (by ofsd)).snoc hq }⟩
  simpa using this

theorem t0F_eq (sk : List Byte) (i : Nat) :
    t0F p sk i = ntt (toRq (bitUnpack ((sk.drop (skT0 p i)).take 416) 4095 4096)) := by
  unfold t0F
  rw [show 128 + lenS p * p.ℓ + lenS p * p.k + 32 * d * i = skT0 p i by
    simp only [skT0, lenS, sLen, Nat.mul_add, d]; omega_arith]
  rfl

/-- `t̂₀`. -/
theorem decT0s_piece {P : Prims} (F : PrimsOk P) (ps : PS p) :
    SP p (fun s₀ s => Ctx (Y p) s₀ s ∧ DKs p p.ℓ p.k 0 s₀ s.mem) (fun s₀ s => Ctx (Y p) s₀ s ∧ DKs p p.ℓ p.k p.k s₀ s.mem)
      (seqR (decT0 P p) 0 p.k) := by
  have := seqR_piece (p := p) (f := decT0 P p) (I := fun r s₀ s => Ctx (Y p) s₀ s ∧ DKs p p.ℓ p.k r s₀ s.mem) 0 p.k
    fun r _ hr => by
      obtain hk := ps_sk ps
      obtain hr' : r < p.k := by omega_arith
      obtain hmul : 416 * r + 416 ≤ 416 * p.k := by omega_arith
      exact decOne_piece F ps (t0B p + r) (skT0 p r) 416 4095 4096 ps.ht0.1 ps.ht0.2
        ⟨by decide, by decide, by decide⟩ (by simp only [nS, t0B]; omega_arith) (by simp only [skT0, Nat.mul_add]; omega_arith) (by decide)
        (fun _ _ _ h => h.1) fun s₀ s s' hp h c' fr hq => ⟨c',
          { (h.2.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (by omega_arith) (by decide) fr (by ofsd)) with
            f0 := (h.2.f0.keep hp ps (by decide) fr (by simp only [nS, t0B]; omega_arith) (by ofsd)).snoc
              (by show PolyIs _ _ (t0F p _ r); rw [t0F_eq]; exact hq) }⟩
  simpa using this

/-! ## `ρ″` -/

/-- `ρ″ = H(K ‖ rnd ‖ μ, 64)`, with `K ‖ rnd` copied to `HIN` first. -/
theorem rpp_piece (ps : PS p) :
    SP p (fun s₀ s => Ctx (Y p) s₀ s ∧ DK p p.ℓ p.k p.k s₀ s.mem) (KD p) rpp := by
  unfold rpp
  obtain hk := ps_sk ps
  refine Piece.seq (B := fun s₀ s => Ctx (Y p) s₀ s ∧ DK p p.ℓ p.k p.k s₀ s.mem ∧
      bytesAt s.mem (Buf.addr s₀ (sc oHIN 32)) 32 = ((skOf p s₀).drop 32).take 32)
    (copy_piece 0 32 SC oHIN 8 (by decide) (by decide) (by ofsd) (fun _ _ _ h => h.1)
      fun s₀ s s' hp h c' fr hb => ⟨c', h.2.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (N := 80)
        (by decide) (show Frame (FR s₀ [sc oHIN 32] 80) s.mem s'.mem from fr.mono (by simp)) (by ofsd), by
          show bytesAt s'.mem (Buf.addr s₀ ⟨SC, oHIN, 4 * 8⟩) (4 * 8) = _
          rw [hb]; exact sk_slice hp h.1 (by omega_arith) (by decide)⟩) ?_
  refine Piece.seq (B := fun s₀ s => Ctx (Y p) s₀ s ∧ DK p p.ℓ p.k p.k s₀ s.mem ∧
      bytesAt s.mem (Buf.addr s₀ (sc oHIN 64)) 64 = ((skOf p s₀).drop 32).take 32 ++ rndOf s₀)
    (copy_piece 2 0 SC (oHIN + 32) 8 (by decide) (by decide) (by ofsd) (fun _ _ _ h => h.1)
      fun s₀ s s' hp h c' fr hb => ⟨c', h.2.1.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (N := 80)
        (by decide) (show Frame (FR s₀ [sc (oHIN + 32) 32] 80) s.mem s'.mem from fr.mono (by simp)) (by ofsd), by
          rw [bytes_split hp s'.mem (o' := oHIN + 32) (l₁ := 32) (l₂ := 32) rfl rfl (sc_ok' ps (by decide) (by decide))
            (sc_ok' ps (by decide) (by decide)), keepB hp (N := 80) (by decide) (show Frame (FR s₀ [sc (oHIN + 32) 32] 80) s.mem s'.mem from fr.mono (by simp))
            (sc_ok' ps (by decide) (by decide)) (by ofsd), h.2.2]
          have : bytesAt s'.mem (Buf.addr s₀ ⟨SC, oHIN + 32, 4 * 8⟩) (4 * 8) = _ := hb
          rw [this, h.1.roBytes hp (b := ⟨2, 0, 4 * 8⟩) (by ofsd) rfl]⟩) ?_
  refine hash2_piece' 136 0x1f (sc oHIN 64) bMu (sc oMS 64) (by decide) (by ofsd) (by decide) (by decide) (by decide)
    (fun _ _ _ h => h.1) fun s₀ s s' hp h c' fr hb => ⟨c', h.2.1.keep hp ps (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (by decide) fr (by ofsd), ?_⟩
  obtain e : BitVec.setWidth 8 (31#32) = Spec.Sha3.shakeSuffix := by decide
  rw [hb, h.2.2, h.1.roBytes hp (b := bMu) (by ofsd) rfl, e, rppS, rppV, VG.Proof.MlDsa.Sample.H_eq]

/-- The private key's polynomials. -/
theorem keys_piece {P : Prims} (F : PrimsOk P) (ps : PS p) :
    SP p (fun s₀ s => Ctx (Y p) s₀ s ∧ DKs p 0 0 0 s₀ s.mem) (fun s₀ s => Ctx (Y p) s₀ s ∧ DKs p p.ℓ p.k p.k s₀ s.mem)
      (keys P p) :=
  (decS1s_piece F ps).seq ((decS2s_piece F ps).seq (decT0s_piece F ps))

end VG.Proof.MlDsa.X86.Sign

end

end


/-!
# ML-DSA signing on x86 (32-bit): the commitment of an iteration

Iteration `t` of the loop (`IT`: the setup, `κ = ℓt` at `KAP` and `814 - t` at
`CNT`) computes `y = ExpandMask(ρ″, κ)` and `ŷ = NTT(y)` (`maskR_piece`), `w =
NTT⁻¹(Â ŷ)` (`rowW_piece`), the encoding of `w₁ = HighBits(w)` at `W1`
(`w1R_piece`), and `c̃ = H(μ ‖ w1Encode(w₁), λ/4)` at `CT` (`commit_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_ copyW)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_shr)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params}

section
variable (p : Params)

/-- `Â`, `y`, `ŷ`, `w` and `c̃` of the iteration with counter `κ`. -/
abbrev Am (s₀ : State) : Nat → Nat → Poly := Av (skOf p s₀)
abbrev Yv (s₀ : State) (κ r : Nat) : Poly := toRq (yF p (rppS p s₀) κ r)
abbrev YHv (s₀ : State) (κ r : Nat) : Poly := yhF p (rppS p s₀) κ r
abbrev Wv (s₀ : State) (κ i : Nat) : Poly := wF p (Am p s₀) (rppS p s₀) κ i
abbrev CTv (s₀ : State) (κ : Nat) : List Byte := ctF p (Am p s₀) (muOf s₀) (rppS p s₀) κ

/-- Iteration `t`, on entry. -/
structure IT (t : Nat) (s₀ s : State) : Prop where
  kd : KD p s₀ s
  kap : scw s₀ s oKAP = BitVec.ofNat 32 (p.ℓ * t)
  cnt : scw s₀ s oCNT = BitVec.ofNat 32 (814 - t)
  lt : t < 814

end

theorem IT.keep {t : Nat} {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : IT p t s₀ s)
    (c' : Ctx (Y p) s₀ s') {bs : List Buf} {N : Nat} (hN : N ≤ 80) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (hb : ∀ c ∈ bs, OutI p c) : IT p t s₀ s' :=
  ⟨⟨c', h.kd.dk.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hN fr fun c hc => (hb c hc).1,
    by rw [keepB hp hN fr (sc_ok' ps (by decide) (by decide)) fun c hc => (hb c hc).2.2, h.kd.ms]⟩,
    by rw [scw, keepW' hp hN fr (sc_ok' ps (by decide) (by decide)) fun c hc => ⟨(hb c hc).2.1.1, fun e => by
      have := (hb c hc).2.1.2 e; simp only [oCNT, oKAP] at this ⊢; omega_arith⟩]; exact h.kap,
    by rw [scw, keepW' hp hN fr (sc_ok' ps (by decide) (by decide)) fun c hc => ⟨(hb c hc).2.1.1, fun e => by
      have := (hb c hc).2.1.2 e; simp only [oCNT, oKAP] at this ⊢; omega_arith⟩]; exact h.cnt, h.lt⟩

theorem aVal_ij {s₀ : State} {i j : Nat} (hj : j < p.ℓ) : aVal p s₀ (p.ℓ * i + j) = Am p s₀ i j := by
  obtain hl : 0 < p.ℓ := by omega_arith
  obtain e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  obtain e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [aVal, e1, e2]

/-! ## `y` and `ŷ` -/

theorem integerToBytes_two (x : Nat) : integerToBytes x 2 = [BitVec.ofNat 8 x, BitVec.ofNat 8 (x / 256)] := by
  simp [integerToBytes, List.range_succ]

theorem kap_lt (ps : PS p) {t r : Nat} (ht : t < 814) (hr : r < p.ℓ) : p.ℓ * t + r < 2 ^ 16 := by
  have := ps.hl
  have : p.ℓ * t ≤ 7 * 813 := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  omega_arith

/-- Iteration `t`, with the first `r` polynomials of `y` and `ŷ`. -/
structure CM (p : Params) (t r : Nat) (s₀ s : State) : Prop where
  it : IT p t s₀ s
  fy : Fam s₀ s.mem (yB p) r (Yv p s₀ (p.ℓ * t))
  fyh : Fam s₀ s.mem (yhB p) r (YHv p s₀ (p.ℓ * t))

/-- `κ + r` to `MS + 64`: the seed of `y[r]` at `MS`. -/
theorem setKappa_piece (ps : PS p) (t r : Nat) (hr : r < p.ℓ) :
    SP p (CM p t r) (fun s₀ s => CM p t r s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ (sc oMS 66)) 66 = rppS p s₀ ++ integerToBytes (p.ℓ * t + r) 2)
      (.block (setKappa r)) := by
  refine blk_piece (fun _ _ _ h => h.it.kd.ctx) (fun s₀ s hp hc => ?_) rfl
  have h := hc.it
  obtain hk := kap_lt ps h.lt hr
  unfold setKappa
  refine wp_ldsc hp h.kd.ctx (sc_ok' ps (by decide) (by decide)) fun s₁ o₁ v₁ => wp_addi fun s₂ o₂ v₂ => ?_
  obtain c₂ := h.kd.ctx.only (o₁.trans o₂) (by simp) (by simp)
  refine wp_st8sc hp c₂ (sc_ok ps (by decide) (by decide)) fun s₃ c₃ g₃ m₃ => wp_shr (by decide) (by decide)
    fun s₄ o₄ v₄ => ?_
  obtain c₄ := c₃.only o₄ (by simp) (by simp)
  refine wp_st8sc hp c₄ (sc_ok ps (by decide) (by decide)) fun s₅ c₅ g₅ m₅ => WP.block_nil_iff.mpr ?_
  obtain ex : s₂.gpr .eax = BitVec.ofNat 32 (p.ℓ * t + r) := by
    rw [v₂, v₁, h.kap, BitVec.ofNat_add]
  obtain fr₃ : Frame (FR s₀ [sc (oMS + 64) 1] 0) s.mem s₃.mem := by
    rw [m₃, ← (o₁.trans o₂).mem]; exact frW8 (Y := Y p)
  obtain fr₅ : Frame (FR s₀ [sc (oMS + 65) 1] 0) s₃.mem s₅.mem := by
    rw [m₅, ← o₄.mem]; exact frW8 (Y := Y p)
  obtain fs : ∀ o, o = oMS + 64 ∨ o = oMS + 65 → ∀ c ∈ [sc o 1], c.arg = SC ∧ oMS + 64 ≤ c.off ∧
      c.off + c.len ≤ oMS + 66 ∧ 0 < c.len :=
    fun o ho c hc => by rw [List.mem_singleton] at hc; subst hc; simp only [oMS, true_and] at ho ⊢; omega_arith
  obtain hhi : oMS + 66 ≤ scrLen p := by have := scr_ge ps; simp only [oP, oMS, nS] at this ⊢; omega_arith
  obtain f := (frSc hp (M := 80) (by decide) (by decide) (by decide) hhi (fs _ (.inl rfl)) fr₃).trans
    (frSc hp (M := 80) (by decide) (by decide) (by decide) hhi (fs _ (.inr rfl)) fr₅)
  refine ⟨⟨h.keep hp ps c₅ (by decide) f (by ofsd), hc.fy.keep hp ps (by decide) f (by simp only [nS, yB]; omega_arith) (by ofsd),
    hc.fyh.keep hp ps (by decide) f (by simp only [nS, yhB]; omega_arith) (by ofsd)⟩, ?_⟩
  obtain b0 : bytesAt s₃.mem (Buf.addr s₀ (sc (oMS + 64) 1)) 1 = [BitVec.ofNat 8 (p.ℓ * t + r)] := by
    rw [m₃, bytes1_write]; show [(s₂.gpr .eax).setWidth 8] = _; rw [ex, setWidth8_ofNat]
  obtain b0' : bytesAt s₅.mem (Buf.addr s₀ (sc (oMS + 64) 1)) 1 = [BitVec.ofNat 8 (p.ℓ * t + r)] := by
    rw [keepB hp (by decide) fr₅ (sc_ok' ps (by decide) (by decide)) fun c hc => by
      rw [List.mem_singleton] at hc; subst hc; exact ⟨sc_ok' ps (by decide) (by decide), fun _ => .inr (Nat.le_refl _)⟩, b0]
  obtain b1 : bytesAt s₅.mem (Buf.addr s₀ (sc (oMS + 65) 1)) 1 = [BitVec.ofNat 8 ((p.ℓ * t + r) / 256)] := by
    rw [m₅, bytes1_write]; show [(s₄.gpr .eax).setWidth 8] = _; rw [v₄, g₃, ex]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
    omega_arith
  obtain hm : bytesAt s₅.mem (Buf.addr s₀ (sc oMS 64)) 64 = rppS p s₀ := by
    rw [keepB hp (by decide) f (sc_ok' ps (by decide) (by decide)) (by ofsd), h.kd.ms]
  rw [bytes_split hp s₅.mem (o' := oMS + 64) (l₁ := 64) (l₂ := 2) rfl rfl (sc_ok' ps (by decide) (by decide))
    (sc_ok' ps (by decide) (by decide)), hm,
    bytes_split hp s₅.mem (o' := oMS + 65) (l₁ := 1) (l₂ := 1) rfl rfl (sc_ok' ps (by decide) (by decide))
    (sc_ok' ps (by decide) (by decide)), b0', b1, integerToBytes_two]
  rfl

/-- `y[r]` and `ŷ[r]`. -/
theorem maskR_piece {P : Prims} (F : PrimsOk P) (ps : PS p) (t r : Nat) (hr : r < p.ℓ) :
    SP p (CM p t r) (CM p t (r + 1)) (maskR P p r) := by
  obtain hj : yB p + r < nS p := by simp only [nS, yB]; omega_arith
  obtain hj' : yhB p + r < nS p := by simp only [nS, yhB]; omega_arith
  refine (setKappa_piece ps t r hr).seq ?_
  refine Piece.seq (B := fun s₀ s => CM p t r s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS (yB p + r))) (Yv p s₀ (p.ℓ * t) r))
    (mask_piece F.expandMask (F.ok _ (by simp)) p.γ₁ ps.hγ₁ SC oMS SC (oP (yB p + r)) SC oPS (by ofsd)
      (fun _ _ _ h => h.1.it.kd.ctx) fun s₀ s s' hp h c' fr hq => ⟨⟨h.1.it.keep hp ps c' (by decide) fr (by ofsd),
        h.1.fy.keep hp ps (by decide) fr (by simp only [nS, yB]; omega_arith) (by ofsd),
        h.1.fyh.keep hp ps (by decide) fr (by simp only [nS, yhB]; omega_arith) (by ofsd)⟩, by rw [h.2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => CM p t r s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS (yB p + r))) (Yv p s₀ (p.ℓ * t) r) ∧
      PolyIs s.mem (Buf.addr s₀ (pS (yhB p + r))) (Yv p s₀ (p.ℓ * t) r))
    (copy_piece SC (oP (yB p + r)) SC (oP (yhB p + r)) 256 (by decide) (by decide) (by ofsd)
      (fun _ _ _ h => h.1.it.kd.ctx) fun s₀ s s' hp h c' fr hb => ?_) ?_
  · have fr' : Frame (FR s₀ [pS (yhB p + r)] 80) s.mem s'.mem := fr.mono (by simp)
    exact ⟨⟨h.1.it.keep hp ps c' (by decide) fr' (by ofsd),
      h.1.fy.keep hp ps (by decide) fr' (by simp only [nS, yB]; omega_arith) (by ofsd),
      h.1.fyh.keep hp ps (by decide) fr' (by simp only [nS, yhB]; omega_arith) (by ofsd)⟩,
      keepP hp ps (by decide) fr' hj (by ofsd) h.2, polyIs_of_bytes hb h.2⟩
  refine inPlace_piece (t := ntt) F.ntt (F.ok _ (by simp)) (pS (yhB p + r)) rfl (by ofsd)
    (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.2.1⟩) fun s₀ s s' hp h c' fr hq => ?_
  rw [h.2.2.2] at hq
  exact ⟨h.1.it.keep hp ps c' (by decide) fr (by ofsd),
    (h.1.fy.keep hp ps (by decide) fr (by simp only [nS, yB]; omega_arith) (by ofsd)).snoc (keepP hp ps (by decide) fr hj (by ofsd) h.2.1),
    (h.1.fyh.keep hp ps (by decide) fr (by simp only [nS, yhB]; omega_arith) (by ofsd)).snoc hq⟩

/-! ## `w` -/

/-- `∑_{j < m} Â[i, j] ŷ[j]`, summed from `j = 0` with `AddNTT`. -/
abbrev wAcc (p : Params) (s₀ : State) (κ i m : Nat) : Poly :=
  ((List.range m).map fun j => multiplyNTT (Am p s₀ i j) (YHv p s₀ κ j)).foldl add zero

theorem add_zero_left (x : Poly) : add zero x = x := by
  apply Vector.ext
  intro j hj
  simp [add, zero]

theorem wAcc_one (s₀ : State) (κ i : Nat) :
    wAcc p s₀ κ i 1 = multiplyNTT (Am p s₀ i 0) (YHv p s₀ κ 0) := by
  simp only [wAcc, List.range_one, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, add_zero_left]

theorem wAcc_succ (s₀ : State) (κ i m : Nat) :
    wAcc p s₀ κ i (m + 1) = add (wAcc p s₀ κ i m) (multiplyNTT (Am p s₀ i m) (YHv p s₀ κ m)) := by
  simp only [wAcc, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- Iteration `t`, with `y`, `ŷ` and the first `i` polynomials of `w`. -/
structure CW (p : Params) (t i : Nat) (s₀ s : State) : Prop where
  cm : CM p t p.ℓ s₀ s
  fw : Fam s₀ s.mem (wB p) i (Wv p s₀ (p.ℓ * t))

theorem CW.keep {t i : Nat} {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CW p t i s₀ s) (hi : i ≤ p.k)
    (c' : Ctx (Y p) s₀ s') {bs : List Buf} {N : Nat} (hN : N ≤ 80) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (hb : ∀ c ∈ bs, OutI p c ∧ Out p (oP (yB p)) (oP (wB p + i)) c) : CW p t i s₀ s' :=
  ⟨⟨h.cm.it.keep hp ps c' hN fr fun c hc => (hb c hc).1,
    h.cm.fy.keep hp ps hN fr (by simp only [nS, yB]; omega_arith) fun c hc => ⟨(hb c hc).2.1, fun e => by
      have := (hb c hc).2.2 e; simp only [oP, yB, wB] at this ⊢; omega_arith⟩,
    h.cm.fyh.keep hp ps hN fr (by simp only [nS, yhB]; omega_arith) fun c hc => ⟨(hb c hc).2.1, fun e => by
      have := (hb c hc).2.2 e; simp only [oP, yB, yhB, wB] at this ⊢; omega_arith⟩⟩,
    h.fw.keep hp ps hN fr (by simp only [nS, wB]; omega_arith) fun c hc => ⟨(hb c hc).2.1, fun e => by
      have := (hb c hc).2.2 e; simp only [oP, yB, wB] at this ⊢; omega_arith⟩⟩

theorem fam_at {s₀ : State} {m : Mem} {b n : Nat} {f : Nat → Poly} (h : Fam s₀ m b n f) {j : Nat} (hj : j < n) :
    PolyIs m (Buf.addr s₀ (pS (b + j))) (f j) := h j hj

/-- `w[i]`. -/
theorem rowW_piece {P : Prims} (F : PrimsOk P) (ps : PS p) (t i : Nat) (hi : i < p.k) :
    SP p (CW p t i) (CW p t (i + 1)) (rowW P p i) := by
  have hl := ps.hl
  obtain hj : wB p + i < nS p := by simp only [nS, wB]; omega_arith
  obtain ha : ∀ j < p.ℓ, p.ℓ * i + j < p.k * p.ℓ := fun j hj => aIdx hi hj
  unfold rowW
  simp only [aP_eq]
  refine Piece.seq (B := fun s₀ s => CW p t i s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS (wB p + i))) (wAcc p s₀ (p.ℓ * t) i 1))
    (mul_piece F.mul (F.ok _ (by simp)) SC (oP (wB p + i)) SC (oP (aBase p + (p.ℓ * i + 0))) SC (oP (yhB p + 0))
      (by have := ha 0 (by omega_arith); ofsd)
      (fun _ _ _ h => ⟨h.cm.it.kd.ctx, (fam_at h.cm.it.kd.dk.fa (ha 0 (by omega_arith))).1, (fam_at h.cm.fyh (by omega_arith)).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps (by omega_arith) c' (by decide) fr (by ofsd), ?_⟩) ?_
  · rw [(fam_at h.cm.it.kd.dk.fa (ha 0 (by omega_arith))).2, (fam_at h.cm.fyh (by omega_arith)).2, aVal_ij (by omega_arith)] at hq
    rw [wAcc_one]; exact hq
  refine Piece.seq (B := fun s₀ s => CW p t i s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS (wB p + i))) (wAcc p s₀ (p.ℓ * t) i p.ℓ))
    ?_ ?_
  · have := seqR_piece (p := p) (I := fun j s₀ s => CW p t i s₀ s ∧
        PolyIs s.mem (Buf.addr s₀ (pS (wB p + i))) (wAcc p s₀ (p.ℓ * t) i j)) 1 (p.ℓ - 1) fun j hj1 hj2 =>
      mulAdd_piece (nm := "vg_mldsa_multiply_add_ntt") F.mulAdd (F.ok _ (by simp)) SC (oP (wB p + i)) SC (oP (aBase p + (p.ℓ * i + j))) SC (oP (yhB p + j))
        (by have := ha j (by omega_arith); ofsd)
        (fun _ _ _ h => ⟨h.1.cm.it.kd.ctx, h.2.1, (fam_at h.1.cm.it.kd.dk.fa (ha j (by omega_arith))).1,
          (fam_at h.1.cm.fyh (by omega_arith)).1⟩)
        fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps (by omega_arith) c' (by decide) fr (by ofsd), by
          rw [h.2.2, (fam_at h.1.cm.it.kd.dk.fa (ha j (by omega_arith))).2, (fam_at h.1.cm.fyh (by omega_arith)).2,
            aVal_ij (by omega_arith)] at hq
          rw [wAcc_succ]; exact hq⟩
    rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega_arith] at this
  refine inPlace_piece (t := nttInv) F.invNtt (F.ok _ (by simp)) (pS (wB p + i)) rfl (by ofsd)
    (fun _ _ _ h => ⟨h.1.cm.it.kd.ctx, h.2.1⟩) fun s₀ s s' hp h c' fr hq => ?_
  rw [h.2.2] at hq
  exact ⟨(h.1.keep hp ps (by omega_arith) c' (by decide) fr (by ofsd)).cm, (h.1.keep hp ps (by omega_arith) c' (by decide) fr
    (by ofsd)).fw.snoc hq⟩

/-! ## `w₁` and `c̃` -/

/-- The encodings of the first `i` polynomials of `w₁`. -/
abbrev w1Enc (p : Params) (s₀ : State) (κ i : Nat) : List Byte :=
  (List.range i).flatMap fun j => simpleBitPack (w1F p (Am p s₀) (rppS p s₀) κ j) (w1Max p)

/-- Iteration `t`, with `y`, `w`, and the encodings of the first `i` polynomials of `w₁` at `W1`. -/
structure CH (p : Params) (t i : Nat) (s₀ s : State) : Prop where
  cw : CW p t p.k s₀ s
  w1 : bytesAt s.mem (Buf.addr s₀ (sc oW1 1024)) (w1Len p * i) = w1Enc p s₀ (p.ℓ * t) i

theorem natPolyIs_coeff {m : Mem} {a : Addr} {f : Vector Nat n} (h : NatPolyIs m a f) {j : Nat} (hj : j < 256) :
    (coeffAt m a j).toNat = f[j] := by
  have := congrArg (·[j]) h
  simp only [natPolyAt, Vector.getElem_ofFn] at this
  exact this

/-- `w1Encode(w₁[i])` to `W1 + w1Len · i`. -/
theorem w1R_piece {P : Prims} (F : PrimsOk P) (ps : PS p) (t i : Nat) (hi : i < p.k) :
    SP p (CH p t i) (CH p t (i + 1)) (w1R P p i) := by
  obtain hj : wB p + i < nS p := by simp only [nS, wB]; omega_arith
  have hw := ps.hw1
  obtain hwl : w1Len p * i + w1Len p ≤ 1024 := by
    have : w1Len p * i + w1Len p ≤ w1Len p * p.k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
    rw [Nat.mul_comm p.k] at hw; omega_arith
  obtain hwp : 0 < w1Len p := by rcases ps.hw1Len with h | h <;> omega_arith
  refine Piece.seq (B := fun s₀ s => CH p t i s₀ s ∧
      NatPolyIs s.mem (Buf.addr s₀ t1P) (w1F p (Am p s₀) (rppS p s₀) (p.ℓ * t) i))
    (hb_piece F.highBits (F.ok _ (by simp)) p.γ₂ ps.hγ₂ SC (oP (wB p + i)) SC (oP 1) (by ofsd)
      (fun _ _ _ h => ⟨h.cw.cm.it.kd.ctx, (fam_at h.cw.fw hi).1⟩) fun s₀ s s' hp h c' fr hq =>
      ⟨⟨h.cw.keep hp ps (Nat.le_refl _) c' (by decide) fr (by ofsd), by
        rw [keepB0 hp (by decide) fr 1024 (by have := scr_ge ps; simp only [oP, oW1, nS] at this ⊢; omega_arith) (by ofsd)]
        exact h.w1⟩, by rw [(fam_at h.cw.fw hi).2] at hq; exact hq⟩) ?_
  refine sbp_piece F.simpleBitPack (F.ok _ (by simp)) (w1Max p) (w1Len p) ps.hw1Max.1 ps.hw1Max.2 SC (oP 1) SC
    (oW1 + w1Len p * i) (by ofsd) (fun _ _ _ h => ⟨h.1.cw.cm.it.kd.ctx, fun j hj => by
      rw [natPolyIs_coeff h.2 hj, w1F, Vector.getElem_map]; exact highBits_le ps.hγ₂ _⟩)
    fun s₀ s s' hp h c' fr hq => ⟨h.1.cw.keep hp ps (Nat.le_refl _) c' (by decide) fr (by ofsd), ?_⟩
  obtain e : Buf.addr s₀ (sc (oW1 + w1Len p * i) (w1Len p)) = Buf.addr s₀ (sc oW1 1024) + BitVec.ofNat 64 (w1Len p * i) :=
    addr_off hp (sc_ok' ps (by decide) (by decide)) (by ofsd)
  rw [Nat.mul_succ, VG.Proof.MlKem.bytesAt_add, ← e, hq, h.2,
    keepB0 hp (by decide) fr 1024 (by have := scr_ge ps; simp only [oP, oW1, nS] at this ⊢; omega_arith) (by ofsd), h.1.w1,
    w1Enc, w1Enc, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- Iteration `t`, with `y`, `w` and `c̃`. -/
structure CC (p : Params) (t : Nat) (s₀ s : State) : Prop where
  cw : CW p t p.k s₀ s
  ct : bytesAt s.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = CTv p s₀ (p.ℓ * t)

theorem w1Enc_eq (s₀ : State) (κ : Nat) :
    w1Enc p s₀ κ p.k = w1Encode p ((List.range p.k).map (w1F p (Am p s₀) (rppS p s₀) κ)) := by
  simp only [w1Enc, w1Encode, List.flatMap_map]

/-- The commitment of iteration `t`. -/
theorem commit_piece {P : Prims} (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (CM p t 0) (CC p t) (commit P p) := by
  have hw := ps.hw1
  have hc := ps.hcLen
  refine Piece.seq (B := CM p t p.ℓ) ?_ ?_
  · have := seqR_piece (p := p) (I := CM p t) 0 p.ℓ fun r _ hr => maskR_piece F ps t r (by omega_arith)
    simpa using this
  refine Piece.seq (B := CW p t p.k) ?_ ?_
  · have := seqR_piece (p := p) (I := CW p t) 0 p.k fun i _ hi => rowW_piece F ps t i (by omega_arith)
    simp only [Nat.zero_add] at this
    exact this.mono (fun _ _ _ h => ⟨h, fun j hj => absurd hj (Nat.not_lt_zero _)⟩) fun _ _ _ h => h
  refine Piece.seq (B := CH p t p.k) ?_ ?_
  · have := seqR_piece (p := p) (I := CH p t) 0 p.k fun i _ hi => w1R_piece F ps t i (by omega_arith)
    simp only [Nat.zero_add] at this
    exact this.mono (fun _ _ _ h => ⟨h, rfl⟩) fun _ _ _ h => h
  refine hash2_piece' 136 0x1f bMu (sc oW1 (p.k * w1Len p)) (sc oCT (cLen p)) (by decide) (by ofsd) (by decide)
    (by show p.k * w1Len p < 2 ^ 32; omega_arith) (by show cLen p < 2 ^ 32; omega_arith) (fun _ _ _ h => h.cw.cm.it.kd.ctx)
    fun s₀ s s' hp h c' fr hb => ⟨h.cw.keep hp ps (Nat.le_refl _) c' (by decide) fr (by ofsd), ?_⟩
  obtain e : BitVec.setWidth 8 (31#32) = Spec.Sha3.shakeSuffix := by decide
  obtain hw1 : bytesAt s.mem (Buf.addr s₀ (sc oW1 (p.k * w1Len p))) (p.k * w1Len p) = w1Enc p s₀ (p.ℓ * t) p.k := by
    rw [Nat.mul_comm]; exact h.w1
  simp only [sc, bMu] at hb hw1 ⊢
  rw [hb, hw1, h.cw.cm.it.kd.ctx.roBytes hp (b := bMu) (by ofsd) rfl, e, w1Enc_eq, CTv, ctF,
    VG.Proof.MlDsa.Sample.H_eq]

end VG.Proof.MlDsa.X86.Sign

end

end


/-!
# ML-DSA signing on x86 (32-bit): what two related runs agree on

Whether every entry of `Â` was sampled (`Good`), and the number of iterations
of the loop (`NI`: the number the implementation's `SampleInBall` and the
checks make, or 1 if `Â` was not sampled), are the same in two runs related by
`SPub`; and at an iteration both reach (`t < NI`), so are `c̃`, whether
`SampleInBall` succeeded, whether the checks passed, and then the hint.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

section
variable (p : Params) (F : PrimsOk P)

/-- Every entry of `Â` was sampled. -/
abbrev Good (s₀ : State) : Prop := okE p F.rejF s₀ (p.k * p.ℓ) = true

/-- The number of iterations of the loop. -/
def NI (s₀ : State) : Nat := if Good p F s₀ then itV p (skOf p s₀) (muOf s₀) (rndOf s₀) F.ballF else 1

end

theorem NI_pos (F : PrimsOk P) (s₀ : State) : 0 < NI p F s₀ := by
  unfold NI; split
  · exact nIt_pos _ (by decide)
  · decide

theorem NI_le (F : PrimsOk P) (s₀ : State) : NI p F s₀ ≤ 814 := by
  unfold NI; split
  · exact nIt_le _ _
  · decide

theorem NI_good {F : PrimsOk P} {s₀ : State} (h : Good p F s₀) :
    NI p F s₀ = itV p (skOf p s₀) (muOf s₀) (rndOf s₀) F.ballF := by
  unfold NI; rw [ifp h]

theorem seedE_eq {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') (e : Nat) : seedE p s₀ e = seedE p s₀' e := by
  show aSeed (rhoS p s₀) _ _ = aSeed (rhoS p s₀') _ _; rw [rhoS_eq ps hq]

theorem okE_eq {F : List Byte → Bool} {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') (e : Nat) :
    okE p F s₀ e = okE p F s₀' e := by
  simp only [okE, seedE_eq ps hq]

theorem skOf_len (ps : PS p) (s₀ : State) : 32 ≤ (skOf p s₀).length := by
  rw [VG.Proof.MlKem.bytesAt_length]; exact skLen_ge ps

/-- `ExpandA` succeeds within `maxBounds` once every entry was sampled. -/
theorem expandA_good {F : PrimsOk P} {s₀ : State} (h : Good p F s₀) :
    expandA p maxBounds (rhoV (skOf p s₀)) = some (amat p (Av (skOf p s₀))) := by
  refine expandA_some fun i hi j hj => ?_
  obtain hl : 0 < p.ℓ := by omega_using [hj]
  obtain he := okE_lt h (aIdx hi hj)
  obtain e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  obtain e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [seedE, e1, e2] at he
  exact F.rejMax _ he

theorem leakV_eq {F : PrimsOk P} {s₀ s₀' : State} (ps : PS p) (h : Good p F s₀) (h' : Good p F s₀')
    (hq : SPub p s₀ s₀') :
    leakV p (skOf p s₀) (muOf s₀) (rndOf s₀) = leakV p (skOf p s₀') (muOf s₀') (rndOf s₀') :=
  leakV_of_leak (skOf_len ps s₀) (skOf_len ps s₀') (expandA_good h) (expandA_good h') hq.coarse

theorem good_iff {F : PrimsOk P} {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') : Good p F s₀ ↔ Good p F s₀' := by
  simp only [Good, okE_eq ps hq]

theorem NI_eq {F : PrimsOk P} {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') : NI p F s₀ = NI p F s₀' := by
  by_cases h : Good p F s₀
  · have h' := (good_iff ps hq).mp h
    rw [NI_good h, NI_good h']
    exact itV_eq ps.hok F.ballMax (leakV_eq ps h h' hq)
  · have h' : ¬ Good p F s₀' := fun h' => h ((good_iff ps hq).mpr h')
    unfold NI; rw [ifn h, ifn h']

/-- Iteration `t` is run. -/
def Run (p : Params) (F : PrimsOk P) (t : Nat) (s₀ : State) : Prop := Good p F s₀ ∧ t < NI p F s₀

instance {F : PrimsOk P} {t : Nat} {s₀ : State} : Decidable (Run p F t s₀) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Run.cont {F : PrimsOk P} {t : Nat} {s₀ : State} (h : Run p F t s₀) :
    ∀ j < t, contV p (skOf p s₀) (muOf s₀) (rndOf s₀) F.ballF j = true := by
  have := h.2; rw [NI_good h.1] at this
  exact nIt_before _ this

theorem Run.lt {F : PrimsOk P} {t : Nat} {s₀ : State} (h : Run p F t s₀) : t < 814 :=
  Nat.lt_of_lt_of_le h.2 (NI_le F s₀)

theorem run_iff {F : PrimsOk P} {t : Nat} {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') :
    Run p F t s₀ ↔ Run p F t s₀' := by
  simp only [Run, good_iff ps hq, NI_eq ps hq]

/-- At an iteration both runs reach: `c̃`, the success of `SampleInBall`,
the outcome of the checks, and the hint. -/
theorem run_at {F : PrimsOk P} {t : Nat} {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') (h : Run p F t s₀) :
    CTv p s₀ (p.ℓ * t) = CTv p s₀' (p.ℓ * t) ∧
      (F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = true →
        (passV p (skOf p s₀) (muOf s₀) (rndOf s₀) (p.ℓ * t) ↔ passV p (skOf p s₀') (muOf s₀') (rndOf s₀') (p.ℓ * t)) ∧
        (passV p (skOf p s₀) (muOf s₀) (rndOf s₀) (p.ℓ * t) →
          hbitsV p (skOf p s₀) (muOf s₀) (rndOf s₀) (p.ℓ * t) = hbitsV p (skOf p s₀') (muOf s₀') (rndOf s₀') (p.ℓ * t))) :=
  leak_at ps.hok F.ballMax (leakV_eq ps h.1 ((good_iff ps hq).mp h.1) hq) (by show t < 1000; have := h.lt; omega_using [this]) h.cont

/-- The full rejection leakage at an iteration both runs reach. -/
theorem run_leak {F : PrimsOk P} {t : Nat} {x y : State} (ps : PS p) (hq : SPub p x y) (h : Run p F t x) :
    signLeakLoop p maxBounds (amat p (Am p x)) ((List.range p.ℓ).map (S1 p x))
      ((List.range p.k).map (S2 p x)) ((List.range p.k).map (T0 p x)) (muOf x) (rppS p x)
      (maxBounds.sign-t) (p.ℓ*t) =
    signLeakLoop p maxBounds (amat p (Am p y)) ((List.range p.ℓ).map (S1 p y))
      ((List.range p.k).map (S2 p y)) ((List.range p.k).map (T0 p y)) (muOf y) (rppS p y)
      (maxBounds.sign-t) (p.ℓ*t) := by
  obtain h' := (good_iff ps hq).mp h.1
  have e := hq.2
  rw [signLeak_eq (expandA_good h.1), signLeak_eq (expandA_good h')] at e
  obtain hr : (skOf p x).take 32 = (skOf p y).take 32 := rhoS_eq ps hq
  rw [hr] at e
  obtain e' : leakVF p (skOf p x) (muOf x) (rndOf x) = leakVF p (skOf p y) (muOf y) (rndOf y) :=
    List.append_cancel_left e
  exact (leak_iterF ps.hok F.ballMax e' (by have := h.lt; show t < 1000; omega_using [this]) h.cont).2

end VG.Proof.MlDsa.X86.Sign

end

end


/-!
# ML-DSA signing on x86 (32-bit): the checks of an iteration

Once `SampleInBall` succeeded (`ballCall_piece`), the checks (`CS`: what they
keep, with `y`, `w`, the hint, `OK` and `ONES` as far as they got) compute `z`
in place of `y` (`zR_piece`), `w - cs₂` in place of `w` and the norm of its
`LowBits` (`r0R_piece`), and `ct₀`, `w - cs₂ + ct₀` and the hint (`hR_piece`);
`OK` is then 1 exactly when the checks pass (`onesOk_piece`, `pass_iff`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_ copyW)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_shr)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

section
variable (p : Params)

/-- `c`, and the values of the checks, of the iteration with counter `κ`. -/
abbrev Cv (s₀ : State) (κ : Nat) : IPoly := cV p (skOf p s₀) (muOf s₀) (rndOf s₀) κ
abbrev Zv (s₀ : State) (κ r : Nat) : Poly := zF p (S1 p s₀) (rppS p s₀) κ (Cv p s₀ κ) r
abbrev W'v (s₀ : State) (κ i : Nat) : Poly := w'F p (Am p s₀) (S2 p s₀) (rppS p s₀) κ (Cv p s₀ κ) i
abbrev R0v (s₀ : State) (κ i : Nat) : Poly := r0F p (Am p s₀) (S2 p s₀) (rppS p s₀) κ (Cv p s₀ κ) i
abbrev CT0v (s₀ : State) (κ i : Nat) : Poly := ct0F (T0 p s₀) (Cv p s₀ κ) i
abbrev W''v (s₀ : State) (κ i : Nat) : Poly := w''F p (Am p s₀) (S2 p s₀) (T0 p s₀) (rppS p s₀) κ (Cv p s₀ κ) i
abbrev Hv (s₀ : State) (κ i : Nat) : Vector Bool n := hF p (Am p s₀) (S2 p s₀) (T0 p s₀) (rppS p s₀) κ (Cv p s₀ κ) i

/-- The checks of the first `r` polynomials. -/
def okZ (s₀ : State) (κ r : Nat) : Bool := (List.range r).all fun j => decide (normRq [Zv p s₀ κ j] < p.γ₁ - p.β)
def okR (s₀ : State) (κ i : Nat) : Bool := (List.range i).all fun j => decide (normRq [R0v p s₀ κ j] < p.γ₂ - p.β)
def okT (s₀ : State) (κ i : Nat) : Bool := (List.range i).all fun j => decide (normRq [CT0v p s₀ κ j] < p.γ₂)
/-- The number of 1s of the first `i` polynomials of the hint. -/
def onesS (s₀ : State) (κ i : Nat) : Nat := ((List.range i).map fun j => hintOnes [Hv p s₀ κ j]).sum

end

theorem all_range_succ {f : Nat → Bool} {r : Nat} :
    (List.range (r + 1)).all f = ((List.range r).all f && f r) := by
  simp only [List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

theorem all_range_iff {f : Nat → Prop} [DecidablePred f] {r : Nat} :
    (List.range r).all (fun j => decide (f j)) = true ↔ ∀ j < r, f j := by
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]

/-- The checks pass exactly when `OK` ends up 1. -/
theorem pass_iff {s₀ : State} {κ : Nat} :
    passV p (skOf p s₀) (muOf s₀) (rndOf s₀) κ ↔
      (okZ p s₀ κ p.ℓ && okR p s₀ κ p.k && okT p s₀ κ p.k && decide (onesS p s₀ κ p.k ≤ p.ω)) = true := by
  simp only [Bool.and_eq_true, okZ, okR, okT, all_range_iff, onesS, passV, passF, and_assoc]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, decide_eq_true d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, of_decide_eq_true d⟩⟩

section
variable (p : Params)
abbrev PassV (σ : State) (κ : Nat) : Prop :=
  passF p (Am p σ) (S1 p σ) (S2 p σ) (T0 p σ) (rppS p σ) κ (Cv p σ κ)
abbrev ZOk (σ : State) (κ : Nat) : Prop := ∀ j < p.ℓ, normRq [Zv p σ κ j] < p.γ₁-p.β
abbrev R0Ok (σ : State) (κ : Nat) : Prop := ∀ j < p.k, normRq [R0v p σ κ j] < p.γ₂-p.β
abbrev iterF (σ : State) (b : Bounds) (κ : Nat) := iterV p (skOf p σ) (muOf σ) (rndOf σ) b κ
abbrev leakL (σ : State) (n κ : Nat) :=
  signLeakLoop p maxBounds (amat p (Am p σ)) ((List.range p.ℓ).map (S1 p σ))
    ((List.range p.k).map (S2 p σ)) ((List.range p.k).map (T0 p σ)) (muOf σ) (rppS p σ) n κ
abbrev LeakEq (t : Nat) (σ₁ σ₂ : State) : Prop := leakL p σ₁ (1000-t) (p.ℓ*t) = leakL p σ₂ (1000-t) (p.ℓ*t)
end

/-- What the branches of the checks need two runs to agree on: whether the
first `r` polynomials of `z` passed, for each `r` (the checks stop at the
first that fails), whether `z` and the first `i` polynomials of `r₀` passed,
for each `i`, and whether the iteration passed. -/
abbrev ChecksAgree (p : Params) (t : Nat) (σ₁ σ₂ : State) : Prop :=
  (∀ r ≤ p.ℓ, (∀ j < r, normRq [Zv p σ₁ (p.ℓ * t) j] < p.γ₁ - p.β) ↔
    (∀ j < r, normRq [Zv p σ₂ (p.ℓ * t) j] < p.γ₁ - p.β)) ∧
  (∀ i ≤ p.k, (ZOk p σ₁ (p.ℓ * t) ∧ ∀ j < i, normRq [R0v p σ₁ (p.ℓ * t) j] < p.γ₂ - p.β) ↔
    (ZOk p σ₂ (p.ℓ * t) ∧ ∀ j < i, normRq [R0v p σ₂ (p.ℓ * t) j] < p.γ₂ - p.β)) ∧
  (PassV p σ₁ (p.ℓ * t) ↔ PassV p σ₂ (p.ℓ * t))

theorem iterF_eq {p : Params} (hp : ParamsOk p) {σ : State} {b : Bounds} {κ : Nat} :
    iterF p σ b κ = (sampleInBall p.τ b.ball (CTv p σ κ)).map fun c =>
      (CTv p σ κ, if passF p (Am p σ) (S1 p σ) (S2 p σ) (T0 p σ) (rppS p σ) κ c then
        some ((List.range p.ℓ).map (zF p (S1 p σ) (rppS p σ) κ c),
          (List.range p.k).map (hF p (Am p σ) (S2 p σ) (T0 p σ) (rppS p σ) κ c)) else none) :=
  iterV_eq hp b

theorem iter_rej {p : Params} {σ : State} {κ : Nat} (hp : ParamsOk p)
    (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome) (hn : ¬ PassV p σ κ) :
    iterF p σ maxBounds κ = some (CTv p σ κ, none) := iterV_rej hp hs hn

section
variable {p : Params} {σ₁ σ₂ : State} {t : Nat}
theorem leq_step (h : LeakEq p t σ₁ σ₂) (ht : t < 814) :
    signLeakLoop p maxBounds (amat p (Am p σ₁)) ((List.range p.ℓ).map (S1 p σ₁)) ((List.range p.k).map (S2 p σ₁))
      ((List.range p.k).map (T0 p σ₁)) (muOf σ₁) (rppS p σ₁) ((999 - t) + 1) (p.ℓ * t) =
    signLeakLoop p maxBounds (amat p (Am p σ₂)) ((List.range p.ℓ).map (S1 p σ₂)) ((List.range p.k).map (S2 p σ₂))
      ((List.range p.k).map (T0 p σ₂)) (muOf σ₂) (rppS p σ₂) ((999 - t) + 1) (p.ℓ * t) := by
  rw [show 999 - t + 1 = 1000 - t by omega_using [ht]]; exact h

theorem outTag_eq (hp : ParamsOk p) {σ : State} {κ : Nat} (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome) :
    outTag (iterF p σ maxBounds κ) = if PassV p σ κ then
      1 :: ((List.range p.k).map (Hv p σ κ)).flatMap (fun hi => hi.toList.map Bool.toNat) else [0] := by
  rw [iterF_eq hp, cV_eq hs, Option.map_some]
  by_cases hv : PassV p σ κ
  · rw [ifp hv, ifp hv]; rfl
  · rw [ifn hv, ifn hv]; rfl

theorem leq_pass (hp : ParamsOk p) (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (sampleInBall p.τ maxBounds.ball (CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (CTv p σ₂ (p.ℓ * t))).isSome) :
    PassV p σ₁ (p.ℓ * t) ↔ PassV p σ₂ (p.ℓ * t) := by
  obtain e := (leakF_step (leq_step h ht)).2.2
  rw [outTag_eq hp hs₁, outTag_eq hp hs₂] at e
  by_cases h1 : PassV p σ₁ (p.ℓ * t) <;> by_cases h2 : PassV p σ₂ (p.ℓ * t)
  · exact iff_of_true h1 h2
  · rw [ifp h1, ifn h2] at e; cases e
  · rw [ifn h1, ifp h2] at e; cases e
  · exact iff_of_false h1 h2

/-- `signRejectTag`'s value: which check failed, and for those of `z` and
`r₀` the first polynomial that failed it. -/
def tagFn (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] (x y : Nat) : Nat :=
  if ¬ a then 5 * x else if ¬ b then 2 + 5 * y else if ¬ c then 3 else 4

theorem tagFn_eq {a b c a' b' c' : Prop} [Decidable a] [Decidable b] [Decidable c] [Decidable a'] [Decidable b']
    [Decidable c'] {x y x' y' : Nat} (h : tagFn a b c x y = tagFn a' b' c' x' y') :
    (a ↔ a') ∧ (¬ a → x = x') ∧ (a ∧ b ↔ a' ∧ b') ∧ (a → ¬ b → y = y') := by
  unfold tagFn at h
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases ha' : a' <;> by_cases hb' : b' <;>
    by_cases hc' : c' <;> simp only [ha, hb, hc, ha', hb', hc', not_true_eq_false, not_false_eq_true,
      ite_true, ite_false] at h <;> first | omega | (simp_all <;> omega_using [h])

/-- The first polynomial of `z` that fails its check, or `ℓ`. -/
abbrev zFirst (p : Params) (σ : State) (κ : Nat) : Nat :=
  (List.range p.ℓ).findIdx fun r => decide (normRq [Zv p σ κ r] ≥ p.γ₁ - p.β)

/-- The first polynomial of `r₀` that fails its check, or `k`. -/
abbrev rFirst (p : Params) (σ : State) (κ : Nat) : Nat :=
  (List.range p.k).findIdx fun i => decide (normRq [R0v p σ κ i] ≥ p.γ₂ - p.β)

theorem tag_eq (hp : ParamsOk p) {σ : State} {κ : Nat}
    (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome) :
    signRejectTag p maxBounds (amat p (Am p σ)) ((List.range p.ℓ).map (S1 p σ)) ((List.range p.k).map (S2 p σ))
      ((List.range p.k).map (T0 p σ)) (muOf σ) (rppS p σ) κ =
      tagFn (ZOk p σ κ) (R0Ok p σ κ) (∀ j < p.k, normRq [CT0v p σ κ j] < p.γ₂) (zFirst p σ κ) (rFirst p σ κ) := by
  rw [signRejectTag_eqF hp, show ctF p (Am p σ) (muOf σ) (rppS p σ) κ = CTv p σ κ from rfl, cV_eq hs]
  rfl

/-- The first `r ≤ n` polynomials pass a check exactly when the first that
fails it comes at `r` or later. -/
theorem prefix_ok {n B : Nat} (f : Nat → Poly) {r : Nat} (hr : r ≤ n) :
    (∀ j < r, normRq [f j] < B) ↔ r ≤ (List.range n).findIdx fun j => decide (normRq [f j] ≥ B) := by
  rw [← prefix_findIdx n _ hr]
  simp only [decide_eq_false_iff_not, ge_iff_le, Nat.not_le]

/-- Two runs that agree on what the iterations from `t` leak agree on the
checks of iteration `t` that pass, polynomial by polynomial. -/
theorem leq_agree (hp : ParamsOk p) (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (sampleInBall p.τ maxBounds.ball (CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (CTv p σ₂ (p.ℓ * t))).isSome) : ChecksAgree p t σ₁ σ₂ := by
  obtain hpass := leq_pass hp h ht hs₁ hs₂
  by_cases h1 : PassV p σ₁ (p.ℓ * t)
  · have h2 := hpass.mp h1
    exact ⟨fun r hr => iff_of_true (fun j hj => h1.1 j (by omega_using [hr, hj])) (fun j hj => h2.1 j (by omega_using [hr, hj])),
      fun i hi => iff_of_true ⟨h1.1, fun j hj => h1.2.1 j (by omega_using [hi, hj])⟩ ⟨h2.1, fun j hj => h2.2.1 j (by omega_using [hi, hj])⟩, hpass⟩
  · have h2 : ¬ PassV p σ₂ (p.ℓ * t) := fun h2 => h1 (hpass.mpr h2)
    obtain e := leakF_tag (leq_step h ht) (iter_rej hp hs₁ h1) (iter_rej hp hs₂ h2)
    rw [tag_eq hp hs₁, tag_eq hp hs₂] at e
    obtain ⟨ea, ex, eab, ey⟩ := tagFn_eq e
    refine ⟨fun r hr => ?_, fun i hi => ?_, hpass⟩
    · by_cases hz : ZOk p σ₁ (p.ℓ * t)
      · exact iff_of_true (fun j hj => hz j (by omega_using [hr, hj])) (fun j hj => ea.mp hz j (by omega_using [hr, hj]))
      · rw [prefix_ok _ hr, prefix_ok _ hr]; exact iff_of_eq (congrArg (r ≤ ·) (ex hz))
    · by_cases hz : ZOk p σ₁ (p.ℓ * t)
      · have hz' := ea.mp hz
        by_cases hr0 : R0Ok p σ₁ (p.ℓ * t)
        · have hr0' := (eab.mp ⟨hz, hr0⟩).2
          exact iff_of_true ⟨hz, fun j hj => hr0 j (by omega_using [hi, hj])⟩ ⟨hz', fun j hj => hr0' j (by omega_using [hi, hj])⟩
        · rw [and_iff_right hz, and_iff_right hz', prefix_ok _ hi, prefix_ok _ hi]
          exact iff_of_eq (congrArg (i ≤ ·) (ey hz hr0))
      · exact iff_of_false (fun h => hz h.1) (fun h => hz (ea.mpr h.1))

end

theorem run_agree {F : PrimsOk P} {t : Nat} {x y : State} (ps : PS p) (hq : SPub p x y)
    (h : Run p F t x) (hs₁ : (sampleInBall p.τ maxBounds.ball (CTv p x (p.ℓ*t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (CTv p y (p.ℓ*t))).isSome) : ChecksAgree p t x y :=
  leq_agree ps.hok (run_leak ps hq h) h.lt hs₁ hs₂

/-! ## The hint -/

/-- The first `nh` polynomials of the hint, in the slots from 5. -/
def HF (s₀ : State) (m : Mem) (nh : Nat) (f : Nat → Vector Bool n) : Prop :=
  ∀ j < nh, HintIs m (Buf.addr s₀ (pS (5 + j))) 1 [f j]

theorem hintIs_congr {m m' : Mem} {a : Addr} {h : Vector Bool n}
    (e : ∀ x < 1024, m' (a + BitVec.ofNat 64 x) = m (a + BitVec.ofNat 64 x)) (hh : HintIs m a 1 [h]) :
    HintIs m' a 1 [h] := by
  refine ⟨hh.1, fun i hi j hj => ?_⟩
  have : coeffAt m' a (256 * i + j) = coeffAt m a (256 * i + j) := by
    unfold coeffAt
    refine Mem.readW_congr fun t ht => ?_
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact e _ (by have : n = 256 := rfl; omega_arith)
  rw [this]; exact hh.2 i hi j hj

theorem HF.keep {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {nh : Nat} (hn : 5 + nh ≤ nS p)
    (h : ∀ c ∈ bs, Out p (oP 5) (oP (5 + nh)) c) {f : Nat → Vector Bool n} (hf : HF s₀ m nh f) : HF s₀ m' nh f :=
  fun j hj => hintIs_congr (VG.Proof.MlKem.X86.Top.keep hp (N := N) (by show N + 16 ≤ 96; omega_arith)
    (apart_of (slot_ok' ps (by omega_arith)) rfl fun c hc => by
      obtain ⟨h₁, h₂⟩ := h c hc
      exact ⟨h₁, fun e => by simp only [oP] at h₂ ⊢; have := h₂ e; omega_arith⟩) fr) (hf j hj)

theorem HF.snoc {s₀ : State} {m : Mem} {nh : Nat} {f : Nat → Vector Bool n} (h : HF s₀ m nh f)
    (h' : HintIs m (Buf.addr s₀ (pS (5 + nh))) 1 [f nh]) : HF s₀ m (nh + 1) f := fun j hj => by
  by_cases e : j < nh
  · exact h j e
  · rw [show j = nh by omega_arith]; exact h'

/-- Slot `r` of a family changed, the others kept. -/
theorem Fam.upd {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {b n r : Nat} (hb : b + n ≤ nS p) (hr : r < n)
    (h : ∀ c ∈ bs, Out p (oP b) (oP (b + r)) c ∧ Out p (oP (b + r + 1)) (oP (b + n)) c) {f g : Nat → Poly}
    (hf : Fam s₀ m b n f) (hv : PolyIs m' (Buf.addr s₀ (pS (b + r))) (g r)) (hg : ∀ j < n, j ≠ r → g j = f j) :
    Fam s₀ m' b n g := fun j hj => by
  by_cases e : j = r
  · subst e; exact hv
  · rw [hg j hj e]
    exact keepP hp ps hN fr (by omega_arith) (fun c hc => by
      obtain ⟨⟨h₁, h₂⟩, -, h₃⟩ := h c hc
      exact ⟨h₁, fun ea => by
        have := h₂ ea; have := h₃ ea; simp only [oP] at *
        rcases (by omega_arith : j < r ∨ r < j) with hj' | hj' <;> omega_arith⟩) (hf j hj)

/-! ## The state of the checks -/

/-- The checks of iteration `t`, with `y`, `w`, the first `nh` polynomials of
the hint, `OK` and `ONES` as `fY`, `fW`, `okb` and `ones` say. -/
structure CS (p : Params) (t : Nat) (fY fW : State → Nat → Poly) (nh : Nat) (okb : State → Bool)
    (ones : State → Nat) (s₀ s : State) : Prop where
  it : IT p t s₀ s
  ct : bytesAt s.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = CTv p s₀ (p.ℓ * t)
  c : PolyIs s.mem (Buf.addr s₀ cP) (chF (Cv p s₀ (p.ℓ * t)))
  fy : Fam s₀ s.mem (yB p) p.ℓ (fY s₀)
  fw : Fam s₀ s.mem (wB p) p.k (fW s₀)
  fh : HF s₀ s.mem nh (Hv p s₀ (p.ℓ * t))
  ok : scw s₀ s oOK = if okb s₀ then 1 else 0
  ones : scw s₀ s oONES = BitVec.ofNat 32 (ones s₀)
  nh : nh ≤ p.k

section
variable {t nh : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
  {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s) (c' : Ctx (Y p) s₀ s')
  {bs : List Buf} {N : Nat} (hN : N ≤ 80) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
include hp ps h c' hN fr

omit c' in
theorem CS.ct_keep (hb : ∀ c ∈ bs, Out p oCT (oCT + 64) c) :
    bytesAt s'.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = CTv p s₀ (p.ℓ * t) := by
  have := ps.hcLen
  rw [keepB hp hN fr (by ofsd) fun c hc => ⟨(hb c hc).1, fun e => by
    have := (hb c hc).2 e; simp only [oCT] at this ⊢; omega_arith⟩, h.ct]

theorem CS.keep (hb : ∀ c ∈ bs, OutC p nh c) : CS p t fY fW nh okb ones s₀ s' := by
  have := h.nh
  exact ⟨h.it.keep hp ps c' hN fr fun c hc => (hb c hc).1, h.ct_keep hp ps hN fr fun c hc => (hb c hc).2.2.1,
    keepP hp ps hN fr (j := 0) (by simp only [nS]; omega_arith) (fun c hc => (hb c hc).2.1) h.c,
    h.fy.keep hp ps hN fr (by simp only [nS, yB]; omega_arith) fun c hc => ⟨(hb c hc).2.2.2.1.1, fun e => by
      have := (hb c hc).2.2.2.1.2 e; simp only [oP, yB, wB] at this ⊢; omega_arith⟩,
    h.fw.keep hp ps hN fr (by simp only [nS, wB]; omega_arith) fun c hc => ⟨(hb c hc).2.2.2.1.1, fun e => by
      have := (hb c hc).2.2.2.1.2 e; simp only [oP, yB, wB] at this ⊢; omega_arith⟩,
    h.fh.keep hp ps hN fr (by simp only [nS]; omega_arith) fun c hc => (hb c hc).2.2.2.2.1,
    by rw [scw, keepW' hp hN fr (sc_ok' ps (by decide) (by decide)) fun c hc => (hb c hc).2.2.2.2.2.1]; exact h.ok,
    by rw [scw, keepW' hp hN fr (sc_ok' ps (by decide) (by decide)) fun c hc => (hb c hc).2.2.2.2.2.2]; exact h.ones,
    h.nh⟩

end

/-! ## `SampleInBall` -/

theorem ball_val {τ : Nat} {x : List Byte} {r : BitVec 32} {out : Poly}
    (h : Outcome (fun b => (sampleInBall τ b.ball x).map toRq) r out) (h1 : r = 1)
    (hm : (sampleInBall τ maxBounds.ball x).isSome) :
    out = toRq ((sampleInBall τ maxBounds.ball x).getD (Vector.replicate n 0)) := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
    obtain e1 := sampleInBall_mono (Nat.le_max_left b.ball maxBounds.ball) hc
    obtain e2 := sampleInBall_mono (Nat.le_max_right b.ball maxBounds.ball) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

/-- After `SampleInBall` in iteration `t`. -/
structure IB (p : Params) (F : PrimsOk P) (t : Nat) (s₀ s : State) : Prop where
  cc : CC p t s₀ s
  run : Run p F t s₀
  eax : s.gpr .eax = if F.ballF p.τ (CTv p s₀ (p.ℓ * t)) then 1 else 0
  yes : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = true → PolyIs s.mem (Buf.addr s₀ cP) (toRq (Cv p s₀ (p.ℓ * t)))
  no : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = false → sampleInBall p.τ minBounds.ball (CTv p s₀ (p.ℓ * t)) = none

theorem CC.keep {t : Nat} {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CC p t s₀ s)
    (c' : Ctx (Y p) s₀ s') {bs : List Buf} {N : Nat} (hN : N ≤ 80) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (hb : ∀ c ∈ bs, (OutI p c ∧ Out p (oP (yB p)) (oP (wB p + p.k)) c) ∧ Out p oCT (oCT + 64) c) : CC p t s₀ s' := by
  have := ps.hcLen
  exact ⟨h.cw.keep hp ps (Nat.le_refl _) c' hN fr fun c hc => (hb c hc).1, by
    rw [keepB hp hN fr (by ofsd) fun c hc => ⟨(hb c hc).2.1, fun e => by
      have := (hb c hc).2.2 e; simp only [oCT] at this ⊢; omega_arith⟩, h.ct]⟩

/-- `c = SampleInBall(c̃)` to `ĉ`'s slot. -/
theorem ballCall_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (fun s₀ s => CC p t s₀ s ∧ Run p F t s₀) (IB p F t) (ballAt P (cLen p) p.τ cP) := by
  have := ps.hcLen
  refine ball_piece F.ball (F.ok _ (by simp)) (cLen p) p.τ ps.hball SC oCT SC (oP 0) SC oPS (by ofsd)
    (fun _ _ _ h => h.1.cw.cm.it.kd.ctx) (fun s₀ s₀' s s' hp hp' hq h h' => ?_)
    fun s₀ s s' hp h c' fr heax hred hout => ?_
  · rw [h.1.ct, h'.1.ct]; exact (run_at ps hq h.2).1
  · rw [h.1.ct] at heax hout
    refine ⟨h.1.keep hp ps c' (by decide) fr (by ofsd), h.2, heax, fun hy => ?_, fun hn => ?_⟩
    · rw [hy] at heax; simp only [↓reduceIte] at heax
      exact ⟨hred heax, ball_val hout heax (F.ballMax _ _ hy)⟩
    · rw [hn] at heax
      rcases hout with ⟨h1, _⟩ | ⟨_, h0⟩
      · rw [heax] at h1; cases h1
      · simpa using h0

/-- Whether `SampleInBall` succeeded, in a run that reaches iteration `t`. -/
def ballB (p : Params) (F : PrimsOk P) (t : Nat) (s₀ : State) : Bool :=
  decide (Run p F t s₀) && F.ballF p.τ (CTv p s₀ (p.ℓ * t))

theorem ballB_eq {F : PrimsOk P} {t : Nat} {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') :
    ballB p F t s₀ = ballB p F t s₀' := by
  unfold ballB
  by_cases h : Run p F t s₀
  · rw [decide_eq_true h, decide_eq_true ((run_iff ps hq).mp h), (run_at ps hq h).1]
  · rw [decide_eq_false h, decide_eq_false fun h' => h ((run_iff ps hq).mpr h'), Bool.false_and, Bool.false_and]

theorem ballB_of {F : PrimsOk P} {t : Nat} {s₀ : State} (h : Run p F t s₀) :
    ballB p F t s₀ = F.ballF p.τ (CTv p s₀ (p.ℓ * t)) := by
  simp only [ballB, decide_eq_true h, Bool.true_and]

/-- `ZF ← eax = 0`, after `SampleInBall`. -/
theorem ballTest_piece (F : PrimsOk P) (t : Nat) :
    SP p (IB p F t) (fun s₀ s => ∃ s', IB p F t s₀ s' ∧ Ctx (Y p) s₀ s ∧ s.mem = s'.mem ∧
      s.zf = some (!ballB p F t s₀)) (.block [.alu .test .eax (.reg .eax)]) := by
  refine blk_piece (fun _ _ _ h => h.cc.cw.cm.it.kd.ctx) (fun s₀ s hp h => wp_test fun s₁ o₁ z₁ =>
    WP.block_nil_iff.mpr ⟨s, h, h.cc.cw.cm.it.kd.ctx.only o₁ (by simp) (by simp), o₁.mem, ?_⟩) rfl
  rw [z₁, h.eax, ballB_of h.run]
  cases F.ballF p.τ (CTv p s₀ (p.ℓ * t)) <;> rfl

/-! ## The start of the checks -/

/-- `y`, with `z` in place of its first `r` polynomials. -/
abbrev zY (p : Params) (t r : Nat) (s₀ : State) (j : Nat) : Poly :=
  if j < r then Zv p s₀ (p.ℓ * t) j else Yv p s₀ (p.ℓ * t) j

/-- `w`, with `w - cs₂` in place of its first `i` polynomials. -/
abbrev rW (p : Params) (t i : Nat) (s₀ : State) (j : Nat) : Poly :=
  if j < i then W'v p s₀ (p.ℓ * t) j else Wv p s₀ (p.ℓ * t) j

/-- `w - cs₂`, with `w - cs₂ + ct₀` in place of its first `i` polynomials. -/
abbrev hW (p : Params) (t i : Nat) (s₀ : State) (j : Nat) : Poly :=
  if j < i then W''v p s₀ (p.ℓ * t) j else W'v p s₀ (p.ℓ * t) j

theorem zY_lt {t r j : Nat} {s₀ : State} (h : j < r) : zY p t r s₀ j = Zv p s₀ (p.ℓ * t) j := ifp h _ _
theorem zY_ge {t r j : Nat} {s₀ : State} (h : ¬ j < r) : zY p t r s₀ j = Yv p s₀ (p.ℓ * t) j := ifn h _ _
theorem rW_lt {t i j : Nat} {s₀ : State} (h : j < i) : rW p t i s₀ j = W'v p s₀ (p.ℓ * t) j := ifp h _ _
theorem rW_ge {t i j : Nat} {s₀ : State} (h : ¬ j < i) : rW p t i s₀ j = Wv p s₀ (p.ℓ * t) j := ifn h _ _
theorem hW_lt {t i j : Nat} {s₀ : State} (h : j < i) : hW p t i s₀ j = W''v p s₀ (p.ℓ * t) j := ifp h _ _
theorem hW_ge {t i j : Nat} {s₀ : State} (h : ¬ j < i) : hW p t i s₀ j = W'v p s₀ (p.ℓ * t) j := ifn h _ _

/-- The family whose first `r` values are `g` changed at `r`, for `r + 1`. -/
theorem upd_step {α : Type} {f g : Nat → α} {r j : Nat} (h : j ≠ r) :
    (if j < r + 1 then g j else f j) = if j < r then g j else f j := by
  by_cases e : j < r
  · rw [ifp (by omega_arith : j < r + 1), ifp e]
  · rw [ifn (by omega_arith : ¬ j < r + 1), ifn e]

/-- What the checks start from. -/
structure KP (p : Params) (F : PrimsOk P) (t : Nat) (s₀ s : State) : Prop where
  cc : CC p t s₀ s
  run : Run p F t s₀
  ball : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = true

theorem CC.ofMem {t : Nat} {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CC p t s₀ s')
    (c : Ctx (Y p) s₀ s) (hm : s.mem = s'.mem) : CC p t s₀ s :=
  h.keep hp ps c (N := 0) (bs := []) (by decide) (by rw [hm]; exact Frame.refl _ _) (by simp)

/-- `OK ← 1` and `ONES ← 0`. -/
theorem checksInit_piece (ps : PS p) (t : Nat) :
    SP p (fun s₀ s => CC p t s₀ s ∧ PolyIs s.mem (Buf.addr s₀ cP) (chF (Cv p s₀ (p.ℓ * t))))
      (CS p t (zY p t 0) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0 (fun s₀ => okZ p s₀ (p.ℓ * t) 0) (fun _ => 0))
      (.block (st32 oOK 1 ++ st32 oONES 0)) := by
  refine blk_piece (fun _ _ _ h => h.1.cw.cm.it.kd.ctx) (fun s₀ s hp h => ?_) rfl
  refine wp_st32 hp h.1.cw.cm.it.kd.ctx (sc_ok ps (by decide) (by decide)) 1 fun s₁ c₁ f₁ v₁ => ?_
  rw [← List.append_nil (st32 oONES 0)]
  refine wp_st32 hp c₁ (sc_ok ps (by decide) (by decide)) 0 fun s₂ c₂ f₂ v₂ => WP.block_nil_iff.mpr ?_
  obtain g₁ := (h.1.keep hp ps c₁ (N := 80) (by decide) (fr0 hp (by decide) f₁) (by ofsd))
  obtain g₂ := (g₁.keep hp ps c₂ (N := 80) (by decide) (fr0 hp (by decide) f₂) (by ofsd))
  obtain hc := keepP hp ps (N := 80) (by decide) (fr0 hp (by decide) f₁) (j := 0) (by simp only [nS]; omega_arith) (by ofsd) h.2
  obtain hc' := keepP hp ps (N := 80) (by decide) (fr0 hp (by decide) f₂) (j := 0) (by simp only [nS]; omega_arith) (by ofsd) hc
  refine ⟨g₂.cw.cm.it, g₂.ct, hc', g₂.cw.cm.fy.congr fun j hj => by simp, g₂.cw.fw, fun j hj => absurd hj (Nat.not_lt_zero _),
    ?_, v₂, Nat.zero_le _⟩
  rw [scw, keepW' hp (N := 80) (by decide) (fr0 hp (by decide) f₂) (sc_ok' ps (by decide) (by decide)) (by ofsd)]
  exact v₁

/-! ## Norms -/

/-- `OK ← OK ∧ b`, with `eax = b`. -/
theorem CS.setOK {t nh : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s) (c' : Ctx (Y p) s₀ s')
    (fr : Frame (FR s₀ [sc oOK 4] 0) s.mem s'.mem) (b : State → Bool)
    (v : scw s₀ s' oOK = scw s₀ s oOK &&& s.gpr .eax) (he : s.gpr .eax = if b s₀ then 1 else 0) :
    CS p t fY fW nh (fun s₀ => okb s₀ && b s₀) ones s₀ s' := by
  have := h.nh
  refine ⟨h.it.keep hp ps c' (N := 80) (by decide) (fr0 hp (by decide) fr) (by ofsd),
    h.ct_keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by ofsd),
    keepP hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (j := 0) (by simp only [nS]; omega_arith) (by ofsd) h.c,
    h.fy.keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by simp only [nS, yB]; omega_arith) (by ofsd),
    h.fw.keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by simp only [nS, wB]; omega_arith) (by ofsd),
    h.fh.keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by simp only [nS]; omega_arith) (by ofsd),
    by rw [v, h.ok, he, and01], ?_, h.nh⟩
  rw [scw, keepW' hp (N := 80) (by decide) (fr0 hp (by decide) fr) (sc_ok' ps (by decide) (by decide)) (by ofsd)]
  exact h.ones

/-- `OK ← OK ∧ ‖f‖∞ < bnd`, for the polynomial `v` in slot `j`, which stays. -/
theorem normAnd_piece (F : PrimsOk P) (ps : PS p) {t nh : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool}
    {ones : State → Nat} (j : Nat) (hj : j < nS p) (bnd : Nat) (hb : bnd < 2 ^ 32) (v : State → Poly) :
    SP p (fun s₀ s => CS p t fY fW nh okb ones s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS j)) (v s₀))
      (fun s₀ s => CS p t fY fW nh (fun s₀ => okb s₀ && decide (normRq [v s₀] < bnd)) ones s₀ s ∧
        PolyIs s.mem (Buf.addr s₀ (pS j)) (v s₀)) (normAt P (pS j) bnd) := by
  refine Piece.seq (B := fun s₀ s => (CS p t fY fW nh okb ones s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS j)) (v s₀)) ∧
      s.gpr .eax = if normRq [v s₀] < bnd then 1 else 0)
    (norm_piece F.normLt (F.ok _ (by simp)) bnd hb SC (oP j) (slot_ok' ps hj) (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr he => ⟨⟨h.1.keep hp ps c' (by decide) fr (by simp),
        keepP hp ps (by decide) fr hj (by simp) h.2⟩, by rw [he, h.2.2]⟩) ?_
  refine blk_piece (fun _ _ _ h => h.1.1.it.kd.ctx) (fun s₀ s hp h => wp_andOK hp h.1.1.it.kd.ctx ps
    fun s' c' fr v' => ⟨h.1.1.setOK hp ps c' fr (fun s₀ => decide (normRq [v s₀] < bnd)) v' ?_,
      keepP hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) hj (by ofsd) h.1.2⟩) rfl
  rw [h.2]; by_cases e : normRq [v s₀] < bnd <;> simp [e]

theorem CS.congr {t nh : Nat} {fY fY' fW fW' : State → Nat → Poly} {okb okb' : State → Bool} {ones : State → Nat}
    {s₀ s : State} (h : CS p t fY fW nh okb ones s₀ s) (e₁ : ∀ j < p.ℓ, fY s₀ j = fY' s₀ j)
    (e₂ : ∀ j < p.k, fW s₀ j = fW' s₀ j) (e₃ : okb s₀ = okb' s₀) : CS p t fY' fW' nh okb' ones s₀ s :=
  { h with fy := h.fy.congr e₁, fw := h.fw.congr e₂, ok := by rw [h.ok, e₃] }

/-- Slot `r` of `y` changed. -/
theorem CS.updY {t nh r : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s) (c' : Ctx (Y p) s₀ s')
    (hr : r < p.ℓ) (fr : Frame (FR s₀ [pS (yB p + r)] 80) s.mem s'.mem) {fY' : State → Nat → Poly}
    (hv : PolyIs s'.mem (Buf.addr s₀ (pS (yB p + r))) (fY' s₀ r)) (hg : ∀ j < p.ℓ, j ≠ r → fY' s₀ j = fY s₀ j) :
    CS p t fY' fW nh okb ones s₀ s' := by
  have := h.nh
  refine ⟨h.it.keep hp ps c' (by decide) fr (by ofsd), h.ct_keep hp ps (by decide) fr (by ofsd),
    keepP hp ps (by decide) fr (j := 0) (by simp only [nS]; omega_arith) (by ofsd) h.c,
    h.fy.upd hp ps (by decide) fr (by simp only [nS, yB]; omega_arith) hr (by ofsd) hv hg,
    h.fw.keep hp ps (by decide) fr (by simp only [nS, wB]; omega_arith) (by ofsd),
    h.fh.keep hp ps (by decide) fr (by simp only [nS]; omega_arith) (by ofsd),
    by rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofsd)]; exact h.ok,
    by rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofsd)]; exact h.ones, h.nh⟩

/-- Slot `i` of `w` changed. -/
theorem CS.updW {t nh i : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s) (c' : Ctx (Y p) s₀ s')
    (hi : i < p.k) (fr : Frame (FR s₀ [pS (wB p + i)] 80) s.mem s'.mem) {fW' : State → Nat → Poly}
    (hv : PolyIs s'.mem (Buf.addr s₀ (pS (wB p + i))) (fW' s₀ i)) (hg : ∀ j < p.k, j ≠ i → fW' s₀ j = fW s₀ j) :
    CS p t fY fW' nh okb ones s₀ s' := by
  have := h.nh
  refine ⟨h.it.keep hp ps c' (by decide) fr (by ofsd), h.ct_keep hp ps (by decide) fr (by ofsd),
    keepP hp ps (by decide) fr (j := 0) (by simp only [nS]; omega_arith) (by ofsd) h.c,
    h.fy.keep hp ps (by decide) fr (by simp only [nS, yB]; omega_arith) (by ofsd),
    h.fw.upd hp ps (by decide) fr (by simp only [nS, wB]; omega_arith) hi (by ofsd) hv hg,
    h.fh.keep hp ps (by decide) fr (by simp only [nS]; omega_arith) (by ofsd),
    by rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofsd)]; exact h.ok,
    by rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofsd)]; exact h.ones, h.nh⟩

/-! ## `z` -/

/-- `z[r] = y[r] + NTT⁻¹(ĉ ŝ₁[r])` in place of `y[r]`, and its norm. -/
theorem zR_piece (F : PrimsOk P) (ps : PS p) (t r : Nat) (hr : r < p.ℓ) :
    SP p (CS p t (zY p t r) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0 (fun s₀ => okZ p s₀ (p.ℓ * t) r) (fun _ => 0))
      (CS p t (zY p t (r + 1)) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0 (fun s₀ => okZ p s₀ (p.ℓ * t) (r + 1)) (fun _ => 0))
      (zR P p r) := by
  obtain hj : s1B p + r < nS p := by simp only [nS, s1B]; omega_arith
  obtain hy : yB p + r < nS p := by simp only [nS, yB]; omega_arith
  have hβ := ps.hβ
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t r) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) r) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t1P) (multiplyNTT (chF (Cv p s₀ (p.ℓ * t))) (S1 p s₀ r)))
    (mul_piece F.mul (F.ok _ (by simp)) SC (oP 1) SC (oP 0) SC (oP (s1B p + r)) (by ofsd)
      (fun _ _ _ h => ⟨h.it.kd.ctx, h.c.1, (fam_at h.it.kd.dk.f1 hr).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps c' (by decide) fr (by ofsd), by
        rw [h.c.2, (fam_at h.it.kd.dk.f1 hr).2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t r) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) r) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t1P) (nttInv (multiplyNTT (chF (Cv p s₀ (p.ℓ * t))) (S1 p s₀ r))))
    (inPlace_piece (t := nttInv) F.invNtt (F.ok _ (by simp)) t1P rfl (by ofsd) (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps c' (by decide) fr (by ofsd), by rw [h.2.2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := CS p t (zY p t (r + 1)) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) r) (fun _ => 0))
    (acc_piece (op := add) F.add (F.ok _ (by simp)) SC (oP (yB p + r)) SC (oP 1) (by ofsd)
      (fun _ _ _ h => ⟨h.1.it.kd.ctx, (fam_at h.1.fy hr).1, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => h.1.updY hp ps c' hr fr (by
        rw [(fam_at h.1.fy hr).2, h.2.2, zY_ge (Nat.lt_irrefl r)] at hq
        rw [zY_lt (Nat.lt_succ_self r)]; exact hq) fun j _ hjr => upd_step hjr) ?_
  refine (normAnd_piece F ps (yB p + r) hy (p.γ₁ - p.β) (by omega_arith) (fun s₀ => Zv p s₀ (p.ℓ * t) r)).mono
    (fun s₀ s _ h => ⟨h, by have := fam_at h.fy hr; rwa [zY_lt (Nat.lt_succ_self r)] at this⟩)
    fun s₀ s _ h => h.1.congr (fun _ _ => rfl)
      (fun _ _ => rfl) (by simp only [okZ, all_range_succ])

/-! ## `r₀` -/

/-- `w[i] - NTT⁻¹(ĉ ŝ₂[i])` in place of `w[i]`, and the norm of its `LowBits`. -/
theorem r0R_piece (F : PrimsOk P) (ps : PS p) (t i : Nat) (hi : i < p.k) :
    SP p (CS p t (zY p t p.ℓ) (rW p t i) 0 (fun s₀ => okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) i) (fun _ => 0))
      (CS p t (zY p t p.ℓ) (rW p t (i + 1)) 0 (fun s₀ => okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) (i + 1))
        (fun _ => 0)) (r0R P p i) := by
  obtain hj : s2B p + i < nS p := by simp only [nS, s2B]; omega_arith
  have hβ := ps.hβ
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t p.ℓ) (rW p t i) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) i) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t1P) (multiplyNTT (chF (Cv p s₀ (p.ℓ * t))) (S2 p s₀ i)))
    (mul_piece F.mul (F.ok _ (by simp)) SC (oP 1) SC (oP 0) SC (oP (s2B p + i)) (by ofsd)
      (fun _ _ _ h => ⟨h.it.kd.ctx, h.c.1, (fam_at h.it.kd.dk.f2 hi).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps c' (by decide) fr (by ofsd), by
        rw [h.c.2, (fam_at h.it.kd.dk.f2 hi).2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t p.ℓ) (rW p t i) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) i) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t1P) (nttInv (multiplyNTT (chF (Cv p s₀ (p.ℓ * t))) (S2 p s₀ i))))
    (inPlace_piece (t := nttInv) F.invNtt (F.ok _ (by simp)) t1P rfl (by ofsd) (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps c' (by decide) fr (by ofsd), by rw [h.2.2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := CS p t (zY p t p.ℓ) (rW p t (i + 1)) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) i) (fun _ => 0))
    (acc_piece (op := sub) F.sub (F.ok _ (by simp)) SC (oP (wB p + i)) SC (oP 1) (by ofsd)
      (fun _ _ _ h => ⟨h.1.it.kd.ctx, (fam_at h.1.fw hi).1, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => h.1.updW hp ps c' hi fr (by
        rw [(fam_at h.1.fw hi).2, h.2.2, rW_ge (Nat.lt_irrefl i)] at hq
        rw [rW_lt (Nat.lt_succ_self i)]; exact hq) fun j _ hji => upd_step hji) ?_
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t p.ℓ) (rW p t (i + 1)) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) i) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t2P) (R0v p s₀ (p.ℓ * t) i))
    (lb_piece F.lowBits (F.ok _ (by simp)) p.γ₂ ps.hγ₂ SC (oP (wB p + i)) SC (oP 2) (by ofsd)
      (fun _ _ _ h => ⟨h.it.kd.ctx, (fam_at h.fw hi).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps c' (by decide) fr (by ofsd), by
        rw [(fam_at h.fw hi).2, rW_lt (Nat.lt_succ_self i)] at hq; exact hq⟩) ?_
  refine (normAnd_piece F ps 2 (by simp only [nS]; omega_arith) (p.γ₂ - p.β) (by omega_arith) (fun s₀ => R0v p s₀ (p.ℓ * t) i)).mono
    (fun s₀ s _ h => h) fun s₀ s _ h => h.1.congr (fun _ _ => rfl) (fun _ _ => rfl)
      (by simp only [okR, all_range_succ, Bool.and_assoc])

/-! ## `ct₀` and the hint -/

theorem zq_sub_add (a b : Zq) : a - (a + b) = -b := by
  apply Fin.ext
  obtain ha := a.isLt; have hb := b.isLt
  simp only [Fin.sub_def, Fin.add_def, Fin.neg_def, q] at *
  omega_arith

theorem sub_add_neg (a b : Poly) : sub a (add a b) = neg b := by
  apply Vector.ext
  intro j hj
  simp only [sub, add, neg, Vector.getElem_zipWith, Vector.getElem_map, zq_sub_add]

theorem hintOnes_le (h : Vector Bool n) : hintOnes [h] ≤ 256 := by
  rw [hintOnes_single]
  exact Nat.le_trans (List.length_filter_le _ _) (by rw [Vector.length_toList])

theorem sum_range_succ (f : Nat → Nat) (i : Nat) :
    ((List.range (i + 1)).map f).sum = ((List.range i).map f).sum + f i := by
  simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, Nat.add_zero]

theorem onesS_succ {s₀ : State} {κ i : Nat} : onesS p s₀ κ (i + 1) = onesS p s₀ κ i + hintOnes [Hv p s₀ κ i] :=
  sum_range_succ _ i

theorem onesS_le {s₀ : State} {κ : Nat} : ∀ i, onesS p s₀ κ i ≤ 256 * i
  | 0 => by simp [onesS]
  | i + 1 => by rw [onesS_succ]; have := onesS_le (s₀ := s₀) (κ := κ) i; have := hintOnes_le (Hv p s₀ κ i); omega_arith

/-- `ONES ← ONES + eax`, with `eax` the number of 1s of the hint's polynomial `nh - 1`. -/
theorem CS.addOnes {t nh : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s) (c' : Ctx (Y p) s₀ s')
    (fr : Frame (FR s₀ [sc oONES 4] 0) s.mem s'.mem) {x : State → Nat}
    (v : scw s₀ s' oONES = scw s₀ s oONES + s.gpr .eax) (he : (s.gpr .eax).toNat = x s₀)
    (hb : ones s₀ + x s₀ < 2 ^ 32) : CS p t fY fW nh okb (fun s₀ => ones s₀ + x s₀) s₀ s' := by
  have := h.nh
  refine ⟨h.it.keep hp ps c' (N := 80) (by decide) (fr0 hp (by decide) fr) (by ofsd),
    h.ct_keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by ofsd),
    keepP hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (j := 0) (by simp only [nS]; omega_arith) (by ofsd) h.c,
    h.fy.keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by simp only [nS, yB]; omega_arith) (by ofsd),
    h.fw.keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by simp only [nS, wB]; omega_arith) (by ofsd),
    h.fh.keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by simp only [nS]; omega_arith) (by ofsd), ?_, ?_, h.nh⟩
  · rw [scw, keepW' hp (N := 80) (by decide) (fr0 hp (by decide) fr) (sc_ok' ps (by decide) (by decide)) (by ofsd)]
    exact h.ok
  · rw [v, h.ones]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, he, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := ones s₀) (by omega_arith),
      Nat.mod_eq_of_lt hb]

/-- The hint's polynomial `nh`, made. -/
theorem CS.addHint {t nh : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s) (c' : Ctx (Y p) s₀ s')
    (hn : nh < p.k) (fr : Frame (FR s₀ [pS (5 + nh)] 80) s.mem s'.mem)
    (hh : HintIs s'.mem (Buf.addr s₀ (pS (5 + nh))) 1 [Hv p s₀ (p.ℓ * t) nh]) :
    CS p t fY fW (nh + 1) okb ones s₀ s' :=
  have k := h.keep hp ps c' (by decide) fr (by ofsd)
  { k with fh := k.fh.snoc hh, nh := hn }

/-- The okays of the checks of `ct₀` so far. -/
abbrev okH (p : Params) (t i : Nat) (s₀ : State) : Bool :=
  okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) p.k && okT p s₀ (p.ℓ * t) i

/-- `ct₀[i]` and its norm, `w - cs₂ + ct₀` in place of `w[i]`, and `h[i]`. -/
theorem hR_piece (F : PrimsOk P) (ps : PS p) (t i : Nat) (hi : i < p.k) :
    SP p (CS p t (zY p t p.ℓ) (hW p t i) i (okH p t i) (fun s₀ => onesS p s₀ (p.ℓ * t) i))
      (CS p t (zY p t p.ℓ) (hW p t (i + 1)) (i + 1) (okH p t (i + 1)) (fun s₀ => onesS p s₀ (p.ℓ * t) (i + 1)))
      (hR P p i) := by
  obtain hj : t0B p + i < nS p := by simp only [nS, t0B]; omega_arith
  obtain hwj : wB p + i < nS p := by simp only [nS, wB]; omega_arith
  have hk := ps.hk
  have hβ := ps.hβ
  let H0 : State → State → Prop := CS p t (zY p t p.ℓ) (hW p t i) i (okH p t i) (fun s₀ => onesS p s₀ (p.ℓ * t) i)
  let H1 : State → State → Prop := CS p t (zY p t p.ℓ) (hW p t i) i
    (fun s₀ => okH p t i s₀ && decide (normRq [CT0v p s₀ (p.ℓ * t) i] < p.γ₂)) (fun s₀ => onesS p s₀ (p.ℓ * t) i)
  let H2 : State → State → Prop := CS p t (zY p t p.ℓ) (hW p t (i + 1)) i
    (fun s₀ => okH p t i s₀ && decide (normRq [CT0v p s₀ (p.ℓ * t) i] < p.γ₂)) (fun s₀ => onesS p s₀ (p.ℓ * t) i)
  refine Piece.seq (B := fun s₀ s => H0 s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t3P) (multiplyNTT (chF (Cv p s₀ (p.ℓ * t))) (T0 p s₀ i)))
    (mul_piece F.mul (F.ok _ (by simp)) SC (oP 3) SC (oP 0) SC (oP (t0B p + i)) (by ofsd)
      (fun _ _ _ h => ⟨h.it.kd.ctx, h.c.1, (fam_at h.it.kd.dk.f0 hi).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps c' (by decide) fr (by ofsd), by
        rw [h.c.2, (fam_at h.it.kd.dk.f0 hi).2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => H0 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS 3)) (CT0v p s₀ (p.ℓ * t) i))
    (inPlace_piece (t := nttInv) F.invNtt (F.ok _ (by simp)) t3P rfl (by ofsd) (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps c' (by decide) fr (by ofsd), by rw [h.2.2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => H1 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS 3)) (CT0v p s₀ (p.ℓ * t) i))
    (normAnd_piece F ps 3 (by simp only [nS]; omega_arith) p.γ₂ (by omega_arith) (fun s₀ => CT0v p s₀ (p.ℓ * t) i)) ?_
  refine Piece.seq (B := fun s₀ s => (H1 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS 3)) (CT0v p s₀ (p.ℓ * t) i)) ∧
      PolyIs s.mem (Buf.addr s₀ t4P) (W'v p s₀ (p.ℓ * t) i))
    (copy_piece SC (oP (wB p + i)) SC (oP 4) 256 (by decide) (by decide) (by ofsd) (fun _ _ _ h => h.1.it.kd.ctx)
      fun s₀ s s' hp h c' fr hb => by
        obtain fr' : Frame (FR s₀ [t4P] 80) s.mem s'.mem := fr.mono (by simp)
        obtain hw := fam_at h.1.fw hi
        rw [hW_ge (Nat.lt_irrefl i)] at hw
        exact ⟨⟨h.1.keep hp ps c' (by decide) fr' (by ofsd), keepP hp ps (by decide) fr' (by simp only [nS]; omega_arith)
          (by ofsd) h.2⟩, polyIs_of_bytes hb hw⟩) ?_
  refine Piece.seq (B := fun s₀ s => H2 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ t4P) (W'v p s₀ (p.ℓ * t) i))
    (acc_piece (op := add) F.add (F.ok _ (by simp)) SC (oP (wB p + i)) SC (oP 3) (by ofsd)
      (fun _ _ _ h => ⟨h.1.1.it.kd.ctx, (fam_at h.1.1.fw hi).1, h.1.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.1.updW hp ps c' hi fr (by
        rw [(fam_at h.1.1.fw hi).2, h.1.2.2, hW_ge (Nat.lt_irrefl i)] at hq
        rw [hW_lt (Nat.lt_succ_self i)]; exact hq) fun j _ hji => upd_step hji,
        keepP hp ps (by decide) fr (by simp only [nS]; omega_arith) (by ofsd) h.2⟩) ?_
  refine Piece.seq (B := fun s₀ s => H2 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ t4P) (neg (CT0v p s₀ (p.ℓ * t) i)))
    (acc_piece (op := sub) F.sub (F.ok _ (by simp)) SC (oP 4) SC (oP (wB p + i)) (by ofsd)
      (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1, (fam_at h.1.fw hi).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps c' (by decide) fr (by ofsd), by
        rw [h.2.2, (fam_at h.1.fw hi).2, hW_lt (Nat.lt_succ_self i)] at hq
        rw [← sub_add_neg]; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t p.ℓ) (hW p t (i + 1)) (i + 1)
      (fun s₀ => okH p t i s₀ && decide (normRq [CT0v p s₀ (p.ℓ * t) i] < p.γ₂)) (fun s₀ => onesS p s₀ (p.ℓ * t) i) s₀ s ∧
      (s.gpr .eax).toNat = hintOnes [Hv p s₀ (p.ℓ * t) i])
    (hint_piece F.makeHint (F.ok _ (by simp)) p.γ₂ ps.hγ₂ SC (oP 4) SC (oP (wB p + i)) SC (oP (5 + i)) (by ofsd)
      (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1, (fam_at h.1.fw hi).1⟩)
      fun s₀ s s' hp h c' fr hh he => by
        rw [h.2.2, (fam_at h.1.fw hi).2, hW_lt (Nat.lt_succ_self i)] at hh he
        exact ⟨h.1.addHint hp ps c' hi fr hh, he⟩) ?_
  refine blk_piece (fun _ _ _ h => h.1.it.kd.ctx) (fun s₀ s hp h => wp_addOnes hp h.1.it.kd.ctx ps
    fun s' c' fr v => ?_) rfl
  obtain hb : onesS p s₀ (p.ℓ * t) i + hintOnes [Hv p s₀ (p.ℓ * t) i] < 2 ^ 32 := by
    have := onesS_le (p := p) (s₀ := s₀) (κ := p.ℓ * t) i; have := hintOnes_le (Hv p s₀ (p.ℓ * t) i); omega_arith
  obtain k := (h.1.addOnes hp ps c' fr (x := fun s₀ => hintOnes [Hv p s₀ (p.ℓ * t) i]) v h.2 hb).congr
    (fun _ _ => rfl) (fun _ _ => rfl) (okb' := okH p t (i + 1)) (by simp only [okH, okT, all_range_succ, Bool.and_assoc])
  exact { k with ones := by rw [k.ones, onesS_succ] }

/-! ## The 1s of the hint -/

theorem sign_bit {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b) >>> 31 = if a < b then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  split
  · show _ = 1
    rw [Nat.shiftRight_eq_div_pow]; omega_arith
  · show _ = 0
    rw [Nat.shiftRight_eq_div_pow]; omega_arith

/-- The okays of all of the checks. -/
abbrev okAll (p : Params) (t : Nat) (s₀ : State) : Bool :=
  okH p t p.k s₀ && decide (onesS p s₀ (p.ℓ * t) p.k ≤ p.ω)

/-- `OK ← OK ∧ ONES ≤ ω`. -/
theorem onesOk_piece (ps : PS p) (t : Nat) :
    SP p (CS p t (zY p t p.ℓ) (hW p t p.k) p.k (okH p t p.k) (fun s₀ => onesS p s₀ (p.ℓ * t) p.k))
      (CS p t (zY p t p.ℓ) (hW p t p.k) p.k (okAll p t) (fun s₀ => onesS p s₀ (p.ℓ * t) p.k)) (.block (onesOk p)) := by
  refine blk_piece (fun _ _ _ h => h.it.kd.ctx) (fun s₀ s hp h => ?_) rfl
  have hω := ps.hω
  have hk := ps.hk
  obtain hS := onesS_le (p := p) (s₀ := s₀) (κ := p.ℓ * t) p.k
  unfold onesOk
  refine wp_ldsc hp h.it.kd.ctx (sc_ok' ps (by decide) (by decide)) fun s₁ o₁ v₁ => wp_subi fun s₂ o₂ v₂ _ =>
    wp_shr (by decide) (by decide) fun s₃ o₃ v₃ => ?_
  obtain o := (o₁.trans o₂).trans o₃
  obtain c₃ := h.it.kd.ctx.only o (by simp) (by simp)
  obtain h₃ : CS p t (zY p t p.ℓ) (hW p t p.k) p.k (okH p t p.k) (fun s₀ => onesS p s₀ (p.ℓ * t) p.k) s₀ s₃ :=
    h.keep hp ps c₃ (N := 0) (bs := []) (by decide) (by rw [o.mem]; exact Frame.refl _ _) (by simp)
  refine wp_andOK hp c₃ ps fun s' c' fr v => h₃.setOK hp ps c' fr (fun s₀ => decide (onesS p s₀ (p.ℓ * t) p.k ≤ p.ω)) v ?_
  rw [v₃, v₂, v₁, h.ones, sign_bit (by omega_arith) (by omega_arith)]
  by_cases e : onesS p s₀ (p.ℓ * t) p.k ≤ p.ω
  · rw [ifp (by omega_arith), decide_eq_true e]; rfl
  · rw [ifn (by omega_arith), decide_eq_false e]; rfl

/-! ## The end of the checks -/

/-- A piece keeps facts about the initial state. -/
theorem sp_pure {A B : State → State → Prop} {c : Prog isa} (φ : State → Prop) (h : SP p A B c) :
    SP p (fun s₀ s => A s₀ s ∧ φ s₀) (fun s₀ s => B s₀ s ∧ φ s₀) c where
  wp s₀ s hp ha := (h.wp s₀ s hp ha.1).mono fun _ hb => ⟨hb, ha.2⟩
  ct s₀ s₀' hp hp' hq := (h.ct s₀ s₀' hp hp' hq).mono (fun _ _ ⟨a, a'⟩ => ⟨a.1, a'.1⟩) fun _ _ h => h

/-- Iteration `t` continues the loop. -/
abbrev contS (p : Params) (F : PrimsOk P) (t : Nat) (s₀ : State) : Bool :=
  contV p (skOf p s₀) (muOf s₀) (rndOf s₀) F.ballF t

/-- The checks of iteration `t` pass. -/
abbrev passS (p : Params) (t : Nat) (s₀ : State) : Prop := passV p (skOf p s₀) (muOf s₀) (rndOf s₀) (p.ℓ * t)

/-- Iteration `t`, before `CNT ← CNT - 1`. -/
structure ED (p : Params) (F : PrimsOk P) (t : Nat) (s₀ s : State) : Prop where
  kd : KD p s₀ s
  run : Run p F t s₀
  cnt : scw s₀ s oCNT = if contS p F t s₀ then BitVec.ofNat 32 (814 - t) else 1
  kap : contS p F t s₀ = true → scw s₀ s oKAP = BitVec.ofNat 32 (p.ℓ * (t + 1))
  ok : scw s₀ s oOK = if (F.ballF p.τ (CTv p s₀ (p.ℓ * t)) && decide (passS p t s₀)) then 1 else 0
  out : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = true → passS p t s₀ →
    Fam s₀ s.mem (yB p) p.ℓ (Zv p s₀ (p.ℓ * t)) ∧ HF s₀ s.mem p.k (Hv p s₀ (p.ℓ * t)) ∧
      bytesAt s.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = CTv p s₀ (p.ℓ * t)
  none : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = false → sampleInBall p.τ minBounds.ball (CTv p s₀ (p.ℓ * t)) = none

theorem KD.keep {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : KD p s₀ s) (c' : Ctx (Y p) s₀ s')
    {bs : List Buf} {N : Nat} (hN : N ≤ 80) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (hb : ∀ c ∈ bs, OutK p p.ℓ p.k p.k c ∧ Out p oMS (oMS + 64) c) : KD p s₀ s' :=
  ⟨c', h.dk.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hN fr fun c hc => (hb c hc).1,
    by rw [keepB hp hN fr (sc_ok' ps (by decide) (by decide)) fun c hc => (hb c hc).2, h.ms]⟩

theorem okAll_eq {t : Nat} {s₀ : State} : okAll p t s₀ = decide (passS p t s₀) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  exact pass_iff.symm

/-- Whether the checks passed, in a run that reaches iteration `t` and whose `SampleInBall` succeeded. -/
def passB (p : Params) (F : PrimsOk P) (t : Nat) (s₀ : State) : Bool :=
  decide (Run p F t s₀ ∧ F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = true ∧ passS p t s₀)

theorem passB_eq {F : PrimsOk P} {t : Nat} {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') :
    passB p F t s₀ = passB p F t s₀' := by
  unfold passB
  by_cases h : Run p F t s₀
  · have h' := (run_iff ps hq).mp h
    obtain ⟨ect, hb⟩ := run_at ps hq h
    by_cases hs : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = true
    · have hs' : F.ballF p.τ (CTv p s₀' (p.ℓ * t)) = true := by rw [← ect]; exact hs
      exact decide_eq_decide.mpr ⟨fun ⟨_, _, a⟩ => ⟨h', hs', (hb hs).1.mp a⟩, fun ⟨_, _, a⟩ => ⟨h, hs, (hb hs).1.mpr a⟩⟩
    · have hs' : ¬ F.ballF p.τ (CTv p s₀' (p.ℓ * t)) = true := by rw [← ect]; exact hs
      exact decide_eq_decide.mpr ⟨fun ⟨_, a, _⟩ => absurd a hs, fun ⟨_, a, _⟩ => absurd a hs'⟩
  · exact decide_eq_decide.mpr ⟨fun ⟨a, _⟩ => absurd a h, fun ⟨a, _⟩ => absurd ((run_iff ps hq).mpr a) h⟩

theorem CS.ofMem {t nh : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s') (c : Ctx (Y p) s₀ s)
    (hm : s.mem = s'.mem) : CS p t fY fW nh okb ones s₀ s :=
  h.keep hp ps c (N := 0) (bs := []) (by decide) (by rw [hm]; exact Frame.refl _ _) (by simp)

/-- Only an accepted candidate needs complete response and hint buffers. -/
structure CE (p : Params) (F : PrimsOk P) (t : Nat) (s₀ s : State) : Prop where
  it : IT p t s₀ s
  run : Run p F t s₀
  ball : F.ballF p.τ (CTv p s₀ (p.ℓ*t)) = true
  ok : scw s₀ s oOK = if decide (passS p t s₀) then 1 else 0
  out : passS p t s₀ → Fam s₀ s.mem (yB p) p.ℓ (Zv p s₀ (p.ℓ*t)) ∧
    HF s₀ s.mem p.k (Hv p s₀ (p.ℓ*t)) ∧
    bytesAt s.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = CTv p s₀ (p.ℓ*t)

theorem CE.ofMem {F : PrimsOk P} {t : Nat} {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p)
    (h : CE p F t s₀ s') (ctx : Ctx (Y p) s₀ s) (hm : s.mem=s'.mem) : CE p F t s₀ s := by
  obtain fr : Frame (FR s₀ [] 0) s'.mem s.mem := by rw [hm]; exact Frame.refl _ _
  exact ⟨h.it.keep hp ps ctx (by decide) fr (by simp), h.run, h.ball,
    by rw [scw, hm]; exact h.ok, fun hp => by rw [hm]; exact h.out hp⟩

/-- `CNT ← 1` if the checks passed, and `κ ← κ + ℓ` otherwise. -/
theorem checksEnd_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (CE p F t) (ED p F t) (ifOkElse (.block (st32 oCNT 1)) (.block (nextKappa p))) := by
  refine okIte_piece (sc_ok' ps (by decide) (by decide)) (passB p F t) (fun s₀ s hp h => ⟨h.it.kd.ctx, ?_⟩)
    (fun s₀ s₀' _ _ hq => passB_eq ps hq) ?_ ?_
  · rw [h.ok]
    simp only [passB, h.run, h.ball, true_and]
  · refine blk_piece (fun _ _ _ h => h.1.choose_spec.2.1) (fun s₀ s₁ hp h => ?_) rfl
    obtain ⟨⟨s, ha, c₁, m₁⟩, hb⟩ := h
    obtain h₁ := ha.ofMem hp ps c₁ m₁
    simp only [passB, decide_eq_true_iff] at hb
    rw [← List.append_nil (st32 oCNT 1)]
    refine wp_st32 hp c₁ (sc_ok ps (by decide) (by decide)) 1 fun s' c' fr v => WP.block_nil_iff.mpr ?_
    obtain fr' := fr0 hp (N := 80) (by decide) fr
    obtain hc : contS p F t s₀ = false := by
      simp only [contS, contV, hb.2.2, decide_true, Bool.not_true, Bool.and_false]
    obtain ⟨hz, hh, hct⟩ := h₁.out hb.2.2
    refine ⟨h₁.it.kd.keep hp ps c' (by decide) fr' (by ofsd), hb.1, by rw [hc, v]; rfl, (fun e => by rw [hc] at e; cases e),
      ?_, fun _ _ => ⟨?_, hh.keep hp ps (by decide) fr' (by simp only [nS]; omega_arith) (by ofsd),
        by rw [keepB hp (by decide) fr' (sc_ok' ps (by ofsd) (by ofsd)) (by ofsd)]; exact hct⟩, (fun e => by rw [hb.2.1] at e; cases e)⟩
    · rw [scw, keepW' hp (by decide) fr' (sc_ok' ps (by decide) (by decide)) (by ofsd), ← scw, h₁.ok,
        hb.2.1, Bool.true_and]
    · exact hz.keep hp ps (by decide) fr' (by simp only [nS,yB]; omega_arith) (by ofsd)
  · refine blk_piece (fun _ _ _ h => h.1.choose_spec.2.1) (fun s₀ s₁ hp h => ?_) rfl
    obtain ⟨⟨s, ha, c₁, m₁⟩, hb⟩ := h
    obtain h₁ := ha.ofMem hp ps c₁ m₁
    obtain hpass : ¬ passS p t s₀ := fun hq => by
      simp only [passB, decide_eq_false_iff_not] at hb; exact hb ⟨ha.run, ha.ball, hq⟩
    obtain hc : contS p F t s₀ = true := by
      simp only [contS, contV, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
      exact ⟨ha.ball, hpass⟩
    unfold nextKappa
    refine wp_ldsc hp c₁ (sc_ok' ps (by decide) (by decide)) fun s₂ o₂ v₂ => wp_addi fun s₃ o₃ v₃ => ?_
    obtain o := o₂.trans o₃
    obtain c₃ := c₁.only o (by simp) (by simp)
    refine wp_stsc hp c₃ (sc_ok ps (by decide) (by decide)) fun s' c' g' m' => WP.block_nil_iff.mpr ?_
    obtain fr : Frame (FR s₀ [sc oKAP 4] 80) s₁.mem s'.mem := fr0 hp (by decide) (by
      rw [m', o.mem]; exact frW32 (Y := Y p))
    refine ⟨h₁.it.kd.keep hp ps c' (by decide) fr (by ofsd), ha.run, ?_, fun _ => ?_, ?_,
      (fun _ e => absurd e hpass), (fun e => by rw [ha.ball] at e; cases e)⟩
    · rw [hc, scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofsd), ← scw, h₁.it.cnt]; rfl
    · rw [scw, m', Mem.readW_writeW_self32, v₃, v₂, h₁.it.kap, ← BitVec.ofNat_add, Nat.mul_succ]
    · rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofsd), ← scw, h₁.ok,
        decide_eq_false hpass, Bool.and_false]

/-- A sequence of checks stops at its first false public prefix predicate. -/
theorem seqOk_piece {I : Nat → State → State → Prop} {f : Nat → Prog isa} (b : Nat → State → Bool) (limit : Nat)
    (hc : (Y p).ok (sc oOK 4) = true)
    (hctx : ∀ k s₀ s, TPre (Y p) s₀ → I k s₀ s → Ctx (Y p) s₀ s)
    (hok : ∀ k s₀ s, I k s₀ s → scw s₀ s oOK = if b k s₀ then 1 else 0)
    (hmem : ∀ k s₀ s s', TPre (Y p) s₀ → I k s₀ s → Ctx (Y p) s₀ s' → s'.mem=s.mem → I k s₀ s')
    (hpub : ∀ k, k≤limit → ∀ x y, TPre (Y p) x → TPre (Y p) y → SPub p x y → b k x=b k y) :
    ∀ (a n : Nat), (∀ k, a≤k → k<a+n → SP p (I k) (I (k+1)) (f k)) → a+n≤limit →
      SP p (I a) (fun s₀ s => ∃ k, a≤k ∧ k≤a+n ∧ I k s₀ s ∧ (k=a+n ∨ b k s₀=false)) (seqOk f a n)
  | a, 0, _, _ => nil_piece fun _ _ _ h => ⟨a, Nat.le_refl _, by omega_using [], h, .inl (by omega_using [])⟩
  | a, n+1, h, hbound => by
    rw [seqOk]
    refine Piece.seq (h a (Nat.le_refl _) (by omega_using [])) ?_
    refine okIte_piece hc (b (a+1)) (fun s₀ s hp hi => ⟨hctx _ _ _ hp hi, hok _ _ _ hi⟩) (hpub (a+1) (by omega_using [hbound])) ?_ ?_
    · refine (seqOk_piece b limit hc hctx hok hmem hpub (a+1) n (fun k hk hk' => h k (by omega_using [hk]) (by omega_using [hk'])) (by omega_using [hbound])).mono
        (fun s₀ s hp h => ?_) (fun s₀ s hp ⟨k,ha,hb,hi,hd⟩ => ⟨k,by omega_using [ha],by omega_using [hb],hi,hd.imp (fun _ => by omega_arith) id⟩)
      obtain ⟨⟨s',hi,ctx,hm⟩,_⟩ := h
      exact hmem _ _ _ _ hp hi ctx hm
    · refine nil_piece fun s₀ s hp h => ?_
      obtain ⟨⟨s',hi,ctx,hm⟩,hb⟩ := h
      exact ⟨a+1,by omega_using [],by omega_using [],hmem _ _ _ _ hp hi ctx hm,.inr hb⟩

/-- A complete phase continues only when every polynomial passed. -/
theorem until_piece {B : State → State → Prop} {J : Nat → State → State → Prop}
    {f : Nat → Prog isa} {cont : Prog isa} (b : Nat → State → Bool) (n : Nat)
    (hc : (Y p).ok (sc oOK 4)=true)
    (hctx : ∀ k s₀ s, TPre (Y p) s₀ → J k s₀ s → Ctx (Y p) s₀ s)
    (hok : ∀ k s₀ s, J k s₀ s → scw s₀ s oOK=if b k s₀ then 1 else 0)
    (hmem : ∀ k s₀ s s', TPre (Y p) s₀ → J k s₀ s → Ctx (Y p) s₀ s' → s'.mem=s.mem → J k s₀ s')
    (hpub : ∀ k, k≤n → ∀ x y, TPre (Y p) x → TPre (Y p) y → SPub p x y → b k x=b k y)
    (hmono : ∀ k s₀ s, k≤n → J k s₀ s → b n s₀=true → b k s₀=true)
    (hfail : ∀ k s₀ s, TPre (Y p) s₀ → k≤n → J k s₀ s → b k s₀=false → B s₀ s)
    (hstep : ∀ k, k<n → SP p (J k) (J (k+1)) (f k))
    (hcont : SP p (J n) B cont) :
    SP p (J 0) B (.seq (seqOk f 0 n) (ifOk cont)) := by
  refine Piece.seq (seqOk_piece b n hc hctx hok hmem hpub 0 n (fun k _ hk => hstep k (by omega_using [hk])) (by omega_using [])) ?_
  refine okIte_piece hc (b n) (fun s₀ s hp ⟨k,_,hk,hj,hd⟩ => ⟨hctx k _ _ hp hj,?_⟩) (hpub n (Nat.le_refl _)) ?_ ?_
  · rw [hok k _ _ hj]
    rcases hd with he|hb
    · simpa only [Nat.zero_add] using congrArg (fun k => if b k s₀ then (1 : BitVec 32) else 0) he
    · have hn : b n s₀=false := Bool.eq_false_iff.mpr (fun h => by
        have := hmono k _ _ (by omega_using [hk]) hj h; rw [hb] at this; cases this)
      rw [hb,hn]
  · refine hcont.mono (fun s₀ s hp h => ?_) (fun _ _ _ h => h)
    obtain ⟨⟨s',⟨k,_,hk,hj,hd⟩,ctx,hm⟩,hb⟩ := h
    obtain hk' : k=n := by
      rcases hd with hd|hd
      · omega_using [hd]
      · have := hmono k _ _ (by omega_using [hk]) hj hb; rw [hd] at this; cases this
    subst hk'
    exact hmem _ _ _ _ hp hj ctx hm
  · refine nil_piece fun s₀ s hp h => ?_
    obtain ⟨⟨s',⟨k,_,hk,hj,hd⟩,ctx,hm⟩,hb⟩ := h
    obtain hj' := hmem _ _ _ _ hp hj ctx hm
    apply hfail k _ _ hp (by omega_using [hk]) hj'
    rcases hd with hd|hd
    · simpa only [Nat.zero_add,hd] using hb
    · exact hd

/-- Prefix outcomes made total by requiring a reached iteration and a sampled challenge. -/
def prefixB (p : Params) (F : PrimsOk P) (t : Nat) (r0 : Bool) (k : Nat) (s₀ : State) : Bool :=
  decide (Run p F t s₀ ∧ F.ballF p.τ (CTv p s₀ (p.ℓ*t))=true) &&
    (if r0 then okZ p s₀ (p.ℓ*t) p.ℓ && okR p s₀ (p.ℓ*t) k else okZ p s₀ (p.ℓ*t) k)

theorem prefixB_eq {F : PrimsOk P} {t k : Nat} {r0 : Bool} (ps : PS p)
    (hk : k ≤ if r0 then p.k else p.ℓ) {x y : State} (hq : SPub p x y) :
    prefixB p F t r0 k x = prefixB p F t r0 k y := by
  unfold prefixB
  by_cases hr : Run p F t x
  · have hr' := (run_iff ps hq).mp hr
    obtain ect := (run_at ps hq hr).1
    by_cases hb : F.ballF p.τ (CTv p x (p.ℓ*t))=true
    · have hb' : F.ballF p.τ (CTv p y (p.ℓ*t))=true := by rw [←ect]; exact hb
      simp only [hr,hr',hb,hb',and_self,decide_true,Bool.true_and]
      obtain ha := run_agree ps hq hr (F.ballMax _ _ hb) (F.ballMax _ _ hb')
      apply Bool.eq_iff_iff.mpr
      cases r0 <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · exact (all_range_iff.trans ((ha.1 k hk).trans all_range_iff.symm))
      · simp only [Bool.and_eq_true,okZ,okR,all_range_iff]
        exact ha.2.1 k hk
    · have hb' : ¬ F.ballF p.τ (CTv p y (p.ℓ*t))=true := by rw [←ect]; exact hb
      simp [hr,hr',hb,hb']
  · have hr' : ¬ Run p F t y := fun h => hr ((run_iff ps hq).mpr h)
    simp only [hr,hr',false_and,decide_false,Bool.false_and]

abbrev Reached (p : Params) (F : PrimsOk P) (t : Nat) (s₀ : State) : Prop :=
  Run p F t s₀ ∧ F.ballF p.τ (CTv p s₀ (p.ℓ*t))=true
abbrev ZCS (p : Params) (F : PrimsOk P) (t r : Nat) (s₀ s : State) : Prop :=
  CS p t (zY p t r) (fun s₀=>Wv p s₀ (p.ℓ*t)) 0 (fun s₀=>okZ p s₀ (p.ℓ*t) r) (fun _=>0) s₀ s ∧ Reached p F t s₀
abbrev RCS (p : Params) (F : PrimsOk P) (t i : Nat) (s₀ s : State) : Prop :=
  CS p t (zY p t p.ℓ) (rW p t i) 0 (fun s₀=>okZ p s₀ (p.ℓ*t) p.ℓ && okR p s₀ (p.ℓ*t) i) (fun _=>0) s₀ s ∧ Reached p F t s₀

/-- Full passing prefixes imply each earlier prefix passes. -/
theorem prefixB_mono {F : PrimsOk P} {t k n : Nat} {r0 : Bool} {s₀ : State} (hk : k≤n) :
    prefixB p F t r0 n s₀=true → prefixB p F t r0 k s₀=true := by
  simp only [prefixB,Bool.and_eq_true]
  rintro ⟨hr,hb⟩
  refine ⟨hr,?_⟩
  cases r0 <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hb ⊢
  · exact all_range_iff.mpr (fun j hj => all_range_iff.mp hb j (by omega_using [hk, hj]))
  · obtain ⟨hz,hb⟩ := Bool.and_eq_true_iff.mp hb
    exact Bool.and_eq_true_iff.mpr ⟨hz,all_range_iff.mpr fun j hj=>all_range_iff.mp hb j (by omega_using [hk, hj])⟩

theorem rejectedCE {F : PrimsOk P} {t nh : Nat} {fy fw : State→Nat→Poly} {okb : State→Bool} {ones : State→Nat}
    {s₀ s : State} (h : CS p t fy fw nh okb ones s₀ s) (hr : Reached p F t s₀)
    (hno : ¬ passS p t s₀) (hb : okb s₀=false) : CE p F t s₀ s :=
  ⟨h.it,hr.1,hr.2,by rw [h.ok,hb,decide_eq_false hno],fun hp=>absurd hp hno⟩

theorem hints_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (RCS p F t p.k) (CE p F t) (.seq (seqR (hR P p) 0 p.k) (.block (onesOk p))) := by
  have hk := ps.hk
  have hl := ps.hl
  let φ := Reached p F t
  refine Piece.seq (B := fun s₀ s=>CS p t (zY p t p.ℓ) (hW p t p.k) p.k (okH p t p.k)
    (fun s₀=>onesS p s₀ (p.ℓ*t) p.k) s₀ s ∧ φ s₀) (sp_pure φ ?_) ?_
  · have h := seqR_piece (p:=p) (I:=fun i=>CS p t (zY p t p.ℓ) (hW p t i) i (okH p t i)
      (fun s₀=>onesS p s₀ (p.ℓ*t) i)) 0 p.k fun i _ hi=>hR_piece F ps t i (by omega_using [hi])
    simp only [Nat.zero_add] at h
    refine h.mono (fun s₀ s _ h=>?_) (fun _ _ _ h=>h)
    obtain h' := h.congr (fY':=zY p t p.ℓ) (fW':=hW p t 0) (okb':=okH p t 0) (fun _ _=>rfl)
      (fun j hj=>by rw [rW_lt hj,hW_ge (Nat.not_lt_zero j)]) (by simp [okH,okT])
    exact {h' with fh:=fun j hj=>absurd hj (Nat.not_lt_zero _),ones:=by rw [h'.ones];rfl,nh:=Nat.zero_le _}
  · refine (sp_pure φ (onesOk_piece ps t)).mono (fun _ _ _ h=>h) (fun s₀ s _ h=>?_)
    exact ⟨h.1.it,h.2.1,h.2.2,by rw [h.1.ok,okAll_eq],fun _=>
      ⟨h.1.fy.congr (fun j hj=>zY_lt hj),h.1.fh,h.1.ct⟩⟩

theorem r0checks_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (RCS p F t 0) (CE p F t) (checksR0 P p) := by
  have hk := ps.hk
  have hl := ps.hl
  unfold checksR0
  apply until_piece (J:=RCS p F t) (prefixB p F t true) p.k (sc_ok' ps (by decide) (by decide))
    (fun _ _ _ _ h=>h.1.it.kd.ctx)
    (fun k s₀ s h=>by rw [h.1.ok]; simp only [prefixB,h.2.1,h.2.2,true_and,decide_true,Bool.true_and,ite_true])
    (fun _ _ _ _ hp h ctx hm=>⟨h.1.ofMem hp ps ctx hm,h.2⟩)
    (fun k hk _ _ _ _ hq=>prefixB_eq ps (by simpa using hk) hq)
    (fun k _ _ hk _ hb=>prefixB_mono hk hb) ?_ ?_ (hints_piece F ps t)
  · intro k s₀ s hp hk h hb
    obtain raw : (okZ p s₀ (p.ℓ*t) p.ℓ && okR p s₀ (p.ℓ*t) k)=false := by
      simpa only [prefixB,h.2.1,h.2.2,true_and,decide_true,Bool.true_and,ite_true] using hb
    refine rejectedCE h.1 h.2 (fun hpass=>?_) raw
    obtain hz : okZ p s₀ (p.ℓ*t) p.ℓ=true := all_range_iff.mpr hpass.1
    obtain hr : okR p s₀ (p.ℓ*t) k=true := all_range_iff.mpr (fun j hj=>hpass.2.1 j (by omega_using [hk, hj]))
    rw [hz,hr] at raw; cases raw
  · intro i hi
    exact sp_pure (Reached p F t) (r0R_piece F ps t i hi)

theorem zchecks_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (ZCS p F t 0) (CE p F t) (.seq (seqOk (zR P p) 0 p.ℓ) (ifOk (checksR0 P p))) := by
  have hk := ps.hk
  have hl := ps.hl
  apply until_piece (J:=ZCS p F t) (prefixB p F t false) p.ℓ (sc_ok' ps (by decide) (by decide))
    (fun _ _ _ _ h=>h.1.it.kd.ctx)
    (fun k s₀ s h=>by rw [h.1.ok]; simp only [prefixB,h.2.1,h.2.2,true_and,decide_true,Bool.true_and,Bool.false_eq_true,ite_false])
    (fun _ _ _ _ hp h ctx hm=>⟨h.1.ofMem hp ps ctx hm,h.2⟩)
    (fun k hk _ _ _ _ hq=>prefixB_eq ps (by simpa using hk) hq)
    (fun k _ _ hk _ hb=>prefixB_mono hk hb) ?_ ?_ ?_
  · intro k s₀ s hp hk h hb
    obtain raw : okZ p s₀ (p.ℓ*t) k=false := by
      simpa only [prefixB,h.2.1,h.2.2,true_and,decide_true,Bool.true_and,Bool.false_eq_true,ite_false] using hb
    refine rejectedCE h.1 h.2 (fun hpass=>?_) raw
    obtain hz : okZ p s₀ (p.ℓ*t) k=true := all_range_iff.mpr (fun j hj=>hpass.1 j (by omega_using [hk, hj]))
    rw [hz] at raw; cases raw
  · intro i hi
    exact sp_pure (Reached p F t) (zR_piece F ps t i hi)
  · refine (r0checks_piece F ps t).mono (fun s₀ s _ h=>⟨?_,h.2⟩) (fun _ _ _ h=>h)
    exact h.1.congr (fun _ _=>rfl) (fun j _=>(rW_ge (Nat.not_lt_zero j)).symm) (by simp [okR])

/-! ## The checks -/

/-- The checks of iteration `t`, once `SampleInBall` succeeded. -/
theorem checks_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (fun s₀ s => KP p F t s₀ s ∧ PolyIs s.mem (Buf.addr s₀ cP) (toRq (Cv p s₀ (p.ℓ * t)))) (ED p F t)
      (checks P p) := by
  have hk := ps.hk
  have hl := ps.hl
  let φ : State → Prop := fun s₀ => Run p F t s₀ ∧ F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = true
  unfold checks
  refine Piece.seq (B := fun s₀ s => (CC p t s₀ s ∧ PolyIs s.mem (Buf.addr s₀ cP) (chF (Cv p s₀ (p.ℓ * t)))) ∧ φ s₀)
    ((inPlace_piece (t := ntt) F.ntt (F.ok _ (by simp)) cP rfl (by ofsd) (fun _ _ _ h => ⟨h.1.cc.cw.cm.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.cc.keep hp ps c' (by decide) fr (by ofsd), by rw [h.2.2] at hq; exact hq⟩).mono
        (fun _ _ _ h => h) (fun _ _ _ h => h) |> sp_pure φ |>.mono (fun _ _ _ h => ⟨h, h.1.run, h.1.ball⟩)
        fun _ _ _ h => h) ?_
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t 0) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) 0) (fun _ => 0) s₀ s ∧ φ s₀) (sp_pure φ (checksInit_piece ps t)) ?_
  exact Piece.seq (zchecks_piece F ps t) (checksEnd_piece F ps t)

end VG.Proof.MlDsa.X86.Sign
