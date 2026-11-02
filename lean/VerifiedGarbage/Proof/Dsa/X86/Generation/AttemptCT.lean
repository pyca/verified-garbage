module

import VerifiedGarbage.Proof.Dsa.X86.Generation.Attempt
public import VerifiedGarbage.Proof.Dsa.X86.Generation.QCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PPartCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CheckCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.AddBE
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GPart
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PPart
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TimingFlags
import VerifiedGarbage.Proof.Dsa.X86.Generation.GRange
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base

/-! # Two runs of a seed leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Proof.Dsa.Generation

/-- Before seed `a.1`, with the witness cursor at `a.2`. -/
def AIn (E : Env) (a : Nat × Nat) (s : State) : Prop :=
  QIn E a s ∧ s.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0

/-- q of seed `a.1`. -/
abbrev qVal (E : Env) (g : Geo) (a : Nat × Nat) : Nat := Spec.Dsa.qCandidate (8 * g.qLen) (chunk E a.1)

/-- q's test. -/
abbrev qRes (E : Env) (g : Geo) (a : Nat × Nat) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.probablePrime (qVal E g a) (E.witT.drop a.2)

/-- The witness cursor after q's test. -/
abbrev qUsed (E : Env) (g : Geo) (a : Nat × Nat) : Nat := nextUsed E.witLen a.2 (qRes E g a)

/-- p's search. -/
abbrev pRes (E : Env) (g : Geo) (a : Nat × Nat) : Option (Option Nat × Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.primeFromSeed (8 * g.pLen) (8 * g.qLen) (qVal E g a) (chunk E a.1) (E.witT.drop (qUsed E g a))

/-- `fP` for p's search. -/
def fpOf : Option (Option Nat × Spec.RsaKeyGen.Rand) → Nat
  | none => 0
  | some (none, _) => 2
  | some (some _, _) => 1

/-- The p found. -/
def pOf : Option (Option Nat × Spec.RsaKeyGen.Rand) → Nat
  | some (some p, _) => p
  | _ => 0

/-- The generator's search. -/
abbrev gRes (E : Env) (g : Geo) (a : Nat × Nat) : Option Nat :=
  Spec.Dsa.generator (pOf (pRes E g a)) (qVal E g a) (hList E)

/-- `fG` for the generator's search. -/
def fgOf : Option Nat → Nat
  | none => 2
  | some _ => 1

/-- The g found. -/
def gOf : Option Nat → Nat
  | none => 0
  | some g => g

theorem PRes.fp {E : Env} {g : Geo} {Q : Nat} {m : Mem} {R : Option (Option Nat × Spec.RsaKeyGen.Rand)}
    (h : PRes E g Q m R) : m.readW (off E.base fP) 32 = BitVec.ofNat 32 (fpOf R) := by
  rcases R with _ | ⟨_ | p, rest⟩
  · exact h
  · exact h.1
  · exact h.1

theorem GRes.fg {E : Env} {g : Geo} {m : Mem} {R : Option Nat} (h : GRes E g m R) :
    m.readW (off E.base fG) 32 = BitVec.ofNat 32 (fgOf R) := by
  rcases R with _ | gv
  · exact h
  · exact h.1

/-- The state a comparison was made from. -/
theorem CmpAfter.elim {α : Type} {Φ : α → State → Prop} {a : α} {t : State} (h : CmpAfter Φ a t) :
    ∃ s, Φ a s ∧ t.mem = s.mem ∧ t.gpr .edi = s.gpr .edi ∧ t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.syms = s.syms := by
  obtain ⟨s, hs, g, m, rd, wr, sy⟩ := h
  exact ⟨s, hs, m, g _ (by decide), g _ (by decide), rd, wr, sy⟩

/-- After q. -/
def AQ (E : Env) (g : Geo) (a : Nat × Nat) (t : State) : Prop := ∃ s, AIn E a s ∧ QPost E g a.1 a.2 s t

/-- q a probable prime: before p. -/
def AQp (E : Env) (g : Geo) (a : Nat × Nat) (t : State) : Prop :=
  CmpAfter (fun a t => CmpAfter (AQ E g) a t ∧
    decide (Proof.Dsa.ProbablePrime.status (qRes E g a) = 0) = false) a t ∧
    decide (Proof.Dsa.ProbablePrime.status (qRes E g a) = 1) = true

/-- After p. -/
def AP (E : Env) (g : Geo) (a : Nat × Nat) (t : State) : Prop :=
  ∃ s, AQp E g a s ∧ PKeep E g a.1 (qVal E g a) s t ∧ PRes E g (qVal E g a) t.mem (pRes E g a)

/-- p found: before g. -/
def APg (E : Env) (g : Geo) (a : Nat × Nat) (t : State) : Prop :=
  CmpAfter (fun a t => CmpAfter (AP E g) a t ∧ decide (fpOf (pRes E g a) = 0) = false) a t ∧
    decide (fpOf (pRes E g a) = 1) = true

/-- After g. -/
def AG (E : Env) (g : Geo) (a : Nat × Nat) (t : State) : Prop :=
  ∃ s, APg E g a s ∧ GKeep E g s t ∧ GRes E g t.mem (gRes E g a)

theorem AQ.base {E : Env} {g : Geo} {a : Nat × Nat} {t : State} (h : AQ E g a t) : Base E t := by
  obtain ⟨_, _, Q⟩ := h; exact Q.base

theorem AP.base {E : Env} {g : Geo} {a : Nat × Nat} {t : State} (h : AP E g a t) : Base E t := by
  obtain ⟨_, _, P, _⟩ := h; exact P.base

theorem AG.base {E : Env} {g : Geo} {a : Nat × Nat} {t : State} (h : AG E g a t) : Base E t := by
  obtain ⟨_, _, K, _⟩ := h; exact K.base

/-- p's inputs, from q. -/
theorem aqp_ppIn {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) {a : Nat × Nat}
    {t : State} (h : AQp E g a t) : PPIn E g (a.1, qVal E g a, qUsed E g a) t := by
  have bd := G.bounds
  obtain ⟨C₂, _⟩ := h
  obtain ⟨t₂, ⟨C₁, _⟩, m₂, e₂, p₂, r₂, w₂, y₂⟩ := C₂.elim
  obtain ⟨t₁, ⟨s, A, Q⟩, m₁, e₁, p₁, r₁, w₁, y₁⟩ := C₁.elim
  have K₁ : AKeep E g s t₁ := ⟨Q.base, Q.chg.widen fun o ho => ⟨o, by simp [atRanges, ho], Nat.le_refl _,
    Nat.le_refl _⟩, Q.rd, Q.wr, Q.syms⟩
  have K : AKeep E g s t := K₁.mem (m₂.trans m₁) (e₂.trans e₁) (p₂.trans p₁) (r₂.trans r₁) (w₂.trans w₁)
    (y₂.trans y₁)
  have qsh := qCandidate_shape (n := 8 * g.qLen) (by omega) (chunk E a.1)
  refine ⟨K.base, A.1.2.1, ?_, by rw [m₂, m₁]; exact Q.q, Nat.lt_of_lt_of_le (Nat.two_pow_pos _) qsh.2.1,
    by rw [m₂, m₁]; exact Q.used, ?_⟩
  · rw [K.word G v hp (by simp only [fSeed]; omega) (by simp only [fSeed, fUsed, hdr]; omega)]
    exact A.1.2.2.1
  · have := A.1.2.2.2.2
    show nextUsed E.witLen a.2 (qRes E g a) ≤ E.witLen
    generalize qRes E g a = r
    rcases r with _ | ⟨_, rest⟩
    · exact this
    · exact Nat.sub_le _ _

/-- The generator's inputs, from p. -/
theorem apg_gpIn {g : Geo} (G : GeoOk g) {E : Env} {a : Nat × Nat} {t : State} (h : APg E g a t) :
    GPIn E g (pOf (pRes E g a), qVal E g a, (pOf (pRes E g a) - 1) / qVal E g a) t := by
  have bd := G.bounds
  obtain ⟨C₂, h1⟩ := h
  obtain ⟨t₂, ⟨C₁, _⟩, m₂, e₂, p₂, r₂, w₂, y₂⟩ := C₂.elim
  obtain ⟨t₁, ⟨s, _, P, R⟩, m₁, e₁, p₁, r₁, w₁, y₁⟩ := C₁.elim
  have B : Base E t := P.base.regs (m₂.trans m₁) (e₂.trans e₁) (p₂.trans p₁) (r₂.trans r₁) (w₂.trans w₁)
    (y₂.trans y₁)
  generalize pRes E g a = R' at R h1 ⊢
  rcases R' with _ | ⟨_ | p, rest⟩
  · simp [fpOf] at h1
  · simp [fpOf] at h1
  obtain ⟨_, plo, phi, podd, _, _, pm, e, pv, one⟩ := R
  have qsh := qCandidate_shape (n := 8 * g.qLen) (by omega) (chunk E a.1)
  have hxl : (p - 1) / qVal E g a < 2 ^ (32 * g.e) := by
    have ex : 8 * g.pLen ≤ 32 * g.e + (8 * g.qLen - 1) := by
      rw [G.e]; rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
    unfold qVal
    rw [Nat.div_lt_iff_lt_mul (by have := Nat.two_pow_pos (8 * g.qLen - 1); have := qsh.2.1; omega)]
    have := Nat.mul_le_mul_left (2 ^ (32 * g.e)) qsh.2.1
    rw [← Nat.pow_add] at this
    have := Nat.pow_le_pow_right (n := 2) (by decide) ex
    omega
  have hp1 : 1 < p := by have := Nat.one_lt_two_pow (n := 8 * g.pLen - 1) (by omega); omega
  simp only [pOf]
  exact ⟨B, rfl, by rw [m₂, m₁]; exact one, by rw [m₂, m₁]; exact pm, by rw [m₂, m₁]; exact pv,
    by rw [m₂, m₁]; exact e, hxl, hp1, podd, phi⟩

/-- p||q||g, for the domain check. -/
theorem ag_cIn {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {a : Nat × Nat} {t : State}
    (h : CmpAfter (AG E g) a t ∧ decide (fgOf (gRes E g a) = 1) = true) :
    CIn E g (Spec.Dsa.encodeParams g.pLen g.qLen ⟨pOf (pRes E g a), qVal E g a, gOf (gRes E g a)⟩) t := by
  have sz := v.size_ge
  have bd := G.bounds
  obtain ⟨C, h1⟩ := h
  obtain ⟨t₇, ⟨t₆, ⟨C₆, hf⟩, GK, GR⟩, m, e, p_, r, w, y⟩ := C.elim
  obtain ⟨t₅, ⟨C₅, _⟩, m₆, -, -, -, -, -⟩ := C₆.elim
  obtain ⟨t₄, ⟨t₃, _, PK, PR⟩, m₅, -, -, -, -, -⟩ := C₅.elim
  refine ⟨GK.base.regs m e p_ r w y, ?_⟩
  generalize gRes E g a = G' at GR h1 ⊢
  rcases G' with _ | gv
  · simp [fgOf] at h1
  generalize pRes E g a = R' at PR hf ⊢
  have gA := gRanges_apart G v
  have gR : ∀ {d n : Nat}, sPk ≤ d → d + n ≤ sPk + g.pLen + g.qLen →
      ∀ o ∈ gRanges g, o.1 + o.2 ≤ E.size ∧ (o.1 + o.2 ≤ d ∨ d + n ≤ o.1) := fun h₁ h₂ o ho => ⟨(gA o ho).1, by
    simp only [gRanges, rRanges, wRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [aTmp, aH, arr, fLo, sPk, fG, fH, fHLeft, hdr] at h₁ h₂ ⊢ <;> omega⟩
  have mem : t₆.mem = t₄.mem := m₆.trans m₅
  have qk : Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen)) g.qLen = Spec.Dsa.encodeBE g.qLen (qVal E g a) := by
    rw [m, Env.Chg.scratch v GK.chg (by simp only [sPk]; omega) (gR (by omega) (by omega)), mem, ← PK.q]
    have h := encodeBE_decodeBE (Spec.Rsa.bytesAt t₄.mem (off E.base (sPk + g.pLen)) g.qLen)
    rw [VG.Proof.Bignum.bytesAt_length] at h
    exact h.symm
  rcases R' with _ | ⟨_ | p, rest⟩
  · simp [fpOf] at hf
  · simp [fpOf] at hf
  obtain ⟨_, _, _, _, _, pk, _⟩ := PR
  have pk' : Spec.Rsa.bytesAt t.mem (off E.base sPk) g.pLen = Spec.Dsa.encodeBE g.pLen p := by
    rw [m, Env.Chg.scratch v GK.chg (by simp only [sPk]; omega) (gR (Nat.le_refl _) (by omega)), mem, pk]
  simp only [pOf, gOf]
  rw [show 2 * g.pLen + g.qLen = g.pLen + (g.qLen + g.pLen) by omega, bytesAt_append, bytesAt_append,
    show VG.Proof.Bignum.off (off E.base sPk) g.pLen = off E.base (sPk + g.pLen) from off_add_ofNat _ _ _,
    show VG.Proof.Bignum.off (off E.base (sPk + g.pLen)) g.qLen = off E.base (sPk + g.pLen + g.qLen)
      from off_add_ofNat _ _ _, pk', qk, m, GR.2, Spec.Dsa.encodeParams, List.append_assoc]

theorem attempt_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen) :
    RelCT isa (Both (AIn E)) g.attempt fun _ _ => True := by
  have sz := v.size_ge
  have bd := G.bounds
  have fpLt : ∀ R : Option (Option Nat × Spec.RsaKeyGen.Rand), fpOf R < 2 ^ 32 := fun R => by
    rcases R with _ | ⟨_ | _, _⟩ <;> simp [fpOf]
  have fgLt : ∀ R : Option Nat, fgOf R < 2 ^ 32 := fun R => by rcases R with _ | _ <;> simp [fgOf]
  unfold Geo.attempt
  simp only [seqs]
  -- q.
  refine RelCT.seq (both_post (Ψ := AQ E g) (both_map id (fun a s h => h.1) (qPart_ct G v hq))
    fun a s h => WP.mono (qPart_ok G v hp hq h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2)
      fun t Q => ⟨s, h, Q⟩) ?_
  refine cmpF_ct (o := fRes) (v := 0) (by simp only [fRes, hdr]; omega) (by decide)
    (fun a => Proof.Dsa.ProbablePrime.status (qRes E g a)) (fun a t h => h.base)
    (fun a t h => by obtain ⟨_, _, Q⟩ := h; exact Q.res) (fun a => status_lt _)
    (stImm_ct (fun a t h => h.1.base fun _ _ h => h.base) _ _) ?_
  refine cmpF_ct (o := fRes) (v := 1) (by simp only [fRes, hdr]; omega) (by decide)
    (fun a => Proof.Dsa.ProbablePrime.status (qRes E g a)) (fun a t h => h.1.base fun _ _ h => h.base)
    (fun a t h => by obtain ⟨u, ⟨s₀, -, Q⟩, m, -⟩ := h.1.elim; rw [m]; exact Q.res) (fun a => status_lt _)
    ?_ (RelCT.block_nil fun _ _ _ => trivial)
  -- p.
  refine (show RelCT isa (Both (AQp E g)) _ _ from ?_)
  refine RelCT.seq (both_post (Ψ := AP E g)
    (both_map (fun a => (a.1, qVal E g a, qUsed E g a)) (fun a t h => aqp_ppIn G v hp h) (pPart_ct G v hq))
    fun a t h => ?_) ?_
  · have I := aqp_ppIn G v hp h
    exact WP.mono (pPart_ok G v hq I.1 I.2.1 I.2.2.1 I.2.2.2.1 I.2.2.2.2.1 I.2.2.2.2.2.1 I.2.2.2.2.2.2)
      fun u ⟨P, R⟩ => ⟨t, h, P, R⟩
  refine cmpF_ct (o := fP) (v := 0) (by simp only [fP, hdr]; omega) (by decide)
    (fun a => fpOf (pRes E g a)) (fun a t h => h.base) (fun a t h => by obtain ⟨_, _, _, R⟩ := h; exact R.fp)
    (fun a => fpLt _) (stImm_ct (fun a t h => h.1.base fun _ _ h => h.base) _ _) ?_
  refine cmpF_ct (o := fP) (v := 1) (by simp only [fP, hdr]; omega) (by decide)
    (fun a => fpOf (pRes E g a)) (fun a t h => h.1.base fun _ _ h => h.base)
    (fun a t h => by obtain ⟨u, ⟨s₀, -, -, R⟩, m, -⟩ := h.1.elim; rw [m]; exact R.fp) (fun a => fpLt _)
    ?_ (RelCT.block_nil fun _ _ _ => trivial)
  -- g.
  refine (show RelCT isa (Both (APg E g)) _ _ from ?_)
  refine RelCT.seq (both_post (Ψ := AG E g)
    (both_map (fun a => (pOf (pRes E g a), qVal E g a, (pOf (pRes E g a) - 1) / qVal E g a))
      (fun a t h => apg_gpIn G h) (gPart_ct G v hp)) fun a t h => ?_) ?_
  · have I := apg_gpIn G h
    exact WP.mono (gPart_ok G v hp I.base I.hx' I.hone I.hpm1 I.hP I.hE I.hxl I.hp1 I.hodd I.hplt)
      fun u ⟨K, R⟩ => ⟨t, h, K, R⟩
  -- The domain check.
  refine cmpF_ct (o := fG) (v := 1) (by simp only [fG, hdr]; omega) (by decide)
    (fun a => fgOf (gRes E g a)) (fun a t h => h.base) (fun a t h => by obtain ⟨_, _, _, R⟩ := h; exact R.fg)
    (fun a => fgLt _) ?_ (RelCT.block_nil fun _ _ _ => trivial)
  exact both_map _ (fun a t h => ag_cIn G v h) (check_ct G v hp hq)

end VG.Proof.Dsa.X86.Generation
