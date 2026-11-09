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

/-- The witnesses p's search left. -/
def pRest : Option (Option Nat × Spec.RsaKeyGen.Rand) → Spec.RsaKeyGen.Rand
  | some (_, r) => r
  | none => []

/-- The octets of `rand` read before the window of `h` candidates. -/
abbrev pUsed (E : Env) (g : Geo) (a : Nat × Nat) : Nat := E.witLen - (pRest (pRes E g a)).length

/-- The window's environment. -/
abbrev gEnv (E : Env) (g : Geo) (a : Nat × Nat) : Env := E.window (pUsed E g a)

/-- The generator's search. -/
abbrev gRes (E : Env) (g : Geo) (a : Nat × Nat) : Option Nat :=
  Spec.Dsa.generator (pOf (pRes E g a)) (qVal E g a) (hList (gEnv E g a))

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

/-- After the window. -/
def AW (E : Env) (g : Geo) (a : Nat × Nat) (t : State) : Prop :=
  ∃ s, APg E g a s ∧ Base E t ∧ E.Chg [(fHs, 4), (fHsLen, 4)] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    t.syms = s.syms ∧ t.mem.readW (off E.base fHs) 32 = (gEnv E g a).hs.setWidth 32 ∧
    t.mem.readW (off E.base fHsLen) 32 = BitVec.ofNat 32 (gEnv E g a).hsLen

/-- After g. -/
def AG (E : Env) (g : Geo) (a : Nat × Nat) (t : State) : Prop :=
  ∃ s, AW E g a s ∧ GKeep (gEnv E g a) g s t ∧ GRes (gEnv E g a) g t.mem (gRes E g a)

/-- After the candidates read. -/
def AU (E : Env) (g : Geo) (a : Nat × Nat) (t : State) : Prop :=
  ∃ s, AG E g a s ∧ (∃ x : BitVec 32, t.mem = s.mem.writeW (off E.base fUsed) x) ∧ t.gpr .edi = s.gpr .edi ∧
    t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms

theorem AQ.base {E : Env} {g : Geo} {a : Nat × Nat} {t : State} (h : AQ E g a t) : Base E t := by
  obtain ⟨_, _, Q⟩ := h; exact Q.base

theorem AP.base {E : Env} {g : Geo} {a : Nat × Nat} {t : State} (h : AP E g a t) : Base E t := by
  obtain ⟨_, _, P, _⟩ := h; exact P.base

theorem AG.base {E : Env} {g : Geo} {a : Nat × Nat} {t : State} (h : AG E g a t) : Base E t := by
  obtain ⟨_, _, K, _⟩ := h; exact K.base.ofWindow

theorem AU.base {E : Env} {g : Geo} (v : E.Valid) {a : Nat × Nat} {t : State} (h : AU E g a t) : Base E t := by
  obtain ⟨s, A, ⟨x, m⟩, e, p, r, w, y⟩ := h
  have := v.size_ge
  have C : E.Chg [(fUsed, 4)] s.mem t.mem := by
    rw [m]; exact (Env.Chg.refl _ _).store (List.mem_singleton_self _) (by decide) x
  exact A.base.keep v C (fun o ho => by
    simp only [List.mem_singleton] at ho; subst ho; simp only [fUsed, fOut, fUsedP, fWitLen, hdr]; omega) e p r w y

/-- The window's length, after the candidates read. -/
theorem AU.len {E : Env} {g : Geo} (G : GeoOk g) (v : E.Valid) {a : Nat × Nat} {t : State} (h : AU E g a t) :
    t.mem.readW (off E.base fHsLen) 32 = BitVec.ofNat 32 (gEnv E g a).hsLen := by
  have sz := v.size_ge
  have bd := G.bounds
  obtain ⟨t₇, ⟨t₆, ⟨t₅, A, -, -, -, -, -, -, hl⟩, GK, _⟩, ⟨x, m⟩, -⟩ := h
  have gA := gRanges_apart G v
  rw [m, word_store_other v _ (by simp only [fHsLen, hdr]; omega) (by simp only [fUsed, hdr]; omega)
    (by simp only [fUsed, fHsLen, hdr]; omega),
    Env.Chg.word v (GK.chg : E.Chg _ _ _) (by simp only [fHsLen, hdr]; omega) (fun o ho => ⟨(gA o ho).1, by
      simp only [gRanges, rRanges, wRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [aTmp, aH, arr, fLo, sPk, fG, fH, fHLeft, fHsLen, hdr] <;> omega⟩), hl]

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

/-- The generator's inputs, from p and the window. -/
theorem aw_gpIn {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {a : Nat × Nat} {t : State} (h : AW E g a t) :
    GPIn (gEnv E g a) g (pOf (pRes E g a), qVal E g a, (pOf (pRes E g a) - 1) / qVal E g a) t := by
  have bd := G.bounds
  have sz := v.size_ge
  obtain ⟨s₀, ⟨C₂, h1⟩, B, CW, -, -, -, hsW, hsLenW⟩ := h
  obtain ⟨t₂, ⟨C₁, _⟩, m₂, e₂, p₂, r₂, w₂, y₂⟩ := C₂.elim
  obtain ⟨t₁, ⟨s, _, P, R⟩, m₁, e₁, p₁, r₁, w₁, y₁⟩ := C₁.elim
  have wV : ∀ d, fHsLen + 4 ≤ d → d + 4 * g.n32 ≤ E.size →
      val32 t.mem E.base d g.n32 = val32 t₁.mem E.base d g.n32 := fun d h h' => by
    rw [Env.Chg.val32 v CW h' fun o ho => ⟨by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp only [fHs, fHsLen, hdr] <;> omega, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp only [fHs, fHsLen, hdr] at h ⊢ <;> omega⟩, m₂, m₁]
  have n32 : g.n32 = g.pLen / 4 := rfl
  generalize pRes E g a = R' at R h1 hsW hsLenW ⊢
  rcases R' with _ | ⟨_ | p, rest⟩
  · simp [fpOf] at h1
  · simp [fpOf] at h1
  obtain ⟨_, plo, phi, podd, ⟨u, hu, fu, du⟩, _, pm, e, pv, one⟩ := R
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
  exact ⟨B.toWindow _, hsW, hsLenW, rfl,
    by show val32 t.mem E.base aOne g.n32 = _
       rw [wV _ (by simp only [aOne, arr, fHsLen, hdr]; omega) (by simp only [aOne, arr]; omega)]; exact one,
    by show val32 t.mem E.base aPm1 g.n32 = _
       rw [wV _ (by simp only [aPm1, arr, fHsLen, hdr]; omega) (by simp only [aPm1, arr]; omega)]; exact pm,
    by show val32 t.mem E.base aP g.n32 = _
       rw [wV _ (by simp only [aP, arr, fHsLen, hdr]; omega) (by simp only [aP, arr]; omega)]; exact pv,
    by show val32 t.mem E.base aE g.n32 = _
       rw [wV _ (by simp only [aE, arr, fHsLen, hdr]; omega) (by simp only [aE, arr]; omega)]; exact e,
    hxl, hp1, podd, phi⟩

/-- p||q||g, for the domain check. -/
theorem ag_cIn {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {a : Nat × Nat} {t : State}
    (h : CmpAfter (AU E g) a t ∧ decide (fgOf (gRes E g a) = 1) = true) :
    CIn E g (Spec.Dsa.encodeParams g.pLen g.qLen ⟨pOf (pRes E g a), qVal E g a, gOf (gRes E g a)⟩) t := by
  have sz := v.size_ge
  have bd := G.bounds
  obtain ⟨C, h1⟩ := h
  obtain ⟨tU, AUh, m, e, p_, r, w, y⟩ := C.elim
  have BU := AUh.base v
  obtain ⟨t₇, ⟨t₆w, ⟨t₆, ⟨C₆, hf⟩, -, CW, -, -, -, -, -⟩, GK, GR⟩, ⟨x, mU⟩, -⟩ := AUh
  obtain ⟨t₅, ⟨C₅, _⟩, m₆, -, -, -, -, -⟩ := C₆.elim
  obtain ⟨t₄, ⟨t₃, _, PK, PR⟩, m₅, -, -, -, -, -⟩ := C₅.elim
  refine ⟨BU.regs m e p_ r w y, ?_⟩
  generalize gRes E g a = G' at GR h1 ⊢
  rcases G' with _ | gv
  · simp [fgOf] at h1
  generalize pRes E g a = R' at PR hf ⊢
  have gA := gRanges_apart G v
  have toU : ∀ {d n : Nat}, sPk ≤ d → d + n ≤ sPk + 2 * g.pLen + g.qLen →
      Spec.Rsa.bytesAt t.mem (off E.base d) n = Spec.Rsa.bytesAt t₇.mem (off E.base d) n := fun h₁ h₂ => by
    rw [m, mU, Env.Chg.scratch v ((Env.Chg.refl [(fUsed, 4)] t₇.mem).store (List.mem_singleton_self _)
      (by decide) _) (by simp only [sPk] at h₂; omega) (fun o ho => by
        simp only [List.mem_singleton] at ho; subst ho; simp only [fUsed, sPk, hdr] at h₁ ⊢; omega)]
  have to6 : ∀ {d n : Nat}, sPk ≤ d → d + n ≤ sPk + g.pLen + g.qLen →
      Spec.Rsa.bytesAt t.mem (off E.base d) n = Spec.Rsa.bytesAt t₆.mem (off E.base d) n := fun h₁ h₂ => by
    rw [toU h₁ (by omega), Env.Chg.scratch v (GK.chg : E.Chg _ _ _) (by simp only [sPk] at h₂; omega)
      (fun o ho => ⟨(gA o ho).1, by
        simp only [gRanges, rRanges, wRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [aTmp, aH, arr, fLo, sPk, fG, fH, fHLeft, hdr] at h₁ h₂ ⊢ <;> omega⟩),
      Env.Chg.scratch v CW (by simp only [sPk] at h₂; omega) (fun o ho => ⟨by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp only [fHs, fHsLen, hdr] <;> omega, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp only [fHs, fHsLen, sPk, hdr] at h₁ ⊢ <;> omega⟩)]
  have mem : t₆.mem = t₄.mem := m₆.trans m₅
  have qk : Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen)) g.qLen = Spec.Dsa.encodeBE g.qLen (qVal E g a) := by
    rw [to6 (by omega) (by omega), mem, ← PK.q]
    have h := encodeBE_decodeBE (Spec.Rsa.bytesAt t₄.mem (off E.base (sPk + g.pLen)) g.qLen)
    rw [VG.Proof.Bignum.bytesAt_length] at h
    exact h.symm
  rcases R' with _ | ⟨_ | p, rest⟩
  · simp [fpOf] at hf
  · simp [fpOf] at hf
  obtain ⟨_, _, _, _, _, pk, _⟩ := PR
  have pk' : Spec.Rsa.bytesAt t.mem (off E.base sPk) g.pLen = Spec.Dsa.encodeBE g.pLen p := by
    rw [to6 (Nat.le_refl _) (by omega), mem, pk]
  have gk : Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen + g.qLen)) g.pLen = Spec.Dsa.encodeBE g.pLen gv := by
    rw [toU (by omega) (by omega)]; exact GR.2
  simp only [pOf, gOf]
  rw [show 2 * g.pLen + g.qLen = g.pLen + (g.qLen + g.pLen) by omega, bytesAt_append, bytesAt_append,
    show VG.Proof.Bignum.off (off E.base sPk) g.pLen = off E.base (sPk + g.pLen) from off_add_ofNat _ _ _,
    show VG.Proof.Bignum.off (off E.base (sPk + g.pLen)) g.qLen = off E.base (sPk + g.pLen + g.qLen)
      from off_add_ofNat _ _ _, pk', qk, gk, Spec.Dsa.encodeParams, List.append_assoc]

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
  -- The window.
  refine (show RelCT isa (Both (APg E g)) _ _ from ?_)
  have apg_u : ∀ a t, APg E g a t → Base E t ∧
      t.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (pUsed E g a) ∧ pUsed E g a ≤ E.witLen := by
    intro a t h
    obtain ⟨C₂, h1⟩ := h
    obtain ⟨t₂, ⟨C₁, _⟩, m₂, e₂, p₂, r₂, w₂, y₂⟩ := C₂.elim
    obtain ⟨t₁, ⟨s, _, P, R⟩, m₁, e₁, p₁, r₁, w₁, y₁⟩ := C₁.elim
    have B : Base E t := P.base.regs (m₂.trans m₁) (e₂.trans e₁) (p₂.trans p₁) (r₂.trans r₁) (w₂.trans w₁)
      (y₂.trans y₁)
    have wl : E.witT.length = E.witLen := by rw [← B.wit, VG.Proof.Bignum.bytesAt_length]
    refine ⟨B, ?_, Nat.sub_le _ _⟩
    show t.mem.readW _ 32 = BitVec.ofNat 32 (E.witLen - (pRest (pRes E g a)).length)
    generalize pRes E g a = R' at R h1 ⊢
    rcases R' with _ | ⟨_ | p, rest⟩
    · simp [fpOf] at h1
    · simp [fpOf] at h1
    obtain ⟨_, _, _, _, ⟨u, hu, fu, du⟩, _⟩ := R
    have : E.witLen - rest.length = u := by rw [← du, List.length_drop, wl]; omega
    rw [m₂, m₁]
    simp only [pRest, this]
    exact fu
  refine RelCT.seq (both_post (Ψ := AW E g) ?_ fun a t h => ?_) ?_
  · unfold Geo.gWindow
    refine RelCT.seq (both_post (Ψ := fun a t => ∃ s, APg E g a s ∧ WinPost E g (pUsed E g a) s t)
      (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => base_pins (apg_u a t h).1) ?_)
      fun a t h => WP.mono (gWinBlock_ok G v (apg_u a t h).1 (apg_u a t h).2.1 (apg_u a t h).2.2)
        fun u W => ⟨t, h, W⟩) ?_
    · rcases G.lengths with ⟨h₁, _⟩ | ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> rw [h₁] <;> exact tcheck _ _ (by decide +kernel)
    · refine both_ite (fun a => decide (E.witLen - pUsed E g a < 128 * g.pLen))
        (fun a t h => by obtain ⟨_, _, W⟩ := h; exact W.cf) (RelCT.block_nil fun _ _ _ => trivial) ?_
      exact stImm_ct (fun a t h => by obtain ⟨_, _, W⟩ := h.1; exact W.base) _ _
  · exact WP.mono (gWindow_ok G v hp (apg_u a t h).1 (apg_u a t h).2.1 (apg_u a t h).2.2)
      fun u ⟨B, C, rd, wr, sy, hs, hl⟩ => ⟨t, h, B, C, rd, wr, sy, hs, hl⟩
  -- g.
  refine RelCT.seq (both_post (Ψ := AG E g) ?_ fun a t h => ?_) ?_
  · refine both_exists fun a => ?_
    exact (gPart_ct G (v.window (Nat.sub_le _ _)) hp).mono
      (fun s t h => ⟨_, aw_gpIn G v h.1, aw_gpIn G v h.2⟩) fun _ _ h => h
  · have I := aw_gpIn G v h
    exact WP.mono (gPart_ok G (v.window (Nat.sub_le _ _)) hp I.base I.hsW I.hsLenW I.hx' I.hone I.hpm1 I.hP I.hE
      I.hxl I.hp1 I.hodd I.hplt) fun u ⟨K, R, _⟩ => ⟨t, h, K, R⟩
  -- The candidates read.
  refine RelCT.seq (both_post (Ψ := AU E g)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => base_pins h.base) (tcheck _ _ (by decide +kernel)))
    fun a t h => WP.mono (gUsed_wp h.base.scr sz) fun u ⟨x, e, p_, r, w, y⟩ => ⟨t, h, x, e, p_, r, w, y⟩) ?_
  -- The domain check, or whether the window was short.
  refine cmpF_ct (o := fG) (v := 1) (by simp only [fG, hdr]; omega) (by decide)
    (fun a => fgOf (gRes E g a)) (fun a t h => h.base v) (fun a t h => ?_)
    (fun a => fgLt _) ?_ ?_
  · obtain ⟨t₇, ⟨_, _, _, R⟩, ⟨x, m⟩, -⟩ := h
    rw [m, word_store_other v _ (by simp only [fG, hdr]; omega) (by simp only [fUsed, hdr]; omega)
      (by simp only [fUsed, fG, hdr]; omega)]
    exact R.fg
  · exact both_map _ (fun a t h => ag_cIn G v h) (check_ct G v hp hq)
  · unfold Geo.gShort
    refine cmpFb_ct (o := fHsLen) (v := 128 * g.pLen) (by simp only [fHsLen, hdr]; omega) (by omega)
      (fun a => (gEnv E g a).hsLen) (fun a t h => h.1.base fun _ _ h => h.base v)
      (fun a t h => by obtain ⟨u, hU, m, -⟩ := h.1.elim; rw [m]; exact hU.len G v) (fun a => ?_)
      (stImm_ct (fun a t h => h.1.base fun _ _ h => h.1.base fun _ _ h => h.base v) _ _)
      (RelCT.block_nil fun _ _ _ => trivial)
    simp only [Env.window, hp]
    omega

end VG.Proof.Dsa.X86.Generation
