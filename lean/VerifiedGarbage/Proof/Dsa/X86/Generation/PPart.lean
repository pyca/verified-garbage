module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.Generation.Search
import VerifiedGarbage.Proof.Dsa.X86.Generation.Seqs
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.X86.Syms

/-! # p's search over `4 L` counters (A.1.1.2 steps 11–15) -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)
open VG.Proof.Dsa.Generation

/-- The ranges p's search changes. -/
def ppRanges (g : Geo) : List (Nat × Nat) := paRanges g ++ [(fCounter, 4), (fOffset, 4)]

theorem ppRanges_apart {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) : E.Apart (ppRanges g) := by
  have sz := v.size_ge
  intro o ho
  rcases List.mem_append.mp ho with h | h
  · exact paRanges_apart G v o h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp only [fCounter, fOffset, fOut, fWitLen, hdr] <;> omega

/-- What memory `m` holds after p's search with result `R`. -/
def PRes (E : Env) (g : Geo) (Q : Nat) (m : Mem) : Option (Option Nat × Spec.RsaKeyGen.Rand) → Prop
  | none => m.readW (off E.base fP) 32 = BitVec.ofNat 32 0
  | some (none, rest) => m.readW (off E.base fP) 32 = BitVec.ofNat 32 2 ∧
      ∃ u, u ≤ E.witLen ∧ m.readW (off E.base fUsed) 32 = BitVec.ofNat 32 u ∧ E.witT.drop u = rest
  | some (some p, rest) => m.readW (off E.base fP) 32 = BitVec.ofNat 32 1 ∧
      2 ^ (8 * g.pLen - 1) ≤ p ∧ p < 2 ^ (8 * g.pLen) ∧ p % 2 = 1 ∧
      (∃ u, u ≤ E.witLen ∧ m.readW (off E.base fUsed) 32 = BitVec.ofNat 32 u ∧ E.witT.drop u = rest) ∧
      Spec.Rsa.bytesAt m (off E.base sPk) g.pLen = Spec.Dsa.encodeBE g.pLen p ∧
      val32 m E.base aPm1 (g.pLen / 4) = p - 1 ∧ val32 m E.base aE (g.pLen / 4) = (p - 1) / Q ∧
      val32 m E.base aP (g.pLen / 4) = p ∧ val32 m E.base aOne (g.pLen / 4) = 1

theorem pcand_bounds {g : Geo} (G : GeoOk g) {E : Env} {k offset Q : Nat} :
    pcand g E k offset Q < 2 ^ (8 * g.pLen) ∧ pcand g E k offset Q % 2 = 1 := by
  have bd := G.bounds
  have hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * g.qLen) bs).length = 8 * g.qLen := fun bs => by
    rw [← G.seedHash, G.hash.hash_length, G.N]
  unfold pcand
  rw [pCandidate_shaped (by omega) hlen]
  have sh := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := 8 * g.pLen) (by omega)
    (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) ((8 * g.pLen - 1) / (8 * g.qLen) + 1))
  have := pReduction_le (q := Q) sh.1
  exact ⟨by dsimp only; omega, pReduction_odd _ _⟩

/-- What p's search keeps. -/
structure PKeep (E : Env) (g : Geo) (k Q : Nat) (s t : State) : Prop where
  base : Base E t
  seed : t.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32
  q : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen)) g.qLen) = Q
  chg : E.Chg (ppRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

/-- At the loop's head, before counter `c`, `u` witness octets read. -/
structure PLoop (E : Env) (g : Geo) (k Q : Nat) (R : Option (Option Nat × Spec.RsaKeyGen.Rand)) (s : State)
    (c u : Nat) (t : State) : Prop where
  keep : PKeep E g k Q s t
  counter : t.mem.readW (off E.base fCounter) 32 = BitVec.ofNat 32 c
  offset : t.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 (1 + c * (g.count + 1))
  fp : t.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 4
  used : t.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 u
  hu : u ≤ E.witLen
  spec : primeSearch (8 * g.pLen) (8 * g.qLen) Q (chunk E k) c (E.witT.drop u) = R

theorem PKeep.mem {E : Env} {g : Geo} {k Q : Nat} {s t t' : State} (P : PKeep E g k Q s t)
    (hm : t'.mem = t.mem) (edi : t'.gpr .edi = t.gpr .edi) (sp : t'.gpr .esp = t.gpr .esp) (rd : t'.rd = t.rd)
    (wr : t'.wr = t.wr) (sy : t'.syms = t.syms) : PKeep E g k Q s t' :=
  ⟨P.base.regs hm edi sp rd wr sy, by rw [hm]; exact P.seed, by rw [hm]; exact P.q, by rw [hm]; exact P.chg,
    by rw [rd, P.rd], by rw [wr, P.wr], by rw [sy, P.syms]⟩

/-- A store to one of the search's state words. -/
theorem PKeep.store {E : Env} {g : Geo} {k Q : Nat} {s t t' : State} (P : PKeep E g k Q s t) (G : GeoOk g)
    (v : E.Valid) {d : Nat} (hd : (d, 4) ∈ ppRanges g) (hs : fSeed + 4 ≤ d) (hdq : d + 4 ≤ sState) (x : BitVec 32)
    (hm : t'.mem = t.mem.writeW (off E.base d) x) (edi : t'.gpr .edi = t.gpr .edi) (sp : t'.gpr .esp = t.gpr .esp)
    (rd : t'.rd = t.rd) (wr : t'.wr = t.wr) (sy : t'.syms = t.syms) : PKeep E g k Q s t' := by
  have sz := v.size_ge
  have bd := G.bounds
  have C : E.Chg [(d, 4)] t.mem t'.mem := by
    rw [hm]; exact (Env.Chg.refl _ _).store (List.mem_singleton_self _) (by decide) x
  refine ⟨P.base.keep v C (fun o ho => ppRanges_apart G v o (by simp only [List.mem_singleton] at ho; rw [ho]; exact hd))
    edi sp rd wr sy, ?_, ?_, P.chg.trans (C.widen fun o ho => ⟨o, by simp only [List.mem_singleton] at ho; rw [ho]; exact hd,
      Nat.le_refl _, Nat.le_refl _⟩), by rw [rd, P.rd], by rw [wr, P.wr], by rw [sy, P.syms]⟩
  · rw [hm, word_store_other v _ (by simp only [fSeed, hdr]; omega) (by simp only [sState] at hdq; omega) (.inl hs),
      P.seed]
  · rw [Env.Chg.scratch v C (by simp only [sPk]; omega) fun o ho => by
      simp only [List.mem_singleton] at ho; subst ho; simp only [sState, sPk] at hdq ⊢; omega, P.q]

/-- One counter: the loop exits with p's result, or goes on to the next. -/
theorem pBody_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen) {k Q : Nat}
    {R : Option (Option Nat × Spec.RsaKeyGen.Rand)} {s : State} (hk : (k + 1) * E.qLen ≤ E.seedsLen) (hQ0 : 0 < Q)
    {c u : Nat} {t : State} (L : PLoop E g k Q R s c u t) (hc : c < 4 * (8 * g.pLen)) :
    WP isa (seqs [g.pAttempt, .block (cmpF fP 4),
      .ite .e (seqs [.block g.pAdvance, .ite .e (.block (stImm fP 2)) (.block [])]) (.block []),
      .block (cmpF fP 4)]) t fun t' =>
      (t'.zf = some false ∧ PKeep E g k Q s t' ∧ PRes E g Q t'.mem R) ∨
      (t'.zf = some true ∧ c + 1 < 4 * (8 * g.pLen) ∧ ∃ u', PLoop E g k Q R s (c + 1) u' t') := by
  have sz := v.size_ge
  have bd := G.bounds
  have cnt : g.count + 1 ≤ 12 := by
    unfold Geo.count; rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
  have cm : c * (g.count + 1) ≤ 12288 * 12 := Nat.mul_le_mul (by omega) cnt
  have cs : (c + 1) * (g.count + 1) = c * (g.count + 1) + (g.count + 1) := Nat.succ_mul _ _
  have wl : E.witT.length = E.witLen := by rw [← L.keep.base.wit, VG.Proof.Bignum.bytesAt_length]
  simp only [seqs]
  refine WP.seq (WP.mono (pAttempt_ok G v hq L.keep.base hk L.keep.seed L.offset (by omega) L.keep.q hQ0 L.used
    L.hu L.fp) fun t₁ A => ?_)
  have spec : (if pcand g E k (1 + c * (g.count + 1)) Q < 2 ^ (8 * g.pLen - 1) then
      primeSearch (8 * g.pLen) (8 * g.qLen) Q (chunk E k) (c + 1) (E.witT.drop u)
      else match Spec.Dsa.probablePrime (pcand g E k (1 + c * (g.count + 1)) Q) (E.witT.drop u) with
        | none => none
        | some (accepted, rest) => if accepted then some (some (pcand g E k (1 + c * (g.count + 1)) Q), rest)
          else primeSearch (8 * g.pLen) (8 * g.qLen) Q (chunk E k) (c + 1) rest) = R := by
    rw [← L.spec, primeSearch_step _ _ hc]; rfl
  -- What the counter leaves: still searching, or p's result.
  have out : ∃ F, t₁.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 F ∧ F < 2 ^ 32 ∧
      ((F = 4 ∧ ∃ u', u' ≤ E.witLen ∧ t₁.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 u' ∧
        primeSearch (8 * g.pLen) (8 * g.qLen) Q (chunk E k) (c + 1) (E.witT.drop u') = R) ∨
      (F ≠ 4 ∧ PRes E g Q t₁.mem R)) := by
    by_cases hlt : pcand g E k (1 + c * (g.count + 1)) Q < 2 ^ (8 * g.pLen - 1)
    · refine ⟨4, by rw [A.fp]; simp only [hlt, ↓reduceIte], by decide, .inl ⟨rfl, u, L.hu, ?_, ?_⟩⟩
      · rw [A.used]; simp only [hlt, ↓reduceIte]
      · rw [← spec]; simp only [hlt, ↓reduceIte]
    · rcases hr : Spec.Dsa.probablePrime (pcand g E k (1 + c * (g.count + 1)) Q) (E.witT.drop u) with
        _ | ⟨_ | _, rest⟩
      · have hR : R = none := by rw [← spec]; simp only [hlt, hr, ↓reduceIte]
        refine ⟨0, by rw [A.fp]; simp only [hlt, hr, ↓reduceIte, pCode], by decide, .inr ⟨by decide, ?_⟩⟩
        rw [hR]; show _ = _; rw [A.fp]; simp only [hlt, hr, ↓reduceIte, pCode]
      · have cur := probablePrime_cursor hr
        rw [wl] at cur
        refine ⟨4, by rw [A.fp]; simp only [hlt, hr, ↓reduceIte, pCode], by decide,
          .inl ⟨rfl, E.witLen - rest.length, by omega, ?_, ?_⟩⟩
        · rw [A.used]; simp only [hlt, hr, ↓reduceIte, nextUsed]
        · rw [cur, ← spec]; simp only [hlt, hr, ↓reduceIte, Bool.false_eq_true]
      · have cur := probablePrime_cursor hr
        rw [wl] at cur
        have hR : R = some (some (pcand g E k (1 + c * (g.count + 1)) Q), rest) := by
          rw [← spec]; simp only [hlt, hr, ↓reduceIte]
        refine ⟨1, by rw [A.fp]; simp only [hlt, hr, ↓reduceIte, pCode], by decide, .inr ⟨by decide, ?_⟩⟩
        rw [hR]
        have pb := pcand_bounds G (E := E) (k := k) (offset := 1 + c * (g.count + 1)) (Q := Q)
        refine ⟨by rw [A.fp]; simp only [hlt, hr, ↓reduceIte, pCode], by omega, pb.1, pb.2,
          ⟨E.witLen - rest.length, by omega, ?_, cur⟩, A.pk, A.pm1, A.e, A.pv, A.one⟩
        rw [A.used]; simp only [hlt, hr, ↓reduceIte, nextUsed]
  obtain ⟨F, hF, Fl, out⟩ := out
  -- What the counter keeps.
  have Apa := paRanges_apart G v
  have K₁ : PKeep E g k Q s t₁ := by
    refine ⟨A.base, ?_, ?_, L.keep.chg.trans (A.chg.widen fun o ho => ⟨o, List.mem_append_left _ ho, Nat.le_refl _,
      Nat.le_refl _⟩), by rw [A.rd, L.keep.rd], by rw [A.wr, L.keep.wr], by rw [A.syms, L.keep.syms]⟩
    · rw [Env.Chg.word v A.chg (by simp only [fSeed, hdr]; omega) (fun o ho => ⟨(Apa o ho).1, by
        simp only [paRanges, pxRanges, aRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [sState, sX, arr, sPk, sPP, ppWords, fRes, fUsed, fUsedOut, fP, fSeed, hdr] <;> omega⟩),
        L.keep.seed]
    · rw [Env.Chg.scratch v A.chg (by simp only [sPk]; omega) (fun o ho => ⟨(Apa o ho).1, by
        simp only [paRanges, pxRanges, aRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [sState, sX, arr, sPk, sPP, ppWords, fRes, fUsed, fUsedOut, fP, hdr] <;> omega⟩), L.keep.q]
  have word₁ : ∀ d, d + 4 ≤ fP → fRes + 4 ≤ d →
      t₁.mem.readW (off E.base d) 32 = t.mem.readW (off E.base d) 32 := fun d h₁ h₂ =>
    Env.Chg.word v A.chg (by simp only [fP, hdr] at h₁; omega) (fun o ho => ⟨(Apa o ho).1, by
      simp only [paRanges, pxRanges, aRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [sState, sX, arr, sPk, sPP, ppWords, fRes, fUsed, fUsedOut, fP, hdr] at h₁ h₂ ⊢ <;> omega⟩)
  have counter₁ : t₁.mem.readW (off E.base fCounter) 32 = BitVec.ofNat 32 c := by
    rw [word₁ fCounter (by simp only [fCounter, fP, hdr]; omega) (by simp only [fCounter, fRes, hdr]; omega),
      L.counter]
  have offset₁ : t₁.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 (1 + c * (g.count + 1)) := by
    rw [word₁ fOffset (by simp only [fOffset, fP, hdr]; omega) (by simp only [fOffset, fRes, hdr]; omega),
      L.offset]
  refine WP.seq (cmpF_end A.base.scr (o := fP) (v := 4) (by simp only [fP, hdr]; omega) hF Fl (by decide)
    fun t₂ g₂ m₂ rd₂ wr₂ sy₂ z₂ => ?_)
  have K₂ := K₁.mem m₂ (g₂ _ (by decide)) (g₂ _ (by decide)) rd₂ wr₂ sy₂
  have fP₂ : t₂.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 F := by rw [m₂, hF]
  refine WP.seq (WP.ite _ z₂ (fun h4 => ?_) (fun h4 => WP.block_nil ?_))
  · -- Still searching: the next counter.
    have F4 : F = 4 := of_decide_eq_true h4
    obtain ⟨u', hu', hU', hs'⟩ := (out.resolve_right fun h => h.1 F4).2
    have wst : ∀ (m : Mem) {d e : Nat}, d + 4 ≤ sState → e + 4 ≤ sState → (d + 4 ≤ e ∨ e + 4 ≤ d) → ∀ x,
        (m.writeW (off E.base e) x).readW (off E.base d) 32 = m.readW (off E.base d) 32 :=
      fun m d e h₁ h₂ h x => word_store_other v m (by simp only [sState] at h₁; omega)
        (by simp only [sState] at h₂; omega) h x
    unfold Geo.pAdvance
    refine WP.seq (ld_ok K₂.base.scr (d := fCounter) (by simp only [fCounter, hdr]; omega) fun t₃ u₃ =>
      wp_addi fun t₄ u₄ => st_ok (Scr.of_eq K₂.base.scr (by rw [u₄.other _ (by decide), u₃.other _ (by decide)])
        (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]) (by rw [u₄.wr, u₃.wr])) (d := fCounter)
        (by simp only [fCounter, hdr]; omega) fun t₅ M₅ => ?_)
    have eax₄ : t₄.gpr .eax = BitVec.ofNat 32 (c + 1) := by
      rw [u₄.gpr, u₃.gpr, m₂, counter₁, BitVec.ofNat_add]; rfl
    have m₅ : t₅.mem = t₂.mem.writeW (off E.base fCounter) (BitVec.ofNat 32 (c + 1)) := by
      rw [M₅.mem, u₄.mem, u₃.mem, eax₄]
    have r₅ : ∀ r, r ≠ .eax → t₅.gpr r = t₂.gpr r := fun r hr => by
      rw [M₅.gpr, u₄.other r hr, u₃.other r hr]
    have K₅ := K₂.store G v (d := fCounter) (by simp [ppRanges]) (by simp only [fSeed, fCounter, hdr]; omega)
      (by simp only [fCounter, sState, hdr]; omega) _ m₅ (r₅ _ (by decide)) (r₅ _ (by decide))
      (by rw [M₅.rd, u₄.rd, u₃.rd]) (by rw [M₅.wr, u₄.wr, u₃.wr]) (by rw [M₅.syms, u₄.syms, u₃.syms])
    refine ld_ok K₅.base.scr (d := fOffset) (by simp only [fOffset, hdr]; omega) fun t₆ u₆ =>
      wp_addi fun t₇ u₇ => st_ok (Scr.of_eq K₅.base.scr (by rw [u₇.other _ (by decide), u₆.other _ (by decide)])
        (by rw [u₇.other _ (by decide), u₆.other _ (by decide)]) (by rw [u₇.wr, u₆.wr])) (d := fOffset)
        (by simp only [fOffset, hdr]; omega) fun t₈ M₈ => wp_cmpi fun t₉ f₉ _ z₉ => WP.block_nil ?_
    have ecx₇ : t₇.gpr .ecx = BitVec.ofNat 32 (1 + (c + 1) * (g.count + 1)) := by
      rw [u₇.gpr, u₆.gpr, m₅, wst _ (by simp only [fOffset, sState, hdr]; omega)
        (by simp only [fCounter, sState, hdr]; omega) (by simp only [fOffset, fCounter, hdr]; omega), m₂,
        offset₁, ← BitVec.ofNat_add, cs, Nat.add_assoc]
    have m₈ : t₈.mem = t₅.mem.writeW (off E.base fOffset) (BitVec.ofNat 32 (1 + (c + 1) * (g.count + 1))) := by
      rw [M₈.mem, u₇.mem, u₆.mem, ecx₇]
    have r₈ : ∀ r, r ≠ .eax → r ≠ .ecx → t₈.gpr r = t₅.gpr r := fun r h₁ h₂ => by
      rw [M₈.gpr, u₇.other r h₂, u₆.other r h₂]
    have K₈ := K₅.store G v (d := fOffset) (by simp [ppRanges]) (by simp only [fSeed, fOffset, hdr]; omega)
      (by simp only [fOffset, sState, hdr]; omega) _ m₈ (r₈ _ (by decide) (by decide)) (r₈ _ (by decide) (by decide))
      (by rw [M₈.rd, u₇.rd, u₆.rd]) (by rw [M₈.wr, u₇.wr, u₆.wr]) (by rw [M₈.syms, u₇.syms, u₆.syms])
    have K₉ := K₈.mem f₉.mem (by rw [f₉.gpr]) (by rw [f₉.gpr]) f₉.rd f₉.wr f₉.syms
    have m₉ : t₉.mem = (t₂.mem.writeW (off E.base fCounter) (BitVec.ofNat 32 (c + 1))).writeW (off E.base fOffset)
        (BitVec.ofNat 32 (1 + (c + 1) * (g.count + 1))) := by rw [f₉.mem, m₈, m₅]
    have word₉ : ∀ d, d + 4 ≤ sState → (d + 4 ≤ fCounter ∨ fOffset + 4 ≤ d) →
        t₉.mem.readW (off E.base d) 32 = t₂.mem.readW (off E.base d) 32 := fun d h₁ h₂ => by
      rw [m₉, wst _ h₁ (by simp only [fOffset, sState, hdr]; omega) (by simp only [fOffset, fCounter, hdr] at h₂ ⊢; omega),
        wst _ h₁ (by simp only [fCounter, sState, hdr]; omega) (by simp only [fOffset, fCounter, hdr] at h₂ ⊢; omega)]
    have zf₉ : isa.eval .e t₉ = some (decide (c + 1 = 4 * (8 * g.pLen))) := by
      show t₉.zf = _
      rw [z₉, M₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), M₅.gpr, eax₄,
        show (BitVec.ofNat 32 (32 * g.pLen) : BitVec 32) = BitVec.ofNat 32 (4 * (8 * g.pLen)) by congr 1; omega,
        sub_beq (by omega) (by omega)]
    have fP₉ : t₉.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 4 := by
      rw [word₉ fP (by simp only [fP, sState, hdr]; omega) (by simp only [fP, fOffset, hdr]; omega), fP₂, F4]
    have fU₉ : t₉.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 u' := by
      rw [word₉ fUsed (by simp only [fUsed, sState, hdr]; omega) (by simp only [fUsed, fCounter, hdr]; omega), m₂, hU']
    have cnt₉ : t₉.mem.readW (off E.base fCounter) 32 = BitVec.ofNat 32 (c + 1) := by
      rw [m₉, wst _ (by simp only [fCounter, sState, hdr]; omega) (by simp only [fOffset, sState, hdr]; omega)
        (by simp only [fOffset, fCounter, hdr]; omega), Mem.readW_writeW_self32]
    have off₉ : t₉.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 (1 + (c + 1) * (g.count + 1)) := by
      rw [m₉, Mem.readW_writeW_self32]
    refine WP.ite _ zf₉ (fun hd => stImm_end K₉.base.scr (o := fP) (v := 2) (by simp only [fP, hdr]; omega)
      fun t₁₀ g₁₀ m₁₀ rd₁₀ wr₁₀ sy₁₀ => ?_) (fun hd => WP.block_nil ?_)
    · -- The `4 L` counters are done: no p.
      have K₁₀ := K₉.store G v (d := fP) (by simp [ppRanges, paRanges]) (by simp only [fSeed, fP, hdr]; omega)
        (by simp only [fP, sState, hdr]; omega) _ m₁₀ (g₁₀ _ (by decide)) (g₁₀ _ (by decide)) rd₁₀ wr₁₀ sy₁₀
      have hR : R = some (none, E.witT.drop u') := by
        rw [← hs', primeSearch_done _ _ (by have := of_decide_eq_true hd; omega)]
      refine cmpF_end K₁₀.base.scr (o := fP) (v := 4) (w := 2) (by simp only [fP, hdr]; omega)
        (by rw [m₁₀, Mem.readW_writeW_self32]) (by decide) (by decide) fun t₁₁ g₁₁ m₁₁ rd₁₁ wr₁₁ sy₁₁ z₁₁ => ?_
      refine .inl ⟨z₁₁, K₁₀.mem m₁₁ (g₁₁ _ (by decide)) (g₁₁ _ (by decide)) rd₁₁ wr₁₁ sy₁₁, ?_⟩
      rw [hR]
      refine ⟨by rw [m₁₁, m₁₀, Mem.readW_writeW_self32], u', hu', ?_, rfl⟩
      rw [m₁₁, m₁₀, word_store_other v _ (by simp only [fUsed, hdr]; omega) (by simp only [fP, hdr]; omega)
        (by simp only [fUsed, fP, hdr]; omega), fU₉]
    · -- On to the next counter.
      refine cmpF_end K₉.base.scr (o := fP) (v := 4) (w := 4) (by simp only [fP, hdr]; omega) fP₉ (by decide)
        (by decide) fun t₁₁ g₁₁ m₁₁ rd₁₁ wr₁₁ sy₁₁ z₁₁ => .inr ⟨z₁₁, by have := of_decide_eq_false hd; omega, u', ?_⟩
      exact ⟨K₉.mem m₁₁ (g₁₁ _ (by decide)) (g₁₁ _ (by decide)) rd₁₁ wr₁₁ sy₁₁, by rw [m₁₁]; exact cnt₉,
        by rw [m₁₁]; exact off₉, by rw [m₁₁]; exact fP₉, by rw [m₁₁]; exact fU₉, hu', hs'⟩
  · -- p's result.
    have F4 : F ≠ 4 := of_decide_eq_false h4
    have res := (out.resolve_left fun h => F4 h.1).2
    refine cmpF_end K₂.base.scr (o := fP) (v := 4) (w := F) (by simp only [fP, hdr]; omega) fP₂ Fl (by decide)
      fun t₃ g₃ m₃ rd₃ wr₃ sy₃ z₃ => .inl ⟨by rw [show t₃.zf = _ from z₃]; simp [F4],
        K₂.mem m₃ (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃ sy₃, by rw [m₃, m₂]; exact res⟩

/-- p's search's state words: counter 0, its offset, still searching. -/
theorem pInit_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s : State} (B : Base E s)
    {k : Nat} (hS : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32) {Q : Nat}
    (hQ : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off E.base (sPk + g.pLen)) g.qLen) = Q)
    {used : Nat} (hU : s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used) (hu : used ≤ E.witLen) :
    WP isa (.block (stImm fCounter 0 ++ stImm fOffset 1 ++ stImm fP 4)) s
      (PLoop E g k Q (Spec.Dsa.primeFromSeed (8 * g.pLen) (8 * g.qLen) Q (chunk E k) (E.witT.drop used)) s 0 used) := by
  have sz := v.size_ge
  have bd := G.bounds
  simp only [List.append_assoc]
  have K₀ : PKeep E g k Q s s := ⟨B, hS, hQ, Env.Chg.refl _ _, rfl, rfl, rfl⟩
  refine stImm_ok B.scr (o := fCounter) (v := 0) (by simp only [fCounter, hdr]; omega)
    fun t₁ g₁ m₁ rd₁ wr₁ sy₁ => ?_
  have K₁ := K₀.store G v (d := fCounter) (by simp [ppRanges]) (by simp only [fSeed, fCounter, hdr]; omega)
    (by simp only [fCounter, sState, hdr]; omega) _ m₁ (g₁ _ (by decide)) (g₁ _ (by decide)) rd₁ wr₁ sy₁
  refine stImm_ok K₁.base.scr (o := fOffset) (v := 1) (by simp only [fOffset, hdr]; omega)
    fun t₂ g₂ m₂ rd₂ wr₂ sy₂ => ?_
  have K₂ := K₁.store G v (d := fOffset) (by simp [ppRanges]) (by simp only [fSeed, fOffset, hdr]; omega)
    (by simp only [fOffset, sState, hdr]; omega) _ m₂ (g₂ _ (by decide)) (g₂ _ (by decide)) rd₂ wr₂ sy₂
  refine stImm_end K₂.base.scr (o := fP) (v := 4) (by simp only [fP, hdr]; omega)
    fun t₃ g₃ m₃ rd₃ wr₃ sy₃ => ?_
  have K₃ := K₂.store G v (d := fP) (by simp [ppRanges, paRanges]) (by simp only [fSeed, fP, hdr]; omega)
    (by simp only [fP, sState, hdr]; omega) _ m₃ (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃ sy₃
  have ws : ∀ (m : Mem) {d e : Nat}, d + 4 ≤ sState → e + 4 ≤ sState → (d + 4 ≤ e ∨ e + 4 ≤ d) → ∀ x,
      (m.writeW (off E.base e) x).readW (off E.base d) 32 = m.readW (off E.base d) 32 :=
    fun m d e h₁ h₂ h x => word_store_other v m (by simp only [sState] at h₁; omega)
      (by simp only [sState] at h₂; omega) h x
  show PLoop E g k Q (Spec.Dsa.primeFromSeed (8 * g.pLen) (8 * g.qLen) Q (chunk E k) (E.witT.drop used)) s
      0 used t₃
  refine ⟨K₃, ?_, ?_, by rw [m₃, Mem.readW_writeW_self32], ?_, hu, primeSearch_start _ _ _ _ _⟩
  · rw [m₃, ws _ (by simp only [fCounter, sState, hdr]; omega) (by simp only [fP, sState, hdr]; omega)
      (by simp only [fCounter, fP, hdr]; omega), m₂, ws _ (by simp only [fCounter, sState, hdr]; omega)
      (by simp only [fOffset, sState, hdr]; omega) (by simp only [fCounter, fOffset, hdr]; omega), m₁,
      Mem.readW_writeW_self32]
  · rw [m₃, ws _ (by simp only [fOffset, sState, hdr]; omega) (by simp only [fP, sState, hdr]; omega)
      (by simp only [fOffset, fP, hdr]; omega), m₂, Mem.readW_writeW_self32, Nat.zero_mul]
  · rw [m₃, ws _ (by simp only [fUsed, sState, hdr]; omega) (by simp only [fP, sState, hdr]; omega)
      (by simp only [fUsed, fP, hdr]; omega), m₂, ws _ (by simp only [fUsed, sState, hdr]; omega)
      (by simp only [fOffset, sState, hdr]; omega) (by simp only [fUsed, fOffset, hdr]; omega), m₁,
      ws _ (by simp only [fUsed, sState, hdr]; omega) (by simp only [fCounter, sState, hdr]; omega)
      (by simp only [fUsed, fCounter, hdr]; omega), hU]

/-- p's search: the counters from 0, until one gives p, the witnesses run
out, or `4 L` are done. -/
theorem pPart_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen) {s : State} (B : Base E s)
    {k : Nat} (hk : (k + 1) * E.qLen ≤ E.seedsLen)
    (hS : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32) {Q : Nat}
    (hQ : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off E.base (sPk + g.pLen)) g.qLen) = Q) (hQ0 : 0 < Q)
    {used : Nat} (hU : s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used) (hu : used ≤ E.witLen) :
    WP isa g.pPart s fun t => PKeep E g k Q s t ∧
      PRes E g Q t.mem (Spec.Dsa.primeFromSeed (8 * g.pLen) (8 * g.qLen) Q (chunk E k) (E.witT.drop used)) := by
  have sz := v.size_ge
  have bd := G.bounds
  unfold Geo.pPart
  show WP isa (.seq (.block _) (.loop _ .e)) s _
  refine WP.seq (WP.mono (pInit_ok G v B hS hQ hU hu) fun t₃ L₀ => ?_)
  refine WP.loop (M := isa) (fun m t => ∃ c u, c + m = 4 * (8 * g.pLen) ∧ c < 4 * (8 * g.pLen) ∧
      PLoop E g k Q (Spec.Dsa.primeFromSeed (8 * g.pLen) (8 * g.qLen) Q (chunk E k) (E.witT.drop used)) s c u t)
    (fun m t ⟨c, u, hm, hc, L⟩ => WP.mono (pBody_ok G v hq hk hQ0 L hc) fun t' h => ?_) (4 * (8 * g.pLen)) t₃
    ⟨0, used, by omega, by omega, L₀⟩
  rcases h with ⟨z, K, res⟩ | ⟨z, hc', u', L'⟩
  · exact .inl ⟨z, K, res⟩
  · exact .inr ⟨z, m - 1, by omega, c + 1, u', by omega, hc', L'⟩

end VG.Proof.Dsa.X86.Generation
