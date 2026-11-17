module

public import VerifiedGarbage.Proof.Framework.RelCTChain
import VerifiedGarbage.Proof.Dsa.X86.PowCall
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Bignum.OutsFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PAttempt
public import VerifiedGarbage.Impl.Dsa.Layout
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geo
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Rsa.X86.DivContext
public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Proof.Dsa.Generation.Search
public import VerifiedGarbage.Proof.Dsa.Generation.GeneratorCount
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
import VerifiedGarbage.Proof.Bignum.X86.LoadBE
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.X86.Wp

/-! ### `Dsa.X86.Generation.GRange`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.Generation.PPart`, which this module and modules that import it used -/

section

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
    rcases h with rfl | rfl <;> simp only [fCounter, fOffset, fOut, fWitLen, hdr] <;> omega_using [sz]

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
  obtain hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * g.qLen) bs).length = 8 * g.qLen := fun bs => by
    rw [← G.seedHash, G.hash.hash_length, G.N]
  unfold pcand
  rw [pCandidate_shaped (by omega_using [bd]) hlen]
  obtain sh := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := 8 * g.pLen) (by omega_using [bd])
    (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) ((8 * g.pLen - 1) / (8 * g.qLen) + 1))
  have := pReduction_le (q := Q) sh.1
  exact ⟨by dsimp only; omega_using [sh, this], pReduction_odd _ _⟩

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
  obtain C : E.Chg [(d, 4)] t.mem t'.mem := by
    rw [hm]; exact (Env.Chg.refl _ _).store (List.mem_singleton_self _) (by decide) x
  refine ⟨P.base.keep v C (fun o ho => ppRanges_apart G v o (by simp only [List.mem_singleton] at ho; rw [ho]; exact hd))
    edi sp rd wr sy, ?_, ?_, P.chg.trans (C.widen fun o ho => ⟨o, by simp only [List.mem_singleton] at ho; rw [ho]; exact hd,
      Nat.le_refl _, Nat.le_refl _⟩), by rw [rd, P.rd], by rw [wr, P.wr], by rw [sy, P.syms]⟩
  · rw [hm, word_store_other v _ (by simp only [fSeed, hdr]; omega_using [sz]) (by simp only [sState] at hdq; omega_using [hdq, sz]) (.inl hs),
      P.seed]
  · rw [Env.Chg.scratch v C (by simp only [sPk]; omega_using [sz, bd]) fun o ho => by
      simp only [List.mem_singleton] at ho; subst ho; simp only [sState, sPk] at hdq ⊢; omega_using [hdq, sz], P.q]

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
  obtain cnt : g.count + 1 ≤ 12 := by
    unfold Geo.count; rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
  obtain cm : c * (g.count + 1) ≤ 12288 * 12 := Nat.mul_le_mul (by omega_arith) cnt
  obtain cs : (c + 1) * (g.count + 1) = c * (g.count + 1) + (g.count + 1) := Nat.succ_mul _ _
  obtain wl : E.witT.length = E.witLen := by rw [← L.keep.base.wit, VG.Proof.Bignum.bytesAt_length]
  simp only [seqs]
  refine WP.seq (WP.mono (pAttempt_ok G v hq L.keep.base hk L.keep.seed L.offset (by omega_arith) L.keep.q hQ0 L.used
    L.hu L.fp) fun t₁ A => ?_)
  obtain spec : (if pcand g E k (1 + c * (g.count + 1)) Q < 2 ^ (8 * g.pLen - 1) then
      primeSearch (8 * g.pLen) (8 * g.qLen) Q (chunk E k) (c + 1) (E.witT.drop u)
      else match Spec.Dsa.probablePrime (pcand g E k (1 + c * (g.count + 1)) Q) (E.witT.drop u) with
        | none => none
        | some (accepted, rest) => if accepted then some (some (pcand g E k (1 + c * (g.count + 1)) Q), rest)
          else primeSearch (8 * g.pLen) (8 * g.qLen) Q (chunk E k) (c + 1) rest) = R := by
    rw [← L.spec, primeSearch_step _ _ hc]; rfl
  -- What the counter leaves: still searching, or p's result.
  obtain out : ∃ F, t₁.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 F ∧ F < 2 ^ 32 ∧
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
          .inl ⟨rfl, E.witLen - rest.length, by omega_arith, ?_, ?_⟩⟩
        · rw [A.used]; simp only [hlt, hr, ↓reduceIte, nextUsed]
        · rw [cur, ← spec]; simp only [hlt, hr, ↓reduceIte, Bool.false_eq_true]
      · have cur := probablePrime_cursor hr
        rw [wl] at cur
        obtain hR : R = some (some (pcand g E k (1 + c * (g.count + 1)) Q), rest) := by
          rw [← spec]; simp only [hlt, hr, ↓reduceIte]
        refine ⟨1, by rw [A.fp]; simp only [hlt, hr, ↓reduceIte, pCode], by decide, .inr ⟨by decide, ?_⟩⟩
        rw [hR]
        obtain pb := pcand_bounds G (E := E) (k := k) (offset := 1 + c * (g.count + 1)) (Q := Q)
        refine ⟨by rw [A.fp]; simp only [hlt, hr, ↓reduceIte, pCode], by omega_arith, pb.1, pb.2,
          ⟨E.witLen - rest.length, by omega_arith, ?_, cur⟩, A.pk, A.pm1, A.e, A.pv, A.one⟩
        rw [A.used]; simp only [hlt, hr, ↓reduceIte, nextUsed]
  obtain ⟨F, hF, Fl, out⟩ := out
  -- What the counter keeps.
  obtain Apa := paRanges_apart G v
  obtain K₁ : PKeep E g k Q s t₁ := by
    refine ⟨A.base, ?_, ?_, L.keep.chg.trans (A.chg.widen fun o ho => ⟨o, List.mem_append_left _ ho, Nat.le_refl _,
      Nat.le_refl _⟩), by rw [A.rd, L.keep.rd], by rw [A.wr, L.keep.wr], by rw [A.syms, L.keep.syms]⟩
    · rw [Env.Chg.word v A.chg (by simp only [fSeed, hdr]; omega_arith) (fun o ho => ⟨(Apa o ho).1, by
        simp only [paRanges, pxRanges, aRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [sState, sX, arr, sPk, sPP, ppWords, fRes, fUsed, fUsedOut, fP, fSeed, hdr] <;> omega_arith⟩),
        L.keep.seed]
    · rw [Env.Chg.scratch v A.chg (by simp only [sPk]; omega_arith) (fun o ho => ⟨(Apa o ho).1, by
        simp only [paRanges, pxRanges, aRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [sState, sX, arr, sPk, sPP, ppWords, fRes, fUsed, fUsedOut, fP, hdr] <;> omega_arith⟩), L.keep.q]
  obtain word₁ : ∀ d, d + 4 ≤ fP → fRes + 4 ≤ d →
      t₁.mem.readW (off E.base d) 32 = t.mem.readW (off E.base d) 32 := fun d h₁ h₂ =>
    Env.Chg.word v A.chg (by simp only [fP, hdr] at h₁; omega_arith) (fun o ho => ⟨(Apa o ho).1, by
      simp only [paRanges, pxRanges, aRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [sState, sX, arr, sPk, sPP, ppWords, fRes, fUsed, fUsedOut, fP, hdr] at h₁ h₂ ⊢ <;> omega_arith⟩)
  obtain counter₁ : t₁.mem.readW (off E.base fCounter) 32 = BitVec.ofNat 32 c := by
    rw [word₁ fCounter (by simp only [fCounter, fP, hdr]; omega_arith) (by simp only [fCounter, fRes, hdr]; omega_arith),
      L.counter]
  obtain offset₁ : t₁.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 (1 + c * (g.count + 1)) := by
    rw [word₁ fOffset (by simp only [fOffset, fP, hdr]; omega_arith) (by simp only [fOffset, fRes, hdr]; omega_arith),
      L.offset]
  refine WP.seq (cmpF_end A.base.scr (o := fP) (v := 4) (by simp only [fP, hdr]; omega_arith) hF Fl (by decide)
    fun t₂ g₂ m₂ rd₂ wr₂ sy₂ z₂ => ?_)
  obtain K₂ := K₁.mem m₂ (g₂ _ (by decide)) (g₂ _ (by decide)) rd₂ wr₂ sy₂
  obtain fP₂ : t₂.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 F := by rw [m₂, hF]
  refine WP.seq (WP.ite _ z₂ (fun h4 => ?_) (fun h4 => WP.block_nil ?_))
  · -- Still searching: the next counter.
    obtain F4 : F = 4 := of_decide_eq_true h4
    obtain ⟨u', hu', hU', hs'⟩ := (out.resolve_right fun h => h.1 F4).2
    obtain wst : ∀ (m : Mem) {d e : Nat}, d + 4 ≤ sState → e + 4 ≤ sState → (d + 4 ≤ e ∨ e + 4 ≤ d) → ∀ x,
        (m.writeW (off E.base e) x).readW (off E.base d) 32 = m.readW (off E.base d) 32 :=
      fun m d e h₁ h₂ h x => word_store_other v m (by simp only [sState] at h₁; omega_arith)
        (by simp only [sState] at h₂; omega_arith) h x
    unfold Geo.pAdvance
    refine WP.seq (ld_ok K₂.base.scr (d := fCounter) (by simp only [fCounter, hdr]; omega_arith) fun t₃ u₃ =>
      wp_addi fun t₄ u₄ => st_ok (Scr.of_eq K₂.base.scr (by rw [u₄.other _ (by decide), u₃.other _ (by decide)])
        (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]) (by rw [u₄.wr, u₃.wr])) (d := fCounter)
        (by simp only [fCounter, hdr]; omega_arith) fun t₅ M₅ => ?_)
    obtain eax₄ : t₄.gpr .eax = BitVec.ofNat 32 (c + 1) := by
      rw [u₄.gpr, u₃.gpr, m₂, counter₁, BitVec.ofNat_add]; rfl
    obtain m₅ : t₅.mem = t₂.mem.writeW (off E.base fCounter) (BitVec.ofNat 32 (c + 1)) := by
      rw [M₅.mem, u₄.mem, u₃.mem, eax₄]
    obtain r₅ : ∀ r, r ≠ .eax → t₅.gpr r = t₂.gpr r := fun r hr => by
      rw [M₅.gpr, u₄.other r hr, u₃.other r hr]
    obtain K₅ := K₂.store G v (d := fCounter) (by simp [ppRanges]) (by simp only [fSeed, fCounter, hdr]; omega_arith)
      (by simp only [fCounter, sState, hdr]; omega_arith) _ m₅ (r₅ _ (by decide)) (r₅ _ (by decide))
      (by rw [M₅.rd, u₄.rd, u₃.rd]) (by rw [M₅.wr, u₄.wr, u₃.wr]) (by rw [M₅.syms, u₄.syms, u₃.syms])
    refine ld_ok K₅.base.scr (d := fOffset) (by simp only [fOffset, hdr]; omega_arith) fun t₆ u₆ =>
      wp_addi fun t₇ u₇ => st_ok (Scr.of_eq K₅.base.scr (by rw [u₇.other _ (by decide), u₆.other _ (by decide)])
        (by rw [u₇.other _ (by decide), u₆.other _ (by decide)]) (by rw [u₇.wr, u₆.wr])) (d := fOffset)
        (by simp only [fOffset, hdr]; omega_arith) fun t₈ M₈ => wp_cmpi fun t₉ f₉ _ z₉ => WP.block_nil ?_
    obtain ecx₇ : t₇.gpr .ecx = BitVec.ofNat 32 (1 + (c + 1) * (g.count + 1)) := by
      rw [u₇.gpr, u₆.gpr, m₅, wst _ (by simp only [fOffset, sState, hdr]; omega_arith)
        (by simp only [fCounter, sState, hdr]; omega_arith) (by simp only [fOffset, fCounter, hdr]; omega_arith), m₂,
        offset₁, ← BitVec.ofNat_add, cs, Nat.add_assoc]
    obtain m₈ : t₈.mem = t₅.mem.writeW (off E.base fOffset) (BitVec.ofNat 32 (1 + (c + 1) * (g.count + 1))) := by
      rw [M₈.mem, u₇.mem, u₆.mem, ecx₇]
    obtain r₈ : ∀ r, r ≠ .eax → r ≠ .ecx → t₈.gpr r = t₅.gpr r := fun r h₁ h₂ => by
      rw [M₈.gpr, u₇.other r h₂, u₆.other r h₂]
    obtain K₈ := K₅.store G v (d := fOffset) (by simp [ppRanges]) (by simp only [fSeed, fOffset, hdr]; omega_arith)
      (by simp only [fOffset, sState, hdr]; omega_arith) _ m₈ (r₈ _ (by decide) (by decide)) (r₈ _ (by decide) (by decide))
      (by rw [M₈.rd, u₇.rd, u₆.rd]) (by rw [M₈.wr, u₇.wr, u₆.wr]) (by rw [M₈.syms, u₇.syms, u₆.syms])
    obtain K₉ := K₈.mem f₉.mem (by rw [f₉.gpr]) (by rw [f₉.gpr]) f₉.rd f₉.wr f₉.syms
    obtain m₉ : t₉.mem = (t₂.mem.writeW (off E.base fCounter) (BitVec.ofNat 32 (c + 1))).writeW (off E.base fOffset)
        (BitVec.ofNat 32 (1 + (c + 1) * (g.count + 1))) := by rw [f₉.mem, m₈, m₅]
    obtain word₉ : ∀ d, d + 4 ≤ sState → (d + 4 ≤ fCounter ∨ fOffset + 4 ≤ d) →
        t₉.mem.readW (off E.base d) 32 = t₂.mem.readW (off E.base d) 32 := fun d h₁ h₂ => by
      rw [m₉, wst _ h₁ (by simp only [fOffset, sState, hdr]; omega_arith) (by simp only [fOffset, fCounter, hdr] at h₂ ⊢; omega_arith),
        wst _ h₁ (by simp only [fCounter, sState, hdr]; omega_arith) (by simp only [fOffset, fCounter, hdr] at h₂ ⊢; omega_arith)]
    obtain zf₉ : isa.eval .e t₉ = some (decide (c + 1 = 4 * (8 * g.pLen))) := by
      show t₉.zf = _
      rw [z₉, M₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), M₅.gpr, eax₄,
        show (BitVec.ofNat 32 (32 * g.pLen) : BitVec 32) = BitVec.ofNat 32 (4 * (8 * g.pLen)) by congr 1; omega_arith,
        sub_beq (by omega_arith) (by omega_arith)]
    obtain fP₉ : t₉.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 4 := by
      rw [word₉ fP (by simp only [fP, sState, hdr]; omega_arith) (by simp only [fP, fOffset, hdr]; omega_arith), fP₂, F4]
    obtain fU₉ : t₉.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 u' := by
      rw [word₉ fUsed (by simp only [fUsed, sState, hdr]; omega_arith) (by simp only [fUsed, fCounter, hdr]; omega_arith), m₂, hU']
    obtain cnt₉ : t₉.mem.readW (off E.base fCounter) 32 = BitVec.ofNat 32 (c + 1) := by
      rw [m₉, wst _ (by simp only [fCounter, sState, hdr]; omega_arith) (by simp only [fOffset, sState, hdr]; omega_arith)
        (by simp only [fOffset, fCounter, hdr]; omega_arith), Mem.readW_writeW_self32]
    obtain off₉ : t₉.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 (1 + (c + 1) * (g.count + 1)) := by
      rw [m₉, Mem.readW_writeW_self32]
    refine WP.ite _ zf₉ (fun hd => stImm_end K₉.base.scr (o := fP) (v := 2) (by simp only [fP, hdr]; omega_arith)
      fun t₁₀ g₁₀ m₁₀ rd₁₀ wr₁₀ sy₁₀ => ?_) (fun hd => WP.block_nil ?_)
    · -- The `4 L` counters are done: no p.
      obtain K₁₀ := K₉.store G v (d := fP) (by simp [ppRanges, paRanges]) (by simp only [fSeed, fP, hdr]; omega_arith)
        (by simp only [fP, sState, hdr]; omega_arith) _ m₁₀ (g₁₀ _ (by decide)) (g₁₀ _ (by decide)) rd₁₀ wr₁₀ sy₁₀
      obtain hR : R = some (none, E.witT.drop u') := by
        rw [← hs', primeSearch_done _ _ (by have := of_decide_eq_true hd; omega_arith)]
      refine cmpF_end K₁₀.base.scr (o := fP) (v := 4) (w := 2) (by simp only [fP, hdr]; omega_arith)
        (by rw [m₁₀, Mem.readW_writeW_self32]) (by decide) (by decide) fun t₁₁ g₁₁ m₁₁ rd₁₁ wr₁₁ sy₁₁ z₁₁ => ?_
      refine .inl ⟨z₁₁, K₁₀.mem m₁₁ (g₁₁ _ (by decide)) (g₁₁ _ (by decide)) rd₁₁ wr₁₁ sy₁₁, ?_⟩
      rw [hR]
      refine ⟨by rw [m₁₁, m₁₀, Mem.readW_writeW_self32], u', hu', ?_, rfl⟩
      rw [m₁₁, m₁₀, word_store_other v _ (by simp only [fUsed, hdr]; omega_arith) (by simp only [fP, hdr]; omega_arith)
        (by simp only [fUsed, fP, hdr]; omega_arith), fU₉]
    · -- On to the next counter.
      refine cmpF_end K₉.base.scr (o := fP) (v := 4) (w := 4) (by simp only [fP, hdr]; omega_arith) fP₉ (by decide)
        (by decide) fun t₁₁ g₁₁ m₁₁ rd₁₁ wr₁₁ sy₁₁ z₁₁ => .inr ⟨z₁₁, by have := of_decide_eq_false hd; omega_arith, u', ?_⟩
      exact ⟨K₉.mem m₁₁ (g₁₁ _ (by decide)) (g₁₁ _ (by decide)) rd₁₁ wr₁₁ sy₁₁, by rw [m₁₁]; exact cnt₉,
        by rw [m₁₁]; exact off₉, by rw [m₁₁]; exact fP₉, by rw [m₁₁]; exact fU₉, hu', hs'⟩
  · -- p's result.
    obtain F4 : F ≠ 4 := of_decide_eq_false h4
    obtain res := (out.resolve_left fun h => F4 h.1).2
    refine cmpF_end K₂.base.scr (o := fP) (v := 4) (w := F) (by simp only [fP, hdr]; omega_arith) fP₂ Fl (by decide)
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
  obtain K₀ : PKeep E g k Q s s := ⟨B, hS, hQ, Env.Chg.refl _ _, rfl, rfl, rfl⟩
  refine stImm_ok B.scr (o := fCounter) (v := 0) (by simp only [fCounter, hdr]; omega_arith)
    fun t₁ g₁ m₁ rd₁ wr₁ sy₁ => ?_
  obtain K₁ := K₀.store G v (d := fCounter) (by simp [ppRanges]) (by simp only [fSeed, fCounter, hdr]; omega_arith)
    (by simp only [fCounter, sState, hdr]; omega_arith) _ m₁ (g₁ _ (by decide)) (g₁ _ (by decide)) rd₁ wr₁ sy₁
  refine stImm_ok K₁.base.scr (o := fOffset) (v := 1) (by simp only [fOffset, hdr]; omega_arith)
    fun t₂ g₂ m₂ rd₂ wr₂ sy₂ => ?_
  obtain K₂ := K₁.store G v (d := fOffset) (by simp [ppRanges]) (by simp only [fSeed, fOffset, hdr]; omega_arith)
    (by simp only [fOffset, sState, hdr]; omega_arith) _ m₂ (g₂ _ (by decide)) (g₂ _ (by decide)) rd₂ wr₂ sy₂
  refine stImm_end K₂.base.scr (o := fP) (v := 4) (by simp only [fP, hdr]; omega_arith)
    fun t₃ g₃ m₃ rd₃ wr₃ sy₃ => ?_
  obtain K₃ := K₂.store G v (d := fP) (by simp [ppRanges, paRanges]) (by simp only [fSeed, fP, hdr]; omega_arith)
    (by simp only [fP, sState, hdr]; omega_arith) _ m₃ (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃ sy₃
  obtain ws : ∀ (m : Mem) {d e : Nat}, d + 4 ≤ sState → e + 4 ≤ sState → (d + 4 ≤ e ∨ e + 4 ≤ d) → ∀ x,
      (m.writeW (off E.base e) x).readW (off E.base d) 32 = m.readW (off E.base d) 32 :=
    fun m d e h₁ h₂ h x => word_store_other v m (by simp only [sState] at h₁; omega_arith)
      (by simp only [sState] at h₂; omega_arith) h x
  show PLoop E g k Q (Spec.Dsa.primeFromSeed (8 * g.pLen) (8 * g.qLen) Q (chunk E k) (E.witT.drop used)) s
      0 used t₃
  refine ⟨K₃, ?_, ?_, by rw [m₃, Mem.readW_writeW_self32], ?_, hu, primeSearch_start _ _ _ _ _⟩
  · rw [m₃, ws _ (by simp only [fCounter, sState, hdr]; omega_arith) (by simp only [fP, sState, hdr]; omega_arith)
      (by simp only [fCounter, fP, hdr]; omega_arith), m₂, ws _ (by simp only [fCounter, sState, hdr]; omega_arith)
      (by simp only [fOffset, sState, hdr]; omega_arith) (by simp only [fCounter, fOffset, hdr]; omega_arith), m₁,
      Mem.readW_writeW_self32]
  · rw [m₃, ws _ (by simp only [fOffset, sState, hdr]; omega_arith) (by simp only [fP, sState, hdr]; omega_arith)
      (by simp only [fOffset, fP, hdr]; omega_arith), m₂, Mem.readW_writeW_self32, Nat.zero_mul]
  · rw [m₃, ws _ (by simp only [fUsed, sState, hdr]; omega_arith) (by simp only [fP, sState, hdr]; omega_arith)
      (by simp only [fUsed, fP, hdr]; omega_arith), m₂, ws _ (by simp only [fUsed, sState, hdr]; omega_arith)
      (by simp only [fOffset, sState, hdr]; omega_arith) (by simp only [fUsed, fOffset, hdr]; omega_arith), m₁,
      ws _ (by simp only [fUsed, sState, hdr]; omega_arith) (by simp only [fCounter, sState, hdr]; omega_arith)
      (by simp only [fUsed, fCounter, hdr]; omega_arith), hU]

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
    ⟨0, used, by omega_using [], by omega_using [bd], L₀⟩
  rcases h with ⟨z, K, res⟩ | ⟨z, hc', u', L'⟩
  · exact .inl ⟨z, K, res⟩
  · exact .inr ⟨z, m - 1, by omega_using [hm, hc], c + 1, u', by omega_using [hm, hc], hc', L'⟩

end VG.Proof.Dsa.X86.Generation

end

end

/-! # The generator's candidate `h` and its range check (A.2.1 steps 1–3) -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)
open VG.Impl.Mont.X86.Dynamic (chainW selectsW)

/-- `h` number `j`: its `pLen` bytes of the tape. -/
def hChunk (E : Env) (j : Nat) : List Byte := (E.hT.drop (j * E.pLen)).take E.pLen

theorem cmask_zf (c : Bool) : (cmask c - 0 == 0) = !c := by cases c <;> decide

theorem cmask_and (a b : Bool) : (cmask a &&& cmask b) = cmask (a && b) := by cases a <;> cases b <;> decide

/-- A borrow out of `a − b` is `a < b`. -/
theorem borrow_lt {o a b K : Nat} {c : Bool} (h : o + b = a + K * c.toNat) (ho : o < K) :
    c = decide (a < b) := by
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at h
  · exact (decide_eq_false (by omega_using [h])).symm
  · exact (decide_eq_true (by omega_using [ho, h])).symm

/-- A change of memory that a helper call makes within ranges of `scratch`
and the call's stack. -/
theorem Env.Chg.of_stackOuts {E : Env} (v : E.Valid) {rs : List (Nat × Nat)} {m m' : Mem}
    (O : VG.Proof.Dsa.X86.StackOuts E.base E.sp rs m m') (fit : ∀ r ∈ rs, r.1 + r.2 ≤ E.size) :
    E.Chg rs m m' := by
  have nw := v.scratchFit
  intro x hx
  refine O x (fun r hr => ?_) (.inr fun hc => ?_)
  · have H := hx ⟨off E.base r.1, r.2⟩ (List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
    obtain I := Offset.lt_iff x E.base (show r.1 + r.2 ≤ 2 ^ 64 by have := fit r hr; omega_using [nw, this])
    change ¬ ((x - off E.base r.1).toNat + 1 ≤ r.2) at H
    change (x - off E.base r.1).toNat < r.2 ↔ r.1 ≤ ofs E.base x ∧ ofs E.base x < r.1 + r.2 at I
    omega_using [H, I]
  · exact hx E.stackRegion (List.mem_append_right _ (List.mem_singleton_self _))
      (below_sub (by decide : 108 ≤ 200) v.low x (show (below E.sp 108).Contains x 1 from hc))

/-- The range check's ranges: the temporary, `h` and the word of the first
borrow. -/
def rRanges : List (Nat × Nat) := [(aTmp, 400), (aH, 400), (fLo, 4)]

/-- After the range check of `h`: `h` in its array and ZF clear exactly when
`1 < h < p − 1`. -/
structure RangePost (E : Env) (g : Geo) (j p : Nat) (s t : State) : Prop where
  base : Base E t
  h : val32 t.mem E.base aH g.n32 = Spec.Dsa.decodeBE (hChunk E j)
  zf : isa.eval .e t = some (!decide (1 < Spec.Dsa.decodeBE (hChunk E j) ∧
    Spec.Dsa.decodeBE (hChunk E j) < p - 1))
  chg : E.Chg rRanges s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem rRanges_apart {E : Env} (v : E.Valid) : E.Apart rRanges := by
  have sz := v.size_ge
  intro o ho
  simp only [rRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl <;> simp only [aTmp, aH, arr, fLo, fOut, fWitLen, hdr] <;> omega_using [sz]

/-- The `pLen` bytes of `h` number `j` at its address in the tape. -/
theorem h_bytes {E : Env} (v : E.Valid) {s : State} (B : Base E s) {j : Nat} (hj : (j + 1) * E.pLen ≤ E.hsLen) :
    Spec.Rsa.bytesAt s.mem (E.hs + BitVec.ofNat 64 (j * E.pLen)) E.pLen = hChunk E j := by
  rw [Nat.succ_mul] at hj
  have := v.hsIn
  rw [Env.hs, VG.Offset.add_add, B.part (by omega_using [hj, this])]
  simp only [hChunk, Env.hT, List.drop_take, List.drop_drop, List.take_take]
  congr 1
  omega_using [hj]

/-- `h` number `j` is loaded, and compared with 1 and `p − 1`. -/
theorem gRange_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) {s : State} (B : Base E s)
    {j p : Nat} (hj : (j + 1) * E.pLen ≤ E.hsLen)
    (hH : s.mem.readW (off E.base fH) 32 = (E.hs + BitVec.ofNat 64 (j * E.pLen)).setWidth 32)
    (hone : val32 s.mem E.base aOne g.n32 = 1) (hpm1 : val32 s.mem E.base aPm1 g.n32 = p - 1)
    {P : Prog isa} {Q : State → Prop} (k : ∀ t, RangePost E g j p s t → WP isa P t Q) :
    WP isa (.seq (.block [.mov .esi (.mem (sc fH)), .mov .ecx (.imm (BitVec.ofNat 32 g.pLen))])
      (.seq (VG.Impl.Bignum.X86.loadBE g.n64 aH) (.seq (chainW .sbb g.n32 aTmp aOne aH)
      (.seq (.block [.store (sc fLo) .ecx]) (.seq (chainW .sbb g.n32 aTmp aH aPm1)
      (.seq (.block [.alu .and .ecx (.mem (sc fLo)), .alu .cmp .ecx (.imm 0)]) P)))))) s Q := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have hf := v.hsFit
  have n64 : g.n64 = g.pLen / 8 := rfl
  have n32 : g.n32 = g.pLen / 4 := rfl
  obtain h2 : 2 * g.n64 = g.n32 := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, n32, h]
  obtain h8 : 8 * g.n64 = g.pLen := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, h]
  obtain jq : j * E.pLen + E.pLen ≤ E.hsLen := by rw [Nat.succ_mul] at hj; omega_arith
  obtain hl : E.hs.toNat < 2 ^ 32 := by have := v.pLen_ge; omega_arith
  obtain hW : ((E.hs + BitVec.ofNat 64 (j * E.pLen)).setWidth 32).setWidth 64 = E.hs + BitVec.ofNat 64 (j * E.pLen) := by
    apply BitVec.eq_of_toNat_eq
    obtain e : (E.hs + BitVec.ofNat 64 (j * E.pLen)).toNat = E.hs.toNat + j * E.pLen := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j * E.pLen) (by omega_arith),
        Nat.mod_eq_of_lt (by omega_arith)]
    simp only [BitVec.toNat_setWidth, e]
    rw [Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  obtain hN : ((E.hs + BitVec.ofNat 64 (j * E.pLen)).setWidth 32).toNat = E.hs.toNat + j * E.pLen := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j * E.pLen) (by omega_arith),
      Nat.mod_eq_of_lt (a := E.hs.toNat + j * E.pLen) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  -- `h`.
  refine WP.seq (ld_ok B.scr (d := fH) (by simp only [fH, hdr]; omega_arith) fun s₁ u₁ => wp_movi fun s₂ u₂ =>
    WP.block_nil ?_)
  obtain hs₂ : Scr s₂ E.base E.size := Scr.of_eq B.scr (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr])
  obtain esi₂ : s₂.gpr .esi = (E.hs + BitVec.ofNat 64 (j * E.pLen)).setWidth 32 := by
    rw [u₂.other _ (by decide), u₁.gpr, hH]
  obtain m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  obtain K₂ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s s₂ :=
    ⟨fun r hr => by rw [u₂.other r (fun e => hr (e ▸ by simp)), u₁.other r (fun e => hr (e ▸ by simp))],
      by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  obtain sub : Region.Sub ⟨E.hs + BitVec.ofNat 64 (j * E.pLen), E.pLen⟩ E.hsRegion :=
    Offset.sub_base _ (show j * E.pLen + E.pLen ≤ E.hsLen by omega_arith)
  refine WP.seq (VG.X86.WP.mono_syms (VG.Proof.Bignum.X86.loadBE_ok hs₂ (n := g.n64) (out := aH) (len := g.pLen)
    (by omega_arith) (by simp only [aH, arr]; omega_arith) (by omega_arith) (by omega_arith) (by rw [esi₂, hN]; omega_arith) u₂.gpr
    (by rw [esi₂, VG.Proof.Bignum.X86.byteAddr, hW, u₂.rd, u₂.wr, u₁.rd, u₁.wr, ← hp]
        have := v.hsIn; have := v.witLen32
        exact ⟨_, List.mem_append_left _ B.tapes, by
          rw [Env.hs, VG.Offset.add_add]
          exact Offset.contains_base _ (show E.hsOff + j * E.pLen + E.pLen ≤ E.witLen by omega_arith) (by omega_arith)⟩)
    (by rw [esi₂, VG.Proof.Bignum.X86.byteAddr, hW, ← hp]
        exact ((v.tapesFar _ (by simp)).1.sub_left sub).sub_right (Offset.sub_base _ (by simp only [aH, arr]; omega_arith))))
    fun t₃ ⟨V₃, O₃, K₃⟩ sy₃ => ?_)
  rw [esi₂, VG.Proof.Bignum.X86.byteAddr, hW, m₂, ← hp, h_bytes v B hj, wordsVal_eq_val32, h2,
    ← VG.Proof.Dsa.decodeBE_os2ip] at V₃
  obtain hs₃ := hs₂.of_keeps K₃ (by decide)
  obtain one₃ : val32 t₃.mem E.base aOne g.n32 = 1 := by
    rw [O₃.val32 (by simp only [aH, aOne, arr]; omega_arith) (by simp only [aOne, arr]; omega_arith), m₂, hone]
  obtain pm₃ : val32 t₃.mem E.base aPm1 g.n32 = p - 1 := by
    rw [O₃.val32 (by simp only [aH, aPm1, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith), m₂, hpm1]
  -- `1 < h`.
  refine WP.seq (VG.X86.WP.mono_syms (chainSubW_ok hs₃ (k := g.n32) (o := aTmp) (a := aOne) (b := aH) (by omega_arith)
    (by simp only [aTmp, arr]; omega_arith) (by simp only [aOne, arr]; omega_arith) (by simp only [aH, arr]; omega_arith)
    (by simp only [aTmp, aOne, arr]; omega_arith) (by simp only [aTmp, aH, arr]; omega_arith)) fun t₄ ⟨O₄, ⟨c₄, e₄, E₄⟩, K₄⟩ sy₄ =>
    ?_)
  rw [one₃, V₃] at E₄
  obtain c₄v := borrow_lt E₄ (val32_lt _ _ _ _)
  obtain hs₄ := hs₃.of_keeps K₄ (by decide)
  refine WP.seq (st_ok hs₄ (d := fLo) (by simp only [fLo, hdr]; omega_arith) fun t₅ M₅ => WP.block_nil ?_)
  obtain hs₅ : Scr t₅ E.base E.size := Scr.of_eq hs₄ (by rw [M₅.gpr]) (by rw [M₅.gpr]) M₅.wr
  obtain O₅ : Outside E.base fLo 4 t₄.mem t₅.mem := by
    rw [M₅.mem]; exact writeW32_outside _ _ _ (by simp only [fLo, hdr]; omega_arith)
  obtain h₅ : val32 t₅.mem E.base aH g.n32 = Spec.Dsa.decodeBE (hChunk E j) := by
    rw [O₅.val32 (by simp only [aH, fLo, arr, hdr]; omega_arith) (by simp only [aH, arr]; omega_arith),
      O₄.val32 (by simp only [aH, aTmp, arr]; omega_arith) (by simp only [aH, arr]; omega_arith), V₃]
  obtain pm₅ : val32 t₅.mem E.base aPm1 g.n32 = p - 1 := by
    rw [O₅.val32 (by simp only [aPm1, fLo, arr, hdr]; omega_arith) (by simp only [aPm1, arr]; omega_arith),
      O₄.val32 (by simp only [aPm1, aTmp, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith), pm₃]
  -- `h < p − 1`.
  refine WP.seq (VG.X86.WP.mono_syms (chainSubW_ok hs₅ (k := g.n32) (o := aTmp) (a := aH) (b := aPm1) (by omega_arith)
    (by simp only [aTmp, arr]; omega_arith) (by simp only [aH, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith)
    (by simp only [aTmp, aH, arr]; omega_arith) (by simp only [aTmp, aPm1, arr]; omega_arith)) fun t₆ ⟨O₆, ⟨c₆, e₆, E₆⟩, K₆⟩ sy₆ =>
    ?_)
  rw [h₅, pm₅] at E₆
  obtain c₆v := borrow_lt E₆ (val32_lt _ _ _ _)
  obtain hs₆ := hs₅.of_keeps K₆ (by decide)
  obtain lo₆ : t₆.mem.readW (off E.base fLo) 32 = cmask c₄ := by
    apply BitVec.eq_of_toNat_eq
    rw [show (t₆.mem.readW (off E.base fLo) 32).toNat = w32 t₆.mem E.base fLo from rfl,
      O₆.w32 (by simp only [aTmp, fLo, arr, hdr]; omega_arith) (by simp only [fLo, hdr]; omega_arith), M₅.mem,
      w32_write_self, e₄]
  refine WP.seq (andm_ok hs₆ (r := .ecx) (d := fLo) (by simp only [fLo, hdr]; omega_arith) fun t₇ u₇ =>
    wp_cmpi fun t₈ f₈ _ z₈ => WP.block_nil (k t₈ ?_))
  obtain h₆ : val32 t₆.mem E.base aH g.n32 = Spec.Dsa.decodeBE (hChunk E j) := by
    rw [O₆.val32 (by simp only [aH, aTmp, arr]; omega_arith) (by simp only [aH, arr]; omega_arith), h₅]
  obtain m₈ : t₈.mem = t₆.mem := by rw [f₈.mem, u₇.mem]
  obtain Ksum : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t₈ :=
    K₂.trans (K₃.trans ((K₄.mono (by decide)).trans ((show Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] t₄ t₅ from
      ⟨fun r _ => by rw [M₅.gpr], M₅.rd, M₅.wr⟩).trans
      ((K₆.mono (by decide)).trans ⟨fun r hr => by rw [f₈.gpr, u₇.other r (fun e => hr (e ▸ by simp))],
        by rw [f₈.rd, u₇.rd], by rw [f₈.wr, u₇.wr]⟩))))
  obtain Ar := rRanges_apart v
  obtain inR : ∀ {o n d len : Nat}, (o, n) ∈ rRanges → o ≤ d → d + len ≤ o + n →
      ∃ r' ∈ (rRanges.map fun o => (⟨off E.base o.1, o.2⟩ : Region)) ++ [E.stackRegion],
        Region.Sub ⟨off E.base d, len⟩ r' := fun ho h₁ h₂ => Env.in_range ho h₁ h₂
  obtain ofOut : ∀ {m m' : Mem} {o n o' n' : Nat}, Outside E.base o n m m' → (o', n') ∈ rRanges → o' ≤ o →
      o + n ≤ o' + n' → E.Chg rRanges m m' := by
    intro m m' o n o' n' O ho h₁ h₂
    obtain fit := (Ar _ ho).1
    refine Env.Chg.of_frame (VG.Proof.Bignum.outs_frame (Outs.of_outside O (List.mem_singleton_self _)) ?_) ?_
    · intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      show o + n ≤ 2 ^ 64
      omega_arith
    · intro r hr
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr
      exact inR ho h₁ h₂
  obtain C₃ : E.Chg rRanges s.mem t₃.mem := by
    rw [← m₂]; exact ofOut O₃ (o' := aH) (n' := 400) (by simp [rRanges]) (Nat.le_refl _)
      (by simp only [aH, arr]; omega_arith)
  obtain C₄ := ofOut O₄ (o' := aTmp) (n' := 400) (by simp [rRanges]) (Nat.le_refl _) (by simp only [aTmp, arr]; omega_arith)
  obtain C₅ := ofOut O₅ (o' := fLo) (n' := 4) (by simp [rRanges]) (Nat.le_refl _) (Nat.le_refl _)
  obtain C₆ := ofOut O₆ (o' := aTmp) (n' := 400) (by simp [rRanges]) (Nat.le_refl _) (by simp only [aTmp, arr]; omega_arith)
  obtain C : E.Chg rRanges s.mem t₈.mem := by
    rw [m₈]; exact C₃.trans (C₄.trans (C₅.trans C₆))
  obtain sy₈ : t₈.syms = s.syms := by
    rw [f₈.syms, u₇.syms, sy₆, M₅.syms, sy₄, sy₃, u₂.syms, u₁.syms]
  refine ⟨B.keep v C Ar (Ksum.1 _ (by decide)) (Ksum.1 _ (by decide)) Ksum.2.1 Ksum.2.2 sy₈, by rw [m₈]; exact h₆,
    ?_, C, Ksum.2.1, Ksum.2.2, sy₈⟩
  show t₈.zf = _
  rw [z₈, u₇.gpr, e₆, lo₆, cmask_and, cmask_zf, c₆v, c₄v, Bool.and_comm, ← Bool.decide_and]

end VG.Proof.Dsa.X86.Generation

end

end

/-! ### `Dsa.X86.Generation.GPow`, which only this module used -/

section

/-! # `g = h^((p − 1)/q) mod p` and its check `g > 1` (A.2.1 steps 4–5) -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)
open VG.Impl.Mont.X86.Dynamic (chainW selectsW slot stride contextBytes)

/-- The first `k` of `k + r` words, when their value fits in `k`. -/
theorem val32_prefix {m : Mem} {base : Addr} {d k r v : Nat} (h : val32 m base d (k + r) = v)
    (hv : v < 2 ^ (32 * k)) : val32 m base d k = v := by
  rw [val32_append] at h
  have := val32_lt m base d k
  obtain hm : 2 ^ (32 * k) * val32 m base (d + 4 * k) r = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m base (d + 4 * k) r) with h0 | h0
    · rw [h0, Nat.mul_zero]
    · have := Nat.mul_le_mul_left (2 ^ (32 * k)) h0; omega_arith
  omega_arith

/-- The ranges `g`'s computation changes: the exponentiation's working space
below the header, the temporary, `g` in p||q||g and `fG`. -/
def wRanges (g : Geo) : List (Nat × Nat) := [(0, 7168), (aTmp, 400), (sPk + g.pLen + g.qLen, g.pLen), (fG, 4)]

theorem wRanges_apart {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) : E.Apart (wRanges g) := by
  have sz := v.size_ge
  have bd := G.bounds
  intro o ho
  simp only [wRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl <;> simp only [aTmp, arr, sPk, fG, fOut, fWitLen, hdr] <;> omega_arith

/-- `h^((p − 1)/q) mod p`, as the exponentiation computes it. -/
def gVal (h p x : Nat) : Nat := h ^ x % p

/-- After `g` from `h`: `fG` := 1 with `g` in p||q||g if `g > 1`. -/
structure PowPost (E : Env) (g : Geo) (gv F : Nat) (s t : State) : Prop where
  base : Base E t
  fg : t.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 (if 1 < gv then 1 else F)
  gb : 1 < gv → Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen + g.qLen)) g.pLen = Spec.Dsa.encodeBE g.pLen gv
  chg : E.Chg (wRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

/-- A change within one range of `scratch` is a change within a range around it. -/
theorem Env.Chg.of_outside {E : Env} (v : E.Valid) {os : List (Nat × Nat)} {m m' : Mem} {o n o' n' : Nat}
    (O : Outside E.base o n m m') (ho : (o', n') ∈ os) (h₁ : o' ≤ o) (h₂ : o + n ≤ o' + n')
    (fit : o' + n' ≤ E.size) : E.Chg os m m' := by
  have nw := v.scratchFit
  refine Env.Chg.of_frame (VG.Proof.Bignum.outs_frame (Outs.of_outside O (List.mem_singleton_self _)) ?_) ?_
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    show o + n ≤ 2 ^ 64
    omega_arith
  · intro r hr
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr
    exact Env.in_range ho h₁ h₂

/-- Before the check `g > 1`: `g` in the exponentiation's result, ZF set
exactly when `g ≤ 1`. -/
structure PowMid (E : Env) (g : Geo) (gv F : Nat) (s t : State) : Prop where
  base : Base E t
  zf : isa.eval .e t = some (!decide (1 < gv))
  res : val32 t.mem E.base (slot g.n64 6) g.n32 = gv
  fg : t.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F
  chg : E.Chg (wRanges g) s.mem t.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  syms : t.syms = s.syms

/-- After the exponentiation's arguments are in place. -/
structure SelPost (E : Env) (g : Geo) (p h x F : Nat) (s t : State) : Prop where
  scr : Scr t E.base E.size
  sp : t.gpr .esp = E.sp
  modv : wordsVal t.mem E.base (slot g.n64 0) g.n64 = p
  basev : val32 t.mem E.base (slot g.n64 5) g.n32 = h
  expv : val32 t.mem E.base (slot g.n64 8) g.e = x
  one : val32 t.mem E.base aOne g.n32 = 1
  fg : t.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F
  chg : E.Chg [(0, 7168), (aTmp, 400)] s.mem t.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  syms : t.syms = s.syms

/-- p, h and `(p − 1)/q` into the exponentiation's arrays. -/
theorem gPowSel_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s : State} (B : Base E s) {p h x F : Nat}
    (hP : val32 s.mem E.base aP g.n32 = p) (hH : val32 s.mem E.base aH g.n32 = h)
    (hE : val32 s.mem E.base aE g.n32 = x) (hx : x < 2 ^ (32 * g.e)) (hone : val32 s.mem E.base aOne g.n32 = 1)
    (hF : s.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F)
    {P : Prog isa} {Q : State → Prop} (k : ∀ t, SelPost E g p h x F s t → WP isa P t Q) :
    WP isa (Prog.chain [.block [.mov .ecx (.imm 0)],
      selectsW g.n32 aP aP (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).modulus,
      .block [.mov .ecx (.imm 0)], selectsW g.n32 aH aH (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).base,
      .block [.mov .ecx (.imm 0)], selectsW g.e aE aE (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).exponent] P) s Q := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have n64 : g.n64 = g.pLen / 8 := rfl
  have n32 : g.n32 = g.pLen / 4 := rfl
  obtain h2 : 2 * g.n64 = g.n32 := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, n32, h]
  obtain h8 : 8 * g.n64 = g.pLen := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, h]
  obtain he : 1 < g.e ∧ g.e ≤ 2 * g.n64 ∧ g.e ≤ g.n32 := by
    rw [G.e, n64, n32]
    rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
  obtain slots : ∀ i, i ≤ 9 → slot g.n64 i ≤ 7048 := fun i hi => by
    simp only [slot, stride]; have := Nat.mul_le_mul hi (show 16 * g.n64 + 8 ≤ 776 by omega_arith); omega_arith
  obtain cb : contextBytes g.n64 ≤ 7048 := slots 9 (Nat.le_refl _)
  obtain sl : ∀ i, slot g.n64 i + 8 * g.n64 ≤ slot g.n64 (i + 1) := fun i => by
    simp only [slot, stride, Nat.succ_mul]; omega_arith
  have mod : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).modulus = slot g.n64 0 := rfl
  have bas : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).base = slot g.n64 5 := rfl
  have exn : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).exponent = slot g.n64 8 := rfl
  have res : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result = slot g.n64 6 := rfl
  rw [mod, bas, exn]
  obtain s0 := slots 0 (by omega_arith); have s5 := slots 5 (by omega_arith); have s6 := slots 6 (by omega_arith)
  obtain s8 := slots 8 (by omega_arith); have s9 := slots 9 (by omega_arith); have s1 := slots 1 (by omega_arith)
  obtain l0 : slot g.n64 0 + 8 * g.n64 ≤ slot g.n64 1 := sl 0
  obtain l5 : slot g.n64 5 + 8 * g.n64 ≤ slot g.n64 6 := sl 5
  obtain l6 : slot g.n64 6 + 8 * g.n64 ≤ slot g.n64 7 := sl 6
  obtain l8 : slot g.n64 8 + 8 * g.n64 ≤ slot g.n64 9 := sl 8
  obtain s7 := slots 7 (by omega_arith)
  obtain o15 : slot g.n64 1 ≤ slot g.n64 5 := by simp only [slot]; omega_arith
  obtain o18 : slot g.n64 1 ≤ slot g.n64 8 := by simp only [slot]; omega_arith
  obtain o68 : slot g.n64 6 ≤ slot g.n64 8 := by simp only [slot]; omega_arith
  obtain o56 : slot g.n64 5 ≤ slot g.n64 6 := by simp only [slot]; omega_arith
  obtain s00 : 64 ≤ slot g.n64 0 := by simp only [slot]; omega_arith
  simp only [Prog.chain]
  -- p, h and `(p − 1)/q` into the exponentiation's arrays.
  refine WP.seq (wp_movi fun s₁ u₁ => WP.block_nil ?_)
  obtain hs₁ : Scr s₁ E.base E.size := Scr.of_eq B.scr (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.wr
  refine WP.seq (VG.X86.WP.mono_syms (selectsW_ok hs₁ (src := aP) (tmp := aP) (o := slot g.n64 0) (n := g.n32) false
    (by rw [u₁.gpr]; rfl) (by omega_arith) (by simp only [aP, arr]; omega_arith) (by simp only [aP, arr]; omega_arith) (by omega_arith)
    (by right; left; simp only [aP, arr]; omega_arith) (by right; left; simp only [aP, arr]; omega_arith))
    fun s₂ ⟨O₂, V₂, K₂⟩ sy₂ => ?_)
  simp only [Bool.false_eq_true, ↓reduceIte] at V₂
  rw [u₁.mem, hP] at V₂
  obtain hs₂ := hs₁.of_keeps K₂ (by decide)
  obtain far : ∀ {m m' : Mem} {o k d n : Nat}, Outside E.base o k m m' → o + k ≤ 7168 → 9728 ≤ d →
      d + 4 * n ≤ E.size → val32 m' E.base d n = val32 m E.base d n := fun O h₁ h₂ h₃ =>
    O.val32 (by right; omega_arith) (by omega_arith)
  refine WP.seq (wp_movi fun s₃ u₃ => WP.block_nil ?_)
  obtain hs₃ : Scr s₃ E.base E.size := Scr.of_eq hs₂ (u₃.other _ (by decide)) (u₃.other _ (by decide)) u₃.wr
  refine WP.seq (VG.X86.WP.mono_syms (selectsW_ok hs₃ (src := aH) (tmp := aH) (o := slot g.n64 5) (n := g.n32) false
    (by rw [u₃.gpr]; rfl) (by omega_arith) (by simp only [aH, arr]; omega_arith) (by simp only [aH, arr]; omega_arith) (by omega_arith)
    (by right; left; simp only [aH, arr]; omega_arith) (by right; left; simp only [aH, arr]; omega_arith))
    fun s₄ ⟨O₄, V₄, K₄⟩ sy₄ => ?_)
  simp only [Bool.false_eq_true, ↓reduceIte] at V₄
  rw [u₃.mem, far O₂ (by omega_arith) (by simp only [aH, arr]; omega_arith) (by simp only [aH, arr]; omega_arith), u₁.mem, hH] at V₄
  obtain hs₄ := hs₃.of_keeps K₄ (by decide)
  refine WP.seq (wp_movi fun s₅ u₅ => WP.block_nil ?_)
  obtain hs₅ : Scr s₅ E.base E.size := Scr.of_eq hs₄ (u₅.other _ (by decide)) (u₅.other _ (by decide)) u₅.wr
  refine WP.seq (VG.X86.WP.mono_syms (selectsW_ok hs₅ (src := aE) (tmp := aE) (o := slot g.n64 8) (n := g.e) false
    (by rw [u₅.gpr]; rfl) (by omega_arith) (by simp only [aE, arr]; omega_arith) (by simp only [aE, arr]; omega_arith) (by omega_arith)
    (by right; left; simp only [aE, arr]; omega_arith) (by right; left; simp only [aE, arr]; omega_arith))
    fun s₆ ⟨O₆, V₆, K₆⟩ sy₆ => ?_)
  simp only [Bool.false_eq_true, ↓reduceIte] at V₆
  obtain xE : val32 s.mem E.base aE g.e = x :=
    val32_prefix (k := g.e) (r := g.n32 - g.e) (by rw [Nat.add_sub_cancel' he.2.2]; exact hE) hx
  rw [u₅.mem, far O₄ (by omega_arith) (by simp only [aE, arr]; omega_arith) (by simp only [aE, arr]; omega_arith), u₃.mem,
    far O₂ (by omega_arith) (by simp only [aE, arr]; omega_arith) (by simp only [aE, arr]; omega_arith), u₁.mem, xE] at V₆
  obtain hs₆ := hs₅.of_keeps K₆ (by decide)
  obtain sp₆ : s₆.gpr .esp = E.sp := by
    rw [K₆.1 _ (by decide), u₅.other _ (by decide), K₄.1 _ (by decide), u₃.other _ (by decide), K₂.1 _ (by decide),
      u₁.other _ (by decide), B.sp]
  obtain hv : wordsVal s₆.mem E.base (slot g.n64 0) g.n64 = p := by
    rw [wordsVal_eq_val32, h2, O₆.val32 (by left; omega_arith) (by omega_arith), u₅.mem, O₄.val32 (by left; omega_arith) (by omega_arith),
      u₃.mem, V₂]
  obtain w0 : (0, 7168) ∈ [(0, 7168), (aTmp, 400)] := by simp
  obtain C₂ := Env.Chg.of_outside v O₂ w0 (Nat.zero_le _) (by omega_arith) (by omega_arith)
  obtain C₄ := Env.Chg.of_outside v O₄ w0 (Nat.zero_le _) (by omega_arith) (by omega_arith)
  obtain C₆ := Env.Chg.of_outside v O₆ w0 (Nat.zero_le _) (by omega_arith) (by omega_arith)
  obtain C₆' : E.Chg [(0, 7168), (aTmp, 400)] s.mem s₆.mem :=
    (by rw [← u₁.mem]; exact C₂ : E.Chg [(0, 7168), (aTmp, 400)] s.mem s₂.mem).trans
      ((by rw [← u₃.mem]; exact C₄ : E.Chg [(0, 7168), (aTmp, 400)] s₂.mem s₄.mem).trans
      (by rw [← u₅.mem]; exact C₆ : E.Chg [(0, 7168), (aTmp, 400)] s₄.mem s₆.mem))
  obtain k₁ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s s₁ :=
    ⟨fun r hr => u₁.other r (fun e => hr (e ▸ by simp)), u₁.rd, u₁.wr⟩
  obtain k₃ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₂ s₃ :=
    ⟨fun r hr => u₃.other r (fun e => hr (e ▸ by simp)), u₃.rd, u₃.wr⟩
  obtain k₅ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₄ s₅ :=
    ⟨fun r hr => u₅.other r (fun e => hr (e ▸ by simp)), u₅.rd, u₅.wr⟩
  refine k s₆ ⟨hs₆, sp₆, hv, ?_, V₆, ?_, ?_, C₆', ?_, ?_⟩
  · rw [O₆.val32 (by left; omega_arith) (by omega_arith), u₅.mem, V₄]
  · rw [far O₆ (by omega_arith) (by simp only [aOne, arr]; omega_arith) (by simp only [aOne, arr]; omega_arith), u₅.mem,
      far O₄ (by omega_arith) (by simp only [aOne, arr]; omega_arith) (by simp only [aOne, arr]; omega_arith), u₃.mem,
      far O₂ (by omega_arith) (by simp only [aOne, arr]; omega_arith) (by simp only [aOne, arr]; omega_arith), u₁.mem, hone]
  · rw [Env.Chg.word v C₆' (by simp only [fG, hdr]; omega_arith) (fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> simp only [aTmp, arr, fG, hdr] <;> omega_arith), hF]
  · exact k₁.trans ((K₂.mono (by decide)).trans (k₃.trans ((K₄.mono (by decide)).trans (k₅.trans
      (K₆.mono (by decide))))))
  · rw [sy₆, u₅.syms, sy₄, u₃.syms, sy₂, u₁.syms]

/-- The exponentiation keeps `esp` and `edi`. -/
theorem gPowCall_regs {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s : State} {p h x F : Nat}
    (hp1 : 1 < p) (hodd : p % 2 = 1) {s₆ : State} (S : SelPost E g p h x F s s₆) :
    WP isa (VG.Impl.Dsa.X86.Pow.call g.n64 g.e) s₆ fun u => u.gpr .esp = s₆.gpr .esp ∧ u.gpr .edi = s₆.gpr .edi := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have n64 : g.n64 = g.pLen / 8 := rfl
  have n32 : g.n32 = g.pLen / 4 := rfl
  obtain h2 : 2 * g.n64 = g.n32 := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, n32, h]
  obtain h8 : 8 * g.n64 = g.pLen := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, h]
  obtain he : 1 < g.e ∧ g.e ≤ 2 * g.n64 ∧ g.e ≤ g.n32 := by
    rw [G.e, n64, n32]
    rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
  obtain slots : ∀ i, i ≤ 9 → slot g.n64 i ≤ 7048 := fun i hi => by
    simp only [slot, stride]; have := Nat.mul_le_mul hi (show 16 * g.n64 + 8 ≤ 776 by omega_arith); omega_arith
  obtain cb : contextBytes g.n64 ≤ 7048 := slots 9 (Nat.le_refl _)
  obtain sl : ∀ i, slot g.n64 i + 8 * g.n64 ≤ slot g.n64 (i + 1) := fun i => by
    simp only [slot, stride, Nat.succ_mul]; omega_arith
  have mod : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).modulus = slot g.n64 0 := rfl
  have bas : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).base = slot g.n64 5 := rfl
  have exn : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).exponent = slot g.n64 8 := rfl
  have res : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result = slot g.n64 6 := rfl
  obtain s0 := slots 0 (by omega_arith); have s5 := slots 5 (by omega_arith); have s6 := slots 6 (by omega_arith)
  obtain s8 := slots 8 (by omega_arith); have s9 := slots 9 (by omega_arith); have s1 := slots 1 (by omega_arith)
  obtain l0 : slot g.n64 0 + 8 * g.n64 ≤ slot g.n64 1 := sl 0
  obtain l5 : slot g.n64 5 + 8 * g.n64 ≤ slot g.n64 6 := sl 5
  obtain l6 : slot g.n64 6 + 8 * g.n64 ≤ slot g.n64 7 := sl 6
  obtain l8 : slot g.n64 8 + 8 * g.n64 ≤ slot g.n64 9 := sl 8
  obtain s7 := slots 7 (by omega_arith)
  obtain o15 : slot g.n64 1 ≤ slot g.n64 5 := by simp only [slot]; omega_arith
  obtain o18 : slot g.n64 1 ≤ slot g.n64 8 := by simp only [slot]; omega_arith
  obtain o68 : slot g.n64 6 ≤ slot g.n64 8 := by simp only [slot]; omega_arith
  obtain o56 : slot g.n64 5 ≤ slot g.n64 6 := by simp only [slot]; omega_arith
  obtain s00 : 64 ≤ slot g.n64 0 := by simp only [slot]; omega_arith
  have low := v.low
  have ss := v.stackScratch
  exact VG.X86.WP.mono_syms (VG.Proof.Dsa.X86.Pow.call_ok S.scr
    (by rw [S.sp]; exact ⟨by omega_arith, ss.elim (fun h => .inl h) (fun h => .inr (by omega_arith))⟩)
    (by omega_arith) (by simp only [VG.Impl.Dsa.Layout.usedBytes]; omega_arith) (by omega_arith) (by omega_arith) he.1 he.2.1 S.modv hp1 hodd)
    fun u ⟨_, _, K⟩ _ => ⟨K.1 _ (by decide), K.1 _ (by decide)⟩

/-- The exponentiation, and the check `g > 1` up to its branch. -/
theorem gPowCall_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s : State} (B : Base E s) {p h x F : Nat}
    (hp1 : 1 < p) (hodd : p % 2 = 1) {s₆ : State} (S : SelPost E g p h x F s s₆)
    {P : Prog isa} {Q : State → Prop} (k : ∀ t, PowMid E g (gVal h p x) F s t → WP isa P t Q) :
    WP isa (Prog.chain [VG.Impl.Dsa.X86.Pow.call g.n64 g.e,
      chainW .sbb g.n32 aTmp aOne (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result,
      .block [.alu .cmp .ecx (.imm 0)]] P) s₆ Q := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have n64 : g.n64 = g.pLen / 8 := rfl
  have n32 : g.n32 = g.pLen / 4 := rfl
  obtain h2 : 2 * g.n64 = g.n32 := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, n32, h]
  obtain h8 : 8 * g.n64 = g.pLen := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, h]
  obtain he : 1 < g.e ∧ g.e ≤ 2 * g.n64 ∧ g.e ≤ g.n32 := by
    rw [G.e, n64, n32]
    rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
  obtain slots : ∀ i, i ≤ 9 → slot g.n64 i ≤ 7048 := fun i hi => by
    simp only [slot, stride]; have := Nat.mul_le_mul hi (show 16 * g.n64 + 8 ≤ 776 by omega_arith); omega_arith
  obtain cb : contextBytes g.n64 ≤ 7048 := slots 9 (Nat.le_refl _)
  obtain sl : ∀ i, slot g.n64 i + 8 * g.n64 ≤ slot g.n64 (i + 1) := fun i => by
    simp only [slot, stride, Nat.succ_mul]; omega_arith
  have mod : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).modulus = slot g.n64 0 := rfl
  have bas : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).base = slot g.n64 5 := rfl
  have exn : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).exponent = slot g.n64 8 := rfl
  have res : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result = slot g.n64 6 := rfl
  rw [res]
  obtain s0 := slots 0 (by omega_arith); have s5 := slots 5 (by omega_arith); have s6 := slots 6 (by omega_arith)
  obtain s8 := slots 8 (by omega_arith); have s9 := slots 9 (by omega_arith); have s1 := slots 1 (by omega_arith)
  obtain l0 : slot g.n64 0 + 8 * g.n64 ≤ slot g.n64 1 := sl 0
  obtain l5 : slot g.n64 5 + 8 * g.n64 ≤ slot g.n64 6 := sl 5
  obtain l6 : slot g.n64 6 + 8 * g.n64 ≤ slot g.n64 7 := sl 6
  obtain l8 : slot g.n64 8 + 8 * g.n64 ≤ slot g.n64 9 := sl 8
  obtain s7 := slots 7 (by omega_arith)
  obtain o15 : slot g.n64 1 ≤ slot g.n64 5 := by simp only [slot]; omega_arith
  obtain o18 : slot g.n64 1 ≤ slot g.n64 8 := by simp only [slot]; omega_arith
  obtain o68 : slot g.n64 6 ≤ slot g.n64 8 := by simp only [slot]; omega_arith
  obtain o56 : slot g.n64 5 ≤ slot g.n64 6 := by simp only [slot]; omega_arith
  obtain s00 : 64 ≤ slot g.n64 0 := by simp only [slot]; omega_arith
  simp only [Prog.chain]
  -- The exponentiation.
  have sp₆ := S.sp
  have hs₆ := S.scr
  have low := v.low
  have ss := v.stackScratch
  have hv := S.modv
  refine WP.seq (VG.X86.WP.mono_syms (VG.Proof.Dsa.X86.Pow.call_ok hs₆
    (by rw [sp₆]; exact ⟨by omega_arith, ss.elim (fun h => .inl h) (fun h => .inr (by omega_arith))⟩)
    (by omega_arith) (by simp only [VG.Impl.Dsa.Layout.usedBytes]; omega_arith) (by omega_arith) (by omega_arith) he.1 he.2.1 hv hp1 hodd)
    fun s₇ ⟨V₇, SO₇, K₇⟩ sy₇ => ?_)
  rw [wordsVal_eq_val32, wordsVal_eq_val32, h2, S.basev, S.expv] at V₇
  obtain hs₇ := hs₆.of_keeps K₇ (by decide)
  obtain one₇ : val32 s₇.mem E.base aOne g.n32 = 1 := by
    rw [SO₇.val32 (fun r hr => by
        simp only [VG.Impl.Dsa.X86.Pow.scratch, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only [aOne, arr, contextBytes] at cb ⊢ <;> omega_arith)
        (by simp only [aOne, arr, VG.Impl.Dsa.Layout.usedBytes]; omega_arith), S.one]
  -- `g > 1`.
  refine WP.seq (VG.X86.WP.mono_syms (chainSubW_ok hs₇ (k := g.n32) (o := aTmp) (a := aOne) (b := slot g.n64 6)
    (by omega_arith) (by simp only [aTmp, arr]; omega_arith) (by simp only [aOne, arr]; omega_arith) (by omega_arith)
    (by simp only [aTmp, aOne, arr]; omega_arith) (by right; simp only [aTmp, arr]; omega_arith))
    fun s₈ ⟨O₈, ⟨c₈, e₈, E₈⟩, K₈⟩ sy₈ => ?_)
  rw [one₇, V₇] at E₈
  obtain c₈v := borrow_lt E₈ (val32_lt _ _ _ _)
  obtain hs₈ := hs₇.of_keeps K₈ (by decide)
  refine WP.seq (wp_cmpi fun s₉ f₉ _ z₉ => WP.block_nil ?_)
  obtain zf₉ : isa.eval .e s₉ = some (!decide (1 < gVal h p x)) := by
    show s₉.zf = _
    rw [z₉, e₈, cmask_zf, c₈v]; rfl
  obtain hs₉ : Scr s₉ E.base E.size := Scr.of_eq hs₈ (by rw [f₉.gpr]) (by rw [f₉.gpr]) f₉.wr
  -- What changed.
  obtain Aw := wRanges_apart G v
  obtain w0 : (0, 7168) ∈ [(0, 7168), (aTmp, 400)] := by simp
  obtain C₇ : E.Chg [(0, 7168), (aTmp, 400)] s₆.mem s₇.mem := by
    rw [sp₆] at SO₇
    refine (Env.Chg.of_stackOuts v SO₇ fun r hr => ?_).widen fun r hr => ⟨(0, 7168), w0, Nat.zero_le _, ?_⟩
    · simp only [VG.Impl.Dsa.X86.Pow.scratch, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [contextBytes] at cb ⊢ <;> omega_arith
    · simp only [VG.Impl.Dsa.X86.Pow.scratch, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [contextBytes] at cb ⊢ <;> omega_arith
  obtain C₈ := Env.Chg.of_outside v O₈ (os := [(0, 7168), (aTmp, 400)]) (o' := aTmp) (n' := 400) (by simp)
    (Nat.le_refl _) (by simp only [aTmp, arr]; omega_arith) (by simp only [aTmp, arr]; omega_arith)
  obtain C₉' : E.Chg [(0, 7168), (aTmp, 400)] s.mem s₉.mem := by
    rw [f₉.mem]
    exact S.chg.trans (C₇.trans C₈)
  obtain C₉ : E.Chg (wRanges g) s.mem s₉.mem := C₉'.widen fun o ho => ⟨o, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> simp [wRanges], Nat.le_refl _, Nat.le_refl _⟩
  obtain k₉ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₈ s₉ := ⟨fun r _ => by rw [f₉.gpr], f₉.rd, f₉.wr⟩
  obtain K₉ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s s₉ :=
    S.keeps.trans ((K₇.mono (by decide)).trans ((K₈.mono (by decide)).trans k₉))
  obtain sy₉ : s₉.syms = s.syms := by
    rw [f₉.syms, sy₈, sy₇, S.syms]
  obtain B₉ : Base E s₉ := B.keep v C₉ Aw (K₉.1 _ (by decide)) (K₉.1 _ (by decide)) K₉.2.1 K₉.2.2 sy₉
  obtain g₉ : val32 s₉.mem E.base (slot g.n64 6) g.n32 = gVal h p x := by
    rw [f₉.mem, O₈.val32 (by left; simp only [aTmp, arr]; omega_arith) (by omega_arith), V₇]; rfl
  obtain fG₉ : s₉.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F := by
    rw [Env.Chg.word v (by rw [f₉.mem]; exact C₇.trans C₈ : E.Chg [(0, 7168), (aTmp, 400)] s₆.mem s₉.mem) (by simp only [fG, hdr]; omega_arith) (fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> simp only [aTmp, arr, fG, hdr] <;> omega_arith), S.fg]
  exact k s₉ ⟨B₉, zf₉, g₉, fG₉, C₉, K₉, sy₉⟩

/-- `g` from `h`, `p` and `(p − 1)/q` in their arrays, up to the check `g > 1`. -/
theorem gPowMid_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s : State} (B : Base E s) {p h x F : Nat}
    (hP : val32 s.mem E.base aP g.n32 = p) (hH : val32 s.mem E.base aH g.n32 = h)
    (hE : val32 s.mem E.base aE g.n32 = x) (hx : x < 2 ^ (32 * g.e)) (hone : val32 s.mem E.base aOne g.n32 = 1)
    (hp1 : 1 < p) (hodd : p % 2 = 1)
    (hF : s.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F)
    {P : Prog isa} {Q : State → Prop} (k : ∀ t, PowMid E g (gVal h p x) F s t → WP isa P t Q) :
    WP isa (Prog.chain [.block [.mov .ecx (.imm 0)],
      selectsW g.n32 aP aP (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).modulus,
      .block [.mov .ecx (.imm 0)], selectsW g.n32 aH aH (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).base,
      .block [.mov .ecx (.imm 0)], selectsW g.e aE aE (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).exponent,
      VG.Impl.Dsa.X86.Pow.call g.n64 g.e,
      chainW .sbb g.n32 aTmp aOne (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result,
      .block [.alu .cmp .ecx (.imm 0)]] P) s Q :=
  gPowSel_ok G v B hP hH hE hx hone hF fun _ S => gPowCall_ok G v B hp1 hodd S k

/-- `g` from `h`, `p` and `(p − 1)/q` in their arrays. -/
theorem gPow_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s : State} (B : Base E s) {p h x F : Nat}
    (hP : val32 s.mem E.base aP g.n32 = p) (hH : val32 s.mem E.base aH g.n32 = h)
    (hE : val32 s.mem E.base aE g.n32 = x) (hx : x < 2 ^ (32 * g.e)) (hone : val32 s.mem E.base aOne g.n32 = 1)
    (hp1 : 1 < p) (hodd : p % 2 = 1) (hplt : p < 2 ^ (8 * g.pLen))
    (hF : s.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F) :
    WP isa (seqs [.block [.mov .ecx (.imm 0)],
      selectsW g.n32 aP aP (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).modulus,
      .block [.mov .ecx (.imm 0)], selectsW g.n32 aH aH (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).base,
      .block [.mov .ecx (.imm 0)], selectsW g.e aE aE (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).exponent,
      VG.Impl.Dsa.X86.Pow.call g.n64 g.e,
      chainW .sbb g.n32 aTmp aOne (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result,
      .block [.alu .cmp .ecx (.imm 0)],
      .ite .e (.block [])
        (seqs [storeS (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result (sPk + g.pLen + g.qLen) g.pLen,
          .block (stImm fG 1)])]) s (PowPost E g (gVal h p x) F s) := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have n64 : g.n64 = g.pLen / 8 := rfl
  have n32 : g.n32 = g.pLen / 4 := rfl
  obtain h2 : 2 * g.n64 = g.n32 := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, n32, h]
  obtain h8 : 8 * g.n64 = g.pLen := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, h]
  obtain he : 1 < g.e ∧ g.e ≤ 2 * g.n64 ∧ g.e ≤ g.n32 := by
    rw [G.e, n64, n32]
    rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
  obtain slots : ∀ i, i ≤ 9 → slot g.n64 i ≤ 7048 := fun i hi => by
    simp only [slot, stride]; have := Nat.mul_le_mul hi (show 16 * g.n64 + 8 ≤ 776 by omega_arith); omega_arith
  obtain cb : contextBytes g.n64 ≤ 7048 := slots 9 (Nat.le_refl _)
  obtain sl : ∀ i, slot g.n64 i + 8 * g.n64 ≤ slot g.n64 (i + 1) := fun i => by
    simp only [slot, stride, Nat.succ_mul]; omega_arith
  have mod : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).modulus = slot g.n64 0 := rfl
  have bas : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).base = slot g.n64 5 := rfl
  have exn : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).exponent = slot g.n64 8 := rfl
  have res : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result = slot g.n64 6 := rfl
  rw [mod, bas, exn, res]
  obtain s0 := slots 0 (by omega_arith); have s5 := slots 5 (by omega_arith); have s6 := slots 6 (by omega_arith)
  obtain s8 := slots 8 (by omega_arith); have s9 := slots 9 (by omega_arith); have s1 := slots 1 (by omega_arith)
  obtain l0 : slot g.n64 0 + 8 * g.n64 ≤ slot g.n64 1 := sl 0
  obtain l5 : slot g.n64 5 + 8 * g.n64 ≤ slot g.n64 6 := sl 5
  obtain l6 : slot g.n64 6 + 8 * g.n64 ≤ slot g.n64 7 := sl 6
  obtain l8 : slot g.n64 8 + 8 * g.n64 ≤ slot g.n64 9 := sl 8
  obtain s7 := slots 7 (by omega_arith)
  obtain o15 : slot g.n64 1 ≤ slot g.n64 5 := by simp only [slot]; omega_arith
  obtain o18 : slot g.n64 1 ≤ slot g.n64 8 := by simp only [slot]; omega_arith
  obtain o68 : slot g.n64 6 ≤ slot g.n64 8 := by simp only [slot]; omega_arith
  obtain o56 : slot g.n64 5 ≤ slot g.n64 6 := by simp only [slot]; omega_arith
  obtain s00 : 64 ≤ slot g.n64 0 := by simp only [slot]; omega_arith
  refine gPowMid_ok (P := .ite .e _ _) G v B hP hH hE hx hone hp1 hodd hF fun s₉ M => ?_
  have hs₉ : Scr s₉ E.base E.size := M.base.scr
  obtain Aw := wRanges_apart G v
  obtain B₉ := M.base; have zf₉ := M.zf; have g₉ := M.res; have fG₉ := M.fg; have C₉ := M.chg
  obtain K₉ := M.keeps; have sy₉ := M.syms
  refine WP.ite _ zf₉ (fun hz => WP.block_nil ⟨B₉, ?_, ?_, C₉, K₉.2.1, K₉.2.2, sy₉⟩) (fun hz => ?_)
  · have : ¬ 1 < gVal h p x := by simpa using hz
    simp only [this, ↓reduceIte]; exact fG₉
  · intro hg; have : ¬ 1 < gVal h p x := by simpa using hz
    exact absurd hg this
  obtain hg : 1 < gVal h p x := by simpa using hz
  obtain glt : gVal h p x < 2 ^ (8 * g.pLen) := by
    have := Nat.mod_lt (h ^ x) (show 0 < p by omega_arith); unfold gVal; omega_arith
  refine WP.seq (VG.X86.WP.mono_syms (storeS_ok hs₉ (o := slot g.n64 6) (dst := sPk + g.pLen + g.qLen)
    (len := g.pLen) (n := g.n64) (by omega_arith) (by omega_arith) (by omega_arith) (by simp only [sPk]; omega_arith)
    (by left; simp only [sPk]; omega_arith) (by rw [h2, g₉]; exact glt)) fun s₁₀ ⟨G₁₀, F₁₀, K₁₀⟩ sy₁₀ => ?_)
  rw [h2, g₉] at G₁₀
  obtain hs₁₀ := hs₉.of_keeps K₁₀ (by decide)
  refine stImm_end hs₁₀ (o := fG) (v := 1) (by simp only [fG, hdr]; omega_arith) fun s₁₁ g₁₁ m₁₁ rd₁₁ wr₁₁ sy₁₁ => ?_
  obtain pk : (sPk + g.pLen + g.qLen, g.pLen) ∈ wRanges g := by simp [wRanges]
  obtain fg : (fG, 4) ∈ wRanges g := by simp [wRanges]
  obtain C₁₀ : E.Chg (wRanges g) s.mem s₁₀.mem := C₉.trans (Env.Chg.of_frame F₁₀ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Env.in_range pk (Nat.le_refl _) (Nat.le_refl _))
  obtain C₁₁ : E.Chg (wRanges g) s.mem s₁₁.mem := by
    rw [m₁₁]; exact C₁₀.store fg (by decide) _
  obtain K₁₁ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s s₁₁ :=
    K₉.trans ((K₁₀.mono (by decide)).trans ⟨fun r hr => g₁₁ r (fun e => hr (e ▸ by simp)), rd₁₁, wr₁₁⟩)
  obtain sy : s₁₁.syms = s.syms := by rw [sy₁₁, sy₁₀, sy₉]
  refine ⟨B.keep v C₁₁ Aw (K₁₁.1 _ (by decide)) (K₁₁.1 _ (by decide)) K₁₁.2.1 K₁₁.2.2 sy, ?_, fun _ => ?_, C₁₁,
    K₁₁.2.1, K₁₁.2.2, sy⟩
  · rw [m₁₁, Mem.readW_writeW_self32]; simp only [hg, ↓reduceIte]
  · rw [m₁₁, Env.Chg.scratch v ((Env.Chg.refl [(fG, 4)] s₁₀.mem).store (List.mem_singleton_self _) (by decide) _)
      (by simp only [sPk]; omega_arith) (fun o ho => by
        simp only [List.mem_singleton] at ho; subst ho; simp only [fG, sPk, hdr]; omega_arith), G₁₀]

end VG.Proof.Dsa.X86.Generation

end

end


/-! # The generator: the `h` of the window in turn (A.2.1) -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- That `h` gives a generator: in range, and its `g` above 1. -/
def Found (h p x : Nat) : Prop := 1 < h ∧ h < p - 1 ∧ 1 < gVal h p x

instance (h p x : Nat) : Decidable (Found h p x) := by unfold Found; infer_instance

/-- After one `h`. -/
structure GStepPost (E : Env) (g : Geo) (j p x F : Nat) (s t : State) : Prop where
  base : Base E t
  fg : t.mem.readW (off E.base fG) 32 =
    BitVec.ofNat 32 (if Found (Spec.Dsa.decodeBE (hChunk E j)) p x then 1 else F)
  gb : Found (Spec.Dsa.decodeBE (hChunk E j)) p x → Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen + g.qLen))
    g.pLen = Spec.Dsa.encodeBE g.pLen (gVal (Spec.Dsa.decodeBE (hChunk E j)) p x)
  chg : E.Chg (rRanges ++ wRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

/-- What the range check of `h` keeps: the arrays the exponentiation reads, and `fG`. -/
theorem range_keeps {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s t : State} {j p x F : Nat}
    (R : RangePost E g j p s t) (hone : val32 s.mem E.base aOne g.n32 = 1)
    (hP : val32 s.mem E.base aP g.n32 = p) (hE : val32 s.mem E.base aE g.n32 = x)
    (hF : s.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F) :
    val32 t.mem E.base aP g.n32 = p ∧ val32 t.mem E.base aE g.n32 = x ∧ val32 t.mem E.base aOne g.n32 = 1 ∧
      t.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F := by
  have sz := v.size_ge
  have bd := G.bounds
  have n32 : g.n32 = g.pLen / 4 := rfl
  obtain nle : g.n32 ≤ 96 := by omega_using [bd, n32]
  obtain rA := rRanges_apart v
  obtain keepR : ∀ {d : Nat}, 9728 + 400 * 10 ≤ d ∨ d + 4 * g.n32 ≤ 9728 + 400 * 8 → d + 4 * g.n32 ≤ E.size →
      fLo + 4 ≤ d ∨ d + 4 * g.n32 ≤ fLo →
      val32 t.mem E.base d g.n32 = val32 s.mem E.base d g.n32 := fun h₁ h₂ h₃ =>
    Env.Chg.val32 v R.chg h₂ fun o ho => ⟨(rA o ho).1, by
      simp only [rRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp only [aTmp, aH, arr, fLo, hdr] at h₃ ⊢ <;> omega_arith⟩
  obtain fGR : t.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F := by
    rw [Env.Chg.word v R.chg (by simp only [fG, hdr]; omega_using [sz]) (fun o ho => ⟨(rA o ho).1, by
      simp only [rRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp only [aTmp, aH, arr, fLo, fG, hdr] <;> omega_using []⟩), hF]
  exact ⟨by rw [keepR (by simp only [aP, arr]; omega_using []) (by simp only [aP, arr]; omega_using [sz, nle])
      (by left; simp only [aP, arr, fLo, hdr]; omega_using []), hP],
    by rw [keepR (by simp only [aE, arr]; omega_using [nle]) (by simp only [aE, arr]; omega_using [sz, nle])
      (by left; simp only [aE, arr, fLo, hdr]; omega_using []), hE],
    by rw [keepR (by simp only [aOne, arr]; omega_using [nle]) (by simp only [aOne, arr]; omega_using [sz, nle])
      (by left; simp only [aOne, arr, fLo, hdr]; omega_using []), hone], fGR⟩

theorem gStep_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) {s : State} (B : Base E s)
    {j p x F : Nat} (hj : (j + 1) * E.pLen ≤ E.hsLen)
    (hH : s.mem.readW (off E.base fH) 32 = (E.hs + BitVec.ofNat 64 (j * E.pLen)).setWidth 32)
    (hone : val32 s.mem E.base aOne g.n32 = 1) (hpm1 : val32 s.mem E.base aPm1 g.n32 = p - 1)
    (hP : val32 s.mem E.base aP g.n32 = p) (hE : val32 s.mem E.base aE g.n32 = x) (hx : x < 2 ^ (32 * g.e))
    (hp1 : 1 < p) (hodd : p % 2 = 1) (hplt : p < 2 ^ (8 * g.pLen))
    (hF : s.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F) :
    WP isa g.gStep s (GStepPost E g j p x F s) := by
  have sz := v.size_ge
  have bd := G.bounds
  unfold Geo.gStep
  refine gRange_ok G v hp B hj hH hone hpm1 (P := .ite .e (.block []) _) fun t R => ?_
  obtain ⟨kP, kE, kOne, fGR⟩ := range_keeps G v R hone hP hE hF
  obtain widenR : E.Chg (rRanges ++ wRanges g) s.mem t.mem :=
    R.chg.widen fun o ho => ⟨o, List.mem_append_left _ ho, Nat.le_refl _, Nat.le_refl _⟩
  refine WP.ite _ R.zf (fun hz => WP.block_nil ?_) (fun hz => ?_)
  · -- Out of range.
    obtain hn : ¬ Found (Spec.Dsa.decodeBE (hChunk E j)) p x := fun ⟨a, b, _⟩ => by
      simp only [a, b, and_self, decide_true, Bool.not_true, Bool.false_eq_true] at hz
    exact ⟨R.base, by rw [fGR]; simp only [hn, ↓reduceIte], fun h => absurd h hn, widenR, R.rd, R.wr, R.syms⟩
  · -- In range: `g`.
    obtain hin : 1 < Spec.Dsa.decodeBE (hChunk E j) ∧ Spec.Dsa.decodeBE (hChunk E j) < p - 1 := by
      simpa using hz
    refine WP.mono (gPow_ok G v R.base (p := p) (h := Spec.Dsa.decodeBE (hChunk E j)) (x := x) (F := F)
      kP R.h kE hx kOne hp1 hodd hplt fGR) fun t' P => ?_
    obtain iff : Found (Spec.Dsa.decodeBE (hChunk E j)) p x ↔ 1 < gVal (Spec.Dsa.decodeBE (hChunk E j)) p x :=
      ⟨fun h => h.2.2, fun h => ⟨hin.1, hin.2, h⟩⟩
    refine ⟨P.base, by rw [P.fg]; simp only [iff], fun h => P.gb (iff.mp h),
      widenR.trans (P.chg.widen fun o ho => ⟨o, List.mem_append_right _ ho, Nat.le_refl _, Nat.le_refl _⟩),
      by rw [P.rd, R.rd], by rw [P.wr, R.wr], by rw [P.syms, R.syms]⟩

/-- The `h` candidates of the tape. -/
def hList (E : Env) : List Nat := (Spec.Dsa.generationChunks E.pLen E.hT).map Spec.Dsa.decodeBE

theorem hList_length (E : Env) : (hList E).length = E.hT.length / E.pLen := by
  simp [hList, Spec.Dsa.generationChunks]

theorem hList_drop (E : Env) {j : Nat} (hj : j < E.hT.length / E.pLen) :
    (hList E).drop j = Spec.Dsa.decodeBE (hChunk E j) :: (hList E).drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [hList_length]; exact hj)]
  simp [hList, Spec.Dsa.generationChunks, hChunk]

/-- The ranges the generator changes. -/
def gRanges (g : Geo) : List (Nat × Nat) := rRanges ++ wRanges g ++ [(fH, 4), (fHLeft, 4)]

theorem gRanges_apart {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) : E.Apart (gRanges g) := by
  have sz := v.size_ge
  intro o ho
  rcases List.mem_append.mp ho with h | h
  · rcases List.mem_append.mp h with h | h
    · exact rRanges_apart v o h
    · exact wRanges_apart G v o h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp only [fH, fHLeft, fOut, fWitLen, hdr] <;> omega_using [sz]

/-- What the generator keeps. -/
structure GKeep (E : Env) (g : Geo) (s t : State) : Prop where
  base : Base E t
  chg : E.Chg (gRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

/-- The generator's result in memory `m`. -/
def GRes (E : Env) (g : Geo) (m : Mem) : Option Nat → Prop
  | none => m.readW (off E.base fG) 32 = BitVec.ofNat 32 2
  | some gv => m.readW (off E.base fG) 32 = BitVec.ofNat 32 1 ∧
      Spec.Rsa.bytesAt m (off E.base (sPk + g.pLen + g.qLen)) g.pLen = Spec.Dsa.encodeBE g.pLen gv

theorem GKeep.mem {E : Env} {g : Geo} {s t t' : State} (K : GKeep E g s t) (hm : t'.mem = t.mem)
    (edi : t'.gpr .edi = t.gpr .edi) (sp : t'.gpr .esp = t.gpr .esp) (rd : t'.rd = t.rd) (wr : t'.wr = t.wr)
    (sy : t'.syms = t.syms) : GKeep E g s t' :=
  ⟨K.base.regs hm edi sp rd wr sy, by rw [hm]; exact K.chg, by rw [rd, K.rd], by rw [wr, K.wr], by rw [sy, K.syms]⟩

theorem GKeep.store {E : Env} {g : Geo} {s t t' : State} (K : GKeep E g s t) (G : GeoOk g) (v : E.Valid) {d : Nat}
    (hd : (d, 4) ∈ gRanges g) (x : BitVec 32) (hm : t'.mem = t.mem.writeW (off E.base d) x)
    (edi : t'.gpr .edi = t.gpr .edi) (sp : t'.gpr .esp = t.gpr .esp) (rd : t'.rd = t.rd) (wr : t'.wr = t.wr)
    (sy : t'.syms = t.syms) : GKeep E g s t' := by
  obtain C : E.Chg [(d, 4)] t.mem t'.mem := by
    rw [hm]; exact (Env.Chg.refl _ _).store (List.mem_singleton_self _) (by decide) x
  exact ⟨K.base.keep v C (fun o ho => gRanges_apart G v o (by simp only [List.mem_singleton] at ho; rw [ho]; exact hd))
    edi sp rd wr sy, K.chg.trans (C.widen fun o ho => ⟨o, by simp only [List.mem_singleton] at ho; rw [ho]; exact hd,
      Nat.le_refl _, Nat.le_refl _⟩), by rw [rd, K.rd], by rw [wr, K.wr], by rw [sy, K.syms]⟩

/-- A pointer into a tape, moved on. -/
theorem ptr_add (x : BitVec 64) (c : Nat) :
    x.setWidth 32 + BitVec.ofNat 32 c = (x + BitVec.ofNat 64 c).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)]
  omega_using []

/-- At the loop's head, before `h` number `j`. -/
structure GLoop (E : Env) (g : Geo) (p Q : Nat) (Rg : Option Nat) (s : State) (j : Nat) (t : State) : Prop where
  keep : GKeep E g s t
  fh : t.mem.readW (off E.base fH) 32 = (E.hs + BitVec.ofNat 64 (j * E.pLen)).setWidth 32
  left : t.mem.readW (off E.base fHLeft) 32 = BitVec.ofNat 32 (E.hsLen - j * E.pLen)
  fg : t.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 4
  hj : j * E.pLen ≤ E.hsLen
  spec : Spec.Dsa.generator p Q ((hList E).drop j) = Rg
  count : VG.Proof.Dsa.Generation.generatorCount p Q (hList E) =
    j + VG.Proof.Dsa.Generation.generatorCount p Q ((hList E).drop j)

/-- The arrays outside the generator's working space are as they were. -/
theorem gkeep_arrs {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s t : State} (K : GKeep E g s t) {d : Nat}
    (h₀ : 9728 ≤ d) (h₁ : d + 4 * g.n32 ≤ 9728 + 400 * 8 ∨ 9728 + 400 * 10 ≤ d) (h₂ : d + 4 * g.n32 ≤ E.size) :
    val32 t.mem E.base d g.n32 = val32 s.mem E.base d g.n32 := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have n32 : g.n32 = g.pLen / 4 := rfl
  obtain gA := gRanges_apart G v
  exact Env.Chg.val32 v K.chg h₂ fun o ho => ⟨(gA o ho).1, by
      simp only [gRanges, rRanges, wRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [aTmp, aH, arr, fLo, sPk, fG, fH, fHLeft, hdr] at h₀ h₁ h₂ ⊢ <;> omega_arith⟩

/-- Whether the loop goes on after `h` number `j`. -/
def gCont (E : Env) (p x j : Nat) : Bool :=
  decide (¬ E.hsLen - j * E.pLen < E.pLen ∧ ¬ Found (Spec.Dsa.decodeBE (hChunk E j)) p x)

/-- Where the search for g leaves `fH`: after the candidates it read. -/
def hEnd (E : Env) (p Q : Nat) : BitVec 32 :=
  (E.hs + BitVec.ofNat 64 (E.pLen * VG.Proof.Dsa.Generation.generatorCount p Q (hList E))).setWidth 32

theorem hit_found {p Q x h : Nat} (hx' : x = (p - 1) / Q) :
    VG.Proof.Dsa.Generation.generatorHit p Q h = decide (Found h p x) := by
  subst hx'
  unfold VG.Proof.Dsa.Generation.generatorHit Found gVal
  rw [VG.Proof.Dsa.powMod_eq]
  by_cases a : 1 < h <;> by_cases b : h < p - 1 <;> by_cases c : 1 < h ^ ((p - 1) / Q) % p <;> simp [a, b, c]

/-- One `h`: the loop exits with the generator's result, or goes on. -/
theorem gBody_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) {p Q x : Nat}
    {Rg : Option Nat} {s : State} (hx' : x = (p - 1) / Q)
    (hone : val32 s.mem E.base aOne g.n32 = 1) (hpm1 : val32 s.mem E.base aPm1 g.n32 = p - 1)
    (hP : val32 s.mem E.base aP g.n32 = p) (hE : val32 s.mem E.base aE g.n32 = x) (hxl : x < 2 ^ (32 * g.e))
    (hp1 : 1 < p) (hodd : p % 2 = 1) (hplt : p < 2 ^ (8 * g.pLen)) {j : Nat} {t : State}
    (L : GLoop E g p Q Rg s j t) :
    WP isa (seqs [.block (cmpF fHLeft g.pLen),
      .ite .b (.block (stImm fG 2))
        (seqs [g.gStep, .block [.mov .eax (.mem (sc fH)), .alu .add .eax (.imm (BitVec.ofNat 32 g.pLen)),
          .store (sc fH) .eax, .mov .eax (.mem (sc fHLeft)), .alu .sub .eax (.imm (BitVec.ofNat 32 g.pLen)),
          .store (sc fHLeft) .eax]]),
      .block (cmpF fG 4)]) t fun t' =>
      (t'.zf = some false ∧ gCont E p x j = false ∧ GKeep E g s t' ∧ GRes E g t'.mem Rg ∧
        t'.mem.readW (off E.base fH) 32 = hEnd E p Q) ∨
      (t'.zf = some true ∧ gCont E p x j = true ∧ (j + 1) * E.pLen ≤ E.hsLen ∧ GLoop E g p Q Rg s (j + 1) t') := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  obtain hl : E.hT.length = E.hsLen := by rw [← L.keep.base.hs v, VG.Proof.Bignum.bytesAt_length]
  have lens := v.witLen32
  obtain hsl : E.hsLen < 2 ^ 32 := by have := v.hsIn; omega_arith
  have pl := v.pLen_ge
  obtain gA := gRanges_apart G v
  obtain arrK : ∀ {d : Nat}, 9728 ≤ d → d + 4 * g.n32 ≤ 9728 + 400 * 8 ∨ 9728 + 400 * 10 ≤ d →
      d + 4 * g.n32 ≤ E.size → val32 t.mem E.base d g.n32 = val32 s.mem E.base d g.n32 := fun h₀ h₁ h₂ =>
    gkeep_arrs G v L.keep h₀ h₁ h₂
  have n32 : g.n32 = g.pLen / 4 := rfl
  simp only [seqs]
  refine WP.seq (cmpFb_end L.keep.base.scr (o := fHLeft) (v := g.pLen) (by simp only [fHLeft, hdr]; omega_arith) L.left
    (by omega_arith) (by omega_arith) fun t₁ g₁ m₁ rd₁ wr₁ sy₁ z₁ => ?_)
  obtain K₁ := L.keep.mem m₁ (g₁ _ (by decide)) (g₁ _ (by decide)) rd₁ wr₁ sy₁
  refine WP.seq (WP.ite _ z₁ (fun hz => stImm_end K₁.base.scr (o := fG) (v := 2) (by simp only [fG, hdr]; omega_arith)
    fun t₂ g₂ m₂ rd₂ wr₂ sy₂ => ?_) (fun hz => ?_))
  · -- No `h` left.
    obtain h0 : E.hsLen - j * E.pLen < E.pLen := by have h := of_decide_eq_true hz; rwa [← hp] at h
    obtain K₂ := K₁.store G v (d := fG) (by simp [gRanges, wRanges]) _ m₂ (g₂ _ (by decide)) (g₂ _ (by decide)) rd₂ wr₂
      sy₂
    refine cmpF_end K₂.base.scr (o := fG) (v := 4) (w := 2) (by simp only [fG, hdr]; omega_arith)
      (by rw [m₂, Mem.readW_writeW_self32]) (by decide) (by decide) fun t₃ g₃ m₃ rd₃ wr₃ sy₃ z₃ => ?_
    obtain hN : E.hT.length / E.pLen ≤ j := by
      rw [hl]
      have := (Nat.div_lt_iff_lt_mul (k := E.pLen) (by omega_arith)).mpr
        (show E.hsLen < (j + 1) * E.pLen by rw [Nat.succ_mul]; omega_arith)
      omega_arith
    obtain hD : (hList E).drop j = [] := List.drop_eq_nil_of_le (by rw [hList_length]; exact hN)
    refine .inl ⟨z₃, by simp [gCont, h0], K₂.mem m₃ (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃ sy₃, ?_, ?_⟩
    · have hR : Rg = none := by
        rw [← L.spec, hD]
        rfl
      rw [hR]; show _ = _; rw [m₃, m₂, Mem.readW_writeW_self32]
    · rw [m₃, m₂, word_store_other v _ (by simp only [fH, hdr]; omega_arith) (by simp only [fG, hdr]; omega_arith)
        (by simp only [fH, fG, hdr]; omega_arith), m₁, L.fh, hEnd, L.count, hD]
      simp only [VG.Proof.Dsa.Generation.generatorCount, Nat.add_zero, Nat.mul_comm]
  · -- `h` number `j`.
    obtain hne : ¬ E.hsLen - j * E.pLen < E.pLen := by have h := of_decide_eq_false hz; rwa [← hp] at h
    obtain hj1 : (j + 1) * E.pLen ≤ E.hsLen := by rw [Nat.succ_mul]; omega_arith
    obtain hjN : j < E.hT.length / E.pLen := by
      rw [hl]; exact (Nat.le_div_iff_mul_le (by omega_arith)).mpr hj1
    refine WP.seq (WP.mono (gStep_ok G v hp K₁.base (j := j) (p := p) (x := x) (F := 4) hj1
      (by rw [m₁]; exact L.fh)
      (by rw [m₁, arrK (by simp only [aOne, arr]; omega_arith) (by simp only [aOne, arr]; omega_arith) (by simp only [aOne, arr]; omega_arith),
        hone])
      (by rw [m₁, arrK (by simp only [aPm1, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith),
        hpm1])
      (by rw [m₁, arrK (by simp only [aP, arr]; omega_arith) (by simp only [aP, arr]; omega_arith) (by simp only [aP, arr]; omega_arith), hP])
      (by rw [m₁, arrK (by simp only [aE, arr]; omega_arith) (by simp only [aE, arr]; omega_arith) (by simp only [aE, arr]; omega_arith), hE])
      hxl hp1 hodd hplt (by rw [m₁]; exact L.fg)) fun t₂ S => ?_)
    obtain K₂ : GKeep E g s t₂ := ⟨S.base, K₁.chg.trans (S.chg.widen fun o ho => ⟨o, List.mem_append_left _ ho,
      Nat.le_refl _, Nat.le_refl _⟩), by rw [S.rd, K₁.rd], by rw [S.wr, K₁.wr], by rw [S.syms, K₁.syms]⟩
    obtain word₂ : ∀ d, hdr ≤ d → d + 4 ≤ fG →
        t₂.mem.readW (off E.base d) 32 = t₁.mem.readW (off E.base d) 32 :=
      fun d hd' hd => Env.Chg.word v S.chg (by simp only [fG, hdr] at hd; omega_arith) fun o ho => ⟨by
        rcases List.mem_append.mp ho with h | h
        · exact (rRanges_apart v o h).1
        · exact (wRanges_apart G v o h).1, by
        simp only [rRanges, wRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [aTmp, aH, arr, fLo, sPk, fG, hdr] at hd hd' ⊢ <;> omega_arith⟩
    -- The next `h`.
    refine ld_ok K₂.base.scr (d := fH) (by simp only [fH, hdr]; omega_arith) fun t₃ u₃ => wp_addi fun t₄ u₄ =>
      st_ok (Scr.of_eq K₂.base.scr (by rw [u₄.other _ (by decide), u₃.other _ (by decide)])
        (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]) (by rw [u₄.wr, u₃.wr])) (d := fH)
        (by simp only [fH, hdr]; omega_arith) fun t₅ M₅ => ?_
    obtain m₅ : t₅.mem = t₂.mem.writeW (off E.base fH) ((E.hs + BitVec.ofNat 64 ((j + 1) * E.pLen)).setWidth 32) := by
      rw [M₅.mem, u₄.mem, u₃.mem, u₄.gpr, u₃.gpr, word₂ fH (by simp only [fH, hdr]; omega_arith) (by simp only [fH, fG, hdr]; omega_arith), m₁, L.fh, ← hp,
        ptr_add, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.succ_mul]
    obtain K₅ := K₂.store G v (d := fH) (by simp [gRanges]) _ m₅
      (by rw [M₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide)])
      (by rw [M₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide)]) (by rw [M₅.rd, u₄.rd, u₃.rd])
      (by rw [M₅.wr, u₄.wr, u₃.wr]) (by rw [M₅.syms, u₄.syms, u₃.syms])
    refine ld_ok K₅.base.scr (d := fHLeft) (by simp only [fHLeft, hdr]; omega_arith) fun t₆ u₆ => wp_subi fun t₇ u₇ _ _ =>
      st_ok (Scr.of_eq K₅.base.scr (by rw [u₇.other _ (by decide), u₆.other _ (by decide)])
        (by rw [u₇.other _ (by decide), u₆.other _ (by decide)]) (by rw [u₇.wr, u₆.wr])) (d := fHLeft)
        (by simp only [fHLeft, hdr]; omega_arith) fun t₈ M₈ => WP.block_nil ?_
    obtain ws : ∀ (m : Mem) {d e : Nat}, d + 4 ≤ sState → e + 4 ≤ sState → (d + 4 ≤ e ∨ e + 4 ≤ d) → ∀ y,
        (m.writeW (off E.base e) y).readW (off E.base d) 32 = m.readW (off E.base d) 32 :=
      fun m d e h₁ h₂ h y => word_store_other v m (by simp only [sState] at h₁; omega_arith)
        (by simp only [sState] at h₂; omega_arith) h y
    obtain m₈ : t₈.mem = t₅.mem.writeW (off E.base fHLeft) (BitVec.ofNat 32 (E.hsLen - (j + 1) * E.pLen)) := by
      rw [M₈.mem, u₇.mem, u₆.mem, u₇.gpr, u₆.gpr, m₅, ws _ (by simp only [fHLeft, sState, hdr]; omega_arith)
        (by simp only [fH, sState, hdr]; omega_arith) (by simp only [fH, fHLeft, hdr]; omega_arith),
        word₂ fHLeft (by simp only [fHLeft, hdr]; omega_arith) (by simp only [fHLeft, fG, hdr]; omega_arith), m₁, L.left, ← hp,
        sub_ofNat (by rw [hp] at hj1 ⊢; rw [Nat.succ_mul] at hj1; omega_arith), Nat.succ_mul, Nat.sub_sub]
    obtain K₈ := K₅.store G v (d := fHLeft) (by simp [gRanges]) _ m₈
      (by rw [M₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide)])
      (by rw [M₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide)]) (by rw [M₈.rd, u₇.rd, u₆.rd])
      (by rw [M₈.wr, u₇.wr, u₆.wr]) (by rw [M₈.syms, u₇.syms, u₆.syms])
    obtain fG₈ : t₈.mem.readW (off E.base fG) 32 =
        BitVec.ofNat 32 (if Found (Spec.Dsa.decodeBE (hChunk E j)) p x then 1 else 4) := by
      rw [m₈, ws _ (by simp only [fG, sState, hdr]; omega_arith) (by simp only [fHLeft, sState, hdr]; omega_arith)
        (by simp only [fG, fHLeft, hdr]; omega_arith), m₅, ws _ (by simp only [fG, sState, hdr]; omega_arith)
        (by simp only [fH, sState, hdr]; omega_arith) (by simp only [fG, fH, hdr]; omega_arith), S.fg]
    have spec := L.spec
    have cnt := L.count
    rw [hList_drop E hjN, VG.Proof.Dsa.Generation.generator_cons] at spec
    rw [hList_drop E hjN, VG.Proof.Dsa.Generation.generatorCount, hit_found hx'] at cnt
    refine cmpF_end K₈.base.scr (o := fG) (v := 4) (by simp only [fG, hdr]; omega_arith) fG₈ (by split <;> omega_arith)
      (by decide) fun t₉ g₉ m₉ rd₉ wr₉ sy₉ z₉ => ?_
    obtain K₉ := K₈.mem m₉ (g₉ _ (by decide)) (g₉ _ (by decide)) rd₉ wr₉ sy₉
    by_cases hf : Found (Spec.Dsa.decodeBE (hChunk E j)) p x
    · -- A generator.
      refine .inl ⟨by rw [show t₉.zf = _ from z₉]; simp [hf], by simp [gCont, hf], K₉, ?_, ?_⟩
      rotate_left
      · simp only [hf, decide_true, ↓reduceIte] at cnt
        rw [m₉, m₈, ws _ (by simp only [fH, sState, hdr]; omega_arith) (by simp only [fHLeft, sState, hdr]; omega_arith)
          (by simp only [fH, fHLeft, hdr]; omega_arith), m₅, Mem.readW_writeW_self32, hEnd, cnt, Nat.mul_comm]
      obtain hR : Rg = some (gVal (Spec.Dsa.decodeBE (hChunk E j)) p x) := by
        rw [← spec]; simp only [hf.1, hf.2.1, and_self, ↓reduceIte]
        rw [VG.Proof.Dsa.powMod_eq, ← hx']
        simp only [show 1 < Spec.Dsa.decodeBE (hChunk E j) ^ x % p from hf.2.2, ↓reduceIte]; rfl
      rw [hR]
      refine ⟨by rw [m₉, fG₈]; simp only [hf, ↓reduceIte], ?_⟩
      rw [m₉, m₈, Env.Chg.scratch v ((Env.Chg.refl [(fHLeft, 4)] t₅.mem).store (List.mem_singleton_self _)
        (by decide) _) (by simp only [sPk]; omega_arith) (fun o ho => by
          simp only [List.mem_singleton] at ho; subst ho; simp only [fHLeft, sPk, hdr]; omega_arith), m₅,
        Env.Chg.scratch v ((Env.Chg.refl [(fH, 4)] t₂.mem).store (List.mem_singleton_self _)
        (by decide) _) (by simp only [sPk]; omega_arith) (fun o ho => by
          simp only [List.mem_singleton] at ho; subst ho; simp only [fH, sPk, hdr]; omega_arith), S.gb hf]
    · -- On to the next `h`.
      refine .inr ⟨by rw [show t₉.zf = _ from z₉]; simp [hf], by simp [gCont, hne, hf], hj1, K₉, ?_, ?_, ?_, hj1, ?_, ?_⟩
      rotate_right
      · simp only [hf, decide_false, Bool.false_eq_true, ↓reduceIte] at cnt
        rw [cnt]; omega_arith
      · rw [m₉, m₈, ws _ (by simp only [fH, sState, hdr]; omega_arith) (by simp only [fHLeft, sState, hdr]; omega_arith)
          (by simp only [fH, fHLeft, hdr]; omega_arith), m₅, Mem.readW_writeW_self32]
      · rw [m₉, m₈, Mem.readW_writeW_self32]
      · rw [m₉, fG₈]; simp only [hf, ↓reduceIte]
      · rw [← spec]
        by_cases hr : 1 < Spec.Dsa.decodeBE (hChunk E j) ∧ Spec.Dsa.decodeBE (hChunk E j) < p - 1
        · have : ¬ 1 < gVal (Spec.Dsa.decodeBE (hChunk E j)) p x := fun h => hf ⟨hr.1, hr.2, h⟩
          simp only [hr, and_self, ↓reduceIte]
          rw [VG.Proof.Dsa.powMod_eq, ← hx']
          simp only [show ¬ 1 < Spec.Dsa.decodeBE (hChunk E j) ^ x % p from this, ↓reduceIte]
        · simp only [hr, ↓reduceIte]

/-- The generator's state words: the first `h`, all of the tape left, `fG` := 4. -/
theorem gInit_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s : State} (B : Base E s) (p Q : Nat)
    (hsW : s.mem.readW (off E.base fHs) 32 = E.hs.setWidth 32)
    (hsLenW : s.mem.readW (off E.base fHsLen) 32 = BitVec.ofNat 32 E.hsLen) :
    WP isa (.block [.mov .eax (.mem (sc fHs)), .store (sc fH) .eax, .mov .eax (.mem (sc fHsLen)),
      .store (sc fHLeft) .eax, .mov .eax (.imm 4), .store (sc fG) .eax]) s
      (GLoop E g p Q (Spec.Dsa.generator p Q (hList E)) s 0) := by
  have sz := v.size_ge
  obtain K₀ : GKeep E g s s := ⟨B, Env.Chg.refl _ _, rfl, rfl, rfl⟩
  obtain ws : ∀ (m : Mem) {d e : Nat}, d + 4 ≤ sState → e + 4 ≤ sState → (d + 4 ≤ e ∨ e + 4 ≤ d) → ∀ y,
      (m.writeW (off E.base e) y).readW (off E.base d) 32 = m.readW (off E.base d) 32 :=
    fun m d e h₁ h₂ h y => word_store_other v m (by simp only [sState] at h₁; omega_using [sz, h₁])
      (by simp only [sState] at h₂; omega_using [sz, h₂]) h y
  refine ld_ok B.scr (d := fHs) (by simp only [fHs, hdr]; omega_using [sz]) fun s₁ u₁ =>
    st_ok (Scr.of_eq B.scr (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.wr) (d := fH)
      (by simp only [fH, hdr]; omega_using [sz]) fun s₂ M₂ => ?_
  obtain K₂ := K₀.store G v (d := fH) (by simp [gRanges]) _ (by rw [M₂.mem, u₁.mem]) (by rw [M₂.gpr, u₁.other _ (by decide)])
    (by rw [M₂.gpr, u₁.other _ (by decide)]) (by rw [M₂.rd, u₁.rd]) (by rw [M₂.wr, u₁.wr]) (by rw [M₂.syms, u₁.syms])
  refine ld_ok K₂.base.scr (d := fHsLen) (by simp only [fHsLen, hdr]; omega_using [sz]) fun s₃ u₃ =>
    st_ok (Scr.of_eq K₂.base.scr (u₃.other _ (by decide)) (u₃.other _ (by decide)) u₃.wr) (d := fHLeft)
      (by simp only [fHLeft, hdr]; omega_using [sz]) fun s₄ M₄ => ?_
  obtain K₄ := K₂.store G v (d := fHLeft) (by simp [gRanges]) _ (by rw [M₄.mem, u₃.mem])
    (by rw [M₄.gpr, u₃.other _ (by decide)]) (by rw [M₄.gpr, u₃.other _ (by decide)]) (by rw [M₄.rd, u₃.rd])
    (by rw [M₄.wr, u₃.wr]) (by rw [M₄.syms, u₃.syms])
  refine wp_movi fun s₅ u₅ => st_ok (Scr.of_eq K₄.base.scr (u₅.other _ (by decide)) (u₅.other _ (by decide)) u₅.wr)
    (d := fG) (by simp only [fG, hdr]; omega_using [sz]) fun s₆ M₆ => WP.block_nil ?_
  obtain K₆ := K₄.store G v (d := fG) (by simp [gRanges, wRanges]) _ (by rw [M₆.mem, u₅.mem])
    (by rw [M₆.gpr, u₅.other _ (by decide)]) (by rw [M₆.gpr, u₅.other _ (by decide)]) (by rw [M₆.rd, u₅.rd])
    (by rw [M₆.wr, u₅.wr]) (by rw [M₆.syms, u₅.syms])
  obtain m₆ : s₆.mem = ((s.mem.writeW (off E.base fH) (s.mem.readW (off E.base fHs) 32)).writeW (off E.base fHLeft)
      (s.mem.readW (off E.base fHsLen) 32)).writeW (off E.base fG) (4 : BitVec 32) := by
    rw [M₆.mem, u₅.mem, u₅.gpr, M₄.mem, u₃.mem, u₃.gpr, M₂.mem, u₁.mem, u₁.gpr,
      ws _ (by simp only [fHsLen, sState, hdr]; omega_using []) (by simp only [fH, sState, hdr]; omega_using [])
      (by simp only [fHsLen, fH, hdr]; omega_using [])]
  refine ⟨K₆, ?_, ?_, by rw [m₆, Mem.readW_writeW_self32]; rfl, by omega_using [], by rw [List.drop_zero],
    by rw [List.drop_zero, Nat.zero_add]⟩
  · rw [m₆, ws _ (by simp only [fH, sState, hdr]; omega_using []) (by simp only [fG, sState, hdr]; omega_using [])
      (by simp only [fH, fG, hdr]; omega_using []), ws _ (by simp only [fH, sState, hdr]; omega_using [])
      (by simp only [fHLeft, sState, hdr]; omega_using []) (by simp only [fH, fHLeft, hdr]; omega_using []),
      Mem.readW_writeW_self32, hsW, Nat.zero_mul, BitVec.add_zero]
  · rw [m₆, ws _ (by simp only [fHLeft, sState, hdr]; omega_using []) (by simp only [fG, sState, hdr]; omega_using [])
      (by simp only [fHLeft, fG, hdr]; omega_using []), Mem.readW_writeW_self32, hsLenW, Nat.zero_mul, Nat.sub_zero]

/-- The generator over the whole `h` tape. -/
theorem gPart_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) {s : State} (B : Base E s)
    (hsW : s.mem.readW (off E.base fHs) 32 = E.hs.setWidth 32)
    (hsLenW : s.mem.readW (off E.base fHsLen) 32 = BitVec.ofNat 32 E.hsLen)
    {p Q x : Nat} (hx' : x = (p - 1) / Q)
    (hone : val32 s.mem E.base aOne g.n32 = 1) (hpm1 : val32 s.mem E.base aPm1 g.n32 = p - 1)
    (hP : val32 s.mem E.base aP g.n32 = p) (hE : val32 s.mem E.base aE g.n32 = x) (hxl : x < 2 ^ (32 * g.e))
    (hp1 : 1 < p) (hodd : p % 2 = 1) (hplt : p < 2 ^ (8 * g.pLen)) :
    WP isa g.gPart s fun t => GKeep E g s t ∧ GRes E g t.mem (Spec.Dsa.generator p Q (hList E)) ∧
      t.mem.readW (off E.base fH) 32 = hEnd E p Q := by
  have sz := v.size_ge
  have lens := v.witLen32
  have pl := v.pLen_ge
  unfold Geo.gPart
  show WP isa (.seq (.block _) (.loop _ .e)) s _
  refine WP.seq (WP.mono (gInit_ok G v B p Q hsW hsLenW) fun s₆ L₀ => ?_)
  obtain hm : E.hsLen / E.pLen * E.pLen ≤ E.hsLen := Nat.div_mul_le_self _ _
  refine WP.loop (M := isa) (fun m t => ∃ j, j + m = E.hsLen / E.pLen + 1 ∧
      GLoop E g p Q (Spec.Dsa.generator p Q (hList E)) s j t)
    (fun m t ⟨j, hm', L⟩ => WP.mono (gBody_ok G v hp hx' hone hpm1 hP hE hxl hp1 hodd hplt L) fun t' h => ?_)
    (E.hsLen / E.pLen + 1) s₆ ⟨0, by omega_using [], L₀⟩
  rcases h with ⟨z, _, K, res, fh⟩ | ⟨z, _, hj1, L'⟩
  · exact .inl ⟨z, K, res, fh⟩
  · have : j + 1 ≤ E.hsLen / E.pLen := (Nat.le_div_iff_mul_le (by omega_using [pl])).mpr hj1
    exact .inr ⟨z, m - 1, by omega_using [hm', this], j + 1, by omega_using [hm', this], L'⟩

end VG.Proof.Dsa.X86.Generation
