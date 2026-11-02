module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Q
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PPart
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GPart
import VerifiedGarbage.Proof.Dsa.X86.Generation.CheckCall
public import VerifiedGarbage.Proof.Dsa.Generation.SeedResult
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geo
import VerifiedGarbage.Proof.Dsa.X86.Generation.GRange
import VerifiedGarbage.Proof.Dsa.X86.Generation.Flags
import VerifiedGarbage.Proof.Dsa.X86.Generation.AddBE
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base

/-! # One seed: q, p, g and the domain check (A.1.1.2, A.2.1) -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Proof.Dsa.Generation

/-- The ranges a seed changes. -/
def atRanges (g : Geo) : List (Nat × Nat) :=
  qRanges g ++ ppRanges g ++ gRanges g ++ [(sChk, 16 * g.pLen * 8), (fStatus, 4)]

/-- A seed's result in memory `m`: `fStatus` 2 if a tape ran out, 1 with
p||q||g if the domain passed, else 0 and the witnesses left. -/
def ARes (E : Env) (g : Geo) (m : Mem) : Option (Option Spec.Dsa.Params × Spec.RsaKeyGen.Rand) → Prop
  | none => m.readW (off E.base fStatus) 32 = BitVec.ofNat 32 2
  | some (none, rest) => m.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0 ∧
      ∃ u, u ≤ E.witLen ∧ m.readW (off E.base fUsed) 32 = BitVec.ofNat 32 u ∧ E.witT.drop u = rest
  | some (some a, _) => m.readW (off E.base fStatus) 32 = BitVec.ofNat 32 1 ∧
      Spec.Rsa.bytesAt m (off E.base sPk) (2 * g.pLen + g.qLen) = Spec.Dsa.encodeParams g.pLen g.qLen a

/-- What a seed keeps. -/
structure AKeep (E : Env) (g : Geo) (s t : State) : Prop where
  base : Base E t
  chg : E.Chg (atRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem generator_lt {p q g : Nat} {hs : List Nat} (hp : 0 < p) (h : Spec.Dsa.generator p q hs = some g) :
    g < p := by
  induction hs with
  | nil => simp [Spec.Dsa.generator] at h
  | cons x xs ih =>
    rw [VG.Proof.Dsa.Generation.generator_cons] at h
    split at h
    · dsimp only at h
      split at h
      · cases h; rw [VG.Proof.Dsa.powMod_eq]; exact Nat.mod_lt _ hp
      · exact ih h
    · exact ih h

theorem atRanges_apart {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) :
    E.Apart (atRanges g) := by
  have sz := v.size_ge
  have bd := G.bounds
  have room : 512 * g.pLen + 8192 ≤ E.size := hp ▸ v.room
  intro o ho
  simp only [atRanges, List.mem_append] at ho
  rcases ho with ((h | h) | h) | h
  · have szq : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 1632 := by
      rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
    simp only [qRanges, qPre, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sState, sHScr, sPk, sPP, fRes, fUsed, fUsedOut, fOut, fWitLen, hdr] <;> omega
  · exact ppRanges_apart G v o h
  · exact gRanges_apart G v o h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp only [sChk, fStatus, fOut, fWitLen, hdr] <;> omega

/-- A seed's result after q's test `r`. -/
def qOutcome (l n q : Nat) (seed : List Byte) (hs : List Nat) :
    Option (Bool × Spec.RsaKeyGen.Rand) → Option (Option Spec.Dsa.Params × Spec.RsaKeyGen.Rand)
  | none => none
  | some (false, rest) => some (none, rest)
  | some (true, rest) => primeResult l n q seed hs rest

theorem seedResult_eq (l n : Nat) (seed : List Byte) (hs : List Nat) (rand : Spec.RsaKeyGen.Rand) :
    seedResult l n seed hs rand =
      qOutcome l n (Spec.Dsa.qCandidate n seed) seed hs (Spec.Dsa.probablePrime (Spec.Dsa.qCandidate n seed) rand) := by
  unfold seedResult qOutcome
  dsimp only
  rcases Spec.Dsa.probablePrime (Spec.Dsa.qCandidate n seed) rand with _ | ⟨_ | _, _⟩ <;> rfl

/-- A seed's result after p's search `R`. -/
def pOutcome (q : Nat) (hs : List Nat) :
    Option (Option Nat × Spec.RsaKeyGen.Rand) → Option (Option Spec.Dsa.Params × Spec.RsaKeyGen.Rand)
  | none => none
  | some (none, rest) => some (none, rest)
  | some (some p, rest) => generatorResult p q hs rest

theorem primeResult_eq (l n q : Nat) (seed : List Byte) (hs : List Nat) (rand : Spec.RsaKeyGen.Rand) :
    primeResult l n q seed hs rand = pOutcome q hs (Spec.Dsa.primeFromSeed l n q seed rand) := by
  unfold primeResult pOutcome
  rcases Spec.Dsa.primeFromSeed l n q seed rand with _ | ⟨_ | _, _⟩ <;> rfl

theorem AKeep.mem {E : Env} {g : Geo} {s t t' : State} (K : AKeep E g s t) (hm : t'.mem = t.mem)
    (edi : t'.gpr .edi = t.gpr .edi) (sp : t'.gpr .esp = t.gpr .esp) (rd : t'.rd = t.rd) (wr : t'.wr = t.wr)
    (sy : t'.syms = t.syms) : AKeep E g s t' :=
  ⟨K.base.regs hm edi sp rd wr sy, by rw [hm]; exact K.chg, by rw [rd, K.rd], by rw [wr, K.wr], by rw [sy, K.syms]⟩

theorem AKeep.store {E : Env} {g : Geo} {s t t' : State} (K : AKeep E g s t) (G : GeoOk g) (v : E.Valid)
    (hp : E.pLen = g.pLen) {d : Nat} (hd : (d, 4) ∈ atRanges g) (x : BitVec 32)
    (hm : t'.mem = t.mem.writeW (off E.base d) x) (edi : t'.gpr .edi = t.gpr .edi) (sp : t'.gpr .esp = t.gpr .esp)
    (rd : t'.rd = t.rd) (wr : t'.wr = t.wr) (sy : t'.syms = t.syms) : AKeep E g s t' := by
  have C : E.Chg [(d, 4)] t.mem t'.mem := by
    rw [hm]; exact (Env.Chg.refl _ _).store (List.mem_singleton_self _) (by decide) x
  exact ⟨K.base.keep v C (fun o ho => atRanges_apart G v hp o
      (by simp only [List.mem_singleton] at ho; rw [ho]; exact hd)) edi sp rd wr sy,
    K.chg.trans (C.widen fun o ho => ⟨o, by simp only [List.mem_singleton] at ho; rw [ho]; exact hd,
      Nat.le_refl _, Nat.le_refl _⟩), by rw [rd, K.rd], by rw [wr, K.wr], by rw [sy, K.syms]⟩

/-- A word of the header apart from every range of a seed. -/
theorem AKeep.word {E : Env} {g : Geo} {s t : State} (K : AKeep E g s t) (G : GeoOk g) (v : E.Valid)
    (hp : E.pLen = g.pLen) {d : Nat} (hd₁ : hdr ≤ d) (hd₂ : d + 4 ≤ fUsed) :
    t.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 := by
  have sz := v.size_ge
  have Aat := atRanges_apart G v hp
  have bd := G.bounds
  have szq : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 1632 := by
    rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
  have key : ∀ o ∈ atRanges g, o.1 + o.2 ≤ d ∨ d + 4 ≤ o.1 := by
    simp only [atRanges, qRanges, qPre, ppRanges, paRanges, pxRanges, aRanges, gRanges, rRanges, wRanges,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    simp only [sState, sHScr, sX, sPk, sPP, ppWords, arr, aTmp, aH, sChk, fRes, fUsed, fUsedOut, fP, fCounter,
      fOffset, fH, fHLeft, fG, fLo, fStatus, hdr] at hd₁ hd₂ ⊢
    repeat' apply And.intro
    all_goals omega
  exact Env.Chg.word v K.chg (by simp only [fUsed, hdr] at hd₂; omega)
    fun o ho => ⟨(Aat o ho).1, key o ho⟩

theorem attempt_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s : State} (B : Base E s) {k : Nat} (hk : (k + 1) * E.qLen ≤ E.seedsLen)
    (hS : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32)
    {used : Nat} (hU : s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used) (hu : used ≤ E.witLen)
    (hst : s.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0) :
    WP isa g.attempt s fun t => AKeep E g s t ∧
      ARes E g t.mem (seedResult (8 * g.pLen) (8 * g.qLen) (chunk E k) (hList E) (E.witT.drop used)) := by
  have sz := v.size_ge
  have bd := G.bounds
  have Aat := atRanges_apart G v hp
  have wl : E.witT.length = E.witLen := by rw [← B.wit, VG.Proof.Bignum.bytesAt_length]
  have qsh := VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * g.qLen) (by omega_arith) (chunk E k)
  unfold Geo.attempt
  simp only [seqs]
  -- q.
  refine WP.seq (WP.mono (qPart_ok G v hp hq B hk hS hU hu) fun t₁ Q₁ => ?_)
  obtain ⟨r, hr⟩ : ∃ r, Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) (E.witT.drop used) = r :=
    ⟨_, rfl⟩
  have res₁ := Q₁.res
  have used₁ := Q₁.used
  rw [hr] at res₁ used₁
  have K₁ : AKeep E g s t₁ := ⟨Q₁.base, Q₁.chg.widen fun o ho => ⟨o, by simp [atRanges, ho], Nat.le_refl _,
    Nat.le_refl _⟩, Q₁.rd, Q₁.wr, Q₁.syms⟩
  have st₁ : t₁.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0 := by
    rw [Env.Chg.word v Q₁.chg (by simp only [fStatus, hdr]; omega_arith) (fun o ho => ⟨(Aat o (by simp [atRanges, ho])).1, by
      have szq : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 1632 := by
        rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
      simp only [qRanges, qPre, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [sState, sHScr, sPk, sPP, fRes, fUsed, fUsedOut, fStatus, hdr] <;> omega_arith⟩), hst]
  rw [seedResult_eq, hr]
  refine WP.seq (cmpF_end K₁.base.scr (o := fRes) (v := 0) (by simp only [fRes, hdr]; omega_arith) res₁ (status_lt r)
    (by decide) fun t₂ g₂ m₂ rd₂ wr₂ sy₂ z₂ => ?_)
  have K₂ := K₁.mem m₂ (g₂ _ (by decide)) (g₂ _ (by decide)) rd₂ wr₂ sy₂
  refine WP.ite _ z₂ (fun h0 => stImm_end K₂.base.scr (o := fStatus) (v := 2) (by simp only [fStatus, hdr]; omega_arith)
    fun t₃ g₃ m₃ rd₃ wr₃ sy₃ => ?_) (fun h0 => ?_)
  · -- The witnesses ran out at q.
    have hn : r = none := by
      rcases r with _ | ⟨_ | _, _⟩ <;> simp_all [Proof.Dsa.ProbablePrime.status]
    subst hn
    exact ⟨K₂.store G v hp (by simp [atRanges]) _ m₃ (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃ sy₃,
      by show _ = _; rw [m₃, Mem.readW_writeW_self32]⟩
  refine WP.seq (cmpF_end K₂.base.scr (o := fRes) (v := 1) (by simp only [fRes, hdr]; omega_arith) (by rw [m₂]; exact res₁)
    (status_lt r) (by decide) fun t₃ g₃ m₃ rd₃ wr₃ sy₃ z₃ => ?_)
  have K₃ := K₂.mem m₃ (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃ sy₃
  have mem₃ : t₃.mem = t₁.mem := by rw [m₃, m₂]
  refine WP.ite _ z₃ (fun h1 => ?_) (fun h1 => WP.block_nil ?_)
  rotate_left
  · -- q composite: the next seed.
    obtain ⟨rest, hrest⟩ : ∃ rest, r = some (false, rest) := by
      rcases r with _ | ⟨_ | _, rest⟩ <;> simp_all [Proof.Dsa.ProbablePrime.status]
    subst hrest
    have cur := probablePrime_cursor hr
    rw [wl] at cur
    refine ⟨K₃, by rw [mem₃]; exact st₁, E.witLen - rest.length, by omega_arith, ?_, cur⟩
    rw [mem₃, used₁]; rfl
  -- q a probable prime: p.
  obtain ⟨rest, hrest⟩ : ∃ rest, r = some (true, rest) := by
    rcases r with _ | ⟨_ | _, rest⟩ <;> simp_all [Proof.Dsa.ProbablePrime.status]
  subst hrest
  have cur := probablePrime_cursor hr
  rw [wl] at cur
  show WP isa _ t₃ fun t => AKeep E g s t ∧ ARes E g t.mem (primeResult (8 * g.pLen) (8 * g.qLen)
    (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) (chunk E k) (hList E) rest)
  rw [primeResult_eq]
  have hS₃ : t₃.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32 := by
    rw [K₃.word G v hp (by simp only [fSeed]; omega_arith) (by simp only [fSeed, fUsed, hdr]; omega_arith), hS]
  have hQ₃ : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t₃.mem (off E.base (sPk + g.pLen)) g.qLen) =
      Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k) := by rw [mem₃]; exact Q₁.q
  have hU₃ : t₃.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (E.witLen - rest.length) := by
    rw [mem₃, used₁]; rfl
  refine WP.seq (WP.mono (pPart_ok G v hq K₃.base hk hS₃ hQ₃ (by omega_arith) hU₃ (by omega_arith)) fun t₄ ⟨P₄, R₄⟩ => ?_)
  rw [cur] at R₄
  have K₄ : AKeep E g s t₄ := ⟨P₄.base, K₃.chg.trans (P₄.chg.widen fun o ho => ⟨o, by simp [atRanges, ho],
    Nat.le_refl _, Nat.le_refl _⟩), by rw [P₄.rd, K₃.rd], by rw [P₄.wr, K₃.wr], by rw [P₄.syms, K₃.syms]⟩
  have ppA := ppRanges_apart G v
  have word₄ : ∀ d, fStatus ≤ d → d + 4 ≤ sState → t₄.mem.readW (off E.base d) 32 = t₃.mem.readW (off E.base d) 32 :=
    fun d h₁ h₂ => Env.Chg.word v P₄.chg (by simp only [sState] at h₂; omega_arith) fun o ho => ⟨(ppA o ho).1, by
      simp only [ppRanges, paRanges, pxRanges, aRanges, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [sState, sX, arr, sPk, sPP, ppWords, fRes, fUsed, fUsedOut, fP, fCounter, fOffset, fStatus,
          hdr] at h₁ h₂ ⊢ <;> omega_arith⟩
  have st₄ : t₄.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0 := by
    rw [word₄ fStatus (Nat.le_refl _) (by simp only [fStatus, sState, hdr]; omega_arith), mem₃, st₁]
  obtain ⟨R, hR⟩ : ∃ R, Spec.Dsa.primeFromSeed (8 * g.pLen) (8 * g.qLen) (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k))
      (chunk E k) rest = R := ⟨_, rfl⟩
  rw [hR] at R₄ ⊢
  rcases R with _ | ⟨_ | p, rest'⟩
  · -- The witnesses ran out at p.
    refine WP.seq (cmpF_end K₄.base.scr (o := fP) (v := 0) (w := 0) (by simp only [fP, hdr]; omega_arith) R₄ (by decide)
      (by decide) fun t₅ g₅ m₅ rd₅ wr₅ sy₅ z₅ => ?_)
    have K₅ := K₄.mem m₅ (g₅ _ (by decide)) (g₅ _ (by decide)) rd₅ wr₅ sy₅
    refine WP.ite _ z₅ (fun _ => stImm_end K₅.base.scr (o := fStatus) (v := 2) (by simp only [fStatus, hdr]; omega_arith)
      fun t₆ g₆ m₆ rd₆ wr₆ sy₆ => ⟨K₅.store G v hp (by simp [atRanges]) _ m₆ (g₆ _ (by decide)) (g₆ _ (by decide))
        rd₆ wr₆ sy₆, by show _ = _; rw [m₆, Mem.readW_writeW_self32]⟩) (fun h => by simp at h)
  · -- No p: the next seed.
    obtain ⟨fp₄, u, hu', fu₄, du⟩ := R₄
    refine WP.seq (cmpF_end K₄.base.scr (o := fP) (v := 0) (w := 2) (by simp only [fP, hdr]; omega_arith) fp₄ (by decide)
      (by decide) fun t₅ g₅ m₅ rd₅ wr₅ sy₅ z₅ => ?_)
    have K₅ := K₄.mem m₅ (g₅ _ (by decide)) (g₅ _ (by decide)) rd₅ wr₅ sy₅
    refine WP.ite _ z₅ (fun h => by simp at h) (fun _ => ?_)
    refine WP.seq (cmpF_end K₅.base.scr (o := fP) (v := 1) (w := 2) (by simp only [fP, hdr]; omega_arith)
      (by rw [m₅]; exact fp₄) (by decide) (by decide) fun t₆ g₆ m₆ rd₆ wr₆ sy₆ z₆ => ?_)
    have K₆ := K₅.mem m₆ (g₆ _ (by decide)) (g₆ _ (by decide)) rd₆ wr₆ sy₆
    refine WP.ite _ z₆ (fun h => by simp at h) (fun _ => WP.block_nil ⟨K₆, ?_, u, hu', ?_, du⟩)
    · rw [m₆, m₅, st₄]
    · rw [m₆, m₅, fu₄]
  · -- p: g.
    obtain ⟨fp₄, plo, phi, podd, ⟨u, hu', fu₄, du⟩, pk₄, pm₄, e₄, pv₄, one₄⟩ := R₄
    refine WP.seq (cmpF_end K₄.base.scr (o := fP) (v := 0) (w := 1) (by simp only [fP, hdr]; omega_arith) fp₄ (by decide)
      (by decide) fun t₅ g₅ m₅ rd₅ wr₅ sy₅ z₅ => ?_)
    have K₅ := K₄.mem m₅ (g₅ _ (by decide)) (g₅ _ (by decide)) rd₅ wr₅ sy₅
    refine WP.ite _ z₅ (fun h => by simp at h) (fun _ => ?_)
    refine WP.seq (cmpF_end K₅.base.scr (o := fP) (v := 1) (w := 1) (by simp only [fP, hdr]; omega_arith)
      (by rw [m₅]; exact fp₄) (by decide) (by decide) fun t₆ g₆ m₆ rd₆ wr₆ sy₆ z₆ => ?_)
    have K₆ := K₅.mem m₆ (g₆ _ (by decide)) (g₆ _ (by decide)) rd₆ wr₆ sy₆
    have mem₆ : t₆.mem = t₄.mem := by rw [m₆, m₅]
    refine WP.ite _ z₆ (fun _ => ?_) (fun h => by simp at h)
    have Qlo := qsh.2.1
    have hxl : (p - 1) / Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k) < 2 ^ (32 * g.e) := by
      have ex : 8 * g.pLen ≤ 32 * g.e + (8 * g.qLen - 1) := by
        rw [G.e]; rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
      rw [Nat.div_lt_iff_lt_mul (by omega_arith)]
      have := Nat.mul_le_mul_left (2 ^ (32 * g.e)) Qlo
      rw [← Nat.pow_add] at this
      have := Nat.pow_le_pow_right (n := 2) (by decide) ex
      omega_arith
    refine WP.seq (WP.mono (gPart_ok G v hp K₆.base (p := p) (Q := Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k))
      (x := (p - 1) / Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) rfl (by rw [mem₆]; exact one₄)
      (by rw [mem₆]; exact pm₄) (by rw [mem₆]; exact pv₄) (by rw [mem₆]; exact e₄) hxl
      (by have := Nat.one_lt_two_pow (n := 8 * g.pLen - 1) (by omega_arith); omega_arith) podd phi) fun t₇ ⟨GK, GR⟩ => ?_)
    clear z₆
    have K₇ : AKeep E g s t₇ := ⟨GK.base, K₆.chg.trans (GK.chg.widen fun o ho => ⟨o, by simp [atRanges, ho],
      Nat.le_refl _, Nat.le_refl _⟩), by rw [GK.rd, K₆.rd], by rw [GK.wr, K₆.wr], by rw [GK.syms, K₆.syms]⟩
    have gA := gRanges_apart G v
    have gR : ∀ {d n : Nat}, sPk ≤ d → d + n ≤ sPk + g.pLen + g.qLen →
        ∀ o ∈ gRanges g, o.1 + o.2 ≤ E.size ∧ (o.1 + o.2 ≤ d ∨ d + n ≤ o.1) := fun h₁ h₂ o ho => ⟨(gA o ho).1, by
      simp only [gRanges, rRanges, wRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [aTmp, aH, arr, fLo, sPk, fG, fH, fHLeft, hdr] at h₁ h₂ ⊢ <;> omega_arith⟩
    have gW : ∀ d, hdr ≤ d → (d + 4 ≤ fH ∨ (fG + 4 ≤ d ∧ d + 4 ≤ fLo)) →
        t₇.mem.readW (off E.base d) 32 = t₆.mem.readW (off E.base d) 32 :=
      fun d h₁ h₂ => Env.Chg.word v GK.chg (by simp only [fH, fG, fLo, hdr] at h₂; omega_arith) fun o ho => ⟨(gA o ho).1, by
        simp only [gRanges, rRanges, wRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [aTmp, aH, arr, fLo, sPk, fG, fH, fHLeft, hdr] at h₁ h₂ ⊢ <;> omega_arith⟩
    have st₇ : t₇.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0 := by
      rw [gW fStatus (by simp only [fStatus]; omega_arith) (.inr (by simp only [fG, fStatus, fLo, hdr]; omega_arith)), mem₆, st₄]
    have fu₇ : t₇.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 u := by
      rw [gW fUsed (by simp only [fUsed]; omega_arith) (.inl (by simp only [fUsed, fH, hdr]; omega_arith)), mem₆, fu₄]
    have pk₇ : Spec.Rsa.bytesAt t₇.mem (off E.base sPk) g.pLen = Spec.Dsa.encodeBE g.pLen p := by
      rw [Env.Chg.scratch v GK.chg (by simp only [sPk]; omega_arith) (gR (Nat.le_refl _) (by omega_arith)), mem₆, pk₄]
    have qk₇ : Spec.Rsa.bytesAt t₇.mem (off E.base (sPk + g.pLen)) g.qLen =
        Spec.Dsa.encodeBE g.qLen (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) := by
      rw [Env.Chg.scratch v GK.chg (by simp only [sPk]; omega_arith) (gR (by omega_arith) (by omega_arith)), mem₆,
        Env.Chg.scratch v P₄.chg (by simp only [sPk]; omega_arith) (fun o ho => ⟨(ppA o ho).1, by
          simp only [ppRanges, paRanges, pxRanges, aRanges, List.cons_append, List.nil_append, List.mem_cons,
            List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp only [sState, sX, arr, sPk, sPP, ppWords, fRes, fUsed, fUsedOut, fP, fCounter, fOffset,
              hdr] <;> omega_arith⟩)]
      rw [← hQ₃]
      have h := encodeBE_decodeBE (Spec.Rsa.bytesAt t₃.mem (off E.base (sPk + g.pLen)) g.qLen)
      rw [VG.Proof.Bignum.bytesAt_length] at h
      exact h.symm
    show WP isa _ t₇ fun t => AKeep E g s t ∧ ARes E g t.mem
      (generatorResult p (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) (hList E) rest')
    unfold generatorResult
    rcases hg : Spec.Dsa.generator p (Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k)) (hList E) with _ | gv
    · -- No g: the next seed.
      rw [hg] at GR
      refine WP.seq (cmpF_end K₇.base.scr (o := fG) (v := 1) (w := 2) (by simp only [fG, hdr]; omega_arith) GR (by decide)
        (by decide) fun t₈ g₈ m₈ rd₈ wr₈ sy₈ z₈ => ?_)
      refine WP.ite _ z₈ (fun h => by simp at h) (fun _ => WP.block_nil ⟨K₇.mem m₈ (g₈ _ (by decide))
        (g₈ _ (by decide)) rd₈ wr₈ sy₈, by rw [m₈, st₇], u, hu', by rw [m₈, fu₇], du⟩)
    · -- g: the domain check.
      rw [hg] at GR
      obtain ⟨fg₇, gk₇⟩ := GR
      refine WP.seq (cmpF_end K₇.base.scr (o := fG) (v := 1) (w := 1) (by simp only [fG, hdr]; omega_arith) fg₇
        (by decide) (by decide) fun t₈ g₈ m₈ rd₈ wr₈ sy₈ z₈ => ?_)
      have K₈ := K₇.mem m₈ (g₈ _ (by decide)) (g₈ _ (by decide)) rd₈ wr₈ sy₈
      refine WP.ite _ z₈ (fun _ => ?_) (fun h => by simp at h)
      have glt := generator_lt (by omega_arith) hg
      have pq : Spec.Rsa.bytesAt t₈.mem (off E.base sPk) (2 * g.pLen + g.qLen) =
          Spec.Dsa.encodeParams g.pLen g.qLen ⟨p, Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k), gv⟩ := by
        rw [m₈, show 2 * g.pLen + g.qLen = g.pLen + (g.qLen + g.pLen) by omega_arith, bytesAt_append, bytesAt_append,
          show VG.Proof.Bignum.off (off E.base sPk) g.pLen = off E.base (sPk + g.pLen) from off_add_ofNat _ _ _,
          show VG.Proof.Bignum.off (off E.base (sPk + g.pLen)) g.qLen = off E.base (sPk + g.pLen + g.qLen)
            from off_add_ofNat _ _ _, pk₇, qk₇, gk₇, Spec.Dsa.encodeParams, List.append_assoc]
      have e256 : ∀ n, (256 : Nat) ^ n = 2 ^ (8 * n) := fun n => by rw [Nat.pow_mul]
      have ck := check_encodedParams (a := ⟨p, Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k), gv⟩)
        (pLen := g.pLen) (qLen := g.qLen)
        (by rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide)
        (by rw [e256]; exact phi) (by rw [e256]; exact qsh.2.2) (by show gv < 256 ^ g.pLen; rw [e256]; omega_arith)
      refine WP.mono (check_ok G v hp hq K₈.base) fun t₉ ⟨B₉, C₉, rd₉, wr₉, sy₉, st₉⟩ => ?_
      rw [pq, ck] at st₉
      have K₉ : AKeep E g s t₉ := ⟨B₉, K₈.chg.trans (C₉.widen fun o ho => ⟨o, by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;> simp [atRanges],
        Nat.le_refl _, Nat.le_refl _⟩), by rw [rd₉, K₈.rd], by rw [wr₉, K₈.wr], by rw [sy₉, K₈.syms]⟩
      have chkR : ∀ o ∈ [(sChk, 16 * g.pLen * 8), (fStatus, 4)], o.1 + o.2 ≤ E.size := fun o ho => by
        have room : 512 * g.pLen + 8192 ≤ E.size := hp ▸ v.room
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp only [sChk, fStatus, hdr] <;> omega_arith
      by_cases hv : Spec.Dsa.parametersValid ⟨p, Spec.Dsa.qCandidate (8 * g.qLen) (chunk E k), gv⟩
      · simp only [hv, decide_true, ↓reduceIte] at st₉ ⊢
        refine ⟨K₉, st₉, ?_⟩
        rw [Env.Chg.scratch v C₉ (by simp only [sPk]; omega_arith) (fun o ho => ⟨chkR o ho, by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;> simp only [sChk, sPk, fStatus, hdr] <;> omega_arith⟩), pq]
      · simp only [hv, decide_false, Bool.false_eq_true, ↓reduceIte] at st₉ ⊢
        refine ⟨K₉, by rw [st₉, m₈, st₇], u, hu', ?_, du⟩
        rw [Env.Chg.word v C₉ (by simp only [fUsed, hdr]; omega_arith) (fun o ho => ⟨chkR o ho, by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;> simp only [sChk, fUsed, fStatus, hdr] <;> omega_arith⟩), m₈, fu₇]

end VG.Proof.Dsa.X86.Generation
