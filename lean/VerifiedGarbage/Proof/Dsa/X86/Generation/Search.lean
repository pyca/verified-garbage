module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Attempt
import VerifiedGarbage.Proof.Dsa.Generation.SeedResult
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.X86.Generation.Flags
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words

/-! # The seeds in turn (A.1.1.2 step 1, the caller's retries) -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)
open VG.Proof.Dsa.Generation

/-- The seeds of the tape. -/
def seedList (E : Env) : List (List Byte) := Spec.Dsa.generationChunks E.qLen E.seedT

theorem seedList_length (E : Env) : (seedList E).length = E.seedT.length / E.qLen := by
  simp [seedList, Spec.Dsa.generationChunks]

theorem seedList_drop (E : Env) {k : Nat} (hk : k < E.seedT.length / E.qLen) :
    (seedList E).drop k = chunk E k :: (seedList E).drop (k + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [seedList_length]; exact hk)]
  simp [seedList, Spec.Dsa.generationChunks, chunk]

/-- The ranges the search changes. -/
def sRanges (g : Geo) : List (Nat × Nat) := atRanges g ++ [(fSeed, 4), (fSeedLeft, 4)]

theorem sRanges_apart {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) :
    E.Apart (sRanges g) := by
  have sz := v.size_ge
  intro o ho
  rcases List.mem_append.mp ho with h | h
  · exact atRanges_apart G v hp o h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp only [fSeed, fSeedLeft, fOut, fHs, fWitLen, hdr] <;> omega

/-- What the search keeps. -/
structure SKeep (E : Env) (g : Geo) (s t : State) : Prop where
  base : Base E t
  chg : E.Chg (sRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem SKeep.mem {E : Env} {g : Geo} {s t t' : State} (K : SKeep E g s t) (hm : t'.mem = t.mem)
    (edi : t'.gpr .edi = t.gpr .edi) (sp : t'.gpr .esp = t.gpr .esp) (rd : t'.rd = t.rd) (wr : t'.wr = t.wr)
    (sy : t'.syms = t.syms) : SKeep E g s t' :=
  ⟨K.base.regs hm edi sp rd wr sy, by rw [hm]; exact K.chg, by rw [rd, K.rd], by rw [wr, K.wr], by rw [sy, K.syms]⟩

theorem SKeep.store {E : Env} {g : Geo} {s t t' : State} (K : SKeep E g s t) (G : GeoOk g) (v : E.Valid)
    (hp : E.pLen = g.pLen) {d : Nat} (hd : (d, 4) ∈ sRanges g) (x : BitVec 32)
    (hm : t'.mem = t.mem.writeW (off E.base d) x) (edi : t'.gpr .edi = t.gpr .edi) (sp : t'.gpr .esp = t.gpr .esp)
    (rd : t'.rd = t.rd) (wr : t'.wr = t.wr) (sy : t'.syms = t.syms) : SKeep E g s t' := by
  have C : E.Chg [(d, 4)] t.mem t'.mem := by
    rw [hm]; exact (Env.Chg.refl _ _).store (List.mem_singleton_self _) (by decide) x
  exact ⟨K.base.keep v C (fun o ho => sRanges_apart G v hp o
      (by simp only [List.mem_singleton] at ho; rw [ho]; exact hd)) edi sp rd wr sy,
    K.chg.trans (C.widen fun o ho => ⟨o, by simp only [List.mem_singleton] at ho; rw [ho]; exact hd,
      Nat.le_refl _, Nat.le_refl _⟩), by rw [rd, K.rd], by rw [wr, K.wr], by rw [sy, K.syms]⟩

/-- The search's result in memory `m`. -/
def SRes (E : Env) (g : Geo) (m : Mem) : Option Spec.Dsa.Params → Prop
  | none => m.readW (off E.base fStatus) 32 = BitVec.ofNat 32 2
  | some a => m.readW (off E.base fStatus) 32 = BitVec.ofNat 32 1 ∧
      Spec.Rsa.bytesAt m (off E.base sPk) (2 * g.pLen + g.qLen) = Spec.Dsa.encodeParams g.pLen g.qLen a

/-- At the loop's head, before seed `k`. -/
structure SLoop (E : Env) (g : Geo) (R : Option Spec.Dsa.Params) (s : State) (k u : Nat) (t : State) : Prop where
  keep : SKeep E g s t
  seed : t.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32
  left : t.mem.readW (off E.base fSeedLeft) 32 = BitVec.ofNat 32 (E.seedsLen - k * E.qLen)
  status : t.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0
  used : t.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 u
  hu : u ≤ E.witLen
  hk : k * E.qLen ≤ E.seedsLen
  spec : Spec.Dsa.generateParameters.attempt (8 * g.pLen) (hList E) (8 * g.qLen) ((seedList E).drop k)
    (E.witT.drop u) = R

/-- Whether a seed's result goes on to the next seed. -/
def contOf : Option (Option Spec.Dsa.Params × Spec.RsaKeyGen.Rand) → Bool
  | some (none, _) => true
  | _ => false

/-- The witnesses a seed's result leaves. -/
def restOf : Option (Option Spec.Dsa.Params × Spec.RsaKeyGen.Rand) → Spec.RsaKeyGen.Rand
  | some (_, r) => r
  | none => []

/-- Whether the search goes on after seed `k`, from witness cursor `u`. -/
def sCont (E : Env) (g : Geo) (k u : Nat) : Bool :=
  decide (E.seedsLen - k * E.qLen ≠ 0) &&
    contOf (seedResult (8 * g.pLen) (8 * g.qLen) (chunk E k) (hList E) (E.witT.drop u))

/-- The witness cursor after seed `k`. -/
def sNext (E : Env) (g : Geo) (k u : Nat) : Nat :=
  E.witLen - (restOf (seedResult (8 * g.pLen) (8 * g.qLen) (chunk E k) (hList E) (E.witT.drop u))).length

/-- One seed: the loop exits with the search's result, or goes on. -/
theorem sBody_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {R : Option Spec.Dsa.Params} {s : State} {k u : Nat} {t : State} (L : SLoop E g R s k u t) :
    WP isa (seqs [.block (cmpF fSeedLeft 0),
      .ite .e (.block (stImm fStatus 2))
        (seqs [g.attempt, .block [.mov .eax (.mem (sc fSeed)), .alu .add .eax (.imm (BitVec.ofNat 32 g.qLen)),
          .store (sc fSeed) .eax, .mov .eax (.mem (sc fSeedLeft)), .alu .sub .eax (.imm (BitVec.ofNat 32 g.qLen)),
          .store (sc fSeedLeft) .eax]]),
      .block (cmpF fStatus 0)]) t fun t' =>
      (t'.zf = some false ∧ sCont E g k u = false ∧ SKeep E g s t' ∧ SRes E g t'.mem R) ∨
      (t'.zf = some true ∧ sCont E g k u = true ∧ (k + 1) * E.qLen ≤ E.seedsLen ∧
        SLoop E g R s (k + 1) (sNext E g k u) t') := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have hl : E.seedT.length = E.seedsLen := by rw [← L.keep.base.seeds, VG.Proof.Bignum.bytesAt_length]
  have lens := v.lens
  have ql : 20 ≤ E.qLen := by rw [hq]; omega_arith
  have whole : E.seedsLen = E.seedsLen / E.qLen * E.qLen :=
    (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero v.seedsWhole)).symm
  have ws : ∀ (m : Mem) {d e : Nat}, d + 4 ≤ sState → e + 4 ≤ sState → (d + 4 ≤ e ∨ e + 4 ≤ d) → ∀ y,
      (m.writeW (off E.base e) y).readW (off E.base d) 32 = m.readW (off E.base d) 32 :=
    fun m d e h₁ h₂ h y => word_store_other v m (by simp only [sState] at h₁; omega_arith)
      (by simp only [sState] at h₂; omega_arith) h y
  simp only [seqs]
  refine WP.seq (cmpF_end L.keep.base.scr (o := fSeedLeft) (v := 0) (by simp only [fSeedLeft, hdr]; omega_arith) L.left
    (by omega_arith) (by decide) fun t₁ g₁ m₁ rd₁ wr₁ sy₁ z₁ => ?_)
  have K₁ := L.keep.mem m₁ (g₁ _ (by decide)) (g₁ _ (by decide)) rd₁ wr₁ sy₁
  refine WP.seq (WP.ite _ z₁ (fun hz => stImm_end K₁.base.scr (o := fStatus) (v := 2)
    (by simp only [fStatus, hdr]; omega_arith) fun t₂ g₂ m₂ rd₂ wr₂ sy₂ => ?_) (fun hz => ?_))
  · -- No seed left.
    have h0 : E.seedsLen - k * E.qLen = 0 := of_decide_eq_true hz
    have K₂ := K₁.store G v hp (d := fStatus) (by simp [sRanges, atRanges]) _ m₂ (g₂ _ (by decide))
      (g₂ _ (by decide)) rd₂ wr₂ sy₂
    refine cmpF_end K₂.base.scr (o := fStatus) (v := 0) (w := 2) (by simp only [fStatus, hdr]; omega_arith)
      (by rw [m₂, Mem.readW_writeW_self32]) (by decide) (by decide) fun t₃ g₃ m₃ rd₃ wr₃ sy₃ z₃ => ?_
    refine .inl ⟨z₃, by simp [sCont, h0], K₂.mem m₃ (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃ sy₃, ?_⟩
    have hN : E.seedT.length / E.qLen ≤ k := by
      rw [hl]; exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; omega_arith)
    have hR : R = none := by
      rw [← L.spec, List.drop_eq_nil_of_le (by rw [seedList_length]; exact hN)]
      rfl
    rw [hR]; show _ = _; rw [m₃, m₂, Mem.readW_writeW_self32]
  · -- Seed number `k`.
    have hne : E.seedsLen - k * E.qLen ≠ 0 := of_decide_eq_false hz
    have hk1 : (k + 1) * E.qLen ≤ E.seedsLen := by
      have hlt : k * E.qLen < E.seedsLen / E.qLen * E.qLen := by omega_arith
      have := Nat.lt_of_mul_lt_mul_right hlt
      have := Nat.mul_le_mul_right E.qLen (show k + 1 ≤ E.seedsLen / E.qLen by omega_arith)
      omega_arith
    have hkN : k < E.seedT.length / E.qLen := by
      rw [hl]; exact Nat.lt_of_mul_lt_mul_right (a := E.qLen) (by rw [Nat.succ_mul] at hk1; omega_arith)
    refine WP.seq (WP.mono (attempt_ok G v hp hq K₁.base hk1 (by rw [m₁]; exact L.seed) (by rw [m₁]; exact L.used)
      L.hu (by rw [m₁]; exact L.status)) fun t₂ ⟨AK, AR⟩ => ?_)
    have K₂ : SKeep E g s t₂ := ⟨AK.base, K₁.chg.trans (AK.chg.widen fun o ho => ⟨o, List.mem_append_left _ ho,
      Nat.le_refl _, Nat.le_refl _⟩), by rw [AK.rd, K₁.rd], by rw [AK.wr, K₁.wr], by rw [AK.syms, K₁.syms]⟩
    have seed₂ : t₂.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32 := by
      rw [AK.word G v hp (by simp only [fSeed]; omega_arith) (by simp only [fSeed, fUsed, hdr]; omega_arith), m₁, L.seed]
    have left₂ : t₂.mem.readW (off E.base fSeedLeft) 32 = BitVec.ofNat 32 (E.seedsLen - k * E.qLen) := by
      rw [AK.word G v hp (by simp only [fSeedLeft]; omega_arith) (by simp only [fSeedLeft, fUsed, hdr]; omega_arith), m₁, L.left]
    -- The next seed.
    refine ld_ok K₂.base.scr (d := fSeed) (by simp only [fSeed, hdr]; omega_arith) fun t₃ u₃ => wp_addi fun t₄ u₄ =>
      st_ok (Scr.of_eq K₂.base.scr (by rw [u₄.other _ (by decide), u₃.other _ (by decide)])
        (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]) (by rw [u₄.wr, u₃.wr])) (d := fSeed)
        (by simp only [fSeed, hdr]; omega_arith) fun t₅ M₅ => ?_
    have m₅ : t₅.mem = t₂.mem.writeW (off E.base fSeed) ((E.seeds + BitVec.ofNat 64 ((k + 1) * E.qLen)).setWidth 32) := by
      rw [M₅.mem, u₄.mem, u₃.mem, u₄.gpr, u₃.gpr, seed₂, ← hq, ptr_add, BitVec.add_assoc, ← BitVec.ofNat_add,
        Nat.succ_mul]
    have K₅ := K₂.store G v hp (d := fSeed) (by simp [sRanges]) _ m₅
      (by rw [M₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide)])
      (by rw [M₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide)]) (by rw [M₅.rd, u₄.rd, u₃.rd])
      (by rw [M₅.wr, u₄.wr, u₃.wr]) (by rw [M₅.syms, u₄.syms, u₃.syms])
    refine ld_ok K₅.base.scr (d := fSeedLeft) (by simp only [fSeedLeft, hdr]; omega_arith) fun t₆ u₆ =>
      wp_subi fun t₇ u₇ _ _ => st_ok (Scr.of_eq K₅.base.scr (by rw [u₇.other _ (by decide), u₆.other _ (by decide)])
        (by rw [u₇.other _ (by decide), u₆.other _ (by decide)]) (by rw [u₇.wr, u₆.wr])) (d := fSeedLeft)
        (by simp only [fSeedLeft, hdr]; omega_arith) fun t₈ M₈ => WP.block_nil ?_
    have m₈ : t₈.mem = t₅.mem.writeW (off E.base fSeedLeft) (BitVec.ofNat 32 (E.seedsLen - (k + 1) * E.qLen)) := by
      rw [M₈.mem, u₇.mem, u₆.mem, u₇.gpr, u₆.gpr, m₅, ws _ (by simp only [fSeedLeft, sState, hdr]; omega_arith)
        (by simp only [fSeed, sState, hdr]; omega_arith) (by simp only [fSeed, fSeedLeft, hdr]; omega_arith), left₂, ← hq,
        sub_ofNat (by rw [Nat.succ_mul] at hk1; omega_arith), Nat.succ_mul, Nat.sub_sub]
    have K₈ := K₅.store G v hp (d := fSeedLeft) (by simp [sRanges]) _ m₈
      (by rw [M₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide)])
      (by rw [M₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide)]) (by rw [M₈.rd, u₇.rd, u₆.rd])
      (by rw [M₈.wr, u₇.wr, u₆.wr]) (by rw [M₈.syms, u₇.syms, u₆.syms])
    have w₈ : ∀ d, d + 4 ≤ sState → (d + 4 ≤ fSeed ∨ fSeedLeft + 4 ≤ d) →
        t₈.mem.readW (off E.base d) 32 = t₂.mem.readW (off E.base d) 32 := fun d h₁ h₂ => by
      rw [m₈, ws _ h₁ (by simp only [fSeedLeft, sState, hdr]; omega_arith)
        (by simp only [fSeed, fSeedLeft, hdr] at h₂ ⊢; omega_arith), m₅,
        ws _ h₁ (by simp only [fSeed, sState, hdr]; omega_arith) (by simp only [fSeed, fSeedLeft, hdr] at h₂ ⊢; omega_arith)]
    have spec := L.spec
    rw [seedList_drop E hkN, VG.Proof.Dsa.Generation.parameterAttempt_seedResult _ _ _ _ _ _
      (by rw [chunk_length L.keep.base hk1, hq])] at spec
    obtain ⟨SR, hSR⟩ : ∃ SR, seedResult (8 * g.pLen) (8 * g.qLen) (chunk E k) (hList E) (E.witT.drop u) = SR :=
      ⟨_, rfl⟩
    rw [hSR] at AR spec
    have st₈ : ∀ F, t₂.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 F →
        t₈.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 F := fun F h => by
      rw [w₈ fStatus (by simp only [fStatus, sState, hdr]; omega_arith) (.inr (by simp only [fStatus, fSeedLeft, hdr]; omega_arith)),
        h]
    rcases SR with _ | ⟨_ | a, rest⟩
    · -- A tape ran out.
      refine cmpF_end K₈.base.scr (o := fStatus) (v := 0) (w := 2) (by simp only [fStatus, hdr]; omega_arith)
        (st₈ 2 AR) (by decide) (by decide) fun t₉ g₉ m₉ rd₉ wr₉ sy₉ z₉ =>
          .inl ⟨z₉, by simp [sCont, hSR, contOf], K₈.mem m₉ (g₉ _ (by decide)) (g₉ _ (by decide)) rd₉ wr₉ sy₉, ?_⟩
      rw [← spec]; show _ = _; rw [m₉, st₈ 2 AR]
    · -- On to the next seed.
      obtain ⟨st₂, u', hu', fu₂, du⟩ := AR
      have wl : E.witT.length = E.witLen := by rw [← L.keep.base.wit, VG.Proof.Bignum.bytesAt_length]
      have hu'' : u' = sNext E g k u := by
        have := congrArg List.length du
        rw [List.length_drop, wl] at this
        simp only [sNext, hSR, restOf]
        omega_arith
      subst hu''
      refine cmpF_end K₈.base.scr (o := fStatus) (v := 0) (w := 0) (by simp only [fStatus, hdr]; omega_arith)
        (st₈ 0 st₂) (by decide) (by decide) fun t₉ g₉ m₉ rd₉ wr₉ sy₉ z₉ =>
          .inr ⟨z₉, by simp [sCont, hne, hSR, contOf], hk1, ?_⟩
      refine ⟨K₈.mem m₉ (g₉ _ (by decide)) (g₉ _ (by decide)) rd₉ wr₉ sy₉, ?_, ?_, by rw [m₉, st₈ 0 st₂], ?_, hu',
        hk1, by rw [du]; exact spec⟩
      · rw [m₉, m₈, ws _ (by simp only [fSeed, sState, hdr]; omega_arith) (by simp only [fSeedLeft, sState, hdr]; omega_arith)
          (by simp only [fSeed, fSeedLeft, hdr]; omega_arith), m₅, Mem.readW_writeW_self32]
      · rw [m₉, m₈, Mem.readW_writeW_self32]
      · rw [m₉, w₈ fUsed (by simp only [fUsed, sState, hdr]; omega_arith) (.inr (by simp only [fUsed, fSeedLeft, hdr]; omega_arith)),
          fu₂]
    · -- A domain.
      obtain ⟨st₂, pk₂⟩ := AR
      refine cmpF_end K₈.base.scr (o := fStatus) (v := 0) (w := 1) (by simp only [fStatus, hdr]; omega_arith)
        (st₈ 1 st₂) (by decide) (by decide) fun t₉ g₉ m₉ rd₉ wr₉ sy₉ z₉ =>
          .inl ⟨z₉, by simp [sCont, hSR, contOf], K₈.mem m₉ (g₉ _ (by decide)) (g₉ _ (by decide)) rd₉ wr₉ sy₉, ?_⟩
      rw [← spec]
      refine ⟨by rw [m₉, st₈ 1 st₂], ?_⟩
      rw [m₉, m₈, Env.Chg.scratch v ((Env.Chg.refl [(fSeedLeft, 4)] t₅.mem).store (List.mem_singleton_self _)
        (by decide) _) (by simp only [sPk]; omega_arith) (fun o ho => by
          simp only [List.mem_singleton] at ho; subst ho; simp only [fSeedLeft, sPk, hdr]; omega_arith), m₅,
        Env.Chg.scratch v ((Env.Chg.refl [(fSeed, 4)] t₂.mem).store (List.mem_singleton_self _)
        (by decide) _) (by simp only [sPk]; omega_arith) (fun o ho => by
          simp only [List.mem_singleton] at ho; subst ho; simp only [fSeed, sPk, hdr]; omega_arith), pk₂]

/-- The seeds from the first, until a domain passes or a tape runs out. -/
theorem search_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s : State} (B : Base E s)
    (hS : s.mem.readW (off E.base fSeed) 32 = E.seeds.setWidth 32)
    (hL : s.mem.readW (off E.base fSeedLeft) 32 = BitVec.ofNat 32 E.seedsLen)
    (hst : s.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0)
    (hU : s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 0) :
    WP isa g.search s fun t => SKeep E g s t ∧
      SRes E g t.mem (Spec.Dsa.generateParameters.attempt (8 * g.pLen) (hList E) (8 * g.qLen) (seedList E) E.witT) := by
  have lens := v.lens
  have ql : 20 ≤ E.qLen := by have := G.bounds; rw [hq]; omega
  have L₀ : SLoop E g (Spec.Dsa.generateParameters.attempt (8 * g.pLen) (hList E) (8 * g.qLen) (seedList E) E.witT)
      s 0 0 s := ⟨⟨B, Env.Chg.refl _ _, rfl, rfl, rfl⟩, by rw [hS, Nat.zero_mul, BitVec.add_zero], by rw [hL, Nat.zero_mul,
        Nat.sub_zero], hst, hU, Nat.zero_le _, by omega, by rw [List.drop_zero, List.drop_zero]⟩
  unfold Geo.search
  refine WP.loop (M := isa) (fun m t => ∃ k u, k + m = E.seedsLen / E.qLen + 1 ∧
      SLoop E g (Spec.Dsa.generateParameters.attempt (8 * g.pLen) (hList E) (8 * g.qLen) (seedList E) E.witT) s k u t)
    (fun m t ⟨k, u, hm, L⟩ => WP.mono (sBody_ok G v hp hq L) fun t' h => ?_) (E.seedsLen / E.qLen + 1) s
    ⟨0, 0, by omega, L₀⟩
  rcases h with ⟨z, _, K, res⟩ | ⟨z, _, hk1, L'⟩
  · exact .inl ⟨z, K, res⟩
  · have : k + 1 ≤ E.seedsLen / E.qLen := (Nat.le_div_iff_mul_le (by omega)).mpr hk1
    exact .inr ⟨z, m - 1, by omega, k + 1, _, by omega, L'⟩

end VG.Proof.Dsa.X86.Generation
