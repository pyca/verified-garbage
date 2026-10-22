module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PPart
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.Syms

/-! # Two runs of p's search from the same seed and q leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)
open VG.Proof.Dsa.Generation

/-- The next counter: its flag, and what it keeps. -/
theorem pAdv_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {t : State} (B : Base E t) {c : Nat}
    (hc : c < 4 * (8 * g.pLen))
    (counter : t.mem.readW (off E.base fCounter) 32 = BitVec.ofNat 32 c)
    (offset : t.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 (1 + c * (g.count + 1))) :
    WP isa (.block g.pAdvance) t fun t' => isa.eval .e t' = some (decide (c + 1 = 4 * (8 * g.pLen))) ∧
      Base E t' ∧ ∀ d, d + 4 ≤ sState → (d + 4 ≤ fCounter ∨ fOffset + 4 ≤ d) →
        t'.mem.readW (off E.base d) 32 = t.mem.readW (off E.base d) 32 := by
  have sz := v.size_ge
  have bd := G.bounds
  have cnt : g.count + 1 ≤ 12 := by
    unfold Geo.count; rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
  have cm : c * (g.count + 1) ≤ 12288 * 12 := Nat.mul_le_mul (by omega) cnt
  have cs : (c + 1) * (g.count + 1) = c * (g.count + 1) + (g.count + 1) := Nat.succ_mul _ _
  have wst : ∀ (m : Mem) {d e : Nat}, d + 4 ≤ sState → e + 4 ≤ sState → (d + 4 ≤ e ∨ e + 4 ≤ d) → ∀ x,
      (m.writeW (off E.base e) x).readW (off E.base d) 32 = m.readW (off E.base d) 32 :=
    fun m d e h₁ h₂ h x => word_store_other v m (by simp only [sState] at h₁; omega)
      (by simp only [sState] at h₂; omega) h x
  unfold Geo.pAdvance
  refine ld_ok B.scr (d := fCounter) (by simp only [fCounter, hdr]; omega) fun t₃ u₃ =>
    wp_addi fun t₄ u₄ => st_ok (Scr.of_eq B.scr (by rw [u₄.other _ (by decide), u₃.other _ (by decide)])
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]) (by rw [u₄.wr, u₃.wr])) (d := fCounter)
      (by simp only [fCounter, hdr]; omega) fun t₅ M₅ => ?_
  have eax₄ : t₄.gpr .eax = BitVec.ofNat 32 (c + 1) := by
    rw [u₄.gpr, u₃.gpr, counter, BitVec.ofNat_add]; rfl
  have m₅ : t₅.mem = t.mem.writeW (off E.base fCounter) (BitVec.ofNat 32 (c + 1)) := by
    rw [M₅.mem, u₄.mem, u₃.mem, eax₄]
  have hs₅ : Scr t₅ E.base E.size := Scr.of_eq B.scr (by rw [M₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide)])
    (by rw [M₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide)]) (by rw [M₅.wr, u₄.wr, u₃.wr])
  refine ld_ok hs₅ (d := fOffset) (by simp only [fOffset, hdr]; omega) fun t₆ u₆ =>
    wp_addi fun t₇ u₇ => st_ok (Scr.of_eq hs₅ (by rw [u₇.other _ (by decide), u₆.other _ (by decide)])
      (by rw [u₇.other _ (by decide), u₆.other _ (by decide)]) (by rw [u₇.wr, u₆.wr])) (d := fOffset)
      (by simp only [fOffset, hdr]; omega) fun t₈ M₈ => wp_cmpi fun t₉ f₉ _ z₉ => WP.block_nil ?_
  have ecx₇ : t₇.gpr .ecx = BitVec.ofNat 32 (1 + (c + 1) * (g.count + 1)) := by
    rw [u₇.gpr, u₆.gpr, m₅, wst _ (by simp only [fOffset, sState, hdr]; omega)
      (by simp only [fCounter, sState, hdr]; omega) (by simp only [fOffset, fCounter, hdr]; omega),
      offset, ← BitVec.ofNat_add, cs, Nat.add_assoc]
  have m₉ : t₉.mem = (t.mem.writeW (off E.base fCounter) (BitVec.ofNat 32 (c + 1))).writeW (off E.base fOffset)
      (BitVec.ofNat 32 (1 + (c + 1) * (g.count + 1))) := by rw [f₉.mem, M₈.mem, u₇.mem, u₆.mem, ecx₇, m₅]
  have g₉ : ∀ r, r ≠ .eax → r ≠ .ecx → t₉.gpr r = t.gpr r := fun r h₁ h₂ => by
    rw [f₉.gpr, M₈.gpr, u₇.other r h₂, u₆.other r h₂, M₅.gpr, u₄.other r h₁, u₃.other r h₁]
  refine ⟨?_, B.keep v (os := [(fCounter, 4), (fOffset, 4)]) ?_ (fun o ho => ?_) (g₉ _ (by decide) (by decide))
    (g₉ _ (by decide) (by decide)) (by rw [f₉.rd, M₈.rd, u₇.rd, u₆.rd, M₅.rd, u₄.rd, u₃.rd])
    (by rw [f₉.wr, M₈.wr, u₇.wr, u₆.wr, M₅.wr, u₄.wr, u₃.wr])
    (by rw [f₉.syms, M₈.syms, u₇.syms, u₆.syms, M₅.syms, u₄.syms, u₃.syms]), fun d h₁ h₂ => ?_⟩
  · show t₉.zf = _
    rw [z₉, M₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), M₅.gpr, eax₄,
      show (BitVec.ofNat 32 (32 * g.pLen) : BitVec 32) = BitVec.ofNat 32 (4 * (8 * g.pLen)) by congr 1; omega,
      sub_beq (by omega) (by omega)]
  · rw [m₉]
    exact ((Env.Chg.refl _ _).store (List.mem_cons_self) (by decide) _).store
      (List.mem_cons_of_mem _ List.mem_cons_self) (by decide) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> simp only [fCounter, fOffset, fOut, fHs, fWitLen, hdr] <;> omega
  · rw [m₉, wst _ h₁ (by simp only [fOffset, sState, hdr]; omega) (by simp only [fOffset, fCounter, hdr] at h₂ ⊢; omega),
      wst _ h₁ (by simp only [fCounter, sState, hdr]; omega) (by simp only [fOffset, fCounter, hdr] at h₂ ⊢; omega)]

/-- `fP` after counter `c`'s candidate, from `u` witness octets read. -/
def fpA (g : Geo) (E : Env) (k Q c u : Nat) : Nat :=
  if pcand g E k (1 + c * (g.count + 1)) Q < 2 ^ (8 * g.pLen - 1) then 4
  else pCode (Spec.Dsa.probablePrime (pcand g E k (1 + c * (g.count + 1)) Q) (E.witT.drop u))

/-- The witness octets read after counter `c`'s candidate. -/
def usedA (g : Geo) (E : Env) (k Q c u : Nat) : Nat :=
  if pcand g E k (1 + c * (g.count + 1)) Q < 2 ^ (8 * g.pLen - 1) then u
  else nextUsed E.witLen u (Spec.Dsa.probablePrime (pcand g E k (1 + c * (g.count + 1)) Q) (E.witT.drop u))

/-- `fP` at the end of counter `c`. -/
def fpEnd (g : Geo) (E : Env) (k Q c u : Nat) : Nat :=
  if fpA g E k Q c u = 4 then (if c + 1 = 4 * (8 * g.pLen) then 2 else 4) else fpA g E k Q c u

theorem fpA_lt (g : Geo) (E : Env) (k Q c u : Nat) : fpA g E k Q c u < 2 ^ 32 := by
  unfold fpA pCode
  split
  · decide
  · split <;> (try split) <;> decide

theorem pAdvance_erase (g : Geo) : Code.erase (.block g.pAdvance) = Code.erase (.block
    [.mov .eax (.mem (sc fCounter)), .alu .add .eax (.imm 1), .store (sc fCounter) .eax,
      .mov .ecx (.mem (sc fOffset)), .alu .add .ecx (.imm 0), .store (sc fOffset) .ecx,
      .alu .cmp .eax (.imm 0)]) := rfl

/-- After counter `c`'s candidate, from the loop's head `s`. -/
def PAfter (E : Env) (g : Geo) (k Q : Nat) (R : Option (Option Nat × Spec.RsaKeyGen.Rand)) (a : Nat × Nat)
    (t : State) : Prop :=
  ∃ s, (∃ σ, PLoop E g k Q R σ a.1 a.2 s) ∧ a.1 < 4 * (8 * g.pLen) ∧
    PAPost E g k (1 + a.1 * (g.count + 1)) Q a.2 s t

/-- The counter's words through its candidate. -/
theorem PAfter.words {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {k Q : Nat}
    {R : Option (Option Nat × Spec.RsaKeyGen.Rand)} {a : Nat × Nat} {t : State} (h : PAfter E g k Q R a t) :
    t.mem.readW (off E.base fCounter) 32 = BitVec.ofNat 32 a.1 ∧
      t.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 (1 + a.1 * (g.count + 1)) := by
  obtain ⟨s, ⟨σ, L⟩, _, A⟩ := h
  have sz := v.size_ge
  have Apa := paRanges_apart G v
  have word₁ : ∀ d, d + 4 ≤ fP → fRes + 4 ≤ d →
      t.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 := fun d h₁ h₂ =>
    Env.Chg.word v A.chg (by simp only [fP, hdr] at h₁; omega) (fun o ho => ⟨(Apa o ho).1, by
      simp only [paRanges, pxRanges, aRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [sState, sX, arr, sPk, sPP, ppWords, fRes, fUsed, fUsedOut, fP, hdr] at h₁ h₂ ⊢ <;> omega⟩)
  exact ⟨by rw [word₁ fCounter (by simp only [fCounter, fP, hdr]; omega) (by simp only [fCounter, fRes, hdr]; omega),
      L.counter],
    by rw [word₁ fOffset (by simp only [fOffset, fP, hdr]; omega) (by simp only [fOffset, fRes, hdr]; omega),
      L.offset]⟩

/-- The rest of a counter but its last comparison: `fP` and the witnesses read. -/
theorem pMid_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {k Q : Nat}
    {R : Option (Option Nat × Spec.RsaKeyGen.Rand)} {a : Nat × Nat} {t : State} (h : PAfter E g k Q R a t) :
    WP isa (.seq (.block (cmpF fP 4)) (.ite .e (seqs [.block g.pAdvance, .ite .e (.block (stImm fP 2)) (.block [])])
      (.block []))) t fun t' => Base E t' ∧
      t'.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 (fpEnd g E k Q a.1 a.2) ∧
      t'.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (usedA g E k Q a.1 a.2) := by
  have sz := v.size_ge
  obtain ⟨cw, ow⟩ := h.words G v
  obtain ⟨s, _, hc, A⟩ := h
  have hU : t.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (usedA g E k Q a.1 a.2) := A.used
  refine WP.seq (cmpF_end A.base.scr (o := fP) (v := 4) (w := fpA g E k Q a.1 a.2) (by simp only [fP, hdr]; omega)
    A.fp (fpA_lt _ _ _ _ _ _) (by decide) fun t₂ g₂ m₂ rd₂ wr₂ sy₂ z₂ => ?_)
  have B₂ := A.base.regs m₂ (g₂ _ (by decide)) (g₂ _ (by decide)) rd₂ wr₂ sy₂
  refine WP.ite _ z₂ (fun h4 => ?_) (fun h4 => WP.block_nil ⟨B₂, ?_, by rw [m₂, hU]⟩)
  · have F4 : fpA g E k Q a.1 a.2 = 4 := of_decide_eq_true h4
    simp only [seqs]
    refine WP.seq (WP.mono (pAdv_ok G v B₂ hc (by rw [m₂]; exact cw) (by rw [m₂]; exact ow)) fun t₃ ⟨z₃, B₃, w₃⟩ => ?_)
    have fP₃ : t₃.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 4 := by
      rw [w₃ fP (by simp only [fP, sState, hdr]; omega) (.inr (by simp only [fP, fOffset, hdr]; omega)), m₂, A.fp]
      exact congrArg _ F4
    have fU₃ : t₃.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (usedA g E k Q a.1 a.2) := by
      rw [w₃ fUsed (by simp only [fUsed, sState, hdr]; omega) (.inl (by simp only [fUsed, fCounter, hdr]; omega)), m₂,
        hU]
    refine WP.ite _ z₃ (fun hd => stImm_end B₃.scr (o := fP) (v := 2) (by simp only [fP, hdr]; omega)
      fun t₄ g₄ m₄ rd₄ wr₄ sy₄ => ⟨?_, ?_, ?_⟩) (fun hd => WP.block_nil ⟨B₃, ?_, fU₃⟩)
    · have C : E.Chg [(fP, 4)] t₃.mem t₄.mem := by
        rw [m₄]; exact (Env.Chg.refl _ _).store (List.mem_singleton_self _) (by decide) _
      have Ap : E.Apart [(fP, 4)] := fun o ho => by
        simp only [List.mem_singleton] at ho; subst ho; simp only [fP, fOut, fHs, fWitLen, hdr]; omega
      exact B₃.keep v C Ap (g₄ _ (by decide)) (g₄ _ (by decide)) rd₄ wr₄ sy₄
    · rw [m₄, Mem.readW_writeW_self32]
      simp only [fpEnd, F4, of_decide_eq_true hd, ↓reduceIte]
    · rw [m₄, word_store_other v _ (by simp only [fUsed, hdr]; omega) (by simp only [fP, hdr]; omega)
        (by simp only [fUsed, fP, hdr]; omega), fU₃]
    · rw [fP₃]
      simp only [fpEnd, F4, of_decide_eq_false hd, ↓reduceIte]
  · rw [m₂, A.fp]
    simp only [fpEnd, of_decide_eq_false h4, ↓reduceIte]
    rfl

/-- Two runs of a counter from the same head: the loop's flag and the witnesses
read agree. -/
theorem pBody_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen) {k Q : Nat}
    {R : Option (Option Nat × Spec.RsaKeyGen.Rand)} (hk : (k + 1) * E.qLen ≤ E.seedsLen) (hQ0 : 0 < Q) :
    RelCT isa (Both fun (a : Nat × Nat) t => (∃ σ, PLoop E g k Q R σ a.1 a.2 t) ∧ a.1 < 4 * (8 * g.pLen))
      (seqs [g.pAttempt, .block (cmpF fP 4),
        .ite .e (seqs [.block g.pAdvance, .ite .e (.block (stImm fP 2)) (.block [])]) (.block []),
        .block (cmpF fP 4)])
      (Both fun (a : Nat × Nat) t => isa.eval .e t = some (decide (fpEnd g E k Q a.1 a.2 = 4)) ∧
        t.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (usedA g E k Q a.1 a.2)) := by
  have sz := v.size_ge
  have bd := G.bounds
  have cnt : g.count + 1 ≤ 12 := by
    unfold Geo.count; rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
  simp only [seqs]
  -- The candidate.
  refine RelCT.seq (both_post (Ψ := PAfter E g k Q R)
    (both_map (fun a => (k, 1 + a.1 * (g.count + 1), Q, a.2)) (fun a t h => by
      obtain ⟨⟨σ, L⟩, hc⟩ := h
      have cm : a.1 * (g.count + 1) ≤ 12288 * 12 := Nat.mul_le_mul (by omega) cnt
      exact ⟨L.keep.base, hk, L.keep.seed, L.offset, by show 1 + a.1 * (g.count + 1) + g.count + 256 ≤ 2 ^ 32; omega,
        L.keep.q, hQ0, L.used, L.hu, L.fp⟩)
      (pAttempt_ct G v hq))
    fun a t h => by
      obtain ⟨⟨σ, L⟩, hc⟩ := h
      have cm : a.1 * (g.count + 1) ≤ 12288 * 12 := Nat.mul_le_mul (by omega) cnt
      exact WP.mono (pAttempt_ok G v hq L.keep.base hk L.keep.seed L.offset (by omega) L.keep.q hQ0 L.used L.hu L.fp)
        fun u A => ⟨t, ⟨σ, L⟩, hc, A⟩) ?_
  -- Still searching or not, and the next counter.
  have hbA : ∀ a t, PAfter E g k Q R a t → Base E t := fun a t h => by obtain ⟨_, _, _, A⟩ := h; exact A.base
  refine RelCT.assoc (RelCT.seq (both_post (Ψ := fun (a : Nat × Nat) t => Base E t ∧
      t.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 (fpEnd g E k Q a.1 a.2) ∧
      t.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (usedA g E k Q a.1 a.2))
    (cmpF_ct (by simp only [fP, hdr]; omega) (by decide) (fun a => fpA g E k Q a.1 a.2) hbA
      (fun a t h => by obtain ⟨_, _, _, A⟩ := h; exact A.fp) (fun a => fpA_lt _ _ _ _ _ _) ?_
      (RelCT.nil fun _ _ _ => trivial))
    fun a t h => pMid_ok G v h) ?_)
  · refine RelCT.seq (both_post (Ψ := fun (a : Nat × Nat) t =>
        isa.eval .e t = some (decide (a.1 + 1 = 4 * (8 * g.pLen))) ∧
        Base E t)
      (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => base_pins (h.1.base hbA))
        (tcheckE _ _ _ (pAdvance_erase g) (by decide +kernel) (by decide +kernel)))
      fun a t h => by
        obtain ⟨⟨s, hs, gs, ms, rds, wrs, sys⟩, _⟩ := h
        obtain ⟨cw, ow⟩ := hs.words G v
        obtain ⟨_, _, hc, _⟩ := id hs
        exact WP.mono (pAdv_ok G v ((hbA a s hs).regs ms (gs _ (by decide)) (gs _ (by decide)) rds wrs sys) hc
          (by rw [ms]; exact cw) (by rw [ms]; exact ow)) fun u ⟨z, B, _⟩ => ⟨z, B⟩) ?_
    exact both_ite (fun a => decide (a.1 + 1 = 4 * (8 * g.pLen))) (fun a t h => h.1)
      (stImm_ct (fun a t h => h.1.2) _ _) (RelCT.nil fun _ _ _ => trivial)
  -- The loop's flag.
  refine both_post (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => base_pins h.1)
    (tcheckE _ _ (.block (cmpF 0 0)) (cmpF_erase _ _) (by decide +kernel) (by decide +kernel)))
    fun a t h => cmpF_end h.1.scr (o := fP) (v := 4) (by simp only [fP, hdr]; omega) h.2.1 ?_ (by decide)
      fun u _ m _ _ _ z => ⟨z, by rw [m]; exact h.2.2⟩
  unfold fpEnd
  split
  · split <;> decide
  · exact fpA_lt _ _ _ _ _ _

/-- Before p's search: seed `a.1`, q `a.2.1`, the witness cursor at `a.2.2`. -/
def PPIn (E : Env) (g : Geo) (a : Nat × Nat × Nat) (s : State) : Prop :=
  Base E s ∧ (a.1 + 1) * E.qLen ≤ E.seedsLen ∧
    s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (a.1 * E.qLen)).setWidth 32 ∧
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off E.base (sPk + g.pLen)) g.qLen) = a.2.1 ∧ 0 < a.2.1 ∧
    s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 a.2.2 ∧ a.2.2 ≤ E.witLen

theorem pPart_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen) :
    RelCT isa (Both (PPIn E g)) g.pPart fun _ _ => True := by
  have sz := v.size_ge
  have lens := v.lens
  refine both_exists fun a => ?_
  obtain ⟨k, Q, used⟩ := a
  refine relct_of_fact (fun s t h => (⟨h.1.2.1, h.1.2.2.2.2.1⟩ : _ ∧ _)) fun ⟨hk, hQ0⟩ => ?_
  unfold Geo.pPart
  show RelCT isa _ (.seq (.block _) (.loop _ .e)) _
  generalize hR : Spec.Dsa.primeFromSeed (8 * g.pLen) (8 * g.qLen) Q (chunk E k) (E.witT.drop used) = R
  let N := 4 * (8 * g.pLen)
  have N0 : 0 < N := by have := G.bounds; show 0 < 4 * (8 * g.pLen); omega
  let I : Nat → State → State → Prop := fun n => Both fun (cu : Nat × Nat) t =>
    (∃ σ, PLoop E g k Q R σ cu.1 cu.2 t) ∧ cu.1 < N ∧ cu.1 + n = N
  refine RelCT.seq (R := I N) ?_ ?_
  · -- The state words.
    have tr : RelCT isa (fun s t => PPIn E g (k, Q, used) s ∧ PPIn E g (k, Q, used) t)
        (.block (stImm fCounter 0 ++ stImm fOffset 1 ++ stImm fP 4)) fun _ _ => True :=
      (tcheck [.esp, .edi] _ (by decide +kernel)).mono (fun s t h => agree_regs fun r hr =>
        (base_pins h.1.1 r hr).trans (base_pins h.2.1 r hr).symm) fun _ _ h => h
    refine (tr.wpDep (F := fun σ t => PLoop E g k Q R σ 0 used t) fun s t h => ⟨?_, ?_⟩).mono (fun _ _ h => h)
      fun s' t' ⟨_, σ₁, σ₂, _, L₁, L₂⟩ => ⟨(0, used), ⟨⟨σ₁, L₁⟩, N0, by simp⟩, ⟨σ₂, L₂⟩, N0, by simp⟩
    · obtain ⟨B, _, hS, hQ, _, hU, hu⟩ := h.1
      rw [← hR]; exact pInit_ok G v B hS hQ hU hu
    · obtain ⟨B, _, hS, hQ, _, hU, hu⟩ := h.2
      rw [← hR]; exact pInit_ok G v B hS hQ hU hu
  -- The counters.
  refine RelCT.loop (M := isa) (Q := fun _ _ => True) I (fun n => ?_) N
  refine both_exists fun cu => ?_
  refine relct_of_fact (fun s t h => h.1.2.2) fun hcN => ?_
  let J : State → Prop := fun t => (∃ σ, PLoop E g k Q R σ cu.1 cu.2 t) ∧ cu.1 < N ∧ cu.1 + n = N
  have tr : RelCT isa (fun s t => J s ∧ J t) _ _ := (pBody_ct G v hq (R := R) (k := k) (Q := Q) hk hQ0).mono
    (fun s t h => by obtain ⟨⟨L₁, c₁, _⟩, L₂, _⟩ := h; exact ⟨cu, ⟨L₁, c₁⟩, L₂, c₁⟩) fun _ _ h => h
  refine (tr.wp (F₁ := fun (t' : State) => ∃ σ, (t'.zf = some false ∧ PKeep E g k Q σ t' ∧ PRes E g Q t'.mem R) ∨
      (t'.zf = some true ∧ cu.1 + 1 < 4 * (8 * g.pLen) ∧ ∃ u', PLoop E g k Q R σ (cu.1 + 1) u' t'))
    (F₂ := fun (t' : State) => ∃ σ, (t'.zf = some false ∧ PKeep E g k Q σ t' ∧ PRes E g Q t'.mem R) ∨
      (t'.zf = some true ∧ cu.1 + 1 < 4 * (8 * g.pLen) ∧ ∃ u', PLoop E g k Q R σ (cu.1 + 1) u' t'))
    fun s t h => ⟨?_, ?_⟩).mono (fun _ _ h => h) fun s' t' H => ?_
  · obtain ⟨⟨σ, L⟩, hc, _⟩ := h.1
    exact WP.mono (pBody_ok G v hq hk hQ0 L hc) fun t' h' => ⟨σ, h'⟩
  · obtain ⟨⟨σ, L⟩, hc, _⟩ := h.2
    exact WP.mono (pBody_ok G v hq hk hQ0 L hc) fun t' h' => ⟨σ, h'⟩
  obtain ⟨⟨a', ψ₁, ψ₂⟩, ⟨σ₁, F₁⟩, ⟨σ₂, F₂⟩⟩ := H
  refine ⟨ψ₁.1.trans ψ₂.1.symm, fun _ => trivial, fun ht => ?_⟩
  change s'.zf = some true at ht
  have ht' : t'.zf = some true := by change isa.eval .e t' = _; rw [ψ₂.1, ← ψ₁.1]; exact ht
  rcases F₁ with ⟨z₁, _⟩ | ⟨_, hc₁, u₁, L₁⟩
  · rw [ht] at z₁; cases z₁
  rcases F₂ with ⟨z₂, _⟩ | ⟨_, _, u₂, L₂⟩
  · rw [ht'] at z₂; cases z₂
  have hu : u₁ = u₂ := by
    have e : BitVec.ofNat 32 u₁ = BitVec.ofNat 32 u₂ := by rw [← L₁.used, ← L₂.used, ψ₁.2, ψ₂.2]
    have := L₁.hu
    have := L₂.hu
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  subst hu
  exact ⟨n - 1, by omega, (cu.1 + 1, u₁), ⟨⟨σ₁, L₁⟩, hc₁, by omega⟩, ⟨σ₂, L₂⟩, hc₁, by omega⟩

end VG.Proof.Dsa.X86.Generation
