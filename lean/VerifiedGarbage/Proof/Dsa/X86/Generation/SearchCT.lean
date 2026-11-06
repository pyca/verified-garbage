module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Search
import VerifiedGarbage.Proof.Dsa.X86.Generation.AttemptCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geo
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TimingBase
import VerifiedGarbage.Proof.Dsa.X86.Generation.TimingFlags
import VerifiedGarbage.Proof.Dsa.X86.Generation.HashCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base

/-! # Two runs of the search over the seeds leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)
open VG.Proof.Dsa.Generation

/-- Before the search: `state[0]` seeds left, the cursor at 0. -/
def SIn (E : Env) (s : State) : Prop :=
  Base E s ∧ s.mem.readW (off E.base fSeedLeft) 32 = BitVec.ofNat 32 E.k0 ∧
    s.mem.readW (off E.base fC) 32 = BitVec.ofNat 32 0 ∧
    s.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0

/-- `fStatus` after the seed at the cursor. -/
def statusOf : Option (Option Spec.Dsa.Params × Spec.RsaKeyGen.Rand) → Nat
  | none => 2
  | some (none, _) => 0
  | some (some _, _) => 1

theorem ARes.status {E : Env} {g : Geo} {m : Mem} {R : Option (Option Spec.Dsa.Params × Spec.RsaKeyGen.Rand)}
    (h : ARes E g m R) : m.readW (off E.base fStatus) 32 = BitVec.ofNat 32 (statusOf R) := by
  rcases R with _ | ⟨_ | _, _⟩
  · exact h
  · exact h.1
  · exact h.1

theorem search_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen) :
    RelCT isa (Both fun (_ : Unit) => SIn E) g.search fun _ _ => True := by
  have sz := v.size_ge
  have lens := v.witLen32
  have bd := G.bounds
  let I : Nat → State → State → Prop := fun n => Both fun (a : Nat × Nat) t =>
    (∃ σ, SLoop E g σ a.1 a.2 t) ∧ a.1 = n
  have L₀ : ∀ s, SIn E s → SLoop E g s E.k0 0 s := fun s ⟨B, hL, hC, hst⟩ =>
    ⟨⟨B, Env.Chg.refl _ _, rfl, rfl, rfl⟩, hL, hC, hst, Nat.zero_le _, v.k0le,
      by simp [Spec.Entropy.Result.consume], rfl⟩
  unfold Geo.search
  refine (RelCT.loop (M := isa) (Q := fun _ _ => True) I (fun n => ?_) E.k0).mono
    (fun s t ⟨_, h₁, h₂⟩ => ⟨(E.k0, 0), ⟨⟨s, L₀ s h₁⟩, rfl⟩, ⟨t, L₀ t h₂⟩, rfl⟩) fun _ _ h => h
  refine both_exists fun a => ?_
  obtain ⟨j, c⟩ := a
  refine relct_of_fact (fun s t h => (⟨h.1.2, by obtain ⟨⟨σ, L⟩, _⟩ := h.1; exact L.hj,
    by obtain ⟨⟨σ, L⟩, _⟩ := h.1; exact L.hc⟩ : j = n ∧ j ≤ Spec.Dsa.parameterSeeds ∧ c ≤ E.witLen))
    fun ⟨hjn, hjs, hcw⟩ => ?_
  let J : State → Prop := fun t => (∃ σ, SLoop E g σ j c t) ∧ j = n
  have hbJ : ∀ (_ : Unit) t, J t → Base E t := fun _ t h => by
    obtain ⟨⟨σ, L⟩, _⟩ := h; exact L.keep.base
  have jl : j < 2 ^ 32 := by simp only [Spec.Dsa.parameterSeeds] at hjs; omega
  have pins : ∀ {Φ : Unit → State → Prop}, (∀ u t, Φ u t → Base E t) →
      ∀ s t, Both Φ s t → VG.X86.Taint.Agree (τr [.esp, .edi]) s t := fun hb s t ⟨u, h₁, h₂⟩ =>
    agree_regs fun r hr => (base_pins (hb u s h₁) r hr).trans (base_pins (hb u t h₂) r hr).symm
  have tr : RelCT isa (fun s t => J s ∧ J t)
      (seqs [.block (cmpF fSeedLeft 0),
        .ite .e (.block (stImm fStatus 3))
          (seqs [.block (Geo.avail ++ ([.alu .cmp .eax (.imm (BitVec.ofNat 32 g.qLen))] : List Instr)),
            .ite .b (.block (stImm fStatus 2))
              (seqs [.block g.seedStart, g.attempt, .block (cmpF fStatus 0),
                .ite .e (.block Geo.rejected) (.block [])])]),
        .block (cmpF fStatus 0)]) fun _ _ => True := by
    refine (show RelCT isa (Both fun (_ : Unit) t => J t) _ _ from ?_).mono (fun s t h => ⟨(), h.1, h.2⟩)
      fun _ _ h => h
    simp only [seqs]
    refine RelCT.assoc (RelCT.seq (cmpF_ct (o := fSeedLeft) (v := 0) (by simp only [fSeedLeft, hdr]; omega)
      (by decide) (fun _ => j) hbJ (fun _ t h => by obtain ⟨⟨σ, L⟩, _⟩ := h; exact L.left)
      (fun _ => jl) (Q := VG.X86.Taint.Agree (τr [.esp, .edi])) ?_ ?_)
      (tcheckE _ _ (.block (cmpF 0 0)) (cmpF_erase _ _) (by decide +kernel) (by decide +kernel)))
    · -- None left.
      exact (tkeep [.esp, .edi] _ (by decide +kernel)).mono (pins fun _ t h => h.1.base hbJ) fun _ _ h => h
    -- The octets left.
    let Φ₁ : Unit → State → Prop := fun _ t => CmpAfter (fun (_ : Unit) t => J t) () t ∧ decide (j = 0) = false
    have b₁ : ∀ u t, Φ₁ u t → Base E t := fun _ t h => h.1.base hbJ
    have c₁ : ∀ u t, Φ₁ u t → t.mem.readW (off E.base fC) 32 = BitVec.ofNat 32 c := fun _ t h => by
      obtain ⟨s, ⟨⟨σ, L⟩, _⟩, m, -⟩ := h.1.elim; rw [m]; exact L.cur
    let Ψ₁ : Unit → State → Prop := fun _ t => ∃ s, Φ₁ () s ∧ Base E t ∧ t.mem = s.mem ∧
      isa.eval .b t = some (decide (E.witLen - c < g.qLen))
    refine RelCT.seq (both_post (Ψ := Ψ₁) (both_agree [.esp, .edi] (fun _ => baseVal E)
      (fun u t h => base_pins (b₁ u t h)) ?_) fun u t h => ?_) ?_
    · rcases G.lengths with ⟨_, h₂⟩ | ⟨_, h₂⟩ | ⟨_, h₂⟩ <;> rw [h₂] <;> exact tcheck _ _ (by decide +kernel)
    · rw [← List.append_nil (Geo.avail ++ _), List.append_assoc]
      exact availCmp_ok v (b₁ u t h) (c₁ u t h) hcw (w := g.qLen) (by omega)
        fun t' g' m' rd' wr' sy' _ cf' => WP.block_nil ⟨t, h, (b₁ u t h).regs m' (g' _ (by decide) (by decide))
          (g' _ (by decide) (by decide)) rd' wr' sy', m', cf'⟩
    have b₂ : ∀ u t, Ψ₁ u t → Base E t := fun _ t h => by obtain ⟨_, _, B, _⟩ := h; exact B
    refine both_ite (fun _ => decide (E.witLen - c < g.qLen)) (fun u t h => by obtain ⟨_, _, _, _, e⟩ := h; exact e)
      ((tkeep [.esp, .edi] _ (by decide +kernel)).mono (pins fun u t h => b₂ u t h.1) fun _ _ h => h) ?_
    -- A seed.
    by_cases short : E.witLen - c < g.qLen
    · exact relct_of_fact (P := False) (fun s t ⟨_, h, _⟩ => by simp [short] at h) fun f => f.elim
    have hcq : c + E.qLen ≤ E.witLen := by omega
    let Φ₂ : Unit → State → Prop := fun u t => Ψ₁ u t ∧ decide (E.witLen - c < g.qLen) = false
    have hS₂ : ∀ u t, Φ₂ u t → t.mem.readW (off E.base fC) 32 = BitVec.ofNat 32 c ∧
        t.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0 := fun _ t h => by
      obtain ⟨⟨s, h₁, _, m, _⟩, _⟩ := h
      obtain ⟨s', ⟨⟨σ, L⟩, _⟩, m', -⟩ := h₁.1.elim
      exact ⟨by rw [m, m']; exact L.cur, by rw [m, m']; exact L.status⟩
    let Ψ₂ : Unit → State → Prop := fun _ t => AIn (E.atSeed c) (0, c + E.qLen) t
    have ws : ∀ (m : Mem) {d e : Nat}, d + 4 ≤ sState → e + 4 ≤ sState → (d + 4 ≤ e ∨ e + 4 ≤ d) → ∀ y,
        (m.writeW (off E.base e) y).readW (off E.base d) 32 = m.readW (off E.base d) 32 :=
      fun m d e h₁ h₂ h y => word_store_other v m (by simp only [sState] at h₁; omega)
        (by simp only [sState] at h₂; omega) h y
    refine RelCT.seq (both_post (Ψ := Ψ₂) (both_agree [.esp, .edi] (fun _ => baseVal E)
      (fun u t h => base_pins (b₂ u t h.1)) ?_) fun u t h => ?_) ?_
    · unfold Geo.seedStart
      rcases G.lengths with ⟨_, h₂⟩ | ⟨_, h₂⟩ | ⟨_, h₂⟩ <;> rw [h₂] <;> exact tcheck _ _ (by decide +kernel)
    · obtain ⟨hc, hst⟩ := hS₂ u t h
      have B := b₂ u t h.1
      refine WP.mono (seedStart_ok v hq B hc) fun t₃ ⟨m₃, g₃, rd₃, wr₃, sy₃⟩ => ?_
      have C₃ : E.Chg [(fSeed, 4), (fUsed, 4)] t.mem t₃.mem := by
        rw [m₃]
        exact ((Env.Chg.refl _ _).store (d := fSeed) (n := 4) (by simp) (by decide) _).store (d := fUsed)
          (n := 4) (by simp) (by decide) _
      have B₃ := B.keep v C₃ (fun o ho => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp only [fSeed, fUsed, fOut, fUsedP, fWitLen, hdr] <;> omega)
        (g₃ _ (by decide) (by decide)) (g₃ _ (by decide) (by decide)) rd₃ wr₃ sy₃
      refine ⟨⟨B₃.toSeed c, by simp only [Env.atSeed]; omega, ?_, ?_, hcq⟩, ?_⟩
      · show t₃.mem.readW (off E.base fSeed) 32 =
          ((E.atSeed c).seeds + BitVec.ofNat 64 (0 * (E.atSeed c).qLen)).setWidth 32
        rw [m₃, ws _ (by simp only [fSeed, sState, hdr]; omega) (by simp only [fUsed, sState, hdr]; omega)
          (by simp only [fSeed, fUsed, hdr]; omega), Mem.readW_writeW_self32, Nat.zero_mul, BitVec.add_zero]
        rfl
      · show t₃.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (c + E.qLen)
        rw [m₃, Mem.readW_writeW_self32]
      · show t₃.mem.readW (off E.base fStatus) 32 = _
        rw [m₃, ws _ (by simp only [fStatus, sState, hdr]; omega) (by simp only [fUsed, sState, hdr]; omega)
          (by simp only [fStatus, fUsed, hdr]; omega), ws _ (by simp only [fStatus, sState, hdr]; omega)
          (by simp only [fSeed, sState, hdr]; omega) (by simp only [fStatus, fSeed, hdr]; omega), hst]
    -- The attempt.
    have v' := v.atSeed hcq
    let Ψ₃ : Unit → State → Prop := fun _ t => ∃ s, Ψ₂ () s ∧ AKeep (E.atSeed c) g s t ∧
      ARes (E.atSeed c) g t.mem (sR E c)
    have b₃ : ∀ u t, Ψ₃ u t → Base E t := fun _ t h => by obtain ⟨_, _, K, _⟩ := h; exact K.base.ofSeed
    have eR : refillAttempt g.pLen g.qLen (chunk (E.atSeed c) 0) ((E.atSeed c).witT.drop (c + E.qLen)) = sR E c := by
      simp only [chunk, Env.seedT, Env.atSeed, sR, hp, hq, Nat.zero_mul, List.drop_zero, List.take_take, Nat.min_self]
    refine RelCT.seq (both_post (Ψ := Ψ₃) (both_map (fun _ => (0, c + E.qLen)) (fun _ t h => h)
      (attempt_ct G v' hp hq)) fun u t h => ?_) ?_
    · exact WP.mono (attempt_ok G v' hp hq h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2 h.2)
        fun t' ⟨K, R⟩ => ⟨t, h, K, by rw [← eR]; exact R⟩
    refine cmpF_ct (o := fStatus) (v := 0) (by simp only [fStatus, hdr]; omega) (by decide)
      (fun _ => statusOf (sR E c)) b₃ (fun _ t h => by obtain ⟨_, _, _, R⟩ := h; exact R.status)
      (fun _ => by rcases sR E c with _ | ⟨_ | _, _⟩ <;> simp [statusOf]) ?_ ?_
    · exact (tkeep [.esp, .edi] _ (by decide +kernel)).mono (pins fun u t h => h.1.base b₃) fun _ _ h => h
    · exact (tkeep [.esp, .edi] _ (by decide +kernel)).mono (pins fun u t h => h.1.base b₃) fun _ _ h => h
  refine (tr.wpDep (F := fun _ t' => ∃ σ, isa.eval .e t' = some (sStep E j c).isSome ∧
      (∀ j' c', sStep E j c = some (j', c') → j' < j ∧ SLoop E g σ j' c' t'))
    fun s t h => ⟨?_, ?_⟩).mono (fun _ _ h => h) fun s' t' H => ?_
  · obtain ⟨⟨σ, L⟩, _⟩ := h.1
    exact WP.mono (sBody_ok G v hp hq L) fun t' ⟨z, _, h'⟩ => ⟨σ, z, h'⟩
  · obtain ⟨⟨σ, L⟩, _⟩ := h.2
    exact WP.mono (sBody_ok G v hp hq L) fun t' ⟨z, _, h'⟩ => ⟨σ, z, h'⟩
  obtain ⟨_, _, _, _, ⟨σ₁, z₁, c₁⟩, ⟨σ₂, z₂, c₂⟩⟩ := H
  refine ⟨z₁.trans z₂.symm, fun _ => trivial, fun ht => ?_⟩
  rw [z₁] at ht
  rcases hs : sStep E j c with _ | ⟨j', c'⟩
  · rw [hs] at ht; simp at ht
  obtain ⟨hj, L₁⟩ := c₁ j' c' hs
  obtain ⟨_, L₂⟩ := c₂ j' c' hs
  exact ⟨j', by omega, (j', c'), ⟨⟨σ₁, L₁⟩, rfl⟩, ⟨σ₂, L₂⟩, rfl⟩

end VG.Proof.Dsa.X86.Generation
