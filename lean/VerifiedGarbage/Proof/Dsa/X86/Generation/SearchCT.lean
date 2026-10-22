module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Search
public import VerifiedGarbage.Proof.Dsa.X86.Generation.AttemptCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Two runs of the search over the seeds leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- Another whole seed is left. -/
theorem next_seed {E : Env} (v : E.Valid) {k : Nat} (hne : E.seedsLen - k * E.qLen ≠ 0) :
    (k + 1) * E.qLen ≤ E.seedsLen := by
  have whole : E.seedsLen = E.seedsLen / E.qLen * E.qLen :=
    (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero v.seedsWhole)).symm
  have hlt : k * E.qLen < E.seedsLen / E.qLen * E.qLen := by omega
  have := Nat.lt_of_mul_lt_mul_right hlt
  have := Nat.mul_le_mul_right E.qLen (show k + 1 ≤ E.seedsLen / E.qLen by omega)
  omega

/-- Before the search: the first seed, all of them left, no witness read. -/
def SIn (E : Env) (s : State) : Prop :=
  Base E s ∧ s.mem.readW (off E.base fSeed) 32 = E.seeds.setWidth 32 ∧
    s.mem.readW (off E.base fSeedLeft) 32 = BitVec.ofNat 32 E.seedsLen ∧
    s.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0 ∧
    s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 0

theorem search_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen) :
    RelCT isa (Both fun (_ : Unit) => SIn E) g.search fun _ _ => True := by
  have sz := v.size_ge
  have lens := v.lens
  have bd := G.bounds
  have ql : 20 ≤ E.qLen := by rw [hq]; omega
  let R := Spec.Dsa.generateParameters.attempt (8 * g.pLen) (hList E) (8 * g.qLen) (seedList E) E.witT
  let N := E.seedsLen / E.qLen + 1
  let I : Nat → State → State → Prop := fun n => Both fun (a : Nat × Nat) t =>
    (∃ σ, SLoop E g R σ a.1 a.2 t) ∧ a.1 + n = N
  have L₀ : ∀ s, SIn E s → SLoop E g R s 0 0 s := fun s ⟨B, hS, hL, hst, hU⟩ =>
    ⟨⟨B, Env.Chg.refl _ _, rfl, rfl, rfl⟩, by rw [hS, Nat.zero_mul, BitVec.add_zero],
      by rw [hL, Nat.zero_mul, Nat.sub_zero], hst, hU, Nat.zero_le _, by omega, by rw [List.drop_zero, List.drop_zero]⟩
  unfold Geo.search
  refine (RelCT.loop (M := isa) (Q := fun _ _ => True) I (fun n => ?_) N).mono
    (fun s t ⟨_, h₁, h₂⟩ => ⟨(0, 0), ⟨⟨s, L₀ s h₁⟩, by simp⟩, ⟨t, L₀ t h₂⟩, by simp⟩) fun _ _ h => h
  refine both_exists fun a => ?_
  obtain ⟨k, u⟩ := a
  refine relct_of_fact (fun s t h => h.1.2) fun hkN => ?_
  let J : State → Prop := fun t => (∃ σ, SLoop E g R σ k u t) ∧ k + n = N
  have hbJ : ∀ (_ : Unit) t, J t → Base E t := fun _ t h => by
    obtain ⟨⟨σ, L⟩, _⟩ := h; exact L.keep.base
  have tr : RelCT isa (fun s t => J s ∧ J t)
      (seqs [.block (cmpF fSeedLeft 0),
        .ite .e (.block (stImm fStatus 2))
          (seqs [g.attempt, .block [.mov .eax (.mem (sc fSeed)), .alu .add .eax (.imm (BitVec.ofNat 32 g.qLen)),
            .store (sc fSeed) .eax, .mov .eax (.mem (sc fSeedLeft)), .alu .sub .eax (.imm (BitVec.ofNat 32 g.qLen)),
            .store (sc fSeedLeft) .eax]]),
        .block (cmpF fStatus 0)]) fun _ _ => True := by
    refine (show RelCT isa (Both fun (_ : Unit) t => J t) _ _ from ?_).mono (fun s t h => ⟨(), h.1, h.2⟩)
      fun _ _ h => h
    simp only [seqs]
    refine RelCT.assoc (RelCT.seq (cmpF_ct (o := fSeedLeft) (v := 0) (by simp only [fSeedLeft, hdr]; omega)
      (by decide) (fun _ => E.seedsLen - k * E.qLen) hbJ (fun _ t h => by obtain ⟨⟨σ, L⟩, _⟩ := h; exact L.left)
      (fun _ => by omega) (Q := VG.X86.Taint.Agree (τr [.esp, .edi])) ?_ ?_)
      (tcheckE _ _ (.block (cmpF 0 0)) (cmpF_erase _ _) (by decide +kernel) (by decide +kernel)))
    · -- None left.
      exact (tkeep [.esp, .edi] _ (by decide +kernel)).mono (fun s t ⟨_, h₁, h₂⟩ => agree_regs fun r hr =>
        (base_pins (h₁.1.base hbJ) r hr).trans (base_pins (h₂.1.base hbJ) r hr).symm) fun _ _ h => h
    · -- Seed number `k`.
      have ai : ∀ (w : Unit) t, CmpAfter (fun (_ : Unit) t => J t) w t ∧
          decide (E.seedsLen - k * E.qLen = 0) = false → AIn E (k, u) t := fun w t h => by
        obtain ⟨C, hz⟩ := h
        obtain ⟨s, ⟨⟨σ, L⟩, _⟩, m, e, p_, r, w, y⟩ := C.elim
        have hne : E.seedsLen - k * E.qLen ≠ 0 := of_decide_eq_false hz
        exact ⟨⟨L.keep.base.regs m e p_ r w y, next_seed v hne, by rw [m]; exact L.seed, by rw [m]; exact L.used,
          L.hu⟩, by rw [m]; exact L.status⟩
      refine RelCT.seq (both_post (Ψ := fun _ t => Base E t)
        (both_map (fun _ => (k, u)) ai (attempt_ct G v hp hq)) fun w t h => ?_) ?_
      · obtain ⟨⟨B, hk, hS, hU, hu⟩, hst⟩ := ai w t h
        exact WP.mono (attempt_ok G v hp hq B hk hS hU hu hst) fun _ ⟨K, _⟩ => K.base
      · refine both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins h) ?_
        rcases G.lengths with ⟨_, h₂⟩ | ⟨_, h₂⟩ | ⟨_, h₂⟩ <;> rw [h₂] <;>
          exact tkeep _ _ (by decide +kernel)
  refine (tr.wpDep (F := fun _ t' => ∃ σ, isa.eval .e t' = some (sCont E g k u) ∧
      (sCont E g k u = true → (k + 1) * E.qLen ≤ E.seedsLen ∧ SLoop E g R σ (k + 1) (sNext E g k u) t'))
    fun s t h => ⟨?_, ?_⟩).mono (fun _ _ h => h) fun s' t' H => ?_
  · obtain ⟨⟨σ, L⟩, _⟩ := h.1
    exact WP.mono (sBody_ok G v hp hq L) fun t' h' => ⟨σ, by
      rcases h' with ⟨z, c, _⟩ | ⟨z, c, hk1, L'⟩
      · exact ⟨by rw [c]; exact z, fun h => absurd (c.symm.trans h) (by decide)⟩
      · exact ⟨by rw [c]; exact z, fun _ => ⟨hk1, L'⟩⟩⟩
  · obtain ⟨⟨σ, L⟩, _⟩ := h.2
    exact WP.mono (sBody_ok G v hp hq L) fun t' h' => ⟨σ, by
      rcases h' with ⟨z, c, _⟩ | ⟨z, c, hk1, L'⟩
      · exact ⟨by rw [c]; exact z, fun h => absurd (c.symm.trans h) (by decide)⟩
      · exact ⟨by rw [c]; exact z, fun _ => ⟨hk1, L'⟩⟩⟩
  obtain ⟨_, _, _, _, ⟨σ₁, z₁, c₁⟩, ⟨σ₂, z₂, c₂⟩⟩ := H
  refine ⟨z₁.trans z₂.symm, fun _ => trivial, fun ht => ?_⟩
  have hc : sCont E g k u = true := by rw [z₁] at ht; exact Option.some.inj ht
  obtain ⟨hk1, L₁⟩ := c₁ hc
  obtain ⟨_, L₂⟩ := c₂ hc
  have : k + 1 ≤ E.seedsLen / E.qLen := (Nat.le_div_iff_mul_le (by omega)).mpr hk1
  exact ⟨n - 1, by omega, (k + 1, sNext E g k u), ⟨⟨σ₁, L₁⟩, by omega⟩, ⟨σ₂, L₂⟩, by omega⟩

end VG.Proof.Dsa.X86.Generation
