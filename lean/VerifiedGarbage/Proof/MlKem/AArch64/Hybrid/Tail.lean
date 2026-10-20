module
public import Mathlib.Tactic.IntervalCases
public import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

meta import VerifiedGarbage.Proof.MlKem.AArch64.Encaps

/-!
# The hashing encapsulation after the matrix

`tailH_ok`: `H(ek)`, the first 32 bytes of the third state, into `HB`, and
`G(m ‖ H(ek))` (`Hybrid.tailH`), with `Â` stored with 16 bits (`w16`) or 32.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Encaps
open VG.Spec.Sha3 (stateAt bytesAt squeezeFrom)
open VG.Spec.MlKem
open VG.Proof.MlKem

variable {P : KemLay}

/-- The first 32 bytes of a state in memory are the first 32 bytes it squeezes. -/
theorem bytesAt_squeeze (m : Mem) (p : Addr) : bytesAt m p 32 = squeezeFrom 136 (stateAt m p) 0 32 := by
  apply List.ext_getElem
  · rw [bytesAt_length, Proof.Sha3.length_squeezeFrom (by decide) (by decide)]
  · intro i h1 h2
    have hi : i < 32 := by simpa only [bytesAt_length] using h1
    rw [Proof.Sha3.squeezeFrom_getElem (by decide) (by decide) _ hi, Nat.zero_add,
      Nat.div_eq_of_lt (by omega : i < 136), Nat.mod_eq_of_lt (by omega : i < 136)]
    show _ = Proof.Sha3.byteOf (stateAt m p) i
    rw [Proof.Sha3.byteOf_stateAt _ _ (by omega)]
    simp only [bytesAt, List.getElem_map, List.getElem_range]

/-- The facts the tail needs and leaves, with `Â` stored with 16 bits (`w16`) or 32. -/
structure AfterTW (w16 : Bool) (P : KemLay) (s₀ : State) (ρ : List Byte) (s : State) : Prop where
  b : BInvW w16 P (enL P) s₀ s.mem ρ (P.k*P.k) s
  key : bytesAt s.mem (kA s₀ 2) 32 = (gE P s₀).1
  r : bytesAt s.mem (sA (enL P) s₀ RB) 32 = (gE P s₀).2
  m : bytesAt s.mem (sA (enL P) s₀ MB) 32 = mE s₀

theorem tailH_ok {w16 : Bool} (hash : FixedHash.HashFn)
    (hG : FixedHash.HashCorrect hash .x28 ST WK 72 6 [⟨.x28,MB,32⟩,⟨.x28,HB,32⟩]
      [⟨.x26,0,32⟩,⟨.x28,RB,32⟩])
    {s₀ sB : State} (hp : Pre P (enL P) s₀) {ρ : List Byte}
    (hB : BInvW w16 P (enL P) s₀ sB.mem ρ (P.k*P.k) sB)
    (hm : bytesAt sB.mem (sA (enL P) s₀ MB) 32 = mE s₀)
    (hst : stateAt sB.mem (kA s₀ (enL P).sc) =
      Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 (BitVec.ofNat 8 6) (ekE P s₀))) :
    WP isa (Impl.MlKem.AArch64.Hybrid.tailH hash) sB (AfterTW w16 P s₀ ρ) := by
  have hw := hp.wf
  -- `H(ek)`
  refine WP.seq (WP.mono (KeyGen.copy_ok (S := kA s₀ 4) (D := kA s₀ 4) (so := KEM.ST) (dO := HB)
    (by decide) (by decide) (by decide) (by decide) (sdisj hp (by lom) (by lom) (by lom))
    hB.kb.x28 hB.kb.x28 (cov_sr hp hB.kb (by lom)) (cov_s hp hB.kb (by lom)))
    fun s₃ ⟨k₁, f₁, b₁⟩ => ?_)
  have kb₃ := hB.kb.frame k₁ f₁ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by lom)
  have far₁ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ HB ∨ HB + 32 ≤ o) →
      ∀ r ∈ [Region.mk (kA s₀ 4 + BitVec.ofNat 64 HB) 32], (R (kA s₀) (enL P).sc o l).Disjoint r :=
    fun f h r hr => by rw [List.mem_singleton.mp hr]; exact sdisj hp f (by lom) h
  have h₃ : bytesAt s₃.mem (sA (enL P) s₀ HB) 32 = H (ekE P s₀) := by
    rw [show sA (enL P) s₀ HB = kA s₀ 4 + BitVec.ofNat 64 HB from rfl, b₁,
      show KEM.ST = 0 from rfl, ptr_zero, H_eq, bytesAt_squeeze]
    show squeezeFrom 136 (stateAt sB.mem (kA s₀ (enL P).sc)) 0 32 = _
    rw [hst]; rfl
  have m₃ : bytesAt s₃.mem (sA (enL P) s₀ MB) 32 = mE s₀ := by
    rw [bytesAt_frame f₁ (far₁ (o := MB) (l := 32) (by lom) (by decide)) (by decide)]; exact hm
  have x24₃ : s₃.gpr .x24 = sB.gpr .x24 := k₁.get .x24
  -- `G(m ‖ H(ek))`
  refine WP.mono (hG (hsetup hp kb₃ (by decide : 72 ∈ Spec.Sha3.rates)) (by decide) (by simp)
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 3) hp kb₃ (by decide) (by enk) (.inr (by decide)) (by decide) (by enk)
      · exact pieceOk (k := 3) hp kb₃ (by decide) (by enk) (.inr (by decide)) (by decide) (by enk))
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 1) hp kb₃ (by decide) (by enk) (.inl (by enk)) (by decide) (by enk)
      · exact pieceOk (k := 3) hp kb₃ (by decide) (by enk) (.inr (by decide)) (by decide) (by enk))
    (by
      refine List.pairwise_pair.mpr ?_
      simp only [preg, kb₃.x26, e28 kb₃]
      exact hp.args.rdisj (by enk) (by enk) (by enk) (by enk) (by enk) (by enk)))
    fun s₄ ⟨k₄, o₄⟩ => ?_
  have kb₄ := kb₃.hash hp k₄ fun p hp' => by
    rcases mem2' hp' with rfl | rfl
    · exact ⟨1, 0, 32, rfl, by decide, by enk, by enk, .inl (by enk)⟩
    · exact ⟨3, RB, 32, rfl, by decide, by enk, by enk, .inr (.inr (by enk))⟩
  have msg : (List.map (pbytes s₃) [⟨.x28, MB, 32⟩, ⟨.x28, HB, 32⟩]).flatten = mE s₀ ++ H (ekE P s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      e28 kb₃]
    rw [m₃, h₃]
  obtain ⟨o₁, o₂, -⟩ := o₄
  rw [msg] at o₁ o₂
  have hG' := G_eq (mE s₀ ++ H (ekE P s₀))
  have key₄ : bytesAt s₄.mem (kA s₀ 2) 32 = (gE P s₀).1 := by
    have e : kA s₀ 2 = s₃.gpr .x26 + BitVec.ofNat 64 0 := by rw [kb₃.x26, ptr_zero]; rfl
    rw [e, o₁]; show _ = (G (mE s₀ ++ H (ekE P s₀))).1; rw [hG']; rfl
  have r₄ : bytesAt s₄.mem (sA (enL P) s₀ RB) 32 = (gE P s₀).2 := by
    rw [← e28 kb₃, o₂]; show _ = (G (mE s₀ ++ H (ekE P s₀))).2; rw [hG']; rfl
  have k₄' := k₄
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₃.x28, kb₃.x26, kb₃.sp] at k₄'
  have far₄ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → 840 ≤ o → (o + l ≤ RB ∨ RB + 32 ≤ o) →
      ∀ r ∈ [Region.mk (kA s₀ (enL P).sc + BitVec.ofNat 64 KEM.ST) 200,
        ⟨kA s₀ (enL P).sc + BitVec.ofNat 64 WK, 640⟩, below s₀.sp 16,
        ⟨kA s₀ ((enL P).slot 1) + BitVec.ofNat 64 0, 32⟩, ⟨kA s₀ (enL P).sc + BitVec.ofNat 64 RB, 32⟩],
      (R (kA s₀) (enL P).sc o l).Disjoint r := fun f h8 hr r hm => by
    rcases mem5 hm with rfl | rfl | rfl | rfl | rfl
    · exact sdisj hp f (by lom) (by lom)
    · exact sdisj hp f (by lom) (by lom)
    · exact below_R hp hp.scb (hp.fs f)
    · exact hp.args.rdisj (by enk) (by enk) (hp.fs f) (by enk) (by enk) (by enk)
    · exact sdisj hp f (by lom) hr
  have far34 : ∀ {o l : Nat}, o + l ≤ SV P + 48 → 840 ≤ o → (o + l ≤ RB ∨ RB + 32 ≤ o) →
      (o + l ≤ HB ∨ HB + 32 ≤ o) →
      bytesAt s₄.mem (sA (enL P) s₀ o) l = bytesAt sB.mem (sA (enL P) s₀ o) l := fun f h8 hr hh => by
    rw [bytesAt_frame k₄'.frame (far₄ f h8 hr) (by lom), bytesAt_frame f₁ (far₁ f hh) (by lom)]
  have farA : ∀ (e : Nat), e < P.k * P.k → ∀ r ∈ [Region.mk (kA s₀ 4 + BitVec.ofNat 64 HB) 32] ++
      [Region.mk (kA s₀ (enL P).sc + BitVec.ofNat 64 KEM.ST) 200,
        ⟨kA s₀ (enL P).sc + BitVec.ofNat 64 WK, 640⟩, below s₀.sp 16,
        ⟨kA s₀ ((enL P).slot 1) + BitVec.ofNat 64 0, 32⟩, ⟨kA s₀ (enL P).sc + BitVec.ofNat 64 RB, 32⟩],
      (polyRegion (aP (enL P) s₀ e)).Disjoint r := fun e he r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact far₁ (o := AH + 1024 * e) (l := 1024) (by lom) (.inr (by lom)) r hr
    · exact far₄ (o := AH + 1024 * e) (l := 1024) (by lom) (by lom) (.inr (by lom)) r hr
  have f14 := (f₁.mono (fun r hr => List.mem_append_left _ hr)).trans
    (k₄'.frame.mono (fun r hr => List.mem_append_right [Region.mk (kA s₀ 4 + BitVec.ofNat 64 HB) 32] hr))
  refine ⟨⟨kb₄, Frame.refl _ _, ?_, ?_, ?_, ?_⟩, key₄, r₄, ?_⟩
  · rw [far34 (o := SB) (l := 32) (by lom) (by lom) (by decide) (by decide)]; exact hB.rho
  · rw [k₄.cs _ (by decide) (by decide), x24₃]; exact hB.acc
  · intro e he; exact reducedW_frame f14 (farA e he) (hB.red e he)
  · intro e he; rw [polyAtW_frame f14 (farA e he)]; exact hB.res e he
  · rw [far34 (o := MB) (l := 32) (by lom) (by lom) (by decide) (by decide)]; exact hm

end VG.Proof.MlKem.AArch64.Hybrid
