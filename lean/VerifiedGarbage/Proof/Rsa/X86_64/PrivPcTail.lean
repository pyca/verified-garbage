module

public import VerifiedGarbage.Proof.Rsa.X86_64.PrivTail
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPcPd
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# `vg_rsa_private_checked_precomputed` on x86-64: the check and the release

`vg_rsa_private_checked`'s (`PrivTail.lean`), with `r₁ & r₂ & 1` for the
release's condition (`tailP_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivCheckedPc
open VG.Impl.Rsa.X86_64.PrivChecked (sp lea oM cmpLoop masks releaseLoop at10 mByte)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa (gOf gOf_cases result)

/-- The comparison's registers. -/
theorem cmpArgsP_ok {s t : State} (hp : PreFPc s) (he : EnvP s t) :
    WP isa (.block cmpArgs) t fun t' => t'.mem = t.mem ∧
      t'.gpr .r11 = gOf (t.gpr .rax) (word t.mem (fbP s) oR1) 1 ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = stackArg s 0 ∧ t'.gpr .rcx = s.gpr .rcx ∧
      t'.gpr .r10 = BitVec.ofNat 64 0 ∧ t'.gpr .rdx = 0 ∧ Keep [.rax, .r11, .rdi, .rsi, .rcx, .r10, .rdx] t t' := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.rax, .r11, .rdi, .rsi, .rcx, .r10, .rdx] (c := .block cmpArgs) (Q := fun t' =>
      t'.mem = t.mem ∧ t'.gpr .r11 = gOf (t.gpr .rax) (word t.mem (fbP s) oR1) 1 ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = stackArg s 0 ∧ t'.gpr .rcx = s.gpr .rcx ∧
      t'.gpr .r10 = BitVec.ofNat 64 0 ∧ t'.gpr .rdx = 0) (by
    xrun [cmpArgs, gOf, BitVec.and_assoc, BitVec.and_self, ea_sp, he.rsp, arg, hs.ld (d := oR1) (by decide),
      hs.ld (d := oOut) (by decide), hs.ld (d := oK) (by decide), argP_in hp he (show 0 < 16 by decide),
      show fbP s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 0) = stackArgAddr s 0 from (stackArgAddr_fbP s 0).symm,
      he.sOut, he.sK, he.arg hp (show 0 < 16 by decide)]) rfl) fun t' ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, k⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, k⟩

/-- The check and the release, after the calls, from `t`: whatever `M`,
`out` and the values returned hold. -/
theorem tailP_ok {s t : State} (hp : PreFPc s) (he : EnvP s t) :
    WP isa (seqs PrivCheckedPc.tail) t fun t' =>
      t'.gpr .rax = result (gOf (t.gpr .rax) (word t.mem (fbP s) oR1) 1)
        (decide (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
          Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)) ∧
      Spec.Rsa.bytesAt t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
        (if gOf (t.gpr .rax) (word t.mem (fbP s) oR1) 1 = 1 ∧
            Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
              Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat
          then Spec.Rsa.bytesAt t.mem (off (fbP s) oM) (s.gpr .rcx).toNat
          else List.replicate (s.gpr .rcx).toNat 0) ∧
      Spec.Rsa.bytesAt t'.mem (off (fbP s) oM) (s.gpr .rcx).toNat = List.replicate (s.gpr .rcx).toNat 0 ∧
      EnvP s t' := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hsi := hp.hsi
  have hil := hp.hil
  -- The input, unchanged.
  have hin : Spec.Rsa.bytesAt t.mem (stackArg s 0) (s.gpr .rcx).toNat =
      Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat :=
    bytesP_of_frame he.mem (by rw [← hil]; exact hp.dKi) (by rw [← hil]; exact hp.dOi) (by rw [← hil]; exact hp.dis.symm)
      (by omega)
  have hout : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) ∈ t.wr := by
    rw [he.wr, hp.hwr, ← hsi]; simp
  have hinp : (⟨stackArg s 0, (s.gpr .rcx).toNat⟩ : Region) ∈ t.rd := by
    rw [he.rd, hp.hrd, ← hil]; simp
  have hfr : (⟨fbP s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have wO : (s.gpr .rcx).toNat ≤ 2 ^ 64 := by omega
  unfold PrivCheckedPc.tail
  simp only [seqs]
  refine WP.seq (WP.mono (cmpArgsP_ok hp he) fun t₁ ⟨hm₁, h11, hdi, hsi₁, hcx, h10, hdx, k₁⟩ => ?_)
  refine WP.seq (WP.mono (cmpLoop_ok (k := (s.gpr .rcx).toNat) (op := s.gpr .rdi) (ip := stackArg s 0) (by omega)
    (by omega) hdi hsi₁ (by rw [hcx]; exact (ofNat_toNat _).symm) h10 hdx
    (fun i hi => ⟨_, List.mem_append_right _ (by rw [k₁.2.2]; exact hout), contains_of_byte rfl wO hi⟩)
    (fun i hi => ⟨_, List.mem_append_left _ (by rw [k₁.2.1]; exact hinp), contains_of_byte rfl wO hi⟩))
    fun t₂ hI => ?_)
  have k12 := k₁.trans hI.keep
  have hrdx : t₂.gpr .rdx = 0 ↔ decide (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
      Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) = true := by
    rw [hI.rdx, decide_eq_true_iff, ← hin, bytesAt_eq_iff, hm₁]
  refine WP.seq (WP.mono (masks_ok (h11 ▸ (hI.keep.gpr (by decide))) (gOf_cases _ _ _) hrdx)
    fun t₃ ⟨hm₃, h9, h11', h10', k₃⟩ => ?_)
  have k13 := k12.trans k₃
  have hsep : ∀ i < (s.gpr .rcx).toNat, ∀ i' < (s.gpr .rcx).toNat,
      s.gpr .rdi + BitVec.ofNat 64 i ≠ off (fbP s) oM + BitVec.ofNat 64 i' := fun i hi i' hi' h => by
    have hc := contains_of_byte (r := mRP s) rfl wO hi'
    rw [← h] at hc
    exact (hp.dKo.sub_left (mRP_sub hp)) _ hc
      (contains_of_byte (r := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩) rfl (by omega) (show i < (s.gpr .rsi).toNat by omega))
  refine WP.seq (WP.mono (releaseLoop_ok (k := (s.gpr .rcx).toNat) (S := fbP s) (by omega) (by omega)
    ((k13.gpr (by decide)).trans he.rsp) (((hI.keep.trans k₃).gpr (by decide)).trans hdi) h9 ?_ h10'
    (fun i hi => ⟨_, by rw [k13.2.2]; exact hout, contains_of_byte rfl wO hi⟩)
    (fun i hi => ⟨_, by rw [k13.2.2]; exact hfr, by
      rw [off, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base _ (by unfold oM frameBytes; omega) (by unfold oM; omega)⟩)
    hsep) fun t₄ hR => ?_)
  · rw [((hI.keep.trans k₃).gpr (by decide)).trans hcx]; exact (ofNat_toNat _).symm
  have hm₃ : t₃.mem = t.mem := hm₃.trans (hI.mem.trans hm₁)
  have k14 := k13.trans hR.keep
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.gpr .rax = t₄.gpr .r11 ∧ t'.mem = t₄.mem) (by xrun) rfl)
    fun t' ⟨⟨hax, hm⟩, k'⟩ => ?_
  have k15 := k14.trans k'
  have hfr4 : Frame [outR s, mRP s] t.mem t'.mem := fun x hx => by
    rw [hm, hR.frame x (fun i hi h => hx _ (List.mem_cons_self ..) (by
        rw [h]; exact contains_of_byte (r := outR s) rfl (by omega) (show i < (s.gpr .rsi).toNat by omega)))
      (fun i hi h => hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by
        rw [h]; exact contains_of_byte rfl wO hi)), hm₃]
  have hslot : ∀ {d : Nat}, 112 ≤ d → d + 8 ≤ oM → word t'.mem (fbP s) d = word t.mem (fbP s) d := fun hd hd' =>
    slotP_keep hfr4 fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.dKo.sub_left (frameP_sub s (by unfold oM frameBytes at *; omega))
      · exact Offset.disjoint _ (.inl hd') (by unfold oM at hd'; omega) (by unfold oM; omega)
  refine ⟨hax.trans ((hR.keep.gpr (by decide)).trans h11'), ?_, ?_, ⟨(k15.gpr (by decide)).trans he.rsp,
    k15.2.1.trans he.rd, k15.2.2.trans he.wr, frameP_call he.mem hfr4 fun r hr => ?_,
    (hslot (by decide) (by decide)).trans he.sOut, (hslot (by decide) (by decide)).trans he.sN,
    (hslot (by decide) (by decide)).trans he.sK, (hslot (by decide) (by decide)).trans he.sE,
    (hslot (by decide) (by decide)).trans he.sEl⟩⟩
  · by_cases hc : gOf (t.gpr .rax) (word t.mem (fbP s) oR1) 1 = 1 ∧
        Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
          Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat
    · have hc' : gOf (t.gpr .rax) (word t.mem (fbP s) oR1) 1 = 1 ∧
          decide (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
            Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) = true := ⟨hc.1, decide_eq_true hc.2⟩
      simp only [hc, and_self, ↓reduceIte]
      simp only [Spec.Rsa.bytesAt, hm]
      exact List.map_congr_left fun i hi => by
        rw [hR.out i (List.mem_range.mp hi), hm₃]; simp only [hc', and_self, ↓reduceIte]
    · have hc' : ¬ (gOf (t.gpr .rax) (word t.mem (fbP s) oR1) 1 = 1 ∧
          decide (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
            Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) = true) :=
        fun h => hc ⟨h.1, of_decide_eq_true h.2⟩
      simp only [hc, ↓reduceIte]
      simp only [Spec.Rsa.bytesAt, hm]
      refine List.ext_getElem (by simp) fun i h₁ _ => ?_
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
      rw [hR.out i (by simpa using h₁)]; simp only [hc', ↓reduceIte]
  · simp only [Spec.Rsa.bytesAt, hm]
    refine List.ext_getElem (by simp) fun i h₁ _ => ?_
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact hR.m i (by simpa using h₁)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inl (sub_refl _))
    · exact .inl (mRP_sub hp)

end VG.Proof.Rsa.X86_64
