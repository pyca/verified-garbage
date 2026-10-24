module

import VerifiedGarbage.Proof.Blowfish.PPC64LE.KeyInit
import VerifiedGarbage.Proof.Blowfish.PPC64LE.KeyP
import VerifiedGarbage.Proof.Blowfish.PPC64LE.KeyEnc
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Blowfish.PPC64LE
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep

/-!
# Blowfish on PPC64LE: key expansion

`expandKey_wp`: the schedule at `r5` becomes the expansion of the key at
`r3`; our caller's `r14`–`r17` are saved in the working space at `r6` and
restored.
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE VG.Spec.Blowfish VG.Proof.Blowfish

/-- What key expansion may assume: the key readable, the schedule and the
working space writable, apart, and a valid key length. -/
structure KeyPre (s : State) : Prop where
  valid : validKey (s.gpr .r4).toNat
  rd : s.rd = [⟨s.gpr .r3, (s.gpr .r4).toNat⟩]
  wr : s.wr = [⟨s.gpr .r5, 4168⟩, ⟨s.gpr .r6, 32⟩]
  keyS : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint ⟨s.gpr .r5, 4168⟩
  keyB : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint ⟨s.gpr .r6, 32⟩
  SB : (⟨s.gpr .r5, 4168⟩ : Region).Disjoint ⟨s.gpr .r6, 32⟩

/-- What key expansion guarantees. -/
structure KeyPost (s s' : State) : Prop where
  sched : scheduleAt s'.mem (s.gpr .r5) = expandKey (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
  saved : ∀ r ∈ saved.map Prod.fst, s'.gpr r = s.gpr r

theorem saved_fits' : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide
theorem saved_lt' : ∀ p ∈ saved, p.2 + 8 ≤ 32 := by decide

theorem save_eq' : save = Spill.saveCode .r6 saved := rfl
theorem restore_eq' : restore = Spill.restoreCode .r6 saved := rfl

theorem expandKey_wp {s : State} (h : KeyPre s) : WP isa Impl.Blowfish.PPC64LE.expandKey s (KeyPost s) := by
  have hv := h.valid
  let K := s.gpr .r3
  let L := (s.gpr .r4).toNat
  let S := s.gpr .r5
  let B := s.gpr .r6
  have sR : (⟨S, 4168⟩ : Region) ∈ s.wr := by rw [h.wr]; simp [S]
  have bR : (⟨B, 32⟩ : Region) ∈ s.wr := by rw [h.wr]; simp [B]
  have slot : ∀ p ∈ saved, Region.Sub ⟨B + BitVec.ofNat 64 p.2, 8⟩ ⟨B, 32⟩ := fun p hp =>
    Offset.sub_base _ (saved_lt' p hp)
  have keyIn : ∀ c < L, (⟨K, L⟩ : Region).Contains (K + BitVec.ofNat 64 c) 1 := fun c hc =>
    Offset.contains_base _ (by omega) (by omega)
  -- frames that miss the key
  have keyFrame : ∀ {m m' : Mem} {r : Region}, (⟨K, L⟩ : Region).Disjoint r → Frame [r] m m' →
      bytesAt m' K L = bytesAt m K L := fun hd hf =>
    bytesAt_frame hf fun c hc r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd _ (keyIn c hc) hcon
  unfold Impl.Blowfish.PPC64LE.expandKey
  apply WP.seq
  rw [save_eq']
  refine Spill.save_ok (by decide) saved_fits' (fun p hp =>
    ⟨_, bR, Offset.contains_base _ (saved_lt' p hp) (by have := saved_lt' p hp; omega)⟩) ?_
  let M₀ := Spill.saveMem s.mem B s.gpr saved
  have F₀ : Frame [⟨B, 32⟩] s.mem M₀ := Spill.saveMem_frame_base (fun p hp => saved_lt' p hp) (by decide) _ _ _
  rw [initSchedule_eq]
  refine WP.mono (initSteps_run (t := { s with mem := M₀ }) (S := S) rfl sR 521 (Nat.le_refl _))
    fun t₁ ⟨held, F₁, k₁⟩ => ?_
  -- the table's bytes
  have hT : ∀ o < 4168, t₁.mem (S + BitVec.ofNat 64 o) = Impl.Blowfish.initByte o := fun o ho =>
    table_byte (fun i hi => by rw [held i hi, initWords_getD hi]) ho
  have B₁ : bytesAt t₁.mem K L = bytesAt s.mem K L := by
    rw [keyFrame h.keyS F₁]; exact keyFrame h.keyB F₀
  have r₁ : t₁.rd = s.rd ∧ t₁.wr = s.wr := ⟨k₁.2.1, k₁.2.2⟩
  have E : KeyPEnv S K L t₁ := by
    refine ⟨by unfold validKey at hv; omega, (s.gpr .r4).isLt, fun c hc => ?_, k₁.gpr (by decide),
      by rw [k₁.gpr (by decide)]; simp [L], k₁.gpr (by decide), by rw [r₁.2]; exact sR,
      fun c hc hcon => h.keyS _ (keyIn c hc) hcon⟩
    rw [r₁.1, r₁.2, h.rd]; exact ⟨_, List.mem_cons_self, keyIn c hc⟩
  apply WP.seq
  refine WP.mono (keyP_run E) fun t₂ I₂ => ?_
  have hS₂ : ∀ o < 4096, t₂.mem (S + BitVec.ofNat 64 o) = Impl.Blowfish.initByte o := fun o ho => by
    rw [← hT o (by omega)]
    refine I₂.frame _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint S (d := o) (n := 1) (e := 4096) (k := 4 * 18) (.inl (by omega)) (by omega) (by omega)
      _ (Region.contains_self _ _) hc
  have hK₂ : scheduleAt t₂.mem S = keyed (bytesAt s.mem K L) := by
    refine keyed_of_mem hS₂ fun i hi => ?_
    rw [I₂.done i hi, table_P hT hi, B₁]
  -- the setup of the encryptions
  have r₂ : t₂.rd = s.rd ∧ t₂.wr = s.wr := by rw [I₂.keep.2.1, I₂.keep.2.2]; exact r₁
  apply WP.seq
  refine WP.mono (WP.keep [.r0, .r3, .r4, .r5] (Q := fun t => t.gpr .r0 = 0#64 ∧ t.gpr .r3 = S ∧
      t.gpr .r4 = 0#64 ∧ t.gpr .r5 = 0#64 ∧ t.mem = t₂.mem)
    (by brun [I₂.keep.gpr (show Reg.r5 ∉ keyPRegs by decide), k₁.gpr (show Reg.r5 ∉ [Reg.r12] by decide),
      BitVec.or_self]; rfl) (by decide) rfl) fun t₃ ⟨⟨z₃, a₃, b₃, c₃, m₃⟩, k₃⟩ => ?_
  have EE : EncEnv S t₃ := ⟨a₃, z₃, by rw [k₃.2.2, r₂.2]; exact sR⟩
  have I₃ : EncInv (bytesAt s.mem K L) S t₃ 0 t₃ :=
    ⟨by rw [m₃, hK₂, ksIter_zero], by rw [b₃, c₃, ksIter_zero]; rfl, Keep.refl _ _, Frame.refl _ _⟩
  apply WP.seq
  refine WP.mono (encryptP_run EE I₃) fun t₄ I₄ => ?_
  apply WP.seq
  refine WP.mono (encryptS_run EE I₄) fun t₅ I₅ => ?_
  -- restore
  rw [restore_eq']
  have r6 : t₅.gpr .r6 = B := by
    rw [I₅.keep.gpr (by decide), k₃.gpr (by decide), I₂.keep.gpr (by decide), k₁.gpr (by decide)]
  have dSlots : ∀ p ∈ saved, ∀ r ∈ [(⟨S, 4168⟩ : Region)], Region.Disjoint ⟨B + BitVec.ofNat 64 p.2, 8⟩ r :=
    fun p hp r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.SB.symm.sub_left (slot p hp))
  have hsv : Spill.Saved B s.gpr saved t₅.mem := by
    have s₀ : Spill.Saved B s.gpr saved M₀ := Spill.saveMem_saved (by decide) s.mem B s.gpr
    have s₁ := s₀.frame F₁ dSlots
    have s₂ := s₁.frame I₂.frame fun p hp r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dSlots p hp _ List.mem_cons_self).sub_right (by
        rw [← Offset.add_add_eq S (a := 4096) (b := 0) rfl, BitVec.add_zero]
        exact Offset.sub_base S (by omega))
    have s₃ : Spill.Saved B s.gpr saved t₃.mem := by rw [m₃]; exact s₂
    exact s₃.frame I₅.frame dSlots
  refine WP.mono (Spill.restore_wp (by decide) r6 saved_fits' (by decide) (fun p hp => ?_) hsv)
    fun s' R => ⟨?_, fun r hr => ?_⟩
  · rw [I₅.keep.2.1, I₅.keep.2.2, k₃.2.1, k₃.2.2, r₂.1, r₂.2]
    exact ⟨_, List.mem_append_right _ bR, Offset.contains_base _ (saved_lt' p hp)
      (by have := saved_lt' p hp; omega)⟩
  · rw [R.mem, I₅.sched, expandKey_eq]
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact R.gpr p hp

end VG.Proof.Blowfish.PPC64LE
