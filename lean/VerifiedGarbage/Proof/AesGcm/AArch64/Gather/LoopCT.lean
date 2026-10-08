import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Loop
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.Framework.Scratch

/-!
# Gathering a list of slices, AArch64: constant time

Untrusted: everything here is checked by Lean. Two runs of `gather` whose
descriptors agree, from states the correctness proof describes with the same
arguments (`GatherPre`), leak the same trace (`gather_rel`): the gathering
loads the descriptors from where they are, and copies each slice from and to
the addresses they give, with branches on the number of slices and their
lengths (by the taint analysis from the registers the correctness proof pins
to the same values in both runs).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Gather

open VG VG.AArch64 VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.SealGather
open VG.Spec.Gcm (gathered gatheredLen)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint rel_ite eval_zero eval_nonzero)

/-- The descriptors agree in two memories: so do the slices they list. -/
theorem desc_agree {m₁ m₂ : Mem} {Src : Addr} {cnt : Nat}
    (hd : ∀ j < cnt * 16, m₁ (Src + BitVec.ofNat 64 j) = m₂ (Src + BitVec.ofNat 64 j)) {i : Nat} (hi : i ≤ cnt) :
    ∀ a, (Sig.descRegion 64 Src i).Contains a 1 → m₁ a = m₂ a := by
  intro a ha
  simp only [Sig.descRegion, Region.Contains] at ha
  have e : Src + BitVec.ofNat 64 (a - Src).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [← e]
  exact hd _ (by have := Nat.mul_le_mul_right 16 hi; omega)

section
variable {e₁ e₂ : State} {Src Dst : Addr} {cnt L : Nat}
  (hd : ∀ j < cnt * 16, e₁.mem (Src + BitVec.ofNat 64 j) = e₂.mem (Src + BitVec.ofNat 64 j))
include hd

theorem gl_agree {i : Nat} (hi : i ≤ cnt) : gatheredLen 64 e₁.mem Src i = gatheredLen 64 e₂.mem Src i := by
  simp only [gatheredLen]
  rw [Sig.listed_congr 64 .u8 Src i (desc_agree hd hi)]

theorem desc_word {d : Nat} (h : d + 8 ≤ cnt * 16) :
    e₁.mem.readW (Src + BitVec.ofNat 64 d) 64 = e₂.mem.readW (Src + BitVec.ofNat 64 d) 64 :=
  Mem.readW_congr fun k hk => by
    rw [Offset.add_ofNat_add_ofNat]; exact hd _ (by simp at hk; omega)

theorem sb_agree {i : Nat} (hi : i < cnt) : sb e₁.mem Src i = sb e₂.mem Src i := desc_word hd (by omega)

theorem sl_agree {i : Nat} (hi : i < cnt) : sl e₁.mem Src i = sl e₂.mem Src i := by
  simp only [sl, Offset.add_ofNat_add_ofNat]
  rw [desc_word hd (by omega)]

variable (h₁ : GatherPre e₁ Src Dst cnt L) (h₂ : GatherPre e₂ Src Dst cnt L) (hsp : e₁.sp = e₂.sp)
include h₁ h₂ hsp

/-- One iteration of the loop, in two runs. -/
theorem body_rel {i : Nat} (hi : i < cnt) :
    RelCT isa (fun u₁ u₂ => GInv e₁ u₁ Src Dst cnt i ∧ GInv e₂ u₂ Src Dst cnt i)
      (.seq (.block next) (.seq copySlice (.block [.subImm .x .x7 .x7 1])))
      (fun u₁ u₂ => GInv e₁ u₁ Src Dst cnt (i + 1) ∧ GInv e₂ u₂ Src Dst cnt (i + 1)) := by
  have hT : RelCT isa (fun u₁ u₂ => GInv e₁ u₁ Src Dst cnt i ∧ GInv e₂ u₂ Src Dst cnt i)
      (.seq (.block next) (.seq copySlice (.block [.subImm .x .x7 .x7 1]))) TT := by
    intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' ⟨g₁, g₂⟩ x₁ x₂
    refine rel_seq (rel_taint [.x6, .x7, .x11] (by rw [g₁.keep.sp, g₂.keep.sp, hsp])
      (by agree_tac [g₁.x6, g₂.x6, g₁.x7, g₂.x7, g₁.x11, g₂.x11, gl_agree hd (Nat.le_of_lt hi)])
      ⟨_, by taint_decide⟩) (next_wp h₁ hi g₁) (next_wp h₂ hi g₂) (fun τ₁ τ₂ n₁ n₂ => ?_)
      σ₁ σ₂ t₁ t₂ σ₁' σ₂' ⟨rfl, rfl⟩ x₁ x₂
    exact rel_taint [.x6, .x7, .x11, .x12, .x13] (by rw [n₁.keep.sp, n₂.keep.sp, hsp])
      (by agree_tac [n₁.x6, n₂.x6, n₁.x7, n₂.x7, n₁.x11, n₂.x11, gl_agree hd (Nat.le_of_lt hi), n₁.x12, n₂.x12,
        sb_agree hd hi, n₁.x13, n₂.x13, sl_agree hd hi]) ⟨_, by taint_decide⟩
  exact (hT.wp fun u₁ u₂ ⟨g₁, g₂⟩ =>
    ⟨WP.seq (WP.mono (next_wp h₁ hi g₁) fun _ n => rest_wp h₁ hi n),
      WP.seq (WP.mono (next_wp h₂ hi g₂) fun _ n => rest_wp h₂ hi n)⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- `gather`, in two runs. -/
theorem gather_rel : RelCT isa (Eq2 e₁ e₂) gather TT := by
  have hc := h₁.hcnt
  refine rel_ite (eval_zero h₁.x7 h₁.hcnt) (eval_zero h₂.x7 h₂.hcnt)
    (fun _ => by exact rel_taint [] hsp (by agree_tac []) ⟨_, by taint_decide⟩) (fun hf => ?_)
  have hpos : cnt ≠ 0 := by simpa using hf
  refine (RelCT.loop (Q := TT) (fun n u₁ u₂ => ∃ i, n = cnt - i ∧ i < cnt ∧
      GInv e₁ u₁ Src Dst cnt i ∧ GInv e₂ u₂ Src Dst cnt i) (fun n => ?_) (cnt - 0)).mono
    (fun a b ⟨ha, hb⟩ => by subst ha hb; exact ⟨0, rfl, by omega, GInv.init h₁, GInv.init h₂⟩) fun _ _ h => h
  refine RelCT.exists_ fun i => ?_
  by_cases hin : n = cnt - i ∧ i < cnt
  · obtain ⟨rfl, hi⟩ := hin
    refine (body_rel hd h₁ h₂ hsp hi).mono (fun _ _ h => h.2.2) ?_
    rintro u₁ u₂ ⟨g₁, g₂⟩
    have ev₁ := eval_nonzero (r := .x7) (a := cnt - (i + 1)) g₁.x7 (by omega)
    have ev₂ := eval_nonzero (r := .x7) (a := cnt - (i + 1)) g₂.x7 (by omega)
    refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ?_⟩
    rw [ev₁] at ht
    have : i + 1 < cnt := by simp at ht; omega
    exact ⟨cnt - (i + 1), by omega, i + 1, rfl, this, g₁, g₂⟩
  · exact RelCT.of_false fun _ _ h => hin ⟨h.1, h.2.1⟩

end

end VG.Proof.AesGcm.AArch64.Gather
