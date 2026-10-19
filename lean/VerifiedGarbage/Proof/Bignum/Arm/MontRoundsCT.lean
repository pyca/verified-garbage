module

public import VerifiedGarbage.Proof.Bignum.Arm.RoundCT
import VerifiedGarbage.Proof.Bignum.Arm.Round

/-! # Constant-time Montgomery scanning with secret operands and inverse -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem montRound_ready {base : BitVec 32} {size tmp a b mod acc n i : Nat} (hi : i < n)
    (s : State) (h : RoundReady base size tmp a b mod acc n i s) :
    WP isa montRound s fun t => RoundReady base size tmp a b mod acc n (i + 1) t ∧
      t.z = decide (i + 1 = n) := by
  obtain ⟨inv, hdr, inverse⟩ := h.secret
  refine WP.mono (montRound_ok s h.ctx hdr hi h.ptr h.bound h.operand inverse) ?_
  intro t post
  have nowrap := h.ctx.workspace.nowrap
  have fitsB := h.ctx.bFits
  have fitsM := h.ctx.mFits
  have accB := h.ctx.accB
  have accM := h.ctx.accM
  have tmpB := h.ctx.tmpB
  have tmpM := h.ctx.tmpM
  have oldB := post.outside.val32 (d := b) (k := n) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  have oldM := post.outside.val32 (d := mod) (k := n) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  refine ⟨⟨h.ctx.congr post.rest.wr, ⟨inv, post.hdr, ?_⟩, post.ptr, ?_, ?_⟩, post.zero⟩
  · rw [oldM]; exact inverse
  · rw [oldM]; exact post.bound
  · rw [oldB, oldM]; exact h.operand

theorem montRounds_ct {base : BitVec 32} {size tmp a b mod acc n : Nat} :
    RelCT isa (fun s t => RoundReady base size tmp a b mod acc n 0 s ∧
      RoundReady base size tmp a b mod acc n 0 t) montRounds (fun _ _ => True) := by
  let I := fun k s t => ∃ i, i + k = n ∧ 0 < k ∧
    RoundReady base size tmp a b mod acc n i s ∧ RoundReady base size tmp a b mod acc n i t
  have step : ∀ k, RelCT isa (I k) montRound fun s t => isa.eval .ne s = isa.eval .ne t ∧
      (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ j < k, I j s t) := by
    intro k
    apply RelCT.exists_
    intro i
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨hik, hk, hs, ht⟩ := h
    have hi : i < n := by omega
    obtain ⟨trace, posts⟩ := pair_posts (montRound_ct hi) (montRound_ready hi)
      s t tr1 tr2 u v ⟨hs, ht⟩ e1 e2
    obtain ⟨⟨hu, zu⟩, ⟨hv, zv⟩⟩ := posts
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!u.z) = some (!v.z)
      rw [zu, zv]
    · intro branch
      have ne : i + 1 ≠ n := by
        intro eq
        change some (!u.z) = some true at branch
        simp only [zu, eq, decide_true, Bool.not_true] at branch
        cases branch
      exact ⟨k - 1, by omega, i + 1, by omega, by omega, hu, hv⟩
  apply (RelCT.loop I step n).mono _ (fun _ _ h => h)
  intro s t h
  have count := h.1.ctx.count
  exact ⟨0, by omega, by omega, h⟩

end VG.Proof.Bignum.Arm
