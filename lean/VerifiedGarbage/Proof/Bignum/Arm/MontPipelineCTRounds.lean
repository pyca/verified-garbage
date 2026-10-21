module

public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineRound
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline
public import VerifiedGarbage.Proof.Bignum.Arm.RoundCT
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Lift a scanning-round constant-time law through the public native loop. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.MontPipeline
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

/-- A replacement native round has a public schedule for its public index and count. -/
def RoundCTLaw (round : Prog isa) : Prop :=
  ∀ {base : BitVec 32} {size tmp a b mod acc n i : Nat}, n % 2 = 0 → i < n →
    RelCT isa (fun s t => RoundReady base size tmp a b mod acc n i s ∧
      RoundReady base size tmp a b mod acc n i t) round (fun _ _ => True)

theorem round_ready (round : Prog isa) (law : RoundLaw round) {base : BitVec 32} {size tmp a b mod acc n i : Nat} (even : n % 2 = 0) (hi : i < n)
    (s : State) (h : RoundReady base size tmp a b mod acc n i s) :
    WP isa round s fun t => RoundReady base size tmp a b mod acc n (i + 1) t ∧
      t.z = decide (i + 1 = n) := by
  obtain ⟨inv, hdr, inverse⟩ := h.secret
  refine WP.mono (law s h.ctx even hdr hi h.ptr h.bound h.operand inverse) ?_
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

theorem rounds_ct (round : Prog isa) (law : RoundLaw round) (ctLaw : RoundCTLaw round) {base : BitVec 32} {size tmp a b mod acc n : Nat} (even : n % 2 = 0) :
    RelCT isa (fun s t => RoundReady base size tmp a b mod acc n 0 s ∧
      RoundReady base size tmp a b mod acc n 0 t) (VG.Impl.Bignum.Arm.MontPipeline.rounds round) (fun _ _ => True) := by
  let I := fun k s t => ∃ i, i + k = n ∧ 0 < k ∧
    RoundReady base size tmp a b mod acc n i s ∧ RoundReady base size tmp a b mod acc n i t
  have step : ∀ k, RelCT isa (I k) round fun s t => isa.eval .ne s = isa.eval .ne t ∧
      (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ j < k, I j s t) := by
    intro k
    apply RelCT.exists_
    intro i s t tr1 tr2 u v h e1 e2
    obtain ⟨hik, hk, hs, ht⟩ := h
    have hi : i < n := by omega
    obtain ⟨trace, posts⟩ := pair_posts (ctLaw even hi) (round_ready round law even hi)
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


end VG.Proof.Bignum.Arm.MontPipeline
