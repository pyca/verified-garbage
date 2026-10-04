import VerifiedGarbage.Proof.AesOcb.AArch64.SealCT
import VerifiedGarbage.Proof.AesOcb.AArch64.Open

/-!
# AES-OCB on AArch64: `vg_aes_ocb_open` is constant time

Untrusted: everything here is checked by Lean. As `seal_ct`, with the tag at
`W + t2O`; then `cmp`, which loads the tag length from `W`: its first block
is split there, and the comparison runs from it (`cmp_rel`); `mask` and the
result read the comparison's result only as data.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Ocb (Block blockAtMem ctxCiph ctxLstar)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq ct_of)

/-- `cmp`, in two runs. -/
theorem cmp_rel {K W D : Addr} {R n : Nat} {SP : Addr} {σ₁ σ₂ : State} (E₁ : Env K W D R n SP σ₁)
    (E₂ : Env K W D R n SP σ₂) {tl : Nat} (htl₁ : σ₁.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (htl₂ : σ₂.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) : RelCT isa (Eq2 σ₁ σ₂) cmp TT := by
  obtain ⟨s₁, run₁, -, x11₁, x12₁, x24₁, -, g₁, sp₁, rd₁, wr₁⟩ := cmpHead_ok E₁ htl₁
  obtain ⟨s₂, run₂, -, x11₂, x12₂, x24₂, -, g₂, sp₂, rd₂, wr₂⟩ := cmpHead_ok E₂ htl₂
  have ne : ∀ r ∈ envRegs, r ∉ cmpRegs := by decide
  unfold cmp
  refine rel_seq (rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) (WP.of_runBlock ⟨s₁, run₁, rfl⟩)
    (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun τ₁ τ₂ h₁ h₂ => ?_
  subst h₁ h₂
  exact rel_env (E₁.keep (fun r hr => g₁ r (ne r hr)) sp₁ rd₁ wr₁) (E₂.keep (fun r hr => g₂ r (ne r hr)) sp₂ rd₂ wr₂)
    [.x11, .x12, .x24] (by agree_tac [x11₁, x11₂, x12₁, x12₂, x24₁, x24₂]) ⟨_, by taint_decide⟩

theorem open_ct (v : BlocksImpl) : ConstantTime isa openAArch64.pre openAArch64.pub («open» (callees v)) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have A₁ := args_of h₁
  have A₂ := args₂_of h₂ hq.1
  have qsp := hq.1.2.2.2.2.2.2.2.2.1
  have L := A₁.lay
  unfold «open»
  refine pre_relk v h₁ h₂ hq.1 fun τ₁ τ₂ P₁ P₂ => ?_
  have E₂ := P₂.env
  rw [← qsp] at E₂
  refine rel_seq (bodyOpen_rel L A₁.rounds v P₁.env E₂ (A₁.data.of_eq P₁.rd P₁.wr) (A₂.data.of_eq P₂.rd P₂.wr)
      P₁.ofs P₁.o0 P₁.ck (by rw [P₁.l0, ctxLstar_W L P₁.frame]) P₂.ofs P₂.o0 P₂.ck
      (by rw [P₂.l0, ctxLstar_W L P₂.frame]))
    (bodyOpen_ok v L P₁.env A₁.rounds (A₁.data.of_eq P₁.rd P₁.wr) P₁.ofs P₁.o0 P₁.ck
      (by rw [P₁.l0, ctxLstar_W L P₁.frame]))
    (bodyOpen_ok v L E₂ A₁.rounds (A₂.data.of_eq P₂.rd P₂.wr) P₂.ofs P₂.o0 P₂.ck
      (by rw [P₂.l0, ctxLstar_W L P₂.frame])) fun u₁ u₂ B₁ B₂ => ?_
  refine rel_seq (tag_rel L A₁.rounds v B₁.env B₂.env (.inr rfl)) (tag_ok v L B₁.env A₁.rounds (.inr rfl))
    (tag_ok v L B₂.env A₁.rounds (.inr rfl)) fun w₁ w₂ T₁ T₂ => ?_
  have S₁ := Slots.of_mut L A₁.data.w ((bodyR_mut B₁.frame).trans (tagR_mut (by decide) T₁.frame)) P₁.slots
  have S₂ := Slots.of_mut L A₁.data.w ((bodyR_mut B₂.frame).trans (tagR_mut (by decide) T₂.frame)) P₂.slots
  refine rel_seq (cmp_rel T₁.env T₂.env S₁.tl S₂.tl) (cmp_ok T₁.env A₁.t1 A₁.t16 S₁.tl)
    (cmp_ok T₂.env A₁.t1 A₁.t16 S₂.tl) fun y₁ y₂ ⟨_, g₁, sp₁, rd₁, wr₁⟩ ⟨_, g₂, sp₂, rd₂, wr₂⟩ => ?_
  have F₁ := T₁.env.others g₁ sp₁ rd₁ wr₁
  have F₂ := T₂.env.others g₂ sp₂ rd₂ wr₂
  refine rel_seqEnv F₁ F₂ (rel_env F₁ F₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · intro z₁ z₂ G₁ G₂
    exact rel_env G₁ G₂ [] (by agree_tac []) ⟨_, by taint_decide⟩

end VG.Proof.AesOcb.AArch64
