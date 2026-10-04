import VerifiedGarbage.Proof.AesOcb.AArch64.SealCT
import VerifiedGarbage.Proof.AesOcb.AArch64.Open

/-!
# AES-OCB on AArch64: `vg_aes_ocb_open` is constant time

Untrusted: everything here is checked by Lean. As `seal_ct`, with the tag at
`W + t2O`; then the copy of the received tag to `W`, whose first block loads
the tag's address from the stack and is split there (`recv_rel`); then
`cmp`, which loads the tag length from `W`: its first block is split there,
and the comparison runs from it (`cmp_rel`); `mask` and the result read the
comparison's result only as data.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
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

/-- `recv` in two runs: its first block loads the tag's address from the
stack, and the copy runs from it. -/
theorem recv_rel {K W D : Addr} {R n : Nat} {SP : Addr} {σ₁ σ₂ : State} (E₁ : Env K W D R n SP σ₁)
    (E₂ : Env K W D R n SP σ₂) {T : Addr} {tl : Nat}
    (htl₁ : σ₁.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (htl₂ : σ₂.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) (hT₁ : stackArg σ₁ 0 = T)
    (hT₂ : stackArg σ₂ 0 = T) (ha₁ : InRegions (σ₁.rd ++ σ₁.wr) (σ₁.sp + BitVec.ofNat 64 (8 * 0)) 8)
    (ha₂ : InRegions (σ₂.rd ++ σ₂.wr) (σ₂.sp + BitVec.ofNat 64 (8 * 0)) 8) : RelCT isa (Eq2 σ₁ σ₂) recv TT := by
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, -, g₁, sp₁, rd₁, wr₁⟩ := recvHead_ok E₁ htl₁ hT₁ ha₁
  obtain ⟨s₂, run₂, x11₂, x12₂, x13₂, -, g₂, sp₂, rd₂, wr₂⟩ := recvHead_ok E₂ htl₂ hT₂ ha₂
  unfold recv
  refine rel_seq (rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) (WP.of_runBlock ⟨s₁, run₁, rfl⟩)
    (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun τ₁ τ₂ h₁ h₂ => ?_
  subst h₁ h₂
  exact rel_env (E₁.others g₁ sp₁ rd₁ wr₁) (E₂.others g₂ sp₂ rd₂ wr₂) [.x11, .x12, .x13]
    (by agree_tac [x11₁, x11₂, x12₁, x12₂, x13₁, x13₂]) ⟨_, by taint_decide⟩

/-- The received tag's copy to `W` keeps the slots. -/
theorem recv_slots {K W D : Addr} {n : Nat} (L : Lay K W) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {tl : Nat}
    (h16 : tl ≤ 16) {m : Mem} {xs : List Byte} (hx : xs.length = tl) {N A : Addr} {nl al : Nat}
    (S : Slots W N A nl al tl m) : Slots W N A nl al tl (writeBytes m W xs) :=
  Slots.of_mut L hDW ((writeBytes_frame _ _ _ (by rw [hx]; exact Region.contains_self _ _)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by omega)⟩) S

theorem open_ct (v : BlocksImpl) : ConstantTime isa openAArch64.pre openAArch64.pub («open» (callees v)) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have A₁ := openArgs_of h₁
  have A₂ := args₂_of hq.1 (openArgs_of h₂)
  have qsp := hq.1.2.2.2.2.2.2.2.2.1
  have qT : stackArg σ₂ 0 = stackArg σ₁ 0 := (hq.1.2.2.2.2.2.2.2.2.2 0 (by decide)).symm
  have L := A₁.lay
  unfold «open» front
  refine rel_front (pre_relk v A₁ A₂ hq.1 fun τ₁ τ₂ P₁ P₂ => ?_)
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
  obtain ⟨t₁, a₁⟩ := front_tag A₁ rfl (by decide) P₁ B₁ T₁ rfl
  obtain ⟨t₂, a₂⟩ := front_tag A₂ qT (by decide) P₂ B₂ T₂ qsp
  refine rel_seq (recv_rel T₁.env T₂.env S₁.tl S₂.tl t₁ t₂ a₁ a₂)
    (recv_ok T₁.env A₁.t1 A₁.t16 S₁.tl t₁ a₁ (by rw [T₁.rd, B₁.rd, P₁.rd, T₁.wr, B₁.wr, P₁.wr]; exact A₁.tag.rd)
      A₁.tag.w)
    (recv_ok T₂.env A₁.t1 A₁.t16 S₂.tl t₂ a₂ (by rw [T₂.rd, B₂.rd, P₂.rd, T₂.wr, B₂.wr, P₂.wr]; exact A₂.tag.rd)
      A₂.tag.w)
    fun y₁ y₂ ⟨m₁, g₁, sp₁, rd₁, wr₁⟩ ⟨m₂, g₂, sp₂, rd₂, wr₂⟩ => ?_
  have Y₁ := T₁.env.others g₁ sp₁ rd₁ wr₁
  have Y₂ := T₂.env.others g₂ sp₂ rd₂ wr₂
  have Sy₁ := recv_slots L A₁.data.w A₁.t16 (Proof.Ocb.length_bytesAt w₁.mem (stackArg σ₁ 0) _) S₁
  have Sy₂ := recv_slots L A₁.data.w A₁.t16 (Proof.Ocb.length_bytesAt w₂.mem (stackArg σ₁ 0) _) S₂
  rw [← m₁] at Sy₁
  rw [← m₂] at Sy₂
  refine rel_seq (cmp_rel Y₁ Y₂ Sy₁.tl Sy₂.tl) (cmp_ok Y₁ A₁.t1 A₁.t16 Sy₁.tl)
    (cmp_ok Y₂ A₁.t1 A₁.t16 Sy₂.tl) fun z₁ z₂ ⟨_, g₁, sp₁, rd₁, wr₁⟩ ⟨_, g₂, sp₂, rd₂, wr₂⟩ => ?_
  have F₁ := Y₁.others g₁ sp₁ rd₁ wr₁
  have F₂ := Y₂.others g₂ sp₂ rd₂ wr₂
  refine rel_seqEnv F₁ F₂ (rel_env F₁ F₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · intro z₁ z₂ G₁ G₂
    exact rel_env G₁ G₂ [] (by agree_tac []) ⟨_, by taint_decide⟩

end VG.Proof.AesOcb.AArch64
