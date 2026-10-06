import VerifiedGarbage.Proof.AesOcb.X86_64.CTBase
import VerifiedGarbage.Proof.AesOcb.X86_64.RestTag

/-!
# AES-OCB on x86-64: the tag is constant time

Untrusted: everything here is checked by Lean. The blocks before and after
the call pass the taint analysis from the public slots (`rel_taintC`); the
call of `vg_aes_encrypt_blocks` has the same arguments in both runs
(`callBlocks_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append)

/-- A call of `vg_aes_encrypt_blocks` on the block at `W + tmpO` keeps the
public arguments. -/
theorem callTmp_one (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) {s : State}
    (o : One K W SP R N A D nl n tl s) :
    WP isa (callBlocks (callees v).enc (oneBlock tmpO)) s (One K W SP R N A D nl n tl) :=
  WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encDepth L o.env hR o.sl.rounds
    (oneBlock_ok o.env.r15 tmpO (by decide)) (dstW L o.env.perm (d := tmpO) (n := 1) (by decide))) fun s' Q => by
    have E' := o.env.of_saved Q.saved Q.rd Q.wr
    refine o.step L hDW E' Q.wr (Q.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
    · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
    · rw [o.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩

/-- The call on the block at `W + tmpO`, in two runs. -/
theorem callTmp_rel (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hn : n ≤ 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → One K W SP R N A D nl n tl s₁ ∧ One K W SP R N A D nl n tl s₂) :
    RelCT isa P (callBlocks (callees v).enc (oneBlock tmpO)) fun s₁ s₂ =>
      One K W SP R N A D nl n tl s₁ ∧ One K W SP R N A D nl n tl s₂ :=
  ((callBlocks_rel (b := (callees v).enc) v.encOk v.encCt L hR hDW hn [] [] (args := oneBlock tmpO)
    ⟨_, by taint_decide⟩ (D' := W + BitVec.ofNat 64 tmpO) (k := 1) fun s₁ s₂ h =>
      ⟨Both.of (hP s₁ s₂ h).1 (hP s₁ s₂ h).2, oneBlock_ok (hP s₁ s₂ h).1.env.r15 tmpO (by decide),
        oneBlock_ok (hP s₁ s₂ h).2.env.r15 tmpO (by decide), dstW L (hP s₁ s₂ h).1.env.perm (by decide),
        dstW L (hP s₁ s₂ h).2.env.perm (by decide)⟩).wp
    (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun s₁ s₂ h => ⟨callTmp_one v L hR hDW (hP s₁ s₂ h).1, callTmp_one v L hR hDW (hP s₁ s₂ h).2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-- The checksum, the offset and `L_$` at `W + tmpO`. -/
theorem tagHead_one {K W SP : Addr} (L : Lay K W SP) {N A D : Addr} {R nl n tl : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) {s : State} (o : One K W SP R N A D nl n tl s) :
    WP isa (.block (copy16 ckO tmpO ++ xor16 .r15 ofsO tmpO ++ xor16 .r15 ldO tmpO)) s
      (One K W SP R N A D nl n tl) := by
  have E := o.env
  obtain ⟨t₁, run₁, B₁⟩ := copy16_ok (s := s) (a := ckO) (d := tmpO) E.r15
    (E.perm.wR (by decide)) (E.perm.wR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have nE : ∀ r ∈ [Reg.r14, .r15, .rsp], r ∉ [Reg.rax, .rdx] := by decide
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => B₁.gpr r (nE r hr)) B₁.rd B₁.wr
  obtain ⟨t₂, run₂, B₂⟩ := xor16_ok (s := t₁) (b := .r15) (a := ofsO) (d := tmpO) E₁.r15 E₁.r15 (by decide) (by decide)
    (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide)) (E₁.perm.wW (by decide)) (E₁.perm.wW (by decide))
  have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => B₂.gpr r (nE r hr)) B₂.rd B₂.wr
  obtain ⟨t₃, run₃, B₃⟩ := xor16_ok (s := t₂) (b := .r15) (a := ldO) (d := tmpO) E₂.r15 E₂.r15 (by decide) (by decide)
    (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide)) (E₂.perm.wW (by decide)) (E₂.perm.wW (by decide))
  have E₃ : Env K W SP t₃ := E₂.keep (fun r hr => B₃.gpr r (nE r hr)) B₃.rd B₃.wr
  refine WP.of_runBlock ⟨t₃, by rw [runBlock_append, runBlock_append, run₁, Option.bind_some, run₂,
    Option.bind_some, run₃], o.step L hDW E₃ (by rw [B₃.wr, B₂.wr, B₁.wr])
      (((B₁.frame.trans B₂.frame).trans B₃.frame).sub fun r hr => ?_)⟩
  simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩

/-- `tag d` in two runs. -/
theorem tag_rel (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hn : n ≤ 2 ^ 64)
    {d : Nat} (hd : d = tagO ∨ d = t2O) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → One K W SP R N A D nl n tl s₁ ∧ One K W SP R N A D nl n tl s₂) :
    RelCT isa P (tag (callees v) d) fun _ _ => True := by
  have a := (rel_taintC [] [] hDW hn (fun s₁ s₂ h => Both.of (hP s₁ s₂ h).1 (hP s₁ s₂ h).2)
    (c := .block (copy16 ckO tmpO ++ xor16 .r15 ofsO tmpO ++ xor16 .r15 ldO tmpO)) ⟨_, by taint_decide⟩).wp
    (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun s₁ s₂ h => ⟨tagHead_one L hDW (hP s₁ s₂ h).1, tagHead_one L hDW (hP s₁ s₂ h).2⟩
  have b := callTmp_rel v L hR hDW hn (P := fun s₁ s₂ => True ∧ One K W SP R N A D nl n tl s₁ ∧
    One K W SP R N A D nl n tl s₂) fun _ _ h => h.2
  have c := rel_taintC [] [] hDW hn (fun s₁ s₂ (h : One K W SP R N A D nl n tl s₁ ∧ One K W SP R N A D nl n tl s₂) =>
    Both.of h.1 h.2) (c := .block (copy16 tmpO d ++ xor16 .r15 sumO d))
    (by rcases hd with rfl | rfl <;> exact ⟨_, by taint_decide⟩)
  exact RelCT.seq a (RelCT.seq b c)

end VG.Proof.AesOcb.X86_64
