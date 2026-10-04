import VerifiedGarbage.Proof.AesCcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesCcm.X86_64.Mac
import VerifiedGarbage.Proof.AesCcm.X86_64.Args

/-!
# AES-CCM on x86-64: the MAC is constant time

Untrusted: everything here is checked by Lean. The code between the calls
of `vg_cmac_aes_update` passes the taint analysis from the public slots and
registers (`rel_taintC`); each call has the same arguments in both runs, by
correctness (`upd_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.Stream.X86_64 (UArgs upd_rel)

/-! ## `updBlock` -/

/-- The arguments of `updBlock`'s call. -/
theorem updArgsBlk_ok {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.block (updArgs y ++ ptr .rcx .r15 bO ++ [.mov32 .r8 (imm 1)])) s fun s₁ =>
      UArgs s₁ K (W + BitVec.ofNat 64 y) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 384) R 1 ∧
      s₁.gpr .rsp = SP := by
  have h15 := E.r15
  have h13 := E.r13
  have r₁ := E.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have hy' : y < 2 ^ 31 := by omega
  obtain ⟨s₁, run₁, hm₁, hdi, hsi, hdx, hcx, hr8, hr9, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      (updArgs y ++ ptr .rcx .r15 bO ++ [.mov32 .r8 (imm 1)]) s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .rdi = K ∧ s₁.gpr .rsi = BitVec.ofNat 64 R ∧ s₁.gpr .rdx = W + BitVec.ofNat 64 y ∧
      s₁.gpr .rcx = W + BitVec.ofNat 64 32 ∧ s₁.gpr .r8 = BitVec.ofNat 64 1 ∧
      s₁.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [updArgs, h15, r₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, h13]
    · simp [gpr_setReg, hRo]
    · simp [gpr_setReg, h15, imm_eq hy']
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg]
    · simp [gpr_setReg, h15]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals rfl
  have E₁ : Env K W SP s₁ := E.keep hg₁ hrd₁ hwr₁
  have hq := srcW (s := s₁) L E₁.perm (t := 32) (k := 16 * 1) (by decide)
  have hqy : (⟨W + BitVec.ofNat 64 32, 16 * 1⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  exact WP.of_runBlock ⟨s₁, run₁, uargs L E₁ hR (by omega) hq hqy (by decide) hdi hsi hdx hcx hr8 hr9, E₁.rsp⟩

theorem updArgs_check {y : Nat} (hy : y = 0 ∨ y = 96) :
    ∃ hc, (taint.check (ccmT []) (.block (updArgs y ++ ptr .rcx .r15 bO ++ [.mov32 .r8 (imm 1)])) hc).isSome = true := by
  rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `updBlock y` in two runs. -/
theorem updBlock_rel (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → Both K W SP R N A D nl al n tl [] s₁ s₂) :
    RelCT isa P (updBlock v.callee v.suffix y) fun _ _ => True := by
  have a := (rel_taintC [] hDW hn hP (c := .block (updArgs y ++ ptr .rcx .r15 bO ++ [.mov32 .r8 (imm 1)]))
    (updArgs_check hy)).wp
    (F₁ := fun (s₁ : State) => UArgs s₁ K (W + BitVec.ofNat 64 y) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 384) R 1 ∧
      s₁.gpr .rsp = SP)
    (F₂ := fun (s₁ : State) => UArgs s₁ K (W + BitVec.ofNat 64 y) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 384) R 1 ∧
      s₁.gpr .rsp = SP)
    fun s₁ s₂ (h : P s₁ s₂) => ⟨updArgsBlk_ok L (hP _ _ h).e₁ hR (hP _ _ h).sl₁.rounds hy,
      updArgsBlk_ok L (hP _ _ h).e₂ hR (hP _ _ h).sl₂.rounds hy⟩
  exact RelCT.seq a (upd_rel v _ fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩)

/-! ## `b0` -/

/-- A run whose `W + 48` holds `Ctr₀` for some nonce of `nl` bytes. -/
def C0 (W : Addr) (nl : Nat) (s : State) : Prop :=
  ∃ nonce : List Byte, nonce.length = nl ∧ bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0

theorem b0Pre_check {y : Nat} (hy : y = 0 ∨ y = 96) :
    ∃ hc, (taint.check (ccmT []) (.seq (.block [.mov .rax (.mem (at_ .r15 tlO)), .alu .sub .rax (imm 2),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .mov32 .rcx (imm 14),
        .alu .sub .rcx (.mem (at_ .r15 nlenO)), .alu .add .rax (.reg .rcx), .mov .rcx (.mem (at_ .r15 alenO)),
        .alu .test .rcx (.reg .rcx)])
      (.seq (.ite .e (.block []) (.block [.alu .add .rax (imm 64)]))
      (.block ([.mov .rcx (.mem (at_ .r15 c0O)), .mov .rdx (.mem (at_ .r15 (c0O + 8))),
        .mov .rsi (.mem (at_ .r15 lenO)), .store (at_ .r15 bO) .rcx, .store8 (at_ .r15 bO) .rax, .bswap .rsi,
        .alu .or .rsi (.reg .rdx), .store (at_ .r15 (bO + 8)) .rsi] ++ zero16 y)))) hc).isSome = true := by
  rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- Both runs, after a frame within what the pieces write. -/
theorem Both.frame {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} (L : Lay K W SP)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {s₁ s₂ s₁' s₂' : State}
    (h : Both K W SP R N A D nl al n tl [] s₁ s₂) (E₁ : Env K W SP s₁') (E₂ : Env K W SP s₂')
    (hrd₁ : s₁'.wr = s₁.wr) (hrd₂ : s₂'.wr = s₂.wr)
    (f₁ : Frame (mutR W SP D n) s₁.mem s₁'.mem) (f₂ : Frame (mutR W SP D n) s₂.mem s₂'.mem) :
    Both K W SP R N A D nl al n tl [] s₁' s₂' :=
  ⟨E₁, E₂, slots_mut L hDW f₁ h.sl₁, slots_mut L hDW f₂ h.sl₂, hrd₁.trans h.wr₁, hrd₂.trans h.wr₂,
    fun _ h => nomatch h⟩

/-- `b0 y` in two runs. -/
theorem b0_rel (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hal : al < 2 ^ 64)
    (hn' : n < 256 ^ (15 - nl)) {y : Nat} (hy : y = 0 ∨ y = 96) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → Both K W SP R N A D nl al n tl [] s₁ s₂ ∧ C0 W nl s₁ ∧ C0 W nl s₂) :
    RelCT isa P (b0 v.callee v.suffix y) fun _ _ => True := by
  have hy16 : y + 16 ≤ 112 := by omega
  have pre : ∀ s, Both K W SP R N A D nl al n tl [] s s → C0 W nl s → WP isa _ s fun s' =>
      Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 y, 16⟩] s.mem s'.mem := fun s hb ⟨nonce, hl, hc⟩ =>
    WP.mono (b0Pre_ok L hb.e₁ hb.sl₁ hl h7 h13 ht4 ht16 hte hal hn' hc hy) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  have hB : ∀ s₁ s₂, P s₁ s₂ → ∀ s, (s = s₁ ∨ s = s₂) → Both K W SP R N A D nl al n tl [] s s ∧ C0 W nl s :=
    fun s₁ s₂ h s hs => by
      obtain ⟨b, c₁, c₂⟩ := hP _ _ h
      rcases hs with rfl | rfl
      · exact ⟨⟨b.e₁, b.e₁, b.sl₁, b.sl₁, b.wr₁, b.wr₁, fun _ h => nomatch h⟩, c₁⟩
      · exact ⟨⟨b.e₂, b.e₂, b.sl₂, b.sl₂, b.wr₂, b.wr₂, fun _ h => nomatch h⟩, c₂⟩
  have a := (rel_taintC [] hDW hn (fun s₁ s₂ h => (hP s₁ s₂ h).1) (b0Pre_check hy)).wpDep
    (F := fun (s s' : State) => Both K W SP R N A D nl al n tl [] s s ∧ Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 y, 16⟩] s.mem s'.mem)
    fun s₁ s₂ (h : P s₁ s₂) => ⟨WP.mono (pre s₁ (hB _ _ h s₁ (.inl rfl)).1 (hB _ _ h s₁ (.inl rfl)).2) fun _ q =>
        ⟨(hB _ _ h s₁ (.inl rfl)).1, q⟩,
      WP.mono (pre s₂ (hB _ _ h s₂ (.inr rfl)).1 (hB _ _ h s₂ (.inr rfl)).2) fun _ q =>
        ⟨(hB _ _ h s₂ (.inr rfl)).1, q⟩⟩
  refine rel_assoc3 (RelCT.seq a (updBlock_rel v L hR hDW hn hy (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    fun s₁' s₂' h => ?_))
  obtain ⟨-, σ₁, σ₂, hσ, ⟨b₁, E₁, -, w₁, f₁⟩, ⟨b₂, E₂, -, w₂, f₂⟩⟩ := h
  have hm : ∀ r ∈ [(⟨W + BitVec.ofNat 64 32, 16⟩ : Region), ⟨W + BitVec.ofNat 64 y, 16⟩],
      ∃ r' ∈ mutR W SP D n, Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
    · exact ⟨wA W, by simp, Offset.sub_base W hy16⟩
  exact ⟨E₁, E₂, slots_mut L hDW (f₁.sub hm) b₁.sl₁, slots_mut L hDW (f₂.sub hm) b₂.sl₁, w₁.trans b₁.wr₁,
    w₂.trans b₂.wr₁, fun _ h => nomatch h⟩

end VG.Proof.AesCcm.X86_64
