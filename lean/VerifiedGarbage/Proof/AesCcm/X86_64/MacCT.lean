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
open VG.Proof.AesGcm.X86_64 (LoopPre copyLoop_ok)
open VG.WriteBytes

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

/-! ## `absorbPad` -/

theorem absorbW1_ok {s : State} {len : Nat} (hbp : s.gpr .rbp = BitVec.ofNat 64 len) (hl : len < 2 ^ 64) :
    WP isa (.block [.mov .r8 (.reg .rbp), .shift .shr .r8 4, .alu .test .r8 (.reg .r8)]) s fun s₁ =>
      s₁.mem = s.mem ∧ s₁.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ (∀ r, r ≠ .r8 → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [gpr_setReg, hbp, shr4 len hl]
  · intro r a; simp [gpr_setReg, gpr_setFlags, a]
  all_goals rfl

theorem absorbWArgs_ok {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : Buf K W SP s P len)
    (h12 : s.gpr .r12 = P) (h8 : s.gpr .r8 = BitVec.ofNat 64 (len / 16)) :
    WP isa (.block (updArgs y ++ [.mov .rcx (.reg .r12)])) s fun s₂ =>
      UArgs s₂ K (W + BitVec.ofNat 64 y) P (W + BitVec.ofNat 64 384) R (len / 16) ∧ s₂.gpr .rsp = SP := by
  have hl := hP.lt
  have h15 := E.r15
  have h13 := E.r13
  have r₁ := E.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have hy' : y < 2 ^ 31 := by omega
  obtain ⟨s₂, run₂, hdi, hsi, hdx, hcx, hr8₂, hr9, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      (updArgs y ++ [.mov .rcx (.reg .r12)]) s = some s₂ ∧
      s₂.gpr .rdi = K ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = W + BitVec.ofNat 64 y ∧
      s₂.gpr .rcx = P ∧ s₂.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ s₂.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], s₂.gpr r = s.gpr r) ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by crun [updArgs, h15, r₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h13]
    · simp [gpr_setReg, hRo]
    · simp [gpr_setReg, h15, imm_eq hy']
    · simp [gpr_setReg, h12]
    · simp [gpr_setReg, h8]
    · simp [gpr_setReg, h15]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals rfl
  have E₂ : Env K W SP s₂ := E.keep hg₂ hrd₂ hwr₂
  have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  have hq := srcBuf ((hP.take hb).of_eq (s' := s₂) hrd₂ hwr₂)
  have hqy : (⟨P, 16 * (len / 16)⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16⟩ :=
    (hP.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by omega))
  exact WP.of_runBlock ⟨s₂, run₂, uargs L E₂ hR (by omega) hq hqy (by omega) hdi hsi hdx hcx hr8₂ hr9, E₂.rsp⟩

theorem absorbT1_ok {s : State} {len : Nat} (hbp : s.gpr .rbp = BitVec.ofNat 64 len) (hl : len < 2 ^ 64) :
    WP isa (.block [.mov .rcx (.reg .rbp), .alu .and .rcx (imm 15), .alu .test .rcx (.reg .rcx)]) s fun s₁ =>
      s₁.mem = s.mem ∧ s₁.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧ (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.zf = some (decide (len % 16 = 0)) := by
  refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [gpr_setReg, hbp, and15', toNat_ofNat_of_lt hl]
  · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
  · rfl
  · rfl
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, hbp, and15', toNat_ofNat_of_lt hl,
      and_self_beq (show len % 16 < 2 ^ 64 by omega)]

theorem absorbT2_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {P : Addr} {len : Nat}
    (hP : Buf K W SP s P len) (h12 : s.gpr .r12 = P) (hbp : s.gpr .rbp = BitVec.ofNat 64 len)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (len % 16)) (h0 : len % 16 ≠ 0) :
    WP isa (.seq (.block (zero16 bO ++ [.mov .rsi (.reg .rbp), .alu .sub .rsi (.reg .rcx), .alu .add .rsi (.reg .r12)] ++
        ptr .rdi .r15 bO)) copyLoop) s fun s' =>
      Env K W SP s' ∧ Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hl := hP.lt
  have h15 := E.r15
  have w₁ := E.perm.wW (show 32 + 8 ≤ 2560 by decide)
  have w₂ := E.perm.wW (show 40 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hm₂, hsi, hdi, hcx₂, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      (zero16 bO ++ [.mov .rsi (.reg .rbp), .alu .sub .rsi (.reg .rcx), .alu .add .rsi (.reg .r12)] ++
        ptr .rdi .r15 bO) s = some s₂ ∧
      s₂.mem = (s.mem.writeW (W + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 40)
        (0 : BitVec 64) ∧
      s₂.gpr .rsi = P + BitVec.ofNat 64 (16 * (len / 16)) ∧ s₂.gpr .rdi = W + BitVec.ofNat 64 32 ∧
      s₂.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdi → s₂.gpr r = s.gpr r) ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by crun [zero16, h15, w₁, w₂, add_ofNat_assoc], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags]; rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbp, h12, hcx]
      rw [ofNat_sub (by omega) hl, BitVec.add_comm, show len - len % 16 = 16 * (len / 16) by omega]
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg, hcx]
    · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have E₂ : Env K W SP s₂ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have hT := (hP.slice (a := 16 * (len / 16)) (k := len % 16) (by omega)).of_eq (s' := s₂) hrd₂ hwr₂
  have lp : LoopPre s₂ (P + BitVec.ofNat 64 (16 * (len / 16))) (W + BitVec.ofNat 64 32) (len % 16) :=
    ⟨hsi, hdi, hcx₂, by omega, by omega, hT.rd, E₂.perm.wC (by omega), hT.w.sub_right (Lay.wSub (by omega))⟩
  refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ⟨E₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃, ?_,
    by rw [hrd₃, hrd₂], by rw [hwr₃, hwr₂]⟩
  have fZ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₂.mem := by
    rw [hm₂]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains W (d := 32) (n := 8) (e := 32) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains W (d := 40) (n := 8) (e := 32) (k := 16) (by decide) (by decide) (by decide))
  refine fZ.trans ?_
  rw [hm₃]
  exact writeBytes_frame _ _ _ (by
    rw [length_bytesAt]
    exact Offset.contains W (d := 32) (n := len % 16) (e := 32) (k := 16) (by decide) (by omega) (by decide))

/-- What a run of `absorbPad` needs: the `len` bytes at `P` in `r12`, `rbp`. -/
structure AbsPre (K W SP : Addr) (P : Addr) (len : Nat) (s : State) : Prop where
  buf : Buf K W SP s P len
  r12 : s.gpr .r12 = P
  rbp : s.gpr .rbp = BitVec.ofNat 64 len

theorem absW1_check : ∃ hc, ((taint.check (ccmT [.r12, .rbp])
    (.block [.mov .r8 (.reg .rbp), .shift .shr .r8 4, .alu .test .r8 (.reg .r8)]) hc).map (·.flags)) = some true :=
  ⟨_, by taint_decide⟩

theorem absWArgs_check {y : Nat} (hy : y = 0 ∨ y = 96) :
    ∃ hc, (taint.check (ccmT [.r12, .r8]) (.block (updArgs y ++ [.mov .rcx (.reg .r12)])) hc).isSome = true := by
  rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- The whole blocks, in two runs. -/
theorem absorbWhole_rel (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → One K W SP R N A D nl al n tl s₁ ∧ One K W SP R N A D nl al n tl s₂ ∧
      AbsPre K W SP P len s₁ ∧ AbsPre K W SP P len s₂) :
    RelCT isa Q (.seq (.block [.mov .r8 (.reg .rbp), .shift .shr .r8 4, .alu .test .r8 (.reg .r8)])
      (.ite .e (.block []) (.seq (.block (updArgs y ++ [.mov .rcx (.reg .r12)])) (callUpdate v.callee v.suffix))))
      fun _ _ => True := by
  have r₁ := (rel_flagsC [.r12, .rbp] hDW hn (fun s₁ s₂ (h : Q s₁ s₂) => by
    obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
    exact Both.of o₁ o₂ (agree_of (l := [(.r12, P), (.rbp, BitVec.ofNat 64 len)])
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₁.r12
                      · exact a₁.rbp)
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₂.r12
                      · exact a₂.rbp))) absW1_check).wpDep
    (F := fun (σ s' : State) => One K W SP R N A D nl al n tl σ ∧ AbsPre K W SP P len σ ∧
      (s'.mem = σ.mem ∧ s'.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ (∀ r, r ≠ .r8 → s'.gpr r = σ.gpr r) ∧
        s'.rd = σ.rd ∧ s'.wr = σ.wr))
    fun s₁ s₂ (h : Q s₁ s₂) => by
      obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
      exact ⟨WP.mono (absorbW1_ok a₁.rbp a₁.buf.lt) fun _ q => ⟨o₁, a₁, q⟩,
        WP.mono (absorbW1_ok a₂.rbp a₂.buf.lt) fun _ q => ⟨o₂, a₂, q⟩⟩
  -- After the first block, in each run.
  have after : ∀ σ s', One K W SP R N A D nl al n tl σ → AbsPre K W SP P len σ →
      (s'.mem = σ.mem ∧ s'.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ (∀ r, r ≠ .r8 → s'.gpr r = σ.gpr r) ∧
        s'.rd = σ.rd ∧ s'.wr = σ.wr) →
      One K W SP R N A D nl al n tl s' ∧ AbsPre K W SP P len s' ∧ s'.gpr .r8 = BitVec.ofNat 64 (len / 16) :=
    fun σ s' o a ⟨hm, h8, hg, hrd, hwr⟩ =>
      ⟨⟨o.env.keep (fun r hr => hg r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
          hrd hwr, hm ▸ o.sl, hwr.trans o.wr⟩,
        ⟨a.buf.of_eq hrd hwr, by rw [hg _ (by decide), a.r12], by rw [hg _ (by decide), a.rbp]⟩, h8⟩
  refine RelCT.seq r₁ (RelCT.ite (fun s₁ s₂ h => eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  have hA : ∀ s₁ s₂, ((s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf) ∧ ∃ σ₁ σ₂, Q σ₁ σ₂ ∧
      (One K W SP R N A D nl al n tl σ₁ ∧ AbsPre K W SP P len σ₁ ∧ (s₁.mem = σ₁.mem ∧
        s₁.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ (∀ r, r ≠ .r8 → s₁.gpr r = σ₁.gpr r) ∧ s₁.rd = σ₁.rd ∧
        s₁.wr = σ₁.wr)) ∧
      (One K W SP R N A D nl al n tl σ₂ ∧ AbsPre K W SP P len σ₂ ∧ (s₂.mem = σ₂.mem ∧
        s₂.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ (∀ r, r ≠ .r8 → s₂.gpr r = σ₂.gpr r) ∧ s₂.rd = σ₂.rd ∧
        s₂.wr = σ₂.wr))) ∧ isa.eval .e s₁ = some false →
      (One K W SP R N A D nl al n tl s₁ ∧ AbsPre K W SP P len s₁ ∧ s₁.gpr .r8 = BitVec.ofNat 64 (len / 16)) ∧
      (One K W SP R N A D nl al n tl s₂ ∧ AbsPre K W SP P len s₂ ∧ s₂.gpr .r8 = BitVec.ofNat 64 (len / 16)) :=
    fun s₁ s₂ ⟨⟨_, σ₁, σ₂, _, ⟨o₁, a₁, q₁⟩, ⟨o₂, a₂, q₂⟩⟩, _⟩ => ⟨after σ₁ s₁ o₁ a₁ q₁, after σ₂ s₂ o₂ a₂ q₂⟩
  have r₂ := (rel_taintC [.r12, .r8] hDW hn (fun s₁ s₂ h => by
    obtain ⟨⟨o₁, a₁, h₁⟩, ⟨o₂, a₂, h₂⟩⟩ := hA s₁ s₂ h
    exact Both.of o₁ o₂ (agree_of (l := [(.r12, P), (.r8, BitVec.ofNat 64 (len / 16))])
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₁.r12
                      · exact h₁)
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₂.r12
                      · exact h₂))) (absWArgs_check hy)).wp
    (F₁ := fun (s : State) => UArgs s K (W + BitVec.ofNat 64 y) P (W + BitVec.ofNat 64 384) R (len / 16) ∧
      s.gpr .rsp = SP)
    (F₂ := fun (s : State) => UArgs s K (W + BitVec.ofNat 64 y) P (W + BitVec.ofNat 64 384) R (len / 16) ∧
      s.gpr .rsp = SP)
    fun s₁ s₂ h => by
      obtain ⟨⟨o₁, a₁, h₁⟩, ⟨o₂, a₂, h₂⟩⟩ := hA s₁ s₂ h
      exact ⟨absorbWArgs_ok L o₁.env hR o₁.sl.rounds hy a₁.buf a₁.r12 h₁,
        absorbWArgs_ok L o₂.env hR o₂.sl.rounds hy a₂.buf a₂.r12 h₂⟩
  exact RelCT.seq r₂ (upd_rel v _ fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩)

theorem absT1_check : ∃ hc, ((taint.check (ccmT [.r12, .rbp])
    (.block [.mov .rcx (.reg .rbp), .alu .and .rcx (imm 15), .alu .test .rcx (.reg .rcx)]) hc).map (·.flags)) =
      some true := ⟨_, by taint_decide⟩

theorem absT2_check : ∃ hc, (taint.check (ccmT [.rcx, .r12, .rbp])
    (.seq (.block (zero16 bO ++ [.mov .rsi (.reg .rbp), .alu .sub .rsi (.reg .rcx), .alu .add .rsi (.reg .r12)] ++
      ptr .rdi .r15 bO)) copyLoop) hc).isSome = true := ⟨_, by taint_decide⟩

/-- The last bytes, in two runs. -/
theorem absorbTail_rel (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → One K W SP R N A D nl al n tl s₁ ∧ One K W SP R N A D nl al n tl s₂ ∧
      AbsPre K W SP P len s₁ ∧ AbsPre K W SP P len s₂) :
    RelCT isa Q (.seq (.block [.mov .rcx (.reg .rbp), .alu .and .rcx (imm 15), .alu .test .rcx (.reg .rcx)])
        (.ite .e (.block [])
          (.seq (.block (zero16 bO ++ [.mov .rsi (.reg .rbp), .alu .sub .rsi (.reg .rcx), .alu .add .rsi (.reg .r12)] ++
              ptr .rdi .r15 bO))
            (.seq copyLoop (updBlock v.callee v.suffix y)))))
      fun _ _ => True := by
  have r₁ := (rel_flagsC [.r12, .rbp] hDW hn (fun s₁ s₂ (h : Q s₁ s₂) => by
    obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
    exact Both.of o₁ o₂ (agree_of (l := [(.r12, P), (.rbp, BitVec.ofNat 64 len)])
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₁.r12
                      · exact a₁.rbp)
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₂.r12
                      · exact a₂.rbp))) absT1_check).wpDep
    (F := fun (σ s' : State) => One K W SP R N A D nl al n tl σ ∧ AbsPre K W SP P len σ ∧
      (s'.mem = σ.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧ (∀ r, r ≠ .rcx → s'.gpr r = σ.gpr r) ∧
        s'.rd = σ.rd ∧ s'.wr = σ.wr ∧ s'.zf = some (decide (len % 16 = 0))))
    fun s₁ s₂ (h : Q s₁ s₂) => by
      obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
      exact ⟨WP.mono (absorbT1_ok a₁.rbp a₁.buf.lt) fun _ q => ⟨o₁, a₁, q⟩,
        WP.mono (absorbT1_ok a₂.rbp a₂.buf.lt) fun _ q => ⟨o₂, a₂, q⟩⟩
  have after : ∀ σ s', One K W SP R N A D nl al n tl σ → AbsPre K W SP P len σ →
      (s'.mem = σ.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧ (∀ r, r ≠ .rcx → s'.gpr r = σ.gpr r) ∧
        s'.rd = σ.rd ∧ s'.wr = σ.wr ∧ s'.zf = some (decide (len % 16 = 0))) →
      One K W SP R N A D nl al n tl s' ∧ AbsPre K W SP P len s' ∧ s'.gpr .rcx = BitVec.ofNat 64 (len % 16) :=
    fun σ s' o a ⟨hm, hc, hg, hrd, hwr, _⟩ =>
      ⟨⟨o.env.keep (fun r hr => hg r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
          hrd hwr, hm ▸ o.sl, hwr.trans o.wr⟩,
        ⟨a.buf.of_eq hrd hwr, by rw [hg _ (by decide), a.r12], by rw [hg _ (by decide), a.rbp]⟩, hc⟩
  refine RelCT.seq r₁ (RelCT.ite (fun s₁ s₂ h => eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  have hA : ∀ s₁ s₂, ((s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf) ∧ ∃ σ₁ σ₂, Q σ₁ σ₂ ∧
      (One K W SP R N A D nl al n tl σ₁ ∧ AbsPre K W SP P len σ₁ ∧ (s₁.mem = σ₁.mem ∧
        s₁.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧ (∀ r, r ≠ .rcx → s₁.gpr r = σ₁.gpr r) ∧ s₁.rd = σ₁.rd ∧
        s₁.wr = σ₁.wr ∧ s₁.zf = some (decide (len % 16 = 0)))) ∧
      (One K W SP R N A D nl al n tl σ₂ ∧ AbsPre K W SP P len σ₂ ∧ (s₂.mem = σ₂.mem ∧
        s₂.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧ (∀ r, r ≠ .rcx → s₂.gpr r = σ₂.gpr r) ∧ s₂.rd = σ₂.rd ∧
        s₂.wr = σ₂.wr ∧ s₂.zf = some (decide (len % 16 = 0))))) ∧ isa.eval .e s₁ = some false →
      (One K W SP R N A D nl al n tl s₁ ∧ AbsPre K W SP P len s₁ ∧ s₁.gpr .rcx = BitVec.ofNat 64 (len % 16)) ∧
      (One K W SP R N A D nl al n tl s₂ ∧ AbsPre K W SP P len s₂ ∧ s₂.gpr .rcx = BitVec.ofNat 64 (len % 16)) ∧
      len % 16 ≠ 0 :=
    fun s₁ s₂ ⟨⟨_, σ₁, σ₂, _, ⟨o₁, a₁, q₁⟩, ⟨o₂, a₂, q₂⟩⟩, he⟩ => by
      refine ⟨after σ₁ s₁ o₁ a₁ q₁, after σ₂ s₂ o₂ a₂ q₂, fun h0 => ?_⟩
      rw [show isa.eval .e s₁ = s₁.zf from rfl, q₁.2.2.2.2.2, h0] at he; cases he
  have r₂ := (rel_taintC [.rcx, .r12, .rbp] hDW hn (fun s₁ s₂ h => by
    obtain ⟨⟨o₁, a₁, h₁⟩, ⟨o₂, a₂, h₂⟩, -⟩ := hA s₁ s₂ h
    exact Both.of o₁ o₂ (agree_of (l := [(.rcx, BitVec.ofNat 64 (len % 16)), (.r12, P), (.rbp, BitVec.ofNat 64 len)])
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl | rfl
                      · exact h₁
                      · exact a₁.r12
                      · exact a₁.rbp)
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl | rfl
                      · exact h₂
                      · exact a₂.r12
                      · exact a₂.rbp))) absT2_check).wpDep
    (F := fun (σ s' : State) => One K W SP R N A D nl al n tl σ ∧
      (Env K W SP s' ∧ Frame [⟨W + BitVec.ofNat 64 32, 16⟩] σ.mem s'.mem ∧ s'.rd = σ.rd ∧ s'.wr = σ.wr))
    fun s₁ s₂ h => by
      obtain ⟨⟨o₁, a₁, h₁⟩, ⟨o₂, a₂, h₂⟩, h0⟩ := hA s₁ s₂ h
      exact ⟨WP.mono (absorbT2_ok o₁.env a₁.buf a₁.r12 a₁.rbp h₁ h0) fun _ q => ⟨o₁, q⟩,
        WP.mono (absorbT2_ok o₂.env a₂.buf a₂.r12 a₂.rbp h₂ h0) fun _ q => ⟨o₂, q⟩⟩
  have hm : ∀ r ∈ [(⟨W + BitVec.ofNat 64 32, 16⟩ : Region)], ∃ r' ∈ mutR W SP D n, Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  refine rel_assoc (RelCT.seq r₂ (updBlock_rel v L hR hDW hn hy (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    fun s₁ s₂ h => ?_))
  obtain ⟨-, σ₁, σ₂, -, ⟨o₁, E₁, f₁, -, w₁⟩, ⟨o₂, E₂, f₂, -, w₂⟩⟩ := h
  exact ⟨E₁, E₂, slots_mut L hDW (f₁.sub hm) o₁.sl, slots_mut L hDW (f₂.sub hm) o₂.sl, w₁.trans o₁.wr,
    w₂.trans o₂.wr, fun _ h => nomatch h⟩

/-- What the pieces of the MAC write, within what the pieces may write. -/
theorem macR_mut (W SP D : Addr) (n : Nat) {y : Nat} (hy : y + 16 ≤ 112) :
    ∀ r ∈ macR W SP y, ∃ r' ∈ mutR W SP D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, Offset.sub_base W hy⟩
  · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- After a piece of the MAC, the public facts of a run. -/
theorem One.macR {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} (L : Lay K W SP)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {y : Nat} (hy : y + 16 ≤ 112) {s s' : State}
    (o : One K W SP R N A D nl al n tl s) (E : Env K W SP s') (hf : Frame (macR W SP y) s.mem s'.mem)
    (hwr : s'.wr = s.wr) : One K W SP R N A D nl al n tl s' :=
  ⟨E, slots_mut L hDW (hf.sub (macR_mut W SP D n hy)) o.sl, hwr.trans o.wr⟩

/-- `absorbPad y` in two runs. -/
theorem absorbPad_rel (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → One K W SP R N A D nl al n tl s₁ ∧ One K W SP R N A D nl al n tl s₂ ∧
      AbsPre K W SP P len s₁ ∧ AbsPre K W SP P len s₂) :
    RelCT isa Q (absorbPad v.callee v.suffix y) fun _ _ => True := by
  have hy16 : y + 16 ≤ 112 := by omega
  have r₁ := (absorbWhole_rel v L hR hDW hn hy hQ).wpDep
    (F := fun (σ s' : State) => One K W SP R N A D nl al n tl σ ∧ AbsPre K W SP P len σ ∧
      ∃ Y, @Absorbed K W SP σ y P len Y s')
    fun s₁ s₂ h => by
      obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
      exact ⟨WP.mono (absorbWhole_ok v L o₁.env hR o₁.sl.rounds hy a₁.buf a₁.r12 a₁.rbp) fun _ q => ⟨o₁, a₁, _, q⟩,
        WP.mono (absorbWhole_ok v L o₂.env hR o₂.sl.rounds hy a₂.buf a₂.r12 a₂.rbp) fun _ q => ⟨o₂, a₂, _, q⟩⟩
  refine rel_assoc (RelCT.seq r₁ (absorbTail_rel v L hR hDW hn hy (N := N) (A := A) (nl := nl) (al := al)
    (tl := tl) (P := P) (len := len) fun s₁ s₂ h => ?_))
  obtain ⟨-, σ₁, σ₂, -, ⟨o₁, a₁, _, A₁⟩, ⟨o₂, a₂, _, A₂⟩⟩ := h
  exact ⟨o₁.macR L hDW hy16 A₁.env A₁.frame A₁.wr, o₂.macR L hDW hy16 A₂.env A₂.frame A₂.wr,
    ⟨a₁.buf.of_eq A₁.rd A₁.wr, A₁.r12, A₁.rbp⟩, ⟨a₂.buf.of_eq A₂.rd A₂.wr, A₂.r12, A₂.rbp⟩⟩

end VG.Proof.AesCcm.X86_64