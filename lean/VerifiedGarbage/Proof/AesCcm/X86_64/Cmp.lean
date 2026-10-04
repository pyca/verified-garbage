import VerifiedGarbage.Proof.AesCcm.X86_64.Run

/-!
# AES-CCM on x86-64: checking a received tag (`recv`, `cmp o`)

Untrusted: everything here is checked by Lean. These are AES-GCM's pieces
(`recv` as it reads the received tag from the working space), with AES-CCM's
working space: `recv` pads the `rbx` bytes of the received tag
at `W` with zeros at `W + 256` (`recv_ok`); `cmp o` pads the first `rbx`
bytes of the tag at `W + o` at `W + 240` and leaves 1 in `rax` if they are
the received ones, 0 if not (`cmp_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr cmp vO rO copyLoop)
open VG.Impl.AesCcm.X86_64 (recv)
open VG.Proof.AesGcm.X86_64 (LoopPre copyLoop_ok)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Proof.Cmac (le8)

/-- `xs` written over 16 zero bytes at `P`. -/
theorem pad_bytes (m : Mem) (P : Addr) (xs : List Byte) (hx : xs.length ≤ 16) :
    bytesAt (writeBytes ((m.writeW P (0 : BitVec 64)).writeW (P + BitVec.ofNat 64 8) (0 : BitVec 64)) P xs) P 16 =
      xs ++ zeros (16 - xs.length) := by
  have h := bytesAt_writeBytes_at ((m.writeW P (0 : BitVec 64)).writeW (P + BitVec.ofNat 64 8) (0 : BitVec 64)) P
    (o := 0) (n := 16) xs (by omega) (by decide)
  rw [BitVec.add_zero] at h
  rw [h, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero, List.take_zero, List.nil_append, Nat.zero_add]
  show xs ++ (Spec.Cmac.zeros 16).drop xs.length = _
  simp only [Spec.Cmac.zeros, List.drop_replicate, zeros]

theorem le8_inj {a b : BitVec 64} (h : le8 a = le8 b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (fun l => (l.getD (i / 8) 0).getLsbD (i % 8)) h
  simp only [Proof.Cmac.getD_le8 _ (show i / 8 < 8 by omega), BitVec.getLsbD_extractLsb',
    show i % 8 < 8 by omega, decide_true, Bool.true_and, show 8 * (i / 8) + i % 8 = i by omega] at e
  exact e

/-- Two blocks are equal iff the OR of the XORs of their words is 0. -/
theorem words_eq (m : Mem) (p q : Addr) :
    ((m.readW p 64 ^^^ m.readW q 64) ||| (m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64)
      = 0) ↔ bytesAt m p 16 = bytesAt m q 16 := by
  rw [Proof.Cmac.bytesAt_split m p, Proof.Cmac.bytesAt_split m q, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW]
  constructor
  · intro h
    have h₁ : m.readW p 64 ^^^ m.readW q 64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (·.getLsbD i) h; simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero] at this ⊢
      simp_all
    have h₂ : m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (·.getLsbD i) h; simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero] at this ⊢
      simp_all
    rw [BitVec.xor_eq_zero_iff.mp h₁, BitVec.xor_eq_zero_iff.mp h₂]
  · intro h
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [Proof.Cmac.length_le8, Proof.Cmac.length_le8])
    rw [le8_inj h₁, le8_inj h₂, BitVec.xor_self, BitVec.xor_self, BitVec.or_self]; rfl

theorem zero16_frame (m : Mem) (p : Addr) :
    Frame [⟨p, 16⟩] m ((m.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)) :=
  Proof.Cmac.frame_store2 _ _ _

theorem writeBytes_frame' (m : Mem) {q : Addr} {xs : List Byte} {n : Nat} (hn : xs.length = n) :
    Frame [⟨q, n⟩] m (writeBytes m q xs) :=
  writeBytes_frame m q xs (by rw [hn]; exact Region.contains_self _ _)

section
variable {K W SP : Addr} (L : Lay K W SP)
include L

/-- `recv`: the `t` bytes of the received tag at `W`, padded at `W + 256`. -/
theorem recv_ok {s : State} (he : Env K W SP s) {t : Nat} (hbx : s.gpr .rbx = BitVec.ofNat 64 t)
    (h1 : 1 ≤ t) (h16 : t ≤ 16) :
    WP isa recv s fun s' => Env K W SP s' ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 256) 16 = bytesAt s.mem W t ++ zeros (16 - t) ∧
      Frame [⟨W + BitVec.ofNat 64 256, 16⟩] s.mem s'.mem ∧ s'.gpr .rbx = s.gpr .rbx ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h15 := he.r15
  have w₁ := he.perm.wW (show 256 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 264 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hm₁, hdi, hsi, hcx, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r15 rO) .rax, .store (at_ .r15 (rO + 8)) .rax] ++
        ptr .rdi .r15 rO ++ [.mov .rsi (.reg .r15), .mov .rcx (.reg .rbx)]) s = some s₁ ∧
      s₁.mem = (s.mem.writeW (W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
        (W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₁.gpr .rdi = W + BitVec.ofNat 64 256 ∧ s₁.gpr .rsi = W ∧ s₁.gpr .rcx = BitVec.ofNat 64 t ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [rO, h15, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, add_ofNat_assoc]; rfl
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg, hbx]
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env K W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have dW : (⟨W, t⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 16⟩ := by
    simpa using L.w_w (a := 0) (n := t) (d := 256) (k := 16) (.inl (by omega)) (by omega) (by decide)
  have lp : LoopPre s₁ W (W + BitVec.ofNat 64 256) t :=
    ⟨hsi, hdi, hcx, h1, by omega, covers_left (by simpa using he₁.perm.wC (d := 0) (n := t) (by omega)),
      he₁.perm.wC (by omega), dW.sub_right (Region.sub_prefix h16)⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ?_
  have fz : Frame [⟨W + BitVec.ofNat 64 256, 16⟩] s.mem s₁.mem := by rw [hm₁]; exact zero16_frame _ _
  have hR : bytesAt s₁.mem W t = bytesAt s.mem W t :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW) (by omega)
  have hlen := length_bytesAt s₁.mem W t
  refine ⟨he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂, ?_, ?_, ?_,
    by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁]⟩
  · rw [hm₂, hm₁, pad_bytes _ _ _ (by rw [length_bytesAt]; exact h16), length_bytesAt, ← hm₁, hR]
  · refine fz.trans ?_
    rw [hm₂]
    exact (writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix h16⟩
  · rw [hg₂ _ (by decide) (by decide), hg₁ _ (by decide) (by decide) (by decide) (by decide)]

/-- `cmp o`: 1 in `rax` iff the first `t` bytes of the tag at `W + o` are
the received tag `T`, padded at `W + 256`. -/
theorem cmp_ok {o : Nat} (ho : o + 16 ≤ 240) {s : State} (he : Env K W SP s) {t : Nat}
    (hbx : s.gpr .rbx = BitVec.ofNat 64 t) (h1 : 1 ≤ t) (h16 : t ≤ 16) {T : List Byte} (hTl : T.length = t)
    (hT : bytesAt s.mem (W + BitVec.ofNat 64 256) 16 = T ++ zeros (16 - t)) :
    WP isa (cmp o) s fun s' => Env K W SP s' ∧
      s'.gpr .rax = (if bytesAt s.mem (W + BitVec.ofNat 64 o) t = T then 1 else 0) ∧
      Frame [⟨W + BitVec.ofNat 64 240, 16⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h15 := he.r15
  have w₁ := he.perm.wW (show 240 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 248 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hm₁, hdi, hsi, hcx, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r15 vO) .rax, .store (at_ .r15 (vO + 8)) .rax] ++
        ptr .rdi .r15 vO ++ ptr .rsi .r15 o ++ [.mov .rcx (.reg .rbx)]) s = some s₁ ∧
      s₁.mem = (s.mem.writeW (W + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₁.gpr .rdi = W + BitVec.ofNat 64 240 ∧ s₁.gpr .rsi = W + BitVec.ofNat 64 o ∧
      s₁.gpr .rcx = BitVec.ofNat 64 t ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    have hoi : o < 2 ^ 31 := by omega
    refine ⟨_, by crun [vO, h15, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, add_ofNat_assoc]; rfl
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg, h15, imm_eq hoi]
    · simp [gpr_setReg, hbx]
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env K W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have dW : (⟨W + BitVec.ofNat 64 o, t⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 240, 16⟩ :=
    L.w_w (.inl (by omega)) (by omega) (by decide)
  have lp : LoopPre s₁ (W + BitVec.ofNat 64 o) (W + BitVec.ofNat 64 240) t :=
    ⟨hsi, hdi, hcx, h1, by omega, covers_left (he₁.perm.wC (by omega)), he₁.perm.wC (by omega),
      dW.sub_right (Region.sub_prefix h16)⟩
  refine WP.seq (WP.mono (copyLoop_ok s₁ lp) fun s₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ?_)
  have fz : Frame [⟨W + BitVec.ofNat 64 240, 16⟩] s.mem s₁.mem := by rw [hm₁]; exact zero16_frame _ _
  have hT' : bytesAt s₁.mem (W + BitVec.ofNat 64 o) t = bytesAt s.mem (W + BitVec.ofNat 64 o) t :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW) (by omega)
  have hlen := length_bytesAt s₁.mem (W + BitVec.ofNat 64 o) t
  have f₂ : Frame [⟨W + BitVec.ofNat 64 240, 16⟩] s.mem s₂.mem := by
    refine fz.trans ?_
    rw [hm₂]
    exact (writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix h16⟩
  have hV : bytesAt s₂.mem (W + BitVec.ofNat 64 240) 16 =
      bytesAt s.mem (W + BitVec.ofNat 64 o) t ++ zeros (16 - t) := by
    rw [hm₂, hm₁, pad_bytes _ _ _ (by rw [length_bytesAt]; exact h16), length_bytesAt, ← hm₁, hT']
  have hT₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 256) 16 = T ++ zeros (16 - t) := by
    rw [bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide), hT]
  have he₂ : Env K W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂
  have r₁ := he₂.perm.wR (show 240 + 8 ≤ 2560 by decide)
  have r₂ := he₂.perm.wR (show 256 + 8 ≤ 2560 by decide)
  have r₃ := he₂.perm.wR (show 248 + 8 ≤ 2560 by decide)
  have r₄ := he₂.perm.wR (show 264 + 8 ≤ 2560 by decide)
  have h15₂ := he₂.r15
  generalize hX : (s₂.mem.readW (W + BitVec.ofNat 64 240) 64 ^^^ s₂.mem.readW (W + BitVec.ofNat 64 256) 64) |||
    (s₂.mem.readW (W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) 64 ^^^
      s₂.mem.readW (W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) 64) = X
  have hXe : X = 0 ↔ bytesAt s.mem (W + BitVec.ofNat 64 o) t = T := by
    rw [← hX, words_eq, hV, hT₂]
    constructor
    · intro e; exact List.append_cancel_right e
    · intro e; rw [e]
  have e248 : W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 248 := add_ofNat_assoc ..
  have e264 : W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 264 := add_ofNat_assoc ..
  rw [e248, e264] at hX
  obtain ⟨s₃, run₃, hax, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
      [.mov .rax (.mem (at_ .r15 vO)), .alu .xor .rax (.mem (at_ .r15 rO)),
        .mov .rdx (.mem (at_ .r15 (vO + 8))), .alu .xor .rdx (.mem (at_ .r15 (rO + 8))),
        .alu .or .rax (.reg .rdx), .alu .cmp .rax (imm 1), .mov32 .rax (imm 0), .alu32 .adc .rax (imm 0)] s₂ =
        some s₃ ∧ s₃.gpr .rax = (if X = 0 then 1 else 0) ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], s₃.gpr r = s₂.gpr r) ∧
      s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by crun [vO, rO, h15₂, r₁, r₂, r₃, r₄, execAlu32], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, cf_setReg, cf_arithFlags, ite_true, ite_false, reduceCtorEq, hX]
      by_cases e : X = 0
      · subst e; rfl
      · have : ¬ X.toNat < 1 := fun h => e (BitVec.eq_of_toNat_eq (by simp; omega))
        simp only [e, ite_false, show (1#64 : BitVec 64).toNat = 1 from rfl, this, decide_false]
        rfl
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  exact WP.of_runBlock ⟨s₃, run₃, he₂.keep hg₃ hrd₃ hwr₃, by rw [hax]; simp only [hXe], hm₃ ▸ f₂,
    by rw [hrd₃, hrd₂, hrd₁], by rw [hwr₃, hwr₂, hwr₁]⟩

end

end VG.Proof.AesCcm.X86_64
