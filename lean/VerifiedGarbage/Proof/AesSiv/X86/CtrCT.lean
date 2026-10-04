import VerifiedGarbage.Proof.AesSiv.X86.Ctr

/-!
# AES-SIV on x86: CTR is constant time

Untrusted: everything here is checked by Lean. The branches of `ctr` are on
the length of the data, and the addresses on `ebp` and the data's address
(pinned where the XOR uses them); the calls of `vg_aes_ctr32` are constant
time by their contract.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 xorLoop)
open VG.Proof.AesGcm.X86 (w64 slotv CT xorLoop_ct)

/-- What CTR starts from, but the counter: the data and its slots. -/
structure CtrPre (C W SP : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (s : State) : Prop where
  env : Env C W SP s
  dat : Dat C W SP s D n
  n32 : n < 2 ^ 32
  ctx : slotv s.mem W ctxO = C
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  data : slotv s.mem W dataO = D
  len : slotv s.mem W lenO = BitVec.ofNat 32 n

theorem ctrWhole_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32} {n : Nat} :
    CT (CtrPre C W SP R D n) (ctrWhole v.callee) := by
  refine CT.block_seq [.ebp] (pin_ebp fun s h => h.env.ebp) (by taint_decide)
    (fun s hs => whole1_ok L hs.env hs.len hs.n32) ?_
  refine CT.ite (decide (n / 16 = 0)) (fun s ⟨_, _, _, zf, _⟩ => eval_e zf) (fun _ => CT.nil) (fun _ => ?_)
  refine CT.block_seq [.ebp] (pin_ebp fun s₁ ⟨s, hs, _, _, g, _⟩ => by rw [g _ (by decide), hs.env.ebp])
    (by taint_decide) (fun s₁ ⟨s, hs, _, _, g, m, rd, wr⟩ =>
      ctrArgs_ok (C := C) (R := R) (D := D) L ⟨by rw [g _ (by decide), hs.env.ebp],
        by rw [g _ (by decide), hs.env.esp], hs.env.perm.of_eq rd wr⟩
        (by rw [m]; exact hs.ctx) (by rw [m]; exact hs.rounds) (by rw [m]; exact hs.data)) ?_
  exact ctrCall_ct v L hR (c := cbOff) (by decide) (D := D) (n := n / 16)
    fun s₂ ⟨s₁, ⟨s, hs, di₁, _, g₁, _, rd₁, wr₁⟩, ax, cx, dx, bx, g₂, _, rd₂, wr₂⟩ =>
      ⟨⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), hs.env.ebp],
        by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), hs.env.esp],
        hs.env.perm.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁)⟩,
        (hs.dat.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁)).dst (Nat.mul_div_le n 16) (by decide),
        ax, cx, dx, bx, by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), di₁]⟩

theorem tailArgs_ct {W : BitVec 32} {I : State → Prop} (hI : ∀ s, I s → s.gpr .ebp = W) :
    CT I (.block (zero4 ksOff ++ ctrArgs ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksOff),
      .mov .edi (imm 1)] : List Instr))) :=
  CT.taint [.ebp] (pin_ebp hI) (by taint_decide)

theorem ctrTail_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32} {n : Nat} :
    CT (CtrPre C W SP R D n) (ctrTail v.callee) := by
  refine CT.block_seq [.ebp] (pin_ebp fun s h => h.env.ebp) (by taint_decide)
    (fun s hs => tail1_ok L hs.env hs.len hs.n32) ?_
  refine CT.ite (decide (n % 16 = 0)) (fun s ⟨_, _, _, zf, _⟩ => eval_e zf) (fun _ => CT.nil) (fun _ => ?_)
  -- After the call: the data and its slots.
  have pre₁ : ∀ s₁, (∃ s, CtrPre C W SP R D n s ∧ s₁.gpr .ecx = BitVec.ofNat 32 (n % 16) ∧
      s₁.zf = some (decide (n % 16 = 0)) ∧ (∀ r, r ≠ .ecx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr) → CtrPre C W SP R D n s₁ := fun s₁ ⟨s, hs, _, _, g, m, rd, wr⟩ =>
    ⟨⟨by rw [g _ (by decide), hs.env.ebp], by rw [g _ (by decide), hs.env.esp], hs.env.perm.of_eq rd wr⟩,
      hs.dat.of_eq rd wr, hs.n32, by rw [m]; exact hs.ctx, by rw [m]; exact hs.rounds, by rw [m]; exact hs.data,
      by rw [m]; exact hs.len⟩
  refine CT.seq (J := fun s₂ => ∃ s₁, CtrPre C W SP R D n s₁ ∧
      s₂.mem = Cmac.zero4 s₁.mem (w64 W + BitVec.ofNat 64 ksOff) ∧
      s₂.gpr .eax = C + BitVec.ofNat 32 272 ∧ s₂.gpr .ecx = BitVec.ofNat 32 R ∧
      s₂.gpr .edx = W + BitVec.ofNat 32 cbOff ∧ s₂.gpr .ebx = W + BitVec.ofNat 32 ksOff ∧
      s₂.gpr .edi = BitVec.ofNat 32 1 ∧ s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr)
    (tailArgs_ct fun s₁ h₁ => (pre₁ s₁ h₁).env.ebp)
    (fun s₁ h₁ => let ⟨s₂, run₂, h₂⟩ := tailArgs_ok' (R := R) L (pre₁ s₁ h₁).env (pre₁ s₁ h₁).ctx (pre₁ s₁ h₁).rounds
      WP.of_runBlock ⟨s₂, run₂, s₁, pre₁ s₁ h₁, h₂⟩) ?_
  refine CT.seq (J := fun s₃ => CtrPre C W SP R D n s₃)
    (ctrCall_ct v L hR (c := cbOff) (by decide) (D := W + BitVec.ofNat 32 ksOff) (n := 1)
      fun s₂ ⟨s₁, h₁, _, ax, cx, dx, bx, di, bp, sp, rd, wr⟩ =>
        have P₂ := h₁.env.perm.of_eq rd wr
        ⟨⟨bp, sp, P₂⟩, dstW L P₂ (by decide) (by decide) (by decide), ax, cx, dx, bx, di⟩)
    (fun s₂ ⟨s₁, h₁, m₂, ax, cx, dx, bx, di, bp, sp, rd, wr⟩ =>
      have P₂ := h₁.env.perm.of_eq rd wr
      WP.mono (ctrCall_ok v L ⟨bp, sp, P₂⟩ hR (c := cbOff) (by decide) (n := 1)
        (dstW L P₂ (by decide) (by decide) (by decide)) ax cx dx bx di) fun s₃ ⟨E₃, rd₃, wr₃, _, f₃, _⟩ => by
        have f : Frame (ctrR W SP D n) s₁.mem s₃.mem := by
          refine (show Frame (ctrR W SP D n) s₁.mem s₂.mem by
            rw [m₂]; exact (Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr
              exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩).trans ?_
          rw [L.aW (o := ksOff) (by decide)] at f₃
          exact f₃.sub fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl
            · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
            · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
            · exact ⟨_, by simp, fun _ h => h⟩
            · exact ⟨_, by simp, fun _ h => h⟩
        have sl := fun {o : Nat} (a : 112 ≤ o) (b : o + 4 ≤ 256) => ctrR_slot L h₁.dat f a b
        exact ⟨E₃, h₁.dat.of_eq (rd₃.trans rd) (wr₃.trans wr), h₁.n32,
          by rw [sl (by decide) (by decide)]; exact h₁.ctx, by rw [sl (by decide) (by decide)]; exact h₁.rounds,
          by rw [sl (by decide) (by decide)]; exact h₁.data, by rw [sl (by decide) (by decide)]; exact h₁.len⟩) ?_
  refine CT.block_seq [.ebp] (pin_ebp fun s h => h.env.ebp) (by taint_decide)
    (fun s hs => xorArgs_ok L hs.env hs.data hs.len hs.n32) ?_
  exact xorLoop_ct (pin3 fun s ⟨_, _, cx, dx, di, _⟩ => ⟨di, dx, cx⟩)

/-- `ctr` is constant time from the data and its slots, whatever the counter. -/
theorem ctr_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32} {n : Nat} :
    CT (fun s => CtrPre C W SP R D n s ∧ Spec.Siv.beNat (bytesAt s.mem (w64 W + BitVec.ofNat 64 cbOff) 16) % 2 ^ 32 <
      2 ^ 31) (ctr v.callee) :=
  CT.seq (J := CtrPre C W SP R D n) ((ctrWhole_ct v L hR).mono fun _ h => h.1)
    (fun s ⟨h, hlow⟩ => WP.mono (ctrWhole_ok v L hR h.env h.dat h.n32 h.ctx h.rounds h.data h.len rfl (by have := h.n32; omega))
      fun s₄ ⟨E₄, rd₄, wr₄, f₄, _⟩ =>
        have sl := fun {o : Nat} (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 256) => ctrR_slot L h.dat f₄ h₁ h₂
        ⟨E₄, h.dat.of_eq rd₄ wr₄, h.n32, by rw [sl (by decide) (by decide)]; exact h.ctx,
          by rw [sl (by decide) (by decide)]; exact h.rounds, by rw [sl (by decide) (by decide)]; exact h.data,
          by rw [sl (by decide) (by decide)]; exact h.len⟩)
    (ctrTail_ct v L hR)

end VG.Proof.AesSiv.X86
