import VerifiedGarbage.Proof.AesCcm.X86.Absorb

/-!
# AES-CCM on x86: `absorbPad y` is constant time

Untrusted: everything here is checked by Lean. What `absorbPad` starts from
(`PadPre`) is public: the pointers and the length it branches on, and the
slots holding them; its pieces are constant time from it (`absorbWhole_ct`,
`absorbTail_ct`, `absorbPad_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4 splitWhole dO nO)
open VG.Proof.AesGcm.X86 (CT w64 slotv WEnv padLoop_ok)

/-- The slots are kept when `dO` and `nO` are written. -/
theorem dn_kept {W : BitVec 32} {m m' : Mem} {a b : BitVec 32}
    (hm : m' = (m.writeW (w64 W + BitVec.ofNat 64 dO) a).writeW (w64 W + BitVec.ofNat 64 nO) b) {o : Nat}
    (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 240) : slotv m' W o = slotv m W o := by
  have f₁ : Frame [wC W] m m' := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 272) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 276) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))
  exact f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide))
    (by decide)

/-- `dO` and `nO`, after they are written. -/
theorem dn_read {W : BitVec 32} {m m' : Mem} {a b : BitVec 32}
    (hm : m' = (m.writeW (w64 W + BitVec.ofNat 64 dO) a).writeW (w64 W + BitVec.ofNat 64 nO) b) :
    slotv m' W dO = a ∧ slotv m' W nO = b := by
  subst hm
  refine ⟨?_, Mem.readW_writeW_self32 _ _ _⟩
  rw [slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
  exact Mem.readW_writeW_self32 _ _ _

/-- What `absorbPad` of the `len` bytes at `P` starts from. -/
structure PadPre (K W SP : BitVec 32) (R : Nat) (P : BitVec 32) (len : Nat) (s : State) : Prop where
  env : Env K W SP s
  ctx : slotv s.mem W ctxO = K
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  buf : 0 < len → Buf W SP s P len
  d : slotv s.mem W dO = P
  n : slotv s.mem W nO = BitVec.ofNat 32 len

/-- The arguments of the call chaining the whole blocks, from `ebp` and
`edi`. -/
theorem wholeArgs_ct {y : Nat} (hy : y = 0 ∨ y = 96) {I : State → Prop} {c : Prog isa} {F : State → State → Prop}
    (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.ebp, .edi], s₁.gpr r = s₂.gpr r)
    (blk : ∀ s, I s → ∃ s', runBlock isa (keyArgs y ++ ([.mov .esi (.reg .edi)] : List Instr) ++ updScr) s = some s' ∧ F s s')
    (h₂ : CT (fun s' => ∃ s, I s ∧ F s s') c) :
    CT I (.seq (.block (keyArgs y ++ ([.mov .esi (.reg .edi)] : List Instr) ++ updScr)) c) := by
  rcases hy with rfl | rfl
  · exact CT.block_seq [.ebp, .edi] hr (by taint_decide) blk h₂
  · exact CT.block_seq [.ebp, .edi] hr (by taint_decide) blk h₂

theorem absorbWhole_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : BitVec 32} {len : Nat} (hl : len < 2 ^ 32) :
    CT (PadPre K W SP R P len) (.seq (.block splitWhole)
        (.ite .e (.block []) (.seq (.block (keyArgs y ++ ([.mov .esi (.reg .edi)] : List Instr) ++ updScr)) (updCall v.callee v.suffix)))) := by
  refine CT.block_seq [.ebp] (pin_ebp fun s h => h.env.ebp) (by taint_decide)
    (fun s hs => split_ok L hs.env hs.d hs.n hl) ?_
  refine CT.ite (decide (len / 16 = 0)) (fun _ ⟨_, _, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil) fun hf => ?_
  have h0 : len / 16 ≠ 0 := of_decide_eq_false hf
  have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  refine wholeArgs_ct hy (pin2 fun _ ⟨_, _, _, hdi, _, hbp, _⟩ => ⟨hbp, hdi⟩)
    (fun s₁ ⟨s, hs, hbx, hdi, _, hbp, hsp, hm₁, hrd₁, hwr₁⟩ =>
      wholeArgs_ok L ⟨hbp, hsp, hs.env.perm.of_eq hrd₁ hwr₁⟩
        (by rw [split_kept hm₁ (by decide) (by decide)]; exact hs.ctx)
        (by rw [split_kept hm₁ (by decide) (by decide)]; exact hs.rounds) hbx hdi y) ?_
  refine updCall_ct v L hR (y := y) (Q := P) (n := len / 16) (by rcases hy with rfl | rfl <;> decide) (by omega_arith)
    fun s₂ ⟨s₁, ⟨s, hs, _, _, _, _, _, _, hrd₁, hwr₁⟩, _, ax, cx, dx, bx, si, di, bp, sp, rd₂, wr₂⟩ => ?_
  have hP := hs.buf (by omega_arith)
  exact ⟨⟨bp, sp, hs.env.perm.of_eq (by rw [rd₂, hrd₁]) (by rw [wr₂, hwr₁])⟩,
    srcBuf ((hP.take hb).of_eq (by rw [rd₂, hrd₁]) (by rw [wr₂, hwr₁])),
    (hP.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by rcases hy with rfl | rfl <;> decide)),
    ax, cx, dx, bx, si, di⟩

/-- What the last bytes' piece starts from. -/
structure TailPre (K W SP : BitVec 32) (R : Nat) (Q : BitVec 32) (t : Nat) (s : State) : Prop where
  env : Env K W SP s
  ctx : slotv s.mem W ctxO = K
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  buf : 0 < t → Buf W SP s Q t
  d : slotv s.mem W dO = Q
  n : slotv s.mem W nO = BitVec.ofNat 32 t

theorem absorbTail_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) {Q : BitVec 32} {t : Nat} (ht : t < 16) :
    CT (TailPre K W SP R Q t) (.seq (.block [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)])
        (.ite .e (.block [])
          (.seq (.block (zero4 blkO ++ ([.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm blkO),
              .mov .ecx (slot nO)] : List Instr)))
            (.seq copyLoop (updBlock v.callee v.suffix y))))) := by
  refine CT.block_seq [.ebp] (pin_ebp fun s h => h.env.ebp) (by taint_decide)
    (fun s hs => testN_ok L hs.env (r := t) (by omega_arith) hs.n) ?_
  refine CT.ite (decide (t = 0)) (fun _ ⟨_, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil) fun hf => ?_
  have h0 : t ≠ 0 := of_decide_eq_false hf
  refine CT.block_seq [.ebp] (pin_ebp fun _ ⟨_, _, _, _, hbp, _⟩ => hbp) (by taint_decide)
    (fun s₁ ⟨s, hs, hm₁, _, hbp, hsp, hrd₁, hwr₁⟩ =>
      tailArgs_ok L ⟨hbp, hsp, hs.env.perm.of_eq hrd₁ hwr₁⟩ (Q := Q) (t := t) (by rw [hm₁]; exact hs.d)
        (by rw [hm₁]; exact hs.n)) ?_
  refine CT.seq (J := fun s₃ => Env K W SP s₃ ∧ slotv s₃.mem W ctxO = K ∧ slotv s₃.mem W roundsO = BitVec.ofNat 32 R)
    (Proof.AesGcm.X86.copyLoop_ct (pin3 fun _ ⟨_, _, _, hdi, hdx, hcx, _⟩ => ⟨hdi, hdx, hcx⟩))
    (fun s₂ ⟨s₁, ⟨s, hs, hm₁, _, _, _, hrd₁, hwr₁⟩, hm₂, hdi, hdx, hcx, hbp₂, hsp₂, hrd₂, hwr₂⟩ => ?_)
    (updBlock_ct v L hR hy fun _ h => h)
  have hB := hs.buf (by omega_arith)
  have he : WEnv W s₂ := ⟨hbp₂, by rw [hwr₂, hwr₁]; exact hs.env.perm.w, L.fw⟩
  refine WP.mono (padLoop_ok (S := Q) (d := 32) (t := t) (m := s₁.mem) he hm₂ hdi hdx hcx (by omega_arith)
    (by omega_arith) (by rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact hB.rd) hB.wrap (hB.w.sub_right (Lay.wSub (by decide)))
    (by decide)) fun s₃ ⟨_, f₃, g₃, rd₃, wr₃⟩ => ?_
  have k₃ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ => by
    rw [← hm₁]
    exact f₃.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide))
      (by decide)
  exact ⟨⟨by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hbp₂],
      by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hsp₂],
      hs.env.perm.of_eq (by rw [rd₃, hrd₂, hrd₁]) (by rw [wr₃, hwr₂, hwr₁])⟩,
    by rw [k₃ _ (by decide) (by decide)]; exact hs.ctx, by rw [k₃ _ (by decide) (by decide)]; exact hs.rounds⟩

theorem absorbPad_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : BitVec 32} {len : Nat} (hl : len < 2 ^ 32) :
    CT (PadPre K W SP R P len) (absorbPad v.callee v.suffix y) := by
  refine RelCT.assoc (CT.seq (J := TailPre K W SP R (P + BitVec.ofNat 32 (16 * (len / 16))) (len % 16))
    (absorbWhole_ct v L hR hy hl)
    (fun s hs => WP.mono (absorbWhole_ok v L hs.env hR hs.ctx hs.rounds hy hs.buf hl hs.d hs.n)
      fun s₁ ⟨A₁, hd₁, hn₁⟩ => ⟨A₁.env, by rw [slot_kept L hy A₁.frame (by decide) (by decide)]; exact hs.ctx,
        by rw [slot_kept L hy A₁.frame (by decide) (by decide)]; exact hs.rounds, fun h => ?_, hd₁, hn₁⟩)
    (absorbTail_ct v L hR hy (Nat.mod_lt _ (by decide))))
  have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  have hP := hs.buf (by omega_arith)
  have := (hP.drop hb (by have := hP.wrap; omega_arith)).of_eq A₁.rd A₁.wr
  rwa [show len - 16 * (len / 16) = len % 16 by omega_arith] at this

end VG.Proof.AesCcm.X86
