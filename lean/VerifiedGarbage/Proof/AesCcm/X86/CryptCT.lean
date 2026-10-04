import VerifiedGarbage.Proof.AesCcm.X86.Crypt
import VerifiedGarbage.Proof.AesCcm.X86.AbsorbCT

/-!
# AES-CCM on x86: counter mode in constant time

Untrusted: everything here is checked by Lean. `ctr` branches on the length
of the data and addresses memory by `W` and the data's address, all public
(`ctr_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 xorLoop splitWhole dO nO)
open VG.Proof.AesGcm.X86 (CT w64 slotv)

/-- What `ctr` starts from. -/
structure CtrPre (K W SP : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (s : State) : Prop where
  env : Env K W SP s
  ctx : slotv s.mem W ctxO = K
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  data : slotv s.mem W dataO = D
  len : slotv s.mem W lenO = BitVec.ofNat 32 n
  c : ∃ nonce, CtrCtx K W SP s R nonce D n

theorem ctrWhole_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : BitVec 32} {n : Nat} (hn32 : n < 2 ^ 32) :
    CT (CtrPre K W SP R D n) (.seq (.block ([.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO),
        .store (at_ .ebp nO) .eax] ++ splitWhole))
      (.ite .e (.block []) (.seq (.block ([.mov .eax (imm 1)] ++ ctrAt ++ keyArgs c1O)) (ctrCall v.callee)))) := by
  have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  refine CT.block_seq [.ebp] (pin_ebp fun _ h => h.env.ebp) (by taint_decide)
    (fun s hs => ctrSplit_ok L hs.env hs.data hs.len hn32) ?_
  refine CT.ite (decide (n / 16 = 0)) (fun _ ⟨_, _, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil) fun hf => ?_
  have h0 : n / 16 ≠ 0 := of_decide_eq_false hf
  have blk : ∀ s₁ : State, (∃ s, CtrPre K W SP R D n s ∧ s₁.gpr .ebx = D ∧ s₁.gpr .edi = BitVec.ofNat 32 (n / 16) ∧
      s₁.zf = some (decide (n / 16 = 0)) ∧ Env K W SP s₁ ∧ Frame [wC W] s.mem s₁.mem ∧
      slotv s₁.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16)) ∧ slotv s₁.mem W nO = BitVec.ofNat 32 (n % 16) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr) →
      ∃ sc, runBlock isa ([.mov .eax (imm 1)] ++ ctrAt ++ keyArgs c1O) s₁ = some sc ∧
        sc.gpr .eax = K ∧ sc.gpr .ecx = BitVec.ofNat 32 R ∧ sc.gpr .edx = W + BitVec.ofNat 32 64 ∧ sc.gpr .ebx = D ∧
        sc.gpr .edi = BitVec.ofNat 32 (n / 16) ∧ sc.gpr .ebp = W ∧ sc.gpr .esp = SP ∧ sc.rd = s₁.rd ∧
        sc.wr = s₁.wr := fun s₁ ⟨s, hs, hbx, hdi, _, E₁, f₁, _, _, rd, wr⟩ => by
    obtain ⟨nonce, C⟩ := hs.c
    have fr₁ : Frame (ctrR W SP D n) s.mem s₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨wC W, by simp, fun _ h => h⟩
    obtain ⟨sc, run, -, -, rest⟩ := ctrArgs_ok L E₁
      (by rw [C.slot_kept fr₁ (by decide) (by decide)]; exact hs.ctx)
      (by rw [C.slot_kept fr₁ (by decide) (by decide)]; exact hs.rounds) C.h7 C.h13 (C.c0_kept fr₁) (i := 1)
      (by
        have : 1 ≤ 256 ^ (15 - nonce.length) := Nat.pow_pos (by decide)
        have := C.hn
        omega) (by decide) hbx hdi
    exact ⟨sc, run, rest⟩
  refine CT.block_seq [.ebp] (pin_ebp fun _ ⟨_, _, _, _, _, E₁, _⟩ => E₁.ebp) (by taint_decide) blk ?_
  refine ctrCall_ct v L hR (c := 64) (Q := D) (n := n / 16) (by decide)
    fun sc ⟨s₁, ⟨s, hs, _, _, _, E₁, _, _, _, rd₁, wr₁⟩, ax, cx, dx, bx, di, bp, sp, rd, wr⟩ => ?_
  obtain ⟨nonce, C⟩ := hs.c
  have rdc : sc.rd = s.rd := by rw [rd, rd₁]
  have wrc : sc.wr = s.wr := by rw [wr, wr₁]
  refine ⟨⟨bp, sp, hs.env.perm.of_eq rdc wrc⟩, srcBuf ((C.buf.take hb).of_eq rdc wrc), ?_,
    (C.buf.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by decide)), C.dk.sub_right (Region.sub_prefix hb),
    ax, cx, dx, bx, di⟩
  rw [wrc]
  intro a k ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact C.dw a k ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩

/-- What `ctr`'s last bytes start from. -/
abbrev CtrTailPre (K W SP : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (t : State) : Prop :=
  ∃ s, CtrPre K W SP R D n s ∧ ∃ nonce, CtrCtx K W SP s R nonce D n ∧ CtrMid K W SP s R nonce D n t

theorem ctrTail_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : BitVec 32} {n : Nat} (hn32 : n < 2 ^ 32) :
    CT (CtrTailPre K W SP R D n) (.seq (.block [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)])
      (.ite .e (.block [])
        (.seq (.block ([.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] ++ ctrAt ++ zero4 ksO ++
            keyArgs c1O ++ [.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)]))
        (.seq (ctrCall v.callee)
          (.seq (.block [.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm ksO), .mov .ecx (slot nO)])
            xorLoop))))) := by
  refine CT.block_seq [.ebp] (pin_ebp fun _ ⟨_, _, _, _, I⟩ => I.env.ebp) (by taint_decide)
    (fun t ⟨_, _, _, _, I⟩ => testN_ok L I.env (r := n % 16) (by omega) I.nO) ?_
  refine CT.ite (decide (n % 16 = 0)) (fun _ ⟨_, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil) fun hf => ?_
  have h0 : n % 16 ≠ 0 := of_decide_eq_false hf
  -- The arguments of the call making the keystream block.
  have blk : ∀ t₀ : State, (∃ t, CtrTailPre K W SP R D n t ∧ t₀.mem = t.mem ∧ t₀.zf = some (decide (n % 16 = 0)) ∧
      t₀.gpr .ebp = W ∧ t₀.gpr .esp = SP ∧ t₀.rd = t.rd ∧ t₀.wr = t.wr) →
      ∃ tc, runBlock isa ([.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] ++ ctrAt ++
          zero4 ksO ++ keyArgs c1O ++ [.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)]) t₀ =
          some tc ∧
        Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩] t₀.mem tc.mem ∧
        tc.gpr .eax = K ∧ tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
        tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 ∧ tc.gpr .ebp = W ∧
        tc.gpr .esp = SP ∧ tc.rd = t₀.rd ∧ tc.wr = t₀.wr :=
    fun t₀ ⟨t, ⟨s, hs, nonce, C, I⟩, hm₀, _, hbp₀, hsp₀, hrd₀, hwr₀⟩ => by
      have E₀ : Env K W SP t₀ := I.env.keep (by rw [hbp₀, I.env.ebp]) (by rw [hsp₀, I.env.esp]) hrd₀ hwr₀
      have k₀ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv t₀.mem W o = slotv s.mem W o := fun o h₁ h₂ => by
        rw [hm₀]; exact C.slot_kept I.frame h₁ h₂
      obtain ⟨tc, run, ft, -, -, rest⟩ := ctrTailArgs_ok L E₀ (by rw [k₀ _ (by decide) (by decide)]; exact hs.ctx)
        (by rw [k₀ _ (by decide) (by decide)]; exact hs.rounds) (by rw [k₀ _ (by decide) (by decide)]; exact hs.len)
        hn32 C.h7 C.h13 (by rw [hm₀]; exact C.c0_kept I.frame) (by have := C.hn; omega)
      exact ⟨tc, run, ft, rest⟩
  refine CT.block_seq [.ebp] (pin_ebp fun _ ⟨_, _, _, _, hbp, _⟩ => hbp) (by taint_decide) blk ?_
  -- The call.
  have a80 : w64 (W + BitVec.ofNat 32 80) = w64 W + BitVec.ofNat 64 80 := L.aW (by decide)
  have pre : ∀ tc : State, (∃ t₀ : State, (∃ t, CtrTailPre K W SP R D n t ∧ t₀.mem = t.mem ∧
      t₀.zf = some (decide (n % 16 = 0)) ∧ t₀.gpr .ebp = W ∧ t₀.gpr .esp = SP ∧ t₀.rd = t.rd ∧ t₀.wr = t.wr) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩] t₀.mem tc.mem ∧
      tc.gpr .eax = K ∧ tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
      tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 ∧ tc.gpr .ebp = W ∧
      tc.gpr .esp = SP ∧ tc.rd = t₀.rd ∧ tc.wr = t₀.wr) →
      Env K W SP tc ∧ Src W SP tc (W + BitVec.ofNat 32 80) (16 * 1) ∧
      Covers [⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩] tc.wr ∧
      (⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 64, 16⟩ ∧
      (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩ ∧ tc.gpr .eax = K ∧
      tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
      tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 :=
    fun tc ⟨t₀, ⟨t, ⟨_, _, _, _, I⟩, _, _, _, _, hrd₀, hwr₀⟩, _, ax, cx, dx, bx, di, bp, sp, rd, wr⟩ => by
      have Ec : Env K W SP tc := ⟨bp, sp, I.env.perm.of_eq (by rw [rd, hrd₀]) (by rw [wr, hwr₀])⟩
      exact ⟨Ec, srcW L Ec.perm (by decide), by rw [a80]; exact Ec.perm.wC (by decide),
        by rw [a80]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide),
        by rw [a80]; exact L.k_w.sub_right (Lay.wSub (by decide)), ax, cx, dx, bx, di⟩
  refine CT.seq (J := fun td => Env K W SP td ∧ slotv td.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16)) ∧
      slotv td.mem W nO = BitVec.ofNat 32 (n % 16))
    (ctrCall_ct v L hR (c := 64) (by decide) pre) (fun tc h => ?_) ?_
  · obtain ⟨Ec, hq, hqw, hqc, hqk, ax, cx, dx, bx, di⟩ := pre tc h
    obtain ⟨t₀, ⟨t, ⟨_, _, _, _, I⟩, hm₀, _⟩, ft, _⟩ := h
    refine WP.mono (ctrCall_ok v L Ec hR (c := 64) (by decide) hq hqc hqk hqw ax cx dx bx di)
      fun td ⟨Ed, _, _, _, fd, _⟩ => ?_
    have fd' := fd
    rw [a80] at fd'
    have kd : ∀ o, 96 ≤ o → o + 4 ≤ 384 → slotv td.mem W o = slotv t.mem W o := fun o h₁ h₂ => by
      rw [← hm₀]
      exact ((ft.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans
        (fd'.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
          · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
          · exact ⟨⟨w64 W + BitVec.ofNat 64 384, 2048⟩, by simp, fun _ h => h⟩
          · exact ⟨below SP 56, by simp, fun _ h => h⟩) :
          Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩, ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 56]
            t₀.mem td.mem).readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
          · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
          · exact (L.stk_w' (by omega)).symm) (by decide)
    exact ⟨Ed, by rw [kd _ (by decide) (by decide)]; exact I.dO, by rw [kd _ (by decide) (by decide)]; exact I.nO⟩
  -- The XOR.
  refine CT.block_seq [.ebp] (pin_ebp fun _ h => h.1.ebp) (by taint_decide)
    (fun td hd => xorArgs_ok L hd.1 hd.2.1 hd.2.2) ?_
  exact Proof.AesGcm.X86.xorLoop_ct (pin3 fun _ ⟨_, _, _, hdi, hdx, hcx, _⟩ => ⟨hdi, hdx, hcx⟩)

theorem ctr_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : BitVec 32} {n : Nat} (hn32 : n < 2 ^ 32) : CT (CtrPre K W SP R D n) (ctr v.callee) :=
  RelCT.assoc (CT.seq (J := CtrTailPre K W SP R D n) (ctrWhole_ct v L hR hn32)
    (fun s hs => by
      obtain ⟨nonce, C⟩ := hs.c
      exact WP.mono (ctrWhole_ok v C hs.env hs.ctx hs.rounds hs.data hs.len) fun t I => ⟨s, hs, nonce, C, I⟩)
    (ctrTail_ct v L hR hn32))

end VG.Proof.AesCcm.X86
