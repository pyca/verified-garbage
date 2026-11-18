module

public import VerifiedGarbage.Proof.AesCcm.X86.Seal
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.X86.Entry
import VerifiedGarbage.Proof.AesCcm.X86.Blocks
import VerifiedGarbage.Proof.AesCcm.X86.Run
meta import VerifiedGarbage.Proof.AesCcm.X86.Seal
meta import VerifiedGarbage.Proof.AesCcm.BytesAt
meta import VerifiedGarbage.Proof.AesCcm.X86.Entry
meta import VerifiedGarbage.Proof.AesCcm.X86.Blocks
meta import VerifiedGarbage.Proof.AesCcm.X86.Run
meta import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.AesGcm.X86.Top
meta import VerifiedGarbage.Proof.AesGcm.X86.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86.Fn
meta import VerifiedGarbage.Proof.AesGcm.X86.Loops
public import VerifiedGarbage.Proof.AesCcm.X86.Absorb
import VerifiedGarbage.Proof.AesCcm.X86.Mac
import VerifiedGarbage.Proof.AesCcm.X86.AadCT
import VerifiedGarbage.Proof.AesCcm.X86.Aad
meta import VerifiedGarbage.Proof.AesCcm.X86.Absorb
meta import VerifiedGarbage.Proof.AesCcm.X86.Mac
meta import VerifiedGarbage.Proof.AesCcm.X86.AadCT
meta import VerifiedGarbage.Proof.AesCcm.X86.Aad
public import VerifiedGarbage.Proof.AesCcm.X86.Crypt
import VerifiedGarbage.Proof.AesCcm.X86.Callee
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesCcm.X86.Crypt
meta import VerifiedGarbage.Proof.AesCcm.X86.Callee
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `AesCcm.X86.CryptCT`, which only this module used -/

section

/-!
# AES-CCM on x86: counter mode in constant time

Untrusted: everything here is checked by Lean. `ctr` branches on the length
of the data and addresses memory by `W` and the data's address, all public
(`ctr_ct`).
-/

@[expose] public section

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
    CT (CtrPre K W SP R D n) (.seq (.block (([.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO),
        .store (at_ .ebp nO) .eax] : List Instr) ++ splitWhole))
      (.ite .e (.block []) (.seq (.block (([.mov .eax (imm 1)] : List Instr) ++ ctrAt ++ keyArgs c1O)) (ctrCall v.callee)))) := by
  have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  refine CT.block_seq [.ebp] (pin_ebp fun _ h => h.env.ebp) (by taint_decide)
    (fun s hs => ctrSplit_ok L hs.env hs.data hs.len hn32) ?_
  refine CT.ite (decide (n / 16 = 0)) (fun _ ⟨_, _, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil) fun hf => ?_
  have h0 : n / 16 ≠ 0 := of_decide_eq_false hf
  have blk : ∀ s₁ : State, (∃ s, CtrPre K W SP R D n s ∧ s₁.gpr .ebx = D ∧ s₁.gpr .edi = BitVec.ofNat 32 (n / 16) ∧
      s₁.zf = some (decide (n / 16 = 0)) ∧ Env K W SP s₁ ∧ Frame [wC W] s.mem s₁.mem ∧
      slotv s₁.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16)) ∧ slotv s₁.mem W nO = BitVec.ofNat 32 (n % 16) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr) →
      ∃ sc, runBlock isa (([.mov .eax (imm 1)] : List Instr) ++ ctrAt ++ keyArgs c1O) s₁ = some sc ∧
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
        omega_using [h0, this]) (by decide) hbx hdi
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
  exact C.dw a k ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_using [hc]⟩

/-- What `ctr`'s last bytes start from. -/
abbrev CtrTailPre (K W SP : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (t : State) : Prop :=
  ∃ s, CtrPre K W SP R D n s ∧ ∃ nonce, CtrCtx K W SP s R nonce D n ∧ CtrMid K W SP s R nonce D n t

theorem ctrTail_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : BitVec 32} {n : Nat} (hn32 : n < 2 ^ 32) :
    CT (CtrTailPre K W SP R D n) (.seq (.block [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)])
      (.ite .e (.block [])
        (.seq (.block (([.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] : List Instr) ++ ctrAt ++ zero4 ksO ++
            keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)] : List Instr)))
        (.seq (ctrCall v.callee)
          (.seq (.block [.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm ksO), .mov .ecx (slot nO)])
            xorLoop))))) := by
  refine CT.block_seq [.ebp] (pin_ebp fun _ ⟨_, _, _, _, I⟩ => I.env.ebp) (by taint_decide)
    (fun t ⟨_, _, _, _, I⟩ => testN_ok L I.env (r := n % 16) (by omega_using []) I.nO) ?_
  refine CT.ite (decide (n % 16 = 0)) (fun _ ⟨_, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil) fun hf => ?_
  have h0 : n % 16 ≠ 0 := of_decide_eq_false hf
  -- The arguments of the call making the keystream block.
  have blk : ∀ t₀ : State, (∃ t, CtrTailPre K W SP R D n t ∧ t₀.mem = t.mem ∧ t₀.zf = some (decide (n % 16 = 0)) ∧
      t₀.gpr .ebp = W ∧ t₀.gpr .esp = SP ∧ t₀.rd = t.rd ∧ t₀.wr = t.wr) →
      ∃ tc, runBlock isa (([.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] : List Instr) ++ ctrAt ++
          zero4 ksO ++ keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)] : List Instr)) t₀ =
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
        hn32 C.h7 C.h13 (by rw [hm₀]; exact C.c0_kept I.frame) (by have := C.hn; omega_using [h0, this])
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
          · exact ⟨below SP 60, by simp, fun _ h => h⟩) :
          Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩, ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 60]
            t₀.mem td.mem).readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Lay.w_w (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)
          · exact Lay.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
          · exact (L.stk_w' (by omega_using [h₂])).symm) (by decide)
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

end

end

/-! ### `AesCcm.X86.MacCT`, which only this module used -/

section

/-!
# AES-CCM on x86: the CBC-MAC and the tag in constant time

Untrusted: everything here is checked by Lean. `b0`, `mac` and `tag` branch
and address memory only by the slots, the lengths and `W`: all public
(`b0_ct`, `mac_ct`, `tag_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 tglO dO nO)
open VG.Proof.AesGcm.X86 (CT w64 slotv)

/-- What the MAC's pieces keep: the slots, and the associated data and the
data readable. -/
structure MacMid (K W SP : BitVec 32) (R : Nat) (N A D T : BitVec 32) (nl al n tl : Nat) (s : State) : Prop where
  env : Env K W SP s
  slots : Slots W K R N A D T nl al n tl s.mem
  aad : Buf W SP s A al
  data : Buf W SP s D n

theorem MacMid.next {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} {N A D T : BitVec 32} {nl al n tl : Nat} {s : State}
    (h : MacMid K W SP R N A D T nl al n tl s) {y : Nat} (hy : y = 0 ∨ y = 96) {s' : State} (E : Env K W SP s')
    (f : Frame (macR W SP y) s.mem s'.mem) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) :
    MacMid K W SP R N A D T nl al n tl s' :=
  ⟨E, h.slots.macR L hy f, h.aad.of_eq rd wr, h.data.of_eq rd wr⟩

/-- What `b0` and `mac` start from: also `Ctr₀` at `W + 48`. -/
structure MacPre (K W SP : BitVec 32) (R : Nat) (N A D T : BitVec 32) (nl al n tl : Nat) (s : State) : Prop
    extends MacMid K W SP R N A D T nl al n tl s where
  c0 : ∃ nonce : List Byte, nonce.length = nl ∧
    bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0

theorem b0Blk_ct {y : Nat} (hy : y = 0 ∨ y = 96) {I : State → Prop}
    (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.ebp], s₁.gpr r = s₂.gpr r) :
    CT I (.block (([.mov .ecx (slot c0O), .store (at_ .ebp blkO) .ecx, .mov .ecx (slot (c0O + 4)),
        .store (at_ .ebp (blkO + 4)) .ecx, .mov .ecx (slot (c0O + 8)), .store (at_ .ebp (blkO + 8)) .ecx,
        .store8 (at_ .ebp blkO) .al, .mov .eax (slot lenO), .bswap .eax, .alu .or .eax (slot (c0O + 12)),
        .store (at_ .ebp (blkO + 12)) .eax] : List Instr) ++ zero4 y)) := by
  rcases hy with rfl | rfl
  · exact CT.taint [.ebp] hr (by taint_decide)
  · exact CT.taint [.ebp] hr (by taint_decide)

theorem b0_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D T : BitVec 32} {nl al n tl : Nat} (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hal : al < 2 ^ 32) (hn : n < 256 ^ (15 - nl)) (hn32 : n < 2 ^ 32) {y : Nat}
    (hy : y = 0 ∨ y = 96) :
    CT (MacPre K W SP R N A D T nl al n tl) (b0 v.callee v.suffix y) := by
  refine CT.assoc3 (CT.seq (J := fun s => Env K W SP s ∧ slotv s.mem W ctxO = K ∧
      slotv s.mem W roundsO = BitVec.ofNat 32 R) ?_ (fun s hs => ?_) (updBlock_ct v L hR hy fun _ h => h))
  · refine CT.block_seq [.ebp] (pin_ebp fun _ h => h.env.ebp) (by taint_decide)
      (fun s hs => b0Flags_ok L hs.env h13 ht4 hal hs.slots.tl hs.slots.nlen hs.slots.alen) ?_
    refine CT.seq (J := fun s => s.gpr .ebp = W)
      (CT.ite (decide (al = 0)) (fun _ ⟨_, _, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil)
        (fun _ => by exact CT.taint [] (fun _ _ _ _ _ h => by simp at h) (by taint_decide)))
      (fun s₁ ⟨_, _, _, _, hzf, hbp, _⟩ => ?_) (b0Blk_ct hy (pin_ebp fun _ h => h))
    refine WP.ite (decide (al = 0)) (eval_e hzf) (fun _ => WP.of_runBlock ⟨s₁, rfl, hbp⟩) (fun _ => ?_)
    exact WP.of_runBlock ⟨_, by crun [], by cregs [hbp]⟩
  · obtain ⟨nonce, hnl, hc0⟩ := hs.c0
    refine WP.mono (b0Pre_ok L hs.env hnl h7 h13 ht4 ht16 hte hal hn hn32 hs.slots.tl hs.slots.nlen hs.slots.alen
      hs.slots.len hc0 hy) fun s₃ ⟨E₃, _, _, f₃, _⟩ => ?_
    have k₃ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
      f₃.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Lay.w_w (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)
        · rcases hy with rfl | rfl
          · exact Lay.w_w (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)
          · exact Lay.w_w (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)) (by decide)
    exact ⟨E₃, by rw [k₃ _ (by decide) (by decide)]; exact hs.slots.ctx,
      by rw [k₃ _ (by decide) (by decide)]; exact hs.slots.rounds⟩

theorem mac_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D T : BitVec 32} {nl al n tl : Nat} (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hal : al < 2 ^ 32) (hn : n < 256 ^ (15 - nl)) (hn32 : n < 2 ^ 32) {y : Nat}
    (hy : y = 0 ∨ y = 96) :
    CT (MacPre K W SP R N A D T nl al n tl) (mac v.callee v.suffix y) := by
  refine CT.seq (J := MacMid K W SP R N A D T nl al n tl) (b0_ct v L hR h7 h13 ht4 ht16 hte hal hn hn32 hy)
    (fun s hs => ?_) ?_
  · obtain ⟨nonce, hnl, hc0⟩ := hs.c0
    exact WP.mono (b0_ok v L hs.env hR hs.slots hnl h7 h13 ht4 ht16 hte hal hn hn32 hc0 hy)
      fun s₁ ⟨E₁, f₁, _, rd, wr⟩ => hs.toMacMid.next L hy E₁ f₁ rd wr
  refine CT.seq (J := MacMid K W SP R N A D T nl al n tl)
    ((aad_ct v L hR hy hal).mono fun s hs => ⟨hs.env, hs.slots.ctx, hs.slots.rounds, hs.slots.aad, hs.slots.alen,
      hs.aad⟩)
    (fun s hs => WP.mono (aad_ok v L hs.env hR hs.slots.ctx hs.slots.rounds hy hs.slots.aad hs.slots.alen hs.aad hal)
      fun s₂ M => hs.next L hy M.env M.frame M.rd M.wr) ?_
  refine CT.block_seq [.ebp] (pin_ebp fun _ h => h.env.ebp) (by taint_decide)
    (fun s hs => dataArgs_ok L hs.env hs.slots.data hs.slots.len) ?_
  exact (absorbPad_ct v L hR hy hn32).mono fun s₃ ⟨s, hs, hm₃, hbp, hsp, hrd, hwr⟩ =>
    ⟨⟨hbp, hsp, hs.env.perm.of_eq hrd hwr⟩, by rw [dn_kept hm₃ (by decide) (by decide)]; exact hs.slots.ctx,
      by rw [dn_kept hm₃ (by decide) (by decide)]; exact hs.slots.rounds, fun _ => hs.data.of_eq hrd hwr,
      (dn_read hm₃).1, (dn_read hm₃).2⟩

/-- What `tag` starts from. -/
structure TagPre (K W SP : BitVec 32) (R : Nat) (s : State) : Prop where
  env : Env K W SP s
  ctx : slotv s.mem W ctxO = K
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  c0 : ∃ nonce : List Byte, 7 ≤ nonce.length ∧ nonce.length ≤ 13 ∧
    bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0

theorem tag_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) : CT (TagPre K W SP R) (tag v.callee y) := by
  have blk : ∀ s, TagPre K W SP R s → ∃ s₃, runBlock isa (([.mov .eax (imm 0)] : List Instr) ++ ctrAt ++ keyArgs c1O ++
      ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm y), .mov .edi (imm 1)] : List Instr)) s = some s₃ ∧
      s₃.gpr .eax = K ∧ s₃.gpr .ecx = BitVec.ofNat 32 R ∧ s₃.gpr .edx = W + BitVec.ofNat 32 64 ∧
      s₃.gpr .ebx = W + BitVec.ofNat 32 y ∧ s₃.gpr .edi = BitVec.ofNat 32 1 ∧ s₃.gpr .ebp = W ∧ s₃.gpr .esp = SP ∧
      s₃.rd = s.rd ∧ s₃.wr = s.wr := fun s hs => by
    obtain ⟨nonce, h7, h13, hc0⟩ := hs.c0
    obtain ⟨s₃, run, -, -, rest⟩ := tagArgs_ok L hs.env hs.ctx hs.rounds h7 h13 hc0 y
    exact ⟨s₃, run, rest⟩
  have h₂ := ctrCall_ct v L hR (c := 64) (Q := W + BitVec.ofNat 32 y) (n := 1) (by decide)
    (I := fun s' => ∃ s, TagPre K W SP R s ∧ s'.gpr .eax = K ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧
      s'.gpr .edx = W + BitVec.ofNat 32 64 ∧ s'.gpr .ebx = W + BitVec.ofNat 32 y ∧ s'.gpr .edi = BitVec.ofNat 32 1 ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    fun s₃ ⟨s, hs, ax, cx, dx, bx, di, bp, sp, rd, wr⟩ => by
      have E₃ : Env K W SP s₃ := ⟨bp, sp, hs.env.perm.of_eq rd wr⟩
      obtain ⟨hq, hqw, hqc, hqk⟩ := tagCall_pre L E₃ hy
      exact ⟨E₃, hq, hqw, hqc, hqk, ax, cx, dx, bx, di⟩
  rcases hy with rfl | rfl
  · exact CT.block_seq [.ebp] (pin_ebp fun _ h => h.env.ebp) (by taint_decide) blk h₂
  · exact CT.block_seq [.ebp] (pin_ebp fun _ h => h.env.ebp) (by taint_decide) blk h₂

end VG.Proof.AesCcm.X86

end

end

/-!
# AES-CCM on x86: the start, and what the pieces after it keep, for
constant time

Untrusted: everything here is checked by Lean. The arguments and `esp` are
public (`pubOf`); from them, `seal` and `open` start (`Top`), the entry and
`Ctr₀` are constant time (`start_ct`), and after them each piece keeps `Run`,
from which the next one's precondition follows.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry saveAt tglO tpO)
open VG.Proof.AesGcm.X86 (CT w64 slotv argA argsR argA_contains ofNat_toNat32 length_bytesAt)

/-- What is public: `esp` and the arguments. -/
def pubOf (s : State) : BitVec 32 × (Nat → BitVec 32) := (s.gpr .esp, fun i => if i < 11 then arg s i else 0)

theorem pubOf_eq {s₁ s₂ : State} (h : onePub s₁ s₂) : pubOf s₁ = pubOf s₂ := by
  obtain ⟨h₁, h₂⟩ := h
  simp only [pubOf, h₁, Prod.mk.injEq, true_and]
  funext i
  split
  · next hi => exact h₂ i hi
  · rfl

/-- `seal` and `open` from their arguments. -/
structure Top (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop where
  args : Args s K W SP N A D T R nl al n tl
  sp : s.gpr .esp = SP
  a0 : arg s 0 = K
  a1 : arg s 1 = BitVec.ofNat 32 R
  a2 : arg s 2 = N
  a3 : arg s 3 = BitVec.ofNat 32 nl
  a4 : arg s 4 = A
  a5 : arg s 5 = BitVec.ofNat 32 al
  a6 : arg s 6 = D
  a7 : arg s 7 = BitVec.ofNat 32 n
  a8 : arg s 8 = T
  a9 : arg s 9 = BitVec.ofNat 32 tl
  a10 : arg s 10 = W

/-- `Top` for the public values `p`. -/
abbrev TopOf (p : BitVec 32 × (Nat → BitVec 32)) : State → Prop :=
  Top (p.2 0) (p.2 10) p.1 (p.2 2) (p.2 4) (p.2 6) (p.2 8) (p.2 1).toNat (p.2 3).toNat (p.2 5).toNat
    (p.2 7).toNat (p.2 9).toNat

theorem top_of {s : State}
    (h : Args s (arg s 0) (arg s 10) (s.gpr .esp) (arg s 2) (arg s 4) (arg s 6) (arg s 8) (arg s 1).toNat
      (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat (arg s 9).toNat)
    {p : BitVec 32 × (Nat → BitVec 32)} (hp : pubOf s = p) : TopOf p s := by
  subst hp
  simp only [pubOf, show (0 : Nat) < 11 from by decide, show (1 : Nat) < 11 from by decide,
    show (2 : Nat) < 11 from by decide, show (3 : Nat) < 11 from by decide, show (4 : Nat) < 11 from by decide,
    show (5 : Nat) < 11 from by decide, show (6 : Nat) < 11 from by decide, show (7 : Nat) < 11 from by decide,
    show (8 : Nat) < 11 from by decide, show (9 : Nat) < 11 from by decide, show (10 : Nat) < 11 from by decide,
    ↓reduceIte]
  exact ⟨h, rfl, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm,
    rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm, rfl⟩

/-! ## The start -/

theorem entry_ct {I : State → Prop} {W SP : BitVec 32}
    (h : ∀ s, I s → s.gpr .esp = SP ∧ arg s 10 = W ∧ Covers [argsR SP 11] (s.rd ++ s.wr) ∧
      SP.toNat + 4 + 4 * 11 ≤ 2 ^ 32) : CT I ccmEntry := by
  refine CT.seq (J := fun s => s.gpr .eax = W ∧ s.gpr .esp = SP)
    (CT.taint [.esp] (pin1 fun s h' => (h s h').1) (by taint_decide)) (fun s hs => ?_)
    (CT.taint [.eax, .esp] (pin2 fun _ h => h) (by taint_decide))
  obtain ⟨hSP, hW, rA, fa⟩ := h s hs
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 10) 4 := rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine WP.of_runBlock ⟨_, by crun [hSP, i₀], ?_, ?_⟩
  · rw [gpr_setReg_self, ← hSP]; exact hW
  · rw [gpr_setReg_of_ne _ _ (by decide), hSP]

theorem start_ct {K W SP N A D T : BitVec 32} {R nl al n tl : Nat} (L : Lay K W SP) (h13 : nl ≤ 13) :
    CT (Top K W SP N A D T R nl al n tl) (.seq ccmEntry ctrs) := by
  refine CT.seq (J := fun s₁ => ∃ s, Top K W SP N A D T R nl al n tl s ∧ Entered s W s₁)
    (entry_ct fun s hs => ⟨hs.sp, hs.a10, hs.args.args, hs.args.fa⟩)
    (fun s hs => WP.mono (entry_ok hs.a10 hs.args.perm.w (by rw [hs.sp]; exact hs.args.args)
      (by rw [hs.sp]; exact hs.args.argsW) (by rw [hs.sp]; exact hs.args.fa) L.fw) fun s₁ E => ⟨s, hs, E⟩)
    (ctrs_ct L h13 fun s₁ ⟨s, hs, E₀⟩ => ⟨⟨E₀.ebp, by rw [E₀.esp, hs.sp], hs.args.perm.of_eq E₀.rd E₀.wr⟩,
      by rw [E₀.slots (2, nonceO) (by simp), hs.a2], by rw [E₀.slots (3, nlenO) (by simp), hs.a3]⟩)

/-! ## What the pieces keep -/

/-- After the start, and the pieces after it. -/
structure Run (s₀ : State) (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop where
  env : Env K W SP s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  st : ∃ s₂, Started s₀ K W SP N A D T R nl al n tl s₂ ∧ Frame (mutR W SP D n) s₂.mem s.mem
  c0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s₀.mem (w64 N) nl) 0

section
variable {s₀ : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}

theorem Run.of_started {s₂ : State} (St : Started s₀ K W SP N A D T R nl al n tl s₂) :
    Run s₀ K W SP N A D T R nl al n tl s₂ :=
  ⟨St.env, St.rd, St.wr, ⟨s₂, St, Frame.refl _ _⟩, St.c0⟩

theorem Run.step {s : State} (h : Run s₀ K W SP N A D T R nl al n tl s) {s' : State} (E : Env K W SP s')
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) {rs : List Region} (f : Frame rs s.mem s'.mem) (hm : InMut W SP D n rs)
    (hc : ∀ r ∈ rs, (⟨w64 W + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r) : Run s₀ K W SP N A D T R nl al n tl s' := by
  obtain ⟨s₂, St, f₂⟩ := h.st
  exact ⟨E, by rw [rd, h.rd], by rw [wr, h.wr], ⟨s₂, St, f₂.trans (frame_toMut f hm)⟩,
    by rw [Proof.AesGcm.X86.bytesAt_frame f hc (by decide), h.c0]⟩

theorem Run.slots {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s) :
    Slots W K R N A D T nl al n tl s.mem := by
  obtain ⟨s₂, St, f₂⟩ := h.st
  exact (St.mut Ar f₂).1

theorem Run.mac_pre {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s) :
    MacPre K W SP R N A D T nl al n tl s :=
  ⟨⟨h.env, h.slots Ar, Ar.aad.of_eq h.rd h.wr, Ar.data.of_eq h.rd h.wr⟩,
    ⟨_, length_bytesAt _ _ _, h.c0⟩⟩

theorem Run.tag_pre {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s) :
    TagPre K W SP R s :=
  ⟨h.env, (h.slots Ar).ctx, (h.slots Ar).rounds,
    ⟨_, by rw [length_bytesAt]; exact Ar.h7, by rw [length_bytesAt]; exact Ar.h13, h.c0⟩⟩

theorem Run.ctr_pre {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s) :
    CtrPre K W SP R D n s :=
  ⟨h.env, (h.slots Ar).ctx, (h.slots Ar).rounds, (h.slots Ar).data, (h.slots Ar).len,
    ⟨_, ⟨Ar.lay, Ar.rounds, by rw [length_bytesAt]; exact Ar.h7, by rw [length_bytesAt]; exact Ar.h13,
      by rw [length_bytesAt]; exact Ar.hn, Ar.n32, h.c0, Ar.data.of_eq h.rd h.wr, by rw [h.wr]; exact Ar.dw,
      Ar.dk⟩⟩⟩

/-- After the MAC into `W + y`. -/
theorem Run.mac {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {Y : List Byte} {s' : State} (A' : Absorbed K W SP s y Y s') :
    Run s₀ K W SP N A D T R nl al n tl s' :=
  h.step A'.env A'.rd A'.wr A'.frame (inMut_macR W SP D n hy) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hy with rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (Ar.lay.stk_w' (by decide)).symm

/-- After the tag at `W + y`. -/
theorem Run.tag {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {s' : State} (E : Env K W SP s') (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (f : Frame [⟨w64 W + BitVec.ofNat 64 64, 16⟩, ⟨w64 W + BitVec.ofNat 64 y, 16⟩, wC W, below SP 60] s.mem s'.mem) :
    Run s₀ K W SP N A D T R nl al n tl s' :=
  h.step E rd wr f (inMut_tag W SP D n hy) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · rcases hy with rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (Ar.lay.stk_w' (by decide)).symm

/-- After counter mode. -/
theorem Run.ctr {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s)
    {s' : State} (E : Env K W SP s') (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (f : Frame (ctrR W SP D n) s.mem s'.mem) :
    Run s₀ K W SP N A D T R nl al n tl s' :=
  h.step E rd wr f (inMut_ctrR W SP D n) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (Ar.lay.stk_w' (by decide)).symm
    · exact (Ar.data.w.sub_right (Lay.wSub (by decide))).symm

end

end VG.Proof.AesCcm.X86
