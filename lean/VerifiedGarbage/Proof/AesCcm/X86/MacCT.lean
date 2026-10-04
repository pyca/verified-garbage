import VerifiedGarbage.Proof.AesCcm.X86.Mac
import VerifiedGarbage.Proof.AesCcm.X86.AadCT

/-!
# AES-CCM on x86: the CBC-MAC and the tag in constant time

Untrusted: everything here is checked by Lean. `b0`, `mac` and `tag` branch
and address memory only by the slots, the lengths and `W`: all public
(`b0_ct`, `mac_ct`, `tag_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 tglO dO nO)
open VG.Proof.AesGcm.X86 (CT w64 slotv)

/-- What the MAC's pieces keep: the slots, and the associated data and the
data readable. -/
structure MacMid (K W SP : BitVec 32) (R : Nat) (N A D : BitVec 32) (nl al n tl : Nat) (s : State) : Prop where
  env : Env K W SP s
  slots : Slots W K R N A D nl al n tl s.mem
  aad : Buf W SP s A al
  data : Buf W SP s D n

theorem MacMid.next {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} {N A D : BitVec 32} {nl al n tl : Nat} {s : State}
    (h : MacMid K W SP R N A D nl al n tl s) {y : Nat} (hy : y = 0 ∨ y = 96) {s' : State} (E : Env K W SP s')
    (f : Frame (macR W SP y) s.mem s'.mem) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) :
    MacMid K W SP R N A D nl al n tl s' :=
  ⟨E, h.slots.macR L hy f, h.aad.of_eq rd wr, h.data.of_eq rd wr⟩

/-- What `b0` and `mac` start from: also `Ctr₀` at `W + 48`. -/
structure MacPre (K W SP : BitVec 32) (R : Nat) (N A D : BitVec 32) (nl al n tl : Nat) (s : State) : Prop
    extends MacMid K W SP R N A D nl al n tl s where
  c0 : ∃ nonce : List Byte, nonce.length = nl ∧
    bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0

theorem b0Blk_ct {y : Nat} (hy : y = 0 ∨ y = 96) {I : State → Prop}
    (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.ebp], s₁.gpr r = s₂.gpr r) :
    CT I (.block ([.mov .ecx (slot c0O), .store (at_ .ebp blkO) .ecx, .mov .ecx (slot (c0O + 4)),
        .store (at_ .ebp (blkO + 4)) .ecx, .mov .ecx (slot (c0O + 8)), .store (at_ .ebp (blkO + 8)) .ecx,
        .store8 (at_ .ebp blkO) .al, .mov .eax (slot lenO), .bswap .eax, .alu .or .eax (slot (c0O + 12)),
        .store (at_ .ebp (blkO + 12)) .eax] ++ zero4 y)) := by
  rcases hy with rfl | rfl
  · exact CT.taint [.ebp] hr (by taint_decide)
  · exact CT.taint [.ebp] hr (by taint_decide)

theorem b0_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : BitVec 32} {nl al n tl : Nat} (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hal : al < 2 ^ 32) (hn : n < 256 ^ (15 - nl)) (hn32 : n < 2 ^ 32) {y : Nat}
    (hy : y = 0 ∨ y = 96) :
    CT (MacPre K W SP R N A D nl al n tl) (b0 v.callee v.suffix y) := by
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
        · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
        · rcases hy with rfl | rfl
          · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
          · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)) (by decide)
    exact ⟨E₃, by rw [k₃ _ (by decide) (by decide)]; exact hs.slots.ctx,
      by rw [k₃ _ (by decide) (by decide)]; exact hs.slots.rounds⟩

theorem mac_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : BitVec 32} {nl al n tl : Nat} (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hal : al < 2 ^ 32) (hn : n < 256 ^ (15 - nl)) (hn32 : n < 2 ^ 32) {y : Nat}
    (hy : y = 0 ∨ y = 96) :
    CT (MacPre K W SP R N A D nl al n tl) (mac v.callee v.suffix y) := by
  refine CT.seq (J := MacMid K W SP R N A D nl al n tl) (b0_ct v L hR h7 h13 ht4 ht16 hte hal hn hn32 hy)
    (fun s hs => ?_) ?_
  · obtain ⟨nonce, hnl, hc0⟩ := hs.c0
    exact WP.mono (b0_ok v L hs.env hR hs.slots hnl h7 h13 ht4 ht16 hte hal hn hn32 hc0 hy)
      fun s₁ ⟨E₁, f₁, _, rd, wr⟩ => hs.toMacMid.next L hy E₁ f₁ rd wr
  refine CT.seq (J := MacMid K W SP R N A D nl al n tl)
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
  have blk : ∀ s, TagPre K W SP R s → ∃ s₃, runBlock isa ([.mov .eax (imm 0)] ++ ctrAt ++ keyArgs c1O ++
      [.mov .ebx (.reg .ebp), .alu .add .ebx (imm y), .mov .edi (imm 1)]) s = some s₃ ∧
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
