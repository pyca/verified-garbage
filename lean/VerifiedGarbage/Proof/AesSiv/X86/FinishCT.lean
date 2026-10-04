import VerifiedGarbage.Proof.AesSiv.X86.Finish

/-!
# AES-SIV on x86: finishing S2V is constant time

Untrusted: everything here is checked by Lean. The taint analysis checks each
block from `ebp`; the registers that hold addresses computed from the
string's length (public) are pinned to their values where a block uses
them, and the calls are constant time by their contracts.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 slotv CT copyLoop_ct copyLoop_ok length_bytesAt)

/-- `copyN` of a public length, from public pointers. -/
theorem copyN_ct {I : State → Prop} {k : Nat} (hk : k < 2 ^ 32)
    (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.edi, .edx, .ecx], s₁.gpr r = s₂.gpr r)
    (hc : ∀ s, I s → s.gpr .ecx = BitVec.ofNat 32 k) : CT I copyN := by
  refine CT.seq (J := fun s' => (∃ s, I s ∧ ∀ r, s'.gpr r = s.gpr r) ∧ s'.zf = some (decide (k = 0)))
    (CT.taint [.ecx] (pin1 fun s h => hc s h) (by taint_decide))
    (fun s hs => WP.of_runBlock ⟨_, by crun [hc s hs], ⟨s, hs, fun r => by cregs []⟩,
      by cmems [hc s hs]; rw [Proof.AesGcm.X86.and_self_beq32 hk]⟩) ?_
  refine CT.ite (decide (k = 0)) (fun s h => eval_e h.2) (fun _ => CT.nil) (fun _ => copyLoop_ct ?_)
  intro s₁ s₂ ⟨⟨t₁, i₁, e₁⟩, _⟩ ⟨⟨t₂, i₂, e₂⟩, _⟩ r hr'
  rw [e₁, e₂]; exact hr t₁ t₂ i₁ i₂ r hr'

/-! ## The short case -/

theorem shortTail_ct {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} {P : BitVec 32} {k : Nat}
    (hk16 : k < 16) {I : State → Prop} (hI : ∀ s, I s → CmacPre C W SP R P k s) : CT I shortTail := by
  refine CT.block_seq [.ebp] (pin_ebp fun s h => (hI s h).env.ebp) (by taint_decide)
    (fun s hs => shortA_ok L (hI s hs).env (hI s hs).str (hI s hs).slen) ?_
  refine CT.seq (J := fun s₂ => s₂.gpr .ebp = W ∧ Env C W SP s₂ ∧ slotv s₂.mem W slenO = BitVec.ofNat 32 k)
    (copyN_ct (k := k) (by omega) (pin3 fun s ⟨_, _, _, di, dx, cx, _⟩ => ⟨di, dx, cx⟩)
      fun s ⟨_, _, _, _, _, cx, _⟩ => cx) (fun s₁ ⟨s, hs, m₁, di₁, dx₁, cx₁, bp₁, sp₁, rd₁, wr₁⟩ => ?_) ?_
  · have h := hI s hs
    have B := h.buf
    have E₁ : Env C W SP s₁ := ⟨bp₁, sp₁, h.env.perm.of_eq rd₁ wr₁⟩
    have hw := L.fw
    refine WP.mono (copyN_ok di₁ dx₁ cx₁ h.k32 B.wrap (by rw [L.nW (by decide)]; omega)
      (by rw [rd₁, wr₁]; exact B.rd) (by rw [L.aW (by decide)]; exact E₁.perm.wC (by omega))
      (by rw [L.aW (by decide)]; exact B.w.sub_right (Lay.wSub (by omega)))) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_
    have bp₂ : s₂.gpr .ebp = W := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), bp₁]
    refine ⟨bp₂, ⟨bp₂, by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), sp₁], E₁.perm.of_eq rd₂ wr₂⟩, ?_⟩
    have f₁ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s.mem s₁.mem := by
      rw [m₁]
      exact ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)⟩).trans
        ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)⟩)
    have f₂ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s₁.mem s₂.mem := by
      rw [m₂, L.aW (by decide)]
      exact writeBytes_frame _ _ _ (by
        rw [length_bytesAt]; exact Offset.contains (w64 W) (d := 32) (n := k) (e := 32) (k := 32) (by omega)
          (by omega) (by omega))
    exact ((f₁.trans f₂).readW (w := 32) (r := ⟨w64 W + BitVec.ofNat 64 slenO, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide)).trans h.slen
  · have e : ([.mov .edx (.reg .ebp), .alu .add .edx (slot slenO), .mov .eax (imm 0x80),
          .store8 (at_ .edx tailOff) .al,
          .mov .eax (slot dOff), .store (at_ .ebp dbOff) .eax, .mov .eax (slot (dOff + 4)),
          .store (at_ .ebp (dbOff + 4)) .eax, .mov .eax (slot (dOff + 8)), .store (at_ .ebp (dbOff + 8)) .eax,
          .mov .eax (slot (dOff + 12)), .store (at_ .ebp (dbOff + 12)) .eax] ++ dblAt dbOff ++
          [.mov .edx (.reg .ebp)] ++ xorInto dbOff tailOff : List Instr) =
        ([.mov .edx (.reg .ebp), .alu .add .edx (slot slenO)] : List Instr) ++
          ([.mov .eax (imm 0x80), .store8 (at_ .edx tailOff) .al,
          .mov .eax (slot dOff), .store (at_ .ebp dbOff) .eax, .mov .eax (slot (dOff + 4)),
          .store (at_ .ebp (dbOff + 4)) .eax, .mov .eax (slot (dOff + 8)), .store (at_ .ebp (dbOff + 8)) .eax,
          .mov .eax (slot (dOff + 12)), .store (at_ .ebp (dbOff + 12)) .eax] ++ dblAt dbOff ++
          [.mov .edx (.reg .ebp)] ++ xorInto dbOff tailOff) := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [e]
    refine RelCT.block_append (CT.seq (J := fun s => s.gpr .ebp = W ∧ s.gpr .edx = W + BitVec.ofNat 32 k)
      (CT.taint [.ebp] (pin_ebp fun s h => h.1) (by taint_decide))
      (fun s ⟨bp, E, sl⟩ => WP.of_runBlock ⟨_, by crun [bp, L.aW, E.perm.wR, sl], by cregs [bp], by cregs [bp, sl]⟩)
      (CT.taint [.ebp, .edx] (pin2 fun s h => h) (by taint_decide)))

theorem shortMac_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {out : Nat} (hout : out = 0 ∨ out = 112) {I : State → Prop}
    (hI : ∀ s, I s → Env C W SP s ∧ slotv s.mem W ctxO = C ∧ slotv s.mem W roundsO = BitVec.ofNat 32 R) :
    CT I (shortMac v.callee v.suffix out) := by
  have hyo : StOk out := by rcases hout with rfl | rfl <;> decide
  have dO : (⟨w64 W + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 out, 16⟩ := by
    rcases hout with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)
  have fin : CT (fun s' => ∃ s, I s ∧ s'.mem = Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 out) ∧
      s'.gpr .eax = C ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧ s'.gpr .edx = W + BitVec.ofNat 32 out ∧
      s'.gpr .ebx = W + BitVec.ofNat 32 32 ∧ s'.gpr .esi = BitVec.ofNat 32 16 ∧
      s'.gpr .edi = W + BitVec.ofNat 32 256 ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧
      s'.wr = s.wr) (finCall v.callee v.suffix) :=
    finCall_ct v L hR (y := out) hyo (P := W + BitVec.ofNat 32 32) (l := 16) (Nat.le_refl _)
      fun s₂ ⟨s, hs, _, ax, cx, dx, bx, si, di, bp, sp, rd, wr⟩ =>
        have P₂ := (hI s hs).1.perm.of_eq rd wr
        ⟨⟨bp, sp, P₂⟩, srcW L P₂ (t := 32) (k := 16) (by decide), by rw [L.aW (o := 32) (by decide)]; exact dO,
          ax, cx, dx, bx, si, di⟩
  rcases hout with rfl | rfl
  all_goals
    refine CT.block_seq [.ebp] (pin_ebp fun s h => (hI s h).1.ebp) (by taint_decide)
      (fun s hs => macPre_ok L (hI s hs).1 (hI s hs).2.1 (hI s hs).2.2 (by decide)) ?_
    exact fin

/-! ## The long case -/

theorem kRound_ct {I : State → Prop} :
    CT I (.block [.mov .eax (.reg .ecx), .alu .sub .eax (imm 1), .alu .and .eax (imm 0xfffffff0),
      .alu .sub .eax (imm 16)]) :=
  CT.taint [] (fun _ _ _ _ r hr => by simp at hr) (by taint_decide)

theorem longTail_ct {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} {P : BitVec 32} {k : Nat}
    (h16 : 16 ≤ k) (hk32 : k < 2 ^ 32) {I : State → Prop} (hI : ∀ s, I s → CmacPre C W SP R P k s) :
    CT I longTail := by
  have hT := kOf_tail h16
  have hkk : 16 * kOf k ≤ k := by omega
  refine CT.block_seq [.ebp] (pin_ebp fun s h => (hI s h).env.ebp) (by taint_decide)
    (fun s hs => cmp17_ok L (hI s hs).env (hI s hs).slen hk32) ?_
  refine CT.seq (J := fun s₂ => ∃ s, I s ∧ s₂.gpr .eax = BitVec.ofNat 32 (16 * kOf k) ∧
      s₂.gpr .ecx = BitVec.ofNat 32 k ∧ s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧
      s₂.wr = s.wr)
    (CT.ite (decide (k < 17)) (fun s ⟨_, _, _, _, cf, _⟩ => eval_b cf) (fun _ => CT.nil)
      (fun _ => kRound_ct))
    (fun s₁ ⟨s, hs, ax, cx, cf, bp, sp, m, rd, wr⟩ => WP.mono (kBranch_wp ax cx cf h16 hk32)
      fun s₂ ⟨ax₂, cx₂, g₂, m₂, rd₂, wr₂⟩ => ⟨s, hs, ax₂, cx₂, by rw [g₂ _ (by decide), bp],
        by rw [g₂ _ (by decide), sp], m₂.trans m, rd₂.trans rd, wr₂.trans wr⟩) ?_
  refine CT.block_seq [.ebp] (pin_ebp fun s ⟨_, _, _, _, bp, _⟩ => bp) (by taint_decide)
    (fun s₂ ⟨s, hs, ax, cx, bp, sp, m, rd, wr⟩ => tailArgs_ok L ⟨bp, sp, (hI s hs).env.perm.of_eq rd wr⟩
      (P := P) ax cx (by rw [m]; exact (hI s hs).str)) ?_
  refine CT.seq (J := fun s₄ => s₄.gpr .ebp = W ∧ Env C W SP s₄ ∧
      slotv s₄.mem W slenO = BitVec.ofNat 32 k ∧ slotv s₄.mem W nbO = BitVec.ofNat 32 (16 * kOf k))
    (copyLoop_ct (pin3 fun s ⟨_, _, _, di, cx, dx, _⟩ => ⟨di, dx, cx⟩))
    (fun s₃ ⟨s₂, ⟨s, hs, ax₂, cx₂, bp₂, sp₂, m₂, rd₂, wr₂⟩, m₃, di₃, cx₃, dx₃, bp₃, sp₃, rd₃, wr₃⟩ => ?_) ?_
  · have h := hI s hs
    have B := h.buf
    have E₃ : Env C W SP s₃ := ⟨bp₃, sp₃, h.env.perm.of_eq (by rw [rd₃, rd₂]) (by rw [wr₃, wr₂])⟩
    have hwk : P.toNat + 16 * kOf k < 2 ^ 32 := by have := B.wrap; omega
    have B₃ : Buf W SP s₃ (P + BitVec.ofNat 32 (16 * kOf k)) (k - 16 * kOf k) :=
      (B.drop hkk hwk).of_eq (by rw [rd₃, rd₂]) (by rw [wr₃, wr₂])
    have hW := L.fw
    refine WP.mono (copyLoop_ok s₃ ⟨di₃, dx₃, by rw [cx₃, Proof.AesGcm.X86.ofNat_sub32 hkk hk32],
      by omega, by omega, B₃.wrap, by rw [L.nW (o := 32) (by decide)]; omega, B₃.rd,
      by rw [L.aW (by decide)]; exact E₃.perm.wC (by omega),
      by rw [L.aW (by decide)]; exact B₃.w.sub_right (Lay.wSub (by omega))⟩) fun s₄ c₄ => ?_
    have bp₄ : s₄.gpr .ebp = W := by rw [c₄.other _ (by decide) (by decide) (by decide) (by decide), bp₃]
    have f₃₄ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s₃.mem s₄.mem := by
      rw [c₄.mem, L.aW (by decide)]
      exact writeBytes_frame _ _ _ (by
        rw [length_bytesAt]; exact Offset.contains (w64 W) (d := 32) (n := k - 16 * kOf k) (e := 32) (k := 32)
          (by omega) (by omega) (by omega))
    have k₄ : ∀ o, 64 ≤ o → o + 4 ≤ 2576 → slotv s₄.mem W o = slotv s₃.mem W o := fun o h₁ h₂ =>
      f₃₄.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by decide))
        (by decide)
    refine ⟨bp₄, ⟨bp₄, by rw [c₄.other _ (by decide) (by decide) (by decide) (by decide), sp₃],
      E₃.perm.of_eq c₄.rd c₄.wr⟩, ?_, ?_⟩
    · rw [k₄ _ (by decide) (by decide), m₃, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide)
        (by decide), m₂]
      exact h.slen
    · rw [k₄ _ (by decide) (by decide), m₃]; exact Mem.readW_writeW_self32 _ _ _
  · have e : ([.mov .edx (.reg .ebp), .alu .add .edx (slot slenO), .alu .sub .edx (slot nbO)] ++
          xorInto dOff (tailOff - 16) : List Instr) =
        ([.mov .edx (.reg .ebp), .alu .add .edx (slot slenO), .alu .sub .edx (slot nbO)] : List Instr) ++
          xorInto dOff (tailOff - 16) := rfl
    rw [e]
    refine RelCT.block_append (CT.seq (J := fun s => s.gpr .ebp = W ∧
        s.gpr .edx = W + BitVec.ofNat 32 k - BitVec.ofNat 32 (16 * kOf k))
      (CT.taint [.ebp] (pin_ebp fun s h => h.1) (by taint_decide))
      (fun s ⟨bp, E, sl, nb⟩ => WP.of_runBlock ⟨_, by crun [bp, L.aW, E.perm.wR, sl, nb], by cregs [bp],
        by cregs [bp, sl, nb]⟩)
      (CT.taint [.ebp, .edx] (pin2 fun s h => h) (by taint_decide)))

theorem jSet_ct {I : State → Prop} : CT I (.block [.mov .esi (imm 1)]) :=
  CT.taint [] (fun _ _ _ _ r hr => by simp at hr) (by taint_decide)

/-- What `longMac` keeps between its calls. -/
structure LMS (C W SP : BitVec 32) (R : Nat) (k : Nat) (s : State) : Prop where
  env : Env C W SP s
  ctx : slotv s.mem W ctxO = C
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  slen : slotv s.mem W slenO = BitVec.ofNat 32 k
  nb : slotv s.mem W nbO = BitVec.ofNat 32 (16 * kOf k)

theorem LMS.of_slots {C W SP : BitVec 32} {R k : Nat} {s s' : State} (h : LMS C W SP R k s) (E : Env C W SP s')
    (hs : ∀ o, 176 ≤ o → o + 4 ≤ jO → slotv s'.mem W o = slotv s.mem W o) : LMS C W SP R k s' :=
  ⟨E, by rw [hs _ (by decide) (by decide)]; exact h.ctx, by rw [hs _ (by decide) (by decide)]; exact h.rounds,
    by rw [hs _ (by decide) (by decide)]; exact h.slen, by rw [hs _ (by decide) (by decide)]; exact h.nb⟩

theorem slot_zero4 {W : BitVec 32} {out : Nat} (hout : out = 0 ∨ out = 112) (m : Mem)
    {o : Nat} (h₁ : 176 ≤ o) (h₂ : o + 4 ≤ 256) :
    slotv (Cmac.zero4 m (w64 W + BitVec.ofNat 64 out)) W o = slotv m W o :=
  (Cmac.frame_store4 _ _ _ _ _).readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by omega))
    (by decide)

theorem longMac_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {k : Nat} (h16 : 16 ≤ k) (hk32 : k < 2 ^ 32) {out : Nat}
    (hout : out = 0 ∨ out = 112) {I : State → Prop}
    (hI : ∀ s, I s → CmacPre C W SP R P k s ∧ slotv s.mem W nbO = BitVec.ofNat 32 (16 * kOf k)) :
    CT I (longMac v.callee v.suffix out) := by
  have hT := kOf_tail h16
  have hJ := jOf_rest h16
  have hj1 := jOf_le k
  have hkk : 16 * kOf k ≤ k := by omega
  have hyo : StOk out := by rcases hout with rfl | rfl <;> decide
  have hout' := hout
  rcases hout with rfl | rfl
  all_goals
    refine CT.block_seq [.ebp] (pin_ebp fun s h => (hI s h).1.env.ebp) (by taint_decide)
      (fun s hs => lm1_ok (C := C) (R := R) (P := P) L (hI s hs).1.env (hI s hs).1.ctx (hI s hs).1.rounds
        (hI s hs).1.str (hI s hs).2 (by omega) hout') ?_
    refine CT.seq (J := LMS C W SP R k)
      (updCall_ct v L hR hyo (Q := P) (n := kOf k) (by omega)
        fun s₂ ⟨s, hs, _, ax, cx, dx, bx, si, di, bp, sp, rd, wr⟩ =>
          have B₂ : Buf W SP s₂ P (16 * kOf k) := ((hI s hs).1.buf.take hkk).of_eq rd wr
          ⟨⟨bp, sp, (hI s hs).1.env.perm.of_eq rd wr⟩, srcBuf B₂, B₂.w.sub_right (Lay.wSub (by decide)),
            ax, cx, dx, bx, si, di⟩)
      (fun s₂ ⟨s, hs, m₂, ax, cx, dx, bx, si, di, bp, sp, rd, wr⟩ =>
        have B₂ : Buf W SP s₂ P (16 * kOf k) := ((hI s hs).1.buf.take hkk).of_eq rd wr
        WP.mono (updCall_ok v L ⟨bp, sp, (hI s hs).1.env.perm.of_eq rd wr⟩ hR hyo (srcBuf B₂)
          (B₂.w.sub_right (Lay.wSub (by decide))) (by omega) ax cx dx bx si di)
          fun s₃ ⟨E₃, _, _, _, f₃, _⟩ =>
            have hs' : ∀ o, 176 ≤ o → o + 4 ≤ 256 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ => by
              rw [slot_call L hout' f₃ h₁ h₂, m₂, slot_zero4 (W := W) hout' _ h₁ h₂]
            ⟨E₃, by rw [hs' _ (by decide) (by decide)]; exact (hI s hs).1.ctx,
              by rw [hs' _ (by decide) (by decide)]; exact (hI s hs).1.rounds,
              by rw [hs' _ (by decide) (by decide)]; exact (hI s hs).1.slen,
              by rw [hs' _ (by decide) (by decide)]; exact (hI s hs).2⟩) ?_
    refine CT.block_seq [.ebp] (pin_ebp fun s h => h.env.ebp) (by taint_decide)
      (fun s hs => cmp17s_ok L hs.env hs.slen hk32) ?_
    refine CT.seq (J := fun s₅ => LMS C W SP R k s₅ ∧ s₅.gpr .esi = BitVec.ofNat 32 (jOf k))
      (CT.ite (decide (k < 17)) (fun s ⟨_, _, _, cf, _⟩ => eval_b cf) (fun _ => CT.nil) (fun _ => jSet_ct))
      (fun s₄ ⟨s, hs, si, cf, g, m, rd, wr⟩ => WP.mono (jBranch_wp si cf)
        fun s₅ ⟨si₅, g₅, m₅, rd₅, wr₅⟩ =>
          ⟨hs.of_slots ⟨by rw [g₅ _ (by decide), g _ (by decide) (by decide), hs.env.ebp],
            by rw [g₅ _ (by decide), g _ (by decide) (by decide), hs.env.esp],
            hs.env.perm.of_eq (rd₅.trans rd) (wr₅.trans wr)⟩ fun o _ _ => by rw [m₅, m], si₅⟩) ?_
    refine CT.block_seq [.ebp] (pin_ebp fun s h => h.1.env.ebp) (by taint_decide)
      (fun s hs => lm3_ok L hs.1.env hs.1.ctx hs.1.rounds hs.2) ?_
    refine CT.seq (J := fun s₇ => LMS C W SP R k s₇ ∧ slotv s₇.mem W jO = BitVec.ofNat 32 (jOf k))
      (updCall_ct v L hR hyo (Q := W + BitVec.ofNat 32 32) (n := jOf k) (by omega)
        fun s₆ ⟨s, hs, _, ax, cx, dx, bx, si, di, bp, sp, rd, wr⟩ =>
          have P₆ := hs.1.env.perm.of_eq rd wr
          ⟨⟨bp, sp, P₆⟩, srcW L P₆ (t := 32) (k := 16 * jOf k) (by omega),
            by rw [L.aW (o := 32) (by decide)]; exact Lay.w_w (by omega) (by omega) (by omega),
            ax, cx, dx, bx, si, di⟩)
      (fun s₆ ⟨s, hs, m₆, ax, cx, dx, bx, si, di, bp, sp, rd, wr⟩ =>
        have P₆ := hs.1.env.perm.of_eq rd wr
        WP.mono (updCall_ok v L ⟨bp, sp, P₆⟩ hR hyo (n := jOf k) (srcW L P₆ (t := 32) (k := 16 * jOf k) (by omega))
          (by rw [L.aW (o := 32) (by decide)]; exact Lay.w_w (by omega) (by omega) (by omega)) (by omega)
          ax cx dx bx si di)
          fun s₇ ⟨E₇, _, _, _, f₇, _⟩ =>
            ⟨hs.1.of_slots E₇ fun o h₁ h₂ => by
              rw [slot_call L hout' f₇ h₁ (by simp only [jO] at h₂; omega), m₆, slotv,
                Proof.AesGcm.X86.readW_writeW_off _ _ _ (.inl h₂) (by simp only [jO] at h₂; omega) (by decide)],
              by rw [slot_call L hout' f₇ (by decide) (by decide), m₆]; exact Mem.readW_writeW_self32 _ _ _⟩) ?_
    refine CT.block_seq [.ebp] (pin_ebp fun s h => h.1.env.ebp) (by taint_decide)
      (fun s hs => lm5_ok L hs.1.env hs.1.ctx hs.1.rounds hs.2 hs.1.slen hs.1.nb hj1 (by omega) hk32) ?_
    exact finCall_ct v L hR hyo (P := W + BitVec.ofNat 32 (32 + 16 * jOf k)) (l := k - 16 * kOf k - 16 * jOf k)
      (by omega) fun s₈ ⟨s, hs, _, ax, cx, dx, bx, si, di, bp, sp, rd, wr⟩ =>
        have P₈ := hs.1.env.perm.of_eq rd wr
        ⟨⟨bp, sp, P₈⟩, srcW L P₈ (t := 32 + 16 * jOf k) (k := k - 16 * kOf k - 16 * jOf k) (by omega),
          by rw [L.aW (by omega)]; exact Lay.w_w (by omega) (by omega) (by omega), ax, cx, dx, bx, si, di⟩

/-! ## The whole -/

/-- `finish out` is constant time from what it starts from. -/
theorem finish_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {k : Nat} (hk32 : k < 2 ^ 32) {out : Nat}
    (hout : out = 0 ∨ out = 112) : CT (CmacPre C W SP R P k) (finish v.callee v.suffix out) := by
  refine CT.block_seq [.ebp] (pin_ebp fun s h => h.env.ebp) (by taint_decide)
    (fun s hs => cmp16_ok L hs.env hs.slen hk32) ?_
  have pre : ∀ s₁, (∃ s, CmacPre C W SP R P k s ∧ s₁.cf = some (decide (k < 16)) ∧
      (∀ r, r ≠ .ecx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr) →
      CmacPre C W SP R P k s₁ := fun s₁ ⟨s, hs, _, g, m, rd, wr⟩ =>
    hs.of_eq (g _ (by decide)) (g _ (by decide)) m rd wr
  refine CT.ite (decide (k < 16)) (fun s ⟨_, _, cf, _⟩ => eval_b cf) (fun ht => ?_) (fun hf => ?_)
  · have hk16 := of_decide_eq_true ht
    refine CT.seq (J := fun s₂ => Env C W SP s₂ ∧ slotv s₂.mem W ctxO = C ∧
        slotv s₂.mem W roundsO = BitVec.ofNat 32 R) (shortTail_ct L hk16 pre)
      (fun s₁ h₁ => WP.mono (shortTail_ok L (pre s₁ h₁) hk16) fun s₂ ⟨E₂, _, _, f₂, _⟩ => ?_)
      (shortMac_ct v L hR hout fun s h => h)
    have h₁ := pre s₁ h₁
    have k₂ : ∀ o, 176 ≤ o → o + 4 ≤ 200 → slotv s₂.mem W o = slotv s₁.mem W o := fun o h₁ h₂ =>
      f₂.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
        · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)) (by decide)
    exact ⟨E₂, by rw [k₂ _ (by decide) (by decide)]; exact h₁.ctx, by rw [k₂ _ (by decide) (by decide)]; exact h₁.rounds⟩
  · have h16 : 16 ≤ k := by have := of_decide_eq_false hf; omega
    refine CT.seq (J := fun s₂ => CmacPre C W SP R P k s₂ ∧ slotv s₂.mem W nbO = BitVec.ofNat 32 (16 * kOf k))
      (longTail_ct L h16 hk32 pre)
      (fun s₁ h₁ => WP.mono (longTail_ok L (pre s₁ h₁) h16) fun s₂ ⟨E₂, rd₂, wr₂, f₂, nb₂, _⟩ => ?_)
      (longMac_ct v L hR h16 hk32 hout fun s h => h)
    have h₁ := pre s₁ h₁
    have k₂ : ∀ o, 176 ≤ o → o + 4 ≤ 208 → slotv s₂.mem W o = slotv s₁.mem W o := fun o h₁ h₂ =>
      f₂.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
        · exact Lay.w_w (.inl h₂) (by omega) (by decide)) (by decide)
    exact ⟨⟨E₂, by rw [k₂ _ (by decide) (by decide)]; exact h₁.ctx, by rw [k₂ _ (by decide) (by decide)]; exact h₁.rounds,
      by rw [k₂ _ (by decide) (by decide)]; exact h₁.str, by rw [k₂ _ (by decide) (by decide)]; exact h₁.slen, h₁.k32,
      h₁.buf.of_eq rd₂ wr₂⟩, nb₂⟩

end VG.Proof.AesSiv.X86
