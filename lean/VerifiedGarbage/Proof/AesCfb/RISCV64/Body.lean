module

public import VerifiedGarbage.Proof.AesCfb.Spec
public import VerifiedGarbage.Impl.AesCfb.RISCV64
public import VerifiedGarbage.Impl.AesOfb.RISCV64
public import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesCfb.Spec
meta import VerifiedGarbage.Impl.AesCfb.RISCV64
meta import VerifiedGarbage.Impl.AesOfb.RISCV64
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
meta import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified

/-!
# AES-CFB128 decryption on RISC-V: one block, and constant time

As on PPC64LE (`Proof/AesCfb/PPC64LE/Body.lean`): `decBody_ok`, one run of
`body decPost` takes the loop invariant AES-CBC's proofs share
(`Proof/AesCbc/RISCV64/Loop.lean`) from `k` blocks to `k + 1`, for
`cfbMode false`. The code before the call (`ivArgs`, `ivA_wp`) and the call
are on the block at `iv`. `decBody_ct`: it is constant time, by the shared
framework. (Encryption runs the CFB128 chain, `Proof/Aes/RISCV64/ChainModes.lean`.)
-/

@[expose] public section

namespace VG.Proof.AesCfb.RISCV64

open VG VG.RISCV64 VG.Impl.AesCfb.RISCV64
open VG.Impl.AesCbc.RISCV64 (whole xorInto copy advance encCall mov)
open VG.Impl.AesOfb.RISCV64 (ivArgs)
open VG.Proof.AesCbc
open VG.Proof.AesCbc.RISCV64
open VG.Spec.Aes (bytesAt)

/-- The arguments of a call on the block at `iv`, with the working space at
the start of the scratch buffer. -/
theorem callPreIv {s₀ : State} (hp : UPre s₀) {s : State}
    (a0 : s.gpr .a0 = W s₀) (a1 : s.gpr .a1 = s₀.gpr .a1) (a2 : s.gpr .a2 = Iv s₀)
    (a3 : s.gpr .a3 = BitVec.ofNat 64 1) (a4 : s.gpr .a4 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre s (W s₀) (Iv s₀) (S s₀) (R s₀) where
  a0 := a0
  a1 := by rw [a1, a1_ofNat]
  a2 := a2
  a3 := a3
  a4 := a4
  rounds := hp.rounds
  wd := hp.sch_iv
  ws := hp.sch_scr.sub_right wsR_sub
  ds := hp.iv_scr.sub_right wsR_sub
  wrap := hp.iv_wrap
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

theorem ivA_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv M s₀ k s) :
    WP isa (.block ivArgs) s (Pre s₀ (Iv s₀) s.mem s) := by
  unfold ivArgs mov
  refine Steps.wp_mv fun s₁ u₁ => Steps.wp_mv fun s₂ u₂ => Steps.wp_mv fun s₃ u₃ =>
    Steps.wp_li (imm := 1) (by decide) fun s₄ u₄ => Steps.wp_mv fun s₅ u₅ => WP.block_nil ?_
  have keep (r : Reg) (hr : r ∈ preserved) : s₅.gpr r = s.gpr r := by
    have h' := (preserved_ne hr).1
    simp only [argRegs5, List.mem_cons, List.not_mem_nil, or_false, not_or] at h'
    obtain ⟨h0, h1, h2, h3, h4⟩ := h'
    rw [u₅.other _ h4, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  refine ⟨callPreIv hp ?_ ?_ ?_ ?_ ?_ ?_ ?_, keep, ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr, h.s1]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), h.s2]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.s3]
  · rw [u₅.other _ (by decide), u₄.gpr]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.s6]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-- What the code before the call and the call leave, for either
direction. -/
structure AfterCall (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  g : ∀ r ∈ preserved, s₂.gpr r = s.gpr r
  wr : s₂.wr = [ivR s₀, dataR s₀, scrR s₀]
  regs : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀]
  rd' : s₂.rd = s.rd
  wr' : s₂.wr = s.wr
  sp' : s₂.sp = s.sp
  frame : Frame [ivR s₀, ⟨S s₀, 2048⟩] s.mem s₂.mem
  iv : bytesAt s₂.mem (Iv s₀) 16 = Spec.Cbc.aesWith (R s₀) (wK s₀) (bytesAt s.mem (Iv s₀) 16)

theorem call_ok {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State}
    (h : LInv M s₀ k s) (post : List Instr) {Q : State → Prop}
    (hq : ∀ s₂, AfterCall s₀ k s s₂ → WP isa (.block post) s₂ Q) :
    WP isa (body post) s Q := by
  refine WP.seq (WP.mono (ivA_wp hp h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames a.pre)
    fun s₂ c => hq s₂ ?_)
  have big : Frame (Big s₀) s₀.mem s.mem := UPre.big_of h.frame
  refine ⟨fun r hr => by rw [c.saved r hr, a.saved r hr], by rw [c.wr, a.wr, h.wrs hp],
    by rw [c.rd, c.wr, a.rd, a.wr, h.regs hp], by rw [c.rd, a.rd], by rw [c.wr, a.wr],
    by rw [c.sp, a.sp], ?_, ?_⟩
  · have fr := c.frame; rw [a.mem] at fr; exact fr
  · rw [c.out, a.mem, UPre.sched_bytes hp big, ← aesWith_state]

theorem xorBlk_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {M : Mode} {s s₂ : State}
    (h : LInv M s₀ k s) (a : AfterCall s₀ k s s₂) {rest : List Instr} {Φ : State → Prop}
    (kk : ∀ s₃, (∀ r, r ≠ .t3 → r ≠ .t4 → s₃.gpr r = s₂.gpr r) →
      bytesAt s₃.mem (blk s₀ k) 16 = Spec.Cbc.xor (bytesAt s.mem (blk s₀ k) 16) (bytesAt s₂.mem (Iv s₀) 16) →
      bytesAt s₃.mem (Iv s₀) 16 = bytesAt s₂.mem (Iv s₀) 16 →
      Frame [⟨blk s₀ k, 16⟩] s₂.mem s₃.mem → s₃.rd = s₂.rd → s₃.wr = s₂.wr → s₃.sp = s₂.sp →
      WP isa (.block rest) s₃ Φ) :
    WP isa (.block (xorInto .s4 .s3 ++ rest)) s₂ Φ :=
  xorInto_wp (P := blk s₀ k) (Q := Iv s₀) (by decide) (by decide) (by decide) (by decide)
    (by rw [a.g .s4 (by decide), h.s4]) (by rw [a.g .s3 (by decide), h.s3])
    ⟨ivR s₀, by rw [a.regs]; simp, fun _ h => h⟩ ⟨dataR s₀, by rw [a.wr]; simp, UPre.data_sub hk⟩
    (hp.blk_iv hk) fun s₃ g₃ x₃ f₃ rd₃ wr₃ sp₃ => by
      refine kk s₃ g₃ ?_ (bytesAt_frame f₃ (one (hp.blk_iv hk).symm) (by decide)) f₃ rd₃ wr₃ sp₃
      rw [x₃, bytesAt_frame a.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.blk_iv hk
        · exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right wsR_sub) (by decide)]

/-- The frame of a block, from the call's and the two blocks'. -/
theorem step_frame {s₀ : State} {k : Nat} {s s₂ : State} (a : AfterCall s₀ k s s₂) {m₃ m₄ : Mem}
    (f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem m₃) (f₄ : Frame [ivR s₀] m₃ m₄) :
    Frame [⟨blk s₀ k, 16⟩, ivR s₀, wsR s₀, cR s₀] s.mem m₄ := by
  refine (a.frame.mono fun r hr => ?_).trans ((f₃.mono (by simp)).trans (f₄.mono (by simp)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp

/-- The invariant after a block, from what the block leaves. -/
theorem linv_succ {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ s₄ : State}
    (h : LInv M s₀ k s) (a : AfterCall s₀ k s s₂)
    (g₄ : ∀ r, r ≠ .t3 → r ≠ .t4 → s₄.gpr r = s₂.gpr r) (rd₄ : s₄.rd = s₂.rd) (wr₄ : s₄.wr = s₂.wr)
    (sp₄ : s₄.sp = s₂.sp)
    (fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, wsR s₀, cR s₀] s.mem s₄.mem)
    (hout : outK M s₀ (k + 1) = outK M s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16])
    (hiv : bytesAt s₄.mem (Iv s₀) 16 = chainK M s₀ (k + 1)) :
    WP isa (.block advance) s₄ (LInv M s₀ (k + 1)) := by
  refine advance_regs (s := s₄) hk
    (by rw [g₄ _ (by decide) (by decide), a.g .s4 (by decide), h.s4])
    (by rw [g₄ _ (by decide) (by decide), a.g .s5 (by decide), h.s5])
    fun s₅ s4₅ s5₅ keep₅ mem₅ rd₅ wr₅ sp₅ => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h4 : r ≠ .s4) (h5 : r ≠ .s5) : s₅.gpr r = s.gpr r := by
    rw [keep₅ r h4 h5, g₄ r (preserved_ne hr).2.2.1 (preserved_ne hr).2.2.2, a.g r hr]
  have hl' : (outK M s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  refine ⟨?_, ?_, ?_, s4₅, s5₅, ?_, fun r hr hv => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g .s1 (by decide) (by decide) (by decide), h.s1]
  · rw [g .s2 (by decide) (by decide) (by decide), h.s2]
  · rw [g .s3 (by decide) (by decide) (by decide), h.s3]
  · rw [g .s6 (by decide) (by decide) (by decide), h.s6]
  · rw [g r hr (fun e => hv (by simp [e])) (fun e => hv (by simp [e])), h.keep r hr hv]
  · rw [rd₅, rd₄, a.rd']; exact h.rd
  · rw [wr₅, wr₄, a.wr']; exact h.wr
  · rw [sp₅, sp₄, a.sp']; exact h.sp
  · rw [mem₅]; exact h.frame.trans (stepFrame hk fStep)
  · rw [mem₅, hp.blocksAt_step hk fStep, h.data, hout,
      set_prefix _ _ _ hl' (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [mem₅, hiv]

theorem decBody_ok : BodyOk (cfbMode false) (body decPost) := by
  intro s₀ hp k hk s h
  refine call_ok hp h decPost fun s₂ a => ?_
  rw [decPost, List.append_assoc]
  refine xorBlk_wp hp hk h a fun s₃ g₃ b₃ i₃ f₃ rd₃ wr₃ sp₃ => ?_
  refine xorInto_wp (P := Iv s₀) (Q := blk s₀ k) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₃ _ (by decide) (by decide), a.g .s3 (by decide), h.s3])
    (by rw [g₃ _ (by decide) (by decide), a.g .s4 (by decide), h.s4])
    ⟨dataR s₀, by rw [rd₃, wr₃, a.regs]; simp, UPre.data_sub hk⟩
    ⟨ivR s₀, by rw [wr₃, a.wr]; simp, fun _ h => h⟩ (hp.blk_iv hk).symm
    fun s₄ g₄ x₄ f₄ rd₄ wr₄ sp₄ => ?_
  have b₄ : bytesAt s₄.mem (blk s₀ k) 16 = bytesAt s₃.mem (blk s₀ k) 16 :=
    bytesAt_frame f₄ (one (hp.blk_iv hk)) (by decide)
  have hb := h.block hk
  have i₄ : bytesAt s₄.mem (Iv s₀) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [x₄, i₃, b₃, hb]
    exact xor_xor_cancel (by simp [Spec.Aes.bytesAt, ← hb])
  have newBlk : bytesAt s₄.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK (cfbMode false) s₀ k)) := by
    rw [b₄, b₃, hb, a.iv, h.iv]
  have outSucc : outK (cfbMode false) s₀ (k + 1) = outK (cfbMode false) s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, chainK, cfbMode_out, cfbMode_chain, cfb, cts, Bool.false_eq_true, ite_false,
      take_succ_blks s₀ hk, decrypt_snoc]
  refine linv_succ hp hk h a (fun r h3 h4 => by rw [g₄ r h3 h4, g₃ r h3 h4]) (by rw [rd₄, rd₃])
    (by rw [wr₄, wr₃]) (by rw [sp₄, sp₃]) (step_frame a f₃ f₄) outSucc ?_
  rw [i₄]
  simp only [chainK, cfbMode_chain, cts, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, next_snoc]

/-! ## Constant time -/

/-- The code before the call, from the pointers. -/
theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs vars) (.block ivArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem decPost_taint : ∃ h, (taint.check (Taint.ofRegs [.s3, .s4, .s5, .s6])
    (.block decPost) h).isSome = true := ⟨_, by taint_decide⟩

theorem decBody_ct : BodyCt (cfbMode false) (body decPost) :=
  fun hp hp' hq k => VG.Proof.AesCbc.RISCV64.body_ct (D := fun s₀ _ => Iv s₀)
    (fun hq _ => pub_Iv hq) Proof.Aes.RISCV64.encryptBlocks_correct Proof.Aes.RISCV64.encryptBlocks_ct
    encryptBlocks_noFrames pre_taint decPost_taint
    (@fun _ hp _ _ _ h => WP.mono (ivA_wp hp h) fun _ a => ⟨_, a⟩) hp hp' hq k

end VG.Proof.AesCfb.RISCV64
