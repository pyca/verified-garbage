import VerifiedGarbage.Proof.AesXts.X86_64.Steps
import VerifiedGarbage.Proof.AesCbc.X86_64.CT

/-!
# XTS-AES on x86-64: one block, and constant time

`body_ok`: one run of `body` takes the loop invariant AES-CBC's proofs share
(`Proof/AesCbc/X86_64/Loop.lean`) from `k` blocks to `k + 1`, for
`xtsMode enc`, for any implementation of the block functions
(`BlocksImpl`), with `vg_aes_encrypt_blocks` for encryption and
`vg_aes_decrypt_blocks` for decryption. The tweak is XORed into the data
block, which is enciphered in place (`preA_wp`, the call), the tweak is
XORed in again, and the tweak is multiplied by `α` (`Steps.lean`).
`body_ct`: it is constant time, by the shared framework, with the call on
the data block.
-/

namespace VG.Proof.AesXts.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesXts.X86_64
open VG.Impl.AesCbc.X86_64 (whole xorInto callArgs advance)
open VG.Proof.AesCbc (xorMem xorMem_frame xorMem_bytes aesWith_state aesInvWith_state set_prefix Mode ciphOf)
open VG.Proof.AesCbc.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)

/-- What the code before the call leaves. -/
structure PreA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) (blk s₀ k) (S s₀) (R s₀)
  saved : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r
  mem : s₁.mem = xorMem s.mem (blk s₀ k) (Iv s₀)
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem preA_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : LInv M s₀ k s) : WP isa (.block (xorInto .r13 .r12 ++ callArgs)) s (PreA s₀ k s) := by
  have hR := h.regs hp
  have hW := h.wrs hp
  obtain ⟨s₁, run₁, g₁, mem₁, rd₁, wr₁⟩ :=
    xorInto_ok s (P := blk s₀ k) (Q := Iv s₀) h.r13 h.r12
      (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
      (by rw [hW]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hW]; exact in_rw (by simp) (hp.cBlk8 hk))
  obtain ⟨s₂, run₂, rdi₂, rsi₂, rdx₂, rcx₂, r8₂, cs₂, mem₂, rd₂, wr₂⟩ := callArgs_ok s₁
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have keep (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s.gpr r := by
    rw [cs₂ r hr, g₁ r (calleeSaved_ne_rax hr)]
  exact ⟨hp.callPre hk (by rw [rdi₂, g₁ _ (by decide), h.rbx]) (by rw [rsi₂, g₁ _ (by decide), h.rbp])
    (by rw [rdx₂, g₁ _ (by decide), h.r13]) rcx₂ (by rw [r8₂, g₁ _ (by decide), h.r15])
    (by rw [keep .rsp (by simp [calleeSaved]), h.rsp]) (by rw [rd₂, rd₁, h.rd]) (by rw [wr₂, wr₁, h.wr]),
    keep, by rw [mem₂, mem₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- One block in the direction `enc`, by a block function `b` computing `f`,
which is `ciphOf enc` on bytes. -/
theorem body_ok' (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp b.code) (depth : b.code.depth = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16)) :
    BodyOk (AesXts.xtsMode enc) (body b) := by
  intro s₀ hp k hk s h
  refine WP.seq (WP.mono (preA_wp hp hk h) fun s₁ a => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [a.saved .rsp (by simp [calleeSaved]), h.rsp]
  refine WP.seq (WP.mono (blk_call ok nosp depth a.pre) fun s₂ c => ?_)
  have g₂ (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s.gpr r := by rw [c.saved r hr, a.saved r hr]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wrs hp]
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [c.rd, c.wr, a.rd, a.wr, h.regs hp]
  obtain ⟨s₃, run₃, g₃, mem₃, rd₃, wr₃⟩ :=
    xorInto_ok s₂ (P := blk s₀ k) (Q := Iv s₀) (by rw [g₂ .r13 (by simp [calleeSaved]), h.r13])
      (by rw [g₂ .r12 (by simp [calleeSaved]), h.r12])
      (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [hR₂]; exact in_rw (by simp) cIv0) (by rw [hR₂]; exact in_rw (by simp) cIv8)
      (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk8 hk))
  have g₃' (r : Reg) (hr : r ∈ calleeSaved) : s₃.gpr r = s.gpr r := by
    rw [g₃ r (calleeSaved_ne_rax hr), g₂ r hr]
  have hR₃ : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd₃, wr₃, hR₂]
  have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₃, hW₂]
  obtain ⟨s₄, run₄, g₄, mem₄, rd₄, wr₄⟩ :=
    mulA_ok s₃ (Q := Iv s₀) (by rw [g₃' .r12 (by simp [calleeSaved]), h.r12])
      (by rw [hR₃]; exact in_rw (by simp) cIv0) (by rw [hR₃]; exact in_rw (by simp) cIv8)
      (by rw [hW₃]; exact in_rw (by simp) cIv0) (by rw [hW₃]; exact in_rw (by simp) cIv8)
  have ne (r : Reg) (hr : r ∈ calleeSaved) : r ≠ .rcx ∧ r ≠ .rdx := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨s₅, run₅, r13₅, r14₅, zf₅, keep₅, mem₅, rd₅, wr₅⟩ := advance_regs (s := s₄) hk
    (by rw [g₄ _ (by decide) (by decide) (by decide), g₃' .r13 (by simp [calleeSaved]), h.r13])
    (by rw [g₄ _ (by decide) (by decide) (by decide), g₃' .r14 (by simp [calleeSaved]), h.r14])
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, WP.of_runBlock ⟨s₅, run₅, ?_⟩⟩
  have g (r : Reg) (hr : r ∈ calleeSaved) (h13 : r ≠ .r13) (h14 : r ≠ .r14) : s₅.gpr r = s.gpr r := by
    rw [keep₅ r h13 h14, g₄ r (calleeSaved_ne_rax hr) (ne r hr).1 (ne r hr).2, g₃' r hr]
  -- Memory.
  have f₁ : Frame [⟨blk s₀ k, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact xorMem_frame _ _ _
  have f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₃.mem := by rw [mem₃]; exact xorMem_frame _ _ _
  have f₄ : Frame [ivR s₀] s₃.mem s₄.mem := by rw [mem₄]; exact alphaMem_frame _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩, stkR s₀] s.mem s₅.mem := by
    rw [mem₅]
    refine (f₁.sub fun r hr => ?_).trans ((c.frame.sub fun r hr => ?_).trans
      ((f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, by rw [rsp₁]; exact fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem :=
    (UPre.big_of h.frame).trans ((stepFrame hk (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)).sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨dataR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  have one (r : Region) (P : Addr) (hd : (⟨P, 16⟩ : Region).Disjoint r) :
      ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hd
  have callIv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨S s₀, 2048⟩, below (s₁.gpr .rsp) 8], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.blk_iv hk).symm
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
    · rw [rsp₁]; exact hp.stk_iv.symm
  -- The tweak on entry to the block, and the block after the call.
  have ivIn : bytesAt s₂.mem (Iv s₀) 16 = chainK (AesXts.xtsMode enc) s₀ k := by
    rw [bytesAt_frame c.frame callIv (by decide), a.mem,
      bytesAt_frame (xorMem_frame _ _ _) (one _ _ (hp.blk_iv hk).symm) (by decide), h.iv]
  have hlt : ((blks s₀).take k).length = k := by simp [Spec.Cbc.blocksAt]; omega
  have newBlk : bytesAt s₅.mem (blk s₀ k) 16 =
      Spec.Xts.block (ciphOf enc (R s₀) (wK s₀)) (Spec.Xts.next (iv0 s₀) k)
        ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)) := by
    rw [mem₅, mem₄, bytesAt_frame (alphaMem_frame _ _) (one _ _ (hp.blk_iv hk)) (by decide), mem₃,
      xorMem_bytes _ (hp.blk_iv hk), ivIn, c.out, hf, UPre.sched_bytes hp big₁, a.mem,
      xorMem_bytes _ (hp.blk_iv hk), h.block hk, h.iv]
    simp only [chainK, AesXts.xtsMode_chain, hlt]
    rfl
  have newIv : bytesAt s₅.mem (Iv s₀) 16 = Spec.Xts.mulAlpha (chainK (AesXts.xtsMode enc) s₀ k) := by
    rw [mem₅, mem₄, alphaMem_bytes, mem₃,
      bytesAt_frame (xorMem_frame _ _ _) (one _ _ (hp.blk_iv hk).symm) (by decide), ivIn]
  have hl : (outK (AesXts.xtsMode enc) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  have outSucc :
      outK (AesXts.xtsMode enc) s₀ (k + 1) = outK (AesXts.xtsMode enc) s₀ k ++ [bytesAt s₅.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, AesXts.xtsMode_out, take_succ_blks s₀ hk, AesXts.crypt_snoc, hlt]
  refine ⟨⟨?_, ?_, ?_, r13₅, r14₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, zf₅⟩
  · rw [g .rbx (by simp [calleeSaved]) (by decide) (by decide), h.rbx]
  · rw [g .rbp (by simp [calleeSaved]) (by decide) (by decide), h.rbp]
  · rw [g .r12 (by simp [calleeSaved]) (by decide) (by decide), h.r12]
  · rw [g .r15 (by simp [calleeSaved]) (by decide) (by decide), h.r15]
  · rw [g .rsp (by simp [calleeSaved]) (by decide) (by decide), h.rsp]
  · rw [rd₅, rd₄, rd₃, c.rd, a.rd, h.rd]
  · rw [wr₅, wr₄, wr₃, c.wr, a.wr, h.wr]
  · exact h.frame.trans (stepFrame hk fStep)
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, AesXts.xtsMode_chain, take_succ_blks s₀ hk, List.length_append, List.length_singleton,
      hlt, AesXts.next_succ]

theorem encBody_ok (v : BlocksImpl) : BodyOk (AesXts.xtsMode true) (body v.enc) :=
  body_ok' true v.encOk v.encNosp v.encDepth fun _ _ _ _ => (aesWith_state _ _ _ _).symm

theorem decBody_ok (v : BlocksImpl) : BodyOk (AesXts.xtsMode false) (body v.dec) :=
  body_ok' false v.decOk v.decNosp v.decDepth fun _ _ _ _ => (aesInvWith_state _ _ _ _).symm

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
    (.block (xorInto .r13 .r12 ++ callArgs)) h).isSome = true := ⟨_, by taint_decide⟩

theorem post_taint : ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14, .r15])
    (.block (xorInto .r13 .r12 ++ mulA ++ advance)) h).isSome = true := ⟨_, by taint_decide⟩

theorem encBody_ct (v : BlocksImpl) : BodyCt (AesXts.xtsMode true) (body v.enc) :=
  fun hp hp' hq k => VG.Proof.AesCbc.X86_64.body_ct (D := fun s₀ k => blk s₀ k) (fun hq k => pub_blk hq k)
    v.encOk v.encCt v.encNosp v.encDepth pre_taint post_taint
    (@fun _ hp _ hk _ h => WP.mono (preA_wp hp hk h) fun _ a => Mid.of h a.pre a.saved) hp hp' hq k

theorem decBody_ct (v : BlocksImpl) : BodyCt (AesXts.xtsMode false) (body v.dec) :=
  fun hp hp' hq k => VG.Proof.AesCbc.X86_64.body_ct (D := fun s₀ k => blk s₀ k) (fun hq k => pub_blk hq k)
    v.decOk v.decCt v.decNosp v.decDepth pre_taint post_taint
    (@fun _ hp _ hk _ h => WP.mono (preA_wp hp hk h) fun _ a => Mid.of h a.pre a.saved) hp hp' hq k

end VG.Proof.AesXts.X86_64
