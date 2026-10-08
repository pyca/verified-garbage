import VerifiedGarbage.Proof.AesCfb.Spec
import VerifiedGarbage.Proof.AesOfb.X86_64.Body
import VerifiedGarbage.Impl.AesCfb.X86_64

/-!
# AES-CFB128 on x86-64: one block, and constant time

`encBody_ok` and `decBody_ok`: one run of `body` takes the loop invariant
AES-CBC's proofs share (`Proof/AesCbc/X86_64/Loop.lean`) from `k` blocks to
`k + 1`, for `cfbMode`, for any implementation of the block functions
(`BlocksImpl`). The code before the call and the call are AES-OFB's
(`Proof/AesOfb/X86_64/Body.lean`). `encBody_ct` and `decBody_ct`: they are
constant time, by the shared framework, with the call on the block at `iv`.
-/

namespace VG.Proof.AesCfb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCfb.X86_64
open VG.Impl.AesCbc.X86_64 (whole xorInto copy advance at_)
open VG.Impl.AesOfb.X86_64 (ivArgs)
open VG.Proof.AesOfb.X86_64 (IvA ivA_wp callPreIv)
open VG.Proof.AesCbc
open VG.Proof.AesCbc.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)

/-- The block at `r12` XORed with the one at `r13`. -/
theorem xorIv_ok (s : State) {P Q : Addr} (hp : s.gpr .r12 = P) (hq : s.gpr .r13 = Q)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wp : InRegions s.wr P 8) (wp8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa (xorInto .r12 .r13) s = some s' ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = xorMem s.mem P Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, xorInto, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.store64, State.ea, offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, hp, hq, BitVec.add_zero, rp, rp8, rq, rq8, wp, wp8]
    rfl, ?_⟩
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp [gpr_setReg, hr]

/-- What the code before the call and the call leave, for either
direction. -/
structure AfterCall (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  g : ∀ r ∈ calleeSaved, s₂.gpr r = s.gpr r
  wr : s₂.wr = [ivR s₀, dataR s₀, scrR s₀]
  regs : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀]
  rd' : s₂.rd = s.rd
  wr' : s₂.wr = s.wr
  frame : Frame [ivR s₀, ⟨S s₀, 2048⟩, stkR s₀] s.mem s₂.mem
  iv : bytesAt s₂.mem (Iv s₀) 16 = Spec.Cbc.aesWith (R s₀) (wK s₀) (bytesAt s.mem (Iv s₀) 16)

theorem call_ok {M : Mode} (v : BlocksImpl) {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State}
    (h : LInv M s₀ k s) (post : List Instr) {Q : State → Prop}
    (hq : ∀ s₂, AfterCall s₀ k s s₂ → WP isa (.block post) s₂ Q) :
    WP isa (body v.enc post) s Q := by
  refine WP.seq (WP.mono (ivA_wp hp h) fun s₁ a => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [a.saved .rsp (by simp [calleeSaved]), h.rsp]
  refine WP.seq (WP.mono (blk_call v.encOk v.encNosp v.encDepth a.pre) fun s₂ c => hq s₂ ?_)
  have big : Frame (Big s₀) s₀.mem s.mem := UPre.big_of h.frame
  refine ⟨fun r hr => by rw [c.saved r hr, a.saved r hr], by rw [c.wr, a.wr, h.wrs hp],
    by rw [c.rd, c.wr, a.rd, a.wr, h.regs hp], by rw [c.rd, a.rd], by rw [c.wr, a.wr], ?_, ?_⟩
  · have fr := c.frame; rw [rsp₁, a.mem] at fr; exact fr
  · rw [c.out, a.mem, UPre.sched_bytes hp big, ← aesWith_state]

/-- The two blocks after XORing the output block into the data block. -/
theorem xor_step {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ : State}
    (a : AfterCall s₀ k s s₂) {m₃ : Mem} (hm : m₃ = xorMem s₂.mem (blk s₀ k) (Iv s₀)) :
    bytesAt m₃ (blk s₀ k) 16 = Spec.Cbc.xor (bytesAt s.mem (blk s₀ k) 16) (bytesAt s₂.mem (Iv s₀) 16) ∧
      bytesAt m₃ (Iv s₀) 16 = bytesAt s₂.mem (Iv s₀) 16 := by
  subst hm
  refine ⟨?_, bytesAt_frame (xorMem_frame _ _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hp.blk_iv hk).symm) (by decide)⟩
  rw [xorMem_bytes _ (hp.blk_iv hk), bytesAt_frame a.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.blk_iv hk
    · exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
    · exact (hp.stk_data.sub_right (UPre.data_sub hk)).symm) (by decide)]

/-- The frame of a block, from the call's and the two blocks'. -/
theorem step_frame {s₀ : State} {k : Nat} {s s₂ : State} (a : AfterCall s₀ k s s₂) {m₃ m₄ : Mem}
    (f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem m₃) (f₄ : Frame [ivR s₀] m₃ m₄) :
    Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩, stkR s₀] s.mem m₄ := by
  refine (a.frame.sub fun r hr => ?_).trans ((f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩

/-- The invariant after a block, from what the block leaves. -/
theorem linv_succ {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ s₄ : State}
    (h : LInv M s₀ k s) (a : AfterCall s₀ k s s₂)
    (g₄ : ∀ r, r ≠ .rax → s₄.gpr r = s₂.gpr r) (rd₄ : s₄.rd = s₂.rd) (wr₄ : s₄.wr = s₂.wr)
    (fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩, stkR s₀] s.mem s₄.mem)
    (hout : outK M s₀ (k + 1) = outK M s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16])
    (hiv : bytesAt s₄.mem (Iv s₀) 16 = chainK M s₀ (k + 1)) :
    WP isa (.block advance) s₄ fun s' => LInv M s₀ (k + 1) s' ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0)) := by
  obtain ⟨s₅, run₅, r13₅, r14₅, zf₅, keep₅, mem₅, rd₅, wr₅⟩ := advance_regs (s := s₄) hk
    (by rw [g₄ _ (by decide), a.g .r13 (by simp [calleeSaved]), h.r13])
    (by rw [g₄ _ (by decide), a.g .r14 (by simp [calleeSaved]), h.r14])
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have g (r : Reg) (hr : r ∈ calleeSaved) (h13 : r ≠ .r13) (h14 : r ≠ .r14) : s₅.gpr r = s.gpr r := by
    rw [keep₅ r h13 h14, g₄ r (calleeSaved_ne_rax hr), a.g r hr]
  have hl' : (outK M s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  refine ⟨⟨?_, ?_, ?_, r13₅, r14₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, zf₅⟩
  · rw [g .rbx (by simp [calleeSaved]) (by decide) (by decide), h.rbx]
  · rw [g .rbp (by simp [calleeSaved]) (by decide) (by decide), h.rbp]
  · rw [g .r12 (by simp [calleeSaved]) (by decide) (by decide), h.r12]
  · rw [g .r15 (by simp [calleeSaved]) (by decide) (by decide), h.r15]
  · rw [g .rsp (by simp [calleeSaved]) (by decide) (by decide), h.rsp]
  · rw [rd₅, rd₄, a.rd']
    exact h.rd
  · rw [wr₅, wr₄, a.wr']
    exact h.wr
  · rw [mem₅]; exact h.frame.trans (stepFrame hk fStep)
  · rw [mem₅, hp.blocksAt_step hk fStep, h.data, hout,
      set_prefix _ _ _ hl' (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [mem₅, hiv]

theorem encBody_ok (v : BlocksImpl) : BodyOk (cfbMode true) (body v.enc encPost) := by
  intro s₀ hp k hk s h
  refine call_ok v hp h encPost fun s₂ a => ?_
  obtain ⟨s₃, run₃, g₃, mem₃, rd₃, wr₃⟩ :=
    xorInto_ok s₂ (P := blk s₀ k) (Q := Iv s₀) (by rw [a.g .r13 (by simp [calleeSaved]), h.r13])
      (by rw [a.g .r12 (by simp [calleeSaved]), h.r12])
      (by rw [a.regs]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [a.regs]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [a.regs]; exact in_rw (by simp) cIv0) (by rw [a.regs]; exact in_rw (by simp) cIv8)
      (by rw [a.wr]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [a.wr]; exact in_rw (by simp) (hp.cBlk8 hk))
  obtain ⟨s₄, run₄, g₄, mem₄, rd₄, wr₄⟩ :=
    copy_ok s₃ (dst := .r12) (src := .r13) (d := 0) (e := 0) (P := Iv s₀) (Q := blk s₀ k)
      (by rw [g₃ _ (by decide), a.g .r12 (by simp [calleeSaved]), h.r12]; simp)
      (by rw [g₃ _ (by decide), a.g .r12 (by simp [calleeSaved]), h.r12])
      (by rw [g₃ _ (by decide), a.g .r13 (by simp [calleeSaved]), h.r13]; simp)
      (by rw [g₃ _ (by decide), a.g .r13 (by simp [calleeSaved]), h.r13])
      (by rw [rd₃, wr₃, a.regs]; exact in_rw (by simp) (hp.cBlk0 hk))
      (by rw [rd₃, wr₃, a.regs]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [wr₃, a.wr]; exact in_rw (by simp) cIv0) (by rw [wr₃, a.wr]; exact in_rw (by simp) cIv8)
      (by decide) (by decide)
  rw [encPost, List.append_assoc, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have ⟨b₃, i₃⟩ := xor_step hp hk a mem₃
  have f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₃.mem := by rw [mem₃]; exact xorMem_frame _ _ _
  have f₄ : Frame [ivR s₀] s₃.mem s₄.mem := by rw [mem₄]; exact copyMem_frame _ _ _
  have b₄ : bytesAt s₄.mem (blk s₀ k) 16 = bytesAt s₃.mem (blk s₀ k) 16 :=
    bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_iv hk) (by decide)
  have i₄ : bytesAt s₄.mem (Iv s₀) 16 = bytesAt s₄.mem (blk s₀ k) 16 := by
    rw [mem₄, copyMem_bytes _ (hp.blk_iv hk).symm, ← mem₄, b₄]
  have newBlk : bytesAt s₄.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK (cfbMode true) s₀ k)) := by
    rw [b₄, b₃, h.block hk, a.iv, h.iv]
  have outSucc : outK (cfbMode true) s₀ (k + 1) = outK (cfbMode true) s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, chainK, cfbMode_out, cfbMode_chain, cfb, cts, ite_true, take_succ_blks s₀ hk,
      encrypt_snoc]
  refine linv_succ hp hk h a (fun r hr => by rw [g₄ r hr, g₃ r hr]) (by rw [rd₄, rd₃]) (by rw [wr₄, wr₃])
    (step_frame a f₃ f₄) outSucc ?_
  rw [i₄]
  simp only [chainK, cfbMode_chain, cts, ite_true, outSucc, next_snoc]

theorem decBody_ok (v : BlocksImpl) : BodyOk (cfbMode false) (body v.enc decPost) := by
  intro s₀ hp k hk s h
  refine call_ok v hp h decPost fun s₂ a => ?_
  obtain ⟨s₃, run₃, g₃, mem₃, rd₃, wr₃⟩ :=
    xorInto_ok s₂ (P := blk s₀ k) (Q := Iv s₀) (by rw [a.g .r13 (by simp [calleeSaved]), h.r13])
      (by rw [a.g .r12 (by simp [calleeSaved]), h.r12])
      (by rw [a.regs]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [a.regs]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [a.regs]; exact in_rw (by simp) cIv0) (by rw [a.regs]; exact in_rw (by simp) cIv8)
      (by rw [a.wr]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [a.wr]; exact in_rw (by simp) (hp.cBlk8 hk))
  obtain ⟨s₄, run₄, g₄, mem₄, rd₄, wr₄⟩ :=
    xorIv_ok s₃ (P := Iv s₀) (Q := blk s₀ k) (by rw [g₃ _ (by decide), a.g .r12 (by simp [calleeSaved]), h.r12])
      (by rw [g₃ _ (by decide), a.g .r13 (by simp [calleeSaved]), h.r13])
      (by rw [rd₃, wr₃, a.regs]; exact in_rw (by simp) cIv0) (by rw [rd₃, wr₃, a.regs]; exact in_rw (by simp) cIv8)
      (by rw [rd₃, wr₃, a.regs]; exact in_rw (by simp) (hp.cBlk0 hk))
      (by rw [rd₃, wr₃, a.regs]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [wr₃, a.wr]; exact in_rw (by simp) cIv0) (by rw [wr₃, a.wr]; exact in_rw (by simp) cIv8)
  rw [decPost, List.append_assoc, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have ⟨b₃, i₃⟩ := xor_step hp hk a mem₃
  have f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₃.mem := by rw [mem₃]; exact xorMem_frame _ _ _
  have f₄ : Frame [ivR s₀] s₃.mem s₄.mem := by rw [mem₄]; exact xorMem_frame _ _ _
  have b₄ : bytesAt s₄.mem (blk s₀ k) 16 = bytesAt s₃.mem (blk s₀ k) 16 :=
    bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_iv hk) (by decide)
  have hb := h.block hk
  have i₄ : bytesAt s₄.mem (Iv s₀) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [mem₄, xorMem_bytes _ (hp.blk_iv hk).symm, i₃, b₃, hb]
    exact xor_xor_cancel (by simp [Spec.Aes.bytesAt, ← hb])
  have newBlk : bytesAt s₄.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK (cfbMode false) s₀ k)) := by
    rw [b₄, b₃, hb, a.iv, h.iv]
  have outSucc : outK (cfbMode false) s₀ (k + 1) = outK (cfbMode false) s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, chainK, cfbMode_out, cfbMode_chain, cfb, cts, Bool.false_eq_true, ite_false,
      take_succ_blks s₀ hk, decrypt_snoc]
  refine linv_succ hp hk h a (fun r hr => by rw [g₄ r hr, g₃ r hr]) (by rw [rd₄, rd₃]) (by rw [wr₄, wr₃])
    (step_frame a f₃ f₄) outSucc ?_
  rw [i₄]
  simp only [chainK, cfbMode_chain, cts, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, next_snoc]

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
    (.block ivArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem encPost_taint : ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14, .r15])
    (.block encPost) h).isSome = true := ⟨_, by taint_decide⟩

theorem decPost_taint : ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14, .r15])
    (.block decPost) h).isSome = true := ⟨_, by taint_decide⟩

theorem encBody_ct (v : BlocksImpl) : BodyCt (cfbMode true) (body v.enc encPost) :=
  fun hp hp' hq k => VG.Proof.AesCbc.X86_64.body_ct (D := fun s₀ _ => Iv s₀) (fun hq _ => pub_Iv hq)
    v.encOk v.encCt v.encNosp v.encDepth pre_taint encPost_taint
    (@fun _ hp _ _ _ h => WP.mono (ivA_wp hp h) fun _ a => Mid.of h a.pre a.saved) hp hp' hq k

theorem decBody_ct (v : BlocksImpl) : BodyCt (cfbMode false) (body v.enc decPost) :=
  fun hp hp' hq k => VG.Proof.AesCbc.X86_64.body_ct (D := fun s₀ _ => Iv s₀) (fun hq _ => pub_Iv hq)
    v.encOk v.encCt v.encNosp v.encDepth pre_taint decPost_taint
    (@fun _ hp _ _ _ h => WP.mono (ivA_wp hp h) fun _ a => Mid.of h a.pre a.saved) hp hp' hq k

end VG.Proof.AesCfb.X86_64
