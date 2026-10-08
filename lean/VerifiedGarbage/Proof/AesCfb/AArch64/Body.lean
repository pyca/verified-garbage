import VerifiedGarbage.Proof.AesCfb.Spec
import VerifiedGarbage.Proof.AesOfb.AArch64.Body
import VerifiedGarbage.Impl.AesCfb.AArch64

/-!
# AES-CFB128 on AArch64: one block, and constant time

`encBody_ok` and `decBody_ok`: one run of `body` takes the loop invariant
AES-CBC's proofs share (`Proof/AesCbc/AArch64/Loop.lean`) from `k` blocks to
`k + 1`, for `cfbMode`, for any implementation of the block functions
(`BlocksImpl`). The code before the call and the call are AES-OFB's
(`Proof/AesOfb/AArch64/Body.lean`). `encBody_ct` and `decBody_ct`: they are
constant time, by the shared framework, with the call on the block at `iv`.
-/

namespace VG.Proof.AesCfb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCfb.AArch64
open VG.Impl.AesCbc.AArch64 (whole xorInto copy advance mov)
open VG.Impl.AesOfb.AArch64 (ivArgs)
open VG.Proof.AesOfb.AArch64 (IvA ivA_wp)
open VG.Proof.AesCbc
open VG.Proof.AesCbc.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-- The block at `x21` XORed with the one at `x22`. -/
theorem xorIv_ok (s : State) {P Q : Addr} (hp : s.gpr .x21 = P) (hq : s.gpr .x22 = Q)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wp : InRegions s.wr P 8) (wp8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa xorIv s = some s' ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = xorMem s.mem P Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [xorIv, hp, hq, rp, rp8, rq, rq8, wp, wp8], ?_⟩
  refine ⟨fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, ?_, rfl, rfl⟩
  simp only [xorMem, Mem.writeW, Mem.readW, BitVec.setWidth_eq]

/-- What the code before the call and the call leave, for either
direction. -/
structure AfterCall (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  g : ∀ r ∈ preserved, r ≠ .x30 → s₂.gpr r = s.gpr r
  sp : s₂.sp = s.sp
  wr : s₂.wr = [ivR s₀, dataR s₀, scrR s₀]
  regs : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀]
  rd' : s₂.rd = s.rd
  wr' : s₂.wr = s.wr
  frame : Frame [ivR s₀, ⟨S s₀, 2048⟩] s.mem s₂.mem
  iv : bytesAt s₂.mem (Iv s₀) 16 = Spec.Cbc.aesWith (R s₀) (wK s₀) (bytesAt s.mem (Iv s₀) 16)

theorem call_ok {M : Mode} (v : BlocksImpl) {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State}
    (h : LInv M s₀ k s) (post : List Instr) {Q : State → Prop}
    (hq : ∀ s₂, AfterCall s₀ k s s₂ → WP isa (.block post) s₂ Q) :
    WP isa (body v.enc post) s Q := by
  refine WP.seq (WP.mono (ivA_wp hp h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call v.encOk v.encNoFrames a.pre) fun s₂ c => hq s₂ ?_)
  have big : Frame (Big s₀) s₀.mem s.mem := UPre.big_of h.frame
  refine ⟨fun r hr h30 => by rw [c.saved r hr h30, a.saved r hr], by rw [c.sp, a.sp],
    by rw [c.wr, a.wr, h.wrs hp], by rw [c.rd, c.wr, a.rd, a.wr, h.regs hp], by rw [c.rd, a.rd],
    by rw [c.wr, a.wr], ?_, ?_⟩
  · have fr := c.frame; rw [a.mem] at fr; exact fr
  · rw [c.out, a.mem, UPre.sched_bytes hp big, ← aesWith_state]

theorem one {r : Region} {P : Addr} (hd : (⟨P, 16⟩ : Region).Disjoint r) :
    ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact hd

/-- The two blocks after XORing the output block into the data block. -/
theorem xor_step {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ : State}
    (a : AfterCall s₀ k s s₂) {m₃ : Mem} (hm : m₃ = xorMem s₂.mem (blk s₀ k) (Iv s₀)) :
    bytesAt m₃ (blk s₀ k) 16 = Spec.Cbc.xor (bytesAt s.mem (blk s₀ k) 16) (bytesAt s₂.mem (Iv s₀) 16) ∧
      bytesAt m₃ (Iv s₀) 16 = bytesAt s₂.mem (Iv s₀) 16 := by
  subst hm
  refine ⟨?_, Proof.Cmac.bytesAt_frame (xorMem_frame _ _ _) (one (hp.blk_iv hk).symm) (by decide)⟩
  rw [xorMem_bytes _ (hp.blk_iv hk), Proof.Cmac.bytesAt_frame a.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.blk_iv hk
    · exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))) (by decide)]

/-- The frame of a block, from the call's and the two blocks'. -/
theorem step_frame {s₀ : State} {k : Nat} {s s₂ : State} (a : AfterCall s₀ k s s₂) {m₃ m₄ : Mem}
    (f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem m₃) (f₄ : Frame [ivR s₀] m₃ m₄) :
    Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩] s.mem m₄ := by
  refine (a.frame.sub fun r hr => ?_).trans ((f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩

/-- The invariant after a block, from what the block leaves. -/
theorem linv_succ {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ s₄ : State}
    (h : LInv M s₀ k s) (a : AfterCall s₀ k s s₂)
    (g₄ : ∀ r, r ≠ .x9 → r ≠ .x10 → s₄.gpr r = s₂.gpr r) (sp₄ : s₄.sp = s₂.sp) (rd₄ : s₄.rd = s₂.rd)
    (wr₄ : s₄.wr = s₂.wr) (fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩] s.mem s₄.mem)
    (hout : outK M s₀ (k + 1) = outK M s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16])
    (hiv : bytesAt s₄.mem (Iv s₀) 16 = chainK M s₀ (k + 1)) :
    WP isa (.block advance) s₄ (LInv M s₀ (k + 1)) := by
  obtain ⟨s₅, run₅, x22₅, x23₅, keep₅, sp₅, mem₅, rd₅, wr₅⟩ := advance_regs (s := s₄) hk
    (by rw [g₄ _ (by decide) (by decide), a.g .x22 (by simp [preserved]) (by decide), h.x22])
    (by rw [g₄ _ (by decide) (by decide), a.g .x23 (by simp [preserved]) (by decide), h.x23])
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have g (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) (h22 : r ≠ .x22) (h23 : r ≠ .x23) :
      s₅.gpr r = s.gpr r := by
    rw [keep₅ r h22 h23, g₄ r (preserved_ne hr).1 (preserved_ne hr).2, a.g r hr h30]
  have hl' : (outK M s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  obtain ⟨x19', x20', x21', x24', other'⟩ := h.next g
  refine ⟨x19', x20', x21', x22₅, x23₅, x24', other', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sp₅, sp₄, a.sp, h.sp]
  · rw [rd₅, rd₄, a.rd']; exact h.rd
  · rw [wr₅, wr₄, a.wr']; exact h.wr
  · rw [mem₅]; exact h.frame.trans (stepFrame hk fStep)
  · rw [mem₅, hp.blocksAt_step hk fStep, h.data, hout,
      set_prefix _ _ _ hl' (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [mem₅, hiv]

theorem encBody_ok (v : BlocksImpl) : BodyOk (cfbMode true) (body v.enc encPost) := by
  intro s₀ hp k hk s h
  refine call_ok v hp h encPost fun s₂ a => ?_
  obtain ⟨s₃, run₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ :=
    xorInto_ok s₂ (P := blk s₀ k) (Q := Iv s₀) (by rw [a.g .x22 (by simp [preserved]) (by decide), h.x22])
      (by rw [a.g .x21 (by simp [preserved]) (by decide), h.x21])
      (by rw [a.regs]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [a.regs]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [a.regs]; exact in_rw (by simp) cIv0) (by rw [a.regs]; exact in_rw (by simp) cIv8)
      (by rw [a.wr]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [a.wr]; exact in_rw (by simp) (hp.cBlk8 hk))
  obtain ⟨s₄, run₄, g₄, sp₄, mem₄, rd₄, wr₄⟩ :=
    copy_ok s₃ (dst := .x21) (src := .x22) (d := 0) (e := 0) (P := Iv s₀) (Q := blk s₀ k)
      (by rw [g₃ _ (by decide) (by decide), a.g .x21 (by simp [preserved]) (by decide), h.x21]; simp)
      (by rw [g₃ _ (by decide) (by decide), a.g .x21 (by simp [preserved]) (by decide), h.x21])
      (by rw [g₃ _ (by decide) (by decide), a.g .x22 (by simp [preserved]) (by decide), h.x22]; simp)
      (by rw [g₃ _ (by decide) (by decide), a.g .x22 (by simp [preserved]) (by decide), h.x22])
      (by rw [rd₃, wr₃, a.regs]; exact in_rw (by simp) (hp.cBlk0 hk))
      (by rw [rd₃, wr₃, a.regs]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [wr₃, a.wr]; exact in_rw (by simp) cIv0) (by rw [wr₃, a.wr]; exact in_rw (by simp) cIv8)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [encPost, List.append_assoc, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have ⟨b₃, _⟩ := xor_step hp hk a mem₃
  have f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₃.mem := by rw [mem₃]; exact xorMem_frame _ _ _
  have f₄ : Frame [ivR s₀] s₃.mem s₄.mem := by rw [mem₄]; exact copyMem_frame _ _ _
  have b₄ : bytesAt s₄.mem (blk s₀ k) 16 = bytesAt s₃.mem (blk s₀ k) 16 :=
    Proof.Cmac.bytesAt_frame f₄ (one (hp.blk_iv hk)) (by decide)
  have i₄ : bytesAt s₄.mem (Iv s₀) 16 = bytesAt s₄.mem (blk s₀ k) 16 := by
    rw [mem₄, copyMem_bytes _ (hp.blk_iv hk).symm, ← mem₄, b₄]
  have newBlk : bytesAt s₄.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK (cfbMode true) s₀ k)) := by
    rw [b₄, b₃, h.block hk, a.iv, h.iv]
  have outSucc :
      outK (cfbMode true) s₀ (k + 1) = outK (cfbMode true) s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, chainK, cfbMode_out, cfbMode_chain, cfb, cts, ite_true, take_succ_blks s₀ hk,
      encrypt_snoc]
  refine linv_succ hp hk h a (fun r h₁ h₂ => by rw [g₄ r h₁, g₃ r h₁ h₂]) (by rw [sp₄, sp₃])
    (by rw [rd₄, rd₃]) (by rw [wr₄, wr₃]) (step_frame a f₃ f₄) outSucc ?_
  rw [i₄]
  simp only [chainK, cfbMode_chain, cts, ite_true, outSucc, next_snoc]

theorem decBody_ok (v : BlocksImpl) : BodyOk (cfbMode false) (body v.enc decPost) := by
  intro s₀ hp k hk s h
  refine call_ok v hp h decPost fun s₂ a => ?_
  obtain ⟨s₃, run₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ :=
    xorInto_ok s₂ (P := blk s₀ k) (Q := Iv s₀) (by rw [a.g .x22 (by simp [preserved]) (by decide), h.x22])
      (by rw [a.g .x21 (by simp [preserved]) (by decide), h.x21])
      (by rw [a.regs]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [a.regs]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [a.regs]; exact in_rw (by simp) cIv0) (by rw [a.regs]; exact in_rw (by simp) cIv8)
      (by rw [a.wr]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [a.wr]; exact in_rw (by simp) (hp.cBlk8 hk))
  obtain ⟨s₄, run₄, g₄, sp₄, mem₄, rd₄, wr₄⟩ :=
    xorIv_ok s₃ (P := Iv s₀) (Q := blk s₀ k)
      (by rw [g₃ _ (by decide) (by decide), a.g .x21 (by simp [preserved]) (by decide), h.x21])
      (by rw [g₃ _ (by decide) (by decide), a.g .x22 (by simp [preserved]) (by decide), h.x22])
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
    Proof.Cmac.bytesAt_frame f₄ (one (hp.blk_iv hk)) (by decide)
  have hb := h.block hk
  have i₄ : bytesAt s₄.mem (Iv s₀) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [mem₄, xorMem_bytes _ (hp.blk_iv hk).symm, i₃, b₃, hb]
    exact xor_xor_cancel (by simp [Spec.Aes.bytesAt, ← hb])
  have newBlk : bytesAt s₄.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK (cfbMode false) s₀ k)) := by
    rw [b₄, b₃, hb, a.iv, h.iv]
  have outSucc :
      outK (cfbMode false) s₀ (k + 1) = outK (cfbMode false) s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, chainK, cfbMode_out, cfbMode_chain, cfb, cts, Bool.false_eq_true, ite_false,
      take_succ_blks s₀ hk, decrypt_snoc]
  refine linv_succ hp hk h a (fun r h₁ h₂ => by rw [g₄ r h₁ h₂, g₃ r h₁ h₂]) (by rw [sp₄, sp₃])
    (by rw [rd₄, rd₃]) (by rw [wr₄, wr₃]) (step_frame a f₃ f₄) outSucc ?_
  rw [i₄]
  simp only [chainK, cfbMode_chain, cts, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, next_snoc]

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24])
    (.block ivArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem encPost_taint : ∃ h, (taint.check (Taint.ofRegs [.x21, .x22, .x23, .x24])
    (.block encPost) h).isSome = true := ⟨_, by taint_decide⟩

theorem decPost_taint : ∃ h, (taint.check (Taint.ofRegs [.x21, .x22, .x23, .x24])
    (.block decPost) h).isSome = true := ⟨_, by taint_decide⟩

theorem encBody_ct (v : BlocksImpl) : BodyCt (cfbMode true) (body v.enc encPost) :=
  fun hp hp' hq k => VG.Proof.AesCbc.AArch64.body_ct (D := fun s₀ _ => Iv s₀) (fun hq _ => pub_Iv hq)
    v.encOk v.encCt v.encNoFrames pre_taint encPost_taint
    (@fun _ hp _ _ _ h => WP.mono (ivA_wp hp h) fun _ a => Mid.of h a.pre a.saved a.sp) hp hp' hq k

theorem decBody_ct (v : BlocksImpl) : BodyCt (cfbMode false) (body v.enc decPost) :=
  fun hp hp' hq k => VG.Proof.AesCbc.AArch64.body_ct (D := fun s₀ _ => Iv s₀) (fun hq _ => pub_Iv hq)
    v.encOk v.encCt v.encNoFrames pre_taint decPost_taint
    (@fun _ hp _ _ _ h => WP.mono (ivA_wp hp h) fun _ a => Mid.of h a.pre a.saved a.sp) hp hp' hq k

end VG.Proof.AesCfb.AArch64
