module

public import VerifiedGarbage.Proof.AesCfb.Spec
public import VerifiedGarbage.Impl.AesCfb.PPC64LE
public import VerifiedGarbage.Proof.AesCbc.Mem
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
import VerifiedGarbage.Proof.AesOfb.PPC64LE.Body
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesCfb.Spec
meta import VerifiedGarbage.Impl.AesCfb.PPC64LE
meta import VerifiedGarbage.Proof.AesCbc.Mem
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.AesOfb.PPC64LE.Body
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-CFB128 on PPC64LE: one block, and constant time

As on x86-64 (`Proof/AesCfb/X86_64/Body.lean`): `encBody_ok` and
`decBody_ok`, one run of `body` takes the loop invariant AES-CBC's proofs
share (`Proof/AesCbc/PPC64LE/Loop.lean`) from `k` blocks to `k + 1`, for
`cfbMode`. The code before the call and the call are AES-OFB's
(`Proof/AesOfb/PPC64LE/Body.lean`). `encBody_ct` and `decBody_ct`: they are
constant time, by the shared framework, with the call on the block at `iv`.
-/

@[expose] public section

namespace VG.Proof.AesCfb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCfb.PPC64LE
open VG.Impl.AesCbc.PPC64LE (whole xorInto copy advance encCall)
open VG.Impl.AesOfb.PPC64LE (ivArgs)
open VG.Proof.AesOfb.PPC64LE (ivA_wp)
open VG.Proof.AesCbc
open VG.Proof.AesCbc.PPC64LE
open VG.Spec.Aes (bytesAt)

/-- What the code before the call and the call leave, for either
direction. -/
structure AfterCall (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  g : ∀ r ∈ preserved, s₂.gpr r = s.gpr r
  wr : s₂.wr = [ivR s₀, dataR s₀, scrR s₀]
  regs : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀]
  rd' : s₂.rd = s.rd
  wr' : s₂.wr = s.wr
  frame : Frame [ivR s₀, ⟨S s₀, 2048⟩] s.mem s₂.mem
  iv : bytesAt s₂.mem (Iv s₀) 16 = Spec.Cbc.aesWith (R s₀) (wK s₀) (bytesAt s.mem (Iv s₀) 16)

theorem call_ok {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State}
    (h : LInv M s₀ k s) (post : List Instr) {Q : State → Prop}
    (hq : ∀ s₂, AfterCall s₀ k s s₂ → WP isa (.block post) s₂ Q) :
    WP isa (body post) s Q := by
  refine WP.seq (WP.mono (ivA_wp hp h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call Proof.Aes.PPC64LE.encryptBlocks_correct encryptBlocks_noFrames a.pre)
    fun s₂ c => hq s₂ ?_)
  have big : Frame (Big s₀) s₀.mem s.mem := UPre.big_of h.frame
  refine ⟨fun r hr => by rw [c.saved r hr, a.saved r hr], by rw [c.wr, a.wr, h.wrs hp],
    by rw [c.rd, c.wr, a.rd, a.wr, h.regs hp], by rw [c.rd, a.rd], by rw [c.wr, a.wr], ?_, ?_⟩
  · have fr := c.frame; rw [a.mem] at fr; exact fr
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
    (g₄ : ∀ r, r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s₂.gpr r) (rd₄ : s₄.rd = s₂.rd) (wr₄ : s₄.wr = s₂.wr)
    (fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩] s.mem s₄.mem)
    (hout : outK M s₀ (k + 1) = outK M s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16])
    (hiv : bytesAt s₄.mem (Iv s₀) 16 = chainK M s₀ (k + 1)) :
    WP isa (.block advance) s₄ (LInv M s₀ (k + 1)) := by
  refine advance_regs (s := s₄) hk
    (by rw [g₄ _ (by decide) (by decide), a.g .r17 (by decide), h.r17])
    (by rw [g₄ _ (by decide) (by decide), a.g .r18 (by decide), h.r18])
    fun s₅ r17₅ r18₅ keep₅ mem₅ rd₅ wr₅ => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h17 : r ≠ .r17) (h18 : r ≠ .r18) : s₅.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, h9, h10⟩ := preserved_ne hr
    rw [keep₅ r h17 h18, g₄ r h9 h10, a.g r hr]
  have hl' : (outK M s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  refine ⟨?_, ?_, ?_, r17₅, r18₅, ?_, fun r hr hv => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g .r14 (by decide) (by decide) (by decide), h.r14]
  · rw [g .r15 (by decide) (by decide) (by decide), h.r15]
  · rw [g .r16 (by decide) (by decide) (by decide), h.r16]
  · rw [g .r19 (by decide) (by decide) (by decide), h.r19]
  · rw [g r hr (fun e => hv (by simp [e])) (fun e => hv (by simp [e])), h.keep r hr hv]
  · rw [rd₅, rd₄, a.rd']; exact h.rd
  · rw [wr₅, wr₄, a.wr']; exact h.wr
  · rw [mem₅]; exact h.frame.trans (stepFrame hk fStep)
  · rw [mem₅, hp.blocksAt_step hk fStep, h.data, hout,
      set_prefix _ _ _ hl' (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [mem₅, hiv]

theorem xorBlk_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {M : Mode} {s s₂ : State}
    (h : LInv M s₀ k s) (a : AfterCall s₀ k s s₂) {rest : List Instr} {Φ : State → Prop}
    (kk : ∀ s₃, (∀ r, r ≠ .r9 → r ≠ .r10 → s₃.gpr r = s₂.gpr r) →
      s₃.mem = xorMem s₂.mem (blk s₀ k) (Iv s₀) → s₃.rd = s₂.rd → s₃.wr = s₂.wr →
      WP isa (.block rest) s₃ Φ) :
    WP isa (.block (xorInto .r17 .r16 ++ rest)) s₂ Φ :=
  xorInto_wp (P := blk s₀ k) (Q := Iv s₀) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [a.g .r17 (by decide), h.r17]) (by rw [a.g .r16 (by decide), h.r16])
    (by rw [a.regs]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [a.regs]; exact in_rw (by simp) (hp.cBlk8 hk))
    (by rw [a.regs]; exact in_rw (by simp) cIv0) (by rw [a.regs]; exact in_rw (by simp) cIv8)
    (by rw [a.wr]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [a.wr]; exact in_rw (by simp) (hp.cBlk8 hk)) kk

theorem encBody_ok : BodyOk (cfbMode true) (body encPost) := by
  intro s₀ hp k hk s h
  refine call_ok hp h encPost fun s₂ a => ?_
  rw [encPost, List.append_assoc]
  refine xorBlk_wp hp hk h a fun s₃ g₃ mem₃ rd₃ wr₃ => ?_
  refine copy_wp (dst := .r16) (src := .r17) (d := 0) (e := 0) (P := Iv s₀) (Q := blk s₀ k)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₃ _ (by decide) (by decide), a.g .r16 (by decide), h.r16, ofNat_zero_add])
    (by rw [g₃ _ (by decide) (by decide), a.g .r16 (by decide), h.r16])
    (by rw [g₃ _ (by decide) (by decide), a.g .r17 (by decide), h.r17, ofNat_zero_add])
    (by rw [g₃ _ (by decide) (by decide), a.g .r17 (by decide), h.r17])
    (by rw [rd₃, wr₃, a.regs]; exact in_rw (by simp) (hp.cBlk0 hk))
    (by rw [rd₃, wr₃, a.regs]; exact in_rw (by simp) (hp.cBlk8 hk))
    (by rw [wr₃, a.wr]; exact in_rw (by simp) cIv0) (by rw [wr₃, a.wr]; exact in_rw (by simp) cIv8)
    fun s₄ g₄ mem₄ rd₄ wr₄ => ?_
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
  refine linv_succ hp hk h a (fun r h9 h10 => by rw [g₄ r h9, g₃ r h9 h10]) (by rw [rd₄, rd₃])
    (by rw [wr₄, wr₃]) (step_frame a f₃ f₄) outSucc ?_
  rw [i₄]
  simp only [chainK, cfbMode_chain, cts, ite_true, outSucc, next_snoc]

theorem decBody_ok : BodyOk (cfbMode false) (body decPost) := by
  intro s₀ hp k hk s h
  refine call_ok hp h decPost fun s₂ a => ?_
  rw [decPost, List.append_assoc]
  refine xorBlk_wp hp hk h a fun s₃ g₃ mem₃ rd₃ wr₃ => ?_
  refine xorInto_wp (P := Iv s₀) (Q := blk s₀ k) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [g₃ _ (by decide) (by decide), a.g .r16 (by decide), h.r16])
    (by rw [g₃ _ (by decide) (by decide), a.g .r17 (by decide), h.r17])
    (by rw [rd₃, wr₃, a.regs]; exact in_rw (by simp) cIv0) (by rw [rd₃, wr₃, a.regs]; exact in_rw (by simp) cIv8)
    (by rw [rd₃, wr₃, a.regs]; exact in_rw (by simp) (hp.cBlk0 hk))
    (by rw [rd₃, wr₃, a.regs]; exact in_rw (by simp) (hp.cBlk8 hk))
    (by rw [wr₃, a.wr]; exact in_rw (by simp) cIv0) (by rw [wr₃, a.wr]; exact in_rw (by simp) cIv8)
    fun s₄ g₄ mem₄ rd₄ wr₄ => ?_
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
  refine linv_succ hp hk h a (fun r h9 h10 => by rw [g₄ r h9 h10, g₃ r h9 h10]) (by rw [rd₄, rd₃])
    (by rw [wr₄, wr₃]) (step_frame a f₃ f₄) outSucc ?_
  rw [i₄]
  simp only [chainK, cfbMode_chain, cts, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, next_snoc]

/-! ## Constant time -/

theorem encPost_taint : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19])
    (.block encPost) h).isSome = true := ⟨_, by taint_decide⟩

theorem decPost_taint : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19])
    (.block decPost) h).isSome = true := ⟨_, by taint_decide⟩

theorem encBody_ct : BodyCt (cfbMode true) (body encPost) :=
  fun hp hp' hq k => VG.Proof.AesCbc.PPC64LE.body_ct (m := fun _ _ s => s.mem) (D := fun s₀ _ => Iv s₀)
    (fun hq _ => pub_Iv hq) Proof.Aes.PPC64LE.encryptBlocks_correct Proof.Aes.PPC64LE.encryptBlocks_ct
    encryptBlocks_noFrames Proof.AesOfb.PPC64LE.pre_taint encPost_taint
    (@fun _ hp _ _ _ h => ivA_wp hp h) hp hp' hq k

theorem decBody_ct : BodyCt (cfbMode false) (body decPost) :=
  fun hp hp' hq k => VG.Proof.AesCbc.PPC64LE.body_ct (m := fun _ _ s => s.mem) (D := fun s₀ _ => Iv s₀)
    (fun hq _ => pub_Iv hq) Proof.Aes.PPC64LE.encryptBlocks_correct Proof.Aes.PPC64LE.encryptBlocks_ct
    encryptBlocks_noFrames Proof.AesOfb.PPC64LE.pre_taint decPost_taint
    (@fun _ hp _ _ _ h => ivA_wp hp h) hp hp' hq k

end VG.Proof.AesCfb.PPC64LE
