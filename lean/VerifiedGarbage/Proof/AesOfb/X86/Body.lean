module

public import VerifiedGarbage.Proof.AesOfb.Spec
public import VerifiedGarbage.Proof.AesCbc.X86.CT
public import VerifiedGarbage.Impl.AesOfb.X86
public import VerifiedGarbage.Proof.AesOfb.Rounds
import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesCbc.X86.Decrypt
import VerifiedGarbage.Proof.AesCbc.X86.Verified
import VerifiedGarbage.Proof.CmacAes.X86.UpdateCorrect
import VerifiedGarbage.Proof.Aes.X86.AesNi.Rounds
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.SpTest
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesOfb.Spec
meta import VerifiedGarbage.Proof.AesCbc.X86.CT
meta import VerifiedGarbage.Impl.AesOfb.X86
meta import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesOfb.Rounds
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.AesCbc.X86.Decrypt
meta import VerifiedGarbage.Proof.AesCbc.X86.Verified
meta import VerifiedGarbage.Proof.CmacAes.X86.UpdateCorrect
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Rounds
meta import VerifiedGarbage.Proof.Framework.X86.Reduce
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.SpTest
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-OFB on x86: one block, and constant time

`body_ok`: one run of `body` takes the loop invariant AES-CBC's proofs
share (`Proof/AesCbc/X86/Body.lean`) from `k` blocks to `k + 1`, for
`ofbMode`, for any implementation of the block functions (`BlocksImpl`).
`body_ct`: it is constant time, by the shared framework, with the call on
the block at `iv`.

With AES-NI (`Ni`): `Impl.AesOfb.X86.cryptNi`, which keeps the output block
in `xmm0` and calls nothing, meets the contract that the code around a block
function meets (`modeX86 ofbMode`), as AES-CBC's encryption with AES-NI does
(`Proof/AesCbc/X86/Decrypt.lean`, whose loop this follows): the invariant
of its loop after `k` blocks (`NInv`), one block (`body_wp`), and its
prologue and epilogue, which are AES-CBC's (`endsZ_wp`). The invariant and
everything but the block are for any mode whose chaining value the loop
keeps in `xmm0` (`whole_wp`): AES-CFB128's encryption uses them too
(`Proof/AesCfb/X86/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOfb.X86

open VG VG.X86 VG.Impl.AesOfb.X86
open VG.Impl.CmacAes.X86 (argOp advance xor4)
open VG.Impl.AesCbc.X86 (whole blkCall)
open VG.Proof.CmacAes.X86 (wp_arg xor4_ok add0 arg_ofNat)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi)
open VG.Proof.AesCbc
open VG.Proof.AesCbc.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (BlocksImpl)

/-- The arguments of a call on the block at `iv`, with the working space at
the start of the scratch buffer. -/
theorem blkPreIv {s₀ : State} (hp : UPre s₀) {s : State}
    (eax : s.gpr .eax = W s₀) (ecx : s.gpr .ecx = arg s₀ 1) (ebx : s.gpr .ebx = Iv s₀)
    (edi : s.gpr .edi = 1) (ebp : s.gpr .ebp = S s₀) (esp : s.gpr .esp = E s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    BlkPre s (W s₀) (Iv s₀) (S s₀) (R s₀) := by
  obtain hb : below (s.gpr .esp) 24 = stkR s₀ := by rw [esp]; exact hp.below_eq
  refine ⟨eax, by rw [ecx]; exact arg_ofNat s₀ 1, ebx, edi, ebp, hp.rounds, by rw [esp]; exact hp.esp24,
    hp.sch_iv, hp.sch_scr.sub_right (Region.sub_prefix (by decide)),
    hp.iv_scr.sub_right (Region.sub_prefix (by decide)), by rw [hb]; exact hp.b_sch, by rw [hb]; exact hp.b_iv,
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), hp.sch_fit, hp.iv_fit,
    by have := hp.scr_fit; omega_using [this], ?_, ?_⟩
  · rw [hrd, hwr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-- What the code before the call leaves. -/
structure IvA (s₀ : State) (s s₁ : State) : Prop where
  pre : BlkPre s₁ (W s₀) (Iv s₀) (S s₀) (R s₀)
  esi : s₁.gpr .esi = s.gpr .esi
  esp : s₁.gpr .esp = s.gpr .esp
  mem : s₁.mem = s.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem ivArgs_eq : ivArgs = [.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .ebx (argOp 2),
    .mov .edi (.imm 1), .mov .ebp (argOp 5)] := rfl

theorem ivA_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv M s₀ k s) :
    WP isa (.block ivArgs) s (IvA s₀ s) := by
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain hargs := hp.args_of (UPre.big_of h.frame)
  have hesp := h.esp
  rw [ivArgs_eq]
  refine wp_arg (s₀ := s₀) hesp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 0 (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), hesp]) (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₁.mem]; exact hargs 1 (by decide)) fun s₂ u₂ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hesp])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₂.mem, u₁.mem]; exact hargs 2 (by decide)) fun s₃ u₃ => wp_movi fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hesp])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hargs 5 (by decide)) fun s₅ u₅ => WP.block_nil ?_
  obtain keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .ebx → r ≠ .edi → r ≠ .ebp → s₅.gpr r = s.gpr r :=
    fun r ha hc hb hd hp' => by
      rw [u₅.other _ hp', u₄.other _ hd, u₃.other _ hb, u₂.other _ hc, u₁.other _ ha]
  obtain rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain esp₅ : s₅.gpr .esp = E s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hesp]
  refine ⟨blkPreIv hp ?_ ?_ ?_ ?_ u₅.gpr esp₅ (by rw [rd₅, h.rd]) (by rw [wr₅, h.wr]),
    keep _ (by decide) (by decide) (by decide) (by decide) (by decide), by rw [esp₅, hesp],
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], rd₅, wr₅⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₅.other _ (by decide), u₄.gpr]

theorem post_eq : post = .mov .ebx (argOp 2) :: (xor4 .esi .ebx .esi 0 0 0 ++ advance) := rfl

theorem body_ok (v : BlocksImpl) : BodyOk ofbMode (body v.enc) := by
  intro s₀ hp k hk s h
  obtain hd := hp.d32 hk
  obtain qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  refine WP.seq (WP.mono (ivA_wp hp h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call v.encOk v.encNosp v.encStack a.pre) fun s₂ c => ?_)
  obtain esp₁ : s₁.gpr .esp = E s₀ := by rw [a.esp, h.esp]
  obtain hb : below (s₁.gpr .esp) 24 = stkR s₀ := by rw [esp₁]; exact hp.below_eq
  -- Memory so far.
  obtain f₂ : Frame [ivR s₀, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀] s.mem s₂.mem := by
    obtain fr := c.frame; rw [hb, a.mem] at fr; exact fr
  obtain fs₂ : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₂.mem :=
    f₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact stepIn (.inr (.inl rfl))
      · exact stepIn (.inr (.inr (.inl (Region.sub_prefix (by decide)))))
      · exact stepIn (.inr (.inr (.inr rfl)))
  obtain bigOf : ∀ {m : Mem}, Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem m →
      Frame (Big s₀) s₀.mem m := fun hf => (UPre.big_of h.frame).trans ((stepFrame hk hf).sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  obtain big₂ := bigOf fs₂
  obtain esi₂ : s₂.gpr .esi = D32 s₀ k := by rw [c.saved .esi (by simp [calleeSaved]), a.esi, h.esi]
  obtain esp₂ : s₂.gpr .esp = E s₀ := by rw [c.saved .esp (by simp [calleeSaved]), esp₁]
  obtain rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, a.rd, a.wr, h.rd, h.wr]
  obtain rwl : s₂.rd ++ s₂.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rw₂, hp.rd, hp.wr]; rfl
  obtain w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wr, hp.wr]
  rw [post_eq]
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rw₂]; exact hp.arg_in (by decide)) (hp.args_of big₂ 2 (by decide))
    fun s₃ u₃ => ?_
  have b₃ : s₃.gpr .ebx = Iv s₀ := u₃.gpr
  obtain i₃ : s₃.gpr .esi = D32 s₀ k := by rw [u₃.other _ (by decide), esi₂]
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [i₃, qN]; omega_using [hk, hdf]) (by rw [b₃]; omega_using [hiv]) (by rw [i₃, qN]; omega_using [hk, hdf])
    (by rw [i₃, add0, hd, u₃.rd, u₃.wr, rwl]; exact covBlk hk (by simp))
    (by rw [b₃, add0, u₃.rd, u₃.wr, rwl]; exact covIv (by simp))
    (by rw [i₃, add0, hd, u₃.wr, w₂]; exact covBlk hk (by simp)) fun s₄ g₄ => ?_
  obtain m₄ : s₄.mem = Proof.Cmac.xor4Mem s₂.mem (blk s₀ k) (blk s₀ k) ((Iv s₀).setWidth 64) := by
    rw [g₄.mem, i₃, b₃, add0, add0, hd, u₃.mem]
  obtain f₄ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₄.mem := by rw [m₄]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  obtain fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₄.mem :=
    fs₂.trans (f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl))
  obtain esp₄ : s₄.gpr .esp = E s₀ := by rw [g₄.gpr _ (by decide) (by decide), u₃.other _ (by decide), esp₂]
  refine WP.mono (advance_wp hp hk (by rw [g₄.gpr _ (by decide) (by decide), i₃]) esp₄
    (hp.args_of (bigOf fStep)) (by rw [g₄.rd, g₄.wr, u₃.rd, u₃.wr, rw₂]))
    fun s₅ ⟨esi₅, esp₅, _, mem₅, rd₅, wr₅, zf₅⟩ => ⟨?_, zf₅⟩
  obtain hblk := h.block hk
  obtain big : Frame (Big s₀) s₀.mem s.mem := UPre.big_of h.frame
  obtain newIv : bytesAt s₅.mem ((Iv s₀).setWidth 64) 16 =
      Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK ofbMode s₀ k) := by
    rw [mem₅, m₄, Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (one (hp.blk_iv hk).symm)
        (by decide),
      c.out, a.mem, UPre.sched_bytes hp big, ← aesWith_state, h.iv]
  obtain newBlk : bytesAt s₅.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (bytesAt s₅.mem ((Iv s₀).setWidth 64) 16) := by
    rw [mem₅, m₄, xorIn4_bytes _ (hp.blk_iv hk), ← hblk,
      Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.blk_iv hk
        · exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
        · exact hp.b_data.symm.sub_left (UPre.data_sub hk)) (by decide),
      Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (one (hp.blk_iv hk).symm) (by decide)]
  obtain hl : ((blks s₀).take k).length = k := by simp [Spec.Cbc.blocksAt]; omega_using [hk]
  obtain outSucc : outK ofbMode s₀ (k + 1) = outK ofbMode s₀ k ++ [bytesAt s₅.mem (blk s₀ k) 16] := by
    rw [newBlk, newIv]
    simp only [outK, chainK, ofbMode_out, ofbMode_chain, take_succ_blks s₀ hk, crypt_snoc, hl]
  obtain hl' : (outK ofbMode s₀ k).length = k := by rw [outK, Mode.length_out, hl]
  refine ⟨esi₅, esp₅, by rw [rd₅, g₄.rd, u₃.rd, c.rd, a.rd, h.rd],
    by rw [wr₅, g₄.wr, u₃.wr, c.wr, a.wr, h.wr], by rw [mem₅]; exact h.frame.trans (stepFrame hk fStep),
    ?_, ?_⟩
  · rw [mem₅, hp.blocksAt_step hk fStep, h.data, ← mem₅, outSucc,
      set_prefix _ _ _ hl' (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, ofbMode_chain, take_succ_blks s₀ hk, List.length_append, List.length_singleton, hl,
      next_succ]

/-! ## Constant time -/

theorem pre_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block ivArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem post_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block post) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- What the code before the call leaves, as `Mid`. -/
theorem mid_of {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₁ : State}
    {M : Mode} (h : LInv M s₀ k s) (a : IvA s₀ s s₁) : Mid s₀ k (Iv s₀) s₁ :=
  ⟨hk, a.pre, ⟨ivR s₀, by simp, fun _ h => h⟩, by rw [a.esi, h.esi],
    ⟨by rw [a.esp, h.esp], by rw [a.wr, h.wr], fun _ hi => by rw [a.mem]; exact hp.arg_keep (UPre.big_of h.frame) hi⟩,
    by rw [a.mem]; exact UPre.big_of h.frame⟩

theorem body_ct (v : BlocksImpl) : BodyCt ofbMode (body v.enc) :=
  fun hp hp' hq k => VG.Proof.AesCbc.X86.body_ct (D := fun s₀ _ => Iv s₀) (fun hq _ => pub_arg hq (by decide))
    v.encOk v.encCt v.encNosp v.encStack pre_taint post_taint
    (@fun _ hp _ hk _ h => WP.mono (ivA_wp hp h) fun _ a => mid_of hp hk h a) hp hp' hq k

end VG.Proof.AesOfb.X86

namespace VG.Proof.AesOfb.X86.Ni

open VG VG.X86 VG.X86.RegUpd
open VG.Impl.AesOfb.X86 (niBody cryptNi)
open VG.Impl.CmacAes.X86 (at_ niPre niPost)
open VG.Proof.Aes.X86.AesNi (aes_ok st st_ext getD_ofFn getD_st byte_xor)
open VG.Proof.CmacAes.X86 (niPre_run niKeys st_readW st_getD sub_one_ofNat add0' arg_ofNat ea_at')
open VG.Proof.AesCbc
open VG.Proof.AesCbc.X86
open VG.Spec.Aes (bytesAt)

/-- `pxor` of a data block with an output block is §6.4's `Pⱼ ⊕ Oⱼ`. -/
theorem st_xor (d o : BitVec 128) :
    (st (XBinOp.eval .pxor d o)).toList = Spec.Cbc.xor (st d).toList (st o).toList := by
  apply Proof.Cmac.ext16 (by simp) (by simp [Spec.Cbc.xor])
  intro i hi
  rw [st_getD _ hi, xor_eq, Proof.Cmac.getD_xor (by simp) (by simpa using hi), st_getD d hi, st_getD o hi]
  exact byte_xor d o i

/-- The invariant of the loop after `k` blocks, for the mode `M`: since the
prologue left the memory `m`, only the data has changed, whose first `k`
blocks are the mode's output (for AES-OFB, XORed with the output blocks),
and the chaining value (the last output block) is in `xmm0`. -/
structure NInv (M : Mode) (s₀ : State) (m : Mem) (k : Nat) (s : State) : Prop where
  esi : s.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * k)
  edi : s.gpr .edi = BitVec.ofNat 32 (N s₀ - k)
  eax : s.gpr .eax = W s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 (R s₀)
  edx : s.gpr .edx = Iv s₀
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀] m s.mem
  data : Spec.Cbc.blocksAt s.mem ((Dp s₀).setWidth 64) (N s₀) = outK M s₀ k ++ (blks s₀).drop k
  chain : (st (s.xmm .xmm0)).toList = chainK M s₀ k

theorem pre_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {s : State} (h : LInv M s₀ 0 s) :
    WP isa (.block niPre) s (NInv M s₀ s.mem 0) := by
  obtain big := UPre.big_of h.frame
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  refine niPre_run h.esp (fun i hi => by rw [hrw]; exact hp.arg_in hi) (fun i hi => hp.arg_keep big hi)
    (by rw [hrw]; exact ⟨ivR s₀, by simp [hp.wr], Region.contains_self _ _⟩)
    fun s' edi eax ecx edx esi esp mem rd wr x => ⟨by rw [esi, h.esi], ?_, eax, ?_, edx, by rw [esp, h.esp],
      by rw [rd, h.rd], by rw [wr, h.wr], by rw [mem]; exact Frame.refl _ _, by rw [mem]; exact h.data, ?_⟩
  · rw [edi, Nat.sub_zero]; exact arg_ofNat s₀ 4
  · rw [ecx]; exact arg_ofNat s₀ 1
  · rw [x, st_readW]; exact h.iv

/-- One block. -/
theorem body_wp {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hm : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m) {k : Nat}
    (hk : k < N s₀) {s : State} (h : NInv ofbMode s₀ m k s) :
    WP isa niBody s fun s' => NInv ofbMode s₀ m (k + 1) s' ∧ s'.zf = some (decide (k + 1 = N s₀)) := by
  obtain big : Frame (Big s₀) s₀.mem s.mem := (UPre.big_of hm).trans (h.frame.mono (by simp))
  obtain hdf := hp.data_fit
  obtain cB : (dataR s₀).Contains (blk s₀ k) 16 :=
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hdf, hk])
  obtain hK := niKeys (s := s) (nr := R s₀) (by rcases hp.rounds with h | h | h <;> omega_using [h]) hp.sch_fit h.eax
    (by rw [h.rd]; simp [hp.rd])
  rw [UPre.sched_bytes hp big] at hK
  -- The output block enciphered in `xmm0`.
  refine WP.seq (WP.mono (aes_ok [.xmm0] (by decide) (by decide) hp.rounds s hK h.ecx) fun s₂ ⟨c₂, f₂⟩ => ?_)
  obtain ⟨o, ho⟩ : ∃ o, s₂.xmm .xmm0 = o := ⟨_, rfl⟩
  obtain newOut : (st o).toList = Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK ofbMode s₀ k) := by
    rw [← ho, c₂ _ List.mem_cons_self, ← h.chain]
    exact congrArg (fun y => (Spec.Aes.cipher (R s₀) _ y).toList) (st_ext fun i hi => by
      rw [getD_ofFn hi]
      exact (st_getD _ hi).trans (getD_st _ hi).symm).symm
  obtain ea₂ : s₂.ea (at_ .esi 0) = blk s₀ k := by
    rw [ea_at', f₂.gpr, h.esi]
    show (Dp s₀ + BitVec.ofNat 32 (16 * k) + BitVec.ofNat 32 0).setWidth 64 = _
    rw [add0']
    exact hp.dataA hk
  obtain hin : InRegions (s₂.rd ++ s₂.wr) (blk s₀ k) 16 := by
    rw [f₂.wr, h.wr]
    exact ⟨dataR s₀, by simp [hp.wr], cB⟩
  -- The data block XORed with it through `xmm7`, and stored.
  obtain ⟨d, hd⟩ : ∃ d, s₂.mem.readW (blk s₀ k) 128 = d := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, XBinOp.eval .pxor d o = x := ⟨_, rfl⟩
  obtain ⟨s₃, hs₃⟩ : ∃ s₃, (s₂.setXmm .xmm7 d).setXmm .xmm7
    (XBinOp.eval .pxor ((s₂.setXmm .xmm7 d).xmm .xmm7) ((s₂.setXmm .xmm7 d).xmm .xmm0)) = s₃ := ⟨_, rfl⟩
  rw [WP.block_cons_iff]
  refine ⟨s₂.setXmm .xmm7 d, by
    simp only [isa, reduceExec, State.load128, ea₂, hin, ite_true, Option.map_some, hd], ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₃, hs₃ ▸ rfl, ?_⟩
  obtain x₃ : s₃.xmm .xmm7 = x := by
    rw [← hs₃, xmm_setXmm_self, xmm_setXmm_self, xmm_setXmm_of_ne _ _ (by decide), ho, hx]
  obtain o₃ : s₃.xmm .xmm0 = o := by
    rw [← hs₃, xmm_setXmm_of_ne _ _ (by decide), xmm_setXmm_of_ne _ _ (by decide), ho]
  obtain g₃ : s₃.gpr = s.gpr := by rw [← hs₃, gpr_setXmm, gpr_setXmm, f₂.gpr]
  obtain m₃ : s₃.mem = s.mem := by rw [← hs₃, mem_setXmm, mem_setXmm, f₂.mem]
  obtain rd₃ : s₃.rd = s₀.rd := by rw [← hs₃, rd_setXmm, rd_setXmm, f₂.rd, h.rd]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [← hs₃, wr_setXmm, wr_setXmm, f₂.wr, h.wr]
  obtain ea₃ : s₃.ea (at_ .esi 0) = blk s₀ k := by rw [← ea₂]; simp only [State.ea, g₃, f₂.gpr]
  obtain hout : InRegions s₃.wr (blk s₀ k) 16 := by
    rw [wr₃]
    exact ⟨dataR s₀, by simp [hp.wr], cB⟩
  obtain ⟨s₄, hs₄⟩ : ∃ s₄ : State, { s₃ with mem := s₃.mem.writeW (blk s₀ k) x } = s₄ := ⟨_, rfl⟩
  rw [WP.block_cons_iff]
  refine ⟨s₄, by simp only [isa, reduceExec, State.store128, ea₃, hout, ite_true, x₃, hs₄], ?_⟩
  obtain g₄ : s₄.gpr = s.gpr := by rw [← hs₄]; exact g₃
  obtain m₄ : s₄.mem = s.mem.writeW (blk s₀ k) x := by rw [← hs₄, ← m₃]
  obtain rd₄ : s₄.rd = s₀.rd := by rw [← hs₄]; exact rd₃
  obtain wr₄ : s₄.wr = s₀.wr := by rw [← hs₄]; exact wr₃
  obtain o₄ : s₄.xmm .xmm0 = o := by rw [← hs₄]; exact o₃
  -- The new block, and the blocks after it.
  obtain fw : Frame [⟨blk s₀ k, 16⟩] s.mem s₄.mem := by
    rw [m₄]
    exact (Frame.refl _ _).writeW (r := ⟨blk s₀ k, 16⟩) List.mem_cons_self _ (Region.contains_self _ _)
  obtain nb : bytesAt s₄.mem (blk s₀ k) 16 = (st x).toList := by
    rw [m₄, ← st_readW, Mem.readW_writeW_self _ _ 16 _ (by decide)]
  obtain hl : ((blks s₀).take k).length = k := by simp [Spec.Cbc.blocksAt]; omega_using [hk]
  obtain hl' : (outK ofbMode s₀ k).length = k := by rw [outK, Mode.length_out, hl]
  obtain newBlk : (st x).toList =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)) (st o).toList := by
    rw [← hx, ← block_of_data h.data hk, ← st_readW, ← f₂.mem, hd]
    exact st_xor d o
  obtain outSucc : outK ofbMode s₀ (k + 1) = outK ofbMode s₀ k ++ [(st x).toList] := by
    rw [newBlk, newOut]
    simp only [outK, chainK, ofbMode_out, ofbMode_chain, take_succ_blks s₀ hk, crypt_snoc, hl]
  obtain hpos : 0 < N s₀ - k := by omega_using [hk]
  obtain edi' : s.gpr .edi - 1 = BitVec.ofNat 32 (N s₀ - (k + 1)) := by
    rw [h.edi, sub_one_ofNat hpos]; rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, execAlu, readSrc, isa, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, xmm_setReg, xmm_arithFlags, zf_setReg, zf_arithFlags, reduceCtorEq, ↓reduceIte, g₄]
  · rw [h.esi, BitVec.add_assoc]
    exact congrArg (Dp s₀ + ·) (BitVec.ofNat_add ..).symm
  · exact edi'
  · exact h.eax
  · exact h.ecx
  · exact h.edx
  · exact h.esp
  · exact rd₄
  · exact wr₄
  · rw [m₄]
    exact h.frame.writeW (r := dataR s₀) List.mem_cons_self _ cB
  · rw [hp.blocksAt_step hk (fw.mono (by simp)), nb, h.data, outSucc,
      set_prefix _ _ _ hl' (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [o₄, newOut]
    simp only [chainK, ofbMode_chain, take_succ_blks s₀ hk, List.length_append, List.length_singleton, hl,
      next_succ]
  · rw [edi', MdStream.X86.ofNat_beq_zero (by have : N s₀ < 2 ^ 32 := (arg s₀ 4).isLt; omega_using [this])]
    exact congrArg some (decide_eq_decide.mpr (by omega_using [hk]))

/-- The loop, from what one run of its body does. -/
theorem loop_wp {M : Mode} {body : Prog isa} {s₀ : State} {m : Mem}
    (hb : ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, NInv M s₀ m k s →
      WP isa body s fun s' => NInv M s₀ m (k + 1) s' ∧ s'.zf = some (decide (k + 1 = N s₀))) {k : Nat}
    (hk : k < N s₀) {s : State} (h : NInv M s₀ m k s) : WP isa (.loop body .ne) s (NInv M s₀ m (N s₀)) := by
  refine WP.loop (M := isa) (body := body) (c := .ne) (Q := NInv M s₀ m (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ NInv M s₀ m j t) ?_ (N s₀ - k) s ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (hb hk h) fun s' ⟨h', hz⟩ => ?_
  obtain ev : isa.eval .ne s' = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s' = _; rw [MdStream.X86.eval_ne, hz]; rfl
  by_cases hz' : k + 1 = N s₀
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [← hz']
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, hz'], h'⟩

/-- The chaining value stored: the invariant the epilogue starts from, with
only the block at `iv` and the data changed since the prologue. -/
theorem post_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hm : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m) {s : State}
    (h : NInv M s₀ m (N s₀) s) :
    WP isa (.block niPost) s fun t => LInv M s₀ (N s₀) t ∧ Frame (FB s₀ 0) m t.mem := by
  obtain ea : s.ea (at_ .edx 0) = (Iv s₀).setWidth 64 := by
    rw [ea_at', h.edx]
    show (Iv s₀ + BitVec.ofNat 32 0).setWidth 64 = _
    rw [add0']
  obtain hout : InRegions s.wr ((Iv s₀).setWidth 64) 16 := by
    rw [h.wr]
    exact ⟨ivR s₀, by simp [hp.wr], Region.contains_self _ _⟩
  obtain fw : Frame [ivR s₀] s.mem (s.mem.writeW ((Iv s₀).setWidth 64) (s.xmm .xmm0)) :=
    (Frame.refl _ _).writeW (r := ivR s₀) List.mem_cons_self _ (Region.contains_self _ _)
  rw [niPost, WP.block_cons_iff]
  refine ⟨{ s with mem := s.mem.writeW ((Iv s₀).setWidth 64) (s.xmm .xmm0) }, by
    simp only [isa, reduceExec, State.store128, ea, hout, ite_true],
    WP.block_nil ⟨⟨h.esi, h.esp, h.rd, h.wr, ?_, ?_, ?_⟩, ?_⟩⟩
  · show Frame _ (savedMem s₀) (s.mem.writeW _ _)
    exact (hm.trans (h.frame.mono (by simp))).writeW (r := ivR s₀) List.mem_cons_self _ (Region.contains_self _ _)
  · show Spec.Cbc.blocksAt (s.mem.writeW _ _) _ _ = _
    rw [← h.data]
    simp only [Spec.Cbc.blocksAt]
    refine List.map_congr_left fun j hj => Proof.Cmac.bytesAt_frame fw (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.iv_data.symm.sub_left (UPre.data_sub (List.mem_range.mp hj))
  · show bytesAt (s.mem.writeW _ _) _ 16 = _
    rw [← st_readW, Mem.readW_writeW_self _ _ 16 _ (by decide), h.chain]
  · show Frame _ m (s.mem.writeW _ _)
    exact (h.frame.mono (by simp)).writeW (r := ivR s₀) List.mem_cons_self _ (Region.contains_self _ _)

/-- The whole function around a loop of `body`, from what one run of `body`
does: the mode's contract, and every byte of the scratch buffer unchanged
or zero. -/
theorem whole_wp {M : Mode} {body : Prog isa}
    (hb : ∀ {s₀ : State}, UPre s₀ → ∀ {m : Mem},
      Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m → ∀ {k : Nat}, k < N s₀ →
        ∀ {s : State}, NInv M s₀ m k s →
          WP isa body s fun s' => NInv M s₀ m (k + 1) s' ∧ s'.zf = some (decide (k + 1 = N s₀)))
    {s₀ : State} (h0 : (modeX86 M).pre s₀) :
    WP isa (.seq (.block Impl.CmacAes.X86.setup)
      (.seq (.ite .e (.block []) (.seq (.block niPre) (.seq (.loop body .ne) (.block niPost))))
        (.block (Impl.CmacAes.X86.restore 5 ++ Impl.AesCbc.X86.zeroSaved)))) s₀ fun s' =>
      abiPreserved s₀ s' ∧ (modeX86 M).post s₀ s' ∧
      ∀ i, 0 ≤ i → i < 2176 →
        s'.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 i) = s₀.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 i) ∨
          s'.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 i) = 0 :=
  endsZ_wp h0 fun h hn => WP.seq (WP.mono (pre_wp (UPre.of h0) h) fun _ x₂ =>
    WP.seq (WP.mono (loop_wp (hb (UPre.of h0) h.frame) hn x₂) fun _ x₃ => post_wp (UPre.of h0) h.frame x₃))

/-- The contract, and every byte of the scratch buffer unchanged or zero. -/
theorem correct_wp {s₀ : State} (h0 : (modeX86 ofbMode).pre s₀) :
    WP isa cryptNi s₀ fun s' => abiPreserved s₀ s' ∧ (modeX86 ofbMode).post s₀ s' ∧
      ∀ i, 0 ≤ i → i < 2176 →
        s'.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 i) = s₀.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 i) ∨
          s'.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 i) = 0 :=
  whole_wp (fun hp _ hm _ hk _ h => body_wp hp hm hk h) h0

/-- It runs to the contract's postcondition, as the code around a block
function does (`whole_wp`). -/
theorem correct (s : State) (hs : (modeX86 ofbMode).pre s) :
    ∃ t s', Exec isa cryptNi s t s' ∧ abiPreserved s s' ∧ (modeX86 ofbMode).post s s' :=
  (correct_wp hs).mono fun _ h => ⟨h.1, h.2.1⟩

theorem ct : ConstantTime isa (modeX86 ofbMode).pre (modeX86 ofbMode).pub cryptNi :=
  VG.Taint.constantTime (A := sseTaint) Decrypt.τ₀
    (fun _ _ h₁ h₂ hp => Decrypt.agree₀ (UPre.of h₁) (UPre.of h₂) hp) (by taint_decide)

/-- It writes `esp` nowhere: it has no frame and no call. -/
theorem noSp : NoSp cryptNi := NoSp.of_all (by lit_decide)

theorem stack : stackUse cryptNi = 0 := by lit_decide

theorem spSafe : cryptNi.all (fun i => !isa.writesSp i) = true := Code.all_of_spTest (by lit_decide)

end VG.Proof.AesOfb.X86.Ni
