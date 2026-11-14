module

import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.CT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Gcm.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksContract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Fin
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Full
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! ### `AesGcm.X86_64.Blocks.Fn`, which only this module used -/

section

/-!
# AES-GCM on whole blocks, x86-64: correctness

Untrusted: everything here is checked by Lean. The entry, the first
`16 ⌊n / 16⌋` blocks in one pass (with `stitch`), and the rest
(`encrypt_wp`, `decrypt_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

section
variable {M : CtxMode} {s : State} (hp : BP M s)
include hp

/-- With nothing left, `Mid` is the end, when encrypting. -/
theorem encDone_of {q k : Nat} {st : State} (M : Mid s q k (ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q)) st)
    (h0 : n s - q = 0) : EncDone s st := by
  have hq : q = n s := by have := M.q_le; omega_using [h0, this]
  subst hq
  exact ⟨⟨M.saved, keep_r hp M.frame⟩, M.data, M.ctr, M.y⟩

/-- With nothing left, `Mid` is the end, when decrypting. -/
theorem decDone_of {q k : Nat} {st : State} (M : Mid s q k (blocksAt s.mem (D s) q) st) (h0 : n s - q = 0) :
    DecDone s st := by
  have hq : q = n s := by have := M.q_le; omega_using [h0, this]
  subst hq
  exact ⟨⟨M.saved, keep_r hp M.frame⟩, M.data, M.ctr, M.y⟩

end

theorem encrypt_wp (v : GcmImpl) {M : CtxMode} {aligned : Bool} (st : Option (StitchCode M aligned)) {s : State}
    (hpre : Proof.AesGcm.blocksPreM M s) :
    WP isa (encrypt v.callees.ctr v.callees.gh (st.map (·.enc)) aligned (encFull st) (encSmall st) (encSmall4 st) (st.map (·.encS))) s (EncDone s) := by
  have hp := BP.ofM hpre
  refine WP.seq (WP.mono (entry_ok hp) fun s₁ ⟨h11, hg, hk, hf, hrd, hwr⟩ => ?_)
  have tl : ∀ q st, Mid s q q (ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q)) st →
      WP isa (tail (ctrCall v.callees.ctr) (ghCall v.callees.gh)) st (EncDone s) := fun q st M =>
    tail_calls hp _ _ M (fun _ M' h0 => encDone_of hp M' h0) fun _ M' hlt => encCalls_ok hp v M' hlt
  cases st with
  | none => exact WP.seq (WP.block_nil (tl 0 s₁ (mid_entry hp hg hk hf hrd hwr)))
  | some p =>
    rcases p with ⟨enc, dec, full, fullD, small, smallD, small4, encS, decS, ok, okS, encP, decP, encPS, decPS⟩
    cases full with
    | false => exact WP.seq (WP.seq (WP.mono (stitchE_ok hp ok h11 hg hk hf hrd hwr) fun st M =>
        WP.mono (rest_ok hp rfl M) fun st' M' => tl _ st' M'))
    | true =>
      exact fullBody_ok hp (aligned := aligned) (small := small) (small4 := small4) (pieceS := some encS) (fun _ h => ok.1 _ h (Nat.mod_one _))
        (fun _ h hl => okS.1 _ h hl)
        (fun _ _ h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP =>
          encDone_of hp (stitchEFull_ok hp h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP) (Nat.sub_self _))
        (fun h16 _ M => WP.seq (WP.mono (rest_ok hp (by omega_using [h16]) M) fun st' M' => tl _ st' M'))
        h11 hg hk hf hrd hwr

theorem decrypt_wp (v : GcmImpl) {M : CtxMode} {aligned : Bool} (st : Option (StitchCode M aligned)) {s : State}
    (hpre : Proof.AesGcm.blocksPreM M s) :
    WP isa (decrypt v.callees.ctr v.callees.gh (st.map (·.dec)) aligned (decFull st) (decSmall st) (decSmall4 st) (st.map (·.decS))) s (DecDone s) := by
  have hp := BP.ofM hpre
  refine WP.seq (WP.mono (entry_ok hp) fun s₁ ⟨h11, hg, hk, hf, hrd, hwr⟩ => ?_)
  have tl : ∀ q st, Mid s q q (blocksAt s.mem (D s) q) st →
      WP isa (tail (ghCall v.callees.gh) (ctrCall v.callees.ctr)) st (DecDone s) := fun q st M =>
    tail_calls hp _ _ M (fun _ M' h0 => decDone_of hp M' h0) fun _ M' hlt => decCalls_ok hp v M' hlt
  cases st with
  | none => exact WP.seq (WP.block_nil (tl 0 s₁ (mid_entry hp hg hk hf hrd hwr)))
  | some p =>
    rcases p with ⟨enc, dec, full, fullD, small, smallD, small4, encS, decS, ok, okS, encP, decP, encPS, decPS⟩
    cases fullD with
    | false => exact WP.seq (WP.seq (WP.mono (stitchD_ok hp ok h11 hg hk hf hrd hwr) fun st M =>
        WP.mono (rest_ok hp rfl M) fun st' M' => tl _ st' M'))
    | true =>
      exact fullBody_ok hp (aligned := aligned) (small := smallD) (small4 := small4) (pieceS := some decS) (dec := true) (fun _ h => ok.2 _ h (Nat.mod_one _))
        (fun _ h hl => okS.2 _ h hl)
        (fun _ _ h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP =>
          decDone_of hp (stitchDFull_ok hp h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP) (Nat.sub_self _))
        (fun h16 _ M => WP.seq (WP.mono (rest_ok hp (by omega_using [h16]) M) fun st' M' => tl _ st' M'))
        h11 hg hk hf hrd hwr

end VG.Proof.AesGcm.X86_64.Blocks

end

end


/-!
# AES-GCM on whole blocks, x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
of `vg_aes_gcm_encrypt_blocks` and `vg_aes_gcm_decrypt_blocks` (for any
implementations `v` of `vg_aes_ctr32` and `vg_ghash`, with or without the
interleaved loops), a state satisfying their precondition, and the shared
contracts of `Spec/Gcm/Contract.lean` (with 8 bytes of stack, for the return
address of a call: the functions called make no calls).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

open Gcm.X86_64.Stitch (CtxMode)

/-- The loops `st` for any kind of key context are the same code. -/
theorem map_code_enc (st : Option StitchImpl) (M : CtxMode) : (st.map (·.code M)).map (·.enc) = st.map (·.enc) := by
  cases st <;> rfl

theorem map_code_dec (st : Option StitchImpl) (M : CtxMode) : (st.map (·.code M)).map (·.dec) = st.map (·.dec) := by
  cases st <;> rfl

section
variable (v : GcmImpl) {M : CtxMode} {aligned : Bool} (st : Option (StitchCode M aligned))

theorem encryptBlocks_mx :
    (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc)) aligned (encFull st) (encSmall st) (encSmall4 st) (st.map (·.encS))).allInstrs (fun i => !loadsMxcsr i) = true := by
  unfold Blocks.encrypt encFull encSmall encSmall4
  refine StitchImpl.blocks_cases st (·.enc) (·.encS) (·.full) (·.small) (·.small4) aligned _ _ (fun c => c.allInstrs (fun i => !loadsMxcsr i) = true) ?_ (fun i b c _ => ?_) (fun i b c _ => ?_)
  · cases aligned <;>
    simp only [Blocks.blocks, Blocks.body, Blocks.head, Blocks.fullBody, Blocks.smallMin, Blocks.skip4, Blocks.smallPart, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.and_self, Blocks.stitchPart, Blocks.scratchSetup,
      Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.gh.mxcsr, Bool.true_and,
      Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;> decide +kernel
  all_goals cases aligned <;> cases b <;> cases c <;>
    simp only [Blocks.blocks, Blocks.body, Blocks.head, Blocks.fullBody, Blocks.smallMin, Blocks.skip4, Blocks.smallPart, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.and_self, Blocks.stitchPart, Blocks.scratchSetup,
      Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.allInstrs, GcmImpl.callees, i.encP.mxcsr, i.encPS.mxcsr, Option.getD_some, v.ctr.mxcsr, v.gh.mxcsr, Bool.true_and,
      Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;> decide +kernel

theorem decryptBlocks_mx :
    (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec)) aligned (decFull st) (decSmall st) (decSmall4 st) (st.map (·.decS))).allInstrs (fun i => !loadsMxcsr i) = true := by
  unfold Blocks.decrypt decFull decSmall decSmall4
  refine StitchImpl.blocks_cases st (·.dec) (·.decS) (·.fullD) (·.smallD) (·.small4) aligned _ _ (fun c => c.allInstrs (fun i => !loadsMxcsr i) = true) ?_ (fun i b c _ => ?_) (fun i b c _ => ?_)
  · cases aligned <;>
    simp only [Blocks.blocks, Blocks.body, Blocks.head, Blocks.fullBody, Blocks.smallMin, Blocks.skip4, Blocks.smallPart, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.and_self, Blocks.stitchPart, Blocks.scratchSetup,
      Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.gh.mxcsr, Bool.true_and,
      Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;> decide +kernel
  all_goals cases aligned <;> cases b <;> cases c <;>
    simp only [Blocks.blocks, Blocks.body, Blocks.head, Blocks.fullBody, Blocks.smallMin, Blocks.skip4, Blocks.smallPart, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.and_self, Blocks.stitchPart, Blocks.scratchSetup,
      Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.allInstrs, GcmImpl.callees, i.decP.mxcsr, i.decPS.mxcsr, Option.getD_some, v.ctr.mxcsr, v.gh.mxcsr, Bool.true_and,
      Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;> decide +kernel

theorem encryptBlocks_spSafe :
    (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc)) aligned (encFull st) (encSmall st) (encSmall4 st) (st.map (·.encS))).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold Blocks.encrypt encFull encSmall encSmall4
  refine StitchImpl.blocks_cases st (·.enc) (·.encS) (·.full) (·.small) (·.small4) aligned _ _ (fun c => c.all (fun i => !X86_64.isa.writesSp i) = true) ?_ (fun i b c _ => ?_) (fun i b c _ => ?_)
  · cases aligned <;>
    simp only [Blocks.blocks, Blocks.body, Blocks.head, Blocks.fullBody, Blocks.smallMin, Blocks.skip4, Blocks.smallPart, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.and_self, Blocks.stitchPart, Blocks.scratchSetup,
      Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.all, GcmImpl.callees, v.ctr.spSafe, v.gh.spSafe, Bool.true_and,
      Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;> decide +kernel
  all_goals cases aligned <;> cases b <;> cases c <;>
    simp only [Blocks.blocks, Blocks.body, Blocks.head, Blocks.fullBody, Blocks.smallMin, Blocks.skip4, Blocks.smallPart, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.and_self, Blocks.stitchPart, Blocks.scratchSetup,
      Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.all, GcmImpl.callees, i.encP.spSafe, i.encPS.spSafe, Option.getD_some, v.ctr.spSafe, v.gh.spSafe, Bool.true_and,
      Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;> decide +kernel

theorem decryptBlocks_spSafe :
    (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec)) aligned (decFull st) (decSmall st) (decSmall4 st) (st.map (·.decS))).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold Blocks.decrypt decFull decSmall decSmall4
  refine StitchImpl.blocks_cases st (·.dec) (·.decS) (·.fullD) (·.smallD) (·.small4) aligned _ _ (fun c => c.all (fun i => !X86_64.isa.writesSp i) = true) ?_ (fun i b c _ => ?_) (fun i b c _ => ?_)
  · cases aligned <;>
    simp only [Blocks.blocks, Blocks.body, Blocks.head, Blocks.fullBody, Blocks.smallMin, Blocks.skip4, Blocks.smallPart, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.and_self, Blocks.stitchPart, Blocks.scratchSetup,
      Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.all, GcmImpl.callees, v.ctr.spSafe, v.gh.spSafe, Bool.true_and,
      Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;> decide +kernel
  all_goals cases aligned <;> cases b <;> cases c <;>
    simp only [Blocks.blocks, Blocks.body, Blocks.head, Blocks.fullBody, Blocks.smallMin, Blocks.skip4, Blocks.smallPart, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.and_self, Blocks.stitchPart, Blocks.scratchSetup,
      Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.all, GcmImpl.callees, i.decP.spSafe, i.decPS.spSafe, Option.getD_some, v.ctr.spSafe, v.gh.spSafe, Bool.true_and,
      Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;> decide +kernel

theorem encryptBlocks_xdepth :
    (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc)) aligned (encFull st) (encSmall st) (encSmall4 st) (st.map (·.encS))).x86_64Depth ≤ 8 := by
  unfold Blocks.encrypt encFull encSmall encSmall4
  refine StitchImpl.blocks_cases st (·.enc) (·.encS) (·.full) (·.small) (·.small4) aligned _ _ (fun c => c.x86_64Depth ≤ 8) ?_ (fun i b c _ => ?_) (fun i b c _ => ?_)
  · cases aligned <;>
    simp only [Blocks.blocks, Blocks.body, Blocks.head, Blocks.fullBody, Blocks.smallMin, Blocks.skip4, Blocks.smallPart, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.and_self, Blocks.stitchPart, Blocks.scratchSetup,
      Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack, v.gh.noStack, Nat.max_le, Bool.true_and,
      Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;> decide +kernel
  all_goals cases aligned <;> cases b <;> cases c <;>
    simp only [Blocks.blocks, Blocks.body, Blocks.head, Blocks.fullBody, Blocks.smallMin, Blocks.skip4, Blocks.smallPart, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.and_self, Blocks.stitchPart, Blocks.scratchSetup,
      Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.x86_64Depth, GcmImpl.callees, i.encP.xdepth, i.encPS.xdepth, Option.getD_some, v.ctr.noStack, v.gh.noStack, Nat.max_le, Bool.true_and,
      Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;> decide +kernel

theorem decryptBlocks_xdepth :
    (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec)) aligned (decFull st) (decSmall st) (decSmall4 st) (st.map (·.decS))).x86_64Depth ≤ 8 := by
  unfold Blocks.decrypt decFull decSmall decSmall4
  refine StitchImpl.blocks_cases st (·.dec) (·.decS) (·.fullD) (·.smallD) (·.small4) aligned _ _ (fun c => c.x86_64Depth ≤ 8) ?_ (fun i b c _ => ?_) (fun i b c _ => ?_)
  · cases aligned <;>
    simp only [Blocks.blocks, Blocks.body, Blocks.head, Blocks.fullBody, Blocks.smallMin, Blocks.skip4, Blocks.smallPart, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.and_self, Blocks.stitchPart, Blocks.scratchSetup,
      Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack, v.gh.noStack, Nat.max_le, Bool.true_and,
      Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;> decide +kernel
  all_goals cases aligned <;> cases b <;> cases c <;>
    simp only [Blocks.blocks, Blocks.body, Blocks.head, Blocks.fullBody, Blocks.smallMin, Blocks.skip4, Blocks.smallPart, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_and, Bool.and_self, Blocks.stitchPart, Blocks.scratchSetup,
      Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.x86_64Depth, GcmImpl.callees, i.decP.xdepth, i.decPS.xdepth, Option.getD_some, v.ctr.noStack, v.gh.noStack, Nat.max_le, Bool.true_and,
      Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;> decide +kernel

theorem encryptBlocksM_correct (s : State) (hs : (Proof.AesGcm.encryptBlocksX86_64M M).pre s) :
    ∃ t s', Exec isa (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc)) aligned (encFull st) (encSmall st) (encSmall4 st) (st.map (·.encS))) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.encryptBlocksX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := Blocks.encrypt_wp v st hs
  exact ⟨t, s', he, abiPreserved_of_exec (encryptBlocks_mx v st) he hg, hp⟩

theorem decryptBlocksM_correct (s : State) (hs : (Proof.AesGcm.decryptBlocksX86_64M M).pre s) :
    ∃ t s', Exec isa (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec)) aligned (decFull st) (decSmall st) (decSmall4 st) (st.map (·.decS))) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.decryptBlocksX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := Blocks.decrypt_wp v st hs
  exact ⟨t, s', he, abiPreserved_of_exec (decryptBlocks_mx v st) he hg, hp⟩

end

section
variable (v : GcmImpl) (st : Option StitchImpl)

/-! The key context of `vg_aes_gcm_init` (`CtxMode.base`). -/

theorem encryptBlocks_mxB :
    (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc)) false (st.any (·.full))).allInstrs (fun i => !loadsMxcsr i) = true := by
  have h := encryptBlocks_mx v (st.map (·.code CtxMode.base)); rwa [map_code_enc, StitchImpl.encFull_code, StitchImpl.encSmall_code] at h

theorem encryptBlocks_xdepthB :
    (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc)) false (st.any (·.full))).x86_64Depth ≤ 8 := by
  have h := encryptBlocks_xdepth v (st.map (·.code CtxMode.base)); rwa [map_code_enc, StitchImpl.encFull_code, StitchImpl.encSmall_code] at h

theorem decryptBlocks_xdepthB :
    (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec))).x86_64Depth ≤ 8 := by
  have h := decryptBlocks_xdepth v (st.map (·.code CtxMode.base)); rwa [map_code_dec, StitchImpl.decFull_code, StitchImpl.decSmall_code] at h

theorem decryptBlocks_mxB :
    (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec))).allInstrs (fun i => !loadsMxcsr i) = true := by
  have h := decryptBlocks_mx v (st.map (·.code CtxMode.base)); rwa [map_code_dec, StitchImpl.decFull_code, StitchImpl.decSmall_code] at h

theorem encryptBlocks_spSafeB :
    (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc)) false (st.any (·.full))).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h := encryptBlocks_spSafe v (st.map (·.code CtxMode.base)); rwa [map_code_enc, StitchImpl.encFull_code, StitchImpl.encSmall_code] at h

theorem decryptBlocks_spSafeB :
    (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec))).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h := decryptBlocks_spSafe v (st.map (·.code CtxMode.base)); rwa [map_code_dec, StitchImpl.decFull_code, StitchImpl.decSmall_code] at h

end

end VG.Proof.AesGcm.X86_64
