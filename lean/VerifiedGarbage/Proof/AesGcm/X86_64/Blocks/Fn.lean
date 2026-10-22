module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Fin
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Full
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

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
  have hq : q = n s := by have := M.q_le; omega
  subst hq
  exact ⟨⟨M.saved, keep_r hp M.frame⟩, M.data, M.ctr, M.y⟩

/-- With nothing left, `Mid` is the end, when decrypting. -/
theorem decDone_of {q k : Nat} {st : State} (M : Mid s q k (blocksAt s.mem (D s) q) st) (h0 : n s - q = 0) :
    DecDone s st := by
  have hq : q = n s := by have := M.q_le; omega
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
        (fun _ h => okS.1 _ h (Nat.mod_one _))
        (fun _ _ h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP =>
          encDone_of hp (stitchEFull_ok hp h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP) (Nat.sub_self _))
        (fun h16 _ M => WP.seq (WP.mono (rest_ok hp (by omega) M) fun st' M' => tl _ st' M'))
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
      exact fullBody_ok hp (aligned := aligned) (small := smallD) (small4 := small4) (pieceS := some decS) (fun _ h => ok.2 _ h (Nat.mod_one _))
        (fun _ h => okS.2 _ h (Nat.mod_one _))
        (fun _ _ h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP =>
          decDone_of hp (stitchDFull_ok hp h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP) (Nat.sub_self _))
        (fun h16 _ M => WP.seq (WP.mono (rest_ok hp (by omega) M) fun st' M' => tl _ st' M'))
        h11 hg hk hf hrd hwr

end VG.Proof.AesGcm.X86_64.Blocks
