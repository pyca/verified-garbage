module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Top
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Top
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
public import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
import VerifiedGarbage.Impl.MlKem.X86_64.Frag
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Sq
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
meta import VerifiedGarbage.Impl.MlKem.X86_64.Frag
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Pro
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Sq
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
meta import VerifiedGarbage.Proof.MlKem.X86_64.Zero
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4_avx2`, constant time but for the seeds

Two runs whose seeds (the declared leak) and pointers agree leak the same. The
code but for the loops of the halves is proven by the taint analysis, from the
pointers (the prologue, the absorption and the first squeeze as in
`vg_mlkem_sample_ntt4_avx2`, `S4.start_ct`). Both runs read the same XOF
output, so in each half's loop they are at the same iteration with the same
coefficients sampled, and each iteration runs as in `vg_mldsa_rej_ntt_poly`
(`RejNttCT.body_ct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample (rnBody)
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (sample4K relInv taintRel relStart Rel2 ofNat64_pred ofNat64_beq_zero RelCT.postDep)
open VG.Proof.MlKem.X86_64.S4 (R4 Pre aP at' pre_of pub_scr pub_aP pub_B env_rbx start_ct)
open VG.Proof.MlDsa.X86_64.Sample (nil_regs WP.all')
open VG.Proof.MlDsa.X86_64.Sample.RejNttCT (BPre BRel body_ct)

theorem pub_Lt4 {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂) {K : Nat} (hK : K < 4) (t : Nat) :
    Lt σ₁ K t = Lt σ₂ K t := by simp only [Lt, Xb, pub_B hq hK]

/-! ## The squeezes -/

/-- Squeezes, from the absorption, given their taint analysis. -/
theorem sqT_ct {fast : Bool} {t b n : Nat} (hn : 0 < n) (hbn : b + n ≤ 3)
    (c : ∃ hc : VG.Taint.Hint X86_64.Taint.T, (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeezes b n fast) hc).isSome = true) :
    RelCT isa (R4 fun σ s => SqT σ t b s) (squeezes b n fast) (R4 fun σ s => SqT σ t (b + n) s) := by
  obtain ⟨_, c⟩ := c
  exact relInv (fun σ s hp h => WP.mono (sqTs_ok (fast := fast) (pre_of hp) hn hbn h) fun _ h' => h'.1)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) c)

/-- The second squeezes, given their taint analysis. -/
theorem sqM_ct {fast : Bool} {b n : Nat} (hn : 0 < n) (hbn : b + n ≤ 3)
    (c : ∃ hc : VG.Taint.Hint X86_64.Taint.T, (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeezes b n fast) hc).isSome = true) :
    RelCT isa (R4 fun σ s => M2 σ b s) (squeezes b n fast) (R4 fun σ s => M2 σ (b + n) s) := by
  obtain ⟨_, c⟩ := c
  exact relInv (fun σ s hp h => sqM_ok (fast := fast) (pre_of hp) hn hbn h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) c)

end VG.Proof.MlDsa.X86_64.Rej4
