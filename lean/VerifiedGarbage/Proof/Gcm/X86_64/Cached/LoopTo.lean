module

import VerifiedGarbage.Proof.Gcm.X86_64.Cached.AesTo
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZHTo
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Keep
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup

/-! # Cached-key GCM groups with distinct input and output buffers -/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZHTo
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo EPostTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch hk y₀
  dp dR pR cR yR bAddr addr_eq in_sub in_sub_int in_rdwr ite_t ite_f ghash_append16 blockAt_writeW_sep'
  storesK_ok pregs_get blockAt_outP)
open VG.Proof.Gcm.X86_64.StitchZ (GEnv QG gRegs gRegs_ok gq_ok QG.data keepP nextE_ok FinOk ghRun_ok ghFin
  store16Z_ok State.zlane_setV256 paddd_two_two lane0_zlane lane1_zlane shuf44_0 shuf44_1 shuf44_2 shuf44_3)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY storesK pregs)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Impl.Gcm.X86_64.StitchZ (gq setupZ lastG)
open VG.Impl.Gcm.X86_64.StitchZHTo (firstTo bodyTo)
open VG.Proof.Gcm.X86_64.StitchZTo hiding batchTo_ok bodyTo_ok firstTo_ok
open VG.Proof.Gcm.X86_64.StitchZH (gq_keeps)
open VG.Proof.Gcm.X86_64.Vpclmul (getLsbD_one8)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Proof.Aes.X86_64.VaesZ (four)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

theorem bodyTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {e : Nat} (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInvTo s₀ P e s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa bodyTo s fun s' => EInvTo s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' :=
  WP.mono (StitchZH.bodyM_ok hp.toM hf he (hI.toM hp) hCache) fun _ ⟨h, hc, hk⟩ => ⟨h.toTo, hc, hk⟩

theorem firstTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} {s : State}
    (hR : ReadyTo s₀ P s) (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) : WP isa firstTo s fun t => EInvTo s₀ P 1 t ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) t :=
  WP.mono (StitchZH.firstM_ok hp.toM hp.nb16 (hR.toM hp) hCache) fun _ ⟨h, hk⟩ => ⟨h.toTo, hk⟩

end VG.Proof.Gcm.X86_64.StitchZHTo
