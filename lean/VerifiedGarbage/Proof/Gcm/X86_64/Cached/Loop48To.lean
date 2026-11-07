module

import VerifiedGarbage.Proof.Gcm.X86_64.Cached.LoopTo
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop48
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop48
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZHTo
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.AesTo
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Keep
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Pow

/-! # Cached-key GCM: the 48-block loops and their tails -/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZHTo
open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Stitch (storeCtr storeY)
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo EPostTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch hk y₀
  dp dR pR cR yR bAddr addr_eq in_sub in_sub_int in_rdwr ite_t ite_f ghash_append16)
open VG.Proof.Gcm.X86_64.StitchZ (GEnv GEnv48 QG48 gRegs48 gRegs48_ok gq48_ok QG48.data QG48.next keepW T48
  FinOk FinOk48 ghRun_ok ghFin adv_ok next48_ok cmp_ok reload_ok ghash_append48 pw16 pow48_ok)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZ (gq48 pow48 lastG adv tab)
open VG.Impl.Gcm.X86_64.StitchZHTo (batchTo bodyTo body48To bigRestTo firstTo)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

open VG.Proof.Gcm.X86_64.StitchZTo hiding batchTo_ok bodyTo_ok firstTo_ok bigRestTo_ok encTailGTo_ok
open VG.Proof.Gcm.X86_64.StitchZH (gq48_keeps)

theorem bigRestTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {T : Nat → Nat → Nat → Block} (hT : FinOk48 (hk s₀) T) (hT2 : ∀ k l, T 2 k l = P k l)
    (h96 : 96 ≤ nb s₀) {s s₁ : State} (hI : EInvTo s₀ P 1 s) (hA₁ : AInvTo s₀ (16 * 1) s₁)
    (hv₁ : ∀ g < 3, ∀ k < 4, ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l)
    (hm₁ : ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) (hg₁ : s₁.gpr = s.gpr)
    (hl₁ : ∀ l < 4, s₁.zlane .xmm2 l = s.zlane .xmm2 l)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s₁) :
    WP isa bigRestTo s₁ fun s' => ∃ e, EInvTo s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' :=
  WP.mono (StitchZH.bigRestM_ok hp.toM hf hT hT2 h96 (hI.toM hp) (hA₁.toM hp) hv₁ hm₁ hg₁ hl₁ hCache)
    fun _ ⟨e, h, hk⟩ => ⟨e, h.toTo, hk⟩

/-- The loop of one group, for any number of blocks: it stops with fewer than
32 blocks from the last group still to hash. -/
theorem loopERTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {e : Nat} {s : State} (hI : EInvTo s₀ P e s) (hcf : s.cf = some (decide (nb s₀ - 16 * (e - 1) < 32)))
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.ite .b (.block []) (.loop bodyTo .ae)) s fun s' => ∃ e, nb s₀ - 16 * (e - 1) < 32 ∧
      EInvTo s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' :=
  WP.mono (StitchZH.loopERM_ok hp.toM hf (hI.toM hp) hcf hCache) fun _ ⟨e, he, h, hk⟩ => ⟨e, he, h.toTo, hk⟩

end VG.Proof.Gcm.X86_64.StitchZHTo
