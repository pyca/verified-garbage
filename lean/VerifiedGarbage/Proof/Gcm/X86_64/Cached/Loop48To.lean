module

import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop48
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop48
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZHTo
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Pow
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
public import VerifiedGarbage.Proof.Framework.X86_64.HighKeep
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Gcm.X86_64.Cached.LoopTo`, which this module and modules that import it used -/

section

/-! ### `Gcm.X86_64.Cached.AesTo`, which this module and modules that import it used -/

section

/-! # A cached-key GCM batch from one buffer to another -/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZHTo
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch dp dR pR
  cR yR bAddr addr_eq in_sub sch_frame)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZHTo (batchTo)
open VG.Proof.Gcm.X86_64.StitchZTo hiding batchTo_ok
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok four ZFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)

theorem batchTo_keeps (j : Nat) (g : Nat → List Instr)
    (hg : ∀ j, (g j).all Instr.keepsH = true) : (batchTo j g).all Instr.keepsH = true :=
  StitchZH.batch_keeps j g hg false true

theorem batchTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ ZFrame G s s')
    (hq : ∀ j s s', Q j s → ZFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, s'.zlane r l = s.zlane r l) →
      Frame [⟨oAddr s₀ c, 256⟩] s.mem s'.mem → Q 10 s')
    (hc : c + 16 ≤ nb s₀) {s : State} (hI : AInvTo s₀ c s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s)
    (hgh : ∀ j, (g j).all Instr.keepsH = true)
    (hrdx : (s.gpr .rdx).toNat + 64 * j = (op s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batchTo j g) s fun s' => AInvTo s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨oAddr s₀ c, 256⟩] s.mem s'.mem ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' :=
  WP.mono (StitchZH.batchM_ok (ix := true) (ld := true) hp.toM rfl (fun _ => rfl) g G hG Q hg hq hqx hc (hI.toM hp) hCache hgh
    (fun _ => hI.r8) hrdx hQ) fun _ ⟨hA, h⟩ => ⟨hA.toTo h.2.1 hI.r8, h⟩

end VG.Proof.Gcm.X86_64.StitchZHTo

end

end

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

end

end

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
