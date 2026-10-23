module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.SealPw
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortOpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenSh
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenStore
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenW
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.SealPw
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortOpenCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenStore
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Verified
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Verified
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/-!
# AES-GCM on AArch64, interleaved: `vg_aes_gcm_open_with_powers` and `vg_aes_gcm_open_store_powers`

Untrusted: everything here is checked by Lean. As `Stitch/SealPw.lean`, for
`open` (`Fast/OpenPw.lean`, `Fast/OpenStore.lean`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-! ## `vg_aes_gcm_open_with_powers` -/

/-- `pwTbl 16` writes the table, from the powers in `pw`. -/
theorem pwTbl_forO {s : State} (hs : openPwN s) :
    TbForOP (Impl.AesGcm.AArch64.Stitch.pwTbl 16) (s.gpr .x0) (stackArg s 3) s.sp (s.gpr .x6) (s.gpr .x7).toNat s :=
  fun u he hrd hwr hf => by
    obtain ⟨hP, hsl, k⟩ := gwCallO_of hs (Y := stackArg s 3 + BitVec.ofNat 64 512)
      (S := stackArg s 3 + BitVec.ofNat 64 512) (Lay.wSub (by decide)) (Lay.wSub (by decide)) hrd hwr he.sp hf
    obtain ⟨ol, -, -⟩ := openLay hs.1
    have hH : Spec.Gcm.blockAt u.mem (s.gpr .x0 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem (s.gpr .x0) :=
      blockAt_frame hf fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ol.ctx.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
        · exact ol.cd.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
    rw [← hH]
    exact Stitch.pwTbl_ok (by decide) he hP hsl k.reads k.repr

/-- The table from `pw`, then the rest of `openShortA`, from the registers it reads. -/
theorem pwRestOpenShort_rel {u₁ u₂ : State} (hsp : u₁.sp = u₂.sp)
    (hr : ∀ r ∈ Reg.x5 :: shRegs, u₁.gpr r = u₂.gpr r) :
    RelCT isa (Eq2 u₁ u₂) (.seq (.block pwRest) openRestZ) TT :=
  rel_taint (.x5 :: shRegs) hsp hr ⟨_, by taint_decide⟩

section
variable (v : GcmImpl) (g : GhashWithImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
include hMK gh

theorem openPwS_correctN (s : State) (hs : openPwN s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Stitch.openWithPw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      openAArch64.post s s' :=
  WP.withPreservedV (openWithSh_wp (w := 3) v _ hMK gh (.inr rfl) hs.1
      (fun _ _ _ _ _ hc sY sS hrd hwr hsp hf =>
        have q := gwCallO_of hs sY sS hrd hwr hsp hf
        pwSel_call v g (k := 16) (by decide) q.1 q.2.1 hc q.2.2) (pwTbl_forO hs))
    (stitchOpenWithS_keepsV v (.inr rfl) (pwTbl_keepsV (.inr rfl)) (pwSel_keepsV v g (.inr rfl)))

theorem openPwS_ctN :
    ConstantTime isa openPwN (fun s₁ s₂ => onePub 4 s₁ s₂ ∧ openLeakOf s₁ = openLeakOf s₂)
      (Impl.AesGcm.AArch64.Stitch.openWithPw v.callees g.fn) :=
  openWithSh_ct (w := 3) v _ hMK gh (.inr rfl) (extra := fun s => [pwRO s]) (fun _ h => h.1)
    (fun p hc sY sS hrd hwr hsp hf =>
      have q := gwCallO_of p sY sS hrd hwr hsp hf
      pwSel_call v g (k := 16) (by decide) q.1 q.2.1 hc q.2.2)
    (fun {σ₁ σ₂ s₁ s₂ _ _ _ _} p₁ p₂ hq c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ => by
      obtain ⟨q0, -, -, -, -, -, q6, q7, qsp, qa⟩ := hq
      have e3 : stackArg σ₁ 3 = stackArg σ₂ 3 := qa 3 (by decide)
      have e2 : stackArg σ₁ 2 = stackArg σ₂ 2 := qa 2 (by decide)
      obtain ⟨hP₁, hs₁, k₁⟩ := gwCallO_of p₁ sY sS r₁ w₁ sp₁ f₁
      obtain ⟨hP₂, hs₂, k₂⟩ := gwCallO_of p₂ (by rw [← e3]; exact sY) (by rw [← e3]; exact sS) r₂ w₂
        (sp₂.trans qsp) (by rw [← e3, ← q6, ← q7]; exact f₂)
      rw [← e2] at hP₂ k₂
      rw [← q0] at k₂
      exact pwSel_rel v g (.inr rfl) hP₁ hs₁ hP₂ hs₂ c₁ k₁ c₂ k₂ (sp₁.trans sp₂.symm))
    (fun p => pwTbl_forO p)
    (fun {σ₁ σ₂} p₁ p₂ hq v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂ => by
      obtain ⟨-, -, -, -, -, -, q6, q7, qsp, qa⟩ := hq
      have e3 : stackArg σ₁ 3 = stackArg σ₂ 3 := qa 3 (by decide)
      have e2 : stackArg σ₁ 2 = stackArg σ₂ 2 := qa 2 (by decide)
      obtain ⟨hP₁, hs₁, -⟩ := gwCallO_of p₁ (Y := stackArg σ₁ 3 + BitVec.ofNat 64 512)
        (S := stackArg σ₁ 3 + BitVec.ofNat 64 512) (Lay.wSub (by decide)) (Lay.wSub (by decide)) r₁ w₁ sp₁ f₁
      obtain ⟨hP₂, hs₂, -⟩ := gwCallO_of p₂ (Y := stackArg σ₂ 3 + BitVec.ofNat 64 512)
        (S := stackArg σ₂ 3 + BitVec.ofNat 64 512) (Lay.wSub (by decide)) (Lay.wSub (by decide)) r₂ w₂
        (sp₂.trans qsp) (by rw [← e3, ← q6, ← q7]; exact f₂)
      rw [← e2] at hP₂
      exact pwTbl_rel (.inr rfl) (fun hsp hr => pwRestDec_rel hsp hr) (sp₁.trans sp₂.symm) hr hP₁ hs₁ hP₂ hs₂)
    fun {σ₁ σ₂} p₁ p₂ hq v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂ => by
      obtain ⟨-, -, -, -, -, -, q6, q7, qsp, qa⟩ := hq
      have e3 : stackArg σ₁ 3 = stackArg σ₂ 3 := qa 3 (by decide)
      have e2 : stackArg σ₁ 2 = stackArg σ₂ 2 := qa 2 (by decide)
      obtain ⟨hP₁, hs₁, -⟩ := gwCallO_of p₁ (Y := stackArg σ₁ 3 + BitVec.ofNat 64 512)
        (S := stackArg σ₁ 3 + BitVec.ofNat 64 512) (Lay.wSub (by decide)) (Lay.wSub (by decide)) r₁ w₁ sp₁ f₁
      obtain ⟨hP₂, hs₂, -⟩ := gwCallO_of p₂ (Y := stackArg σ₂ 3 + BitVec.ofNat 64 512)
        (S := stackArg σ₂ 3 + BitVec.ofNat 64 512) (Lay.wSub (by decide)) (Lay.wSub (by decide)) r₂ w₂
        (sp₂.trans qsp) (by rw [← e3, ← q6, ← q7]; exact f₂)
      rw [← e2] at hP₂
      exact pwTbl_relR shRegs (.inr rfl) (fun hsp hr => pwRestOpenShort_rel hsp hr) (sp₁.trans sp₂.symm) hr hP₁ hs₁ hP₂
        hs₂

end

/-! ## On the shared contract's regions -/

section
variable (v : GcmImpl) (g : GhashWithImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
  (gh : Gh8Ok)
include hMK gh

theorem openPwS_correct (s : State) (hs : openPwAArch64.pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Stitch.openWithPw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      openPwAArch64.post s s' := by
  obtain ⟨t, s₁, he, ha, hp⟩ := openPwS_correctN v g hMK gh _ (narrowPO_pre hs)
  exact ⟨t, _, narrowPO_exec hs he, ha, hp⟩

theorem openPwS_ct :
    ConstantTime isa openPwAArch64.pre openPwAArch64.pub (Impl.AesGcm.AArch64.Stitch.openWithPw v.callees g.fn) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨u₁, r₁, f₁, -⟩ := openPwS_correctN v g hMK gh _ (narrowPO_pre h₁)
  obtain ⟨u₂, r₂, f₂, -⟩ := openPwS_correctN v g hMK gh _ (narrowPO_pre h₂)
  rw [(Exec.det e₁ (narrowPO_exec h₁ f₁)).1, (Exec.det e₂ (narrowPO_exec h₂ f₂)).1]
  exact openPwS_ctN v g hMK gh _ _ _ _ _ _ (narrowPO_pre h₁) (narrowPO_pre h₂) hq f₁ f₂

theorem openPwS_verified :
    Verified AArch64.target (Impl.AesGcm.AArch64.Stitch.openWithPw v.callees g.fn)
      (Proof.AesGcm.openWithPowersScratchContract AArch64.abi) :=
  Verified.of_correct (openPwS_correct v g hMK gh) (openPwS_ct v g hMK gh)
    { pre := by
        sig_implies_pre [Proof.AesGcm.openWithPowersScratchContract, Proof.AesGcm.openWithPowersScratchSig,
          Spec.Gcm.openWithPowersPre, Spec.Gcm.openPre, Spec.Gcm.openWithPowersPost, Spec.Gcm.openPost,
          Spec.Gcm.openWithPowersLeak, Spec.Gcm.openLeak, openPwAArch64, openPwW, pwRO, openAArch64, onePub,
          openRes, openLeakOf, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
          List.getD, List.range, List.range.loop]
      post := by
        sig_implies_post [Proof.AesGcm.openWithPowersScratchContract, Proof.AesGcm.openWithPowersScratchSig,
          Spec.Gcm.openWithPowersPre, Spec.Gcm.openPre, Spec.Gcm.openWithPowersPost, Spec.Gcm.openPost,
          Spec.Gcm.openWithPowersLeak, Spec.Gcm.openLeak, openPwAArch64, openPwW, pwRO, openAArch64, onePub,
          openRes, openLeakOf, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
          List.getD, List.range, List.range.loop]
      pub := by
        sig_implies_pub [Proof.AesGcm.openWithPowersScratchContract, Proof.AesGcm.openWithPowersScratchSig,
          Spec.Gcm.openWithPowersPre, Spec.Gcm.openPre, Spec.Gcm.openWithPowersPost, Spec.Gcm.openPost,
          Spec.Gcm.openWithPowersLeak, Spec.Gcm.openLeak, openPwAArch64, openPwW, pwRO, openAArch64, onePub,
          openRes, openLeakOf, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
          List.getD, List.range, List.range.loop]
      sat := ⟨openSatPw, by
        sig_pre [Proof.AesGcm.openWithPowersScratchContract, Proof.AesGcm.openWithPowersScratchSig,
          Spec.Gcm.openWithPowersPre, Spec.Gcm.openPre, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop, openSatPw, openSat,
          stackArg, stackArgAddr, Mem.readW, Mem.read]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact Proof.AesGcm.powers8Repr_of_zeroMem (by decide) openSatPw_zero⟩ }

end

theorem openPwS_framed (v : GcmImpl) (g : GhashWithImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 3 (Impl.AesGcm.AArch64.Stitch.openWithPw v.callees g.fn))
      (Spec.Gcm.openWithPowersContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Gcm.openWithPowersSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openWithPowersPre AArch64.abi.ptrBits)
    (post := Spec.Gcm.openWithPowersPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (leak := some (Spec.Gcm.openWithPowersLeak AArch64.abi.ptrBits))
    (openPwS_verified v g hMK gh) (by decide) (by decide) (Proof.AesGcm.openWithPowersPre_local _)
    (Proof.AesGcm.openWithPowersPost_local _) openFrameSatPw_pre
    (hleak := Proof.AesGcm.openWithPowersLeak_local _)

/-! ## `vg_aes_gcm_open_store_powers` -/

section
variable (v : GcmImpl) (g : GhashStoreImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
  (hP : Proof.Gcm.AArch64.Pmull.PrepPow) (gh : Gh8Ok)
include hMK hP gh

theorem openStS_correctN (s : State) (hs : openStN s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Stitch.openStorePw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      openStAArch64.post s s' := by
  have hs' := hs
  obtain ⟨hpx, pd, pw, pc, h16, h12, htl⟩ := hs'
  exact WP.withPreservedV (WP.mono (openWithSX_wp (w := 3) v _ hMK gh (.inr rfl) (ex := [pwRO s]) hpx ⟨h16, h12⟩ htl
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact pw.symm)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact pd.symm)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact pc.symm)
      (fun hi hf => powers_keepO hs hi hf)
      (fun s' _ _ _ _ hc sY sS hrd hwr hsp hf hd =>
        have q := gsCallO_of hs sY sS hrd hwr hsp hf hd
        WP.mono (pwS_call g (k := 16) (by decide) q.1 q.2.1 hc q.2.2.1) fun _ ⟨gp, pp⟩ =>
          ⟨gp, by rw [← q.2.2.2]; exact pp⟩) (powTbl_forO hP _ _ _ _ _ s)) fun _ ⟨⟨ga, p⟩, q⟩ => ⟨ga, p, q⟩)
    (stitchOpenWithS_keepsV v (.inr rfl) powTbl_keepsV (pwCallS16_keepsV g))

theorem openStS_ctN :
    ConstantTime isa openStN (fun s₁ s₂ => onePub 4 s₁ s₂ ∧ openLeakOf s₁ = openLeakOf s₂)
      (Impl.AesGcm.AArch64.Stitch.openStorePw v.callees g.fn) :=
  openWithSX_ct (w := 3) v _ hMK gh (.inr rfl) (extra := fun _ => []) (extraW := fun s => [pwRO s])
    (ex := fun s => [pwRO s]) (fun _ h => h.1)
    (fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2.2.1.symm)
    (fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2.1.symm)
    (fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2.2.2.1.symm)
    (fun hq => by obtain ⟨-, -, -, -, -, -, -, -, -, qa⟩ := hq; simp only [pwRO, qa 2 (by decide)])
    (fun p hc sY sS hrd hwr hsp hf hd =>
      have q := gsCallO_of p sY sS hrd hwr hsp hf hd
      WP.mono (pwS_call g (k := 16) (by decide) q.1 q.2.1 hc q.2.2.1) fun _ q' => q'.1)
    (fun {σ₁ σ₂ s₁ s₂ _ _ _ _} p₁ p₂ hq c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd => by
      obtain ⟨q0, -, -, -, -, -, q6, q7, qsp, qa⟩ := hq
      have e3 : stackArg σ₁ 3 = stackArg σ₂ 3 := qa 3 (by decide)
      have e2 : stackArg σ₁ 2 = stackArg σ₂ 2 := qa 2 (by decide)
      obtain ⟨hP₁, hs₁, k₁, -⟩ := gsCallO_of p₁ sY sS r₁ w₁ sp₁ f₁ hd
      obtain ⟨hP₂, hs₂, k₂, -⟩ := gsCallO_of p₂ (by rw [← e3]; exact sY) (by rw [← e3]; exact sS) r₂ w₂
        (sp₂.trans qsp) (by rw [← e3, ← q6, ← q7]; exact f₂) (by rw [← q6, ← q7]; exact hd)
      rw [← e2] at hP₂ k₂
      rw [← q0] at k₂
      exact pwS_rel g (.inr rfl) hP₁ hs₁ hP₂ hs₂ c₁ k₁ c₂ k₂ (sp₁.trans sp₂.symm))
    (fun {σ} _ => powTbl_forO hP _ _ _ _ _ σ)
    fun _ _ _ _ _ sp₁ sp₂ hr _ _ _ _ _ _ => powTblDec_rel (sp₁.trans sp₂.symm) hr

end

section
variable (v : GcmImpl) (g : GhashStoreImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
  (hP : Proof.Gcm.AArch64.Pmull.PrepPow) (gh : Gh8Ok)
include hMK hP gh

theorem openStS_correct (s : State) (hs : openStAArch64.pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Stitch.openStorePw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      openStAArch64.post s s' := by
  obtain ⟨t, s₁, he, ha, hp⟩ := openStS_correctN v g hMK hP gh _ (narrowSO_pre hs)
  exact ⟨t, _, narrowSO_exec hs he, ha, hp⟩

theorem openStS_ct :
    ConstantTime isa openStAArch64.pre openStAArch64.pub (Impl.AesGcm.AArch64.Stitch.openStorePw v.callees g.fn) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨u₁, r₁, f₁, -⟩ := openStS_correctN v g hMK hP gh _ (narrowSO_pre h₁)
  obtain ⟨u₂, r₂, f₂, -⟩ := openStS_correctN v g hMK hP gh _ (narrowSO_pre h₂)
  rw [(Exec.det e₁ (narrowSO_exec h₁ f₁)).1, (Exec.det e₂ (narrowSO_exec h₂ f₂)).1]
  exact openStS_ctN v g hMK hP gh _ _ _ _ _ _ (narrowSO_pre h₁) (narrowSO_pre h₂) hq f₁ f₂

theorem openStS_verified :
    Verified AArch64.target (Impl.AesGcm.AArch64.Stitch.openStorePw v.callees g.fn)
      (Proof.AesGcm.openStorePowersScratchContract AArch64.abi) :=
  Verified.of_correct (openStS_correct v g hMK hP gh) (openStS_ct v g hMK hP gh)
    { pre := by
        sig_implies_pre [Proof.AesGcm.openStorePowersScratchContract, Proof.AesGcm.openStorePowersScratchSig,
          Proof.AesGcm.openStorePowersPreP, Spec.Gcm.openPre, Spec.Gcm.storePowersOk,
          Spec.Gcm.openStorePowersPost, Spec.Gcm.openPost, Proof.AesGcm.openStorePowersLeakP, Spec.Gcm.openLeak,
          openStAArch64, openStW, pwRO, openAArch64, onePub, openRes, openLeakOf, args, rounds, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        intro s s' _ h
        sig_post [Proof.AesGcm.openStorePowersScratchContract, Proof.AesGcm.openStorePowersScratchSig,
          Proof.AesGcm.openStorePowersPreP, Spec.Gcm.openPre, Spec.Gcm.storePowersOk,
          Spec.Gcm.openStorePowersPost, Spec.Gcm.openPost, Proof.AesGcm.openStorePowersLeakP, Spec.Gcm.openLeak,
          openStAArch64, openStW, pwRO, openAArch64, onePub, openRes, openLeakOf, args, rounds, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
        sig_reduce [openStAArch64, openAArch64, openRes, AArch64.stackArg, AArch64.stackArgAddr] at h
        sig_simp [openStAArch64, openAArch64, openRes, AArch64.stackArg, AArch64.stackArgAddr] [] at h
        exact ⟨fun _ => h.1, h.2⟩
      pub := by
        sig_implies_pub [Proof.AesGcm.openStorePowersScratchContract, Proof.AesGcm.openStorePowersScratchSig,
          Proof.AesGcm.openStorePowersPreP, Spec.Gcm.openPre, Spec.Gcm.storePowersOk,
          Spec.Gcm.openStorePowersPost, Spec.Gcm.openPost, Proof.AesGcm.openStorePowersLeakP, Spec.Gcm.openLeak,
          openStAArch64, openStW, pwRO, openAArch64, onePub, openRes, openLeakOf, args, rounds, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      sat := ⟨openSatSt, by
        sig_pre [Proof.AesGcm.openStorePowersScratchContract, Proof.AesGcm.openStorePowersScratchSig,
          Proof.AesGcm.openStorePowersPreP, Spec.Gcm.openPre, Spec.Gcm.storePowersOk, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop,
          openSatSt, openSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)⟩ }

end

theorem openStS_framed (v : GcmImpl) (g : GhashStoreImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
    (hP : Proof.Gcm.AArch64.Pmull.PrepPow) (gh : Gh8Ok) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 3 (Impl.AesGcm.AArch64.Stitch.openStorePw v.callees g.fn))
      (Spec.Gcm.openStorePowersContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Gcm.openStorePowersSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.AesGcm.openStorePowersPreP AArch64.abi.ptrBits)
    (post := Spec.Gcm.openStorePowersPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (leak := some (Proof.AesGcm.openStorePowersLeakP AArch64.abi.ptrBits))
    (openStS_verified v g hMK hP gh) (by decide) (by decide) (Proof.AesGcm.openStorePowersPre_local _)
    (Proof.AesGcm.openStorePowersPost_local _) openFrameSatSt_pre
    (hleak := Proof.AesGcm.openStorePowersLeak_local _)

end VG.Proof.AesGcm.AArch64.Fast
