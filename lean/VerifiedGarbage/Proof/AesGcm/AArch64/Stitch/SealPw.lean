module

import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.SealStore
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.CT
import VerifiedGarbage.Proof.RsaPss.AArch64.RelSplit
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Verified
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.SealStore
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.CT
meta import VerifiedGarbage.Proof.RsaPss.AArch64.RelSplit
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/-!
# AES-GCM on AArch64, interleaved: `vg_aes_gcm_seal_with_powers` and `vg_aes_gcm_seal_store_powers`

Untrusted: everything here is checked by Lean. As `Fast/SealPw.lean` and
`Fast/SealStore.lean`, for the code with the interleaved path for TLS
records: `with_powers` writes the table of keys from the powers in `pw`
(`pwTbl`, `pwTbl_for`), whose pointer, loaded from the stack, is public
(`pwTbl_rel`); `store_powers` computes them from `H'`, as `seal` does
(`powTbl`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.Taint VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-! ## The table from `pw` -/

/-- What follows `pwTbl`'s load of `pw`: the powers loaded and the table written. -/
abbrev pwRest : List Instr :=
  (List.range 8).flatMap (fun k => Impl.Gcm.AArch64.Pmull.loadPw (k + 1)) ++ Impl.AesGcm.AArch64.Stitch.tbl

theorem pwRestEnc_rel {u₁ u₂ : State} (hsp : u₁.sp = u₂.sp) (hr : ∀ r ∈ Reg.x5 :: stRegs, u₁.gpr r = u₂.gpr r) :
    RelCT isa (Eq2 u₁ u₂) (.seq (.block pwRest) Impl.Gcm.AArch64.Stitch.enc) TT :=
  rel_taint (.x5 :: stRegs) hsp hr ⟨_, by taint_decide⟩

theorem pwRestDec_rel {u₁ u₂ : State} (hsp : u₁.sp = u₂.sp) (hr : ∀ r ∈ Reg.x5 :: stRegs, u₁.gpr r = u₂.gpr r) :
    RelCT isa (Eq2 u₁ u₂) (.seq (.block pwRest) Impl.Gcm.AArch64.Stitch.dec) TT :=
  rel_taint (.x5 :: stRegs) hsp hr ⟨_, by taint_decide⟩

/-- `pwTbl k` then `l`, in two runs that agree on the arguments and find the
same `pw` at `[sp + k]`. -/
theorem pwTbl_rel {k : Nat} (hk : k = 8 ∨ k = 16) {l : Prog isa}
    (hl : ∀ {u₁ u₂ : State}, u₁.sp = u₂.sp → (∀ r ∈ Reg.x5 :: stRegs, u₁.gpr r = u₂.gpr r) →
      RelCT isa (Eq2 u₁ u₂) (.seq (.block pwRest) l) TT)
    {v₁ v₂ : State} (hsp : v₁.sp = v₂.sp) (hr : ∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) {P : Addr}
    (hP₁ : v₁.mem.readW (v₁.sp + BitVec.ofNat 64 k) 64 = P) (hsl₁ : InRegions (v₁.rd ++ v₁.wr) (v₁.sp + BitVec.ofNat 64 k) 8)
    (hP₂ : v₂.mem.readW (v₂.sp + BitVec.ofNat 64 k) 64 = P) (hsl₂ : InRegions (v₂.rd ++ v₂.wr) (v₂.sp + BitVec.ofNat 64 k) 8) :
    RelCT isa (Eq2 v₁ v₂) (.seq (.block (Impl.AesGcm.AArch64.Stitch.pwTbl k)) l) TT := by
  have hk' : k % 8 = 0 ∧ k < 32768 := by rcases hk with rfl | rfl <;> decide
  have t : ∃ h, (taint.check (Taint.ofRegs []) (.block [.ldrSp .x5 k]) h).isSome = true := by
    rcases hk with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  unfold Impl.AesGcm.AArch64.Stitch.pwTbl
  rw [List.append_assoc]
  refine RelCT.seq_block_append ?_
  obtain ⟨s₁, run₁, x5₁, g₁, sp₁, -, -, -⟩ := ldrSp_ok (t := .x5) hk' hP₁ hsl₁
  obtain ⟨s₂, run₂, x5₂, g₂, sp₂, -, -, -⟩ := ldrSp_ok (t := .x5) hk' hP₂ hsl₂
  refine rel_seq (rel_taint [] hsp (by agree_tac []) t) (F₁ := fun u => u = s₁) (F₂ := fun u => u = s₂)
    (WP.of_runBlock ⟨s₁, run₁, rfl⟩) (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun _ _ e₁ e₂ => ?_
  subst e₁ e₂
  refine hl (by rw [sp₁, sp₂, hsp]) fun r hr' => ?_
  by_cases h5 : r = .x5
  · subst h5; rw [x5₁, x5₂]
  · rw [g₁ r h5, g₂ r h5]; exact hr r ((List.mem_cons.mp hr').resolve_left h5)

/-! ## `vg_aes_gcm_seal_with_powers` -/

/-- `pwTbl 8` writes the table, from the powers in `pw`. -/
theorem pwTbl_for {s : State} (hs : sealPwN s) : TbFor (Impl.AesGcm.AArch64.Stitch.pwTbl 8) 2 s :=
  fun u he hrd hwr hf _ => by
    obtain ⟨hP, hsl, k⟩ := gwCall_of hs (Y := stackArg s 2 + BitVec.ofNat 64 512)
      (S := stackArg s 2 + BitVec.ofNat 64 512) (Lay.wSub (by decide)) (Lay.wSub (by decide)) hrd hwr he.sp hf
    obtain ⟨ol, -, -, -⟩ := sealLay hs.1
    have hH : Spec.Gcm.blockAt u.mem (s.gpr .x0 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem (s.gpr .x0) :=
      blockAt_frame hf fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ol.ctx.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
        · exact ol.cd.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
    rw [← hH]
    exact Stitch.pwTbl_ok (by decide) he hP hsl k.reads k.repr

section
variable (v : GcmImpl) (g : GhashWithImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
include hMK gh

theorem sealPwS_correctN (s : State) (hs : sealPwN s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Stitch.sealWithPw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      sealAArch64.post s s' :=
  WP.withPreservedV (sealWithS_wp (w := 2) v _ hMK gh (.inr rfl) hs.1
      (fun _ _ _ _ _ hc sY sS hrd hwr hsp hf =>
        have q := gwCall_of hs sY sS hrd hwr hsp hf
        pw_call g (k := 8) (by decide) q.1 q.2.1 hc q.2.2) (pwTbl_for hs))
    (stitchSealWithS_keepsV v (.inr rfl) (pwTbl_keepsV (.inl rfl)) (pwCall_keepsV g))

theorem sealPwS_ctN :
    ConstantTime isa sealPwN (onePub 3) (Impl.AesGcm.AArch64.Stitch.sealWithPw v.callees g.fn) :=
  sealWithS_ct (w := 2) v _ hMK gh (.inr rfl) (extra := fun s => [pwR s]) (fun _ h => h.1)
    (fun p hc sY sS hrd hwr hsp hf =>
      have q := gwCall_of p sY sS hrd hwr hsp hf
      pw_call g (k := 8) (by decide) q.1 q.2.1 hc q.2.2)
    (fun {σ₁ σ₂ s₁ s₂ _ _ _ _} p₁ p₂ hq c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ => by
      obtain ⟨q0, -, -, -, -, -, q6, q7, qsp, qa⟩ := hq
      have e2 : stackArg σ₁ 2 = stackArg σ₂ 2 := qa 2 (by decide)
      have e1 : stackArg σ₁ 1 = stackArg σ₂ 1 := qa 1 (by decide)
      obtain ⟨hP₁, hs₁, k₁⟩ := gwCall_of p₁ sY sS r₁ w₁ sp₁ f₁
      obtain ⟨hP₂, hs₂, k₂⟩ := gwCall_of p₂ (by rw [← e2]; exact sY) (by rw [← e2]; exact sS) r₂ w₂
        (sp₂.trans qsp) (by rw [← e2, ← q6, ← q7]; exact f₂)
      rw [← e1] at hP₂ k₂
      rw [← q0] at k₂
      exact pw_rel g (.inl rfl) hP₁ hs₁ hP₂ hs₂ c₁ k₁ c₂ k₂ (sp₁.trans sp₂.symm))
    (fun p => pwTbl_for p)
    fun {σ₁ σ₂} p₁ p₂ hq v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂ => by
      obtain ⟨-, -, -, -, -, -, q6, q7, qsp, qa⟩ := hq
      have e2 : stackArg σ₁ 2 = stackArg σ₂ 2 := qa 2 (by decide)
      have e1 : stackArg σ₁ 1 = stackArg σ₂ 1 := qa 1 (by decide)
      obtain ⟨hP₁, hs₁, -⟩ := gwCall_of p₁ (Y := stackArg σ₁ 2 + BitVec.ofNat 64 512)
        (S := stackArg σ₁ 2 + BitVec.ofNat 64 512) (Lay.wSub (by decide)) (Lay.wSub (by decide)) r₁ w₁ sp₁ f₁
      obtain ⟨hP₂, hs₂, -⟩ := gwCall_of p₂ (Y := stackArg σ₂ 2 + BitVec.ofNat 64 512)
        (S := stackArg σ₂ 2 + BitVec.ofNat 64 512) (Lay.wSub (by decide)) (Lay.wSub (by decide)) r₂ w₂
        (sp₂.trans qsp) (by rw [← e2, ← q6, ← q7]; exact f₂)
      rw [← e1] at hP₂
      exact pwTbl_rel (.inl rfl) (fun hsp hr => pwRestEnc_rel hsp hr) (sp₁.trans sp₂.symm) hr hP₁ hs₁ hP₂ hs₂

end

/-! ## On the shared contract's regions -/

section
variable (v : GcmImpl) (g : GhashWithImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
  (gh : Gh8Ok)
include hMK gh

theorem sealPwS_correct (s : State) (hs : sealPwAArch64.pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Stitch.sealWithPw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      sealPwAArch64.post s s' := by
  obtain ⟨t, s₁, he, ha, hp⟩ := sealPwS_correctN v g hMK gh _ (narrowP_pre hs)
  exact ⟨t, _, narrowP_exec hs he, ha, hp⟩

theorem sealPwS_ct :
    ConstantTime isa sealPwAArch64.pre sealPwAArch64.pub (Impl.AesGcm.AArch64.Stitch.sealWithPw v.callees g.fn) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨u₁, r₁, f₁, -⟩ := sealPwS_correctN v g hMK gh _ (narrowP_pre h₁)
  obtain ⟨u₂, r₂, f₂, -⟩ := sealPwS_correctN v g hMK gh _ (narrowP_pre h₂)
  rw [(Exec.det e₁ (narrowP_exec h₁ f₁)).1, (Exec.det e₂ (narrowP_exec h₂ f₂)).1]
  exact sealPwS_ctN v g hMK gh _ _ _ _ _ _ (narrowP_pre h₁) (narrowP_pre h₂) hq f₁ f₂

theorem sealPwS_verified :
    Verified AArch64.target (Impl.AesGcm.AArch64.Stitch.sealWithPw v.callees g.fn)
      (Proof.AesGcm.sealWithPowersScratchContract AArch64.abi) :=
  Verified.of_correct (sealPwS_correct v g hMK gh) (sealPwS_ct v g hMK gh)
    { pre := by
        sig_implies_pre [Proof.AesGcm.sealWithPowersScratchContract, Proof.AesGcm.sealWithPowersScratchSig,
          Spec.Gcm.sealWithPowersPre, Spec.Gcm.sealPre, Spec.Gcm.sealWithPowersPost, Spec.Gcm.sealPost,
          sealPwAArch64, sealPwW, pwR, sealAArch64, onePub, args, rounds, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        sig_implies_post [Proof.AesGcm.sealWithPowersScratchContract, Proof.AesGcm.sealWithPowersScratchSig,
          Spec.Gcm.sealWithPowersPre, Spec.Gcm.sealPre, Spec.Gcm.sealWithPowersPost, Spec.Gcm.sealPost,
          sealPwAArch64, sealPwW, pwR, sealAArch64, onePub, args, rounds, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      pub := by
        sig_implies_pub [Proof.AesGcm.sealWithPowersScratchContract, Proof.AesGcm.sealWithPowersScratchSig,
          Spec.Gcm.sealWithPowersPre, Spec.Gcm.sealPre, Spec.Gcm.sealWithPowersPost, Spec.Gcm.sealPost,
          sealPwAArch64, sealPwW, pwR, sealAArch64, onePub, args, rounds, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      sat := ⟨sealSatPw, by
        sig_pre [Proof.AesGcm.sealWithPowersScratchContract, Proof.AesGcm.sealWithPowersScratchSig,
          Spec.Gcm.sealWithPowersPre, Spec.Gcm.sealPre, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop, sealSatPw, sealSat,
          stackArg, stackArgAddr, Mem.readW, Mem.read]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact Proof.AesGcm.powers8Repr_of_zeroMem (by decide) sealSatPw_zero⟩ }

end

theorem sealPwS_framed (v : GcmImpl) (g : GhashWithImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (Impl.AesGcm.AArch64.Stitch.sealWithPw v.callees g.fn))
      (Spec.Gcm.sealWithPowersContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Gcm.sealWithPowersSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.sealWithPowersPre AArch64.abi.ptrBits)
    (post := Spec.Gcm.sealWithPowersPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (sealPwS_verified v g hMK gh) (by decide) (by decide) (Proof.AesGcm.sealWithPowersPre_local _)
    (Proof.AesGcm.sealWithPowersPost_local _) sealFrameSatPw_pre

/-! ## `vg_aes_gcm_seal_store_powers` -/

section
variable (v : GcmImpl) (g : GhashStoreImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
  (hP : Proof.Gcm.AArch64.Pmull.PrepPow) (gh : Gh8Ok)
include hMK hP gh

theorem sealStS_correctN (s : State) (hs : sealStN s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Stitch.sealStorePw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      sealStAArch64.post s s' := by
  have hs' := hs
  obtain ⟨hpx, pd, pw, pc, -, h16, h12⟩ := hs'
  exact WP.withPreservedV (WP.mono (sealWithSX_wp (w := 2) v _ hMK gh (.inr rfl) (ex := [pwR s]) hpx ⟨h16, h12⟩
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact pw.symm)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact pd.symm)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact pc.symm)
    (fun hi hf => powers_keep hs hi hf)
    (fun s' _ _ _ _ hc sY sS hrd hwr hsp hf hd =>
      have q := gsCall_of hs sY sS hrd hwr hsp hf hd
      WP.mono (pwS_call g (k := 8) (by decide) q.1 q.2.1 hc q.2.2.1) fun _ ⟨gp, pp⟩ =>
        ⟨gp, by rw [← q.2.2.2]; exact pp⟩) (powTbl_for hP 2 s)) fun _ ⟨⟨ga, p⟩, q⟩ => ⟨ga, p, q⟩)
    (stitchSealWithS_keepsV v (.inr rfl) powTbl_keepsV (pwCallS_keepsV g))

theorem sealStS_ctN :
    ConstantTime isa sealStN (onePub 3) (Impl.AesGcm.AArch64.Stitch.sealStorePw v.callees g.fn) :=
  sealWithSX_ct (w := 2) v _ hMK gh (.inr rfl) (extra := fun _ => []) (extraW := fun s => [pwR s])
    (ex := fun s => [pwR s]) (fun _ h => h.1)
    (fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2.2.1.symm)
    (fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2.2.2.1.symm)
    (fun hq => by obtain ⟨-, -, -, -, -, -, -, -, -, qa⟩ := hq; simp only [pwR, qa 1 (by decide)])
    (fun p hc sY sS hrd hwr hsp hf hd =>
      have q := gsCall_of p sY sS hrd hwr hsp hf hd
      WP.mono (pwS_call g (k := 8) (by decide) q.1 q.2.1 hc q.2.2.1) fun _ q' => q'.1)
    (fun {σ₁ σ₂ s₁ s₂ _ _ _ _} p₁ p₂ hq c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd => by
      obtain ⟨q0, -, -, -, -, -, q6, q7, qsp, qa⟩ := hq
      have e2 : stackArg σ₁ 2 = stackArg σ₂ 2 := qa 2 (by decide)
      have e1 : stackArg σ₁ 1 = stackArg σ₂ 1 := qa 1 (by decide)
      obtain ⟨hP₁, hs₁, k₁, -⟩ := gsCall_of p₁ sY sS r₁ w₁ sp₁ f₁ hd
      obtain ⟨hP₂, hs₂, k₂, -⟩ := gsCall_of p₂ (by rw [← e2]; exact sY) (by rw [← e2]; exact sS) r₂ w₂
        (sp₂.trans qsp) (by rw [← e2, ← q6, ← q7]; exact f₂) (by rw [← q6, ← q7]; exact hd)
      rw [← e1] at hP₂ k₂
      rw [← q0] at k₂
      exact pwS_rel g (.inl rfl) hP₁ hs₁ hP₂ hs₂ c₁ k₁ c₂ k₂ (sp₁.trans sp₂.symm))
    (fun {σ} _ => powTbl_for hP 2 σ)
    fun _ _ _ _ _ sp₁ sp₂ hr _ _ _ _ _ _ => powTblEnc_rel (sp₁.trans sp₂.symm) hr

end

section
variable (v : GcmImpl) (g : GhashStoreImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
  (hP : Proof.Gcm.AArch64.Pmull.PrepPow) (gh : Gh8Ok)
include hMK hP gh

theorem sealStS_correct (s : State) (hs : sealStAArch64.pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Stitch.sealStorePw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      sealStAArch64.post s s' := by
  obtain ⟨t, s₁, he, ha, hp⟩ := sealStS_correctN v g hMK hP gh _ (narrowS_pre hs)
  exact ⟨t, _, narrowS_exec hs he, ha, hp⟩

theorem sealStS_ct :
    ConstantTime isa sealStAArch64.pre sealStAArch64.pub (Impl.AesGcm.AArch64.Stitch.sealStorePw v.callees g.fn) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨u₁, r₁, f₁, -⟩ := sealStS_correctN v g hMK hP gh _ (narrowS_pre h₁)
  obtain ⟨u₂, r₂, f₂, -⟩ := sealStS_correctN v g hMK hP gh _ (narrowS_pre h₂)
  rw [(Exec.det e₁ (narrowS_exec h₁ f₁)).1, (Exec.det e₂ (narrowS_exec h₂ f₂)).1]
  exact sealStS_ctN v g hMK hP gh _ _ _ _ _ _ (narrowS_pre h₁) (narrowS_pre h₂) hq f₁ f₂

theorem sealStS_verified :
    Verified AArch64.target (Impl.AesGcm.AArch64.Stitch.sealStorePw v.callees g.fn)
      (Proof.AesGcm.sealStorePowersScratchContract AArch64.abi) :=
  Verified.of_correct (sealStS_correct v g hMK hP gh) (sealStS_ct v g hMK hP gh)
    { pre := by
        sig_implies_pre [Proof.AesGcm.sealStorePowersScratchContract, Proof.AesGcm.sealStorePowersScratchSig,
          Proof.AesGcm.sealStorePowersPreP, Spec.Gcm.sealPre, Spec.Gcm.storePowersOk,
          Spec.Gcm.sealStorePowersPost, Spec.Gcm.sealPost,
          sealStAArch64, sealStW, pwR, sealAArch64, onePub, args, rounds, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        intro s s' _ h
        sig_post [Proof.AesGcm.sealStorePowersScratchContract, Proof.AesGcm.sealStorePowersScratchSig,
          Proof.AesGcm.sealStorePowersPreP, Spec.Gcm.sealPre, Spec.Gcm.storePowersOk,
          Spec.Gcm.sealStorePowersPost, Spec.Gcm.sealPost,
          sealStAArch64, sealStW, pwR, sealAArch64, onePub, args, rounds, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
        sig_reduce [sealStAArch64, sealAArch64, AArch64.stackArg, AArch64.stackArgAddr] at h
        sig_simp [sealStAArch64, sealAArch64, AArch64.stackArg, AArch64.stackArgAddr] [] at h
        exact ⟨fun _ => h.1, h.2⟩
      pub := by
        sig_implies_pub [Proof.AesGcm.sealStorePowersScratchContract, Proof.AesGcm.sealStorePowersScratchSig,
          Proof.AesGcm.sealStorePowersPreP, Spec.Gcm.sealPre, Spec.Gcm.storePowersOk,
          Spec.Gcm.sealStorePowersPost, Spec.Gcm.sealPost,
          sealStAArch64, sealStW, pwR, sealAArch64, onePub, args, rounds, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      sat := ⟨sealSatSt, by
        sig_pre [Proof.AesGcm.sealStorePowersScratchContract, Proof.AesGcm.sealStorePowersScratchSig,
          Proof.AesGcm.sealStorePowersPreP, Spec.Gcm.sealPre, Spec.Gcm.storePowersOk, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop,
          sealSatSt, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)⟩ }

end

theorem sealStS_framed (v : GcmImpl) (g : GhashStoreImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
    (hP : Proof.Gcm.AArch64.Pmull.PrepPow) (gh : Gh8Ok) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (Impl.AesGcm.AArch64.Stitch.sealStorePw v.callees g.fn))
      (Spec.Gcm.sealStorePowersContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Gcm.sealStorePowersSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.AesGcm.sealStorePowersPreP AArch64.abi.ptrBits)
    (post := Spec.Gcm.sealStorePowersPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (sealStS_verified v g hMK hP gh) (by decide) (by decide) (Proof.AesGcm.sealStorePowersPre_local _)
    (Proof.AesGcm.sealStorePowersPost_local _) sealFrameSatSt_pre

end VG.Proof.AesGcm.AArch64.Fast
