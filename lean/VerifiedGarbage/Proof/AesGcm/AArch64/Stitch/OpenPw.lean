module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.SealPw
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortOpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenSh
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenW
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.SealPw
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortOpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Verified
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Verified
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenPw
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenTo
meta import VerifiedGarbage.Proof.AesGcm.Rounds
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenPw

/-!
# AES-GCM on AArch64, interleaved: `vg_aes_gcm_open_with_powers`

Untrusted: everything here is checked by Lean. As `Stitch/SealPw.lean`, for
`open` (`Fast/OpenPw.lean`); and `vg_aes_gcm_open_to_with_powers` in one pass
(`Stitch.openToWithPw`, the same code out of place), as `Fast/OpenTo.lean`
does for `Fast.openToWithPw`.
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
    (stitchOpenWithS_keepsV v (.inl ⟨rfl, rfl⟩) (pwTbl_keepsV (.inr (.inl rfl))) (pwSel_keepsV v g (.inr (.inl rfl))))

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
      exact pwSel_rel v g (.inr (.inl rfl)) hP₁ hs₁ hP₂ hs₂ c₁ k₁ c₂ k₂ (sp₁.trans sp₂.symm))
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
      exact pwTbl_rel (.inr (.inl rfl)) (fun hsp hr => pwRestDec_rel hsp hr) (sp₁.trans sp₂.symm) hr hP₁ hs₁ hP₂ hs₂)
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
      exact pwTbl_relR shRegs (.inr (.inl rfl)) (fun hsp hr => pwRestOpenShort_rel hsp hr) (sp₁.trans sp₂.symm) hr hP₁ hs₁ hP₂
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
          Spec.Gcm.openWithPowersPre, Spec.Gcm.openPre, Proof.AesGcm.openWithPowersRoundsPost, Proof.AesGcm.openRoundsPost,
          Spec.Gcm.openWithPowersLeak, Spec.Gcm.openLeak, openPwAArch64, openPwW, pwRO, openAArch64, onePub,
          openRes, openLeakOf, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
          List.getD, List.range, List.range.loop]
      post := by
        sig_implies_post [Proof.AesGcm.openWithPowersScratchContract, Proof.AesGcm.openWithPowersScratchSig,
          Spec.Gcm.openWithPowersPre, Spec.Gcm.openPre, Proof.AesGcm.openWithPowersRoundsPost, Proof.AesGcm.openRoundsPost,
          Spec.Gcm.openWithPowersLeak, Spec.Gcm.openLeak, openPwAArch64, openPwW, pwRO, openAArch64, onePub,
          openRes, openLeakOf, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
          List.getD, List.range, List.range.loop]
      pub := by
        sig_implies_pub [Proof.AesGcm.openWithPowersScratchContract, Proof.AesGcm.openWithPowersScratchSig,
          Spec.Gcm.openWithPowersPre, Spec.Gcm.openPre, Proof.AesGcm.openWithPowersRoundsPost, Proof.AesGcm.openRoundsPost,
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
      (Proof.AesGcm.openWithPowersRoundsContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Gcm.openWithPowersSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openWithPowersPre AArch64.abi.ptrBits)
    (post := Proof.AesGcm.openWithPowersRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (leak := some (Spec.Gcm.openWithPowersLeak AArch64.abi.ptrBits))
    (openPwS_verified v g hMK gh) (by decide) (by decide) (Proof.AesGcm.openWithPowersPre_local _)
    (Proof.AesGcm.openWithPowersPost_local _) openFrameSatPw_pre
    (hleak := Proof.AesGcm.openWithPowersLeak_local _)

/-! ## `vg_aes_gcm_open_to_with_powers`, in one pass

`Stitch.openToWithPw` is the same code out of place (`openWithSG c true 5`):
`pw` is the stack argument 4, read from `[sp + 32]` by the table and the
call of `vg_ghash_with_powers`, which may come after the loop has written
the first bytes of `dst`. `pw` is readable, and apart from `dst`, which is
writable, as the contract's buffers are. -/

/-- `dst`, of `len` bytes. -/
abbrev dstRT (s : State) : Region := ⟨stackArg s 0, (s.gpr .x7).toNat⟩

/-- What `vg_aes_gcm_open_to_with_powers` needs in one pass, on the regions
its proofs run on: `openToPwN`, with `pw` apart from `dst`. -/
def openToPwSN (s : State) : Prop := openToPwN s ∧ (pwRT s).Disjoint (dstRT s)

/-- What `vg_aes_gcm_open_to_with_powers` needs in one pass: `openToPwW`,
with `pw` apart from `dst`. -/
def openToPwSW (s : State) : Prop := openToPwW s ∧ (pwRT s).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩

theorem openToPwSW_N {s : State} (h : openToPwSW s) : openToPwSN (narrowPT s) := by
  obtain ⟨hw, pd⟩ := h
  refine ⟨narrowPT_pre hw, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hl, -⟩ := hw
  show (pwRT s).Disjoint ⟨stackArg s 0, (s.gpr .x7).toNat⟩
  rw [← hl]; exact pd

/-- `vg_aes_gcm_open_to_with_powers`, in one pass. -/
def openToPwSAArch64 : Contract isa where
  pre := openToPwSW
  post := openToPostOf
  pub s₁ s₂ := onePub 6 s₁ s₂ ∧ openToLeakOf s₁ = openToLeakOf s₂

/-- At the call, with memory changed since the entry only in the working
space and `dst`: `pw` is at `[sp + 32]`, readable, apart from the
accumulator and the working space of the call, and holds the powers. -/
theorem gwCallToS_of {σ s : State} {Y S : Addr} (hs : openToPwSN σ)
    (sY : Region.Sub ⟨Y, 16⟩ (workR (stackArg σ 5))) (sS : Region.Sub ⟨S, 256⟩ (workR (stackArg σ 5)))
    (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr) (hsp : s.sp = σ.sp)
    (hf : Frame [workR (stackArg σ 5), dstRT σ] σ.mem s.mem) :
    s.mem.readW (s.sp + BitVec.ofNat 64 32) 64 = stackArg σ 4 ∧
      InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 32) 8 ∧
      GhWCall s (σ.gpr .x0) Y S (stackArg σ 4) := by
  obtain ⟨⟨hpx, pw, rep⟩, pd⟩ := hs
  have T := openToLay hpx
  have hrd₀ := hpx.1
  have hp' := hpx
  simp only [openToPreXW] at hp'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, dda, -, -, -, -, -, -, -, -, -, -, -, hlen⟩ := hp'
  have hspA := T.hsp 4 (by decide)
  have sA : Region.Sub ⟨σ.sp + BitVec.ofNat 64 32, 8⟩ (args σ 6) := by
    show Region.Sub ⟨σ.sp + BitVec.ofNat 64 32, 8⟩ ⟨σ.sp + BitVec.ofNat 64 (8 * 0), 8 * 6⟩
    rw [show σ.sp + BitVec.ofNat 64 (8 * 0) = σ.sp by rw [Nat.mul_zero, BitVec.add_zero]]
    exact Offset.sub_base _ (by decide)
  have dda' : (dstRT σ).Disjoint (args σ 6) := by
    show (⟨stackArg σ 0, (σ.gpr .x7).toNat⟩ : Region).Disjoint (args σ 6)
    rw [← hlen]; exact dda
  refine ⟨?_, by rw [hrd, hwr, hsp]; exact hspA, ⟨?_, (pw.sub_right sY).symm, (pw.sub_right sS).symm, ?_⟩⟩
  · rw [hsp, hf.readW (r := ⟨σ.sp + BitVec.ofNat 64 32, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact T.args.sub_left sA
      · exact (dda'.sub_right sA).symm) (by decide)]
    rfl
  · refine Covers.left (Covers.of_mem fun r hr => ?_)
    simp only [List.mem_singleton] at hr
    subst hr
    rw [hrd, hrd₀]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · have hH : Spec.Gcm.blockAt s.mem (σ.gpr .x0 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH σ.mem (σ.gpr .x0) :=
      blockAt_frame hf fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact T.dcW.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
        · exact T.dst.ctx.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
    rw [hH]
    exact Proof.AesGcm.powers8Repr_congr (fun i hi => hf.bytes (R := pwRT σ) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact pw
        · exact pd) (show 128 ≤ 2 ^ 64 by decide) hi) rep

/-- `pwTbl 32` writes the table, from the powers in `pw`. -/
theorem pwTbl_forT {s : State} (hs : openToPwSN s) :
    TbForOP (Impl.AesGcm.AArch64.Stitch.pwTbl 32) (s.gpr .x0) (stackArg s 5) s.sp (stackArg s 0)
      (s.gpr .x7).toNat s :=
  fun u he hrd hwr hf => by
    obtain ⟨hP, hsl, k⟩ := gwCallToS_of hs (Y := stackArg s 5 + BitVec.ofNat 64 512)
      (S := stackArg s 5 + BitVec.ofNat 64 512) (Lay.wSub (by decide)) (Lay.wSub (by decide)) hrd hwr he.sp hf
    have T := openToLay hs.1.1
    have hH : Spec.Gcm.blockAt u.mem (s.gpr .x0 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem (s.gpr .x0) :=
      blockAt_frame hf fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact T.dcW.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
        · exact T.dst.ctx.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
    rw [← hH]
    exact Stitch.pwTbl_ok (by decide) he hP hsl k.reads k.repr

section
variable (v : GcmImpl) (g : GhashWithImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
include hMK gh

theorem openToPwS_correctN (s : State) (hs : openToPwSN s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Stitch.openToWithPw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      openToPostOf s s' :=
  WP.withPreservedV (openToWithSh_wp (w := 5) v _ hMK gh (.inr rfl) hs.1.1
      (fun _ _ _ _ _ hc sY sS hrd hwr hsp hf =>
        have q := gwCallToS_of hs sY sS hrd hwr hsp hf
        pwSel_call v g (k := 32) (by decide) q.1 q.2.1 hc q.2.2) (pwTbl_forT hs))
    (stitchOpenWithS_keepsV v (.inr ⟨rfl, rfl⟩) (pwTbl_keepsV (.inr (.inr rfl))) (pwSel_keepsV v g (.inr (.inr rfl))))

theorem openToPwS_ctN :
    ConstantTime isa openToPwSN (fun s₁ s₂ => onePub 6 s₁ s₂ ∧ openToLeakOf s₁ = openToLeakOf s₂)
      (Impl.AesGcm.AArch64.Stitch.openToWithPw v.callees g.fn) :=
  openToWithSh_ct (w := 5) v _ hMK gh (.inr rfl) (extra := fun s => [pwRT s]) (extraW := fun _ => [])
    (fun _ h => h.1.1)
    (fun p hc sY sS hrd hwr hsp hf =>
      have q := gwCallToS_of p sY sS hrd hwr hsp hf
      pwSel_call v g (k := 32) (by decide) q.1 q.2.1 hc q.2.2)
    (fun {σ₁ σ₂ s₁ s₂ _ _ _ _} p₁ p₂ hq c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ => by
      obtain ⟨q0, -, -, -, -, -, -, q7, qsp, qa⟩ := hq
      have e5 : stackArg σ₁ 5 = stackArg σ₂ 5 := qa 5 (by decide)
      have e4 : stackArg σ₁ 4 = stackArg σ₂ 4 := qa 4 (by decide)
      have e0 : stackArg σ₁ 0 = stackArg σ₂ 0 := qa 0 (by decide)
      obtain ⟨hP₁, hs₁, k₁⟩ := gwCallToS_of p₁ sY sS r₁ w₁ sp₁ f₁
      obtain ⟨hP₂, hs₂, k₂⟩ := gwCallToS_of p₂ (by rw [← e5]; exact sY) (by rw [← e5]; exact sS) r₂ w₂
        (sp₂.trans qsp) (by rw [← e5]; show Frame [_, ⟨stackArg σ₂ 0, (σ₂.gpr .x7).toNat⟩] _ _; rw [← e0, ← q7]; exact f₂)
      rw [← e4] at hP₂ k₂
      rw [← q0] at k₂
      exact pwSel_rel v g (.inr (.inr rfl)) hP₁ hs₁ hP₂ hs₂ c₁ k₁ c₂ k₂ (sp₁.trans sp₂.symm))
    (fun p => pwTbl_forT p)
    (fun {σ₁ σ₂} p₁ p₂ hq v₁ v₂ sp₁ sp₂ hr h15 r₁ w₁ f₁ r₂ w₂ f₂ => by
      obtain ⟨-, -, -, -, -, -, -, q7, qsp, qa⟩ := hq
      have e5 : stackArg σ₁ 5 = stackArg σ₂ 5 := qa 5 (by decide)
      have e4 : stackArg σ₁ 4 = stackArg σ₂ 4 := qa 4 (by decide)
      have e0 : stackArg σ₁ 0 = stackArg σ₂ 0 := qa 0 (by decide)
      obtain ⟨hP₁, hs₁, -⟩ := gwCallToS_of p₁ (Y := stackArg σ₁ 5 + BitVec.ofNat 64 512)
        (S := stackArg σ₁ 5 + BitVec.ofNat 64 512) (Lay.wSub (by decide)) (Lay.wSub (by decide)) r₁ w₁ sp₁ f₁
      obtain ⟨hP₂, hs₂, -⟩ := gwCallToS_of p₂ (Y := stackArg σ₂ 5 + BitVec.ofNat 64 512)
        (S := stackArg σ₂ 5 + BitVec.ofNat 64 512) (Lay.wSub (by decide)) (Lay.wSub (by decide)) r₂ w₂
        (sp₂.trans qsp) (by rw [← e5]; show Frame [_, ⟨stackArg σ₂ 0, (σ₂.gpr .x7).toNat⟩] _ _; rw [← e0, ← q7]; exact f₂)
      rw [← e4] at hP₂
      exact pwTbl_relR (.x15 :: stRegs) (.inr (.inr rfl)) (fun hsp hr => pwRestDecTo_rel hsp hr)
        (sp₁.trans sp₂.symm) (fun r hr' => by
          rcases List.mem_cons.mp hr' with rfl | hr'
          · exact h15
          · exact hr r hr') hP₁ hs₁ hP₂ hs₂)
    fun {σ₁ σ₂} p₁ p₂ hq v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂ => by
      obtain ⟨-, -, -, -, -, -, -, q7, qsp, qa⟩ := hq
      have e5 : stackArg σ₁ 5 = stackArg σ₂ 5 := qa 5 (by decide)
      have e4 : stackArg σ₁ 4 = stackArg σ₂ 4 := qa 4 (by decide)
      have e0 : stackArg σ₁ 0 = stackArg σ₂ 0 := qa 0 (by decide)
      obtain ⟨hP₁, hs₁, -⟩ := gwCallToS_of p₁ (Y := stackArg σ₁ 5 + BitVec.ofNat 64 512)
        (S := stackArg σ₁ 5 + BitVec.ofNat 64 512) (Lay.wSub (by decide)) (Lay.wSub (by decide)) r₁ w₁ sp₁ f₁
      obtain ⟨hP₂, hs₂, -⟩ := gwCallToS_of p₂ (Y := stackArg σ₂ 5 + BitVec.ofNat 64 512)
        (S := stackArg σ₂ 5 + BitVec.ofNat 64 512) (Lay.wSub (by decide)) (Lay.wSub (by decide)) r₂ w₂
        (sp₂.trans qsp) (by rw [← e5]; show Frame [_, ⟨stackArg σ₂ 0, (σ₂.gpr .x7).toNat⟩] _ _; rw [← e0, ← q7]; exact f₂)
      rw [← e4] at hP₂
      exact pwTbl_relR shRegs (.inr (.inr rfl)) (fun hsp hr => pwRestOpenShort_rel hsp hr) (sp₁.trans sp₂.symm) hr
        hP₁ hs₁ hP₂ hs₂

theorem openToPwS_correct (s : State) (hs : openToPwSAArch64.pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Stitch.openToWithPw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      openToPwSAArch64.post s s' := by
  obtain ⟨t, s₁, he, ha, hp⟩ := openToPwS_correctN v g hMK gh _ (openToPwSW_N hs)
  exact ⟨t, _, narrowPT_exec hs.1 he, ha, hp⟩

theorem openToPwS_ct :
    ConstantTime isa openToPwSAArch64.pre openToPwSAArch64.pub
      (Impl.AesGcm.AArch64.Stitch.openToWithPw v.callees g.fn) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨u₁, r₁, f₁, -⟩ := openToPwS_correctN v g hMK gh _ (openToPwSW_N h₁)
  obtain ⟨u₂, r₂, f₂, -⟩ := openToPwS_correctN v g hMK gh _ (openToPwSW_N h₂)
  rw [(Exec.det e₁ (narrowPT_exec h₁.1 f₁)).1, (Exec.det e₂ (narrowPT_exec h₂.1 f₂)).1]
  exact openToPwS_ctN v g hMK gh _ _ _ _ _ _ (openToPwSW_N h₁) (openToPwSW_N h₂) hq f₁ f₂

theorem openToPwS_verified :
    Verified AArch64.target (Impl.AesGcm.AArch64.Stitch.openToWithPw v.callees g.fn)
      (Proof.AesGcm.openToWithPowersScratchContract AArch64.abi) :=
  Verified.of_correct (openToPwS_correct v g hMK gh) (openToPwS_ct v g hMK gh)
    { pre := by
        sig_implies_pre [Proof.AesGcm.openToWithPowersScratchContract, Proof.AesGcm.openToWithPowersScratchSig,
          Spec.Gcm.openToWithPowersPre, Spec.Gcm.openToPre, Proof.AesGcm.openToWithPowersRoundsPost,
          Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToWithPowersLeak, Spec.Gcm.openToLeak, openToPwSAArch64,
          openToPwSW, openToPwW, pwRT, onePub, openToRes, openToPostOf, openToLeakOf, args, rounds,
          AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
          List.range.loop]
      post := by
        sig_implies_post [Proof.AesGcm.openToWithPowersScratchContract, Proof.AesGcm.openToWithPowersScratchSig,
          Spec.Gcm.openToWithPowersPre, Spec.Gcm.openToPre, Proof.AesGcm.openToWithPowersRoundsPost,
          Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToWithPowersLeak, Spec.Gcm.openToLeak, openToPwSAArch64,
          openToPwSW, openToPwW, pwRT, onePub, openToRes, openToPostOf, openToLeakOf, args, rounds,
          AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
          List.range.loop]
      pub := by
        sig_implies_pub [Proof.AesGcm.openToWithPowersScratchContract, Proof.AesGcm.openToWithPowersScratchSig,
          Spec.Gcm.openToWithPowersPre, Spec.Gcm.openToPre, Proof.AesGcm.openToWithPowersRoundsPost,
          Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToWithPowersLeak, Spec.Gcm.openToLeak, openToPwSAArch64,
          openToPwSW, openToPwW, pwRT, onePub, openToRes, openToPostOf, openToLeakOf, args, rounds,
          AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
          List.range.loop]
      sat := ⟨openToSatPw, by
        sig_pre [Proof.AesGcm.openToWithPowersScratchContract, Proof.AesGcm.openToWithPowersScratchSig,
          Spec.Gcm.openToWithPowersPre, Spec.Gcm.openToPre, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop, openToSatPw, openToSat,
          stackArg, stackArgAddr, Mem.readW, Mem.read]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact Proof.AesGcm.powers8Repr_of_zeroMem (by decide) openToSatPw_zero⟩ }

end

/-- `Stitch.openToWithPw` in a frame of 2608 bytes holding its working space
and copies of its five other stack arguments. -/
theorem openToPwS_framed (v : GcmImpl) (g : GhashWithImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2608 5 (Impl.AesGcm.AArch64.Stitch.openToWithPw v.callees g.fn))
      (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi 2608) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Gcm.openToWithPowersSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openToWithPowersPre AArch64.abi.ptrBits)
    (post := Proof.AesGcm.openToWithPowersRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2608) (leak := some (Spec.Gcm.openToWithPowersLeak AArch64.abi.ptrBits))
    (openToPwS_verified v g hMK gh) (by decide) (by decide) (Proof.AesGcm.openToWithPowersPre_local _)
    (Proof.AesGcm.openToWithPowersPost_local _) openToFrameSatPw_pre
    (hleak := Proof.AesGcm.openToWithPowersLeak_local _)

end VG.Proof.AesGcm.AArch64.Fast
