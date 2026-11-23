module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Sm4.Arm.Fn
public import VerifiedGarbage.Proof.Sm4.Arm.KeyVerified
public import VerifiedGarbage.Proof.Sm4.Arm.EcbCall
public import VerifiedGarbage.Proof.Sm4.Arm.SerialCbcVerified
public import VerifiedGarbage.Proof.Sm4.Arm.CbcBatchVerified
public import VerifiedGarbage.Proof.Sm4.Arm.SerialCfbVerified
public import VerifiedGarbage.Proof.Sm4.Arm.CfbBatchVerified
public import VerifiedGarbage.Proof.Sm4.Arm.SerialOfbVerified
public import VerifiedGarbage.Proof.Sm4.Arm.BatchVerified
public import VerifiedGarbage.Proof.Sm4.Arm.CtrFinal
public import VerifiedGarbage.Proof.Sm4.Arm.FbFinalVerified
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Sm4.CbcScratch
import VerifiedGarbage.Proof.Sm4.FbScratch
import VerifiedGarbage.Proof.Sm4.CtrFinal
import VerifiedGarbage.Proof.Sm4.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Modes.Arm.ScrubCode
import VerifiedGarbage.Proof.Modes.Arm.Wrap
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Argon2.Arm.Push
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.Sm4.Arm.Fn
meta import VerifiedGarbage.Proof.Sm4.Arm.KeyVerified
meta import VerifiedGarbage.Proof.Sm4.Arm.EcbCall
meta import VerifiedGarbage.Proof.Sm4.Arm.SerialCbcVerified
meta import VerifiedGarbage.Proof.Sm4.Arm.CbcBatchVerified
meta import VerifiedGarbage.Proof.Sm4.Arm.SerialCfbVerified
meta import VerifiedGarbage.Proof.Sm4.Arm.CfbBatchVerified
meta import VerifiedGarbage.Proof.Sm4.Arm.SerialOfbVerified
meta import VerifiedGarbage.Proof.Sm4.Arm.BatchVerified
meta import VerifiedGarbage.Proof.Sm4.Arm.CtrFinal
meta import VerifiedGarbage.Proof.Sm4.Arm.FbFinalVerified
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Sm4.CbcScratch
meta import VerifiedGarbage.Proof.Sm4.FbScratch
meta import VerifiedGarbage.Proof.Sm4.CtrFinal
meta import VerifiedGarbage.Proof.Sm4.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Modes.Arm.ScrubCode
meta import VerifiedGarbage.Proof.Modes.Arm.Wrap
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Frame
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.MdStream.Arm.Common
meta import VerifiedGarbage.Proof.Argon2.Arm.Push
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# SM4's key expansion, ECB and modes on ARMv7, as emitted

Each function is its code with its cleanup (`Impl.Sm4.Arm.Fn`): the stack
its contract reserves zeroed in a loop (`Impl.Scrub.Arm.scrubAll`), and the
registers a callee may change set to constants. `Fn` below has the theorem of
each: it meets its contract in constant time and returns without secret
residue (`VerifiedScrubbed`), from `Arm.Scrub.verifiedScrubbedAll`, given
that its frames are within that stack (`CodeOk`), which is what its
registration binds.

The postconditions read the memory on return only within their buffers
(`Arm.Scrub.PostOut`, from the lemmas of `Proof/Sm4/Scratch.lean` and its
neighbours, which RISC-V's uses too). ECB's contract reserves 1480 bytes, the
key expansion's 1464 and the final CFB and OFB functions' 1560, which are no
frame size of the model (`FrameOk`): they are proven with 1488, 1472 and 1568
(`Arm.Scrub.Verified.stack_le`).
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Impl.StackScratch.Arm

/-! ## The stack, rounded up to a frame of the model -/

theorem ecbSat (d : Impl.Sm4.Arm.Dir) :
    ∃ s, (Spec.Sm4.ecbContract Arm.abi (specDirArm d) 1488).pre s := by
  cases d <;>
  sig_implies_sat [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, specDirArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, State.addr] [ecbCallSat] using ecbCallSat

theorem ecb_verified (d : Impl.Sm4.Arm.Dir) :
    Verified Arm.target (Impl.Sm4.Arm.ecbCall d) (Spec.Sm4.ecbContract Arm.abi (specDirArm d) 1488) :=
  Verified.stack_le (by decide) (ecbCall_verified d) (ecbSat d)

theorem cfbEncryptFinalSat : ∃ s, (Spec.Sm4.cfbEncryptFinalContract Arm.abi 1568).pre s := by
  implies_sat [Spec.Sm4.cfbEncryptFinalContract, Spec.Sm4.cfbFinalSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 1

theorem cfbDecryptFinalSat : ∃ s, (Spec.Sm4.cfbDecryptFinalContract Arm.abi 1568).pre s := by
  implies_sat [Spec.Sm4.cfbDecryptFinalContract, Spec.Sm4.cfbFinalSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 1

theorem ofbFinalSat : ∃ s, (Spec.Sm4.ofbFinalContract Arm.abi 1568).pre s := by
  implies_sat [Spec.Sm4.ofbFinalContract, Spec.Sm4.ofbFinalSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 1

/-! ## The key expansion, a call of `vg_sm4_expand_key_core`

`vg_sm4_expand_key` (`expandKeyCall`) calls the key expansion's code with its
working space on the stack (`expandKey_framedU`), the internal
`vg_sm4_expand_key_core` that SM4-GCM's functions call too, in a frame saving
`r4` and `lr`, with `lr` kept in `r4` across the call (`WrapEntry`): 8 bytes
of stack above the callee's 1456, so 1464, proven as 1472, a frame size of
the model. -/

section

open VG.Proof.Modes.Arm (WrapEntry wrapMov_wp wrap_covers wrapMov_rel wrapRet_rel)

/-- The key expansion's contract with `stack = 1464`, as `sig_pre` evaluates it. -/
def keyCallArm : Contract Arm.isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 16⟩
    let sch : Region := ⟨State.addr (s.gpr .r1), 128⟩
    let stk : Region := ⟨State.addr s.sp - BitVec.ofNat 64 1464, 1464⟩
    1464 ≤ s.sp.toNat ∧ s.rd = [key] ∧ s.wr = [sch] ∧ key.Disjoint sch ∧ stk.Disjoint key ∧
      stk.Disjoint sch ∧ (s.gpr .r0).toNat + 16 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 128 ≤ 2 ^ 32
  post s s' :=
    Spec.Sm4.scheduleAt s'.mem (State.addr (s.gpr .r1)) =
      Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem (State.addr (s.gpr .r0)))
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1

theorem keyCode_stack : armStack (withRegScratch 1456 .r2 Impl.Sm4.Arm.expandKey) ≤ 1456 := by decide +kernel

private theorem keyEntry_pre {s₀ σ : State} (hs : keyCallArm.pre s₀) (e : WrapEntry s₀ σ) :
    (Spec.Sm4.expandKeyContract Arm.abi 1456).pre (σ.callEntry.withRegions s₀.rd s₀.wr) := by
  obtain ⟨hsp, hrd, hwr, dKS, sK, sS, fitK, fitS⟩ := hs
  have sp8 : (s₀.sp - BitVec.ofNat 32 8).toNat = s₀.sp.toNat - 8 := sub_toNat' (by omega_arith)
  sig_pre [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]
  have stS : Region.Sub (Argon2.Arm.stkR σ.sp 1456) ⟨State.addr s₀.sp - BitVec.ofNat 64 1464, 1464⟩ := by
    rw [e.sp]; exact Argon2.Arm.stkR_inner (by omega_arith) hsp
  rw [e.gpr .r0 (by decide), e.gpr .r1 (by decide)]
  exact ⟨by rw [e.sp, sp8]; omega_arith, by have := σ.sp.isLt; omega_arith, hrd, hwr, dKS, sK.sub_left stS,
    sS.sub_left stS, fitK, fitS⟩

theorem keyCall_correct (s₀ : State) (hs : keyCallArm.pre s₀) :
    ∃ t s', Exec isa Impl.Sm4.Arm.expandKeyCall s₀ t s' ∧ abiPreserved s₀ s' ∧ keyCallArm.post s₀ s' := by
  obtain ⟨hsp, hrd, hwr, dKS, sK, sS, fitK, fitS⟩ := hs
  -- The frame's 8 bytes, below the stack the contract reserves.
  have frSub : Region.Sub (Argon2.Arm.stkR s₀.sp 8) ⟨State.addr s₀.sp - BitVec.ofNat 64 1464, 1464⟩ :=
    Argon2.Arm.stkR_sub (by omega_arith) hsp
  have hfr : Frame [Argon2.Arm.stkR s₀.sp 8] s₀.mem (pushed [.r4, .lr] s₀).mem :=
    Argon2.Arm.pushed_stk (rs := [.r4, .lr]) (by simp; omega_arith)
  have hkey : Spec.Sm4.blockAt (pushed [.r4, .lr] s₀).mem (State.addr (s₀.gpr .r0)) =
      Spec.Sm4.blockAt s₀.mem (State.addr (s₀.gpr .r0)) := by
    apply Vector.ext; intro i hi
    simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn]
    exact hfr.bytes (R := ⟨State.addr (s₀.gpr .r0), 16⟩) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact (sK.sub_left frSub).symm) (by show 16 ≤ 2 ^ 64; decide) hi
  unfold Impl.Sm4.Arm.expandKeyCall
  have hn8 : 4 * [Reg.r4, .lr].length ≤ s₀.sp.toNat := by simp; omega_arith
  refine (WP.frame (rs := [.r4, .lr]) (r := .r4) (by decide) hn8 (by decide) ?_).elim
    fun t ⟨s', he, hq⟩ => ⟨t, s', he, hq⟩
  refine WP.seq (WP.mono (wrapMov_wp s₀) fun σ₃ e => ?_)
  have pre₃ := keyEntry_pre ⟨hsp, hrd, hwr, dKS, sK, sS, fitK, fitS⟩ e
  have cov₃ := wrap_covers e
  have sp8 : (s₀.sp - BitVec.ofNat 32 8).toNat = s₀.sp.toNat - 8 := sub_toNat' (by omega_arith)
  refine WP.seq (FrameStack.WP.callF (k := Spec.Sm4.expandKeyContract Arm.abi 1456) Proof.Sm4.Arm.expandKey_framedU.1
    (rd := s₀.rd) (wr := s₀.wr) pre₃ cov₃.1 cov₃.2 (by rw [e.sp, sp8]; have := keyCode_stack; omega_arith) ?_)
  intro s' rd' wr' sp' fr' pres' post'
  refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun σ₄ u₄ => WP.block_nil ?_
  have r4' : s'.gpr .r4 = s₀.gpr .lr := by rw [pres' .r4 (by decide) (by decide), e.r4]
  have sp4 : σ₄.sp = s₀.sp - BitVec.ofNat 32 8 := by rw [u₄.sp, sp', e.sp]
  have hsp8 : 8 ≤ s₀.sp.toNat := by omega_arith
  -- The word `r4` was pushed to, in the frame below the stack the contract reserves.
  have hsub4 : Region.Sub ⟨State.addr (s₀.sp - BitVec.ofNat 32 8), 4⟩
      ⟨State.addr s₀.sp - BitVec.ofNat 64 1464, 1464⟩ := by
    refine fun x hx => frSub x ?_
    rw [FrameStack.addr_sub' hsp8] at hx
    have := Offset.sub_base (State.addr s₀.sp - BitVec.ofNat 64 8) (d := 0) (n := 4) (k := 8) (by omega_arith)
    simp only [BitVec.add_zero] at this
    exact this x hx
  have hw4 : s'.mem.readW (State.addr (s₀.sp - BitVec.ofNat 32 8)) 32 = s₀.gpr .r4 := by
    rw [fr'.readW (r := ⟨State.addr (s₀.sp - BitVec.ofNat 32 8), 4⟩) (Region.contains_self _ _) ?_
      (by decide), e.mem]
    · have := Argon2.Arm.storeWords_readW s₀.mem (s₀.sp - BitVec.ofNat 32 8) [s₀.gpr .r4, s₀.gpr .lr]
        (by rw [sp8]; have := s₀.sp.isLt; simp; omega_arith) (i := 0) (by simp)
      simpa [pushed] using this
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · rw [hwr, List.mem_singleton] at hr; subst hr; exact sS.sub_left hsub4
      · rw [List.mem_singleton] at hr; subst hr
        rw [e.sp]
        simp only [FrameStack.belowA]
        have := keyCode_stack
        rw [FrameStack.addr_sub' (x := s₀.sp - BitVec.ofNat 32 8) (by rw [sp8]; omega_arith)]
        exact Offset.base_disjoint_below _ (by omega_arith)
  intro ml ul hfl
  have hfl' : Frame [Argon2.Arm.stkR s₀.sp 8] σ₄.mem ml := by
    rw [show 4 * [Reg.r4, Reg.lr].length = 8 from rfl, FrameStack.addr_sub' hsp8] at hfl; exact hfl
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩ <;> dsimp only
  · by_cases h4 : r = .r4
    · subst h4
      show (σ₄.setReg .r4 (σ₄.mem.readW (State.addr σ₄.sp) 32)).gpr .r4 = _
      rw [RegUpd.gpr_setReg_self, sp4, u₄.mem]; exact hw4
    · rw [popped_gpr h4]
      by_cases hl : r = .lr
      · subst hl; rw [u₄.gpr, r4']
      · rw [u₄.other r hl, pres' r hr hl, e.gpr r h4]
  · rw [popped_sp, sp4]; exact BitVec.sub_add_cancel _ _
  · sig_post [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at post'
    rw [e.gpr .r0 (by decide), e.gpr .r1 (by decide), e.mem] at post'
    simp only [State.addr] at hkey
    rw [hkey] at post'
    show Spec.Sm4.scheduleAt ml _ = _
    rw [Proof.Sm4.scheduleAt_frame hfl' (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        simpa [State.addr] using (sS.sub_left frSub).symm),
      u₄.mem]
    exact post'

private theorem keyEntry_pub {s₁ s₂ σ₁ σ₂ : State} (hp : keyCallArm.pub s₁ s₂)
    (e₁ : WrapEntry s₁ σ₁) (e₂ : WrapEntry s₂ σ₂) {rd wr : List Region} :
    (Spec.Sm4.expandKeyContract Arm.abi 1456).pub (σ₁.callEntry.withRegions rd wr)
      (σ₂.callEntry.withRegions rd wr) := by
  sig_pub [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]
  obtain ⟨psp, p0, p1⟩ := hp
  exact ⟨by rw [e₁.sp, e₂.sp, psp], by rw [e₁.gpr _ (by decide), e₂.gpr _ (by decide), p0],
    by rw [e₁.gpr _ (by decide), e₂.gpr _ (by decide), p1]⟩

theorem keyCall_ct : ConstantTime isa keyCallArm.pre keyCallArm.pub Impl.Sm4.Arm.expandKeyCall := by
  unfold Impl.Sm4.Arm.expandKeyCall
  refine RelCT.constantTime (RelCT.frame (fun s₁ s₂ h => h.2.2.1) ?_)
  refine RelCT.mono (P := fun a b => ∃ p : State × State, (keyCallArm.pre p.1 ∧ keyCallArm.pre p.2 ∧
      keyCallArm.pub p.1 p.2) ∧ a = pushed [.r4, .lr] p.1 ∧ b = pushed [.r4, .lr] p.2) ?_
    (fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ⟨(s₁, s₂), hp, Argon2.Arm.push_eq (by decide) pa,
      Argon2.Arm.push_eq (by decide) pb⟩) (fun _ _ h => h)
  refine RelCT.exists_ fun ⟨s₁, s₂⟩ => ?_
  let H := keyCallArm.pre s₁ ∧ keyCallArm.pre s₂ ∧ keyCallArm.pub s₁ s₂
  refine RelCT.seq (RelCT.wp (F₁ := fun σ => H ∧ WrapEntry s₁ σ) (F₂ := WrapEntry s₂)
    wrapMov_rel fun a b ⟨h, ha, hb⟩ =>
      ⟨ha ▸ WP.mono (wrapMov_wp s₁) fun _ e => ⟨h, e⟩, hb ▸ wrapMov_wp s₂⟩) ?_
  refine RelCT.seq (RelCT.call Proof.Sm4.Arm.expandKey_framedU.1 Proof.Sm4.Arm.expandKey_framedU.2.1 s₁.rd s₁.wr
    fun σ₁ σ₂ ⟨_, ⟨⟨h₁, h₂, hp⟩, e₁⟩, e₂⟩ => ?_) wrapRet_rel
  have hrd : s₂.rd = s₁.rd := by rw [h₁.2.1, h₂.2.1, hp.2.1]
  have hwr : s₂.wr = s₁.wr := by rw [h₁.2.2.1, h₂.2.2.1, hp.2.2]
  have p₂ := keyEntry_pre h₂ e₂
  rw [hrd, hwr] at p₂
  have c₂ := wrap_covers e₂
  rw [hrd, hwr] at c₂
  exact ⟨keyEntry_pre h₁ e₁, p₂, keyEntry_pub hp e₁ e₂, (wrap_covers e₁).1, (wrap_covers e₁).2, c₂.1, c₂.2⟩

/-- `vg_sm4_expand_key`: 1464 bytes of stack. -/
theorem keyCall_verified :
    Verified Arm.target Impl.Sm4.Arm.expandKeyCall (Spec.Sm4.expandKeyContract Arm.abi 1464) :=
  Verified.of_correct keyCall_correct keyCall_ct (by
    sig_implies [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, keyCallArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, State.addr] [Proof.Sm4.Arm.expandKeyFrameSat] using
      Proof.Sm4.Arm.expandKeyFrameSat)

theorem expandKeySat : ∃ s, (Spec.Sm4.expandKeyContract Arm.abi 1472).pre s := by
  implies_sat [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [Proof.Sm4.Arm.expandKeyFrameSat] using Proof.Sm4.Arm.expandKeyFrameSat

theorem expandKey_verified :
    Verified Arm.target Impl.Sm4.Arm.expandKeyCall (Spec.Sm4.expandKeyContract Arm.abi 1472) :=
  Verified.stack_le (by decide) keyCall_verified expandKeySat

end

/-! ## The stack the functions zeroed in a loop use

The frames of the key expansion and of the modes over whole blocks, which
`scrubAll` zeroes (`Arm.Scrub.CodeOk`). -/

theorem expandKeyCore_code : CodeOk (withRegScratch 1456 .r2 Impl.Sm4.Arm.expandKey) 1456 := by lit_decide
theorem cbcEncryptChained_code : CodeOk (withStackScratch 1520 0 Impl.Sm4.Arm.SerialCbc.encrypt) 1520 := by
  lit_decide
theorem cbcDecryptChained_code : CodeOk (withStackScratch 1520 0 Impl.Sm4.Arm.BatchCbc.decrypt) 1520 := by
  lit_decide
theorem cfbEncrypt_code : CodeOk (withStackScratch 1520 0 Impl.Sm4.Arm.SerialCfb.encrypt) 1520 := by lit_decide
theorem cfbDecrypt_code : CodeOk (withStackScratch 1520 0 Impl.Sm4.Arm.BatchCfb.decrypt) 1520 := by lit_decide
theorem ctr_code : CodeOk (withStackScratch 1520 0 Impl.Sm4.Arm.BatchCtr.ctr) 1520 := by lit_decide
theorem ofb_code : CodeOk (withStackScratch 1520 0 Impl.Sm4.Arm.SerialOfb.crypt) 1520 := by lit_decide

/-! ## The stack of ECB and of the modes over a message's last piece

ECB calls `vg_sm4_ecb` in a frame of 8 bytes, the final CFB and OFB call
ECB's code (`ecbCore`), and the final CTR CTR's, in frames of their own of
80 and 64 bytes: `scrubAll` zeroes the stack of all of them. -/

private theorem blk (is : List Instr) (n : Nat) : CodeOk (.block is) n := (CodeOk.block is).mono (Nat.zero_le n)

private theorem stackScratch_code {b m n : Nat} {c : Prog isa} (h : CodeOk c n) :
    CodeOk (withStackScratch b m c) (n + b) :=
  CodeOk.alloc (CodeOk.seq (blk _ _) h)

theorem ecbAny_code : CodeOk Impl.Sm4.Arm.ecbAnyCode 1472 := by unfold Impl.Sm4.Arm.ecbAnyCode; lit_decide

theorem expandKey_code : CodeOk Impl.Sm4.Arm.expandKeyCall 1472 :=
  CodeOk.push (n := 1464) (CodeOk.seq (blk _ _) (CodeOk.seq (CodeOk.call (expandKeyCore_code.mono (by decide)))
    (blk _ _)))

theorem ecb_code (d : Impl.Sm4.Arm.Dir) : CodeOk (Impl.Sm4.Arm.ecbCall d) 1488 :=
  CodeOk.push (n := 1480) (CodeOk.seq (blk _ _) (CodeOk.seq (CodeOk.call (ecbAny_code.mono (by decide))) (blk _ _)))

private theorem ecbCore_code :
    armStack (Impl.Sm4.Arm.ecbCore .encrypt).code + Proof.Modes.Arm.callExtraArm (Impl.Sm4.Arm.ecbCore .encrypt)
      ≤ 1488 ∧ noIcall (Impl.Sm4.Arm.ecbCore .encrypt).code = true :=
  ⟨by rw [show Proof.Modes.Arm.callExtraArm (Impl.Sm4.Arm.ecbCore .encrypt) = 0 from rfl, Nat.add_zero]
      exact (ecb_code .encrypt).1, (ecb_code .encrypt).2⟩

theorem cfbEncryptFinal_code : CodeOk (withStackScratch 80 0 Impl.Sm4.Arm.cfbEncryptFinal) 1568 :=
  stackScratch_code (Proof.Modes.Arm.seqFinal_scrubArm ecbCore_code _)
theorem cfbDecryptFinal_code : CodeOk (withStackScratch 80 0 Impl.Sm4.Arm.cfbDecryptFinal) 1568 :=
  stackScratch_code (Proof.Modes.Arm.seqFinal_scrubArm ecbCore_code _)
theorem ofbFinal_code : CodeOk (withStackScratch 80 0 Impl.Sm4.Arm.ofbFinal) 1568 :=
  stackScratch_code (Proof.Modes.Arm.seqFinal_scrubArm ecbCore_code _)

private theorem ctrCall_code : CodeOk Impl.Sm4.Arm.ctrCall 1520 := CodeOk.call ctr_code

theorem ctrFinal_code : CodeOk (withStackScratch 64 0 Impl.Sm4.Arm.ctrFinal) 1584 :=
  stackScratch_code (CodeOk.seq (blk _ _) (CodeOk.seq ctrCall_code (CodeOk.seq (blk _ _)
    (CodeOk.seq (CodeOk.ite (blk _ _) (CodeOk.seq (blk _ _) (CodeOk.seq ctrCall_code
      (CodeOk.seq (blk _ _) (CodeOk.loop (blk _ _)))))) (blk _ _)))))

end VG.Proof.Sm4.Arm.Scrub

namespace VG.Proof.Sm4.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Impl.StackScratch.Arm

/-- `vg_sm4_expand_key`. -/
theorem expandKey :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.expandKey (Spec.Sm4.expandKeyContract abi 1472) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.expandKeyApi)
    { code := Impl.Sm4.Arm.expandKeyCall
      verified := Scrub.expandKey_verified }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.expandKeyPostOut_local _))
    (scrubSideF_of Scrub.expandKey_code (by decide) _)

/-- `vg_sm4_ecb_encrypt`. -/
theorem ecbEncrypt :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.ecbEncrypt (Spec.Sm4.ecbContract abi .encrypt 1488) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.ecbEncryptApi)
    { code := Impl.Sm4.Arm.ecbCall .encrypt, verified := Scrub.ecb_verified .encrypt }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ecbPostOut_local _ .encrypt))
    (scrubSideF_of (Scrub.ecb_code .encrypt) (by decide) _)

/-- `vg_sm4_ecb_decrypt`. -/
theorem ecbDecrypt :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.ecbDecrypt (Spec.Sm4.ecbContract abi .decrypt 1488) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.ecbDecryptApi)
    { code := Impl.Sm4.Arm.ecbCall .decrypt, verified := Scrub.ecb_verified .decrypt }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ecbPostOut_local _ .decrypt))
    (scrubSideF_of (Scrub.ecb_code .decrypt) (by decide) _)

/-- `vg_sm4_cbc_encrypt_chained`. -/
theorem cbcEncryptChained :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.cbcEncryptChained
      (Spec.Sm4.cbcEncryptChainedContract abi 1520) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.cbcEncryptChainedApi)
    { code := withStackScratch 1520 0 Impl.Sm4.Arm.SerialCbc.encrypt
      verified := Proof.Sm4.Arm.SerialCbcVerified.framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cbcEncChainedPostOut_local _))
    (scrubSideF_of Scrub.cbcEncryptChained_code (by decide) _)

/-- `vg_sm4_cbc_decrypt_chained`. -/
theorem cbcDecryptChained :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.cbcDecryptChained
      (Spec.Sm4.cbcDecryptChainedContract abi 1520) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.cbcDecryptChainedApi)
    { code := withStackScratch 1520 0 Impl.Sm4.Arm.BatchCbc.decrypt
      verified := Proof.Sm4.Arm.CbcBatchVerified.framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cbcDecChainedPostOut_local _))
    (scrubSideF_of Scrub.cbcDecryptChained_code (by decide) _)

/-- `vg_sm4_cfb128_encrypt`. -/
theorem cfbEncrypt :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.cfbEncrypt (Spec.Sm4.cfbEncryptContract abi 1520) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.cfbEncryptApi)
    { code := withStackScratch 1520 0 Impl.Sm4.Arm.SerialCfb.encrypt
      verified := Proof.Sm4.Arm.SerialCfbVerified.framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cfbEncPostOut_local _))
    (scrubSideF_of Scrub.cfbEncrypt_code (by decide) _)

/-- `vg_sm4_cfb128_decrypt`. -/
theorem cfbDecrypt :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.cfbDecrypt (Spec.Sm4.cfbDecryptContract abi 1520) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.cfbDecryptApi)
    { code := withStackScratch 1520 0 Impl.Sm4.Arm.BatchCfb.decrypt
      verified := Proof.Sm4.Arm.CfbBatchVerified.framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cfbDecPostOut_local _))
    (scrubSideF_of Scrub.cfbDecrypt_code (by decide) _)

/-- `vg_sm4_cfb128_encrypt_final`. -/
theorem cfbEncryptFinal :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.cfbEncryptFinal (Spec.Sm4.cfbEncryptFinalContract abi 1568) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.cfbEncryptFinalApi)
    { code := withStackScratch 80 0 Impl.Sm4.Arm.cfbEncryptFinal
      verified := Verified.stack_le (by decide) Proof.Sm4.Arm.cfbEncryptFinal_framed Scrub.cfbEncryptFinalSat }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _))
    (scrubSideF_of Scrub.cfbEncryptFinal_code (by decide) _)

/-- `vg_sm4_cfb128_decrypt_final`. -/
theorem cfbDecryptFinal :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.cfbDecryptFinal (Spec.Sm4.cfbDecryptFinalContract abi 1568) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.cfbDecryptFinalApi)
    { code := withStackScratch 80 0 Impl.Sm4.Arm.cfbDecryptFinal
      verified := Verified.stack_le (by decide) Proof.Sm4.Arm.cfbDecryptFinal_framed Scrub.cfbDecryptFinalSat }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _))
    (scrubSideF_of Scrub.cfbDecryptFinal_code (by decide) _)

/-- `vg_sm4_ctr`. -/
theorem ctr : VerifiedScrubbed target Impl.Sm4.Arm.Fn.ctr (Spec.Sm4.ctrContract abi 1520) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.ctrApi)
    { code := withStackScratch 1520 0 Impl.Sm4.Arm.BatchCtr.ctr
      verified := Proof.Sm4.Arm.BatchVerified.framedU }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ctrPostOut_local _))
    (scrubSideF_of Scrub.ctr_code (by decide) _)

/-- `vg_sm4_ctr_final`. -/
theorem ctrFinal :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.ctrFinal (Spec.Sm4.ctrFinalContract abi 1584) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.ctrFinalApi)
    { code := withStackScratch 64 0 Impl.Sm4.Arm.ctrFinal
      verified := Proof.Sm4.Arm.CtrFinal.ctrFinal_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ctrFinalPostOut_local _))
    (scrubSideF_of Scrub.ctrFinal_code (by decide) _)

/-- `vg_sm4_ofb`. -/
theorem ofb : VerifiedScrubbed target Impl.Sm4.Arm.Fn.ofb (Spec.Sm4.ofbContract abi 1520) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.ofbApi)
    { code := withStackScratch 1520 0 Impl.Sm4.Arm.SerialOfb.crypt
      verified := Proof.Sm4.Arm.SerialOfbVerified.framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ofbPostOut_local _))
    (scrubSideF_of Scrub.ofb_code (by decide) _)

/-- `vg_sm4_ofb_final`. -/
theorem ofbFinal :
    VerifiedScrubbed target Impl.Sm4.Arm.Fn.ofbFinal (Spec.Sm4.ofbFinalContract abi 1568) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.ofbFinalApi)
    { code := withStackScratch 80 0 Impl.Sm4.Arm.ofbFinal
      verified := Verified.stack_le (by decide) Proof.Sm4.Arm.ofbFinal_framed Scrub.ofbFinalSat }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _))
    (scrubSideF_of Scrub.ofbFinal_code (by decide) _)

end VG.Proof.Sm4.Arm.Fn
