module

public import VerifiedGarbage.Impl.AesGcm.AArch64
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Proof.AesGcm.ScratchOpenTo
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesGcm.AArch64.Open
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Open
import VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.OneCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.OneCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
public import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Verified
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc

/-!
# AES-GCM on AArch64: `vg_aes_gcm_open_to` in one pass, constant time and `Verified`

Untrusted: everything here is checked by Lean. `openG c true w` leaks only
whether the tag is right, as `open` does (`OpenCT.lean`), by the same
relational lemmas, generic over `to`: the entry loads `work` and keeps `dst`,
`tag_len` and `tag` (`openEntryTo_rel`), and the rest is `open`'s
(`openRestWithFl_rel`, `openMainG_rel`); the branches depend only on the
public lengths and on whether the tag is right. Out of place the whole blocks
are decrypted by a call of `vg_aes_ctr32_to` (`cryptAlG_rel`), and the wipe
loop, if the tag is wrong or its length not allowed, branches only on `len`
(`wipeTo_rel`).

With correctness (`openTo_wp`), `openG c true 4` is `Verified` against
`vg_aes_gcm_open_to`'s contract with its working space as an argument
(`Proof.AesGcm.openToScratchContract`, `openTo_verified`), and so in a frame
of 2608 bytes holding it and copies of the four stack arguments before it
(`openTo_framed`, `openTo_depth`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH ctxCiph)

/-- The entry of `open_to` in two runs, with `work` the stack argument `w`:
the first load gives `work` (public), and the rest is checked by the taint
analysis from it and the argument registers. -/
theorem openEntryTo_rel {w : Nat} (hw : w = 4 ∨ w = 5) {σ₁ σ₂ : State} (T₁ : ToLay σ₁ w) (T₂ : ToLay σ₂ w)
    (qw : stackArg σ₁ w = stackArg σ₂ w) (qsp : σ₁.sp = σ₂.sp)
    (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (.block (openEntryG true w)) TT := by
  have e : openEntryG true w = [.ldrSp .x9 (8 * w)] ++ (openEntryG true w).drop 1 := by
    rcases hw with rfl | rfl <;> rfl
  have hk : 8 * w % 8 = 0 ∧ 8 * w < 32768 := by omega
  have t₁ : ∃ h, (taint.check (Taint.ofRegs []) (.block [.ldrSp .x9 (8 * w)]) h).isSome = true := by
    rcases hw with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have t₂ : ∃ h, (taint.check (Taint.ofRegs [.x9, .x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7])
      (.block ((openEntryG true w).drop 1)) h).isSome = true := by
    rcases hw with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have hW₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 (8 * w)) 64 = stackArg σ₁ w := rfl
  have hW₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 (8 * w)) 64 = stackArg σ₁ w := qw.symm
  rw [e]
  refine RelCT.block_split (rel_seq (rel_taint [] qsp (by agree_tac []) t₁)
    (ldr9_ok hk hW₁ (T₁.hsp w (by omega))) (ldr9_ok hk hW₂ (T₂.hsp w (by omega)))
    fun τ₁ τ₂ ⟨x9₁, g₁, sp₁, _, _⟩ ⟨x9₂, g₂, sp₂, _, _⟩ => ?_)
  refine rel_taint [.x9, .x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] (by rw [sp₁, sp₂, qsp]) ?_ t₂
  intro r hr
  by_cases h9 : r = .x9
  · subst h9; rw [x9₁, x9₂]
  · rw [g₁ r h9, g₂ r h9]
    exact hq r (by simpa only [List.mem_cons, List.not_mem_nil, or_false, h9, false_or] using hr)

/-- `x0` zeroed. -/
theorem imm0_ok (s : State) : WP isa (.block [imm .x0 0]) s fun s' => Regs [.x0] s s' :=
  WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by subst hs'; exact ⟨by others_tac, rfl, rfl, rfl, rfl⟩

/-- The branch of `open_to` when the tag length is not allowed, in two runs:
0 returned, and the output zeroed. -/
theorem failTo_rel {Ctx W SP Np A D O Tg : Addr} {R nl al n tl : Nat} {σ₁ σ₂ s₁ s₂ : State}
    (o₁ : OpenInG true Ctx W SP Np A D O Tg R nl al n tl σ₁ s₁)
    (o₂ : OpenInG true Ctx W SP Np A D O Tg R nl al n tl σ₂ s₂) :
    RelCT isa (Eq2 s₁ s₂) (.seq (.block [imm .x0 0]) (wipeG true)) TT := by
  have t0 : ∃ h, (taint.check (Taint.ofRegs []) (.block [imm .x0 0]) h).isSome = true := ⟨_, by taint_decide⟩
  refine rel_seq (rel_taint [] (by rw [o₁.env.sp, o₂.env.sp]) (by agree_tac []) t0) (imm0_ok s₁) (imm0_ok s₂)
    fun u₁ u₂ r₁ r₂ => ?_
  have q₁ := o₁.of_regs r₁
  have q₂ := o₂.of_regs r₂
  have ou₁ : OutIn Ctx W D O n u₁ := q₁.out
  have ou₂ : OutIn Ctx W D O n u₂ := q₂.out
  exact wipeTo_rel q₁.env q₂.env ou₁.sO ou₂.sO q₁.sN q₂.sN

/-- `vg_aes_gcm_open_to` (`openG c true w`, with `work` the stack argument
`w`: 4, or 5 after the powers) leaks only whether the tag is right. -/
theorem openTo_ctW (v : GcmImpl) {w : Nat} (hw : w = 4 ∨ w = 5) {pre : State → Prop}
    {extra extraW : State → List Region} (hpre : ∀ s, pre s → openToPreXW w (extra s) s (extraW s)) :
    ConstantTime isa pre (fun s₁ s₂ => onePub (w + 1) s₁ s₂ ∧ openToLeakOf s₁ = openToLeakOf s₂)
      (openG v.callees true w) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := hpre _ p₁
  have h₂ := hpre _ p₂
  obtain ⟨hq, hres⟩ := hq
  have T₁ := openToLay h₁
  have T₂ := openToLay h₂
  have hR₁ : rounds (σ₁.gpr .x1) := T₁.rounds
  have hR₂ : rounds (σ₂.gpr .x1) := T₂.rounds
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have qw : stackArg σ₁ w = stackArg σ₂ w := qa w (by omega)
  have qd : stackArg σ₁ 0 = stackArg σ₂ 0 := qa 0 (by omega)
  have qg : stackArg σ₁ 2 = stackArg σ₂ 2 := qa 2 (by omega)
  have qt : stackArg σ₁ 3 = stackArg σ₂ 3 := qa 3 (by omega)
  unfold openG openRestG
  refine rel_seq (openEntryTo_rel hw T₁ T₂ qw qsp (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7]))
    (openEntryTo_ok (by omega) h₁) (openEntryTo_ok (by omega) h₂) fun s₁ s₂ ⟨o₁, x12₁⟩ ⟨o₂, x12₂⟩ => ?_
  rw [← q0, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7, ← qsp, ← qw, ← qd, ← qg, ← qt] at o₂
  rw [← qg] at x12₂
  have hb : (openToRes σ₁).isSome = (openToRes σ₂).isSome := by
    rw [openToLeakOf, openToLeakOf, ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hR₁)),
      ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hR₂))] at hres
    revert hres; cases (openToRes σ₁).isSome <;> cases (openToRes σ₂).isSome <;> simp
  have hr₂ : openToRes σ₂ = Spec.Gcm.openResult (ctxCiph σ₂.mem (σ₁.gpr .x0) (σ₁.gpr .x1).toNat)
      (ctxH σ₂.mem (σ₁.gpr .x0)) (stackArg σ₁ 3).toNat
      (bytesAt σ₂.mem (σ₁.gpr .x2) (σ₁.gpr .x3).toNat) (bytesAt σ₂.mem (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
      (bytesAt σ₂.mem (σ₁.gpr .x4) (σ₁.gpr .x5).toNat) (bytesAt σ₂.mem (stackArg σ₁ 2) (stackArg σ₁ 3).toNat) := by
    unfold openToRes; rw [← q0, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7, ← qt, ← qg]
  rw [hr₂] at hb
  simp only [openToRes] at hb
  exact openRestWithFl_rel (fl := .seq (.block [imm .x0 0]) (wipeG true)) (m := openMainG v.callees true)
    (C₁ := bytesAt σ₁.mem (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
    (F₁ := fun m => bytesAt m (stackArg σ₁ 0) (σ₁.gpr .x7).toNat = List.replicate (σ₁.gpr .x7).toNat 0)
    (C₂ := bytesAt σ₂.mem (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
    (F₂ := fun m => bytesAt m (stackArg σ₁ 0) (σ₁.gpr .x7).toNat = List.replicate (σ₁.gpr .x7).toNat 0)
    o₁ o₂ x12₁ x12₂ (fun o' _ _ hok => failTo_ok o' hok) (fun o' _ _ hok => failTo_ok o' hok)
    (fun p₁ p₂ _ => failTo_rel p₁ p₂) (fun o' hT hok _ => openMainG_post v true o' hT hok)
    (fun o' hT hok _ => openMainG_post v true o' hT hok)
    fun p₁ p₂ rt₁ rt₂ hok _ _ => openMainG_rel v true p₁ p₂ rt₁ rt₂ hok hb

theorem openTo_ct (v : GcmImpl) : ConstantTime isa openToAArch64.pre openToAArch64.pub (openG v.callees true 4) :=
  openTo_ctW v (.inl rfl) (extra := fun _ => []) (extraW := fun _ => []) fun _ h => h

/-! ## `Verified` -/

theorem openTo_keepsV (v : GcmImpl) : (openG v.callees true 4).allInstrs keepsV = true := by
  simp only [openG, openEntryG, openRestG, openMainG, oneCryptG, cryptAlG, crArgsG, crArgs, ctrCallG, crTailG,
    wipeG, wipeLoop, tagLenOk, tagIn, cmpSeg, cmp, cmp16, j0, j0hash, oneAad, absorbAl, decAbs, fo, textAbs,
    finBody, tag, crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, xorB,
    Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Bool.cond_true, Code.allInstrs, v.ctr.keepsV,
    v.ctr.toKeepsV, v.key.keepsV, v.gh.keepsV]
  decide +kernel

theorem openTo_correct (v : GcmImpl) (s : State) (hs : openToAArch64.pre s) :
    ∃ t s', Exec isa (openG v.callees true 4) s t s' ∧ abiPreserved s s' ∧ openToAArch64.post s s' :=
  WP.withPreservedV (openTo_wp v (.inl rfl) hs) (openTo_keepsV v)

/-- `dst` and `tag` at 0 and empty, and `work` at `0x5000` (`[sp + 32]`). -/
def openToSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8021 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 40⟩]
  wr := [⟨0, 0⟩, ⟨0x5000, 2560⟩]

theorem openTo_verified (v : GcmImpl) :
    Verified AArch64.target (openG v.callees true 4) (Proof.AesGcm.openToScratchContract AArch64.abi) :=
  Verified.of_correct (openTo_correct v) (openTo_ct v) (by
    sig_implies [Proof.AesGcm.openToScratchContract, Proof.AesGcm.openToScratchSig, Spec.Gcm.openToPre,
      Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, openToAArch64, openToPreXW, List.append_nil, onePub,
      openToRes, openToPostOf, openToLeakOf, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [openToSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openToSat)

/-- A state satisfying `vg_aes_gcm_open_to`'s precondition, without the
working space: its four other stack arguments. -/
def openToFrameSat : State :=
  { openToSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 32⟩],
                   wr := [⟨0, 0⟩] }

theorem openToFrameSat_pre : ∃ s, (Proof.AesGcm.openToRoundsContract AArch64.abi 2608).pre s := by
  implies_sat [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToPre,
    Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
    AArch64.stackArgAddr, List.getD, List.range, List.range.loop] [openToFrameSat, openToSat, stackArg,
    stackArgAddr, Mem.readW, Mem.read] using openToFrameSat

/-- `open_to` in a frame of 2608 bytes holding its working space and copies of
its four other stack arguments. -/
theorem openTo_framed (v : GcmImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2608 4 (openG v.callees true 4))
      (Proof.AesGcm.openToRoundsContract AArch64.abi 2608) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Gcm.openToSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openToPre AArch64.abi.ptrBits)
    (post := Proof.AesGcm.openToRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2608)
    (leak := some (Spec.Gcm.openToLeak AArch64.abi.ptrBits))
    (openTo_verified v) (by decide) (by decide) (Proof.AesGcm.openToPre_local _)
    (Proof.AesGcm.openToRoundsPostBase_local _) openToFrameSat_pre (hleak := Proof.AesGcm.openToLeakBase_local _)

open VG.Proof.AesGcm.AArch64.Gather in
/-- The frames of `open_to`, in its frame of 2608 bytes, use at most those. -/
theorem openTo_depth (v : GcmImpl) :
    16 * (Impl.StackScratch.AArch64.withStackArgScratch 2608 4 (openG v.callees true 4)).aarch64Depth ≤ 2608 := by
  simp only [Impl.StackScratch.AArch64.withStackArgScratch, openG, openRestG, openMainG, oneCryptG, cryptAlG,
    crArgsG, ctrCallG, crTailG, wipeG, wipeLoop, tagLenOk, tagIn, cmpSeg, cmp, cmp16, j0, j0hash, oneAad,
    absorbAl, decAbs, fo, textAbs, finBody, tag, crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1, absTail, minK,
    copy, copyB, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Bool.cond_true,
    Code.aarch64Depth, Instr.frameUnits, depth_of_noFrames v.ctr.noFrames, depth_of_noFrames v.ctr.toNoFrames,
    depth_of_noFrames v.gh.noFrames]
  decide

end VG.Proof.AesGcm.AArch64
