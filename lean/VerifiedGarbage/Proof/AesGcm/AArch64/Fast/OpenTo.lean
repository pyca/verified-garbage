module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Proof.AesGcm.ScratchOpenTo
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
public import VerifiedGarbage.Proof.AesGcm.AArch64.Open
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
public import VerifiedGarbage.Proof.AesGcm.AArch64.Env
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Open
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Open
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Open
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
public import VerifiedGarbage.Proof.AesGcm.AArch64.OpenToOne
meta import VerifiedGarbage.Proof.AesGcm.AArch64.OpenToOne
import VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.CalleePw
meta import VerifiedGarbage.Proof.AesGcm.AArch64.CalleePw
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.AesGcm.AArch64.Verified
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Verified
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8
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
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc

/-!
# AES-GCM on AArch64: `vg_aes_gcm_open_to` with the path for TLS records

Untrusted: everything here is checked by Lean. `Fast.openWithEG c true w cl`
is `open_to` (`openG c true w`) with `open`'s path for TLS records, decrypting
out of place: its correctness (`openToWithE_wp`, `Fast/Open.lean`) and its
constant time (`openToWithE_ct`) are those of `open`'s path, generic over
`to` (`openRunWithG_postE`, `openRunWithG_relX`), and of `open_to`'s entry,
branch on the tag length and other path (`OpenToOne.lean`).

`Fast.openTo` (`vg_ghash` hashing the whole blocks) and
`Fast.openToWithPw` (`vg_ghash_with_powers`, `pw` the stack argument 4) are
`Verified` against `open_to`'s contracts with the working space as an
argument, and so in a frame of 2608 bytes; `openToCode` and `openToPwCode`
choose them for the implementations with PMULL.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull (MulKey)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH ctxCiph)

/-- `vg_aes_gcm_open_to` with the path for TLS records, its whole blocks
hashed by `cl`, is constant time, for a `cl` that hashes as `vg_ghash` and
leaks the same in two runs, called with memory changed since the entry only
in the working space. -/
theorem openToWithE_ct (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) {w : Nat} (hw : w = 4 ∨ w = 5)
    {pre : State → Prop} {extra extraW : State → List Region}
    (hpre : ∀ s, pre s → openToPreXW w (extra s) s (extraW s))
    (hgh : ∀ {σ s : State} {Y Dd S : Addr} {nb : Nat}, pre σ →
      GhCall s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ w)) →
      s.rd = σ.rd → s.wr = σ.wr → s.sp = σ.sp → Frame [workR (stackArg σ w)] σ.mem s.mem →
      WP isa cl s (GhPost s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (hrel : ∀ {σ₁ σ₂ s₁ s₂ : State} {Y Dd S : Addr} {nb : Nat}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ →
      GhCall s₁ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      GhCall s₂ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ₁ w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ₁ w)) →
      s₁.sp = σ₁.sp → s₂.sp = σ₁.sp → s₁.rd = σ₁.rd → s₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w)] σ₁.mem s₁.mem → s₂.rd = σ₂.rd → s₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w)] σ₂.mem s₂.mem → RelCT isa (Eq2 s₁ s₂) cl TT) :
    ConstantTime isa pre (fun s₁ s₂ => onePub (w + 1) s₁ s₂ ∧ openToLeakOf s₁ = openToLeakOf s₂)
      (Impl.AesGcm.AArch64.Fast.openWithEG v.callees true w cl) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := hpre _ p₁
  have h₂ := hpre _ p₂
  have hq₀ := hq.1
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
  have ka : (Code.block (openEntryG true w) : Prog isa).allInstrs
      (fun i => [Reg.x4, .x5, .x6, .x7].all fun r => !clobbers i r) = true := by
    rcases hw with rfl | rfl <;> decide
  have kc : (Code.block (openEntryG true w) : Prog isa).noCalls = true := by
    rcases hw with rfl | rfl <;> decide
  have kq : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], σ₂.gpr r = σ₁.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact q4.symm
    · exact q5.symm
    · exact q6.symm
    · exact q7.symm
  unfold Impl.AesGcm.AArch64.Fast.openWithEG
  refine rel_seq (openEntryTo_rel hw T₁ T₂ qw qsp (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7]))
    (WP.gprs (rs := [.x4, .x5, .x6, .x7]) (openEntryTo_ok (by omega) h₁) ka kc)
    (WP.gprs (rs := [.x4, .x5, .x6, .x7]) (openEntryTo_ok (by omega) h₂) ka kc)
    fun s₁ s₂ ⟨⟨o₁, x12₁⟩, k₁⟩ ⟨⟨o₂, x12₂⟩, k₂⟩ => ?_
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
  -- The branch on the lengths.
  have k5₁ : s₁.gpr .x5 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat := by rw [k₁ .x5 (by simp), ofNat_toNat']
  have k5₂ : s₂.gpr .x5 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat := by
    rw [k₂ .x5 (by simp), kq .x5 (by simp), ofNat_toNat']
  refine rel_seq (rel_taint [.x5, .x24] (by rw [o₁.env.sp, o₂.env.sp]) (by agree_tac [k5₁, k5₂, o₁.x24, o₂.x24])
      ⟨_, by taint_decide⟩)
    (cond_ok k5₁ (σ₁.gpr .x5).isLt o₁.x24 (σ₁.gpr .x3).isLt) (cond_ok k5₂ (σ₁.gpr .x5).isLt o₂.x24 (σ₁.gpr .x3).isLt)
    fun u₁ u₂ ⟨c₁, r₁⟩ ⟨c₂, r₂⟩ => ?_
  have v₁ := o₁.of_regs r₁
  have v₂ := o₂.of_regs r₂
  have y12₁ : u₁.gpr .x12 = stackArg σ₁ 2 := by rw [r₁.others _ (by decide), x12₁]
  have y12₂ : u₂.gpr .x12 = stackArg σ₁ 2 := by rw [r₂.others _ (by decide), x12₂]
  have kk₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₁.gpr r = σ₁.gpr r := fun r hr => by
    rw [r₁.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), k₁ r hr]
  have kk₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₂.gpr r = σ₁.gpr r := fun r hr => by
    rw [r₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), k₂ r hr, kq r hr]
  have hlt : ((if (σ₁.gpr .x5).toNat ≤ 16 ∧ (σ₁.gpr .x3).toNat = 12 then 0 else 1 : Nat)) < 2 ^ 64 := by
    split <;> decide
  have hgh₂ := @hgh σ₂
  rw [← q0, ← qw] at hgh₂
  refine rel_ite (eval_zero c₁ hlt) (eval_zero c₂ hlt) (fun ht => ?_) (fun _ => ?_)
  · have hc : (σ₁.gpr .x5).toNat ≤ 16 ∧ (σ₁.gpr .x3).toNat = 12 := by
      by_contra hc; simp [hc] at ht
    have regs : ∀ {u t : State}, (∀ r ∈ [Reg.x4, .x5, .x6, .x7], u.gpr r = σ₁.gpr r) →
        (∀ r ∈ [Reg.x4, .x5, .x6, .x7], t.gpr r = u.gpr r) →
        t.gpr .x4 = σ₁.gpr .x4 ∧ t.gpr .x5 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat ∧ t.gpr .x6 = σ₁.gpr .x6 ∧
          t.gpr .x7 = BitVec.ofNat 64 (σ₁.gpr .x7).toNat := fun ku kt =>
      ⟨by rw [kt _ (by simp), ku _ (by simp)], by rw [kt _ (by simp), ku _ (by simp), ofNat_toNat'],
        by rw [kt _ (by simp), ku _ (by simp)], by rw [kt _ (by simp), ku _ (by simp), ofNat_toNat']⟩
    unfold Impl.AesGcm.AArch64.Fast.openFastPG
    exact openRestWithFl_rel (fl := .seq (.block [imm .x0 0]) (wipeG true))
      (m := Impl.AesGcm.AArch64.Fast.openRunWithPG v.callees true cl)
      (C₁ := bytesAt σ₁.mem (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
      (F₁ := fun m => bytesAt m (stackArg σ₁ 0) (σ₁.gpr .x7).toNat = List.replicate (σ₁.gpr .x7).toNat 0)
      (C₂ := bytesAt σ₂.mem (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
      (F₂ := fun m => bytesAt m (stackArg σ₁ 0) (σ₁.gpr .x7).toNat = List.replicate (σ₁.gpr .x7).toNat 0)
      v₁ v₂ y12₁ y12₂ (fun o' _ _ hok => failTo_ok o' hok) (fun o' _ _ hok => failTo_ok o' hok)
      (fun p₁' p₂' _ => failTo_rel p₁' p₂')
      (fun o' hT hok hx => have e := regs kk₁ hx
        openRunWithG_postE cl v hMK (ex := []) o' hc.2 e.1 e.2.1 e.2.2.1 e.2.2.2 hc.1 hT hok (by simp) (by simp)
          (by simp) fun s' _ _ _ _ c sY sS hr hw hsp hf _ => hgh p₁ c sY sS hr hw hsp hf)
      (fun o' hT hok hx => have e := regs kk₂ hx
        openRunWithG_postE cl v hMK (ex := []) o' hc.2 e.1 e.2.1 e.2.2.1 e.2.2.2 hc.1 hT hok (by simp) (by simp)
          (by simp) fun s' _ _ _ _ c sY sS hr hw hsp hf _ => hgh₂ p₂ c sY sS hr hw (hsp.trans qsp) hf)
      fun p₁' p₂' rt₁ rt₂ hok hx₁ hx₂ => openRunWithG_relX v cl hMK (ex := []) (by simp) (by simp) (by simp)
        p₁' p₂' hc.2 (regs kk₁ hx₁) (regs kk₂ hx₂) hc.1 rt₁ rt₂ hok hb
        (fun s' _ _ _ _ c sY sS hr hw hsp hf _ => hgh p₁ c sY sS hr hw hsp hf)
        (fun s' _ _ _ _ c sY sS hr hw hsp hf _ => hgh₂ p₂ c sY sS hr hw (hsp.trans qsp) hf)
        fun c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ _ => hrel p₁ p₂ hq₀ c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂
  · unfold openRestG
    exact openRestWithFl_rel (fl := .seq (.block [imm .x0 0]) (wipeG true)) (m := openMainG v.callees true)
      (C₁ := bytesAt σ₁.mem (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
      (F₁ := fun m => bytesAt m (stackArg σ₁ 0) (σ₁.gpr .x7).toNat = List.replicate (σ₁.gpr .x7).toNat 0)
      (C₂ := bytesAt σ₂.mem (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
      (F₂ := fun m => bytesAt m (stackArg σ₁ 0) (σ₁.gpr .x7).toNat = List.replicate (σ₁.gpr .x7).toNat 0)
      v₁ v₂ y12₁ y12₂ (fun o' _ _ hok => failTo_ok o' hok) (fun o' _ _ hok => failTo_ok o' hok)
      (fun p₁' p₂' _ => failTo_rel p₁' p₂') (fun o' hT hok _ => openMainG_post v true o' hT hok)
      (fun o' hT hok _ => openMainG_post v true o' hT hok)
      fun p₁' p₂' rt₁ rt₂ hok _ _ => openMainG_rel v true p₁' p₂' rt₁ rt₂ hok hb

/-! ## `Fast.openTo`: hashing with `vg_ghash` -/

theorem fastOpenToWithE_keepsV (v : GcmImpl) {w : Nat} (hw : w = 4 ∨ w = 5) {cl : Prog isa}
    (hcl : cl.allInstrs keepsV = true) :
    (Impl.AesGcm.AArch64.Fast.openWithEG v.callees true w cl).allInstrs keepsV = true := by
  rcases hw with rfl | rfl <;>
  simp only [Impl.AesGcm.AArch64.Fast.openWithEG, Impl.AesGcm.AArch64.Fast.openFastPG,
    Impl.AesGcm.AArch64.Fast.openRunWithPG, Impl.AesGcm.AArch64.Fast.oneCryptTG, Impl.AesGcm.AArch64.Fast.front,
    Impl.AesGcm.AArch64.Fast.cond, Impl.AesGcm.AArch64.Fast.padMul, Impl.AesGcm.AArch64.Fast.padMulT,
    openEntryG, openRestG, openMainG, oneCryptG, cryptAlG, crArgsG, ctrCallG, crTailG, wipeG, wipeLoop, crArgs,
    tagLenOk, tagIn, cmpSeg, cmp, cmp16, j0, j0hash, oneAad, absorbAl, decAbs, fo, textAbs, finBody, tag,
    crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, Impl.AesGcm.AArch64.xor,
    padSeg, flush, lens, GcmImpl.callees, Bool.cond_true, Code.allInstrs, v.ctr.keepsV, v.ctr.toKeepsV,
    v.gh.keepsV, hcl] <;>
  decide +kernel

open VG.Proof.AesGcm.AArch64.Gather in
/-- `openWithEG c true w` has no frames of its own. -/
theorem fastOpenToWithE_depth0 (v : GcmImpl) {w : Nat} (hw : w = 4 ∨ w = 5) {cl : Prog isa}
    (hcl : cl.aarch64Depth = 0) :
    (Impl.AesGcm.AArch64.Fast.openWithEG v.callees true w cl).aarch64Depth = 0 := by
  rcases hw with rfl | rfl <;>
  simp only [Impl.AesGcm.AArch64.Fast.openWithEG, Impl.AesGcm.AArch64.Fast.openFastPG,
    Impl.AesGcm.AArch64.Fast.openRunWithPG, Impl.AesGcm.AArch64.Fast.oneCryptTG, Impl.AesGcm.AArch64.Fast.front,
    Impl.AesGcm.AArch64.Fast.cond, Impl.AesGcm.AArch64.Fast.padMul, Impl.AesGcm.AArch64.Fast.padMulT,
    openEntryG, openRestG, openMainG, oneCryptG, cryptAlG, crArgsG, ctrCallG, crTailG, wipeG, wipeLoop, crArgs,
    tagLenOk, tagIn, cmpSeg, cmp, cmp16, j0, j0hash, oneAad, absorbAl, decAbs, fo, textAbs, finBody, tag,
    crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, Impl.AesGcm.AArch64.xor,
    padSeg, flush, lens, GcmImpl.callees, Bool.cond_true, Code.aarch64Depth, depth_of_noFrames v.ctr.noFrames,
    depth_of_noFrames v.ctr.toNoFrames, depth_of_noFrames v.gh.noFrames, hcl] <;> decide

section
variable (v : GcmImpl) (hMK : MulKey)
include hMK

theorem fastOpenTo_correct (s : State) (hs : openToAArch64.pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Fast.openTo v.callees) s t s' ∧ abiPreserved s s' ∧
      openToAArch64.post s s' :=
  WP.withPreservedV (openToWithE_wp (w := 4) _ v hMK (.inl rfl) hs
      fun _ _ _ _ _ hc _ _ _ _ _ _ => gh_call v.gh hc)
    (fastOpenToWithE_keepsV v (.inl rfl) (by simp only [Code.allInstrs, GcmImpl.callees, v.gh.keepsV]))

theorem fastOpenTo_ct :
    ConstantTime isa openToAArch64.pre openToAArch64.pub (Impl.AesGcm.AArch64.Fast.openTo v.callees) :=
  openToWithE_ct (w := 4) v _ hMK (.inl rfl) (extra := fun _ => []) (extraW := fun _ => []) (fun _ h => h)
    (fun _ hc _ _ _ _ _ _ => gh_call v.gh hc)
    fun _ _ _ c₁ c₂ _ _ sp₁ sp₂ _ _ _ _ _ _ => rel_gh v.gh c₁ c₂ (sp₁.trans sp₂.symm)

theorem fastOpenTo_verified :
    Verified AArch64.target (Impl.AesGcm.AArch64.Fast.openTo v.callees)
      (Proof.AesGcm.openToScratchContract AArch64.abi) :=
  Verified.of_correct (fastOpenTo_correct v hMK) (fastOpenTo_ct v hMK) (by
    sig_implies [Proof.AesGcm.openToScratchContract, Proof.AesGcm.openToScratchSig, Spec.Gcm.openToPre,
      Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, openToAArch64, openToPreXW, List.append_nil, onePub,
      openToRes, openToPostOf, openToLeakOf, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [openToSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openToSat)

/-- `Fast.openTo` in a frame of 2608 bytes holding its working space and
copies of its four other stack arguments. -/
theorem fastOpenTo_framed :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2608 4 (Impl.AesGcm.AArch64.Fast.openTo v.callees))
      (Proof.AesGcm.openToRoundsContract AArch64.abi 2608) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Gcm.openToSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openToPre AArch64.abi.ptrBits)
    (post := Proof.AesGcm.openToRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2608)
    (leak := some (Spec.Gcm.openToLeak AArch64.abi.ptrBits))
    (fastOpenTo_verified v hMK) (by decide) (by decide) (Proof.AesGcm.openToPre_local _)
    (Proof.AesGcm.openToRoundsPostBase_local _) openToFrameSat_pre (hleak := Proof.AesGcm.openToLeakBase_local _)

end

open VG.Proof.AesGcm.AArch64.Gather in
/-- The frames of `Fast.openTo`, in its frame of 2608 bytes, use at most those. -/
theorem fastOpenTo_depth (v : GcmImpl) :
    16 * (Impl.StackScratch.AArch64.withStackArgScratch 2608 4
      (Impl.AesGcm.AArch64.Fast.openTo v.callees)).aarch64Depth ≤ 2608 := by
  simp only [Impl.StackScratch.AArch64.withStackArgScratch, Impl.AesGcm.AArch64.Fast.openTo, Code.aarch64Depth,
    Instr.frameUnits, fastOpenToWithE_depth0 v (.inl rfl) (cl := .call v.callees.gh.name v.callees.gh.code)
      (by simp only [Code.aarch64Depth, GcmImpl.callees, depth_of_noFrames v.gh.noFrames])]
  decide

/-! ## `Fast.openToWithPw`: with the powers in their own buffer

`vg_aes_gcm_open_to_with_powers` takes `pw` as the stack argument 4, so
`work` is the stack argument 5; on the path for TLS records its whole blocks
are hashed by `vg_ghash_with_powers`, called with `pw` loaded from
`[sp + 32]` (`Fast.pwSel 32`). The call reads `pw`, which nothing before it
writes: out of place, only the working space is written before the call. -/

/-- The powers' buffer, the stack argument 4. -/
abbrev pwRT (s : State) : Region := ⟨stackArg s 4, 128⟩

/-- What `vg_aes_gcm_open_to_with_powers` needs, on the regions its proofs
run on: `openToPreXW 5`, with `pw` readable, apart from the working space,
and holding the powers of the hash subkey. -/
def openToPwN (s : State) : Prop :=
  openToPreXW 5 [pwRT s] s ∧ (pwRT s).Disjoint ⟨stackArg s 5, 2560⟩ ∧
    Spec.Gcm.Powers8Repr s.mem (stackArg s 4) (Spec.Gcm.ctxH s.mem (s.gpr .x0))

/-- What `vg_aes_gcm_open_to_with_powers` needs: `openToPreXW 5`, with `pw`
readable before the stack arguments, holding the powers. -/
def openToPwW (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let src : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let dst : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let tag : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
  let pw : Region := pwRT s
  let work : Region := ⟨stackArg s 5, 2560⟩
  s.rd = [ctx, nonce, aad, src, tag, pw, args s 6] ∧ s.wr = [dst, work] ∧
    ctx.Disjoint dst ∧ ctx.Disjoint work ∧ nonce.Disjoint dst ∧ nonce.Disjoint work ∧
    aad.Disjoint dst ∧ aad.Disjoint work ∧ src.Disjoint dst ∧ src.Disjoint work ∧
    dst.Disjoint tag ∧ dst.Disjoint work ∧ dst.Disjoint (args s 6) ∧
    tag.Disjoint work ∧ work.Disjoint (args s 6) ∧ pw.Disjoint work ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
    (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
    (stackArg s 5).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 * 6 ≤ 2 ^ 64 ∧ rounds (s.gpr .x1) ∧
    (stackArg s 1).toNat = (s.gpr .x7).toNat ∧
    Spec.Gcm.Powers8Repr s.mem (stackArg s 4) (Spec.Gcm.ctxH s.mem (s.gpr .x0))

/-- `vg_aes_gcm_open_to_with_powers`. -/
def openToPwAArch64 : Contract isa where
  pre := openToPwW
  post := openToPostOf
  pub s₁ s₂ := onePub 6 s₁ s₂ ∧ openToLeakOf s₁ = openToLeakOf s₂

/-- At the call, with memory changed since the entry only in the working
space: `pw` is at `[sp + 32]`, readable, apart from the accumulator and the
working space of the call, and holds the powers. -/
theorem gwCallTo_of {σ s : State} {Y S : Addr} (hs : openToPwN σ)
    (sY : Region.Sub ⟨Y, 16⟩ (workR (stackArg σ 5))) (sS : Region.Sub ⟨S, 256⟩ (workR (stackArg σ 5)))
    (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr) (hsp : s.sp = σ.sp)
    (hf : Frame [workR (stackArg σ 5)] σ.mem s.mem) :
    s.mem.readW (s.sp + BitVec.ofNat 64 32) 64 = stackArg σ 4 ∧
      InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 32) 8 ∧
      GhWCall s (σ.gpr .x0) Y S (stackArg σ 4) := by
  obtain ⟨hpx, pw, rep⟩ := hs
  have T := openToLay hpx
  have hrd₀ := hpx.1
  have hspA := T.hsp 4 (by decide)
  have sA : Region.Sub ⟨σ.sp + BitVec.ofNat 64 32, 8⟩ (args σ 6) := by
    show Region.Sub ⟨σ.sp + BitVec.ofNat 64 32, 8⟩ ⟨σ.sp + BitVec.ofNat 64 (8 * 0), 8 * 6⟩
    rw [show σ.sp + BitVec.ofNat 64 (8 * 0) = σ.sp by rw [Nat.mul_zero, BitVec.add_zero]]
    exact Offset.sub_base _ (by decide)
  have kW : ∀ {X : Region}, X.Disjoint (workR (stackArg σ 5)) →
      ∀ r ∈ [workR (stackArg σ 5)], X.Disjoint r := fun hX r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hX
  refine ⟨?_, by rw [hrd, hwr, hsp]; exact hspA, ⟨?_, (pw.sub_right sY).symm, (pw.sub_right sS).symm, ?_⟩⟩
  · rw [hsp, hf.readW (r := ⟨σ.sp + BitVec.ofNat 64 32, 8⟩) (Region.contains_self _ _)
      (kW (T.args.sub_left sA)) (by decide)]
    rfl
  · refine Covers.left (Covers.of_mem fun r hr => ?_)
    simp only [List.mem_singleton] at hr
    subst hr
    rw [hrd, hrd₀]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · have hH : Spec.Gcm.blockAt s.mem (σ.gpr .x0 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH σ.mem (σ.gpr .x0) :=
      blockAt_frame hf (kW (T.dcW.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))))
    rw [hH]
    exact Proof.AesGcm.powers8Repr_congr (fun i hi => hf.bytes (R := pwRT σ) (kW pw)
      (show 128 ≤ 2 ^ 64 by decide) hi) rep

section
variable (v : GcmImpl) (g : GhashWithImpl) (hMK : MulKey)
include hMK

theorem openToPw_correctN (s : State) (hs : openToPwN s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Fast.openToWithPw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      openToPostOf s s' :=
  WP.withPreservedV (openToWithE_wp (w := 5) _ v hMK (.inr rfl) hs.1 fun _ _ _ _ _ hc sY sS hrd hwr hsp hf =>
      have q := gwCallTo_of hs sY sS hrd hwr hsp hf
      pwSel_call v g (k := 32) (by decide) q.1 q.2.1 hc q.2.2)
    (fastOpenToWithE_keepsV v (.inr rfl) (pwSel_keepsV v g (.inr (.inr rfl))))

theorem openToPw_ctN :
    ConstantTime isa openToPwN (fun s₁ s₂ => onePub 6 s₁ s₂ ∧ openToLeakOf s₁ = openToLeakOf s₂)
      (Impl.AesGcm.AArch64.Fast.openToWithPw v.callees g.fn) :=
  openToWithE_ct (w := 5) v _ hMK (.inr rfl) (extra := fun s => [pwRT s]) (extraW := fun _ => [])
    (fun _ h => h.1)
    (fun p hc sY sS hrd hwr hsp hf =>
      have q := gwCallTo_of p sY sS hrd hwr hsp hf
      pwSel_call v g (k := 32) (by decide) q.1 q.2.1 hc q.2.2)
    fun {σ₁ σ₂ s₁ s₂ _ _ _ _} p₁ p₂ hq c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ => by
      obtain ⟨q0, -, -, -, -, -, -, -, qsp, qa⟩ := hq
      have e5 : stackArg σ₁ 5 = stackArg σ₂ 5 := qa 5 (by decide)
      have e4 : stackArg σ₁ 4 = stackArg σ₂ 4 := qa 4 (by decide)
      obtain ⟨hP₁, hs₁, k₁⟩ := gwCallTo_of p₁ sY sS r₁ w₁ sp₁ f₁
      obtain ⟨hP₂, hs₂, k₂⟩ := gwCallTo_of p₂ (by rw [← e5]; exact sY) (by rw [← e5]; exact sS) r₂ w₂
        (sp₂.trans qsp) (by rw [← e5]; exact f₂)
      rw [← e4] at hP₂ k₂
      rw [← q0] at k₂
      exact pwSel_rel v g (.inr (.inr rfl)) hP₁ hs₁ hP₂ hs₂ c₁ k₁ c₂ k₂ (sp₁.trans sp₂.symm)

end

/-- The readable regions of the proofs: `pw` after the stack arguments. -/
def narrowRdPT (s : State) : List Region :=
  [⟨s.gpr .x0, 256⟩, ⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x4, (s.gpr .x5).toNat⟩,
    ⟨s.gpr .x6, (s.gpr .x7).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩, args s 6, pwRT s]

/-- `s` with the readable regions of the proofs. -/
def narrowPT (s : State) : State := s.withRegions (narrowRdPT s) s.wr

theorem narrowPT_pre {s : State} (h : openToPwW s) : openToPwN (narrowPT s) := by
  obtain ⟨-, hwr, cd, cw, nd, nw, ad, aw, sd, sw, dt, dw, da, tw, wa, pw, b0, b2, b4, b6, bd, bt, b1, bsp, hr,
    hl, rep⟩ := h
  exact ⟨⟨rfl, hwr, cd, cw, nd, nw, ad, aw, sd, sw, dt, dw, da, tw, wa, b0, b2, b4, b6, bd, bt, b1, bsp, hr, hl⟩,
    pw, rep⟩

theorem narrowPT_covers {s : State} (h : openToPwW s) :
    Covers ((narrowPT s).rd ++ (narrowPT s).wr) (s.rd ++ s.wr) := by
  rw [show (narrowPT s).rd = narrowRdPT s from rfl, show (narrowPT s).wr = s.wr from rfl, h.1]
  refine Covers.append (Covers.of_mem fun r hr => ?_) (Covers.refl _)
  simp only [narrowRdPT, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem narrowPT_exec {c : Prog isa} {s s₁ : State} {t : List Leak} (h : openToPwW s)
    (he : Exec isa c (narrowPT s) t s₁) : Exec isa c s t (s₁.withRegions s.rd s.wr) := by
  have := Exec.widen he (narrowPT_covers h) (Covers.refl _)
  rwa [show (narrowPT s).withRegions s.rd s.wr = s from rfl] at this

/-- A state satisfying `vg_aes_gcm_open_to_with_powers`'s precondition:
`openToSat` with `pw` at `0x6000` (`[sp + 32]`) and `work` at `0x5000`
(`[sp + 40]`). -/
def openToSatPw : State :=
  { openToSat with
    mem := fun a => if a = 0x8029 then 0x50 else if a = 0x8021 then 0x60 else 0
    rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0, 0⟩, ⟨0x6000, 128⟩, ⟨0x8000, 48⟩] }

/-- `pw`'s bytes in `openToSatPw` are zero. -/
theorem openToSatPw_zero : ∀ i < 16 * 8, openToSatPw.mem (stackArg openToSatPw 4 + BitVec.ofNat 64 i) = 0 := by
  intro i hi
  have hP : stackArg openToSatPw 4 = 0x6000 := by decide
  rw [hP]
  show (if (0x6000 : BitVec 64) + BitVec.ofNat 64 i = 0x8029 then 0x50
    else if (0x6000 : BitVec 64) + BitVec.ofNat 64 i = 0x8021 then 0x60 else 0) = 0
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by bv_omega)), ite_eq_right_of_eq_false _ _ (eq_false (by bv_omega))]

section
variable (v : GcmImpl) (g : GhashWithImpl) (hMK : MulKey)
include hMK

theorem openToPw_correct (s : State) (hs : openToPwAArch64.pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Fast.openToWithPw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      openToPwAArch64.post s s' := by
  obtain ⟨t, s₁, he, ha, hp⟩ := openToPw_correctN v g hMK _ (narrowPT_pre hs)
  exact ⟨t, _, narrowPT_exec hs he, ha, hp⟩

theorem openToPw_ct :
    ConstantTime isa openToPwAArch64.pre openToPwAArch64.pub
      (Impl.AesGcm.AArch64.Fast.openToWithPw v.callees g.fn) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨u₁, r₁, f₁, -⟩ := openToPw_correctN v g hMK _ (narrowPT_pre h₁)
  obtain ⟨u₂, r₂, f₂, -⟩ := openToPw_correctN v g hMK _ (narrowPT_pre h₂)
  rw [(Exec.det e₁ (narrowPT_exec h₁ f₁)).1, (Exec.det e₂ (narrowPT_exec h₂ f₂)).1]
  exact openToPw_ctN v g hMK _ _ _ _ _ _ (narrowPT_pre h₁) (narrowPT_pre h₂) hq f₁ f₂

theorem openToPw_verified :
    Verified AArch64.target (Impl.AesGcm.AArch64.Fast.openToWithPw v.callees g.fn)
      (Proof.AesGcm.openToWithPowersScratchContract AArch64.abi) :=
  Verified.of_correct (openToPw_correct v g hMK) (openToPw_ct v g hMK)
    { pre := by
        sig_implies_pre [Proof.AesGcm.openToWithPowersScratchContract, Proof.AesGcm.openToWithPowersScratchSig,
          Spec.Gcm.openToWithPowersPre, Spec.Gcm.openToPre, Proof.AesGcm.openToWithPowersRoundsPost,
          Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToWithPowersLeak, Spec.Gcm.openToLeak, openToPwAArch64,
          openToPwW, pwRT, onePub, openToRes, openToPostOf, openToLeakOf, args, rounds, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        sig_implies_post [Proof.AesGcm.openToWithPowersScratchContract, Proof.AesGcm.openToWithPowersScratchSig,
          Spec.Gcm.openToWithPowersPre, Spec.Gcm.openToPre, Proof.AesGcm.openToWithPowersRoundsPost,
          Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToWithPowersLeak, Spec.Gcm.openToLeak, openToPwAArch64,
          openToPwW, pwRT, onePub, openToRes, openToPostOf, openToLeakOf, args, rounds, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      pub := by
        sig_implies_pub [Proof.AesGcm.openToWithPowersScratchContract, Proof.AesGcm.openToWithPowersScratchSig,
          Spec.Gcm.openToWithPowersPre, Spec.Gcm.openToPre, Proof.AesGcm.openToWithPowersRoundsPost,
          Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToWithPowersLeak, Spec.Gcm.openToLeak, openToPwAArch64,
          openToPwW, pwRT, onePub, openToRes, openToPostOf, openToLeakOf, args, rounds, AArch64.abi,
          AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
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

/-- `openToSatPw` with its stack arguments `dst`, `dst_len`, `tag`,
`tag_len` and `pw` only. -/
def openToFrameSatPw : State :=
  { openToSatPw with
    rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0, 0⟩, ⟨0x6000, 128⟩, ⟨0x8000, 40⟩],
    wr := [⟨0, 0⟩] }

theorem openToFrameSatPw_pre :
    ∃ s, (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi 2608).pre s := by
  refine ⟨openToFrameSatPw, ?_⟩
  sig_pre [Proof.AesGcm.openToWithPowersRoundsContract, Spec.Gcm.openToWithPowersSig, Spec.Gcm.openToSig,
    Spec.Gcm.withPowersParam, Spec.Gcm.openToWithPowersPre, Spec.Gcm.openToPre,
    Proof.AesGcm.openToWithPowersRoundsPost, Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToWithPowersLeak,
    Spec.Gcm.openToLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD,
    List.range, List.range.loop, List.cons_append, List.nil_append, openToFrameSatPw, openToSatPw, openToSat,
    stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.powers8Repr_of_zeroMem (by decide) openToSatPw_zero

/-- `Fast.openToWithPw` in a frame of 2608 bytes holding its working space and
copies of its five other stack arguments. -/
theorem openToPw_framed (v : GcmImpl) (g : GhashWithImpl) (hMK : MulKey) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2608 5
        (Impl.AesGcm.AArch64.Fast.openToWithPw v.callees g.fn))
      (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi 2608) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Gcm.openToWithPowersSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openToWithPowersPre AArch64.abi.ptrBits)
    (post := Proof.AesGcm.openToWithPowersRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2608) (leak := some (Spec.Gcm.openToWithPowersLeak AArch64.abi.ptrBits))
    (openToPw_verified v g hMK) (by decide) (by decide) (Proof.AesGcm.openToWithPowersPre_local _)
    (Proof.AesGcm.openToWithPowersPost_local _) openToFrameSatPw_pre
    (hleak := Proof.AesGcm.openToWithPowersLeak_local _)

open VG.Proof.AesGcm.AArch64.Gather in
/-- The frames of `Fast.openToWithPw`, in its frame of 2608 bytes, use at
most those. -/
theorem openToPw_depth (v : GcmImpl) (g : GhashWithImpl) :
    16 * (Impl.StackScratch.AArch64.withStackArgScratch 2608 5
      (Impl.AesGcm.AArch64.Fast.openToWithPw v.callees g.fn)).aarch64Depth ≤ 2608 := by
  simp only [Impl.StackScratch.AArch64.withStackArgScratch, Impl.AesGcm.AArch64.Fast.openToWithPw,
    Code.aarch64Depth, Instr.frameUnits, fastOpenToWithE_depth0 v (.inr rfl)
      (cl := Impl.AesGcm.AArch64.Fast.pwSel v.callees 32 g.fn)
      (by simp only [Impl.AesGcm.AArch64.Fast.pwSel, Impl.AesGcm.AArch64.Fast.pwCall, Code.aarch64Depth,
        GcmImpl.callees, depth_of_noFrames v.gh.noFrames, depth_of_noFrames g.noFrames]; decide)]
  decide

/-! ## The code chosen per implementation -/

end VG.Proof.AesGcm.AArch64.Fast

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64

/-- `vg_aes_gcm_open_to` for the implementations `v`: with the path for TLS
records where PMULL is there (`GhashImpl.pmull`), as `openCode`. -/
def openToCode (v : GcmImpl) : Prog isa :=
  if v.gh.pmull then Impl.AesGcm.AArch64.Fast.openTo v.callees else openG v.callees true 4

theorem openToCode_framed (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 2608 4 (openToCode v))
      (Proof.AesGcm.openToRoundsContract AArch64.abi 2608) := by
  unfold openToCode
  split
  · exact Fast.fastOpenTo_framed v hMK
  · exact openTo_framed v

theorem openToCode_depth (v : GcmImpl) :
    16 * (Impl.StackScratch.AArch64.withStackArgScratch 2608 4 (openToCode v)).aarch64Depth ≤ 2608 := by
  unfold openToCode
  split
  · exact Fast.fastOpenTo_depth v
  · exact openTo_depth v

/-- `vg_aes_gcm_open_to_with_powers` for the implementations `v` with
`vg_ghash_with_powers` (`g`), which have PMULL: the path for TLS records,
calling `g`, as `vg_aes_gcm_open_with_powers` (`openPwCode`) for those
without the interleaved loops. -/
def openToPwCode (v : GcmImpl) (g : GhashWithImpl) : Prog isa :=
  Impl.AesGcm.AArch64.Fast.openToWithPw v.callees g.fn

theorem openToPwCode_framed (v : GcmImpl) (g : GhashWithImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 2608 5 (openToPwCode v g))
      (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi 2608) :=
  Fast.openToPw_framed v g hMK

theorem openToPwCode_depth (v : GcmImpl) (g : GhashWithImpl) :
    16 * (Impl.StackScratch.AArch64.withStackArgScratch 2608 5 (openToPwCode v g)).aarch64Depth ≤ 2608 :=
  Fast.openToPw_depth v g

end VG.Proof.AesGcm.AArch64
