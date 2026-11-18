module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Callee
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Contract
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Save
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Tag
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Flush
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.AesGcm.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.OneCT
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.FinCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.StreamVerify
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Sm4Gcm.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Rel
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Callee
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Contract
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Rel
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Env
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Save
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.OneCT
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Cmp
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Cmp
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.FinCT
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.BodyCT
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.BodyCT
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.StreamVerify
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Body
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Gcm.Bits

/-! ### `Sm4Gcm.AArch64.OpenCT`, which only this module used -/

section

/-! ### `Sm4Gcm.AArch64.SealCT`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on AArch64: `vg_sm4_gcm_seal` is constant time

Untrusted: everything here is checked by Lean. The entry by `entry_rel`,
`j0` and the additional data by `front_rel`, the text by `encBody_rel` and
the tag by `finBody_rel`; the blocks between them by the taint analysis, with
`tag`, which the code loads from memory, public in both runs.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- What `oneCore` gives, with the values of the first run. -/
structure OneFacts (σ σ₀ : State) (n w : Nat) : Prop where
  ol : OneLay σ₀ n w
  hW : stackArg σ w = stackArg σ₀ w
  perm : Perm (σ₀.gpr .x0) (stackArg σ₀ w + BitVec.ofNat 64 16) (stackArg σ₀ w) σ
  hsp : ∀ i < n, InRegions (σ.rd ++ σ.wr) (σ.sp + BitVec.ofNat 64 (8 * i)) 8
  nonceR : Covers [⟨σ₀.gpr .x1, (σ₀.gpr .x2).toNat⟩] (σ.rd ++ σ.wr)
  aadR : Covers [⟨σ₀.gpr .x3, (σ₀.gpr .x4).toNat⟩] (σ.rd ++ σ.wr)
  dataW : Covers [⟨σ₀.gpr .x5, (σ₀.gpr .x6).toNat⟩] σ.wr
  args : (args σ n).Disjoint (workR (stackArg σ₀ w))

theorem oneFacts {σ₁ σ₂ : State} {n w : Nat} (hw : w < n) (h₁ : oneCore n w σ₁) (h₂ : oneCore n w σ₂)
    (hq : onePub n σ₁ σ₂) : OneFacts σ₁ σ₁ n w ∧ OneFacts σ₂ σ₁ n w := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, -, -, qa⟩ := hq
  obtain qw : stackArg σ₁ w = stackArg σ₂ w := qa w hw
  obtain o₁ := oneLay h₁
  obtain o₂ := oneLay h₂
  refine ⟨⟨o₁, rfl, o₁.perm, o₁.hsp, o₁.nonceR, o₁.aadR, o₁.dataW, o₁.args⟩,
    ⟨o₁, qw.symm, ?_, o₂.hsp, ?_, ?_, ?_, ?_⟩⟩
  · have := o₂.perm; rw [← q0, ← qw] at this; exact this
  · have := o₂.nonceR; rw [← q1, ← q2] at this; exact this
  · have := o₂.aadR; rw [← q3, ← q4] at this; exact this
  · have := o₂.dataW; rw [← q5, ← q6] at this; exact this
  · have := o₂.args; rw [← qw] at this; exact this

/-- What the entry of `seal` and `open` leaves in a run from `σ`, with the
values of the first run `σ₀`. -/
abbrev Entered (w : Nat) (σ σ₀ τ : State) : Prop :=
  Env (σ₀.gpr .x0) (stackArg σ₀ w + BitVec.ofNat 64 16) (stackArg σ₀ w) σ.sp τ ∧
    τ.gpr .x23 = σ.gpr .x1 ∧ τ.gpr .x24 = σ.gpr .x2 ∧ τ.gpr .x26 = σ.gpr .x2 ∧ τ.gpr .x27 = 0 ∧
    τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 216) 64 = σ.gpr .x3 ∧
    τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 224) 64 = σ.gpr .x4 ∧
    τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 232) 64 = σ.gpr .x5 ∧
    τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 240) 64 = σ.gpr .x6

/-- `FrontIn` after the entry. -/
theorem frontIn_of {σ σ₀ τ : State} {n w : Nat} (f : OneFacts σ σ₀ n w)
    (h1 : σ.gpr .x1 = σ₀.gpr .x1) (h2 : σ.gpr .x2 = σ₀.gpr .x2) (h3 : σ.gpr .x3 = σ₀.gpr .x3)
    (h4 : σ.gpr .x4 = σ₀.gpr .x4) (h5 : σ.gpr .x5 = σ₀.gpr .x5) (h6 : σ.gpr .x6 = σ₀.gpr .x6)
    (a : Entered w σ σ₀ τ) (rd : τ.rd = σ.rd) (wr : τ.wr = σ.wr) :
    FrontIn (σ₀.gpr .x0) (stackArg σ₀ w + BitVec.ofNat 64 16) (stackArg σ₀ w) σ.sp τ.gpr (σ₀.gpr .x1)
      (σ₀.gpr .x3) (σ₀.gpr .x5) (σ₀.gpr .x2).toNat (σ₀.gpr .x4).toNat (σ₀.gpr .x6).toNat τ := by
  obtain ⟨he, x23, x24, x26, x27, s1, s2, s3, s4⟩ := a
  obtain sub16 : Region.Sub ⟨stackArg σ₀ w + BitVec.ofNat 64 16, 80⟩ (workR (stackArg σ₀ w)) := Lay.wSub (by decide)
  exact ⟨he, fun _ _ => rfl, by rw [x23, h1], by rw [x24, h2, ofNat_toNat'], by rw [x26, h2, ofNat_toNat'], x27,
    ⟨by rw [rd, wr]; exact f.nonceR, (σ₀.gpr .x2).isLt, f.ol.nw, f.ol.nonce.sub_right sub16, f.ol.nonce⟩,
    ⟨by rw [rd, wr]; exact f.aadR, (σ₀.gpr .x4).isLt, f.ol.aw, f.ol.aad.sub_right sub16, f.ol.aad⟩,
    by rw [s1, h3], by rw [s2, h4, ofNat_toNat'], by rw [s3, h5], by rw [s4, h6, ofNat_toNat']⟩

/-- `Entered`, from `SealEntry`. -/
theorem SealEntry.entered {σ σ₀ τ : State} (a : SealEntry σ τ) (h0 : σ.gpr .x0 = σ₀.gpr .x0)
    (hW : stackArg σ 0 = stackArg σ₀ 0) : Entered 0 σ σ₀ τ := by
  have he := a.env
  have sA := a.sA
  have sL := a.sL
  have sD := a.sD
  have sN := a.sN
  rw [h0, hW] at he
  rw [hW] at sA sL sD sN
  exact ⟨he, a.x23, a.x24, a.x26, a.x27, sA, sL, sD, sN⟩

/-- The entry of `seal` in two runs. -/
theorem sealEntry_rel {σ₁ σ₂ : State} (f₁ : OneFacts σ₁ σ₁ 1 0) (f₂ : OneFacts σ₂ σ₁ 1 0) (qsp : σ₁.sp = σ₂.sp)
    (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6], σ₁.gpr r = σ₂.gpr r) (q7 : σ₁.gpr .x7 = σ₂.gpr .x7) :
    RelCT isa (Eq2 σ₁ σ₂) (.block (oneEntry 0 ++ ([.str .x .x7 .x19 tlO, mov .x28 .x7] : List Instr))) TT := by
  have hW₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 0) 64 = stackArg σ₁ 0 := rfl
  have hW₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 0) 64 = stackArg σ₁ 0 := f₂.hW
  obtain ts : ∃ h, (taint.check (Taint.ofRegs [.x19, .x7])
      (.block [.str .x .x7 .x19 tlO, mov .x28 .x7]) h).isSome = true := ⟨_, by taint_decide⟩
  refine RelCT.block_split (rel_seq (entry_rel (.inl rfl) hW₁ hW₂ (f₁.hsp 0 (by decide)) (f₂.hsp 0 (by decide))
      f₁.perm.w f₂.perm.w qsp hq)
    (oneEntry_ok (by decide) hW₁ (f₁.hsp 0 (by decide)) rfl f₁.perm)
    (oneEntry_ok (by decide) hW₂ (f₂.hsp 0 (by decide)) (hq .x0 (by simp)).symm f₂.perm)
    fun τ₁ τ₂ a₁ a₂ => rel_taint [.x19, .x7] (by rw [a₁.1.sp, a₂.1.sp, qsp])
      (by agree_tac [a₁.1.x19, a₂.1.x19, a₁.2.2.2.2.2.1, a₂.2.2.2.2.2.1, q7]) ts)

/-- `seal` after its entry, in two runs. -/
theorem sealRest_rel (v : GcmImpl) {σ₁ σ₂ τ₁ τ₂ : State} (h₁ : sealPre σ₁) (h₂ : sealPre σ₂)
    (hq : onePub 1 σ₁ σ₂) (a₁ : SealEntry σ₁ τ₁) (a₂ : SealEntry σ₂ τ₂) :
    RelCT isa (Eq2 τ₁ τ₂) (sealRest v.callees) TT := by
  unfold sealRest
  obtain ⟨f₁, f₂⟩ := oneFacts (by decide : 0 < 1) (sealCore h₁) (sealCore h₂) hq
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, -⟩ := hq
  have L := f₁.ol.lay
  obtain i₁ := frontIn_of f₁ rfl rfl rfl rfl rfl rfl (a₁.entered rfl rfl) a₁.rd a₁.wr
  obtain i₂ := frontIn_of f₂ q1.symm q2.symm q3.symm q4.symm q5.symm q6.symm (a₂.entered q0.symm f₂.hW) a₂.rd a₂.wr
  rw [← qsp] at i₂
  have s2₁ := a₁.sL
  have s4₁ := a₁.sN
  have s5₁ := a₁.sT
  have s2₂ := a₂.sL
  have s4₂ := a₂.sN
  have s5₂ := a₂.sT
  rw [f₂.hW] at s2₂ s4₂ s5₂
  rw [← q4] at s2₂
  rw [← q6] at s4₂
  rw [← q7] at s5₂
  have ol := f₁.ol
  obtain sub16 : Region.Sub ⟨stackArg σ₁ 0 + BitVec.ofNat 64 16, 80⟩ (workR (stackArg σ₁ 0)) := Lay.wSub (by decide)
  obtain hal := (σ₁.gpr .x4).isLt
  obtain hn := (σ₁.gpr .x6).isLt
  refine front_rel L v i₁ i₂ fun u₁ u₂ o₁ o₂ => ?_
  obtain mkB : ∀ {σ τ u : State}, OneFacts σ σ₁ 1 0 → τ.wr = σ.wr →
      FrontOut (σ₁.gpr .x0) (stackArg σ₁ 0 + BitVec.ofNat 64 16) (stackArg σ₁ 0) σ₁.sp τ.gpr (σ₁.gpr .x5)
        (σ₁.gpr .x4).toNat (σ₁.gpr .x6).toNat τ u →
      BodyIn (σ₁.gpr .x0) (stackArg σ₁ 0 + BitVec.ofNat 64 16) (stackArg σ₁ 0) σ₁.sp u.gpr
        (σ₁.gpr .x6).toNat 0 (σ₁.gpr .x5) (Spec.Gcm.zeros (σ₁.gpr .x4).toNat) []
        (blockAt u.mem (σ₁.gpr .x0 + BitVec.ofNat 64 240)) u := fun f wr o =>
    ⟨o.env, fun _ _ => rfl, by rw [o.x25, Proof.Gcm.length_zeros],
      o.x26, o.x27, o.x28, rfl, by decide,
      ⟨⟨covers_left (by rw [o.wr, wr]; exact f.dataW), hn, ol.dw, ol.data.sub_right sub16, ol.data⟩,
        by rw [o.wr, wr]; exact f.dataW, ol.cd, ol.kd⟩, rfl⟩
  obtain B₁ := mkB f₁ a₁.wr o₁
  obtain B₂ := mkB f₂ a₂.wr o₂
  refine rel_seq (encBody_rel L v B₁ B₂ rfl) (WP.with_rdwr (encBody_ok L v B₁ 0))
    (WP.with_rdwr (encBody_ok L v B₂ 0)) fun w₁ w₂ ⟨b₁, _, _⟩ ⟨b₂, _, _⟩ => ?_
  obtain sl : ∀ {τ u ω : State},
      FrontOut (σ₁.gpr .x0) (stackArg σ₁ 0 + BitVec.ofNat 64 16) (stackArg σ₁ 0) σ₁.sp τ.gpr (σ₁.gpr .x5)
        (σ₁.gpr .x4).toNat (σ₁.gpr .x6).toNat τ u →
      Frame (bodyFrame (stackArg σ₁ 0 + BitVec.ofNat 64 16) (stackArg σ₁ 0) σ₁.sp (σ₁.gpr .x5) (σ₁.gpr .x6).toNat)
        u.mem ω.mem → ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      ω.mem.readW (stackArg σ₁ 0 + BitVec.ofNat 64 d) 64 = τ.mem.readW (stackArg σ₁ 0 + BitVec.ofNat 64 d) 64 :=
    fun o fb d h₁ h₂ => by
      rw [slot_kept fb (slots_bodyFrame L ol.data) h₁ h₂, slot_kept o.frame (slots_frontFrame L) h₁ h₂]
  refine rel_seq (rel_taint [.x19] (by rw [b₁.env.sp, b₂.env.sp]) (by agree_tac [b₁.env.x19, b₂.env.x19])
      ⟨_, by taint_decide⟩)
    (finPrep_ok (al := (σ₁.gpr .x4).toNat) (n := (σ₁.gpr .x6).toNat) b₁.env.x19 (covers_left b₁.env.perm.w)
      (by rw [sl o₁ b₁.frame 224 (by decide) (by decide), s2₁, ofNat_toNat'])
      (by rw [sl o₁ b₁.frame 240 (by decide) (by decide), s4₁, ofNat_toNat']))
    (finPrep_ok (al := (σ₁.gpr .x4).toNat) (n := (σ₁.gpr .x6).toNat) b₂.env.x19 (covers_left b₂.env.perm.w)
      (by rw [sl o₂ b₂.frame 224 (by decide) (by decide), s2₂, ofNat_toNat'])
      (by rw [sl o₂ b₂.frame 240 (by decide) (by decide), s4₂, ofNat_toNat']))
    fun z₁ z₂ ⟨x26₁, x27₁, r₁⟩ ⟨x26₂, x27₂, r₂⟩ => ?_
  refine rel_seq (rel_taint [.x19] (by rw [r₁.sp, r₂.sp, b₁.env.sp, b₂.env.sp])
      (by agree_tac [r₁.others .x19 (by decide), r₂.others .x19 (by decide), b₁.env.x19, b₂.env.x19])
      ⟨_, by taint_decide⟩)
    (ldr28_ok (V := σ₁.gpr .x7) (b₁.env.of_regs r₁) (by rw [r₁.mem, sl o₁ b₁.frame 248 (by decide) (by decide), s5₁]))
    (ldr28_ok (V := σ₁.gpr .x7) (b₂.env.of_regs r₂) (by rw [r₂.mem, sl o₂ b₂.frame 248 (by decide) (by decide), s5₂]))
    fun z₁' z₂' ⟨x28₁, r₁'⟩ ⟨x28₂, r₂'⟩ => ?_
  obtain e₁ := (b₁.env.of_regs r₁).of_regs r₁'
  obtain e₂ := (b₂.env.of_regs r₂).of_regs r₂'
  obtain y26₁ : z₁'.gpr .x26 = _ := (r₁'.others .x26 (by decide)).trans x26₁
  obtain y26₂ : z₂'.gpr .x26 = _ := (r₂'.others .x26 (by decide)).trans x26₂
  obtain y27₁ : z₁'.gpr .x27 = _ := (r₁'.others .x27 (by decide)).trans x27₁
  obtain y27₂ : z₂'.gpr .x27 = _ := (r₂'.others .x27 (by decide)).trans x27₂
  refine rel_seq (finBody_rel L v (.inl rfl) e₁ e₂ (fun _ _ => rfl)
      (fun _ _ => rfl) y26₁ y26₂ y27₁ y27₂ hal hn)
    (finBody_env v L (.inl rfl) e₁ (fun _ _ => rfl) y26₁ y27₁ hn)
    (finBody_env v L (.inl rfl) e₂ (fun _ _ => rfl) y26₂ y27₂ hn) fun g₁ g₂ h₁ h₂ => ?_
  obtain c28₁ : g₁.gpr .x28 = σ₁.gpr .x7 := (h₁.2.1 .x28 (by decide)).trans x28₁
  obtain c28₂ : g₂.gpr .x28 = σ₁.gpr .x7 := (h₂.2.1 .x28 (by decide)).trans x28₂
  exact rel_taint [.x19, .x28] (by rw [h₁.1.sp, h₂.1.sp])
    (by agree_tac [h₁.1.x19, h₂.1.x19, c28₁, c28₂]) ⟨_, by taint_decide⟩

theorem seal_ct (v : GcmImpl) : ConstantTime isa sealAArch64.pre sealAArch64.pub («seal» v.callees) := by
  unfold «seal»
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨f₁, f₂⟩ := oneFacts (by decide : 0 < 1) (sealCore h₁) (sealCore h₂) hq
  have hq₀ := hq
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, -⟩ := hq
  exact rel_seq (sealEntry_rel f₁ f₂ qsp (by agree_tac [q0, q1, q2, q3, q4, q5, q6]) q7)
    (sealEntry_ok h₁) (sealEntry_ok h₂) fun _ _ a₁ a₂ => sealRest_rel v h₁ h₂ hq₀ a₁ a₂

end VG.Proof.Sm4Gcm.AArch64

end

end

/-!
# SM4-GCM on AArch64: `vg_sm4_gcm_open` leaks only whether the tag is right

Untrusted: everything here is checked by Lean. As for `seal` (`SealCT.lean`),
with the received tag copied in and compared, and the text decrypted, by
`decAbs_rel` and the taint analysis. The branches on the tag length and on the comparison are public:
the tag length is an argument, and whether the tag is right is what
`openAArch64.pub` leaks.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Spec.Gcm (ctxH)

/-- The bit `openMain` computes, after `tagIn`, is whether `open` succeeds. -/
theorem tagBit {Ctx W SP Np A D Tg : Addr} {nl al n tl : Nat} {s₀ t : State}
    (o : OpenIn Ctx W SP Np A D Tg nl al n tl s₀ t) (rt : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true) :
    decide ((Spec.Gcm.fullTag (ciphOf t.mem Ctx) (blockAt t.mem (Ctx + BitVec.ofNat 64 240))
      (bytesAt t.mem Np nl) (bytesAt t.mem A al) (bytesAt t.mem D n)).take tl = bytesAt t.mem W tl) =
    (Spec.Gcm.openResult (ctxCiph s₀.mem Ctx) (ctxH s₀.mem Ctx) tl (bytesAt s₀.mem Np nl)
      (bytesAt s₀.mem D n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tg tl)).isSome := by
  obtain ⟨hc₃, hH₃, hN₃, hA₃, hD₃⟩ := o.vals
  rw [hc₃, hH₃, hN₃, hA₃, hD₃, rt, Spec.Gcm.openResult, ite_eq_left hok, Spec.Gcm.decryptWith]
  by_cases hc : (Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)
      (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl
  · rw [ite_eq_left hc]; simp [hc]
  · rw [ite_eq_right hc]; simp [hc]

/-- `FrontIn` from `OpenIn`. -/
theorem OpenIn.front {Ctx W SP Np A D Tg : Addr} {nl al n tl : Nat} {s₀ t : State}
    (o : OpenIn Ctx W SP Np A D Tg nl al n tl s₀ t) :
    FrontIn Ctx (W + BitVec.ofNat 64 16) W SP t.gpr Np A D nl al n t :=
  ⟨o.env, fun _ _ => rfl, o.x23, o.x24, o.x26, o.x27, o.non, o.aad, o.sA, o.sL, o.sD, o.sN⟩

/-- `openMain` up to the branch on the tag, in two runs. -/
theorem omA_rel (v : GcmImpl) {Ctx W SP Np A D Tg : Addr} {nl al n tl : Nat} {s₁ s₂ t₁ t₂ : State}
    (o₁ : OpenIn Ctx W SP Np A D Tg nl al n tl s₁ t₁) (o₂ : OpenIn Ctx W SP Np A D Tg nl al n tl s₂ t₂) :
    RelCT isa (Eq2 t₁ t₂) (omA v.callees) TT := by
  have L := o₁.lay
  have hal := o₁.aad.lt
  have hn := o₁.dat.ok.lt
  have sl := slots_omFrame L o₁.ddW
  have mF : ∀ {rs : List Region}, (∀ r ∈ rs, r ∈ omFrame W SP) → ∀ {m m' : Mem}, Frame rs m m' →
      Frame (omFrame W SP) m m' := fun hs _ _ hf => hf.mono hs
  unfold omA
  refine front_rel L v o₁.front o₂.front fun u₁ u₂ p₁ p₂ => ?_
  have mkB : ∀ {s t u : State}, OpenIn Ctx W SP Np A D Tg nl al n tl s t →
      FrontOut Ctx (W + BitVec.ofNat 64 16) W SP t.gpr D al n t u →
      BodyIn Ctx (W + BitVec.ofNat 64 16) W SP u.gpr n 0 D (Spec.Gcm.zeros al) []
        (blockAt u.mem (Ctx + BitVec.ofNat 64 240)) u := fun o p =>
    ⟨p.env, fun _ _ => rfl, by rw [p.x25, Proof.Gcm.length_zeros],
      p.x26, p.x27, p.x28, rfl, by decide, o.dat.of_eq (by rw [p.rd]) (by rw [p.wr]), rfl⟩
  have B₁ := mkB o₁ p₁
  have B₂ := mkB o₂ p₂
  refine rel_seq (decAbs_rel L v B₁ B₂ rfl) (decAbs_ok L v B₁) (decAbs_ok L v B₂)
    fun w₁ w₂ ⟨e₁, kk₁, _, fr₁, _, _, _⟩ ⟨e₂, kk₂, _, fr₂, _, _, _⟩ => ?_
  have F₁ : Frame (omFrame W SP) t₁.mem w₁.mem :=
    (mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))) p₁.frame).trans
      (mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hr))) fr₁)
  have F₂ : Frame (omFrame W SP) t₂.mem w₂.mem :=
    (mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))) p₂.frame).trans
      (mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hr))) fr₂)
  refine rel_seq (rel_taint [.x19] (by rw [e₁.sp, e₂.sp]) (by agree_tac [e₁.x19, e₂.x19]) ⟨_, by taint_decide⟩)
    (finPrep_ok (al := al) (n := n) e₁.x19 (covers_left e₁.perm.w)
      (by rw [slot_kept F₁ sl (by decide) (by decide), o₁.sL]) (by rw [slot_kept F₁ sl (by decide) (by decide), o₁.sN]))
    (finPrep_ok (al := al) (n := n) e₂.x19 (covers_left e₂.perm.w)
      (by rw [slot_kept F₂ sl (by decide) (by decide), o₂.sL]) (by rw [slot_kept F₂ sl (by decide) (by decide), o₂.sN]))
    fun z₁ z₂ ⟨x26₁, x27₁, r₁⟩ ⟨x26₂, x27₂, r₂⟩ => ?_
  refine rel_seq (finBody_rel L v (.inr rfl) (e₁.of_regs r₁) (e₂.of_regs r₂) (fun _ _ => rfl)
      (fun _ _ => rfl) x26₁ x26₂ x27₁ x27₂ hal hn)
    (finBody_env v L (.inr rfl) (e₁.of_regs r₁) (fun _ _ => rfl) x26₁ x27₁ hn)
    (finBody_env v L (.inr rfl) (e₂.of_regs r₂) (fun _ _ => rfl) x26₂ x27₂ hn)
    fun g₁ g₂ ⟨ge₁, _, gf₁⟩ ⟨ge₂, _, gf₂⟩ => ?_
  have G₁ : Frame (omFrame W SP) t₁.mem g₁.mem :=
    F₁.trans (by rw [r₁.mem] at gf₁; exact mF (fun r hr => List.mem_append_left _ (List.mem_append_right _ hr)) gf₁)
  have G₂ : Frame (omFrame W SP) t₂.mem g₂.mem :=
    F₂.trans (by rw [r₂.mem] at gf₂; exact mF (fun r hr => List.mem_append_left _ (List.mem_append_right _ hr)) gf₂)
  refine rel_seq (rel_taint [.x19] (by rw [ge₁.sp, ge₂.sp]) (by agree_tac [ge₁.x19, ge₂.x19]) ⟨_, by taint_decide⟩)
    (ldr28_ok (V := BitVec.ofNat 64 tl) ge₁ (by rw [slot_kept G₁ sl (by decide) (by decide), o₁.sT]))
    (ldr28_ok (V := BitVec.ofNat 64 tl) ge₂ (by rw [slot_kept G₂ sl (by decide) (by decide), o₂.sT]))
    fun h₁ h₂ ⟨x28₁, q₁⟩ ⟨x28₂, q₂⟩ => ?_
  exact rel_taint [.x19, .x28] (by rw [q₁.sp, q₂.sp, ge₁.sp, ge₂.sp])
    (by agree_tac [x28₁, x28₂, q₁.others .x19 (by decide), q₂.others .x19 (by decide), ge₁.x19, ge₂.x19])
    ⟨_, by taint_decide⟩

/-- The rest of `openMain`, in two runs that agree on the tag. -/
theorem omB_rel (v : GcmImpl) {Ctx W SP D Np A : Addr} {nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {fr : List Region} {s s' m₁ m₂ : State}
    (mo₁ : MidO fr Ctx W SP D Np A nl al n tl s m₁) (mo₂ : MidO fr Ctx W SP D Np A nl al n tl s' m₂)
    (dD : ∀ r ∈ fr, (⟨D, n⟩ : Region).Disjoint r) (dC : ∀ r ∈ fr, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hx : m₁.gpr .x27 = m₂.gpr .x27) :
    RelCT isa (Eq2 m₁ m₂) (omB v.callees) TT := by
  unfold omB
  have tm : ∃ h, (taint.check (Taint.ofRegs [.x27]) (.block [mov .x0 .x27]) h).isSome = true :=
    ⟨_, by taint_decide⟩
  refine rel_seq ?_ (omIte_ok v L mo₁ dD dC) (omIte_ok v L mo₂ dD dC)
    fun a b ⟨ea, xa, _, _⟩ ⟨eb, xb, _, _⟩ =>
      rel_taint [.x27] (by rw [ea.sp, eb.sp]) (by agree_tac [xa, xb, hx]) tm
  have x27₁ := mo₁.x27
  have x27₂ : m₂.gpr .x27 = _ := hx ▸ x27₁
  have hlt : ∀ B : Bool, (if B then 1 else 0 : Nat) < 2 ^ 64 := fun B => by cases B <;> decide
  refine rel_ite (eval_zero x27₁ (hlt _)) (eval_zero x27₂ (hlt _)) (fun _ => ?_) (fun _ => ?_)
  · exact rel_taint [] (by rw [mo₁.env.sp, mo₂.env.sp]) (by agree_tac []) ⟨_, by taint_decide⟩
  · refine rel_seq (rel_taint [.x19] (by rw [mo₁.env.sp, mo₂.env.sp]) (by agree_tac [mo₁.env.x19, mo₂.env.x19])
      ⟨_, by taint_decide⟩) (ocLdr_ok mo₁.env mo₁.sD mo₁.sN) (ocLdr_ok mo₂.env mo₂.sD mo₂.sN)
      fun c₁ c₂ h₁ h₂ => ?_
    exact cryptAl_rel L v (oc_in mo₁ h₁) (oc_in mo₂ h₂) rfl

/-- `openMain` in two runs, after `tagIn`, whose tags compare alike. -/
theorem openMain_rel (v : GcmImpl) {Ctx W SP Np A D Tg : Addr} {nl al n tl : Nat} {σ₁ σ₂ t₁ t₂ : State}
    (p₁ : OpenIn Ctx W SP Np A D Tg nl al n tl σ₁ t₁) (p₂ : OpenIn Ctx W SP Np A D Tg nl al n tl σ₂ t₂)
    (rt₁ : bytesAt t₁.mem W tl = bytesAt σ₁.mem Tg tl) (rt₂ : bytesAt t₂.mem W tl = bytesAt σ₂.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true)
    (hb : (Spec.Gcm.openResult (ctxCiph σ₁.mem Ctx) (ctxH σ₁.mem Ctx) tl (bytesAt σ₁.mem Np nl)
        (bytesAt σ₁.mem D n) (bytesAt σ₁.mem A al) (bytesAt σ₁.mem Tg tl)).isSome =
      (Spec.Gcm.openResult (ctxCiph σ₂.mem Ctx) (ctxH σ₂.mem Ctx) tl (bytesAt σ₂.mem Np nl)
        (bytesAt σ₂.mem D n) (bytesAt σ₂.mem A al) (bytesAt σ₂.mem Tg tl)).isSome) :
    RelCT isa (Eq2 t₁ t₂) (openMain v.callees) TT := by
  have L := p₁.lay
  refine (openMain_split v.callees).symm.rel (rel_seq (omA_rel v p₁ p₂)
    (openMainA_ok v L p₁.env p₁.x23 p₁.x24 p₁.x26 p₁.x27 p₁.non p₁.aad p₁.dat p₁.ddW
      p₁.dcW p₁.sA p₁.sL p₁.sD p₁.sN p₁.sT hok)
    (openMainA_ok v L p₂.env p₂.x23 p₂.x24 p₂.x26 p₂.x27 p₂.non p₂.aad p₂.dat p₂.ddW
      p₂.dcW p₂.sA p₂.sL p₂.sD p₂.sN p₂.sT hok) fun m₁ m₂ mo₁ mo₂ => ?_)
  refine omB_rel v L mo₁ mo₂ (keep_om p₁.ddW p₁.dat.stk.symm) (keep_om p₁.dcW L.kc.symm) ?_
  rw [mo₁.x27, mo₂.x27, tagBit p₁ rt₁ hok, tagBit p₂ rt₂ hok, hb]

/-- `open` after its entry, in two runs from the same public arguments. -/
theorem openRest_rel (v : GcmImpl) {σ₁ σ₂ s₁ s₂ : State}
    (o₁ : OpenIn (σ₁.gpr .x0) (stackArg σ₁ 1) σ₁.sp (σ₁.gpr .x1) (σ₁.gpr .x3) (σ₁.gpr .x5) (σ₁.gpr .x7)
      (σ₁.gpr .x2).toNat (σ₁.gpr .x4).toNat (σ₁.gpr .x6).toNat (stackArg σ₁ 0).toNat σ₁ s₁)
    (o₂ : OpenIn (σ₁.gpr .x0) (stackArg σ₁ 1) σ₁.sp (σ₁.gpr .x1) (σ₁.gpr .x3) (σ₁.gpr .x5) (σ₁.gpr .x7)
      (σ₁.gpr .x2).toNat (σ₁.gpr .x4).toNat (σ₁.gpr .x6).toNat (stackArg σ₁ 0).toNat σ₂ s₂)
    (x12₁ : s₁.gpr .x12 = σ₁.gpr .x7) (x12₂ : s₂.gpr .x12 = σ₁.gpr .x7)
    (hb : (Spec.Gcm.openResult (ctxCiph σ₁.mem (σ₁.gpr .x0)) (ctxH σ₁.mem (σ₁.gpr .x0)) (stackArg σ₁ 0).toNat
        (bytesAt σ₁.mem (σ₁.gpr .x1) (σ₁.gpr .x2).toNat) (bytesAt σ₁.mem (σ₁.gpr .x5) (σ₁.gpr .x6).toNat)
        (bytesAt σ₁.mem (σ₁.gpr .x3) (σ₁.gpr .x4).toNat) (bytesAt σ₁.mem (σ₁.gpr .x7) (stackArg σ₁ 0).toNat)).isSome =
      (Spec.Gcm.openResult (ctxCiph σ₂.mem (σ₁.gpr .x0)) (ctxH σ₂.mem (σ₁.gpr .x0)) (stackArg σ₁ 0).toNat
        (bytesAt σ₂.mem (σ₁.gpr .x1) (σ₁.gpr .x2).toNat) (bytesAt σ₂.mem (σ₁.gpr .x5) (σ₁.gpr .x6).toNat)
        (bytesAt σ₂.mem (σ₁.gpr .x3) (σ₁.gpr .x4).toNat) (bytesAt σ₂.mem (σ₁.gpr .x7) (stackArg σ₁ 0).toNat)).isSome) :
    RelCT isa (Eq2 s₁ s₂) (openRest v.callees) TT := by
  unfold openRest
  refine rel_seq (rel_taint [.x28] (by rw [o₁.env.sp, o₂.env.sp]) (by agree_tac [o₁.x28, o₂.x28])
      ⟨_, by taint_decide⟩)
    (tagLenOk_ok s₁ o₁.x28 o₁.tlt) (tagLenOk_ok s₂ o₂.x28 o₂.tlt) fun u₁ u₂ ⟨x9₁, r₁⟩ ⟨x9₂, r₂⟩ => ?_
  have tr : ∃ h, (taint.check (Taint.ofRegs [.x19]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have p₁ := o₁.of_regs r₁
  have p₂ := o₂.of_regs r₂
  have y12₁ : u₁.gpr .x12 = σ₁.gpr .x7 := by rw [r₁.others _ (by decide), x12₁]
  have y12₂ : u₂.gpr .x12 = σ₁.gpr .x7 := by rw [r₂.others _ (by decide), x12₂]
  have hlt : ((if Spec.Gcm.tagLenOk (stackArg σ₁ 0).toNat then 1 else 0 : Nat)) < 2 ^ 64 := by split <;> decide
  refine rel_seq (rel_ite (eval_zero x9₁ hlt) (eval_zero x9₂ hlt) (fun _ => ?_) (fun hf => ?_))
    (oiteWith_ok p₁ y12₁ x9₁ fun o' hT hok _ => openMain_post v o' hT hok)
    (oiteWith_ok p₂ y12₂ x9₂ fun o' hT hok _ => openMain_post v o' hT hok) fun w₁ w₂ e₁ e₂ =>
      rel_taint [.x19] (by rw [e₁.1.sp, e₂.1.sp]) (by agree_tac [e₁.1.x19, e₂.1.x19]) tr
  · exact rel_taint [] (by rw [p₁.env.sp, p₂.env.sp]) (by agree_tac []) ⟨_, by taint_decide⟩
  have hok : Spec.Gcm.tagLenOk (stackArg σ₁ 0).toNat = true := by
    revert hf; cases Spec.Gcm.tagLenOk (stackArg σ₁ 0).toNat <;> simp
  have hle := tagLenOk_le hok
  refine rel_seq (rel_taint [.x19, .x28, .x12] (by rw [p₁.env.sp, p₂.env.sp])
      (by agree_tac [p₁.env.x19, p₂.env.x19, p₁.x28, p₂.x28, y12₁, y12₂]) ⟨_, by taint_decide⟩)
    (tagIn_ok p₁.env.x19 y12₁ p₁.x28 hle p₁.tagR p₁.env.perm.w (p₁.dtW.sub_right (Region.sub_prefix (by decide))))
    (tagIn_ok p₂.env.x19 y12₂ p₂.x28 hle p₂.tagR p₂.env.perm.w (p₂.dtW.sub_right (Region.sub_prefix (by decide))))
    fun t₁ t₂ ⟨rt₁, g₁, og₁, sp₁, rd₁, wr₁⟩ ⟨rt₂, g₂, og₂, sp₂, rd₂, wr₂⟩ => ?_
  exact openMain_rel v (p₁.tagIn g₁ og₁ sp₁ rd₁ wr₁) (p₂.tagIn g₂ og₂ sp₂ rd₂ wr₂) (by rw [rt₁, p₁.tag])
    (by rw [rt₂, p₂.tag]) hok hb

/-- The entry of `open` in two runs. -/
theorem openEntry_rel {σ₁ σ₂ : State} (f₁ : OneFacts σ₁ σ₁ 2 1) (f₂ : OneFacts σ₂ σ₁ 2 1) (qsp : σ₁.sp = σ₂.sp)
    (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6], σ₁.gpr r = σ₂.gpr r) (q7 : σ₁.gpr .x7 = σ₂.gpr .x7) :
    RelCT isa (Eq2 σ₁ σ₂) (.block openEntry) TT := by
  have hW₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 8) 64 = stackArg σ₁ 1 := rfl
  have hW₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 8) 64 = stackArg σ₁ 1 := f₂.hW
  have ts : ∃ h, (taint.check (Taint.ofRegs [.x19, .x7])
      (.block [.ldrSp .x10 0, .str .x .x10 .x19 tlO, mov .x28 .x10, mov .x12 .x7]) h).isSome = true :=
    ⟨_, by taint_decide⟩
  unfold openEntry
  refine RelCT.block_split (rel_seq (entry_rel (.inr rfl) hW₁ hW₂ (f₁.hsp 1 (by decide)) (f₂.hsp 1 (by decide))
      f₁.perm.w f₂.perm.w qsp hq)
    (oneEntry_ok (by decide) hW₁ (f₁.hsp 1 (by decide)) rfl f₁.perm)
    (oneEntry_ok (by decide) hW₂ (f₂.hsp 1 (by decide)) (hq .x0 (by simp)).symm f₂.perm)
    fun τ₁ τ₂ a₁ a₂ => rel_taint [.x19, .x7] (by rw [a₁.1.sp, a₂.1.sp, qsp])
      (by agree_tac [a₁.1.x19, a₂.1.x19, a₁.2.2.2.2.2.1, a₂.2.2.2.2.2.1, q7]) ts)

theorem open_ct (v : GcmImpl) : ConstantTime isa openAArch64.pre openAArch64.pub («open» v.callees) := by
  unfold «open»
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨hq, hres⟩ := hq
  obtain ⟨f₁, f₂⟩ := oneFacts (by decide : 1 < 2) (openCore h₁) (openCore h₂) hq
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have qt : stackArg σ₁ 0 = stackArg σ₂ 0 := qa 0 (by decide)
  have qw : stackArg σ₁ 1 = stackArg σ₂ 1 := qa 1 (by decide)
  refine rel_seq (openEntry_rel f₁ f₂ qsp (by agree_tac [q0, q1, q2, q3, q4, q5, q6]) q7)
    (openEntry_ok h₁) (openEntry_ok h₂) fun s₁ s₂ ⟨o₁, x12₁⟩ ⟨o₂, x12₂⟩ => ?_
  rw [← q0, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7, ← qsp, ← qt, ← qw] at o₂
  rw [← q7] at x12₂
  have hb : (openRes σ₁).isSome = (openRes σ₂).isSome := by
    simp only [openLeakOf, List.cons.injEq, and_true] at hres
    revert hres; cases (openRes σ₁).isSome <;> cases (openRes σ₂).isSome <;> simp
  have hr₂ : openRes σ₂ = Spec.Gcm.openResult (ctxCiph σ₂.mem (σ₁.gpr .x0)) (ctxH σ₂.mem (σ₁.gpr .x0))
      (stackArg σ₁ 0).toNat (bytesAt σ₂.mem (σ₁.gpr .x1) (σ₁.gpr .x2).toNat)
      (bytesAt σ₂.mem (σ₁.gpr .x5) (σ₁.gpr .x6).toNat) (bytesAt σ₂.mem (σ₁.gpr .x3) (σ₁.gpr .x4).toNat)
      (bytesAt σ₂.mem (σ₁.gpr .x7) (stackArg σ₁ 0).toNat) := by
    unfold openRes; rw [← q0, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7, ← qt]
  rw [hr₂] at hb
  exact openRest_rel v o₁ o₂ x12₁ x12₂ hb

end VG.Proof.Sm4Gcm.AArch64

end

end

/-! ### `Sm4Gcm.AArch64.InitCT`, which only this module used -/

section

/-!
# SM4-GCM on AArch64: `vg_sm4_gcm_init` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/AArch64/Verified.lean`): the code around the calls by the taint
analysis, from the public arguments and the registers the correctness proof
pins (`init1_ok`, `init2_ok`); the calls by their callees' proofs, with the
arguments those proofs give.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (mov ptr imm tO save)
open VG.Proof.AesGcm.AArch64

/-- The block before the call of `vg_sm4_expand_key`. -/
theorem init1_ok {s : State} {K Ctx W : Addr} (hK : s.gpr .x0 = K) (hCtx : s.gpr .x1 = Ctx)
    (hW : s.gpr .x2 = W) (hsp : 3264 ≤ s.sp.toNat) (hrd : s.rd = [⟨K, 16⟩])
    (hwr : s.wr = [⟨Ctx, 256⟩, ⟨W, 768⟩]) (d_kc : (⟨K, 16⟩ : Region).Disjoint ⟨Ctx, 256⟩)
    (sK : (stk s.sp).Disjoint ⟨K, 16⟩) (sC : (stk s.sp).Disjoint ⟨Ctx, 256⟩)
    (fK : K.toNat + 16 ≤ 2 ^ 64) (fC : Ctx.toNat + 256 ≤ 2 ^ 64) :
    WP isa (.block initSeg1) s fun s₂ => KeyCall s₂ K Ctx ∧ s₂.gpr .x19 = W ∧
      s₂.gpr .x21 = Ctx ∧ s₂.sp = s.sp ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  have pW : Covers [⟨W, 768⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have pK : Covers [⟨K, 16⟩] (s.rd ++ s.wr) := by rw [hrd]; exact covers_of_mem (by simp)
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s .x2 hW pW
  obtain ⟨s₂, run₂, x19₂, x21₂, x0₂, x1₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x2, mov .x21 .x1] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x21 = Ctx ∧ s₂.gpr .x0 = K ∧ s₂.gpr .x1 = Ctx ∧
      s₂.sp = s₁.sp ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp [gpr_write, g₁, hW]
    · simp [gpr_write, g₁, hCtx]
    · simp [gpr_write, g₁, hK]
    · simp [gpr_write, g₁, hCtx]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  have rd₂' : s₂.rd = s.rd := rd₂.trans rd₁
  have wr₂' : s₂.wr = s.wr := wr₂.trans wr₁
  have sp₂' : s₂.sp = s.sp := sp₂.trans sp₁
  refine ⟨⟨x0₂, x1₂, by rw [sp₂']; exact hsp, fK, by omega_using [fC], d_kc.sub_right (Region.sub_prefix (by decide)),
      by rw [sp₂']; exact sK, by rw [sp₂']; exact sC.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩,
    x19₂, x21₂, sp₂', rd₂', wr₂'⟩
  · rw [rd₂', wr₂']
    exact covers_cons pK (covers_left (covers_prefix pC (by decide)))
  · rw [wr₂']; exact covers_prefix pC (by decide)

/-- The block before the call of `vg_sm4_ctr32`. -/
theorem init2_ok {s : State} {Ctx W : Addr} (h19 : s.gpr .x19 = W) (h21 : s.gpr .x21 = Ctx)
    (hsp : 3264 ≤ s.sp.toNat) (pC : Covers [⟨Ctx, 256⟩] s.wr) (pW : Covers [⟨W, 768⟩] s.wr)
    (d_cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 768⟩) (sC : (stk s.sp).Disjoint ⟨Ctx, 256⟩)
    (sW : (stk s.sp).Disjoint ⟨W, 768⟩) (fC : Ctx.toNat + 256 ≤ 2 ^ 64) (fW : W.toNat + 768 ≤ 2 ^ 64) :
    WP isa (.block initSeg2) s fun s₄ =>
      CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240) 1 ∧
      s₄.gpr .x19 = W ∧ s₄.gpr .x21 = Ctx ∧ s₄.sp = s.sp := by
  have w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₃ := in_off pW (show 96 + 8 ≤ 768 by decide) (by decide)
  have w₄ := in_off pW (show 104 + 8 ≤ 768 by decide) (by decide)
  obtain ⟨s₄, run₄, x0₄, x1₄, x2₄, x3₄, og₄, sp₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa initSeg2 s = some s₄ ∧
      s₄.gpr .x0 = Ctx ∧ s₄.gpr .x1 = W + BitVec.ofNat 64 96 ∧ s₄.gpr .x2 = Ctx + BitVec.ofNat 64 240 ∧
      s₄.gpr .x3 = BitVec.ofNat 64 1 ∧ Others [.x9, .x0, .x1, .x2, .x3] s s₄ ∧
      s₄.sp = s.sp ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr := by
    refine ⟨_, by simp only [initSeg2]; arun [h19, h21, w₁, w₂, w₃, w₄], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp [gpr_write, h21]
    · simp [gpr_write, h19]
    · simp [gpr_write, h21]
    · simp [gpr_write]
  refine WP.of_runBlock ⟨s₄, run₄, ?_, by rw [og₄ _ (by decide), h19], by rw [og₄ _ (by decide), h21], sp₄⟩
  have dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 768 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ he)
  have dK0 : (⟨Ctx, 128⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega_using [])
  have pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [wr₄]; exact pC
  have pW' : Covers [⟨W, 768⟩] s₄.wr := by rw [wr₄]; exact pW
  refine ⟨x0₄, x1₄, x2₄, x3₄, by rw [sp₄]; exact hsp, by decide, ?_, by omega_using [fC], ?_,
    ?_, dK0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); omega_using [fC]
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (W.toNat + 96 % 2 ^ 64) (2 ^ 64); omega_using [fW]
  · simpa using dCW 0 128 (by decide) 96 16 (by decide)
  · exact (dCW 240 16 (by decide) 96 16 (by decide)).symm
  · rw [sp₄]; exact sC.sub_right (Region.sub_prefix (by decide))
  · rw [sp₄]; exact sW.sub_right (Offset.sub_base W (by decide))
  · rw [sp₄]; exact sC.sub_right (Offset.sub_base Ctx (by decide))
  · exact covers_cons (covers_left (covers_prefix pC' (by decide))) (covers_cons
      (covers_left (covers_off pW' (by decide) (by decide)))
      (covers_left (covers_off pC' (by decide) (by decide))))
  · exact covers_cons (covers_off pW' (by decide) (by decide)) (covers_off pC' (by decide) (by decide))

theorem init_ct (v : GcmImpl) : ConstantTime isa initAArch64.pre initAArch64.pub (init v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, qsp⟩ := hq
  simp only [initAArch64] at h₁ h₂
  rw [← q0, ← q1, ← q2, ← qsp] at h₂
  obtain ⟨hsp, hrd₁, hwr₁, d_kc, -, d_cs, sK, sC, sW, fK, fC, fW⟩ := h₁
  obtain ⟨-, hrd₂, hwr₂, -⟩ := h₂
  generalize hK : σ₁.gpr .x0 = K at *
  generalize hCtx : σ₁.gpr .x1 = Ctx at *
  generalize hW : σ₁.gpr .x2 = W at *
  refine rel_seq (rel_taint [.x0, .x1, .x2] qsp (by agree_tac [hK, hCtx, hW, ← q0, ← q1, ← q2])
      ⟨_, by taint_decide⟩)
    (init1_ok hK hCtx hW hsp hrd₁ hwr₁ d_kc sK sC fK fC)
    (init1_ok q0.symm q1.symm q2.symm (by rw [← qsp]; exact hsp) hrd₂ hwr₂ d_kc (by rw [← qsp]; exact sK)
      (by rw [← qsp]; exact sC) fK fC)
    fun τ₁ τ₂ ⟨k₁, x19₁, x21₁, sp₁, rd₁, wr₁⟩ ⟨k₂, x19₂, x21₂, sp₂, rd₂, wr₂⟩ => ?_
  refine rel_seq (rel_key v.ctr.key k₁ k₂ (by rw [sp₁, sp₂, qsp])) (key_call v.ctr.key k₁)
      (key_call v.ctr.key k₂)
    fun τ₁' τ₂' g₁ g₂ => ?_
  have pv : ∀ {σ τ τ' : State}, σ.wr = [⟨Ctx, 256⟩, ⟨W, 768⟩] → τ.wr = σ.wr → τ.sp = σ.sp →
      σ.sp = σ₁.sp → KeyPost τ K Ctx τ' → τ.gpr .x19 = W → τ.gpr .x21 = Ctx →
      WP isa (.block initSeg2) τ' fun s₄ => CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240) 1 ∧
        s₄.gpr .x19 = W ∧ s₄.gpr .x21 = Ctx ∧ s₄.sp = τ'.sp :=
    fun hwr wr sp sp' g h19 h21 => init2_ok (by rw [g.saved .x19 (by decide) (by decide), h19])
      (by rw [g.saved .x21 (by decide) (by decide), h21]) (by rw [g.sp, sp, sp']; exact hsp)
      (by rw [g.wr, wr, hwr]; exact covers_of_mem (by simp))
      (by rw [g.wr, wr, hwr]; exact covers_of_mem (by simp)) d_cs (by rw [g.sp, sp, sp']; exact sC)
      (by rw [g.sp, sp, sp']; exact sW) fC fW
  refine rel_seq (rel_taint [.x19, .x21] (by rw [g₁.sp, g₂.sp, sp₁, sp₂, qsp])
      (by agree_tac [g₁.saved .x19 (by decide) (by decide), g₂.saved .x19 (by decide) (by decide),
        g₁.saved .x21 (by decide) (by decide), g₂.saved .x21 (by decide) (by decide), x19₁, x19₂, x21₁, x21₂])
      ⟨_, by taint_decide⟩)
    (pv hwr₁ wr₁ sp₁ rfl g₁ x19₁ x21₁) (pv hwr₂ wr₂ sp₂ qsp.symm g₂ x19₂ x21₂)
    fun τ₁ τ₂ ⟨c₁, y₁, z₁, s₁'⟩ ⟨c₂, y₂, z₂, s₂'⟩ => ?_
  refine rel_seq (rel_ctr v.ctr c₁ c₂ (by rw [s₁', s₂', g₁.sp, g₂.sp, sp₁, sp₂, qsp]))
    (ctr_call v.ctr c₁) (ctr_call v.ctr c₂) fun τ₁ τ₂ e₁ e₂ => ?_
  exact rel_taint [.x19, .x21] (by rw [e₁.sp, e₂.sp, s₁', s₂', g₁.sp, g₂.sp, sp₁, sp₂, qsp])
    (by agree_tac [e₁.saved .x19 (by decide) (by decide), e₂.saved .x19 (by decide) (by decide), y₁, y₂,
      e₁.saved .x21 (by decide) (by decide), e₂.saved .x21 (by decide) (by decide), z₁, z₂]) ⟨_, by taint_decide⟩

end VG.Proof.Sm4Gcm.AArch64

end

end

/-! ### `Sm4Gcm.AArch64.Verified`, which only this module used -/

section

/-! ### `Sm4Gcm.AArch64.Init`, which only this module used -/

section

/-!
# SM4-GCM on AArch64: `vg_sm4_gcm_init`

Untrusted: everything here is checked by Lean. The key schedule from
`vg_sm4_expand_key` in the context's first 128 bytes, then the hash subkey
`CIPH_K(0¹²⁸)` at byte 240 from `vg_sm4_ctr32` over a zero block with a zero
counter block (`init_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (mov ptr imm tO scrO save saved restore)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Spec.Sm4.Gcm (KeyRepr)
open VG.Spec.Gcm (ctxH)

/-- SM4's block at `p` is the 16 bytes there. -/
theorem sm4BlockAt_eq (m : Mem) (p : Addr) :
    Spec.Sm4.blockAt m p = Vector.ofFn fun i : Fin 16 => (bytesAt m p 16).getD i.val 0 := by
  unfold Spec.Sm4.blockAt
  congr 1
  funext i
  simp [bytesAt, i.isLt]

/-- `vg_sm4_gcm_init`. -/
theorem init_wp (v : GcmImpl) {s : State} (hp : initAArch64.pre s) :
    WP isa (init v.callees) s fun s' => GprAbi s s' ∧ initAArch64.post s s' := by
  simp only [initAArch64] at hp ⊢
  obtain ⟨hsp, hrd, hwr, d_kc, d_ks, d_cs, sK, sC, sW, fK, fC, fW⟩ := hp
  generalize hK : s.gpr .x0 = K at *
  generalize hCtx : s.gpr .x1 = Ctx at *
  generalize hW : s.gpr .x2 = W at *
  obtain pW : Covers [⟨W, 768⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  obtain pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  obtain pK : Covers [⟨K, 16⟩] (s.rd ++ s.wr) := by rw [hrd]; exact covers_of_mem (by simp)
  -- The registers saved, the context and `W` to `x21` and `x19`.
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s .x2 hW pW
  obtain ⟨s₂, run₂, x19₂, x21₂, x0₂, x1₂, og₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x2, mov .x21 .x1] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x21 = Ctx ∧ s₂.gpr .x0 = K ∧ s₂.gpr .x1 = Ctx ∧
      Others [.x19, .x21] s₁ s₂ ∧ s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, g₁, hW]
    · simp [gpr_write, g₁, hCtx]
    · simp [gpr_write, g₁, hK]
    · simp [gpr_write, g₁, hCtx]
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩))
  obtain rd₂' : s₂.rd = s.rd := rd₂.trans rd₁
  obtain wr₂' : s₂.wr = s.wr := wr₂.trans wr₁
  obtain sp₂' : s₂.sp = s.sp := sp₂.trans sp₁
  -- The key schedule.
  obtain kc : KeyCall s₂ K Ctx := by
    refine ⟨x0₂, x1₂, by rw [sp₂']; exact hsp, fK, by omega_arith, d_kc.sub_right (Region.sub_prefix (by decide)),
      by rw [sp₂']; exact sK, by rw [sp₂']; exact sC.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩
    · rw [rd₂', wr₂']
      exact covers_cons pK (covers_left (covers_prefix pC (by decide)))
    · rw [wr₂']; exact covers_prefix pC (by decide)
  refine WP.seq (WP.mono (key_call v.ctr.key kc) fun s₃ g => ?_)
  obtain g19 : s₃.gpr .x19 = W := by rw [g.saved .x19 (by decide) (by decide), x19₂]
  obtain g21 : s₃.gpr .x21 = Ctx := by rw [g.saved .x21 (by decide) (by decide), x21₂]
  obtain rd₃ : s₃.rd = s.rd := g.rd.trans rd₂'
  obtain wr₃ : s₃.wr = s.wr := g.wr.trans wr₂'
  obtain sp₃ : s₃.sp = s.sp := g.sp.trans sp₂'
  have gf := g.frame
  rw [sp₂'] at gf
  -- A zero block at the context's `H` and a zero counter block in `T`.
  obtain w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  obtain w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  obtain w₃ := in_off pW (show 96 + 8 ≤ 768 by decide) (by decide)
  obtain w₄ := in_off pW (show 104 + 8 ≤ 768 by decide) (by decide)
  rw [← wr₃] at w₁ w₂ w₃ w₄
  obtain ⟨s₄, run₄, hm₄, x0₄, x1₄, x2₄, x3₄, og₄, sp₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa initSeg2 s₃ = some s₄ ∧
      s₄.mem = (((s₃.mem.writeW (Ctx + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (Ctx + BitVec.ofNat 64 248) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96)
        (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 104) (0 : BitVec 64) ∧
      s₄.gpr .x0 = Ctx ∧ s₄.gpr .x1 = W + BitVec.ofNat 64 96 ∧ s₄.gpr .x2 = Ctx + BitVec.ofNat 64 240 ∧
      s₄.gpr .x3 = BitVec.ofNat 64 1 ∧ Others [.x9, .x0, .x1, .x2, .x3] s₃ s₄ ∧
      s₄.sp = s₃.sp ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    refine ⟨_, by simp only [initSeg2]; arun [g19, g21, w₁, w₂, w₃, w₄], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp only [mem_write]; rfl
    · simp [gpr_write, g21]
    · simp [gpr_write, g19]
    · simp [gpr_write, g21]
    · simp [gpr_write]
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  obtain rd₄' : s₄.rd = s.rd := rd₄.trans rd₃
  obtain wr₄' : s₄.wr = s.wr := wr₄.trans wr₃
  obtain sp₄' : s₄.sp = s.sp := sp₄.trans sp₃
  obtain dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 768 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ he)
  obtain dK0 : (⟨Ctx, 128⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega_arith)
  obtain e248 : Ctx + BitVec.ofNat 64 248 = Ctx + BitVec.ofNat 64 240 + BitVec.ofNat 64 8 :=
    (add_ofNat_assoc _ 240 8).symm
  obtain e104 : W + BitVec.ofNat 64 104 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 :=
    (add_ofNat_assoc _ 96 8).symm
  rw [e248, e104] at hm₄
  obtain f₄ : Frame [⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩] s₃.mem s₄.mem := by
    rw [hm₄]
    exact ((Proof.Cmac.frame_store2 _ _ _).mono (by simp)).trans ((Proof.Cmac.frame_store2 _ _ _).mono (by simp))
  obtain hT₄ : blockAt s₄.mem (W + BitVec.ofNat 64 96) = 0 := by
    rw [blockAt, hm₄, zeroT_bytes]; decide
  obtain hD₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = 0 := by
    rw [blockAt, hm₄, bytesAt_frame (Proof.Cmac.frame_store2 _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dCW 240 16 (by decide) 96 16 (by decide)) (by decide),
      zeroT_bytes]
    decide
  obtain fsv : Frame [savedR W] s.mem s₁.mem := by rw [m₁]; exact savedMem_frame _ _ _
  -- The key, as the callee read it, and the schedule.
  obtain hKey : Spec.Sm4.blockAt s₂.mem K = Vector.ofFn fun i : Fin 16 => (bytesAt s.mem K 16).getD i.val 0 := by
    rw [sm4BlockAt_eq, m₂, bytesAt_frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact d_ks.sub_right (Offset.sub_base W (by decide)))
      (by decide)]
  obtain hk₄ : Spec.Sm4.scheduleAt s₄.mem Ctx =
      Spec.Sm4.expandKey (Vector.ofFn fun i : Fin 16 => (bytesAt s.mem K 16).getD i.val 0) := by
    rw [Proof.Sm4.scheduleAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dK0
        · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base W (by decide))),
      g.out, hKey]
  obtain pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [wr₄']; exact pC
  obtain pW' : Covers [⟨W, 768⟩] s₄.wr := by rw [wr₄']; exact pW
  -- `H = CIPH_K(0¹²⁸)`.
  obtain cc : CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240) 1 := by
    refine ⟨x0₄, x1₄, x2₄, x3₄, by rw [sp₄']; exact hsp, by decide, ?_, by omega_arith, ?_,
      ?_, dK0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); omega_arith
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (W.toNat + 96 % 2 ^ 64) (2 ^ 64); omega_arith
    · simpa using dCW 0 128 (by decide) 96 16 (by decide)
    · exact (dCW 240 16 (by decide) 96 16 (by decide)).symm
    · rw [sp₄']; exact sC.sub_right (Region.sub_prefix (by decide))
    · rw [sp₄']; exact sW.sub_right (Offset.sub_base W (by decide))
    · rw [sp₄']; exact sC.sub_right (Offset.sub_base Ctx (by decide))
    · exact covers_cons (covers_left (covers_prefix pC' (by decide))) (covers_cons
        (covers_left (covers_off pW' (by decide) (by decide)))
        (covers_left (covers_off pC' (by decide) (by decide))))
    · exact covers_cons (covers_off pW' (by decide) (by decide)) (covers_off pC' (by decide) (by decide))
  refine WP.seq (WP.mono (ctr_call v.ctr cc) fun s₅ c => ?_)
  have cf := c.frame
  rw [sp₄'] at cf
  have gout := c.out
  rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq, hT₄, hD₄, hk₄] at gout
  obtain c19 : s₅.gpr .x19 = W := by rw [c.saved .x19 (by decide) (by decide), og₄ _ (by decide), g19]
  obtain dSvK : ∀ r ∈ [(⟨Ctx, 128⟩ : Region), stk s.sp], (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base W (by decide)) |>.symm
    · exact (sW.sub_right (Offset.sub_base W (by decide))).symm
  obtain dSv₄ : ∀ r ∈ [(⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region), ⟨W + BitVec.ofNat 64 96, 16⟩],
      (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dCW 240 16 (by decide) 128 88 (by decide)).symm
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by omega_arith)
  obtain dSv₅ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region), ⟨Ctx + BitVec.ofNat 64 240, 16 * 1⟩, stk s.sp],
      (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by omega_arith)
    · exact (dCW 240 16 (by decide) 128 88 (by decide)).symm
    · exact (sW.sub_right (Offset.sub_base W (by decide))).symm
  obtain hsv₁ : SavedAt s₁.mem W s := by rw [m₁]; exact savedAt_save _ _ _
  obtain hsv₅ : SavedAt s₅.mem W s :=
    (((hsv₁.frame (by rw [← m₂]; exact gf) dSvK).frame f₄ dSv₄).frame cf dSv₅)
  obtain pWr : Covers [⟨W, 768⟩] (s₅.rd ++ s₅.wr) := by rw [c.rd, c.wr, rd₄', wr₄']; exact covers_left pW
  refine WP.mono (exit_ok c19 (by rw [c.sp, sp₄']) pWr hsv₅) fun s' ⟨hg, hm, _⟩ => ⟨hg, ?_, ?_⟩
  · rw [hm, Proof.Sm4.scheduleAt_frame cf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base W (by decide))
      · exact dK0
      · exact (sC.sub_right (Region.sub_prefix (by decide))).symm), hk₄]
  · show blockAt s'.mem (Ctx + 240) = _
    rw [hm, ofNat_lit, gout.1]
    simp [Spec.Sm4.gcmCipherOfKey]

end VG.Proof.Sm4Gcm.AArch64

end

end


/-!
# SM4-GCM on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_ghash` and `vg_sm4_ctr32`), a state satisfying each
precondition, and the shared contracts of `Spec/Sm4/Gcm/Contract.lean` with
the working space as a last argument (`Sig.scratchContract`) and the 3264
bytes of stack `vg_sm4_ctr32` and `vg_sm4_expand_key` use below the stack
pointer.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (minK copy copyB xorB tagLenOk tagIn cmpSeg cmp cmp16 fo textArgs tagOut restore)

/-- The CPU features of the functions calling `vg_ghash`: its implementation's. -/
def GcmImpl.features (v : GcmImpl) : List String := v.gh.features

/-! ## v8–v15 -/

theorem init_keepsV (v : GcmImpl) : (init v.callees).allInstrs keepsV = true := by
  simp only [init, ctrCall, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.ctr.key.keepsV]; lit_decide

theorem streamEncrypt_keepsV (v : GcmImpl) : (streamEncrypt v.callees).allInstrs keepsV = true := by
  simp only [streamEncrypt, encBody, fo, textAbs, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall, absorb,
    absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees,
    Code.allInstrs, v.ctr.keepsV, v.gh.keepsV]; lit_decide

theorem streamDecrypt_keepsV (v : GcmImpl) : (streamDecrypt v.callees).allInstrs keepsV = true := by
  simp only [streamDecrypt, decBody, decAbs, fo, textAbs, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall,
    absorb, absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush, lens,
    GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.gh.keepsV]; lit_decide

theorem streamFinish_keepsV (v : GcmImpl) : (streamFinish v.callees).allInstrs keepsV = true := by
  simp only [streamFinish, finBody, tag, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, xorB,
    Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV,
    v.gh.keepsV]; lit_decide

theorem streamVerify_keepsV (v : GcmImpl) : (streamVerify v.callees).allInstrs keepsV = true := by
  simp only [streamVerify, tagLenOk, tagIn, cmpSeg, cmp, cmp16, finBody, tag, ctrCall, ghCall, absorb,
    absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees,
    Code.allInstrs, v.ctr.keepsV, v.gh.keepsV]; lit_decide

theorem seal_keepsV (v : GcmImpl) : («seal» v.callees).allInstrs keepsV = true := by
  simp only [«seal», sealRest, j0, j0hash, oneAad, absorbAl, encBody, fo, textAbs, finBody, tag, crypt, crSeg1,
    crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor,
    padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.gh.keepsV]; lit_decide

theorem open_keepsV (v : GcmImpl) : («open» v.callees).allInstrs keepsV = true := by
  simp only [«open», openEntry, openRest, openMain, oneCrypt, cryptAl, crArgs, tagLenOk, tagIn, cmpSeg, cmp,
    cmp16, j0, j0hash, oneAad, absorbAl, decAbs, fo, textAbs, finBody, tag, crypt, crSeg1, crSeg2, crTail,
    ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, copyB, xorB, Impl.AesGcm.AArch64.xor, padSeg, flush,
    lens, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.gh.keepsV]
  lit_decide

/-! ## Correctness -/

theorem init_correct (v : GcmImpl) (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa (init v.callees) s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  WP.withPreservedV (init_wp v hs) (init_keepsV v)

theorem streamEncrypt_correct (v : GcmImpl) (s : State) (hs : streamEncryptAArch64.pre s) :
    ∃ t s', Exec isa (streamEncrypt v.callees) s t s' ∧ abiPreserved s s' ∧ streamEncryptAArch64.post s s' :=
  WP.withPreservedV (streamEncrypt_wp v hs) (streamEncrypt_keepsV v)

theorem streamDecrypt_correct (v : GcmImpl) (s : State) (hs : streamDecryptAArch64.pre s) :
    ∃ t s', Exec isa (streamDecrypt v.callees) s t s' ∧ abiPreserved s s' ∧ streamDecryptAArch64.post s s' :=
  WP.withPreservedV (streamDecrypt_wp v hs) (streamDecrypt_keepsV v)

theorem streamFinish_correct (v : GcmImpl) (s : State) (hs : streamFinishAArch64.pre s) :
    ∃ t s', Exec isa (streamFinish v.callees) s t s' ∧ abiPreserved s s' ∧ streamFinishAArch64.post s s' :=
  WP.withPreservedV (streamFinish_wp v hs) (streamFinish_keepsV v)

theorem streamVerify_correct (v : GcmImpl) (s : State) (hs : streamVerifyAArch64.pre s) :
    ∃ t s', Exec isa (streamVerify v.callees) s t s' ∧ abiPreserved s s' ∧ streamVerifyAArch64.post s s' :=
  WP.withPreservedV (streamVerify_wp v hs) (streamVerify_keepsV v)

theorem seal_correct (v : GcmImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa («seal» v.callees) s t s' ∧ abiPreserved s s' ∧ sealAArch64.post s s' :=
  WP.withPreservedV (seal_wp v hs) (seal_keepsV v)

theorem open_correct (v : GcmImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa («open» v.callees) s t s' ∧ abiPreserved s s' ∧ openAArch64.post s s' :=
  WP.withPreservedV (open_wp v hs) (open_keepsV v)

/-! ## States satisfying the preconditions (with empty buffers)

The stack pointer is `0x8000`, and the 3264 bytes below it are apart from
every buffer. -/

def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 768⟩]

def streamCryptSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x4 => 0x2000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 768⟩]

def finSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x4 => 0x5000 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 768⟩]

def verSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x4 => 0x5000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 768⟩]

/-- `tag` at `0x6000` and `work` at `0x5000` (`[sp]`). -/
def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | .x7 => 0x6000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8001 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x6000, 16⟩, ⟨0x5000, 768⟩]

/-- `tag` at `0x6000`, `tag_len` 0 (`[sp]`) and `work` at `0x5000` (`[sp + 8]`). -/
def openSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | .x7 => 0x6000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8009 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x6000, 0⟩, ⟨0x8000, 16⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 768⟩]

/-! ## The shared contracts -/

theorem init_verified (v : GcmImpl) :
    Verified AArch64.target (init v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.initSig "scratch" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.initPost AArch64.abi.ptrBits) true 3264) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.initSig,
      Spec.Sm4.Gcm.initPost, initAArch64, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow]
      [initSat] using initSat)

theorem streamEncrypt_verified (v : GcmImpl) :
    Verified AArch64.target (streamEncrypt v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.streamCryptSig "scratch" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamEncryptPost AArch64.abi.ptrBits) true 3264) :=
  Verified.of_correct (streamEncrypt_correct v) (streamEncrypt_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow,
      Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamEncryptPost, streamEncryptAArch64, streamCryptPre, streamCryptPub]
      [streamCryptSat] using streamCryptSat)

theorem streamDecrypt_verified (v : GcmImpl) :
    Verified AArch64.target (streamDecrypt v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.streamCryptSig "scratch" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamDecryptPost AArch64.abi.ptrBits) true 3264) :=
  Verified.of_correct (streamDecrypt_correct v) (streamDecrypt_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow,
      Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamDecryptPost, streamDecryptAArch64, streamCryptPre, streamCryptPub]
      [streamCryptSat] using streamCryptSat)

theorem streamFinish_verified (v : GcmImpl) :
    Verified AArch64.target (streamFinish v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.streamFinishSig "work" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamFinishPost AArch64.abi.ptrBits) true 3264) :=
  Verified.of_correct (streamFinish_correct v) (streamFinish_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow,
      Spec.Sm4.Gcm.streamFinishSig, Spec.Sm4.Gcm.streamFinishPost, streamFinishAArch64, finPre]
      [finSat] using finSat)

theorem streamVerify_verified (v : GcmImpl) :
    Verified AArch64.target (streamVerify v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.streamVerifySig "work" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamVerifyPost AArch64.abi.ptrBits) true 3264) :=
  Verified.of_correct (streamVerify_correct v) (streamVerify_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow,
      Spec.Sm4.Gcm.streamVerifySig, Spec.Sm4.Gcm.streamVerifyPost, streamVerifyAArch64, verPre]
      [verSat] using verSat)

theorem seal_verified (v : GcmImpl) :
    Verified AArch64.target («seal» v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.sealSig "work" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.sealPost AArch64.abi.ptrBits) true 3264) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow,
      Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost, sealAArch64, sealPre, onePub]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem open_verified (v : GcmImpl) :
    Verified AArch64.target («open» v.callees) (Sig.scratchContract AArch64.abi Spec.Sm4.Gcm.openSig "work" .u64 96
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.openPost AArch64.abi.ptrBits) true 3264 (some (Spec.Sm4.Gcm.openLeak AArch64.abi.ptrBits))) :=
  Verified.of_correct (open_correct v) (open_ct v) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, args, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop, stackBelow,
      Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost, openAArch64, openPre, onePub, openRes, openLeakOf, Spec.Sm4.Gcm.openLeak, stackArg, stackArgAddr, Curry.app, Option.map]
      [openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat)

end VG.Proof.Sm4Gcm.AArch64

end

end


/-!
# SM4-GCM on AArch64, with its working space on the stack

Every function of SM4-GCM runs its code, proved with the working space as its
last argument (`Verified.lean`), in a frame that allocates it: 768 bytes for
the working space in a register (`Verified.stackScratch`); for `seal` and
`open`, whose working space is their first and second stack argument, 784
bytes that also hold a copy of the stack argument before it, if any
(`Verified.stackArgScratch`). Below the frame, the code's calls of
`vg_sm4_ctr32` and `vg_sm4_expand_key` use 3264 bytes of stack.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.Impl.Sm4Gcm.AArch64

/-- A state satisfying `vg_sm4_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.initContract AArch64.abi 4032).pre s := by
  implies_sat [Spec.Sm4.Gcm.initContract, Spec.Sm4.Gcm.initSig, Spec.Sm4.Gcm.initPost, AArch64.abi,
    AArch64.argRegs, stackBelow] [initFrameSat, initSat] using initFrameSat

theorem init_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 768 .x2 (init v.callees))
      (Spec.Sm4.Gcm.initContract AArch64.abi 4032) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm4.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 96)
    (post := Spec.Sm4.Gcm.initPost AArch64.abi.ptrBits) (wa := true) (stack := 3264) (bytes := 768)
    (init_verified v) (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.initPostOut_local _ vs m m₁ m₂ r hl) initFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_encrypt`'s precondition, without the working
space. -/
def streamEncryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamEncryptContract AArch64.abi 4032).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamEncryptContract, Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamEncryptPost, AArch64.abi,
    AArch64.argRegs, stackBelow] [streamEncryptFrameSat, streamCryptSat] using streamEncryptFrameSat

theorem streamEncrypt_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (streamEncrypt v.callees))
      (Spec.Sm4.Gcm.streamEncryptContract AArch64.abi 4032) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64) (n := 96)
    (post := Spec.Sm4.Gcm.streamEncryptPost AArch64.abi.ptrBits) (wa := true) (stack := 3264) (bytes := 768)
    (streamEncrypt_verified v) (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.streamEncryptPostOut_local _ vs m m₁ m₂ r hl) streamEncryptFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_decrypt`'s precondition, without the working
space. -/
def streamDecryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamDecryptContract AArch64.abi 4032).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamDecryptContract, Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamDecryptPost, AArch64.abi,
    AArch64.argRegs, stackBelow] [streamDecryptFrameSat, streamCryptSat] using streamDecryptFrameSat

theorem streamDecrypt_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (streamDecrypt v.callees))
      (Spec.Sm4.Gcm.streamDecryptContract AArch64.abi 4032) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64) (n := 96)
    (post := Spec.Sm4.Gcm.streamDecryptPost AArch64.abi.ptrBits) (wa := true) (stack := 3264) (bytes := 768)
    (streamDecrypt_verified v) (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.streamDecryptPostOut_local _ vs m m₁ m₂ r hl) streamDecryptFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition, without the working
space. -/
def streamFinishFrameSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩] }

theorem streamFinishFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamFinishContract AArch64.abi 4032).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamFinishContract, Spec.Sm4.Gcm.streamFinishSig, Spec.Sm4.Gcm.streamFinishPost, AArch64.abi,
    AArch64.argRegs, stackBelow] [streamFinishFrameSat, finSat] using streamFinishFrameSat

theorem streamFinish_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 768 .x5 (streamFinish v.callees))
      (Spec.Sm4.Gcm.streamFinishContract AArch64.abi 4032) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamFinishSig) (nm := "work") (e := .u64) (n := 96)
    (post := Spec.Sm4.Gcm.streamFinishPost AArch64.abi.ptrBits) (wa := true) (stack := 3264) (bytes := 768)
    (streamFinish_verified v) (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.streamFinishPostOut_local _ vs m m₁ m₂ r hl) streamFinishFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition, without the working
space. -/
def streamVerifyFrameSat : State := { verSat with wr := [⟨0x3000, 80⟩] }

theorem streamVerifyFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamVerifyContract AArch64.abi 4032).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamVerifyContract, Spec.Sm4.Gcm.streamVerifySig, Spec.Sm4.Gcm.streamVerifyPost, AArch64.abi,
    AArch64.argRegs, stackBelow] [streamVerifyFrameSat, verSat] using streamVerifyFrameSat

theorem streamVerify_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (streamVerify v.callees))
      (Spec.Sm4.Gcm.streamVerifyContract AArch64.abi 4032) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamVerifySig) (nm := "work") (e := .u64) (n := 96)
    (post := Spec.Sm4.Gcm.streamVerifyPost AArch64.abi.ptrBits) (wa := true) (stack := 3264) (bytes := 768)
    (streamVerify_verified v) (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.streamVerifyPostOut_local _ vs m m₁ m₂ r hl) streamVerifyFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition, without the working
space: no stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩], wr := [⟨0x4000, 0⟩, ⟨0x6000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.sealContract AArch64.abi 4048).pre s := by
  implies_sat [Spec.Sm4.Gcm.sealContract, Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost,
    AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop, stackBelow] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed (v : GcmImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 784 0 («seal» v.callees))
      (Spec.Sm4.Gcm.sealContract AArch64.abi 4048) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Sm4.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.sealPost AArch64.abi.ptrBits) (wa := true) (stack := 3264)
    (bytes := 784) (seal_verified v) (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _)
    (Proof.Sm4Gcm.sealPost_local (pb := AArch64.abi.ptrBits))
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.sealPostOut_local _ vs m m₁ m₂ r hl) sealFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_open`'s precondition, without the working
space: `tag_len` 0, its one stack argument. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x6000, 0⟩, ⟨0x8000, 8⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.openContract AArch64.abi 4048).pre s := by
  implies_sat [Spec.Sm4.Gcm.openContract, Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost,
    Spec.Sm4.Gcm.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
    List.getD, List.range, List.range.loop, stackBelow] [openFrameSat, openSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using openFrameSat

theorem open_framed (v : GcmImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 784 1 («open» v.callees))
      (Spec.Sm4.Gcm.openContract AArch64.abi 4048) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Sm4.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.openPost AArch64.abi.ptrBits) (wa := true) (stack := 3264)
    (bytes := 784) (leak := some (Spec.Sm4.Gcm.openLeak AArch64.abi.ptrBits))
    (open_verified v) (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _)
    (Proof.Sm4Gcm.openPost_local (pb := AArch64.abi.ptrBits))
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.openPostOut_local _ vs m m₁ m₂ r hl) openFrameSat_pre
    (hleak := Proof.Sm4Gcm.openLeak_local (pb := AArch64.abi.ptrBits))

end VG.Proof.Sm4Gcm.AArch64
