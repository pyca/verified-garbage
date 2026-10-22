module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.OneCT
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.OneCT
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.OneShot
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.OneShot
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.FinCT
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Seal
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.FinCT
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Seal
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.BodyCT
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.BodyCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Fn
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.PieceCT
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Rel
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.StreamCryptCT
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.StreamFinish
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.StreamVerify
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.Bits

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
  have qw : stackArg σ₁ w = stackArg σ₂ w := qa w hw
  have o₁ := oneLay h₁
  have o₂ := oneLay h₂
  refine ⟨⟨o₁, rfl, o₁.perm, o₁.hsp, o₁.nonceR, o₁.aadR, o₁.dataW, o₁.args⟩,
    ⟨o₁, qw.symm, ?_, o₂.hsp, ?_, ?_, ?_, ?_⟩⟩
  · have := o₂.perm; rw [← q0, ← qw] at this; exact this
  · have := o₂.nonceR; rw [← q1, ← q2] at this; exact this
  · have := o₂.aadR; rw [← q3, ← q4] at this; exact this
  · have := o₂.dataW; rw [← q5, ← q6] at this; exact this
  · have := o₂.args; rw [← qw] at this; exact this

/-- A stack argument, at `sp + j` with `j < 8 * n`, is outside `work`. -/
theorem OneFacts.argW {σ σ₀ : State} {n w : Nat} (f : OneFacts σ σ₀ n w) {j : Nat} (hj : j + 8 ≤ 8 * n) :
    (⟨σ.sp + BitVec.ofNat 64 j, 8⟩ : Region).Disjoint (workR (stackArg σ₀ w)) := by
  refine f.args.sub_left ?_
  show Region.Sub ⟨σ.sp + BitVec.ofNat 64 j, 8⟩ ⟨σ.sp + BitVec.ofNat 64 (8 * 0), 8 * n⟩
  rw [show σ.sp + BitVec.ofNat 64 (8 * 0) = σ.sp by rw [Nat.mul_zero, BitVec.add_zero]]
  exact Offset.sub_base _ hj

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
  have sub16 : Region.Sub ⟨stackArg σ₀ w + BitVec.ofNat 64 16, 80⟩ (workR (stackArg σ₀ w)) := Lay.wSub (by decide)
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
  have ts : ∃ h, (taint.check (Taint.ofRegs [.x19, .x7])
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
  have i₁ := frontIn_of f₁ rfl rfl rfl rfl rfl rfl (a₁.entered rfl rfl) a₁.rd a₁.wr
  have i₂ := frontIn_of f₂ q1.symm q2.symm q3.symm q4.symm q5.symm q6.symm (a₂.entered q0.symm f₂.hW) a₂.rd a₂.wr
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
  have sub16 : Region.Sub ⟨stackArg σ₁ 0 + BitVec.ofNat 64 16, 80⟩ (workR (stackArg σ₁ 0)) := Lay.wSub (by decide)
  have hal := (σ₁.gpr .x4).isLt
  have hn := (σ₁.gpr .x6).isLt
  refine front_rel L v i₁ i₂ fun u₁ u₂ o₁ o₂ => ?_
  have mkB : ∀ {σ τ u : State}, OneFacts σ σ₁ 1 0 → τ.wr = σ.wr →
      FrontOut (σ₁.gpr .x0) (stackArg σ₁ 0 + BitVec.ofNat 64 16) (stackArg σ₁ 0) σ₁.sp τ.gpr (σ₁.gpr .x5)
        (σ₁.gpr .x4).toNat (σ₁.gpr .x6).toNat τ u →
      BodyIn (σ₁.gpr .x0) (stackArg σ₁ 0 + BitVec.ofNat 64 16) (stackArg σ₁ 0) σ₁.sp u.gpr
        (σ₁.gpr .x6).toNat 0 (σ₁.gpr .x5) (Spec.Gcm.zeros (σ₁.gpr .x4).toNat) []
        (blockAt u.mem (σ₁.gpr .x0 + BitVec.ofNat 64 240)) u := fun f wr o =>
    ⟨o.env, fun _ _ => rfl, by rw [o.x25, Proof.Gcm.length_zeros],
      o.x26, o.x27, o.x28, rfl, by decide,
      ⟨⟨covers_left (by rw [o.wr, wr]; exact f.dataW), hn, ol.dw, ol.data.sub_right sub16, ol.data⟩,
        by rw [o.wr, wr]; exact f.dataW, ol.cd, ol.kd⟩, rfl⟩
  have B₁ := mkB f₁ a₁.wr o₁
  have B₂ := mkB f₂ a₂.wr o₂
  refine rel_seq (encBody_rel L v B₁ B₂ rfl) (WP.with_rdwr (encBody_ok L v B₁ 0))
    (WP.with_rdwr (encBody_ok L v B₂ 0)) fun w₁ w₂ ⟨b₁, _, _⟩ ⟨b₂, _, _⟩ => ?_
  have sl : ∀ {τ u ω : State},
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
  have e₁ := (b₁.env.of_regs r₁).of_regs r₁'
  have e₂ := (b₂.env.of_regs r₂).of_regs r₂'
  have y26₁ : z₁'.gpr .x26 = _ := (r₁'.others .x26 (by decide)).trans x26₁
  have y26₂ : z₂'.gpr .x26 = _ := (r₂'.others .x26 (by decide)).trans x26₂
  have y27₁ : z₁'.gpr .x27 = _ := (r₁'.others .x27 (by decide)).trans x27₁
  have y27₂ : z₂'.gpr .x27 = _ := (r₂'.others .x27 (by decide)).trans x27₂
  refine rel_seq (finBody_rel L v (.inl rfl) e₁ e₂ (fun _ _ => rfl)
      (fun _ _ => rfl) y26₁ y26₂ y27₁ y27₂ hal hn)
    (finBody_env v L (.inl rfl) e₁ (fun _ _ => rfl) y26₁ y27₁ hn)
    (finBody_env v L (.inl rfl) e₂ (fun _ _ => rfl) y26₂ y27₂ hn) fun g₁ g₂ h₁ h₂ => ?_
  have c28₁ : g₁.gpr .x28 = σ₁.gpr .x7 := (h₁.2.1 .x28 (by decide)).trans x28₁
  have c28₂ : g₂.gpr .x28 = σ₁.gpr .x7 := (h₂.2.1 .x28 (by decide)).trans x28₂
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
