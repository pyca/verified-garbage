module
public import VerifiedGarbage.Proof.AesGcm.Arm.OneShot

import VerifiedGarbage.Proof.AesGcm.Arm.Seal
import VerifiedGarbage.Proof.AesGcm.Arm.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.Arm.StreamVerify
import VerifiedGarbage.Proof.AesGcm.Arm.Compare
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. `open` checks the tag length;
if it is allowed, it computes the tag of the ciphertext into `W + 112`
(`oneAad`, `oneTag 112`), copies the received tag (at `tag`) to `W + 256`, compares
the first `tag_len` bytes of each, and decrypts the data in place only if
they are equal; `r0` is the result (`open_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph ghashInput fullTag zeros padLen j0 inc32 gctr decryptWith openResult toBytes)
open VG.Proof.Gcm (Absorbed)

theorem SO1.keep {n wi : Nat} {s₀ s₁ s₂ : State} (h1 : SO1 n wi s₀ s₁)
    (hg : ∀ r, r ≠ .r0 → r ≠ .r6 → s₂.gpr r = s₁.gpr r) (hk : Keeps s₁ s₂) : SO1 n wi s₀ s₂ :=
  ⟨h1.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hk.sp hk.rd hk.wr,
    by rw [hg _ (by decide) (by decide)]; exact h1.r4, by rw [hg _ (by decide) (by decide)]; exact h1.r5,
    h1.args.of_eq hk.mem hk.sp hk.rd hk.wr, hk.mem ▸ h1.saved, hk.mem ▸ h1.frame⟩

/-! ## The layout of `open` and `open_to` -/

/-- The words of stack arguments, `work` included: 7 in place, 9 out of place. -/
abbrev oNa : Bool → Nat | false => 7 | true => 9
/-- The index of `work`. -/
abbrev oWi : Bool → Nat | false => 6 | true => 8
/-- The index of `tag`. -/
abbrev oTi : Bool → Nat | false => 4 | true => 6
/-- The index of `tag_len`. -/
abbrev oLi : Bool → Nat | false => 5 | true => 7
/-- Where the text is written: `data` in place, `dst` out of place. -/
abbrev oDi : Bool → Nat | false => 2 | true => 4

theorem tagOff_eq (to : Bool) : 4 * oTi to = tagOff to := by cases to <;> rfl
theorem tagLenOff_eq (to : Bool) : 4 * oLi to = tagLenOff to := by cases to <;> rfl
theorem workOff_eq (to : Bool) : 4 * oWi to = workOff to := by cases to <;> rfl
theorem tagOff_lt (to : Bool) : tagOff to < 4096 := by cases to <;> decide
theorem tagLenOff_lt (to : Bool) : tagLenOff to < 4096 := by cases to <;> decide

/-- The destination, apart from everything the code writes but it, and (out
of place) from the source; out of place, the 12 bytes below the stack
pointer that the call of `vg_aes_ctr32_to` pushes are apart from what that
call reads and writes. -/
def DstOk : Bool → State → Prop
  | false, s => (⟨State.addr (arg s 2), (arg s 3).toNat⟩ : Region) ∈ s.wr
  | true, s =>
    let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
    let src : Region := ⟨State.addr (arg s 2), (arg s 3).toNat⟩
    let dst : Region := ⟨State.addr (arg s 4), (arg s 3).toNat⟩
    let work : Region := ⟨State.addr (arg s 8), 2560⟩
    dst ∈ s.wr ∧ ctx.Disjoint dst ∧ src.Disjoint dst ∧ dst.Disjoint work ∧ dst.Disjoint (args s 9) ∧
      (bel s).Disjoint dst ∧ (arg s 4).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ 12 ≤ s.sp.toNat ∧
      (below12 s.sp).Disjoint ctx ∧ (below12 s.sp).Disjoint src ∧ (below12 s.sp).Disjoint dst ∧
      (below12 s.sp).Disjoint work

/-- What `open` (`to = false`) and `open_to` need: `onePre`, the received tag
readable, apart from `W` and the stack, and the destination. -/
structure OPre (to : Bool) (s₀ : State) : Prop where
  one : onePre (oNa to) (oWi to) s₀
  trd : (⟨State.addr (arg s₀ (oTi to)), (arg s₀ (oLi to)).toNat⟩ : Region) ∈ s₀.rd
  tW : (⟨State.addr (arg s₀ (oTi to)), (arg s₀ (oLi to)).toNat⟩ : Region).Disjoint ⟨State.addr (arg s₀ (oWi to)), 2560⟩
  bT : (bel s₀).Disjoint ⟨State.addr (arg s₀ (oTi to)), (arg s₀ (oLi to)).toNat⟩
  fT : (arg s₀ (oTi to)).toNat + (arg s₀ (oLi to)).toNat ≤ 2 ^ 32
  dst : DstOk to s₀

theorem openPreArm.oPre {s₀ : State} (ho : openPreArm s₀) : OPre false s₀ :=
  have t := openPreArm.tag ho
  ⟨openPreArm.one ho, t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩

/-- What `open` promises, given the result `r0` and the data. -/
def OpenPost (s₀ s : State) : Prop :=
  match openRes s₀ with
  | some pt => s.gpr .r0 = 1 ∧ bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = pt
  | none => s.gpr .r0 = 0 ∧
      bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat

theorem openPost_none {s₀ s : State} (h : openRes s₀ = none) (h0 : s.gpr .r0 = 0)
    (hd : bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat) :
    OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

theorem openPost_some {s₀ s : State} {pt : List Byte} (h : openRes s₀ = some pt) (h0 : s.gpr .r0 = 1)
    (hd : bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = pt) : OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

/-- Whether the computed tag, cut to the tag length, is the received one. -/
abbrev openTagOk (to : Bool) (s₀ : State) : Prop :=
  (fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat)
      (bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat)
      (bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat)).take (arg s₀ (oLi to)).toNat =
    bytesAt s₀.mem (State.addr (arg s₀ (oTi to))) (arg s₀ (oLi to)).toNat

/-- After the tags are compared, with the result in `r7` and `Z`. -/
structure OpenMid (to : Bool) (s₀ s : State) : Prop where
  env : Env (s₀.gpr .r0) (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp (s.gpr .r7) (s₀.gpr .r1) s
  args : ArgsKeep (oNa to) s₀ s
  saved : SavedAt s.mem (arg s₀ (oWi to)) s₀
  dat : bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat
  ciph : ciphOf s.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
    ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat
  cb : blockAt s.mem (State.addr (oSt s₀ (oWi to)) + BitVec.ofNat 64 48) =
    inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat))
  r7 : s.gpr .r7 = if openTagOk to s₀ then 1 else 0
  z : s.z = decide (¬ openTagOk to s₀)

/-- `open` up to the comparison of the tags, followed by any `T`. -/
theorem open_head {to : Bool} {s₀ s₂ : State} (ho : OPre to s₀) (h2 : SO1 (oNa to) (oWi to) s₀ s₂)
    (hok : Spec.Gcm.tagLenOk (arg s₀ (oLi to)).toNat = true) {T : Prog isa} {Q : State → Prop}
    (k : ∀ s₈, OpenMid to s₀ s₈ → WP isa T s₈ Q) :
    WP isa (.seq oneAad (.seq (oneTag uO) (.seq (.block [.ldrSp .r6 (tagLenOff to)]) (.seq (recvAt (tagOff to))
      (.seq (cmp uO) (.seq (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) T)))))) s₂ Q := by
  have h : onePre (oNa to) (oWi to) s₀ := ho.one
  have tW := ho.tW
  have bT := ho.bT
  have fT := ho.fT
  have dTW : ∀ {d k : Nat}, d + k ≤ 2560 →
      (⟨State.addr (arg s₀ (oTi to)), (arg s₀ (oLi to)).toNat⟩ : Region).Disjoint
      ⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 d, k⟩ := fun hd => tW.sub_right (Lay.wSub hd)
  have L := oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ (oNa to) ∈ s₀.rd := h.1.2.2.2
  obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (164 ≤ d ∨ d + k ≤ 128) →
      (savedR (arg s₀ (oWi to))).Disjoint ⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ h₂ => Lay.w_w (by omega) (by decide) h₁
  refine WP.seq (WP.mono (oneAad_ok h (by cases to <;> decide) h2) fun s₃ oa => ?_)
  obtain ⟨k7, he₃⟩ := oa.env
  refine WP.seq (WP.mono (oneTag_ok h (by cases to <;> decide) (o := 112) (.inr rfl) he₃ oa.args oa.hH (length_bytesAt _ _ _).symm
    oa.abs) fun s₄ ot => ?_)
  obtain ⟨k7₄, he₄⟩ := ot.env
  obtain ⟨j5, w5⟩ := ot.args.at spf hin (oLi to) (by cases to <;> decide) (tagLenOff_eq to)
  have htl := tagLenOff_lt to
  obtain ⟨s₅, run₅, h6₅, g₅, k₅⟩ : ∃ s₅, runBlock isa [.ldrSp .r6 (tagLenOff to)] s₄ = some s₅ ∧
      s₅.gpr .r6 = BitVec.ofNat 32 (arg s₀ (oLi to)).toNat ∧ (∀ r, r ≠ .r6 → s₅.gpr r = s₄.gpr r) ∧
      Keeps s₄ s₅ := by
    refine ⟨_, by arun [j5, w5, htl], ?_, ?_, ?_⟩
    · simp [gpr_setReg, w5]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide)) k₅.sp k₅.rd k₅.wr
  have hk₅ := ot.args.of_eq k₅.mem k₅.sp k₅.rd k₅.wr
  obtain ⟨i4, v4⟩ := hk₅.at spf hin (oTi to) (by cases to <;> decide) (tagOff_eq to)
  refine WP.seq (WP.mono (recvAt_ok L (tagOff_lt to) he₅ i4 v4
    (by rw [hk₅.rd, hk₅.wr]; exact covers_of_mem (List.mem_append_left _ ho.trd)) fT
    (dTW (by decide)) h6₅ t1 t16) fun s₆ hh => ?_)
  obtain ⟨hb₆, hf₆, g₆, rd₆, wr₆, sp₆⟩ := hh
  have he₆ := he₅.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) sp₆ rd₆ wr₆
  have h6₆ : s₆.gpr .r6 = BitVec.ofNat 32 (arg s₀ (oLi to)).toNat := by
    rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), h6₅]
  refine WP.seq (WP.mono (cmp_ok L he₆ (o := 112) (.inr rfl) h6₆ t1 t16) fun s₇ hh => ?_)
  obtain ⟨h0₇, hf₇, g₇, rd₇, wr₇, sp₇⟩ := hh
  have he₇ := he₆.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) sp₇ rd₇ wr₇
  -- what the pieces leave
  let rs : List Region := [savedR (arg s₀ (oWi to))] ++ j0Frame (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp ++
    otFrame (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp 112 ++
    [⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 256, 16⟩, ⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 240, 16⟩]
  have F₇ : Frame rs s₀.mem s₇.mem := by
    have e₂ : Frame [savedR (arg s₀ (oWi to))] s₀.mem s₂.mem := h2.frame
    refine ((((e₂.mono ?_).trans (oa.frame.mono ?_)).trans (ot.frame.mono ?_)).trans
      ((k₅.mem ▸ hf₆ : Frame _ s₄.mem s₆.mem).mono ?_)).trans (hf₇.mono ?_)
    all_goals intro r hr; simp only [rs, List.mem_append]
    · exact .inl (.inl (.inl hr))
    · exact .inl (.inl (.inr hr))
    · exact .inl (.inr hr)
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
  have hp := h
  obtain ⟨-, -, dcD, dcW, -, -, -, -, dDW, -, -, bc, -, -, bD, bW, -⟩ := hp
  have dC : ∀ r ∈ rs, (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [rs, List.mem_append] at hr
    rcases hr with ((hr | hr) | hr) | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.cs
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.kc.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.cs.sub_right (Region.sub_prefix (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.kc.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
  have dD : ∀ r ∈ rs, (⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩ : Region).Disjoint r := by
    intro r hr
    simp only [rs, List.mem_append] at hr
    rcases hr with ((hr | hr) | hr) | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact dDW.sub_right (Lay.wSub (by decide))
    · exact one_dataJ0 h dDW bD r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [oSt_addr h]; exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact bD.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
  let ciph := ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat
  let H := ctxH s₀.mem (State.addr (s₀.gpr .r0))
  let iv := bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat
  let aad := bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat
  let dat := bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat
  let tl := (arg s₀ (oLi to)).toNat
  let tag₀ := bytesAt s₀.mem (State.addr (arg s₀ (oTi to))) tl
  have F₃ : Frame ([savedR (arg s₀ (oWi to))] ++ j0Frame (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp) s₀.mem s₃.mem :=
    (h2.frame.mono fun r hr => List.mem_append_left _ hr).trans (oa.frame.mono fun r hr => List.mem_append_right _ hr)
  have sub₃ : ∀ r ∈ [savedR (arg s₀ (oWi to))] ++ j0Frame (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp, r ∈ rs := fun r hr => by
    simp only [rs, List.mem_append] at hr ⊢; exact .inl (.inl hr)
  have hD₃ : bytesAt s₃.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = dat :=
    bytesAt_frame F₃ (fun r hr => dD r (sub₃ r hr)) (by omega)
  have hT₄ : bytesAt s₄.mem (State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 112) 16 = fullTag ciph H iv aad dat := by
    rw [ot.out, hD₃, ciph_keep F₃ (fun r hr => dC r (sub₃ r hr)) hR, oa.j, ← Proof.Gcm.fullTag_eq]
  have F₄ : Frame ([savedR (arg s₀ (oWi to))] ++ j0Frame (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp ++ otFrame (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp 112)
      s₀.mem s₄.mem :=
    (F₃.mono fun r hr => List.mem_append_left _ hr).trans (ot.frame.mono fun r hr => List.mem_append_right _ hr)
  have hR₀ : bytesAt s₄.mem (State.addr (arg s₀ (oTi to))) tl = tag₀ := by
    refine bytesAt_frame F₄ (fun r hr => ?_) (by omega)
    have hst := oSt_addr h
    have z : ∀ {d k : Nat}, d + k ≤ 2560 → 16 ≤ d →
        (⟨State.addr (arg s₀ (oTi to)), tl⟩ : Region).Disjoint ⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 d, k⟩ :=
      fun h₁ _ => dTW h₁
    simp only [List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact z (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hst]; exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact bT.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hst]; exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact bT.symm
  have hX : (bytesAt s₆.mem (State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 112) tl ++ zeros (16 - tl) =
      bytesAt s₆.mem (State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 256) 16) ↔ (fullTag ciph H iv aad dat).take tl = tag₀ := by
    rw [hb₆, k₅.mem, hR₀, bytesAt_frame hf₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by decide))
        (by omega), k₅.mem, bytesAt_take _ _ t16, hT₄, List.append_cancel_right_eq]
  let X : Prop := bytesAt s₆.mem (State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 112) tl ++ zeros (16 - tl) =
      bytesAt s₆.mem (State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 256) 16
  obtain ⟨s₈, run₈, h7₈, hz₈, g₈, k₈⟩ : ∃ s₈, runBlock isa [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)] s₇ = some s₈ ∧
      s₈.gpr .r7 = s₇.gpr .r0 ∧ s₈.z = decide ((s₇.gpr .r0).toNat = 0) ∧ (∀ r, r ≠ .r7 → s₈.gpr r = s₇.gpr r) ∧
      Keeps s₇ s₈ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp only [z_subFlags, gpr_setReg, reduceCtorEq, ite_false]; exact z_sub0 _
    · intro r hr; simp only [gpr_subFlags, gpr_setReg, hr, ite_false]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
  have he₈ := he₇.set7 h7₈ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₈ _ (by decide)) k₈.sp k₈.rd k₈.wr
  have dA6 : ∀ {d : Nat}, d + 16 ≤ 2560 → ∀ r ∈ [(⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 d, 16⟩ : Region)],
      (args s₀ (oNa to)).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (h.2.2.2.2.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
  have hk₈ : ArgsKeep (oNa to) s₀ s₈ :=
    ((((ot.args.of_eq k₅.mem k₅.sp k₅.rd k₅.wr).frame spf hf₆ (dA6 (by decide)) sp₆ rd₆ wr₆).frame spf hf₇
      (dA6 (by decide)) sp₇ rd₇ wr₇).of_eq k₈.mem k₈.sp k₈.rd k₈.wr)
  have F₈ : Frame rs s₀.mem s₈.mem := by rw [k₈.mem]; exact F₇
  have hdat₈ : bytesAt s₈.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = dat := bytesAt_frame F₈ dD (by omega)
  have hc₈ : ciphOf s₈.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat = ciph := ciph_keep F₈ dC hR
  have hcb₈ : blockAt s₈.mem (State.addr (oSt s₀ (oWi to)) + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
    have F₃₈ : Frame (otFrame (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp 112 ++
        [⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 256, 16⟩, ⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 240, 16⟩])
        s₃.mem s₈.mem := by
      rw [k₈.mem]
      refine ((ot.frame.mono fun r hr => List.mem_append_left _ hr).trans
        ((k₅.mem ▸ hf₆ : Frame _ s₄.mem s₆.mem).mono fun r hr => ?_)).trans (hf₇.mono fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; simp [hr]
      · simp only [List.mem_singleton] at hr; simp [hr]
    rw [blockAt_frame F₃₈ (fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
      · have := Lay.st_st (st := oSt s₀ (oWi to)) (a := 48) (n := 16) (d := 0) (k := 48) (.inr (by decide)) (by decide)
          (by decide)
        rwa [add_ofNat_zero] at this
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact (L.stk_st (by decide)).symm
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩))]
    exact oa.cb
  have F₂₈ : Frame (j0Frame (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp ++ otFrame (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp 112 ++
      [⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 256, 16⟩, ⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 240, 16⟩])
      s₂.mem s₈.mem := by
    rw [k₈.mem]
    refine (((oa.frame.mono ?_).trans (ot.frame.mono ?_)).trans
      ((k₅.mem ▸ hf₆ : Frame _ s₄.mem s₆.mem).mono ?_)).trans (hf₇.mono ?_)
    all_goals intro r hr; simp only [List.mem_append]
    · exact .inl (.inl hr)
    · exact .inl (.inr hr)
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
  have sv₈ : SavedAt s₈.mem (arg s₀ (oWi to)) s₀ := by
    refine h2.saved.frame F₂₈ fun r hr => ?_
    simp only [List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact saved_j0Frame L r hr
    · exact saved_otFrame h (.inr rfl) r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dW (by decide) (.inl (by decide))
      · exact dW (by decide) (.inl (by decide))
  have hX0 : (s₇.gpr .r0).toNat = 0 ↔ ¬X := by
    rw [h0₇]
    split
    · next hx => exact ⟨fun e => absurd e (by decide), fun e => absurd hx e⟩
    · next hx => exact ⟨fun _ => hx, fun _ => rfl⟩
  refine k s₈ ⟨by rw [h7₈]; exact he₈, hk₈, sv₈, hdat₈, hc₈, hcb₈, ?_, ?_⟩
  · rw [h7₈, h0₇]; exact ite_congr (propext hX) (fun _ => rfl) (fun _ => rfl)
  · rw [hz₈]; exact decide_eq_decide.mpr (hX0.trans (not_congr hX))

/-! ## Out of place -/

theorem below12_args (s : State) {n : Nat} (hf : s.sp.toNat + 4 * n ≤ 2 ^ 32) (h12 : 12 ≤ s.sp.toNat) :
    (below12 s.sp).Disjoint (args s n) := by
  simp only [args, argAddr_zero]
  exact (VG.Offset.base_disjoint_below (State.addr s.sp) (n := 12) (k := 4 * n) (by omega)).symm

theorem dataArgsTo_run {s₀ s : State} (hk : ArgsKeep 9 s₀ s) (hf : s₀.sp.toNat + 4 * 9 ≤ 2 ^ 32)
    (hin : args s₀ 9 ∈ s₀.rd) :
    ∃ s', runBlock isa dataArgsTo s = some s' ∧ s'.gpr .r4 = arg s₀ 2 ∧ s'.gpr .r5 = arg s₀ 3 ∧
      s'.gpr .r6 = arg s₀ 4 ∧ (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨a2, v2⟩ := hk.at hf hin 2 (by decide) (show 4 * 2 = 8 from rfl)
  obtain ⟨a3, v3⟩ := hk.at hf hin 3 (by decide) (show 4 * 3 = 12 from rfl)
  obtain ⟨a4, v4⟩ := hk.at hf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
  refine ⟨_, by simp only [dataArgsTo]; arun [a2, v2, a3, v3, a4, v4], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, v2]
  · simp [gpr_setReg, v3]
  · simp [gpr_setReg, v4]
  · intro r x y z; simp [gpr_setReg, x, y, z]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- After `oneCryptG true`, from `m₀`. -/
structure OCTo (s₀ : State) (k7 : BitVec 32) (icb : Block) (m₀ : Mem) (s : State) : Prop where
  env : Env (s₀.gpr .r0) (oSt s₀ (oWi true)) (arg s₀ (oWi true)) s₀.sp k7 (s₀.gpr .r1) s
  args : ArgsKeep (oNa true) s₀ s
  out : bytesAt s.mem (State.addr (arg s₀ 4)) (arg s₀ 3).toNat =
    gctr (ciphOf m₀ (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) icb (bytesAt m₀ (State.addr (arg s₀ 2)) (arg s₀ 3).toNat)
  frame : Frame (crFrameG true (oSt s₀ (oWi true)) (arg s₀ (oWi true)) s₀.sp (arg s₀ 4) (arg s₀ 3).toNat) m₀ s.mem

/-- After `dataArgsTo`, with the public values named: `cryptTo` runs from
the first counter block, keeping the stack arguments. -/
theorem cryptTo_in {s₀ s₁ : State} (ho : OPre true s₀) {c st w sp k7 k8 S T : BitVec 32} {R n : Nat}
    (ec : s₀.gpr .r0 = c) (ew : arg s₀ (oWi true) = w) (est : oSt s₀ (oWi true) = st) (esp : s₀.sp = sp)
    (ek : s₀.gpr .r1 = k8) (eR : (s₀.gpr .r1).toNat = R) (eS : arg s₀ 2 = S) (eT : arg s₀ 4 = T)
    (en : (arg s₀ 3).toNat = n) (he : Env c st w sp k7 k8 s₁) (hk : ArgsKeep (oNa true) s₀ s₁)
    (h4 : s₁.gpr .r4 = S) (h5 : s₁.gpr .r5 = BitVec.ofNat 32 n) (h6 : s₁.gpr .r6 = T) (icb : Block) :
    CrMidG true c st w sp k7 k8 R icb 0 S T n s₁.mem 0 s₁ ∧
      WP isa cryptTo s₁ fun s₂ => CrOutG true c st w sp k7 k8 R icb 0 S T n s₁.mem s₂ ∧
        ArgsKeep (oNa true) s₀ s₂ := by
  subst ec ew est esp ek eR eS eT en
  have h := ho.one
  have L := oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have dWA := h.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨dw, cD, sD, dW, dA, bD, fD, sp12, b12c, b12s, b12d, b12w⟩ := ho.dst
  have hst := oSt_addr h
  have dok : DataOk (oSt s₀ (oWi true)) (arg s₀ (oWi true)) s₀.sp s₁ (arg s₀ 4) (arg s₀ 3).toNat :=
    ⟨by rw [hk.rd, hk.wr]; exact covers_left (covers_of_mem dw), (arg s₀ 3).isLt, fD, oSt_disj h dW, dW, bD⟩
  have ci : CrMidG true (s₀.gpr .r0) (oSt s₀ (oWi true)) (arg s₀ (oWi true)) s₀.sp k7 (s₀.gpr .r1)
      (s₀.gpr .r1).toNat icb 0 (arg s₀ 2) (arg s₀ 4) (arg s₀ 3).toNat s₁.mem 0 s₁ :=
    ⟨he, Nat.zero_le _, by rw [h4, add_ofNat_zero], by rw [h5, Nat.sub_zero], by rw [he.r8]; simp, hR,
      ⟨dok, by rw [hk.wr]; exact covers_of_mem dw, cD⟩, fun hc₀ => by simpa using hc₀,
      fun _ => by simp [bytesAt]; rfl, by rw [add_ofNat_zero], .inr (by decide), Frame.refl _ _,
      fun _ => by rw [h6, add_ofNat_zero], one_dataOk h hk,
      ⟨sD, sp12, b12c, by rw [hst]; exact b12w.sub_right (Lay.wSub (by decide)), b12w, b12s, b12d⟩⟩
  refine ⟨ci, WP.mono (WP.with_rdwr (cryptTo_ok L ci)) fun s₂ hh => ?_⟩
  obtain ⟨co, rd₂, wr₂, sp₂⟩ := hh
  have hA : ∀ r ∈ crFrameG true (oSt s₀ (oWi true)) (arg s₀ (oWi true)) s₀.sp (arg s₀ 4) (arg s₀ 3).toNat,
      (args s₀ (oNa true)).Disjoint r := by
    intro r hr
    simp only [crFrameG, crFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | rfl
    · exact dA.symm
    · rw [hst, add_ofNat_assoc]; exact (dWA.sub_left (Lay.wSub (by decide))).symm
    · exact (dWA.sub_left (Lay.wSub (by decide))).symm
    · exact (below_args s₀ spf).symm
    · exact (below12_args s₀ spf sp12).symm
  exact ⟨co, hk.frame spf co.frame hA sp₂ rd₂ wr₂⟩

/-- The source decrypted to the destination, from the first counter block. -/
theorem oneCryptTo_ok {s₀ s : State} (ho : OPre true s₀) {k7 : BitVec 32}
    (he : Env (s₀.gpr .r0) (oSt s₀ (oWi true)) (arg s₀ (oWi true)) s₀.sp k7 (s₀.gpr .r1) s)
    (hk : ArgsKeep (oNa true) s₀ s) {icb : Block}
    (hcb : blockAt s.mem (State.addr (oSt s₀ (oWi true)) + BitVec.ofNat 64 48) = icb) :
    WP isa (oneCryptG true) s (OCTo s₀ k7 icb s.mem) := by
  have spf := ho.one.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ (oNa true) ∈ s₀.rd := ho.one.1.2.2.2
  obtain ⟨s₁, run₁, h4, h5, h6, g₁, k₁⟩ := dataArgsTo_run hk spf hin
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have hk₁ := hk.of_eq k₁.mem k₁.sp k₁.rd k₁.wr
  refine WP.mono (cryptTo_in ho rfl rfl rfl rfl rfl rfl rfl rfl rfl he₁ hk₁ h4 (by rw [h5]; simp) h6 icb).2
    fun s₂ ⟨co, hk₂⟩ => ?_
  rw [k₁.mem] at co
  have c0 := Proof.Gcm.ctr_zero s.mem _ (State.addr (oSt s₀ (oWi true)) + BitVec.ofNat 64 64)
    (ciphOf s.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) hcb
  exact ⟨co.env, hk₂, by rw [co.out c0, Proof.Gcm.gctr_eq], co.frame⟩

/-! ## The body -/

/-- What `vg_aes_gcm_open` and `vg_aes_gcm_open_to` compute. -/
abbrev openResG (to : Bool) (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (ctxH s.mem (State.addr (s.gpr .r0)))
    (arg s (oLi to)).toNat (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    (bytesAt s.mem (State.addr (arg s 2)) (arg s 3).toNat) (bytesAt s.mem (State.addr (arg s 0)) (arg s 1).toNat)
    (bytesAt s.mem (State.addr (arg s (oTi to))) (arg s (oLi to)).toNat)

/-- What the body leaves: the result in `r0` and the text at the destination
if it is 1; in place, the data as it was if it is 0 (out of place, the
destination is wiped after). -/
def OpenPostG (to : Bool) (s₀ s : State) : Prop :=
  match openResG to s₀ with
  | some pt => s.gpr .r0 = 1 ∧ bytesAt s.mem (State.addr (arg s₀ (oDi to))) (arg s₀ 3).toNat = pt
  | none => s.gpr .r0 = 0 ∧ (to = false →
      bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat)

/-- The code of the body once the tag length is known to be allowed. -/
abbrev openGood (to : Bool) : Prog isa :=
  .seq oneAad (.seq (oneTag uO) (.seq (.block [.ldrSp .r6 (tagLenOff to)]) (.seq (recvAt (tagOff to))
    (.seq (cmp uO) (.seq (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) (.seq (.ite .eq (.block []) (oneCryptG to))
      (.block [.mov .r0 (.reg .r7)])))))))

/-- What the body leaves, from `s₀`. -/
structure OB (to : Bool) (s₀ s : State) : Prop where
  env : ∃ k7, Env (s₀.gpr .r0) (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp k7 (s₀.gpr .r1) s
  saved : SavedAt s.mem (arg s₀ (oWi to)) s₀
  args : ArgsKeep (oNa to) s₀ s
  post : OpenPostG to s₀ s

theorem open_good {to : Bool} {s₀ s₂ : State} (ho : OPre to s₀) (h2 : SO1 (oNa to) (oWi to) s₀ s₂)
    (hok : Spec.Gcm.tagLenOk (arg s₀ (oLi to)).toNat = true) : WP isa (openGood to) s₂ (OB to s₀) := by
  have h := ho.one
  have L := oneLay h
  refine open_head ho h2 hok fun s₈ om => ?_
  let pt := gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
    (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat)))
    (bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat)
  -- the data decrypted only if the tags are equal
  have mid : WP isa (.ite .eq (.block []) (oneCryptG to)) s₈ fun s₉ =>
      Env (s₀.gpr .r0) (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp (s₈.gpr .r7) (s₀.gpr .r1) s₉ ∧
      SavedAt s₉.mem (arg s₀ (oWi to)) s₀ ∧ ArgsKeep (oNa to) s₀ s₉ ∧
      (openTagOk to s₀ → bytesAt s₉.mem (State.addr (arg s₀ (oDi to))) (arg s₀ 3).toNat = pt) ∧
      (¬openTagOk to s₀ → to = false → bytesAt s₉.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
        bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat) := by
    refine WP.ite _ (eval_eq' om.z) (fun ht => ?_) (fun hf => ?_)
    · have hx : ¬openTagOk to s₀ := of_decide_eq_true ht
      exact WP.block_nil ⟨om.env, om.saved, om.args, fun x => absurd x hx, fun _ _ => om.dat⟩
    · have hx : openTagOk to s₀ := Classical.not_not.mp (of_decide_eq_false hf)
      cases to
      · have hw : (⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩ : Region) ∈ s₀.wr := ho.dst
        refine WP.mono (oneCrypt_ok h hw (by decide) om.env om.args om.cb) fun s₉ oc => ?_
        exact ⟨oc.env, om.saved.frame oc.frame (saved_crFrame L (one_dataW h hw om.args 0 0)), oc.args,
          fun _ => by show bytesAt s₉.mem (State.addr (arg s₀ 2)) _ = _; rw [oc.out, om.ciph, om.dat],
          fun x => absurd hx x⟩
      · refine WP.mono (oneCryptTo_ok ho om.env om.args om.cb) fun s₉ oc => ?_
        obtain ⟨dw, cD, sD, dW, dA, bD, fD, sp12, b12c, b12s, b12d, b12w⟩ := ho.dst
        have sv : ∀ r ∈ crFrameG true (oSt s₀ (oWi true)) (arg s₀ (oWi true)) s₀.sp (arg s₀ 4) (arg s₀ 3).toNat,
            (savedR (arg s₀ (oWi true))).Disjoint r := by
          intro r hr
          simp only [crFrameG, List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · exact saved_crFrame L (c := s₀.gpr .r0) (k7 := 0) (k8 := 0) (s := s₉)
              ⟨⟨covers_left (covers_of_mem (by rw [oc.args.wr]; exact dw)), (arg s₀ 3).isLt, fD, oSt_disj h dW, dW,
                bD⟩, covers_of_mem (by rw [oc.args.wr]; exact dw), cD⟩ r hr
          · exact (b12w.sub_right (Lay.wSub (by decide))).symm
        exact ⟨oc.env, om.saved.frame oc.frame sv, oc.args,
          fun _ => by show bytesAt s₉.mem (State.addr (arg s₀ 4)) _ = _; rw [oc.out, om.ciph, om.dat],
          fun _ h => nomatch h⟩
  refine WP.seq (WP.mono mid fun s₉ hh => ?_)
  obtain ⟨he₉, sv₉, hk₉, hd₁, hd₂⟩ := hh
  refine WP.of_runBlock ⟨s₉.setReg .r0 (s₉.gpr .r7), by arun [], ⟨⟨_, he₉.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl) rfl rfl rfl⟩, sv₉, hk₉.of_eq rfl rfl rfl rfl, ?_⟩⟩
  have hres : openResG to s₀ = if openTagOk to s₀ then some pt else none := by
    simp only [openResG, openResult, hok, ite_true, decryptWith]; rfl
  have r0 : (s₉.setReg .r0 (s₉.gpr .r7)).gpr .r0 = if openTagOk to s₀ then 1 else 0 := by
    rw [gpr_setReg_self, he₉.r7, om.r7]
  unfold OpenPostG
  by_cases e : openTagOk to s₀
  · rw [hres, ite_eq_left_iff.mpr (fun h => absurd e h)]
    exact ⟨r0.trans (ite_eq_left_iff.mpr (fun h => absurd e h)), hd₁ e⟩
  · rw [hres, ite_eq_right_iff.mpr (fun h => absurd h e)]
    exact ⟨r0.trans (ite_eq_right_iff.mpr (fun h => absurd h e)), hd₂ e⟩

/-- The branch on the tag length. -/
theorem openMid_wp {to : Bool} {s₀ s₃ : State} (ho : OPre to s₀) (h3 : SO1 (oNa to) (oWi to) s₀ s₃)
    (hz₃ : s₃.z = !Spec.Gcm.tagLenOk (arg s₀ (oLi to)).toNat) :
    WP isa (.ite .eq (.block [.mov .r0 (imm 0)]) (openGood to)) s₃ (OB to s₀) := by
  have h' := ho.one
  refine WP.ite _ (eval_eq' hz₃) (fun ht => ?_) (fun hf => open_good ho h3 (by simpa using hf))
  have hbad : Spec.Gcm.tagLenOk (arg s₀ (oLi to)).toNat = false := by simpa using ht
  refine WP.of_runBlock ⟨s₃.setReg .r0 (BitVec.ofNat 32 0), by arun [], ⟨_, h3.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl) rfl rfl rfl⟩, h3.saved, h3.args.of_eq rfl rfl rfl rfl, ?_⟩
  unfold OpenPostG
  rw [show openResG to s₀ = none by simp only [openResG, openResult, hbad]; rfl]
  refine ⟨by simp [gpr_setReg], fun _ => ?_⟩
  show bytesAt s₃.mem _ _ = _
  exact bytesAt_frame h3.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h'.2.2.2.2.2.2.2.2.1.sub_right (Lay.wSub (by decide))) (by omega)

/-- The entry, with the tag length in `r6`. -/
theorem openEntry_wp {to : Bool} {s₀ : State} (h : onePre (oNa to) (oWi to) s₀) :
    WP isa (.block (oneEntry (workOff to) ++ ([.ldrSp .r6 (tagLenOff to)] : List Instr))) s₀ fun s =>
      SO1 (oNa to) (oWi to) s₀ s ∧ s.gpr .r6 = BitVec.ofNat 32 (arg s₀ (oLi to)).toNat := by
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ (oNa to) ∈ s₀.rd := h.1.2.2.2
  rw [← workOff_eq to]
  refine WP.block_append (one1_wp h (by cases to <;> decide) (by cases to <;> decide) fun s₁ h1 => ?_)
  obtain ⟨i5, v5⟩ := h1.args.at spf hin (oLi to) (by cases to <;> decide) (tagLenOff_eq to)
  have htl := tagLenOff_lt to
  refine WP.of_runBlock ⟨_, by arun [i5, v5, htl], ?_⟩
  exact ⟨h1.keep (fun r _ b => by simp [gpr_setReg, b]) ⟨rfl, rfl, rfl, rfl⟩, by simp [gpr_setReg, v5]⟩

/-- The body of `open` (`to = false`) and `open_to`, up to their ends. -/
theorem openBody_wp {to : Bool} {s₀ : State} (ho : OPre to s₀) {Q : State → Prop}
    (k : ∀ s, OB to s₀ s → WP isa (openEnd to) s Q) : WP isa (openG to) s₀ Q := by
  have h' := ho.one
  have L := oneLay h'
  have spf := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ (oNa to) ∈ s₀.rd := h'.1.2.2.2
  unfold openG
  rw [← workOff_eq to]
  refine WP.seq (WP.block_append (one1_wp (wi := oWi to) h' (by cases to <;> decide) (by cases to <;> decide)
    fun s₁ h1 => ?_))
  obtain ⟨i5, v5⟩ := h1.args.at spf hin (oLi to) (by cases to <;> decide) (tagLenOff_eq to)
  have htl := tagLenOff_lt to
  obtain ⟨s₂, run₂, h6₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [.ldrSp .r6 (tagLenOff to)] s₁ = some s₂ ∧
      s₂.gpr .r6 = BitVec.ofNat 32 (arg s₀ (oLi to)).toNat ∧ (∀ r, r ≠ .r6 → s₂.gpr r = s₁.gpr r) ∧
      Keeps s₁ s₂ := by
    refine ⟨_, by arun [i5, v5, htl], ?_, ?_, ?_⟩
    · simp [gpr_setReg, v5]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  refine WP.seq (WP.mono (tagLenOk_ok h6₂ (arg s₀ (oLi to)).isLt) fun s₃ ⟨hz₃, g₃, k₃⟩ => ?_)
  have h3 : SO1 (oNa to) (oWi to) s₀ s₃ := (h1.keep (fun r a b => g₂ r b) k₂).keep (fun r a b => g₃ r a) k₃
  exact WP.seq (WP.mono (openMid_wp ho h3 hz₃) k)

theorem open_wp {s₀ : State} (h : openArm.pre s₀) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧ openArm.post s₀ s' := by
  have ho := openPreArm.oPre h
  have h' := ho.one
  have fW := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine openBody_wp ho fun s₄ ob => ?_
  obtain ⟨⟨k7, he⟩, sv, -, op⟩ := ob
  refine WP.mono (restore_ok he.r11 fW (covers_left he.perm.w) sv he.sp) fun s' hh => ⟨hh.1, ?_⟩
  show match openRes s₀ with
    | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = pt
    | none => s'.gpr .r0 = 0 ∧
        bytesAt s'.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat = bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat
  unfold OpenPostG at op
  rw [hh.2.1, hh.2.2.1]
  show match openResG false s₀ with
    | some pt => _ | none => _
  split
  · next pt e => rw [e] at op; exact op
  · next e => rw [e] at op; exact ⟨op.1, op.2 rfl⟩

end VG.Proof.AesGcm.Arm
