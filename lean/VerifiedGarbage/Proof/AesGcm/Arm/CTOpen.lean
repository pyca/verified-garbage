module
public import VerifiedGarbage.Proof.AesGcm.Arm.CTVerify
public import VerifiedGarbage.Proof.AesGcm.Arm.Open
public import VerifiedGarbage.Proof.AesGcm.Arm.CTOne

meta import VerifiedGarbage.Proof.AesGcm.Arm.CTOne
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.Arm.CTFn
import VerifiedGarbage.Proof.AesGcm.Arm.StreamVerify
meta import VerifiedGarbage.Proof.AesGcm.Arm.CTFn
meta import VerifiedGarbage.Proof.AesGcm.Arm.StreamVerify
import VerifiedGarbage.Proof.AesGcm.Arm.Compare
meta import VerifiedGarbage.Proof.AesGcm.Arm.Compare
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.AesGcm.Arm.CTCryptFn
import VerifiedGarbage.Proof.AesGcm.Arm.CTCrypt
import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
import VerifiedGarbage.Proof.AesGcm.Arm.Entry
import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
import VerifiedGarbage.Proof.AesGcm.Arm.Seal
import VerifiedGarbage.Proof.AesGcm.Arm.StreamCrypt
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rsa.ZeroTest32
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Impl.Aes.Arm.Alloc
meta import VerifiedGarbage.Proof.AesGcm.Arm.CTCryptFn
meta import VerifiedGarbage.Proof.AesGcm.Arm.CTVerify
meta import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.Arm.Entry
meta import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.Arm.Open
meta import VerifiedGarbage.Proof.AesGcm.Arm.Seal
meta import VerifiedGarbage.Proof.AesGcm.Arm.StreamCrypt
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Bytes
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.ZeroTest32
meta import VerifiedGarbage.Proof.Sha256.Stream

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_seal` and `vg_aes_gcm_open` are constant time

Untrusted: everything here is checked by Lean. `open` decrypts only if the
tags are equal, which its contract makes public: the comparison, done
without a branch, is related across the runs by what each run computes
(`rel_ghost`, `open_head`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm

theorem one_entry_agree {n wi : Nat} {rs : List Reg} (hrs : ∀ r ∈ rs, r = .r0 ∨ r = .r1 ∨ r = .r2 ∨ r = .r3)
    {s₀ s₀' : State} (h0 : onePre n wi s₀) (h0' : onePre n wi s₀') (hq : onePub n s₀ s₀') :
    ∀ s s', s = s₀ → s' = s₀' → VG.Arm.Taint.Agree (argTaint rs (4 * n)) s s' := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  intro s s' e e'
  subst e e'
  refine (ArgsKeep.refl n s).agree (ArgsKeep.refl n s') q₀
    h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 qa (one_hw h0) (one_hw h0') fun r hr => ?_
  rcases hrs r hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem seal_rel {s₀ s₀' : State} (h0 : sealArm.pre s₀) (h0' : sealArm.pre s₀') (hq : sealArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') «seal» fun _ _ => True := by
  have h6 : onePre 6 5 s₀ := sealPreArm.one h0
  have h6' : onePre 6 5 s₀' := sealPreArm.one h0'
  have hq6 : onePub 6 s₀ s₀' := hq
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := id hq6
  have L := oneLay h6
  have spf := h6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h6'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, -, -, tW, -, -, -, -, -, -, -, -, -, -, -, -, fT, -⟩ := h0
  obtain ⟨-, hwr', -, -, -, -, -, -, -, -, -, -, -, -, tW', -, -, -, -, -, -, -, -, -, -, -, -, fT', -⟩ := h0'
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := SO1 6 5 s₀) (G' := SO1 6 5 s₀')
    (argTaint [.r0, .r1, .r2, .r3] (4 * 6)) (c := .block (oneEntry 20))
    (one_entry_agree (by simp) h6 h6' hq6) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact one1_wp h6 (by decide) (by decide) fun _ h => h)
    (fun s e => by rw [e]; exact one1_wp h6' (by decide) (by decide) fun _ h => h)
  -- the tag copied out
  let W : State → Prop := fun s => s.gpr .r11 = arg s₀ 5
  have c := rel_agree (F := OF 6 5 s₀ s₀) (F' := OF 6 5 s₀ s₀') (G := W) (G' := W) (argTaint [.r11] (4 * 6))
    (c := .block tagOut)
    (fun s s' ⟨_, he, hk⟩ ⟨_, he', hk'⟩ => hk.agree hk' q₀ spf qa (one_hw h6) (one_hw h6') fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [he.r11, he'.r11]) ⟨_, by taint_decide⟩
    (fun s ⟨_, he, hk⟩ => tagOut_wp L (by decide) he hk spf h6.1.2.2.2 (by rw [hwr]; simp) fT
      (tW.sub_right (Region.sub_prefix (by decide))))
    (fun s ⟨_, he, hk⟩ => tagOut_wp L (by decide) he hk spf' h6'.1.2.2.2 (by rw [hwr']; simp) fT'
      (by rw [qa 5 (by decide)]; exact tW'.sub_right (Region.sub_prefix (by decide))))
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have d := RelCT.taint (A := taint) (P := fun s₁ s₂ => W s₁ ∧ W s₂) (c := .block restore)
    (Taint.ofRegs [.r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1, h.2]) hB
  exact a.seq ((oneAad_rel h6 h6' hq6 (by decide) (by decide)).seq ((oneCrypt_rel h6 h6' hq6 (by decide) (by decide)
    (by rw [hwr]; simp) (by rw [hwr']; simp)).seq
    ((oneTag_rel h6 h6' hq6 (by decide) (by decide) (.inl rfl)).seq (c.seq d))))

theorem seal_ct : ConstantTime isa sealArm.pre sealArm.pub «seal» :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (seal_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `open` -/

theorem openRes_isSome {to : Bool} {t : State} (hok : Spec.Gcm.tagLenOk (arg t (oLi to)).toNat = true) :
    (openResG to t).isSome = decide (openTagOk to t) := by
  simp only [openResG, Spec.Gcm.openResult, hok, ite_true, Spec.Gcm.decryptWith]
  by_cases h : openTagOk to t
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), decide_eq_true h]; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), decide_eq_false h]; rfl

section
variable {c st w sp : BitVec 32} {R : Nat} {t₀ : State}

theorem blk_wp {na : Nat} {s : State} (h : P7n na c st w sp R t₀ s) :
    WP isa (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) s (FT na t₀ c st w sp R) := by
  obtain ⟨⟨k7, he, hk⟩, -⟩ := h
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  exact ⟨_, he.set7 rfl (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_subFlags, gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩

theorem mov07_wp {s : State} (h : s.gpr .r11 = w) :
    WP isa (.block [.mov .r0 (.reg .r7)]) s fun s' => s'.gpr .r11 = w :=
  WP.of_runBlock ⟨_, by arun [], by simp [gpr_setReg, h]⟩

theorem daTo_wpI (hf : t₀.sp.toNat + 4 * oNa true ≤ 2 ^ 32) (hin : args t₀ (oNa true) ∈ t₀.rd) {s : State}
    (hs : FT (oNa true) t₀ c st w sp R s) :
    WP isa (.block dataArgsTo) s fun s' => FT (oNa true) t₀ c st w sp R s' ∧
      s'.gpr .r4 = arg t₀ 2 ∧ s'.gpr .r5 = arg t₀ 3 ∧ s'.gpr .r6 = arg t₀ 4 := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ⟨s', run, h4, h5, h6, g, k⟩ := dataArgsTo_run hk hf hin
  exact WP.of_runBlock ⟨s', run, ⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)) k.sp k.rd k.wr,
    hk.of_eq k.mem k.sp k.rd k.wr⟩, h4, h5, h6⟩

end

/-- The source decrypted to the destination, in both runs. -/
theorem oneCryptTo_rel {s₀ s₀' : State} (ho : OPre true s₀) (ho' : OPre true s₀')
    (hq : onePub (oNa true) s₀ s₀') :
    RelCT isa (fun a b => OF (oNa true) (oWi true) s₀ s₀ a ∧ OF (oNa true) (oWi true) s₀ s₀' b) (oneCryptG true)
      fun a b => OF (oNa true) (oWi true) s₀ s₀ a ∧ OF (oNa true) (oWi true) s₀ s₀' b := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := id hq
  have h0 := ho.one
  have h0' := ho'.one
  have L := oneLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ (oNa true) ∈ s₀.rd := h0.1.2.2.2
  have hin' : args s₀' (oNa true) ∈ s₀'.rd := h0'.1.2.2.2
  have e4 : arg s₀' (oWi true) = arg s₀ (oWi true) := (qa (oWi true) (by decide)).symm
  have est : oSt s₀' (oWi true) = oSt s₀ (oWi true) := by show arg s₀' _ + _ = arg s₀ _ + _; rw [e4]
  let D1 : State → State → Prop := fun t₀ s => OF (oNa true) (oWi true) s₀ t₀ s ∧ s.gpr .r4 = arg s₀ 2 ∧
    s.gpr .r5 = arg s₀ 3 ∧ s.gpr .r6 = arg s₀ 4
  have x1 := rel_wp (F := OF (oNa true) (oWi true) s₀ s₀) (F' := OF (oNa true) (oWi true) s₀ s₀')
    (G := D1 s₀) (G' := D1 s₀')
    (argsR (by decide) q₀ spf qa (one_hw h0) (one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2))
    (fun s h => daTo_wpI spf hin h)
    (fun s h => WP.mono (daTo_wpI spf' hin' h) fun s' ⟨y₁, y₂, y₃, y₄⟩ =>
      ⟨y₁, by rw [y₂, qa 2 (by decide)], by rw [y₃, qa 3 (by decide)], by rw [y₄, qa 4 (by decide)]⟩)
  have eR : (s₀'.gpr .r1).toNat = (s₀.gpr .r1).toNat := by rw [q₂]
  have ek : ∀ t : State, (t.gpr .r1).toNat = (s₀.gpr .r1).toNat →
      t.gpr .r1 = BitVec.ofNat 32 (s₀.gpr .r1).toNat := fun t e => by rw [← e]; simp
  have run : ∀ {t : State} (hot : OPre true t) (ec : t.gpr .r0 = s₀.gpr .r0)
      (ew : arg t (oWi true) = arg s₀ (oWi true)) (esp : t.sp = s₀.sp) (eR : (t.gpr .r1).toNat = (s₀.gpr .r1).toNat)
      (eS : arg t 2 = arg s₀ 2) (eT : arg t 4 = arg s₀ 4) (en : arg t 3 = arg s₀ 3) {s : State} (h : D1 t s),
      CrMG true (s₀.gpr .r0) (oSt s₀ (oWi true)) (arg s₀ (oWi true)) s₀.sp (BitVec.ofNat 32 (s₀.gpr .r1).toNat)
        (s₀.gpr .r1).toNat (arg s₀ 2) (arg s₀ 4) (arg s₀ 3).toNat 0 0 s ∧
      WP isa cryptTo s (OF (oNa true) (oWi true) s₀ t) := fun {t} hot ec ew esp eR eS eT en s h =>
    have r := cryptTo_in hot ec ew (by show arg t _ + _ = arg s₀ _ + _; rw [ew]) esp (ek t eR) eR eS eT
      (by rw [en]) h.1.choose_spec.1 h.1.choose_spec.2 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2 (Spec.Gcm.blockAt s.mem 0)
    ⟨⟨_, _, 0, _, rfl, r.1⟩, WP.mono r.2 fun _ ⟨co, hk⟩ => ⟨_, co.env, hk⟩⟩
  have r₀ := @run s₀ ho rfl rfl rfl rfl rfl rfl rfl
  have r₁ := @run s₀' ho' q₁.symm e4 q₀.symm eR (qa 2 (by decide)).symm (qa 4 (by decide)).symm
    (qa 3 (by decide)).symm
  have x2 := rel_wp (F := D1 s₀) (F' := D1 s₀') (G := OF (oNa true) (oWi true) s₀ s₀)
    (G' := OF (oNa true) (oWi true) s₀ s₀')
    (rel_of_ct (cryptTo_ct L) (fun s h => (r₀ h).1) (fun s h => (r₁ h).1))
    (fun s h => (r₀ h).2) (fun s h => (r₁ h).2)
  exact x1.seq x2

/-- The body of `open` (`to = false`) and `open_to`, up to their ends, in
both runs: whether the tags are equal is public. -/
theorem openBody_rel {to : Bool} {s₀ s₀' : State} (ho : OPre to s₀) (ho' : OPre to s₀')
    (hq6 : onePub (oNa to) s₀ s₀') (hres : (openResG to s₀).isSome = (openResG to s₀').isSome)
    {Q : State → State → Prop} (hend : RelCT isa (fun a b => OB to s₀ a ∧ OB to s₀' b) (openEnd to) Q) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (openG to) Q := by
  have h6 := ho.one
  have h6' := ho'.one
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := id hq6
  have L := oneLay h6
  have spf := h6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h6'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ (oNa to) ∈ s₀.rd := h6.1.2.2.2
  have hin' : args s₀' (oNa to) ∈ s₀'.rd := h6'.1.2.2.2
  have hn : 5 ≤ oNa to := by cases to <;> decide
  have hwi : oWi to < oNa to := by cases to <;> decide
  have hli : oLi to < oNa to := by cases to <;> decide
  have hti : oTi to < oNa to := by cases to <;> decide
  have e4 : arg s₀' (oWi to) = arg s₀ (oWi to) := (qa _ hwi).symm
  have h5' : (arg s₀' (oLi to)).toNat = (arg s₀ (oLi to)).toNat := by rw [qa _ hli]
  have eT : arg s₀' (oTi to) = arg s₀ (oTi to) := (qa _ hti).symm
  let W : State → Prop := fun s => s.gpr .r11 = arg s₀ (oWi to)
  have r11 : ∀ {t₀ s : State}, OF (oNa to) (oWi to) s₀ t₀ s → W s := fun h => h.choose_spec.1.r11
  -- the entry, and the tag length
  let G1 : State → State → Prop := fun t₀ s =>
    SO1 (oNa to) (oWi to) t₀ s ∧ s.gpr .r6 = BitVec.ofNat 32 (arg s₀ (oLi to)).toNat
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := G1 s₀) (G' := G1 s₀')
    (argTaint [.r0, .r1, .r2, .r3] (4 * oNa to))
    (c := .block (oneEntry (workOff to) ++ [.ldrSp .r6 (tagLenOff to)]))
    (one_entry_agree (by simp) h6 h6' hq6) (by cases to <;> exact ⟨_, by taint_decide⟩)
    (fun s e => by rw [e]; exact openEntry_wp h6)
    (fun s e => by rw [e]; exact WP.mono (openEntry_wp h6') fun s' ⟨y₁, y₂⟩ => ⟨y₁, by rw [y₂, h5']⟩)
  let G2 : State → State → Prop := fun t₀ s =>
    SO1 (oNa to) (oWi to) t₀ s ∧ s.z = !Spec.Gcm.tagLenOk (arg s₀ (oLi to)).toNat
  have tl : ∀ {t₀ s : State}, G1 t₀ s → WP isa tagLenOk s (G2 t₀) := fun {t₀ s} ⟨h1, h6r⟩ =>
    WP.mono (tagLenOk_ok h6r (arg s₀ (oLi to)).isLt) fun s' ⟨hz, g, k⟩ => ⟨h1.keep (fun r a _ => g r a) k, hz⟩
  obtain ⟨_, hT⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6]) tagLenOk h).isSome = true := ⟨_, by taint_decide⟩
  have b := rel_wp (F := G1 s₀) (F' := G1 s₀') (G := G2 s₀) (G' := G2 s₀')
    (RelCT.taint (A := taint) (Taint.ofRegs [.r6]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]) hT)
    (fun s h => tl h) (fun s h => tl h)
  -- the branches
  let rest6 : Prog isa := .seq (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) (.block [])
  let rest5 : Prog isa := .seq (cmp uO) rest6
  let rest4 : Prog isa := .seq (recvAt (tagOff to)) rest5
  let rest3 : Prog isa := .seq (.block [.ldrSp .r6 (tagLenOff to)]) rest4
  let rest2 : Prog isa := .seq (oneTag uO) rest3
  let Z : State → State → Prop := fun t₀ s => s.z = decide (¬openTagOk to t₀)
  have mid : RelCT isa (fun a b => G2 s₀ a ∧ G2 s₀' b)
      (.ite .eq (.block [.mov .r0 (imm 0)]) (openGood to)) fun a b => W a ∧ W b := by
    refine rel_iteQ (!Spec.Gcm.tagLenOk (arg s₀ (oLi to)).toNat) (fun s h => h.2) (fun s h => h.2)
      (fun _ => ?_) (fun hb => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block [.mov .r0 (imm 0)]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      exact rel_wp (F := G2 s₀) (F' := G2 s₀') (G := W) (G' := W)
        (RelCT.taint (A := taint) (Taint.ofRegs []) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp at hr) hc)
        (fun s h => mov0_wp h.1.env.r11) (fun s h => mov0_wp (by rw [h.1.env.r11, e4]))
    · have hok : Spec.Gcm.tagLenOk (arg s₀ (oLi to)).toNat = true := by simpa using hb
      have hok' : Spec.Gcm.tagLenOk (arg s₀' (oLi to)).toNat = true := by rw [h5']; exact hok
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      have eZ : decide (¬openTagOk to s₀') = decide (¬openTagOk to s₀) := by
        rw [decide_not, decide_not, ← openRes_isSome hok, ← openRes_isSome hok', hres]
      -- what each run reaches: whether the tags are equal
      have pfx : ∀ {t₀ s : State}, OPre to t₀ → Spec.Gcm.tagLenOk (arg t₀ (oLi to)).toNat = true →
          SO1 (oNa to) (oWi to) t₀ s → WP isa (.seq oneAad rest2) s (Z t₀) := fun ht hk h2 =>
        open_head ht h2 hk (T := .block []) fun s₈ om => WP.block_nil om.z
      have y1 := rel_ghost (R := rest2) (Z := Z s₀) (Z' := Z s₀') (oneAad_rel h6 h6' hq6 hn hwi)
      have y2 := rel_ghost (R := rest3) (Z := Z s₀) (Z' := Z s₀')
        (oneTag_rel h6 h6' hq6 hn hwi (o := uO) (.inr rfl))
      let P6s : State → State → Prop := P6n (oNa to) (s₀.gpr .r0) (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp
        (s₀.gpr .r1).toNat (arg s₀ (oLi to)).toNat
      let P7s : State → State → Prop := P7n (oNa to) (s₀.gpr .r0) (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp
        (s₀.gpr .r1).toNat
      have y3 := rel_ghost (R := rest4) (Z := Z s₀) (Z' := Z s₀')
        (rel_agree (F := OF (oNa to) (oWi to) s₀ s₀) (F' := OF (oNa to) (oWi to) s₀ s₀')
          (G := P6s s₀) (G' := P6s s₀')
          (argTaint [] (4 * oNa to)) (c := .block [.ldrSp .r6 (tagLenOff to)])
          (fun s s' h h' => h.choose_spec.2.agree h'.choose_spec.2 q₀ spf qa (one_hw h6) (one_hw h6') (rs := [])
            (by simp)) (by cases to <;> exact ⟨_, by taint_decide⟩)
          (fun s h => ld6n_wp (tagLenOff_lt to) hli (tagLenOff_eq to) spf hin rfl h)
          (fun s h => ld6n_wp (tagLenOff_lt to) hli (tagLenOff_eq to) spf' hin' h5' h))
      have hD : ∀ {d k : Nat}, d + k ≤ 2560 →
          (args s₀ (oNa to)).Disjoint ⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 d, k⟩ :=
        fun hd => (h6.2.2.2.2.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
      have hD' : ∀ {d k : Nat}, d + k ≤ 2560 →
          (args s₀' (oNa to)).Disjoint ⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 d, k⟩ := fun hd => by
        rw [← e4]; exact (h6'.2.2.2.2.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
      have y4 := rel_ghost (R := rest5) (Z := Z s₀) (Z' := Z s₀')
        (rel_agree (F := P6s s₀) (F' := P6s s₀') (G := P6s s₀) (G' := P6s s₀')
          (argTaint [.r6, .r11] (4 * oNa to)) (c := recvAt (tagOff to))
          (fun s s' h h' => h.1.choose_spec.2.agree h'.1.choose_spec.2 q₀ spf qa (one_hw h6) (one_hw h6')
            fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl
              · rw [h.2, h'.2]
              · rw [r11 h.1, r11 h'.1]) (by cases to <;> exact ⟨_, by taint_decide⟩)
          (fun s h => recvn_wp L (tagOff_lt to) hti (tagOff_eq to) spf hin (hD (by decide)) ho.trd ho.fT
            (ho.tW.sub_right (Lay.wSub (by decide))) t1 t16 h)
          (fun s h => recvn_wp L (tagOff_lt to) hti (tagOff_eq to) spf' hin' (hD' (by decide))
            (by rw [← h5']; exact ho'.trd) (by rw [← h5']; exact ho'.fT)
            (by rw [← h5', ← e4]; exact ho'.tW.sub_right (Lay.wSub (by decide))) t1 t16 h))
      obtain ⟨_, c5⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6, .r11]) (cmp uO) h).isSome = true :=
        ⟨_, by taint_decide⟩
      have y5 := rel_ghost (R := rest6) (Z := Z s₀) (Z' := Z s₀')
        (rel_wp (F := P6s s₀) (F' := P6s s₀') (G := P7s s₀) (G' := P7s s₀')
          (RelCT.taint (A := taint) (Taint.ofRegs [.r6, .r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · rw [h.1.2, h.2.2]
            · rw [r11 h.1.1, r11 h.2.1]) c5)
          (fun s h => cmpn_wp L spf (.inr rfl) (hD (by decide)) t1 t16 h)
          (fun s h => cmpn_wp L spf' (.inr rfl) (hD' (by decide)) t1 t16 h))
      obtain ⟨_, c6⟩ : ∃ h, (taint.check (Taint.ofRegs [])
          (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
      have y6 := rel_ghost (R := .block []) (Z := Z s₀) (Z' := Z s₀')
        (rel_wp (F := P7s s₀) (F' := P7s s₀')
          (G := OF (oNa to) (oWi to) s₀ s₀) (G' := OF (oNa to) (oWi to) s₀ s₀')
          (RelCT.taint (A := taint) (Taint.ofRegs []) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
            simp at hr) c6)
          (fun s h => blk_wp h) (fun s h => blk_wp h))
      -- the data decrypted only if the tags are equal, which is public
      have cr : RelCT isa (fun a b => OF (oNa to) (oWi to) s₀ s₀ a ∧ OF (oNa to) (oWi to) s₀ s₀' b)
          (oneCryptG to) fun a b => OF (oNa to) (oWi to) s₀ s₀ a ∧ OF (oNa to) (oWi to) s₀ s₀' b := by
        cases to
        · exact oneCrypt_rel h6 h6' hq6 hn hwi ho.dst ho'.dst
        · exact oneCryptTo_rel ho ho' hq6
      have y7 : RelCT isa (fun a b => (OF (oNa to) (oWi to) s₀ s₀ a ∧ WP isa (.block []) a (Z s₀)) ∧
          (OF (oNa to) (oWi to) s₀ s₀' b ∧ WP isa (.block []) b (Z s₀'))) (.ite .eq (.block []) (oneCryptG to))
          fun a b => W a ∧ W b :=
        rel_iteQ (decide (¬openTagOk to s₀)) (fun s h => wp_nil h.2) (fun s h => (wp_nil h.2).trans eZ)
          (fun _ => RelCT.block_nil fun x y h => ⟨r11 h.1.1, r11 h.2.1⟩)
          (fun _ => cr.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => ⟨r11 h.1, r11 h.2⟩)
      obtain ⟨_, c8⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block [.mov .r0 (.reg .r7)]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      have y8 := rel_wp (F := W) (F' := W) (G := W) (G' := W)
        (RelCT.taint (A := taint) (Taint.ofRegs [.r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [h.1, h.2]) c8)
        (fun s h => mov07_wp h) (fun s h => mov07_wp h)
      refine RelCT.mono (y1.seq (y2.seq (y3.seq (y4.seq (y5.seq (y6.seq (y7.seq y8))))))) (fun s s' h => ?_)
        fun _ _ h => h
      exact ⟨⟨h.1.1, pfx ho hok h.1.1⟩, ⟨h.2.1, pfx ho' hok' h.2.1⟩⟩
  -- what each run computes
  have mid' := rel_ghost (R := .block []) (Z := OB to s₀) (Z' := OB to s₀') mid
  refine a.seq (b.seq ((RelCT.mono mid' (fun s s' h => ⟨⟨h.1, ?_⟩, ⟨h.2, ?_⟩⟩)
    fun _ _ h => ⟨wp_nil h.1.2, wp_nil h.2.2⟩).seq hend))
  · exact WP.seq (WP.mono (openMid_wp ho h.1.1 h.1.2) fun _ h => WP.block_nil h)
  · exact WP.seq (WP.mono (openMid_wp ho' h.2.1 (by rw [h.2.2, h5'])) fun _ h => WP.block_nil h)

theorem open_rel {s₀ s₀' : State} (h0 : openArm.pre s₀) (h0' : openArm.pre s₀') (hq : openArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') «open» fun _ _ => True := by
  have ho := openPreArm.oPre h0
  have ho' := openPreArm.oPre h0'
  have hR : roundsOk s₀ := ho.one.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have e4 : arg s₀' 6 = arg s₀ 6 := (hq.1.2.2.2.2.2 6 (by decide)).symm
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have d := RelCT.taint (A := taint) (P := fun s₁ s₂ => OB false s₀ s₁ ∧ OB false s₀' s₂) (c := .block restore)
    (Taint.ofRegs [.r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.env.choose_spec.r11, h.2.env.choose_spec.r11]; exact e4.symm) hB
  exact openBody_rel ho ho' hq.1 (hq.2 hR) d

theorem open_ct : ConstantTime isa openArm.pre openArm.pub «open» :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (open_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.Arm
