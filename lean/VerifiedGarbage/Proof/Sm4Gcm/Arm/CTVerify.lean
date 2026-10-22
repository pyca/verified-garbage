module

public import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTFin
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTFin
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTFn
import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamFinish
import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamVerify
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTFn
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamFinish
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamVerify
import VerifiedGarbage.Proof.Sm4Gcm.Arm.Compare
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Compare
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTAbsorb
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTCryptFn
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTJ0
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CryptOk
import VerifiedGarbage.Proof.Sm4Gcm.Arm.Entry
import VerifiedGarbage.Proof.Sm4Gcm.Arm.Ghash1
import VerifiedGarbage.Proof.Sm4Gcm.Arm.Open
import VerifiedGarbage.Proof.Sm4Gcm.Arm.Seal
import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamCrypt
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
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTAbsorb
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTCryptFn
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTJ0
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CryptOk
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Entry
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Ghash1
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Open
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Seal
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamCrypt
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
# SM4-GCM on ARMv7: `vg_sm4_gcm_stream_verify` is constant time

Untrusted: everything here is checked by Lean. Only the (public) tag length
decides which code runs: the tags are compared without a branch.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm

/-- `rel_ite`, with a postcondition. -/
theorem rel_iteQ {F F' : State → Prop} {Q : State → State → Prop} {t e : Prog isa} (b : Bool)
    (hz : ∀ s, F s → s.z = b) (hz' : ∀ s, F' s → s.z = b)
    (ht : b = true → RelCT isa (fun a b => F a ∧ F' b) t Q)
    (he : b = false → RelCT isa (fun a b => F a ∧ F' b) e Q) :
    RelCT isa (fun a b => F a ∧ F' b) (.ite .eq t e) Q := by
  refine RelCT.ite (fun _ _ h => by rw [eval_eq' (hz _ h.1), eval_eq' (hz' _ h.2)]) ?_ ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [eval_eq' (hz _ hp.1)] at hc
    exact ht (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [eval_eq' (hz _ hp.1)] at hc
    exact he (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂

/-- `finTag`'s state with the tag length in `r6`. -/
def P6 (na : Nat) (c st w sp k8 : BitVec 32) (tl : Nat) (t₀ s : State) : Prop :=
  FT na t₀ c st w sp k8 s ∧ s.gpr .r6 = BitVec.ofNat 32 tl

/-- After the comparison: `r0` is 1 or 0. -/
def P7 (na : Nat) (c st w sp k8 : BitVec 32) (t₀ s : State) : Prop :=
  FT na t₀ c st w sp k8 s ∧ ∃ b : Bool, s.gpr .r0 = if b then 1 else 0

theorem ite_bool {p : Prop} [Decidable p] {x : BitVec 32} (h : x = if p then 1 else 0) :
    ∃ b : Bool, x = if b then 1 else 0 :=
  ⟨decide p, by rw [h]; simp only [decide_eq_true_eq]⟩

section
variable {na : Nat} {c st w sp k8 : BitVec 32} {tl : Nat} {t₀ : State}

/-- The tag length, stack argument `ti` (at `off`), into `r6`. -/
theorem ld6_wp {s : State} {ti off : Nat} (hti : ti < na) (eoff : 4 * ti = off) (hoff : off = 12 ∨ off = 16)
    (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : args t₀ na ∈ t₀.rd)
    (h5 : (arg t₀ ti).toNat = tl) (h : FT na t₀ c st w sp k8 s) :
    WP isa (.block [.ldrSp .r6 off]) s (P6 na c st w sp k8 tl t₀) := by
  subst h5
  obtain ⟨k7, he, hk⟩ := h
  obtain ⟨i5, v5⟩ := hk.at hf hin ti hti eoff
  refine WP.of_runBlock ⟨_, by rcases hoff with rfl | rfl <;> arun [i5, v5], ?_⟩
  refine ⟨⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
  simp [gpr_setReg, v5]

theorem tlo_wp {s : State} (htl : tl < 2 ^ 32) (h : P6 na c st w sp k8 tl t₀ s) :
    WP isa tagLenOk s fun s' => P6 na c st w sp k8 tl t₀ s' ∧ s'.z = !Spec.Gcm.tagLenOk tl := by
  obtain ⟨⟨k7, he, hk⟩, h6⟩ := h
  refine WP.mono (tagLenOk_ok h6 htl) fun s' ⟨hz, g, k⟩ => ⟨⟨⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g _ (by decide)) k.sp k.rd k.wr,
    hk.of_eq k.mem k.sp k.rd k.wr⟩, by rw [g _ (by decide), h6]⟩, hz⟩

theorem mov0_wp {s : State} (h : s.gpr .r11 = w) :
    WP isa (.block [.mov .r0 (imm 0)]) s fun s' => s'.gpr .r11 = w :=
  WP.of_runBlock ⟨_, by arun [], by simp [gpr_setReg, h]⟩

variable (L : Lay c st w sp)
include L

/-- `recv ta`, with the received tag stack argument `ti` (at `ta`). -/
theorem recv_wp {s : State} {ti ta : Nat} (hti : ti < na) (hta : ta = 8 ∨ ta = 12) (eta : 4 * ti = ta)
    (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : args t₀ na ∈ t₀.rd)
    (hD : (args t₀ na).Disjoint ⟨State.addr w + BitVec.ofNat 64 256, 16⟩)
    (hTr : (⟨State.addr (arg t₀ ti), tl⟩ : Region) ∈ t₀.rd) (hTf : (arg t₀ ti).toNat + tl ≤ 2 ^ 32)
    (hTd : (⟨State.addr (arg t₀ ti), tl⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 256, 16⟩)
    (h1 : 1 ≤ tl) (h16 : tl ≤ 16) (h : P6 na c st w sp k8 tl t₀ s) :
    WP isa (recv ta) s (P6 na c st w sp k8 tl t₀) := by
  obtain ⟨⟨k7, he, hk⟩, h6⟩ := h
  obtain ⟨i4, v4⟩ := hk.at hf hin ti hti eta
  refine WP.mono (recv_ok L he hta i4 v4 (by rw [hk.rd, hk.wr]; exact covers_of_mem (List.mem_append_left _ hTr))
    hTf hTd h6 h1 h16) fun s' ⟨_, hf₄, g₄, rd₄, wr₄, sp₄⟩ => ?_
  refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) sp₄ rd₄ wr₄,
    hk.frame hf hf₄ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hD) sp₄ rd₄ wr₄⟩, ?_⟩
  rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), h6]

theorem ft_wp {s : State} (hna : 2 ≤ na) (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : args t₀ na ∈ t₀.rd)
    (hA : ∀ r ∈ tagFrame st w sp 0, (args t₀ na).Disjoint r)
    (h : FT na t₀ c st w sp k8 s) : WP isa (finTag 0) s (FT na t₀ c st w sp k8) := by
  obtain ⟨k7, he, hk⟩ := h
  exact WP.mono (finTag_ok L hna (.inl rfl) he hk hf hin hA rfl
    (a := List.replicate (k8.toNat % 16) 0) (ct := List.replicate (arg t₀ 1 ++ arg t₀ 0).toNat 0)
    (by simp) (by simp)) fun s' h => ⟨h.env.choose, h.env.choose_spec, h.args⟩

theorem cmp_wp {s : State} (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) {o : Nat} (ho : o = 0 ∨ o = 112)
    (hD : (args t₀ na).Disjoint ⟨State.addr w + BitVec.ofNat 64 240, 16⟩) (h1 : 1 ≤ tl) (h16 : tl ≤ 16)
    (h : P6 na c st w sp k8 tl t₀ s) : WP isa (cmp o) s (P7 na c st w sp k8 t₀) := by
  obtain ⟨⟨k7, he, hk⟩, h6⟩ := h
  refine WP.mono (cmp_ok L he ho h6 h1 h16) fun s' ⟨h0, hf₇, g₇, rd₇, wr₇, sp₇⟩ => ?_
  refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₇ _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) sp₇ rd₇ wr₇,
    hk.frame hf hf₇ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hD) sp₇ rd₇ wr₇⟩,
    ite_bool h0⟩

end

theorem streamVerify_rel {s₀ s₀' : State} (h0 : streamVerifyArm.pre s₀) (h0' : streamVerifyArm.pre s₀')
    (hq : streamVerifyArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamVerify fun _ _ => True := by
  have h0₅ : finPre 5 4 s₀ := streamVerifyPreArm.fin h0
  have h0₅' : finPre 5 4 s₀' := streamVerifyPreArm.fin h0'
  obtain ⟨q₀, q₁, q₂, q₃, -, qa⟩ := id hq
  have L := finLay h0₅
  have spf := h0₅.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf' := h0₅'.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ 5 ∈ s₀.rd := h0₅.1.2
  have hin' : args s₀' 5 ∈ s₀'.rd := h0₅'.1.2
  obtain ⟨hrd, -, -, -, -, -, -, tW, -, -, -, -, -, -, -, fT, -⟩ := h0
  obtain ⟨hrd', -, -, -, -, -, -, tW', -, -, -, -, -, -, -, fT', -⟩ := h0'
  have hA := fin_argsTag h0₅ (o := 0) (.inl rfl)
  have hA' : ∀ r ∈ tagFrame (s₀.gpr .r1) (arg s₀ 4) s₀.sp 0, (args s₀' 5).Disjoint r := by
    have := fin_argsTag h0₅' (o := 0) (.inl rfl); rwa [← q₂, ← qa 4 (by decide), ← q₀] at this
  have hD : ∀ {d k : Nat}, d + k ≤ 768 →
      (args s₀ 5).Disjoint ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 d, k⟩ :=
    fun hd => (h0₅.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
  have hD' : ∀ {d k : Nat}, d + k ≤ 768 →
      (args s₀' 5).Disjoint ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 d, k⟩ := fun hd => by
    rw [qa 4 (by decide)]; exact (h0₅'.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
  have h5' : (arg s₀' 3).toNat = (arg s₀ 3).toNat := by rw [qa 3 (by decide)]
  -- shorthands for the public data
  let P6₀ := P6 5 (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ 4) s₀.sp (s₀.gpr .r2) (arg s₀ 3).toNat
  let FT₀ := fun t₀ => FT 5 t₀ (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ 4) s₀.sp (s₀.gpr .r2)
  let P7₀ := P7 5 (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ 4) s₀.sp (s₀.gpr .r2)
  let P3 : State → State → Prop := fun t₀ s => P6₀ t₀ s ∧ s.z = !Spec.Gcm.tagLenOk (arg s₀ 3).toNat
  let W : State → Prop := fun s => s.gpr .r11 = arg s₀ 4
  have r11 : ∀ {t₀ s}, FT₀ t₀ s → s.gpr .r11 = arg s₀ 4 := fun h => h.choose_spec.1.r11
  -- the entry, and the tag length
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := P6₀ s₀) (G' := P6₀ s₀')
    (argTaint [.r0, .r1, .r2, .r3] (4 * 5)) (c := .block (finEntry 16 ++ [.ldrSp .r6 12]))
    (fin_entry_agree h0₅ h0₅' hq) ⟨_, by taint_decide⟩
    (fun s e => by
      rw [e]
      exact WP.block_append (fin1_wp h0₅ (by decide) (by decide) fun s₁ h1 =>
        ld6_wp (ti := 3) (by decide) rfl (.inl rfl) spf hin rfl ⟨_, h1.env, h1.args⟩))
    (fun s e => by
      rw [e]
      exact WP.block_append (fin1_wp h0₅' (by decide) (by decide) fun s₁ h1 =>
        ld6_wp (ti := 3) (by decide) rfl (.inl rfl) spf' hin' h5' ⟨_, by
          have := h1.env; rw [← q₁, ← q₂, ← q₃, ← qa 4 (by decide), ← q₀] at this; exact this, h1.args⟩))
  -- whether the length is allowed
  obtain ⟨_, hT⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6]) tagLenOk h).isSome = true := ⟨_, by taint_decide⟩
  have b := rel_wp (F := P6₀ s₀) (F' := P6₀ s₀') (G := P3 s₀) (G' := P3 s₀')
    (RelCT.taint (A := taint) (Taint.ofRegs [.r6]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]) hT)
    (fun s h => tlo_wp (arg s₀ 3).isLt h) (fun s h => tlo_wp (arg s₀ 3).isLt h)
  -- the branches
  have mid : RelCT isa (fun a b => P3 s₀ a ∧ P3 s₀' b)
      (.ite .eq (.block [.mov .r0 (imm 0)]) (.seq (recv 8) (.seq (finTag 0) (.seq (.block [.ldrSp .r6 12])
        (cmp 0))))) fun a b => W a ∧ W b := by
    refine rel_iteQ (!Spec.Gcm.tagLenOk (arg s₀ 3).toNat) (fun s h => h.2) (fun s h => h.2) (fun _ => ?_)
      (fun hb => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block [.mov .r0 (imm 0)]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      exact rel_wp (F := P3 s₀) (F' := P3 s₀') (G := W) (G' := W)
        (RelCT.taint (A := taint) (Taint.ofRegs []) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp at hr) hc)
        (fun s h => mov0_wp (r11 h.1.1)) (fun s h => mov0_wp (r11 h.1.1))
    · have hok : Spec.Gcm.tagLenOk (arg s₀ 3).toNat = true := by simpa using hb
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      have x1 := rel_agree (F := P3 s₀) (F' := P3 s₀') (G := P6₀ s₀) (G' := P6₀ s₀')
        (argTaint [.r6, .r11] (4 * 5)) (c := recv 8)
        (fun s s' h h' => h.1.1.choose_spec.2.agree h'.1.1.choose_spec.2 q₀ spf qa (fin_hw h0₅) (fin_hw h0₅')
          fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · rw [h.1.2, h'.1.2]
            · rw [r11 h.1.1, r11 h'.1.1]) ⟨_, by taint_decide⟩
        (fun s h => recv_wp L (ti := 2) (by decide) (.inl rfl) rfl spf hin (hD (by decide)) (by rw [hrd]; simp) fT
          (tW.sub_right (Lay.wSub (by decide))) t1 t16 h.1)
        (fun s h => recv_wp L (ti := 2) (by decide) (.inl rfl) rfl spf' hin' (hD' (by decide)) (by rw [hrd', h5']; simp)
          (by rw [← h5']; exact fT') (by rw [← h5', qa 4 (by decide)]; exact tW'.sub_right (Lay.wSub (by decide)))
          t1 t16 h.1)
      have x2 := rel_wp (F := P6₀ s₀) (F' := P6₀ s₀') (G := FT₀ s₀) (G' := FT₀ s₀')
        (finTag_rel L (na := 5) (by decide) (o := 0) (.inl rfl) (k8 := s₀.gpr .r2) spf q₀ qa (fin_hw h0₅) (fin_hw h0₅') hin hin'
          hA hA' |>.mono (fun s s' h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
        (fun s h => ft_wp L (by decide) spf hin hA h.1) (fun s h => ft_wp L (by decide) spf' hin' hA' h.1)
      have x3 := rel_agree (F := FT₀ s₀) (F' := FT₀ s₀') (G := P6₀ s₀) (G' := P6₀ s₀')
        (argTaint [] (4 * 5)) (c := .block [.ldrSp .r6 12])
        (fun s s' h h' => h.choose_spec.2.agree h'.choose_spec.2 q₀ spf qa (fin_hw h0₅) (fin_hw h0₅') (rs := [])
          (by simp)) ⟨_, by taint_decide⟩
        (fun s h => ld6_wp (ti := 3) (by decide) rfl (.inl rfl) spf hin rfl h)
        (fun s h => ld6_wp (ti := 3) (by decide) rfl (.inl rfl) spf' hin' h5' h)
      obtain ⟨_, c4⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6, .r11]) (cmp 0) h).isSome = true :=
        ⟨_, by taint_decide⟩
      have x4 := rel_wp (F := P6₀ s₀) (F' := P6₀ s₀') (G := W) (G' := W)
        (RelCT.taint (A := taint) (Taint.ofRegs [.r6, .r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h.1.2, h.2.2]
          · rw [r11 h.1.1, r11 h.2.1]) c4)
        (fun s h => WP.mono (cmp_wp L spf (.inl rfl) (hD (by decide)) t1 t16 h) fun _ h => r11 h.1)
        (fun s h => WP.mono (cmp_wp L spf' (.inl rfl) (hD' (by decide)) t1 t16 h) fun _ h => r11 h.1)
      exact x1.seq (x2.seq (x3.seq x4))
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have d := RelCT.taint (A := taint) (P := fun s₁ s₂ => W s₁ ∧ W s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1, h.2]) hB
  exact a.seq (b.seq (mid.seq d))

theorem streamVerify_ct : ConstantTime isa streamVerifyArm.pre streamVerifyArm.pub streamVerify :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (streamVerify_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Sm4Gcm.Arm
