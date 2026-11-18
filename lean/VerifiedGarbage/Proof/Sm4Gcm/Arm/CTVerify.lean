module

import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTFn
import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamFinish
import VerifiedGarbage.Proof.Sm4Gcm.Arm.Open
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTFn
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamFinish
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Open
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTAbsorb
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTCryptFn
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTJ0
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Entry
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Flush
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
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Args
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTCrypt
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTAbsorb
import VerifiedGarbage.Proof.Sm4Gcm.Arm.TextAbsorb
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Args
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Fn
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTCrypt
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.TextAbsorb
meta import VerifiedGarbage.Impl.Sm4Gcm.Arm
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTBase
meta import VerifiedGarbage.TCB.Arm.Isa

/-! ### `Sm4Gcm.Arm.CTFin`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on ARMv7: `finTag`, `vg_sm4_gcm_stream_finish` and `vg_sm4_gcm_stream_verify` are constant time

Untrusted: everything here is checked by Lean. `finish` copies the tag to
`tag` through a pointer read from the stack (`tagOut_wp`); `verify` compares
the tags without a branch: only the tag length decides which code runs.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm
open VG.Spec.Gcm (Block blockAt)

/-- What `finTag` needs, in a run from `s₀`. -/
def FT (na : Nat) (s₀ : State) (c st w sp k8 : BitVec 32) (s : State) : Prop :=
  ∃ k7, Env c st w sp k7 k8 s ∧ ArgsKeep na s₀ s

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem finTag_rel [VG.Proof.Gcm.Arm.GhashLaw] {na : Nat} (hna : 2 ≤ na) {o : Nat} (ho : o = 0 ∨ o = 112) {k8 : BitVec 32}
    {s₀ s₀' : State} (hf : s₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hsp : s₀.sp = s₀'.sp)
    (ha : ∀ i < na, arg s₀ i = arg s₀' i) (hw : ∀ r ∈ s₀.wr, (args s₀ na).Disjoint r)
    (hw' : ∀ r ∈ s₀'.wr, (args s₀' na).Disjoint r) (hin : args s₀ na ∈ s₀.rd) (hin' : args s₀' na ∈ s₀'.rd)
    (hA : ∀ r ∈ tagFrame st w sp o, (args s₀ na).Disjoint r) (hA' : ∀ r ∈ tagFrame st w sp o, (args s₀' na).Disjoint r) :
    RelCT isa (fun a b => FT na s₀ c st w sp k8 a ∧ FT na s₀' c st w sp k8 b) (finTag o) fun _ _ => True := by
  have hf' : s₀'.sp.toNat + 4 * na ≤ 2 ^ 32 := by rw [← hsp]; exact hf
  have ag : ∀ {s s'}, ArgsKeep na s₀ s → ArgsKeep na s₀' s' →
      VG.Arm.Taint.Agree (argTaint [] (4 * 2)) s s' := fun k k' =>
    (k.weaken hna).agree (k'.weaken hna) hsp (by omega_using [hna, hf]) (fun i hi => ha i (by omega_using [hna, hi]))
      (fun r hr => (hw r hr).sub_left (args_sub _ hna)) (fun r hr => (hw' r hr).sub_left (args_sub _ hna)) (by simp)
  -- whether there is text
  let GA : State → State → Prop := fun t₀ s => FT na t₀ c st w sp k8 s ∧
    s.z = decide ((arg t₀ 1 ++ arg t₀ 0).toNat = 0)
  have runA : ∀ {t₀ s : State}, FT na t₀ c st w sp k8 s → t₀.sp.toNat + 4 * na ≤ 2 ^ 32 → args t₀ na ∈ t₀.rd →
      WP isa (.block tlenZero) s (GA t₀) := fun {t₀ s} ⟨k7, he, hk⟩ f i => by
    obtain ⟨i2, v2⟩ := hk.at f i 0 (by omega_using [hna]) (show 4 * 0 = 0 from rfl)
    obtain ⟨i3, v3⟩ := hk.at f i 1 (by omega_using [hna]) (show 4 * 1 = 4 from rfl)
    refine WP.of_runBlock ⟨_, by simp only [tlenZero]; arun [i2, v2, i3, v3], ?_⟩
    refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_subFlags]) rfl rfl rfl,
      hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
    simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, v2, v3]
    rw [z_sub0]
    exact decide_eq_decide.mpr (or_zero_iff _ _)
  have a := rel_agree (F := FT na s₀ c st w sp k8) (F' := FT na s₀' c st w sp k8) (G := GA s₀) (G' := GA s₀')
    (argTaint [] (4 * 2)) (c := .block tlenZero)
    (fun s s' ⟨_, _, k⟩ ⟨_, _, k'⟩ => ag k k') ⟨_, by taint_decide⟩
    (fun s h => runA h hf hin) (fun s h => runA h hf' hin')
  refine a.seq ?_
  -- the buffered bytes' length: the additional data's if there is no text
  let v : State → BitVec 32 := fun t₀ => if (arg t₀ 1 ++ arg t₀ 0).toNat = 0 then k8 else arg t₀ 0
  let GB : State → State → Prop := fun t₀ s => FT na t₀ c st w sp k8 s ∧ s.gpr .r6 = v t₀
  have runB : ∀ {t₀ s : State}, GA t₀ s → t₀.sp.toNat + 4 * na ≤ 2 ^ 32 → args t₀ na ∈ t₀.rd →
      WP isa (.ite .eq (.block [.mov .r6 (.reg .r8)]) (.block [.ldrSp .r6 0])) s (GB t₀) :=
    fun {t₀ s} ⟨⟨k7, he, hk⟩, hz⟩ f i => by
    refine WP.ite _ (eval_eq' hz) (fun ht => ?_) (fun hf₀ => ?_)
    · have h8 := he.r8
      refine WP.of_runBlock ⟨_, by arun [], ?_⟩
      refine ⟨⟨k7, he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
      have : (arg t₀ 1 ++ arg t₀ 0).toNat = 0 := by simpa using ht
      simp [gpr_setReg, h8, v, this]
    · obtain ⟨i2, v2⟩ := hk.at f i 0 (by omega_using [hna]) (show 4 * 0 = 0 from rfl)
      refine WP.of_runBlock ⟨_, by arun [i2, v2], ?_⟩
      refine ⟨⟨k7, he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
      have : (arg t₀ 1 ++ arg t₀ 0).toNat ≠ 0 := by simpa using hf₀
      simp [gpr_setReg, v2, v, this]
  have b : RelCT isa (fun a b => GA s₀ a ∧ GA s₀' b) (.ite .eq (.block [.mov .r6 (.reg .r8)]) (.block [.ldrSp .r6 0]))
      fun _ _ => True := by
    refine rel_ite (decide ((arg s₀ 1 ++ arg s₀ 0).toNat = 0)) (fun s h => h.2)
      (fun s h => by rw [h.2, ha 1 (by omega_using [hna]), ha 0 (by omega_using [hna])]) (fun _ => ?_) (fun _ => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (taint.check (Taint.ofRegs [.r8]) (.block [.mov .r6 (.reg .r8)]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      exact RelCT.taint (A := taint) (Taint.ofRegs [.r8]) (fun s s' h => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.1.1.choose_spec.1.r8, h.2.1.choose_spec.1.r8]) hc
    · obtain ⟨_, hc⟩ : ∃ h, (taint.check (argTaint [] (4 * 2)) (.block [.ldrSp .r6 0]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      exact RelCT.taint (A := taint) (argTaint [] (4 * 2)) (fun s s' h =>
        ag h.1.1.choose_spec.2 h.2.1.choose_spec.2) hc
  refine (rel_wp b (fun s h => runB h hf hin) (fun s h => runB h hf' hin')).seq ?_
  have hv : v s₀' = v s₀ := by simp only [v, ha 0 (by omega_using [hna]), ha 1 (by omega_using [hna])]
  -- modulo 16
  let GC : State → State → Prop := fun t₀ s => FT na t₀ c st w sp k8 s ∧
    s.gpr .r6 = BitVec.ofNat 32 ((v s₀).toNat % 16)
  have runC : ∀ {t₀ s : State}, v t₀ = v s₀ → GB t₀ s → WP isa (.block [.dp .and .r6 .r6 (imm 15)]) s (GC t₀) :=
    fun {t₀ s} e ⟨⟨k7, he, hk⟩, h6⟩ => by
    refine WP.of_runBlock ⟨_, by arun [], ?_⟩
    refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
    simp only [gpr_setReg, ite_true, h6, and15, e]
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6]) (.block [.dp .and .r6 .r6 (imm 15)]) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have cC := rel_wp (F := GB s₀) (F' := GB s₀') (G := GC s₀) (G' := GC s₀')
    (RelCT.taint (A := taint) (Taint.ofRegs [.r6]) (fun s s' h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2, hv]) hC)
    (fun s h => runC rfl h) (fun s h => runC hv h)
  refine cC.seq ?_
  -- the buffered bytes padded
  have runF : ∀ {t₀ s : State}, t₀.sp.toNat + 4 * na ≤ 2 ^ 32 → (∀ r ∈ tagFrame st w sp o, (args t₀ na).Disjoint r) →
      GC t₀ s → WP isa (flush 16) s (FT na t₀ c st w sp k8) := fun {t₀ s} f hA₀ ⟨⟨k7, he, hk⟩, h6⟩ => by
    have hq := Nat.mod_lt (v s₀).toNat (show 16 > 0 by decide)
    refine WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := List.replicate ((v s₀).toNat % 16) 0)
      (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) ⟨he, rfl⟩ (by simp [h6, Nat.mod_eq_of_lt hq])))
      fun s' ⟨fl, rd, wr, sp'⟩ => ⟨k7, fl.env, hk.frame f fl.frame (disj_sub hA₀ tFrame_sub) sp' rd wr⟩
  have cF := rel_wp (F := GC s₀) (F' := GC s₀') (G := FT na s₀ c st w sp k8) (G' := FT na s₀' c st w sp k8)
    (rel_of_ct (flush_ct L (yo := 16) (.inr rfl) (q := (v s₀).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩) (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩))
    (fun s h => runF hf hA h) (fun s h => runF hf' hA' h)
  refine cF.seq ?_
  -- the lengths
  have runD : ∀ {t₀ s : State}, t₀.sp.toNat + 4 * na ≤ 2 ^ 32 → args t₀ na ∈ t₀.rd → FT na t₀ c st w sp k8 s →
      WP isa (.block [.mov .r4 (.reg .r8), .mov .r5 (.reg .r7), .ldrSp .r6 0, .ldrSp .r7 4]) s
        (FT na t₀ c st w sp k8) :=
    fun {t₀ s} f i ⟨k7, he, hk⟩ => by
    obtain ⟨j0, w0⟩ := hk.at f i 0 (by omega_using [hna]) (show 4 * 0 = 0 from rfl)
    obtain ⟨j1, w1⟩ := hk.at f i 1 (by omega_using [hna]) (show 4 * 1 = 4 from rfl)
    refine WP.of_runBlock ⟨_, by arun [j0, w0, j1, w1], ?_⟩
    exact ⟨_, he.set7 (k7' := arg t₀ 1) (by simp [gpr_setReg, w1]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩
  have cD := rel_agree (F := FT na s₀ c st w sp k8) (F' := FT na s₀' c st w sp k8) (G := FT na s₀ c st w sp k8)
    (G' := FT na s₀' c st w sp k8) (argTaint [] (4 * 2))
    (c := .block [.mov .r4 (.reg .r8), .mov .r5 (.reg .r7), .ldrSp .r6 0, .ldrSp .r7 4])
    (fun s s' ⟨_, _, k⟩ ⟨_, _, k'⟩ => ag k k') ⟨_, by taint_decide⟩
    (fun s h => runD hf hin h) (fun s h => runD hf' hin' h)
  exact cD.seq (rel_of_ct (tag_ct L ho) (fun s ⟨k7, he, _⟩ => ⟨k7, he⟩) (fun s ⟨k7, he, _⟩ => ⟨k7, he⟩))

end

/-- `tagOut ta` in a run from `t₀`, with the tag at its stack argument `ti`: what follows needs only `r11`. -/
theorem tagOut_wp {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {n ti ta : Nat} (hti : ti < n) (hta : ta = 8 ∨ ta = 12)
    (eta : 4 * ti = ta) {t₀ s : State}
    (he : Env c st w sp k7 k8 s) (hk : ArgsKeep n t₀ s) (hf : t₀.sp.toNat + 4 * n ≤ 2 ^ 32)
    (hin : args t₀ n ∈ t₀.rd) (hTw : (⟨State.addr (arg t₀ ti), 16⟩ : Region) ∈ t₀.wr)
    (hTf : (arg t₀ ti).toNat + 16 ≤ 2 ^ 32) (hTd : (⟨State.addr (arg t₀ ti), 16⟩ : Region).Disjoint ⟨State.addr w, 16⟩) :
    WP isa (.block (tagOut ta)) s fun s' => s'.gpr .r11 = w := by
  obtain ⟨i4, v4⟩ := hk.at hf hin ti hti eta
  obtain ⟨s', run, -, -, g, -⟩ := tagOut_ok L he hta i4 v4 (by rw [hk.wr]; exact covers_of_mem hTw) hTf hTd
  exact WP.of_runBlock ⟨s', run, by rw [g _ (by decide) (by decide), he.r11]⟩

theorem fin_hw {n wi : Nat} {t : State} (ht : finPre n wi t) : ∀ r ∈ t.wr, (args t n).Disjoint r := ht.2.1.2.2

theorem fin_entry_agree {n wi : Nat} {s₀ s₀' : State} (h0 : finPre n wi s₀) (h0' : finPre n wi s₀')
    (hq : finPub n s₀ s₀') :
    ∀ s s', s = s₀ → s' = s₀' → VG.Arm.Taint.Agree (argTaint [.r0, .r1, .r2, .r3] (4 * n)) s s' := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  intro s s' e e'
  subst e e'
  refine (ArgsKeep.refl n s).agree (ArgsKeep.refl n s') q₀ h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2 qa (fin_hw h0) (fin_hw h0')
    fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem streamFinish_rel [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₀' : State} (h0 : streamFinishArm.pre s₀) (h0' : streamFinishArm.pre s₀')
    (hq : streamFinishArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamFinish fun _ _ => True := by
  have h0₄ : finPre 4 3 s₀ := streamFinishPreArm.fin h0
  have h0₄' : finPre 4 3 s₀' := streamFinishPreArm.fin h0'
  obtain ⟨q₀, q₁, q₂, q₃, -, qa⟩ := id hq
  have L := finLay h0₄
  have spf := h0₄.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf' := h0₄'.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := SF1 4 3 s₀) (G' := SF1 4 3 s₀')
    (argTaint [.r0, .r1, .r2, .r3] (4 * 4)) (c := .block (finEntry 12)) (fin_entry_agree h0₄ h0₄' hq)
    ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact fin1_wp h0₄ (by decide) (by decide) fun _ h => h)
    (fun s e => by rw [e]; exact fin1_wp h0₄' (by decide) (by decide) fun _ h => h)
  let G : State → State → Prop := fun t₀ s =>
    (∃ k7 k8, Env (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ 3) s₀.sp k7 k8 s) ∧ ArgsKeep 4 t₀ s
  have tg : ∀ {t₀ : State}, finPre 4 3 t₀ → t₀.sp = s₀.sp → arg t₀ 3 = arg s₀ 3 → t₀.gpr .r0 = s₀.gpr .r0 →
      t₀.gpr .r1 = s₀.gpr .r1 → ∀ s, SF1 4 3 t₀ s → WP isa (finTag 0) s (G t₀) := fun {t₀} ht e0 e3 er0 er1 s h1 =>
    WP.mono (fin_tag ht (by decide) h1 (.inl rfl) (a := List.replicate ((t₀.gpr .r2).toNat % 16) 0)
      (ct := List.replicate (arg t₀ 1 ++ arg t₀ 0).toNat 0) (by simp) (by simp)) fun s' h => by
      obtain ⟨k7, he⟩ := h.env
      rw [e0, e3, er0, er1] at he
      exact ⟨⟨k7, _, he⟩, h.args⟩
  have b := rel_wp (F := SF1 4 3 s₀) (F' := SF1 4 3 s₀') (G := G s₀) (G' := G s₀')
    (finTag_rel L (na := 4) (by decide) (o := 0) (.inl rfl) (k8 := s₀.gpr .r2) spf q₀ qa (fin_hw h0₄) (fin_hw h0₄')
      h0₄.1.2 h0₄'.1.2 (fin_argsTag h0₄ (.inl rfl))
      (by have := fin_argsTag h0₄' (o := 0) (.inl rfl); rwa [← q₂, ← qa 3 (by decide), ← q₀] at this) |>.mono
      (fun s s' ⟨h₁, h₂⟩ => ⟨⟨_, h₁.env, h₁.args⟩, ⟨_, by
        have := h₂.env; rw [← q₁, ← q₂, ← q₃, ← qa 3 (by decide), ← q₀] at this; exact this, h₂.args⟩⟩)
      fun _ _ h => h)
    (tg h0₄ rfl rfl rfl rfl) (tg h0₄' q₀.symm (qa 3 (by decide)).symm q₁.symm q₂.symm)
  -- the tag copied out
  let W : State → Prop := fun s => s.gpr .r11 = arg s₀ 3
  obtain ⟨hrd, hwr, -, -, -, -, -, -, tW, -, -, -, -, -, -, -, -, fT, -⟩ := h0
  obtain ⟨-, hwr', -, -, -, -, -, -, tW', -, -, -, -, -, -, -, -, fT', -⟩ := h0'
  have c := rel_agree (F := G s₀) (F' := G s₀') (G := W) (G' := W) (argTaint [.r11] (4 * 4)) (c := .block (tagOut 8))
    (fun s s' ⟨⟨_, _, he⟩, hk⟩ ⟨⟨_, _, he'⟩, hk'⟩ => hk.agree hk' q₀ spf qa (fin_hw h0₄) (fin_hw h0₄') fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [he.r11, he'.r11]) ⟨_, by taint_decide⟩
    (fun s ⟨⟨_, _, he⟩, hk⟩ => tagOut_wp L (ti := 2) (by decide) (.inl rfl) rfl he hk spf h0₄.1.2
      (by rw [hwr]; simp) fT (tW.sub_right (Region.sub_prefix (by decide))))
    (fun s ⟨⟨_, _, he⟩, hk⟩ => tagOut_wp L (ti := 2) (by decide) (.inl rfl) rfl he hk spf' h0₄'.1.2
      (by rw [hwr']; simp) fT' (by rw [qa 3 (by decide)]; exact tW'.sub_right (Region.sub_prefix (by decide))))
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have d := RelCT.taint (A := taint) (P := fun s₁ s₂ => W s₁ ∧ W s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ ⟨h₁, h₂⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) hB
  exact a.seq (b.seq (c.seq d))

theorem streamFinish_ct [VG.Proof.Gcm.Arm.GhashLaw] : ConstantTime isa streamFinishArm.pre streamFinishArm.pub streamFinish :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (streamFinish_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Sm4Gcm.Arm

end

end

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

theorem ft_wp [VG.Proof.Gcm.Arm.GhashLaw] {s : State} (hna : 2 ≤ na) (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : args t₀ na ∈ t₀.rd)
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

theorem streamVerify_rel [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₀' : State} (h0 : streamVerifyArm.pre s₀) (h0' : streamVerifyArm.pre s₀')
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

theorem streamVerify_ct [VG.Proof.Gcm.Arm.GhashLaw] : ConstantTime isa streamVerifyArm.pre streamVerifyArm.pub streamVerify :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (streamVerify_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Sm4Gcm.Arm
