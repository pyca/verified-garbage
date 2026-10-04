import VerifiedGarbage.Proof.AesSiv.AArch64.FinishLong

/-!
# AES-SIV on AArch64: finishing S2V (`finish`)

`finish` branches on `L >> 4` to the short case (`finishShort_wp`) or the
long one (`finishLong_wp`), which leave S2V's end at `W + out`. Every
branch and loop in it is on `L`, and the arguments of its calls are the same
in two runs with the same pointers and lengths (`finish_rel`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64
open VG.Proof.AesSiv (kOf jOf kOf_tail jOf_rest jOf_le)
open VG.Proof.CmacAes.AArch64 (agree_of)
open VG.Proof.CmacAes.Stream.AArch64 (UArgs FArgs toNat_ofNat upd_call upd_rel fin_rel eval_zero)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem lsrL_ok {s : State} (h23 : s.gpr .x23 = BitVec.ofNat 64 L) (hL : L < 2 ^ 64) :
    ∃ s', runBlock isa [.lsr .x .x9 .x23 4] s = some s' ∧ s'.gpr .x9 = BitVec.ofNat 64 (L / 16) ∧
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [↓reduceIte, Nat.reduceLT, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      State.read, BitVec.setWidth_eq]
    rfl, ?_⟩
  exact ⟨by simp [gpr_write, h23, lsr4 hL], fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩

theorem FinPost.of_mem {s₁ s s' : State} {out : Nat} (hm : s₁.mem = s.mem) (hg : Hold2 s s₁)
    (h : FinPost s₀ C D P W R L out s₁ s') : FinPost s₀ C D P W R L out s s' :=
  ⟨h.regs, hg.trans h.hold, hm ▸ h.frame, hm ▸ h.out⟩

theorem finish_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : Env s₀ C D P W R L) {s : State}
    (hr : Regs s₀ C D P W R L s) {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (finish v.callee v.ctr.callee v.ctr.suffix out) s (FinPost s₀ C D P W R L out s) := by
  obtain ⟨s₁, run₁, x9₁, g₁, sp₁, m₁, rd₁, wr₁⟩ := lsrL_ok hr.x23 h.lt
  have hr₁ : Regs s₀ C D P W R L s₁ := hr.keep' (fun r hr' => g₁ r (dec_ne (by decide) hr')) sp₁ rd₁ wr₁
  have hg₁ : Hold2 s s₁ := ⟨g₁ _ (by decide), g₁ _ (by decide)⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have ev := eval_zero (s := s₁) (r := .x9) (x := L / 16) (by have := h.lt; omega) x9₁
  by_cases hL : L < 16
  · refine WP.ite true (by rw [ev]; simp; omega) (fun _ => ?_) (fun h => by cases h)
    exact WP.mono (finishShort_wp v h hr₁ hL hout) fun _ p => p.of_mem m₁ hg₁
  · refine WP.ite false (by rw [ev]; simp; omega) (fun h => by cases h) (fun _ => ?_)
    exact WP.mono (finishLong_wp v h hr₁ (by omega) hout) fun _ p => p.of_mem m₁ hg₁

/-! ## Constant time -/

/-- The pair of runs, with the same arguments. -/
abbrev RR (s₀ s₀' : State) (C D P W : Addr) (R L : Nat) (a b : State) : Prop :=
  Regs s₀ C D P W R L a ∧ Regs s₀' C D P W R L b

/-- `regs_agree`, with other registers whose values both runs know. -/
theorem regs_agree' {s₀ s₀' a b : State} (hq : s₀.sp = s₀'.sp) (ha : Regs s₀ C D P W R L a)
    (hb : Regs s₀' C D P W R L b) {rs : List Reg} (hrs : ∀ r ∈ rs, a.gpr r = b.gpr r) :
    taint.Agree (Taint.ofRegs (([.x19, .x20, .x21, .x22, .x23] : List Reg) ++ rs)) a b := by
  refine agree_of (by rw [ha.sp, hb.sp, hq]) fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [ha.x19, hb.x19]
    · rw [ha.x20, hb.x20]
    · rw [ha.x21, hb.x21]
    · rw [ha.x22, hb.x22]
    · rw [ha.x23, hb.x23]
  · exact hrs r hr

theorem short_rel (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀' : State} (h : Env s₀ C D P W R L)
    (h' : Env s₀' C D P W R L) (hq : s₀.sp = s₀'.sp) (hL : L < 16) {out : Nat} (hout : out = 0 ∨ out = 112) :
    RelCT isa (RR s₀ s₀' C D P W R L) (.seq shortTail (shortMac v.ctr.callee v.ctr.suffix out))
      (RR s₀ s₀' C D P W R L) := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23]) shortTail
      hc).isSome = true := ⟨_, by taint_decide⟩
  have hB' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23])
      (.block (shortArgs o)) hc).isSome = true := by
    rintro o (rfl | rfl)
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ := hB' out hout
  have t₁ := (RelCT.taint (A := taint) (P := RR s₀ s₀' C D P W R L) _ (fun a b hab => regs_agree hq hab.1 hab.2)
    hA).wp (F₁ := Regs s₀ C D P W R L) (F₂ := Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (shortTail_wp h hab.1 hL) fun _ p => p.1, WP.mono (shortTail_wp h' hab.2 hL) fun _ p => p.1⟩
  have mpre {σ x : State} (hσ : Env σ C D P W R L) (hx : Regs σ C D P W R L x) :
      WP isa (.block (shortArgs out)) x fun y => Regs σ C D P W R L y ∧
        FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R := by
    obtain ⟨y, run, hy, _, fa, _⟩ := macPre_ok hσ hx hout
    exact WP.of_runBlock ⟨y, run, hy, fa⟩
  have t₂ := (RelCT.taint (A := taint) (P := RR s₀ s₀' C D P W R L) _ (fun a b hab => regs_agree hq hab.1 hab.2)
    hB).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧
      FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧
      FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R)
    fun a b hab => ⟨mpre h hab.1, mpre h' hab.2⟩
  have t₃ := (fin_rel v.ctr ("vg_cmac_aes_finalize" ++ v.ctr.suffix)
    (P := fun a b => (Regs s₀ C D P W R L a ∧
      FArgs a C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R) ∧
      Regs s₀' C D P W R L b ∧
      FArgs b C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R)
    fun a b hab => ⟨hab.1.2, hab.2.2, by rw [hab.1.1.sp, hab.2.1.sp, hq]⟩).wp
    (F₁ := Regs s₀ C D P W R L) (F₂ := Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (finr_call v.ctr _ hab.1.2) fun _ p => hab.1.1.keep p.saved p.sp p.rd p.wr,
      WP.mono (finr_call v.ctr _ hab.2.2) fun _ p => hab.2.1.keep p.saved p.sp p.rd p.wr⟩
  exact (t₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((t₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    (t₃.mono (fun _ _ h => h) fun _ _ h => h.2))

theorem long_rel (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀' : State} (h : Env s₀ C D P W R L)
    (h' : Env s₀' C D P W R L) (hq : s₀.sp = s₀'.sp) (hL16 : 16 ≤ L) {out : Nat} (hout : out = 0 ∨ out = 112) :
    RelCT isa (RR s₀ s₀' C D P W R L) (.seq longTail (longMac v.callee v.ctr.callee v.ctr.suffix out))
      (RR s₀ s₀' C D P W R L) := by
  have hlt := h.lt
  have hT := kOf_tail hL16
  have hJ := jOf_rest hL16
  have hj1 := jOf_le L
  obtain ⟨_, hT₀⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23]) longTail
      hc).isSome = true := ⟨_, by taint_decide⟩
  have hM1' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs ([.x19, .x20, .x21, .x22, .x23] ++
      [.x28])) (.block (longArgs₁ o)) hc).isSome = true := by
    rintro o (rfl | rfl)
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, hM1⟩ := hM1' out hout
  obtain ⟨_, hJb⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23]) jBlock
      hc).isSome = true := ⟨_, by taint_decide⟩
  have hM2' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs ([.x19, .x20, .x21, .x22, .x23] ++
      [.x25])) (.block (longArgs₂ o)) hc).isSome = true := by
    rintro o (rfl | rfl)
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, hM2⟩ := hM2' out hout
  have hM3' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs ([.x19, .x20, .x21, .x22, .x23] ++
      [.x25, .x28])) (.block (longArgs₃ o)) hc).isSome = true := by
    rintro o (rfl | rfl)
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, hM3⟩ := hM3' out hout
  -- What each run keeps between the pieces.
  let K := fun (x : State) => x.gpr .x28 = BitVec.ofNat 64 (16 * kOf L)
  let J := fun (x : State) => x.gpr .x25 = BitVec.ofNat 64 (jOf L)
  have wT {σ x : State} (hσ : Env σ C D P W R L) (hx : Regs σ C D P W R L x) :
      WP isa longTail x fun y => Regs σ C D P W R L y ∧ K y :=
    WP.mono (longTail_wp hσ hx hL16) fun _ p => ⟨p.regs, p.x28⟩
  have wM1 {σ x : State} (hσ : Env σ C D P W R L) (hx : Regs σ C D P W R L x) (hk : K x) :
      WP isa (.block (longArgs₁ out)) x fun y => Regs σ C D P W R L y ∧
        UArgs y C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L) ∧ K y := by
    obtain ⟨y, run, hy, g, u, _⟩ := m1_ok hσ hx hout hL16 hk
    exact WP.of_runBlock ⟨y, run, hy, u, by show y.gpr .x28 = _; rw [g _ (by decide)]; exact hk⟩
  have wU1 {σ x : State} (hx : Regs σ C D P W R L x)
      (hu : UArgs x C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L)) (hk : K x) :
      WP isa (callUpdate v.callee) x fun y => Regs σ C D P W R L y ∧ K y :=
    WP.mono (upd_call v _ hu) fun y p => ⟨hx.keep p.saved p.sp p.rd p.wr,
      by show y.gpr .x28 = _; rw [p.saved _ (by decide) (by decide)]; exact hk⟩
  have wJ {σ x : State} (hx : Regs σ C D P W R L x) (hk : K x) :
      WP isa jBlock x fun y => Regs σ C D P W R L y ∧ K y ∧ J y :=
    WP.mono (jBlock_wp hx.x23 hL16 hlt) fun y ⟨x25, g, sp, _, rd, wr⟩ =>
      ⟨hx.keep' (fun r hr => g r (dec_ne (by decide) hr) (dec_ne (by decide) hr)) sp rd wr,
        by show y.gpr .x28 = _; rw [g _ (by decide) (by decide)]; exact hk, x25⟩
  have wM2 {σ x : State} (hσ : Env σ C D P W R L) (hx : Regs σ C D P W R L x) (hk : K x) (hj : J x) :
      WP isa (.block (longArgs₂ out)) x fun y => Regs σ C D P W R L y ∧
        UArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L) ∧
        K y ∧ J y := by
    obtain ⟨y, run, hy, g, _, u⟩ := m3_ok hσ hx hout hj
    exact WP.of_runBlock ⟨y, run, hy, u, by show y.gpr .x28 = _; rw [g _ (by decide)]; exact hk,
      by show y.gpr .x25 = _; rw [g _ (by decide)]; exact hj⟩
  have wU2 {σ x : State} (hx : Regs σ C D P W R L x)
      (hu : UArgs x C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L))
      (hk : K x) (hj : J x) :
      WP isa (callUpdate v.callee) x fun y => Regs σ C D P W R L y ∧ K y ∧ J y :=
    WP.mono (upd_call v _ hu) fun y p => ⟨hx.keep p.saved p.sp p.rd p.wr,
      by show y.gpr .x28 = _; rw [p.saved _ (by decide) (by decide)]; exact hk,
      by show y.gpr .x25 = _; rw [p.saved _ (by decide) (by decide)]; exact hj⟩
  have wM3 {σ x : State} (hσ : Env σ C D P W R L) (hx : Regs σ C D P W R L x) (hk : K x) (hj : J x) :
      WP isa (.block (longArgs₃ out)) x fun y => Regs σ C D P W R L y ∧
        FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (W + BitVec.ofNat 64 256)
          (L - 16 * kOf L - 16 * jOf L) R := by
    obtain ⟨y, run, hy, _, _, fa⟩ := m4_ok hσ hx hout hL16 hk hj
    exact WP.of_runBlock ⟨y, run, hy, fa⟩
  have kk {a b : State} (ha : K a) (hb : K b) : a.gpr .x28 = b.gpr .x28 := by rw [ha, hb]
  have jj {a b : State} (ha : J a) (hb : J b) : a.gpr .x25 = b.gpr .x25 := by rw [ha, hb]
  -- The relations, segment by segment.
  have rT := (RelCT.taint (A := taint) (P := RR s₀ s₀' C D P W R L) _ (fun a b hab => regs_agree hq hab.1 hab.2)
    hT₀).wp (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧ K y)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧ K y)
    fun a b hab => ⟨wT h hab.1, wT h' hab.2⟩
  have rM1 := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧ K a) ∧ Regs s₀' C D P W R L b ∧ K b) _
    (fun a b hab => regs_agree' hq hab.1.1 hab.2.1 fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact kk hab.1.2 hab.2.2) hM1).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧
      UArgs y C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L) ∧ K y)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧
      UArgs y C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L) ∧ K y)
    fun a b hab => ⟨wM1 h hab.1.1 hab.1.2, wM1 h' hab.2.1 hab.2.2⟩
  have rU1 := (upd_rel v v.callee.name
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧
      UArgs a C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L) ∧ K a) ∧
      Regs s₀' C D P W R L b ∧ UArgs b C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L) ∧ K b)
    fun a b hab => ⟨hab.1.2.1, hab.2.2.1, by rw [hab.1.1.sp, hab.2.1.sp, hq]⟩).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧ K y) (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧ K y)
    fun a b hab => ⟨wU1 hab.1.1 hab.1.2.1 hab.1.2.2, wU1 hab.2.1 hab.2.2.1 hab.2.2.2⟩
  have rJ := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧ K a) ∧ Regs s₀' C D P W R L b ∧ K b) _
    (fun a b hab => regs_agree hq hab.1.1 hab.2.1) hJb).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧ K y ∧ J y)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧ K y ∧ J y)
    fun a b hab => ⟨wJ hab.1.1 hab.1.2, wJ hab.2.1 hab.2.2⟩
  have rM2 := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧ K a ∧ J a) ∧ Regs s₀' C D P W R L b ∧ K b ∧ J b) _
    (fun a b hab => regs_agree' hq hab.1.1 hab.2.1 fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact jj hab.1.2.2 hab.2.2.2) hM2).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧
      UArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L) ∧ K y ∧ J y)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧
      UArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L) ∧ K y ∧ J y)
    fun a b hab => ⟨wM2 h hab.1.1 hab.1.2.1 hab.1.2.2, wM2 h' hab.2.1 hab.2.2.1 hab.2.2.2⟩
  have rU2 := (upd_rel v v.callee.name
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧
      UArgs a C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L) ∧ K a ∧ J a) ∧
      Regs s₀' C D P W R L b ∧
      UArgs b C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L) ∧ K b ∧ J b)
    fun a b hab => ⟨hab.1.2.1, hab.2.2.1, by rw [hab.1.1.sp, hab.2.1.sp, hq]⟩).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧ K y ∧ J y)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧ K y ∧ J y)
    fun a b hab => ⟨wU2 hab.1.1 hab.1.2.1 hab.1.2.2.1 hab.1.2.2.2, wU2 hab.2.1 hab.2.2.1 hab.2.2.2.1 hab.2.2.2.2⟩
  have rM3 := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧ K a ∧ J a) ∧ Regs s₀' C D P W R L b ∧ K b ∧ J b) _
    (fun a b hab => regs_agree' hq hab.1.1 hab.2.1 fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact jj hab.1.2.2 hab.2.2.2
      · exact kk hab.1.2.1 hab.2.2.1) hM3).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧
      FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * kOf L - 16 * jOf L) R)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧
      FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * kOf L - 16 * jOf L) R)
    fun a b hab => ⟨wM3 h hab.1.1 hab.1.2.1 hab.1.2.2, wM3 h' hab.2.1 hab.2.2.1 hab.2.2.2⟩
  have rF := (fin_rel v.ctr ("vg_cmac_aes_finalize" ++ v.ctr.suffix)
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧
      FArgs a C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * kOf L - 16 * jOf L) R) ∧ Regs s₀' C D P W R L b ∧
      FArgs b C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * kOf L - 16 * jOf L) R)
    fun a b hab => ⟨hab.1.2, hab.2.2, by rw [hab.1.1.sp, hab.2.1.sp, hq]⟩).wp
    (F₁ := Regs s₀ C D P W R L) (F₂ := Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (finr_call v.ctr _ hab.1.2) fun _ p => hab.1.1.keep p.saved p.sp p.rd p.wr,
      WP.mono (finr_call v.ctr _ hab.2.2) fun _ p => hab.2.1.keep p.saved p.sp p.rd p.wr⟩
  exact (rT.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((rM1.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((rU1.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((rJ.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((rM2.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((rU2.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((rM3.mono (fun _ _ h => h) fun _ _ h => h.2).seq (rF.mono (fun _ _ h => h) fun _ _ h => h.2)))))))

theorem finish_rel (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀' : State} (h : Env s₀ C D P W R L)
    (h' : Env s₀' C D P W R L) (hq : s₀.sp = s₀'.sp) {out : Nat} (hout : out = 0 ∨ out = 112) :
    RelCT isa (RR s₀ s₀' C D P W R L) (finish v.callee v.ctr.callee v.ctr.suffix out) (RR s₀ s₀' C D P W R L) := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23])
      (.block [.lsr .x .x9 .x23 4]) hc).isSome = true := ⟨_, by taint_decide⟩
  have w {σ x : State} (hx : Regs σ C D P W R L x) :
      WP isa (.block [.lsr .x .x9 .x23 4]) x fun y => Regs σ C D P W R L y ∧
        y.gpr .x9 = BitVec.ofNat 64 (L / 16) := by
    obtain ⟨y, run, x9, g, sp, _, rd, wr⟩ := lsrL_ok hx.x23 h.lt
    exact WP.of_runBlock ⟨y, run, hx.keep' (fun r hr => g r (dec_ne (by decide) hr)) sp rd wr, x9⟩
  have a := (RelCT.taint (A := taint) (P := RR s₀ s₀' C D P W R L) _ (fun a b hab => regs_agree hq hab.1 hab.2)
    hA).wp (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧ y.gpr .x9 = BitVec.ofNat 64 (L / 16))
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧ y.gpr .x9 = BitVec.ofNat 64 (L / 16))
    fun a b hab => ⟨w hab.1, w hab.2⟩
  have ev {y : State} (hy : y.gpr .x9 = BitVec.ofNat 64 (L / 16)) :=
    eval_zero (s := y) (r := .x9) (x := L / 16) (by have := h.lt; omega) hy
  refine (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq (RelCT.ite (fun a b hab => by
    rw [ev hab.1.2, ev hab.2.2]) ?_ ?_)
  · by_cases hL : L < 16
    · exact (short_rel v h h' hq hL hout).mono (fun _ _ p => ⟨p.1.1.1, p.1.2.1⟩) fun _ _ p => p
    · exact RelCT.of_false fun a b hab => by
        have e := hab.2; rw [ev hab.1.1.2] at e; simp at e; omega
  · by_cases hL : L < 16
    · exact RelCT.of_false fun a b hab => by
        have e := hab.2; rw [ev hab.1.1.2] at e; simp at e; omega
    · exact (long_rel v h h' hq (by omega) hout).mono (fun _ _ p => ⟨p.1.1.1, p.1.2.1⟩) fun _ _ p => p

end VG.Proof.AesSiv.AArch64
