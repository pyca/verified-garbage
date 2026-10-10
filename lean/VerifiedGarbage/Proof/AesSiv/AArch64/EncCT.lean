import VerifiedGarbage.Proof.AesSiv.AArch64.Enc
import VerifiedGarbage.Proof.AesSiv.AArch64.CtrCT

/-!
# AES-SIV on AArch64: `encrypt` and `decrypt` are constant time

Two runs with the same public arguments and the same descriptors (`EPub`)
leak the same trace. The taint analysis proves the straight-line pieces from
the registers that are public, with what correctness says about the values
they load: in each iteration the component's address and length from the
descriptor (`adNext_wp`), the same in both runs since the descriptors are.
The calls are related by their callees' contracts (`fin_rel`, `cmacOf_rel`,
`finish_rel`, `ctr_rel'`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.CmacAes.AArch64 (agree_of)
open VG.Proof.CmacAes.Stream.AArch64 (FArgs fin_rel eval_zero eval_nonzero)

variable {s₀ s₀' : State} {C A P W D : Addr} {R N L : Nat}

/-- What two runs agree on besides the arguments `EPre` names: the stack
pointer and the descriptors. -/
structure EPub (s₀ s₀' : State) (A : Addr) (N : Nat) : Prop where
  sp : s₀.sp = s₀'.sp
  desc : ∀ j < N * 16, s₀.mem (A + BitVec.ofNat 64 j) = s₀'.mem (A + BitVec.ofNat 64 j)

/-- The same descriptors list the same components. -/
theorem EPub.comp_eq (hq : EPub s₀ s₀' A N) {i : Nat} (hi : i < N) : comp s₀.mem A i = comp s₀'.mem A i := by
  have r {d : Nat} (hd : d + 8 ≤ N * 16) : s₀.mem.readW (A + BitVec.ofNat 64 d) 64 =
      s₀'.mem.readW (A + BitVec.ofNat 64 d) 64 := by
    have e := Mem.read_congr (m := s₀.mem) (m' := s₀'.mem) (a := A + BitVec.ofNat 64 d) (n := 64 / 8)
      fun j hj => by rw [Offset.add_add]; exact hq.desc (d + j) (by omega)
    simp only [Mem.readW, e]
  unfold comp
  rw [r (d := 16 * i) (by omega), r (d := 16 * i + 8) (by omega)]

/-- The save and S2V's first state. -/
theorem start_rel (v : Proof.CmacAes.AArch64.UpdateImpl) (h : EPre s₀ C A P W D R N L)
    (h' : EPre s₀' C A P W D R N L) (hq : s₀.sp = s₀'.sp) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀')
      (.seq (.block (encPre ++ startPre)) (callFinalize v.ctr.callee v.ctr.suffix))
      fun a b => AInv s₀ C A P W D R N L 0 a ∧ AInv s₀' C A P W D R N L 0 b := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x7])
      (.block (encPre ++ startPre)) hc).isSome = true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    refine agree_of hq fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.x0, h'.x0]
    · rw [h.x1, h'.x1]
    · rw [h.x2, h'.x2]
    · rw [h.x3, h'.x3]
    · rw [h.x4, h'.x4]
    · rw [h.x5, h'.x5]
    · rw [h.x7, h'.x7]) hA).wp
    (F₁ := Started s₀ C A P W D R N L) (F₂ := Started s₀' C A P W D R N L)
    fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨start_ok h, start_ok h'⟩
  have f := (fin_rel v.ctr ("vg_cmac_aes_finalize" ++ v.ctr.suffix)
    (P := fun a b => Started s₀ C A P W D R N L a ∧ Started s₀' C A P W D R N L b)
    fun a b hab => ⟨hab.1.fargs h, hab.2.fargs h', by rw [hab.1.sp, hab.2.sp, hq]⟩).wp
    (F₁ := AInv s₀ C A P W D R N L 0) (F₂ := AInv s₀' C A P W D R N L 0)
    fun a b hab => ⟨start_wp v h hab.1, start_wp v h' hab.2⟩
  exact (a.mono (fun _ _ p => p) fun _ _ p => p.2).seq (f.mono (fun _ _ p => p) fun _ _ p => p.2)

/-- The state before the components, in both runs. -/
abbrev AA (s₀ s₀' : State) (C A P W D : Addr) (R N L i : Nat) (a b : State) : Prop :=
  AInv s₀ C A P W D R N L i a ∧ AInv s₀' C A P W D R N L i b

/-- The descriptor's pointer and the count left, as in the loop's state. -/
def XA (A : Addr) (N i : Nat) (s : State) : Prop :=
  s.gpr .x24 = A + BitVec.ofNat 64 (16 * i) ∧ s.gpr .x25 = BitVec.ofNat 64 (N - i)

/-- One component in both runs. -/
theorem adBody_rel (v : Proof.CmacAes.AArch64.UpdateImpl) (h : EPre s₀ C A P W D R N L)
    (h' : EPre s₀' C A P W D R N L) (hq : EPub s₀ s₀' A N) {i : Nat} (hiN : i < N) :
    RelCT isa (AA s₀ s₀' C A P W D R N L i)
      (.seq (.block adNext) (.seq (cmacOf v.callee v.ctr.callee v.ctr.suffix stOff) (.block adStep)))
      (AA s₀ s₀' C A P W D R N L (i + 1)) := by
  have hQ := h.comps _ (comp_mem s₀.mem A hiN)
  have hQ' := h'.comps _ (comp_mem s₀'.mem A hiN)
  have ec := hq.comp_eq hiN
  rw [← ec] at hQ'
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x24, .x25])
      (.block adNext) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24, .x25])
      (.block adStep) hc).isSome = true := ⟨_, by taint_decide⟩
  have p₁ := (RelCT.taint (A := taint) (P := AA s₀ s₀' C A P W D R N L i) _
    (fun a b hab => by
      refine agree_of (by rw [hab.1.sp, hab.2.sp, hq.sp]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hab.1.x19, hab.2.x19]
      · rw [hab.1.x20, hab.2.x20]
      · rw [hab.1.x21, hab.2.x21]
      · rw [hab.1.x24, hab.2.x24]
      · rw [hab.1.x25, hab.2.x25]) hA).wp
    (F₁ := fun (s : State) => Regs s₀ C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len s ∧ XA A N i s)
    (F₂ := fun (s : State) => Regs s₀' C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len s ∧ XA A N i s)
    fun a b hab => ⟨WP.mono (adNext_wp h hiN hab.1) fun _ p =>
        ⟨p.1, by rw [p.2.1 _ (by decide) (by decide), hab.1.x24], by rw [p.2.1 _ (by decide) (by decide), hab.1.x25]⟩,
      WP.mono (adNext_wp h' hiN hab.2) fun _ p => ⟨by rw [ec]; exact p.1,
        by rw [p.2.1 _ (by decide) (by decide), hab.2.x24], by rw [p.2.1 _ (by decide) (by decide), hab.2.x25]⟩⟩
  have xa {σ s : State} (hσ : Env σ C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len)
      (hs : Regs σ C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len s ∧ XA A N i s) :
      WP isa (cmacOf v.callee v.ctr.callee v.ctr.suffix stOff) s fun t =>
        Regs σ C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len t ∧ XA A N i t :=
    WP.mono (cmacOf_wp v hσ hs.1) fun _ p =>
      ⟨p.regs, by rw [p.hold _ (by decide), hs.2.1], by rw [p.hold _ (by decide), hs.2.2]⟩
  have p₂ := ((cmacOf_rel v hQ hQ' hq.sp).mono
    (P' := fun a b => (Regs s₀ C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len a ∧ XA A N i a) ∧
      Regs s₀' C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len b ∧ XA A N i b)
    (fun _ _ p => ⟨p.1.1, p.2.1⟩) fun _ _ p => p).wp
    (F₁ := fun (s : State) => Regs s₀ C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len s ∧ XA A N i s)
    (F₂ := fun (s : State) => Regs s₀' C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len s ∧ XA A N i s)
    fun a b hab => ⟨xa hQ hab.1, xa hQ' hab.2⟩
  have p₃ := RelCT.taint (A := taint)
    (P := fun a b => (Regs s₀ C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len a ∧ XA A N i a) ∧
      Regs s₀' C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len b ∧ XA A N i b) _
    (fun a b hab => by
      have e := regs_agree' (rs := [.x24, .x25]) hq.sp hab.1.1 hab.2.1 fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.2.1, hab.2.2.1]
        · rw [hab.1.2.2, hab.2.2.2]
      exact e) hC
  have body := (p₁.mono (fun _ _ p => p) fun _ _ p => p.2).seq
    ((p₂.mono (fun _ _ p => p) fun _ _ p => p.2).seq p₃)
  exact (body.wp (F₁ := AInv s₀ C A P W D R N L (i + 1)) (F₂ := AInv s₀' C A P W D R N L (i + 1))
    fun a b hab => ⟨adBody_wp v h hiN hab.1, adBody_wp v h' hiN hab.2⟩).mono (fun _ _ p => p) fun _ _ p => p.2

/-- S2V over the components in both runs. -/
theorem ads_rel (v : Proof.CmacAes.AArch64.UpdateImpl) (h : EPre s₀ C A P W D R N L)
    (h' : EPre s₀' C A P W D R N L) (hq : EPub s₀ s₀' A N) :
    RelCT isa (AA s₀ s₀' C A P W D R N L 0) (s2vAds v.callee v.ctr.callee v.ctr.suffix)
      (AA s₀ s₀' C A P W D R N L N) := by
  have hN := h.N_lt
  have ev {σ s : State} (hs : AInv σ C A P W D R N L 0 s) : isa.eval (.zero .x .x25) s = some (decide (N = 0)) :=
    eval_zero hN (by rw [hs.x25, Nat.sub_zero])
  refine RelCT.ite (fun a b hab => by rw [ev hab.1, ev hab.2]) ?_ ?_
  · refine RelCT.block_nil fun a b hab => ?_
    have e := hab.2
    rw [ev hab.1.1] at e
    have hN0 : N = 0 := by simpa using e
    rw [hN0] at hab ⊢
    exact hab.1
  by_cases hN0 : N = 0
  · exact RelCT.of_false fun a b hab => by
      have e := hab.2; rw [ev hab.1.1] at e; simp [hN0] at e
  refine (RelCT.loop (M := isa) (c := .nonzero .x .x25)
    (fun (n : Nat) (a b : State) => ∃ i, n = N - i ∧ i < N ∧ AA s₀ s₀' C A P W D R N L i a b) (fun n => ?_)
    (N - 0)).mono (fun a b hab => ⟨0, rfl, Nat.pos_of_ne_zero hN0, hab.1⟩) fun _ _ p => p
  refine RelCT.exists_ fun i => ?_
  by_cases hc : n = N - i ∧ i < N
  swap
  · exact RelCT.of_false fun _ _ p => hc ⟨p.1, p.2.1⟩
  obtain ⟨rfl, hiN⟩ := hc
  refine (adBody_rel v h h' hq hiN).mono (fun _ _ p => p.2.2) fun a b p => ?_
  have ea := eval_nonzero (s := a) (r := .x25) (x := N - (i + 1)) (by omega) p.1.x25
  have eb := eval_nonzero (s := b) (r := .x25) (x := N - (i + 1)) (by omega) p.2.x25
  refine ⟨by rw [ea, eb], fun e => ?_, fun e => ?_⟩
  · have he : i + 1 = N := by rw [ea] at e; simp at e; omega
    subst he; exact p
  · have he : i + 1 ≠ N := by rw [ea] at e; simp at e; omega
    exact ⟨N - (i + 1), by omega, i + 1, rfl, by omega, p⟩

/-- S2V of the associated data in both runs. -/
theorem encS2v_rel (v : Proof.CmacAes.AArch64.UpdateImpl) (h : EPre s₀ C A P W D R N L)
    (h' : EPre s₀' C A P W D R N L) (hq : EPub s₀ s₀' A N) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (encS2v v.callee v.ctr.callee v.ctr.suffix)
      fun a b => SDone s₀ C A P W D R N L a ∧ SDone s₀' C A P W D R N L b := by
  obtain ⟨_, hE⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x26, .x27])
      (.block [mov .x22 .x26, mov .x23 .x27]) hc).isSome = true := ⟨_, by taint_decide⟩
  have e := (RelCT.taint (A := taint) (P := AA s₀ s₀' C A P W D R N L N) _
    (fun a b hab => by
      refine agree_of (by rw [hab.1.sp, hab.2.sp, hq.sp]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hab.1.x26, hab.2.x26]
      · rw [hab.1.x27, hab.2.x27]) hE).wp
    (F₁ := SDone s₀ C A P W D R N L) (F₂ := SDone s₀' C A P W D R N L)
    fun a b hab => ⟨adsEnd_wp hab.1, adsEnd_wp hab.2⟩
  exact RelCT.assoc ((start_rel v h h' hq.sp).seq ((ads_rel v h h' hq).seq
    (e.mono (fun _ _ p => p) fun _ _ p => p.2)))

/-! ## The ends -/

theorem finish_spre (v : Proof.CmacAes.AArch64.UpdateImpl) {σ : State} {C D P W : Addr} {R L : Nat}
    (h : Env σ C D P W R L) {s : State} (hs : SPre σ C D P W R L s) {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (finish v.callee v.ctr.callee v.ctr.suffix out) s (SPre σ C D P W R L) :=
  WP.mono (finish_wp v h hs.regs hout) fun t ht =>
    ⟨ht.regs, by rw [ht.hold.1, hs.x26], by rw [ht.hold.2, hs.x27]⟩

theorem counter_ctrPre {σ : State} {C D P W : Addr} {R L : Nat} (h : Env σ C D P W R L) {s : State}
    (hs : SPre σ C D P W R L s) : WP isa (.block (counter 0)) s (CtrPre σ C D P W R L) := by
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := counter_ok h hs.regs.x19 hs.regs.rd hs.regs.wr
  obtain ⟨hi, lo, e₁, e₂, e₃⟩ := counter_cnt s.mem W
  refine WP.of_runBlock ⟨s₁, run₁, hs.regs.keep' (fun r hr => g₁ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) sp₁ rd₁ wr₁, by rw [g₁ _ (by decide) (by decide), hs.x26],
    by rw [g₁ _ (by decide) (by decide), hs.x27], ⟨hi, lo, _, by rw [m₁]; exact e₁, by rw [m₁]; exact e₂, e₃, length_counter _, counter_low _⟩⟩

/-- The registers of both runs, with the data in `x26` and `x27`. -/
abbrev RD (s₀ s₀' : State) (C D P W : Addr) (R L : Nat) (a b : State) : Prop :=
  (Regs s₀ C D P W R L a ∧ a.gpr .x26 = P ∧ a.gpr .x27 = BitVec.ofNat 64 L) ∧
    Regs s₀' C D P W R L b ∧ b.gpr .x26 = P ∧ b.gpr .x27 = BitVec.ofNat 64 L

theorem rd_agree {s₀ s₀' : State} {C D P W : Addr} {R L : Nat} (hq : s₀.sp = s₀'.sp) {a b : State}
    (hab : RD s₀ s₀' C D P W R L a b) :
    taint.Agree (Taint.ofRegs (([.x19, .x20, .x21, .x22, .x23] : List Reg) ++ ([.x26, .x27] : List Reg))) a b :=
  regs_agree' hq hab.1.1 hab.2.1 fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hab.1.2.1, hab.2.2.1]
    · rw [hab.1.2.2, hab.2.2.2]

/-- The address of `siv`, `T`, in its slot of the working space. -/
abbrev Slot (W T : Addr) (s : State) : Prop := s.mem.readW (W + BitVec.ofNat 64 248) 64 = T

theorem finish_slot (v : Proof.CmacAes.AArch64.UpdateImpl) {σ : State} {C D P W T : Addr} {R L : Nat}
    (h : Env σ C D P W R L) {s : State} (hs : SPre σ C D P W R L s) (hl : Slot W T s) :
    WP isa (finish v.callee v.ctr.callee v.ctr.suffix 0) s fun t => SPre σ C D P W R L t ∧ Slot W T t :=
  WP.mono (finish_wp v h hs.regs (Or.inl rfl)) fun t ht =>
    ⟨⟨ht.regs, by rw [ht.hold.1, hs.x26], by rw [ht.hold.2, hs.x27]⟩, by
      rw [Slot, ht.frame.readW (Region.contains_self _ _)
        (fin_dis h (out := 0) (d := 248) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)) (by decide)]
      exact hl⟩

theorem counter_slot {σ : State} {C D P W T : Addr} {R L : Nat} (h : Env σ C D P W R L) {s : State}
    (hs : SPre σ C D P W R L s) (hl : Slot W T s) :
    WP isa (.block (counter 0)) s fun t => CtrPre σ C D P W R L t ∧ Slot W T t := by
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := counter_ok h hs.regs.x19 hs.regs.rd hs.regs.wr
  obtain ⟨hi, lo, e₁, e₂, e₃⟩ := counter_cnt s.mem W
  refine WP.of_runBlock ⟨s₁, run₁, ⟨hs.regs.keep' (fun r hr => g₁ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) sp₁ rd₁ wr₁, by rw [g₁ _ (by decide) (by decide), hs.x26],
    by rw [g₁ _ (by decide) (by decide), hs.x27], ⟨hi, lo, _, by rw [m₁]; exact e₁, by rw [m₁]; exact e₂, e₃, length_counter _, counter_low _⟩⟩, ?_⟩
  have f₁ : Frame (cntRegions W) s.mem s₁.mem := m₁ ▸ counter_frame _ _ _ _
  rw [Slot, f₁.readW (Region.contains_self _ _) (cnt_dis (d := 248) (by decide) (by decide)) (by decide)]
  exact hl

theorem ctr_slot (v : Proof.Aes.AArch64.Ctr32Impl) {σ : State} {C D P W T : Addr} {R L : Nat}
    (h : Env σ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (hPw : (⟨P, L⟩ : Region) ∈ σ.wr)
    {s : State} (hs : CtrPre σ C D P W R L s) (hl : Slot W T s) :
    WP isa (ctr v.callee) s (Slot W T) := by
  obtain ⟨hi, lo, q, e₁, e₂, e₃, hql, hlow⟩ := hs.cnt
  refine WP.mono (ctr_wp v h hcp hPw hs.regs hql hlow ⟨hi, lo, e₁, e₂, e₃⟩ hs.x26 hs.x27) fun t ht => ?_
  rw [Slot, ht.frame.readW (Region.contains_self _ _) (ctr_dis h (d := 248) (by decide) (by decide))
    (by decide)]
  exact hl

/-- The copy of the IV to `siv`, in both runs: its addresses, `T` and `W`,
are the same. -/
theorem sivOut_rel {σ σ' : State} {C D P W T : Addr} {R L : Nat} (h : Env σ C D P W R L)
    (h' : Env σ' C D P W R L) (hq : σ.sp = σ'.sp) (hTw : (⟨T, 16⟩ : Region) ∈ σ.wr)
    (hTw' : (⟨T, 16⟩ : Region) ∈ σ'.wr) (wT : T.toNat + 16 ≤ 2 ^ 64) :
    RelCT isa (fun a b => (RD σ σ' C D P W R L a b ∧ Slot W T a) ∧ Slot W T b) (.block sivOut)
      fun a b => (a.gpr .x19 = W ∧ a.sp = σ.sp) ∧ b.gpr .x19 = W ∧ b.sp = σ'.sp := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19]) (.block (sivOut.take 1)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x9, .x19]) (.block (sivOut.drop 1)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have run {σ : State} (e : Env σ C D P W R L) (hTw : (⟨T, 16⟩ : Region) ∈ σ.wr) {s : State}
      (hr : Regs σ C D P W R L s) (hl : Slot W T s) :
      ∃ s', runBlock isa sivOut s = some s' ∧ s'.gpr .x19 = W ∧ s'.sp = σ.sp := by
    have inT (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (T + BitVec.ofNat 64 d) 8 := by
      rw [hr.wr]; exact ⟨_, hTw, Offset.contains_base T hd (by have := wT; omega)⟩
    obtain ⟨s', run', -, g', sp', -, -⟩ := sivOut_ok hr.x19 hl (e.inRW hr.rd hr.wr (d := 248) (n := 8) (by decide))
      (e.inRW hr.rd hr.wr (d := 0) (n := 8) (by decide)) (e.inRW hr.rd hr.wr (d := 8) (n := 8) (by decide))
      (inT 0 (by decide)) (inT 8 (by decide))
    exact ⟨s', run', by rw [g' _ (by decide) (by decide), hr.x19], by rw [sp', hr.sp]⟩
  have head {σ : State} (e : Env σ C D P W R L) {s : State} (hr : Regs σ C D P W R L s) (hl : Slot W T s) :
      WP isa (.block (sivOut.take 1)) s fun t => t.gpr .x9 = T ∧ t.gpr .x19 = W ∧ t.sp = σ.sp := by
    have r₂ := e.inRW hr.rd hr.wr (d := 248) (n := 8) (by decide)
    simp only [Slot, Mem.readW, BitVec.setWidth_eq] at hl
    exact WP.of_runBlock ⟨_, by
      simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceMul, and_self, sivOut, List.take,
        runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits,
        Option.bind_some, Option.map_some, BitVec.setWidth_eq, hr.x19, r₂, hl]
      rfl, by simp [gpr_write], by simp [gpr_write, hr.x19], by rw [← hr.sp]; rfl⟩
  have a := (RelCT.taint (A := taint) (P := fun (a b : State) => (RD σ σ' C D P W R L a b ∧ Slot W T a) ∧ Slot W T b) _
    (fun a b hab => agree_of (by rw [hab.1.1.1.1.sp, hab.1.1.2.1.sp, hq]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.1.1.1.x19, hab.1.1.2.1.x19]) hA).wp
    (F₁ := fun (t : State) => t.gpr .x9 = T ∧ t.gpr .x19 = W ∧ t.sp = σ.sp)
    (F₂ := fun (t : State) => t.gpr .x9 = T ∧ t.gpr .x19 = W ∧ t.sp = σ'.sp)
    fun a b hab => ⟨head h hab.1.1.1.1 hab.1.2, head h' hab.1.1.2.1 hab.2⟩
  have b := RelCT.taint (A := taint)
    (P := fun (a b : State) => (a.gpr .x9 = T ∧ a.gpr .x19 = W ∧ a.sp = σ.sp) ∧
      b.gpr .x9 = T ∧ b.gpr .x19 = W ∧ b.sp = σ'.sp) _
    (fun a b hab => agree_of (by rw [hab.1.2.2, hab.2.2.2, hq]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hab.1.1, hab.2.1]
      · rw [hab.1.2.1, hab.2.2.1]) hB
  rw [show (Code.block sivOut : Prog isa) = .block (sivOut.take 1 ++ sivOut.drop 1) by
    rw [List.take_append_drop]]
  refine ((RelCT.block_append ((a.mono (fun _ _ p => p) fun _ _ p => p.2).seq b)).wp
    (F₁ := fun (t : State) => t.gpr .x19 = W ∧ t.sp = σ.sp)
    (F₂ := fun (t : State) => t.gpr .x19 = W ∧ t.sp = σ'.sp) fun a b hab => ?_).mono
    (fun _ _ p => p) fun _ _ p => p.2
  rw [List.take_append_drop]
  obtain ⟨a', ra, xa, sa⟩ := run h hTw hab.1.1.1.1 hab.1.2
  obtain ⟨b', rb, xb, sb⟩ := run h' hTw' hab.1.1.2.1 hab.2
  exact ⟨WP.of_runBlock ⟨a', ra, xa, sa⟩, WP.of_runBlock ⟨b', rb, xb, sb⟩⟩

theorem sealTail_rel (v : Proof.CmacAes.AArch64.UpdateImpl) {σ σ' : State} {C D P W T : Addr} {R L : Nat}
    (h : Env σ C D P W R L) (h' : Env σ' C D P W R L) (hq : σ.sp = σ'.sp)
    (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (hPw : (⟨P, L⟩ : Region) ∈ σ.wr)
    (hPw' : (⟨P, L⟩ : Region) ∈ σ'.wr) (hTw : (⟨T, 16⟩ : Region) ∈ σ.wr)
    (hTw' : (⟨T, 16⟩ : Region) ∈ σ'.wr) (wT : T.toNat + 16 ≤ 2 ^ 64) :
    RelCT isa (fun a b => (SPre σ C D P W R L a ∧ Slot W T a) ∧ SPre σ' C D P W R L b ∧ Slot W T b)
      (.seq (finish v.callee v.ctr.callee v.ctr.suffix 0)
        (.seq (.block (counter 0)) (.seq (ctr v.ctr.callee) (.seq (.block sivOut) (.block restore)))))
      fun _ _ => True := by
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23])
      (.block (counter 0)) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19]) (.block restore) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have f := ((finish_rel v h h' hq (Or.inl rfl)).mono
      (P' := fun (a b : State) => (SPre σ C D P W R L a ∧ Slot W T a) ∧ SPre σ' C D P W R L b ∧ Slot W T b)
      (fun _ _ p => ⟨p.1.1.regs, p.2.1.regs⟩) fun _ _ p => p).wp
    (F₁ := fun (t : State) => SPre σ C D P W R L t ∧ Slot W T t)
    (F₂ := fun (t : State) => SPre σ' C D P W R L t ∧ Slot W T t)
    fun a b hab => ⟨finish_slot v h hab.1.1 hab.1.2, finish_slot v h' hab.2.1 hab.2.2⟩
  have c := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (SPre σ C D P W R L a ∧ Slot W T a) ∧ SPre σ' C D P W R L b ∧ Slot W T b) _
    (fun a b hab => regs_agree hq hab.1.1.regs hab.2.1.regs) hB).wp
    (F₁ := fun (t : State) => CtrPre σ C D P W R L t ∧ Slot W T t)
    (F₂ := fun (t : State) => CtrPre σ' C D P W R L t ∧ Slot W T t)
    fun a b hab => ⟨counter_slot h hab.1.1 hab.1.2, counter_slot h' hab.2.1 hab.2.2⟩
  have k := ((ctr_rel' v.ctr h h' hq hcp hPw hPw').mono
      (P' := fun (a b : State) => (CtrPre σ C D P W R L a ∧ Slot W T a) ∧ CtrPre σ' C D P W R L b ∧ Slot W T b)
      (fun _ _ p => ⟨p.1.1, p.2.1⟩) fun _ _ p => p).wp
    (F₁ := Slot W T) (F₂ := Slot W T)
    fun a b hab => ⟨ctr_slot v.ctr h hcp hPw hab.1.1 hab.1.2, ctr_slot v.ctr h' hcp hPw' hab.2.1 hab.2.2⟩
  have r := RelCT.taint (A := taint)
    (P := fun (a b : State) => (a.gpr .x19 = W ∧ a.sp = σ.sp) ∧ b.gpr .x19 = W ∧ b.sp = σ'.sp) _
    (fun a b hab => agree_of (by rw [hab.1.2, hab.2.2, hq]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.1, hab.2.1]) hC
  exact (f.mono (fun _ _ p => p) fun _ _ p => p.2).seq ((c.mono (fun _ _ p => p) fun _ _ p => p.2).seq
    ((k.mono (fun _ _ p => p) fun _ _ p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩).seq ((sivOut_rel h h' hq hTw hTw' wT).seq r)))

/-- `decrypt`'s end, from the registers in both runs: it compares the IVs
and masks the data without a branch, so nothing it does depends on the
result. -/
theorem openTail_rel (v : Proof.CmacAes.AArch64.UpdateImpl) {σ σ' : State} {C D P W : Addr} {R L : Nat}
    (h : Env σ C D P W R L) (h' : Env σ' C D P W R L) (hq : σ.sp = σ'.sp)
    (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (hPw : (⟨P, L⟩ : Region) ∈ σ.wr)
    (hPw' : (⟨P, L⟩ : Region) ∈ σ'.wr) :
    RelCT isa (fun a b => SPre σ C D P W R L a ∧ SPre σ' C D P W R L b)
      (.seq (.block (counter 0)) (.seq (ctr v.ctr.callee) (.seq (finish v.callee v.ctr.callee v.ctr.suffix tOff)
        (.seq (.block Impl.AesSiv.AArch64.compare) (.seq maskData (.block restore))))))
      fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23])
      (.block (counter 0)) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs (([.x19, .x20, .x21, .x22, .x23] : List Reg) ++ ([.x26, .x27] : List Reg)))
      (.seq (.block Impl.AesSiv.AArch64.compare) (.seq maskData (.block restore))) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have c := (RelCT.taint (A := taint) (P := fun a b => SPre σ C D P W R L a ∧ SPre σ' C D P W R L b) _
    (fun a b hab => regs_agree hq hab.1.regs hab.2.regs) hA).wp
    (F₁ := CtrPre σ C D P W R L) (F₂ := CtrPre σ' C D P W R L) fun a b hab =>
      ⟨counter_ctrPre h hab.1, counter_ctrPre h' hab.2⟩
  have f := ((finish_rel v h h' hq (Or.inr rfl)).mono (P' := RD σ σ' C D P W R L)
      (fun _ _ p => ⟨p.1.1, p.2.1⟩) fun _ _ p => p).wp
    (F₁ := SPre σ C D P W R L) (F₂ := SPre σ' C D P W R L) fun a b hab =>
      ⟨finish_spre v h ⟨hab.1.1, hab.1.2.1, hab.1.2.2⟩ (Or.inr rfl),
        finish_spre v h' ⟨hab.2.1, hab.2.2.1, hab.2.2.2⟩ (Or.inr rfl)⟩
  have t := RelCT.taint (A := taint) (P := fun a b => SPre σ C D P W R L a ∧ SPre σ' C D P W R L b)
    _
    (fun a b hab => rd_agree hq ⟨⟨hab.1.regs, hab.1.x26, hab.1.x27⟩, hab.2.regs, hab.2.x26, hab.2.x27⟩) hB
  exact (c.mono (fun _ _ p => p) fun _ _ p => p.2).seq ((ctr_rel' v.ctr h h' hq hcp hPw hPw').seq
    ((f.mono (fun _ _ p => p) fun _ _ p => p.2).seq t))

/-- The address of `siv` in its slot after S2V. -/
theorem SDone.slot {T : Addr} (hT : SivArg s₀ P W D T L) {s : State} (hs : SDone s₀ C A P W D R N L s) :
    Slot W T s := by
  show s.mem.readW (W + BitVec.ofNat 64 248) 64 = T
  rw [hs.saved (.x6, 248) (by decide), hT.x6]

theorem encrypt_rel (v : Proof.CmacAes.AArch64.UpdateImpl) (h : EPre s₀ C A P W D R N L)
    (h' : EPre s₀' C A P W D R N L) {T : Addr} (hT : SivArg s₀ P W D T L) (hT' : SivArg s₀' P W D T L)
    (hTw : (⟨T, 16⟩ : Region) ∈ s₀.wr) (hTw' : (⟨T, 16⟩ : Region) ∈ s₀'.wr) (hq : EPub s₀ s₀' A N) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (encrypt v.callee v.ctr.callee v.ctr.suffix) fun _ _ => True :=
  (encS2v_rel v h h' hq).seq ((sealTail_rel v h.env h'.env hq.sp h.cp h.pw h'.pw hTw hTw' hT.wT).mono
    (fun _ _ p => ⟨⟨p.1.spre, p.1.slot hT⟩, p.2.spre, p.2.slot hT'⟩) fun _ _ p => p)

/-- The copy of the received IV to `W`, in both runs: its addresses, `T` and
`W`, are the same. -/
theorem sivIn_rel (h : EPre s₀ C A P W D R N L) (h' : EPre s₀' C A P W D R N L) {T : Addr}
    (hT : SivArg s₀ P W D T L) (hT' : SivArg s₀' P W D T L) (hq : s₀.sp = s₀'.sp) :
    RelCT isa (fun a b => SDone s₀ C A P W D R N L a ∧ SDone s₀' C A P W D R N L b) (.block sivIn)
      fun a b => SPre s₀ C D P W R L a ∧ SPre s₀' C D P W R L b := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19]) (.block (sivIn.take 1)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x9, .x19]) (.block (sivIn.drop 1)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have head {σ : State} (e : EPre σ C A P W D R N L) (hT : SivArg σ P W D T L) {s : State}
      (hs : SDone σ C A P W D R N L s) :
      WP isa (.block (sivIn.take 1)) s fun t => t.gpr .x9 = T ∧ t.gpr .x19 = W ∧ t.sp = σ.sp := by
    have hr := hs.spre.regs
    have r₂ := e.env.inRW hr.rd hr.wr (d := 248) (n := 8) (by decide)
    have hl := hs.slot hT
    simp only [Slot, Mem.readW, BitVec.setWidth_eq] at hl
    exact WP.of_runBlock ⟨_, by
      simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceMul, and_self, sivIn, List.take,
        runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits,
        Option.bind_some, Option.map_some, BitVec.setWidth_eq, hr.x19, r₂, hl]
      rfl, by simp [gpr_write], by simp [gpr_write, hr.x19], by rw [← hr.sp]; rfl⟩
  have a := (RelCT.taint (A := taint)
    (P := fun (a b : State) => SDone s₀ C A P W D R N L a ∧ SDone s₀' C A P W D R N L b) _
    (fun a b hab => agree_of (by rw [hab.1.spre.regs.sp, hab.2.spre.regs.sp, hq]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.spre.regs.x19, hab.2.spre.regs.x19]) hA).wp
    (F₁ := fun (t : State) => t.gpr .x9 = T ∧ t.gpr .x19 = W ∧ t.sp = s₀.sp)
    (F₂ := fun (t : State) => t.gpr .x9 = T ∧ t.gpr .x19 = W ∧ t.sp = s₀'.sp)
    fun a b hab => ⟨head h hT hab.1, head h' hT' hab.2⟩
  have b := RelCT.taint (A := taint)
    (P := fun (a b : State) => (a.gpr .x9 = T ∧ a.gpr .x19 = W ∧ a.sp = s₀.sp) ∧
      b.gpr .x9 = T ∧ b.gpr .x19 = W ∧ b.sp = s₀'.sp) _
    (fun a b hab => agree_of (by rw [hab.1.2.2, hab.2.2.2, hq]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hab.1.1, hab.2.1]
      · rw [hab.1.2.1, hab.2.2.1]) hB
  rw [show (Code.block sivIn : Prog isa) = .block (sivIn.take 1 ++ sivIn.drop 1) by
    rw [List.take_append_drop]]
  refine ((RelCT.block_append ((a.mono (fun _ _ p => p) fun _ _ p => p.2).seq b)).wp
    (F₁ := SPre s₀ C D P W R L) (F₂ := SPre s₀' C D P W R L) fun a b hab => ?_).mono
    (fun _ _ p => p) fun _ _ p => p.2
  rw [List.take_append_drop]
  exact ⟨WP.mono (sivIn_wp h hT hab.1) fun _ p => p.1, WP.mono (sivIn_wp h' hT' hab.2) fun _ p => p.1⟩

theorem decrypt_rel (v : Proof.CmacAes.AArch64.UpdateImpl) (h : EPre s₀ C A P W D R N L)
    (h' : EPre s₀' C A P W D R N L) {T : Addr} (hT : SivArg s₀ P W D T L) (hT' : SivArg s₀' P W D T L)
    (hq : EPub s₀ s₀' A N) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (decrypt v.callee v.ctr.callee v.ctr.suffix) fun _ _ => True :=
  (encS2v_rel v h h' hq).seq ((sivIn_rel h h' hT hT' hq.sp).seq
    (openTail_rel v h.env h'.env hq.sp h.cp h.pw h'.pw))

end VG.Proof.AesSiv.AArch64
