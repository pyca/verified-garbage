module

public import VerifiedGarbage.Proof.Rsa.X86.KcTimeCheck
public import VerifiedGarbage.Proof.Rsa.X86.KcWordChecks
public import VerifiedGarbage.Proof.Rsa.X86.KcLoads
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Time
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Rsa.X86.KcOps
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.X86.KcLoad
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Mul
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Loop
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega

/-! # The traces of the checks of an RSA key on i686

The runs are related piece by piece: what the taint analysis checks with
the arguments, `edi` and `esp` public (`τV`), from states that keep them
(`Run`), and the loops counted in the header by `WordRt`'s relations. Up to
the guard, each run's values are known (`Stg`); the guard, of the arguments
and `n`'s top word, is the same in both runs when their `n` is; after it,
each piece keeps only the frame (`Fm`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck VG.Impl.Rsa.X86.KeyCheckRt
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.WordRt (MLen wq mw Bal)

/-! ## Runs -/

/-- The return address and the arguments lie apart from every writable region. -/
def ArgsOk (full : Bool) (s : State) : Prop :=
  (s.gpr .esp).toNat + argSpan full ≤ 2 ^ 32 ∧
    ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, argSpan full⟩ r

theorem τV_wf {full : Bool} {s : State} (A : ArgsOk full s) : VG.X86.Taint.Wf (τV full) s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => A, fun _ h => (List.not_mem_nil h).elim⟩

theorem agreeV {g : CallGeometry} {s₁ s₂ : State} (h₁ : Inputs g s₁) (h₂ : Inputs g s₂)
    (A₁ : ArgsOk g.full s₁) (A₂ : ArgsOk g.full s₂) (sp : s₁.gpr .esp = s₂.gpr .esp) :
    VG.X86.Taint.Agree (τV g.full) s₁ s₂ := by
  have f₁ := A₁.1
  have f₂ := A₂.1
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τV_wf A₁, τV_wf A₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τV, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (h₁.ws.workspace.edi_toNat.trans h₂.ws.workspace.edi_toNat.symm)
    · exact sp
  · simp only [τV, argSpan] at hk
    rw [show VG.X86.Taint.depth (τV g.full).stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (show arg s₁ _ = arg s₂ _ from
      (h₁.arguments _ (by omega)).value.trans (h₂.arguments _ (by omega)).value.symm)

/-- What a narrowed run of `sized` keeps: the inputs, the arguments apart and `esp`. -/
def Run (g : CallGeometry) (sp : BitVec 32) (s : State) : Prop :=
  Inputs g s ∧ ArgsOk g.full s ∧ s.gpr .esp = sp

/-- A run through a frame of the working space. -/
theorem Run.frame {g : CallGeometry} {sp : BitVec 32} {u t : State} (h : Run g sp u) {rs : List Reg}
    (K : Keeps rs u t) (di : .edi ∉ rs) (spn : .esp ∉ rs) (O : Outside g.base 0 g.size u.mem t.mem) :
    Run g sp t :=
  ⟨h.1.after K di spn (h.1.scratchFrame O), ⟨by rw [K.1 _ spn]; exact h.2.1.1, by rw [K.2.2, K.1 _ spn]; exact h.2.1.2⟩,
    (K.1 _ spn).trans h.2.2⟩

theorem Run.agree {g : CallGeometry} {sp : BitVec 32} {t₁ t₂ : State} (h₁ : Run g sp t₁) (h₂ : Run g sp t₂) :
    VG.X86.Taint.Agree (τV g.full) t₁ t₂ :=
  agreeV h₁.1 h₂.1 h₁.2.1 h₂.2.1 (h₁.2.2.trans h₂.2.2.symm)

/-! ## Sequences -/

theorem exec_seqs_append {l₁ l₂ : List (Prog isa)} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) {s s' : State} {tr : List Leak}
    (e : Exec isa (seqs (l₁ ++ l₂)) s tr s') : Exec isa (.seq (seqs l₁) (seqs l₂)) s tr s' := by
  induction l₁ generalizing s tr with
  | nil => exact absurd rfl h₁
  | cons c l ih =>
    rcases l with _ | ⟨d, l⟩
    · match l₂, h₂ with
      | _ :: _, _ => exact e
    · rw [List.cons_append] at e
      change Exec isa (.seq c (seqs ((d :: l) ++ l₂))) s tr s' at e
      cases e with
      | seq e₁ e₂ =>
        cases ih (by simp) e₂ with
        | seq a b =>
          rw [← List.append_assoc]
          exact .seq (.seq e₁ a) b

theorem RelCT.seqs_append {P Q : State → State → Prop} {l₁ l₂ : List (Prog isa)} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ [])
    (h : RelCT isa P (.seq (seqs l₁) (seqs l₂)) Q) : RelCT isa P (seqs (l₁ ++ l₂)) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (exec_seqs_append h₁ h₂ e₁) (exec_seqs_append h₁ h₂ e₂)

theorem RelCT.seqs_cons {P R Q : State → State → Prop} {c : Prog isa} {l : List (Prog isa)} (hl : l ≠ [])
    (h₁ : RelCT isa P c R) (h₂ : RelCT isa R (seqs l) Q) : RelCT isa P (seqs (c :: l)) Q := by
  match l, hl with
  | _ :: _, _ => exact VG.RelCT.seq h₁ h₂

/-- The same relation through every element of a sequence. -/
theorem RelCT.seqs_all {P : State → State → Prop} :
    ∀ {l : List (Prog isa)}, l ≠ [] → (∀ c ∈ l, RelCT isa P c P) → RelCT isa P (seqs l) P
  | [c], _, h => h c (by simp)
  | c :: d :: l, _, h => RelCT.seqs_cons (by simp) (h c (by simp))
      (RelCT.seqs_all (l := d :: l) (by simp) fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ## Lifting the relations of pieces -/

/-- A piece related from the states of both runs, each from its own start `u`, run by each from
what it knows of its run. -/
theorem relLift {α : Type} {c : Prog isa} {P Q : α → State → Prop} {Rel : α → α → Prop}
    (hrel : RelCT isa (fun t₁ t₂ => ∃ u₁ u₂, Rel u₁ u₂ ∧ P u₁ t₁ ∧ P u₂ t₂) c fun _ _ => True)
    (hw : ∀ u t, P u t → WP isa c t (Q u)) :
    RelCT isa (fun t₁ t₂ => ∃ u₁ u₂, Rel u₁ u₂ ∧ P u₁ t₁ ∧ P u₂ t₂) c
      (fun t₁ t₂ => ∃ u₁ u₂, Rel u₁ u₂ ∧ Q u₁ t₁ ∧ Q u₂ t₂) := by
  refine (VG.RelCT.exists_ (P := fun (x : α × α) t₁ t₂ => Rel x.1 x.2 ∧ P x.1 t₁ ∧ P x.2 t₂)
    fun ⟨u₁, u₂⟩ => ?_).mono (fun t₁ t₂ ⟨u₁, u₂, r, h₁, h₂⟩ => ⟨⟨u₁, u₂⟩, r, h₁, h₂⟩) fun _ _ h => h
  rcases Classical.em (Rel u₁ u₂) with hr | hr
  · exact (VG.RelCT.wp (F₁ := Q u₁) (F₂ := Q u₂)
      (hrel.mono (fun t₁ t₂ h => ⟨u₁, u₂, h⟩) fun _ _ h => h)
      fun t₁ t₂ h => ⟨hw u₁ t₁ h.2.1, hw u₂ t₂ h.2.2⟩).mono (fun _ _ h => h)
      fun _ _ ⟨_, q₁, q₂⟩ => ⟨u₁, u₂, hr, q₁, q₂⟩
  · exact VG.RelCT.of_false fun _ _ h => hr h.1

/-! ## The frame -/

/-- The frame of the checks, from the state `u` they start from: `Stg` without the values. -/
structure Fm (G : Geo) (u t : State) : Prop where
  ws : VG.Proof.Rsa.X86.KeyRt.RtWs G.L t G.B G.Z G.len nArr
  keep : Keep G.B G.w (List.range nArr) bodySlots u.mem t.mem
  rest : Keeps bodyRegs u t
  mask : slot t.mem G.B sMask ≤ 1

theorem Stg.fm {G : Geo} {u t : State} {A : Nat → Nat} {live : List Nat} {c : Bool} (h : Stg G u A live c t) :
    Fm G u t := ⟨h.ws, h.keep, h.rest, bit_le h.mask⟩

theorem Fm.next {G : Geo} {u s t : State} (h : Fm G u s) {js ds : List Nat} {rs : List Reg}
    (hw : VG.Proof.Rsa.X86.KeyRt.RtWs G.L t G.B G.Z G.len nArr)
    (k : Keep G.B G.w js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < nArr) (hds : ∀ d ∈ ds, d ∈ bodySlots)
    (r : Keeps rs s t) (hrs : ∀ x ∈ rs, x ∈ bodyRegs) (mk : slot t.mem G.B sMask ≤ 1) : Fm G u t :=
  ⟨hw, h.keep.trans (k.mono (fun j hj => List.mem_range.2 (hjs j hj)) hds), h.rest.trans (r.mono hrs), mk⟩

theorem Fm.mask_keep {G : Geo} {u s : State} (h : Fm G u s) {js ds : List Nat} {m' : Mem}
    (k : Keep G.B G.w js ds s.mem m') (hd : ∀ d ∈ ds, sMask + 4 ≤ d ∨ d + 4 ≤ sMask) :
    slot m' G.B sMask ≤ 1 := by
  rw [k.slot (by decide) hd]; exact h.mask

/-- A run's frame from its start. -/
theorem Fm.run {g : CallGeometry} {sp : BitVec 32} {u t : State} (h : Fm (geometry g) u t) (r : Run g sp u) :
    Run g sp t :=
  r.frame h.rest (by decide) (by decide)
    (VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws.ws h.keep (fun j hj => List.mem_range.mp hj) (by decide))

/-! ## The frame through the pieces of the word steps -/

theorem fm_ltA {G : Geo} {u t : State} (h : Fm G u t) {a b : Nat} (ha : a < nArr) (hb : b < nArr) :
    WP isa (seqs (ltA G.full a b)) t (Fm G u) := by
  rw [ltA, wp_seqs_cons (by simp)]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.sub3_ok h.ws (o := aW) (a := a) (b := b) (by decide) ha hb)
    fun t1 ⟨h1, k1, _, b1, r1⟩ => ?_
  have f1 := h.next h1 k1 (by decide) (by simp) r1 subRegs_body (h.mask_keep k1 (by simp))
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.storeSlot_ok h1 (d := sF) (by decide) .ebx) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  have f2 := f1.next h2 k2 (by simp) (by decide) r2 (by simp) (f1.mask_keep k2 (by decide))
  show WP isa (.block acc) t2 _
  unfold acc
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.andS_ok h2 (d := sMask) (a := sMask) (b := sF) (by decide) (by decide)
    (by decide) f2.mask (by rw [e2]; exact b1)) fun t3 ⟨h3, k3, e3, r3⟩ =>
      f2.next h3 k3 (by simp) (by decide) r3 (by decide) (by rw [e3]; split <;> decide)

theorem fm_eqA {G : Geo} {u t : State} (h : Fm G u t) {a b : Nat} (ha : a < nArr) (hb : b < nArr)
    (haW : aW ≠ a) (hbW : aW ≠ b) :
    WP isa (seqs (eqA G.full a b)) t (Fm G u) := by
  rw [eqA, wp_seqs_cons (by simp)]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.eqS_ok h.ws (d := sF) (a := a) (b := b) (t := aW) (by decide) ha hb haW hbW
    (by decide)) fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  have f1 := h.next h1 k1 (by decide) (by decide) r1 opRegs_body (h.mask_keep k1 (by decide))
  show WP isa (.block acc) t1 _
  unfold acc
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.andS_ok h1 (d := sMask) (a := sMask) (b := sF) (by decide) (by decide)
    (by decide) f1.mask (by rw [e1]; split <;> decide)) fun t3 ⟨h3, k3, e3, r3⟩ =>
      f1.next h3 k3 (by simp) (by decide) r3 (by decide) (by rw [e3]; split <;> decide)

theorem fm_mulShort {G : Geo} {u t : State} (h : Fm G u t) {o a b : Nat} (hw2 : 2 ≤ G.w) (ho : o + 1 < nArr)
    (ha : a < nArr) (hb : b < nArr) (hao : a ≠ o) (hao1 : a ≠ o + 1) (hbo : b ≠ o) (hbo1 : b ≠ o + 1) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulShort G.L o a b) t (Fm G u) :=
  WP.mono (VG.Proof.Rsa.X86.WordRt.mulShort_ok h.ws hw2 ho ha hb hao hao1 hbo hbo1) fun _ ⟨h1, k1, _, r1⟩ =>
    h.next h1 k1 (by simp; omega) (by decide) r1 wordRegs_body (h.mask_keep k1 (by decide))

theorem fm_mulWide {G : Geo} {u t : State} (h : Fm G u t) {o a b : Nat} (ho : o + 1 < nArr)
    (ha : a < nArr) (hb : b < nArr) (hao : a ≠ o) (hao1 : a ≠ o + 1) (hbo : b ≠ o) (hbo1 : b ≠ o + 1) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulWide G.L o a b) t (Fm G u) :=
  WP.mono (VG.Proof.Rsa.X86.WordRt.mulWide_ok h.ws ho ha hb hao hao1 hbo hbo1) fun _ ⟨h1, k1, _, r1⟩ =>
    h.next h1 k1 (by simp; omega) (by decide) r1 wordRegs_body (h.mask_keep k1 (by decide))

theorem fm_wordMod {G : Geo} {u t : State} (h : Fm G u t) {x r m a : Nat} {wide : Bool}
    (hm : MLen t G.B G.Z (pLenArg G.full) a) (h4 : 4 ≤ wq a) (hw : wq a ≤ G.w)
    (hx : x + wide.toNat < nArr) (hr : r < nArr) (hmN : m < nArr)
    (hrT : r ≠ aT) (hmT : m ≠ aT) (hrm : r ≠ m) (hxr : r ≠ x) (hxt : aT ≠ x) (hxm : m ≠ x)
    (hxr1 : wide = true → r ≠ x + 1) (hxt1 : wide = true → aT ≠ x + 1) (hxm1 : wide = true → m ≠ x + 1) :
    WP isa (wordMod G.full x r m wide) t (Fm G u) :=
  WP.mono (VG.Proof.Rsa.X86.WordRt.wordMod_ok h.ws hm hx hr hmN (by decide) hrT hmT hrm hxr hxt hxm hxr1 hxt1 hxm1
    h4 hw) fun _ ⟨h1, k1, _, _, _, r1⟩ =>
    h.next h1 k1 (by
      intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl
      · exact hmN
      · exact hr
      · decide) (by decide) r1 wordRegs_body (h.mask_keep k1 (by decide))

/-! ## The word steps' relation -/

/-- A run in the word steps: from its start `u`, with `p`'s length `a` that the guard admits. -/
def WIn (g : CallGeometry) (sp : BitVec 32) (a : Nat) (u t : State) : Prop :=
  Run g sp u ∧ Fm (geometry g) u t ∧ MLen u g.base g.size (pLenArg g.full) a ∧ 4 ≤ wq a ∧
    wq a + 2 ≤ (geometry g).w

/-- Both runs in the word steps. -/
def WR (g : CallGeometry) (sp : BitVec 32) (a : Nat) (t₁ t₂ : State) : Prop :=
  ∃ u₁ u₂, True ∧ WIn g sp a u₁ t₁ ∧ WIn g sp a u₂ t₂

theorem WIn.run {g : CallGeometry} {sp : BitVec 32} {a : Nat} {u t : State} (h : WIn g sp a u t) : Run g sp t :=
  h.2.1.run h.1

theorem WIn.mlen {g : CallGeometry} {sp : BitVec 32} {a : Nat} {u t : State} (h : WIn g sp a u t) :
    MLen t g.base g.size (pLenArg g.full) a :=
  h.2.2.1.keep h.2.1.rest (by decide)
    (VG.Proof.Rsa.X86.KeyRt.keep_outside h.2.1.ws.ws h.2.1.keep (fun j hj => List.mem_range.mp hj) (by decide))

theorem τV_regs (full : Bool) : ∀ r ∈ [Reg.edi, .esp], (τV full).regs.mem r = true := by
  intro r hr
  change r ∈ RegSet.ofList [Reg.edi, .esp]
  simpa only [RegSet.mem_ofList] using hr

/-- A piece the taint analysis checks. -/
theorem wTaint {g : CallGeometry} {sp : BitVec 32} {a : Nat} {c : Prog isa}
    (hc : ∃ hint, (VG.Taint.check sseTaint (τV g.full) c hint).isSome = true)
    (hf : ∀ u t, Fm (geometry g) u t → WP isa c t (Fm (geometry g) u)) :
    RelCT isa (WR g sp a) c (WR g sp a) := by
  obtain ⟨_, hc⟩ := hc
  exact relLift (Rel := fun _ _ => True) (P := WIn g sp a)
    (VG.RelCT.taint (A := sseTaint) (τV g.full) (fun t₁ t₂ ⟨_, _, _, h₁, h₂⟩ => h₁.run.agree h₂.run) hc)
    fun u t h => WP.mono (hf u t h.2.1) fun t' f => ⟨h.1, f, h.2.2⟩

/-- The taint checks of `mulRows` for `o`, `a`, `b`. -/
structure RowsCk (full : Bool) (o a b : Nat) (rows : Option Nat) : Prop where
  c₀ : ∃ hint, (VG.Taint.check sseTaint (τV full) (.seq (.seq (VG.Impl.Rsa.X86.KeyRt.zeroWide (lay full) o)
    (VG.Impl.Rsa.X86.KeyRt.zeroWide (lay full) (o + 1)))
    (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc VG.Impl.Rsa.X86.WordModRt.oJ) .eax])) hint).isSome = true
  c₁ : ∃ hint, (VG.Taint.check sseTaint (τV full) (.block (VG.Proof.Rsa.X86.WordRt.rowHead (lay full) b)) hint).isSome = true
  c₂ : ∃ hint, (VG.Taint.check sseTaint { τV full with regs := .ofList [.edi, .esp, .eax, .ebx] }
    (.seq (.block (VG.Proof.Rsa.X86.WordRt.rowH₂ (lay full) o a)) (VG.Proof.Rsa.X86.WordRt.rowTail (lay full) o a b rows))
    hint).isSome = true

/-- The taint checks of `wordMod` for `x`, `r`, `m`. -/
structure ModCk (full : Bool) (x r m : Nat) (wide : Bool) : Prop where
  c₀ : ∃ hint, (VG.Taint.check sseTaint (τV full) (.seq (.seq (.block (VG.Impl.Rsa.X86.WordModRt.orTop (lay full) (pLenArg full) m))
      (VG.Impl.Rsa.X86.WordModRt.recip (lay full))) (VG.Impl.Rsa.X86.WordModRt.seed (lay full) (pLenArg full) x r wide))
    hint).isSome = true
  c₁ : ∃ hint, (VG.Taint.check sseTaint (τV full) (.block (VG.Proof.Rsa.X86.WordRt.digitHead (lay full) x)) hint).isSome = true
  c₂ : ∃ hint, (VG.Taint.check sseTaint { τV full with regs := .ofList [.edi, .esp, .eax, .ebx] }
    (.seq (.block VG.Proof.Rsa.X86.WordRt.digitH₂) (VG.Proof.Rsa.X86.WordRt.digitTail (lay full) (pLenArg full) x r m aT))
    hint).isSome = true

theorem wMulShort {g : CallGeometry} {sp : BitVec 32} {a : Nat} {o x b : Nat} (ck : RowsCk g.full o x b (some 2))
    (ho : o + 1 < nArr) (hx : x < nArr) (hb : b < nArr) (hxo : x ≠ o) (hxo1 : x ≠ o + 1) (hbo : b ≠ o)
    (hbo1 : b ≠ o + 1) :
    RelCT isa (WR g sp a) (VG.Impl.Rsa.X86.WordModRt.mulShort (lay g.full) o x b) (WR g sp a) := by
  refine relLift (Rel := fun _ _ => True) (P := WIn g sp a) ?_ fun u t h =>
    WP.mono (fm_mulShort h.2.1 (by have := h.2.2.2.2; omega) ho hx hb hxo hxo1 hbo hbo1) fun t' f => ⟨h.1, f, h.2.2⟩
  have w2 : ∀ {u t : State}, WIn g sp a u t → 2 ≤ VG.Proof.Rsa.X86.KeyRt.kw (g.args 1).toNat := fun h => by
    have := h.2.2.2.2; have := h.2.2.2.1; simp only [geometry, Geo.w] at *; omega
  refine fun t₁ t₂ t₁' t₂' s₁ s₂ hp e₁ e₂ => ?_
  obtain ⟨_, _, _, h₁, h₂⟩ := hp
  exact VG.Proof.Rsa.X86.WordRt.mulRows_relCT (τ := τV g.full) (Fr := Run g sp) (B := g.base) (Z := g.size)
    (fun _ _ a b => a.agree b) (fun f K d e O => f.frame K d e O) (τV_regs g.full)
    (rows := some 2) (by show 1 ≤ 2; decide) (by show 2 ≤ _; exact w2 h₁) (fun k hk => by cases hk; decide)
    ho hx hb hxo hxo1 hbo hbo1 ck.c₀ ck.c₁ ck.c₂
    _ _ _ _ _ _ ⟨⟨h₁.2.1.ws, h₁.run⟩, ⟨h₂.2.1.ws, h₂.run⟩⟩ e₁ e₂

theorem wMulWide {g : CallGeometry} {sp : BitVec 32} {a : Nat} {o x b : Nat} (ck : RowsCk g.full o x b none)
    (ho : o + 1 < nArr) (hx : x < nArr) (hb : b < nArr) (hxo : x ≠ o) (hxo1 : x ≠ o + 1) (hbo : b ≠ o)
    (hbo1 : b ≠ o + 1) :
    RelCT isa (WR g sp a) (VG.Impl.Rsa.X86.WordModRt.mulWide (lay g.full) o x b) (WR g sp a) := by
  refine relLift (Rel := fun _ _ => True) (P := WIn g sp a) ?_ fun u t h =>
    WP.mono (fm_mulWide h.2.1 ho hx hb hxo hxo1 hbo hbo1) fun t' f => ⟨h.1, f, h.2.2⟩
  refine fun t₁ t₂ t₁' t₂' s₁ s₂ hp e₁ e₂ => ?_
  obtain ⟨_, _, _, h₁, h₂⟩ := hp
  exact VG.Proof.Rsa.X86.WordRt.mulRows_relCT (τ := τV g.full) (Fr := Run g sp) (B := g.base) (Z := g.size)
    (fun _ _ a b => a.agree b) (fun f K d e O => f.frame K d e O) (τV_regs g.full)
    (rows := none) (by show 1 ≤ VG.Proof.Rsa.X86.KeyRt.kw _; exact h₁.2.1.ws.kw_pos) (Nat.le_refl _)
    (fun k hk => by cases hk) ho hx hb hxo hxo1 hbo hbo1 ck.c₀ ck.c₁ ck.c₂
    _ _ _ _ _ _ ⟨⟨h₁.2.1.ws, h₁.run⟩, ⟨h₂.2.1.ws, h₂.run⟩⟩ e₁ e₂

theorem wWordMod {g : CallGeometry} {sp : BitVec 32} {a : Nat} {x r m : Nat} {wide : Bool}
    (ck : ModCk g.full x r m wide)
    (hx : x + wide.toNat < nArr) (hr : r < nArr) (hmN : m < nArr)
    (hrT : r ≠ aT) (hmT : m ≠ aT) (hrm : r ≠ m) (hxr : r ≠ x) (hxt : aT ≠ x) (hxm : m ≠ x)
    (hxr1 : wide = true → r ≠ x + 1) (hxt1 : wide = true → aT ≠ x + 1) (hxm1 : wide = true → m ≠ x + 1) :
    RelCT isa (WR g sp a) (wordMod g.full x r m wide) (WR g sp a) := by
  refine relLift (Rel := fun _ _ => True) (P := WIn g sp a) ?_ fun u t h =>
    WP.mono (fm_wordMod h.2.1 h.mlen h.2.2.2.1 (by have := h.2.2.2.2; simp only [Geo.w] at this ⊢; omega) hx hr hmN hrT hmT hrm hxr hxt hxm
      hxr1 hxt1 hxm1) fun t' f => ⟨h.1, f, h.2.2⟩
  refine fun t₁ t₂ t₁' t₂' s₁ s₂ hp e₁ e₂ => ?_
  obtain ⟨_, _, _, h₁, h₂⟩ := hp
  exact VG.Proof.Rsa.X86.WordRt.wordMod_relCT (τ := τV g.full) (Fr := Run g sp) (B := g.base) (Z := g.size)
    (fun _ _ a b => a.agree b) (fun f K d e O => f.frame K d e O) (τV_regs g.full)
    hx hr hmN (by decide) hrT hmT hrm hxr hxt hxm hxr1 hxt1 hxm1 h₁.2.2.2.1
    (by have := h₁.2.2.2.2; simp only [geometry, Geo.w] at this ⊢; omega)
    ck.c₀ ck.c₁ ck.c₂ _ _ _ _ _ _ ⟨⟨h₁.2.1.ws, h₁.run, h₁.mlen⟩, ⟨h₂.2.1.ws, h₂.run, h₂.mlen⟩⟩ e₁ e₂

end VG.Proof.Rsa.X86.KeyCheck
