module

public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Mul
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Loop
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega

/-! # The word steps' traces: loops counted in the header

The taint analysis takes every word of the working space secret, so it
cannot follow a count kept in a header word, as `mulRows` keeps its row
(`oJ`). The runs are related instead (`relCT_counted`): each iteration of
both runs starts from the same count, its body leaks the same trace (the
count, loaded into a register, is the same in both runs: `relCT_head`), and
its last comparison is the same. What the taint analysis needs public in
both runs (`edi`, `esp`, the arguments) comes from a predicate `Fr` of each
run that a frame keeps.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.WordRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Keep arr num S slot)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw arrPtr_ok lenSrc)
open VG.Impl.Rsa.X86.WordModRt (oJ)

/-! ## Relating runs -/

/-- A block, split in front of a sequence. -/
theorem RelCT.seqBlock_append {P Q : State → State → Prop} {l₁ l₂ : List Instr} {c : Prog isa}
    (h : RelCT isa P (.seq (.block l₁) (.seq (.block l₂) c)) Q) : RelCT isa P (.seq (.block (l₁ ++ l₂)) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ c₁ =>
    cases e₂ with
    | seq a₂ c₂ =>
      rw [Exec.block_iff, execBlock_append] at a₁ a₂
      obtain ⟨⟨x₁, u₁⟩, hx₁, hy₁⟩ := Option.bind_eq_some_iff.mp a₁
      obtain ⟨⟨y₁, w₁⟩, hz₁, he₁⟩ := Option.map_eq_some_iff.mp hy₁
      obtain ⟨⟨x₂, u₂⟩, hx₂, hy₂⟩ := Option.bind_eq_some_iff.mp a₂
      obtain ⟨⟨y₂, w₂⟩, hz₂, he₂⟩ := Option.map_eq_some_iff.mp hy₂
      simp only [Prod.mk.injEq] at he₁ he₂
      obtain ⟨rfl, rfl⟩ := he₁
      obtain ⟨rfl, rfl⟩ := he₂
      obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.block hx₁) (.seq (.block hz₁) c₁))
        (.seq (.block hx₂) (.seq (.block hz₂) c₂))
      simp only [List.append_assoc] at ht ⊢
      exact ⟨ht, hq⟩

/-- `τ` with the registers `R` public instead. -/
theorem agree_regs' {τ : VG.X86.Taint.T} {R : RegSet Reg} {s₁ s₂ : State} (h : VG.X86.Taint.Agree τ s₁ s₂)
    (hr : ∀ r ∈ R, s₁.gpr r = s₂.gpr r) : VG.X86.Taint.Agree { τ with regs := R } s₁ s₂ :=
  have wf : ∀ {s : State}, VG.X86.Taint.Wf τ s → VG.X86.Taint.Wf { τ with regs := R } s := fun w =>
    ⟨w.lens, w.bases, w.wbases, w.args, w.argBases, w.stk, w.frames, w.room⟩
  ⟨⟨hr, h.rf.2⟩, h.wr, wf h.wf₁, wf h.wf₂, h.ok, h.slots, h.sp, h.argMem⟩

/-- A loop of `N` iterations, the `n`-th of each run from `Inv p n` for its own `p`: its body
leaks the same trace from the same `n`, and its last comparison says whether it was the last. -/
theorem relCT_counted {α : Type} {body : Prog isa} (Inv : α → Nat → State → Prop) (N : Nat)
    (hb : ∀ n, n < N → RelCT isa (fun t₁ t₂ => ∃ p₁ p₂, Inv p₁ n t₁ ∧ Inv p₂ n t₂) body fun _ _ => True)
    (hw : ∀ p n t, n < N → Inv p n t →
      WP isa body t fun t' => t'.zf = some (decide (n + 1 = N)) ∧ (n + 1 < N → Inv p (n + 1) t'))
    {n : Nat} (hn : n < N) :
    RelCT isa (fun t₁ t₂ => ∃ p₁ p₂, Inv p₁ n t₁ ∧ Inv p₂ n t₂) (.loop body .ne) fun _ _ => True := by
  refine (VG.RelCT.loop (M := isa) (fun k t₁ t₂ => ∃ n, n + k = N ∧ n < N ∧ ∃ p₁ p₂, Inv p₁ n t₁ ∧ Inv p₂ n t₂)
    ?_ (N - n)).mono (fun t₁ t₂ ⟨p₁, p₂, h₁, h₂⟩ => ⟨n, by omega, hn, p₁, p₂, h₁, h₂⟩) fun _ _ h => h
  intro k
  refine (VG.RelCT.exists_ (P := fun (x : Nat × α × α) t₁ t₂ => x.1 + k = N ∧ x.1 < N ∧
    Inv x.2.1 x.1 t₁ ∧ Inv x.2.2 x.1 t₂) fun ⟨m, p₁, p₂⟩ => ?_).mono
    (fun t₁ t₂ ⟨m, e, hm, p₁, p₂, h₁, h₂⟩ => ⟨⟨m, p₁, p₂⟩, e, hm, h₁, h₂⟩) fun _ _ h => h
  by_cases hk : m + k = N ∧ m < N
  swap
  · exact VG.RelCT.of_false fun _ _ h => hk ⟨h.1, h.2.1⟩
  refine ((VG.RelCT.wp ((hb m hk.2).mono (fun t₁ t₂ h => ⟨p₁, p₂, h.2.2.1, h.2.2.2⟩) fun _ _ h => h)
    (fun t₁ t₂ h => ⟨hw p₁ m t₁ h.2.1 h.2.2.1, hw p₂ m t₂ h.2.1 h.2.2.2⟩)).mono (fun _ _ h => h)) ?_
  rintro t₁ t₂ ⟨-, ⟨z₁, i₁⟩, ⟨z₂, i₂⟩⟩
  have e₁ : isa.eval .ne t₁ = some (!decide (m + 1 = N)) := by
    change t₁.zf.map (!·) = _; rw [z₁]; rfl
  have e₂ : isa.eval .ne t₂ = some (!decide (m + 1 = N)) := by
    change t₂.zf.map (!·) = _; rw [z₂]; rfl
  refine ⟨e₁.trans e₂.symm, fun _ => trivial, fun et => ?_⟩
  rw [e₁] at et
  have hlt : m + 1 < N := by
    by_cases h : m + 1 = N
    · simp [h] at et
    · omega
  exact ⟨k - 1, by omega, m + 1, by omega, hlt, p₁, p₂, i₁ hlt, i₂ hlt⟩

/-- A block whose first part `l₁` loads what makes the registers of `τ'` agree: `l₁` checked
from `τ`, the rest from `τ'`. -/
theorem relCT_head {α : Type} {J : α → State → Prop} {l₁ l₂ : List Instr} {c : Prog isa}
    {τ τ' : VG.X86.Taint.T} {G : α → State → Prop}
    (hag : ∀ p₁ p₂ t₁ t₂, J p₁ t₁ → J p₂ t₂ → VG.X86.Taint.Agree τ t₁ t₂)
    (c₁ : ∃ hint, (VG.Taint.check sseTaint τ (.block l₁) hint).isSome = true)
    (hw : ∀ p t, J p t → WP isa (.block l₁) t (G p))
    (hag' : ∀ p₁ p₂ m₁ m₂, G p₁ m₁ → G p₂ m₂ → VG.X86.Taint.Agree τ' m₁ m₂)
    (c₂ : ∃ hint, (VG.Taint.check sseTaint τ' (.seq (.block l₂) c) hint).isSome = true) :
    RelCT isa (fun t₁ t₂ => ∃ p₁ p₂, J p₁ t₁ ∧ J p₂ t₂) (.seq (.block (l₁ ++ l₂)) c) fun _ _ => True := by
  obtain ⟨_, c₁⟩ := c₁
  obtain ⟨_, c₂⟩ := c₂
  refine RelCT.seqBlock_append (VG.RelCT.seq (R := fun m₁ m₂ => VG.X86.Taint.Agree τ' m₁ m₂) ?_
    (VG.RelCT.taint (A := sseTaint) τ' (fun _ _ h => by exact h) c₂))
  refine (VG.RelCT.exists_ (P := fun (x : α × α) t₁ t₂ => J x.1 t₁ ∧ J x.2 t₂) fun ⟨p₁, p₂⟩ => ?_).mono
    (fun t₁ t₂ ⟨p₁, p₂, h₁, h₂⟩ => ⟨⟨p₁, p₂⟩, h₁, h₂⟩) fun _ _ h => h
  exact (VG.RelCT.wp (F₁ := G p₁) (F₂ := G p₂)
    (VG.RelCT.taint (A := sseTaint) τ (fun t₁ t₂ h => hag p₁ p₂ t₁ t₂ h.1 h.2) c₁)
    (fun t₁ t₂ h => ⟨hw p₁ t₁ h.1, hw p₂ t₂ h.2⟩)).mono (fun _ _ h => h)
    fun m₁ m₂ ⟨_, g₁, g₂⟩ => hag' p₁ p₂ m₁ m₂ g₁ g₂

/-! ## Sequences -/

theorem exec_seqs_append {l₁ l₂ : List (Prog isa)} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) {s s' : State} {tr : List Leak}
    (e : Exec isa (VG.Impl.Rsa.X86.Keys.seqs (l₁ ++ l₂)) s tr s') : Exec isa (.seq (VG.Impl.Rsa.X86.Keys.seqs l₁) (VG.Impl.Rsa.X86.Keys.seqs l₂)) s tr s' := by
  induction l₁ generalizing s tr with
  | nil => exact absurd rfl h₁
  | cons c l ih =>
    rcases l with _ | ⟨d, l⟩
    · match l₂, h₂ with
      | _ :: _, _ => exact e
    · rw [List.cons_append] at e
      change Exec isa (.seq c (VG.Impl.Rsa.X86.Keys.seqs ((d :: l) ++ l₂))) s tr s' at e
      cases e with
      | seq e₁ e₂ =>
        cases ih (by simp) e₂ with
        | seq a b =>
          rw [← List.append_assoc]
          exact .seq (.seq e₁ a) b

theorem RelCT.seqs_append {P Q : State → State → Prop} {l₁ l₂ : List (Prog isa)} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ [])
    (h : RelCT isa P (.seq (VG.Impl.Rsa.X86.Keys.seqs l₁) (VG.Impl.Rsa.X86.Keys.seqs l₂)) Q) : RelCT isa P (VG.Impl.Rsa.X86.Keys.seqs (l₁ ++ l₂)) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (exec_seqs_append h₁ h₂ e₁) (exec_seqs_append h₁ h₂ e₂)

theorem RelCT.seqs_cons {P R Q : State → State → Prop} {c : Prog isa} {l : List (Prog isa)} (hl : l ≠ [])
    (h₁ : RelCT isa P c R) (h₂ : RelCT isa R (VG.Impl.Rsa.X86.Keys.seqs l) Q) : RelCT isa P (VG.Impl.Rsa.X86.Keys.seqs (c :: l)) Q := by
  match l, hl with
  | _ :: _, _ => exact VG.RelCT.seq h₁ h₂

/-- The same relation through every element of a sequence. -/
theorem RelCT.seqs_all {P : State → State → Prop} :
    ∀ {l : List (Prog isa)}, l ≠ [] → (∀ c ∈ l, RelCT isa P c P) → RelCT isa P (VG.Impl.Rsa.X86.Keys.seqs l) P
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

/-! ## `mulRows` -/

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- A row's first part: `ebx` at `[b]`, the row's count in `eax`. -/
def rowHead (L : Lay) (b : Nat) : List Instr := arrPtr L .ebx b .edx ++ [.mov .eax (.mem (sc oJ))]

/-- The rest of a row's first block. -/
def rowH₂ (L : Lay) (o a : Nat) (half : Bool := false) : List Instr :=
  [.alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .ebx (.reg .eax),
    .mov .ecx (.mem (at_ .ebx 0))] ++ arrPtr L .ebp o .edx ++ [.alu .add .ebp (.reg .eax)] ++
    arrPtr L .esi a .edx ++ bytesB L .edi ++ (if half then [.shift .shr .edi 1] else []) ++ [.mov .ebx (.imm 0)]

/-- A row after its first block. -/
def rowTail (L : Lay) (o a b : Nat) (rows : Option Nat) (half : Bool := false) : Prog isa :=
  match VG.Impl.Rsa.X86.WordModRt.mulRow L o a b rows half with
  | .seq _ x => x
  | _ => .block []

theorem mulRow_eq (L : Lay) (o a b : Nat) (rows : Option Nat) (half : Bool) :
    VG.Impl.Rsa.X86.WordModRt.mulRow L o a b rows half =
      .seq (.block (rowHead L b ++ rowH₂ L o a half)) (rowTail L o a b rows half) := by
  simp only [rowTail, rowHead, rowH₂, VG.Impl.Rsa.X86.WordModRt.mulRow, VG.Impl.Rsa.X86.WordModRt.seqs,
    List.append_assoc, List.cons_append, List.nil_append]

/-- `ebx` at `[b]`, header word `d` in `eax`. -/
theorem loadHead_ok {t : State} (h : RtWs L t B Z len N) {b d j : Nat} (hb : b < N) (hd : d + 4 ≤ 160)
    (hj : slot t.mem B d = j) :
    WP isa (.block (arrPtr L .ebx b .edx ++ ([.mov .eax (.mem (sc d))] : List Instr))) t fun m => Keeps [.ebx, .edx, .eax] t m ∧
      m.mem = t.mem ∧ PtrAt m B .ebx (arr (kw len) b) ∧ (m.gpr .eax).toNat = j := by
  have nw := h.ws.workspace.nowrap
  have fb := h.ws.arr_fit hb
  have hdr := h.ws.hdr_le
  simp only [S] at fb
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hdr
  refine arrPtr_ok (lenSrc h) h.lenLe h.edi (r := .ebx) (t := .edx) (j := b) (by decide) (by decide)
    (by omega) fun u₁ K₁ m₁ p₁ _ => ?_
  have h₁ := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine wp_movS (readSrc_sc h₁.ws.workspace (d := d) (by omega)) fun m U _ => WP.block_nil ?_
  refine ⟨(K₁.mono (by decide)).trans (U.keeps.mono (by decide)), by rw [U.mem, m₁], ?_, ?_⟩
  · rw [PtrAt, U.other .ebx (by decide)]; exact p₁
  · rw [U.gpr, m₁]; exact hj

theorem rowHead_ok {t : State} (h : RtWs L t B Z len N) {b j : Nat} (hb : b < N) (hj : slot t.mem B oJ = j) :
    WP isa (.block (rowHead L b)) t fun m => Keeps [.ebx, .edx, .eax] t m ∧ m.mem = t.mem ∧
      PtrAt m B .ebx (arr (kw len) b) ∧ (m.gpr .eax).toNat = j :=
  loadHead_ok h hb (by decide) hj

/-- Two pointers into the same working space at the same offset agree. -/
theorem ptr_eq {s₁ s₂ : State} {r : Reg} {x : Nat} (h₁ : PtrAt s₁ B r x) (h₂ : PtrAt s₂ B r x) :
    s₁.gpr r = s₂.gpr r := BitVec.eq_of_toNat_eq (h₁.trans h₂.symm)

/-- The rows' traces from `init`, which starts them: the same from states in the same working space. -/
theorem rowsFrom_relCT {τ : VG.X86.Taint.T} {Fr : State → Prop}
    (hA : ∀ t₁ t₂, Fr t₁ → Fr t₂ → VG.X86.Taint.Agree τ t₁ t₂)
    (hF : ∀ {u t : State} {rs : List Reg}, Fr u → Keeps rs u t → .edi ∉ rs → .esp ∉ rs →
      Outside B 0 Z u.mem t.mem → Fr t)
    (hτ : ∀ r ∈ [Reg.edi, .esp], τ.regs.mem r = true)
    {o a b : Nat} {rows : Option Nat} {half : Bool} {init : Prog isa}
    (hInit : ∀ t, RtWs L t B Z len N → WP isa init t (RowsI L t B Z len N o a b 0 half))
    (hR1 : 1 ≤ rowsN len rows half) (hRw : rowsN len rows half ≤ kw len) (hRk : ∀ k, rows = some k → k < 2 ^ 32)
    (ho : o + 1 < N) (ha : a < N) (hb : b < N) (hao : a ≠ o) (hao1 : a ≠ o + 1) (hbo : b ≠ o)
    (hbo1 : b ≠ o + 1)
    (c₀ : ∃ hint, (VG.Taint.check sseTaint τ init hint).isSome = true)
    (c₁ : ∃ hint, (VG.Taint.check sseTaint τ (.block (rowHead L b)) hint).isSome = true)
    (c₂ : ∃ hint, (VG.Taint.check sseTaint { τ with regs := .ofList [.edi, .esp, .eax, .ebx] }
      (.seq (.block (rowH₂ L o a half)) (rowTail L o a b rows half)) hint).isSome = true) :
    RelCT isa (fun t₁ t₂ => (RtWs L t₁ B Z len N ∧ Fr t₁) ∧ (RtWs L t₂ B Z len N ∧ Fr t₂))
      (.seq init (.loop (VG.Impl.Rsa.X86.WordModRt.mulRow L o a b rows half) .ne)) fun _ _ => True := by
  -- The invariant of each run, from its own start.
  let Inv : State → Nat → State → Prop := fun p j t =>
    (RtWs L p B Z len N ∧ Fr p) ∧ RowsI L p B Z len N o a b j half t
  have frAt : ∀ {p j t}, Inv p j t → Fr t := fun {p j t} ⟨⟨_, fp⟩, I⟩ =>
    hF fp I.rest (by decide) (by decide)
      (VG.Proof.Rsa.X86.KeyRt.keep_outside I.ws.ws I.keep (by simp; omega) (by decide))
  refine VG.RelCT.seq (R := fun t₁ t₂ => ∃ p₁ p₂, Inv p₁ 0 t₁ ∧ Inv p₂ 0 t₂) ?_
    (relCT_counted Inv (rowsN len rows half) (fun j hj => ?_) (fun p j t hj ⟨P, I⟩ => ?_) (n := 0) (by omega))
  · -- The rows' start, by the taint analysis.
    obtain ⟨_, c₀⟩ := c₀
    have init : ∀ t, RtWs L t B Z len N → Fr t → WP isa init t (fun u => Inv t 0 u) := fun t ht ft =>
      WP.mono (hInit t ht) fun _ I => ⟨⟨ht, ft⟩, I⟩
    exact (VG.RelCT.wpDep (VG.RelCT.taint (A := sseTaint) τ (fun t₁ t₂ h => hA t₁ t₂ h.1.2 h.2.2) c₀)
      (F := fun p t => Inv p 0 t) fun t₁ t₂ h => ⟨init t₁ h.1.1 h.1.2, init t₂ h.2.1 h.2.2⟩).mono (fun _ _ h => h)
      fun _ _ ⟨_, σ₁, σ₂, _, g₁, g₂⟩ => ⟨σ₁, σ₂, g₁, g₂⟩
  · -- A row: its count in `eax` and `[b]` in `ebx` agree.
    rw [mulRow_eq _ _ _ _ _ half]
    refine relCT_head (J := fun p t => Inv p j t) (τ := τ) (τ' := { τ with regs := .ofList [.edi, .esp, .eax, .ebx] })
      (G := fun _ m => Fr m ∧ PtrAt m B .ebx (arr (kw len) b) ∧ (m.gpr .eax).toNat = j)
      (fun _ _ t₁ t₂ i₁ i₂ => hA t₁ t₂ (frAt i₁) (frAt i₂)) c₁
      (fun _ t i => WP.mono (rowHead_ok i.2.ws hb i.2.cnt) fun m ⟨K, mm, pb, ea⟩ =>
        ⟨hF (frAt i) K (by decide) (by decide) (by rw [mm]; exact Outside.refl _ _ _ _), pb, ea⟩)
      (fun _ _ m₁ m₂ ⟨f₁, b₁, e₁⟩ ⟨f₂, b₂, e₂⟩ => agree_regs' (hA m₁ m₂ f₁ f₂) fun r hr => ?_) c₂
    have G := hA m₁ m₂ f₁ f₂
    simp only [RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact G.rf.1 _ (hτ _ (by simp))
    · exact G.rf.1 _ (hτ _ (by simp))
    · exact BitVec.eq_of_toNat_eq (e₁.trans e₂.symm)
    · exact ptr_eq b₁ b₂
  · exact WP.mono (rowsStep_ok P.1 hRk hRw ho ha hb hao hao1 hbo hbo1 hj I) fun _ ⟨zv, I'⟩ => ⟨zv, fun _ => ⟨P, I'⟩⟩

/-- `mulRows`' traces: the same from states in the same working space. -/
theorem mulRows_relCT {τ : VG.X86.Taint.T} {Fr : State → Prop}
    (hA : ∀ t₁ t₂, Fr t₁ → Fr t₂ → VG.X86.Taint.Agree τ t₁ t₂)
    (hF : ∀ {u t : State} {rs : List Reg}, Fr u → Keeps rs u t → .edi ∉ rs → .esp ∉ rs →
      Outside B 0 Z u.mem t.mem → Fr t)
    (hτ : ∀ r ∈ [Reg.edi, .esp], τ.regs.mem r = true)
    {o a b : Nat} {rows : Option Nat}
    (hR1 : 1 ≤ rowsN len rows) (hRw : rowsN len rows ≤ kw len) (hRk : ∀ k, rows = some k → k < 2 ^ 32)
    (ho : o + 1 < N) (ha : a < N) (hb : b < N) (hao : a ≠ o) (hao1 : a ≠ o + 1) (hbo : b ≠ o)
    (hbo1 : b ≠ o + 1)
    (c₀ : ∃ hint, (VG.Taint.check sseTaint τ (.seq (.seq (zeroWide L o) (zeroWide L (o + 1)))
      (.block [.mov .eax (.imm 0), .store (sc oJ) .eax])) hint).isSome = true)
    (c₁ : ∃ hint, (VG.Taint.check sseTaint τ (.block (rowHead L b)) hint).isSome = true)
    (c₂ : ∃ hint, (VG.Taint.check sseTaint { τ with regs := .ofList [.edi, .esp, .eax, .ebx] }
      (.seq (.block (rowH₂ L o a)) (rowTail L o a b rows)) hint).isSome = true) :
    RelCT isa (fun t₁ t₂ => (RtWs L t₁ B Z len N ∧ Fr t₁) ∧ (RtWs L t₂ B Z len N ∧ Fr t₂))
      (VG.Impl.Rsa.X86.WordModRt.seqs [zeroWide L o, zeroWide L (o + 1),
        .block [.mov .eax (.imm 0), .store (sc oJ) .eax], .loop (VG.Impl.Rsa.X86.WordModRt.mulRow L o a b rows) .ne])
      fun _ _ => True := by
  simp only [VG.Impl.Rsa.X86.WordModRt.seqs]
  exact VG.RelCT.assoc (VG.RelCT.assoc (rowsFrom_relCT hA hF hτ (half := false)
    (fun t ht => WP.assoc' (by simpa only [VG.Impl.Rsa.X86.WordModRt.seqs] using rowsInit_ok ht (a := a) (b := b) ho))
    hR1 hRw hRk ho ha hb hao hao1 hbo hbo1 c₀ c₁ c₂))

/-- `mulHalf`'s traces: the same from states in the same working space. -/
theorem mulHalf_relCT {τ : VG.X86.Taint.T} {Fr : State → Prop}
    (hA : ∀ t₁ t₂, Fr t₁ → Fr t₂ → VG.X86.Taint.Agree τ t₁ t₂)
    (hF : ∀ {u t : State} {rs : List Reg}, Fr u → Keeps rs u t → .edi ∉ rs → .esp ∉ rs →
      Outside B 0 Z u.mem t.mem → Fr t)
    (hτ : ∀ r ∈ [Reg.edi, .esp], τ.regs.mem r = true)
    {o a b : Nat} (hw : 1 ≤ kw len)
    (ho : o + 1 < N) (ha : a < N) (hb : b < N) (hao : a ≠ o) (hao1 : a ≠ o + 1) (hbo : b ≠ o)
    (hbo1 : b ≠ o + 1)
    (c₀ : ∃ hint, (VG.Taint.check sseTaint τ (.seq (.seq (.seq (zeroWide L o) (zeroWide L (o + 1)))
      (.block (VG.Impl.Rsa.X86.WordModRt.topZero L o))) (.block [.mov .eax (.imm 0), .store (sc oJ) .eax]))
      hint).isSome = true)
    (c₁ : ∃ hint, (VG.Taint.check sseTaint τ (.block (rowHead L b)) hint).isSome = true)
    (c₂ : ∃ hint, (VG.Taint.check sseTaint { τ with regs := .ofList [.edi, .esp, .eax, .ebx] }
      (.seq (.block (rowH₂ L o a true)) (rowTail L o a b none true)) hint).isSome = true) :
    RelCT isa (fun t₁ t₂ => (RtWs L t₁ B Z len N ∧ Fr t₁) ∧ (RtWs L t₂ B Z len N ∧ Fr t₂))
      (VG.Impl.Rsa.X86.WordModRt.mulHalf L o a b) fun _ _ => True := by
  have kwe : kw len = 2 * Spec.Rsa.modulusWords len := rfl
  unfold VG.Impl.Rsa.X86.WordModRt.mulHalf
  simp only [VG.Impl.Rsa.X86.WordModRt.seqs]
  exact VG.RelCT.assoc (VG.RelCT.assoc (VG.RelCT.assoc (rowsFrom_relCT hA hF hτ (half := true) (rows := none)
    (fun t ht => WP.assoc' (WP.assoc'
      (by simpa only [VG.Impl.Rsa.X86.WordModRt.seqs] using halfInit_ok ht (a := a) (b := b) ho)))
    (by simp only [rowsN, rowW]; omega) (by simp only [rowsN, rowW]; omega) (by simp)
    ho ha hb hao hao1 hbo hbo1 c₀ c₁ c₂)))

/-! ## `wordMod` -/

open VG.Impl.Rsa.X86.WordModRt (oSteps oDig)

/-- A digit step's first part: `ebx` at `[x]`, the count in `eax`. -/
def digitHead (L : Lay) (x : Nat) : List Instr := arrPtr L .ebx x .edx ++ [.mov .eax (.mem (sc oSteps))]

/-- The rest of a digit step's first block. -/
def digitH₂ : List Instr :=
  [.alu .sub .eax (.imm 1), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .ebx (.reg .eax),
    .mov .eax (.mem (at_ .ebx 0)), .store (sc oDig) .eax]

/-- A digit step after its first block. -/
def digitTail (L : Lay) (ml x r m t : Nat) : Prog isa :=
  match VG.Impl.Rsa.X86.WordModRt.digitStep L ml x r m t with
  | .seq _ c => c
  | _ => .block []

theorem digitStep_eq (L : Lay) (ml x r m t : Nat) :
    VG.Impl.Rsa.X86.WordModRt.digitStep L ml x r m t =
      .seq (.block (digitHead L x ++ digitH₂)) (digitTail L ml x r m t) := by
  simp only [digitTail, digitHead, digitH₂, VG.Impl.Rsa.X86.WordModRt.digitStep, VG.Impl.Rsa.X86.WordModRt.seqs,
    List.append_assoc, List.cons_append, List.nil_append]

/-- `wordMod`'s traces: the same from states in the same working space, with the same divisor's
length. -/
theorem wordMod_relCT {τ : VG.X86.Taint.T} {Fr : State → Prop}
    (hA : ∀ t₁ t₂, Fr t₁ → Fr t₂ → VG.X86.Taint.Agree τ t₁ t₂)
    (hF : ∀ {u t : State} {rs : List Reg}, Fr u → Keeps rs u t → .edi ∉ rs → .esp ∉ rs →
      Outside B 0 Z u.mem t.mem → Fr t)
    (hτ : ∀ r ∈ [Reg.edi, .esp], τ.regs.mem r = true)
    {ml a x r m t : Nat} {wide : Bool}
    (hx : x + wide.toNat < N) (hr : r < N) (hmN : m < N) (ht : t < N)
    (hrt : r ≠ t) (hmt : m ≠ t) (hrm : r ≠ m) (hxr : r ≠ x) (hxt : t ≠ x) (hxm : m ≠ x)
    (hxr1 : wide = true → r ≠ x + 1) (hxt1 : wide = true → t ≠ x + 1) (hxm1 : wide = true → m ≠ x + 1)
    (h4 : 4 ≤ wq a) (hw : wq a ≤ kw len)
    (c₀ : ∃ hint, (VG.Taint.check sseTaint τ (.seq (.seq (.block (VG.Impl.Rsa.X86.WordModRt.orTop L ml m))
      (VG.Impl.Rsa.X86.WordModRt.recip L)) (VG.Impl.Rsa.X86.WordModRt.seed L ml x r wide)) hint).isSome = true)
    (c₁ : ∃ hint, (VG.Taint.check sseTaint τ (.block (digitHead L x)) hint).isSome = true)
    (c₂ : ∃ hint, (VG.Taint.check sseTaint { τ with regs := .ofList [.edi, .esp, .eax, .ebx] }
      (.seq (.block digitH₂) (digitTail L ml x r m t)) hint).isSome = true) :
    RelCT isa (fun t₁ t₂ => (RtWs L t₁ B Z len N ∧ Fr t₁ ∧ MLen t₁ B Z ml a) ∧
      (RtWs L t₂ B Z len N ∧ Fr t₂ ∧ MLen t₂ B Z ml a))
      (VG.Impl.Rsa.X86.WordModRt.wordMod L ml x r m t wide) fun _ _ => True := by
  let Sc := xw len wide - wq a + 1
  let Inv : State × Nat × Nat → Nat → State → Prop := fun p i u =>
    (Fr p.1 ∧ val32 p.1.mem B (arr (kw len) x) (xw len wide) = p.2.2 ∧
      val32 p.1.mem B (arr (kw len) m) (wq a) = p.2.1 ∧ StepHdr p.1.mem B p.2.1 (wq a)) ∧
    LoopI L p.1 B Z len N ml a r t p.2.1 p.2.2 Sc i u
  have frAt : ∀ {p i u}, Inv p i u → Fr u := fun {p i u} ⟨⟨fp, _⟩, I⟩ =>
    hF fp I.rest (by decide) (by decide)
      (VG.Proof.Rsa.X86.KeyRt.keep_outside I.ws.ws I.keep (by simp; omega) (by decide))
  unfold VG.Impl.Rsa.X86.WordModRt.wordMod
  simp only [VG.Impl.Rsa.X86.WordModRt.seqs]
  refine VG.RelCT.assoc (VG.RelCT.assoc (VG.RelCT.seq (R := fun t₁ t₂ => ∃ p₁ p₂, Inv p₁ 0 t₁ ∧ Inv p₂ 0 t₂) ?_
    ((relCT_counted Inv Sc (fun i hi => ?_) (fun p i u hi ⟨P, I⟩ => ?_) (n := 0) (by omega)))))
  · -- `orTop`, `recip` and `seed`, by the taint analysis.
    obtain ⟨_, c₀⟩ := c₀
    have pre : ∀ u, RtWs L u B Z len N → Fr u → MLen u B Z ml a →
        WP isa (.seq (.seq (.block (VG.Impl.Rsa.X86.WordModRt.orTop L ml m)) (VG.Impl.Rsa.X86.WordModRt.recip L))
          (VG.Impl.Rsa.X86.WordModRt.seed L ml x r wide)) u (fun v => ∃ p, Inv p 0 v) := fun u hu fu mu =>
      WP.mono (wordModPre_ok (t := t) hu mu hx hr hmN hrm hxr hxm hxr1 hxm1 h4 hw)
        fun v ⟨Mn, X₀, _, X₃, M₃, H₃, I₀, k₀, _, _, K₀⟩ =>
          ⟨(v, Mn, X₀), ⟨hF fu K₀ (by decide) (by decide)
            (VG.Proof.Rsa.X86.KeyRt.keep_outside hu.ws k₀ (by simp; omega) (by decide)), X₃, M₃, H₃⟩, I₀⟩
    exact (VG.RelCT.wpDep (VG.RelCT.taint (A := sseTaint) τ (fun t₁ t₂ h => hA t₁ t₂ h.1.2.1 h.2.2.1) c₀)
      (F := fun _ v => ∃ p, Inv p 0 v) fun t₁ t₂ h => ⟨pre t₁ h.1.1 h.1.2.1 h.1.2.2, pre t₂ h.2.1 h.2.2.1 h.2.2.2⟩).mono
      (fun _ _ h => h) fun _ _ ⟨_, _, _, _, ⟨p₁, g₁⟩, ⟨p₂, g₂⟩⟩ => ⟨p₁, p₂, g₁, g₂⟩
  · -- A digit step: its count in `eax` and `[x]` in `ebx` agree.
    rw [digitStep_eq]
    refine relCT_head (J := fun p u => Inv p i u) (τ := τ) (τ' := { τ with regs := .ofList [.edi, .esp, .eax, .ebx] })
      (G := fun _ v => Fr v ∧ PtrAt v B .ebx (arr (kw len) x) ∧ (v.gpr .eax).toNat = Sc - i)
      (fun _ _ t₁ t₂ i₁ i₂ => hA t₁ t₂ (frAt i₁) (frAt i₂)) c₁
      (fun _ u iu => WP.mono (loadHead_ok iu.2.ws (by omega) (by decide) iu.2.steps) fun v ⟨K, mm, pb, ea⟩ =>
        ⟨hF (frAt iu) K (by decide) (by decide) (by rw [mm]; exact Outside.refl _ _ _ _), pb, ea⟩)
      (fun _ _ m₁ m₂ ⟨f₁, b₁, e₁⟩ ⟨f₂, b₂, e₂⟩ => agree_regs' (hA m₁ m₂ f₁ f₂) fun r hr => ?_) c₂
    have G := hA m₁ m₂ f₁ f₂
    simp only [RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact G.rf.1 _ (hτ _ (by simp))
    · exact G.rf.1 _ (hτ _ (by simp))
    · exact BitVec.eq_of_toNat_eq (e₁.trans e₂.symm)
    · exact ptr_eq b₁ b₂
  · exact WP.mono (digitStep_ok hx hr hmN ht hrt hmt hrm hxr hxt hxr1 hxt1 h4 hw P.2.1 P.2.2.1 P.2.2.2 rfl hi I)
      fun _ ⟨I', z⟩ => ⟨z, fun _ => ⟨P, I'⟩⟩

end VG.Proof.Rsa.X86.WordRt
