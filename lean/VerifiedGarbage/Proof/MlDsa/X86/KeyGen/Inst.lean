import VerifiedGarbage.Proof.MlKem.X86.CheckEk
import VerifiedGarbage.Impl.MlDsa.X86.KeyGen.Call
import VerifiedGarbage.Proof.MlDsa.KeyGen.Good
import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.Impl.MlDsa.X86.KeyGen.KeyGen
import VerifiedGarbage.Spec.MlDsa.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Impl.MlDsa.X86.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.X86.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.X86.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejBounded
import VerifiedGarbage.Proof.MlDsa.X86.Round.Power2Round
import VerifiedGarbage.Proof.MlDsa.X86.Pack.Unpack

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Call`. -/
section

/-!
# ML-DSA on x86 (32-bit): calls of the primitives from the top-level functions

The top-level functions are proven as ML-KEM's (`Proof/MlKem/X86/Top.lean`:
`Lay`, `Buf`, `Ctx`, `Piece`), for any verified implementations of the
primitives (`Callee`).

A call (`callP`, `callPR`) sets its arguments (`setArgs_ok`: each register
holds its argument's value, `Arg.val`), pushes them and calls. The callee's
entry state (`Ent`) has those arguments on its stack, the memory of the
buffers as the caller left it, and the stack of the call below `E1` (`esp`
in the body): the arguments, the return address, and the callee's own
stack. `callP_piece` makes the call a `Piece` from the callee's precondition
and public data on such an entry state, and gives its postcondition, with
the memory changed only in the buffers it writes and the 80 bytes of stack
below `E1`: at most 5 arguments, the return address and the callee's 56 bytes.
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen (Arg argRegs setArgs argRs callP callPR)

/-! ## The primitives -/

/-- Code verified against `k (K + 1)`, for some stack `K + 1 ≤ 56` (every
function uses some stack, if only for its return address), using at most 56
bytes of stack, and that never writes `esp` but by frames and calls. -/
structure Callee (c : Prog isa) (k : Nat → Contract isa) : Prop where
  verified : ∃ K, K + 1 ≤ 56 ∧ Verified X86.target c (k (K + 1))
  stack : stackUse c ≤ 56
  nosp : NoSp c


variable {Y : VG.Proof.MlKem.X86.Top.Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-! ## Arguments -/

/-- An argument within the layout: a buffer of it, or an immediate of 32 bits. -/
def _root_.VG.Impl.MlDsa.X86.KeyGen.Arg.ok (Y : VG.Proof.MlKem.X86.Top.Lay) : Arg → Bool
  | .buf b => Y.ok b
  | .imm v => decide (v < 2 ^ 32)

/-- The value of an argument. -/
def _root_.VG.Impl.MlDsa.X86.KeyGen.Arg.val (s₀ : State) : Arg → BitVec 32
  | .buf b => b.ptr s₀
  | .imm v => BitVec.ofNat 32 v

theorem _root_.VG.Impl.MlDsa.X86.KeyGen.Arg.val_eq {s₀ s₀' : State} (hq : TPub Y lk s₀ s₀') {a : Arg} (ha : a.ok Y = true) :
    a.val s₀ = a.val s₀' := by
  cases a with
  | buf b => exact hq.ptr ha
  | imm v => rfl

/-- Setting the arguments `as` in the registers `rs`. -/
theorem setArgs_ok {s₀ : State} (hp : TPre Y s₀) {Q : State → Prop} {is : List Instr} :
    ∀ (rs : List Reg) (as : List Arg) (s : State), VG.Proof.MlKem.X86.Top.Ctx Y s₀ s → (∀ r ∈ rs, r ≠ .esp ∧ r ≠ .esi) →
      rs.Nodup → as.all (Arg.ok Y) = true →
      (∀ s', Only rs s s' → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
        (∀ i (h₁ : i < rs.length) (h₂ : i < as.length), s'.gpr rs[i] = as[i].val s₀) → WP isa (.block is) s' Q) →
      WP isa (.block (setArgs Y.sc rs as ++ is)) s Q
  | [], _, s, h, _, _, _, k => k s (Only.refl _ _) h fun _ h₁ => absurd h₁ (Nat.not_lt_zero _)
  | _ :: _, [], s, h, _, _, _, k => k s (Only.refl _ _) h fun _ _ h₂ => absurd h₂ (Nat.not_lt_zero _)
  | r :: rs, a :: as, s, h, hr, hnd, hok, k => by
    have hr0 := hr r (List.mem_cons_self ..)
    rw [List.all_cons, Bool.and_eq_true] at hok
    obtain ⟨hnr, hnd'⟩ := List.nodup_cons.mp hnd
    have step : ∀ s₁, Only [r] s s₁ → s₁.gpr r = a.val s₀ →
        WP isa (.block (setArgs Y.sc rs as ++ is)) s₁ Q := by
      intro s₁ o₁ v₁
      have c₁ := h.only o₁ (by simpa using hr0.1.symm) (by simpa using hr0.2.symm)
      refine VG.Proof.MlDsa.X86.KeyGen.setArgs_ok hp rs as s₁ c₁ (fun r' h' => hr r' (List.mem_cons_of_mem _ h')) hnd' hok.2
        fun s' o' c' v' => k s' ((o₁.trans o').mono fun x hx => by simpa using hx) c' fun i h₁ h₂ => ?_
      cases i with
      | zero => simp only [List.getElem_cons_zero]; rw [o'.gpr r hnr, v₁]
      | succ i => simpa using v' i (by simpa using h₁) (by simpa using h₂)
    show WP isa (.block ((Arg.set Y.sc r a ++ setArgs Y.sc rs as) ++ is)) s Q
    rw [List.append_assoc]
    cases a with
    | buf b => exact ptrTo_ok hp h hok.1 step
    | imm v => exact VG.Proof.MlKem.X86.Top.wp_movi fun s₁ o₁ v₁ => step s₁ o₁ v₁

/-! ## The callee's entry -/

/-- `e` is the entry state of a call with the arguments `as`, set from `s`. -/
structure Ent (Y : VG.Proof.MlKem.X86.Top.Lay) (s₀ s : State) (as : List Arg) (e : State) : Prop where
  esp : e.gpr .esp = E1 s₀ - BitVec.ofNat 32 (4 * as.length + 4)
  arg : ∀ i (h : i < as.length), arg e i = as[i].val s₀
  argAddr0 : argAddr e 0 = (E1 s₀ - BitVec.ofNat 32 (4 * as.length)).setWidth 64
  mem : ∀ b, Y.ok b = true → ∀ i < b.len, e.mem (b.addr s₀ + BitVec.ofNat 64 i) = s.mem (b.addr s₀ + BitVec.ofNat 64 i)

theorem argRs_len {n : Nat} (hn : n ≤ 6) : (argRs n).length = n := by
  simp only [argRs, List.length_reverse, List.length_take, argRegs, List.length_cons, List.length_nil]; omega

theorem argRs_ne {n : Nat} (hn : n ≠ 0) (hn' : n ≤ 6) : argRs n ≠ [] := fun h => by
  have := VG.Proof.MlDsa.X86.KeyGen.argRs_len hn'; rw [h] at this; exact hn this.symm

theorem esp_argRs (n : Nat) : Reg.esp ∉ argRs n := by
  simp only [argRs, List.mem_reverse]
  intro h
  have := List.mem_of_mem_take h
  simp [argRegs] at this

theorem argRs_getD : ∀ n ≤ 6, ∀ i < n, (argRs n).getD ((argRs n).length - 1 - i) .esp = argRegs.getD i .esp := by
  decide

theorem ctx_E' {s₀ s : State} (hp : TPre Y s₀) (h : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s) (hN : 96 ≤ Y.stk) :
    80 ≤ (s.gpr .esp).toNat := ctx_E hp h (N := 80) (by omega)

theorem ent_of {s₀ s s₁ : State} (hp : TPre Y s₀) (hN : 96 ≤ Y.stk) (h₁ : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s₁) (m₁ : s₁.mem = s.mem)
    {as : List Arg} (hn : as.length ≤ 5)
    (v : ∀ i (h₁ : i < argRegs.length) (h₂ : i < as.length), s₁.gpr argRegs[i] = as[i].val s₀) :
    VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀ s as (pushed (argRs as.length) s₁).callEntry := by
  have hE := VG.Proof.MlDsa.X86.KeyGen.ctx_E' hp h₁ hN
  have hl := VG.Proof.MlDsa.X86.KeyGen.argRs_len (n := as.length) (by omega)
  have fit : 4 * (argRs as.length).length + 4 ≤ (s₁.gpr .esp).toNat := by rw [hl]; omega
  refine ⟨?_, fun i hi => ?_, ?_, fun b hb i hi => ?_⟩
  · rw [callEntry_esp', h₁.esp, hl]
  · rw [callEntry_arg fit (VG.Proof.MlDsa.X86.KeyGen.esp_argRs _) (by rw [hl]; exact hi), List.getElem_eq_getD .esp,
      VG.Proof.MlDsa.X86.KeyGen.argRs_getD as.length (by omega) i hi]
    rw [← List.getElem_eq_getD (h := by simp [argRegs]; omega) Reg.esp]
    exact v i (by simp [argRegs]; omega) hi
  · rw [callEntry_argAddr0, h₁.esp, hl]
  · rw [← m₁]
    exact ent_keep hp h₁ (VG.Proof.MlDsa.X86.KeyGen.esp_argRs _) (by rw [hl]; omega) hb i hi

/-- The regions of the callee's entry, apart from a buffer. -/
theorem Ent.rgn {s₀ s e : State} {as : List Arg} (he : VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀ s as e) (hp : TPre Y s₀) (hN : 96 ≤ Y.stk)
    (hn : as.length ≤ 5) {b : Buf} (hb : Y.ok b = true) {K : Nat} (hK : K ≤ 56) :
    (b.rgn s₀).Disjoint (below (E1 s₀) (4 * as.length)) ∧
      (⟨(e.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (b.rgn s₀) ∧
      (⟨(e.gpr .esp).setWidth 64 - BitVec.ofNat 64 K, K⟩ : Region).Disjoint (b.rgn s₀) := by
  have hE : 4 * as.length + 4 + K ≤ (E1 s₀).toNat := by rw [E1_nat s₀ hp.E0_big]; have := hp.sp; omega
  rw [he.esp]
  exact entry_regions hE (Buf.stkD hp hb (N := 4 * as.length + 4 + K) (by omega))

/-- The callee's own regions, apart from each other. -/
theorem Ent.self {s₀ s e : State} {as : List Arg} (he : VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀ s as e) (hp : TPre Y s₀) (hN : 96 ≤ Y.stk)
    (hn : as.length ≤ 5) {K : Nat} (hK : K ≤ 56) :
    (⟨(e.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (below (E1 s₀) (4 * as.length)) ∧
      (⟨(e.gpr .esp).setWidth 64 - BitVec.ofNat 64 K, K⟩ : Region).Disjoint (below (E1 s₀) (4 * as.length)) := by
  have hE : 4 * as.length + 4 + K ≤ (E1 s₀).toNat := by rw [E1_nat s₀ hp.E0_big]; have := hp.sp; omega
  rw [he.esp]
  exact entry_self hE

/-- The callee's stack pointer, as a number. -/
theorem Ent.espNat {s₀ s e : State} {as : List Arg} (he : VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀ s as e) (hp : TPre Y s₀) (hN : 96 ≤ Y.stk)
    (hn : as.length ≤ 5) : (e.gpr .esp).toNat = (E1 s₀).toNat - (4 * as.length + 4) ∧ 80 ≤ (E1 s₀).toNat := by
  have hE : 80 ≤ (E1 s₀).toNat := by rw [E1_nat s₀ hp.E0_big]; have := hp.sp; omega
  rw [he.esp, sub_toNat (by omega)]
  exact ⟨rfl, hE⟩

/-! ## A call -/

/-- The regions of a call: the buffers it reads, and those it writes and its arguments. -/
abbrev rdR (s₀ : State) (rB : List Buf) : List Region := rB.map (Buf.rgn s₀)
abbrev wrR (s₀ : State) (wB : List Buf) (n : Nat) : List Region := wB.map (Buf.rgn s₀) ++ [below (E1 s₀) (4 * n)]

section
variable {k : Contract isa} {nm : String} {c : Prog isa} (as : List Arg) (rB wB : List Buf)

/-- The setting of the arguments of a call. -/
theorem setup_call (hok : as.all (Arg.ok Y) = true)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs Y.sc argRegs as)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s) :
    Piece (TPre Y) (TPub Y lk) A (fun s₀ s₁ => ∃ s, A s₀ s ∧ VG.Proof.MlKem.X86.Top.Ctx Y s₀ s₁ ∧ s₁.mem = s.mem ∧
      ∀ i (h₁ : i < argRegs.length) (h₂ : i < as.length), s₁.gpr argRegs[i] = as[i].val s₀)
      (.block (setArgs Y.sc argRegs as)) :=
  VG.Proof.MlKem.X86.Top.setup_piece _ (fun s₀ s hp h => by
    rw [← List.append_nil (setArgs Y.sc argRegs as)]
    exact VG.Proof.MlDsa.X86.KeyGen.setArgs_ok hp argRegs as s h (by decide) (by decide) hok fun s' o c v =>
      WP.block_nil_iff.mpr ⟨c, o.mem, v⟩) hA tt

theorem call_hd {s₀ s₁ : State} (hp : TPre Y s₀) (hN : 96 ≤ Y.stk) (h₁ : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s₁) (hst : stackUse c ≤ 56)
    (hn : as.length ≤ 5) : 4 * (argRs as.length).length + stackUse c + 4 ≤ (s₁.gpr .esp).toNat := by
  rw [VG.Proof.MlDsa.X86.KeyGen.argRs_len (by omega)]; have := VG.Proof.MlDsa.X86.KeyGen.ctx_E' hp h₁ hN; omega

theorem call_cov {s₀ s₁ : State} (hp : TPre Y s₀) (h₁ : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s₁) (hn : as.length ≤ 5)
    (hr : rB.all Y.ok = true) (hw : wB.all Y.okW = true) :
    Covers (VG.Proof.MlDsa.X86.KeyGen.rdR s₀ rB ++ VG.Proof.MlDsa.X86.KeyGen.wrR s₀ wB as.length)
        (s₁.rd ++ below (s₁.gpr .esp) (4 * (argRs as.length).length) :: s₁.wr) ∧
      Covers (VG.Proof.MlDsa.X86.KeyGen.wrR s₀ wB as.length) (below (s₁.gpr .esp) (4 * (argRs as.length).length) :: s₁.wr) := by
  rw [VG.Proof.MlDsa.X86.KeyGen.argRs_len (by omega)]
  refine covers_of (fun r h => ?_) fun r h => ?_
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
    exact Buf.within hp (List.all_eq_true.mp hr b hb) h₁.rd h₁.wr
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
      obtain ⟨o, w⟩ := Lay.okW_iff.mp (List.all_eq_true.mp hw b hb)
      exact .inr (Buf.withinW hp o w h₁.wr)
    · rw [List.mem_singleton] at h; subst h
      exact .inl (by rw [h₁.esp])

theorem call_fr {s₀ s₁ : State} (hp : TPre Y s₀) (hN : 96 ≤ Y.stk) (h₁ : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s₁) (hst : stackUse c ≤ 56)
    (hn : as.length ≤ 5) {m m' : Mem}
    (fr : Frame (VG.Proof.MlDsa.X86.KeyGen.wrR s₀ wB as.length ++ [below (s₁.gpr .esp) (4 * (argRs as.length).length + stackUse c + 4)]) m m') :
    Frame (FR s₀ wB 80) m m' := by
  rw [h₁.esp, VG.Proof.MlDsa.X86.KeyGen.argRs_len (by omega)] at fr
  refine fr.sub fun r hr => ?_
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with (hr | rfl) | rfl
  · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), stk_sub hp (by omega) (by omega)⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), stk_sub hp (by omega) (by omega)⟩

theorem call_W {s₀ : State} (hp : TPre Y s₀) (hN : 96 ≤ Y.stk) (hw : wB.all Y.okW = true) :
    ∀ r ∈ FR s₀ wB 80, ∃ r' ∈ VG.Proof.MlKem.X86.Top.W Y s₀, Region.Sub r r' := wr_sub hp hw (by omega)

theorem call_pubs {s₀ s₀' s s' e e' : State} (hq : TPub Y lk s₀ s₀') (hok : as.all (Arg.ok Y) = true)
    (he : VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀ s as e) (he' : VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀' s' as e') :
    e.gpr .esp = e'.gpr .esp ∧ ∀ i < as.length, arg e i = arg e' i := by
  refine ⟨by rw [he.esp, he'.esp, hq.E1], fun i hi => ?_⟩
  rw [he.arg i hi, he'.arg i hi]
  exact Arg.val_eq hq (List.all_eq_true.mp hok _ (List.getElem_mem hi))

/-- A call of a primitive: see the module documentation. -/
theorem callP_piece (hv : Verified X86.target c k) (hsp : NoSp c) (hst : stackUse c ≤ 56)
    (hn₀ : as.length ≠ 0) (hn : as.length ≤ 5) (hok : as.all (Arg.ok Y) = true) (hN : 96 ≤ Y.stk)
    (hr : rB.all Y.ok = true) (hw : wB.all Y.okW = true)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs Y.sc argRegs as)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hpre : ∀ s₀ s e, TPre Y s₀ → A s₀ s → VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀ s as e →
      k.pre (e.withRegions (VG.Proof.MlDsa.X86.KeyGen.rdR s₀ rB) (VG.Proof.MlDsa.X86.KeyGen.wrR s₀ wB as.length)))
    (hpub : ∀ s₀ s₀' s s' e e', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀ s as e → VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀' s' as e' →
      k.pub (e.withRegions (VG.Proof.MlDsa.X86.KeyGen.rdR s₀ rB) (VG.Proof.MlDsa.X86.KeyGen.wrR s₀ wB as.length)) (e'.withRegions (VG.Proof.MlDsa.X86.KeyGen.rdR s₀ rB) (VG.Proof.MlDsa.X86.KeyGen.wrR s₀ wB as.length)))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → Frame (FR s₀ wB 80) s.mem s'.mem →
      (∃ e s₂, VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀ s as e ∧ s₂.mem = s'.mem ∧ k.post (e.withRegions (VG.Proof.MlDsa.X86.KeyGen.rdR s₀ rB) (VG.Proof.MlDsa.X86.KeyGen.wrR s₀ wB as.length)) s₂) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (VG.Impl.MlDsa.X86.KeyGen.callP Y.sc nm c as) := by
  refine Piece.seq (VG.Proof.MlDsa.X86.KeyGen.setup_call as hok tt hA) ?_
  refine Piece.callWith hv.1 hv.2.1 hsp (VG.Proof.MlDsa.X86.KeyGen.argRs_ne hn₀ (by omega)) (VG.Proof.MlDsa.X86.KeyGen.esp_argRs _)
    (fun s₀ => VG.Proof.MlDsa.X86.KeyGen.rdR s₀ rB) (fun s₀ => VG.Proof.MlDsa.X86.KeyGen.wrR s₀ wB as.length)
    (fun s₀ s₁ hp ⟨_, _, h₁, _⟩ => VG.Proof.MlDsa.X86.KeyGen.call_hd as hp hN h₁ hst hn)
    (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, v⟩ => ⟨hpre s₀ s _ hp ha (VG.Proof.MlDsa.X86.KeyGen.ent_of hp hN h₁ m₁ hn v),
      (VG.Proof.MlDsa.X86.KeyGen.call_cov as rB wB hp h₁ hn hr hw).1, (VG.Proof.MlDsa.X86.KeyGen.call_cov as rB wB hp h₁ hn hr hw).2⟩)
    (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h₁, m₁, v⟩ ⟨s', ha', h₁', m₁', v'⟩ => ?_)
    (fun s₀ s₁ s' hp ⟨s, ha, h₁, m₁, v⟩ e₁ e₂ e₃ fr ⟨s₂, m₂, post⟩ => ?_)
  · have er : VG.Proof.MlDsa.X86.KeyGen.rdR s₀ rB = VG.Proof.MlDsa.X86.KeyGen.rdR s₀' rB := List.map_congr_left fun b hb => by
      simp only [Buf.rgn, hq.ptr (List.all_eq_true.mp hr b hb)]
    have ew : VG.Proof.MlDsa.X86.KeyGen.wrR s₀ wB as.length = VG.Proof.MlDsa.X86.KeyGen.wrR s₀' wB as.length := by
      simp only [VG.Proof.MlDsa.X86.KeyGen.wrR, hq.E1]
      exact congrArg (· ++ _) (List.map_congr_left fun b hb => by
        simp only [Buf.rgn, hq.ptr (Lay.okW_iff.mp (List.all_eq_true.mp hw b hb)).1])
    refine ⟨er, ew, by rw [h₁.esp, h₁'.esp, hq.E1], ?_⟩
    have := hpub s₀ s₀' s s' _ _ hp hp' hq ha ha' (VG.Proof.MlDsa.X86.KeyGen.ent_of hp hN h₁ m₁ hn v) (VG.Proof.MlDsa.X86.KeyGen.ent_of hp' hN h₁' m₁' hn v')
    exact this
  · have fr' := VG.Proof.MlDsa.X86.KeyGen.call_fr as wB hp hN h₁ hst hn fr
    have h' : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' := h₁.call e₁ e₂ e₃ fr' (VG.Proof.MlDsa.X86.KeyGen.call_W wB hp hN hw)
    rw [m₁] at fr'
    exact hQ s₀ s s' hp ha h' fr' ⟨_, s₂, VG.Proof.MlDsa.X86.KeyGen.ent_of hp hN h₁ m₁ hn v, m₂, post⟩

/-- `callP_piece`, for a call that returns a value in `eax` (`callPR`). -/
theorem callPR_piece (hv : Verified X86.target c k) (hsp : NoSp c) (hst : stackUse c ≤ 56)
    (hn₀ : as.length ≠ 0) (hn : as.length ≤ 5) (hok : as.all (Arg.ok Y) = true) (hN : 96 ≤ Y.stk)
    (hr : rB.all Y.ok = true) (hw : wB.all Y.okW = true)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs Y.sc argRegs as)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hpre : ∀ s₀ s e, TPre Y s₀ → A s₀ s → VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀ s as e →
      k.pre (e.withRegions (VG.Proof.MlDsa.X86.KeyGen.rdR s₀ rB) (VG.Proof.MlDsa.X86.KeyGen.wrR s₀ wB as.length)))
    (hpub : ∀ s₀ s₀' s s' e e', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀ s as e → VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀' s' as e' →
      k.pub (e.withRegions (VG.Proof.MlDsa.X86.KeyGen.rdR s₀ rB) (VG.Proof.MlDsa.X86.KeyGen.wrR s₀ wB as.length)) (e'.withRegions (VG.Proof.MlDsa.X86.KeyGen.rdR s₀ rB) (VG.Proof.MlDsa.X86.KeyGen.wrR s₀ wB as.length)))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → Frame (FR s₀ wB 80) s.mem s'.mem →
      (∃ e s₂, VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀ s as e ∧ s₂.mem = s'.mem ∧ s₂.gpr .eax = s'.gpr .eax ∧
        k.post (e.withRegions (VG.Proof.MlDsa.X86.KeyGen.rdR s₀ rB) (VG.Proof.MlDsa.X86.KeyGen.wrR s₀ wB as.length)) s₂) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (VG.Impl.MlDsa.X86.KeyGen.callPR Y.sc nm c as) := by
  refine Piece.seq (VG.Proof.MlDsa.X86.KeyGen.setup_call as hok tt hA) ?_
  refine Piece.callRet hv.1 hv.2.1 hsp (VG.Proof.MlDsa.X86.KeyGen.argRs_ne hn₀ (by omega)) (VG.Proof.MlDsa.X86.KeyGen.esp_argRs _)
    (fun s₀ => VG.Proof.MlDsa.X86.KeyGen.rdR s₀ rB) (fun s₀ => VG.Proof.MlDsa.X86.KeyGen.wrR s₀ wB as.length)
    (fun s₀ s₁ hp ⟨_, _, h₁, _⟩ => VG.Proof.MlDsa.X86.KeyGen.call_hd as hp hN h₁ hst hn)
    (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, v⟩ => ⟨hpre s₀ s _ hp ha (VG.Proof.MlDsa.X86.KeyGen.ent_of hp hN h₁ m₁ hn v),
      (VG.Proof.MlDsa.X86.KeyGen.call_cov as rB wB hp h₁ hn hr hw).1, (VG.Proof.MlDsa.X86.KeyGen.call_cov as rB wB hp h₁ hn hr hw).2⟩)
    (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h₁, m₁, v⟩ ⟨s', ha', h₁', m₁', v'⟩ => ?_)
    (fun s₀ s₁ s' hp ⟨s, ha, h₁, m₁, v⟩ e₁ e₂ e₃ fr ⟨s₂, m₂, g₂, post⟩ => ?_)
  · have er : VG.Proof.MlDsa.X86.KeyGen.rdR s₀ rB = VG.Proof.MlDsa.X86.KeyGen.rdR s₀' rB := List.map_congr_left fun b hb => by
      simp only [Buf.rgn, hq.ptr (List.all_eq_true.mp hr b hb)]
    have ew : VG.Proof.MlDsa.X86.KeyGen.wrR s₀ wB as.length = VG.Proof.MlDsa.X86.KeyGen.wrR s₀' wB as.length := by
      simp only [VG.Proof.MlDsa.X86.KeyGen.wrR, hq.E1]
      exact congrArg (· ++ _) (List.map_congr_left fun b hb => by
        simp only [Buf.rgn, hq.ptr (Lay.okW_iff.mp (List.all_eq_true.mp hw b hb)).1])
    refine ⟨er, ew, by rw [h₁.esp, h₁'.esp, hq.E1], ?_⟩
    have := hpub s₀ s₀' s s' _ _ hp hp' hq ha ha' (VG.Proof.MlDsa.X86.KeyGen.ent_of hp hN h₁ m₁ hn v) (VG.Proof.MlDsa.X86.KeyGen.ent_of hp' hN h₁' m₁' hn v')
    exact this
  · have fr' := VG.Proof.MlDsa.X86.KeyGen.call_fr as wB hp hN h₁ hst hn fr
    have h' : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' := h₁.call e₁ e₂ e₃ fr' (VG.Proof.MlDsa.X86.KeyGen.call_W wB hp hN hw)
    rw [m₁] at fr'
    exact hQ s₀ s s' hp ha h' fr' ⟨_, s₂, VG.Proof.MlDsa.X86.KeyGen.ent_of hp hN h₁ m₁ hn v, m₂, g₂, post⟩

end

/-! ## Calls of functions that may not write their arguments -/

/-- The regions of such a call: the buffers it reads and its arguments, and those it writes. -/
abbrev rdRO (s₀ : State) (rB : List Buf) (n : Nat) : List Region := rB.map (Buf.rgn s₀) ++ [below (E1 s₀) (4 * n)]
abbrev wrRO (s₀ : State) (wB : List Buf) : List Region := wB.map (Buf.rgn s₀)

section
variable {k : Contract isa} {nm : String} {c : Prog isa} (as : List Arg) (rB wB : List Buf)

theorem call_covRO {s₀ s₁ : State} (hp : TPre Y s₀) (h₁ : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s₁) (hn : as.length ≤ 5)
    (hr : rB.all Y.ok = true) (hw : wB.all Y.okW = true) :
    Covers (VG.Proof.MlDsa.X86.KeyGen.rdRO s₀ rB as.length ++ VG.Proof.MlDsa.X86.KeyGen.wrRO s₀ wB)
        (s₁.rd ++ below (s₁.gpr .esp) (4 * (argRs as.length).length) :: s₁.wr) ∧
      Covers (VG.Proof.MlDsa.X86.KeyGen.wrRO s₀ wB) (below (s₁.gpr .esp) (4 * (argRs as.length).length) :: s₁.wr) := by
  rw [VG.Proof.MlDsa.X86.KeyGen.argRs_len (by omega)]
  refine ⟨Covers.of_sub fun r hr' => ?_, Covers.of_sub fun r hr' => ?_⟩
  · rcases List.mem_append.mp hr' with hr' | hr'
    · rcases List.mem_append.mp hr' with hr' | hr'
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr'
        obtain ⟨r', h', o, e, l⟩ := Buf.within hp (List.all_eq_true.mp hr b hb) h₁.rd h₁.wr
        refine ⟨r', ?_, o, e, l⟩
        rcases List.mem_append.mp h' with h' | h'
        · exact List.mem_append_left _ h'
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h')
      · rw [List.mem_singleton] at hr'; subst hr'
        exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), 0, by rw [h₁.esp]; simp, by simp⟩
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr'
      obtain ⟨o, w⟩ := Lay.okW_iff.mp (List.all_eq_true.mp hw b hb)
      obtain ⟨r', h', o', e, l⟩ := Buf.withinW hp o w h₁.wr
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ h'), o', e, l⟩
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr'
    obtain ⟨o, w⟩ := Lay.okW_iff.mp (List.all_eq_true.mp hw b hb)
    obtain ⟨r', h', o', e, l⟩ := Buf.withinW hp o w h₁.wr
    exact ⟨r', List.mem_cons_of_mem _ h', o', e, l⟩

theorem call_frRO {s₀ s₁ : State} (hp : TPre Y s₀) (hN : 96 ≤ Y.stk) (h₁ : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s₁) (hst : stackUse c ≤ 56)
    (hn : as.length ≤ 5) {m m' : Mem}
    (fr : Frame (VG.Proof.MlDsa.X86.KeyGen.wrRO s₀ wB ++ [below (s₁.gpr .esp) (4 * (argRs as.length).length + stackUse c + 4)]) m m') :
    Frame (FR s₀ wB 80) m m' := by
  rw [h₁.esp, VG.Proof.MlDsa.X86.KeyGen.argRs_len (by omega)] at fr
  refine fr.sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
  · rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), stk_sub hp (by omega) (by omega)⟩

/-- `callPR_piece`, for a function that may not write its arguments. -/
theorem callPR_pieceRO (hv : Verified X86.target c k) (hsp : NoSp c) (hst : stackUse c ≤ 56)
    (hn₀ : as.length ≠ 0) (hn : as.length ≤ 5) (hok : as.all (Arg.ok Y) = true) (hN : 96 ≤ Y.stk)
    (hr : rB.all Y.ok = true) (hw : wB.all Y.okW = true)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs Y.sc argRegs as)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hpre : ∀ s₀ s e, TPre Y s₀ → A s₀ s → VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀ s as e →
      k.pre (e.withRegions (VG.Proof.MlDsa.X86.KeyGen.rdRO s₀ rB as.length) (VG.Proof.MlDsa.X86.KeyGen.wrRO s₀ wB)))
    (hpub : ∀ s₀ s₀' s s' e e', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀ s as e → VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀' s' as e' →
      k.pub (e.withRegions (VG.Proof.MlDsa.X86.KeyGen.rdRO s₀ rB as.length) (VG.Proof.MlDsa.X86.KeyGen.wrRO s₀ wB))
        (e'.withRegions (VG.Proof.MlDsa.X86.KeyGen.rdRO s₀ rB as.length) (VG.Proof.MlDsa.X86.KeyGen.wrRO s₀ wB)))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → Frame (FR s₀ wB 80) s.mem s'.mem →
      (∃ e s₂, VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀ s as e ∧ s₂.mem = s'.mem ∧ s₂.gpr .eax = s'.gpr .eax ∧
        k.post (e.withRegions (VG.Proof.MlDsa.X86.KeyGen.rdRO s₀ rB as.length) (VG.Proof.MlDsa.X86.KeyGen.wrRO s₀ wB)) s₂) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (VG.Impl.MlDsa.X86.KeyGen.callPR Y.sc nm c as) := by
  refine Piece.seq (VG.Proof.MlDsa.X86.KeyGen.setup_call as hok tt hA) ?_
  refine Piece.callRet hv.1 hv.2.1 hsp (VG.Proof.MlDsa.X86.KeyGen.argRs_ne hn₀ (by omega)) (VG.Proof.MlDsa.X86.KeyGen.esp_argRs _)
    (fun s₀ => VG.Proof.MlDsa.X86.KeyGen.rdRO s₀ rB as.length) (fun s₀ => VG.Proof.MlDsa.X86.KeyGen.wrRO s₀ wB)
    (fun s₀ s₁ hp ⟨_, _, h₁, _⟩ => VG.Proof.MlDsa.X86.KeyGen.call_hd as hp hN h₁ hst hn)
    (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, v⟩ => ⟨hpre s₀ s _ hp ha (VG.Proof.MlDsa.X86.KeyGen.ent_of hp hN h₁ m₁ hn v),
      (VG.Proof.MlDsa.X86.KeyGen.call_covRO as rB wB hp h₁ hn hr hw).1, (VG.Proof.MlDsa.X86.KeyGen.call_covRO as rB wB hp h₁ hn hr hw).2⟩)
    (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h₁, m₁, v⟩ ⟨s', ha', h₁', m₁', v'⟩ => ?_)
    (fun s₀ s₁ s' hp ⟨s, ha, h₁, m₁, v⟩ e₁ e₂ e₃ fr ⟨s₂, m₂, g₂, post⟩ => ?_)
  · have er : VG.Proof.MlDsa.X86.KeyGen.rdRO s₀ rB as.length = VG.Proof.MlDsa.X86.KeyGen.rdRO s₀' rB as.length := by
      simp only [VG.Proof.MlDsa.X86.KeyGen.rdRO, hq.E1]
      exact congrArg (· ++ _) (List.map_congr_left fun b hb => by
        simp only [Buf.rgn, hq.ptr (List.all_eq_true.mp hr b hb)])
    have ew : VG.Proof.MlDsa.X86.KeyGen.wrRO s₀ wB = VG.Proof.MlDsa.X86.KeyGen.wrRO s₀' wB := List.map_congr_left fun b hb => by
      simp only [Buf.rgn, hq.ptr (Lay.okW_iff.mp (List.all_eq_true.mp hw b hb)).1]
    refine ⟨er, ew, by rw [h₁.esp, h₁'.esp, hq.E1], ?_⟩
    exact hpub s₀ s₀' s s' _ _ hp hp' hq ha ha' (VG.Proof.MlDsa.X86.KeyGen.ent_of hp hN h₁ m₁ hn v) (VG.Proof.MlDsa.X86.KeyGen.ent_of hp' hN h₁' m₁' hn v')
  · have fr' := VG.Proof.MlDsa.X86.KeyGen.call_frRO as wB hp hN h₁ hst hn fr
    have h' : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' := h₁.call e₁ e₂ e₃ fr' (VG.Proof.MlDsa.X86.KeyGen.call_W wB hp hN hw)
    rw [m₁] at fr'
    exact hQ s₀ s s' hp ha h' fr' ⟨_, s₂, VG.Proof.MlDsa.X86.KeyGen.ent_of hp hN h₁ m₁ hn v, m₂, g₂, post⟩

end

end VG.Proof.MlDsa.X86.KeyGen

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen (Arg)

variable {Y : VG.Proof.MlKem.X86.Top.Lay}

/-- What a callee's precondition needs of a buffer it is passed. -/
theorem Ent.buf {s₀ s e : State} {as : List Arg} (he : VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀ s as e) (hp : TPre Y s₀) (hN : 96 ≤ Y.stk)
    (hn : as.length ≤ 5) {b : Buf} (hb : Y.ok b = true) {K : Nat} (hK : K ≤ 56) :
    (b.rgn s₀).Disjoint (below (E1 s₀) (4 * as.length)) ∧
      (⟨(e.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (b.rgn s₀) ∧
      (⟨(e.gpr .esp).setWidth 64 - BitVec.ofNat 64 K, K⟩ : Region).Disjoint (b.rgn s₀) ∧
      (b.ptr s₀).toNat + b.len ≤ 2 ^ 32 :=
  ⟨(he.rgn hp hN hn hb hK).1, (he.rgn hp hN hn hb hK).2.1, (he.rgn hp hN hn hb hK).2.2, Buf.fit hp hb⟩

end VG.Proof.MlDsa.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim`. -/
section

/-!
# ML-DSA on x86 (32-bit): calls of the polynomial primitives

For each signature of the primitives key generation and verification call, a
call (`callP_piece`) of any code verified against its contract (`Callee`),
with its arguments named as buffers and immediates: its precondition on entry
and its public data, from the layout, and its postcondition restated on the
caller's memory.

The facts about regions and the stack of the callee's precondition are
those `Ent.buf` gives for each buffer, `Ent.self` for the callee's own
regions, and `Buf.disj` for pairs of buffers.
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen (Arg argRegs setArgs callP callPR)
open VG.Spec.MlDsa (Poly Reduced PolyIs polyAt)

variable {Y : VG.Proof.MlKem.X86.Top.Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-- Closes the facts of a callee's precondition about its stack and regions,
from those in the context. -/
macro "ent_pre" : tactic => `(tactic| (and_intros <;>
  first | exact True.intro | with_reducible assumption | omega | rfl))

theorem sw_app (a b : BitVec 32) : BitVec.setWidth 32 (a ++ b) = b := BitVec.setWidth_append_eq_right

theorem ent_polyAt {s₀ s e : State} {as : List Arg} (he : VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀ s as e) {a o : Nat}
    (hb : Y.ok ⟨a, o, 1024⟩ = true) :
    polyAt e.mem (Buf.addr s₀ ⟨a, o, 1024⟩) = polyAt s.mem (Buf.addr s₀ ⟨a, o, 1024⟩) :=
  Proof.MlDsa.KeyGen.polyAt_congr (he.mem _ hb)

theorem ent_reduced {s₀ s e : State} {as : List Arg} (he : VG.Proof.MlDsa.X86.KeyGen.Ent Y s₀ s as e) {a o : Nat}
    (hb : Y.ok ⟨a, o, 1024⟩ = true) (h : Reduced s.mem (Buf.addr s₀ ⟨a, o, 1024⟩)) :
    Reduced e.mem (Buf.addr s₀ ⟨a, o, 1024⟩) :=
  Proof.MlDsa.KeyGen.reduced_congr (he.mem _ hb) h

/-! ## In place: `vg_mldsa_ntt`, `vg_mldsa_inv_ntt` -/

theorem inPlace_piece {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {nm : String} {c : Prog isa}
    (hc : VG.Proof.MlDsa.X86.KeyGen.Callee c fun stk => Spec.MlDsa.inPlaceContract X86.abi t stk) (fa fo wa wo : Nat)
    (hk : (Y.okW ⟨fa, fo, 1024⟩ && Y.okW ⟨wa, wo, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨wa, wo, 1024⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨fa, fo, 1024⟩, .buf ⟨wa, wo, 1024⟩])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame (FR s₀ [⟨fa, fo, 1024⟩, ⟨wa, wo, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (t (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (VG.Impl.MlDsa.X86.KeyGen.callP Y.sc nm c [.buf ⟨fa, fo, 1024⟩, .buf ⟨wa, wo, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hF, hW⟩, dFW⟩ := hk
  have hF' := (Lay.okW_iff.mp hF).1
  have hW' := (Lay.okW_iff.mp hW).1
  refine VG.Proof.MlDsa.X86.KeyGen.callP_piece _ [] [⟨fa, fo, 1024⟩, ⟨wa, wo, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hF', hW']) hN (by simp) (by simp [hF, hW]) tt (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF' hK
    obtain ⟨w₁, w₂, w₃, w₄⟩ := he.buf hp hN (by simp) hW' hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hF' hW' dFW
    have r₁ := VG.Proof.MlDsa.X86.KeyGen.ent_reduced he hF' (hA s₀ s hp ha).2
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, aa, List.getElem_cons_zero, List.getElem_cons_succ,
      Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at *
    exact ⟨by omega, by omega, rfl, d₁, f₁, w₁, f₂, w₂, x₁, f₃, w₃, x₂, f₄, w₄, r₁⟩
  · obtain ⟨esp, ags⟩ := VG.Proof.MlDsa.X86.KeyGen.call_pubs _ hq (by simp [Arg.ok, hF', hW']) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    simp only [arg_withRegions, a₀, List.getElem_cons_zero, Arg.val, m₂] at post
    rw [VG.Proof.MlDsa.X86.KeyGen.ent_polyAt he hF'] at post
    exact hQ s₀ s s' hp ha h' fr post

theorem toNat_ofNat32 {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 32 v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## `vg_mldsa_rej_ntt_poly` -/

theorem rejNtt_piece {c : Prog isa} (hc : VG.Proof.MlDsa.X86.KeyGen.Callee c fun stk => Spec.MlDsa.rejNTTContract X86.abi stk)
    (da dO aa ao wa wo : Nat)
    (hk : (Y.ok ⟨da, dO, 34⟩ && Y.okW ⟨aa, ao, 1024⟩ && Y.okW ⟨wa, wo, 2048⟩ && Y.sep ⟨da, dO, 34⟩ ⟨aa, ao, 1024⟩ &&
      Y.sep ⟨da, dO, 34⟩ ⟨wa, wo, 2048⟩ && Y.sep ⟨aa, ao, 1024⟩ ⟨wa, wo, 2048⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨da, dO, 34⟩, .buf ⟨aa, ao, 1024⟩, .buf ⟨wa, wo, 2048⟩])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hseed : ∀ s₀ s₀' s s', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34 = Spec.Sha3.bytesAt s'.mem (Buf.addr s₀' ⟨da, dO, 34⟩) 34)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame (FR s₀ [⟨aa, ao, 1024⟩, ⟨wa, wo, 2048⟩] 80) s.mem s'.mem →
      (s'.gpr .eax = 1 → Reduced s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) →
      Spec.MlDsa.Outcome (fun b => Spec.MlDsa.rejNTTPoly b.rejNTT
        (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34)) (s'.gpr .eax)
        (polyAt s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (VG.Impl.MlDsa.X86.KeyGen.callPR Y.sc "vg_mldsa_rej_ntt_poly" c [.buf ⟨da, dO, 34⟩, .buf ⟨aa, ao, 1024⟩, .buf ⟨wa, wo, 2048⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨hD, hAw⟩, hW⟩, dDA⟩, dDW⟩, dAW⟩ := hk
  have hA₁ := (Lay.okW_iff.mp hAw).1
  have hW₁ := (Lay.okW_iff.mp hW).1
  refine VG.Proof.MlDsa.X86.KeyGen.callPR_piece _ [⟨da, dO, 34⟩] [⟨aa, ao, 1024⟩, ⟨wa, wo, 2048⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hD, hA₁, hW₁]) hN (by simp [hD]) (by simp [hAw, hW]) tt hA
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, g₂, post⟩ => ?_)
  · obtain ⟨b₁, b₂, b₃, b₄⟩ := he.buf hp hN (by simp) hD hK
    obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hA₁ hK
    obtain ⟨w₁, w₂, w₃, w₄⟩ := he.buf hp hN (by simp) hW₁ hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hD hA₁ dDA
    have d₂ := Buf.disj hp hD hW₁ dDW
    have d₃ := Buf.disj hp hA₁ hW₁ dAW
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at *
    ent_pre
  · obtain ⟨esp, ags⟩ := VG.Proof.MlDsa.X86.KeyGen.call_pubs _ hq (by simp [Arg.ok, hD, hA₁, hW₁]) he he'
    have hs := hseed s₀ s₀' s s' hp hp' hq ha ha'
    have a₀ := he.arg 0 (by simp)
    have a₀' := he'.arg 0 (by simp)
    rw [← Proof.MlKem.bytesAt_congr (he.mem _ hD), ← Proof.MlKem.bytesAt_congr (he'.mem _ hD)] at hs
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [List.getElem_cons_zero, Arg.val] at a₀ a₀'
    simp only [Buf.addr, ← a₀, ← a₀'] at hs
    simp only [arg_withRegions]
    exact ⟨esp, by rw [hs], ags 0 (by simp), ags 1 (by simp), ags 2 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂, g₂, VG.Proof.MlDsa.X86.KeyGen.sw_app] at post
    rw [Proof.MlKem.bytesAt_congr (he.mem _ hD)] at post
    exact hQ s₀ s s' hp ha h' fr post.1 post.2


/-! ## Three polynomials: `vg_mldsa_multiply_ntt`, `vg_mldsa_multiply_add_ntt`, `vg_mldsa_power2round` -/

section
variable (ha hao fa fo ga go : Nat)

/-- The checks of the buffers of a call with the arguments `h` (written), `f` and `g`. -/
abbrev chk3 (Y : VG.Proof.MlKem.X86.Top.Lay) (h f g : Buf) : Bool :=
  Y.okW h && Y.ok f && Y.ok g && Y.sep h f && Y.sep h g

theorem chk3_iff {h f g : Buf} (hk : VG.Proof.MlDsa.X86.KeyGen.chk3 Y h f g = true) :
    Y.okW h = true ∧ Y.ok h = true ∧ Y.ok f = true ∧ Y.ok g = true ∧ Y.sep h f = true ∧ Y.sep h g = true := by
  simp only [VG.Proof.MlDsa.X86.KeyGen.chk3, Bool.and_eq_true] at hk
  exact ⟨hk.1.1.1.1, (Lay.okW_iff.mp hk.1.1.1.1).1, hk.1.1.1.2, hk.1.1.2, hk.1.2, hk.2⟩

theorem mul_piece {c : Prog isa} (hc : VG.Proof.MlDsa.X86.KeyGen.Callee c fun stk => Spec.MlDsa.mulContract X86.abi stk)
    (hk : VG.Proof.MlDsa.X86.KeyGen.chk3 Y ⟨ha, hao, 1024⟩ ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩ = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨ha, hao, 1024⟩, .buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → Frame (FR s₀ [⟨ha, hao, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨ha, hao, 1024⟩) (Spec.MlDsa.multiplyNTT (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
        (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (VG.Impl.MlDsa.X86.KeyGen.callP Y.sc "vg_mldsa_multiply_ntt" c [.buf ⟨ha, hao, 1024⟩, .buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  obtain ⟨hHw, hH, hF, hG, dHF, dHG⟩ := VG.Proof.MlDsa.X86.KeyGen.chk3_iff hk
  refine VG.Proof.MlDsa.X86.KeyGen.callP_piece _ [⟨fa, fo, 1024⟩, ⟨ga, go, 1024⟩] [⟨ha, hao, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hH, hF, hG]) hN (by simp [hF, hG]) (by simp [hHw]) tt (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := he.buf hp hN (by simp) hH hK
    obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF hK
    obtain ⟨g₁, g₂, g₃, g₄⟩ := he.buf hp hN (by simp) hG hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hH hF dHF
    have d₂ := Buf.disj hp hH hG dHG
    have rf := VG.Proof.MlDsa.X86.KeyGen.ent_reduced he hF (hA s₀ s hp ha).2.1
    have rg := VG.Proof.MlDsa.X86.KeyGen.ent_reduced he hG (hA s₀ s hp ha).2.2
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at *
    ent_pre
  · obtain ⟨esp, ags⟩ := VG.Proof.MlDsa.X86.KeyGen.call_pubs _ hq (by simp [Arg.ok, hH, hF, hG]) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂] at post
    rw [VG.Proof.MlDsa.X86.KeyGen.ent_polyAt he hF, VG.Proof.MlDsa.X86.KeyGen.ent_polyAt he hG] at post
    exact hQ s₀ s s' hp ha h' (fr.mono fun r hr => by simp at hr ⊢; grind) post

theorem mulAdd_piece {c : Prog isa} (hc : VG.Proof.MlDsa.X86.KeyGen.Callee c fun stk => Spec.MlDsa.mulAddContract X86.abi stk)
    (hk : VG.Proof.MlDsa.X86.KeyGen.chk3 Y ⟨ha, hao, 1024⟩ ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩ = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨ha, hao, 1024⟩, .buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨ha, hao, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧ Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → Frame (FR s₀ [⟨ha, hao, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨ha, hao, 1024⟩) (Spec.MlDsa.add (polyAt s.mem (Buf.addr s₀ ⟨ha, hao, 1024⟩))
        (Spec.MlDsa.multiplyNTT (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
        (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩)))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (VG.Impl.MlDsa.X86.KeyGen.callP Y.sc "vg_mldsa_multiply_add_ntt" c [.buf ⟨ha, hao, 1024⟩, .buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  obtain ⟨hHw, hH, hF, hG, dHF, dHG⟩ := VG.Proof.MlDsa.X86.KeyGen.chk3_iff hk
  refine VG.Proof.MlDsa.X86.KeyGen.callP_piece _ [⟨fa, fo, 1024⟩, ⟨ga, go, 1024⟩] [⟨ha, hao, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hH, hF, hG]) hN (by simp [hF, hG]) (by simp [hHw]) tt (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := he.buf hp hN (by simp) hH hK
    obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF hK
    obtain ⟨g₁, g₂, g₃, g₄⟩ := he.buf hp hN (by simp) hG hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hH hF dHF
    have d₂ := Buf.disj hp hH hG dHG
    have rh := VG.Proof.MlDsa.X86.KeyGen.ent_reduced he hH (hA s₀ s hp ha).2.1
    have rf := VG.Proof.MlDsa.X86.KeyGen.ent_reduced he hF (hA s₀ s hp ha).2.2.1
    have rg := VG.Proof.MlDsa.X86.KeyGen.ent_reduced he hG (hA s₀ s hp ha).2.2.2
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at *
    ent_pre
  · obtain ⟨esp, ags⟩ := VG.Proof.MlDsa.X86.KeyGen.call_pubs _ hq (by simp [Arg.ok, hH, hF, hG]) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂] at post
    rw [VG.Proof.MlDsa.X86.KeyGen.ent_polyAt he hH, VG.Proof.MlDsa.X86.KeyGen.ent_polyAt he hF, VG.Proof.MlDsa.X86.KeyGen.ent_polyAt he hG] at post
    exact hQ s₀ s s' hp ha h' (fr.mono fun r hr => by simp at hr ⊢; grind) post

/-- The checks of the buffers of a call with the arguments `t`, `t₁` and `t₀` (both written). -/
abbrev chkP2 (Y : VG.Proof.MlKem.X86.Top.Lay) (t t1 t0 : Buf) : Bool :=
  Y.ok t && Y.okW t1 && Y.okW t0 && Y.sep t t1 && Y.sep t t0 && Y.sep t1 t0

theorem p2r_piece {c : Prog isa} (hc : VG.Proof.MlDsa.X86.KeyGen.Callee c fun stk => Spec.MlDsa.power2RoundContract X86.abi stk)
    (hk : VG.Proof.MlDsa.X86.KeyGen.chkP2 Y ⟨ha, hao, 1024⟩ ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩ = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨ha, hao, 1024⟩, .buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨ha, hao, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame (FR s₀ [⟨fa, fo, 1024⟩, ⟨ga, go, 1024⟩] 80) s.mem s'.mem →
      Spec.MlDsa.NatPolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        ((polyAt s.mem (Buf.addr s₀ ⟨ha, hao, 1024⟩)).map fun c => (Spec.MlDsa.power2Round c).1.toNat) →
      PolyIs s'.mem (Buf.addr s₀ ⟨ga, go, 1024⟩)
        ((polyAt s.mem (Buf.addr s₀ ⟨ha, hao, 1024⟩)).map fun c => Spec.MlDsa.ofInt (Spec.MlDsa.power2Round c).2) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (VG.Impl.MlDsa.X86.KeyGen.callP Y.sc "vg_mldsa_power2round" c [.buf ⟨ha, hao, 1024⟩, .buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [VG.Proof.MlDsa.X86.KeyGen.chkP2, Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨hH, hFw⟩, hGw⟩, dHF⟩, dHG⟩, dFG⟩ := hk
  have hF := (Lay.okW_iff.mp hFw).1
  have hG := (Lay.okW_iff.mp hGw).1
  refine VG.Proof.MlDsa.X86.KeyGen.callP_piece _ [⟨ha, hao, 1024⟩] [⟨fa, fo, 1024⟩, ⟨ga, go, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hH, hF, hG]) hN (by simp [hH]) (by simp [hFw, hGw]) tt (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := he.buf hp hN (by simp) hH hK
    obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF hK
    obtain ⟨g₁, g₂, g₃, g₄⟩ := he.buf hp hN (by simp) hG hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hH hF dHF
    have d₂ := Buf.disj hp hH hG dHG
    have d₃ := Buf.disj hp hF hG dFG
    have rh := VG.Proof.MlDsa.X86.KeyGen.ent_reduced he hH (hA s₀ s hp ha).2
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.power2RoundContract, Spec.MlDsa.power2RoundSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at *
    ent_pre
  · obtain ⟨esp, ags⟩ := VG.Proof.MlDsa.X86.KeyGen.call_pubs _ hq (by simp [Arg.ok, hH, hF, hG]) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.power2RoundContract, Spec.MlDsa.power2RoundSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.power2RoundContract, Spec.MlDsa.power2RoundSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂] at post
    rw [VG.Proof.MlDsa.X86.KeyGen.ent_polyAt he hH] at post
    exact hQ s₀ s s' hp ha h' fr post.1 post.2

end

/-! ## Two polynomials: `vg_mldsa_add`, `vg_mldsa_sub` -/

theorem acc_piece {op : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {nm : String} {c : Prog isa}
    (hc : VG.Proof.MlDsa.X86.KeyGen.Callee c fun stk => Spec.MlDsa.accSig.contract X86.abi
      (pre := fun f g m => Reduced m f ∧ Reduced m g)
      (post := fun f g m m' _ => PolyIs m' f (op (polyAt m f) (polyAt m g))) (writeArgs := true) (stack := stk))
    (fa fo ga go : Nat)
    (hk : (Y.okW ⟨fa, fo, 1024⟩ && Y.ok ⟨ga, go, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → Frame (FR s₀ [⟨fa, fo, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (op (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (VG.Impl.MlDsa.X86.KeyGen.callP Y.sc nm c [.buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hFw, hG⟩, dFG⟩ := hk
  have hF := (Lay.okW_iff.mp hFw).1
  refine VG.Proof.MlDsa.X86.KeyGen.callP_piece _ [⟨ga, go, 1024⟩] [⟨fa, fo, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hF, hG]) hN (by simp [hG]) (by simp [hFw]) tt (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF hK
    obtain ⟨g₁, g₂, g₃, g₄⟩ := he.buf hp hN (by simp) hG hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hF hG dFG
    have rf := VG.Proof.MlDsa.X86.KeyGen.ent_reduced he hF (hA s₀ s hp ha).2.1
    have rg := VG.Proof.MlDsa.X86.KeyGen.ent_reduced he hG (hA s₀ s hp ha).2.2
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at *
    ent_pre
  · obtain ⟨esp, ags⟩ := VG.Proof.MlDsa.X86.KeyGen.call_pubs _ hq (by simp [Arg.ok, hF, hG]) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂] at post
    rw [VG.Proof.MlDsa.X86.KeyGen.ent_polyAt he hF, VG.Proof.MlDsa.X86.KeyGen.ent_polyAt he hG] at post
    exact hQ s₀ s s' hp ha h' fr post


/-! ## `vg_mldsa_rej_bounded_poly` -/

theorem rejBounded_piece {c : Prog isa} (hc : VG.Proof.MlDsa.X86.KeyGen.Callee c fun stk => Spec.MlDsa.rejBoundedContract X86.abi stk)
    (da dO η aa ao wa wo : Nat) (hη : η = 2 ∨ η = 4)
    (hk : (Y.ok ⟨da, dO, 66⟩ && Y.okW ⟨aa, ao, 1024⟩ && Y.okW ⟨wa, wo, 2048⟩ && Y.sep ⟨da, dO, 66⟩ ⟨aa, ao, 1024⟩ &&
      Y.sep ⟨da, dO, 66⟩ ⟨wa, wo, 2048⟩ && Y.sep ⟨aa, ao, 1024⟩ ⟨wa, wo, 2048⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨da, dO, 66⟩, .imm η, .buf ⟨aa, ao, 1024⟩, .buf ⟨wa, wo, 2048⟩])) ht).isSome
      = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hseed : ∀ s₀ s₀' s s', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Spec.MlDsa.rejBoundedLeak η (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 66⟩) 66) =
        Spec.MlDsa.rejBoundedLeak η (Spec.Sha3.bytesAt s'.mem (Buf.addr s₀' ⟨da, dO, 66⟩) 66))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame (FR s₀ [⟨aa, ao, 1024⟩, ⟨wa, wo, 2048⟩] 80) s.mem s'.mem →
      (s'.gpr .eax = 1 → Reduced s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) →
      Spec.MlDsa.Outcome (fun b => (Spec.MlDsa.rejBoundedPoly η b.rejBounded
        (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 66⟩) 66)).map Spec.MlDsa.toRq) (s'.gpr .eax)
        (polyAt s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (VG.Impl.MlDsa.X86.KeyGen.callPR Y.sc "vg_mldsa_rej_bounded_poly" c
        [.buf ⟨da, dO, 66⟩, .imm η, .buf ⟨aa, ao, 1024⟩, .buf ⟨wa, wo, 2048⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨hD, hAw⟩, hW⟩, dDA⟩, dDW⟩, dAW⟩ := hk
  have hA₁ := (Lay.okW_iff.mp hAw).1
  have hW₁ := (Lay.okW_iff.mp hW).1
  have hη' : η < 2 ^ 32 := by omega
  have eη : (BitVec.ofNat 32 η).toNat = η := VG.Proof.MlDsa.X86.KeyGen.toNat_ofNat32 hη'
  refine VG.Proof.MlDsa.X86.KeyGen.callPR_piece _ [⟨da, dO, 66⟩] [⟨aa, ao, 1024⟩, ⟨wa, wo, 2048⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hD, hA₁, hW₁, hη']) hN (by simp [hD]) (by simp [hAw, hW]) tt hA
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, g₂, post⟩ => ?_)
  · obtain ⟨b₁, b₂, b₃, b₄⟩ := he.buf hp hN (by simp) hD hK
    obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hA₁ hK
    obtain ⟨w₁, w₂, w₃, w₄⟩ := he.buf hp hN (by simp) hW₁ hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hD hA₁ dDA
    have d₂ := Buf.disj hp hD hW₁ dDW
    have d₃ := Buf.disj hp hA₁ hW₁ dAW
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, eη] at *
    ent_pre
  · obtain ⟨esp, ags⟩ := VG.Proof.MlDsa.X86.KeyGen.call_pubs _ hq (by simp [Arg.ok, hD, hA₁, hW₁, hη']) he he'
    have hs := hseed s₀ s₀' s s' hp hp' hq ha ha'
    have a₀ := he.arg 0 (by simp)
    have a₀' := he'.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    rw [← Proof.MlKem.bytesAt_congr (he.mem _ hD), ← Proof.MlKem.bytesAt_congr (he'.mem _ hD)] at hs
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Arg.val] at a₀ a₀' a₁
    simp only [Buf.addr, ← a₀, ← a₀'] at hs
    simp only [arg_withRegions]
    refine ⟨esp, ?_, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp), ags 3 (by simp)⟩
    rw [← ags 1 (by simp), a₁, eη, hs]
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂, g₂, VG.Proof.MlDsa.X86.KeyGen.sw_app,
      eη] at post
    rw [Proof.MlKem.bytesAt_congr (he.mem _ hD)] at post
    exact hQ s₀ s s' hp ha h' fr post.1 post.2

/-! ## Packing: `vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack` -/

theorem sbp_bounds : ∀ b ∈ Spec.MlDsa.simpleBitPackBounds, b < 2 ^ 32 ∧ 32 * Spec.MlDsa.bitlen b < 2 ^ 32 := by
  decide

theorem sbp_piece {c : Prog isa} (hc : VG.Proof.MlDsa.X86.KeyGen.Callee c fun stk => Spec.MlDsa.simpleBitPackContract X86.abi stk)
    (fa fo b oa oo L : Nat) (hb : b ∈ Spec.MlDsa.simpleBitPackBounds) (hL : L = 32 * Spec.MlDsa.bitlen b)
    (hk : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, L⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, L⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨fa, fo, 1024⟩, .imm b, .buf ⟨oa, oo, L⟩, .imm L])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧
      ∀ i < Spec.MlDsa.n, (Spec.MlDsa.coeffAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) i).toNat ≤ b)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → Frame (FR s₀ [⟨oa, oo, L⟩] 80) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, L⟩) L =
        Spec.MlDsa.simpleBitPack (Spec.MlDsa.natPolyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) b → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (VG.Impl.MlDsa.X86.KeyGen.callP Y.sc "vg_mldsa_simple_bit_pack" c [.buf ⟨fa, fo, 1024⟩, .imm b, .buf ⟨oa, oo, L⟩, .imm L]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hF, hOw⟩, dFO⟩ := hk
  have hO := (Lay.okW_iff.mp hOw).1
  obtain ⟨hb', hL'⟩ := VG.Proof.MlDsa.X86.KeyGen.sbp_bounds b hb
  rw [← hL] at hL'
  have eb : (BitVec.ofNat 32 b).toNat = b := VG.Proof.MlDsa.X86.KeyGen.toNat_ofNat32 hb'
  have eL : (BitVec.ofNat 32 L).toNat = L := VG.Proof.MlDsa.X86.KeyGen.toNat_ofNat32 hL'
  refine VG.Proof.MlDsa.X86.KeyGen.callP_piece _ [⟨fa, fo, 1024⟩] [⟨oa, oo, L⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hF, hO, hb', hL']) hN (by simp [hF]) (by simp [hOw]) tt (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF hK
    obtain ⟨o₁, o₂, o₃, o₄⟩ := he.buf hp hN (by simp) hO hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hF hO dFO
    have cb : ∀ i < Spec.MlDsa.n, (Spec.MlDsa.coeffAt e.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) i).toNat ≤ b :=
      fun i hi => by rw [Proof.MlDsa.KeyGen.coeffAt_congr (he.mem _ hF) hi]; exact (hA s₀ s hp ha).2 i hi
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.simpleBitPackContract, Spec.MlDsa.simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, eb, eL] at *
    have := hb
    have := hL
    ent_pre
  · obtain ⟨esp, ags⟩ := VG.Proof.MlDsa.X86.KeyGen.call_pubs _ hq (by simp [Arg.ok, hF, hO, hb', hL']) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.simpleBitPackContract, Spec.MlDsa.simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp), ags 3 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.simpleBitPackContract, Spec.MlDsa.simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, a₃, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂, eb,
      eL] at post
    rw [Proof.MlDsa.KeyGen.natPolyAt_congr (he.mem _ hF)] at post
    exact hQ s₀ s s' hp ha h' fr post


theorem bp_bounds : ∀ ab ∈ Spec.MlDsa.bitPackParams, ab.1 < 2 ^ 32 ∧ ab.2 < 2 ^ 32 ∧
    32 * Spec.MlDsa.bitlen (ab.1 + ab.2) < 2 ^ 32 := by
  decide

theorem bp_piece {c : Prog isa} (hc : VG.Proof.MlDsa.X86.KeyGen.Callee c fun stk => Spec.MlDsa.bitPackContract X86.abi stk)
    (fa fo a b oa oo L : Nat) (hab : (a, b) ∈ Spec.MlDsa.bitPackParams) (hL : L = 32 * Spec.MlDsa.bitlen (a + b))
    (hk : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, L⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, L⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨fa, fo, 1024⟩, .imm a, .imm b, .buf ⟨oa, oo, L⟩, .imm L])) ht).isSome
      = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      ∀ i < Spec.MlDsa.n, -(a : Int) ≤ Spec.MlDsa.modPm (Spec.MlDsa.coeffAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) i).toNat
        Spec.MlDsa.q ∧
        Spec.MlDsa.modPm (Spec.MlDsa.coeffAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) i).toNat Spec.MlDsa.q ≤ b)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → Frame (FR s₀ [⟨oa, oo, L⟩] 80) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, L⟩) L =
        Spec.MlDsa.bitPack ((polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)).map fun c => Spec.MlDsa.modPm c.val Spec.MlDsa.q)
          a b → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (VG.Impl.MlDsa.X86.KeyGen.callP Y.sc "vg_mldsa_bit_pack" c [.buf ⟨fa, fo, 1024⟩, .imm a, .imm b, .buf ⟨oa, oo, L⟩, .imm L]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hF, hOw⟩, dFO⟩ := hk
  have hO := (Lay.okW_iff.mp hOw).1
  obtain ⟨hav, hbv, hL'⟩ := VG.Proof.MlDsa.X86.KeyGen.bp_bounds (a, b) hab
  rw [← hL] at hL'
  have ea : (BitVec.ofNat 32 a).toNat = a := VG.Proof.MlDsa.X86.KeyGen.toNat_ofNat32 hav
  have eb : (BitVec.ofNat 32 b).toNat = b := VG.Proof.MlDsa.X86.KeyGen.toNat_ofNat32 hbv
  have eL : (BitVec.ofNat 32 L).toNat = L := VG.Proof.MlDsa.X86.KeyGen.toNat_ofNat32 hL'
  refine VG.Proof.MlDsa.X86.KeyGen.callP_piece _ [⟨fa, fo, 1024⟩] [⟨oa, oo, L⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hF, hO, hav, hbv, hL']) hN (by simp [hF]) (by simp [hOw]) tt
    (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF hK
    obtain ⟨o₁, o₂, o₃, o₄⟩ := he.buf hp hN (by simp) hO hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hF hO dFO
    have rf := VG.Proof.MlDsa.X86.KeyGen.ent_reduced he hF (hA s₀ s hp ha).2.1
    have cb : ∀ i < Spec.MlDsa.n, -(a : Int) ≤ Spec.MlDsa.modPm (Spec.MlDsa.coeffAt e.mem
        (Buf.addr s₀ ⟨fa, fo, 1024⟩) i).toNat Spec.MlDsa.q ∧
        Spec.MlDsa.modPm (Spec.MlDsa.coeffAt e.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) i).toNat Spec.MlDsa.q ≤ b :=
      fun i hi => by rw [Proof.MlDsa.KeyGen.coeffAt_congr (he.mem _ hF) hi]; exact (hA s₀ s hp ha).2.2 i hi
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have a₄ := he.arg 4 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.bitPackContract, Spec.MlDsa.bitPackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, a₄, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, ea, eb,
      eL] at *
    have := hab
    have := hL
    ent_pre
  · obtain ⟨esp, ags⟩ := VG.Proof.MlDsa.X86.KeyGen.call_pubs _ hq (by simp [Arg.ok, hF, hO, hav, hbv, hL']) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.bitPackContract, Spec.MlDsa.bitPackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp), ags 3 (by simp), ags 4 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have a₄ := he.arg 4 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.bitPackContract, Spec.MlDsa.bitPackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, a₃, a₄, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂,
      ea, eb, eL] at post
    rw [VG.Proof.MlDsa.X86.KeyGen.ent_polyAt he hF] at post
    exact hQ s₀ s s' hp ha h' fr post

end VG.Proof.MlDsa.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Lay`. -/
section

/-!
# ML-DSA key generation on x86 (32-bit): parameters and layout

What the proof uses of a parameter set (`PFacts`), the layout of key
generation's arguments (`YK p`: `seed`, `pk`, `sk` and `scratch`, and 96 bytes
of stack), and the tactic `lay`, which proves the checks of buffers against a
layout (`Lay.ok`, `Lay.sep`, `Lay.apart`, …) whose offsets depend on the
parameters and on indices, by unfolding them into arithmetic for `omega`.
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)

/-- What the proof uses of a parameter set. -/
structure PFacts (p : Params) : Prop where
  k : 1 ≤ p.k ∧ p.k ≤ 8
  l : 1 ≤ p.ℓ ∧ p.ℓ ≤ 7
  kl : p.k * p.ℓ ≤ 56
  eta : (p.η = 2 ∧ lenS p = 96) ∨ (p.η = 4 ∧ lenS p = 128)
  pk : p.pkLen = 32 + 320 * p.k
  sk : p.skLen = oT0 p + 416 * p.k
  sw : scratchWords p = 128 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32)

theorem pfacts {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : VG.Proof.MlDsa.X86.KeyGen.PFacts p := by
  rcases hp with rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩

/-- The size of `scratch`, in bytes. -/
abbrev scrLen (p : Params) : Nat := scratchWords p * 8

/-- `seed` (32 bytes, read), `pk`, `sk` and `scratch` (written); 96 bytes of stack. -/
def YK (p : Params) : VG.Proof.MlKem.X86.Top.Lay := ⟨[(32, false), (p.pkLen, true), (p.skLen, true), (VG.Proof.MlDsa.X86.KeyGen.scrLen p, true)], 3, 96⟩

theorem YK_sc (p : Params) : (VG.Proof.MlDsa.X86.KeyGen.YK p).sc = kS := rfl
theorem YK_stk (p : Params) : (VG.Proof.MlDsa.X86.KeyGen.YK p).stk = 96 := rfl
theorem stkN {p : Params} {N : Nat} (h : N + 16 ≤ 96) : N + 16 ≤ (VG.Proof.MlDsa.X86.KeyGen.YK p).stk := h
theorem YK_n (p : Params) : (VG.Proof.MlDsa.X86.KeyGen.YK p).n = 4 := rfl
theorem YK_alen0 (p : Params) : (VG.Proof.MlDsa.X86.KeyGen.YK p).alen 0 = 32 := rfl
theorem YK_alen1 (p : Params) : (VG.Proof.MlDsa.X86.KeyGen.YK p).alen 1 = p.pkLen := rfl
theorem YK_alen2 (p : Params) : (VG.Proof.MlDsa.X86.KeyGen.YK p).alen 2 = p.skLen := rfl
theorem YK_alen3 (p : Params) : (VG.Proof.MlDsa.X86.KeyGen.YK p).alen 3 = VG.Proof.MlDsa.X86.KeyGen.scrLen p := rfl
theorem YK_awr0 (p : Params) : (VG.Proof.MlDsa.X86.KeyGen.YK p).awr 0 = false := rfl
theorem YK_awr1 (p : Params) : (VG.Proof.MlDsa.X86.KeyGen.YK p).awr 1 = true := rfl
theorem YK_awr2 (p : Params) : (VG.Proof.MlDsa.X86.KeyGen.YK p).awr 2 = true := rfl
theorem YK_awr3 (p : Params) : (VG.Proof.MlDsa.X86.KeyGen.YK p).awr 3 = true := rfl

/-- Unfolds checks of buffers against a layout into arithmetic, then `omega`. -/
syntax "lay" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| lay) => `(tactic| lay [])
  | `(tactic| lay [$ls,*]) => `(tactic| (
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [VG.Proof.MlKem.X86.Top.Lay.apart, VG.Proof.MlKem.X86.Top.Lay.ok,
        VG.Proof.MlKem.X86.Top.Lay.okW, VG.Proof.MlKem.X86.Top.Lay.sep, VG.Impl.MlDsa.X86.KeyGen.Arg.ok, VG.Impl.MlDsa.X86.KeyGen.sb,
        VG.Impl.MlDsa.X86.KeyGen.pB, VG.Impl.MlDsa.X86.KeyGen.aB, VG.Impl.MlDsa.X86.KeyGen.sB,
        VG.Impl.MlDsa.X86.KeyGen.tB, VG.Impl.MlDsa.X86.KeyGen.t1B, VG.Impl.MlDsa.X86.KeyGen.t0B,
        VG.Impl.MlDsa.X86.KeyGen.ssB, VG.Impl.MlDsa.X86.KeyGen.kS,
        VG.Proof.MlDsa.X86.KeyGen.YK_n, VG.Proof.MlDsa.X86.KeyGen.YK_sc,
        VG.Proof.MlDsa.X86.KeyGen.YK_alen0, VG.Proof.MlDsa.X86.KeyGen.YK_alen1,
        VG.Proof.MlDsa.X86.KeyGen.YK_alen2, VG.Proof.MlDsa.X86.KeyGen.YK_alen3,
        VG.Proof.MlDsa.X86.KeyGen.YK_awr0, VG.Proof.MlDsa.X86.KeyGen.YK_awr1,
        VG.Proof.MlDsa.X86.KeyGen.YK_awr2, VG.Proof.MlDsa.X86.KeyGen.YK_awr3,
        List.all_cons, List.all_nil, List.length_cons, List.length_nil, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq, Bool.and_true, Bool.true_and, Bool.true_or, Bool.or_true, true_and, and_true,
        true_or, or_true, ↓reduceIte, $ls,*]
      set_option linter.unusedSimpArgs false in
      all_goals try simp only [VG.Proof.MlDsa.X86.KeyGen.scrLen, VG.Impl.MlDsa.X86.KeyGen.oP,
        VG.Impl.MlDsa.X86.KeyGen.oSA, VG.Impl.MlDsa.X86.KeyGen.oSB, VG.Impl.MlDsa.X86.KeyGen.oHX,
        VG.Impl.MlDsa.X86.KeyGen.oKL, VG.Impl.MlDsa.X86.KeyGen.oACC, VG.Impl.MlDsa.X86.KeyGen.oSS,
        VG.Impl.MlDsa.X86.KeyGen.oT0, decide_eq_true_eq, $ls,*]
      all_goals (and_intros <;> omega_arith)))

/-- `lay`, with the facts of the parameter set `hF : PFacts p`: for any `η` if the check does not
depend on it, and otherwise in each case of `η`. -/
syntax "layp " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| layp $hF) => `(tactic| layp $hF [])
  | `(tactic| layp $hF [$ls,*]) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl
      first
        | lay [($hF).pk, ($hF).sk, ($hF).sw, $ls,*]
        | rcases ($hF).eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
            lay [hlen, ($hF).pk, ($hF).sk, ($hF).sw, $ls,*]))

end VG.Proof.MlDsa.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Base`. -/
section

/-!
# ML-DSA key generation on x86 (32-bit): the setting

Key generation is proven for any implementations of the primitives it calls
that are verified against their contracts (`PrimsOk`), as ML-KEM's top-level
functions on x86 (`Proof/MlKem/X86/`): the contract's precondition gives the
layout of the arguments (`pre_of`), and its public data the pointers and what
key generation may leak, as bytes (`lkK`, `pub_of`). `ξ` gives `(ρ, ρ′, K)`
(`hxOf`), which the body keeps in `scratch` (`KB`).
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds keyGenLeak integerToBytes)
open VG.Spec.Sha3 (bytesAt)

/-- Verified implementations of the primitives key generation calls. -/
structure PrimsOk (P : Prims) : Prop where
  ntt : VG.Proof.MlDsa.X86.KeyGen.Callee P.ntt (fun stk => Spec.MlDsa.nttContract X86.abi stk)
  invNtt : VG.Proof.MlDsa.X86.KeyGen.Callee P.invNtt (fun stk => Spec.MlDsa.nttInvContract X86.abi stk)
  mul : VG.Proof.MlDsa.X86.KeyGen.Callee P.mul (fun stk => Spec.MlDsa.mulContract X86.abi stk)
  mulAdd : VG.Proof.MlDsa.X86.KeyGen.Callee P.mulAdd (fun stk => Spec.MlDsa.mulAddContract X86.abi stk)
  add : VG.Proof.MlDsa.X86.KeyGen.Callee P.add (fun stk => Spec.MlDsa.addContract X86.abi stk)
  rejNtt : VG.Proof.MlDsa.X86.KeyGen.Callee P.rejNtt (fun stk => Spec.MlDsa.rejNTTContract X86.abi stk)
  rejBounded : VG.Proof.MlDsa.X86.KeyGen.Callee P.rejBounded (fun stk => Spec.MlDsa.rejBoundedContract X86.abi stk)
  power2Round : VG.Proof.MlDsa.X86.KeyGen.Callee P.power2Round (fun stk => Spec.MlDsa.power2RoundContract X86.abi stk)
  simpleBitPack : VG.Proof.MlDsa.X86.KeyGen.Callee P.simpleBitPack (fun stk => Spec.MlDsa.simpleBitPackContract X86.abi stk)
  bitPack : VG.Proof.MlDsa.X86.KeyGen.Callee P.bitPack (fun stk => Spec.MlDsa.bitPackContract X86.abi stk)

section
variable (p : Params) (s₀ : State)

/-- `ξ`. -/
abbrev xiOf : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, 32⟩) 32
/-- `H(ξ ‖ k ‖ ℓ, 128)`. -/
abbrev hxOf : List Byte := Spec.MlDsa.H (VG.Proof.MlDsa.X86.KeyGen.xiOf s₀ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128
/-- `ρ`, `ρ′` and `K`. -/
abbrev rhoOf : List Byte := (keyGenSeeds p (VG.Proof.MlDsa.X86.KeyGen.xiOf s₀)).1
abbrev rho'Of : List Byte := (keyGenSeeds p (VG.Proof.MlDsa.X86.KeyGen.xiOf s₀)).2.1
abbrev kOf : List Byte := (keyGenSeeds p (VG.Proof.MlDsa.X86.KeyGen.xiOf s₀)).2.2
/-- What key generation may leak, as bytes. -/
def lkK : List Byte := (keyGenLeak p (VG.Proof.MlDsa.X86.KeyGen.xiOf s₀)).map (BitVec.ofNat 8)
/-- The AND of the samplers' results. -/
abbrev accV (s : State) : BitVec 32 := s.mem.readW (Buf.addr s₀ (sb oACC 4)) 32

end

/-- A piece of key generation. -/
abbrev KP (p : Params) := Piece (TPre (VG.Proof.MlDsa.X86.KeyGen.YK p)) (TPub (VG.Proof.MlDsa.X86.KeyGen.YK p) (VG.Proof.MlDsa.X86.KeyGen.lkK p))

theorem addr0 (s₀ : State) (i : Nat) (l : Nat) : Buf.addr s₀ ⟨i, 0, l⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

/-! ## The contract -/

theorem pre_of {p : Params} {s₀ : State} (h : (Spec.MlDsa.keyGenContract p X86.abi 96).pre s₀) :
    TPre (VG.Proof.MlDsa.X86.KeyGen.YK p) s₀ := by
  sig_pre [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 96#64, 96⟩ : Region) = below (E0 s₀) 96 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h20 h21 h22 h23 h24
  have c4 : ∀ i, i < (VG.Proof.MlDsa.X86.KeyGen.YK p).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by
    rw [VG.Proof.MlDsa.X86.KeyGen.YK_n] at hi; omega
  refine ⟨h1, by rw [VG.Proof.MlDsa.X86.KeyGen.YK_stk]; omega, by rw [VG.Proof.MlDsa.X86.KeyGen.YK_n]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h24, ?_, by rw [VG.Proof.MlDsa.X86.KeyGen.YK_sc, VG.Proof.MlDsa.X86.KeyGen.YK_n]; decide⟩
  · intro i hi hw
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · rw [h3]; exact List.mem_singleton_self _
    all_goals simp [VG.Proof.MlDsa.X86.KeyGen.YK, Lay.awr] at hw
  · intro i hi hw
    rw [h4]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · simp [VG.Proof.MlDsa.X86.KeyGen.YK, Lay.awr] at hw
    all_goals simp [VG.Proof.MlKem.X86.Top.argR, Lay.alen, VG.Proof.MlDsa.X86.KeyGen.YK, VG.Proof.MlDsa.X86.KeyGen.scrLen]
  · rw [h4]; simp [VG.Proof.MlKem.X86.Top.gR, Lay.n, VG.Proof.MlDsa.X86.KeyGen.YK]
  · intro i hi j hj hne _
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> rcases c4 j hj with rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | skip
    all_goals simp only [VG.Proof.MlKem.X86.Top.argR, VG.Proof.MlDsa.X86.KeyGen.YK_alen0, VG.Proof.MlDsa.X86.KeyGen.YK_alen1, VG.Proof.MlDsa.X86.KeyGen.YK_alen2, VG.Proof.MlDsa.X86.KeyGen.YK_alen3, VG.Proof.MlDsa.X86.KeyGen.scrLen]
    exacts [h5, h6, h7, h5.symm, h9, h10, h6.symm, h9.symm, h12, h7.symm, h10.symm, h12.symm]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> simp only [VG.Proof.MlKem.X86.Top.argR, VG.Proof.MlKem.X86.Top.gR, VG.Proof.MlDsa.X86.KeyGen.YK_n, VG.Proof.MlDsa.X86.KeyGen.YK_alen0, VG.Proof.MlDsa.X86.KeyGen.YK_alen1, VG.Proof.MlDsa.X86.KeyGen.YK_alen2, VG.Proof.MlDsa.X86.KeyGen.YK_alen3, VG.Proof.MlDsa.X86.KeyGen.scrLen]
    · exact h8.symm
    · exact h11.symm
    · exact h13.symm
    · exact h14.symm
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> simp only [VG.Proof.MlKem.X86.Top.argR, VG.Proof.MlDsa.X86.KeyGen.YK_alen0, VG.Proof.MlDsa.X86.KeyGen.YK_alen1, VG.Proof.MlDsa.X86.KeyGen.YK_alen2, VG.Proof.MlDsa.X86.KeyGen.YK_alen3, VG.Proof.MlDsa.X86.KeyGen.scrLen]
    · exact h15
    · exact h16
    · exact h17
    · exact h18
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> simp only [VG.Proof.MlKem.X86.Top.argR, VG.Proof.MlDsa.X86.KeyGen.YK_stk, VG.Proof.MlDsa.X86.KeyGen.YK_alen0, VG.Proof.MlDsa.X86.KeyGen.YK_alen1, VG.Proof.MlDsa.X86.KeyGen.YK_alen2, VG.Proof.MlDsa.X86.KeyGen.YK_alen3, VG.Proof.MlDsa.X86.KeyGen.scrLen]
    · exact h20
    · exact h21
    · exact h22
    · exact h23
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> simp only [VG.Proof.MlDsa.X86.KeyGen.YK_alen0, VG.Proof.MlDsa.X86.KeyGen.YK_alen1, VG.Proof.MlDsa.X86.KeyGen.YK_alen2, VG.Proof.MlDsa.X86.KeyGen.YK_alen3, VG.Proof.MlDsa.X86.KeyGen.scrLen]
    · exact h25
    · exact h26
    · exact h27
    · exact h28

theorem pub_of {p : Params} {s₀ s₀' : State} (h : (Spec.MlDsa.keyGenContract p X86.abi 96).pub s₀ s₀') :
    TPub (VG.Proof.MlDsa.X86.KeyGen.YK p) (VG.Proof.MlDsa.X86.KeyGen.lkK p) s₀ s₀' := by
  sig_pub [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · rw [VG.Proof.MlDsa.X86.KeyGen.YK_n] at hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    exacts [e₃, e₄, e₅, e₆]
  · simp only [VG.Proof.MlDsa.X86.KeyGen.lkK, VG.Proof.MlDsa.X86.KeyGen.xiOf, VG.Proof.MlDsa.X86.KeyGen.addr0]
    rw [e₂]

/-- Two runs agree on `ρ`, and on what each `RejBoundedPoly` of `ExpandS` leaks. -/
theorem TPub.leak {p : Params} {s₀ s₀' : State} (hq : TPub (VG.Proof.MlDsa.X86.KeyGen.YK p) (VG.Proof.MlDsa.X86.KeyGen.lkK p) s₀ s₀') :
    VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀ = VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀' ∧ ∀ r < p.ℓ + p.k, Spec.MlDsa.rejBoundedLeak p.η (Proof.MlDsa.KeyGen.seedS (VG.Proof.MlDsa.X86.KeyGen.rho'Of p s₀) r) =
      Spec.MlDsa.rejBoundedLeak p.η (Proof.MlDsa.KeyGen.seedS (VG.Proof.MlDsa.X86.KeyGen.rho'Of p s₀') r) :=
  Proof.MlDsa.KeyGen.keyGenLeak_split (Proof.MlDsa.KeyGen.keyGenLeak_bytes hq.2.2)

end VG.Proof.MlDsa.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Inv`. -/
section

/-!
# ML-DSA key generation on x86 (32-bit): what holds between the pieces

After the seeds, `scratch` holds `(ρ, ρ′, K)` and the seeds of the samplers
(`KB`); after the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`, the
polynomials sampled, reduced (and small), and the AND of the samplers'
results, which is 1 if they are those of the standard for some bounds, and 0
if key generation fails within the least bounds (`Good`, `KSamp`). Each is
kept by a piece that writes only buffers apart from those it describes
(`KB.keep`, `KSamp.keep`).
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly Bounds minBounds rejNTTPoly rejBoundedPoly keyGenInternal toRq polyAt
  Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (seedA seedS)
open VG.Spec.Sha3 (bytesAt)

/-! ## Bytes -/

theorem st8_bytes (s₀ : State) (m : Mem) (sc o v : Nat) :
    bytesAt (m.writeW (Buf.addr s₀ ⟨sc, o, 1⟩) ((BitVec.ofNat 32 v).setWidth 8)) (Buf.addr s₀ ⟨sc, o, 1⟩) 1 =
      [BitVec.ofNat 8 v] := by
  refine Proof.MlKem.bytesAt_eq (L := [BitVec.ofNat 8 v]) rfl fun i hi => ?_
  obtain rfl : i = 0 := by omega
  simp only [BitVec.add_zero, Proof.MlKem.writeW8_apply, List.getElem_cons_zero, ite_true]
  rw [BitVec.setWidth_ofNat_of_le (by decide)]

/-- The bytes of a part of a buffer. -/
theorem bytes_sub {Y : VG.Proof.MlKem.X86.Top.Lay} {s₀ : State} (hp : TPre Y s₀) (m : Mem) {a o L k c : Nat} (hkc : k + c ≤ L)
    (h₁ : Y.ok ⟨a, o, L⟩ = true) (h₂ : Y.ok ⟨a, o + k, c⟩ = true) :
    bytesAt m (Buf.addr s₀ ⟨a, o + k, c⟩) c = ((bytesAt m (Buf.addr s₀ ⟨a, o, L⟩) L).drop k).take c := by
  rw [Proof.MlKem.bytesAt_slice _ _ hkc, Buf.addr_eq hp h₁, Buf.addr_eq hp h₂, BitVec.add_assoc,
    ← BitVec.ofNat_add]

/-- The bytes of two adjacent buffers. -/
theorem bytes_cat {Y : VG.Proof.MlKem.X86.Top.Lay} {s₀ : State} (hp : TPre Y s₀) (m : Mem) {a o l₁ l₂ : Nat}
    (h₂ : Y.ok ⟨a, o + l₁, l₂⟩ = true) (h : Y.ok ⟨a, o, l₁ + l₂⟩ = true) :
    bytesAt m (Buf.addr s₀ ⟨a, o, l₁ + l₂⟩) (l₁ + l₂) =
      bytesAt m (Buf.addr s₀ ⟨a, o, l₁⟩) l₁ ++ bytesAt m (Buf.addr s₀ ⟨a, o + l₁, l₂⟩) l₂ := by
  have e : Buf.addr s₀ ⟨a, o + l₁, l₂⟩ = Buf.addr s₀ ⟨a, o, l₁ + l₂⟩ + BitVec.ofNat 64 l₁ := by
    rw [Buf.addr_eq hp h₂, Buf.addr_eq hp h, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [Proof.MlKem.bytesAt_add, e]

/-- An ML-DSA polynomial apart from what a piece writes. -/
theorem keepPolyD {Y : VG.Proof.MlKem.X86.Top.Lay} {s₀ : State} (hp : TPre Y s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ Y.stk)
    {a o : Nat} (hs : Y.apart ⟨a, o, 1024⟩ bs = true) {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {f : VG.Spec.MlDsa.Poly}
    (h : PolyIs m (Buf.addr s₀ ⟨a, o, 1024⟩) f) : PolyIs m' (Buf.addr s₀ ⟨a, o, 1024⟩) f :=
  Proof.MlDsa.KeyGen.polyIs_congr (Top.keep hp hN hs fr) h

theorem keepRedD {Y : VG.Proof.MlKem.X86.Top.Lay} {s₀ : State} (hp : TPre Y s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ Y.stk)
    {a o : Nat} (hs : Y.apart ⟨a, o, 1024⟩ bs = true) {m m' : Mem} (fr : Frame (FR s₀ bs N) m m')
    (h : Reduced m (Buf.addr s₀ ⟨a, o, 1024⟩)) : Reduced m' (Buf.addr s₀ ⟨a, o, 1024⟩) :=
  Proof.MlDsa.KeyGen.reduced_congr (Top.keep hp hN hs fr) h

theorem keepPolyAtD {Y : VG.Proof.MlKem.X86.Top.Lay} {s₀ : State} (hp : TPre Y s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ Y.stk)
    {a o : Nat} (hs : Y.apart ⟨a, o, 1024⟩ bs = true) {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') :
    polyAt m' (Buf.addr s₀ ⟨a, o, 1024⟩) = polyAt m (Buf.addr s₀ ⟨a, o, 1024⟩) :=
  Proof.MlDsa.KeyGen.polyAt_congr (Top.keep hp hN hs fr)

/-! ## After the seeds -/

section
variable (p : Params) (s₀ : State)

/-- `(ρ, ρ′, K)`, `ρ` and `ρ′ ‖ · ‖ 0` in `scratch`. -/
structure KB (s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.KeyGen.YK p) s₀ s
  hx : bytesAt s.mem (Buf.addr s₀ (sb oHX 128)) 128 = VG.Proof.MlDsa.X86.KeyGen.hxOf p s₀
  sa : bytesAt s.mem (Buf.addr s₀ (sb oSA 32)) 32 = VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀
  sbb : bytesAt s.mem (Buf.addr s₀ (sb oSB 64)) 64 = VG.Proof.MlDsa.X86.KeyGen.rho'Of p s₀
  z : bytesAt s.mem (Buf.addr s₀ (sb (oSB + 65) 1)) 1 = [0]

/-- The buffers of `KB` are apart from `bs`. -/
def safeKB (bs : List Buf) : Bool :=
  (VG.Proof.MlDsa.X86.KeyGen.YK p).apart (sb oHX 128) bs && (VG.Proof.MlDsa.X86.KeyGen.YK p).apart (sb oSA 32) bs && (VG.Proof.MlDsa.X86.KeyGen.YK p).apart (sb oSB 64) bs &&
    (VG.Proof.MlDsa.X86.KeyGen.YK p).apart (sb (oSB + 65) 1) bs

end

theorem KB.keep {p : Params} {s₀ s s' : State} (h : VG.Proof.MlDsa.X86.KeyGen.KB p s₀ s) (hp : TPre (VG.Proof.MlDsa.X86.KeyGen.YK p) s₀) {bs : List Buf} {N : Nat}
    (hN : N + 16 ≤ 96) (hs : VG.Proof.MlDsa.X86.KeyGen.safeKB p bs = true) (fr : Frame (FR s₀ bs N) s.mem s'.mem) (h' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.KeyGen.YK p) s₀ s') :
    VG.Proof.MlDsa.X86.KeyGen.KB p s₀ s' := by
  simp only [VG.Proof.MlDsa.X86.KeyGen.safeKB, Bool.and_eq_true] at hs
  obtain ⟨⟨⟨s₁, s₂⟩, s₃⟩, s₄⟩ := hs
  exact ⟨h', by rw [keepBytes hp hN s₁ fr]; exact h.hx, by rw [keepBytes hp hN s₂ fr]; exact h.sa,
    by rw [keepBytes hp hN s₃ fr]; exact h.sbb, by rw [keepBytes hp hN s₄ fr]; exact h.z⟩

/-! ## The samplers -/

/-- The coefficients of `x` are in `[-η, η]`. -/
def Small (η : Nat) (x : IPoly) : Prop := ∀ c ∈ x.toList, -(η : Int) ≤ c ∧ c ≤ η

/-- The AND `v` of the samplers' results after the first `e` entries of `Â` and
`r` of `s₁ ‖ s₂`: 1 if they are those of the standard, `A` and `S`, for some
bounds; 0 if key generation fails within the least bounds. -/
def Good (p : Params) (s₀ : State) (e r : Nat) (A : Nat → VG.Spec.MlDsa.Poly) (S : Nat → IPoly) (v : BitVec 32) : Prop :=
  (v = 1 ∧ ∃ b : Bounds, (∀ e' < e, rejNTTPoly b.rejNTT (seedA (VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀) (e' / p.ℓ) (e' % p.ℓ)) = some (A e')) ∧
      ∀ r' < r, rejBoundedPoly p.η b.rejBounded (seedS (VG.Proof.MlDsa.X86.KeyGen.rho'Of p s₀) r') = some (S r')) ∨
    (v = 0 ∧ keyGenInternal p minBounds (VG.Proof.MlDsa.X86.KeyGen.xiOf s₀) = none)

theorem good_01 {p : Params} {s₀ : State} {e r : Nat} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {v : BitVec 32}
    (h : VG.Proof.MlDsa.X86.KeyGen.Good p s₀ e r A S v) : v = 0 ∨ v = 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inr h, .inl h]

/-- After the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`. -/
structure KSamp (p : Params) (e r : Nat) (s₀ s : State) : Prop where
  kb : VG.Proof.MlDsa.X86.KeyGen.KB p s₀ s
  ex : ∃ (A : Nat → VG.Spec.MlDsa.Poly) (S : Nat → IPoly), (∀ e' < e, PolyIs s.mem (Buf.addr s₀ (aB e')) (A e')) ∧
    (∀ r' < r, PolyIs s.mem (Buf.addr s₀ (VG.Impl.MlDsa.X86.KeyGen.sB p r')) (toRq (S r')) ∧ VG.Proof.MlDsa.X86.KeyGen.Small p.η (S r')) ∧
    VG.Proof.MlDsa.X86.KeyGen.Good p s₀ e r A S (VG.Proof.MlDsa.X86.KeyGen.accV s₀ s)

/-- The buffers of `KSamp` are apart from `bs`. -/
structure SafeS (p : Params) (e r : Nat) (bs : List Buf) : Prop where
  kb : VG.Proof.MlDsa.X86.KeyGen.safeKB p bs = true
  acc : (VG.Proof.MlDsa.X86.KeyGen.YK p).apart (sb oACC 4) bs = true
  a : ∀ e' < e, (VG.Proof.MlDsa.X86.KeyGen.YK p).apart (aB e') bs = true
  s : ∀ r' < r, (VG.Proof.MlDsa.X86.KeyGen.YK p).apart (VG.Impl.MlDsa.X86.KeyGen.sB p r') bs = true

theorem KSamp.keep {p : Params} {e r : Nat} {s₀ s s' : State} (h : VG.Proof.MlDsa.X86.KeyGen.KSamp p e r s₀ s) (hp : TPre (VG.Proof.MlDsa.X86.KeyGen.YK p) s₀)
    {bs : List Buf} {N : Nat} (hN : N + 16 ≤ 96) (hs : VG.Proof.MlDsa.X86.KeyGen.SafeS p e r bs) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (h' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.KeyGen.YK p) s₀ s') : VG.Proof.MlDsa.X86.KeyGen.KSamp p e r s₀ s' := by
  obtain ⟨A, S, hA, hS, hG⟩ := h.ex
  refine ⟨h.kb.keep hp hN hs.kb fr h', A, S, fun e' he' => VG.Proof.MlDsa.X86.KeyGen.keepPolyD hp hN (hs.a e' he') fr (hA e' he'),
    fun r' hr' => ⟨VG.Proof.MlDsa.X86.KeyGen.keepPolyD hp hN (hs.s r' hr') fr (hS r' hr').1, (hS r' hr').2⟩, ?_⟩
  rw [show VG.Proof.MlDsa.X86.KeyGen.accV s₀ s' = VG.Proof.MlDsa.X86.KeyGen.accV s₀ s from keepW hp hN hs.acc fr]
  exact hG

end VG.Proof.MlDsa.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds`. -/
section

/-!
# ML-DSA key generation on x86 (32-bit): the seeds

The AND of the samplers' results set to 1, `(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)`,
`ρ` to the seed of `RejNTTPoly` and `ρ′ ‖ · ‖ 0` to that of `RejBoundedPoly`
(`seeds_piece`, which ends in `KB` with the AND 1).
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds integerToBytes)
open VG.Spec.Sha3 (bytesAt)

/-- SHAKE256 as the sponge functions compute it. -/
theorem sponge_H (m : List Byte) (d : Nat) :
    Spec.Sha3.squeezeFrom 136 (Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 ((BitVec.ofNat 32 0x1f).setWidth 8) m)) 0 d =
      Spec.MlDsa.H m d := by
  rw [show (BitVec.ofNat 32 0x1f).setWidth 8 = Spec.Sha3.shakeSuffix from Proof.MlKem.shakeSuffix32]
  exact (Proof.MlKem.shake256_eq m d).symm

theorem seeds_eq (p : Params) (ξ : List Byte) :
    keyGenSeeds p ξ = ((Spec.MlDsa.H (ξ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128).take 32,
      ((Spec.MlDsa.H (ξ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128).drop 32).take 64,
      ((Spec.MlDsa.H (ξ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128).drop 96).take 32) := rfl

section
variable {p : Params}

/-- After `oACC ← 1`. -/
abbrev A1 (p : Params) (s₀ s : State) : Prop := VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.KeyGen.YK p) s₀ s ∧ VG.Proof.MlDsa.X86.KeyGen.accV s₀ s = 1

theorem acc_keep {s₀ s s' : State} (hp : TPre (VG.Proof.MlDsa.X86.KeyGen.YK p) s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ 96)
    (hs : (VG.Proof.MlDsa.X86.KeyGen.YK p).apart (sb oACC 4) bs = true) (fr : Frame (FR s₀ bs N) s.mem s'.mem) :
    VG.Proof.MlDsa.X86.KeyGen.accV s₀ s' = VG.Proof.MlDsa.X86.KeyGen.accV s₀ s := keepW hp hN hs fr

theorem seeds_piece (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) :
    VG.Proof.MlDsa.X86.KeyGen.KP p (VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.KeyGen.YK p)) (fun s₀ s => VG.Proof.MlDsa.X86.KeyGen.KB p s₀ s ∧ VG.Proof.MlDsa.X86.KeyGen.accV s₀ s = 1) (seeds p) := by
  have hk := hF.k; have hl := hF.l
  unfold seeds
  refine Piece.seq (B := VG.Proof.MlDsa.X86.KeyGen.A1 p) (st32_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) oACC 1 (by layp hF) (by taint_decide) (fun _ _ _ h => h)
    fun s₀ s s' hp _ h' m' => ⟨h', by rw [VG.Proof.MlDsa.X86.KeyGen.accV, m']; exact Mem.readW_writeW_self32 _ _ _⟩) ?_
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.KeyGen.A1 p s₀ s ∧ bytesAt s.mem (Buf.addr s₀ (sb oKL 1)) 1 = [BitVec.ofNat 8 p.k])
    (st8_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) oKL p.k (by layp hF) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1)
      fun s₀ s s' hp h h' m' => ⟨⟨h', by rw [VG.Proof.MlDsa.X86.KeyGen.acc_keep hp (N := 0) (by omega) (by layp hF) (m' ▸ frW8)]; exact h.2⟩,
        by rw [m', VG.Proof.MlDsa.X86.KeyGen.YK_sc]; exact VG.Proof.MlDsa.X86.KeyGen.st8_bytes _ _ _ _ _⟩) ?_
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.KeyGen.A1 p s₀ s ∧ bytesAt s.mem (Buf.addr s₀ (sb oKL 2)) 2 =
      integerToBytes p.k 1 ++ integerToBytes p.ℓ 1)
    (st8_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) (oKL + 1) p.ℓ (by layp hF) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1.1)
      fun s₀ s s' hp h h' m' => ⟨⟨h', by rw [VG.Proof.MlDsa.X86.KeyGen.acc_keep hp (N := 0) (by omega) (by layp hF) (m' ▸ frW8)]; exact h.1.2⟩,
        ?_⟩) ?_
  · rw [VG.Proof.MlDsa.X86.KeyGen.bytes_cat hp _ (l₁ := 1) (l₂ := 1) (by layp hF) (by layp hF), Proof.MlDsa.KeyGen.integerToBytes_one,
      Proof.MlDsa.KeyGen.integerToBytes_one, keepBytes hp (N := 0) (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (by layp hF) (m' ▸ frW8), h.2, m', VG.Proof.MlDsa.X86.KeyGen.YK_sc,
      VG.Proof.MlDsa.X86.KeyGen.st8_bytes]
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.KeyGen.A1 p s₀ s ∧ bytesAt s.mem (Buf.addr s₀ (sb oHX 128)) 128 = VG.Proof.MlDsa.X86.KeyGen.hxOf p s₀)
    (hash2_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) 0 200 136 0x1f ⟨0, 0, 32⟩ (sb oKL 2) (sb oHX 128) Proof.MlKem.rate136 (by layp hF)
      (by rw [VG.Proof.MlDsa.X86.KeyGen.YK_stk]; omega) (by decide) (by decide) (by decide) (by taint_decide)
      (h₁ := .block []) (by kernel_rfl) (h₂ := .block []) (by kernel_rfl) (h₃ := .block []) (by kernel_rfl)
      (h₄ := .block []) (by kernel_rfl) (fun _ _ _ h => h.1.1) fun s₀ s s' hp h h' fr out => ⟨⟨h',
        by rw [VG.Proof.MlDsa.X86.KeyGen.acc_keep hp (N := 40) (by omega) (by layp hF) fr]; exact h.1.2⟩, ?_⟩) ?_
  · rw [out, h.2, Ctx.roBytes hp h.1.1 (b := ⟨0, 0, 32⟩) (by layp hF) rfl, VG.Proof.MlDsa.X86.KeyGen.sponge_H, VG.Proof.MlDsa.X86.KeyGen.hxOf, List.append_assoc]
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.KeyGen.A1 p s₀ s ∧ bytesAt s.mem (Buf.addr s₀ (sb oHX 128)) 128 = VG.Proof.MlDsa.X86.KeyGen.hxOf p s₀ ∧
      bytesAt s.mem (Buf.addr s₀ (sb oSA 32)) 32 = VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀)
    (copyW_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) kS oHX kS oSA 8 (by decide) (by decide) (by layp hF) (h₁ := .block []) (by kernel_rfl)
      (by taint_decide) (fun _ _ _ h => h.1.1) fun s₀ s s' hp h h' fr cp => ⟨⟨h',
        by rw [VG.Proof.MlDsa.X86.KeyGen.acc_keep hp (N := 0) (by omega) (by layp hF) (fr1 fr)]; exact h.1.2⟩,
        by rw [keepBytes hp (N := 0) (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (b := sb oHX 128) (by layp hF) (fr1 fr)]; exact h.2, ?_⟩) ?_
  · show bytesAt s'.mem (Buf.addr s₀ (sb oSA 32)) 32 = _
    rw [cp]
    show bytesAt s.mem (Buf.addr s₀ (sb oHX 32)) 32 = (keyGenSeeds p (VG.Proof.MlDsa.X86.KeyGen.xiOf s₀)).1
    rw [VG.Proof.MlDsa.X86.KeyGen.seeds_eq]
    show _ = (VG.Proof.MlDsa.X86.KeyGen.hxOf p s₀).take 32
    rw [← h.2, Proof.MlKem.bytesAt_take _ _ (by decide)]
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.KeyGen.A1 p s₀ s ∧ bytesAt s.mem (Buf.addr s₀ (sb oHX 128)) 128 = VG.Proof.MlDsa.X86.KeyGen.hxOf p s₀ ∧
      bytesAt s.mem (Buf.addr s₀ (sb oSA 32)) 32 = VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀ ∧
      bytesAt s.mem (Buf.addr s₀ (sb oSB 64)) 64 = VG.Proof.MlDsa.X86.KeyGen.rho'Of p s₀)
    (copyW_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) kS (oHX + 32) kS oSB 16 (by decide) (by decide) (by layp hF) (h₁ := .block [])
      (by kernel_rfl) (by taint_decide) (fun _ _ _ h => h.1.1) fun s₀ s s' hp h h' fr cp => ⟨⟨h',
        by rw [VG.Proof.MlDsa.X86.KeyGen.acc_keep hp (N := 0) (by omega) (by layp hF) (fr1 fr)]; exact h.1.2⟩,
        by rw [keepBytes hp (N := 0) (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (b := sb oHX 128) (by layp hF) (fr1 fr)]; exact h.2.1,
        by rw [keepBytes hp (N := 0) (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (b := sb oSA 32) (by layp hF) (fr1 fr)]; exact h.2.2, ?_⟩) ?_
  · show bytesAt s'.mem (Buf.addr s₀ (sb oSB 64)) 64 = _
    rw [cp]
    show bytesAt s.mem (Buf.addr s₀ (sb (oHX + 32) 64)) 64 = (keyGenSeeds p (VG.Proof.MlDsa.X86.KeyGen.xiOf s₀)).2.1
    rw [VG.Proof.MlDsa.X86.KeyGen.seeds_eq]
    show _ = ((VG.Proof.MlDsa.X86.KeyGen.hxOf p s₀).drop 32).take 64
    rw [← h.2.1, VG.Proof.MlDsa.X86.KeyGen.bytes_sub hp _ (k := 32) (c := 64) (L := 128) (by decide) (by layp hF) (by layp hF)]
  refine st8_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) (oSB + 65) 0 (by layp hF) (by taint_decide) (fun _ _ _ h => h.1.1)
    fun s₀ s s' hp h h' m' => ⟨⟨h', ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [keepBytes hp (N := 0) (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (b := sb oHX 128) (by layp hF) (m' ▸ frW8)]; exact h.2.1
  · rw [keepBytes hp (N := 0) (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (b := sb oSA 32) (by layp hF) (m' ▸ frW8)]; exact h.2.2.1
  · rw [keepBytes hp (N := 0) (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (b := sb oSB 64) (by layp hF) (m' ▸ frW8)]; exact h.2.2.2
  · rw [m', VG.Proof.MlDsa.X86.KeyGen.YK_sc, VG.Proof.MlDsa.X86.KeyGen.st8_bytes]; rfl
  · rw [VG.Proof.MlDsa.X86.KeyGen.acc_keep hp (N := 0) (by omega) (by layp hF) (m' ▸ frW8)]; exact h.1.2

end

end VG.Proof.MlDsa.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Samp`. -/
section

/-!
# ML-DSA key generation on x86 (32-bit): the samplers

Each entry of `Â` (`expA_piece`) and of `s₁ ‖ s₂` (`expS_piece`): its seed
set, the sampler called, its result ANDed into `oACC` and the polynomial
masked with it (`maskA`), which keeps `KSamp` for one more entry.
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly Bounds minBounds rejNTTPoly rejBoundedPoly keyGenInternal toRq polyAt
  coeffAt Reduced PolyIs integerToBytes)
open VG.Proof.MlDsa.KeyGen (seedA seedS bmax)
open VG.Spec.Sha3 (bytesAt)

/-- The taint check of the mask is the same for every polynomial. -/
theorem maskA_tt (po : Nat) : (VG.X86.taint.check (τr [.esi]) (maskA oACC po)
    (VG.Taint.hintOf VG.X86.taint (τr [.esi]) (maskA oACC 0))).isSome = true := by
  kernel_rfl

theorem ifp {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a := ite_eq_left_iff.mpr fun h' => absurd h h'
theorem ifn {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b := ite_eq_right_iff.mpr fun h' => absurd h' h

/-! ## An entry of `Â` -/

theorem seedA_eq (ρ : List Byte) (r s : Nat) :
    seedA ρ r s = ρ ++ ([BitVec.ofNat 8 s] ++ [BitVec.ofNat 8 r]) := by
  simp only [seedA, Proof.MlDsa.KeyGen.integerToBytes_one, List.append_assoc]

/-! ## An entry of `s₁ ‖ s₂` -/

theorem seedS_eq (ρ' : List Byte) {r : Nat} (hr : r < 256) :
    seedS ρ' r = ρ' ++ ([BitVec.ofNat 8 r] ++ [0]) := by
  simp only [seedS, Proof.MlDsa.KeyGen.integerToBytes_two hr]; rfl

theorem eta_of {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) : p.η = 2 ∨ p.η = 4 := by
  rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inl h, .inr h]

section
variable {P : Prims} (hP : VG.Proof.MlDsa.X86.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p)
include hP hF

/-- Before the call of `RejNTTPoly` for entry `e`. -/
structure SA2 (p : Params) (e : Nat) (s₀ s : State) : Prop extends VG.Proof.MlDsa.X86.KeyGen.KSamp p e 0 s₀ s where
  seed : bytesAt s.mem (Buf.addr s₀ (sb oSA 34)) 34 = seedA (VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀) (e / p.ℓ) (e % p.ℓ)

/-- After it. -/
structure SA3 (p : Params) (e : Nat) (s₀ s : State) : Prop where
  kb : VG.Proof.MlDsa.X86.KeyGen.KB p s₀ s
  ex : ∃ (A : Nat → VG.Spec.MlDsa.Poly) (S : Nat → IPoly), (∀ e' < e, PolyIs s.mem (Buf.addr s₀ (aB e')) (A e')) ∧
    VG.Proof.MlDsa.X86.KeyGen.Good p s₀ e 0 A S (VG.Proof.MlDsa.X86.KeyGen.accV s₀ s)
  red : s.gpr .eax = 1 → Reduced s.mem (Buf.addr s₀ (aB e))
  out : Spec.MlDsa.Outcome (fun b => rejNTTPoly b.rejNTT (seedA (VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀) (e / p.ℓ) (e % p.ℓ))) (s.gpr .eax)
    (polyAt s.mem (Buf.addr s₀ (aB e)))

theorem expA_piece {e : Nat} (he : e < p.k * p.ℓ) : VG.Proof.MlDsa.X86.KeyGen.KP p (VG.Proof.MlDsa.X86.KeyGen.KSamp p e 0) (VG.Proof.MlDsa.X86.KeyGen.KSamp p (e + 1) 0) (expA P p e) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega)
  unfold expA
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.KeyGen.KSamp p e 0 s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ (sb (oSA + 32) 1)) 1 = [BitVec.ofNat 8 (e % p.ℓ)])
    (st8_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) (oSA + 32) (e % p.ℓ) (by layp hF) (ht := .block []) (by kernel_rfl)
      (fun _ _ _ h => h.kb.ctx) fun s₀ s s' hp h h' m' =>
        ⟨h.keep hp (N := 0) (by omega) ⟨by layp hF [VG.Proof.MlDsa.X86.KeyGen.safeKB], by layp hF, fun _ _ => by layp hF, fun _ h => absurd h (by omega)⟩
          (m' ▸ frW8) h', by rw [m', VG.Proof.MlDsa.X86.KeyGen.YK_sc]; exact VG.Proof.MlDsa.X86.KeyGen.st8_bytes _ _ _ _ _⟩) ?_
  refine Piece.seq (B := VG.Proof.MlDsa.X86.KeyGen.SA2 p e)
    (st8_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) (oSA + 33) (e / p.ℓ) (by layp hF) (ht := .block []) (by kernel_rfl)
      (fun _ _ _ h => h.1.kb.ctx) fun s₀ s s' hp h h' m' =>
        ⟨h.1.keep hp (N := 0) (by omega) ⟨by layp hF [VG.Proof.MlDsa.X86.KeyGen.safeKB], by layp hF, fun _ _ => by layp hF,
          fun _ h => absurd h (by omega)⟩ (m' ▸ frW8) h', ?_⟩) ?_
  · have k32 := keepBytes hp (N := 0) (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (b := sb oSA 32) (by layp hF) (m' ▸ frW8)
    have k1 := keepBytes hp (N := 0) (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (b := sb (oSA + 32) 1) (by layp hF) (m' ▸ frW8)
    rw [show (34 : Nat) = 32 + (1 + 1) from rfl, VG.Proof.MlDsa.X86.KeyGen.bytes_cat hp _ (l₁ := 32) (by layp hF) (by layp hF),
      VG.Proof.MlDsa.X86.KeyGen.bytes_cat hp _ (l₁ := 1) (l₂ := 1) (by layp hF) (by layp hF), k32, k1, h.1.kb.sa, h.2, VG.Proof.MlDsa.X86.KeyGen.seedA_eq, m', VG.Proof.MlDsa.X86.KeyGen.YK_sc,
      VG.Proof.MlDsa.X86.KeyGen.st8_bytes]
  refine Piece.seq (B := VG.Proof.MlDsa.X86.KeyGen.SA3 p e) (VG.Proof.MlDsa.X86.KeyGen.rejNtt_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) hP.rejNtt kS oSA kS (VG.Impl.MlDsa.X86.KeyGen.oP e) kS oSS (by layp hF)
    (Nat.le_of_eq (VG.Proof.MlDsa.X86.KeyGen.YK_stk p).symm) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.kb.ctx)
    (fun s₀ s₀' s s' _ _ hq h h' => by rw [h.seed, h'.seed, (TPub.leak hq).1])
    fun s₀ s s' hp h h' fr red out => ?_) ?_
  · obtain ⟨A, S, hA, -, hG⟩ := h.ex
    have sf : VG.Proof.MlDsa.X86.KeyGen.SafeS p e 0 [aB e, ssB 2048] := ⟨by layp hF [VG.Proof.MlDsa.X86.KeyGen.safeKB], by layp hF, fun _ _ => by layp hF,
      fun _ h => absurd h (by omega)⟩
    refine ⟨h.kb.keep hp (N := 80) (by omega) sf.kb fr h', ⟨A, S, fun e' he' => VG.Proof.MlDsa.X86.KeyGen.keepPolyD hp (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega))
      (sf.a e' he') fr (hA e' he'), ?_⟩, red, ?_⟩
    · rw [VG.Proof.MlDsa.X86.KeyGen.acc_keep hp (N := 80) (by omega) sf.acc fr]; exact hG
    · rw [← h.seed]; exact out
  refine maskA_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) oACC (VG.Impl.MlDsa.X86.KeyGen.oP e) (by layp hF) (VG.Proof.MlDsa.X86.KeyGen.maskA_tt _) (fun _ _ _ h => h.kb.ctx)
    fun s₀ s s' hp h h' fr ha hc => ?_
  simp only [VG.Proof.MlDsa.X86.KeyGen.YK_sc] at fr ha hc
  obtain ⟨A, S, hA, hG⟩ := h.ex
  have r01 : s.gpr .eax = 0 ∨ s.gpr .eax = 1 := by
    rcases h.out with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  obtain ⟨m1, m0⟩ := Proof.MlDsa.KeyGen.masked r01 hc
  obtain ⟨a01, aiff⟩ := Proof.MlDsa.KeyGen.acc_and (VG.Proof.MlDsa.X86.KeyGen.good_01 hG) r01
  have fr' := fr2 fr
  have sk : VG.Proof.MlDsa.X86.KeyGen.safeKB p [sb oACC 4, aB e] = true := by layp hF [VG.Proof.MlDsa.X86.KeyGen.safeKB]
  have sa : ∀ e' < e, (VG.Proof.MlDsa.X86.KeyGen.YK p).apart (aB e') [sb oACC 4, aB e] = true := fun _ _ => by layp hF
  refine ⟨h.kb.keep hp (N := 0) (by omega) sk fr' h', fun e' => if e' = e then polyAt s'.mem (Buf.addr s₀ (aB e))
    else A e', S, fun e' he' => ?_, fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
  · dsimp only
    rcases (by omega : e' < e ∨ e' = e) with he' | rfl
    · rw [VG.Proof.MlDsa.X86.KeyGen.ifn (by omega)]
      exact VG.Proof.MlDsa.X86.KeyGen.keepPolyD hp (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (sa e' he') fr' (hA e' he')
    · rw [VG.Proof.MlDsa.X86.KeyGen.ifp rfl]
      refine ⟨?_, rfl⟩
      rcases r01 with e0 | e1
      · exact (m0 e0).1
      · exact (m1 e1).2.2 (h.red e1)
  · have ea : VG.Proof.MlDsa.X86.KeyGen.accV s₀ s' = VG.Proof.MlDsa.X86.KeyGen.accV s₀ s &&& s.gpr .eax := ha
    rw [ea]
    rcases hG with ⟨h1, b, hb, _⟩ | ⟨h0, hn⟩
    · rcases h.out with ⟨ho, b', hb'⟩ | ⟨ho, hn⟩
      · refine .inl ⟨aiff.mpr ⟨h1, ho⟩, bmax b b', fun e' he' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
        dsimp only
        rcases (by omega : e' < e + 1 → e' < e ∨ e' = e) he' with he' | rfl
        · rw [VG.Proof.MlDsa.X86.KeyGen.ifn (by omega)]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_left b b').rejNTT (hb e' he')
        · rw [VG.Proof.MlDsa.X86.KeyGen.ifp rfl, (m1 ho).2.1]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_right b b').rejNTT hb'
      · rw [ho, h1]
        exact .inr ⟨by decide, Proof.MlDsa.KeyGen.keyGenInternal_none_A hq hr hn⟩
    · rw [h0]
      exact .inr ⟨BitVec.zero_and, hn⟩


/-- Before the call of `RejBoundedPoly` for entry `r`. -/
structure SS2 (p : Params) (r : Nat) (s₀ s : State) : Prop extends VG.Proof.MlDsa.X86.KeyGen.KSamp p (p.k * p.ℓ) r s₀ s where
  seed : bytesAt s.mem (Buf.addr s₀ (sb oSB 66)) 66 = seedS (VG.Proof.MlDsa.X86.KeyGen.rho'Of p s₀) r

/-- After it. -/
structure SS3 (p : Params) (r : Nat) (s₀ s : State) : Prop where
  kb : VG.Proof.MlDsa.X86.KeyGen.KB p s₀ s
  ex : ∃ (A : Nat → VG.Spec.MlDsa.Poly) (S : Nat → IPoly), (∀ e' < p.k * p.ℓ, PolyIs s.mem (Buf.addr s₀ (aB e')) (A e')) ∧
    (∀ r' < r, PolyIs s.mem (Buf.addr s₀ (VG.Impl.MlDsa.X86.KeyGen.sB p r')) (toRq (S r')) ∧ VG.Proof.MlDsa.X86.KeyGen.Small p.η (S r')) ∧
    VG.Proof.MlDsa.X86.KeyGen.Good p s₀ (p.k * p.ℓ) r A S (VG.Proof.MlDsa.X86.KeyGen.accV s₀ s)
  red : s.gpr .eax = 1 → Reduced s.mem (Buf.addr s₀ (VG.Impl.MlDsa.X86.KeyGen.sB p r))
  out : Spec.MlDsa.Outcome (fun b => (rejBoundedPoly p.η b.rejBounded (seedS (VG.Proof.MlDsa.X86.KeyGen.rho'Of p s₀) r)).map toRq)
    (s.gpr .eax) (polyAt s.mem (Buf.addr s₀ (VG.Impl.MlDsa.X86.KeyGen.sB p r)))

theorem expS_piece {r : Nat} (hr : r < p.ℓ + p.k) :
    VG.Proof.MlDsa.X86.KeyGen.KP p (VG.Proof.MlDsa.X86.KeyGen.KSamp p (p.k * p.ℓ) r) (VG.Proof.MlDsa.X86.KeyGen.KSamp p (p.k * p.ℓ) (r + 1)) (expS P p r) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hr256 : r < 256 := by omega
  unfold expS
  refine Piece.seq (B := VG.Proof.MlDsa.X86.KeyGen.SS2 p r)
    (st8_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) (oSB + 64) r (by layp hF) (ht := .block []) (by kernel_rfl)
      (fun _ _ _ h => h.kb.ctx) fun s₀ s s' hp h h' m' =>
        ⟨h.keep hp (N := 0) (by omega) ⟨by layp hF [VG.Proof.MlDsa.X86.KeyGen.safeKB], by layp hF, fun _ _ => by layp hF,
          fun _ _ => by layp hF⟩ (m' ▸ frW8) h', ?_⟩) ?_
  · have k64 := keepBytes hp (N := 0) (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (b := sb oSB 64) (by layp hF) (m' ▸ frW8)
    have k65 := keepBytes hp (N := 0) (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (b := sb (oSB + 65) 1) (by layp hF) (m' ▸ frW8)
    rw [show (66 : Nat) = 64 + (1 + 1) from rfl, VG.Proof.MlDsa.X86.KeyGen.bytes_cat hp _ (l₁ := 64) (by layp hF) (by layp hF),
      VG.Proof.MlDsa.X86.KeyGen.bytes_cat hp _ (l₁ := 1) (l₂ := 1) (by layp hF) (by layp hF), k64, show oSB + 64 + 1 = oSB + 65 from rfl, k65,
      h.kb.sbb, h.kb.z, VG.Proof.MlDsa.X86.KeyGen.seedS_eq _ hr256, m', VG.Proof.MlDsa.X86.KeyGen.YK_sc, VG.Proof.MlDsa.X86.KeyGen.st8_bytes]
  refine Piece.seq (B := VG.Proof.MlDsa.X86.KeyGen.SS3 p r) (VG.Proof.MlDsa.X86.KeyGen.rejBounded_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) hP.rejBounded kS oSB p.η kS (VG.Impl.MlDsa.X86.KeyGen.oP (p.k * p.ℓ + r))
    kS oSS (VG.Proof.MlDsa.X86.KeyGen.eta_of hF) (by layp hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.KeyGen.YK_stk p).symm) (ht := .block []) (by kernel_rfl)
    (fun _ _ _ h => h.kb.ctx) (fun s₀ s₀' s s' _ _ hq h h' => by rw [h.seed, h'.seed, (TPub.leak hq).2 r hr])
    fun s₀ s s' hp h h' fr red out => ?_) ?_
  · obtain ⟨A, S, hA, hS, hG⟩ := h.ex
    have sf : VG.Proof.MlDsa.X86.KeyGen.SafeS p (p.k * p.ℓ) r [VG.Impl.MlDsa.X86.KeyGen.sB p r, ssB 2048] := ⟨by layp hF [VG.Proof.MlDsa.X86.KeyGen.safeKB], by layp hF, fun _ _ => by layp hF,
      fun _ _ => by layp hF⟩
    refine ⟨h.kb.keep hp (N := 80) (by omega) sf.kb fr h', ⟨A, S, fun e' he' => VG.Proof.MlDsa.X86.KeyGen.keepPolyD hp (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega))
      (sf.a e' he') fr (hA e' he'), fun r' hr' => ⟨VG.Proof.MlDsa.X86.KeyGen.keepPolyD hp (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (sf.s r' hr') fr (hS r' hr').1,
        (hS r' hr').2⟩, ?_⟩, red, ?_⟩
    · rw [VG.Proof.MlDsa.X86.KeyGen.acc_keep hp (N := 80) (by omega) sf.acc fr]; exact hG
    · rw [← h.seed]; exact out
  refine maskA_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) oACC (VG.Impl.MlDsa.X86.KeyGen.oP (p.k * p.ℓ + r)) (by layp hF) (VG.Proof.MlDsa.X86.KeyGen.maskA_tt _) (fun _ _ _ h => h.kb.ctx)
    fun s₀ s s' hp h h' fr ha hc => ?_
  simp only [VG.Proof.MlDsa.X86.KeyGen.YK_sc] at fr ha hc
  obtain ⟨A, S, hA, hS, hG⟩ := h.ex
  have r01 : s.gpr .eax = 0 ∨ s.gpr .eax = 1 := by
    rcases h.out with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  obtain ⟨m1, m0⟩ := Proof.MlDsa.KeyGen.masked r01 hc
  obtain ⟨a01, aiff⟩ := Proof.MlDsa.KeyGen.acc_and (VG.Proof.MlDsa.X86.KeyGen.good_01 hG) r01
  have fr' := fr2 fr
  have sk : VG.Proof.MlDsa.X86.KeyGen.safeKB p [sb oACC 4, VG.Impl.MlDsa.X86.KeyGen.sB p r] = true := by layp hF [VG.Proof.MlDsa.X86.KeyGen.safeKB]
  have sa : ∀ e' < p.k * p.ℓ, (VG.Proof.MlDsa.X86.KeyGen.YK p).apart (aB e') [sb oACC 4, VG.Impl.MlDsa.X86.KeyGen.sB p r] = true := fun _ _ => by layp hF
  have ss : ∀ r' < r, (VG.Proof.MlDsa.X86.KeyGen.YK p).apart (VG.Impl.MlDsa.X86.KeyGen.sB p r') [sb oACC 4, VG.Impl.MlDsa.X86.KeyGen.sB p r] = true := fun _ _ => by layp hF
  have kA : ∀ e' < p.k * p.ℓ, PolyIs s'.mem (Buf.addr s₀ (aB e')) (A e') := fun e' he' =>
    VG.Proof.MlDsa.X86.KeyGen.keepPolyD hp (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (sa e' he') fr' (hA e' he')
  have kS' : ∀ r' < r, PolyIs s'.mem (Buf.addr s₀ (VG.Impl.MlDsa.X86.KeyGen.sB p r')) (toRq (S r')) ∧ VG.Proof.MlDsa.X86.KeyGen.Small p.η (S r') := fun r' hr' =>
    ⟨VG.Proof.MlDsa.X86.KeyGen.keepPolyD hp (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (ss r' hr') fr' (hS r' hr').1, (hS r' hr').2⟩
  have ea : VG.Proof.MlDsa.X86.KeyGen.accV s₀ s' = VG.Proof.MlDsa.X86.KeyGen.accV s₀ s &&& s.gpr .eax := ha
  rcases r01 with e0 | e1
  · -- The sampler failed: the polynomial is zero.
    have hn : rejBoundedPoly p.η minBounds.rejBounded (seedS (VG.Proof.MlDsa.X86.KeyGen.rho'Of p s₀) r) = none := by
      rcases h.out with ⟨h, _⟩ | ⟨_, h⟩
      · rw [e0] at h; exact absurd h (by decide)
      · exact Option.map_eq_none_iff.mp h
    refine ⟨h.kb.keep hp (N := 0) (by omega) sk fr' h', A, fun r' => if r' = r then Proof.MlDsa.KeyGen.zeroI
      else S r', kA, fun r' hr' => ?_, ?_⟩
    · dsimp only
      rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
      · rw [VG.Proof.MlDsa.X86.KeyGen.ifn (by omega)]; exact kS' r' hr'
      · rw [VG.Proof.MlDsa.X86.KeyGen.ifp rfl]; exact ⟨(m0 e0), Proof.MlDsa.KeyGen.zeroI_small _⟩
    · rw [ea, e0]
      exact .inr ⟨BitVec.and_zero, Proof.MlDsa.KeyGen.keyGenInternal_none_S hr hn⟩
  · -- It succeeded.
    obtain ⟨b', hb'⟩ : ∃ b' : Bounds, (rejBoundedPoly p.η b'.rejBounded (seedS (VG.Proof.MlDsa.X86.KeyGen.rho'Of p s₀) r)).map toRq =
        some (polyAt s.mem (Buf.addr s₀ (VG.Impl.MlDsa.X86.KeyGen.sB p r))) := by
      rcases h.out with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · rw [e1] at h; exact absurd h (by decide)
    obtain ⟨x, hx, htx⟩ := Option.map_eq_some_iff.mp hb'
    refine ⟨h.kb.keep hp (N := 0) (by omega) sk fr' h', A, fun r' => if r' = r then x else S r', kA,
      fun r' hr' => ?_, ?_⟩
    · dsimp only
      rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
      · rw [VG.Proof.MlDsa.X86.KeyGen.ifn (by omega)]; exact kS' r' hr'
      · rw [VG.Proof.MlDsa.X86.KeyGen.ifp rfl, htx, ← (m1 e1).2.1]
        exact ⟨⟨(m1 e1).2.2 (h.red e1), rfl⟩, Proof.MlDsa.KeyGen.rejBoundedPoly_range hx⟩
    · rw [ea]
      rcases hG with ⟨h1, b, hbA, hbS⟩ | ⟨h0, hn⟩
      · refine .inl ⟨aiff.mpr ⟨h1, e1⟩, bmax b b', fun e' he' =>
          Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_left b b').rejNTT (hbA e' he'),
          fun r' hr' => ?_⟩
        dsimp only
        rcases (by omega : r' < r + 1 → r' < r ∨ r' = r) hr' with hr' | rfl
        · rw [VG.Proof.MlDsa.X86.KeyGen.ifn (by omega)]
          exact Proof.MlDsa.KeyGen.rejBoundedPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_left b b').rejBounded
            (hbS r' hr')
        · rw [VG.Proof.MlDsa.X86.KeyGen.ifp rfl]
          exact Proof.MlDsa.KeyGen.rejBoundedPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_right b b').rejBounded hx
      · rw [h0]
        exact .inr ⟨BitVec.zero_and, hn⟩

end

/-! ## The samplers, in sequence -/

theorem seqR_piece {Pre : State → Prop} {Pub : State → State → Prop} {f : Nat → Prog isa}
    {I : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → Piece Pre Pub (I k) (I (k + 1)) (f k)) →
      Piece Pre Pub (I a) (I (a + n)) (VG.Impl.MlDsa.X86.KeyGen.seqR f a n)
  | 0, a, _ => ⟨fun _ _ _ h => WP.block_nil_iff.mpr h, fun _ _ _ _ _ => RelCT.nil fun _ _ _ => trivial⟩
  | n + 1, a, h => by
    refine Piece.seq (h a (Nat.le_refl _) (by omega)) ?_
    rw [show a + (n + 1) = a + 1 + n by omega]
    exact VG.Proof.MlDsa.X86.KeyGen.seqR_piece n (a + 1) fun k h₁ h₂ => h k (by omega) (by omega)

end VG.Proof.MlDsa.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.KeyGen.RestBase`. -/
section

/-!
# ML-DSA key generation on x86 (32-bit): after the samplers

Once the samplers are done, with `Â` and `s₁ ‖ s₂` in memory as `A` and `S`
(`Good`), the rest of the function computes the keys from them, whatever they
are (`KR`): after the copies of `ρ` and `K` (`copies_piece`), the first `np`
entries of `s₁ ‖ s₂` packed to `sk`, the first `nj` of `s₁` in the NTT domain,
and the first `nr` rows of `t` packed to `pk` and `sk`.
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt coeffAt Reduced PolyIs bitPack simpleBitPack keyGenSeeds)
open VG.Proof.MlDsa.KeyGen (t1K t0K)
open VG.Spec.Sha3 (bytesAt)

/-- After the samplers: the keys from `A` and `S`, so far. -/
structure KR (p : Params) (A : Nat → VG.Spec.MlDsa.Poly) (S : Nat → IPoly) (np nj nr : Nat) (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.KeyGen.YK p) s₀ s
  good : VG.Proof.MlDsa.X86.KeyGen.Good p s₀ (p.k * p.ℓ) (p.ℓ + p.k) A S (VG.Proof.MlDsa.X86.KeyGen.accV s₀ s)
  small : ∀ r < p.ℓ + p.k, VG.Proof.MlDsa.X86.KeyGen.Small p.η (S r)
  aS : ∀ e < p.k * p.ℓ, PolyIs s.mem (Buf.addr s₀ (aB e)) (A e)
  s2 : ∀ i < p.k, PolyIs s.mem (Buf.addr s₀ (VG.Impl.MlDsa.X86.KeyGen.sB p (p.ℓ + i))) (toRq (S (p.ℓ + i)))
  s1 : ∀ j < p.ℓ, PolyIs s.mem (Buf.addr s₀ (VG.Impl.MlDsa.X86.KeyGen.sB p j)) (if j < nj then VG.Spec.MlDsa.ntt (toRq (S j)) else toRq (S j))
  pk0 : bytesAt s.mem (Buf.addr s₀ ⟨1, 0, 32⟩) 32 = VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀
  sk0 : bytesAt s.mem (Buf.addr s₀ ⟨2, 0, 32⟩) 32 = VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀
  sk1 : bytesAt s.mem (Buf.addr s₀ ⟨2, 32, 32⟩) 32 = VG.Proof.MlDsa.X86.KeyGen.kOf p s₀
  packs : ∀ r < np, bytesAt s.mem (Buf.addr s₀ ⟨2, 128 + lenS p * r, lenS p⟩) (lenS p) = VG.Spec.MlDsa.bitPack (S r) p.η p.η
  rows : ∀ i < nr, bytesAt s.mem (Buf.addr s₀ ⟨1, 32 + 320 * i, 320⟩) 320 = VG.Spec.MlDsa.simpleBitPack (t1K p A S i) 1023 ∧
    bytesAt s.mem (Buf.addr s₀ ⟨2, oT0 p + 416 * i, 416⟩) 416 = VG.Spec.MlDsa.bitPack (t0K p A S i) 4095 4096

/-- The buffers of `KR` but the polynomials of `s₁` apart from `bs`. -/
structure SafeR (p : Params) (np nr : Nat) (bs : List Buf) : Prop where
  acc : (VG.Proof.MlDsa.X86.KeyGen.YK p).apart (sb oACC 4) bs = true
  aS : ∀ e < p.k * p.ℓ, (VG.Proof.MlDsa.X86.KeyGen.YK p).apart (aB e) bs = true
  s2 : ∀ i < p.k, (VG.Proof.MlDsa.X86.KeyGen.YK p).apart (VG.Impl.MlDsa.X86.KeyGen.sB p (p.ℓ + i)) bs = true
  pk0 : (VG.Proof.MlDsa.X86.KeyGen.YK p).apart ⟨1, 0, 32⟩ bs = true
  sk0 : (VG.Proof.MlDsa.X86.KeyGen.YK p).apart ⟨2, 0, 32⟩ bs = true
  sk1 : (VG.Proof.MlDsa.X86.KeyGen.YK p).apart ⟨2, 32, 32⟩ bs = true
  packs : ∀ r < np, (VG.Proof.MlDsa.X86.KeyGen.YK p).apart ⟨2, 128 + lenS p * r, lenS p⟩ bs = true
  rows : ∀ i < nr, (VG.Proof.MlDsa.X86.KeyGen.YK p).apart ⟨1, 32 + 320 * i, 320⟩ bs = true ∧ (VG.Proof.MlDsa.X86.KeyGen.YK p).apart ⟨2, oT0 p + 416 * i, 416⟩ bs = true

/-- Proves a `SafeR`, with the facts of the parameter set `hF`. -/
macro "safeR " hF:term:max : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> (try refine ⟨?_, ?_⟩) <;> layp $hF))

theorem apart_append {Y : VG.Proof.MlKem.X86.Top.Lay} {b : Buf} {bs₁ bs₂ : List Buf} (h₁ : Y.apart b bs₁ = true)
    (h₂ : Y.apart b bs₂ = true) : Y.apart b (bs₁ ++ bs₂) = true := by
  simp only [Lay.apart, List.all_append, Bool.and_eq_true] at *
  exact ⟨h₁.1, h₁.2, h₂.2⟩

/-- `SafeR` of two lists of buffers, for both. -/
theorem SafeR.append {p : Params} {np nr : Nat} {bs₁ bs₂ : List Buf} (h₁ : VG.Proof.MlDsa.X86.KeyGen.SafeR p np nr bs₁)
    (h₂ : VG.Proof.MlDsa.X86.KeyGen.SafeR p np nr bs₂) : VG.Proof.MlDsa.X86.KeyGen.SafeR p np nr (bs₁ ++ bs₂) :=
  ⟨VG.Proof.MlDsa.X86.KeyGen.apart_append h₁.acc h₂.acc, fun e he => VG.Proof.MlDsa.X86.KeyGen.apart_append (h₁.aS e he) (h₂.aS e he),
    fun i hi => VG.Proof.MlDsa.X86.KeyGen.apart_append (h₁.s2 i hi) (h₂.s2 i hi), VG.Proof.MlDsa.X86.KeyGen.apart_append h₁.pk0 h₂.pk0, VG.Proof.MlDsa.X86.KeyGen.apart_append h₁.sk0 h₂.sk0,
    VG.Proof.MlDsa.X86.KeyGen.apart_append h₁.sk1 h₂.sk1, fun r hr => VG.Proof.MlDsa.X86.KeyGen.apart_append (h₁.packs r hr) (h₂.packs r hr),
    fun i hi => ⟨VG.Proof.MlDsa.X86.KeyGen.apart_append (h₁.rows i hi).1 (h₂.rows i hi).1, VG.Proof.MlDsa.X86.KeyGen.apart_append (h₁.rows i hi).2 (h₂.rows i hi).2⟩⟩

/-! `SafeR` of one buffer, proved once for any buffer (`safeR` on a literal list
of buffers costs seconds). -/

/-- A buffer of `scratch` apart from the accumulator, `Â` and `s₂`. -/
theorem SafeR.sc {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) {np nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) {o l : Nat}
    (h0 : 0 < l) (h1 : o + l ≤ oACC ∨ oACC + 4 ≤ o)
    (h2 : o + l ≤ VG.Impl.MlDsa.X86.KeyGen.oP 0 ∨ (VG.Impl.MlDsa.X86.KeyGen.oP (p.k * p.ℓ) ≤ o ∧ o + l ≤ VG.Impl.MlDsa.X86.KeyGen.oP (p.k * p.ℓ + p.ℓ)) ∨ VG.Impl.MlDsa.X86.KeyGen.oP (p.k * p.ℓ + p.ℓ + p.k) ≤ o)
    (h3 : o + l ≤ VG.Proof.MlDsa.X86.KeyGen.scrLen p) : VG.Proof.MlDsa.X86.KeyGen.SafeR p np nr [sb o l] := by
  simp only [oACC, VG.Impl.MlDsa.X86.KeyGen.oP] at h1 h2
  simp only [VG.Proof.MlDsa.X86.KeyGen.scrLen, hF.sw] at h3
  safeR hF

/-- A buffer of `pk` after the rows so far. -/
theorem SafeR.pk {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) {np nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) {o l : Nat}
    (h0 : 0 < l) (h1 : 32 + 320 * nr ≤ o) (h2 : o + l ≤ p.pkLen) : VG.Proof.MlDsa.X86.KeyGen.SafeR p np nr [⟨1, o, l⟩] := by
  rw [hF.pk] at h2
  safeR hF

/-- A buffer of `sk` after `ρ` and `K`, apart from the entries packed and the rows so far. -/
theorem SafeR.sk {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) {np nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) {o l : Nat}
    (h0 : 0 < l) (h1 : 64 ≤ o) (hp : o + l ≤ 128 ∨ 128 + lenS p * np ≤ o) (hr : o + l ≤ oT0 p ∨ oT0 p + 416 * nr ≤ o)
    (h2 : o + l ≤ p.skLen) : VG.Proof.MlDsa.X86.KeyGen.SafeR p np nr [⟨2, o, l⟩] := by
  rw [hF.sk] at h2
  simp only [oT0] at hr h2
  have := hF.k; have := hF.l; have := hF.kl
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> rw [hlen] at hp hr h2 <;>
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> (try refine ⟨?_, ?_⟩) <;>
  lay [hlen, hF.pk, hF.sk, hF.sw]

theorem KR.keep {p : Params} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {np nj nr : Nat} {s₀ s s' : State}
    (h : VG.Proof.MlDsa.X86.KeyGen.KR p A S np nj nr s₀ s) (hp : TPre (VG.Proof.MlDsa.X86.KeyGen.YK p) s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ 96)
    (hs : VG.Proof.MlDsa.X86.KeyGen.SafeR p np nr bs) (hs1 : ∀ j < p.ℓ, (VG.Proof.MlDsa.X86.KeyGen.YK p).apart (VG.Impl.MlDsa.X86.KeyGen.sB p j) bs = true) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (h' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.KeyGen.YK p) s₀ s') : VG.Proof.MlDsa.X86.KeyGen.KR p A S np nj nr s₀ s' where
  ctx := h'
  good := by rw [VG.Proof.MlDsa.X86.KeyGen.acc_keep hp hN hs.acc fr]; exact h.good
  small := h.small
  aS e he := VG.Proof.MlDsa.X86.KeyGen.keepPolyD hp hN (hs.aS e he) fr (h.aS e he)
  s2 i hi := VG.Proof.MlDsa.X86.KeyGen.keepPolyD hp hN (hs.s2 i hi) fr (h.s2 i hi)
  s1 j hj := VG.Proof.MlDsa.X86.KeyGen.keepPolyD hp hN (hs1 j hj) fr (h.s1 j hj)
  pk0 := by rw [keepBytes hp hN hs.pk0 fr]; exact h.pk0
  sk0 := by rw [keepBytes hp hN hs.sk0 fr]; exact h.sk0
  sk1 := by rw [keepBytes hp hN hs.sk1 fr]; exact h.sk1
  packs r hr := by rw [keepBytes hp hN (hs.packs r hr) fr]; exact h.packs r hr
  rows i hi := ⟨by rw [keepBytes hp hN (hs.rows i hi).1 fr]; exact (h.rows i hi).1,
    by rw [keepBytes hp hN (hs.rows i hi).2 fr]; exact (h.rows i hi).2⟩

/-- The states after the copies, and the first `np` entries packed, `nj` in the NTT domain and `nr` rows. -/
abbrev KRx (p : Params) (np nj nr : Nat) (s₀ s : State) : Prop := ∃ A S, VG.Proof.MlDsa.X86.KeyGen.KR p A S np nj nr s₀ s

/-! ## `ρ` and `K` to the keys -/

theorem KB.rho {p : Params} {s₀ s : State} (h : VG.Proof.MlDsa.X86.KeyGen.KB p s₀ s) :
    bytesAt s.mem (Buf.addr s₀ (sb oHX 32)) 32 = VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀ := by
  show _ = (keyGenSeeds p (VG.Proof.MlDsa.X86.KeyGen.xiOf s₀)).1
  rw [VG.Proof.MlDsa.X86.KeyGen.seeds_eq]
  show _ = (VG.Proof.MlDsa.X86.KeyGen.hxOf p s₀).take 32
  rw [← h.hx, Proof.MlKem.bytesAt_take _ _ (by decide)]

theorem KB.kk {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) {s₀ s : State} (hp : TPre (VG.Proof.MlDsa.X86.KeyGen.YK p) s₀) (h : VG.Proof.MlDsa.X86.KeyGen.KB p s₀ s) :
    bytesAt s.mem (Buf.addr s₀ (sb (oHX + 96) 32)) 32 = VG.Proof.MlDsa.X86.KeyGen.kOf p s₀ := by
  show _ = (keyGenSeeds p (VG.Proof.MlDsa.X86.KeyGen.xiOf s₀)).2.2
  rw [VG.Proof.MlDsa.X86.KeyGen.seeds_eq]
  show _ = ((VG.Proof.MlDsa.X86.KeyGen.hxOf p s₀).drop 96).take 32
  rw [← h.hx, VG.Proof.MlDsa.X86.KeyGen.bytes_sub hp _ (k := 96) (c := 32) (L := 128) (by decide) (by layp hF) (by layp hF)]

theorem copies_piece {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) :
    VG.Proof.MlDsa.X86.KeyGen.KP p (VG.Proof.MlDsa.X86.KeyGen.KSamp p (p.k * p.ℓ) (p.ℓ + p.k)) (VG.Proof.MlDsa.X86.KeyGen.KRx p 0 0 0) copies := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  unfold copies
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.KeyGen.KSamp p (p.k * p.ℓ) (p.ℓ + p.k) s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ ⟨1, 0, 32⟩) 32 = VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀)
    (copyW_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) kS oHX 1 0 8 (by decide) (by decide) (by layp hF) (h₁ := .block []) (by kernel_rfl)
      (by taint_decide) (fun _ _ _ h => h.kb.ctx) fun s₀ s s' hp h h' fr cp => ⟨h.keep hp (N := 0) (by omega)
        ⟨by layp hF [VG.Proof.MlDsa.X86.KeyGen.safeKB], by layp hF, fun _ _ => by layp hF, fun _ _ => by layp hF⟩ (fr1 fr) h', ?_⟩) ?_
  · show bytesAt s'.mem _ 32 = _
    rw [cp]; exact h.kb.rho
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.KeyGen.KSamp p (p.k * p.ℓ) (p.ℓ + p.k) s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ ⟨1, 0, 32⟩) 32 = VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀ ∧ bytesAt s.mem (Buf.addr s₀ ⟨2, 0, 32⟩) 32 = VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀)
    (copyW_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) kS oHX 2 0 8 (by decide) (by decide) (by layp hF) (h₁ := .block []) (by kernel_rfl)
      (by taint_decide) (fun _ _ _ h => h.1.kb.ctx) fun s₀ s s' hp h h' fr cp => ⟨h.1.keep hp (N := 0) (by omega)
        ⟨by layp hF [VG.Proof.MlDsa.X86.KeyGen.safeKB], by layp hF, fun _ _ => by layp hF, fun _ _ => by layp hF⟩ (fr1 fr) h',
        by rw [keepBytes hp (N := 0) (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (b := ⟨1, 0, 32⟩) (by layp hF) (fr1 fr)]; exact h.2, ?_⟩) ?_
  · show bytesAt s'.mem _ 32 = _
    rw [cp]; exact h.1.kb.rho
  refine copyW_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) kS (oHX + 96) 2 32 8 (by decide) (by decide) (by layp hF) (h₁ := .block [])
    (by kernel_rfl) (by taint_decide) (fun _ _ _ h => h.1.kb.ctx) fun s₀ s s' hp h h' fr cp => ?_
  obtain ⟨⟨kb, A, S, hA, hS, hG⟩, e1, e2⟩ := h
  have k : ∀ b : Buf, (VG.Proof.MlDsa.X86.KeyGen.YK p).apart b [⟨2, 32, 32⟩] = true →
      bytesAt s'.mem (Buf.addr s₀ b) b.len = bytesAt s.mem (Buf.addr s₀ b) b.len :=
    fun b hb => keepBytes hp (N := 0) (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) hb (fr1 fr)
  refine ⟨A, S, h', ?_, fun r hr => (hS r hr).2, fun e he => VG.Proof.MlDsa.X86.KeyGen.keepPolyD hp (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (by layp hF) (fr1 fr)
    (hA e he), fun i hi => VG.Proof.MlDsa.X86.KeyGen.keepPolyD hp (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (by layp hF) (fr1 fr) (hS _ (by omega)).1,
    fun j hj => ?_, by rw [k _ (by layp hF)]; exact e1, by rw [k _ (by layp hF)]; exact e2, ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · rw [VG.Proof.MlDsa.X86.KeyGen.acc_keep hp (N := 0) (by omega) (by layp hF) (fr1 fr)]; exact hG
  · rw [VG.Proof.MlDsa.X86.KeyGen.ifn (Nat.not_lt_zero j)]
    exact VG.Proof.MlDsa.X86.KeyGen.keepPolyD hp (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (by layp hF) (fr1 fr) (hS _ (by omega)).1
  · show bytesAt s'.mem _ 32 = _
    rw [cp]; exact kb.kk hF hp

end VG.Proof.MlDsa.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.KeyGen.RestPack`. -/
section

/-!
# ML-DSA key generation on x86 (32-bit): `s₁ ‖ s₂` packed, and `ŝ₁`

Each entry of `s₁ ‖ s₂`, `BitPack`ed to `sk` (`packS_piece`: its coefficients
are in `[-η, η]`), and `ŝ₁[j] = NTT(s₁[j])` (`nttS_piece`).
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt coeffAt Reduced PolyIs bitPack simpleBitPack)
open VG.Spec.Sha3 (bytesAt)

theorem coeff_val {m : Mem} {q : Addr} {f : VG.Spec.MlDsa.Poly} (h : PolyIs m q f) {i : Nat} (hi : i < 256) :
    (coeffAt m q i).toNat = (f[i]'hi).val := by
  have e := congrArg (fun g : VG.Spec.MlDsa.Poly => (g[i]'hi).val) h.2
  simp only [polyAt, Vector.getElem_ofFn, Fin.val_ofNat] at e
  rw [← e, Nat.mod_eq_of_lt (h.1 i hi)]

theorem small_mem {η : Nat} {x : IPoly} (h : VG.Proof.MlDsa.X86.KeyGen.Small η x) {i : Nat} (hi : i < 256) :
    -(η : Int) ≤ x[i] ∧ x[i] ≤ η := h _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hi))

theorem small_big {η : Nat} (hη : η ≤ 4) {x : IPoly} (hs : VG.Proof.MlDsa.X86.KeyGen.Small η x) :
    ∀ c ∈ x.toList, -4190208 ≤ c ∧ c ≤ 4190208 := fun c hc => by
  have := hs c hc; omega

theorem eta_le {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) : p.η ≤ 4 := by rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem eta_params {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) : (p.η, p.η) ∈ Spec.MlDsa.bitPackParams := by
  rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> decide

theorem lenS_eq (p : Params) : lenS p = 32 * Spec.MlDsa.bitlen (p.η + p.η) := by
  rw [lenS, Nat.two_mul]

/-- The coefficients of a small polynomial are in `[-η, η]`, as `BitPack` needs. -/
theorem packIn {m : Mem} {q : Addr} {η : Nat} (hη : η ≤ 4) {x : IPoly} (h : PolyIs m q (toRq x)) (hs : VG.Proof.MlDsa.X86.KeyGen.Small η x) :
    ∀ i < Spec.MlDsa.n, -(η : Int) ≤ Spec.MlDsa.modPm (coeffAt m q i).toNat Spec.MlDsa.q ∧
      Spec.MlDsa.modPm (coeffAt m q i).toNat Spec.MlDsa.q ≤ η := fun i hi => by
  have hx := VG.Proof.MlDsa.X86.KeyGen.small_mem hs hi
  rw [VG.Proof.MlDsa.X86.KeyGen.coeff_val h hi]
  simp only [toRq, Vector.getElem_map]
  rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
  exact hx

/-- The entry `r` of `s₁ ‖ s₂`, before `NTT`. -/
theorem KR.sPoly {p : Params} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {np nr : Nat} {s₀ s : State}
    (h : VG.Proof.MlDsa.X86.KeyGen.KR p A S np 0 nr s₀ s) {r : Nat} (hr : r < p.ℓ + p.k) :
    PolyIs s.mem (Buf.addr s₀ (VG.Impl.MlDsa.X86.KeyGen.sB p r)) (toRq (S r)) := by
  by_cases hl : r < p.ℓ
  · have := h.s1 r hl; rwa [VG.Proof.MlDsa.X86.KeyGen.ifn (Nat.not_lt_zero r)] at this
  · have := h.s2 (r - p.ℓ) (by omega); rwa [show p.ℓ + (r - p.ℓ) = r by omega] at this

section
variable {P : Prims} (hP : VG.Proof.MlDsa.X86.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p)
include hP hF

theorem packS_piece {r : Nat} (hr : r < p.ℓ + p.k) : VG.Proof.MlDsa.X86.KeyGen.KP p (VG.Proof.MlDsa.X86.KeyGen.KRx p r 0 0) (VG.Proof.MlDsa.X86.KeyGen.KRx p (r + 1) 0 0) (packS P p r) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  unfold packS
  refine Piece.mono (A := fun s₀ s => ∃ A S, VG.Proof.MlDsa.X86.KeyGen.KR p A S r 0 0 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (VG.Impl.MlDsa.X86.KeyGen.sB p r)) (toRq (S r)))
    ?_ (fun s₀ s _ ⟨A, S, h⟩ => ⟨A, S, h, h.sPoly hr⟩) fun _ _ _ h => h
  refine VG.Proof.MlDsa.X86.KeyGen.bp_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) hP.bitPack kS (VG.Impl.MlDsa.X86.KeyGen.oP (p.k * p.ℓ + r)) p.η p.η 2 (128 + lenS p * r) (lenS p)
    (VG.Proof.MlDsa.X86.KeyGen.eta_params hF) (VG.Proof.MlDsa.X86.KeyGen.lenS_eq p) (by layp hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.KeyGen.YK_stk p).symm) (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨A, S, h, hs⟩ => ⟨h.ctx, hs.1, VG.Proof.MlDsa.X86.KeyGen.packIn (VG.Proof.MlDsa.X86.KeyGen.eta_le hF) hs (h.small r hr)⟩)
    fun s₀ s s' hp ⟨A, S, h, hs⟩ h' fr out => ⟨A, S, ?_⟩
  have hpos : 0 < lenS p := by rcases hF.eta with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  have hle : 128 + lenS p * r + lenS p ≤ oT0 p := by
    simp only [oT0]; rw [Nat.add_assoc, ← Nat.mul_succ]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hr) _
  have hsf : VG.Proof.MlDsa.X86.KeyGen.SafeR p r 0 [⟨2, 128 + lenS p * r, lenS p⟩] := SafeR.sk hF (Nat.le_of_lt hr) (Nat.zero_le _) hpos
    (by omega) (.inr (Nat.le_refl _)) (.inl hle) (by rw [hF.sk]; omega)
  have k := h.keep hp (N := 80) (by omega) hsf (fun _ _ => by layp hF) fr h'
  refine { k with packs := fun r' hr' => ?_ }
  rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
  · exact k.packs r' hr'
  · rw [out, hs.2, Proof.MlDsa.KeyGen.modPm_toRq (VG.Proof.MlDsa.X86.KeyGen.small_big (VG.Proof.MlDsa.X86.KeyGen.eta_le hF) (h.small r' hr))]

theorem nttS_piece {j : Nat} (hj : j < p.ℓ) :
    VG.Proof.MlDsa.X86.KeyGen.KP p (VG.Proof.MlDsa.X86.KeyGen.KRx p (p.ℓ + p.k) j 0) (VG.Proof.MlDsa.X86.KeyGen.KRx p (p.ℓ + p.k) (j + 1) 0) (VG.Impl.MlDsa.X86.KeyGen.nttS P p j) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  unfold VG.Impl.MlDsa.X86.KeyGen.nttS
  refine Piece.mono (A := fun s₀ s => ∃ A S, VG.Proof.MlDsa.X86.KeyGen.KR p A S (p.ℓ + p.k) j 0 s₀ s)
    ?_ (fun _ _ _ h => h) fun _ _ _ h => h
  refine VG.Proof.MlDsa.X86.KeyGen.inPlace_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) hP.ntt kS (VG.Impl.MlDsa.X86.KeyGen.oP (p.k * p.ℓ + j)) kS oSS (by layp hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.KeyGen.YK_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨A, S, h⟩ => ⟨h.ctx, (h.s1 j hj).1⟩)
    fun s₀ s s' hp ⟨A, S, h⟩ h' fr out => ⟨A, S, ?_⟩
  have hS := h.s1 j hj
  rw [VG.Proof.MlDsa.X86.KeyGen.ifn (Nat.lt_irrefl j)] at hS
  have hs : VG.Proof.MlDsa.X86.KeyGen.SafeR p (p.ℓ + p.k) 0 [VG.Impl.MlDsa.X86.KeyGen.sB p j, ssB 1024] :=
    (SafeR.sc hF (Nat.le_refl _) (Nat.zero_le _) (by decide) (.inr (by simp only [oACC, VG.Impl.MlDsa.X86.KeyGen.oP]; omega))
      (.inr (.inl (by simp only [VG.Impl.MlDsa.X86.KeyGen.oP]; omega))) (by simp only [VG.Proof.MlDsa.X86.KeyGen.scrLen, hF.sw, VG.Impl.MlDsa.X86.KeyGen.oP]; omega)).append (bs₁ := [_])
    (SafeR.sc (o := oSS) (l := 1024) hF (Nat.le_refl _) (Nat.zero_le _) (by decide) (.inr (by decide))
      (.inl (by decide)) (by simp only [VG.Proof.MlDsa.X86.KeyGen.scrLen, hF.sw, oSS]; omega))
  exact { ctx := h'
          good := by rw [VG.Proof.MlDsa.X86.KeyGen.acc_keep hp (N := 80) (by omega) hs.acc fr]; exact h.good
          small := h.small
          aS := fun e he => VG.Proof.MlDsa.X86.KeyGen.keepPolyD hp (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (hs.aS e he) fr (h.aS e he)
          s2 := fun i hi => VG.Proof.MlDsa.X86.KeyGen.keepPolyD hp (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (hs.s2 i hi) fr (h.s2 i hi)
          s1 := fun j' hj' => if e : j' = j then by
              subst e; rw [VG.Proof.MlDsa.X86.KeyGen.ifp (Nat.lt_succ_self j'), ← hS.2]; exact out
            else by
              have := VG.Proof.MlDsa.X86.KeyGen.keepPolyD hp (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (by layp hF) fr (h.s1 j' hj')
              by_cases hlt : j' < j
              · rwa [VG.Proof.MlDsa.X86.KeyGen.ifp hlt, ← VG.Proof.MlDsa.X86.KeyGen.ifp (show j' < j + 1 by omega) (VG.Spec.MlDsa.ntt (toRq (S j'))) (toRq (S j'))] at this
              · rwa [VG.Proof.MlDsa.X86.KeyGen.ifn hlt, ← VG.Proof.MlDsa.X86.KeyGen.ifn (show ¬ j' < j + 1 by omega) (VG.Spec.MlDsa.ntt (toRq (S j'))) (toRq (S j'))] at this
          pk0 := by rw [keepBytes hp (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) hs.pk0 fr]; exact h.pk0
          sk0 := by rw [keepBytes hp (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) hs.sk0 fr]; exact h.sk0
          sk1 := by rw [keepBytes hp (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) hs.sk1 fr]; exact h.sk1
          packs := fun r hr => by rw [keepBytes hp (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (hs.packs r hr) fr]; exact h.packs r hr
          rows := fun _ h => absurd h (Nat.not_lt_zero _) }

end

end VG.Proof.MlDsa.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.KeyGen.RestRow`. -/
section

/-!
# ML-DSA key generation on x86 (32-bit): the rows of `t`

Row `i` (`row_piece`): `t = Σⱼ Â[i, j] ŝ₁[j]` (`dotK`, a product then `ℓ - 1`
products added), `NTT⁻¹`, `s₂[i]` added (`tK`), `Power2Round`, and `t₁`
`SimpleBitPack`ed to `pk` and `t₀` `BitPack`ed to `sk`.
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt nttInv polyAt coeffAt Reduced PolyIs NatPolyIs bitPack
  simpleBitPack power2Round ofInt)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K)
open VG.Spec.Sha3 (bytesAt)

/-- During row `i`: the keys so far, and `t` holding `v`. -/
abbrev RowT (p : Params) (i : Nat) (v : (Nat → VG.Spec.MlDsa.Poly) → (Nat → IPoly) → VG.Spec.MlDsa.Poly) (s₀ s : State) : Prop :=
  ∃ A S, VG.Proof.MlDsa.X86.KeyGen.KR p A S (p.ℓ + p.k) p.ℓ i s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (tB p)) (v A S)

theorem KR.nttS {p : Params} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {nr : Nat} {s₀ s : State}
    (h : VG.Proof.MlDsa.X86.KeyGen.KR p A S (p.ℓ + p.k) p.ℓ nr s₀ s) {j : Nat} (hj : j < p.ℓ) :
    PolyIs s.mem (Buf.addr s₀ (VG.Impl.MlDsa.X86.KeyGen.sB p j)) (VG.Spec.MlDsa.ntt (toRq (S j))) := by
  have := h.s1 j hj; rwa [VG.Proof.MlDsa.X86.KeyGen.ifp hj] at this

theorem t0_params : ((4095 : Nat), (4096 : Nat)) ∈ Spec.MlDsa.bitPackParams := by decide

theorem power2Round_fst' (c : Spec.MlDsa.Zq) : (VG.Spec.MlDsa.power2Round c).1.toNat ≤ 1023 := by
  have := Proof.MlDsa.KeyGen.power2Round_fst c; omega

/-! ## `SafeR` of the buffers a row writes, once each -/

theorem safe_poly {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) {j : Nat} (hj : j < 3) :
    VG.Proof.MlDsa.X86.KeyGen.SafeR p (p.ℓ + p.k) i [pB (p.k * p.ℓ + p.ℓ + p.k + j)] := by
  have := hF.k; have := hF.l; have := hF.kl
  exact SafeR.sc hF (by omega) (by omega) (by decide) (.inr (by simp only [oACC, VG.Impl.MlDsa.X86.KeyGen.oP]; omega))
    (.inr (.inr (by simp only [VG.Impl.MlDsa.X86.KeyGen.oP]; omega))) (by simp only [VG.Proof.MlDsa.X86.KeyGen.scrLen, hF.sw, VG.Impl.MlDsa.X86.KeyGen.oP]; omega)

theorem safe_t {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) : VG.Proof.MlDsa.X86.KeyGen.SafeR p (p.ℓ + p.k) i [tB p] := by
  have := VG.Proof.MlDsa.X86.KeyGen.safe_poly hF hi (j := 0) (by decide); rwa [Nat.add_zero] at this

theorem safe_inv {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.X86.KeyGen.SafeR p (p.ℓ + p.k) i [tB p, ssB 1024] := by
  have := hF.k; have := hF.l; have := hF.kl
  exact (VG.Proof.MlDsa.X86.KeyGen.safe_t hF hi).append (bs₁ := [_]) (SafeR.sc (o := oSS) (l := 1024) hF (by omega) (by omega) (by decide)
    (.inr (by decide)) (.inl (by decide)) (by simp only [VG.Proof.MlDsa.X86.KeyGen.scrLen, hF.sw, oSS]; omega))

theorem safe_p2r {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.X86.KeyGen.SafeR p (p.ℓ + p.k) i [t1B p, t0B p] :=
  (VG.Proof.MlDsa.X86.KeyGen.safe_poly hF hi (j := 1) (by decide)).append (bs₁ := [_]) (VG.Proof.MlDsa.X86.KeyGen.safe_poly hF hi (j := 2) (by decide))

theorem safe_sbp {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.X86.KeyGen.SafeR p (p.ℓ + p.k) i [⟨1, 32 + 320 * i, 320⟩] :=
  SafeR.pk hF (Nat.le_refl _) (Nat.le_of_lt hi) (by decide) (Nat.le_refl _) (by rw [hF.pk]; omega)

theorem safe_bp {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.X86.KeyGen.SafeR p (p.ℓ + p.k) i [⟨2, oT0 p + 416 * i, 416⟩] := by
  have := hF.k; have := hF.l
  exact SafeR.sk hF (Nat.le_refl _) (Nat.le_of_lt hi) (by decide) (by simp only [oT0]; omega)
    (.inr (by simp only [oT0]; omega)) (.inr (Nat.le_refl _)) (by rw [hF.sk]; omega)

section
variable {P : Prims} (hP : VG.Proof.MlDsa.X86.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) {i : Nat} (hi : i < p.k)
include hP hF hi

theorem mul_row : VG.Proof.MlDsa.X86.KeyGen.KP p (VG.Proof.MlDsa.X86.KeyGen.KRx p (p.ℓ + p.k) p.ℓ i) (VG.Proof.MlDsa.X86.KeyGen.RowT p i fun A S => dotK p A S i 1)
    (VG.Impl.MlDsa.X86.KeyGen.callP kS "vg_mldsa_multiply_ntt" P.mul [.buf (tB p), .buf (aB (p.ℓ * i)), .buf (VG.Impl.MlDsa.X86.KeyGen.sB p 0)]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have he : p.ℓ * i < p.k * p.ℓ := by
    have : p.ℓ * (i + 1) ≤ p.ℓ * p.k := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_comm p.k]; rw [Nat.mul_succ] at this; omega
  refine VG.Proof.MlDsa.X86.KeyGen.mul_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) _ _ _ _ _ _ hP.mul (by layp hF [VG.Proof.MlDsa.X86.KeyGen.chk3]) (Nat.le_of_eq (VG.Proof.MlDsa.X86.KeyGen.YK_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨A, S, h⟩ => ⟨h.ctx, (h.aS _ he).1, (h.nttS (by omega)).1⟩)
    fun s₀ s s' hp ⟨A, S, h⟩ h' fr out => ⟨A, S, h.keep hp (N := 80) (by omega) (by exact VG.Proof.MlDsa.X86.KeyGen.safe_t hF hi)
      (fun _ _ => by layp hF) fr h', ?_⟩
  rw [(h.aS _ he).2, (h.nttS (by omega)).2, ← Proof.MlDsa.KeyGen.dotK_one] at out
  exact out

theorem mulAdd_row {j : Nat} (hj₁ : 1 ≤ j) (hj : j < p.ℓ) :
    VG.Proof.MlDsa.X86.KeyGen.KP p (VG.Proof.MlDsa.X86.KeyGen.RowT p i fun A S => dotK p A S i j) (VG.Proof.MlDsa.X86.KeyGen.RowT p i fun A S => dotK p A S i (j + 1)) (mulAddS P p i j) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have he : p.ℓ * i + j < p.k * p.ℓ := by
    have : p.ℓ * (i + 1) ≤ p.ℓ * p.k := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_comm p.k]; rw [Nat.mul_succ] at this; omega
  refine VG.Proof.MlDsa.X86.KeyGen.mulAdd_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) _ _ _ _ _ _ hP.mulAdd (by layp hF [VG.Proof.MlDsa.X86.KeyGen.chk3]) (Nat.le_of_eq (VG.Proof.MlDsa.X86.KeyGen.YK_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨A, S, h, ht⟩ => ⟨h.ctx, ht.1, (h.aS _ he).1, (h.nttS hj).1⟩)
    fun s₀ s s' hp ⟨A, S, h, ht⟩ h' fr out => ⟨A, S, h.keep hp (N := 80) (by omega) (by exact VG.Proof.MlDsa.X86.KeyGen.safe_t hF hi)
      (fun _ _ => by layp hF) fr h', ?_⟩
  rw [ht.2, (h.aS _ he).2, (h.nttS hj).2, ← Proof.MlDsa.KeyGen.dotK_succ] at out
  exact out

theorem inv_row : VG.Proof.MlDsa.X86.KeyGen.KP p (VG.Proof.MlDsa.X86.KeyGen.RowT p i fun A S => dotK p A S i p.ℓ) (VG.Proof.MlDsa.X86.KeyGen.RowT p i fun A S => VG.Spec.MlDsa.nttInv (dotK p A S i p.ℓ))
    (VG.Impl.MlDsa.X86.KeyGen.callP kS "vg_mldsa_inv_ntt" P.invNtt [.buf (tB p), .buf (ssB 1024)]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine VG.Proof.MlDsa.X86.KeyGen.inPlace_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) hP.invNtt _ _ _ _ (by layp hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.KeyGen.YK_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun s₀ s _ ⟨A, S, h, ht⟩ => ⟨h.ctx, ht.1⟩)
    fun s₀ s s' hp ⟨A, S, h, ht⟩ h' fr out => ⟨A, S, h.keep hp (N := 80) (by omega) (by exact VG.Proof.MlDsa.X86.KeyGen.safe_inv hF hi)
      (fun _ _ => by layp hF) fr h', ?_⟩
  rw [ht.2] at out
  exact out

theorem add_row : VG.Proof.MlDsa.X86.KeyGen.KP p (VG.Proof.MlDsa.X86.KeyGen.RowT p i fun A S => VG.Spec.MlDsa.nttInv (dotK p A S i p.ℓ)) (VG.Proof.MlDsa.X86.KeyGen.RowT p i fun A S => tK p A S i)
    (VG.Impl.MlDsa.X86.KeyGen.callP kS "vg_mldsa_add" P.add [.buf (tB p), .buf (VG.Impl.MlDsa.X86.KeyGen.sB p (p.ℓ + i))]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine VG.Proof.MlDsa.X86.KeyGen.acc_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) hP.add _ _ _ _ (by layp hF) (Nat.le_of_eq (VG.Proof.MlDsa.X86.KeyGen.YK_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun s₀ s _ ⟨A, S, h, ht⟩ => ⟨h.ctx, ht.1, (h.s2 i hi).1⟩)
    fun s₀ s s' hp ⟨A, S, h, ht⟩ h' fr out => ⟨A, S, h.keep hp (N := 80) (by omega) (by exact VG.Proof.MlDsa.X86.KeyGen.safe_t hF hi)
      (fun _ _ => by layp hF) fr h', ?_⟩
  rw [ht.2, (h.s2 i hi).2] at out
  exact out

/-- After `Power2Round` of row `i`. -/
abbrev RowP (p : Params) (i : Nat) (s₀ s : State) : Prop :=
  ∃ A S, VG.Proof.MlDsa.X86.KeyGen.KR p A S (p.ℓ + p.k) p.ℓ i s₀ s ∧ NatPolyIs s.mem (Buf.addr s₀ (t1B p)) (t1K p A S i) ∧
    PolyIs s.mem (Buf.addr s₀ (t0B p)) ((tK p A S i).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2)

theorem p2r_row : VG.Proof.MlDsa.X86.KeyGen.KP p (VG.Proof.MlDsa.X86.KeyGen.RowT p i fun A S => tK p A S i) (VG.Proof.MlDsa.X86.KeyGen.RowP p i)
    (VG.Impl.MlDsa.X86.KeyGen.callP kS "vg_mldsa_power2round" P.power2Round [.buf (tB p), .buf (t1B p), .buf (t0B p)]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine VG.Proof.MlDsa.X86.KeyGen.p2r_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) _ _ _ _ _ _ hP.power2Round (by layp hF [VG.Proof.MlDsa.X86.KeyGen.chkP2]) (Nat.le_of_eq (VG.Proof.MlDsa.X86.KeyGen.YK_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun s₀ s _ ⟨A, S, h, ht⟩ => ⟨h.ctx, ht.1⟩)
    fun s₀ s s' hp ⟨A, S, h, ht⟩ h' fr o₁ o₂ => ⟨A, S, h.keep hp (N := 80) (by omega) (by exact VG.Proof.MlDsa.X86.KeyGen.safe_p2r hF hi)
      (fun _ _ => by layp hF) fr h', ?_, ?_⟩
  · rw [ht.2] at o₁; exact o₁
  · rw [ht.2] at o₂; exact o₂

/-- After `t₁` is packed. -/
abbrev RowQ (p : Params) (i : Nat) (s₀ s : State) : Prop :=
  ∃ A S, VG.Proof.MlDsa.X86.KeyGen.KR p A S (p.ℓ + p.k) p.ℓ i s₀ s ∧
    PolyIs s.mem (Buf.addr s₀ (t0B p)) ((tK p A S i).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2) ∧
    bytesAt s.mem (Buf.addr s₀ ⟨1, 32 + 320 * i, 320⟩) 320 = VG.Spec.MlDsa.simpleBitPack (t1K p A S i) 1023

theorem sbp_row : VG.Proof.MlDsa.X86.KeyGen.KP p (VG.Proof.MlDsa.X86.KeyGen.RowP p i) (VG.Proof.MlDsa.X86.KeyGen.RowQ p i)
    (VG.Impl.MlDsa.X86.KeyGen.callP kS "vg_mldsa_simple_bit_pack" P.simpleBitPack
      [.buf (t1B p), .imm 1023, .buf ⟨1, 32 + 320 * i, 320⟩, .imm 320]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine VG.Proof.MlDsa.X86.KeyGen.sbp_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) hP.simpleBitPack _ _ 1023 _ _ 320 (by decide) (by decide) (by layp hF)
    (Nat.le_of_eq (VG.Proof.MlDsa.X86.KeyGen.YK_stk p).symm) (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨A, S, h, h1, _⟩ => ⟨h.ctx, fun j hj => ?_⟩)
    fun s₀ s s' hp ⟨A, S, h, h1, h0⟩ h' fr out => ⟨A, S, h.keep hp (N := 80) (by omega) (by exact VG.Proof.MlDsa.X86.KeyGen.safe_sbp hF hi)
      (fun _ _ => by layp hF) fr h', VG.Proof.MlDsa.X86.KeyGen.keepPolyD hp (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (by layp hF) fr h0, ?_⟩
  · have e := congrArg (fun v : Vector Nat 256 => v[j]'hj) h1
    simp only [Spec.MlDsa.natPolyAt, Vector.getElem_ofFn, t1K, Vector.getElem_map] at e
    rw [e]; exact VG.Proof.MlDsa.X86.KeyGen.power2Round_fst' _
  · rw [out, h1]

theorem bp_row : VG.Proof.MlDsa.X86.KeyGen.KP p (VG.Proof.MlDsa.X86.KeyGen.RowQ p i) (VG.Proof.MlDsa.X86.KeyGen.KRx p (p.ℓ + p.k) p.ℓ (i + 1))
    (VG.Impl.MlDsa.X86.KeyGen.callP kS "vg_mldsa_bit_pack" P.bitPack
      [.buf (t0B p), .imm 4095, .imm 4096, .buf ⟨2, oT0 p + 416 * i, 416⟩, .imm 416]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine VG.Proof.MlDsa.X86.KeyGen.bp_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) hP.bitPack _ _ 4095 4096 _ _ 416 VG.Proof.MlDsa.X86.KeyGen.t0_params (by decide) (by layp hF)
    (Nat.le_of_eq (VG.Proof.MlDsa.X86.KeyGen.YK_stk p).symm) (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨A, S, h, h0, _⟩ => ⟨h.ctx, h0.1, fun j hj => ?_⟩)
    fun s₀ s s' hp ⟨A, S, h, h0, hb⟩ h' fr out => ⟨A, S, ?_⟩
  · rw [VG.Proof.MlDsa.X86.KeyGen.coeff_val h0 hj]
    simp only [Vector.getElem_map]
    have := Proof.MlDsa.KeyGen.power2Round_snd ((tK p A S i)[j]'hj)
    rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
    omega
  · have k := h.keep hp (N := 80) (by omega) (by exact VG.Proof.MlDsa.X86.KeyGen.safe_bp hF hi) (fun _ _ => by layp hF) fr h'
    refine { k with rows := fun i' hi' => ?_ }
    rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
    · exact k.rows i' hi'
    · refine ⟨by rw [keepBytes hp (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (by layp hF) fr]; exact hb, ?_⟩
      rw [out, h0.2, Vector.map_map]
      congr 1
      refine Vector.map_congr_left fun c _ => ?_
      have := Proof.MlDsa.KeyGen.power2Round_snd c
      exact Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)

theorem row_piece : VG.Proof.MlDsa.X86.KeyGen.KP p (VG.Proof.MlDsa.X86.KeyGen.KRx p (p.ℓ + p.k) p.ℓ i) (VG.Proof.MlDsa.X86.KeyGen.KRx p (p.ℓ + p.k) p.ℓ (i + 1)) (row P p i) := by
  have hl := hF.l
  unfold row
  refine (VG.Proof.MlDsa.X86.KeyGen.mul_row hP hF hi).seq (Piece.seq ?_ ((VG.Proof.MlDsa.X86.KeyGen.inv_row hP hF hi).seq ((VG.Proof.MlDsa.X86.KeyGen.add_row hP hF hi).seq
    ((VG.Proof.MlDsa.X86.KeyGen.p2r_row hP hF hi).seq ((VG.Proof.MlDsa.X86.KeyGen.sbp_row hP hF hi).seq (VG.Proof.MlDsa.X86.KeyGen.bp_row hP hF hi))))))
  refine Piece.mono (VG.Proof.MlDsa.X86.KeyGen.seqR_piece (I := fun j => VG.Proof.MlDsa.X86.KeyGen.RowT p i fun A S => dotK p A S i j) (p.ℓ - 1) 1
    fun j h1 h2 => VG.Proof.MlDsa.X86.KeyGen.mulAdd_row hP hF hi h1 (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega] at h

end

end VG.Proof.MlDsa.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.KeyGen.NoSp`. -/
section

/-!
# ML-DSA on x86 (32-bit): code that writes `esp` only by frames and calls

`NoSp` of code built from pieces, for any code of the primitives it calls:
sequences (`NoSp.seq`, `NoSp.seqR`) and calls with their arguments
(`NoSp.callP`, `NoSp.callPR`). Code that calls no primitive is checked by
evaluation (`NoSp.of_all`).
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86
open VG.Impl.MlDsa.X86.KeyGen (Arg argRegs setArgs argRs callP callPR seqR)

theorem NoSp.seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := fun i hi => by
  simp only [VG.instrs, List.mem_append] at hi
  rcases hi with h | h
  exacts [ha i h, hb i h]

theorem NoSp.seqR {f : Nat → Prog isa} (h : ∀ k, NoSp (f k)) : ∀ a n, NoSp (VG.Impl.MlDsa.X86.KeyGen.seqR f a n)
  | _, 0 => fun i hi => by simp [Impl.MlDsa.X86.KeyGen.seqR, VG.instrs] at hi
  | a, n + 1 => NoSp.seq (h a) (NoSp.seqR h (a + 1) n)

theorem setArgs_nosp (sc : Nat) : ∀ (rs : List Reg) (as : List Arg), (∀ r ∈ rs, r ≠ .esp) →
    ∀ i ∈ setArgs sc rs as, Taint.clobbers i .esp = false
  | [], _, _, _, hi => by simp [setArgs] at hi
  | _ :: _, [], _, _, hi => by simp [setArgs] at hi
  | r :: rs, a :: as, hr, i, hi => by
    simp only [setArgs, List.mem_append] at hi
    rcases hi with hi | hi
    · have hr0 := hr r (List.mem_cons_self ..)
      cases a with
      | buf b =>
        simp only [Impl.MlDsa.X86.KeyGen.Arg.set, Impl.MlKem.X86.ptrTo] at hi
        split at hi <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hi <;>
          rcases hi with rfl | rfl <;> simp [Taint.clobbers, Taint.dst, hr0]
      | imm v =>
        simp only [Impl.MlDsa.X86.KeyGen.Arg.set, List.mem_singleton] at hi
        subst hi; simp [Taint.clobbers, Taint.dst, hr0]
    · exact VG.Proof.MlDsa.X86.KeyGen.setArgs_nosp sc rs as (fun r' h => hr r' (List.mem_cons_of_mem _ h)) i hi

theorem NoSp.callP {sc : Nat} {nm : String} {c : Prog isa} {as : List Arg} (hc : NoSp c) :
    NoSp (VG.Impl.MlDsa.X86.KeyGen.callP sc nm c as) := by
  refine NoSp.seq (fun i hi => VG.Proof.MlDsa.X86.KeyGen.setArgs_nosp sc argRegs as (by decide) i hi) fun i hi => ?_
  simp only [Impl.MlKem.X86.callWith, VG.instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact hc i hi
  · rfl

theorem NoSp.callPR {sc : Nat} {nm : String} {c : Prog isa} {as : List Arg} (hc : NoSp c) :
    NoSp (VG.Impl.MlDsa.X86.KeyGen.callPR sc nm c as) := by
  refine NoSp.seq (fun i hi => VG.Proof.MlDsa.X86.KeyGen.setArgs_nosp sc argRegs as (by decide) i hi) fun i hi => ?_
  simp only [Impl.MlKem.X86.callRet, VG.instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact hc i hi
  · rfl

end VG.Proof.MlDsa.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Top`. -/
section

/-!
# ML-DSA key generation on x86 (32-bit): `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

The body, piece by piece (`body_piece`), for any parameter set of Table 1 and
any verified implementations of the primitives: it returns 1 with
`KeyGen_internal(ξ)` in `pk` and `sk` if every sampler succeeded (for some
bounds), and 0 if key generation fails within the least bounds (`post`); it
leaks only the pointers, `ρ` and what `RejBoundedPoly` leaks; so the function
meets the shared contract (`keyGen_verified`).
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt Reduced PolyIs bitPack simpleBitPack keyGenInternal)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K pkK skK)
open VG.Spec.Sha3 (bytesAt)

/-! ## `tr = H(pk, 64)`, and the value returned -/

/-- At the end: the keys, and the value returned. -/
structure KFin (p : Params) (s₀ s : State) : Prop where
  ex : ∃ A S, VG.Proof.MlDsa.X86.KeyGen.KR p A S (p.ℓ + p.k) p.ℓ p.k s₀ s ∧
    bytesAt s.mem (Buf.addr s₀ ⟨2, 64, 64⟩) 64 = Spec.MlDsa.H (bytesAt s.mem (Buf.addr s₀ ⟨1, 0, p.pkLen⟩) p.pkLen) 64

theorem trHash_piece {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) : VG.Proof.MlDsa.X86.KeyGen.KP p (VG.Proof.MlDsa.X86.KeyGen.KRx p (p.ℓ + p.k) p.ℓ p.k) (VG.Proof.MlDsa.X86.KeyGen.KFin p) (trHash p) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine hash1_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) 0 200 136 0x1f ⟨1, 0, p.pkLen⟩ ⟨2, 64, 64⟩ Proof.MlKem.rate136 (by layp hF)
    (by rw [VG.Proof.MlDsa.X86.KeyGen.YK_stk]; omega) (by show p.pkLen < 2 ^ 32; rw [hF.pk]; omega) (by decide) (by taint_decide) (h₁ := .block [])
    (by kernel_rfl) (h₃ := .block []) (by kernel_rfl) (h₄ := .block []) (by kernel_rfl)
    (fun _ _ _ ⟨_, _, h⟩ => h.ctx) fun s₀ s s' hp ⟨A, S, h⟩ h' fr out => ⟨A, S, ?_, ?_⟩
  · have hs : VG.Proof.MlDsa.X86.KeyGen.SafeR p (p.ℓ + p.k) p.k [sb 0 200, sb 200 640, ⟨2, 64, 64⟩] :=
      (SafeR.sc hF (Nat.le_refl _) (Nat.le_refl _) (by decide) (.inl (by decide)) (.inl (by decide))
        (by simp only [VG.Proof.MlDsa.X86.KeyGen.scrLen, hF.sw]; omega)).append (bs₁ := [_])
      ((SafeR.sc hF (Nat.le_refl _) (Nat.le_refl _) (by decide) (.inl (by decide)) (.inl (by decide))
        (by simp only [VG.Proof.MlDsa.X86.KeyGen.scrLen, hF.sw]; omega)).append (bs₁ := [_])
      (SafeR.sk hF (Nat.le_refl _) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide))
        (.inl (by simp only [oT0]; omega)) (by rw [hF.sk, oT0]; omega)))
    exact h.keep hp (N := 40) (by omega) hs (fun _ _ => by layp hF) fr h'
  · rw [out, VG.Proof.MlDsa.X86.KeyGen.sponge_H, keepBytes hp (N := 40) (VG.Proof.MlDsa.X86.KeyGen.stkN (by omega)) (b := ⟨1, 0, p.pkLen⟩) (by layp hF) fr]

/-- The body's end: the keys, and `eax` the AND of the samplers' results. -/
structure Done (p : Params) (s₀ s : State) : Prop extends VG.Proof.MlDsa.X86.KeyGen.KFin p s₀ s where
  eax : s.gpr .eax = VG.Proof.MlDsa.X86.KeyGen.accV s₀ s

theorem ret_piece {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) :
    VG.Proof.MlDsa.X86.KeyGen.KP p (VG.Proof.MlDsa.X86.KeyGen.KFin p) (fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.KeyGen.YK p) s₀ s ∧ VG.Proof.MlDsa.X86.KeyGen.Done p s₀ s) (.block [.mov .eax (.mem (at_ .esi oACC))]) := by
  refine ld32_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) oACC (by layp hF) (ht := .block []) (by kernel_rfl)
    (fun _ _ _ h => by obtain ⟨_, _, h, _⟩ := h.ex; exact h.ctx) fun s₀ s s' hp h h' m' e => ⟨h', ?_, ?_⟩
  · obtain ⟨A, S, hk, htr⟩ := h.ex
    exact ⟨A, S, hk.keep hp (bs := []) (N := 0) (by omega) (by safeR hF) (fun _ _ => by layp hF) (by rw [m']; exact Frame.refl _ _)
      h', by rw [m']; exact htr⟩
  · rw [e, VG.Proof.MlDsa.X86.KeyGen.accV, m']; rfl

/-! ## The body -/

theorem body_piece {P : Prims} (hP : VG.Proof.MlDsa.X86.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) :
    VG.Proof.MlDsa.X86.KeyGen.KP p (fun s₀ s => s = P0 s₀) (fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlDsa.X86.KeyGen.YK p) s₀ s ∧ VG.Proof.MlDsa.X86.KeyGen.Done p s₀ s) (body P p) := by
  have hk := hF.k; have hl := hF.l
  unfold body
  refine (ldsc_piece (Y := VG.Proof.MlDsa.X86.KeyGen.YK p) (ht := .block []) (by kernel_rfl)).seq ((VG.Proof.MlDsa.X86.KeyGen.seeds_piece hF).seq ?_)
  refine Piece.seq (B := VG.Proof.MlDsa.X86.KeyGen.KSamp p (p.k * p.ℓ) 0) (Piece.mono (VG.Proof.MlDsa.X86.KeyGen.seqR_piece (I := fun e => VG.Proof.MlDsa.X86.KeyGen.KSamp p e 0)
    (p.k * p.ℓ) 0 fun e _ he => VG.Proof.MlDsa.X86.KeyGen.expA_piece hP hF (by omega)) (fun s₀ s _ h => ⟨h.1, fun _ => Proof.MlDsa.KeyGen.zeroI.map
      (fun _ => 0), fun _ => Proof.MlDsa.KeyGen.zeroI, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), .inl ⟨h.2, ⟨0, 0, 0, 0⟩, fun _ h => absurd h (Nat.not_lt_zero _),
        fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩) fun _ _ _ h => by simpa using h) ?_
  refine Piece.seq (B := VG.Proof.MlDsa.X86.KeyGen.KSamp p (p.k * p.ℓ) (p.ℓ + p.k)) (Piece.mono (VG.Proof.MlDsa.X86.KeyGen.seqR_piece
    (I := fun r => VG.Proof.MlDsa.X86.KeyGen.KSamp p (p.k * p.ℓ) r) (p.ℓ + p.k) 0 fun r _ hr => VG.Proof.MlDsa.X86.KeyGen.expS_piece hP hF (by omega))
    (fun _ _ _ h => h) fun _ _ _ h => by simpa using h) ?_
  refine (VG.Proof.MlDsa.X86.KeyGen.copies_piece hF).seq ?_
  refine Piece.seq (B := VG.Proof.MlDsa.X86.KeyGen.KRx p (p.ℓ + p.k) 0 0) (Piece.mono (VG.Proof.MlDsa.X86.KeyGen.seqR_piece (I := fun r => VG.Proof.MlDsa.X86.KeyGen.KRx p r 0 0) (p.ℓ + p.k) 0
    fun r _ hr => VG.Proof.MlDsa.X86.KeyGen.packS_piece hP hF (by omega)) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h) ?_
  refine Piece.seq (B := VG.Proof.MlDsa.X86.KeyGen.KRx p (p.ℓ + p.k) p.ℓ 0) (Piece.mono (VG.Proof.MlDsa.X86.KeyGen.seqR_piece (I := fun j => VG.Proof.MlDsa.X86.KeyGen.KRx p (p.ℓ + p.k) j 0) p.ℓ 0
    fun j _ hj => VG.Proof.MlDsa.X86.KeyGen.nttS_piece hP hF (by omega)) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h) ?_
  refine Piece.seq (B := VG.Proof.MlDsa.X86.KeyGen.KRx p (p.ℓ + p.k) p.ℓ p.k) (Piece.mono (VG.Proof.MlDsa.X86.KeyGen.seqR_piece
    (I := fun i => VG.Proof.MlDsa.X86.KeyGen.KRx p (p.ℓ + p.k) p.ℓ i) p.k 0 fun i _ hi => VG.Proof.MlDsa.X86.KeyGen.row_piece hP hF (by omega))
    (fun _ _ _ h => h) fun _ _ _ h => by simpa using h) ?_
  exact (VG.Proof.MlDsa.X86.KeyGen.trHash_piece hF).seq (VG.Proof.MlDsa.X86.KeyGen.ret_piece hF)

theorem body_nosp {P : Prims} (hP : VG.Proof.MlDsa.X86.KeyGen.PrimsOk P) (p : Params) : NoSp (body P p) := by
  unfold body
  refine NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq
    (NoSp.seqR (fun e => ?_) _ _) (NoSp.seq (NoSp.seqR (fun r => ?_) _ _) (NoSp.seq (NoSp.of_all (by kernel_rfl))
    (NoSp.seq (NoSp.seqR (fun r => NoSp.callP hP.bitPack.nosp) _ _) (NoSp.seq (NoSp.seqR (fun j =>
      NoSp.callP hP.ntt.nosp) _ _) (NoSp.seq (NoSp.seqR (fun i => ?_) _ _) (NoSp.seq (NoSp.of_all (by kernel_rfl))
    (NoSp.of_all (by kernel_rfl))))))))))
  · unfold expA
    exact NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq (NoSp.of_all (by kernel_rfl))
      (NoSp.seq (NoSp.callPR hP.rejNtt.nosp) (NoSp.of_all (by kernel_rfl))))
  · unfold expS
    exact NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq (NoSp.callPR hP.rejBounded.nosp)
      (NoSp.of_all (by kernel_rfl)))
  · unfold row
    exact NoSp.seq (NoSp.callP hP.mul.nosp) (NoSp.seq (NoSp.seqR (fun j => NoSp.callP hP.mulAdd.nosp) _ _)
      (NoSp.seq (NoSp.callP hP.invNtt.nosp) (NoSp.seq (NoSp.callP hP.add.nosp) (NoSp.seq
        (NoSp.callP hP.power2Round.nosp) (NoSp.seq (NoSp.callP hP.simpleBitPack.nosp) (NoSp.callP hP.bitPack.nosp))))))

/-! ## The keys in memory -/

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      VG.Proof.MlDsa.X86.KeyGen.flatMap_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem t1Max_eq : Spec.MlDsa.t1Max = 1023 := by decide

section
variable {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) {s₀ s : State} (hp : TPre (VG.Proof.MlDsa.X86.KeyGen.YK p) s₀)
include hF hp

omit hF in
/-- A buffer of `pk` or `sk`, from the start of its argument. -/
theorem addr_arg {a o l : Nat} (h : (VG.Proof.MlDsa.X86.KeyGen.YK p).ok ⟨a, o, l⟩ = true) :
    Buf.addr s₀ ⟨a, o, l⟩ = (arg s₀ a).setWidth 64 + BitVec.ofNat 64 o := Buf.addr_eq hp h

theorem pk_bytes {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {np nj : Nat} (h : VG.Proof.MlDsa.X86.KeyGen.KR p A S np nj p.k s₀ s) :
    bytesAt s.mem (Buf.addr s₀ ⟨1, 0, p.pkLen⟩) p.pkLen = pkK p A S (VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have e0 := VG.Proof.MlDsa.X86.KeyGen.addr_arg hp (a := 1) (o := 0) (l := p.pkLen) (by layp hF)
  have e1 := VG.Proof.MlDsa.X86.KeyGen.addr_arg hp (a := 1) (o := 0) (l := 32) (by layp hF)
  rw [BitVec.add_zero] at e0 e1
  rw [hF.pk] at e0 ⊢
  rw [e0, Proof.MlKem.bytesAt_add, ← e1, h.pk0, e1, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ 32 320 p.k, pkK,
    VG.Proof.MlDsa.X86.KeyGen.t1Max_eq]
  refine congrArg _ (VG.Proof.MlDsa.X86.KeyGen.flatMap_congr_mem fun i hi => ?_)
  have hi := List.mem_range.mp hi
  rw [← VG.Proof.MlDsa.X86.KeyGen.addr_arg hp (a := 1) (o := 32 + 320 * i) (l := 320) (by layp hF)]
  exact (h.rows i hi).1

theorem sk_bytes {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {nj : Nat} (h : VG.Proof.MlDsa.X86.KeyGen.KR p A S (p.ℓ + p.k) nj p.k s₀ s)
    (htr : bytesAt s.mem (Buf.addr s₀ ⟨2, 64, 64⟩) 64 = Spec.MlDsa.H (pkK p A S (VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀)) 64) :
    bytesAt s.mem (Buf.addr s₀ ⟨2, 0, p.skLen⟩) p.skLen = skK p A S (VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀) (VG.Proof.MlDsa.X86.KeyGen.kOf p s₀) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have a0 := VG.Proof.MlDsa.X86.KeyGen.addr_arg hp (a := 2) (o := 0) (l := p.skLen) (by layp hF)
  have a1 := VG.Proof.MlDsa.X86.KeyGen.addr_arg hp (a := 2) (o := 0) (l := 32) (by layp hF)
  have a2 := VG.Proof.MlDsa.X86.KeyGen.addr_arg hp (a := 2) (o := 32) (l := 32) (by layp hF)
  have a3 := VG.Proof.MlDsa.X86.KeyGen.addr_arg hp (a := 2) (o := 64) (l := 64) (by layp hF)
  rw [BitVec.add_zero] at a0 a1
  have h0 : bytesAt s.mem ((arg s₀ 2).setWidth 64) 32 = VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀ := by rw [← a1]; exact h.sk0
  have h1 : bytesAt s.mem ((arg s₀ 2).setWidth 64 + BitVec.ofNat 64 32) 32 = VG.Proof.MlDsa.X86.KeyGen.kOf p s₀ := by rw [← a2]; exact h.sk1
  have h2 : bytesAt s.mem ((arg s₀ 2).setWidth 64 + BitVec.ofNat 64 (32 + 32)) 64 =
      Spec.MlDsa.H (pkK p A S (VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀)) 64 := by rw [← a3]; exact htr
  rw [a0, hF.sk, oT0, show 128 = 32 + 32 + 64 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add,
    Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h0, h1, h2]
  have p1 := Proof.MlDsa.KeyGen.bytesAt_pieces s.mem ((arg s₀ 2).setWidth 64) (32 + 32 + 64) (lenS p) (p.ℓ + p.k)
  have p2 := Proof.MlDsa.KeyGen.bytesAt_pieces s.mem ((arg s₀ 2).setWidth 64) (oT0 p) 416 p.k
  rw [oT0] at p2
  have q1 : (List.range (p.ℓ + p.k)).flatMap (fun i => bytesAt s.mem ((arg s₀ 2).setWidth 64 +
      BitVec.ofNat 64 (32 + 32 + 64 + lenS p * i)) (lenS p)) =
      (List.range (p.ℓ + p.k)).flatMap fun r => VG.Spec.MlDsa.bitPack (S r) p.η p.η := VG.Proof.MlDsa.X86.KeyGen.flatMap_congr_mem fun r hr => by
    rw [← VG.Proof.MlDsa.X86.KeyGen.addr_arg hp (a := 2) (o := 32 + 32 + 64 + lenS p * r) (l := lenS p) (by have := List.mem_range.mp hr; layp hF)]
    exact h.packs r (List.mem_range.mp hr)
  have q2 : (List.range p.k).flatMap (fun i => bytesAt s.mem ((arg s₀ 2).setWidth 64 +
      BitVec.ofNat 64 (128 + lenS p * (p.ℓ + p.k) + 416 * i)) 416) =
      (List.range p.k).flatMap fun i => VG.Spec.MlDsa.bitPack (t0K p A S i) 4095 4096 := VG.Proof.MlDsa.X86.KeyGen.flatMap_congr_mem fun i hi => by
    rw [show 128 + lenS p * (p.ℓ + p.k) = oT0 p from rfl,
      ← VG.Proof.MlDsa.X86.KeyGen.addr_arg hp (a := 2) (o := oT0 p + 416 * i) (l := 416) (by have := List.mem_range.mp hi; layp hF)]
    exact (h.rows i (List.mem_range.mp hi)).2
  rw [p1, p2, q1, q2, skK]
  rfl

end

/-! ## The return -/

theorem idx_lt {p : Params} {r s : Nat} (hr : r < p.k) (hs : s < p.ℓ) : p.ℓ * r + s < p.k * p.ℓ := by
  have : p.ℓ * (r + 1) ≤ p.ℓ * p.k := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_comm p.k]; rw [Nat.mul_succ] at this; omega

theorem outcome_of {p : Params} {s₀ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {v : BitVec 32}
    (hl : 0 < p.ℓ) (hG : VG.Proof.MlDsa.X86.KeyGen.Good p s₀ (p.k * p.ℓ) (p.ℓ + p.k) A S v) :
    Spec.MlDsa.Outcome (fun b => keyGenInternal p b (VG.Proof.MlDsa.X86.KeyGen.xiOf s₀)) v
      (pkK p A S (VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀), skK p A S (VG.Proof.MlDsa.X86.KeyGen.rhoOf p s₀) (VG.Proof.MlDsa.X86.KeyGen.kOf p s₀)) := by
  rcases hG with ⟨rfl, b, hbA, hbS⟩ | ⟨rfl, hn⟩
  · refine .inl ⟨rfl, b, ?_⟩
    show keyGenInternal p b (VG.Proof.MlDsa.X86.KeyGen.xiOf s₀) = _
    rw [Proof.MlDsa.KeyGen.keyGenInternal_eq,
      Proof.MlDsa.KeyGen.expandA_some (A := fun r s => A (p.ℓ * r + s)) fun r hr s hs => ?_,
      Option.bind_some, Proof.MlDsa.KeyGen.expandS_some (S := S) hbS, Option.map_some,
      Proof.MlDsa.KeyGen.kgRest_eq]
    have := hbA (p.ℓ * r + s) (VG.Proof.MlDsa.X86.KeyGen.idx_lt hr hs)
    rwa [Nat.mul_add_div hl, Nat.div_eq_of_lt hs, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hs] at this
  · exact .inr ⟨rfl, hn⟩

theorem post {p : Params} (hF : VG.Proof.MlDsa.X86.KeyGen.PFacts p) {s₀ s : State} (hp : TPre (VG.Proof.MlDsa.X86.KeyGen.YK p) s₀) (h : VG.Proof.MlDsa.X86.KeyGen.Done p s₀ s) :
    Spec.MlDsa.Outcome (fun b => keyGenInternal p b (VG.Proof.MlDsa.X86.KeyGen.xiOf s₀)) (VG.Proof.MlDsa.X86.KeyGen.accV s₀ s)
      (bytesAt s.mem (Buf.addr s₀ ⟨1, 0, p.pkLen⟩) p.pkLen, bytesAt s.mem (Buf.addr s₀ ⟨2, 0, p.skLen⟩) p.skLen) := by
  obtain ⟨A, S, hk, htr⟩ := h.ex
  rw [VG.Proof.MlDsa.X86.KeyGen.pk_bytes hF hp hk] at htr
  rw [VG.Proof.MlDsa.X86.KeyGen.pk_bytes hF hp hk, VG.Proof.MlDsa.X86.KeyGen.sk_bytes hF hp hk htr]
  exact VG.Proof.MlDsa.X86.KeyGen.outcome_of (by have := hF.l; omega) hk.good

end VG.Proof.MlDsa.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Verified`. -/
section

/-!
# ML-DSA key generation on x86 (32-bit): the contract

`vg_mldsa*_keygen` of the parameter sets of Table 1 meets `keyGenContract`
with 96 bytes of stack (`keyGen_verified`), for any verified implementations
of the primitives it calls (`PrimsOk`): the body, as a leaf (`topLeaf`), from
the contract's precondition and public data (`pre_of`, `pub_of`), to its
postcondition (`post`).
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params)

/-- Memory with the arguments `0`, `0x1000`, `0x3000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 0x10 else if a = 0x500d then 0x30 else if a = 0x5012 then 1 else 0

/-- A state satisfying the precondition. -/
def keyGenSat (p : Params) : State :=
  VG.Proof.MlKem.X86.satState VG.Proof.MlDsa.X86.KeyGen.satMem [⟨0, 32⟩] [⟨0x1000, p.pkLen⟩, ⟨0x3000, p.skLen⟩, ⟨0x10000, VG.Proof.MlDsa.X86.KeyGen.scrLen p⟩, ⟨0x5004, 16⟩]

theorem keyGen_verified {P : Prims} (hP : VG.Proof.MlDsa.X86.KeyGen.PrimsOk P) (p : Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    Verified X86.target (keyGen P p) (Spec.MlDsa.keyGenContract p X86.abi 96) := by
  have hF := VG.Proof.MlDsa.X86.KeyGen.pfacts hp
  refine Piece.verified (((topLeaf (VG.Proof.MlDsa.X86.KeyGen.body_nosp hP p) (VG.Proof.MlDsa.X86.KeyGen.body_piece hP hF)).pre_mono (fun _ h => VG.Proof.MlDsa.X86.KeyGen.pre_of h)
    fun _ _ _ _ h => VG.Proof.MlDsa.X86.KeyGen.pub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hd, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [VG.Proof.MlDsa.X86.KeyGen.sw_app, hax, hd.eax, hm]
    have r := VG.Proof.MlDsa.X86.KeyGen.post hF (VG.Proof.MlDsa.X86.KeyGen.pre_of h₀) hd
    simp only [VG.Proof.MlDsa.X86.KeyGen.xiOf, VG.Proof.MlDsa.X86.KeyGen.addr0] at r
    exact r
  · rcases hp with rfl | rfl | rfl
    · exact ⟨VG.Proof.MlDsa.X86.KeyGen.keyGenSat Spec.MlDsa.mlDsa44, by sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, VG.Proof.MlDsa.X86.KeyGen.keyGenSat, VG.Proof.MlKem.X86.satState, VG.Proof.MlDsa.X86.KeyGen.satMem]⟩
    · exact ⟨VG.Proof.MlDsa.X86.KeyGen.keyGenSat Spec.MlDsa.mlDsa65, by sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, VG.Proof.MlDsa.X86.KeyGen.keyGenSat, VG.Proof.MlKem.X86.satState, VG.Proof.MlDsa.X86.KeyGen.satMem]⟩
    · exact ⟨VG.Proof.MlDsa.X86.KeyGen.keyGenSat Spec.MlDsa.mlDsa87, by sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, VG.Proof.MlDsa.X86.KeyGen.keyGenSat, VG.Proof.MlKem.X86.satState, VG.Proof.MlDsa.X86.KeyGen.satMem]⟩

end VG.Proof.MlDsa.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Inst`. -/
section

/-!
# ML-DSA key generation on x86 (32-bit), with this library's primitives

The x86 primitives (`Impl.MlDsa.X86.KeyGen.prims`) are verified against their
contracts, use at most 56 bytes of stack and write `esp` only by frames and
calls (`prims_ok`), so `vg_mldsa{44,65,87}_keygen` meet theirs
(`keyGen44_verified`, …).
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86
open VG.Impl.MlDsa.X86.KeyGen (prims keyGen44 keyGen65 keyGen87)

theorem prims_ok : VG.Proof.MlDsa.X86.KeyGen.PrimsOk prims where
  ntt := ⟨⟨15, by decide, Arith.NttFwd.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  invNtt := ⟨⟨15, by decide, Arith.NttInvP.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  mul := ⟨⟨15, by decide, Arith.mul_verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  mulAdd := ⟨⟨15, by decide, Arith.mulAdd_verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  add := ⟨⟨15, by decide, Arith.add_verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  rejNtt := ⟨⟨55, by decide, Sample.RejNtt.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  rejBounded := ⟨⟨55, by decide, Sample.RejBounded.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  power2Round := ⟨⟨15, by decide, Round.power2Round_verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩
  simpleBitPack := ⟨⟨15, by decide, Pack.SimpleBitPack.verified⟩, by decide +kernel,
    NoSp.of_all (by decide +kernel)⟩
  bitPack := ⟨⟨15, by decide, Pack.BitPack.verified⟩, by decide +kernel, NoSp.of_all (by decide +kernel)⟩

theorem keyGen44_verified :
    Verified X86.target keyGen44 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 X86.abi 96) :=
  VG.Proof.MlDsa.X86.KeyGen.keyGen_verified VG.Proof.MlDsa.X86.KeyGen.prims_ok _ (.inl rfl)

theorem keyGen65_verified :
    Verified X86.target keyGen65 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 X86.abi 96) :=
  VG.Proof.MlDsa.X86.KeyGen.keyGen_verified VG.Proof.MlDsa.X86.KeyGen.prims_ok _ (.inr (.inl rfl))

theorem keyGen87_verified :
    Verified X86.target keyGen87 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 X86.abi 96) :=
  VG.Proof.MlDsa.X86.KeyGen.keyGen_verified VG.Proof.MlDsa.X86.KeyGen.prims_ok _ (.inr (.inr rfl))

end VG.Proof.MlDsa.X86.KeyGen

end
