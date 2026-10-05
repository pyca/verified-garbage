import VerifiedGarbage.Impl.MlDsa.AArch64.Call
import VerifiedGarbage.Proof.MlKem.AArch64.Sample
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlDsa.KeyGen.Good
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlKem.AArch64.KeyGen
import VerifiedGarbage.Proof.MlKem.KPke1024

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Call.Base`. -/
section

/-!
# ML-DSA on AArch64: moves, layouts and what code leaves

The framework of the proofs of `vg_mldsa*_keygen`, `vg_mldsa*_sign` and
`vg_mldsa*_verify` on AArch64:

* The moves of a call's arguments (`glue_ok`): each argument register holds
  the argument's value (`Arg.val`: a pointer's address `pa`, or an integer).
* Layouts (`Lay S`, `Proof/Framework/CallLay.lean`): the function keeps the
  address of each buffer it works in (its arguments and its working space)
  in a callee-saved register of `keptRegs`; a layout lists these registers
  with the lengths of their buffers, read (`rbs`) or written (`wbs`), which
  are apart from the `S` bytes of stack below the stack pointer (which the
  calls use), and from each other where one of them is written. A pointer (a
  register and an offset) into a buffer, and two pointers apart, are checked
  by evaluation (`inB`, `sepB`).
* What a piece of code leaves (`PostB`): the permissions, the registers
  `keptRegs` and the stack pointer, the low halves of v8–v15, and memory but
  within the regions it writes and the stack.
* Two runs whose registers `B` (the function's `bases`) agree (`SameIn B`).
-/

namespace VG.Proof.MlDsa.AArch64

open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_movz wp_movImm wp_addImm wp_add)
open VG.Spec.Sha3 (bytesAt)

/-! ## Relating two runs -/

/-- Two states each related by `I` to an entry state; the entry states
satisfy `Pre` and agree by `Pub`. -/
def Rel2 (Pre : State → Prop) (Pub : State → State → Prop) (I : State → State → Prop) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂, Pre σ₁ ∧ Pre σ₂ ∧ Pub σ₁ σ₂ ∧ I σ₁ s₁ ∧ I σ₂ s₂

/-- A piece that leaks the same from states related by `I`, and takes each
run from `I` to `I'`. -/
theorem relInv {Pre : State → Prop} {Pub : State → State → Prop} {I I' : State → State → Prop}
    {c : Prog isa} (hw : ∀ σ s, Pre σ → I σ s → WP isa c s (I' σ))
    (ht : RelCT isa (VG.Proof.MlDsa.AArch64.Rel2 Pre Pub I) c fun _ _ => True) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Rel2 Pre Pub I) c (VG.Proof.MlDsa.AArch64.Rel2 Pre Pub I') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', -⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩ := hr
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩

/-- Constant time, from a relation of the runs from the entry states. -/
theorem relStart {Pre : State → Prop} {Pub : State → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (VG.Proof.MlDsa.AArch64.Rel2 Pre Pub fun σ s => s = σ) c Q) : ConstantTime isa Pre Pub c :=
  RelCT.constantTime (RelCT.mono h (fun s₁ s₂ ⟨p₁, p₂, hp⟩ => ⟨s₁, s₂, p₁, p₂, hp, rfl, rfl⟩) fun _ _ h => h)

/-- The final states of two runs related by `P` satisfy what correctness
says of each, from its own initial state. -/
theorem RelCT.postDep {P Q : State → State → Prop} {c : Prog isa} {F : State → State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x (F x) ∧ WP isa c y (F y))
    (hQ : ∀ x y x' y', P x y → F x x' → F y y' → Q x' y') : RelCT isa P c Q :=
  RelCT.mono (RelCT.wpDep h hw) (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, f₁, f₂⟩ => hQ _ _ _ _ hp f₁ f₂

/-- Code the taint analysis proves constant time from the registers `rs`,
which hold the same values in runs related by `P`, as does the stack pointer. -/
theorem taintRel {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint AArch64.Taint.T}
    (h : (taint.check (AArch64.Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (AArch64.Taint.ofRegs rs)
    (fun x y hp => ⟨(hr x y hp).1, fun r h => (hr x y hp).2 r (AArch64.Taint.mem_ofRegs.mp h)⟩) h

/-! ## Moves -/

/-- The address of the pointer `p` in `s`. -/
abbrev pa (s : State) (p : Ptr) : Addr := s.gpr p.1 + BitVec.ofNat 64 p.2

/-- The registers the moves of arguments, and the other blocks between
calls, write. -/
abbrev argRegs : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9]

theorem argRegs_pres : ∀ r ∈ preserved, r ∉ VG.Proof.MlDsa.AArch64.argRegs := by decide

theorem imm16_ofNat {v : Nat} (h : v < 65536) : (BitVec.ofNat 16 v).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem movV_ok (d : Reg) (v : Nat) {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = BitVec.ofNat 64 v → WP isa (.block is) s' Q) :
    WP isa (.block (movV d v ++ is)) s Q := by
  unfold movV
  split
  · exact wp_movz fun s' h e => k s' h (by rw [e, VG.Proof.MlDsa.AArch64.imm16_ofNat ‹_›])
  · exact wp_movImm k

theorem lea_ok {d b : Reg} (hd : d ≠ b) (off : Nat) {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr b + BitVec.ofNat 64 off → WP isa (.block is) s' Q) :
    WP isa (.block (lea d b off ++ is)) s Q := by
  unfold lea
  split
  · exact wp_addImm ‹_› k
  · rw [List.append_assoc]
    refine VG.Proof.MlDsa.AArch64.movV_ok d off fun s₁ h₁ e₁ => wp_add fun s₂ h₂ e₂ => k s₂ ((h₁.trans h₂).mono (by simp)) ?_
    rw [e₂, h₁.get b (by simpa using hd.symm), e₁]

/-- The value of an argument. -/
def _root_.VG.Impl.MlDsa.AArch64.Call.Arg.val (s : State) : Arg → BitVec 64
  | .ptr p => VG.Proof.MlDsa.AArch64.pa s p
  | .imm v => BitVec.ofNat 64 v

/-- An argument whose moves `glue` makes: a pointer based in a register the
moves do not write. -/
def _root_.VG.Impl.MlDsa.AArch64.Call.Arg.Ok : Arg → Prop
  | .ptr p => p.1 ∉ VG.Proof.MlDsa.AArch64.argRegs
  | .imm _ => True

theorem arg_ok (d : Reg) (hd : d ∈ VG.Proof.MlDsa.AArch64.argRegs) (a : Arg) (ha : a.Ok) (s : State) :
    WP isa (.block (a.instrs d)) s fun s' => s'.gpr d = a.val s ∧ Only [d] s s' := by
  cases a with
  | ptr p =>
    rw [← List.append_nil (Arg.instrs d _)]
    exact VG.Proof.MlDsa.AArch64.lea_ok (fun e => ha (by rw [← e]; exact hd)) p.2 fun s' h e => wp_nil ⟨e, h⟩
  | imm v =>
    rw [← List.append_nil (Arg.instrs d _)]
    exact VG.Proof.MlDsa.AArch64.movV_ok d v fun s' h e => wp_nil ⟨e, h⟩

/-- The arguments of a call, in their registers. -/
abbrev Args (as : List (Reg × Arg)) (s s1 : State) : Prop :=
  ((∀ a ∈ as, s1.gpr a.1 = a.2.val s) ∧ s1.mem = s.mem) ∧ Keep VG.Proof.MlDsa.AArch64.argRegs s s1

theorem glue_aux : ∀ (as : List (Reg × Arg)), (∀ a ∈ as, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.AArch64.argRegs) → (as.map (·.1)).Nodup →
    ∀ s : State, WP isa (.block (glue as)) s fun s' =>
      ((∀ a ∈ as, s'.gpr a.1 = a.2.val s) ∧ s'.mem = s.mem) ∧ Keep (as.map (·.1)) s s'
  | [], _, _, s => WP.block_nil ⟨⟨fun _ h => absurd h List.not_mem_nil, rfl⟩, Keep.refl _ _⟩
  | (d, a) :: as, hok, hnd, s => by
    simp only [glue]
    rw [WP.block_append_iff]
    have ha := hok (d, a) (List.mem_cons_self ..)
    rw [List.map_cons, List.nodup_cons] at hnd
    refine WP.mono (VG.Proof.MlDsa.AArch64.arg_ok d ha.2 a ha.1 s) fun s₁ ⟨hd, h₁⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.AArch64.glue_aux as (fun b hb => hok b (List.mem_cons_of_mem _ hb)) hnd.2 s₁)
      fun s₂ ⟨⟨hv, hm₂⟩, k₂⟩ => ⟨⟨fun b hb => ?_, hm₂.trans h₁.mem⟩, (h₁.keep.trans k₂).mono fun r hr => ?_⟩
    · have hval : ∀ c : Arg, c.Ok → c.val s₁ = c.val s := fun c hc => by
        cases c with
        | ptr p => simp only [Arg.val, VG.Proof.MlDsa.AArch64.pa]; rw [h₁.get p.1 (fun h => hc (by
            simp only [List.mem_singleton] at h; rw [h]; exact ha.2))]
        | imm v => rfl
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [k₂.gpr _ hnd.1, hd]
      · rw [hv b hb, hval b.2 (hok b (List.mem_cons_of_mem _ hb)).1]
    · rcases List.mem_append.mp hr with hr | hr
      · simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ hr

/-- The moves of the arguments `as`, to distinct argument registers. -/
theorem glue_ok {as : List (Reg × Arg)} (hok : ∀ a ∈ as, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.AArch64.argRegs) (hnd : (as.map (·.1)).Nodup)
    (s : State) : WP isa (.block (glue as)) s (VG.Proof.MlDsa.AArch64.Args as s) :=
  WP.mono (VG.Proof.MlDsa.AArch64.glue_aux as hok hnd s) fun _ ⟨h, k⟩ => ⟨h, k.mono fun r hr => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr; exact (hok a ha).2⟩

/-! ## What a piece leaves -/

/-- The callee-saved registers the functions never write (all but `x24`, and
`x30`, which calls overwrite): the functions keep the addresses of their
buffers in some of them. -/
abbrev keptRegs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27, .x28]

theorem kept_pres : ∀ r ∈ VG.Proof.MlDsa.AArch64.keptRegs, r ∈ preserved ∧ r ≠ .x30 := by decide

/-- What a call leaves: the permissions, the stack pointer and the
callee-saved GPRs but `x30`, the low halves of v8–v15, and memory changed only within `W` and the
`S` bytes of stack below the stack pointer. -/
structure Post (S : Nat) (s s' : State) (W : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame (W ++ [below s.sp S]) s.mem s'.mem
  vcs : ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-- What a piece of code leaves: the permissions, the registers `keptRegs`,
the stack pointer, the low halves of v8–v15, and memory but within `W` and
the stack. -/
structure PostB (S : Nat) (s s' : State) (W : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ VG.Proof.MlDsa.AArch64.keptRegs, s'.gpr r = s.gpr r
  frame : Frame (W ++ [below s.sp S]) s.mem s'.mem
  vcs : ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

section
variable {S : Nat}

theorem Post.b {s s' : State} {W : List Region} (h : VG.Proof.MlDsa.AArch64.Post S s s' W) : VG.Proof.MlDsa.AArch64.PostB S s s' W :=
  ⟨h.rd, h.wr, h.sp, fun r hr => h.cs r (VG.Proof.MlDsa.AArch64.kept_pres r hr).1 (VG.Proof.MlDsa.AArch64.kept_pres r hr).2, h.frame, h.vcs⟩

theorem PostB.bs {s s' : State} {W : List Region} (h : VG.Proof.MlDsa.AArch64.PostB S s s' W) : ∀ r ∈ VG.Proof.MlDsa.AArch64.keptRegs, s'.gpr r = s.gpr r :=
  h.cs

theorem PostB.refl (s : State) (W : List Region) : VG.Proof.MlDsa.AArch64.PostB S s s W :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _, fun _ _ => rfl⟩

theorem PostB.trans {s s₁ s₂ : State} {W₁ W₂ W : List Region} (h₁ : VG.Proof.MlDsa.AArch64.PostB S s s₁ W₁) (h₂ : VG.Proof.MlDsa.AArch64.PostB S s₁ s₂ W₂)
    (hw₁ : ∀ r ∈ W₁, r ∈ W) (hw₂ : ∀ r ∈ W₂, r ∈ W) : VG.Proof.MlDsa.AArch64.PostB S s s₂ W := by
  refine ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp, fun r hr => (h₂.cs r hr).trans (h₁.cs r hr), ?_,
    fun r hr => (h₂.vcs r hr).trans (h₁.vcs r hr)⟩
  have f₂ := h₂.frame
  rw [h₁.sp] at f₂
  refine (h₁.frame.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₁ r hr), List.mem_append_right _ hr]
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₂ r hr), List.mem_append_right _ hr]

/-- A block that keeps the registers `keptRegs` and the permissions, and writes within `W`. -/
theorem postB_of_keep {rs : List Reg} {s s' : State} {W : List Region} (k : Keep rs s s')
    (hrs : ∀ r ∈ VG.Proof.MlDsa.AArch64.keptRegs, r ∉ rs) (hf : Frame W s.mem s'.mem) : VG.Proof.MlDsa.AArch64.PostB S s s' W :=
  ⟨k.rd, k.wr, k.sp, fun r hr => k.gpr r (hrs r hr), (hf.mono fun _ hr => List.mem_append_left _ hr), k.vcs⟩

theorem PostB.pa {s s' : State} {W : List Region} (hP : VG.Proof.MlDsa.AArch64.PostB S s s' W) {p : Ptr} (h : p.1 ∈ VG.Proof.MlDsa.AArch64.keptRegs) :
    VG.Proof.MlDsa.AArch64.pa s' p = VG.Proof.MlDsa.AArch64.pa s p := by
  simp only [VG.Proof.MlDsa.AArch64.pa, hP.bs _ h]

end

/-! ## Checks -/

export VG.CallLay (inB isW lookup_mem inB_spec contains_trans inRegions_sub)

/-- The `l` bytes at `p` and the `k` bytes at `q` lie within their buffers,
apart: in different buffers, one of them written, or in the same buffer
(`CallLay.sepB`, unfolded one level for the checks' `simp`). -/
def sepB (rbs wbs : List (Reg × Nat)) (p : Ptr) (l : Nat) (q : Ptr) (k : Nat) : Bool :=
  VG.CallLay.inB (rbs ++ wbs) p l && VG.CallLay.inB (rbs ++ wbs) q k &&
    ((p.1 != q.1 && (VG.CallLay.isW wbs p.1 || isW wbs q.1)) ||
      (p.1 == q.1 && (decide (p.2 + l ≤ q.2) || decide (q.2 + k ≤ p.2))))

/-- The `l` bytes at `p` lie in the layout, apart from the regions `ws`
(`CallLay.keepB`; its register is one the code keeps, `Lay.bs`, so there is no
register to check). -/
def keepB (rbs wbs : List (Reg × Nat)) (ws : List (Ptr × Nat)) (p : Ptr) (l : Nat) : Bool :=
  VG.CallLay.inB (rbs ++ wbs) p l && ws.all fun w => VG.Proof.MlDsa.AArch64.sepB rbs wbs p l w.1 w.2

theorem sepB_eq (rbs wbs : List (Reg × Nat)) (p : Ptr) (l : Nat) (q : Ptr) (k : Nat) :
    VG.Proof.MlDsa.AArch64.sepB rbs wbs p l q k = CallLay.sepB (VG.CallLay.isW wbs) (rbs ++ wbs) p l q k := rfl

theorem keepB_eq (rbs wbs : List (Reg × Nat)) (ws : List (Ptr × Nat)) (p : Ptr) (l : Nat) :
    VG.Proof.MlDsa.AArch64.keepB rbs wbs ws p l = CallLay.keepB (fun _ => true) (VG.CallLay.isW wbs) (rbs ++ wbs) ws p l := rfl

/-- Two pointers into the same buffer are apart if their offsets are. -/
theorem sepB_same (rbs wbs : List (Reg × Nat)) (r : Reg) (o l o' l' : Nat) :
    VG.Proof.MlDsa.AArch64.sepB rbs wbs (r, o) l (r, o') l' =
      (VG.CallLay.inB (rbs ++ wbs) (r, o) l && VG.CallLay.inB (rbs ++ wbs) (r, o') l' && (decide (o + l ≤ o') || decide (o' + l' ≤ o))) :=
  CallLay.sepB_same _ _ r o l o' l'

/-- Two pointers into different buffers, one of them written, are apart. -/
theorem sepB_ne {rbs wbs : List (Reg × Nat)} {r r' : Reg} (h : r ≠ r') (hw : (VG.CallLay.isW wbs r || isW wbs r') = true)
    (o l o' l' : Nat) :
    VG.Proof.MlDsa.AArch64.sepB rbs wbs (r, o) l (r', o') l' = (VG.CallLay.inB (rbs ++ wbs) (r, o) l && VG.CallLay.inB (rbs ++ wbs) (r', o') l') :=
  CallLay.sepB_ne _ h hw o l o' l'

theorem sepB_spec {rbs wbs : List (Reg × Nat)} {p q : Ptr} {l k : Nat} (h : VG.Proof.MlDsa.AArch64.sepB rbs wbs p l q k = true) :
    VG.CallLay.inB (rbs ++ wbs) p l = true ∧ VG.CallLay.inB (rbs ++ wbs) q k = true ∧
      ((p.1 ≠ q.1 ∧ (VG.CallLay.isW wbs p.1 || isW wbs q.1) = true) ∨ (p.1 = q.1 ∧ (p.2 + l ≤ q.2 ∨ q.2 + k ≤ p.2))) :=
  CallLay.sepB_spec (VG.Proof.MlDsa.AArch64.sepB_eq .. ▸ h)

theorem keepB_in {rbs wbs : List (Reg × Nat)} {ws : List (Ptr × Nat)} {p : Ptr} {l : Nat}
    (hc : VG.Proof.MlDsa.AArch64.keepB rbs wbs ws p l = true) : VG.CallLay.inB (rbs ++ wbs) p l = true :=
  CallLay.keepB_in (VG.Proof.MlDsa.AArch64.keepB_eq .. ▸ hc)

theorem keepB_sub {rbs wbs : List (Reg × Nat)} {ws : List (Ptr × Nat)} {r : Reg} {o L o' l : Nat}
    (h : VG.Proof.MlDsa.AArch64.keepB rbs wbs ws (r, o) L = true) (h1 : o ≤ o') (h2 : o' + l ≤ o + L) : VG.Proof.MlDsa.AArch64.keepB rbs wbs ws (r, o') l = true :=
  VG.Proof.MlDsa.AArch64.keepB_eq .. ▸ CallLay.keepB_sub (VG.Proof.MlDsa.AArch64.keepB_eq .. ▸ h) h1 h2

/-! ## Layouts -/

/-- The buffers of `rbs` (read) and `wbs` (written), at the addresses in
their registers (`CallLay.Lay`): small, apart from each other (where one is
written) and from the `S` bytes of stack below the stack pointer, not
wrapping around, and permitted; and in registers of `keptRegs`. -/
structure Lay (S : Nat) (rbs wbs : List (Reg × Nat)) (s : State) : Prop
    extends CallLay.Lay (VG.CallLay.isW wbs) s.gpr s.rd s.wr (below s.sp S) rbs wbs where
  bs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlDsa.AArch64.keptRegs
  spS : S ≤ s.sp.toNat

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s)
include L

omit L in
theorem sub_of_inB {p : Ptr} {l : Nat} (h : VG.CallLay.inB (rbs ++ wbs) p l = true) :
    ∃ n, (p.1, n) ∈ rbs ++ wbs ∧ Region.Sub ⟨VG.Proof.MlDsa.AArch64.pa s p, l⟩ ⟨s.gpr p.1, n⟩ :=
  CallLay.sub_of_inB h

theorem Lay.disj {p q : Ptr} {l k : Nat} (h : VG.Proof.MlDsa.AArch64.sepB rbs wbs p l q k = true) :
    Region.Disjoint ⟨VG.Proof.MlDsa.AArch64.pa s p, l⟩ ⟨VG.Proof.MlDsa.AArch64.pa s q, k⟩ :=
  L.toLay.disj (VG.Proof.MlDsa.AArch64.sepB_eq .. ▸ h)

theorem Lay.stkD {p : Ptr} {l : Nat} (h : VG.CallLay.inB (rbs ++ wbs) p l = true) :
    (below s.sp S).Disjoint ⟨VG.Proof.MlDsa.AArch64.pa s p, l⟩ :=
  L.toLay.stkD h

theorem Lay.nwp {p : Ptr} {l : Nat} (h : VG.CallLay.inB (rbs ++ wbs) p l = true) : (VG.Proof.MlDsa.AArch64.pa s p).toNat + l ≤ 2 ^ 64 :=
  L.toLay.nwp h

theorem Lay.inR {p : Ptr} {l : Nat} (h : VG.CallLay.inB (rbs ++ wbs) p l = true) : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.AArch64.pa s p) l :=
  L.toLay.inR h

theorem Lay.inW {p : Ptr} {l : Nat} (h : VG.CallLay.inB wbs p l = true) : InRegions s.wr (VG.Proof.MlDsa.AArch64.pa s p) l :=
  L.toLay.inW h

theorem Lay.cR {p : Ptr} {l : Nat} (h : VG.CallLay.inB (rbs ++ wbs) p l = true) : Covers [⟨VG.Proof.MlDsa.AArch64.pa s p, l⟩] (s.rd ++ s.wr) :=
  Covers.one (L.inR h)

theorem Lay.cW {p : Ptr} {l : Nat} (h : VG.CallLay.inB wbs p l = true) : Covers [⟨VG.Proof.MlDsa.AArch64.pa s p, l⟩] s.wr :=
  Covers.one (L.inW h)

theorem Lay.s64 : S < 2 ^ 64 := Nat.lt_of_le_of_lt L.spS s.sp.isLt

theorem Lay.ptrBs {p : Ptr} {l : Nat} (h : VG.CallLay.inB (rbs ++ wbs) p l = true) : p.1 ∈ VG.Proof.MlDsa.AArch64.keptRegs := by
  obtain ⟨n, hn, _⟩ := VG.CallLay.inB_spec h
  exact L.bs (p.1, n) hn

theorem Lay.post {s' : State} {W : List Region} (hP : VG.Proof.MlDsa.AArch64.PostB S s s' W) : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s' := by
  have L' := L.toLay.congr (g' := s'.gpr) fun b hb => hP.bs _ (L.bs b hb)
  rw [← hP.rd, ← hP.wr, ← hP.sp] at L'
  exact ⟨L', L.bs, by rw [hP.sp]; exact L.spS⟩

end

/-! ## What is kept -/

/-- The region of `w.2` bytes at the pointer `w.1`. -/
abbrev toR (s : State) (w : Ptr × Nat) : Region := ⟨VG.Proof.MlDsa.AArch64.pa s w.1, w.2⟩

/-- `PostB`, with the regions written given as pointers. -/
abbrev PPostB (S : Nat) (s s' : State) (ws : List (Ptr × Nat)) : Prop := VG.Proof.MlDsa.AArch64.PostB S s s' (ws.map (VG.Proof.MlDsa.AArch64.toR s))

section
variable {S : Nat}

theorem map_toR_post {s s' : State} {W : List Region} (hP : VG.Proof.MlDsa.AArch64.PostB S s s' W) {ws : List (Ptr × Nat)}
    (h : ∀ w ∈ ws, w.1.1 ∈ VG.Proof.MlDsa.AArch64.keptRegs) : ws.map (VG.Proof.MlDsa.AArch64.toR s') = ws.map (VG.Proof.MlDsa.AArch64.toR s) :=
  List.map_congr_left fun w hw => by simp only [VG.Proof.MlDsa.AArch64.toR, hP.pa (h w hw)]

theorem PPostB.trans {s s₁ s₂ : State} {ws₁ ws₂ ws : List (Ptr × Nat)} (h₁ : VG.Proof.MlDsa.AArch64.PPostB S s s₁ ws₁)
    (h₂ : VG.Proof.MlDsa.AArch64.PPostB S s₁ s₂ ws₂) (hcs : ∀ w ∈ ws₂, w.1.1 ∈ VG.Proof.MlDsa.AArch64.keptRegs) (hw₁ : ∀ w ∈ ws₁, w ∈ ws)
    (hw₂ : ∀ w ∈ ws₂, w ∈ ws) : VG.Proof.MlDsa.AArch64.PPostB S s s₂ ws := by
  have h₂' : VG.Proof.MlDsa.AArch64.PostB S s₁ s₂ (ws₂.map (VG.Proof.MlDsa.AArch64.toR s)) := by rw [← VG.Proof.MlDsa.AArch64.map_toR_post h₁ hcs]; exact h₂
  refine PostB.trans h₁ h₂' (fun r hr => ?_) fun r hr => ?_
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₁ w hw)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₂ w hw)

theorem PPostB.mono {s s' : State} {ws ws' : List (Ptr × Nat)} (h : VG.Proof.MlDsa.AArch64.PPostB S s s' ws) (hw : ∀ w ∈ ws, w ∈ ws') :
    VG.Proof.MlDsa.AArch64.PPostB S s s' ws' :=
  PostB.trans (PostB.refl s []) h (fun _ h => absurd h List.not_mem_nil) fun r hr => by
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw w hw')

end

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {ws : List (Ptr × Nat)}
  {p : Ptr} {l : Nat}
include L

theorem Lay.keepBs (hc : VG.Proof.MlDsa.AArch64.keepB rbs wbs ws p l = true) : p.1 ∈ VG.Proof.MlDsa.AArch64.keptRegs := L.ptrBs (VG.Proof.MlDsa.AArch64.keepB_in hc)

theorem Lay.fdisj (hc : VG.Proof.MlDsa.AArch64.keepB rbs wbs ws p l = true) :
    ∀ r ∈ ws.map (VG.Proof.MlDsa.AArch64.toR s) ++ [below s.sp S], Region.Disjoint ⟨VG.Proof.MlDsa.AArch64.pa s p, l⟩ r :=
  L.toLay.fdisj (VG.Proof.MlDsa.AArch64.keepB_eq .. ▸ hc)

theorem Lay.keepBytes (hP : VG.Proof.MlDsa.AArch64.PPostB S s s' ws) (hc : VG.Proof.MlDsa.AArch64.keepB rbs wbs ws p l = true) :
    bytesAt s'.mem (VG.Proof.MlDsa.AArch64.pa s' p) l = bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s p) l := by
  rw [hP.pa (L.keepBs hc)]
  obtain ⟨n, hn, hl⟩ := VG.CallLay.inB_spec (VG.Proof.MlDsa.AArch64.keepB_in hc)
  exact Proof.MlKem.bytesAt_frame hP.frame (L.fdisj hc) (by have := L.small _ hn; simp only at this; omega)

theorem Lay.keepPoly {f : Spec.MlDsa.Poly} (hP : VG.Proof.MlDsa.AArch64.PPostB S s s' ws) (hc : VG.Proof.MlDsa.AArch64.keepB rbs wbs ws p 1024 = true)
    (h : Spec.MlDsa.PolyIs s.mem (VG.Proof.MlDsa.AArch64.pa s p) f) : Spec.MlDsa.PolyIs s'.mem (VG.Proof.MlDsa.AArch64.pa s' p) f := by
  rw [hP.pa (L.keepBs hc)]
  exact Proof.MlDsa.Verify.polyIs_frame hP.frame (L.fdisj hc) h

theorem Lay.keepPolyAt (hP : VG.Proof.MlDsa.AArch64.PPostB S s s' ws) (hc : VG.Proof.MlDsa.AArch64.keepB rbs wbs ws p 1024 = true) :
    Spec.MlDsa.polyAt s'.mem (VG.Proof.MlDsa.AArch64.pa s' p) = Spec.MlDsa.polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s p) := by
  rw [hP.pa (L.keepBs hc)]
  exact Proof.MlDsa.Verify.polyAt_frame hP.frame (L.fdisj hc)

theorem Lay.keepRed (hP : VG.Proof.MlDsa.AArch64.PPostB S s s' ws) (hc : VG.Proof.MlDsa.AArch64.keepB rbs wbs ws p 1024 = true)
    (h : Spec.MlDsa.Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s p)) : Spec.MlDsa.Reduced s'.mem (VG.Proof.MlDsa.AArch64.pa s' p) := by
  rw [hP.pa (L.keepBs hc)]
  exact Proof.MlDsa.Verify.reduced_frame hP.frame (L.fdisj hc) h

theorem Lay.keepHint {k : Nat} {h : List (Vector Bool Spec.MlDsa.n)} (hP : VG.Proof.MlDsa.AArch64.PPostB S s s' ws)
    (hc : VG.Proof.MlDsa.AArch64.keepB rbs wbs ws p (1024 * k) = true)
    (hh : Spec.MlDsa.HintIs s.mem (VG.Proof.MlDsa.AArch64.pa s p) k h) : Spec.MlDsa.HintIs s'.mem (VG.Proof.MlDsa.AArch64.pa s' p) k h := by
  rw [hP.pa (L.keepBs hc)]
  obtain ⟨n, hn, hl⟩ := VG.CallLay.inB_spec (VG.Proof.MlDsa.AArch64.keepB_in hc)
  exact Proof.MlDsa.Verify.hintIs_frame hP.frame (by have := L.small _ hn; simp only at this; omega)
    (L.fdisj hc) hh

theorem Lay.keepW (hP : VG.Proof.MlDsa.AArch64.PPostB S s s' ws) (hc : VG.Proof.MlDsa.AArch64.keepB rbs wbs ws p 8 = true) :
    s'.mem.readW (VG.Proof.MlDsa.AArch64.pa s' p) 64 = s.mem.readW (VG.Proof.MlDsa.AArch64.pa s p) 64 := by
  rw [hP.pa (L.keepBs hc)]
  exact hP.frame.readW (Region.contains_self _ _) (L.fdisj hc) (by decide)

end

/-! ## Two runs -/

/-- Two states whose registers `B` and stack pointer agree. -/
def SameIn (B : List Reg) (x y : State) : Prop := (∀ r ∈ B, x.gpr r = y.gpr r) ∧ x.sp = y.sp

theorem SameIn.pa {B : List Reg} {x y : State} (h : VG.Proof.MlDsa.AArch64.SameIn B x y) {p : Ptr} (hp : p.1 ∈ B) : VG.Proof.MlDsa.AArch64.pa x p = VG.Proof.MlDsa.AArch64.pa y p := by
  simp only [VG.Proof.MlDsa.AArch64.pa, h.1 _ hp]

/-- The buffers of a layout are in registers of `B` (which are among `keptRegs`). -/
def LayIn (B : List Reg) (bs : List (Reg × Nat)) : Prop := ∀ b ∈ bs, b.1 ∈ B ∧ b.1 ∈ VG.Proof.MlDsa.AArch64.keptRegs

theorem ptr_bs {B : List Reg} {bs : List (Reg × Nat)} (L : VG.Proof.MlDsa.AArch64.LayIn B bs) {p : Ptr} {l : Nat}
    (h : VG.CallLay.inB bs p l = true) : p.1 ∈ B := by
  obtain ⟨n, hn, _⟩ := VG.CallLay.inB_spec h
  exact (L (p.1, n) hn).1

theorem ptr_kept {B : List Reg} {bs : List (Reg × Nat)} (L : VG.Proof.MlDsa.AArch64.LayIn B bs) {p : Ptr} {l : Nat}
    (h : VG.CallLay.inB bs p l = true) : p.1 ∈ VG.Proof.MlDsa.AArch64.keptRegs := by
  obtain ⟨n, hn, _⟩ := VG.CallLay.inB_spec h
  exact (L (p.1, n) hn).2

theorem Lay.ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) :
    VG.Proof.MlDsa.AArch64.LayIn VG.Proof.MlDsa.AArch64.keptRegs (rbs ++ wbs) :=
  fun b hb => ⟨L.bs b hb, L.bs b hb⟩

end VG.Proof.MlDsa.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call`. -/
section

/-!
# ML-DSA on AArch64: calls

A call of verified code, with the moves of its arguments before it
(`callAt_ok`), leaves the permissions, the stack pointer, the low halves of
v8–v15 and the callee-saved GPRs but `x30` as they were, and changes memory only
within the buffers it writes and the `S` bytes of stack below the stack pointer
(`Post`); two runs whose callee's preconditions hold and whose public data agree
leak the same (`callAt_tr`).

A callee (`CalleeOk S`) is correct and constant time under its contract
with a stack of `S` bytes, and its frames use at most those `S` bytes; one
verified against its contract with any stack up to `S` is
(`CalleeOk.of_verified`, from `pre_stack`).
-/

namespace VG.Proof.MlDsa.AArch64

open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep)

/-! ## Blocks that access no memory -/

theorem execBlock_nomem {is : List Instr} (h : ∀ i ∈ is, ∀ s, isa.addrs i s = []) :
    ∀ {s s' : State} {t : List Leak}, execBlock isa is s = some (s', t) → t = [] := by
  induction is with
  | nil => intro s s' t e; simp [execBlock] at e; exact e.2
  | cons i is ih =>
    intro s s' t e
    simp only [execBlock] at e
    split at e
    · cases e
    · obtain ⟨⟨s₂, t₂⟩, e₂, he⟩ := Option.map_eq_some_iff.mp e
      simp only [Prod.mk.injEq] at he
      rw [← he.2, show addrs i s = [] from h i (List.mem_cons_self ..) s,
        ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) e₂]
      rfl

/-- A block that accesses no memory leaks nothing. -/
theorem block_nomem_tr {is : List Instr} (h : ∀ i ∈ is, ∀ s, isa.addrs i s = []) {P : State → State → Prop} :
    RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨(VG.Proof.MlDsa.AArch64.execBlock_nomem h e₁).trans (VG.Proof.MlDsa.AArch64.execBlock_nomem h e₂).symm, trivial⟩

theorem movV_nomem (d : Reg) (v : Nat) : ∀ i ∈ movV d v, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  unfold movV Impl.MlKem.AArch64.movImm at hi
  split at hi <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hi <;>
    rcases hi with rfl | rfl | rfl | rfl <;> rfl

theorem lea_nomem (d b : Reg) (off : Nat) : ∀ i ∈ lea d b off, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  unfold lea at hi
  split at hi
  · simp only [List.mem_singleton] at hi; subst hi; rfl
  · rcases List.mem_append.mp hi with hi | hi
    · exact VG.Proof.MlDsa.AArch64.movV_nomem d off i hi s
    · simp only [List.mem_singleton] at hi; subst hi; rfl

theorem glue_nomem : ∀ (as : List (Reg × Arg)), ∀ i ∈ glue as, ∀ s, isa.addrs i s = []
  | [], _, h, _ => absurd h List.not_mem_nil
  | (d, a) :: as, i, h, s => by
    simp only [glue] at h
    rcases List.mem_append.mp h with h | h
    · cases a with
      | ptr p => exact VG.Proof.MlDsa.AArch64.lea_nomem d p.1 p.2 i h s
      | imm v => exact VG.Proof.MlDsa.AArch64.movV_nomem d v i h s
    · exact VG.Proof.MlDsa.AArch64.glue_nomem as i h s

/-! ## Callees -/

/-- A callee: correct and constant time under the contract `k` (a shared
contract with `S` bytes of stack), whose frames use at most those `S` bytes. -/
structure CalleeOk (S : Nat) (c : Prog isa) (k : Contract isa) : Prop where
  correct : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s'
  ct : ConstantTime isa k.pre k.pub c
  fd : 16 * c.aarch64Depth ≤ S

theorem stackBelow_sub (sp : Addr) {n S : Nat} (hn : n ≤ S) (hS : S < 2 ^ 64) :
    ∀ r ∈ stackBelow sp n, Region.Sub r (below sp S) := by
  intro r hr
  match n, hr with
  | m + 1, hr =>
    simp only [stackBelow, List.mem_singleton] at hr
    subst hr
    exact below_sub hn hS

/-- What `AArch64.abi.wf` asks of the stack pointer for a stack of `n` bytes. -/
def wfP (n sp : Nat) : Prop := match n with | 0 => True | n => n ≤ sp

theorem wf_mono {n S sp : Nat} (hn : n ≤ S) (h : VG.Proof.MlDsa.AArch64.wfP S sp) : VG.Proof.MlDsa.AArch64.wfP n sp := by
  unfold VG.Proof.MlDsa.AArch64.wfP at h ⊢
  rcases n with _ | n
  · trivial
  · rcases S with _ | S
    · omega
    · exact Nat.le_trans hn h

/-- A contract with a stack of at most `S` bytes asks no more than with `S`. -/
theorem pre_stack {sig : Sig} {pre : Curry (sig.words AArch64.abi.ptrBits) (Mem → Prop)}
    {post : sig.Post AArch64.abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words AArch64.abi.ptrBits) (Mem → List Nat))} {n S : Nat} (hn : n ≤ S)
    (hS : S < 2 ^ 64) {s : State}
    (h : (sig.contract AArch64.abi pre post wa S leak).pre s) : (sig.contract AArch64.abi pre post wa n leak).pre s := by
  unfold Sig.contract at h ⊢
  dsimp only at h ⊢
  generalize AArch64.abi.args ((sig.words AArch64.abi.ptrBits).map (·.bits AArch64.abi.ptrBits)) = o at h ⊢
  cases o with
  | none => exact h
  | some vals =>
    obtain ⟨hwf, hrd, hwr, hpw, hres, hnw, hpre⟩ := h
    refine ⟨?_, hrd, hwr, hpw, fun r hr a ha => ?_, hnw, hpre⟩
    · simp only [AArch64.abi] at hwf ⊢
      split at hwf
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ‹_›)]; exact VG.Proof.MlDsa.AArch64.wf_mono hn hwf
      · rw [ite_eq_right_of_eq_false _ _ (eq_false ‹_›)]; exact ⟨VG.Proof.MlDsa.AArch64.wf_mono hn hwf.1, hwf.2⟩
    · simp only [AArch64.abi] at hr hres
      rcases S with _ | S
      · rcases n with _ | n
        · simp [stackBelow] at hr
        · omega
      · exact (hres _ (List.mem_singleton_self _) a ha).sub_left (VG.Proof.MlDsa.AArch64.stackBelow_sub _ hn hS r hr)

/-- A callee verified against its shared contract with at most `S` bytes of
stack, whose frames use at most `S` bytes. -/
theorem CalleeOk.of_verified {S : Nat} (hS : S < 2 ^ 64) {c : Prog isa} {sig : Sig}
    {pre : Curry (sig.words AArch64.abi.ptrBits) (Mem → Prop)} {post : sig.Post AArch64.abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words AArch64.abi.ptrBits) (Mem → List Nat))} {n : Nat}
    (h : Verified AArch64.target c (sig.contract AArch64.abi pre post wa n leak)) (hn : n ≤ S)
    (hfd : 16 * c.aarch64Depth ≤ S) :
    VG.Proof.MlDsa.AArch64.CalleeOk S c (sig.contract AArch64.abi pre post wa S leak) :=
  ⟨fun s hs => h.1 s (VG.Proof.MlDsa.AArch64.pre_stack hn hS hs),
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
      h.2.1 s₁ s₂ t₁ t₂ s₁' s₂' (VG.Proof.MlDsa.AArch64.pre_stack hn hS h₁) (VG.Proof.MlDsa.AArch64.pre_stack hn hS h₂) hp e₁ e₂, hfd⟩

/-- `k` with the fact `X` of each run added to its postcondition. -/
def withPost (k : Contract isa) (X : State → State → Prop) : Contract isa :=
  { k with post := fun s s' => k.post s s' ∧ X s s' }

theorem CalleeOk.withPost {S : Nat} {c : Prog isa} {k : Contract isa} (C : VG.Proof.MlDsa.AArch64.CalleeOk S c k)
    {X : State → State → Prop} (hx : ∀ s t s', k.pre s → Exec isa c s t s' → X s s') :
    VG.Proof.MlDsa.AArch64.CalleeOk S c (VG.Proof.MlDsa.AArch64.withPost k X) :=
  ⟨fun s hs => let ⟨t, s', e, a, p⟩ := C.correct s hs; ⟨t, s', e, a, p, hx s t s' hs e⟩, C.ct, C.fd⟩

/-! ## Calls -/

theorem callAt_ok {S : Nat} (hS : S < 2 ^ 64) {n : String} {c : Prog isa} {k : Contract isa}
    (C : VG.Proof.MlDsa.AArch64.CalleeOk S c k) {as : List (Reg × Arg)} (hok : ∀ a ∈ as, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.AArch64.argRegs)
    (hnd : (as.map (·.1)).Nodup) {s : State} {rd wr : List Region}
    (hpre : ∀ s1, VG.Proof.MlDsa.AArch64.Args as s s1 → k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (callAt n c as) s fun s' => VG.Proof.MlDsa.AArch64.Post S s s' wr ∧
      ∃ s1, VG.Proof.MlDsa.AArch64.Args as s s1 ∧ k.post (s1.callEntry.withRegions rd wr) (s'.withRegions rd wr) := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.glue_ok hok hnd s) fun s1 h1 => ?_)
  have k1 := h1.2
  refine WP.callFV C.correct (hpre s1 h1) (by rw [k1.rd, k1.wr]; exact hc) (by rw [k1.wr]; exact hw)
    (fun s' hrd hwr hsp hf hcs hvcs hpost => ?_) (by have := C.fd; omega)
  refine ⟨⟨hrd.trans k1.rd, hwr.trans k1.wr, hsp.trans k1.sp,
    fun r hr h30 => by rw [hcs r hr h30, k1.gpr r (VG.Proof.MlDsa.AArch64.argRegs_pres r hr)], ?_, fun r hr => (hvcs r hr).trans (k1.vcs r hr)⟩, s1, h1, hpost⟩
  rw [h1.1.2, k1.sp] at hf
  exact Frame.below_mono hf C.fd hS

/-- The trace of the moves then a call, from two runs whose callee's
preconditions hold and whose callee's public data agree. -/
theorem callAt_tr {S : Nat} {n : String} {c : Prog isa} {k : Contract isa} (C : VG.Proof.MlDsa.AArch64.CalleeOk S c k)
    {as : List (Reg × Arg)} (hok : ∀ a ∈ as, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.AArch64.argRegs) (hnd : (as.map (·.1)).Nodup)
    {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → VG.Proof.MlDsa.AArch64.Args as x x1 → VG.Proof.MlDsa.AArch64.Args as y y1 → ∃ rd wr : List Region,
      k.pre (x1.callEntry.withRegions rd wr) ∧ k.pre (y1.callEntry.withRegions rd wr) ∧
      k.pub (x1.callEntry.withRegions rd wr) (y1.callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) (x.rd ++ x.wr) ∧ Covers wr x.wr ∧
      Covers (rd ++ wr) (y.rd ++ y.wr) ∧ Covers wr y.wr) :
    RelCT isa P (callAt n c as) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, P x y ∧ VG.Proof.MlDsa.AArch64.Args as x x1 ∧ VG.Proof.MlDsa.AArch64.Args as y y1)
      (VG.Proof.MlDsa.AArch64.block_nomem_tr (VG.Proof.MlDsa.AArch64.glue_nomem as)) (fun x y _ => ⟨VG.Proof.MlDsa.AArch64.glue_ok hok hnd x, VG.Proof.MlDsa.AArch64.glue_ok hok hnd y⟩)
      fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.mono (RelCT.exists_ (P := fun (a : List Region × List Region) (x1 y1 : State) =>
        k.pre (x1.callEntry.withRegions a.1 a.2) ∧ k.pre (y1.callEntry.withRegions a.1 a.2) ∧
        k.pub (x1.callEntry.withRegions a.1 a.2) (y1.callEntry.withRegions a.1 a.2) ∧
        Covers (a.1 ++ a.2) (x1.rd ++ x1.wr) ∧ Covers a.2 x1.wr ∧
        Covers (a.1 ++ a.2) (y1.rd ++ y1.wr) ∧ Covers a.2 y1.wr)
      fun a => RelCT.call C.correct C.ct a.1 a.2 fun _ _ h => h)
      (fun x1 y1 ⟨x, y, hp, h1, h2⟩ => by
        obtain ⟨rd, wr, p₁, p₂, pub, c₁, w₁, c₂, w₂⟩ := hP x y x1 y1 hp h1 h2
        exact ⟨(rd, wr), p₁, p₂, pub, by rw [h1.2.rd, h1.2.wr]; exact c₁, by rw [h1.2.wr]; exact w₁,
          by rw [h2.2.rd, h2.2.wr]; exact c₂, by rw [h2.2.wr]; exact w₂⟩)
      fun _ _ h => h)

/-! ## Sequences -/

theorem nil_tr {P : State → State → Prop} : RelCT isa P (.block []) P := RelCT.block_nil fun _ _ h => h

theorem seqR_ok {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → ∀ s, I k s → WP isa (f k) s (I (k + 1))) →
      ∀ s, I a s → WP isa (seqR f a n) s (I (a + n))
  | 0, a, _, s, h => by simp only [seqR, Nat.add_zero]; exact WP.block_nil h
  | n + 1, a, hf, s, h => by
    refine WP.seq (WP.mono (hf a (Nat.le_refl _) (by omega) s h) fun s' h' => ?_)
    have := VG.Proof.MlDsa.AArch64.seqR_ok n (a + 1) (fun k h₁ h₂ => hf k (by omega) (by omega)) s' h'
    rwa [show a + 1 + n = a + (n + 1) by omega] at this

theorem seqR_tr {f : Nat → Prog isa} {Q : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → RelCT isa (Q k) (f k) (Q (k + 1))) →
      RelCT isa (Q a) (seqR f a n) (Q (a + n))
  | 0, a, _ => by simp only [seqR, Nat.add_zero]; exact RelCT.block_nil (fun _ _ h => h)
  | n + 1, a, hf => by
    have := VG.Proof.MlDsa.AArch64.seqR_tr n (a + 1) (fun k h₁ h₂ => hf k (by omega) (by omega))
    rw [show a + 1 + n = a + (n + 1) by omega] at this
    exact RelCT.seq (hf a (Nat.le_refl _) (by omega)) this

end VG.Proof.MlDsa.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry`. -/
section

/-!
# ML-DSA on AArch64: entry to a callee

What a callee's contract needs on its entry (the state of the call, with the
link registers changed), from the layout of the caller (`cpre`): the stack it
may use (`wfP_of`, `resv`), and its buffers apart from that stack and from
each other, and not wrapping around. The values of the arguments after their
moves (`Args.ptr`, `Args.imm`), the same in runs whose layout registers
agree (`SameIn.args`).
-/

namespace VG.Proof.MlDsa.AArch64

open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Spec.MlDsa

theorem wfP_of {S sp : Nat} (h : S ≤ sp) : VG.Proof.MlDsa.AArch64.wfP S sp := by unfold VG.Proof.MlDsa.AArch64.wfP; split <;> trivial

theorem stackBelow_mem {sp : Addr} {S : Nat} {r : Region} (h : r ∈ stackBelow sp S) : r = below sp S := by
  rcases S with _ | S
  · simp [stackBelow] at h
  · simp only [stackBelow, List.mem_singleton] at h; exact h

/-- The disjointness of the callee's stack from its buffers. -/
theorem resv {S : Nat} {sp : Addr} {f : Region → List Prop} (h : ∀ r ∈ stackBelow sp S, Sig.conj (f r)) :
    Sig.conj ((stackBelow sp S).map f).flatten := by
  rcases S with _ | S
  · trivial
  · simp only [stackBelow, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact h _ (List.mem_singleton_self _)

theorem conj_cons {p : Prop} {l : List Prop} (hp : p) (hl : Sig.conj l) : Sig.conj (p :: l) :=
  Sig.conj_cons.mpr ⟨hp, hl⟩

theorem conj_nil : Sig.conj [] := trivial

/-! ## Arguments -/

theorem Args.ptr {as : List (Reg × Arg)} {s s1 : State} (h : VG.Proof.MlDsa.AArch64.Args as s s1) {r : Reg} {p : Ptr}
    (hm : (r, Arg.ptr p) ∈ as := by simp) : s1.gpr r = VG.Proof.MlDsa.AArch64.pa s p := h.1.1 _ hm

theorem Args.imm {as : List (Reg × Arg)} {s s1 : State} (h : VG.Proof.MlDsa.AArch64.Args as s s1) {r : Reg} {v : Nat}
    (hm : (r, Arg.imm v) ∈ as := by simp) : s1.gpr r = BitVec.ofNat 64 v := h.1.1 _ hm

theorem Args.r0 {r : Reg} {a : Arg} {as : List (Reg × Arg)} {s s1 : State} (h : VG.Proof.MlDsa.AArch64.Args ((r, a) :: as) s s1) :
    s1.gpr r = a.val s := h.1.1 _ (List.mem_cons_self ..)

theorem Args.r1 {r r1 : Reg} {a a1 : Arg} {as : List (Reg × Arg)} {s s1 : State}
    (h : VG.Proof.MlDsa.AArch64.Args ((r1, a1) :: (r, a) :: as) s s1) : s1.gpr r = a.val s :=
  h.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem Args.r2 {r r1 r2 : Reg} {a a1 a2 : Arg} {as : List (Reg × Arg)} {s s1 : State}
    (h : VG.Proof.MlDsa.AArch64.Args ((r2, a2) :: (r1, a1) :: (r, a) :: as) s s1) : s1.gpr r = a.val s :=
  h.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem Args.r3 {r r1 r2 r3 : Reg} {a a1 a2 a3 : Arg} {as : List (Reg × Arg)} {s s1 : State}
    (h : VG.Proof.MlDsa.AArch64.Args ((r3, a3) :: (r2, a2) :: (r1, a1) :: (r, a) :: as) s s1) : s1.gpr r = a.val s :=
  h.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem Args.r4 {r r1 r2 r3 r4 : Reg} {a a1 a2 a3 a4 : Arg} {as : List (Reg × Arg)} {s s1 : State}
    (h : VG.Proof.MlDsa.AArch64.Args ((r4, a4) :: (r3, a3) :: (r2, a2) :: (r1, a1) :: (r, a) :: as) s s1) : s1.gpr r = a.val s :=
  h.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..)))))

theorem Args.sp {as : List (Reg × Arg)} {s s1 : State} (h : VG.Proof.MlDsa.AArch64.Args as s s1) : s1.sp = s.sp := h.2.sp

theorem Args.mem {as : List (Reg × Arg)} {s s1 : State} (h : VG.Proof.MlDsa.AArch64.Args as s s1) : s1.mem = s.mem := h.1.2

theorem imm32 {v : Nat} (h : v < 2 ^ 32) : (BitVec.setWidth 32 (BitVec.ofNat 64 v)).toNat = v := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem ptr_ok {p : Ptr} (h : p.1 ∈ VG.Proof.MlDsa.AArch64.keptRegs) : (Arg.ptr p).Ok := by
  show p.1 ∉ VG.Proof.MlDsa.AArch64.argRegs
  revert h; generalize p.1 = r; cases r <;> decide

theorem SameIn.args {B : List Reg} {as : List (Reg × Arg)} {x y x1 y1 : State} (h : VG.Proof.MlDsa.AArch64.SameIn B x y) (h1 : VG.Proof.MlDsa.AArch64.Args as x x1)
    (h2 : VG.Proof.MlDsa.AArch64.Args as y y1) {r : Reg} {p : Ptr} (hp : p.1 ∈ B) (hm : (r, Arg.ptr p) ∈ as := by simp) :
    x1.gpr r = y1.gpr r := by
  rw [h1.ptr hm, h2.ptr hm, h.pa hp]

theorem SameIn.argi {as : List (Reg × Arg)} {x y x1 y1 : State} (h1 : VG.Proof.MlDsa.AArch64.Args as x x1)
    (h2 : VG.Proof.MlDsa.AArch64.Args as y y1) {r : Reg} {v : Nat} (hm : (r, Arg.imm v) ∈ as := by simp) :
    x1.gpr r = y1.gpr r := by
  rw [h1.imm hm, h2.imm hm]

/-- The facts of a callee's precondition that the layout gives: its stack,
the disjointness of its buffers, and that they do not wrap around. -/
syntax "cpre " term:max : tactic
macro_rules
  | `(tactic| cpre $L) => `(tactic| (
      and_intros
      all_goals first
        | with_reducible rfl
        | exact True.intro
        | exact wfP_of (Lay.spS $L)
        | exact resv fun _ hr => by
            rw [stackBelow_mem hr]
            repeat' first
              | exact conj_nil
              | refine conj_cons (Lay.stkD $L (by assumption)) ?_
        | exact Lay.disj $L (by assumption)
        | exact (Lay.disj $L (by assumption)).symm
        | exact Lay.nwp $L (by assumption)
        | skip))

end VG.Proof.MlDsa.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Call.Arith`. -/
section

/-!
# ML-DSA on AArch64: calls of the arithmetic primitives

For each call of `vg_mldsa_ntt`, `vg_mldsa_inv_ntt` (`ipAt`),
`vg_mldsa_multiply_ntt`, `vg_mldsa_multiply_add_ntt`, `vg_mldsa_add` and
`vg_mldsa_sub`: what it needs of the layout (a check evaluated on the
pointers, `…Chk`), what it does (`…_ok`), and that two runs whose layout
registers agree leak the same (`…_tr`).
-/

namespace VG.Proof.MlDsa.AArch64

open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Spec.MlDsa

/-! ## `NTT` and `NTT⁻¹` -/

def ipChk (rbs wbs : List (Reg × Nat)) (f ss : Ptr) : Bool :=
  VG.Proof.MlDsa.AArch64.sepB rbs wbs f 1024 ss 1024 && VG.CallLay.inB (rbs ++ wbs) f 1024 && VG.CallLay.inB (rbs ++ wbs) ss 1024 && VG.CallLay.inB wbs f 1024 &&
    VG.CallLay.inB wbs ss 1024

abbrev ipArgs (f ss : Ptr) : List (Reg × Arg) := [(.x0, .ptr f), (.x1, .ptr ss)]

theorem ip_args {B : List Reg} {bs : List (Reg × Nat)} (L : VG.Proof.MlDsa.AArch64.LayIn B bs) {f ss : Ptr} (c2 : VG.CallLay.inB bs f 1024 = true)
    (c3 : VG.CallLay.inB bs ss 1024 = true) : ∀ a ∈ VG.Proof.MlDsa.AArch64.ipArgs f ss, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.AArch64.argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c2), by decide⟩, ⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c3), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {f ss : Ptr}
  (hc : VG.Proof.MlDsa.AArch64.ipChk rbs wbs f ss = true)
include L hc

theorem ip_cov : Covers ([] ++ [⟨VG.Proof.MlDsa.AArch64.pa s f, 1024⟩, ⟨VG.Proof.MlDsa.AArch64.pa s ss, 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨VG.Proof.MlDsa.AArch64.pa s f, 1024⟩, ⟨VG.Proof.MlDsa.AArch64.pa s ss, 1024⟩] s.wr := by
  simp only [VG.Proof.MlDsa.AArch64.ipChk, Bool.and_eq_true] at hc
  exact ⟨Covers.right (Covers.cons (L.cW hc.1.2) (L.cW hc.2)), Covers.cons (L.cW hc.1.2) (L.cW hc.2)⟩

theorem ip_pre {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} (hr : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) {s1 : State} (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.ipArgs f ss) s s1) :
    (inPlaceContract AArch64.abi t S).pre (s1.callEntry.withRegions [] [⟨VG.Proof.MlDsa.AArch64.pa s f, 1024⟩, ⟨VG.Proof.MlDsa.AArch64.pa s ss, 1024⟩]) := by
  simp only [VG.Proof.MlDsa.AArch64.ipChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, _⟩, _⟩ := hc
  sig_pre [inPlaceContract, inPlaceSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val]
  cpre L
  exact hr

end

theorem ipAt_ok {S : Nat} (hS : S < 2 ^ 64) {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {n : String} {c : Prog isa}
    (C : VG.Proof.MlDsa.AArch64.CalleeOk S c (inPlaceContract AArch64.abi t S)) {rbs wbs : List (Reg × Nat)} {s : State}
    (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {f ss : Ptr} (hc : VG.Proof.MlDsa.AArch64.ipChk rbs wbs f ss = true) (hr : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) :
    WP isa (callAt n c (VG.Proof.MlDsa.AArch64.ipArgs f ss)) s fun s' => VG.Proof.MlDsa.AArch64.PPostB S s s' [(f, 1024), (ss, 1024)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧ PolyIs s'.mem (VG.Proof.MlDsa.AArch64.pa s f) (t (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s f))) := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.ipChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨_, c2⟩, c3⟩, _⟩, _⟩ := hc'
  refine WP.mono (VG.Proof.MlDsa.AArch64.callAt_ok hS C (VG.Proof.MlDsa.AArch64.ip_args L.ok c2 c3) (by simp only [List.map_cons, List.map_nil]; decide) (fun s1 h1 => VG.Proof.MlDsa.AArch64.ip_pre L hc hr h1)
    (VG.Proof.MlDsa.AArch64.ip_cov L hc).1 (VG.Proof.MlDsa.AArch64.ip_cov L hc).2) fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [inPlaceContract, inPlaceSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.mem h1] at hq
  exact hq

theorem ipAt_tr {S : Nat} {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {n : String} {c : Prog isa}
    (C : VG.Proof.MlDsa.AArch64.CalleeOk S c (inPlaceContract AArch64.abi t S)) {rbs wbs : List (Reg × Nat)} {B : List Reg} (hB : VG.Proof.MlDsa.AArch64.LayIn B (rbs ++ wbs))
    {f ss : Ptr} (hc : VG.Proof.MlDsa.AArch64.ipChk rbs wbs f ss = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.AArch64.Lay S rbs wbs x ∧ VG.Proof.MlDsa.AArch64.Lay S rbs wbs y ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f) ∧
      VG.Proof.MlDsa.AArch64.SameIn B x y) :
    RelCT isa Q (callAt n c (VG.Proof.MlDsa.AArch64.ipArgs f ss)) fun _ _ => True := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.ipChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨_, c2⟩, c3⟩, _⟩, _⟩ := hc'
  refine VG.Proof.MlDsa.AArch64.callAt_tr C (VG.Proof.MlDsa.AArch64.ip_args hB c2 c3) (by simp only [List.map_cons, List.map_nil]; decide) fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨[], [⟨VG.Proof.MlDsa.AArch64.pa x f, 1024⟩, ⟨VG.Proof.MlDsa.AArch64.pa x ss, 1024⟩], VG.Proof.MlDsa.AArch64.ip_pre Lx hc rx h1, ?_, ?_, (VG.Proof.MlDsa.AArch64.ip_cov Lx hc).1, (VG.Proof.MlDsa.AArch64.ip_cov Lx hc).2,
    by rw [e.pa (VG.Proof.MlDsa.AArch64.ptr_bs hB c2), e.pa (VG.Proof.MlDsa.AArch64.ptr_bs hB c3)]; exact (VG.Proof.MlDsa.AArch64.ip_cov Ly hc).1,
    by rw [e.pa (VG.Proof.MlDsa.AArch64.ptr_bs hB c2), e.pa (VG.Proof.MlDsa.AArch64.ptr_bs hB c3)]; exact (VG.Proof.MlDsa.AArch64.ip_cov Ly hc).2⟩
  · rw [e.pa (VG.Proof.MlDsa.AArch64.ptr_bs hB c2), e.pa (VG.Proof.MlDsa.AArch64.ptr_bs hB c3)]; exact VG.Proof.MlDsa.AArch64.ip_pre Ly hc ry h2
  · sig_pub [inPlaceContract, inPlaceSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r0 h2, Args.r1 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa (VG.Proof.MlDsa.AArch64.ptr_bs hB c2), e.pa (VG.Proof.MlDsa.AArch64.ptr_bs hB c3)⟩

/-! ## Products -/

def mulChk (rbs wbs : List (Reg × Nat)) (h f g : Ptr) : Bool :=
  VG.Proof.MlDsa.AArch64.sepB rbs wbs h 1024 f 1024 && VG.Proof.MlDsa.AArch64.sepB rbs wbs h 1024 g 1024 && VG.CallLay.inB (rbs ++ wbs) h 1024 &&
    VG.CallLay.inB (rbs ++ wbs) f 1024 && VG.CallLay.inB (rbs ++ wbs) g 1024 && VG.CallLay.inB wbs h 1024

abbrev mulArgs (h f g : Ptr) : List (Reg × Arg) := [(.x0, .ptr h), (.x1, .ptr f), (.x2, .ptr g)]

theorem mul_args {B : List Reg} {bs : List (Reg × Nat)} (L : VG.Proof.MlDsa.AArch64.LayIn B bs) {h f g : Ptr} (c3 : VG.CallLay.inB bs h 1024 = true)
    (c4 : VG.CallLay.inB bs f 1024 = true) (c5 : VG.CallLay.inB bs g 1024 = true) :
    ∀ a ∈ VG.Proof.MlDsa.AArch64.mulArgs h f g, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.AArch64.argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c3), by decide⟩, ⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c4), by decide⟩, ⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c5), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {h f g : Ptr}
  (hc : VG.Proof.MlDsa.AArch64.mulChk rbs wbs h f g = true)
include L hc

theorem mul_cov : Covers ([⟨VG.Proof.MlDsa.AArch64.pa s f, 1024⟩, ⟨VG.Proof.MlDsa.AArch64.pa s g, 1024⟩] ++ [⟨VG.Proof.MlDsa.AArch64.pa s h, 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨VG.Proof.MlDsa.AArch64.pa s h, 1024⟩] s.wr := by
  simp only [VG.Proof.MlDsa.AArch64.mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, c4⟩, c5⟩, c6⟩ := hc
  exact ⟨Covers.append_left (Covers.cons (L.cR c4) (L.cR c5)) (Covers.right (L.cW c6)), L.cW c6⟩

theorem mul_pre (hf : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (hg : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s g)) {s1 : State}
    (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.mulArgs h f g) s s1) :
    (mulContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.AArch64.pa s f, 1024⟩, ⟨VG.Proof.MlDsa.AArch64.pa s g, 1024⟩] [⟨VG.Proof.MlDsa.AArch64.pa s h, 1024⟩]) := by
  simp only [VG.Proof.MlDsa.AArch64.mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc
  sig_pre [mulContract, mulSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val]
  cpre L
  exacts [hf, hg]

theorem mulAdd_pre (hh : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s h)) (hf : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (hg : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s g))
    {s1 : State} (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.mulArgs h f g) s s1) :
    (mulAddContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.AArch64.pa s f, 1024⟩, ⟨VG.Proof.MlDsa.AArch64.pa s g, 1024⟩] [⟨VG.Proof.MlDsa.AArch64.pa s h, 1024⟩]) := by
  simp only [VG.Proof.MlDsa.AArch64.mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc
  sig_pre [mulAddContract, mulSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val]
  cpre L
  exacts [hh, hf, hg]

end

theorem mulAt_ok {S : Nat} (hS : S < 2 ^ 64) {n : String} {c : Prog isa} (C : VG.Proof.MlDsa.AArch64.CalleeOk S c (mulContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {h f g : Ptr} (hc : VG.Proof.MlDsa.AArch64.mulChk rbs wbs h f g = true)
    (hf : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (hg : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s g)) :
    WP isa (callAt n c (VG.Proof.MlDsa.AArch64.mulArgs h f g)) s fun s' => VG.Proof.MlDsa.AArch64.PPostB S s s' [(h, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.AArch64.pa s h) (multiplyNTT (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s g))) := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.mulChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, _⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  refine WP.mono (VG.Proof.MlDsa.AArch64.callAt_ok hS C (VG.Proof.MlDsa.AArch64.mul_args L.ok c3 c4 c5) (by simp only [List.map_cons, List.map_nil]; decide) (fun s1 h1 => VG.Proof.MlDsa.AArch64.mul_pre L hc hf hg h1)
    (VG.Proof.MlDsa.AArch64.mul_cov L hc).1 (VG.Proof.MlDsa.AArch64.mul_cov L hc).2) fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [mulContract, mulSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1] at hq
  exact hq

theorem mulAddAt_ok {S : Nat} (hS : S < 2 ^ 64) {n : String} {c : Prog isa} (C : VG.Proof.MlDsa.AArch64.CalleeOk S c (mulAddContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {h f g : Ptr} (hc : VG.Proof.MlDsa.AArch64.mulChk rbs wbs h f g = true)
    (hh : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s h)) (hf : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (hg : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s g)) :
    WP isa (callAt n c (VG.Proof.MlDsa.AArch64.mulArgs h f g)) s fun s' => VG.Proof.MlDsa.AArch64.PPostB S s s' [(h, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.AArch64.pa s h) (add (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s h)) (multiplyNTT (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s g)))) := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.mulChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, _⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  refine WP.mono (VG.Proof.MlDsa.AArch64.callAt_ok hS C (VG.Proof.MlDsa.AArch64.mul_args L.ok c3 c4 c5) (by simp only [List.map_cons, List.map_nil]; decide) (fun s1 h1 => VG.Proof.MlDsa.AArch64.mulAdd_pre L hc hh hf hg h1)
    (VG.Proof.MlDsa.AArch64.mul_cov L hc).1 (VG.Proof.MlDsa.AArch64.mul_cov L hc).2) fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [mulAddContract, mulSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1] at hq
  exact hq

theorem mul_pub {x y x1 y1 : State} {h f g : Ptr} {B : List Reg} (hb : h.1 ∈ B ∧ f.1 ∈ B ∧ g.1 ∈ B) (e : VG.Proof.MlDsa.AArch64.SameIn B x y)
    (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.mulArgs h f g) x x1) (h2 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.mulArgs h f g) y y1) :
    x1.sp = y1.sp ∧ x1.gpr .x0 = y1.gpr .x0 ∧ x1.gpr .x1 = y1.gpr .x1 ∧ x1.gpr .x2 = y1.gpr .x2 := by
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2]
  simp only [Arg.val]
  exact ⟨e.2, e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩

theorem mulAt_tr {S : Nat} {n : String} {c : Prog isa} (C : VG.Proof.MlDsa.AArch64.CalleeOk S c (mulContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {B : List Reg} (hB : VG.Proof.MlDsa.AArch64.LayIn B (rbs ++ wbs)) {h f g : Ptr} (hc : VG.Proof.MlDsa.AArch64.mulChk rbs wbs h f g = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.AArch64.Lay S rbs wbs x ∧ VG.Proof.MlDsa.AArch64.Lay S rbs wbs y ∧ (Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y g)) ∧ VG.Proof.MlDsa.AArch64.SameIn B x y) :
    RelCT isa Q (callAt n c (VG.Proof.MlDsa.AArch64.mulArgs h f g)) fun _ _ => True := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.mulChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, _⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  have hb : h.1 ∈ B ∧ f.1 ∈ B ∧ g.1 ∈ B := ⟨VG.Proof.MlDsa.AArch64.ptr_bs hB c3, VG.Proof.MlDsa.AArch64.ptr_bs hB c4, VG.Proof.MlDsa.AArch64.ptr_bs hB c5⟩
  refine VG.Proof.MlDsa.AArch64.callAt_tr C (VG.Proof.MlDsa.AArch64.mul_args hB c3 c4 c5) (by simp only [List.map_cons, List.map_nil]; decide) fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.mul_pre Lx hc rx.1 rx.2 h1, ?_, ?_, (VG.Proof.MlDsa.AArch64.mul_cov Lx hc).1, (VG.Proof.MlDsa.AArch64.mul_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact VG.Proof.MlDsa.AArch64.mul_pre Ly hc ry.1 ry.2 h2
  · sig_pub [mulContract, mulSig, AArch64.abi, VG.AArch64.argRegs]
    exact VG.Proof.MlDsa.AArch64.mul_pub hb e h1 h2
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.mul_cov Ly hc).1
  · rw [e.pa hb.1]; exact (VG.Proof.MlDsa.AArch64.mul_cov Ly hc).2

theorem mulAddAt_tr {S : Nat} {n : String} {c : Prog isa} (C : VG.Proof.MlDsa.AArch64.CalleeOk S c (mulAddContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {B : List Reg} (hB : VG.Proof.MlDsa.AArch64.LayIn B (rbs ++ wbs)) {h f g : Ptr} (hc : VG.Proof.MlDsa.AArch64.mulChk rbs wbs h f g = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.AArch64.Lay S rbs wbs x ∧ VG.Proof.MlDsa.AArch64.Lay S rbs wbs y ∧
      (Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x h) ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y h) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y g)) ∧ VG.Proof.MlDsa.AArch64.SameIn B x y) :
    RelCT isa Q (callAt n c (VG.Proof.MlDsa.AArch64.mulArgs h f g)) fun _ _ => True := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.mulChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, _⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  have hb : h.1 ∈ B ∧ f.1 ∈ B ∧ g.1 ∈ B := ⟨VG.Proof.MlDsa.AArch64.ptr_bs hB c3, VG.Proof.MlDsa.AArch64.ptr_bs hB c4, VG.Proof.MlDsa.AArch64.ptr_bs hB c5⟩
  refine VG.Proof.MlDsa.AArch64.callAt_tr C (VG.Proof.MlDsa.AArch64.mul_args hB c3 c4 c5) (by simp only [List.map_cons, List.map_nil]; decide) fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.mulAdd_pre Lx hc rx.1 rx.2.1 rx.2.2 h1, ?_, ?_, (VG.Proof.MlDsa.AArch64.mul_cov Lx hc).1, (VG.Proof.MlDsa.AArch64.mul_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact VG.Proof.MlDsa.AArch64.mulAdd_pre Ly hc ry.1 ry.2.1 ry.2.2 h2
  · sig_pub [mulAddContract, mulSig, AArch64.abi, VG.AArch64.argRegs]
    exact VG.Proof.MlDsa.AArch64.mul_pub hb e h1 h2
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.mul_cov Ly hc).1
  · rw [e.pa hb.1]; exact (VG.Proof.MlDsa.AArch64.mul_cov Ly hc).2

/-! ## Addition and subtraction -/

def accChk (rbs wbs : List (Reg × Nat)) (f g : Ptr) : Bool :=
  VG.Proof.MlDsa.AArch64.sepB rbs wbs f 1024 g 1024 && VG.CallLay.inB (rbs ++ wbs) f 1024 && VG.CallLay.inB (rbs ++ wbs) g 1024 && VG.CallLay.inB wbs f 1024

abbrev accArgs (f g : Ptr) : List (Reg × Arg) := [(.x0, .ptr f), (.x1, .ptr g)]

theorem acc_args {B : List Reg} {bs : List (Reg × Nat)} (L : VG.Proof.MlDsa.AArch64.LayIn B bs) {f g : Ptr} (c2 : VG.CallLay.inB bs f 1024 = true)
    (c3 : VG.CallLay.inB bs g 1024 = true) : ∀ a ∈ VG.Proof.MlDsa.AArch64.accArgs f g, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.AArch64.argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c2), by decide⟩, ⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c3), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {f g : Ptr}
  (hc : VG.Proof.MlDsa.AArch64.accChk rbs wbs f g = true)
include L hc

theorem acc_cov : Covers ([⟨VG.Proof.MlDsa.AArch64.pa s g, 1024⟩] ++ [⟨VG.Proof.MlDsa.AArch64.pa s f, 1024⟩]) (s.rd ++ s.wr) ∧ Covers [⟨VG.Proof.MlDsa.AArch64.pa s f, 1024⟩] s.wr := by
  simp only [VG.Proof.MlDsa.AArch64.accChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, _⟩, c3⟩, c4⟩ := hc
  exact ⟨Covers.append_left (L.cR c3) (Covers.right (L.cW c4)), L.cW c4⟩

theorem acc_pre {op : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} (hf : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (hg : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s g)) {s1 : State}
    (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.accArgs f g) s s1) :
    (accSig.contract AArch64.abi (pre := fun f g m => Reduced m f ∧ Reduced m g)
      (post := fun f g m m' _ => PolyIs m' f (op (polyAt m f) (polyAt m g))) (writeArgs := true) (stack := S)).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.AArch64.pa s g, 1024⟩] [⟨VG.Proof.MlDsa.AArch64.pa s f, 1024⟩]) := by
  simp only [VG.Proof.MlDsa.AArch64.accChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, _⟩ := hc
  sig_pre [accSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val]
  cpre L
  exacts [hf, hg]

end

theorem accAt_ok {S : Nat} (hS : S < 2 ^ 64) {op : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {n : String} {c : Prog isa}
    (C : VG.Proof.MlDsa.AArch64.CalleeOk S c (accSig.contract AArch64.abi (pre := fun f g m => Reduced m f ∧ Reduced m g)
      (post := fun f g m m' _ => PolyIs m' f (op (polyAt m f) (polyAt m g))) (writeArgs := true) (stack := S)))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {f g : Ptr} (hc : VG.Proof.MlDsa.AArch64.accChk rbs wbs f g = true)
    (hf : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (hg : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s g)) :
    WP isa (callAt n c (VG.Proof.MlDsa.AArch64.accArgs f g)) s fun s' => VG.Proof.MlDsa.AArch64.PPostB S s s' [(f, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.AArch64.pa s f) (op (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s g))) := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.accChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc'
  refine WP.mono (VG.Proof.MlDsa.AArch64.callAt_ok hS C (VG.Proof.MlDsa.AArch64.acc_args L.ok c2 c3) (by simp only [List.map_cons, List.map_nil]; decide) (fun s1 h1 => VG.Proof.MlDsa.AArch64.acc_pre L hc hf hg h1)
    (VG.Proof.MlDsa.AArch64.acc_cov L hc).1 (VG.Proof.MlDsa.AArch64.acc_cov L hc).2) fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [accSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.mem h1] at hq
  exact hq

theorem accAt_tr {S : Nat} {op : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {n : String} {c : Prog isa}
    (C : VG.Proof.MlDsa.AArch64.CalleeOk S c (accSig.contract AArch64.abi (pre := fun f g m => Reduced m f ∧ Reduced m g)
      (post := fun f g m m' _ => PolyIs m' f (op (polyAt m f) (polyAt m g))) (writeArgs := true) (stack := S)))
    {rbs wbs : List (Reg × Nat)} {B : List Reg} (hB : VG.Proof.MlDsa.AArch64.LayIn B (rbs ++ wbs)) {f g : Ptr} (hc : VG.Proof.MlDsa.AArch64.accChk rbs wbs f g = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.AArch64.Lay S rbs wbs x ∧ VG.Proof.MlDsa.AArch64.Lay S rbs wbs y ∧ (Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y g)) ∧ VG.Proof.MlDsa.AArch64.SameIn B x y) :
    RelCT isa Q (callAt n c (VG.Proof.MlDsa.AArch64.accArgs f g)) fun _ _ => True := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.accChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc'
  have hb : f.1 ∈ B ∧ g.1 ∈ B := ⟨VG.Proof.MlDsa.AArch64.ptr_bs hB c2, VG.Proof.MlDsa.AArch64.ptr_bs hB c3⟩
  refine VG.Proof.MlDsa.AArch64.callAt_tr C (VG.Proof.MlDsa.AArch64.acc_args hB c2 c3) (by simp only [List.map_cons, List.map_nil]; decide) fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.acc_pre Lx hc rx.1 rx.2 h1, ?_, ?_, (VG.Proof.MlDsa.AArch64.acc_cov Lx hc).1, (VG.Proof.MlDsa.AArch64.acc_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2]; exact VG.Proof.MlDsa.AArch64.acc_pre Ly hc ry.1 ry.2 h2
  · sig_pub [accSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r0 h2, Args.r1 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb.1, e.pa hb.2⟩
  · rw [e.pa hb.1, e.pa hb.2]; exact (VG.Proof.MlDsa.AArch64.acc_cov Ly hc).1
  · rw [e.pa hb.1]; exact (VG.Proof.MlDsa.AArch64.acc_cov Ly hc).2

end VG.Proof.MlDsa.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Call.Blocks`. -/
section

/-!
# ML-DSA on AArch64: the blocks between calls

What the top-level functions' own instructions between their calls do, in
their layout: byte stores (`setB_ok`), copies of 32 bytes (`copyP_ok`,
ML-KEM's `copy32`), and the AND of a callee's result into `x24` (`and24_ok`).
-/

namespace VG.Proof.MlDsa.AArch64

open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_movz wp_strb)
open VG.Spec.Sha3 (bytesAt)

/-! ## 32-bit operations -/

theorem only_write32 (s : State) (d : Reg) (v : BitVec 32) : Only [d] s (s.write .w d v) :=
  ⟨fun r h => by simp only [List.mem_singleton] at h; simp [State.write, h], rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem write32_gpr (s : State) (d : Reg) (v : BitVec 32) : (s.write .w d v).gpr d = v.setWidth 64 := by
  simp [State.write]

theorem wp_and32 {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = ((s.gpr n).setWidth 32 &&& (s.gpr m).setWidth 32).setWidth 64 →
      WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and .w d n m :: is)) s Q :=
  VG.Proof.MlKem.AArch64.WP.cons (s' := s.write .w d ((s.gpr n).setWidth 32 &&& (s.gpr m).setWidth 32))
    (by simp [exec, State.read]) (k _ (VG.Proof.MlDsa.AArch64.only_write32 _ _ _) (VG.Proof.MlDsa.AArch64.write32_gpr _ _ _))

theorem and24_ok (s : State) :
    WP isa (.block and24) s fun s' => Only [.x24] s s' ∧
      s'.gpr .x24 = ((s.gpr .x24).setWidth 32 &&& (s.gpr .x0).setWidth 32).setWidth 64 :=
  VG.Proof.MlDsa.AArch64.wp_and32 fun _ h e => wp_nil ⟨h, e⟩

/-! ## Byte stores -/

theorem imm8 (v : Nat) : ((BitVec.ofNat 16 v).setWidth 64).setWidth 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem bytesAt_one (m : Mem) (a : Addr) : bytesAt m a 1 = [m a] := by
  simp [Spec.Sha3.bytesAt, BitVec.add_zero]

theorem writeW8_self (m : Mem) (a : Addr) (b : Byte) : m.writeW a b a = b := by
  rw [Proof.MlKem.writeW8_apply, Proof.MlDsa.KeyGen.ifp rfl]

theorem ne_x9 {r : Reg} (h : r ∈ VG.Proof.MlDsa.AArch64.keptRegs) : r ≠ .x9 := by
  intro e; rw [e] at h; revert h; decide

/-- The byte `v` to `p`. -/
theorem setB_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {p : Ptr} {v : Nat}
    (ho : p.2 < 4096) (hw : VG.CallLay.inB wbs p 1 = true) (hb : p.1 ∈ VG.Proof.MlDsa.AArch64.keptRegs) :
    WP isa (.block (setB p v)) s fun s' => VG.Proof.MlDsa.AArch64.PPostB S s s' [(p, 1)] ∧ Keep [.x9] s s' ∧
      s'.mem = s.mem.writeW (VG.Proof.MlDsa.AArch64.pa s p) (BitVec.ofNat 8 v) := by
  have h9 := VG.Proof.MlDsa.AArch64.ne_x9 hb
  refine wp_movz fun s₁ h₁ e₁ => wp_strb (a := VG.Proof.MlDsa.AArch64.pa s p) ho (by rw [h₁.get p.1 (by simpa using h9)])
    (by rw [h₁.wr]; exact L.inW hw) fun s₂ h₂ => wp_nil ?_
  have m₂ : s₂.mem = s.mem.writeW (VG.Proof.MlDsa.AArch64.pa s p) (BitVec.ofNat 8 v) := by rw [h₂.mem, e₁, h₁.mem, VG.Proof.MlDsa.AArch64.imm8 v]
  have k₂ : Keep [.x9] s s₂ := (h₁.keep.trans h₂.keep).mono (by simp)
  refine ⟨VG.Proof.MlDsa.AArch64.postB_of_keep k₂ (by decide) ?_, k₂, m₂⟩
  rw [m₂]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-! ## Copies of 32 bytes -/

/-- The 32 bytes at `src` can be copied to `dst`. -/
def copyPChk (rbs wbs : List (Reg × Nat)) (dst src : Ptr) : Bool :=
  decide (src.2 % 8 = 0 ∧ src.2 + 32 ≤ 32768) && decide (dst.2 % 8 = 0 ∧ dst.2 + 32 ≤ 32768) &&
    VG.Proof.MlDsa.AArch64.sepB rbs wbs src 32 dst 32 && VG.CallLay.inB wbs dst 32

theorem copyP_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {dst src : Ptr}
    (hc : VG.Proof.MlDsa.AArch64.copyPChk rbs wbs dst src = true) :
    WP isa (.block (Impl.MlKem.AArch64.copy32 src.1 src.2 dst.1 dst.2)) s fun s' =>
      VG.Proof.MlDsa.AArch64.PPostB S s s' [(dst, 32)] ∧ Keep [.x9] s s' ∧ bytesAt s'.mem (VG.Proof.MlDsa.AArch64.pa s dst) 32 = bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s src) 32 := by
  simp only [VG.Proof.MlDsa.AArch64.copyPChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hso, hdo⟩, hsep⟩, hw⟩ := hc
  have i1 := (VG.Proof.MlDsa.AArch64.sepB_spec hsep).1
  have i2 := (VG.Proof.MlDsa.AArch64.sepB_spec hsep).2.1
  refine WP.mono (Proof.MlKem.AArch64.KeyGen.copy_ok (S := s.gpr src.1) (D := s.gpr dst.1)
    (VG.Proof.MlDsa.AArch64.ne_x9 (L.ptrBs i1)) (VG.Proof.MlDsa.AArch64.ne_x9 (L.ptrBs i2)) hso hdo (L.disj hsep) rfl rfl (L.cR i1) (L.cW hw))
    fun s' ⟨k, f, b⟩ => ⟨VG.Proof.MlDsa.AArch64.postB_of_keep k (by decide) f, k, b⟩

end VG.Proof.MlDsa.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Call.Hash`. -/
section

/-!
# ML-DSA on AArch64: `H`, SHAKE256

`hashWith c .x28 0 200 136 0x1f ins [out]` (ML-KEM's `hash` on AArch64,
`Proof/MlKem/AArch64/HashProof.lean`, with the Keccak state and its working
space at the start of `scratch`): if the pieces are in the layout (a check
evaluated on the pointers, `hashChk`), it writes `H` of the concatenation of
the input pieces to the output piece, and changes nothing else but the Keccak
state and working space and the 16 bytes of stack below the stack pointer
(`shake_ok`).
-/

namespace VG.Proof.MlDsa.AArch64

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (HSetup PieceOk preg pbytes Kept Outs hashWith_ok)
open VG.Spec.Sha3 (bytesAt)

/-- The pointer and length of a piece. -/
abbrev pieceP (q : Impl.MlKem.AArch64.Piece) : Ptr × Nat := ((q.base, q.off), q.len)

/-- A piece in the layout (written if `w`), apart from the Keccak state and working space. -/
def pieceChk (rbs wbs : List (Reg × Nat)) (w : Bool) (q : Impl.MlKem.AArch64.Piece) : Bool :=
  decide (q.off < 65536) && decide (q.len < 65536) &&
    (if w then VG.CallLay.inB wbs (q.base, q.off) q.len else true) &&
    VG.Proof.MlDsa.AArch64.sepB rbs wbs (q.base, q.off) q.len (sc 0) 200 && VG.Proof.MlDsa.AArch64.sepB rbs wbs (q.base, q.off) q.len (sc 200) 640

/-- `H` of the pieces `ins`, to `out`, can run in the layout. -/
def hashChk (rbs wbs : List (Reg × Nat)) (ins : List Impl.MlKem.AArch64.Piece) (out : Impl.MlKem.AArch64.Piece) :
    Bool :=
  VG.CallLay.inB wbs (sc 0) 200 && VG.CallLay.inB wbs (sc 200) 640 && VG.Proof.MlDsa.AArch64.sepB rbs wbs (sc 0) 200 (sc 200) 640 &&
    ins.all (VG.Proof.MlDsa.AArch64.pieceChk rbs wbs false) && VG.Proof.MlDsa.AArch64.pieceChk rbs wbs true out

theorem hashChk_parts {rbs wbs : List (Reg × Nat)} {ins : List Impl.MlKem.AArch64.Piece}
    {out : Impl.MlKem.AArch64.Piece} (hc : VG.Proof.MlDsa.AArch64.hashChk rbs wbs ins out = true) :
    VG.CallLay.inB wbs (sc 0) 200 = true ∧ VG.CallLay.inB wbs (sc 200) 640 = true ∧ VG.Proof.MlDsa.AArch64.sepB rbs wbs (sc 0) 200 (sc 200) 640 = true ∧
      (∀ q ∈ ins, VG.Proof.MlDsa.AArch64.pieceChk rbs wbs false q = true) ∧ VG.Proof.MlDsa.AArch64.pieceChk rbs wbs true out = true := by
  simp only [VG.Proof.MlDsa.AArch64.hashChk, Bool.and_eq_true, List.all_eq_true] at hc
  exact ⟨hc.1.1.1.1, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) (h16 : 16 ≤ S) (hS : S < 2 ^ 64)
include L h16 hS

theorem Lay.stk16 {p : Ptr} {l : Nat} (h : VG.CallLay.inB (rbs ++ wbs) p l = true) :
    (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨VG.Proof.MlDsa.AArch64.pa s p, l⟩ :=
  (L.stkD h).sub_left (below_sub h16 hS)

theorem hsetup (hc : VG.CallLay.inB wbs (sc 0) 200 = true) (hc' : VG.CallLay.inB wbs (sc 200) 640 = true)
    (hd : VG.Proof.MlDsa.AArch64.sepB rbs wbs (sc 0) 200 (sc 200) 640 = true) : HSetup .x28 0 200 136 s := by
  have i1 : VG.CallLay.inB (rbs ++ wbs) (sc 0) 200 = true := (VG.Proof.MlDsa.AArch64.sepB_spec hd).1
  have i2 : VG.CallLay.inB (rbs ++ wbs) (sc 200) 640 = true := (VG.Proof.MlDsa.AArch64.sepB_spec hd).2.1
  have hd' := L.disj hd
  have k1 := L.stk16 h16 hS i1
  have k2 := L.stk16 h16 hS i2
  have cv := Covers.cons (L.cW hc) (L.cW hc')
  simp only [VG.Proof.MlDsa.AArch64.pa] at hd' k1 k2 cv
  have hr : (136 : Nat) ∈ Spec.Sha3.rates := by simp [Spec.Sha3.rates]
  have hsp : 16 ≤ s.sp.toNat := by have := L.spS; omega
  exact ⟨by decide, by decide, by decide, hr, hd', hsp, k1, k2, cv⟩

theorem pieceOk {w : Bool} {q : Impl.MlKem.AArch64.Piece} (hc : VG.Proof.MlDsa.AArch64.pieceChk rbs wbs w q = true) :
    PieceOk .x28 0 200 s w q := by
  simp only [VG.Proof.MlDsa.AArch64.pieceChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨ho, hl⟩, hw⟩, d1⟩, d2⟩ := hc
  have hin : VG.CallLay.inB (rbs ++ wbs) (q.base, q.off) q.len = true := (VG.Proof.MlDsa.AArch64.sepB_spec d1).1
  have hb : q.base ∈ VG.Proof.MlDsa.AArch64.keptRegs := L.ptrBs hin
  have e1 := L.disj d1
  have e2 := L.disj d2
  have e3 := L.stk16 h16 hS hin
  simp only [VG.Proof.MlDsa.AArch64.pa] at e1 e2 e3
  refine ⟨VG.Proof.MlDsa.AArch64.kept_pres _ hb, ho, hl, e1, e2, e3, ?_⟩
  cases w
  · exact L.cR hin
  · simp only [ite_true] at hw ⊢; exact L.cW hw

end

theorem shake256_eq' (m : List Byte) (d : Nat) :
    Spec.MlDsa.H m d = Spec.Sha3.squeezeFrom 136 (Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 (BitVec.ofNat 8 0x1f) m)) 0 d :=
  Proof.MlKem.shake256_eq m d

/-- `H` of the input pieces, to the output piece. -/
theorem shake_ok {S : Nat} (h16 : 16 ≤ S) (hS : S < 2 ^ 64) {rbs wbs : List (Reg × Nat)} {s : State}
    (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {ins : List Impl.MlKem.AArch64.Piece} {out : Impl.MlKem.AArch64.Piece}
    (hne : ins ≠ []) (hc : VG.Proof.MlDsa.AArch64.hashChk rbs wbs ins out = true) :
    WP isa (Impl.MlKem.AArch64.hashWith keccak.callee .x28 0 200 136 0x1f ins [out]) s fun s' =>
      VG.Proof.MlDsa.AArch64.PPostB S s s' [(sc 0, 200), (sc 200, 640), VG.Proof.MlDsa.AArch64.pieceP out] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (VG.Proof.MlDsa.AArch64.pa s (out.base, out.off)) out.len = Spec.MlDsa.H (ins.map (pbytes s)).flatten out.len := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := VG.Proof.MlDsa.AArch64.hashChk_parts hc
  refine WP.mono (hashWith_ok keccak (VG.Proof.MlDsa.AArch64.hsetup L h16 hS c1 c2 c3) (by decide) hne (fun q hq => VG.Proof.MlDsa.AArch64.pieceOk L h16 hS (c4 q hq))
    (fun q hq => by rw [List.mem_singleton.mp hq]; exact VG.Proof.MlDsa.AArch64.pieceOk L h16 hS c5) (List.pairwise_singleton _ _))
    fun s' ⟨k', o'⟩ => ⟨⟨k'.rd, k'.wr, k'.sp, fun r hr => k'.cs r (VG.Proof.MlDsa.AArch64.kept_pres r hr).1 (VG.Proof.MlDsa.AArch64.kept_pres r hr).2, ?_, k'.vcs⟩,
      k'.cs .x24 (by decide) (by decide), ?_⟩
  · refine k'.frame.sub fun r hr => ?_
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub h16 hS⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))),
        fun _ h => h⟩
  · rw [VG.Proof.MlDsa.AArch64.shake256_eq']
    exact o'.1

end VG.Proof.MlDsa.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Call.Pack`. -/
section

/-!
# ML-DSA on AArch64: calls of the encodings

For each call of `vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack` and
`vg_mldsa_bit_unpack`: what it needs of the layout (`…Chk`), what it does
(`…_ok`), and that two runs whose layout registers agree leak the same
(`…_tr`).
-/

namespace VG.Proof.MlDsa.AArch64

open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A polynomial read and a buffer written, apart. -/
def rwChk (rbs wbs : List (Reg × Nat)) (f : Ptr) (lf : Nat) (out : Ptr) (lo : Nat) : Bool :=
  VG.Proof.MlDsa.AArch64.sepB rbs wbs f lf out lo && VG.CallLay.inB (rbs ++ wbs) f lf && VG.CallLay.inB (rbs ++ wbs) out lo && VG.CallLay.inB wbs out lo

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {f out : Ptr} {lf lo : Nat}
  (hc : VG.Proof.MlDsa.AArch64.rwChk rbs wbs f lf out lo = true)
include L hc

theorem rw_cov : Covers ([⟨VG.Proof.MlDsa.AArch64.pa s f, lf⟩] ++ [⟨VG.Proof.MlDsa.AArch64.pa s out, lo⟩]) (s.rd ++ s.wr) ∧ Covers [⟨VG.Proof.MlDsa.AArch64.pa s out, lo⟩] s.wr := by
  simp only [VG.Proof.MlDsa.AArch64.rwChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, c2, _, c4⟩ := hc
  exact ⟨Covers.append_left (L.cR c2) (Covers.right (L.cW c4)), L.cW c4⟩

end

theorem rw_parts {rbs wbs : List (Reg × Nat)} {f out : Ptr} {lf lo : Nat} (hc : VG.Proof.MlDsa.AArch64.rwChk rbs wbs f lf out lo = true) :
    VG.Proof.MlDsa.AArch64.sepB rbs wbs f lf out lo = true ∧ VG.CallLay.inB (rbs ++ wbs) f lf = true ∧ VG.CallLay.inB (rbs ++ wbs) out lo = true := by
  simp only [VG.Proof.MlDsa.AArch64.rwChk, Bool.and_eq_true, and_assoc] at hc
  exact ⟨hc.1, hc.2.1, hc.2.2.1⟩

/-! ## `SimpleBitPack` -/

abbrev sbpArgs (f : Ptr) (b : Nat) (out : Ptr) (len : Nat) : List (Reg × Arg) :=
  [(.x0, .ptr f), (.x1, .imm b), (.x2, .ptr out), (.x3, .imm len)]

theorem sbp_args {B : List Reg} {bs : List (Reg × Nat)} (L : VG.Proof.MlDsa.AArch64.LayIn B bs) {f out : Ptr} (b len : Nat) (c2 : VG.CallLay.inB bs f 1024 = true)
    (c3 : VG.CallLay.inB bs out len = true) : ∀ x ∈ VG.Proof.MlDsa.AArch64.sbpArgs f b out len, x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.AArch64.argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c2), by decide⟩, ⟨trivial, by decide⟩, ⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c3), by decide⟩,
    ⟨trivial, by decide⟩⟩

/-- What `SimpleBitPack` asks of its arguments. -/
structure SbpOk (b len : Nat) : Prop where
  hb : b ∈ simpleBitPackBounds
  hlen : len = 32 * bitlen b
  hlt : b < 2 ^ 32 ∧ len < 2 ^ 32

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {f out : Ptr} {b len : Nat}
  (hc : VG.Proof.MlDsa.AArch64.rwChk rbs wbs f 1024 out len = true)
include L hc

theorem sbp_pre (hb : VG.Proof.MlDsa.AArch64.SbpOk b len) (hf : ∀ i < n, (coeffAt s.mem (VG.Proof.MlDsa.AArch64.pa s f) i).toNat ≤ b) {s1 : State}
    (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.sbpArgs f b out len) s s1) :
    (simpleBitPackContract AArch64.abi S).pre (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.AArch64.pa s f, 1024⟩] [⟨VG.Proof.MlDsa.AArch64.pa s out, len⟩]) := by
  obtain ⟨c1, c2, c3⟩ := VG.Proof.MlDsa.AArch64.rw_parts hc
  sig_pre [simpleBitPackContract, simpleBitPackSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val, VG.Proof.MlDsa.AArch64.imm32 hb.hlt.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show len < 2 ^ 64 by have := hb.hlt.2; omega)]
  cpre L
  exacts [hb.hb, hb.hlen, hf]

end

theorem sbpAt_ok {S : Nat} (hS : S < 2 ^ 64) {nm : String} {cd : Prog isa}
    (C : VG.Proof.MlDsa.AArch64.CalleeOk S cd (simpleBitPackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {f out : Ptr} {b len : Nat}
    (hc : VG.Proof.MlDsa.AArch64.rwChk rbs wbs f 1024 out len = true) (hb : VG.Proof.MlDsa.AArch64.SbpOk b len)
    (hf : ∀ i < n, (coeffAt s.mem (VG.Proof.MlDsa.AArch64.pa s f) i).toNat ≤ b) :
    WP isa (callAt nm cd (VG.Proof.MlDsa.AArch64.sbpArgs f b out len)) s fun s' => VG.Proof.MlDsa.AArch64.PPostB S s s' [(out, len)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (VG.Proof.MlDsa.AArch64.pa s out) len = simpleBitPack (natPolyAt s.mem (VG.Proof.MlDsa.AArch64.pa s f)) b := by
  obtain ⟨_, c2, c3⟩ := VG.Proof.MlDsa.AArch64.rw_parts hc
  refine WP.mono (VG.Proof.MlDsa.AArch64.callAt_ok hS C (VG.Proof.MlDsa.AArch64.sbp_args L.ok b len c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.AArch64.sbp_pre L hc hb hf h1) (VG.Proof.MlDsa.AArch64.rw_cov L hc).1 (VG.Proof.MlDsa.AArch64.rw_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [simpleBitPackContract, simpleBitPackSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.mem h1] at hq
  simp only [Arg.val, VG.Proof.MlDsa.AArch64.imm32 hb.hlt.1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by have := hb.hlt.2; omega)] at hq
  exact hq

theorem sbpAt_tr {S : Nat} {nm : String} {cd : Prog isa} (C : VG.Proof.MlDsa.AArch64.CalleeOk S cd (simpleBitPackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {B : List Reg} (hB : VG.Proof.MlDsa.AArch64.LayIn B (rbs ++ wbs)) {f out : Ptr} {b len : Nat}
    (hc : VG.Proof.MlDsa.AArch64.rwChk rbs wbs f 1024 out len = true) (hb : VG.Proof.MlDsa.AArch64.SbpOk b len) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.AArch64.Lay S rbs wbs x ∧ VG.Proof.MlDsa.AArch64.Lay S rbs wbs y ∧ (∀ i < n, (coeffAt x.mem (VG.Proof.MlDsa.AArch64.pa x f) i).toNat ≤ b) ∧
      (∀ i < n, (coeffAt y.mem (VG.Proof.MlDsa.AArch64.pa y f) i).toNat ≤ b) ∧ VG.Proof.MlDsa.AArch64.SameIn B x y) :
    RelCT isa Q (callAt nm cd (VG.Proof.MlDsa.AArch64.sbpArgs f b out len)) fun _ _ => True := by
  obtain ⟨_, c2, c3⟩ := VG.Proof.MlDsa.AArch64.rw_parts hc
  have hbs : f.1 ∈ B ∧ out.1 ∈ B := ⟨VG.Proof.MlDsa.AArch64.ptr_bs hB c2, VG.Proof.MlDsa.AArch64.ptr_bs hB c3⟩
  refine VG.Proof.MlDsa.AArch64.callAt_tr C (VG.Proof.MlDsa.AArch64.sbp_args hB b len c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.sbp_pre Lx hc hb rx h1, ?_, ?_, (VG.Proof.MlDsa.AArch64.rw_cov Lx hc).1, (VG.Proof.MlDsa.AArch64.rw_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact VG.Proof.MlDsa.AArch64.sbp_pre Ly hc hb ry h2
  · sig_pub [simpleBitPackContract, simpleBitPackSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.r3 h2,
      Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hbs.1, trivial, e.pa hbs.2, trivial⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact (VG.Proof.MlDsa.AArch64.rw_cov Ly hc).1
  · rw [e.pa hbs.2]; exact (VG.Proof.MlDsa.AArch64.rw_cov Ly hc).2

/-! ## `BitPack` -/

abbrev bpArgs (f : Ptr) (a b : Nat) (out : Ptr) (len : Nat) : List (Reg × Arg) :=
  [(.x0, .ptr f), (.x1, .imm a), (.x2, .imm b), (.x3, .ptr out), (.x4, .imm len)]

theorem bp_args {B : List Reg} {bs : List (Reg × Nat)} (L : VG.Proof.MlDsa.AArch64.LayIn B bs) {f out : Ptr} (a b len : Nat) (c2 : VG.CallLay.inB bs f 1024 = true)
    (c3 : VG.CallLay.inB bs out len = true) : ∀ x ∈ VG.Proof.MlDsa.AArch64.bpArgs f a b out len, x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.AArch64.argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c2), by decide⟩, ⟨trivial, by decide⟩, ⟨trivial, by decide⟩,
    ⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c3), by decide⟩, ⟨trivial, by decide⟩⟩

/-- What `BitPack` and `BitUnpack` ask of their arguments. -/
structure BpOk (a b len : Nat) : Prop where
  hab : (a, b) ∈ bitPackParams
  hlen : len = 32 * bitlen (a + b)
  hlt : a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ len < 2 ^ 32

/-- The coefficients `BitPack` packs are in range. -/
def BpRange (m : Mem) (f : Addr) (a b : Nat) : Prop :=
  ∀ i < n, -(a : Int) ≤ modPm (coeffAt m f i).toNat q ∧ modPm (coeffAt m f i).toNat q ≤ b

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {f out : Ptr} {a b len : Nat}
  (hc : VG.Proof.MlDsa.AArch64.rwChk rbs wbs f 1024 out len = true)
include L hc

theorem bp_pre (hb : VG.Proof.MlDsa.AArch64.BpOk a b len) (hr : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (hf : VG.Proof.MlDsa.AArch64.BpRange s.mem (VG.Proof.MlDsa.AArch64.pa s f) a b) {s1 : State}
    (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.bpArgs f a b out len) s s1) :
    (bitPackContract AArch64.abi S).pre (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.AArch64.pa s f, 1024⟩] [⟨VG.Proof.MlDsa.AArch64.pa s out, len⟩]) := by
  obtain ⟨c1, c2, c3⟩ := VG.Proof.MlDsa.AArch64.rw_parts hc
  sig_pre [bitPackContract, bitPackSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val, VG.Proof.MlDsa.AArch64.imm32 hb.hlt.1, VG.Proof.MlDsa.AArch64.imm32 hb.hlt.2.1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by have := hb.hlt.2.2; omega)]
  cpre L
  exacts [hb.hab, hb.hlen, hr, hf]

end

theorem bpAt_ok {S : Nat} (hS : S < 2 ^ 64) {nm : String} {cd : Prog isa} (C : VG.Proof.MlDsa.AArch64.CalleeOk S cd (bitPackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {f out : Ptr} {a b len : Nat}
    (hc : VG.Proof.MlDsa.AArch64.rwChk rbs wbs f 1024 out len = true) (hb : VG.Proof.MlDsa.AArch64.BpOk a b len) (hr : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f))
    (hf : VG.Proof.MlDsa.AArch64.BpRange s.mem (VG.Proof.MlDsa.AArch64.pa s f) a b) :
    WP isa (callAt nm cd (VG.Proof.MlDsa.AArch64.bpArgs f a b out len)) s fun s' => VG.Proof.MlDsa.AArch64.PPostB S s s' [(out, len)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (VG.Proof.MlDsa.AArch64.pa s out) len = bitPack ((polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s f)).map fun c => modPm c.val q) a b := by
  obtain ⟨_, c2, c3⟩ := VG.Proof.MlDsa.AArch64.rw_parts hc
  refine WP.mono (VG.Proof.MlDsa.AArch64.callAt_ok hS C (VG.Proof.MlDsa.AArch64.bp_args L.ok a b len c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.AArch64.bp_pre L hc hb hr hf h1) (VG.Proof.MlDsa.AArch64.rw_cov L hc).1 (VG.Proof.MlDsa.AArch64.rw_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [bitPackContract, bitPackSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.mem h1] at hq
  simp only [Arg.val, VG.Proof.MlDsa.AArch64.imm32 hb.hlt.1, VG.Proof.MlDsa.AArch64.imm32 hb.hlt.2.1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by have := hb.hlt.2.2; omega)] at hq
  exact hq

theorem bpAt_tr {S : Nat} {nm : String} {cd : Prog isa} (C : VG.Proof.MlDsa.AArch64.CalleeOk S cd (bitPackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {B : List Reg} (hB : VG.Proof.MlDsa.AArch64.LayIn B (rbs ++ wbs)) {f out : Ptr} {a b len : Nat}
    (hc : VG.Proof.MlDsa.AArch64.rwChk rbs wbs f 1024 out len = true) (hb : VG.Proof.MlDsa.AArch64.BpOk a b len) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.AArch64.Lay S rbs wbs x ∧ VG.Proof.MlDsa.AArch64.Lay S rbs wbs y ∧
      (Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ VG.Proof.MlDsa.AArch64.BpRange x.mem (VG.Proof.MlDsa.AArch64.pa x f) a b) ∧ (Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f) ∧ VG.Proof.MlDsa.AArch64.BpRange y.mem (VG.Proof.MlDsa.AArch64.pa y f) a b) ∧
      VG.Proof.MlDsa.AArch64.SameIn B x y) :
    RelCT isa Q (callAt nm cd (VG.Proof.MlDsa.AArch64.bpArgs f a b out len)) fun _ _ => True := by
  obtain ⟨_, c2, c3⟩ := VG.Proof.MlDsa.AArch64.rw_parts hc
  have hbs : f.1 ∈ B ∧ out.1 ∈ B := ⟨VG.Proof.MlDsa.AArch64.ptr_bs hB c2, VG.Proof.MlDsa.AArch64.ptr_bs hB c3⟩
  refine VG.Proof.MlDsa.AArch64.callAt_tr C (VG.Proof.MlDsa.AArch64.bp_args hB a b len c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.bp_pre Lx hc hb rx.1 rx.2 h1, ?_, ?_, (VG.Proof.MlDsa.AArch64.rw_cov Lx hc).1, (VG.Proof.MlDsa.AArch64.rw_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact VG.Proof.MlDsa.AArch64.bp_pre Ly hc hb ry.1 ry.2 h2
  · sig_pub [bitPackContract, bitPackSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2,
      Args.r3 h2, Args.r4 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hbs.1, trivial, trivial, e.pa hbs.2, trivial⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact (VG.Proof.MlDsa.AArch64.rw_cov Ly hc).1
  · rw [e.pa hbs.2]; exact (VG.Proof.MlDsa.AArch64.rw_cov Ly hc).2

/-! ## `BitUnpack` -/

abbrev buArgs (v : Ptr) (len a b : Nat) (f : Ptr) : List (Reg × Arg) :=
  [(.x0, .ptr v), (.x1, .imm len), (.x2, .imm a), (.x3, .imm b), (.x4, .ptr f)]

theorem bu_args {B : List Reg} {bs : List (Reg × Nat)} (L : VG.Proof.MlDsa.AArch64.LayIn B bs) {v f : Ptr} (len a b : Nat) (c2 : VG.CallLay.inB bs v len = true)
    (c3 : VG.CallLay.inB bs f 1024 = true) : ∀ x ∈ VG.Proof.MlDsa.AArch64.buArgs v len a b f, x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.AArch64.argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c2), by decide⟩, ⟨trivial, by decide⟩, ⟨trivial, by decide⟩, ⟨trivial, by decide⟩,
    ⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c3), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {v f : Ptr} {a b len : Nat}
  (hc : VG.Proof.MlDsa.AArch64.rwChk rbs wbs v len f 1024 = true)
include L hc

theorem bu_pre (hb : VG.Proof.MlDsa.AArch64.BpOk a b len) {s1 : State} (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.buArgs v len a b f) s s1) :
    (bitUnpackContract AArch64.abi S).pre (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.AArch64.pa s v, len⟩] [⟨VG.Proof.MlDsa.AArch64.pa s f, 1024⟩]) := by
  obtain ⟨c1, c2, c3⟩ := VG.Proof.MlDsa.AArch64.rw_parts hc
  sig_pre [bitUnpackContract, bitUnpackSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.sp h1]
  simp only [Arg.val, VG.Proof.MlDsa.AArch64.imm32 hb.hlt.1, VG.Proof.MlDsa.AArch64.imm32 hb.hlt.2.1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by have := hb.hlt.2.2; omega)]
  cpre L
  exacts [hb.hab, hb.hlen]

end

theorem buAt_ok {S : Nat} (hS : S < 2 ^ 64) {nm : String} {cd : Prog isa} (C : VG.Proof.MlDsa.AArch64.CalleeOk S cd (bitUnpackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {v f : Ptr} {a b len : Nat}
    (hc : VG.Proof.MlDsa.AArch64.rwChk rbs wbs v len f 1024 = true) (hb : VG.Proof.MlDsa.AArch64.BpOk a b len) :
    WP isa (callAt nm cd (VG.Proof.MlDsa.AArch64.buArgs v len a b f)) s fun s' => VG.Proof.MlDsa.AArch64.PPostB S s s' [(f, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.AArch64.pa s f) (toRq (bitUnpack (bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s v) len) a b)) := by
  obtain ⟨_, c2, c3⟩ := VG.Proof.MlDsa.AArch64.rw_parts hc
  refine WP.mono (VG.Proof.MlDsa.AArch64.callAt_ok hS C (VG.Proof.MlDsa.AArch64.bu_args L.ok len a b c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.AArch64.bu_pre L hc hb h1) (VG.Proof.MlDsa.AArch64.rw_cov L hc).1 (VG.Proof.MlDsa.AArch64.rw_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [bitUnpackContract, bitUnpackSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.mem h1] at hq
  simp only [Arg.val, VG.Proof.MlDsa.AArch64.imm32 hb.hlt.1, VG.Proof.MlDsa.AArch64.imm32 hb.hlt.2.1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by have := hb.hlt.2.2; omega)] at hq
  exact hq

theorem buAt_tr {S : Nat} {nm : String} {cd : Prog isa} (C : VG.Proof.MlDsa.AArch64.CalleeOk S cd (bitUnpackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {B : List Reg} (hB : VG.Proof.MlDsa.AArch64.LayIn B (rbs ++ wbs)) {v f : Ptr} {a b len : Nat}
    (hc : VG.Proof.MlDsa.AArch64.rwChk rbs wbs v len f 1024 = true) (hb : VG.Proof.MlDsa.AArch64.BpOk a b len) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.AArch64.Lay S rbs wbs x ∧ VG.Proof.MlDsa.AArch64.Lay S rbs wbs y ∧ VG.Proof.MlDsa.AArch64.SameIn B x y) :
    RelCT isa Q (callAt nm cd (VG.Proof.MlDsa.AArch64.buArgs v len a b f)) fun _ _ => True := by
  obtain ⟨_, c2, c3⟩ := VG.Proof.MlDsa.AArch64.rw_parts hc
  have hbs : v.1 ∈ B ∧ f.1 ∈ B := ⟨VG.Proof.MlDsa.AArch64.ptr_bs hB c2, VG.Proof.MlDsa.AArch64.ptr_bs hB c3⟩
  refine VG.Proof.MlDsa.AArch64.callAt_tr C (VG.Proof.MlDsa.AArch64.bu_args hB len a b c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, e⟩ := hQ x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.bu_pre Lx hc hb h1, ?_, ?_, (VG.Proof.MlDsa.AArch64.rw_cov Lx hc).1, (VG.Proof.MlDsa.AArch64.rw_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact VG.Proof.MlDsa.AArch64.bu_pre Ly hc hb h2
  · sig_pub [bitUnpackContract, bitUnpackSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2,
      Args.r3 h2, Args.r4 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hbs.1, trivial, trivial, trivial, e.pa hbs.2⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact (VG.Proof.MlDsa.AArch64.rw_cov Ly hc).1
  · rw [e.pa hbs.2]; exact (VG.Proof.MlDsa.AArch64.rw_cov Ly hc).2

end VG.Proof.MlDsa.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Call.Round`. -/
section

/-!
# ML-DSA on AArch64: calls of the norm

For each call of `vg_mldsa_norm_lt`: what it needs of the layout (`…Chk`),
what it does (`…_ok`), and that two runs whose layout registers agree leak the
same (`…_tr`).
-/

namespace VG.Proof.MlDsa.AArch64

open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The norm -/

abbrev normArgs (f : Ptr) (bound : Nat) : List (Reg × Arg) := [(.x0, .ptr f), (.x1, .imm bound)]

theorem norm_args {B : List Reg} {bs : List (Reg × Nat)} (L : VG.Proof.MlDsa.AArch64.LayIn B bs) {f : Ptr} (bound : Nat) (c1 : VG.CallLay.inB bs f 1024 = true) :
    ∀ x ∈ VG.Proof.MlDsa.AArch64.normArgs f bound, x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.AArch64.argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c1), by decide⟩, ⟨trivial, by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {f : Ptr}
  (hc : VG.CallLay.inB (rbs ++ wbs) f 1024 = true)
include L hc

theorem norm_cov : Covers ([⟨VG.Proof.MlDsa.AArch64.pa s f, 1024⟩] ++ []) (s.rd ++ s.wr) ∧ Covers [] s.wr :=
  ⟨by rw [List.append_nil]; exact L.cR hc, Covers.nil⟩

theorem norm_pre {bound : Nat} (hr : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) {s1 : State} (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.normArgs f bound) s s1) :
    (normLtContract AArch64.abi S).pre (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.AArch64.pa s f, 1024⟩] []) := by
  sig_pre [normLtContract, normLtSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val]
  cpre L
  exact hr

end

theorem normAt_ok {S : Nat} (hS : S < 2 ^ 64) {nm : String} {cd : Prog isa} (C : VG.Proof.MlDsa.AArch64.CalleeOk S cd (normLtContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {f : Ptr} (hc : VG.CallLay.inB (rbs ++ wbs) f 1024 = true)
    {bound : Nat} (hb : bound < 2 ^ 32) (hr : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) :
    WP isa (callAt nm cd (VG.Proof.MlDsa.AArch64.normArgs f bound)) s fun s' => VG.Proof.MlDsa.AArch64.PPostB S s s' [] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      (s'.gpr .x0).setWidth 32 = if normRq [polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s f)] < bound then 1 else 0 := by
  refine WP.mono (VG.Proof.MlDsa.AArch64.callAt_ok hS C (VG.Proof.MlDsa.AArch64.norm_args L.ok bound hc) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.AArch64.norm_pre L hc hr h1) (VG.Proof.MlDsa.AArch64.norm_cov L hc).1 (VG.Proof.MlDsa.AArch64.norm_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [normLtContract, normLtSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.mem h1] at hq
  simp only [Arg.val, VG.Proof.MlDsa.AArch64.imm32 hb] at hq
  exact hq

theorem normAt_tr {S : Nat} {nm : String} {cd : Prog isa} (C : VG.Proof.MlDsa.AArch64.CalleeOk S cd (normLtContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {B : List Reg} (hB : VG.Proof.MlDsa.AArch64.LayIn B (rbs ++ wbs)) {f : Ptr} (hc : VG.CallLay.inB (rbs ++ wbs) f 1024 = true)
    {bound : Nat} {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.AArch64.Lay S rbs wbs x ∧ VG.Proof.MlDsa.AArch64.Lay S rbs wbs y ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f) ∧
      VG.Proof.MlDsa.AArch64.SameIn B x y) :
    RelCT isa Q (callAt nm cd (VG.Proof.MlDsa.AArch64.normArgs f bound)) fun _ _ => True := by
  have hb : f.1 ∈ B := VG.Proof.MlDsa.AArch64.ptr_bs hB hc
  refine VG.Proof.MlDsa.AArch64.callAt_tr C (VG.Proof.MlDsa.AArch64.norm_args hB bound hc) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.norm_pre Lx hc rx h1, ?_, ?_, (VG.Proof.MlDsa.AArch64.norm_cov Lx hc).1, (VG.Proof.MlDsa.AArch64.norm_cov Lx hc).2, ?_, (VG.Proof.MlDsa.AArch64.norm_cov Ly hc).2⟩
  · rw [e.pa hb]; exact VG.Proof.MlDsa.AArch64.norm_pre Ly hc ry h2
  · sig_pub [normLtContract, normLtSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r0 h2, Args.r1 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb, trivial⟩
  · rw [e.pa hb]; exact (VG.Proof.MlDsa.AArch64.norm_cov Ly hc).1

/-- The values of `γ₂`, as an immediate. -/
theorem gamma2_lt {g2 : Nat} (h : g2 ∈ gamma2s) : g2 < 2 ^ 32 := by
  simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Call.Sample`. -/
section

/-!
# ML-DSA on AArch64: calls of the samplers

For each call of `vg_mldsa_rej_ntt_poly` and `vg_mldsa_sample_in_ball`: what it
needs of the layout (`…Chk`), what it does (`…_ok`), and that two runs whose
layout registers agree, and whose sampler leaks the same, leak the same
(`…_tr`).
-/

namespace VG.Proof.MlDsa.AArch64

open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `RejNTTPoly` -/

def rejNttChk (rbs wbs : List (Reg × Nat)) (seed a ss : Ptr) : Bool :=
  VG.Proof.MlDsa.AArch64.sepB rbs wbs seed 34 a 1024 && VG.Proof.MlDsa.AArch64.sepB rbs wbs seed 34 ss 2048 && VG.Proof.MlDsa.AArch64.sepB rbs wbs a 1024 ss 2048 &&
    VG.CallLay.inB (rbs ++ wbs) seed 34 && VG.CallLay.inB (rbs ++ wbs) a 1024 && VG.CallLay.inB (rbs ++ wbs) ss 2048 && VG.CallLay.inB wbs a 1024 &&
    VG.CallLay.inB wbs ss 2048

abbrev rejNttArgs (seed a ss : Ptr) : List (Reg × Arg) := [(.x0, .ptr seed), (.x1, .ptr a), (.x2, .ptr ss)]

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {seed a ss : Ptr}
  (hc : VG.Proof.MlDsa.AArch64.rejNttChk rbs wbs seed a ss = true)
include L hc

theorem rejNtt_cov : Covers ([⟨VG.Proof.MlDsa.AArch64.pa s seed, 34⟩] ++ [⟨VG.Proof.MlDsa.AArch64.pa s a, 1024⟩, ⟨VG.Proof.MlDsa.AArch64.pa s ss, 2048⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨VG.Proof.MlDsa.AArch64.pa s a, 1024⟩, ⟨VG.Proof.MlDsa.AArch64.pa s ss, 2048⟩] s.wr := by
  simp only [VG.Proof.MlDsa.AArch64.rejNttChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, _, c4, _, _, c7, c8⟩ := hc
  exact ⟨Covers.append_left (L.cR c4) (Covers.right (Covers.cons (L.cW c7) (L.cW c8))), Covers.cons (L.cW c7) (L.cW c8)⟩

theorem rejNtt_pre {s1 : State} (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.rejNttArgs seed a ss) s s1) :
    (rejNTTContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.AArch64.pa s seed, 34⟩] [⟨VG.Proof.MlDsa.AArch64.pa s a, 1024⟩, ⟨VG.Proof.MlDsa.AArch64.pa s ss, 2048⟩]) := by
  simp only [VG.Proof.MlDsa.AArch64.rejNttChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [rejNTTContract, rejNTTSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.sp h1]
  simp only [Arg.val]
  cpre L

end

theorem rejNtt_args {B : List Reg} {bs : List (Reg × Nat)} (L : VG.Proof.MlDsa.AArch64.LayIn B bs) {seed a ss : Ptr} (c4 : VG.CallLay.inB bs seed 34 = true)
    (c5 : VG.CallLay.inB bs a 1024 = true) (c6 : VG.CallLay.inB bs ss 2048 = true) :
    ∀ x ∈ VG.Proof.MlDsa.AArch64.rejNttArgs seed a ss, x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.AArch64.argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c4), by decide⟩, ⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c5), by decide⟩, ⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c6), by decide⟩⟩

theorem rejNttAt_ok {S : Nat} (hS : S < 2 ^ 64) {nm : String} {cd : Prog isa} (C : VG.Proof.MlDsa.AArch64.CalleeOk S cd (rejNTTContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {seed a ss : Ptr}
    (hc : VG.Proof.MlDsa.AArch64.rejNttChk rbs wbs seed a ss = true) :
    WP isa (callAt nm cd (VG.Proof.MlDsa.AArch64.rejNttArgs seed a ss)) s fun s' => VG.Proof.MlDsa.AArch64.PPostB S s s' [(a, 1024), (ss, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → Reduced s'.mem (VG.Proof.MlDsa.AArch64.pa s a)) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s seed) 34)) ((s'.gpr .x0).setWidth 32)
        (polyAt s'.mem (VG.Proof.MlDsa.AArch64.pa s a)) := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.rejNttChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (VG.Proof.MlDsa.AArch64.callAt_ok hS C (VG.Proof.MlDsa.AArch64.rejNtt_args L.ok c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.AArch64.rejNtt_pre L hc h1) (VG.Proof.MlDsa.AArch64.rejNtt_cov L hc).1 (VG.Proof.MlDsa.AArch64.rejNtt_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [rejNTTContract, rejNTTSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.mem h1] at hq
  exact hq

theorem rejNttAt_tr {S : Nat} {nm : String} {cd : Prog isa} (C : VG.Proof.MlDsa.AArch64.CalleeOk S cd (rejNTTContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {B : List Reg} (hB : VG.Proof.MlDsa.AArch64.LayIn B (rbs ++ wbs)) {seed a ss : Ptr} (hc : VG.Proof.MlDsa.AArch64.rejNttChk rbs wbs seed a ss = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.AArch64.Lay S rbs wbs x ∧ VG.Proof.MlDsa.AArch64.Lay S rbs wbs y ∧
      bytesAt x.mem (VG.Proof.MlDsa.AArch64.pa x seed) 34 = bytesAt y.mem (VG.Proof.MlDsa.AArch64.pa y seed) 34 ∧ VG.Proof.MlDsa.AArch64.SameIn B x y) :
    RelCT isa Q (callAt nm cd (VG.Proof.MlDsa.AArch64.rejNttArgs seed a ss)) fun _ _ => True := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.rejNttChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ B ∧ a.1 ∈ B ∧ ss.1 ∈ B := ⟨VG.Proof.MlDsa.AArch64.ptr_bs hB c4, VG.Proof.MlDsa.AArch64.ptr_bs hB c5, VG.Proof.MlDsa.AArch64.ptr_bs hB c6⟩
  refine VG.Proof.MlDsa.AArch64.callAt_tr C (VG.Proof.MlDsa.AArch64.rejNtt_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.rejNtt_pre Lx hc h1, ?_, ?_, (VG.Proof.MlDsa.AArch64.rejNtt_cov Lx hc).1, (VG.Proof.MlDsa.AArch64.rejNtt_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact VG.Proof.MlDsa.AArch64.rejNtt_pre Ly hc h2
  · sig_pub [rejNTTContract, rejNTTSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2,
      Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.rejNtt_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.rejNtt_cov Ly hc).2

/-! ## `SampleInBall` -/

def ballChk (rbs wbs : List (Reg × Nat)) (ct : Ptr) (len : Nat) (c ss : Ptr) : Bool :=
  VG.Proof.MlDsa.AArch64.sepB rbs wbs ct len c 1024 && VG.Proof.MlDsa.AArch64.sepB rbs wbs ct len ss 2048 && VG.Proof.MlDsa.AArch64.sepB rbs wbs c 1024 ss 2048 &&
    VG.CallLay.inB (rbs ++ wbs) ct len && VG.CallLay.inB (rbs ++ wbs) c 1024 && VG.CallLay.inB (rbs ++ wbs) ss 2048 && VG.CallLay.inB wbs c 1024 &&
    VG.CallLay.inB wbs ss 2048

abbrev ballArgs (ct : Ptr) (len tau : Nat) (c ss : Ptr) : List (Reg × Arg) :=
  [(.x0, .ptr ct), (.x1, .imm len), (.x2, .imm tau), (.x3, .ptr c), (.x4, .ptr ss)]

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {ct c ss : Ptr} {len : Nat}
  (hc : VG.Proof.MlDsa.AArch64.ballChk rbs wbs ct len c ss = true)
include L hc

theorem ball_cov : Covers ([⟨VG.Proof.MlDsa.AArch64.pa s ct, len⟩] ++ [⟨VG.Proof.MlDsa.AArch64.pa s c, 1024⟩, ⟨VG.Proof.MlDsa.AArch64.pa s ss, 2048⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨VG.Proof.MlDsa.AArch64.pa s c, 1024⟩, ⟨VG.Proof.MlDsa.AArch64.pa s ss, 2048⟩] s.wr := by
  simp only [VG.Proof.MlDsa.AArch64.ballChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, _, c4, _, _, c7, c8⟩ := hc
  exact ⟨Covers.append_left (L.cR c4) (Covers.right (Covers.cons (L.cW c7) (L.cW c8))), Covers.cons (L.cW c7) (L.cW c8)⟩

theorem ball_pre {tau : Nat} (ht : (len, tau) ∈ ballParams) {s1 : State}
    (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.ballArgs ct len tau c ss) s s1) :
    (sampleInBallContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.AArch64.pa s ct, len⟩] [⟨VG.Proof.MlDsa.AArch64.pa s c, 1024⟩, ⟨VG.Proof.MlDsa.AArch64.pa s ss, 2048⟩]) := by
  have hl : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at ht; omega
  simp only [VG.Proof.MlDsa.AArch64.ballChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [sampleInBallContract, sampleInBallSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.sp h1]
  simp only [Arg.val]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), VG.Proof.MlDsa.AArch64.imm32 hl.2]
  cpre L
  exact ht

end

theorem ball_args {B : List Reg} {bs : List (Reg × Nat)} (L : VG.Proof.MlDsa.AArch64.LayIn B bs) {ct c ss : Ptr} (len tau : Nat) (c4 : VG.CallLay.inB bs ct len = true)
    (c5 : VG.CallLay.inB bs c 1024 = true) (c6 : VG.CallLay.inB bs ss 2048 = true) :
    ∀ x ∈ VG.Proof.MlDsa.AArch64.ballArgs ct len tau c ss, x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.AArch64.argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c4), by decide⟩, ⟨trivial, by decide⟩, ⟨trivial, by decide⟩,
    ⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c5), by decide⟩, ⟨VG.Proof.MlDsa.AArch64.ptr_ok (VG.Proof.MlDsa.AArch64.ptr_kept L c6), by decide⟩⟩

theorem ballAt_ok {S : Nat} (hS : S < 2 ^ 64) {nm : String} {cd : Prog isa} (C : VG.Proof.MlDsa.AArch64.CalleeOk S cd (sampleInBallContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.AArch64.Lay S rbs wbs s) {ct c ss : Ptr} {len : Nat}
    (hc : VG.Proof.MlDsa.AArch64.ballChk rbs wbs ct len c ss = true) {tau : Nat} (ht : (len, tau) ∈ ballParams) :
    WP isa (callAt nm cd (VG.Proof.MlDsa.AArch64.ballArgs ct len tau c ss)) s fun s' => VG.Proof.MlDsa.AArch64.PPostB S s s' [(c, 1024), (ss, 2048)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → Reduced s'.mem (VG.Proof.MlDsa.AArch64.pa s c)) ∧
      Outcome (fun b => (sampleInBall tau b.ball (bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s ct) len)).map toRq)
        ((s'.gpr .x0).setWidth 32) (polyAt s'.mem (VG.Proof.MlDsa.AArch64.pa s c)) := by
  have hl : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at ht; omega
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.ballChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (VG.Proof.MlDsa.AArch64.callAt_ok hS C (VG.Proof.MlDsa.AArch64.ball_args L.ok len tau c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.AArch64.ball_pre L hc ht h1) (VG.Proof.MlDsa.AArch64.ball_cov L hc).1 (VG.Proof.MlDsa.AArch64.ball_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [sampleInBallContract, sampleInBallSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.mem h1] at hq
  simp only [Arg.val] at hq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), VG.Proof.MlDsa.AArch64.imm32 hl.2] at hq
  exact hq

theorem ballAt_tr {S : Nat} {nm : String} {cd : Prog isa} (C : VG.Proof.MlDsa.AArch64.CalleeOk S cd (sampleInBallContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {B : List Reg} (hB : VG.Proof.MlDsa.AArch64.LayIn B (rbs ++ wbs)) {ct c ss : Ptr} {len : Nat}
    (hc : VG.Proof.MlDsa.AArch64.ballChk rbs wbs ct len c ss = true) {tau : Nat} (ht : (len, tau) ∈ ballParams) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.AArch64.Lay S rbs wbs x ∧ VG.Proof.MlDsa.AArch64.Lay S rbs wbs y ∧
      bytesAt x.mem (VG.Proof.MlDsa.AArch64.pa x ct) len = bytesAt y.mem (VG.Proof.MlDsa.AArch64.pa y ct) len ∧ VG.Proof.MlDsa.AArch64.SameIn B x y) :
    RelCT isa Q (callAt nm cd (VG.Proof.MlDsa.AArch64.ballArgs ct len tau c ss)) fun _ _ => True := by
  have hl : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at ht; omega
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.ballChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : ct.1 ∈ B ∧ c.1 ∈ B ∧ ss.1 ∈ B := ⟨VG.Proof.MlDsa.AArch64.ptr_bs hB c4, VG.Proof.MlDsa.AArch64.ptr_bs hB c5, VG.Proof.MlDsa.AArch64.ptr_bs hB c6⟩
  refine VG.Proof.MlDsa.AArch64.callAt_tr C (VG.Proof.MlDsa.AArch64.ball_args hB len tau c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.ball_pre Lx hc ht h1, ?_, ?_, (VG.Proof.MlDsa.AArch64.ball_cov Lx hc).1, (VG.Proof.MlDsa.AArch64.ball_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact VG.Proof.MlDsa.AArch64.ball_pre Ly hc ht h2
  · sig_pub [sampleInBallContract, sampleInBallSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2,
      Args.r3 h2, Args.r4 h2, Args.sp h1, Args.sp h2, Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, trivial, trivial, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.ball_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.ball_cov Ly hc).2

end VG.Proof.MlDsa.AArch64

end
