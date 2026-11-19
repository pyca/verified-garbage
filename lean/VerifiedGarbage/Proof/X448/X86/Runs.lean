module

import VerifiedGarbage.Proof.X448.X86.Square
import VerifiedGarbage.Proof.X448.X86.FnLit
import VerifiedGarbage.Proof.X448.X86.Counters
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X448.X86.Square
meta import VerifiedGarbage.Proof.X448.X86.FnLit
meta import VerifiedGarbage.Proof.X448.X86.Counters
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Impl.X25519.X86
meta import VerifiedGarbage.Impl.X25519.X86
public import VerifiedGarbage.Proof.X448.X86.FnVerified
public import VerifiedGarbage.Proof.X448.X86.Ops
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.X86.TaintErase
meta import VerifiedGarbage.Proof.X448.X86.FnVerified
meta import VerifiedGarbage.Proof.X448.X86.Ops
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.TaintErase

/-! ### `X448.X86.CallCT`, which this module and modules that import it used -/

section

/-!
# X448 on x86 (32-bit): constant time of the field-function calls

The taint analysis forgets the arguments a field function reads from its
caller's frame once the function stores secrets through its row pointer (it
cannot place that pointer in a region), so the code that calls the field
functions is related run by run (`RelCT`) instead: a call leaks the same in
two runs whose public data agree, by the function's own constant time
(`Verified`'s, `FnVerified.lean`; `RelCT.callWith`), and what each run
knows of the other's state is carried in the relation.

`RF base` relates two runs with the working space at `base`, the call stack
apart from it and bounded slots (`FInv`) in each, that agree on `esp`: a
field operation (`fieldOp_rel`), and a list of them (`ops_rel`), leaks the
same and keeps `RF`.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- What a run of the field arithmetic knows: the working space at `base`,
the stack its calls use apart from it, and every slot bounded. -/
structure FInv (base : Addr) (s : State) : Prop where
  scr : Scr s base
  ctx : CallCtx s base
  bounded : BoundedEnv s.mem base

/-- Two runs of the field arithmetic whose stack pointers agree. -/
def RF (base : Addr) (s₁ s₂ : State) : Prop :=
  FInv base s₁ ∧ FInv base s₂ ∧ s₁.gpr .esp = s₂.gpr .esp

theorem edi_eq {base : Addr} {s₁ s₂ : State} (h₁ : Scr s₁ base) (h₂ : Scr s₂ base) :
    s₁.gpr .edi = s₂.gpr .edi :=
  BitVec.setWidth_32_64_inj.mp (h₁.edi.trans h₂.edi.symm)

theorem RF.agree {base : Addr} {s₁ s₂ : State} (h : RF base s₁ s₂) :
    VG.X86.Taint.Agree (τr [.esp, .edi]) s₁ s₂ := by
  refine agree_regs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.2.2
  · exact edi_eq h.1.scr h.2.1.scr

/-- Code that keeps `Keep` and the bounds keeps `RF`. -/
theorem RF.keep {base : Addr} {c : Prog isa} (htr : RelCT isa (RF base) c fun _ _ => True)
    (hw : ∀ s, FInv base s → WP isa c s fun t => Keep base s t ∧ BoundedEnv t.mem base) :
    RelCT isa (RF base) c (RF base) := by
  refine (htr.wpDep (F := fun (s t : State) => Keep base s t ∧ BoundedEnv t.mem base)
    fun s₁ s₂ h => ⟨hw s₁ h.1, hw s₂ h.2.1⟩).mono (fun _ _ h => h) ?_
  rintro t₁ t₂ ⟨-, s₁, s₂, ⟨f₁, f₂, e⟩, ⟨k₁, b₁⟩, ⟨k₂, b₂⟩⟩
  exact ⟨⟨k₁.scr f₁.scr, k₁.ctx f₁.ctx, b₁⟩, ⟨k₂.scr f₂.scr, k₂.ctx f₂.ctx, b₂⟩,
    by rw [k₁.regs.1 _ (by decide), k₂.regs.1 _ (by decide), e]⟩

/-! ## The callee's precondition at a call -/

section
variable {rs : List Reg} {s : State} {base : Addr}

/-- The state a field function is entered in, from `s` with the arguments
`rs` pushed: its arguments readable, the working space writable. -/
abbrev entryOf (rs : List Reg) (s : State) (base : Addr) : State :=
  (pushed rs s).callEntry.withRegions [below (s.gpr .esp) (4 * rs.length)] [⟨base, 8192⟩]

theorem entryOf_arg (hrs : .esp ∉ rs) (hl : rs.length ≤ 4) (hc : CallCtx s base) {i : Nat}
    (hi : i < rs.length) : arg (entryOf rs s base) i = s.gpr rs[rs.length - 1 - i] :=
  callEntry_arg (by have := hc.sp; omega_using [hl, this]) hrs hi

theorem entryOf_fnPre (hl : rs.length ≤ 4) (hs : Scr s base) (hc : CallCtx s base)
    (hw : arg (entryOf rs s base) 0 = s.gpr .edi) :
    fnPre (4 * rs.length) (entryOf rs s base) := by
  have hE := hc.sp
  have ws : wsOf (entryOf rs s base) = base := by rw [wsOf, hw]; exact hs.edi
  have esp : (entryOf rs s base).gpr .esp = s.gpr .esp - BitVec.ofNat 32 (4 * rs.length + 4) :=
    callEntry_esp' rs s
  have a0 : argAddr (entryOf rs s base) 0 = (s.gpr .esp - BitVec.ofNat 32 (4 * rs.length)).setWidth 64 :=
    callEntry_argAddr0 rs s
  refine ⟨?_, by rw [a0]; rfl, by rw [ws]; rfl, ?_, ?_, ?_⟩
  · rw [esp, sub_toNat (by omega_using [hl, hE])]; have := (s.gpr .esp).isLt; omega_using [hl]
  · rw [ws, a0]
    exact hc.sep.sub_right (below_sub (by omega_using [hl]) hE)
  · rw [ws, esp]
    refine (hc.sep.sub_right ?_).symm
    refine fun x hx => below_inner (sp := s.gpr .esp) (a := 4) (k := 4 * rs.length) (b := 20) (by omega_using [hl]) hE x ?_
    have e : s.gpr .esp - BitVec.ofNat 32 (4 * rs.length + 4) =
        s.gpr .esp - BitVec.ofNat 32 (4 * rs.length) - BitVec.ofNat 32 4 := by
      rw [BitVec.sub_sub, BitVec.ofNat_add]
    simp only [below]
    rw [← e]; exact hx
  · rw [hw]; exact hs.nowrap

theorem entryOf_mem (hrs : .esp ∉ rs) (hl : rs.length ≤ 4) (hc : CallCtx s base) :
    WsEq base s.mem (entryOf rs s base).mem :=
  WsEq.of_frame hc ((callEntry_frame (by have := hc.sp; omega_using [hl, this]) hrs).sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨callStk s, List.mem_singleton_self _, below_sub (by omega_using [hl]) hc.sp⟩)

theorem entryOf_cov (hs : Scr s base) :
    Covers ([below (s.gpr .esp) (4 * rs.length)] ++ [⟨base, 8192⟩])
      (s.rd ++ below (s.gpr .esp) (4 * rs.length) :: s.wr) := Covers.of_mem fun r hr => by
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ List.mem_cons_self
  · rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hs.wr)

theorem entryOf_covw (hs : Scr s base) :
    Covers [⟨base, 8192⟩] (below (s.gpr .esp) (4 * rs.length) :: s.wr) :=
  Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ hs.wr

end

theorem fits_slot {o : Nat} (h : Slot o) : Proof.X448.Field16.Fits (BitVec.ofNat 32 o) := by
  have : o + 112 ≤ 3584 := h
  show (BitVec.ofNat 32 o).toNat + 112 ≤ 3584
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [this])]; exact this

theorem limbs_slot {m : Mem} {base : Addr} {a : Nat} (h : Slot a) (hb : Bounded m base a) :
    Proof.X448.Field16.Limbs m base (BitVec.ofNat 32 a) := by
  have : a + 112 ≤ 3584 := h
  rw [limbs_spec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [this])]; exact hb

/-- A binary function's precondition, at its call after the offsets' `mov`s. -/
theorem callPre_bin {r : Nat → Nat → Nat → Prop} {s : State} {base : Addr} (hs : Scr s base)
    (hc : CallCtx s base) {o a b : Nat} (ho : Slot o) (ha : Slot a) (hb : Slot b)
    (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) (heax : s.gpr .eax = BitVec.ofNat 32 o)
    (hecx : s.gpr .ecx = BitVec.ofNat 32 a) (hedx : s.gpr .edx = BitVec.ofNat 32 b) :
    CallPre (binX86 r) [.edx, .ecx, .eax, .edi] [below (s.gpr .esp) (4 * [Reg.edx, .ecx, .eax, .edi].length)]
      [⟨base, 8192⟩] s := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  have av := fun i (hi : i < 4) => entryOf_arg (rs := [.edx, .ecx, .eax, .edi]) (base := base) (by decide)
    (by decide) hc hi
  have w : WsEq base s.mem (entryOf [.edx, .ecx, .eax, .edi] s base).mem := entryOf_mem (by decide) (by decide) hc
  have hw : wsOf (entryOf [.edx, .ecx, .eax, .edi] s base) = base := by
    rw [wsOf, av 0 (by decide)]; exact hs.edi
  have a1 : arg (entryOf [.edx, .ecx, .eax, .edi] s base) 1 = BitVec.ofNat 32 o := (av 1 (by decide)).trans heax
  have a2 : arg (entryOf [.edx, .ecx, .eax, .edi] s base) 2 = BitVec.ofNat 32 a := (av 2 (by decide)).trans hecx
  have a3 : arg (entryOf [.edx, .ecx, .eax, .edi] s base) 3 = BitVec.ofNat 32 b := (av 3 (by decide)).trans hedx
  have pre : (binX86 r).pre (entryOf [.edx, .ecx, .eax, .edi] s base) := by
    refine ⟨entryOf_fnPre (by decide) hs hc (av 0 (by decide)), ?_, ?_, ?_, ?_, ?_⟩
    · rw [a1]; exact fits_slot ho
    · rw [a2]; exact fits_slot ha
    · rw [a3]; exact fits_slot hb
    · rw [hw, a2]; exact limbs_slot ha (w.bounded (by omega_using [ha']) ab)
    · rw [hw, a3]; exact limbs_slot hb (w.bounded (by omega_using [hb']) bb)
  exact ⟨pre, entryOf_cov hs, entryOf_covw hs⟩

/-- A unary field function's precondition, at its call after the offsets' `mov`s. -/
theorem callPre_un {r : Nat → Nat → Prop} {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base)
    {o a : Nat} (ho : Slot o) (ha : Slot a) (ab : Bounded s.mem base a)
    (heax : s.gpr .eax = BitVec.ofNat 32 o) (hecx : s.gpr .ecx = BitVec.ofNat 32 a) :
    CallPre (unX86 r) [.ecx, .eax, .edi] [below (s.gpr .esp) (4 * [Reg.ecx, .eax, .edi].length)]
      [⟨base, 8192⟩] s := by
  have ha' : a + 112 ≤ 3584 := ha
  have av := fun i (hi : i < 3) => entryOf_arg (rs := [.ecx, .eax, .edi]) (base := base) (by decide)
    (by decide) hc hi
  have w : WsEq base s.mem (entryOf [.ecx, .eax, .edi] s base).mem := entryOf_mem (by decide) (by decide) hc
  have hw : wsOf (entryOf [.ecx, .eax, .edi] s base) = base := by
    rw [wsOf, av 0 (by decide)]; exact hs.edi
  have a1 : arg (entryOf [.ecx, .eax, .edi] s base) 1 = BitVec.ofNat 32 o := (av 1 (by decide)).trans heax
  have a2 : arg (entryOf [.ecx, .eax, .edi] s base) 2 = BitVec.ofNat 32 a := (av 2 (by decide)).trans hecx
  have pre : (unX86 r).pre (entryOf [.ecx, .eax, .edi] s base) := by
    refine ⟨entryOf_fnPre (by decide) hs hc (av 0 (by decide)), ?_, ?_, ?_⟩
    · rw [a1]; exact fits_slot ho
    · rw [a2]; exact fits_slot ha
    · rw [hw, a2]; exact limbs_slot ha (w.bounded (by omega_using [ha']) ab)
  exact ⟨pre, entryOf_cov hs, entryOf_covw hs⟩

/-! ## Calls -/

/-- Before a call: the working space, the call stack apart from it, the
slots bounded, `esp` at `sp` in both runs, `edi` the same, and the
offsets `v` in `eax`, `ecx` and `edx`. -/
def MovRel (base : Addr) (sp : BitVec 32) (v : List (Reg × Nat)) (t₁ t₂ : State) : Prop :=
  FInv base t₁ ∧ FInv base t₂ ∧ t₁.gpr .esp = sp ∧ t₂.gpr .esp = sp ∧
    (∀ p ∈ v, t₁.gpr p.1 = BitVec.ofNat 32 p.2 ∧ t₂.gpr p.1 = BitVec.ofNat 32 p.2)

/-- The `mov`s of offsets before a call. -/
theorem movs_rel {base : Addr} (sp : BitVec 32) (v : List (Reg × Nat))
    (hv : ∀ p ∈ v, p.1 ≠ .esp ∧ p.1 ≠ .edi)
    (hc : (taint.check (τr [.esp, .edi]) (.block (v.map fun p => .mov p.1 (.imm (BitVec.ofNat 32 p.2))))
      (Taint.hintOf taint (τr [.esp, .edi])
        (.block (v.map fun p => .mov p.1 (.imm (BitVec.ofNat 32 p.2)))))).isSome = true)
    (hw : ∀ s, WP isa (.block (v.map fun p => .mov p.1 (.imm (BitVec.ofNat 32 p.2)))) s fun t =>
      Keeps (v.map Prod.fst) s t ∧ t.mem = s.mem ∧ ∀ p ∈ v, t.gpr p.1 = BitVec.ofNat 32 p.2) :
    RelCT isa (fun s₁ s₂ => RF base s₁ s₂ ∧ s₁.gpr .esp = sp)
      (.block (v.map fun p => .mov p.1 (.imm (BitVec.ofNat 32 p.2)))) (MovRel base sp v) := by
  refine ((RelCT.taint (A := taint) _ (fun _ _ h => h.1.agree) hc).wpDep
    (F := fun (s t : State) => Keeps (v.map Prod.fst) s t ∧ t.mem = s.mem ∧ ∀ p ∈ v, t.gpr p.1 = BitVec.ofNat 32 p.2)
    fun s₁ s₂ _ => ⟨hw s₁, hw s₂⟩).mono (fun _ _ h => h) ?_
  rintro t₁ t₂ ⟨-, s₁, s₂, ⟨⟨f₁, f₂, e⟩, sp₁⟩, ⟨k₁, m₁, v₁⟩, ⟨k₂, m₂, v₂⟩⟩
  have ne : ∀ r ∈ [Reg.esp, .edi], r ∉ v.map Prod.fst := by
    intro r hr hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    have := hv p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h <;> simp_all
  have fi : ∀ {s t : State}, FInv base s → Keeps (v.map Prod.fst) s t → t.mem = s.mem → FInv base t :=
    fun f k m => ⟨f.scr.of_keeps k (ne _ (by simp)), f.ctx.keep (k.1 _ (ne _ (by simp))), m ▸ f.bounded⟩
  exact ⟨fi f₁ k₁ m₁, fi f₂ k₂ m₂, by rw [k₁.1 _ (ne _ (by simp)), sp₁],
    by rw [k₂.1 _ (ne _ (by simp)), ← e, sp₁], fun p hp => ⟨v₁ p hp, v₂ p hp⟩⟩

theorem movs_wp (v : List (Reg × Nat)) (hd : v.map Prod.fst |>.Nodup) (s : State) :
    WP isa (.block (v.map fun p => .mov p.1 (.imm (BitVec.ofNat 32 p.2)))) s fun t =>
      Keeps (v.map Prod.fst) s t ∧ t.mem = s.mem ∧ ∀ p ∈ v, t.gpr p.1 = BitVec.ofNat 32 p.2 := by
  induction v generalizing s with
  | nil => exact WP.block_nil ⟨Keeps.refl _ _, rfl, fun _ h => (List.not_mem_nil h).elim⟩
  | cons p v ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hd
    refine wp_mov rfl fun t ht => WP.mono (ih hd.2 t) fun u ⟨uk, um, uv⟩ => ⟨?_, um.trans ht.mem, ?_⟩
    · exact (ht.rest (List.mem_cons_self)).trans (uk.mono fun r hr => List.mem_cons_of_mem _ hr)
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rw [uk.1 _ fun h => hd.1 (by obtain ⟨q', hq', e⟩ := List.mem_map.mp h; exact ⟨q', hq', e⟩)]
        exact ht.gpr
      · exact uv q hq

/-- The trace of a call of a binary field function, from `RF`. -/
theorem call3_tr {name : String} {body : Prog isa} {r : Nat → Nat → Nat → Prop}
    (hv : ∀ s, (binX86 r).pre s → ∃ t s', Exec isa body s t s' ∧ abiPreserved s s' ∧ (binX86 r).post s s')
    (hct : ConstantTime isa (binX86 r).pre (binX86 r).pub body) {base : Addr} (o a b : Index) :
    RelCT isa (RF base) (call3 name body (slot o.val) (slot a.val) (slot b.val)) fun _ _ => True := by
  have pre : ∀ sp, RelCT isa (fun s₁ s₂ => RF base s₁ s₂ ∧ s₁.gpr .esp = sp)
      (call3 name body (slot o.val) (slot a.val) (slot b.val)) fun _ _ => True := by
    intro sp
    let v : List (Reg × Nat) := [(.eax, slot o.val), (.ecx, slot a.val), (.edx, slot b.val)]
    refine RelCT.seq (movs_rel (v := v) sp (by
        intro p hp; simp only [v, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> exact ⟨nofun, nofun⟩) (by rfl)
      (movs_wp v (by simp [v])))
      (RelCT.callWith hv hct [below sp (4 * [Reg.edx, .ecx, .eax, .edi].length)] [⟨base, 8192⟩] ?_)
    rintro t₁ t₂ ⟨f₁, f₂, e₁, e₂, hv'⟩
    have g := fun (p : Reg × Nat) (hp : p ∈ v) => hv' p hp
    have ga := g _ (List.mem_cons_self)
    have gc := g _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have gd := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    refine ⟨?_, ?_, e₁.trans e₂.symm, ?_⟩
    · rw [← e₁]; exact callPre_bin f₁.scr f₁.ctx (slot_bound o) (slot_bound a) (slot_bound b)
        (f₁.bounded a) (f₁.bounded b) ga.1 gc.1 gd.1
    · rw [← e₂]; exact callPre_bin f₂.scr f₂.ctx (slot_bound o) (slot_bound a) (slot_bound b)
        (f₂.bounded a) (f₂.bounded b) ga.2 gc.2 gd.2
    · have hr : ∀ q ∈ [Reg.edx, .ecx, .eax, .edi], t₁.gpr q = t₂.gpr q := by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · rw [gd.1, gd.2]
        · rw [gc.1, gc.2]
        · rw [ga.1, ga.2]
        · exact edi_eq f₁.scr f₂.scr
      have fit : 4 * [Reg.edx, .ecx, .eax, .edi].length + 4 ≤ (t₁.gpr .esp).toNat := f₁.ctx.sp
      have ae := fun i (hi : i < 4) => callEntry_arg_eq (by decide) fit (e₁.trans e₂.symm) hr hi
      exact ⟨by rw [State.withRegions_gpr, State.withRegions_gpr, callEntry_esp', callEntry_esp', e₁, e₂],
        ae 0 (by decide), ae 1 (by decide), ae 2 (by decide), ae 3 (by decide)⟩
  exact (RelCT.exists_ fun sp => pre sp).mono (fun s₁ s₂ h => ⟨_, h, rfl⟩) fun _ _ h => h

/-- The trace of a call of a unary field function, from `RF`. -/
theorem call2_tr {name : String} {body : Prog isa} {r : Nat → Nat → Prop}
    (hv : ∀ s, (unX86 r).pre s → ∃ t s', Exec isa body s t s' ∧ abiPreserved s s' ∧ (unX86 r).post s s')
    (hct : ConstantTime isa (unX86 r).pre (unX86 r).pub body) {base : Addr} (o a : Index) :
    RelCT isa (RF base) (call2 name body (slot o.val) (slot a.val)) fun _ _ => True := by
  have pre : ∀ sp, RelCT isa (fun s₁ s₂ => RF base s₁ s₂ ∧ s₁.gpr .esp = sp)
      (call2 name body (slot o.val) (slot a.val)) fun _ _ => True := by
    intro sp
    let v : List (Reg × Nat) := [(.eax, slot o.val), (.ecx, slot a.val)]
    refine RelCT.seq (movs_rel (v := v) sp (by
        intro p hp; simp only [v, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> exact ⟨nofun, nofun⟩) (by rfl)
      (movs_wp v (by simp [v])))
      (RelCT.callWith hv hct [below sp (4 * [Reg.ecx, .eax, .edi].length)] [⟨base, 8192⟩] ?_)
    rintro t₁ t₂ ⟨f₁, f₂, e₁, e₂, hv'⟩
    have ga := hv' _ (List.mem_cons_self)
    have gc := hv' _ (List.mem_cons_of_mem _ List.mem_cons_self)
    refine ⟨?_, ?_, e₁.trans e₂.symm, ?_⟩
    · rw [← e₁]; exact callPre_un f₁.scr f₁.ctx (slot_bound o) (slot_bound a) (f₁.bounded a) ga.1 gc.1
    · rw [← e₂]; exact callPre_un f₂.scr f₂.ctx (slot_bound o) (slot_bound a) (f₂.bounded a) ga.2 gc.2
    · have hr : ∀ q ∈ [Reg.ecx, .eax, .edi], t₁.gpr q = t₂.gpr q := by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · rw [gc.1, gc.2]
        · rw [ga.1, ga.2]
        · exact edi_eq f₁.scr f₂.scr
      have fit : 4 * [Reg.ecx, .eax, .edi].length + 4 ≤ (t₁.gpr .esp).toNat := by
        have := f₁.ctx.sp; simp; omega_using [this]
      have ae := fun i (hi : i < 3) => callEntry_arg_eq (by decide) fit (e₁.trans e₂.symm) hr hi
      exact ⟨by rw [State.withRegions_gpr, State.withRegions_gpr, callEntry_esp', callEntry_esp', e₁, e₂],
        ae 0 (by decide), ae 1 (by decide), ae 2 (by decide)⟩
  exact (RelCT.exists_ fun sp => pre sp).mono (fun s₁ s₂ h => ⟨_, h, rfl⟩) fun _ _ h => h

/-! ## Field operations -/

/-- A copy between slots, whose code is the same but for its displacements. -/
theorem copy_check (o a : Nat) :
    (taint.check (τr [.esp, .edi]) (.block (copy o a)) (.block [] 256)).isSome = true := by
  have e : Code.erase (.block (copy o a)) = Code.erase (.block (copy 0 0)) := by
    simp only [Code.erase, KList.map_eq, copy, List.map_flatMap]; rfl
  have h := Taint.check_erase (.block (copy o a)) (τr [.esp, .edi]) (.block [] 256) rfl rfl
  rw [e] at h
  have h0 : (taint.check (τr [.esp, .edi]) (Code.erase (.block (copy 0 0))) (.block [] 256)).isSome =
    true := by decide +kernel
  exact (congrArg Option.isSome h).symm.trans h0

theorem fieldOp_rel {base : Addr} (op : FieldOp) : RelCT isa (RF base) op.impl.code (RF base) := by
  refine RF.keep ?_ fun s h => WP.mono (fieldOp_ok h.scr h.ctx h.bounded op) fun _ ⟨k, b, _⟩ => ⟨k, b⟩
  cases op with
  | mul o a b =>
    change RelCT isa (RF base) (mulCall (slot o.val) (slot a.val) (slot b.val)) _
    unfold mulCall
    split
    · exact call2_tr sqrFn_correct (sqrFn_ct un_agree) o a
    · exact call3_tr mulFn_correct (mulFn_ct bin_agree) o a b
  | add o a b => exact call3_tr addFn_correct (addFn_ct bin_agree) o a b
  | sub o a b => exact call3_tr subFn_correct (subFn_ct bin_agree) o a b
  | mulSmall o a => exact call2_tr mulA24Fn_correct (mulA24Fn_ct un_agree) o a
  | copy o a =>
    exact RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ h => h.agree)
      (copy_check (slot o.val) (slot a.val))

theorem ops_rel {base : Addr} (xs : List FieldOp) :
    RelCT isa (RF base) (ops (xs.map FieldOp.impl)) (RF base) := by
  induction xs with
  | nil => exact RelCT.nil fun _ _ h => h
  | cons op rest ih => exact RelCT.seq (fieldOp_rel op) ih

end VG.Proof.X448.X86

end

end

/-!
# Field arithmetic on x86 (32-bit): two runs, piece by piece

The constant time of code calling the field functions is proven run by run
(`RelCT`): each piece's trace agrees in two runs from what each run's
correctness proof says of its own state. `Runs P₀ F` relates two runs from
entry states that `P₀` relates (the contract's precondition in both and its
public data), each in a state `F` says of its own run; `Runs.then` and
`Runs.step` relate a piece whose trace agrees, by determinism, with what
each run's correctness says of its result.

`FE bs σ` is what field arithmetic keeps in a run from the entry state `σ`
with the working space at `bs σ`: `FInv`, `esp` and the writable regions,
and the memory but the writable regions and the 20 bytes of stack below the
return address, where the calls of the field functions put their arguments.
Field operations (`ops_tr`) leak the same in two runs in it.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- Two runs from entry states `P₀` relates, each in a state `F` says of its own run. -/
def Runs (P₀ F : State → State → Prop) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂, P₀ σ₁ σ₂ ∧ F σ₁ s₁ ∧ F σ₂ s₂

/-- Code whose traces agree in runs `P` relates (which `Runs P₀ F` relates
too), with what each run's correctness says of it. -/
theorem Runs.then {P₀ F G P R Q : State → State → Prop} {c : Prog isa}
    (hP : ∀ s₁ s₂, P s₁ s₂ → Runs P₀ F s₁ s₂) (htr : RelCT isa P c R)
    (hw : ∀ σ s, F σ s → WP isa c s (G σ))
    (hq : ∀ σ₁ σ₂ t₁ t₂, P₀ σ₁ σ₂ → R t₁ t₂ → G σ₁ t₁ → G σ₂ t₂ → Q t₁ t₂) :
    RelCT isa P c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hr⟩ := htr _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨σ₁, σ₂, hP', f₁, f₂⟩ := hP _ _ hp
  obtain ⟨_, u₁, x₁, g₁⟩ := hw _ _ f₁
  obtain ⟨_, u₂, x₂, g₂⟩ := hw _ _ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, hq _ _ _ _ hP' hr g₁ g₂⟩

theorem Runs.step {P₀ F G R : State → State → Prop} {c : Prog isa}
    (htr : RelCT isa (Runs P₀ F) c R) (hw : ∀ σ s, F σ s → WP isa c s (G σ)) :
    RelCT isa (Runs P₀ F) c (Runs P₀ G) :=
  Runs.then (fun _ _ h => h) htr hw fun _ _ _ _ hP _ g₁ g₂ => ⟨_, _, hP, g₁, g₂⟩

/-- What field arithmetic keeps in a run from the entry state `σ`. -/
structure FE (bs : State → Addr) (σ t : State) : Prop where
  fin : FInv (bs σ) t
  sp : t.gpr .esp = σ.gpr .esp
  wr : t.wr = σ.wr
  frame : Frame (σ.wr ++ [below (σ.gpr .esp) 20]) σ.mem t.mem

/-- What the calls of the field functions need of a run from the entry state `σ`. -/
def FS (bs : State → Addr) (σ t : State) : Prop := FInv (bs σ) t ∧ t.gpr .esp = σ.gpr .esp

theorem FE.fs {bs : State → Addr} {σ t : State} (h : FE bs σ t) : FS bs σ t := ⟨h.fin, h.sp⟩

theorem FS.rf {bs : State → Addr} {σ₁ σ₂ t₁ t₂ : State} (hb : bs σ₁ = bs σ₂)
    (hs : σ₁.gpr .esp = σ₂.gpr .esp) (h₁ : FS bs σ₁ t₁) (h₂ : FS bs σ₂ t₂) : RF (bs σ₁) t₁ t₂ :=
  ⟨h₁.1, hb ▸ h₂.1, h₁.2.trans (hs.trans h₂.2.symm)⟩

/-- Code that keeps the field arithmetic's invariant, `esp` and the writable
regions, and uses at most 20 bytes of stack, keeps `FE`. -/
theorem FE.wp {bs : State → Addr} {σ s : State} (h : FE bs σ s) {c : Prog isa} (hc : NoSp c)
    (hu : stackUse c ≤ 20) {Q : State → Prop}
    (hw : WP isa c s fun t => FInv (bs σ) t ∧ t.gpr .esp = s.gpr .esp ∧ t.wr = s.wr ∧ Q t) :
    WP isa c s fun t => FE bs σ t ∧ Q t := by
  have room : 20 ≤ (σ.gpr .esp).toNat := h.sp ▸ h.fin.ctx.sp
  refine WP.mono (WP.withFrame hc (by rw [h.sp]; exact Nat.le_trans hu room) hw)
    fun t ⟨⟨f, sp, wr, q⟩, fr⟩ => ⟨⟨f, sp.trans h.sp, wr.trans h.wr, h.frame.trans ?_⟩, q⟩
  rw [h.sp, h.wr] at fr
  exact Frame.below_mono fr hu room

theorem call3_nosp {name : String} {body : Prog isa} (hb : NoSp body) (o a b : Nat) :
    NoSp (call3 name body o a b) := by
  intro i hi
  simp only [call3, instrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl | rfl) | (rfl | hi) | rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hb i hi
  · rfl

theorem call2_nosp {name : String} {body : Prog isa} (hb : NoSp body) (o a : Nat) :
    NoSp (call2 name body o a) := by
  intro i hi
  simp only [call2, instrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl) | (rfl | hi) | rfl
  · rfl
  · rfl
  · rfl
  · exact hb i hi
  · rfl

theorem op_nosp (op : FieldOp) : NoSp op.impl.code := by
  cases op with
  | mul o a b =>
    change NoSp (mulCall (slot o.val) (slot a.val) (slot b.val))
    unfold mulCall
    split
    · exact call2_nosp (NoSp.of_all (by lit_decide)) _ _
    · exact call3_nosp (NoSp.of_all (by lit_decide)) _ _ _
  | add o a b => exact call3_nosp (NoSp.of_all (by lit_decide)) _ _ _
  | sub o a b => exact call3_nosp (NoSp.of_all (by lit_decide)) _ _ _
  | mulSmall o a => exact call2_nosp (NoSp.of_all (by lit_decide)) _ _
  | copy o a =>
    intro i hi
    simp only [FieldOp.impl, Op.code, instrs, copy, List.mem_flatMap, List.mem_range] at hi
    obtain ⟨j, -, hj⟩ := hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> rfl

theorem op_stack (op : FieldOp) : stackUse op.impl.code ≤ 20 := by
  cases op with
  | mul o a b =>
    change stackUse (mulCall (slot o.val) (slot a.val) (slot b.val)) ≤ 20
    unfold mulCall
    split <;> exact Nat.le_of_ble_eq_true rfl
  | _ => exact Nat.le_of_ble_eq_true rfl

theorem ops_nosp (xs : List FieldOp) : NoSp (ops (xs.map FieldOp.impl)) := by
  induction xs with
  | nil => intro i hi; simp only [List.map_nil, ops, instrs, List.not_mem_nil] at hi
  | cons op xs ih =>
    intro i hi
    change i ∈ instrs op.impl.code ++ instrs (ops (xs.map FieldOp.impl)) at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact op_nosp op i hi
    · exact ih i hi

theorem ops_stack (xs : List FieldOp) : stackUse (ops (xs.map FieldOp.impl)) ≤ 20 := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons op xs ih => exact Nat.max_le.mpr ⟨op_stack op, ih⟩

/-- Field operations keep `FE`. -/
theorem ops_FE {bs : State → Addr} {σ s : State} (h : FE bs σ s) (xs : List FieldOp) :
    WP isa (ops (xs.map FieldOp.impl)) s fun t => FE bs σ t ∧ Keep (bs σ) s t ∧
      E t.mem (bs σ) = applyOps xs (E s.mem (bs σ)) :=
  h.wp (ops_nosp xs) (ops_stack xs) (WP.mono (ops_ok h.fin.scr h.fin.ctx h.fin.bounded xs)
    fun _ ⟨k, b, e⟩ => ⟨⟨k.scr h.fin.scr, k.ctx h.fin.ctx, b⟩, k.regs.1 _ (by decide), k.regs.2.2, k, e⟩)

/-- The traces of field operations agree in two runs in `FE`. -/
theorem ops_tr {P₀ F : State → State → Prop} {bs : State → Addr}
    (hP : ∀ σ₁ σ₂, P₀ σ₁ σ₂ → bs σ₁ = bs σ₂ ∧ σ₁.gpr .esp = σ₂.gpr .esp)
    (hF : ∀ σ s, F σ s → FS bs σ s) (xs : List FieldOp) :
    RelCT isa (Runs P₀ F) (ops (xs.map FieldOp.impl)) fun _ _ => True :=
  (RelCT.exists_ fun b => (ops_rel (base := b) xs).mono (fun _ _ h => h) fun _ _ _ => trivial).mono
    (fun _ _ ⟨_, _, hp, f₁, f₂⟩ => ⟨_, FS.rf (hP _ _ hp).1 (hP _ _ hp).2 (hF _ _ f₁) (hF _ _ f₂)⟩)
    fun _ _ h => h

/-! ## The inversion -/

theorem FInv.of_counter {base : Addr} {s t : State} (hf : FInv base s)
    (hg : ∀ r, r ≠ .esi → t.gpr r = s.gpr r) (hm : t.mem = s.mem) (hr : t.rd = s.rd)
    (hw : t.wr = s.wr) : FInv base t :=
  let k := counter_keep (base := base) hg hm hr hw
  ⟨k.scr hf.scr, k.ctx hf.ctx, hm ▸ hf.bounded⟩

theorem eval_ne {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .ne s = some (!b) := by
  change s.zf.map (!·) = _
  rw [h]; rfl

/-- `m + 1` squarings left. -/
def SqRel (base : Addr) (m : Nat) (t₁ t₂ : State) : Prop :=
  FInv base t₁ ∧ FInv base t₂ ∧ t₁.gpr .esp = t₂.gpr .esp ∧
    t₁.gpr .esi = BitVec.ofNat 32 (m + 1) ∧ t₂.gpr .esi = BitVec.ofNat 32 (m + 1) ∧ m + 1 < 2 ^ 16

theorem SqRel.rf {base : Addr} {m : Nat} {t₁ t₂ : State} (h : SqRel base m t₁ t₂) : RF base t₁ t₂ :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem sqBody_ok {base : Addr} (o : Index) {m : Nat} (hm : m + 1 < 2 ^ 16) {s : State}
    (hf : FInv base s) (he : s.gpr .esi = BitVec.ofNat 32 (m + 1)) :
    WP isa (.seq (mulCall (slot o.val) (slot o.val) (slot o.val)) (.block [.alu .sub .esi (.imm 1)])) s
      fun t => FInv base t ∧ t.gpr .esp = s.gpr .esp ∧ t.gpr .esi = BitVec.ofNat 32 m ∧
        t.zf = some (decide (m = 0)) := by
  rw [WP.seq_iff]
  refine WP.mono (mulE hf.scr hf.ctx hf.bounded o o o) fun v ⟨kv, bv, _⟩ => ?_
  have cv : v.gpr .esi = BitVec.ofNat 32 (m + 1) := (kv.regs.1 _ (by decide)).trans he
  refine WP.mono (decCounter_ok (k := m) (by omega_using [hm]) cv) fun w ⟨cw, wg, wm, wr, ww, wz⟩ => ?_
  exact ⟨FInv.of_counter ⟨kv.scr hf.scr, kv.ctx hf.ctx, bv⟩ wg wm wr ww,
    (wg _ (by decide)).trans (kv.regs.1 _ (by decide)), cw, wz⟩

theorem sqn_rel (base : Addr) (o : Index) {n : Nat} (hn : 1 ≤ n) (hn' : n < 2 ^ 16) :
    RelCT isa (RF base) (Impl.X448.X86.sqn (slot o.val) n) (RF base) := by
  refine RelCT.seq (R := SqRel base (n - 1)) ?_ (RelCT.loop (M := isa) (SqRel base) ?_ (n - 1))
  · refine ((RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ h => h.agree) (hc := .block [] 256)
        (by rfl)).wpDep
      (F := fun (s t : State) => t.gpr .esi = BitVec.ofNat 32 n ∧ (∀ r, r ≠ .esi → t.gpr r = s.gpr r) ∧
        t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr)
      fun s₁ s₂ _ => ⟨setCounter_ok s₁ n hn', setCounter_ok s₂ n hn'⟩).mono (fun _ _ h => h) ?_
    rintro t₁ t₂ ⟨-, s₁, s₂, ⟨f₁, f₂, e⟩, ⟨c₁, g₁, m₁, r₁, w₁⟩, ⟨c₂, g₂, m₂, r₂, w₂⟩⟩
    have hn1 : n - 1 + 1 = n := by omega_using [hn]
    refine ⟨FInv.of_counter f₁ g₁ m₁ r₁ w₁, FInv.of_counter f₂ g₂ m₂ r₂ w₂, ?_, by rw [hn1]; exact c₁,
      by rw [hn1]; exact c₂, by omega_using [hn']⟩
    rw [g₁ _ (by decide), g₂ _ (by decide), e]
  · intro m
    have tr : RelCT isa (SqRel base m)
        (.seq (mulCall (slot o.val) (slot o.val) (slot o.val)) (.block [.alu .sub .esi (.imm 1)]))
        fun _ _ => True :=
      RelCT.seq ((fieldOp_rel (.mul o o o)).mono (fun _ _ h => h.rf) fun _ _ h => h)
        (RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ h => RF.agree h) (by taint_decide))
    refine (tr.wpDep (F := fun (s t : State) => FInv base t ∧ t.gpr .esp = s.gpr .esp ∧
        t.gpr .esi = BitVec.ofNat 32 m ∧ t.zf = some (decide (m = 0)))
      fun s₁ s₂ h => ⟨sqBody_ok o h.2.2.2.2.2 h.1 h.2.2.2.1, sqBody_ok o h.2.2.2.2.2 h.2.1 h.2.2.2.2.1⟩).mono
      (fun _ _ h => h) ?_
    rintro t₁ t₂ ⟨-, s₁, s₂, h, ⟨f₁, p₁, c₁, z₁⟩, ⟨f₂, p₂, c₂, z₂⟩⟩
    rw [eval_ne z₁, eval_ne z₂]
    refine ⟨rfl, fun hz => ⟨f₁, f₂, by rw [p₁, p₂, h.2.2.1]⟩, fun hz => ?_⟩
    have hm0 : m ≠ 0 := fun h0 => by simp [h0] at hz
    refine ⟨m - 1, by omega_using [hm0], f₁, f₂, by rw [p₁, p₂, h.2.2.1], ?_, ?_, by have := h.2.2.2.2.2; omega_using [this]⟩
    · rw [show m - 1 + 1 = m by omega_using [hm0]]; exact c₁
    · rw [show m - 1 + 1 = m by omega_using [hm0]]; exact c₂

theorem invert_rel (base : Addr) : RelCT isa (RF base) Impl.X448.X86.invert (RF base) := by
  have h : RelCT isa (RF base) _ (RF base) :=
    (ops_rel [.copy 14 2]).seq <|
    (sqn_rel base 14 (n := 1) (by decide) (by decide)).seq <|
    (ops_rel [.mul 14 14 2, .copy 15 14]).seq <|
    (sqn_rel base 15 (n := 2) (by decide) (by decide)).seq <|
    (ops_rel [.mul 15 15 14, .copy 16 15]).seq <|
    (sqn_rel base 16 (n := 4) (by decide) (by decide)).seq <|
    (ops_rel [.mul 16 16 15, .copy 17 16]).seq <|
    (sqn_rel base 17 (n := 8) (by decide) (by decide)).seq <|
    (ops_rel [.mul 17 17 16, .copy 18 17]).seq <|
    (sqn_rel base 18 (n := 16) (by decide) (by decide)).seq <|
    (ops_rel [.mul 18 18 17, .copy 19 18]).seq <|
    (sqn_rel base 19 (n := 32) (by decide) (by decide)).seq <|
    (ops_rel [.mul 19 19 18, .copy 20 19]).seq <|
    (sqn_rel base 20 (n := 64) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 19]).seq <|
    (sqn_rel base 20 (n := 64) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 19]).seq <|
    (sqn_rel base 20 (n := 16) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 17]).seq <|
    (sqn_rel base 20 (n := 8) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 16]).seq <|
    (sqn_rel base 20 (n := 4) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 15]).seq <|
    (sqn_rel base 20 (n := 2) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 14, .copy 21 20]).seq <|
    (sqn_rel base 21 (n := 1) (by decide) (by decide)).seq <|
    (ops_rel [.mul 21 21 2]).seq <|
    (sqn_rel base 21 (n := 225) (by decide) (by decide)).seq <|
    (sqn_rel base 20 (n := 2) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 2, .mul 21 21 20])
  exact h

/-- The traces of code that keeps `RF` agree in two runs in `FE`. -/
theorem rf_tr {P₀ F : State → State → Prop} {bs : State → Addr}
    (hP : ∀ σ₁ σ₂, P₀ σ₁ σ₂ → bs σ₁ = bs σ₂ ∧ σ₁.gpr .esp = σ₂.gpr .esp)
    (hF : ∀ σ s, F σ s → FS bs σ s) {c : Prog isa} (h : ∀ b, RelCT isa (RF b) c (RF b)) :
    RelCT isa (Runs P₀ F) c fun _ _ => True :=
  (RelCT.exists_ fun b => (h b).mono (fun _ _ h => h) fun _ _ _ => trivial).mono
    (fun _ _ ⟨_, _, hp, f₁, f₂⟩ => ⟨_, FS.rf (hP _ _ hp).1 (hP _ _ hp).2 (hF _ _ f₁) (hF _ _ f₂)⟩)
    fun _ _ h => h

/-! ## Code reading the arguments -/

/-- An argument's byte, in a run of field arithmetic, is that on entry. -/
theorem FE.argByte {bs : State → Addr} {σ s : State} (h : FE bs σ s) {n : Nat}
    (hfit : (σ.gpr .esp).toNat + 4 + n ≤ 2 ^ 32)
    (hd : ∀ r ∈ σ.wr ++ [below (σ.gpr .esp) 20], (⟨argAddr σ 0, n⟩ : Region).Disjoint r) {k : Nat}
    (h4 : 4 ≤ k) (hk : k < 4 + n) :
    s.mem (VG.X86.Taint.argByte s k) = σ.mem (VG.X86.Taint.argByte σ k) := by
  have e : VG.X86.Taint.argByte s k = argAddr σ 0 + BitVec.ofNat 64 (k - 4) := by
    simp only [argAddr, Nat.mul_zero, Nat.add_zero]
    rw [show (σ.gpr .esp + BitVec.ofNat 32 4).setWidth 64 = addr (σ.gpr .esp) 4 from rfl,
      addr_eq (by omega_using [hfit, h4, hk])]
    simp only [VG.X86.Taint.argByte, h.sp]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega_using [h4]
  have hc : (⟨argAddr σ 0, n⟩ : Region).Contains (VG.X86.Taint.argByte s k) 1 := by
    rw [e]; exact Offset.contains_base _ (by omega_using [h4, hk]) (by omega_using [hfit, hk])
  rw [h.frame _ fun r hr hr' => hd r hr _ hc hr']
  simp only [VG.X86.Taint.argByte, h.sp]

/-- What code reading `n - 4` bytes of arguments needs public: `esp`, `edi`
and the arguments. -/
def τa (n : Nat) : VG.X86.Taint.T := { regs := .ofList [.esp, .edi], flags := false, argLen := n }

theorem FE.wfA {bs : State → Addr} {σ s : State} (h : FE bs σ s) {n : Nat}
    (hfit : (σ.gpr .esp).toNat + n ≤ 2 ^ 32)
    (hwr : ∀ r ∈ σ.wr, Region.Disjoint ⟨(σ.gpr .esp).setWidth 64, n⟩ r) : VG.X86.Taint.Wf (τa n) s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by rw [h.sp]; exact hfit, by rw [h.wr, h.sp]; exact hwr⟩,
    fun _ h => (List.not_mem_nil h).elim⟩

/-- Two runs of field arithmetic agree on what code reading the arguments
needs public, if their entry states agree on the arguments. -/
theorem FE.agreeA {bs : State → Addr} {σ₁ σ₂ s₁ s₂ : State} (h₁ : FE bs σ₁ s₁) (h₂ : FE bs σ₂ s₂)
    (hb : bs σ₁ = bs σ₂) (hs : σ₁.gpr .esp = σ₂.gpr .esp) {n : Nat}
    (hfit₁ : (σ₁.gpr .esp).toNat + n ≤ 2 ^ 32) (hfit₂ : (σ₂.gpr .esp).toNat + n ≤ 2 ^ 32)
    (hwr₁ : ∀ r ∈ σ₁.wr, Region.Disjoint ⟨(σ₁.gpr .esp).setWidth 64, n⟩ r)
    (hwr₂ : ∀ r ∈ σ₂.wr, Region.Disjoint ⟨(σ₂.gpr .esp).setWidth 64, n⟩ r)
    (hd₁ : ∀ r ∈ σ₁.wr ++ [below (σ₁.gpr .esp) 20], (⟨argAddr σ₁ 0, n - 4⟩ : Region).Disjoint r)
    (hd₂ : ∀ r ∈ σ₂.wr ++ [below (σ₂.gpr .esp) 20], (⟨argAddr σ₂ 0, n - 4⟩ : Region).Disjoint r)
    (hm : ∀ k, 4 ≤ k → k < n →
      σ₁.mem (VG.X86.Taint.argByte σ₁ k) = σ₂.mem (VG.X86.Taint.argByte σ₂ k)) :
    VG.X86.Taint.Agree (τa n) s₁ s₂ := by
  have esp : s₁.gpr .esp = s₂.gpr .esp := h₁.sp.trans (hs.trans h₂.sp.symm)
  have edi : s₁.gpr .edi = s₂.gpr .edi := edi_eq h₁.fin.scr (hb ▸ h₂.fin.scr)
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, h₁.wfA hfit₁ hwr₁,
    h₂.wfA hfit₂ hwr₂, VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty,
    fun _ => esp, fun k h4 hk => ?_⟩
  · simp only [τa, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact esp
    · exact edi
  · simp only [τa, VG.X86.Taint.depth, Nat.zero_add] at hk ⊢
    rw [h₁.argByte (by omega_using [hfit₁, h4, hk]) hd₁ h4 (by omega_using [hk]), h₂.argByte (by omega_using [hfit₂, h4, hk]) hd₂ h4 (by omega_using [hk])]
    exact hm k h4 hk

end VG.Proof.X448.X86
