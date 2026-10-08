import VerifiedGarbage.Proof.X448.X86.Ops
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.TaintErase

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
  callEntry_arg (by have := hc.sp; omega) hrs hi

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
  · rw [esp, sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega
  · rw [ws, a0]
    exact hc.sep.sub_right (below_sub (by omega) hE)
  · rw [ws, esp]
    refine (hc.sep.sub_right ?_).symm
    refine fun x hx => below_inner (sp := s.gpr .esp) (a := 4) (k := 4 * rs.length) (b := 20) (by omega) hE x ?_
    have e : s.gpr .esp - BitVec.ofNat 32 (4 * rs.length + 4) =
        s.gpr .esp - BitVec.ofNat 32 (4 * rs.length) - BitVec.ofNat 32 4 := by
      rw [BitVec.sub_sub, BitVec.ofNat_add]
    simp only [below]
    rw [← e]; exact hx
  · rw [hw]; exact hs.nowrap

theorem entryOf_mem (hrs : .esp ∉ rs) (hl : rs.length ≤ 4) (hc : CallCtx s base) :
    WsEq base s.mem (entryOf rs s base).mem :=
  WsEq.of_frame hc ((callEntry_frame (by have := hc.sp; omega) hrs).sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨callStk s, List.mem_singleton_self _, below_sub (by omega) hc.sp⟩)

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

theorem fits_slot {o : Nat} (h : Slot o) : Spec.X448.Field16.Fits (BitVec.ofNat 32 o) := by
  have : o + 112 ≤ 3584 := h
  show (BitVec.ofNat 32 o).toNat + 112 ≤ 3584
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact this

theorem limbs_slot {m : Mem} {base : Addr} {a : Nat} (h : Slot a) (hb : Bounded m base a) :
    Spec.X448.Field16.Limbs m base (BitVec.ofNat 32 a) := by
  have : a + 112 ≤ 3584 := h
  rw [limbs_spec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hb

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
    · rw [hw, a2]; exact limbs_slot ha (w.bounded (by omega) ab)
    · rw [hw, a3]; exact limbs_slot hb (w.bounded (by omega) bb)
  exact ⟨pre, entryOf_cov hs, entryOf_covw hs⟩

/-- `vg_gf448_r16_mul_a24`'s precondition, at its call after the offsets' `mov`s. -/
theorem callPre_a24 {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base) {o a : Nat}
    (ho : Slot o) (ha : Slot a) (ab : Bounded s.mem base a) (heax : s.gpr .eax = BitVec.ofNat 32 o)
    (hecx : s.gpr .ecx = BitVec.ofNat 32 a) :
    CallPre a24X86 [.ecx, .eax, .edi] [below (s.gpr .esp) (4 * [Reg.ecx, .eax, .edi].length)]
      [⟨base, 8192⟩] s := by
  have ha' : a + 112 ≤ 3584 := ha
  have av := fun i (hi : i < 3) => entryOf_arg (rs := [.ecx, .eax, .edi]) (base := base) (by decide)
    (by decide) hc hi
  have w : WsEq base s.mem (entryOf [.ecx, .eax, .edi] s base).mem := entryOf_mem (by decide) (by decide) hc
  have hw : wsOf (entryOf [.ecx, .eax, .edi] s base) = base := by
    rw [wsOf, av 0 (by decide)]; exact hs.edi
  have a1 : arg (entryOf [.ecx, .eax, .edi] s base) 1 = BitVec.ofNat 32 o := (av 1 (by decide)).trans heax
  have a2 : arg (entryOf [.ecx, .eax, .edi] s base) 2 = BitVec.ofNat 32 a := (av 2 (by decide)).trans hecx
  have pre : a24X86.pre (entryOf [.ecx, .eax, .edi] s base) := by
    refine ⟨entryOf_fnPre (by decide) hs hc (av 0 (by decide)), ?_, ?_, ?_⟩
    · rw [a1]; exact fits_slot ho
    · rw [a2]; exact fits_slot ha
    · rw [hw, a2]; exact limbs_slot ha (w.bounded (by omega) ab)
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

/-- The trace of a call of `vg_gf448_r16_mul_a24`, from `RF`. -/
theorem call2_tr {name : String} {body : Prog isa}
    (hv : ∀ s, a24X86.pre s → ∃ t s', Exec isa body s t s' ∧ abiPreserved s s' ∧ a24X86.post s s')
    (hct : ConstantTime isa a24X86.pre a24X86.pub body) {base : Addr} (o a : Index) :
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
    · rw [← e₁]; exact callPre_a24 f₁.scr f₁.ctx (slot_bound o) (slot_bound a) (f₁.bounded a) ga.1 gc.1
    · rw [← e₂]; exact callPre_a24 f₂.scr f₂.ctx (slot_bound o) (slot_bound a) (f₂.bounded a) ga.2 gc.2
    · have hr : ∀ q ∈ [Reg.ecx, .eax, .edi], t₁.gpr q = t₂.gpr q := by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · rw [gc.1, gc.2]
        · rw [ga.1, ga.2]
        · exact edi_eq f₁.scr f₂.scr
      have fit : 4 * [Reg.ecx, .eax, .edi].length + 4 ≤ (t₁.gpr .esp).toNat := by
        have := f₁.ctx.sp; simp; omega
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
  | mul o a b => exact call3_tr mulFn_correct (mulFn_ct bin_agree) o a b
  | add o a b => exact call3_tr addFn_correct (addFn_ct bin_agree) o a b
  | sub o a b => exact call3_tr subFn_correct (subFn_ct bin_agree) o a b
  | mulSmall o a => exact call2_tr mulA24Fn_correct (mulA24Fn_ct a24_agree) o a
  | copy o a =>
    exact RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ h => h.agree)
      (copy_check (slot o.val) (slot a.val))

theorem ops_rel {base : Addr} (xs : List FieldOp) :
    RelCT isa (RF base) (ops (xs.map FieldOp.impl)) (RF base) := by
  induction xs with
  | nil => exact RelCT.nil fun _ _ h => h
  | cons op rest ih => exact RelCT.seq (fieldOp_rel op) ih

end VG.Proof.X448.X86
