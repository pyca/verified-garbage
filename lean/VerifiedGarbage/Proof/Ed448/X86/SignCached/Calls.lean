import VerifiedGarbage.Proof.Ed448.X86.SignCached.Hash
import VerifiedGarbage.Proof.Ed448.X86.BaseLocal
import VerifiedGarbage.Proof.Ed448.X86.Callee
import VerifiedGarbage.Proof.Ed448.X86.ScalarVerified
import VerifiedGarbage.Proof.Ed448.X86.ScalarLit

/-!
# Ed448 signing with a cached key on x86 (32-bit): the scalar calls

Each call's arguments set up in the outgoing slots (`…Slots`, `…_setup`),
its contract's precondition from them (`…_pre`, `…_ready`), and what it
leaves (`…_call`), for `r` (`vg_ed448_scalar_reduce` into the second half of
`out`), `R` (`base`, into the first half), `k` (`vg_ed448_scalar_reduce`
into the frame at `K`) and `S` (`vg_ed448_scalar_mul_add` over `r`).
-/

namespace VG.Proof.Ed448.X86.SignCached

open VG VG.X86 VG.Impl.Ed448.X86.SignCached
open VG.Impl.Ed25519.X86.Whole (Value)
open VG.Impl.Ed448.X86.Shake (callWith)
open VG.Proof.Ed448.X86.Shake
open VG.Proof.Ed25519.X86 (Whole.slots Whole.Within Whole.FR Whole.call_ok Whole.CallReady)

variable {s t u : State} {g : Reg → BitVec 32} {m : Mem}

theorem reduce_nosp : NoSp Impl.Ed448.X86.scalarReduce := NoSp.of_all (by lit_decide)
theorem reduce_stack : stackUse Impl.Ed448.X86.scalarReduce ≤ 20 := by lit_decide
theorem mulAdd_nosp : NoSp Impl.Ed448.X86.scalarMulAdd := NoSp.of_all (by lit_decide)
theorem mulAdd_stack : stackUse Impl.Ed448.X86.scalarMulAdd ≤ 20 := by lit_decide


section
variable (h : Facts s)
include h

theorem out_lo : (Lo (base s)).Disjoint (OUT s) := ((kit h).ko _ (out_in s)).sub_left (lo_sub _)
theorem out1_lo : (Lo (base s)).Disjoint (OUT1 s) := (out_lo h).sub_right (out1_within s).sub
theorem out2_lo : (Lo (base s)).Disjoint (OUT2 s) := (out_lo h).sub_right (out2_within s).sub
theorem out1_scr : (OUT1 s).Disjoint (SCR (arg s 7)) := h.oc.sub_left (out1_within s).sub
theorem out2_scr : (OUT2 s).Disjoint (SCR (arg s 7)) := h.oc.sub_left (out2_within s).sub

theorem out2_fit : (arg s 0 + BitVec.ofNat 32 57).toNat + 57 ≤ 2 ^ 32 := by
  have := h.out
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 57) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

omit h in
theorem ab_eq (hu : GCtx s g m u) : ∀ rd wr, argAddr (u.callEntry.withRegions rd wr) 0 = (base s).setWidth 64 :=
  VG.Proof.Ed25519.X86.Whole.arg_base hu.esp

/-! ## `r` -/

structure RSlots (s u : State) : Prop where
  a0 : Whole.slots (base s) u 0 = arg s 0 + BitVec.ofNat 32 57
  a1 : Whole.slots (base s) u 1 = base s + BitVec.ofNat 32 HASH
  a2 : Whole.slots (base s) u 2 = arg s 7

theorem r_setup (hc : GCtx s g m t) (ha : Shake.Args (base s) 8 (arg s) m) :
    WP isa (.block reduceRArgs) t fun u => GCtx s g m u ∧ Frame [⟨(base s).setWidth 64, 24⟩] t.mem u.mem ∧
      RSlots s u := by
  unfold reduceRArgs
  refine WP.mono ((kit h).setup_ok hc ha (vs := [.caller 0 57, .frame HASH, .caller SC 0]) (by decide)
    (by simp only [List.forall_mem_cons]; exact ⟨show 0 < 8 by decide, trivial, show 7 < 8 by decide,
      fun _ h => nomatch h⟩)) fun u ⟨hu, hm, hs, _⟩ => ⟨hu, hm, ?_⟩
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  simp only [argVal_frame, argVal_caller, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero]
    at a0 a1 a2
  exact ⟨a0, a1, a2⟩

theorem r_pre (hu : GCtx s g m u) (hs : RSlots s u) :
    Proof.Ed448.X86.scalarReduceLocal.pre (u.callEntry.withRegions
      [fr (base s) HASH 114, ⟨(base s).setWidth 64, 12⟩] [OUT2 s, SCR (arg s 7)]) := by
  have hk := kit h
  have fh := hk.fr_addr (d := HASH) (by decide)
  have hb := hk.below
  have hf := hk.frame
  have e4 := hk.esp4
  simp only [Proof.Ed448.X86.scalarReduceLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hu.esp, hk.slot_arg hu (j := 0) (by decide) hs.a0,
    hk.slot_arg hu (j := 1) (by decide) hs.a1, hk.slot_arg hu (j := 2) (by decide) hs.a2, ab_eq hu, fh,
    out2_addr h]
  exact ⟨trivial, trivial, out2_scr h, hk.fr_scr (by decide), Kit.args_disj (by decide) (out2_lo h),
    Kit.args_disj (by decide) hk.lo_scr, hk.ret_disj (out2_lo h), hk.ret_disj hk.lo_scr, out2_fit h,
    hk.fr_fit (by decide), h.scratch, by omega⟩

omit h in
theorem r_covers (s : State) :
    Covers ([fr (base s) HASH 114, ⟨(base s).setWidth 64, 12⟩] ++ [OUT2 s, SCR (arg s 7)])
      (scRd s ++ Whole.FR (base s) :: scWr s) := by
  refine covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inl (frame_within _ (by decide))
  · exact .inl (args_within _ (by decide))
  · exact .inr ⟨_, List.mem_append_right _ (out_in s), out2_within s⟩
  · exact .inr ⟨_, List.mem_append_right _ (scr_in s), whole _⟩

omit h in
theorem r_writes (s : State) : ∀ r ∈ [OUT2 s, SCR (arg s 7)],
    Whole.Within r (Whole.FR (base s)) ∨ ∃ R ∈ scWr s, Whole.Within r R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr ⟨_, out_in s, out2_within s⟩
  · exact .inr ⟨_, scr_in s, whole _⟩

def r_ready (hu : GCtx s g m u) (hs : RSlots s u) :
    Whole.CallReady Proof.Ed448.X86.scalarReduceLocal (base s) (scRd s) (scWr s) u :=
  ⟨_, _, r_pre h hu hs, r_covers s, r_writes s⟩

/-- A call's frame, into a list of the regions it may write and `Lo E`. -/
theorem call_frame3 {a b : Region} {m₁ m₂ : Mem} (hf : Frame ([a, b] ++ [VG.X86.below (base s) 24]) m₁ m₂) :
    Frame [a, b, Lo (base s)] m₁ m₂ := by
  refine Frame.sub hf fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨r, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨r, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · exact ⟨Lo (base s), by simp, below_lo (kit h).below⟩

theorem r_call (hu : GCtx s g m u) (hs : RSlots s u) :
    WP isa (.call "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) u fun v => GCtx s g m v ∧
      Frame [OUT2 s, SCR (arg s 7), Lo (base s)] u.mem v.mem ∧
      Spec.Ed448.bytesAt v.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 57) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114) := by
  have hk := kit h
  have fh := hk.fr_addr (d := HASH) (by decide)
  refine Whole.call_ok hu hk.below (fun s h => Proof.Ed448.X86.scalarReduce_ok s h) reduce_nosp reduce_stack
    (r_pre h hu hs) (r_covers s) (r_writes s) fun v hv hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hv, call_frame3 h hf, ?_⟩
  simp only [Proof.Ed448.X86.scalarReduceLocal, State.withRegions_mem, arg_withRegions, hm₂,
    hk.slot_arg hu (j := 0) (by decide) hs.a0, hk.slot_arg hu (j := 1) (by decide) hs.a1, fh, out2_addr h] at hpost
  rw [hpost, hk.entry_bytes hu (D := fr (base s) HASH 114) (lo_fr _ (by decide) (by decide))
    (by show 114 ≤ 2 ^ 64; decide)]

/-! ## `R` -/

structure BSlots (s u : State) : Prop where
  a0 : Whole.slots (base s) u 0 = arg s 0
  a1 : Whole.slots (base s) u 1 = arg s 0 + BitVec.ofNat 32 57
  a2 : Whole.slots (base s) u 2 = arg s 7

theorem b_setup (hc : GCtx s g m t) (ha : Shake.Args (base s) 8 (arg s) m) :
    WP isa (.block baseArgs) t fun u => GCtx s g m u ∧ Frame [⟨(base s).setWidth 64, 24⟩] t.mem u.mem ∧
      BSlots s u := by
  unfold baseArgs
  refine WP.mono ((kit h).setup_ok hc ha (vs := [.caller 0 0, .caller 0 57, .caller SC 0]) (by decide)
    (by simp only [List.forall_mem_cons]; exact ⟨show 0 < 8 by decide, show 0 < 8 by decide,
      show 7 < 8 by decide, fun _ h => nomatch h⟩)) fun u ⟨hu, hm, hs, _⟩ => ⟨hu, hm, ?_⟩
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  simp only [argVal_caller, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2
  exact ⟨a0, a1, a2⟩

theorem b_pre (hu : GCtx s g m u) (hs : BSlots s u) :
    scalarBaseLocal.pre (u.callEntry.withRegions [OUT2 s, ⟨(base s).setWidth 64, 12⟩] [OUT1 s, SCR (arg s 7)]) := by
  have hk := kit h
  have hb := hk.below
  have hf := hk.frame
  have e4 := hk.esp4
  simp only [scalarBaseLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hu.esp, hk.slot_arg hu (j := 0) (by decide) hs.a0,
    hk.slot_arg hu (j := 1) (by decide) hs.a1, hk.slot_arg hu (j := 2) (by decide) hs.a2, ab_eq hu,
    out2_addr h]
  exact ⟨trivial, trivial, out1_scr h, out2_scr h, Kit.args_disj (by decide) (out1_lo h),
    Kit.args_disj (by decide) hk.lo_scr, hk.ret_disj (out1_lo h), hk.ret_disj hk.lo_scr,
    by have := h.out; omega, out2_fit h, h.scratch, by omega⟩

omit h in
theorem b_covers (s : State) :
    Covers ([OUT2 s, ⟨(base s).setWidth 64, 12⟩] ++ [OUT1 s, SCR (arg s 7)]) (scRd s ++ Whole.FR (base s) :: scWr s) := by
  refine covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inr ⟨_, List.mem_append_right _ (out_in s), out2_within s⟩
  · exact .inl (args_within _ (by decide))
  · exact .inr ⟨_, List.mem_append_right _ (out_in s), out1_within s⟩
  · exact .inr ⟨_, List.mem_append_right _ (scr_in s), whole _⟩

omit h in
theorem b_writes (s : State) : ∀ r ∈ [OUT1 s, SCR (arg s 7)],
    Whole.Within r (Whole.FR (base s)) ∨ ∃ R ∈ scWr s, Whole.Within r R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr ⟨_, out_in s, out1_within s⟩
  · exact .inr ⟨_, scr_in s, whole _⟩

def b_ready (hu : GCtx s g m u) (hs : BSlots s u) :
    Whole.CallReady scalarBaseLocal (base s) (scRd s) (scWr s) u :=
  ⟨_, _, b_pre h hu hs, b_covers s, b_writes s⟩

theorem b_call {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') (hu : GCtx s g m u) (hs : BSlots s u) :
    WP isa (.call "vg_ed448_scalar_base" base') u fun v => GCtx s g m v ∧
      Frame [OUT1 s, SCR (arg s 7), Lo (base s)] u.mem v.mem ∧
      Spec.Ed448.bytesAt v.mem ((arg s 0).setWidth 64) 57 =
        Spec.Ed448.scalarBase (Spec.Ed448.bytesAt u.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 57) 57) := by
  have hk := kit h
  refine Whole.call_ok hu hk.below hB.ok hB.nosp hB.stack (b_pre h hu hs) (b_covers s) (b_writes s)
    fun v hv hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hv, call_frame3 h hf, ?_⟩
  simp only [scalarBaseLocal, State.withRegions_mem, arg_withRegions, hm₂,
    hk.slot_arg hu (j := 0) (by decide) hs.a0, hk.slot_arg hu (j := 1) (by decide) hs.a1, out2_addr h] at hpost
  rw [hpost, hk.entry_bytes hu (D := OUT2 s) (out2_lo h) (by show 57 ≤ 2 ^ 64; decide)]

/-! ## `k` -/

structure KSlots (s u : State) : Prop where
  a0 : Whole.slots (base s) u 0 = base s + BitVec.ofNat 32 K
  a1 : Whole.slots (base s) u 1 = base s + BitVec.ofNat 32 HASH
  a2 : Whole.slots (base s) u 2 = arg s 7

theorem k_setup (hc : GCtx s g m t) (ha : Shake.Args (base s) 8 (arg s) m) :
    WP isa (.block reduceKArgs) t fun u => GCtx s g m u ∧ Frame [⟨(base s).setWidth 64, 24⟩] t.mem u.mem ∧
      KSlots s u := by
  unfold reduceKArgs
  refine WP.mono ((kit h).setup_ok hc ha (vs := [.frame K, .frame HASH, .caller SC 0]) (by decide)
    (by simp only [List.forall_mem_cons]; exact ⟨trivial, trivial, show 7 < 8 by decide,
      fun _ h => nomatch h⟩)) fun u ⟨hu, hm, hs, _⟩ => ⟨hu, hm, ?_⟩
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  simp only [argVal_frame, argVal_caller, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero]
    at a0 a1 a2
  exact ⟨a0, a1, a2⟩

theorem k_pre (hu : GCtx s g m u) (hs : KSlots s u) :
    Proof.Ed448.X86.scalarReduceLocal.pre (u.callEntry.withRegions
      [fr (base s) HASH 114, ⟨(base s).setWidth 64, 12⟩] [fr (base s) K 57, SCR (arg s 7)]) := by
  have hk := kit h
  have fk := hk.fr_addr (d := K) (by decide)
  have fh := hk.fr_addr (d := HASH) (by decide)
  have hb := hk.below
  have hf := hk.frame
  have e4 := hk.esp4
  simp only [Proof.Ed448.X86.scalarReduceLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hu.esp, hk.slot_arg hu (j := 0) (by decide) hs.a0,
    hk.slot_arg hu (j := 1) (by decide) hs.a1, hk.slot_arg hu (j := 2) (by decide) hs.a2, ab_eq hu, fk, fh]
  exact ⟨trivial, trivial, hk.fr_scr (by decide), hk.fr_scr (by decide),
    Offset.base_disjoint _ (by decide) (by decide), Kit.args_disj (by decide) hk.lo_scr,
    hk.ret_disj (lo_fr _ (by decide) (by decide)), hk.ret_disj hk.lo_scr, hk.fr_fit (by decide),
    hk.fr_fit (by decide), h.scratch, by omega⟩

omit h in
theorem k_covers (s : State) :
    Covers ([fr (base s) HASH 114, ⟨(base s).setWidth 64, 12⟩] ++ [fr (base s) K 57, SCR (arg s 7)])
      (scRd s ++ Whole.FR (base s) :: scWr s) := by
  refine covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inl (frame_within _ (by decide))
  · exact .inl (args_within _ (by decide))
  · exact .inl (frame_within _ (by decide))
  · exact .inr ⟨_, List.mem_append_right _ (scr_in s), whole _⟩

omit h in
theorem k_writes (s : State) : ∀ r ∈ [fr (base s) K 57, SCR (arg s 7)],
    Whole.Within r (Whole.FR (base s)) ∨ ∃ R ∈ scWr s, Whole.Within r R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inl (frame_within _ (by decide))
  · exact .inr ⟨_, scr_in s, whole _⟩

def k_ready (hu : GCtx s g m u) (hs : KSlots s u) :
    Whole.CallReady Proof.Ed448.X86.scalarReduceLocal (base s) (scRd s) (scWr s) u :=
  ⟨_, _, k_pre h hu hs, k_covers s, k_writes s⟩

theorem k_call (hu : GCtx s g m u) (hs : KSlots s u) :
    WP isa (.call "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) u fun v => GCtx s g m v ∧
      Frame [fr (base s) K 57, SCR (arg s 7), Lo (base s)] u.mem v.mem ∧
      Spec.Ed448.bytesAt v.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114) := by
  have hk := kit h
  have fk := hk.fr_addr (d := K) (by decide)
  have fh := hk.fr_addr (d := HASH) (by decide)
  refine Whole.call_ok hu hk.below (fun s h => Proof.Ed448.X86.scalarReduce_ok s h) reduce_nosp reduce_stack
    (k_pre h hu hs) (k_covers s) (k_writes s) fun v hv hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hv, call_frame3 h hf, ?_⟩
  simp only [Proof.Ed448.X86.scalarReduceLocal, State.withRegions_mem, arg_withRegions, hm₂,
    hk.slot_arg hu (j := 0) (by decide) hs.a0, hk.slot_arg hu (j := 1) (by decide) hs.a1, fk, fh] at hpost
  rw [hpost, hk.entry_bytes hu (D := fr (base s) HASH 114) (lo_fr _ (by decide) (by decide))
    (by show 114 ≤ 2 ^ 64; decide)]

/-! ## `S` -/

structure MSlots (s u : State) : Prop where
  a0 : Whole.slots (base s) u 0 = arg s 0 + BitVec.ofNat 32 57
  a1 : Whole.slots (base s) u 1 = arg s 0 + BitVec.ofNat 32 57
  a2 : Whole.slots (base s) u 2 = base s + BitVec.ofNat 32 K
  a3 : Whole.slots (base s) u 3 = base s + BitVec.ofNat 32 S
  a4 : Whole.slots (base s) u 4 = arg s 7

theorem m_setup (hc : GCtx s g m t) (ha : Shake.Args (base s) 8 (arg s) m) :
    WP isa (.block mulAddArgs) t fun u => GCtx s g m u ∧ Frame [⟨(base s).setWidth 64, 24⟩] t.mem u.mem ∧
      MSlots s u := by
  unfold mulAddArgs
  refine WP.mono ((kit h).setup_ok hc ha (vs := [.caller 0 57, .caller 0 57, .frame K, .frame S, .caller SC 0])
    (by decide) (by simp only [List.forall_mem_cons]; exact ⟨show 0 < 8 by decide, show 0 < 8 by decide,
      trivial, trivial, show 7 < 8 by decide, fun _ h => nomatch h⟩)) fun u ⟨hu, hm, hs, _⟩ => ⟨hu, hm, ?_⟩
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  have a3 := hs 3 (by decide)
  have a4 := hs 4 (by decide)
  simp only [argVal_frame, argVal_caller, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero]
    at a0 a1 a2 a3 a4
  exact ⟨a0, a1, a2, a3, a4⟩

theorem m_pre (hu : GCtx s g m u) (hs : MSlots s u) :
    Proof.Ed448.X86.scalarMulAddLocal.pre (u.callEntry.withRegions
      [OUT2 s, fr (base s) K 57, fr (base s) S 57, ⟨(base s).setWidth 64, 20⟩] [OUT2 s, SCR (arg s 7)]) := by
  have hk := kit h
  have fk := hk.fr_addr (d := K) (by decide)
  have fs := hk.fr_addr (d := S) (by decide)
  have hb := hk.below
  have hf := hk.frame
  have e4 := hk.esp4
  simp only [Proof.Ed448.X86.scalarMulAddLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hu.esp, hk.slot_arg hu (j := 0) (by decide) hs.a0,
    hk.slot_arg hu (j := 1) (by decide) hs.a1, hk.slot_arg hu (j := 2) (by decide) hs.a2,
    hk.slot_arg hu (j := 3) (by decide) hs.a3, hk.slot_arg hu (j := 4) (by decide) hs.a4, ab_eq hu, fk, fs,
    out2_addr h]
  exact ⟨trivial, trivial, out2_scr h, out2_scr h, hk.fr_scr (by decide), hk.fr_scr (by decide),
    Kit.args_disj (by decide) (out2_lo h), Kit.args_disj (by decide) hk.lo_scr, hk.ret_disj (out2_lo h),
    hk.ret_disj hk.lo_scr, out2_fit h, out2_fit h, hk.fr_fit (by decide), hk.fr_fit (by decide), h.scratch,
    by omega⟩

omit h in
theorem m_covers (s : State) :
    Covers ([OUT2 s, fr (base s) K 57, fr (base s) S 57, ⟨(base s).setWidth 64, 20⟩] ++ [OUT2 s, SCR (arg s 7)])
      (scRd s ++ Whole.FR (base s) :: scWr s) := by
  refine covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨_, List.mem_append_right _ (out_in s), out2_within s⟩
  · exact .inl (frame_within _ (by decide))
  · exact .inl (frame_within _ (by decide))
  · exact .inl (args_within _ (by decide))
  · exact .inr ⟨_, List.mem_append_right _ (out_in s), out2_within s⟩
  · exact .inr ⟨_, List.mem_append_right _ (scr_in s), whole _⟩

def m_ready (hu : GCtx s g m u) (hs : MSlots s u) :
    Whole.CallReady Proof.Ed448.X86.scalarMulAddLocal (base s) (scRd s) (scWr s) u :=
  ⟨_, _, m_pre h hu hs, m_covers s, r_writes s⟩

theorem m_call (hu : GCtx s g m u) (hs : MSlots s u) :
    WP isa (.call "vg_ed448_scalar_mul_add" Impl.Ed448.X86.scalarMulAdd) u fun v => GCtx s g m v ∧
      Frame [OUT2 s, SCR (arg s 7), Lo (base s)] u.mem v.mem ∧
      Spec.Ed448.bytesAt v.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 57) 57 =
        Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt u.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 57) 57)
          (Spec.Ed448.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57)
          (Spec.Ed448.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 S) 57) := by
  have hk := kit h
  have fk := hk.fr_addr (d := K) (by decide)
  have fs := hk.fr_addr (d := S) (by decide)
  refine Whole.call_ok hu hk.below (fun s h => Proof.Ed448.X86.scalarMulAdd_ok s h) mulAdd_nosp mulAdd_stack
    (m_pre h hu hs) (m_covers s) (r_writes s) fun v hv hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hv, call_frame3 h hf, ?_⟩
  simp only [Proof.Ed448.X86.scalarMulAddLocal, State.withRegions_mem, arg_withRegions, hm₂,
    hk.slot_arg hu (j := 0) (by decide) hs.a0, hk.slot_arg hu (j := 1) (by decide) hs.a1,
    hk.slot_arg hu (j := 2) (by decide) hs.a2, hk.slot_arg hu (j := 3) (by decide) hs.a3, fk, fs,
    out2_addr h] at hpost
  rw [hpost, hk.entry_bytes hu (D := OUT2 s) (out2_lo h) (by show 57 ≤ 2 ^ 64; decide),
    hk.entry_bytes hu (D := fr (base s) K 57) (lo_fr _ (by decide) (by decide)) (by show 57 ≤ 2 ^ 64; decide),
    hk.entry_bytes hu (D := fr (base s) S 57) (lo_fr _ (by decide) (by decide)) (by show 57 ≤ 2 ^ 64; decide)]

end

end VG.Proof.Ed448.X86.SignCached
