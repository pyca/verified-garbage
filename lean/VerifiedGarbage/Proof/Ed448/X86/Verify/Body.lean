import VerifiedGarbage.Proof.Ed448.X86.Verify.Layout
import VerifiedGarbage.Proof.Ed448.X86.Shake.Sponge
import VerifiedGarbage.Proof.Ed448.X86.Shake.Header
import VerifiedGarbage.Proof.Ed448.X86.Shake.Prune
import VerifiedGarbage.Proof.Ed448.X86.VerifyLocal
import VerifiedGarbage.Proof.Ed448.X86.Callee
import VerifiedGarbage.Proof.Ed448.X86.ScalarVerified
import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
import VerifiedGarbage.Impl.Ed448.X86.Verify

/-!
# Ed448 verification on x86 (32-bit): correctness

For any `eq` meeting `verifyEquationLocal` (`CalleeOk`): the header of
`dom4` in the frame at `HDR` (`Kit.hdr_ok`), `H(dom4(0, C) ‖ R ‖ A ‖ M)` at
`HASH` (`hash_ok`), `k`, the hash reduced modulo `L`, at `K`
(`reduce_step`, by `vg_ed448_scalar_reduce`), and `eq`'s result in `eax`
(`eq_step`); `verify_ok`: the whole function, which returns 0 at once for a
context of 256 bytes or more.
-/

namespace VG.Proof.Ed448.X86.Verify

open VG VG.X86 VG.X86.Wp VG.Impl.Ed448.X86.Verify
open VG.Impl.Ed25519.X86.Whole (Value setup)
open VG.Impl.Ed448.X86.Shake (callWith)
open VG.Spec.Sha3 (stateAt)
open VG.Proof.Ed448.X86.Shake
open VG.Proof.Ed25519.X86 (Whole.slots Whole.Within Whole.FR Whole.valid Whole.call_ok Whole.CallReady)

variable {s t u : State} {g : Reg → BitVec 32} {m : Mem}

/-- The frame's invariant, from any registers and memory on entry. -/
abbrev GCtx (s : State) (g : Reg → BitVec 32) (m : Mem) (t : State) : Prop :=
  VG.Proof.Ed25519.X86.Whole.Ctx (base s) g m (vfRd s) (vfWr s) t

theorem scr_at (s : State) : ScrAt 7 (arg s) 6 (arg s 6) := ⟨by decide, rfl⟩

theorem sig57 (s : State) : Whole.Within ⟨(arg s 5).setWidth 64, 57⟩ (SIG s) :=
  ⟨0, (BitVec.add_zero _).symm, by show 0 + 57 ≤ 114; decide⟩

/-! ## The hash -/

/-- `H(dom4(0, C) ‖ R ‖ A ‖ M)` in the frame at `HASH`, with the header of
`dom4` in the frame. -/
theorem hash_ok (h : Facts s) (hc : GCtx s g m t) (ha : Shake.Args (base s) 7 (arg s) m)
    (hh : Spec.Sha3.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 HDR) 10 = hdrBytes (arg s 2)) :
    WP isa Impl.Ed448.X86.Verify.hash t fun u => GCtx s g m u ∧
      Spec.Sha3.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114 =
        Spec.Ed448.hash (Spec.Sha3.bytesAt m ((arg s 1).setWidth 64) (arg s 2).toNat)
          (Spec.Sha3.bytesAt m ((arg s 5).setWidth 64) 57 ++ Spec.Sha3.bytesAt m ((arg s 0).setWidth 64) 57 ++
            Spec.Sha3.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat) := by
  have hk := kit h
  have fa := hk.fr_addr (d := HDR) (by decide)
  unfold Impl.Ed448.X86.Verify.hash
  -- Zero the state.
  refine WP.seq (WP.mono (hk.zero_ok hc ha (scr_at s)) fun t1 ⟨hc1, hz, hf1⟩ => ?_)
  have hh1 := sframe_bytes hf1 (D := fr (base s) HDR 10)
    (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hk.fr_scr (by decide)).sub_right (hk.kWr_sub _ (kWr_state _)).sub)
    (by show 10 ≤ 2 ^ 64; decide)
  -- The header.
  refine WP.seq (WP.mono (hk.first_abs hc1 ha (scr_at s) (src := .frame HDR) (len := .const 10)
    (P := base s + BitVec.ofNat 32 HDR) (N := 10) trivial trivial rfl rfl
    (by rw [fa]; exact .inl (frame_within _ (by decide)))
    (by rw [fa]; exact hk.away_fr (by decide) (by decide))
    (hk.fr_fit (by decide)) (repr_nil hz)) fun t2 ⟨hc2, _, hr2, hp2⟩ => ?_)
  rw [fa] at hr2
  have e1 : Spec.Sha3.bytesAt t1.mem ((base s).setWidth 64 + BitVec.ofNat 64 HDR) 10 = hdrBytes (arg s 2) :=
    hh1.trans hh
  rw [e1] at hr2
  have hp2' : t2.gpr .eax = BitVec.ofNat 32 ((hdrBytes (arg s 2)).length % 136) := by rw [hp2, hdr_len]
  -- The context.
  refine WP.seq (WP.mono (hk.next_abs hc2 ha (scr_at s) (src := .caller 1 0) (len := .caller 2 0)
    (P := arg s 1) (N := (arg s 2).toNat) (show 1 < 7 by decide) (show 2 < 7 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (ctx_in s), whole _⟩) (hk.away_input (ctx_in s) (whole _)) h.ctx
    hr2 hp2') fun t3 ⟨hc3, _, hr3, hp3⟩ => ?_)
  have ex : Spec.Sha3.bytesAt t2.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      Spec.Sha3.bytesAt m ((arg s 1).setWidth 64) (arg s 2).toNat :=
    hk.input_bytes (D := CTX s) hc2 (ctx_in s) (whole (CTX s)) (by show (arg s 2).toNat ≤ 2 ^ 64; have := (arg s 2).isLt; omega)
  rw [ex] at hr3 hp3
  -- `R`.
  refine WP.seq (WP.mono (hk.next_abs hc3 ha (scr_at s) (src := .caller 5 0) (len := .const 57)
    (P := arg s 5) (N := 57) (show 5 < 7 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨_, List.mem_append_left _ (sig_in s), sig57 s⟩) (hk.away_input (sig_in s) (sig57 s))
    (by have := h.sig; omega) hr3 hp3) fun t4 ⟨hc4, _, hr4, hp4⟩ => ?_)
  have es : Spec.Sha3.bytesAt t3.mem ((arg s 5).setWidth 64) 57 = Spec.Sha3.bytesAt m ((arg s 5).setWidth 64) 57 :=
    hk.input_bytes (D := ⟨(arg s 5).setWidth 64, 57⟩) hc3 (sig_in s) (sig57 s) (by show 57 ≤ 2 ^ 64; decide)
  rw [es] at hr4 hp4
  -- `A`.
  refine WP.seq (WP.mono (hk.next_abs hc4 ha (scr_at s) (src := .caller 0 0) (len := .const 57)
    (P := arg s 0) (N := 57) (show 0 < 7 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨_, List.mem_append_left _ (pk_in s), whole _⟩) (hk.away_input (pk_in s) (whole _))
    h.pk hr4 hp4) fun t5 ⟨hc5, _, hr5, hp5⟩ => ?_)
  have ep : Spec.Sha3.bytesAt t4.mem ((arg s 0).setWidth 64) 57 = Spec.Sha3.bytesAt m ((arg s 0).setWidth 64) 57 :=
    hk.input_bytes (D := PK s) hc4 (pk_in s) (whole (PK s)) (by show 57 ≤ 2 ^ 64; decide)
  rw [ep] at hr5 hp5
  -- The message.
  refine WP.seq (WP.mono (hk.next_abs hc5 ha (scr_at s) (src := .caller 3 0) (len := .caller 4 0)
    (P := arg s 3) (N := (arg s 4).toNat) (show 3 < 7 by decide) (show 4 < 7 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (msg_in s), whole _⟩) (hk.away_input (msg_in s) (whole _)) h.msg
    hr5 hp5) fun t6 ⟨hc6, _, hr6, hp6⟩ => ?_)
  have em : Spec.Sha3.bytesAt t5.mem ((arg s 3).setWidth 64) (arg s 4).toNat =
      Spec.Sha3.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat :=
    hk.input_bytes (D := MSG s) hc5 (msg_in s) (whole (MSG s)) (by show (arg s 4).toNat ≤ 2 ^ 64; have := (arg s 4).isLt; omega)
  rw [em] at hr6 hp6
  -- Pad and squeeze.
  refine WP.seq (WP.mono (hk.pad_step hc6 ha (scr_at s) hr6 hp6) fun t7 ⟨hc7, _, hs7⟩ => ?_)
  refine WP.mono (hk.sqz_step hc7 ha (scr_at s) (d := HASH) (by decide) (by decide)) fun u ⟨hu, _, hb⟩ =>
    ⟨hu, ?_⟩
  rw [hb, hs7, ← shake256_eq, Spec.Ed448.hash, dom4_eq (arg s 2) _ _ (length_sbytes _ _ _)]
  simp only [List.append_assoc]

/-! ## `k`: the hash reduced modulo `L` -/

theorem reduce_nosp : NoSp Impl.Ed448.X86.scalarReduce := NoSp.of_all (by lit_decide)
theorem reduce_stack : stackUse Impl.Ed448.X86.scalarReduce ≤ 20 := by lit_decide

/-- The outgoing arguments of `scalar_reduce(esp + K, esp + HASH, scratch)`. -/
structure ReduceSlots (s u : State) : Prop where
  a0 : Whole.slots (base s) u 0 = base s + BitVec.ofNat 32 K
  a1 : Whole.slots (base s) u 1 = base s + BitVec.ofNat 32 HASH
  a2 : Whole.slots (base s) u 2 = arg s 6

theorem reduce_setup (h : Facts s) (hc : GCtx s g m t) (ha : Shake.Args (base s) 7 (arg s) m) :
    WP isa (.block reduceArgs) t fun u => GCtx s g m u ∧ Frame [⟨(base s).setWidth 64, 24⟩] t.mem u.mem ∧
      ReduceSlots s u := by
  have hk := kit h
  unfold reduceArgs
  refine WP.mono (hk.setup_ok hc ha (vs := [.frame K, .frame HASH, .caller SC 0]) (by decide)
    (by simp only [List.forall_mem_cons]; exact ⟨trivial, trivial, show 6 < 7 by decide,
      fun _ h => nomatch h⟩)) fun u ⟨hu, hm, hs, _⟩ => ⟨hu, hm, ?_⟩
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  simp only [argVal_frame, argVal_caller, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero]
    at a0 a1 a2
  exact ⟨a0, a1, a2⟩

theorem reduce_pre (h : Facts s) (hu : GCtx s g m u) (hs : ReduceSlots s u) :
    Proof.Ed448.X86.scalarReduceLocal.pre (u.callEntry.withRegions
      [fr (base s) HASH 114, ⟨(base s).setWidth 64, 12⟩] [fr (base s) K 57, SCR (arg s 6)]) := by
  have hk := kit h
  have fk := hk.fr_addr (d := K) (by decide)
  have fh := hk.fr_addr (d := HASH) (by decide)
  have hb := hk.below
  have hf := hk.frame
  have e4 := hk.esp4
  have ab : ∀ rd wr, argAddr (u.callEntry.withRegions rd wr) 0 = (base s).setWidth 64 :=
    VG.Proof.Ed25519.X86.Whole.arg_base hu.esp
  simp only [Proof.Ed448.X86.scalarReduceLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hu.esp, hk.slot_arg hu (j := 0) (by decide) hs.a0,
    hk.slot_arg hu (j := 1) (by decide) hs.a1, hk.slot_arg hu (j := 2) (by decide) hs.a2, ab, fk, fh]
  exact ⟨trivial, trivial, hk.fr_scr (by decide), hk.fr_scr (by decide),
    Offset.base_disjoint _ (by decide) (by decide), Kit.args_disj (by decide) hk.lo_scr,
    hk.ret_disj (lo_fr _ (by decide) (by decide)), hk.ret_disj hk.lo_scr, hk.fr_fit (by decide),
    hk.fr_fit (by decide), h.scratch, by omega⟩

theorem reduce_covers (s : State) :
    Covers ([fr (base s) HASH 114, ⟨(base s).setWidth 64, 12⟩] ++ [fr (base s) K 57, SCR (arg s 6)])
      (vfRd s ++ Whole.FR (base s) :: vfWr s) := by
  refine covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inl (frame_within _ (by decide))
  · exact .inl (args_within _ (by decide))
  · exact .inl (frame_within _ (by decide))
  · exact .inr ⟨_, List.mem_append_right _ (scr_in s), whole _⟩

theorem reduce_writes (s : State) : ∀ r ∈ [fr (base s) K 57, SCR (arg s 6)],
    Whole.Within r (Whole.FR (base s)) ∨ ∃ R ∈ vfWr s, Whole.Within r R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inl (frame_within _ (by decide))
  · exact .inr ⟨_, scr_in s, whole _⟩

def reduce_ready (h : Facts s) (hu : GCtx s g m u) (hs : ReduceSlots s u) :
    Whole.CallReady Proof.Ed448.X86.scalarReduceLocal (base s) (vfRd s) (vfWr s) u :=
  ⟨_, _, reduce_pre h hu hs, reduce_covers s, reduce_writes s⟩

theorem reduce_call (h : Facts s) (hu : GCtx s g m u) (hs : ReduceSlots s u) :
    WP isa (.call "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) u fun v => GCtx s g m v ∧
      Frame (vfWr s ++ [fr (base s) K 57] ++ [Lo (base s)]) u.mem v.mem ∧
      Spec.Ed448.bytesAt v.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114) := by
  have hk := kit h
  have fk := hk.fr_addr (d := K) (by decide)
  have fh := hk.fr_addr (d := HASH) (by decide)
  refine Whole.call_ok hu hk.below (fun s h => Proof.Ed448.X86.scalarReduce_ok s h) reduce_nosp reduce_stack
    (reduce_pre h hu hs) (reduce_covers s) (reduce_writes s) fun v hv hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hv, ?_, ?_⟩
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp [vfWr], fun _ h => h⟩
    · exact ⟨Lo (base s), by simp, below_lo hk.below⟩
  · simp only [Proof.Ed448.X86.scalarReduceLocal, State.withRegions_mem, arg_withRegions, hm₂,
      hk.slot_arg hu (j := 0) (by decide) hs.a0, hk.slot_arg hu (j := 1) (by decide) hs.a1, fk, fh] at hpost
    rw [hpost, hk.entry_bytes hu (D := fr (base s) HASH 114) (lo_fr _ (by decide) (by decide))
      (by show 114 ≤ 2 ^ 64; decide)]

/-- `k = H(…) mod L` in the frame at `K`. -/
theorem reduce_step (h : Facts s) (hc : GCtx s g m t) (ha : Shake.Args (base s) 7 (arg s) m) :
    WP isa (callWith reduceArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) t fun u => GCtx s g m u ∧
      Frame (vfWr s ++ [fr (base s) K 57] ++ [Lo (base s)]) t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114) := by
  refine WP.seq (WP.mono (reduce_setup h hc ha) fun u ⟨hu, hm, hs⟩ => ?_)
  refine WP.mono (reduce_call h hu hs) fun v ⟨hv, hf, ho⟩ => ⟨hv, ?_, ?_⟩
  · refine (hm.sub fun r hr => ⟨Lo (base s), by simp, ?_⟩).trans hf
    rw [List.mem_singleton.mp hr]; exact args_lo _ (by decide)
  · rw [ho, frame_bytes hm (D := fr (base s) HASH 114) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide))
      (by show 114 ≤ 2 ^ 64; decide)]

/-! ## The equation -/

/-- The outgoing arguments of `verify_equation(pk, signature, esp + K, scratch)`. -/
structure EqSlots (s u : State) : Prop where
  a0 : Whole.slots (base s) u 0 = arg s 0
  a1 : Whole.slots (base s) u 1 = arg s 5
  a2 : Whole.slots (base s) u 2 = base s + BitVec.ofNat 32 K
  a3 : Whole.slots (base s) u 3 = arg s 6

theorem eq_setup (h : Facts s) (hc : GCtx s g m t) (ha : Shake.Args (base s) 7 (arg s) m) :
    WP isa (.block equationArgs) t fun u => GCtx s g m u ∧ Frame [⟨(base s).setWidth 64, 24⟩] t.mem u.mem ∧
      EqSlots s u := by
  have hk := kit h
  unfold equationArgs
  refine WP.mono (hk.setup_ok hc ha (vs := [.caller 0 0, .caller 5 0, .frame K, .caller SC 0]) (by decide)
    (by simp only [List.forall_mem_cons]; exact ⟨show 0 < 7 by decide, show 5 < 7 by decide, trivial,
      show 6 < 7 by decide, fun _ h => nomatch h⟩)) fun u ⟨hu, hm, hs, _⟩ => ⟨hu, hm, ?_⟩
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  have a3 := hs 3 (by decide)
  simp only [argVal_frame, argVal_caller, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero]
    at a0 a1 a2 a3
  exact ⟨a0, a1, a2, a3⟩

theorem eq_pre (h : Facts s) (hu : GCtx s g m u) (hs : EqSlots s u) :
    Proof.Ed448.X86.verifyEquationLocal.pre (u.callEntry.withRegions
      [PK s, SIG s, fr (base s) K 57, ⟨(base s).setWidth 64, 16⟩] [SCR (arg s 6)]) := by
  have hk := kit h
  have fk := hk.fr_addr (d := K) (by decide)
  have hb := hk.below
  have hf := hk.frame
  have e4 := hk.esp4
  have ab : ∀ rd wr, argAddr (u.callEntry.withRegions rd wr) 0 = (base s).setWidth 64 :=
    VG.Proof.Ed25519.X86.Whole.arg_base hu.esp
  simp only [Proof.Ed448.X86.verifyEquationLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hu.esp, hk.slot_arg hu (j := 0) (by decide) hs.a0,
    hk.slot_arg hu (j := 1) (by decide) hs.a1, hk.slot_arg hu (j := 2) (by decide) hs.a2,
    hk.slot_arg hu (j := 3) (by decide) hs.a3, ab, fk]
  exact ⟨trivial, trivial, h.pc, h.sc, hk.fr_scr (by decide), Kit.args_disj (by decide) hk.lo_scr,
    hk.ret_disj hk.lo_scr, h.pk, h.sig, hk.fr_fit (by decide), h.scratch, by omega⟩

theorem eq_covers (s : State) :
    Covers ([PK s, SIG s, fr (base s) K 57, ⟨(base s).setWidth 64, 16⟩] ++ [SCR (arg s 6)])
      (vfRd s ++ Whole.FR (base s) :: vfWr s) := by
  refine covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨_, List.mem_append_left _ (pk_in s), whole _⟩
  · exact .inr ⟨_, List.mem_append_left _ (sig_in s), whole _⟩
  · exact .inl (frame_within _ (by decide))
  · exact .inl (args_within _ (by decide))
  · exact .inr ⟨_, List.mem_append_right _ (scr_in s), whole _⟩

theorem eq_writes (s : State) : ∀ r ∈ [SCR (arg s 6)],
    Whole.Within r (Whole.FR (base s)) ∨ ∃ R ∈ vfWr s, Whole.Within r R := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact .inr ⟨_, scr_in s, whole _⟩

def eq_ready (h : Facts s) (hu : GCtx s g m u) (hs : EqSlots s u) :
    Whole.CallReady Proof.Ed448.X86.verifyEquationLocal (base s) (vfRd s) (vfWr s) u :=
  ⟨_, _, eq_pre h hu hs, eq_covers s, eq_writes s⟩

theorem eq_call {eq : Prog isa} (hE : CalleeOk Proof.Ed448.X86.verifyEquationLocal eq) (h : Facts s)
    (hu : GCtx s g m u) (hs : EqSlots s u) :
    WP isa (.call "vg_ed448_verify_equation" eq) u fun v => GCtx s g m v ∧
      v.gpr .eax = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt u.mem ((arg s 0).setWidth 64) 57)
        (Spec.Ed448.bytesAt u.mem ((arg s 5).setWidth 64) 114)
        (Spec.Ed448.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57) then 1 else 0 := by
  have hk := kit h
  have fk := hk.fr_addr (d := K) (by decide)
  refine Whole.call_ok hu hk.below hE.ok hE.nosp hE.stack (eq_pre h hu hs) (eq_covers s) (eq_writes s)
    fun v hv _ _ ⟨s₂, _, hg, hpost⟩ => ⟨hv, ?_⟩
  simp only [Proof.Ed448.X86.verifyEquationLocal, State.withRegions_mem, arg_withRegions,
    hk.slot_arg hu (j := 0) (by decide) hs.a0, hk.slot_arg hu (j := 1) (by decide) hs.a1,
    hk.slot_arg hu (j := 2) (by decide) hs.a2, fk] at hpost
  rw [← hg .eax (by decide), hpost,
    hk.entry_bytes hu (D := PK s) (hk.away_input (pk_in s) (whole _)).lo (by show 57 ≤ 2 ^ 64; decide),
    hk.entry_bytes hu (D := SIG s) (hk.away_input (sig_in s) (whole _)).lo (by show 114 ≤ 2 ^ 64; decide),
    hk.entry_bytes hu (D := fr (base s) K 57) (lo_fr _ (by decide) (by decide)) (by show 57 ≤ 2 ^ 64; decide)]

theorem eq_step {eq : Prog isa} (hE : CalleeOk Proof.Ed448.X86.verifyEquationLocal eq) (h : Facts s)
    (hc : GCtx s g m t) (ha : Shake.Args (base s) 7 (arg s) m) :
    WP isa (callWith equationArgs "vg_ed448_verify_equation" eq) t fun v => GCtx s g m v ∧
      v.gpr .eax = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt t.mem ((arg s 0).setWidth 64) 57)
        (Spec.Ed448.bytesAt t.mem ((arg s 5).setWidth 64) 114)
        (Spec.Ed448.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57) then 1 else 0 := by
  have hk := kit h
  refine WP.seq (WP.mono (eq_setup h hc ha) fun u ⟨hu, hm, hs⟩ => ?_)
  refine WP.mono (eq_call hE h hu hs) fun v ⟨hv, ho⟩ => ⟨hv, ?_⟩
  have away : ∀ D : Region, (Lo (base s)).Disjoint D → ∀ r ∈ [(⟨(base s).setWidth 64, 24⟩ : Region)], D.Disjoint r :=
    fun D hD r hr => by rw [List.mem_singleton.mp hr]; exact (hD.sub_left (args_lo _ (by decide))).symm
  rw [ho, frame_bytes hm (D := PK s) (away _ (hk.away_input (pk_in s) (whole _)).lo) (by show 57 ≤ 2 ^ 64; decide),
    frame_bytes hm (D := SIG s) (away _ (hk.away_input (sig_in s) (whole _)).lo) (by show 114 ≤ 2 ^ 64; decide),
    frame_bytes hm (D := fr (base s) K 57) (away _ (lo_fr _ (by decide) (by decide))) (by show 57 ≤ 2 ^ 64; decide)]

/-! ## The body -/

/-- What `vg_ed448_verify` returns, for a context below 256 bytes. -/
abbrev result (s : State) (m : Mem) : BitVec 32 :=
  if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt m ((arg s 0).setWidth 64) 57)
    (Spec.Ed448.bytesAt m ((arg s 5).setWidth 64) 114)
    (Spec.Ed448.scalarReduce (Spec.Ed448.hash (Spec.Ed448.bytesAt m ((arg s 1).setWidth 64) (arg s 2).toNat)
      (Spec.Ed448.bytesAt m ((arg s 5).setWidth 64) 57 ++ Spec.Ed448.bytesAt m ((arg s 0).setWidth 64) 57 ++
        Spec.Ed448.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat))) then 1 else 0

theorem body_ok {eq : Prog isa} (hE : CalleeOk Proof.Ed448.X86.verifyEquationLocal eq) (h : Facts s)
    (hc : GCtx s g m t) (ha : Shake.Args (base s) 7 (arg s) m) (hcl : (arg s 2).toNat < 256) :
    WP isa (body eq) t fun u => GCtx s g m u ∧ u.gpr .eax = result s m := by
  have hk := kit h
  refine WP.seq (WP.mono (hk.hdr_ok hc ha (j := 2) (off := HDR) (by decide) hcl (by decide))
    fun t₁ ⟨hc₁, _, hh, _⟩ => ?_)
  refine WP.seq (WP.mono (hash_ok h hc₁ ha hh) fun t₂ ⟨hc₂, hb₂⟩ => ?_)
  refine WP.seq (WP.mono (reduce_step h hc₂ ha) fun t₃ ⟨hc₃, _, hk₃⟩ => ?_)
  refine WP.mono (eq_step hE h hc₃ ha) fun u ⟨hu, ho⟩ => ⟨hu, ?_⟩
  have hb₂' : Spec.Ed448.bytesAt t₂.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114 =
      Spec.Ed448.hash (Spec.Ed448.bytesAt m ((arg s 1).setWidth 64) (arg s 2).toNat)
        (Spec.Ed448.bytesAt m ((arg s 5).setWidth 64) 57 ++ Spec.Ed448.bytesAt m ((arg s 0).setWidth 64) 57 ++
          Spec.Ed448.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat) := hb₂
  rw [ho, hk₃, hb₂', hk.input_bytes (D := PK s) hc₃ (pk_in s) (whole (PK s)) (by show 57 ≤ 2 ^ 64; decide),
    hk.input_bytes (D := SIG s) hc₃ (sig_in s) (whole (SIG s)) (by show 114 ≤ 2 ^ 64; decide)]

theorem body_nosp {eq : Prog isa} (hE : CalleeOk Proof.Ed448.X86.verifyEquationLocal eq) : NoSp (body eq) :=
  nosp_seq (NoSp.of_all (by decide +kernel))
    (nosp_seq
      (nosp_seq (NoSp.of_all (by decide +kernel))
        (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
          (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
            (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
              (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
                (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
                  (nosp_seq (pad_nosp' (NoSp.of_all (by decide +kernel)))
                    (squeeze_nosp' (NoSp.of_all (by decide +kernel))))))))))
      (nosp_seq (nosp_seq (NoSp.of_all (by decide +kernel)) reduce_nosp)
        (nosp_seq (NoSp.of_all (by decide +kernel)) hE.nosp)))

/-! ## The whole function -/

theorem shr8_beq (x : BitVec 32) : (x >>> 8 - 0 == 0) = decide (x.toNat < 256) := by
  have hz : x >>> 8 - (0 : BitVec 32) = x >>> 8 := BitVec.sub_zero _
  rw [hz]
  have e : (x >>> 8).toNat = x.toNat / 256 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases hx : x.toNat < 256
  · have : x >>> 8 = 0 := BitVec.eq_of_toNat_eq (by rw [e, Nat.div_eq_of_lt hx]; rfl)
    simp [this, hx]
  · have : x >>> 8 ≠ 0 := fun h' => hx (by
      have := congrArg BitVec.toNat h'
      rw [e] at this
      change x.toNat / 256 = 0 at this
      omega)
    rw [beq_eq_false_iff_ne.mpr this]
    simp [hx]

/-- The check of `ctxlen`: ZF is `ctxlen < 256`. -/
theorem check_ok {s : State} (h : Facts s) (hrd : s.rd = vfRd s) :
    WP isa (.block check) s fun t => t.gpr .esp = s.gpr .esp ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧ t.zf = some (decide ((arg s 2).toNat < 256)) := by
  unfold check
  refine wp_ldm (b := .esp) (o := 12) rfl ?_ fun s1 v1 => wp_shr (n := 8) (by decide) fun s2 v2 _ =>
    wp_cmpi fun s3 v3 _ hz => WP.block_nil ⟨?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩
  · rw [hrd]
    exact ⟨ARGS s 7, List.mem_append_left _ (args_in s),
      Shake.args_contains (n := 7) (by have := h.above; omega) (j := 2) (by decide)⟩
  · rw [v3.gpr, v2.other _ (by decide), v1.other _ (by decide)]
  · rw [v3.mem, v2.mem, v1.mem]
  · rw [v3.rd, v2.rd, v1.rd]
  · rw [v3.wr, v2.wr, v1.wr]
  · rw [v3.gpr, v2.other r hr, v1.other r hr]
  · rw [hz, v2.gpr, v1.gpr]
    exact congrArg some (shr8_beq (arg s 2))

/-- The frame and the body, from the state after the check. -/
theorem framed_ok {eq : Prog isa} (hE : CalleeOk Proof.Ed448.X86.verifyEquationLocal eq) {s t : State}
    (hp : vfLocal.pre s) (he : t.gpr .esp = s.gpr .esp) (hm : t.mem = s.mem) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hg : ∀ r, r ≠ .eax → t.gpr r = s.gpr r) (hcl : (arg s 2).toNat < 256) :
    WP isa (.frame (.push (List.replicate 64 .eax)) (body eq) (.pop .edx 64)) t fun u =>
      abiPreserved s u ∧ u.gpr .eax = result s s.mem := by
  have h := facts hp
  have eb : base t = base s := by simp only [base, he]
  have hb : 280 ≤ (t.gpr .esp).toNat := by rw [he]; exact h.below
  have c0 := push_ctx (s := t) (hrd.trans hp.1) (hwr.trans hp.2.1) hb
  rw [eb] at c0
  have ha : Shake.Args (base s) 7 (arg s) t.mem := by rw [hm]; exact args_val s 7
  refine WP.frame (rs := List.replicate 64 .eax) (by simp) (by simp) (by decide)
    (by simp only [List.length_replicate]; omega) (body_nosp hE)
    (WP.mono (body_ok hE h c0 ha hcl) fun u ⟨hu, ho⟩ => ⟨?_, ?_⟩)
  · have hu' : VG.Proof.Ed25519.X86.Whole.Ctx (base t) t.gpr t.mem (vfRd s) (vfWr s) u := by
      rw [eb]; exact hu
    refine Shake.abi_of (s' := t) (fun r hr => hg r (by rintro rfl; simp [calleeSaved] at hr)) hm
      (pop_abi (by decide) hb hu' fun R hR => ?_)
    have := ret_out h R hR
    simp only [RET, he]
    exact this
  · rw [popped_gpr _ _ _ (by decide) (by decide), ho, hm]

theorem verify_ok {eq : Prog isa} (hE : CalleeOk Proof.Ed448.X86.verifyEquationLocal eq) {s : State}
    (hp : vfLocal.pre s) : WP isa (code eq) s fun t => abiPreserved s t ∧ vfLocal.post s t := by
  have h := facts hp
  unfold code
  refine WP.seq (WP.mono (check_ok h hp.1) fun t ⟨he, hm, hrd, hwr, hg, hz⟩ => ?_)
  refine WP.ite _ hz (fun hcl => ?_) (fun hcl => ?_)
  · have hcl' : (arg s 2).toNat < 256 := of_decide_eq_true hcl
    refine WP.mono (framed_ok hE hp he hm hrd hwr hg hcl') fun u ⟨ha, ho⟩ => ⟨ha, ?_⟩
    change u.gpr .eax = _
    have hl : (Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat).length = (arg s 2).toNat := by
      simp [Spec.Ed448.bytesAt]
    rw [ho, Spec.Ed448.verify, bytesAt_take57, hl]
    simp only [show (arg s 2).toNat ≤ 255 by omega, decide_true, Bool.true_and]
  · have hcl' : ¬ (arg s 2).toNat < 256 := of_decide_eq_false hcl
    refine wp_movi fun u vu => WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · rw [vu.other r (by rintro rfl; simp [calleeSaved] at hr), hg r (by rintro rfl; simp [calleeSaved] at hr)]
    · rw [vu.mem, hm]
    · change u.gpr .eax = _
      have hl : (Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat).length = (arg s 2).toNat := by
        simp [Spec.Ed448.bytesAt]
      rw [vu.gpr, Spec.Ed448.verify, hl]
      simp only [show ¬ (arg s 2).toNat ≤ 255 by omega, decide_false, Bool.false_and]
      rfl

end VG.Proof.Ed448.X86.Verify
