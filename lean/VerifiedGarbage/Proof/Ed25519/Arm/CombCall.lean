module

public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTMul
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory

/-! The shared comb's call spills `r12` before a possible linker veneer and saves
its own return address beyond the outer function's headers. The inline kernel's
narrower frame proves that the nested calls preserve this return address. -/

@[expose] public section
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev combReturnRegion (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 combReturn, 4⟩
abbrev combRegions (b : BitVec 32) : List Region := combReturnRegion b :: pointRegions b

structure CombKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest powersClob s t
  frame : Frame (combRegions b) s.mem t.mem

theorem PointKeep.toCombKeep {b : BitVec 32} {s t : State} (h : PointKeep b s t) : CombKeep b s t :=
  ⟨h.rest, h.frame.mono fun _ hr => List.mem_cons_of_mem _ hr⟩
theorem CombKeep.ctx {b : BitVec 32} {s t : State} (h : CombKeep b s t) (hc : Ctx b s) : Ctx b t :=
  hc.of_rest h.rest (by decide)
theorem CombKeep.trans {b : BitVec 32} {s t u : State} (h : CombKeep b s t) (k : CombKeep b t u) :
    CombKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩
theorem CombKeep.word {b : BitVec 32} {s t : State} (h : CombKeep b s t)
    (d : Nat) (hd : d = 48 ∨ 7776 ≤ d) (hn : d + 4 ≤ 8192)
    (hs : d + 4 ≤ combReturn ∨ combReturn + 4 ≤ d := by decide) :
    t.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 = s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    simp only [combRegions, pointRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ hs (by omega_using [hn]) (by decide)
    all_goals exact Offset.disjoint _ (by omega_using [hd]) (by omega_using [hn]) (by decide)
theorem CombKeep.table {b : BitVec 32} {s t : State} (h : CombKeep b s t) {d : Nat}
    (hd : 7776 ≤ d) (hn : d + 128 ≤ combReturn) : tablePoint t.mem b d = tablePoint s.mem b d := by
  refine tablePoint_frame h.frame fun r hr => ?_
  simp only [combRegions, pointRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ (.inl hn) (by simp only [combReturn] at hn; omega_using [hn]) (by decide)
  all_goals exact Offset.disjoint _ (.inr (by omega_using [hd])) (by simp only [combReturn] at hn; omega_using [hn]) (by decide)

/-- A write to either temporary word leaves all field slots bounded. -/
theorem combTemp_lim {b : BitVec 32} {m m' : Mem} {d : Nat}
    (hd : d = combInput ∨ d = combReturn)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 d, 4⟩] m m') (hl : AllLim m b) : AllLim m' b := by
  intro sl
  exact (env_frame hf sl (slot_apart sl (by
    obtain ⟨lo, hi⟩ := slot_range sl
    rcases hd with rfl | rfl <;> simp only [combInput, combReturn, ACC] at * <;> omega_using [lo, hi])
    (by rcases hd with rfl | rfl <;> decide))).2 (hl sl)

/-- Save a workspace word without changing registers. -/
theorem combStore_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (r : Reg) (d : Nat)
    (hd : d < 4096) (hn : d + 4 ≤ 8192) :
    WP isa (.block [.str r .r0 d]) s fun t => Rest [] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 d, 4⟩] s.mem t.mem ∧
      t.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 d) (s.gpr r) := by
  refine wp_str (a := State.addr b + BitVec.ofNat 64 d) hd (by rw [hc.r0]; exact hc.ptr_addr (by omega_using [hn])) (in_base hc.wr hn (by omega_using [hn])) fun t ht => WP.block_nil ?_
  refine ⟨ht.rest [], ?_, ht.mem⟩
  rw [ht.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 4)

/-- Save the helper's link and recover the input pointer after the call. -/
theorem combEnter_ok {b P : BitVec 32} {s : State} (hc : Ctx b s)
    (hp : s.mem.readW (State.addr b + BitVec.ofNat 64 combInput) 32 = P) :
    WP isa (.block (scratchAddr combReturn ++ ([.str .lr .r12 0, .ldr .r12 .r0 combInput] : List Instr))) s fun t =>
      Rest [.r12] s t ∧ Frame [combReturnRegion b] s.mem t.mem ∧
      t.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 combReturn) (s.gpr .lr) ∧ t.gpr .r12 = P := by
  refine WP.append (scratchAddr_ok hc combReturn (by decide)) fun u ⟨ur, um, up⟩ => ?_
  refine wp_str (a := State.addr b + BitVec.ofNat 64 combReturn) (by decide)
    (by rw [up]; exact (congrArg State.addr (BitVec.add_zero _)).trans (hc.ptr_addr (by decide)))
    (by rw [ur.wr]; exact in_base hc.wr (by decide) (by decide)) fun v hv => ?_
  have vm : v.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 combReturn) (s.gpr .lr) := by
    rw [hv.mem, um, ur.gpr _ (by decide)]
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 combInput) (by decide)
    (by rw [hv.gpr, ur.gpr _ (by decide), hc.r0]; exact hc.ptr_addr (by decide))
    (by rw [hv.rd, hv.wr, ur.rd, ur.wr]; exact in_base (List.mem_append_right _ hc.wr) (by decide) (by decide))
    fun t ht => WP.block_nil ?_
  refine ⟨ur.trans ((hv.rest [.r12]).trans (ht.rest (by decide))), ?_, ht.mem.trans vm, ?_⟩
  · rw [ht.mem, vm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 4)
  · rw [ht.gpr, vm, Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide)]
    exact hp

/-- Recover the helper's link from its protected workspace word. -/
theorem combLeave_ok {b : BitVec 32} {s : State} (hc : Ctx b s) :
    WP isa (.block (scratchAddr combReturn ++ ([.ldr .lr .r12 0] : List Instr))) s fun t =>
      Rest [.r12, .lr] s t ∧ t.mem = s.mem ∧
      t.gpr .lr = s.mem.readW (State.addr b + BitVec.ofNat 64 combReturn) 32 := by
  refine WP.append (scratchAddr_ok hc combReturn (by decide)) fun u ⟨ur, um, up⟩ => ?_
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 combReturn) (by decide)
    (by rw [up]; exact (congrArg State.addr (BitVec.add_zero _)).trans (hc.ptr_addr (by decide)))
    (by rw [ur.rd, ur.wr]; exact in_base (List.mem_append_right _ hc.wr) (by decide) (by decide))
    fun t ht => WP.block_nil ⟨(ur.mono (by decide)).trans (ht.rest (by decide)), ht.mem.trans um, ?_⟩
  rw [ht.gpr, um]

/-- Reading the scalar is unchanged by writes confined to the workspace. -/
theorem combBytes_frame {b P : BitVec 32} {m m' : Mem} {rs : List Region}
    (hf : Frame rs m m') (hsub : ∀ r ∈ rs, r.Sub ⟨State.addr b, 8192⟩)
    (hsep : (⟨State.addr P, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
    Spec.Ed25519.bytesAt m' (State.addr P) 32 = Spec.Ed25519.bytesAt m (State.addr P) 32 := by
  unfold Spec.Ed25519.bytesAt
  exact List.map_congr_left fun n hn => hf.bytes (R := ⟨State.addr P, 32⟩)
    (fun r hr => hsep.sub_right (hsub r hr)) (show (32 : Nat) ≤ 2 ^ 64 by decide) (List.mem_range.mp hn)

/-- The call's two temporary words are separate from either permitted scalar input. -/
theorem combInput_bytes_frame {s : State} {b P : BitVec 32} {m m' : Mem} {d : Nat}
    (hc : Ctx b s) (hd : d = combInput ∨ d = combReturn)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 d, 4⟩] m m') (hs : CombInputOk b P) :
    Spec.Ed25519.bytesAt m' (State.addr P) 32 = Spec.Ed25519.bytesAt m (State.addr P) 32 := by
  rcases hs with hs | rfl
  · exact combBytes_frame hf (by
      intro r hr; rw [List.mem_singleton.mp hr]
      exact Offset.sub_base _ (by rcases hd with rfl | rfl <;> decide)) hs
  · unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun n hn => ?_
    rw [addr_add (by simp only [SCAL]; omega_using [hc.fit])]
    exact hf.bytes (R := scalR b) (by
      intro r hr; rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by rcases hd with rfl | rfl <;> decide) (by decide)
        (by rcases hd with rfl | rfl <;> decide))
      (show (32 : Nat) ≤ 2 ^ 64 by decide) (List.mem_range.mp hn)

/-- The function preserves its incoming link even though the comb calls field functions. -/
theorem combMultiplyFn_ok {umaal : Bool} {s : State} {b P T : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (hp : s.mem.readW (State.addr b + BitVec.ofNat 64 combInput) 32 = P) (hfit : P.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ k < 32, InRegions (s.rd ++ s.wr) (State.addr P + BitVec.ofNat 64 k) 1)
    (hsep : CombInputOk b P)
    (hT : TblAt s T) (hsym : s.syms combSym = T) (apart : (TBL T).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa (combMultiplyFn umaal) s fun t => CombKeep b s t ∧ t.gpr .lr = s.gpr .lr ∧ AllLim t.mem b ∧
      Rep (point (env t.mem b) 0 1 2 3)
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr P) 32) • baseAff) := by
  rw [combMultiplyFn]
  refine WP.seq (WP.mono_syms (combEnter_ok hc hp) fun u ⟨ur, uf, um, up⟩ syu => ?_)
  have hcu := hc.of_rest ur (by decide)
  have sub : ∀ r ∈ [combReturnRegion b], r.Sub ⟨State.addr b, 8192⟩ := by
    intro r hr; rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)
  have lu := combTemp_lim (.inr rfl) uf hl
  have tu : TblAt u T := hT.of_frame (by rw [ur.rd, ur.wr]) uf fun r hr => apart.sub_right (sub r hr)
  have ru : ∀ k < 32, InRegions (u.rd ++ u.wr) (State.addr P + BitVec.ofNat 64 k) 1 := by
    rw [ur.rd, ur.wr]; exact hr
  have bytes := combInput_bytes_frame hc (.inr rfl) uf hsep
  refine WP.seq (WP.mono (combMultiplyInline_ok hcu lu up hfit ru hsep tu (by rw [syu]; exact hsym) apart)
    fun v ⟨vk, vl, vr⟩ => ?_)
  refine WP.mono (combLeave_ok (vk.ctx hcu)) fun t ⟨tr, tm, tl⟩ => ?_
  have uk : CombKeep b s u := ⟨ur.mono (by decide), uf.mono fun _ hr => by
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..⟩
  have vt : CombKeep b v t := ⟨tr.mono (by decide), by rw [tm]; exact Frame.refl _ _⟩
  refine ⟨uk.trans (vk.toCombKeep.trans vt), ?_, by rw [tm]; exact vl, ?_⟩
  · rw [tl, vk.word combReturn (.inr (by decide)) (by decide), um, Mem.readW_writeW_self32]
  · rw [tm]; rw [bytes] at vr; exact vr

/-- The spill and call have the inline comb's mathematical result. -/
theorem combMultiply_ok {umaal : Bool} {s : State} {b P T : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (hp : s.gpr .r12 = P) (hfit : P.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ k < 32, InRegions (s.rd ++ s.wr) (State.addr P + BitVec.ofNat 64 k) 1)
    (hsep : CombInputOk b P)
    (hT : TblAt s T) (hsym : s.syms combSym = T) (apart : (TBL T).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa (combMultiply umaal) s fun t => CombKeep b s t ∧ AllLim t.mem b ∧
      Rep (point (env t.mem b) 0 1 2 3)
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr P) 32) • baseAff) := by
  rw [combMultiply]
  refine WP.seq (WP.mono_syms (combStore_ok hc .r12 combInput (by decide) (by decide))
    fun u ⟨ur, uf, um⟩ syu => ?_)
  have hcu := hc.of_rest ur (by decide)
  have sub : ∀ r ∈ [(⟨State.addr b + BitVec.ofNat 64 combInput, 4⟩ : Region)], r.Sub ⟨State.addr b, 8192⟩ := by
    intro r hr; rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)
  have lu := combTemp_lim (.inl rfl) uf hl
  have tu : TblAt u T := hT.of_frame (by rw [ur.rd, ur.wr]) uf fun r hr => apart.sub_right (sub r hr)
  have ce : Rest powersClob u u.callEntry := ⟨fun r hr => State.callEntry_gpr _ (by
    revert hr; cases r <;> decide), rfl, rfl, rfl⟩
  have hce := hcu.of_rest ce (by decide)
  have ru : ∀ k < 32, InRegions (u.callEntry.rd ++ u.callEntry.wr) (State.addr P + BitVec.ofNat 64 k) 1 := by
    rw [State.callEntry_rd, State.callEntry_wr, ur.rd, ur.wr]; exact hr
  have pu : u.callEntry.mem.readW (State.addr b + BitVec.ofNat 64 combInput) 32 = P := by
    rw [State.callEntry_mem, um, Mem.readW_writeW_self32, hp]
  obtain ⟨tt, t, te, tk, tl, lt, rt⟩ := combMultiplyFn_ok hce lu pu hfit ru hsep ⟨tu.fit, tu.rd, tu.words⟩ (by change u.syms combSym = T; rw [syu]; exact hsym) apart
  have uk : CombKeep b s u := (PointKeep.of_small ur (by decide) uf (by decide) (by decide)).toCombKeep
  have ck : CombKeep b u u.callEntry := ⟨ce, Frame.refl _ _⟩
  refine ⟨_, t, Exec.call (call_callEntry u) te ?_, uk.trans (ck.trans tk), lt, ?_⟩
  · simp only [isa, ret, tl, ite_true]
  · rw [State.callEntry_mem, combInput_bytes_frame hc (.inl rfl) uf hsep] at rt; exact rt

end VG.Proof.Ed25519.Arm
