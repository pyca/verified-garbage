module

public import VerifiedGarbage.Proof.Ffdh.X86.Entry
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Stage
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.CallBody
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape

/-!
# FFDH on i686: `prepare .wide`, called

`prepCall` calls `prepare .wide` (`vg_ffdh_prepare_wide`) in a frame of its own of 76 bytes, which it
fills with a copy of the caller's synthetic arguments (`copyArg`): the operations read them at `esp`.
The call changes the 176 bytes below the caller's `esp` (its return address, the frame and the
operations' 96 bytes) and the working space's ranges of `prepare` (`prepCall_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Impl.Ffdh.X86

/-- The first `c` synthetic arguments copied into the frame at `P` (`esp`) from the words `g`
above it, keeping everything else but `eax`. -/
theorem copyArgs_ok {t : State} {g : Nat → BitVec 32} {P : Addr}
    (hP : (t.gpr .esp).setWidth 64 = P) (hesp : (t.gpr .esp).toNat + 76 ≤ 2 ^ 32)
    (hfr : (⟨P, 76⟩ : Region) ∈ t.wr)
    (hr : ∀ j < 18, readSrc t (.mem (at_ .esp (84 + 4 * j))) = some (g j))
    (hargs : ∀ j < 18, Region.Disjoint ⟨t.ea (at_ .esp (84 + 4 * j)), 4⟩ ⟨P, 76⟩) :
    ∀ c, c ≤ 18 → ∀ {is : List Instr} {Q : State → Prop},
      (∀ u, Keeps [.eax] t u → Frame [⟨P, 76⟩] t.mem u.mem →
        (∀ i < c, u.mem.readW (slotAddr P i) 32 = g i) → WP isa (.block is) u Q) →
      WP isa (.block ((List.range c).flatMap copyArg ++ is)) t Q
  | 0, _, _, _, k => k t (Keeps.refl _ _) (Frame.refl _ _) fun _ h => absurd h (by omega_using [])
  | c + 1, hc, is, Q, k => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine copyArgs_ok hP hesp hfr hr hargs c (by omega_using [hc]) fun u K F S => ?_
    obtain hr' : readSrc u (.mem (at_ .esp (84 + 4 * c))) = some (g c) := by
      rw [← hr c (by omega_using [hc])]
      exact src_frame K (by decide) F fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hargs c (by omega_using [hc])
    unfold copyArg
    simp only [List.cons_append, List.nil_append]
    refine wp_movS hr' fun v U _ => ?_
    obtain Kv : Keeps [.eax] u v := U.keeps
    obtain Pv : (v.gpr .esp).setWidth 64 = P := by rw [Kv.1 _ (by decide), K.1 _ (by decide), hP]
    obtain ev' : (v.gpr .esp).toNat + 76 ≤ 2 ^ 32 := by rw [Kv.1 _ (by decide), K.1 _ (by decide)]; exact hesp
    obtain wv : (⟨P, 76⟩ : Region) ∈ v.wr := by rw [Kv.2.2, K.2.2]; exact hfr
    obtain ⟨ea, wr⟩ := frame76_store Pv ev' wv (i := c) (by omega_using [hc])
    refine wp_storeS ea wr fun w M => ?_
    refine k w ((K.trans Kv).trans ((M.keeps []).mono (by decide))) ?_ fun i hi => ?_
    · rw [M.mem, U.mem]
      exact F.trans (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega_using [hc]) (by omega_using [hc])))
    · rw [M.mem, U.mem]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [frame76_other _ _ _ (by omega_using [hi]) (by omega_using [hc]) (by omega_arith), S i hi]
      · rw [Mem.readW_writeW_self32, U.gpr]

/-- The 176 bytes below `sp`, from their base: the callee's 96 below its `esp`, then its frame of 76. -/
theorem below176_parts {sp : BitVec 32} (low : 176 ≤ sp.toNat) :
    ((sp - BitVec.ofNat 32 80).setWidth 64 = (sp - BitVec.ofNat 32 176).setWidth 64 + BitVec.ofNat 64 96) ∧
      below (sp - BitVec.ofNat 32 80) 96 = ⟨(sp - BitVec.ofNat 32 176).setWidth 64, 96⟩ := by
  have := sp.isLt
  refine ⟨BitVec.eq_of_toNat_eq ?_, ?_⟩
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_arith
  · simp only [below]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith

/-- The callee's inputs: those of the caller, read from the frame of the copied arguments at `esp`,
80 bytes below the caller's. -/
theorem in_callee {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat}
    {args : Nat → BitVec 32} {s f : State} (h : In Ex base bytes len args s)
    (RF : RoomF (s.gpr .esp) base bytes) (ef : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 80)
    (edi : f.gpr .edi = s.gpr .edi) (rd : f.rd = s.rd)
    (wr : f.wr = ⟨(f.gpr .esp).setWidth 64, 76⟩ :: s.wr)
    (vals : ∀ i < 18, f.mem.readW (slotAddr ((f.gpr .esp).setWidth 64) i) 32 = args i) :
    In (fun _ _ => True) base bytes len args f := by
  have low := RF.low
  have top := h.top
  have hE := (s.gpr .esp).isLt
  have nw := h.scratch.nowrap
  have bl := h.bytes_lt
  obtain ⟨e1, e2⟩ := below176_parts low
  obtain fN : (f.gpr .esp).toNat = (s.gpr .esp).toNat - 80 := by
    rw [ef]; exact VG.X86.sub_toNat (by omega_using [low])
  generalize hX : (s.gpr .esp - BitVec.ofNat 32 176).setWidth 64 = X at e1 e2
  obtain b176 : below (s.gpr .esp) 176 = ⟨X, 176⟩ := by rw [← hX]
  obtain fP : (f.gpr .esp).setWidth 64 = X + BitVec.ofNat 64 96 := by rw [ef, e1]
  obtain frameSub : Region.Sub ⟨(f.gpr .esp).setWidth 64, 76⟩ (below (s.gpr .esp) 176) := by
    rw [fP, b176]
    have := Offset.sub X (d := 96) (n := 76) (e := 0) (k := 176) (by decide) (by decide)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  obtain frameWs : Region.Disjoint ⟨(f.gpr .esp).setWidth 64, 76⟩ ⟨base, bytes⟩ := RF.apart.sub_left frameSub
  obtain belowWs : Region.Disjoint (below (f.gpr .esp) 96) ⟨base, bytes⟩ := by
    rw [ef, e2]
    exact RF.apart.sub_left (by rw [b176]; exact Region.sub_prefix (by decide))
  obtain SA : ∀ i < 18, VG.Proof.Dsa.X86.stackAddress f i = slotAddr ((f.gpr .esp).setWidth 64) i :=
    fun i hi => addr_eq (by omega_using [fN, hi, top])
  refine ⟨⟨by rw [edi]; exact h.scratch.edi, by rw [wr]; exact List.mem_cons_of_mem _ h.scratch.wr, nw, ?_⟩,
    h.lower, h.upper, fun i hi => ⟨⟨?_, ?_⟩, ?_⟩, h.outLen, ⟨by rw [fN]; omega_using [low], belowWs⟩,
    by rw [fN]; omega_using [top], h.need, h.hbase, h.hbytes, trivial⟩
  · refine VG.Proof.Weierstrass.X86.stkOk_of (z := 96) (by decide) (by rw [fN]; omega_using [low]) nw
      (by have := h.need; simp only [CrtRt.need, Impl.Bignum.X86.CrtRt.numBase] at this; omega_using [this]) ?_
    have e := belowWs
    simp only [below] at e
    rwa [VG.X86.Taint.sub_setWidth (by rw [fN]; omega_using [low])] at e
  · rw [SA i hi, rd, wr]
    exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..),
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [SA i hi]; exact frameWs.sub_left (Offset.sub_base _ (by omega_using [hi]))
  · show f.mem.readW (VG.Proof.Dsa.X86.stackAddress f i) 32 = args i
    rw [SA i hi]; exact vals i hi

/-- The callee's regions below `sp`, as offsets of the base of the 176 bytes below it. -/
theorem callee_addrs {sp : BitVec 32} (low : 176 ≤ sp.toNat) :
    (sp - 4).setWidth 64 = (sp - BitVec.ofNat 32 176).setWidth 64 + BitVec.ofNat 64 172 ∧
      (sp - 4 - BitVec.ofNat 32 76).setWidth 64 = (sp - BitVec.ofNat 32 176).setWidth 64 + BitVec.ofNat 64 96 ∧
      sp.setWidth 64 = (sp - BitVec.ofNat 32 176).setWidth 64 + BitVec.ofNat 64 176 := by
  have := sp.isLt
  rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl]
  refine ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_⟩ <;>
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega_arith

/-- What the call writes, within the 176 bytes below `sp`: its return address, its frame and the 96 bytes
below the frame, and the return address apart from the frame. -/
theorem callee_regions {sp : BitVec 32} (low : 176 ≤ sp.toNat) :
    Region.Sub ⟨(sp - 4).setWidth 64, 4⟩ (below sp 176) ∧ Region.Sub (below (sp - 4) 76) (below sp 176) ∧
      Region.Sub (below (sp - 4 - BitVec.ofNat 32 76) 96) (below sp 176) ∧
      Region.Disjoint ⟨(sp - 4).setWidth 64, 4⟩ (below (sp - 4) 76) ∧
      Region.Disjoint ⟨(sp - 4).setWidth 64, 4⟩ (below (sp - 4 - BitVec.ofNat 32 76) 96) := by
  obtain ⟨a4, a80, a0⟩ := callee_addrs low
  generalize hX : (sp - BitVec.ofNat 32 176).setWidth 64 = X at a4 a80 a0
  obtain b176 : below sp 176 = ⟨X + BitVec.ofNat 64 0, 176⟩ := by rw [← hX, BitVec.add_zero]
  obtain b76 : below (sp - 4) 76 = ⟨X + BitVec.ofNat 64 96, 76⟩ := by simp only [below]; rw [a80]
  obtain e176 : (sp - 4 - BitVec.ofNat 32 76 - BitVec.ofNat 32 96).setWidth 64 = X + BitVec.ofNat 64 0 := by
    rw [← hX, BitVec.add_zero]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have := sp.isLt
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl]
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith
  obtain b96 : below (sp - 4 - BitVec.ofNat 32 76) 96 = ⟨X + BitVec.ofNat 64 0, 96⟩ := by
    simp only [below]; rw [e176]
  rw [b176, b76, b96, a4]
  exact ⟨Offset.sub X (by decide) (by decide), Offset.sub X (by decide) (by decide),
    Offset.sub X (by decide) (by decide), Offset.disjoint X (by decide) (by decide) (by decide),
    Offset.disjoint X (by decide) (by decide) (by decide)⟩

/-- Changes within regions in the 176 bytes below `sp`, as a stage's. -/
theorem frameF_of_sub {base : Addr} {sp : BitVec 32} {ws : List (Nat × Nat)} {rs : List Region} {m m' : Mem}
    (F : Frame rs m m') (h : ∀ r ∈ rs, Region.Sub r (below sp 176)) : Frame (frameF base sp ws) m m' :=
  F.sub fun r hr => ⟨_, List.mem_cons_self .., h r hr⟩

/-- The operations' changes, from a stack pointer whose 96 bytes below it are within the 176 below `sp`. -/
theorem frameF_of_frameR {base : Addr} {sp sp' : BitVec 32} {ws : List (Nat × Nat)} {m m' : Mem}
    (F : Frame (frameR base sp' ws) m m') (h : Region.Sub (below sp' 96) (below sp 176)) :
    Frame (frameF base sp ws) m m' :=
  F.sub fun r hr => by
    simp only [frameR, List.mem_cons, List.mem_map] at hr
    rcases hr with rfl | ⟨p, hp, rfl⟩
    · exact ⟨_, List.mem_cons_self .., h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, hp, rfl⟩)), fun _ h => h⟩

theorem prepBody_noSp :
    NoSp (.seq (.block ((List.range 18).flatMap copyArg)) (prepare .wide) : Prog isa) :=
  NoSp.of_all (by rsa_stack_shape)

/-- What `prepCall` leaves: `prepCtx_ok`'s, with the changes within a stage's. -/
abbrev PrepPost (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (s u : State) : Prop :=
  CtxOk Ex base bytes len args .wide (safeM (sv s.mem base len .wide 0)) u ∧ sv u.mem base len .wide 3 = 1 ∧
    sv u.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % safeM (sv s.mem base len .wide 0) ∧
    Frame (frameF base (s.gpr .esp) (prepR len .wide)) s.mem u.mem ∧
    Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- A number of the working space, through changes in the 176 bytes below `sp`. -/
theorem val32_below {sp : BitVec 32} (RF : RoomF sp base bytes) (nw : base.toNat + bytes ≤ 2 ^ 32)
    {rs : List Region} {m m' : Mem} (F : Frame rs m m') (hr : ∀ r ∈ rs, Region.Sub r (below sp 176))
    {d k : Nat} (hd : d + 4 * k ≤ bytes) : val32 m' base d k = val32 m base d k :=
  frameF_val32 (ws := []) (frameF_of_sub F hr) RF nw hd (fun _ h => nomatch h) (fun _ h => nomatch h)

/-- `PrepPost` holds through changes in the 176 bytes below `esp`. -/
theorem PrepPost.below {s u : State} (P : PrepPost Ex base bytes len args s u) (RF : RoomF (s.gpr .esp) base bytes)
    {rs : List Region} {m : Mem} (F : Frame rs u.mem m) (hr : ∀ r ∈ rs, Region.Sub r (below (s.gpr .esp) 176))
    (un : Nat → BitVec 32) : PrepPost Ex base bytes len args s { u with mem := m, unknowns := un } := by
  obtain ⟨C, one, R2, Fu, K⟩ := P
  have nw := C.inp.scratch.nowrap
  have sp : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  obtain K' : Keeps [] u { u with mem := m, unknowns := un } := ⟨fun _ _ => rfl, rfl, rfl⟩
  obtain sv_eq : ∀ j, j ≤ 27 → sv m base len .wide j = sv u.mem base len .wide j := fun j hj => by
    have := C.inp.slot_fit .wide hj
    have bw := bc_eq_cwc len .wide
    have est : st len .wide = 2 * bc len .wide + 32 := rfl
    exact val32_below RF nw F hr (by omega_arith)
  refine ⟨⟨in_keepFF C.inp K' (by decide) (by decide) (by rw [sp]; exact RF) (ws := [])
      (by rw [sp]; exact frameF_of_sub F hr) (fun _ h => nomatch h), ?_, C.gt, C.odd, ?_⟩,
    by show sv m _ _ _ _ = _; rw [sv_eq 3 (by decide)]; exact one,
    by show sv m _ _ _ _ = _; rw [sv_eq 4 (by decide)]; exact R2,
    Fu.trans (frameF_of_sub F hr), K⟩
  · show sv m _ _ _ _ = _; rw [sv_eq 0 (by decide)]; exact C.mod
  · show (_ * w32 m base invOff + 1) % _ = _
    obtain e : w32 m base invOff = w32 u.mem base invOff := by
      have := val32_below (d := invOff) (k := 1) RF nw F hr (by
        have := C.inp.need; simp only [invOff, CrtRt.need, Impl.Bignum.X86.CrtRt.numBase] at this ⊢; omega_arith)
      simpa only [val32, w32, Nat.mul_zero, Nat.add_zero] using this
    rw [e]; exact C.inv

/-- The return address and the frame, apart from the caller's arguments above `sp`. -/
theorem callee_args_apart {sp : BitVec 32} (low : 176 ≤ sp.toNat) (top : sp.toNat + 76 ≤ 2 ^ 32) {j : Nat}
    (hj : j < 18) :
    Region.Disjoint ⟨addr sp (4 + 4 * j), 4⟩ ⟨(sp - 4).setWidth 64, 4⟩ ∧
      Region.Disjoint ⟨addr sp (4 + 4 * j), 4⟩ ⟨(sp - 4 - BitVec.ofNat 32 76).setWidth 64, 76⟩ := by
  obtain ⟨a4, a80, a0⟩ := callee_addrs low
  have e : addr sp (4 + 4 * j) = sp.setWidth 64 + BitVec.ofNat 64 (4 + 4 * j) :=
    addr_eq (by omega_using [top, hj])
  rw [e, a4, a80, a0, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact ⟨Offset.disjoint _ (by omega_using []) (by omega_using [hj]) (by decide),
    Offset.disjoint _ (by omega_using []) (by omega_using [hj]) (by decide)⟩

/-- The callee's state after the call and the allocation of its frame. -/
theorem callee_entry {s t0 : State} (ht0 : allocFrame argsFrame s.callEntry = t0) (low : 176 ≤ (s.gpr .esp).toNat) :
    t0.gpr .esp = s.gpr .esp - 4 - BitVec.ofNat 32 76 ∧ t0.gpr .esp = s.gpr .esp - BitVec.ofNat 32 80 ∧
      (t0.gpr .esp).toNat = (s.gpr .esp).toNat - 80 ∧ t0.wr = ⟨(t0.gpr .esp).setWidth 64, 76⟩ :: s.wr ∧
      t0.rd = s.rd ∧ t0.mem = s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.unknowns 0) ∧
      (∀ r, r ≠ .esp → t0.gpr r = s.gpr r) := by
  obtain t0esp : t0.gpr .esp = s.gpr .esp - 4 - BitVec.ofNat 32 76 := by
    rw [← ht0, allocFrame_esp, State.callEntry_esp]; rfl
  obtain t0esp80 : t0.gpr .esp = s.gpr .esp - BitVec.ofNat 32 80 := by
    rw [t0esp, BitVec.sub_sub]; rfl
  obtain t0N : (t0.gpr .esp).toNat = (s.gpr .esp).toNat - 80 := by
    rw [t0esp80]; exact VG.X86.sub_toNat (by omega_using [low])
  obtain t0wr : t0.wr = ⟨(t0.gpr .esp).setWidth 64, 76⟩ :: s.wr := by
    rw [← ht0, allocFrame_wr, State.callEntry_wr, allocFrame_esp]; rfl
  obtain t0rd : t0.rd = s.rd := by rw [← ht0, allocFrame_rd, State.callEntry_rd]
  obtain t0mem : t0.mem = s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.unknowns 0) := by
    rw [← ht0, allocFrame_mem]; rfl
  obtain t0gpr : ∀ r, r ≠ .esp → t0.gpr r = s.gpr r := fun r hr => by
    rw [← ht0, allocFrame_gpr _ _ hr, State.callEntry_gpr _ hr]
  exact ⟨t0esp, t0esp80, t0N, t0wr, t0rd, t0mem, t0gpr⟩

/-- The copy of the caller's arguments into the callee's frame. -/
theorem callee_copy {s t0 : State} (h : In Ex base bytes len args s) (RF : RoomF (s.gpr .esp) base bytes)
    (ht0 : allocFrame argsFrame s.callEntry = t0) {Q : State → Prop}
    (k : ∀ u, Keeps [.eax] t0 u → Frame [⟨(t0.gpr .esp).setWidth 64, 76⟩] t0.mem u.mem →
      (∀ i < 18, u.mem.readW (slotAddr ((t0.gpr .esp).setWidth 64) i) 32 = args i) → Q u) :
    WP isa (.block ((List.range 18).flatMap copyArg)) t0 Q := by
  have low := RF.low
  have top := h.top
  obtain ⟨t0esp, -, t0N, t0wr, t0rd, t0mem, -⟩ := callee_entry ht0 low
  obtain Fret : Frame [⟨(s.gpr .esp - 4).setWidth 64, 4⟩] s.mem t0.mem := by
    rw [t0mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  -- The caller's arguments, read from the frame's state.
  obtain hr : ∀ j < 18, readSrc t0 (.mem (at_ .esp (84 + 4 * j))) = some (args j) := fun j hj => by
    have A := h.stack j hj
    obtain ⟨ar, af⟩ := callee_args_apart low top hj
    have ea : t0.ea (at_ .esp (84 + 4 * j)) = VG.Proof.Dsa.X86.stackAddress s j := by
      change addr (t0.gpr .esp) (84 + 4 * j) = addr (s.gpr .esp) (4 + 4 * j)
      rw [addr_eq (by omega_using [t0N, top, hj]), addr_eq (by omega_using [top, hj])]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, t0N]
      omega_arith
    simp only [readSrc, State.load32, ea, t0rd, t0wr]
    obtain ⟨r, hr, hc⟩ := A.stack.read
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨r, by
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr), hc⟩)]
    rw [Fret.readW (r := ⟨VG.Proof.Dsa.X86.stackAddress s j, 4⟩) (Region.contains_self _ _)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact ar) (by decide)]
    exact congrArg some A.value
  obtain hargs : ∀ j < 18, Region.Disjoint ⟨t0.ea (at_ .esp (84 + 4 * j)), 4⟩ ⟨(t0.gpr .esp).setWidth 64, 76⟩ :=
    fun j hj => by
      obtain ⟨_, af⟩ := callee_args_apart low top hj
      have ea : t0.ea (at_ .esp (84 + 4 * j)) = VG.Proof.Dsa.X86.stackAddress s j := by
        change addr (t0.gpr .esp) (84 + 4 * j) = addr (s.gpr .esp) (4 + 4 * j)
        rw [addr_eq (by omega_using [t0N, top, hj]), addr_eq (by omega_using [top, hj])]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, t0N]
        omega_arith
      rw [ea, t0esp]; exact af
  rw [show (List.range 18).flatMap copyArg = (List.range 18).flatMap copyArg ++ [] from (List.append_nil _).symm]
  exact copyArgs_ok rfl (by rw [t0N]; omega_using [low, top]) (by rw [t0wr]; exact List.mem_cons_self ..)
    hr hargs 18 (Nat.le_refl _) fun u K Fc S => WP.block_nil (k u K Fc S)

/-- The callee's frame, 80 bytes below `sp`, lies apart from the working space. -/
theorem callee_frame_apart {sp e : BitVec 32} (RF : RoomF sp base bytes) (ef : e = sp - BitVec.ofNat 32 80) :
    Region.Disjoint ⟨e.setWidth 64, 76⟩ ⟨base, bytes⟩ := by
  obtain ⟨e1, -⟩ := below176_parts RF.low
  generalize hX : (sp - BitVec.ofNat 32 176).setWidth 64 = X at e1
  obtain b176 : below sp 176 = ⟨X, 176⟩ := by rw [← hX]
  obtain fP : e.setWidth 64 = X + BitVec.ofNat 64 96 := by rw [ef, e1]
  refine RF.apart.sub_left ?_
  rw [fP, b176]
  have := Offset.sub X (d := 96) (n := 76) (e := 0) (k := 176) (by decide) (by decide)
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

/-- The callee's state after the copy of the arguments: its inputs, its `esp` 80 bytes below the caller's
`sp`, and its frame apart from the working space. -/
def CalleeAt (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (u : State) : Prop :=
  In (fun _ _ => True) base bytes len args u ∧ u.gpr .esp = sp - BitVec.ofNat 32 80 ∧
    Region.Disjoint ⟨(u.gpr .esp).setWidth 64, 76⟩ ⟨base, bytes⟩

/-- The copy of the arguments reaches the callee's state. -/
theorem callee_at {s : State} (h : In Ex base bytes len args s) (RF : RoomF (s.gpr .esp) base bytes) :
    WP isa (.block ((List.range 18).flatMap copyArg)) (allocFrame argsFrame s.callEntry)
      (CalleeAt base bytes len args (s.gpr .esp)) := by
  obtain ⟨-, t0esp80, -, t0wr, t0rd, -, t0gpr⟩ := callee_entry rfl RF.low
  refine callee_copy h RF rfl fun u K _ S => ?_
  obtain uesp : u.gpr .esp = (allocFrame argsFrame s.callEntry).gpr .esp := K.1 _ (by decide)
  obtain ue : u.gpr .esp = s.gpr .esp - BitVec.ofNat 32 80 := by rw [uesp, t0esp80]
  exact ⟨in_callee h RF (f := u) ue (by rw [K.1 _ (by decide), t0gpr _ (by decide)])
    (by rw [K.2.1, t0rd]) (by rw [K.2.2, t0wr, uesp]) (by rw [uesp]; exact S), ue, callee_frame_apart RF ue⟩


theorem prepCall_ok {s : State} (h : In Ex base bytes len args s) (RF : RoomF (s.gpr .esp) base bytes) :
    WP isa prepCall s (PrepPost Ex base bytes len args s) := by
  have low := RF.low
  have top := h.top
  have hE := (s.gpr .esp).isLt
  have nw := h.scratch.nowrap
  obtain ⟨r4, r76, r96, d76, d96⟩ := callee_regions low
  obtain sN : (s.gpr .esp - 4).toNat = (s.gpr .esp).toNat - 4 := by
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl]; exact VG.X86.sub_toNat (by omega_using [low])
  obtain retWs : Region.Disjoint ⟨(s.gpr .esp - 4).setWidth 64, 4⟩ ⟨base, bytes⟩ := RF.apart.sub_left r4
  unfold prepCall
  refine WP.callBody ?_
  refine WP.frameAllocLocal (bytes := argsFrame) (by decide) (by decide) (by decide)
    (by rw [State.callEntry_esp, sN]; show 76 ≤ _; omega_using [low]) prepBody_noSp ?_ ?_
  · intro t m un ⟨e, rt, P⟩ F
    rw [State.callEntry_esp] at F
    refine ⟨e, ?_, ?_⟩
    · show m.readW _ 32 = _
      rw [F.readW (r := ⟨(s.gpr .esp - 4).setWidth 64, 4⟩) (Region.contains_self _ _)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact d76) (by decide)]
      exact rt
    · exact P.below RF F (fun r hr => by rw [List.mem_singleton.mp hr]; exact r76) un
  -- The frame's state.
  generalize ht0 : allocFrame argsFrame s.callEntry = t0
  obtain ⟨t0esp, t0esp80, -, t0wr, t0rd, t0mem, t0gpr⟩ := callee_entry ht0 low
  obtain frameEq : below (s.gpr .esp - 4) 76 = ⟨(t0.gpr .esp).setWidth 64, 76⟩ := by simp only [below]; rw [t0esp]
  rw [frameEq] at r76 d76
  obtain Fret : Frame [⟨(s.gpr .esp - 4).setWidth 64, 4⟩] s.mem t0.mem := by
    rw [t0mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.seq (callee_copy h RF ht0 fun u K Fc S => ?_)
  obtain uesp : u.gpr .esp = t0.gpr .esp := K.1 _ (by decide)
  obtain h' := in_callee h RF (f := u) (by rw [uesp, t0esp80]) (by rw [K.1 _ (by decide), t0gpr _ (by decide)])
    (by rw [K.2.1, t0rd]) (by rw [K.2.2, t0wr, uesp]) (by rw [uesp]; exact S)
  refine WP.mono (prepCtx_ok h' .wide) fun v ⟨C, one, R2, Fp, Kv⟩ => ?_
  obtain vesp : v.gpr .esp = t0.gpr .esp := (Kv.1 _ (by decide)).trans uesp
  rw [uesp, t0esp] at Fp
  -- The working space's numbers before the operations.
  obtain Fs : Frame (frameF base (s.gpr .esp) []) s.mem u.mem :=
    (frameF_of_sub Fret fun r hr => by rw [List.mem_singleton.mp hr]; exact r4).trans
      (frameF_of_sub Fc fun r hr => by rw [List.mem_singleton.mp hr]; exact r76)
  obtain u0 : sv u.mem base len .wide 0 = sv s.mem base len .wide 0 := by
    have := h.slot_fit .wide (j := 0) (by decide)
    have bw := bc_eq_cwc len .wide
    have est : st len .wide = 2 * bc len .wide + 32 := rfl
    exact frameF_val32 Fs RF nw (by omega_arith) (fun _ h => nomatch h) (fun _ h => nomatch h)
  rw [u0] at R2 C
  obtain Fw : Frame (frameF base (s.gpr .esp) (prepR len .wide)) s.mem v.mem :=
    (frameF_mono Fs (fun _ h => nomatch h)).trans (frameF_of_frameR Fp r96)
  refine ⟨?_, ?_, ?_⟩
  · rw [freed_esp, vesp, t0esp80]
    apply BitVec.eq_of_toNat_eq
    have fb : argsFrame = 76 := rfl
    rw [BitVec.toNat_add, VG.X86.sub_toNat (by omega_using [low]), sN, BitVec.toNat_ofNat]
    omega_using [low, hE, fb]
  · rw [freed_mem]
    rw [Fp.readW (r := ⟨(s.gpr .esp - 4).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
        rw [frameR, List.mem_cons, List.mem_map] at hr
        rcases hr with rfl | ⟨p, hp, rfl⟩
        · exact d96
        · exact retWs.sub_right (Offset.sub_base _ (by have := (prepR_fit2 h .wide).1 p hp; omega_using [this])))
      (by decide),
      Fc.readW (r := ⟨(s.gpr .esp - 4).setWidth 64, 4⟩) (Region.contains_self _ _)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact d76) (by decide),
      t0mem, Mem.readW_writeW_self32]
  · -- Back in the caller.
    obtain Kw : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s ((freed argsFrame v).setReg .esp (s.gpr .esp)) := by
      refine ⟨fun r hr => ?_, by simp only [State.setReg, freed_rd]; rw [Kv.2.1, K.2.1, t0rd], ?_⟩
      · by_cases e : r = .esp
        · subst e; simp [State.setReg]
        · simp only [State.setReg, e, ↓reduceIte]
          rw [freed_gpr _ _ e, Kv.1 r hr, K.1 r (by simp_all), t0gpr r e]
      · simp only [State.setReg, freed_wr]; rw [Kv.2.2, K.2.2, t0wr]; rfl
    refine ⟨⟨in_keepFF h Kw (by decide) (by decide) RF Fw (prepR_fit2 h .wide).1, C.mod, C.gt, C.odd, C.inv⟩,
      one, R2, Fw, Kw⟩

end

end VG.Proof.Ffdh.X86

end
