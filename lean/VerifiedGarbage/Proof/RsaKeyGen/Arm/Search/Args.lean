module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Data
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Slots
public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Search
public import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: the candidate's arguments, whose stores build in parallel with the rest of the call

/-! # The candidate's arguments (ARMv7)

`arguments`, in the candidate's frame of 32 bytes at `S2 = sp - 72`: the
argument registers, and the seven stack arguments, each read from the
search's own (`argWord`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Search

/-- The candidate's stack arguments, for the tape from `used`. -/
def callArgs (p : SearchPublic) (used : Nat) : List (Nat × BitVec 32) :=
  [(0, BitVec.ofNat 32 p.elen), (1, p.pp), (2, BitVec.ofNat 32 p.plen), (3, p.rp + BitVec.ofNat 32 used),
    (4, BitVec.ofNat 32 p.randLen - BitVec.ofNat 32 used), (5, p.B), (6, BitVec.ofNat 32 p.words)]

theorem callArgs_bound (p : SearchPublic) (used : Nat) : ∀ e ∈ callArgs p used, e.1 < 8 := by
  simp only [callArgs, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

/-- What holds while the arguments are stored, from the state `a` after the
candidate's frame is allocated, `k` of them stored. -/
structure ArgCtx (p : SearchPublic) (o a : State) (used k : Nat) (u : State) : Prop where
  input : SearchInput p o
  lr : u.gpr .lr = p.S2
  r8 : u.gpr .r8 = BitVec.ofNat 32 used
  sp : u.sp = p.S2
  rd : u.rd = o.rd
  wr : u.wr = ⟨State.addr p.S2, 32⟩ :: a.wr.tail
  wrA : a.wr = ⟨State.addr p.S2, 32⟩ :: a.wr.tail
  args : ∀ j < 8, a.mem.readW (stackArgAddr o j) 32 = stackArg o j
  mem : u.mem = writeSlots a.mem (State.addr p.S2) ((callArgs p used).take k)

namespace ArgCtx

variable {p : SearchPublic} {o a u : State} {used k : Nat}

theorem S2_toNat (h : ArgCtx p o a used k u) : p.S2.toNat = p.sp.toNat - 72 :=
  FrameStack.sub_toNat' (Nat.le_trans (by decide) h.input.room)

theorem S2_fits (h : ArgCtx p o a used k u) : p.S2.toNat + 32 ≤ 2 ^ 32 := by
  have := h.S2_toNat; have := h.input.top; omega

/-- The search's stack argument `j`, from below both frames. -/
theorem arg_addr (h : ArgCtx p o a used k u) (j : Nat) :
    State.addr (u.sp + BitVec.ofNat 32 (pushBytes + 32 + 4 * j)) = stackArgAddr o j := by
  rw [h.sp, SearchPublic.S2, h.input.sp_eq, show pushBytes + 32 + 4 * j = 72 + 4 * j from rfl, sub_add_ofNat]
  rfl

theorem arg_read (h : ArgCtx p o a used k u) {j : Nat} (hj : j < 8) :
    InRegions (u.rd ++ u.wr) (stackArgAddr o j) 4 := by
  have top := h.input.top
  refine ⟨inArgs o, List.mem_append_left _ (by rw [h.rd, h.input.rd]; simp [inReads]), ?_⟩
  have e : stackArgAddr o j = stackArgAddr o 0 + BitVec.ofNat 64 (4 * j) := by
    simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    exact VG.Arm.addr_add (by rw [← h.input.sp_eq]; omega)
  rw [e]; exact Offset.contains_base _ (by omega) (by omega)

/-- The search's stack argument `j`, from the candidate's frame. -/
theorem arg_off (h : ArgCtx p o a used k u) {j : Nat} (hj : j < 8) :
    stackArgAddr o j = State.addr p.S2 + BitVec.ofNat 64 (72 + 4 * j) := by
  have room := h.input.room
  have top := h.input.top
  have e : o.sp + BitVec.ofNat 32 (4 * j) = p.S2 + BitVec.ofNat 32 (72 + 4 * j) := by
    rw [SearchPublic.S2, sub_add_ofNat, h.input.sp_eq]
  unfold stackArgAddr
  rw [e]
  exact VG.Arm.addr_add (by have := h.S2_toNat; omega)

/-- The candidate's frame is apart from the search's stack arguments. -/
theorem frame_sep (h : ArgCtx p o a used k u) {j d : Nat} (hj : j < 8) (hd : d + 4 ≤ 32) :
    Mem.Sep (stackArgAddr o j) (32 / 8) (off (State.addr p.S2) d) (32 / 8) := by
  rw [h.arg_off hj]
  exact Offset.sep _ (Or.inr (by omega)) (by omega) (by omega)

theorem arg_value (h : ArgCtx p o a used k u) {j : Nat} (hj : j < 8) :
    u.mem.readW (stackArgAddr o j) 32 = stackArg o j := by
  rw [h.mem, readW_writeSlots_sep _ _ _ _ fun e he => h.frame_sep hj (by
    have := callArgs_bound p used e (List.mem_of_mem_take he); omega)]
  exact h.args j hj

theorem store_addr (h : ArgCtx p o a used k u) {d : Nat} (hd : d < 32) :
    State.addr (u.gpr .lr + BitVec.ofNat 32 d) = off (State.addr p.S2) d := by
  rw [h.lr]; exact VG.Arm.addr_add (by have := h.S2_fits; omega)

theorem store_write (h : ArgCtx p o a used k u) {d : Nat} (hd : d + 4 ≤ 32) :
    InRegions u.wr (off (State.addr p.S2) d) 4 :=
  ⟨_, by rw [h.wr]; exact List.mem_cons_self .., Offset.contains_base _ hd (by omega)⟩

theorem keep (h : ArgCtx p o a used k u) {t : State} (hr : Rest [.r12] u t) (hm : t.mem = u.mem) :
    ArgCtx p o a used k t :=
  ⟨h.input, (hr.gpr .lr (by decide)).trans h.lr, (hr.gpr .r8 (by decide)).trans h.r8, hr.sp.trans h.sp,
    hr.rd.trans h.rd, hr.wr.trans h.wr, h.wrA, h.args, hm.trans h.mem⟩

end ArgCtx

/-- Argument `j`, `f` of the search's. -/
theorem argWord_ok {p : SearchPublic} {o a u : State} {used : Nat} {j : Nat} (hj : j < 7)
    {adjust : List Instr} {f : BitVec 32 → BitVec 32}
    (hadj : ∀ t, t.gpr .r8 = BitVec.ofNat 32 used →
      WP isa (.block adjust) t fun t' => (t'.gpr .r12 = f (t.gpr .r12) ∧ t'.mem = t.mem) ∧ Rest [.r12] t t')
    (hv : (callArgs p used)[j]? = some (j, f (stackArg o j))) (h : ArgCtx p o a used j u) :
    WP isa (.block (argWord j adjust)) u fun t => ArgCtx p o a used (j + 1) t ∧ Rest [.r12] u t := by
  have c1 : pushBytes + 32 + 4 * j < 4096 := by unfold pushBytes; omega
  have c2 : 4 * j < 4096 := by omega
  rw [show argWord j adjust = [arg .r12 32 j] ++ (adjust ++ [.str .r12 .lr (4 * j)]) from rfl]
  refine WP.block_append (WP.mono (withRest_all (c := .block [arg .r12 32 j]) [.r12]
    (Q := fun t => t.gpr .r12 = stackArg o j ∧ t.mem = u.mem) ?_ (by rfl) (by rfl)) fun u1 ⟨⟨h12, hm1⟩, k1⟩ => ?_)
  · unfold arg
    ffrun [h.arg_addr j, h.arg_read (j := j) (by omega), h.arg_value (j := j) (by omega), c1]
  have h1 := h.keep k1 hm1
  refine WP.block_append (WP.mono (hadj u1 h1.r8) fun u2 ⟨⟨h12', hm2⟩, k2⟩ => ?_)
  have h2 := h1.keep k2 hm2
  refine WP.mono (withRest_all (c := .block [.str .r12 .lr (4 * j)]) [.r12]
    (Q := fun t => t.mem = u2.mem.writeW (off (State.addr p.S2) (4 * j)) (f (stackArg o j))) ?_ (by rfl) (by rfl))
    fun t ⟨hmt, kt⟩ => ⟨⟨h.input, ?_, ?_, ?_, ?_, ?_, h.wrA, h.args, ?_⟩, k1.trans (k2.trans kt)⟩
  · ffrun [h2.store_addr (d := 4 * j) (by omega), h2.store_write (d := 4 * j) (by omega), h12', h12, c2]
  · exact (kt.gpr .lr (by decide)).trans h2.lr
  · exact (kt.gpr .r8 (by decide)).trans h2.r8
  · exact kt.sp.trans h2.sp
  · exact kt.rd.trans h2.rd
  · exact kt.wr.trans h2.wr
  · rw [hmt, h2.mem, List.take_add_one, hv, Option.toList_some, writeSlots_append]
    rfl

theorem adjust_none (used : Nat) : ∀ t, t.gpr .r8 = BitVec.ofNat 32 used →
    WP isa (.block []) t fun t' => (t'.gpr .r12 = id (t.gpr .r12) ∧ t'.mem = t.mem) ∧ Rest [.r12] t t' :=
  fun _ _ => WP.block_nil ⟨⟨rfl, rfl⟩, Rest.refl _ _⟩

theorem adjust_add (used : Nat) : ∀ t, t.gpr .r8 = BitVec.ofNat 32 used →
    WP isa (.block [.dp .add .r12 .r12 (.reg .r8)]) t fun t' =>
      (t'.gpr .r12 = (· + BitVec.ofNat 32 used) (t.gpr .r12) ∧ t'.mem = t.mem) ∧ Rest [.r12] t t' := by
  intro t h8
  refine withRest_all [.r12] ?_ (by rfl) (by rfl)
  ffrun [h8]

theorem adjust_sub (used : Nat) : ∀ t, t.gpr .r8 = BitVec.ofNat 32 used →
    WP isa (.block [.dp .sub .r12 .r12 (.reg .r8)]) t fun t' =>
      (t'.gpr .r12 = (· - BitVec.ofNat 32 used) (t.gpr .r12) ∧ t'.mem = t.mem) ∧ Rest [.r12] t t' := by
  intro t h8
  refine withRest_all [.r12] ?_ (by rfl) (by rfl)
  ffrun [h8]

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The registers and stack arguments of the candidate, from a loop state. -/
def ArgDone (p : SearchPublic) (o a : State) (used : Nat) (u : State) : Prop :=
  ArgCtx p o a used 7 u ∧ u.gpr .r0 = p.op ∧ u.gpr .r1 = BitVec.ofNat 32 p.len ∧ u.gpr .r2 = p.up ∧
    u.gpr .r3 = p.ep

/-- The argument registers, and `lr` the candidate frame's base. -/
def argHead : List Instr :=
  [.mov .r0 (.reg .r4), .mov .r1 (.reg .r5), .mov .r2 (.reg .r6), .mov .r3 (.reg .r7), .addSp .lr 0]

theorem arguments_eq : arguments = argHead ++ (argWord 0 [] ++ (argWord 1 [] ++ (argWord 2 [] ++
    (argWord 3 [.dp .add .r12 .r12 (.reg .r8)] ++ (argWord 4 [.dp .sub .r12 .r12 (.reg .r8)] ++
      (argWord 5 [] ++ argWord 6 [])))))) := by
  simp only [arguments, argHead, List.append_assoc]

/-- The candidate's argument registers. -/
def ArgRegs (p : SearchPublic) (u : State) : Prop :=
  u.gpr .r0 = p.op ∧ u.gpr .r1 = BitVec.ofNat 32 p.len ∧ u.gpr .r2 = p.up ∧ u.gpr .r3 = p.ep

theorem ArgRegs.keep {p : SearchPublic} {u t : State} (h : ArgRegs p u) (k : Rest [.r12] u t) : ArgRegs p t :=
  ⟨(k.gpr .r0 (by decide)).trans h.1, (k.gpr .r1 (by decide)).trans h.2.1, (k.gpr .r2 (by decide)).trans h.2.2.1,
    (k.gpr .r3 (by decide)).trans h.2.2.2⟩

theorem argHead_ok {p : SearchPublic} {o s : State} {used remaining : Nat}
    (h : SearchLive p o used remaining s) :
    WP isa (.block argHead) (allocated 32 s) fun u =>
      (ArgCtx p o (allocated 32 s) used 0 u ∧ ArgRegs p u) ∧ Rest [.r0, .r1, .r2, .r3, .lr] (allocated 32 s) u := by
  have hi := h.input
  have hS2 : (allocated 32 s).sp = p.S2 := by
    change s.sp - BitVec.ofNat 32 32 = p.S2
    rw [h.sp, SearchPublic.S1, SearchPublic.S2, BitVec.sub_sub, ← BitVec.ofNat_add]
  have hw : (allocated 32 s).wr = ⟨State.addr p.S2, 32⟩ :: (allocated 32 s).wr.tail := by
    change ⟨State.addr (s.sp - BitVec.ofNat 32 32), 32⟩ :: s.wr = _
    rw [← hS2]; rfl
  have hargs : ∀ j < 8, (allocated 32 s).mem.readW (stackArgAddr o j) 32 = stackArg o j := fun j hj => by
    change s.mem.readW _ 32 = _
    rw [hi.arg_frame h.frame hj]; rfl
  refine WP.mono (withRest_all [.r0, .r1, .r2, .r3, .lr]
    (Q := fun t => t.gpr .r0 = p.op ∧ t.gpr .r1 = BitVec.ofNat 32 p.len ∧ t.gpr .r2 = p.up ∧ t.gpr .r3 = p.ep ∧
      t.gpr .lr = p.S2 ∧ t.mem = (allocated 32 s).mem) ?_ (by rfl) (by rfl)) fun u0 ⟨⟨h0, h1, h2, h3, hlr, hm⟩, k0⟩ =>
    ⟨⟨⟨hi, hlr, (k0.gpr .r8 (by decide)).trans h.r8, k0.sp.trans hS2, k0.rd.trans h.rd, k0.wr.trans hw, hw,
      hargs, hm⟩, h0, h1, h2, h3⟩, k0⟩
  have ag : (allocated 32 s).gpr = s.gpr := rfl
  unfold argHead
  ffrun [hS2, ag, h.r4, h.r5, h.r6, h.r7, BitVec.add_zero]

theorem hv_of {p : SearchPublic} {o : State} (hi : SearchInput p o) (used j : Nat) (f : BitVec 32 → BitVec 32)
    (e : (callArgs (searchOfState o) used)[j]? = some (j, f (stackArg o j))) :
    (callArgs p used)[j]? = some (j, f (stackArg o j)) := by rw [← hi.2]; exact e

theorem arguments_ok {p : SearchPublic} {o s : State} {used remaining : Nat}
    (h : SearchLive p o used remaining s) :
    WP isa (.block arguments) (allocated 32 s) fun u =>
      ArgDone p o (allocated 32 s) used u ∧ Rest [.r0, .r1, .r2, .r3, .r12, .lr] (allocated 32 s) u := by
  have hi := h.input
  have hv := hv_of hi used
  rw [arguments_eq]
  refine WP.block_append (WP.mono (argHead_ok h) fun u0 ⟨⟨c0, r0⟩, k0⟩ => ?_)
  refine WP.block_append (WP.mono (argWord_ok (j := 0) (f := id) (by decide) (adjust_none used)
    (hv 0 id (by simp [callArgs, searchOfState])) c0) fun u1 ⟨c1, k1⟩ => ?_)
  refine WP.block_append (WP.mono (argWord_ok (j := 1) (f := id) (by decide) (adjust_none used)
    (hv 1 id (by simp [callArgs, searchOfState])) c1) fun u2 ⟨c2, k2⟩ => ?_)
  refine WP.block_append (WP.mono (argWord_ok (j := 2) (f := id) (by decide) (adjust_none used)
    (hv 2 id (by simp [callArgs, searchOfState])) c2) fun u3 ⟨c3, k3⟩ => ?_)
  refine WP.block_append (WP.mono (argWord_ok (j := 3) (f := (· + BitVec.ofNat 32 used)) (by decide) (adjust_add used)
    (hv 3 (· + BitVec.ofNat 32 used) (by simp [callArgs, searchOfState])) c3) fun u4 ⟨c4, k4⟩ => ?_)
  refine WP.block_append (WP.mono (argWord_ok (j := 4) (f := (· - BitVec.ofNat 32 used)) (by decide) (adjust_sub used)
    (hv 4 (· - BitVec.ofNat 32 used) (by simp [callArgs, searchOfState])) c4) fun u5 ⟨c5, k5⟩ => ?_)
  refine WP.block_append (WP.mono (argWord_ok (j := 5) (f := id) (by decide) (adjust_none used)
    (hv 5 id (by simp [callArgs, searchOfState])) c5) fun u6 ⟨c6, k6⟩ => ?_)
  refine WP.mono (argWord_ok (j := 6) (f := id) (by decide) (adjust_none used)
    (hv 6 id (by simp [callArgs, searchOfState])) c6) fun u7 ⟨c7, k7⟩ => ?_
  have k := k1.trans (k2.trans (k3.trans (k4.trans (k5.trans (k6.trans k7)))))
  exact ⟨⟨c7, r0.keep k⟩, (k0.mono (by decide)).trans (k.mono (by decide))⟩

end VG.Proof.RsaKeyGen.Arm.Search
