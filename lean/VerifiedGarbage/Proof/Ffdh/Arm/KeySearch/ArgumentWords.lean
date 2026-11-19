module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.AttemptPost
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Fields
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ffdh.Arm.Block

/-! ### `Ffdh.Arm.KeySearch.Arguments`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.KeySearch.ArgumentBlocks`, which this module and modules that import it used -/

section

/-! Small native blocks used to place the selected attempt's stack arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem argumentHead_ok (s : State) {base x y : BitVec 32} {n : Nat}
    (h : Controller base s) (xvalue : lowWord s.mem base 5 = x)
    (yvalue : lowWord s.mem base 6 = y) (width : lowWord s.mem base 2 = BitVec.ofNat 32 n) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 5, VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 2,
      VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 6, VG.Impl.Ffdh.Arm.KeySearch.ldf .r3 2, .addSp .r12 0]) s fun t =>
      (t.gpr .r0 = x ∧ t.gpr .r1 = BitVec.ofNat 32 n ∧ t.gpr .r2 = y ∧
        t.gpr .r3 = BitVec.ofNat 32 n ∧ t.gpr .r12 = s.sp ∧ t.mem = s.mem) ∧
      Rest [.r0, .r1, .r2, .r3, .r12] s t := by
  refine withRest_all [.r0, .r1, .r2, .r3, .r12] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.KeySearch.ldf lowWord at *
  ffrun [h.addr (by decide : 5 < 16), h.addr (by decide : 6 < 16), h.addr (by decide : 2 < 16),
    h.read (by decide : 5 < 16), h.read (by decide : 6 < 16), h.read (by decide : 2 < 16),
    xvalue, yvalue, width, BitVec.add_zero]

theorem argumentCopyAt_ok (s : State) {base value : BitVec 32} {offset d bytes : Nat}
    (h : Controller base s) (sourceFit : offset + 4 ≤ 128)
    (stack : Workspace s s.sp bytes) (fit : d + 4 ≤ bytes)
    (stackBase : s.gpr .r12 = s.sp)
    (source : s.mem.readW (off (State.addr base) offset) 32 = value)
    (small : d < 4096 := by omega) :
    WP isa (.block [.ldr .r9 .r4 offset, .str .r9 .r12 d]) s fun t =>
      t.mem = s.mem.writeW (off (State.addr s.sp) d) value ∧ Rest [.r9] s t := by
  refine withRest_all [.r9] ?_ (by rfl) (by rfl)
  have address : State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := stack.nowrap; omega_using [fit, this])
  have sourceAddress : State.addr (base + BitVec.ofNat 32 offset) = off (State.addr base) offset :=
    VG.Arm.addr_add (by have := h.space.nowrap; omega_using [sourceFit, this])
  ffrun [(by omega_using [sourceFit] : offset < 4096), small, h.ptr, sourceAddress, h.space.read sourceFit,
    stackBase, address, stack.write fit, source]

theorem argumentStore_ok (s : State) {value : BitVec 32} {d bytes : Nat} (r : Reg)
    (stack : Workspace s s.sp bytes) (fit : d + 4 ≤ bytes) (stackBase : s.gpr .r12 = s.sp)
    (source : s.gpr r = value) (small : d < 4096 := by omega) :
    WP isa (.block [.str r .r12 d]) s fun t =>
      t.mem = s.mem.writeW (off (State.addr s.sp) d) value ∧ Rest [] s t := by
  refine withRest_all [] ?_ (by rfl) (by rfl)
  have address : State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := stack.nowrap; omega_using [fit, this])
  ffrun [small, stackBase, address, stack.write fit, source]

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.ArgumentContext`, which only this module used -/

section

/-! The argument frame can be filled without changing the selected domain,
entropy-tape pointer, or register arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure ArgumentContext (p : KeyPublic sampling) (used keys scalars : Nat) (s : State) : Prop where
  controller : Controller p.control s
  stack : Workspace s s.sp sampling.argumentBytes
  separate : (⟨State.addr p.control, 128⟩ : Region).Disjoint ⟨State.addr s.sp, sampling.argumentBytes⟩
  headers : Slots s.mem p.control (p.headers used keys scalars)
  stackBase : s.gpr .r12 = s.sp
  x : s.gpr .r0 = p.xp
  xlen : s.gpr .r1 = BitVec.ofNat 32 p.len
  y : s.gpr .r2 = p.yp
  ylen : s.gpr .r3 = BitVec.ofNat 32 p.len
  cachedSlots : CachedSlots p s.mem

theorem ArgumentContext.after {p : KeyPublic sampling} {used keys scalars : Nat} {s t : State}
    (h : ArgumentContext p used keys scalars s) {rs : List Reg} (rest : Rest rs s t)
    (frame : Frame [⟨State.addr s.sp, sampling.argumentBytes⟩] s.mem t.mem)
    (kept : ∀ r ∈ [.r0, .r1, .r2, .r3, .r4, .r12], r ∉ rs := by decide) :
    ArgumentContext p used keys scalars t := by
  refine ⟨⟨h.controller.space.congr rest.wr, (rest.gpr .r4 (kept .r4 (by decide))).trans h.controller.ptr⟩,
    ?_, ?_, ?_, ?_, (rest.gpr .r0 (kept .r0 (by decide))).trans h.x,
    (rest.gpr .r1 (kept .r1 (by decide))).trans h.xlen,
    (rest.gpr .r2 (kept .r2 (by decide))).trans h.y,
    (rest.gpr .r3 (kept .r3 (by decide))).trans h.ylen, ?_⟩
  · rw [rest.sp]; exact h.stack.congr rest.wr
  · rw [rest.sp]; exact h.separate
  · apply (slots_fields _ _ _ _ _ _).mpr
    intro j hj
    have bound := headerIndices_bound hj
    exact (frame.readW (r := ⟨State.addr p.control, 128⟩)
      (Offset.contains_base _ (by omega_using [bound]) (by omega_using [bound])) (by simpa using h.separate) (by decide)).trans
        ((slots_fields _ _ _ _ _ _).mp h.headers j hj)
  · rw [rest.sp]
    exact (rest.gpr .r12 (kept .r12 (by decide))).trans h.stackBase

  · intro cached
    obtain ⟨ptr, words⟩ := h.cachedSlots cached
    constructor
    · exact (frame.readW (r := ⟨State.addr p.control, 128⟩)
        (Offset.contains_base _ (by decide : 32 + 4 ≤ 128) (by decide))
        (by simpa using h.separate) (by decide)).trans ptr
    · exact (frame.readW (r := ⟨State.addr p.control, 128⟩)
        (Offset.contains_base _ (by decide : 36 + 4 ≤ 128) (by decide))
        (by simpa using h.separate) (by decide)).trans words

theorem wp_argumentCopyAt {p : KeyPublic sampling} {used keys scalars : Nat} {s : State} {is : List Instr}
    {Q : State → Prop} {value : BitVec 32} {offset d : Nat}
    (h : ArgumentContext p used keys scalars s) (sourceFit : offset + 4 ≤ 128)
    (fit : d + 4 ≤ sampling.argumentBytes)
    (source : s.mem.readW (off (State.addr p.control) offset) 32 = value)
    (next : ∀ t, ArgumentContext p used keys scalars t →
      t.mem = s.mem.writeW (off (State.addr s.sp) d) value → Rest [.r9] s t → WP isa (.block is) t Q) :
    WP isa (.block (.ldr .r9 .r4 offset :: .str .r9 .r12 d :: is)) s Q := by
  change WP isa (.block ([.ldr .r9 .r4 offset, .str .r9 .r12 d] ++ is)) s Q
  rw [WP.block_append_iff]
  have small := argumentBytes_max sampling
  refine WP.mono (argumentCopyAt_ok s h.controller sourceFit h.stack fit h.stackBase source) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨State.addr s.sp, sampling.argumentBytes⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (by simp) _ (Offset.contains_base _ fit (by have := h.stack.nowrap; omega_using [fit, small]))
  exact next t (h.after rest frame) mem rest

theorem wp_argumentCopy {p : KeyPublic sampling} {used keys scalars : Nat} {s : State} {is : List Instr}
    {Q : State → Prop} {value : BitVec 32} {j d : Nat}
    (h : ArgumentContext p used keys scalars s) (slot : j < 16) (fit : d + 4 ≤ sampling.argumentBytes)
    (source : lowWord s.mem p.control j = value)
    (next : ∀ t, ArgumentContext p used keys scalars t →
      t.mem = s.mem.writeW (off (State.addr s.sp) d) value → Rest [.r9] s t → WP isa (.block is) t Q) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.ldf .r9 j :: .str .r9 .r12 d :: is)) s Q :=
  wp_argumentCopyAt h (by omega_using [slot]) fit source next

theorem wp_argumentStore {p : KeyPublic sampling} {used keys scalars : Nat} {s : State} {is : List Instr}
    {Q : State → Prop} {d : Nat} (h : ArgumentContext p used keys scalars s) (fit : d + 4 ≤ sampling.argumentBytes)
    (next : ∀ t, ArgumentContext p used keys scalars t →
      t.mem = s.mem.writeW (off (State.addr s.sp) d) (BitVec.ofNat 32 p.len) →
      Rest [] s t → WP isa (.block is) t Q) :
    WP isa (.block (.str .r1 .r12 d :: is)) s Q := by
  change WP isa (.block ([.str .r1 .r12 d] ++ is)) s Q
  rw [WP.block_append_iff]
  have small := argumentBytes_max sampling
  refine WP.mono (argumentStore_ok s .r1 h.stack fit h.stackBase h.xlen) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨State.addr s.sp, sampling.argumentBytes⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (by simp) _ (Offset.contains_base _ fit (by have := h.stack.nowrap; omega_using [fit, small]))
  exact next t (h.after rest frame) mem rest

end VG.Proof.Ffdh.Arm.KeySearch

end

end


/-! Exact AAPCS arguments and stack-memory effects of the nested key attempt. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

def callMemBase (p : KeyPublic sampling) (used : Nat) (m : Mem) (sp : BitVec 32) : Mem :=
  ((((((m.writeW (off (State.addr sp) 0) p.dp).writeW
    (off (State.addr sp) 4) (BitVec.ofNat 32 p.dlen)).writeW
    (off (State.addr sp) 8) (BitVec.ofNat 32 p.len)).writeW
    (off (State.addr sp) 12) (p.rp + BitVec.ofNat 32 used)).writeW
    (off (State.addr sp) 16) (BitVec.ofNat 32 p.len)).writeW
    (off (State.addr sp) 20) p.scratch).writeW
    (off (State.addr sp) 24) (BitVec.ofNat 32 p.capacity)

/-- Append the cached attempt's two readonly-context arguments. -/
def callMem (p : KeyPublic sampling) (used : Nat) (m : Mem) (sp : BitVec 32) : Mem :=
  if sampling.cachedContext then
    ((callMemBase p used m sp).writeW (off (State.addr sp) 28) p.context).writeW
      (off (State.addr sp) 32) (BitVec.ofNat 32 p.contextWords)
  else callMemBase p used m sp

theorem argumentsBase_ok (s : State) {p : KeyPublic sampling} {used keys scalars : Nat}
    (h : Controller p.control s) (stack : Workspace s s.sp sampling.argumentBytes)
    (separate : (⟨State.addr p.control, 128⟩ : Region).Disjoint ⟨State.addr s.sp, sampling.argumentBytes⟩)
    (headers : Slots s.mem p.control (p.headers used keys scalars))
    (cacheSlots : CachedSlots p s.mem) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.arguments) s fun t =>
      (ArgumentContext p used keys scalars t ∧ t.mem = callMemBase p used s.mem s.sp) ∧
      Rest [.r0, .r1, .r2, .r3, .r9, .r12] s t := by
  refine withRest_all [.r0, .r1, .r2, .r3, .r9, .r12] ?_ (by rfl) (by rfl)
  change WP isa (.block ([VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 5, VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 2,
    VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 6, VG.Impl.Ffdh.Arm.KeySearch.ldf .r3 2, .addSp .r12 0] ++ _)) s _
  rw [WP.block_append_iff]
  refine WP.mono (argumentHead_ok s h
    (headers (5, p.xp) (by simp [KeyPublic.headers])) (headers (6, p.yp) (by simp [KeyPublic.headers]))
    (headers (2, BitVec.ofNat 32 p.len) (by simp [KeyPublic.headers]))) ?_
  rintro u ⟨⟨x, xlen, y, ylen, ptr, mem⟩, rest⟩
  have context : ArgumentContext p used keys scalars u :=
    ⟨⟨h.space.congr rest.wr, (rest.gpr .r4 (by simp)).trans h.ptr⟩,
      by rw [rest.sp]; exact stack.congr rest.wr,
      by rw [rest.sp]; exact separate,
      by rw [mem]; exact headers,
      by rw [rest.sp]; exact ptr, x, xlen, y, ylen, by rw [mem]; exact cacheSlots⟩
  refine wp_argumentCopy (j := 7) (d := 0) context (by decide) (by have := argumentBytes_min sampling; omega_using [this])
    (context.headers (7, p.dp) (by simp [KeyPublic.headers])) fun s1 c1 m1 r1 => ?_
  have sp1 := r1.sp.trans rest.sp
  refine wp_argumentCopy (j := 8) (d := 4) c1 (by decide) (by have := argumentBytes_min sampling; omega_using [this])
    (c1.headers (8, BitVec.ofNat 32 p.dlen) (by simp [KeyPublic.headers])) fun s2 c2 m2 r2 => ?_
  have sp2 := r2.sp.trans sp1
  refine wp_argumentStore (d := 8) c2 (by have := argumentBytes_min sampling; omega_using [this]) fun s3 c3 m3 r3 => ?_
  have sp3 := r3.sp.trans sp2
  refine wp_argumentCopy (j := 9) (d := 12) c3 (by decide) (by have := argumentBytes_min sampling; omega_using [this])
    (c3.headers (9, p.rp + BitVec.ofNat 32 used) (by simp [KeyPublic.headers])) fun s4 c4 m4 r4 => ?_
  have sp4 := r4.sp.trans sp3
  refine wp_argumentStore (d := 16) c4 (by have := argumentBytes_min sampling; omega_using [this]) fun s5 c5 m5 r5 => ?_
  have sp5 := r5.sp.trans sp4
  refine wp_argumentCopy (j := 12) (d := 20) c5 (by decide) (by have := argumentBytes_min sampling; omega_using [this])
    (c5.headers (12, p.scratch) (by simp [KeyPublic.headers])) fun s6 c6 m6 r6 => ?_
  have sp6 := r6.sp.trans sp5
  refine wp_argumentCopy (j := 13) (d := 24) c6 (by decide) (by have := argumentBytes_min sampling; omega_using [this])
    (c6.headers (13, BitVec.ofNat 32 p.capacity) (by simp [KeyPublic.headers])) fun s7 c7 m7 _ => ?_
  apply WP.block_nil
  refine ⟨c7, ?_⟩
  rw [m7, m6, m5, m4, m3, m2, m1, mem, sp6, sp5, sp4, sp3, sp2, sp1, rest.sp]
  rfl

theorem arguments_ok (s : State) {p : KeyPublic sampling} {used keys scalars : Nat}
    (h : Controller p.control s) (stack : Workspace s s.sp sampling.argumentBytes)
    (separate : (⟨State.addr p.control, 128⟩ : Region).Disjoint ⟨State.addr s.sp, sampling.argumentBytes⟩)
    (headers : Slots s.mem p.control (p.headers used keys scalars))
    (cacheSlots : CachedSlots p s.mem) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.argumentsFor sampling.cachedContext)) s fun t =>
      (ArgumentContext p used keys scalars t ∧ t.mem = callMem p used s.mem s.sp) ∧
      Rest [.r0, .r1, .r2, .r3, .r9, .r12] s t := by
  refine withRest_all [.r0, .r1, .r2, .r3, .r9, .r12] ?_ (by cases sampling <;> rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.KeySearch.argumentsFor
  rw [WP.block_append_iff]
  refine WP.mono (argumentsBase_ok s h stack separate headers cacheSlots) ?_
  rintro u ⟨⟨context, mem⟩, rest⟩
  cases active : sampling.cachedContext with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    apply WP.block_nil
    exact ⟨context, by simpa only [callMem, active, Bool.false_eq_true, ite_false] using mem⟩
  | true =>
    change WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r9 4, .str .r9 .r12 28,
      .ldr .r9 .r4 36, .str .r9 .r12 32]) u _
    have size : sampling.argumentBytes = 40 := by simp [GenerationPolicy.argumentBytes, active]
    refine wp_argumentCopy (j := 4) (d := 28) context (by decide) (by rw [size]; decide)
      (context.cachedSlots active).1 fun v cv mv rv => ?_
    have spv := rv.sp.trans rest.sp
    refine wp_argumentCopyAt (offset := 36) (d := 32) cv (by decide) (by rw [size]; decide)
      (cv.cachedSlots active).2 fun t ct mt _ => ?_
    apply WP.block_nil
    refine ⟨ct, ?_⟩
    simp only [callMem, active, ite_true]
    rw [mt, mv, mem, spv, rest.sp]

theorem callMemBase_frame (p : KeyPublic sampling) (used : Nat) (m : Mem) (sp : BitVec 32) :
    Frame [⟨State.addr sp, sampling.argumentBytes⟩] m (callMemBase p used m sp) := by
  unfold callMemBase
  exact (((((((Frame.refl _ _).writeW (by simp) _ (Offset.contains_base _ (by cases sampling <;> decide : 0 + 4 ≤ sampling.argumentBytes) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by cases sampling <;> decide : 4 + 4 ≤ sampling.argumentBytes) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by cases sampling <;> decide : 8 + 4 ≤ sampling.argumentBytes) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by cases sampling <;> decide : 12 + 4 ≤ sampling.argumentBytes) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by cases sampling <;> decide : 16 + 4 ≤ sampling.argumentBytes) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by cases sampling <;> decide : 20 + 4 ≤ sampling.argumentBytes) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by cases sampling <;> decide : 24 + 4 ≤ sampling.argumentBytes) (by decide))

theorem callMem_frame (p : KeyPublic sampling) (used : Nat) (m : Mem) (sp : BitVec 32) :
    Frame [⟨State.addr sp, sampling.argumentBytes⟩] m (callMem p used m sp) := by
  unfold callMem
  split
  · rename_i active
    have size : sampling.argumentBytes = 40 := by simp [GenerationPolicy.argumentBytes, active]
    exact ((callMemBase_frame p used m sp).writeW (by simp) _
      (Offset.contains_base _ (by omega_using [size] : 28 + 4 ≤ sampling.argumentBytes) (by decide))).writeW
        (by simp) _ (Offset.contains_base _ (by omega_using [size] : 32 + 4 ≤ sampling.argumentBytes) (by decide))
  · exact callMemBase_frame p used m sp

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.CallFacts`, which only this module used -/

section

/-! The nested attempt's buffers and private stack satisfy its shared signature. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeySearch/Tape.lean`, which only this module imported.
section

/-! A nested attempt receives exactly the next public-width slice of entropy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont

abbrev rTape (p : KeyPublic sampling) (used : Nat) : Region :=
  ⟨State.addr (p.rp + BitVec.ofNat 32 used), p.len⟩

theorem KeyInput.tape_addr {p : KeyPublic sampling} {s : State} {used : Nat}
    (h : KeyInput p s) (room : used + p.len ≤ p.randLen) :
    State.addr (p.rp + BitVec.ofNat 32 used) = off (State.addr p.rp) used :=
  VG.Arm.addr_add (by have := h.bounds.randomFit; have := h.bounds.minLength; omega_arith)

theorem KeyInput.tape_sub {p : KeyPublic sampling} {s : State} {used : Nat}
    (h : KeyInput p s) (room : used + p.len ≤ p.randLen) : (rTape p used).Sub (rRandom p) := by
  change (⟨State.addr (p.rp + BitVec.ofNat 32 used), p.len⟩ : Region).Sub _
  rw [h.tape_addr room]
  exact Offset.sub_base _ room

theorem KeyInput.tape_fits {p : KeyPublic sampling} {s : State} {used : Nat}
    (h : KeyInput p s) (room : used + p.len ≤ p.randLen) :
    (p.rp + BitVec.ofNat 32 used).toNat + p.len ≤ 2 ^ 32 := by
  have fits := h.bounds.randomFit
  have positive := h.bounds.minLength
  have usedFits : used < 2 ^ 32 := by omega_using [room, fits, positive]
  have pointerFits : p.rp.toNat + used < 2 ^ 32 := by omega_using [room, fits, positive]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt usedFits, Nat.mod_eq_of_lt pointerFits]
  omega_using [room, fits]

end VG.Proof.Ffdh.Arm.KeySearch
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Spec.Ffdh

abbrev rCallArgs (p : KeyPublic sampling) : Region := ⟨State.addr (callSp p), sampling.argumentBytes - 4⟩

structure CallFacts (p : KeyPublic sampling) (used : Nat) : Prop where
  stackFits : 176 ≤ (callSp p).toNat
  argsFit : (callSp p).toNat + (sampling.argumentBytes - 4) ≤ 2 ^ 32
  xy : (rX p).Disjoint (rY p)
  xd : (rX p).Disjoint (rDomain p)
  xr : (rX p).Disjoint (rTape p used)
  xs : (rX p).Disjoint (rScratch p)
  xa : (rX p).Disjoint (rCallArgs p)
  yd : (rY p).Disjoint (rDomain p)
  yr : (rY p).Disjoint (rTape p used)
  ys : (rY p).Disjoint (rScratch p)
  ya : (rY p).Disjoint (rCallArgs p)
  ds : (rDomain p).Disjoint (rScratch p)
  rs : (rTape p used).Disjoint (rScratch p)
  sa : (rScratch p).Disjoint (rCallArgs p)
  stack : ∀ r ∈ [rX p, rY p, rDomain p, rTape p used, rScratch p, rCallArgs p],
    (rCallStack p).Disjoint r
  xFit : p.xp.toNat + p.len ≤ 2 ^ 32
  yFit : p.yp.toNat + p.len ≤ 2 ^ 32
  domainFit : p.dp.toNat + p.dlen ≤ 2 ^ 32
  tapeFit : (p.rp + BitVec.ofNat 32 used).toNat + p.len ≤ 2 ^ 32
  scratchFit : p.scratch.toNat + p.capacity * 8 ≤ 2 ^ 32
  length : pLenValid p.len
  domainLength : domainLenValid p.len p.dlen
  scratch : Spec.Rsa.scratchWords p.len ≤ p.capacity
  lenFits : p.len < 2 ^ 32
  domainLenFits : p.dlen < 2 ^ 32
  capacityFits : p.capacity < 2 ^ 32

theorem KeyInput.callFacts {p : KeyPublic sampling} {original : State} {used : Nat}
    (h : KeyInput p original) (room : used + p.len ≤ p.randLen) : CallFacts p used := by
  have fit : stackUse sampling ≤ p.sp.toNat := h.bounds.stackFits
  have sizeMin := argumentBytes_min sampling
  have sizeMax := argumentBytes_max sampling
  have callNat : (callSp p).toNat = p.sp.toNat - (24 + sampling.argumentBytes) :=
    FrameStack.sub_toNat' (by change 24 + sampling.argumentBytes + 176 ≤ p.sp.toNat at fit; omega_using [fit])
  have rootWrite (r : Region) (hr : r ∈ [rX p, rY p, rScratch p]) : r ∈ original.wr := by
    rw [h.write_regions]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp
  have rootRead (r : Region) (hr : r ∈ [rDomain p, rRandom p]) : r ∈ original.rd := by
    rw [h.read_regions]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  have cross (w : Region) (hw : w ∈ [rX p, rY p, rScratch p])
      (r : Region) (hr : r ∈ [rDomain p, rRandom p]) : w.Disjoint r :=
    h.layout.separate w (by rw [← h.layout.wr]; exact rootWrite w hw)
      r (by rw [← h.layout.rd]; exact rootRead r hr)
  have tape := h.tape_sub room
  have argsSub : (rCallArgs p).Sub (FrameStack.belowA p.sp (stackUse sampling)) :=
    fun a ha => (arguments_sub h.bounds.stackFits) a (Region.sub_prefix (by omega_using [] : sampling.argumentBytes - 4 ≤ sampling.argumentBytes) a ha)
  have stackSub := callStack_sub h.bounds.stackFits
  have stackWrite (r : Region) (hr : r ∈ [rX p, rY p, rScratch p]) :
      (FrameStack.belowA p.sp (stackUse sampling)).Disjoint r :=
    h.stack_separate (List.mem_append_left _ (rootWrite r hr))
  have stackRead (r : Region) (hr : r ∈ [rDomain p, rRandom p]) :
      (FrameStack.belowA p.sp (stackUse sampling)).Disjoint r :=
    h.stack_separate (List.mem_append_right _ (rootRead r hr))
  have geometry := h.output_regions_disjoint
  change 24 + sampling.argumentBytes + 176 ≤ p.sp.toNat at fit
  refine ⟨by rw [callNat]; omega_using [fit], by rw [callNat]; have := p.sp.isLt; omega_using [sizeMax],
    geometry.1, cross _ (by simp) _ (by simp), (cross _ (by simp) _ (by simp)).sub_right tape,
    geometry.2.1, (stackWrite _ (by simp)).symm.sub_right argsSub,
    cross _ (by simp) _ (by simp), (cross _ (by simp) _ (by simp)).sub_right tape,
    geometry.2.2.1, (stackWrite _ (by simp)).symm.sub_right argsSub,
    (cross _ (by simp) _ (by simp)).symm, ((cross _ (by simp) _ (by simp)).sub_right tape).symm,
    (stackWrite _ (by simp)).symm.sub_right argsSub, ?_, h.bounds.xFit, h.bounds.yFit,
    h.bounds.domainFit, h.tape_fits room, by simpa only [Nat.mul_comm] using h.bounds.scratchFit,
    ⟨h.bounds.minLength, h.bounds.maxLength⟩, h.bounds.domainLength, h.bounds.scratchSpace,
    by have := h.bounds.maxLength; omega_using [this], ?_, h.bounds.capacityFits⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (stackWrite _ (by simp)).sub_left stackSub
    · exact (stackWrite _ (by simp)).sub_left stackSub
    · exact (stackRead _ (by simp)).sub_left stackSub
    · exact ((stackRead _ (by simp)).sub_left stackSub).sub_right tape
    · exact (stackWrite _ (by simp)).sub_left stackSub
    · have enough : 176 ≤ (callSp p).toNat := by rw [callNat]; omega_using [fit]
      rw [rCallStack, FrameStack.belowA, FrameStack.addr_sub' enough]
      exact (Offset.base_disjoint_below _ (by omega_using [sizeMax] : 176 + (sampling.argumentBytes - 4) ≤ 2 ^ 64)).symm
  · have lengths := h.bounds.domainLength
    have maxLength := h.bounds.maxLength
    unfold domainLenValid at lengths
    rcases lengths with eq | eq <;> omega_using [maxLength, eq]

end VG.Proof.Ffdh.Arm.KeySearch

end

end


/-! Reading the seven ARM stack arguments after filling the call frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont

def stackWord (m : Mem) (sp : BitVec 32) (j : Nat) : BitVec 32 :=
  m.readW (off (State.addr sp) (4 * j)) 32

def callValue (p : KeyPublic sampling) (used j : Nat) : BitVec 32 :=
  match j with
  | 0 => p.dp
  | 1 => BitVec.ofNat 32 p.dlen
  | 2 => BitVec.ofNat 32 p.len
  | 3 => p.rp + BitVec.ofNat 32 used
  | 4 => BitVec.ofNat 32 p.len
  | 5 => p.scratch
  | 6 => BitVec.ofNat 32 p.capacity
  | 7 => p.context
  | 8 => BitVec.ofNat 32 p.contextWords
  | _ => 0

theorem stackWord_store (m : Mem) (sp : BitVec 32) (v : BitVec 32) {i j : Nat}
    (hi : i < 10) (hj : j < 10) :
    stackWord (m.writeW (off (State.addr sp) (4 * i)) v) sp j =
      if j = i then v else stackWord m sp j := by
  by_cases same : j = i
  · subst j
    rw [ite_eq_left rfl]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [ite_eq_right same]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega_using [same]) (by omega_using [hj]) (by omega_using [hi])) (by decide)

theorem callMemBase_word (p : KeyPublic sampling) (used : Nat) (m : Mem) (sp : BitVec 32) {j : Nat} (bound : j < 7) :
    stackWord (callMemBase p used m sp) sp j = callValue p used j := by
  unfold callMemBase
  rw [stackWord_store (i := 6) _ _ _ (by decide) (by omega_using [bound]),
    stackWord_store (i := 5) _ _ _ (by decide) (by omega_using [bound]),
    stackWord_store (i := 4) _ _ _ (by decide) (by omega_using [bound]),
    stackWord_store (i := 3) _ _ _ (by decide) (by omega_using [bound]),
    stackWord_store (i := 2) _ _ _ (by decide) (by omega_using [bound]),
    stackWord_store (i := 1) _ _ _ (by decide) (by omega_using [bound]),
    stackWord_store (i := 0) _ _ _ (by decide) (by omega_using [bound])]
  have casesJ : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega_using [bound]
  rcases casesJ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [callValue]

abbrev attemptWords (sampling : GenerationPolicy) : Nat :=
  if sampling.cachedContext then 9 else 7

theorem callMem_word (p : KeyPublic sampling) (used : Nat) (m : Mem) (sp : BitVec 32) {j : Nat}
    (bound : j < attemptWords sampling) : stackWord (callMem p used m sp) sp j = callValue p used j := by
  unfold callMem
  split <;> rename_i active
  · have bound : j < 9 := by simpa only [attemptWords, active, ite_true] using bound
    rw [stackWord_store (i := 8) _ _ _ (by decide) (by omega_using [bound]),
      stackWord_store (i := 7) _ _ _ (by decide) (by omega_using [bound])]
    by_cases eight : j = 8
    · subst j; rfl
    by_cases seven : j = 7
    · subst j; rfl
    simp only [eight, seven, ite_false]
    exact callMemBase_word _ _ _ _ (by omega_using [bound, eight, seven])
  · have bound : j < 7 := by simpa only [attemptWords, active, Bool.false_eq_true, ite_false] using bound
    exact callMemBase_word _ _ _ _ bound

def callRdPlain (p : KeyPublic sampling) (used : Nat) : List Region := [rDomain p, rTape p used] ++ contextRegions p ++ [rCallArgs p]

def callRd (p : KeyPublic sampling) (used : Nat) : List Region :=
  callRdPlain p used ++ KeyConstants.regions sampling p.tablePtr
def callWr (p : KeyPublic sampling) : List Region := [rX p, rY p, rScratch p]

abbrev callState (p : KeyPublic sampling) (used : Nat) (s : State) : State :=
  s.callEntry.withRegions (callRd p used) (callWr p)

abbrev plainCallState (p : KeyPublic sampling) (used : Nat) (s : State) : State :=
  s.callEntry.withRegions (callRdPlain p used) (callWr p)

theorem call_stackArg {p : KeyPublic sampling} {used : Nat} {s : State} {m : Mem} {j : Nat}
    (facts : CallFacts p used) (sp : s.sp = callSp p) (mem : s.mem = callMem p used m (callSp p))
    (bound : j < attemptWords sampling) : stackArg (callState p used s) j = callValue p used j := by
  change s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * j))) 32 = _
  rw [sp, VG.Arm.addr_add (by have fit := facts.argsFit; cases sampling <;> simp only [attemptWords, GenerationPolicy.cachedContext, GenerationPolicy.argumentBytes, Bool.false_eq_true, ite_true, ite_false] at bound fit <;> omega_using [bound, fit]), mem]
  exact callMem_word _ _ _ _ bound

end VG.Proof.Ffdh.Arm.KeySearch
