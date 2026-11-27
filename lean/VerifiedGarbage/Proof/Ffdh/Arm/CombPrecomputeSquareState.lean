module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.Locals
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont

/-! ### `Ffdh.Arm.CombPrecomputeSquare`, which this module and modules that import it used -/

section

/-! One shared Montgomery square doubles the encoded public exponent. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest)

theorem square5_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32} {exponent : Nat}
    (h : Core p sp s) (power : Power5 p exponent s) :
    WP isa (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul 5 5 5) s fun t =>
      Core p sp t ∧ Power5 p (2*exponent) t ∧
      Keeps (State.addr p.base) p.len p.w 5 s.mem t.mem ∧
      Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t := by
  let K := TwoExp.sharedMontgomery p.base sp p.len p.w backend.name backend.mul
    (fun _ _ _ ho ha hb v input => backend.correct v input ho ha hb) backend.stackOk
  have persistent : TwoExp.CallReady p.base sp p.len s := ⟨h.memory.calls.stack,h.memory.fixed⟩
  have operand : Operand 5 := by simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp]
  have positive : 0 < p.P := by have := h.memory.ready.modulus; rw [h.modulus] at this; omega_using [this]
  have bound : numAt s.mem (State.addr p.base) p.w 5 < numAt s.mem (State.addr p.base) p.w 0 := by
    rw [h.modulus,power]
    exact Nat.mod_lt _ positive
  refine WP.mono (K.op_ok s 5 5 5 h.memory.ready persistent operand operand operand (by decide) bound) ?_
  rintro t ⟨ready,_,canonical,value,keeps,_,frame,rest⟩
  have frame' : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem := by
    simpa only [K,h.memory.fixed] using frame
  have memory := h.memory.after_arithmetic ready frame' rest
  have core := h.after_array memory keeps (by decide) (by decide) (by decide)
  rw [h.modulus] at canonical value
  have encoded := VG.Proof.Rsa.FixedBaseComb.mont_square_encoded
    (VG.Proof.Bignum.coprime_pow2 h.odd (64*p.w)) canonical power value
  exact ⟨core,encoded,keeps,frame',rest⟩

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! ### `Ffdh.Arm.CombPrecomputeSquareCounter`, which only this module used -/

section

/-! Native public counter initialization and decrement for basis squaring. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Impl.Ffdh.Arm.CombPrecompute
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem squaresInit_raw (s : State) {base : BitVec 32} {len d : Nat}
    (locals : Locals base len s)
    (saved : s.mem.readW (off (State.addr s.sp) 44) 32=BitVec.ofNat 32 d) :
    WP isa (.block squaresInit) s fun t =>
      t.mem=s.mem.writeW (off (State.addr s.sp) 68) (BitVec.ofNat 32 d) ∧ Rest [.r3,.r12] s t := by
  have a44 : State.addr (s.sp+BitVec.ofNat 32 44)=off (State.addr s.sp) 44 := addr_add (by have := locals.space.nowrap; omega_using [this])
  have a68 : State.addr (s.sp+BitVec.ofNat 32 68)=off (State.addr s.sp) 68 := addr_add (by have := locals.space.nowrap; omega_using [this])
  have read := locals.read (d:=44) (by decide)
  have write := locals.space.write (off:=68) (by decide)
  refine withRest_all (c:=.block squaresInit) [.r3,.r12] ?_ (by rfl) rfl
  unfold squaresInit VG.Impl.Ffdh.Arm.Domain.st
  ffrun [a44,a68,read,write,saved,off,BitVec.add_zero]

theorem squaresNext_raw (s : State) {base : BitVec 32} {len n : Nat}
    (locals : Locals base len s) (positive : 0<n) (fit : n<2^32)
    (saved : s.mem.readW (off (State.addr s.sp) 68) 32=BitVec.ofNat 32 n) :
    WP isa (.block squaresNext) s fun t =>
      (t.mem=s.mem.writeW (off (State.addr s.sp) 68) (BitVec.ofNat 32 (n-1)) ∧ t.z=decide (n-1=0)) ∧ Rest [.r3,.r12] s t := by
  have a68 : State.addr (s.sp+BitVec.ofNat 32 68)=off (State.addr s.sp) 68 := addr_add (by have := locals.space.nowrap; omega_using [this])
  have read := locals.read (d:=68) (by decide)
  have write := locals.space.write (off:=68) (by decide)
  have sub : BitVec.ofNat 32 n-1=BitVec.ofNat 32 (n-1) := BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive
  have val : (BitVec.ofNat 32 (n-1)).toNat=n-1 := Nat.mod_eq_of_lt (by omega_using [fit])
  refine withRest_all (c:=.block squaresNext) [.r3,.r12] ?_ (by rfl) rfl
  unfold squaresNext VG.Impl.Ffdh.Arm.Domain.st
  ffrun [a68,read,write,saved,sub,val,off,BitVec.add_zero,subFlags]
  exact ofNat_beq_zero (by omega_using [fit])

end VG.Proof.Ffdh.Arm.CombBuilder

end

end


/-! Persistent basis state across the public square-loop counter writes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def squareNarrowWrites (p : Inputs) (sp : BitVec 32) : List Region :=
  [⟨State.addr p.base,8*p.len⟩,⟨off (State.addr sp) 68,4⟩,FrameStack.belowA sp 48]

def SquareCount (sp : BitVec 32) (n : Nat) (s : State) : Prop :=
  s.mem.readW (off (State.addr sp) 68) 32=BitVec.ofNat 32 n

theorem Memory.squareNarrowContextEq {p : Inputs} {sp : BitVec 32} {s t : State}
    (h : Memory p sp s) (frame : Frame (squareNarrowWrites p sp) s.mem t.mem) :
    WorkspaceEq (State.addr p.output) (bytes p) s.mem t.mem := by
  apply WorkspaceEq.of_frame (by have := h.output.fits; omega_using [this]) frame
  intro r hr
  simp only [squareNarrowWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact h.workspaceSeparate.symm
  · exact h.localSeparate.symm.sub_right (Offset.sub_base _ (by decide))
  · exact h.callSeparate

theorem Memory.squareNarrowRead36 {p : Inputs} {sp : BitVec 32} {s t : State}
    (h : Memory p sp s) (frame : Frame (squareNarrowWrites p sp) s.mem t.mem) :
    t.mem.readW (off (State.addr sp) 36) 32=s.mem.readW (off (State.addr sp) 36) 32 := by
  apply frame.readW (r:=⟨off (State.addr sp) 36,4⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  simp only [squareNarrowWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  have sub : (⟨off (State.addr sp) 36,4⟩ : Region).Sub ⟨State.addr sp,72⟩ := Offset.sub_base _ (by decide)
  rcases hr with rfl|rfl|rfl
  · have sep := h.context.locals.separate
    rw [h.fixed] at sep
    exact sep.sub_left sub
  · exact Offset.disjoint _ (Or.inl (by decide : 36+4≤68)) (by decide) (by decide)
  · have fit : 48≤sp.toNat := by rw [←h.fixed]; exact h.calls.stack.fit
    rw [FrameStack.belowA,FrameStack.addr_sub' fit]
    exact ((Offset.below_disjoint _ (by decide : 48+72≤2^64)).symm).sub_left sub

theorem control68_state (s : State) {p : Inputs} {sp : BitVec 32} {E n : Nat}
    (h : Core p sp s) (power : Power5 p E s) {t : State}
    (mem : t.mem=s.mem.writeW (off (State.addr s.sp) 68) (BitVec.ofNat 32 n))
    (rest : Rest [.r3,.r12] s t) :
    Core p sp t ∧ Power5 p E t ∧ SquareCount sp n t ∧
      Frame (squareNarrowWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  have raw : Frame [⟨off (State.addr s.sp) 68,4⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have r : Rest roundClobbers s t := rest.mono (by simp [roundClobbers])
  have next := h.memory.after_control (by simp) raw r ((rest.gpr .r0 (by simp)).trans h.memory.context.ptr)
  refine ⟨h.after_workspace next.1 next.2,power.after_workspace h next.2,?_,?_,r⟩
  · change t.mem.readW (off (State.addr sp) 68) 32=BitVec.ofNat 32 n
    rw [mem,←h.memory.fixed,Mem.readW_writeW_self32]
  · apply raw.sub
    intro region hr
    have eq := List.mem_singleton.mp hr
    subst region
    refine ⟨⟨off (State.addr sp) 68,4⟩,by simp [squareNarrowWrites],?_⟩
    rw [h.memory.fixed]
    exact fun _ hx => hx

theorem squaresInit_state (s : State) {p : Inputs} {sp : BitVec 32} {E : Nat}
    (h : Core p sp s) (power : Power5 p E s) :
    WP isa (.block VG.Impl.Ffdh.Arm.CombPrecompute.squaresInit) s fun t =>
      Core p sp t ∧ Power5 p E t ∧ SquareCount sp (Spec.Rsa.FixedBaseComb.rows (bits p)) t ∧
      Frame (squareNarrowWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (squaresInit_raw s h.memory.context.locals (by rw [h.memory.fixed]; exact h.memory.rowsSaved)) ?_
  rintro t ⟨mem,rest⟩
  exact control68_state s h power mem rest

theorem squaresNext_state (s : State) {p : Inputs} {sp : BitVec 32} {E n : Nat}
    (h : Core p sp s) (power : Power5 p E s) (positive : 0<n) (fits : n<2^32)
    (counter : SquareCount sp n s) :
    WP isa (.block VG.Impl.Ffdh.Arm.CombPrecompute.squaresNext) s fun t =>
      Core p sp t ∧ Power5 p E t ∧ SquareCount sp (n-1) t ∧ t.z=decide (n-1=0) ∧
      Frame (squareNarrowWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (squaresNext_raw s h.memory.context.locals positive fits (by rw [h.memory.fixed]; exact counter)) ?_
  rintro t ⟨⟨mem,zero⟩,rest⟩
  obtain ⟨core,pow,count,frame,r⟩ := control68_state s h power mem rest
  exact ⟨core,pow,count,zero,frame,r⟩

end VG.Proof.Ffdh.Arm.CombBuilder
