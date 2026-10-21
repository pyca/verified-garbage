module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.Arm.CopyBytes
import VerifiedGarbage.Proof.Bignum.Arm.CopyRegion
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Buffer and frame facts for copying and shaping a parameter candidate. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

def shapeValues (dst src : BitVec 32) (n bits : Nat) : Nat → BitVec 32
  | 4 => dst
  | 12 => BitVec.ofNat 32 n
  | 16 => src
  | 24 => BitVec.ofNat 32 bits
  | _ => 0

def shapeSlots : List Nat := [4, 12, 16, 24]

structure ShapeContext (dst src : BitVec 32) (bs : List Byte) (bits : Nat) (s : State) : Prop where
  frame : SavedFrame (shapeValues dst src bs.length bits) shapeSlots s
  minBits : 9 ≤ bits
  maxBits : bits ≤ 8192
  length : bs.length = (bits + 7) / 8
  sourceFits : src.toNat + bs.length ≤ 2 ^ 32
  destFits : dst.toNat + bs.length ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr src) bs.length
  write : InRegions s.wr (State.addr dst) bs.length
  buffers : (⟨State.addr src, bs.length⟩ : Region).Disjoint ⟨State.addr dst, bs.length⟩
  stack : (⟨State.addr dst, bs.length⟩ : Region).Disjoint ⟨State.addr s.sp, 72⟩
  bytes : Spec.Rsa.bytesAt s.mem (State.addr src) bs.length = bs

theorem shapeSlots_bound {d : Nat} (member : d ∈ shapeSlots) : d + 4 ≤ 72 := by
  simp only [shapeSlots, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

theorem ShapeContext.size {dst src : BitVec 32} {bs : List Byte} {bits : Nat} {s : State}
    (h : ShapeContext dst src bs bits s) : 2 ≤ bs.length ∧ bs.length ≤ 1024 := by
  have := h.length
  have := h.minBits
  have := h.maxBits
  omega

theorem ShapeContext.byte {dst src : BitVec 32} {bs : List Byte} {bits : Nat} {s : State}
    (h : ShapeContext dst src bs bits s) {i : Nat} (bound : i < bs.length) :
    s.mem (State.addr (src + BitVec.ofNat 32 i)) = bs[i]?.getD 0 := by
  have value := congrArg (fun l : List Byte => l[i]?) h.bytes
  rw [VG.Arm.addr_add (by have := h.sourceFits; omega)]
  simpa only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range bound,
    Option.map_some, List.getElem?_eq_getElem bound, Option.getD_some, Option.some.injEq] using value

theorem ShapeContext.copyCtx {dst src : BitVec 32} {bs : List Byte} {bits : Nat} {s : State}
    (h : ShapeContext dst src bs bits s) : VG.Proof.Bignum.Arm.CopyCtx s src dst bs.length := by
  exact VG.Proof.Bignum.Arm.copyCtx_of_regions s src dst (by have := h.size; omega)
    h.sourceFits h.destFits h.read h.write h.buffers

theorem ShapeContext.writeByte {dst src : BitVec 32} {bs : List Byte} {bits : Nat} {s : State}
    (h : ShapeContext dst src bs bits s) {i : Nat} (bound : i < bs.length) :
    InRegions s.wr (State.addr (dst + BitVec.ofNat 32 i)) 1 := h.copyCtx.writable i bound

theorem ShapeContext.readByte {dst src : BitVec 32} {bs : List Byte} {bits : Nat} {s : State}
    (h : ShapeContext dst src bs bits s) {i : Nat} (bound : i < bs.length) :
    InRegions (s.rd ++ s.wr) (State.addr (dst + BitVec.ofNat 32 i)) 1 := by
  obtain ⟨r, member, contains⟩ := h.writeByte bound
  exact ⟨r, List.mem_append_right _ member, contains⟩

theorem ShapeContext.containsByte {dst src : BitVec 32} {bs : List Byte} {bits : Nat} {s : State}
    (h : ShapeContext dst src bs bits s) {i : Nat} (bound : i < bs.length) :
    (⟨State.addr dst, bs.length⟩ : Region).Contains (State.addr (dst + BitVec.ofNat 32 i)) 1 := by
  rw [VG.Arm.addr_add (by have := h.destFits; omega)]
  exact Offset.contains_base _ (by omega) (by have := h.size; omega)

theorem ShapeContext.after_output {dst src : BitVec 32} {bs : List Byte} {bits : Nat} {s t : State}
    {rs : List Reg} (h : ShapeContext dst src bs bits s)
    (frame : Frame [⟨State.addr dst, bs.length⟩] s.mem t.mem) (rest : Rest rs s t) :
    ShapeContext dst src bs bits t := by
  refine ⟨h.frame.after_output (fun _ hd => shapeSlots_bound hd) frame rest h.stack,
    h.minBits, h.maxBits, h.length, h.sourceFits, h.destFits, ?_, ?_, h.buffers, ?_, ?_⟩
  · rw [rest.rd, rest.wr]
    exact h.read
  · rw [rest.wr]
    exact h.write
  · rw [rest.sp]
    exact h.stack
  · rw [VG.Proof.Bignum.Arm.rsa_bytes_frame frame (by have := h.size; omega)
      (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact h.buffers)]
    exact h.bytes

theorem ShapeContext.after_memory {dst src : BitVec 32} {bs : List Byte} {bits : Nat} {s t : State}
    {rs : List Reg} (h : ShapeContext dst src bs bits s) (memory : t.mem = s.mem) (rest : Rest rs s t) :
    ShapeContext dst src bs bits t := by
  have frame : Frame [⟨State.addr dst, bs.length⟩] s.mem t.mem := by
    rw [memory]
    exact Frame.refl _ _
  exact h.after_output frame rest

end VG.Proof.Ffdh.Arm.ParameterCandidate
