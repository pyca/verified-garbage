module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Arm.CopyRegion
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.Arm.CopyBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions

/-! ### `Ffdh.Arm.ParameterCandidate.ShapeContext`, which this module and modules that import it used -/

section

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
  omega_arith

theorem ShapeContext.byte {dst src : BitVec 32} {bs : List Byte} {bits : Nat} {s : State}
    (h : ShapeContext dst src bs bits s) {i : Nat} (bound : i < bs.length) :
    s.mem (State.addr (src + BitVec.ofNat 32 i)) = bs[i]?.getD 0 := by
  have value := congrArg (fun l : List Byte => l[i]?) h.bytes
  rw [VG.Arm.addr_add (by have := h.sourceFits; omega_using [bound, this])]
  simpa only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range bound,
    Option.map_some, List.getElem?_eq_getElem bound, Option.getD_some, Option.some.injEq] using value

theorem ShapeContext.copyCtx {dst src : BitVec 32} {bs : List Byte} {bits : Nat} {s : State}
    (h : ShapeContext dst src bs bits s) : VG.Proof.Bignum.Arm.CopyCtx s src dst bs.length := by
  exact VG.Proof.Bignum.Arm.copyCtx_of_regions s src dst (by have := h.size; omega_using [this])
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
  rw [VG.Arm.addr_add (by have := h.destFits; omega_using [bound, this])]
  exact Offset.contains_base _ (by omega_using [bound]) (by have := h.size; omega_using [bound, this])

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
  · rw [VG.Proof.Bignum.Arm.rsa_bytes_frame frame (by have := h.size; omega_using [this])
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

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.ShapeTop`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.ShapeFirst`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.ShapeBits`, which only this module used -/

section

/-! Native 32-bit mask construction implements the shared first-octet
shaping rule, including an exact byte boundary. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG

private theorem topMask_nat (x j : Nat) :
    x % 2 ^ (j + 1) ||| 2 ^ j = x % 2 ^ j + 2 ^ j := by
  rw [← Nat.or_two_pow_eq_add_of_lt (Nat.mod_lt x (Nat.two_pow_pos j))]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
  by_cases same : i = j
  · simp [same]
  · have cut : (i < j + 1) = (i < j) := propext (by omega_using [same])
    simp only [cut]

theorem topMask_byte (b : Byte) {j : Nat} (bound : j < 8) :
    (((b.setWidth 32 &&& BitVec.ofNat 32 (2 ^ (j + 1) - 1)) |||
      BitVec.ofNat 32 (2 ^ j)).setWidth 8) = VG.Proof.Ffdh.ParameterCandidate.topByte j b := by
  have high : 2 ^ j < 256 := Nat.pow_lt_pow_right (by decide) bound
  have full : 2 ^ (j + 1) ≤ 256 := Nat.pow_le_pow_right (n := 2) (i := j + 1) (j := 8) (by decide) (by omega_using [bound])
  have byte := b.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_and,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_using [] : b.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega_using [full] : 2 ^ (j + 1) - 1 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega_using [high] : 2 ^ j < 2 ^ 32), Nat.and_two_pow_sub_one_eq_mod,
    topMask_nat, VG.Proof.Ffdh.ParameterCandidate.topByte_value bound]
  apply Nat.mod_eq_of_lt
  have lo := Nat.mod_lt b.toNat (Nat.two_pow_pos j)
  have pow : 2 ^ (j + 1) = 2 ^ j * 2 := Nat.pow_succ 2 j
  omega

theorem maskTopWord {j : Nat} (bound : j < 8) :
    (BitVec.ofNat 32 (2 ^ (j + 1) - 1) >>> 1) + 1 = BitVec.ofNat 32 (2 ^ j) := by
  have full : 2 ^ (j + 1) ≤ 256 := Nat.pow_le_pow_right (n := 2) (i := j + 1) (j := 8) (by decide) (by omega_using [bound])
  have pow : 2 ^ (j + 1) = 2 ^ j * 2 := Nat.pow_succ 2 j
  have positive := Nat.two_pow_pos j
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega_using [full] : 2 ^ (j + 1) - 1 < 2 ^ 32), BitVec.toNat_ofNat]
  have half : (2 ^ (j + 1) - 1) / 2 ^ 1 + 1 = 2 ^ j := by omega_using [positive]
  rw [half]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! Apply the generated mask and high bit to the candidate's first octet. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem shapeFirst_ok (s : State) (dst : BitVec 32) {j : Nat} (bound : j < 8)
    (slotRead : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 4)) 4)
    (slot : s.mem.readW (State.addr (s.sp + 4)) 32 = dst)
    (read : InRegions (s.rd ++ s.wr) (State.addr dst) 1)
    (write : InRegions s.wr (State.addr dst) 1)
    (mask : s.gpr .r7 = BitVec.ofNat 32 (2 ^ (j + 1) - 1)) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeFirst) s fun t =>
      (t.gpr .r4 = dst ∧ t.mem = s.mem.writeW (State.addr dst)
        (VG.Proof.Ffdh.ParameterCandidate.topByte j (s.mem (State.addr dst)))) ∧
        Rest [.r3, .r4, .r9] s t := by
  refine withRest_all [.r3, .r4, .r9] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.shapeFirst
  ffrun [show (4#32) = (4 : BitVec 32) from rfl, BitVec.add_zero,
    slotRead, slot, read, write, mask, maskTopWord bound, topMask_byte _ bound]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! First-octet shaping preserves all other copied bytes and saved arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

theorem shapeTop_ok (s : State) {dst src : BitVec 32} {bs : List Byte} {bits j : Nat}
    (h : ShapeContext dst src bs bits s) (bound : j < 8)
    (copied : ∀ i < bs.length, s.mem (State.addr (dst + BitVec.ofNat 32 i)) = bs[i]?.getD 0)
    (mask : s.gpr .r7 = BitVec.ofNat 32 (2 ^ (j + 1) - 1)) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeFirst) s fun t =>
      ShapeContext dst src bs bits t ∧ t.gpr .r4 = dst ∧
      (∀ i < bs.length, t.mem (State.addr (dst + BitVec.ofNat 32 i)) =
        (VG.Proof.Ffdh.ParameterCandidate.topCut bs j).getD i 0) ∧
      Frame [⟨State.addr dst, bs.length⟩] s.mem t.mem ∧ Rest [.r3, .r4, .r9] s t := by
  have positive : 0 < bs.length := by have := h.size; omega_using [this]
  have read := h.readByte (i := 0) positive
  have write := h.writeByte (i := 0) positive
  simp only [BitVec.add_zero] at read write
  refine WP.mono (shapeFirst_ok s dst bound (h.frame.read (d := 4) (by decide))
    (h.frame.saved 4 (by decide)) read write mask) ?_
  rintro t ⟨⟨ptr, mem⟩, rest⟩
  have contains := h.containsByte (i := 0) positive
  simp only [BitVec.add_zero] at contains
  have frame : Frame [⟨State.addr dst, bs.length⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (by simp) _ contains
  refine ⟨h.after_output frame rest, ptr, ?_, frame, rest⟩
  intro i hi
  rw [mem, VG.WriteBytes.writeW8_apply, VG.Proof.Ffdh.ParameterCandidate.topCut_getD]
  by_cases first : i = 0
  · subst i
    simp only [BitVec.add_zero, ite_true]
    have byte := copied 0 positive
    simp only [BitVec.add_zero] at byte
    rw [byte]
    rfl
  · have different : State.addr (dst + BitVec.ofNat 32 i) ≠ State.addr dst := by
      intro same
      have eq := h.copyCtx.distinct i hi 0 positive (by simpa using same)
      exact first eq
    rw [ite_eq_right different, ite_eq_right first]
    exact copied i hi

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.ShapeMasks`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.Mask`, which only this module used -/

section

/-! The same native mask loop covers partial bytes and full 32-bit limbs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem maskStep_ok (s : State) {n i : Nat} (bound : n ≤ 32) (more : i < n)
    (mask : s.gpr .r7 = BitVec.ofNat 32 (2 ^ i - 1))
    (count : s.gpr .r6 = BitVec.ofNat 32 (n - i)) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.maskStep) s fun t =>
      (t.gpr .r7 = BitVec.ofNat 32 (2 ^ (i + 1) - 1) ∧
        t.gpr .r6 = BitVec.ofNat 32 (n - (i + 1)) ∧
        t.z = decide (i + 1 = n) ∧ t.mem = s.mem) ∧ Rest [.r6, .r7] s t := by
  have inc : BitVec.ofNat 32 (2 ^ i - 1) + BitVec.ofNat 32 (2 ^ i - 1) + 1 =
      BitVec.ofNat 32 (2 ^ (i + 1) - 1) := by
    change BitVec.ofNat 32 (2 ^ i - 1) + BitVec.ofNat 32 (2 ^ i - 1) + BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
    congr 1
    have positive := Nat.two_pow_pos i
    rw [Nat.pow_succ]
    omega_using [positive]
  have dec : BitVec.ofNat 32 (n - i) - 1 = BitVec.ofNat 32 (n - (i + 1)) := by
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [more])]
    congr 1
  have zero : (BitVec.ofNat 32 (n - (i + 1)) == (0 : BitVec 32)) = decide (i + 1 = n) := by
    rw [ofNat_beq_zero (k := n - (i + 1)) (by omega_using [bound])]
    simp only [show n - (i + 1) = 0 ↔ i + 1 = n by omega_using [more]]
  refine withRest_all [.r6, .r7] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.maskStep
  ffrun [mask, count, inc, dec, zero]

/-- Construct a low-bit mask without a shift by the register width. -/
theorem maskLoop_ok (s : State) {n : Nat} (positive : 0 < n) (bound : n ≤ 32)
    (mask : s.gpr .r7 = 0) (count : s.gpr .r6 = BitVec.ofNat 32 n) :
    WP isa (.loop (.block VG.Impl.Ffdh.Arm.ParameterCandidate.maskStep) .ne) s fun t =>
      t.gpr .r7 = BitVec.ofNat 32 (2 ^ n - 1) ∧
      t.gpr .r6 = 0 ∧ t.mem = s.mem ∧ Rest [.r6, .r7] s t := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧
    t.gpr .r7 = BitVec.ofNat 32 (2 ^ i - 1) ∧
    t.gpr .r6 = BitVec.ofNat 32 (n - i) ∧ t.mem = s.mem ∧ Rest [.r6, .r7] s t
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hm, hc, mem, rest⟩ := h
    refine WP.mono (maskStep_ok t bound (by omega_using [hik, hk]) hm hc) ?_
    rintro u ⟨⟨um, uc, uz, umem⟩, ur⟩
    by_cases last : i + 1 = n
    · left
      refine ⟨?_, ?_⟩
      · change some (!u.z) = some false
        simp only [uz, last, decide_true, Bool.not_true]
      · exact ⟨last ▸ um, by simpa [last] using uc,
          umem.trans mem, rest.trans ur⟩
    · right
      refine ⟨?_, k - 1, by omega_using [hk], i + 1, by omega_using [hik, hk], by omega_using [hik, hk, last],
        um, uc, umem.trans mem, rest.trans ur⟩
      change some (!u.z) = some true
      simp only [uz, last, decide_false, Bool.not_false]
  · exact ⟨0, by omega_using [], positive, by simpa using mask,
      by simpa using count, rfl, Rest.refl _ _⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! Derive the first-byte mask from the public bit length. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem maskCount (bits : Nat) (positive : 0 < bits) (fits : bits < 2 ^ 32) :
    ((BitVec.ofNat 32 bits - 1) &&& 7) + 1 = BitVec.ofNat 32 ((bits - 1) % 8 + 1) := by
  change ((BitVec.ofNat 32 bits - BitVec.ofNat 32 1) &&& 7) + 1 = _
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_using [fits] : bits - 1 < 2 ^ 32)]
  change ((bits - 1 &&& (2 ^ 3 - 1)) + 1) % 2 ^ 32 = (((bits - 1) % 8 + 1) % 2 ^ 32)
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem shapeMaskHead_ok (s : State) {bits : Nat} (positive : 0 < bits) (fits : bits < 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 24)) 4)
    (value : s.mem.readW (State.addr (s.sp + 24)) 32 = BitVec.ofNat 32 bits) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeMaskHead) s fun t =>
      (t.gpr .r6 = BitVec.ofNat 32 ((bits - 1) % 8 + 1) ∧ t.gpr .r7 = 0 ∧ t.mem = s.mem) ∧
        Rest [.r6, .r7] s t := by
  refine withRest_all [.r6, .r7] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.shapeMaskHead
  ffrun [show (24#32) = (24 : BitVec 32) from rfl, read, value, maskCount bits positive fits]

theorem shapeMasks_ok (s : State) {bits : Nat} (positive : 0 < bits) (fits : bits < 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 24)) 4)
    (value : s.mem.readW (State.addr (s.sp + 24)) 32 = BitVec.ofNat 32 bits) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.shapeMasks s fun t =>
      t.gpr .r7 = BitVec.ofNat 32 (2 ^ ((bits - 1) % 8 + 1) - 1) ∧ t.mem = s.mem ∧
        Rest [.r6, .r7] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.shapeMasks
  refine WP.seq (WP.mono (shapeMaskHead_ok s positive fits read value) ?_)
  rintro u ⟨⟨count, mask, mem⟩, rest⟩
  have small := Nat.mod_lt (bits - 1) (by decide : 0 < 8)
  refine WP.mono (maskLoop_ok u (by omega_using []) (by omega_using []) mask count) ?_
  rintro t ⟨result, _, memory, keep⟩
  exact ⟨result, memory.trans mem, rest.trans keep⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.ShapeCopy`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.ShapeCopyHead`, which this module and modules that import it used -/

section

/-! Load the common RSA byte-copy routine's native arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem shapeCopyHead_ok (s : State) {dst src : BitVec 32} {bs : List Byte} {bits : Nat}
    (h : ShapeContext dst src bs bits s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeCopyHead) s fun t =>
      (t.gpr .r0 = dst ∧ t.gpr .r1 = src ∧ t.gpr .lr = BitVec.ofNat 32 bs.length ∧ t.mem = s.mem) ∧
        Rest [.r0, .r1, .lr] s t := by
  refine withRest_all [.r0, .r1, .lr] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.shapeCopyHead
  ffrun [h.frame.read (d := 4) (by decide), h.frame.read (d := 12) (by decide),
    h.frame.read (d := 16) (by decide), h.frame.saved 4 (by decide),
    h.frame.saved 12 (by decide), h.frame.saved 16 (by decide), shapeValues]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Reuse RSA's verified disjoint-buffer copy for the candidate tape prefix. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

theorem shapeCopy_ok (s : State) {dst src : BitVec 32} {bs : List Byte} {bits : Nat}
    (h : ShapeContext dst src bs bits s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.shapeCopy s fun t =>
      ShapeContext dst src bs bits t ∧
      (∀ i < bs.length, t.mem (State.addr (dst + BitVec.ofNat 32 i)) = bs[i]?.getD 0) ∧
      Frame [⟨State.addr dst, bs.length⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.shapeCopy
  refine WP.seq (WP.mono (shapeCopyHead_ok s h) ?_)
  rintro u ⟨⟨dest, source, count, memory⟩, rest⟩
  have context := h.after_memory memory rest
  refine WP.mono (copyBytes_ok u
    (copyCtx_of_regions u src dst (by have := h.size; omega_using [this]) h.sourceFits h.destFits
      context.read context.write h.buffers)
    (by have := h.size; omega_using [this]) source dest count) ?_
  intro t copied
  have frame := copied.frame h.destFits
  refine ⟨context.after_output frame copied.rest, ?_, ?_, (rest.mono (by simp)).trans copied.rest⟩
  · intro i hi
    rw [copied.copied i hi, memory]
    exact h.byte hi
  · rw [memory] at frame
    exact frame

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.ShapeLast`, which only this module used -/

section

/-! Make the copied candidate odd by setting its final octet's low bit. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem byteOrOne (b : Byte) : ((b.setWidth 32 ||| (1 : BitVec 32)).setWidth 8) = b ||| 1 := by
  rw [BitVec.setWidth_or]
  simp

theorem shapeLast_ok (s : State) (n : Nat)
    (slotRead : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 12)) 4)
    (slot : s.mem.readW (State.addr (s.sp + 12)) 32 = BitVec.ofNat 32 n)
    (read : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r4 + BitVec.ofNat 32 n - 1)) 1)
    (write : InRegions s.wr (State.addr (s.gpr .r4 + BitVec.ofNat 32 n - 1)) 1) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeLast) s fun t =>
      (t.gpr .r4 = s.gpr .r4 + BitVec.ofNat 32 n - 1 ∧
        t.mem = s.mem.writeW (State.addr (s.gpr .r4 + BitVec.ofNat 32 n - 1))
          (s.mem (State.addr (s.gpr .r4 + BitVec.ofNat 32 n - 1)) ||| 1)) ∧
        Rest [.r3, .r4, .r5] s t := by
  refine withRest_all [.r3, .r4, .r5] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.shapeLast
  ffrun [show (12#32) = (12 : BitVec 32) from rfl, BitVec.add_zero,
    slotRead, slot, read, write, byteOrOne]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! Setting the final bit preserves the full shaped encoding and its frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

theorem shapeOdd_ok (s : State) {dst src : BitVec 32} {bs xs : List Byte} {bits : Nat}
    (h : ShapeContext dst src bs bits s) (length : xs.length = bs.length)
    (copied : ∀ i < bs.length, s.mem (State.addr (dst + BitVec.ofNat 32 i)) = xs[i]?.getD 0)
    (dest : s.gpr .r4 = dst) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeLast) s fun t =>
      ShapeContext dst src bs bits t ∧
      (∀ i < bs.length, t.mem (State.addr (dst + BitVec.ofNat 32 i)) =
        (VG.Proof.Ffdh.ParameterCandidate.lastOne xs).getD i 0) ∧
      Frame [⟨State.addr dst, bs.length⟩] s.mem t.mem ∧ Rest [.r3, .r4, .r5] s t := by
  have size := h.size
  have last : bs.length - 1 < bs.length := by omega_using [size]
  have ptr : s.gpr .r4 + BitVec.ofNat 32 bs.length - 1 =
      dst + BitVec.ofNat 32 (bs.length - 1) := by
    rw [dest, BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg]
    change dst + (BitVec.ofNat 32 bs.length - BitVec.ofNat 32 1) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [size])]
  refine WP.mono (shapeLast_ok s bs.length (h.frame.read (d := 12) (by decide))
    (h.frame.saved 12 (by decide)) (by rw [ptr]; exact h.readByte last)
    (by rw [ptr]; exact h.writeByte last)) ?_
  rintro t ⟨⟨_, mem⟩, rest⟩
  rw [ptr, copied _ last] at mem
  have frame : Frame [⟨State.addr dst, bs.length⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (by simp) _ (h.containsByte last)
  refine ⟨h.after_output frame rest, ?_, frame, rest⟩
  intro i hi
  have hi' : i < xs.length := by omega_using [length, hi]
  rw [VG.Proof.Ffdh.ParameterCandidate.lastOne_getD hi', length, mem, VG.WriteBytes.writeW8_apply]
  by_cases final : i + 1 = bs.length
  · have same : i = bs.length - 1 := by omega_using [final]
    subst i
    rw [ite_eq_left rfl, ite_eq_left final]
    rfl
  · have different : State.addr (dst + BitVec.ofNat 32 i) ≠
        State.addr (dst + BitVec.ofNat 32 (bs.length - 1)) := by
      intro same
      have := h.copyCtx.distinct i hi (bs.length - 1) last same
      omega_using [size, final, this]
    rw [ite_eq_right different, ite_eq_right final]
    exact copied i hi

end VG.Proof.Ffdh.Arm.ParameterCandidate
