module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontData
public import VerifiedGarbage.Proof.MillerRabin.Arm.Contract
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Ffdh.Arm.ParameterCandidate.RoundData`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.KeptArrays`, which only this module used -/

section

/-! The shared RSA arithmetic and Miller–Rabin preservation contracts also
protect constants in arrays above the eight Montgomery arithmetic arrays. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt Keeps)
open VG.Proof.MillerRabin.Arm (KeepsLite wJs)

theorem operand_keeps_extended {m m' : Mem} {base : Addr} {capacity w o q d n : Nat}
    (keep : Keeps base capacity w o m m') (fits : arrAt w 28 ≤ 8 * capacity) (bound : q < 28)
    (q2 : q ≠ 2) (q3 : q ≠ 3) (qo : q ≠ o) (bytes : d + n ≤ 8 * (w + 2)) :
    m'.read (off base (arrAt w q + d)) n = m.read (off base (arrAt w q + d)) n := by
  have arrayFit := Nat.le_trans (array_end_le bound) fits
  apply Mem.read_congr
  intro i hi
  change m' (base + BitVec.ofNat 64 (arrAt w q + d) + BitVec.ofNat 64 i) = _
  rw [Offset.add_add]
  apply keep (arrAt w q + d + i) (by omega_using [bytes, arrayFit, hi])
  intro a ha
  have different : q ≠ a := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact q2
    · exact q3
    · exact qo
  have := array_sep (w := w) different
  omega_using [bytes, hi, this]

theorem round_keeps_read {m m' : Mem} {base : Addr} {capacity w d n : Nat}
    (keep : KeepsLite base capacity w m m') (fit : d + n ≤ 8 * capacity)
    (header : ∀ k ∈ [23, 26, 29, 30], d + n ≤ 8 * k ∨ 8 * k + 8 ≤ d)
    (arrays : ∀ j ∈ wJs, d + n ≤ arrAt w j ∨ arrAt w j + 8 * (w + 2) ≤ d) :
    m'.read (off base d) n = m.read (off base d) n := by
  apply Mem.read_congr
  intro i hi
  change m' (base + BitVec.ofNat 64 d + BitVec.ofNat 64 i) = _
  rw [Offset.add_add]
  apply keep (d + i) (by omega_using [fit, hi])
  · intro k hk
    have := header k hk
    omega_using [hi, this]
  · intro j hj
    have := arrays j hj
    omega_using [hi, this]

theorem round_keeps_header {m m' : Mem} {base : Addr} {capacity w d bits : Nat}
    (keep : KeepsLite base capacity w m m') (size : 128 ≤ 8 * capacity) (fit : d + bits / 8 ≤ 128) :
    m'.readW (off base d) bits = m.readW (off base d) bits := by
  unfold Mem.readW
  rw [round_keeps_read keep (by omega_using [size, fit]) (by
    intro k hk
    have bound : ∀ k ∈ [23, 26, 29, 30], 16 ≤ k := by decide
    have := bound k hk
    left
    omega_using [fit, this]) (by
    intro j _
    left
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes]
    omega_using [fit])]

theorem round_keeps_array {m m' : Mem} {base : Addr} {capacity w q d n : Nat}
    (keep : KeepsLite base capacity w m m') (fits : arrAt w 28 ≤ 8 * capacity) (bound : q < 28)
    (unwritten : q ∉ wJs) (bytes : d + n ≤ 8 * (w + 2)) :
    m'.read (off base (arrAt w q + d)) n = m.read (off base (arrAt w q + d)) n := by
  have arrayFit := Nat.le_trans (array_end_le bound) fits
  refine round_keeps_read keep (by omega_using [bytes, arrayFit]) ?_ ?_
  · intro k hk
    have upper : ∀ k ∈ [23, 26, 29, 30], k ≤ 30 := by decide
    have := upper k hk
    right
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes]
    omega_using [this]
  · intro j hj
    have different : q ≠ j := fun same => unwritten (same ▸ hj)
    have := array_sep (w := w) different
    omega_using [bytes, this]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! The phase's immutable shared-round constants. Witness imports,
Montgomery conversions and the shared round itself preserve these data. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Keeps)
open VG.Proof.MillerRabin.Arm (LayoutLite PreparedLite KeepsLite wJs)

structure RoundData (base : BitVec 32) (capacity w n : Nat) (m : Mem) : Prop where
  data : MontData base capacity w m
  minWords : 4 ≤ w
  maxWords : w ≤ 128
  fits : arrAt w 28 ≤ 8 * capacity
  large : 3 ≤ n
  odd : n % 2 = 1
  modulus : numAt m (VG.Arm.State.addr base) w 0 = n
  r2 : numAt m (VG.Arm.State.addr base) w 4 = 2 ^ (128 * w) % n
  one : numAt m (VG.Arm.State.addr base) w 9 = 2 ^ (64 * w) % n
  minus : numAt m (VG.Arm.State.addr base) w 10 = n - 2 ^ (64 * w) % n
  exponent : numAt m (VG.Arm.State.addr base) w 27 = Proof.MillerRabin.Round.exponent n
  power : m.readW (off (VG.Arm.State.addr base) (arrAt w 27 + 8 * w)) 64 =
    BitVec.twoPow 64 ((Spec.Rsa.splitTwos (n - 1)).1 % 64)

theorem RoundData.layout {base : BitVec 32} {capacity w n : Nat} {m : Mem}
    (h : RoundData base capacity w n m) : LayoutLite m (VG.Arm.State.addr base) capacity := by
  refine ⟨h.data.layout, ?_⟩
  rw [h.data.width]
  exact ⟨h.minWords, h.maxWords, h.fits⟩

theorem RoundData.prepared {base : BitVec 32} {capacity w n : Nat} {m : Mem}
    (h : RoundData base capacity w n m) (witness : numAt m (VG.Arm.State.addr base) w 5 < n) :
    PreparedLite m (VG.Arm.State.addr base) := by
  unfold PreparedLite
  rw [h.data.width]
  dsimp only
  rw [h.modulus]
  exact ⟨h.large, h.odd, h.data.inverse, witness, h.one, h.minus, h.exponent, h.power⟩

theorem RoundData.after_reads {base : BitVec 32} {capacity w n : Nat} {m m' : Mem}
    (h : RoundData base capacity w n m)
    (header : ∀ d, d + 8 ≤ 128 → m'.readW (off (VG.Arm.State.addr base) d) 64 =
      m.readW (off (VG.Arm.State.addr base) d) 64)
    (arrays : ∀ q ∈ [0, 4, 9, 10, 27], numAt m' (VG.Arm.State.addr base) w q =
      numAt m (VG.Arm.State.addr base) w q)
    (power : m'.readW (off (VG.Arm.State.addr base) (arrAt w 27 + 8 * w)) 64 =
      m.readW (off (VG.Arm.State.addr base) (arrAt w 27 + 8 * w)) 64) : RoundData base capacity w n m' :=
  ⟨(h.data.after_reads header (arrays 0 (by simp))).1, h.minWords, h.maxWords, h.fits, h.large, h.odd,
    (arrays 0 (by simp)).trans h.modulus, (arrays 4 (by simp)).trans h.r2,
    (arrays 9 (by simp)).trans h.one, (arrays 10 (by simp)).trans h.minus,
    (arrays 27 (by simp)).trans h.exponent, power.trans h.power⟩

theorem RoundData.after_operand {base : BitVec 32} {capacity w n o : Nat} {m m' : Mem}
    (h : RoundData base capacity w n m) (oBound : o < 8) (o0 : o ≠ 0) (o4 : o ≠ 4)
    (keep : Keeps (VG.Arm.State.addr base) capacity w o m m') : RoundData base capacity w n m' := by
  have size : 256 ≤ 8 * capacity :=
    Nat.le_trans (Nat.le_add_right 256 (28 * (8 * (w + 2)))) h.fits
  have unwritten (q : Nat) (member : q ∈ [0, 4, 9, 10, 27]) : q < 28 ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ o := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> omega_arith
  refine h.after_reads (fun _ bound => keeps_header_readW keep size (by omega_using [bound])) ?_ ?_
  · intro q member
    have p := unwritten q member
    have read := operand_keeps_extended keep h.fits p.1 p.2.1 p.2.2.1 p.2.2.2 (d := 0) (n := 8 * w) (by omega_using [])
    simpa only [numAt, off, Nat.add_zero] using congrArg BitVec.toNat read
  · unfold Mem.readW
    rw [operand_keeps_extended keep h.fits (q := 27) (by decide) (by decide) (by decide) (by omega_using [oBound])
      (d := 8 * w) (n := 8) (by omega_using [])]

theorem RoundData.after_round {base : BitVec 32} {capacity w n : Nat} {m m' : Mem}
    (h : RoundData base capacity w n m)
    (keep : KeepsLite (VG.Arm.State.addr base) capacity w m m') : RoundData base capacity w n m' := by
  have size : 128 ≤ 8 * capacity := Nat.le_trans (by decide : 128 ≤ 256)
    (Nat.le_trans (Nat.le_add_right 256 (28 * (8 * (w + 2)))) h.fits)
  have unwritten : ∀ q ∈ [0, 4, 9, 10, 27], q < 28 ∧ q ∉ wJs := by decide
  refine h.after_reads (fun _ bound => round_keeps_header keep size bound) ?_ ?_
  · intro q member
    have p := unwritten q member
    have read := round_keeps_array keep h.fits p.1 p.2 (d := 0) (n := 8 * w) (by omega_using [])
    simpa only [numAt, off, Nat.add_zero] using congrArg BitVec.toNat read
  · unfold Mem.readW
    rw [round_keeps_array keep h.fits (q := 27) (by decide) (by decide) (d := 8 * w) (n := 8) (by omega_using [])]

private theorem array64 {w q : Nat} (words : w ≤ 128) (index : q ≤ 27) :
    arrAt w q + 8 * (w + 2) ≤ 2 ^ 64 := by
  have scale := Nat.mul_le_mul_right (8 * (w + 2)) index
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes]
  omega_using [words, scale]

theorem RoundData.after_aux_word {base : BitVec 32} {capacity w n d : Nat} {m : Mem}
    (h : RoundData base capacity w n m) (lower : 128 ≤ d) (upper : d + 4 ≤ 256) (value : BitVec 32) :
    RoundData base capacity w n (m.writeW (off (VG.Arm.State.addr base) d) value) := by
  have outside := writeW32_outside m (VG.Arm.State.addr base) value (d := d) (by omega_using [upper])
  refine h.after_reads (fun _ bound => outside.word (.inl (by omega_using [lower, bound])) (by omega_using [bound])) ?_ ?_
  · intro q member
    have indexBound : ∀ q ∈ [0, 4, 9, 10, 27], q ≤ 27 := by decide
    have fit := array64 h.maxWords (indexBound q member)
    rw [numAt_native, numAt_native]
    apply outside.val32
    · right
      simp only [arrAt, Proof.Rsa.Mont.hdrBytes]
      omega_using [upper]
    · exact Nat.le_trans (by omega_using []) fit
  · have fit := array64 h.maxWords (q := 27) (by decide)
    exact outside.word (.inr (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using [upper])) (by omega_using [fit])

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Public phase state for rejection-sampled Miller–Rabin witnesses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

structure WitnessParams where
  base : BitVec 32
  tape : BitVec 32
  capacity : Nat
  words : Nat
  modulus : Nat
  bits : Nat
  checks : Nat
  bytes : List Byte

def witnessValues (p : WitnessParams) (used passed : Nat) : Nat → BitVec 32
  | 0 => p.base
  | 16 => p.tape
  | 20 => BitVec.ofNat 32 p.bytes.length
  | 36 => BitVec.ofNat 32 p.capacity
  | 40 => BitVec.ofNat 32 used
  | 44 => BitVec.ofNat 32 p.bits
  | 48 => BitVec.ofNat 32 ((p.bits + 7) / 8)
  | 52 => BitVec.ofNat 32 p.checks
  | 56 => BitVec.ofNat 32 passed
  | _ => 0

def witnessSlots : List Nat := [0, 16, 20, 36, 40, 44, 48, 52, 56]

def witnessRegions (p : WitnessParams) (sp : BitVec 32) : List Region :=
  [⟨State.addr p.base, 8 * p.capacity⟩, FrameStack.belowA sp 56,
    ⟨State.addr (sp + 40#32), 4⟩, ⟨State.addr (sp + 56#32), 4⟩]

structure WitnessState (p : WitnessParams) (used passed : Nat) (s : State) : Prop where
  data : RoundData p.base p.capacity p.words p.modulus s.mem
  workspace : Workspace s p.base (8 * p.capacity)
  saved : SavedFrame (witnessValues p used passed) witnessSlots s
  stackScratch : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.base, 8 * p.capacity⟩
  stackBelow : 56 ≤ s.sp.toNat
  belowScratch : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr p.base, 8 * p.capacity⟩
  bitsExact : p.bits = Spec.RsaKeyGen.bitLength (p.modulus - 1)
  bitsPositive : 0 < p.bits
  bitsBound : p.bits ≤ 8192
  bitsFit : p.bits ≤ 64 * p.words
  checksPositive : 0 < p.checks
  checksBound : p.checks ≤ 128
  usedBound : used ≤ p.bytes.length
  passedBound : passed ≤ p.checks
  tapeCount : p.bytes.length < 2 ^ 32
  tapeFits : p.tape.toNat + p.bytes.length ≤ 2 ^ 32
  tapeRead : InRegions (s.rd ++ s.wr) (State.addr p.tape) p.bytes.length
  tapeScratch : (⟨State.addr p.tape, p.bytes.length⟩ : Region).Disjoint ⟨State.addr p.base, 8 * p.capacity⟩
  tapeStack : (⟨State.addr p.tape, p.bytes.length⟩ : Region).Disjoint ⟨State.addr s.sp, 72⟩
  tapeBelow : (⟨State.addr p.tape, p.bytes.length⟩ : Region).Disjoint (FrameStack.belowA s.sp 56)
  tapeBytes : Spec.Rsa.bytesAt s.mem (State.addr p.tape) p.bytes.length = p.bytes

theorem witnessSlots_bound {d : Nat} (member : d ∈ witnessSlots) : d + 4 ≤ 72 := by
  simp only [witnessSlots, List.mem_cons, List.not_mem_nil, or_false] at member
  omega_using [member]

theorem WitnessState.after_frame {s t : State} {p : WitnessParams} {used passed nextUsed nextPassed : Nat}
    {rs : List Reg} (h : WitnessState p used passed s)
    (data : RoundData p.base p.capacity p.words p.modulus t.mem)
    (saved : SavedFrame (witnessValues p nextUsed nextPassed) witnessSlots t)
    (usedBound : nextUsed ≤ p.bytes.length) (passedBound : nextPassed ≤ p.checks)
    (changed : Frame (witnessRegions p s.sp) s.mem t.mem) (rest : Rest rs s t) :
    WitnessState p nextUsed nextPassed t := by
  refine ⟨data, h.workspace.congr rest.wr, saved, ?_, ?_, ?_, h.bitsExact,
    h.bitsPositive, h.bitsBound, h.bitsFit, h.checksPositive, h.checksBound, usedBound, passedBound,
    h.tapeCount, h.tapeFits, ?_, h.tapeScratch, ?_, ?_, ?_⟩
  · rw [rest.sp]; exact h.stackScratch
  · rw [rest.sp]; exact h.stackBelow
  · rw [rest.sp]; exact h.belowScratch
  · rw [rest.rd, rest.wr]; exact h.tapeRead
  · rw [rest.sp]; exact h.tapeStack
  · rw [rest.sp]; exact h.tapeBelow
  · refine (rsa_bytes_frame changed (by have := h.tapeCount; omega_using [this]) ?_).trans h.tapeBytes
    intro r hr
    simp only [witnessRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.tapeScratch
    · exact h.tapeBelow
    · rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega_using [this])]
      exact h.tapeStack.sub_right (Offset.sub_base _ (by decide : 40 + 4 ≤ 72))
    · rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega_using [this])]
      exact h.tapeStack.sub_right (Offset.sub_base _ (by decide : 56 + 4 ≤ 72))

theorem WitnessState.after_memory {s t : State} {p : WitnessParams} {used passed : Nat} {rs : List Reg}
    (h : WitnessState p used passed s) (memory : t.mem = s.mem) (rest : Rest rs s t) :
    WitnessState p used passed t := h.after_frame (memory ▸ h.data) (h.saved.after_memory memory rest)
      h.usedBound h.passedBound (by rw [memory]; exact Frame.refl _ _) rest

end VG.Proof.Ffdh.Arm.ParameterCandidate
