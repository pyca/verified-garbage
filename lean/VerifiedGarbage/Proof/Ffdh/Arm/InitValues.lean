module

public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Spec.Ffdh.Generation
import VerifiedGarbage.Spec.Ffdh.KeyGeneration
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Rc2.PairMem
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.Impl.Ffdh.Arm.Init
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

/-! ### `Ffdh.Arm.ParameterInitStores`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.InitStores`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ControlMemory`, which only this module used -/

section

/-! The shared 64-bit FFDH controller encoded with native 32-bit stores. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont

def controlSlots : List (Reg × Nat) :=
  [(.r0, 0), (.r1, 4), (.r2, 8), (.r3, 12),
   (.r4, 16), (.r5, 20), (.r6, 24), (.r7, 28)]

def controlMem (m : Mem) (B : Addr) (g : Reg → BitVec 32) : Mem :=
  Spill.saveMem m B g controlSlots

theorem controlMem_saved (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    Spill.Saved (controlMem m B g) B g controlSlots :=
  Spill.saveMem_saved B g m controlSlots (by decide : Spill.Slots 0 32 controlSlots)

theorem controlMem_words (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    Spec.Rsa.wordsAt (controlMem m B g) B 4 =
      [g .r1 ++ g .r0, g .r3 ++ g .r2, g .r5 ++ g .r4, g .r7 ++ g .r6] := by
  have h := controlMem_saved m B g
  have wordPair (d : Nat) (lo hi : Reg)
      (low : (lo, d) ∈ controlSlots) (high : (hi, d + 4) ∈ controlSlots) :
      (controlMem m B g).readW (off B d) 64 = g hi ++ g lo := by
    rw [VG.Proof.Rc2.Word32.read64_pair]
    have a : (controlMem m B g).readW (off B d) 32 = g lo := h (lo, d) low
    have b : (controlMem m B g).readW (off B (d + 4)) 32 = g hi := h (hi, d + 4) high
    rw [show off B d + BitVec.ofNat 64 4 = off B (d + 4) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add], b, a]
  change [(controlMem m B g).readW (off B 0) 64,
    (controlMem m B g).readW (off B 8) 64,
    (controlMem m B g).readW (off B 16) 64,
    (controlMem m B g).readW (off B 24) 64] = _
  rw [wordPair 0 .r0 .r1 (by decide) (by decide),
    wordPair 8 .r2 .r3 (by decide) (by decide),
    wordPair 16 .r4 .r5 (by decide) (by decide),
    wordPair 24 .r6 .r7 (by decide) (by decide)]

end VG.Proof.Ffdh.Arm

end

end


/-! Exact controller stores made by ARMv7 initialization. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Impl.Ffdh.Arm
open VG.Proof.Mont (off)

theorem clearController_ok (s : State) {base : BitVec 32}
    (h : Workspace s base 128) (ptr : s.gpr .r0 = base) :
    WP isa clearController s fun t =>
      t.gpr .r0 = 0 ∧ t.mem = controlMem s.mem (State.addr base) (fun _ => 0) := by
  have write (d : Nat) (hd : d ≤ 28) :
      InRegions s.wr (State.addr base + BitVec.ofNat 64 d) 4 := by
    exact h.write (by omega_using [hd])
  have write0 : InRegions s.wr (State.addr base) 4 := by
    simpa only [BitVec.add_zero] using write 0 (by decide)
  have addr (d : Nat) (hd : d ≤ 28) :
      State.addr (base + BitVec.ofNat 32 d) = State.addr base + BitVec.ofNat 64 d :=
    VG.Arm.addr_add (by have := h.nowrap; omega_using [hd, this])
  unfold clearController controlMem controlSlots Spill.saveMem
  ffrun [ptr, write0, write 0 (by decide), write 4 (by decide), write 8 (by decide), write 12 (by decide),
    write 16 (by decide), write 20 (by decide), write 24 (by decide), write 28 (by decide),
    BitVec.add_zero, off, Spill.saveMem, addr 4 (by decide), addr 8 (by decide),
    addr 12 (by decide), addr 16 (by decide), addr 20 (by decide), addr 24 (by decide), addr 28 (by decide)]

def keyInitValues (k : BitVec 32) : Reg → BitVec 32
  | .r0 | .r2 => 128
  | .r4 | .r6 => k
  | _ => 0

theorem keyInitializeState_ok (s : State) {base : BitVec 32}
    (h : Workspace s base 128) (ptr : s.gpr .r0 = base) :
    WP isa KeyGeneration.initializeState s fun t =>
      t.gpr .r0 = 1 ∧ t.mem = controlMem s.mem (State.addr base) (keyInitValues (s.gpr .r1)) := by
  have write (d : Nat) (hd : d ≤ 28) :
      InRegions s.wr (State.addr base + BitVec.ofNat 64 d) 4 := h.write (by omega_using [hd])
  have write0 : InRegions s.wr (State.addr base) 4 := by
    simpa only [BitVec.add_zero] using write 0 (by decide)
  have addr (d : Nat) (hd : d ≤ 28) :
      State.addr (base + BitVec.ofNat 32 d) = State.addr base + BitVec.ofNat 64 d :=
    VG.Arm.addr_add (by have := h.nowrap; omega_using [hd, this])
  unfold KeyGeneration.initializeState controlMem controlSlots Spill.saveMem
  ffrun [ptr, write0, write 4 (by decide), write 8 (by decide), write 12 (by decide),
    write 16 (by decide), write 20 (by decide), write 24 (by decide), write 28 (by decide),
    BitVec.add_zero, off, Spill.saveMem, keyInitValues,
    addr 4 (by decide), addr 8 (by decide), addr 12 (by decide), addr 16 (by decide),
    addr 20 (by decide), addr 24 (by decide), addr 28 (by decide)]

def parameterInitValues (bits : BitVec 32) : Reg → BitVec 32
  | .r0 => (bits * bits) <<< 6
  | .r1 => (bits * bits) >>> 26
  | .r2 => (bits + 7) >>> 3
  | .r4 => ((bits + 7) >>> 3) + (((bits + 7) >>> 3) <<< 15)
  | .r6 => ((bits + 7) >>> 3) <<< 9
  | _ => 0

end VG.Proof.Ffdh.Arm

end

end

/-! Small independent blocks keep controller symbolic execution bounded. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Impl.Ffdh.Arm
open VG.Proof.Mont (off)

def pairStore (m : Mem) (B : Addr) (d : Nat) (lo hi : BitVec 32) : Mem :=
  (m.writeW (off B d) lo).writeW (off B (d + 4)) hi

theorem budget_ok (s : State) {base : BitVec 32}
    (h : Workspace s base 128) (ptr : s.gpr .r0 = base) :
    WP isa Generation.budget s fun t =>
      t.gpr .r0 = base ∧ t.gpr .r1 = s.gpr .r1 ∧ t.wr = s.wr ∧
      t.mem = pairStore s.mem (State.addr base) 0
        ((s.gpr .r1 * s.gpr .r1) <<< 6) ((s.gpr .r1 * s.gpr .r1) >>> 26) := by
  have w0 : InRegions s.wr (State.addr base) 4 := by
    simpa only [off, BitVec.add_zero] using h.write (off := 0) (by decide)
  have w4 := h.write (off := 4) (by decide)
  have a4 : State.addr (base + BitVec.ofNat 32 4) = off (State.addr base) 4 :=
    VG.Arm.addr_add (by have := h.nowrap; omega_using [this])
  unfold Generation.budget pairStore
  ffrun [ptr, w0, w4, a4, off, BitVec.add_zero]

theorem width_ok (s : State) {base : BitVec 32}
    (h : Workspace s base 128) (ptr : s.gpr .r0 = base) :
    WP isa Generation.width s fun t =>
      t.gpr .r0 = base ∧ t.gpr .r2 = 0 ∧ t.gpr .r3 = (s.gpr .r1 + 7) >>> 3 ∧ t.wr = s.wr ∧
      t.mem = pairStore s.mem (State.addr base) 8 ((s.gpr .r1 + 7) >>> 3) 0 := by
  have w8 := h.write (off := 8) (by decide)
  have w12 := h.write (off := 12) (by decide)
  have a8 : State.addr (base + BitVec.ofNat 32 8) = off (State.addr base) 8 :=
    VG.Arm.addr_add (by have := h.nowrap; omega_using [this])
  have a12 : State.addr (base + BitVec.ofNat 32 12) = off (State.addr base) 12 :=
    VG.Arm.addr_add (by have := h.nowrap; omega_using [this])
  unfold Generation.width pairStore
  ffrun [ptr, w8, w12, a8, a12, off]

theorem entropy_ok (s : State) {base : BitVec 32}
    (h : Workspace s base 128) (ptr : s.gpr .r0 = base) (zero : s.gpr .r2 = 0) :
    WP isa Generation.entropy s fun t =>
      t.gpr .r0 = base ∧ t.gpr .r2 = 0 ∧ t.gpr .r3 = s.gpr .r3 ∧ t.wr = s.wr ∧
      t.mem = pairStore s.mem (State.addr base) 16 (s.gpr .r3 + (s.gpr .r3 <<< 15)) 0 := by
  have w16 := h.write (off := 16) (by decide)
  have w20 := h.write (off := 20) (by decide)
  have a16 : State.addr (base + BitVec.ofNat 32 16) = off (State.addr base) 16 :=
    VG.Arm.addr_add (by have := h.nowrap; omega_using [this])
  have a20 : State.addr (base + BitVec.ofNat 32 20) = off (State.addr base) 20 :=
    VG.Arm.addr_add (by have := h.nowrap; omega_using [this])
  unfold Generation.entropy pairStore
  ffrun [ptr, zero, w16, w20, a16, a20, off]

theorem request_ok (s : State) {base : BitVec 32}
    (h : Workspace s base 128) (ptr : s.gpr .r0 = base) (zero : s.gpr .r2 = 0) :
    WP isa Generation.request s fun t =>
      t.gpr .r0 = 1 ∧ t.mem = pairStore s.mem (State.addr base) 24 (s.gpr .r3 <<< 9) 0 := by
  have w24 := h.write (off := 24) (by decide)
  have w28 := h.write (off := 28) (by decide)
  have a24 : State.addr (base + BitVec.ofNat 32 24) = off (State.addr base) 24 :=
    VG.Arm.addr_add (by have := h.nowrap; omega_using [this])
  have a28 : State.addr (base + BitVec.ofNat 32 28) = off (State.addr base) 28 :=
    VG.Arm.addr_add (by have := h.nowrap; omega_using [this])
  unfold Generation.request pairStore
  ffrun [ptr, zero, w24, w28, a24, a28, off]

theorem parameterInitializeState_ok (s : State) {base : BitVec 32}
    (h : Workspace s base 128) (ptr : s.gpr .r0 = base) :
    WP isa Generation.initializeState s fun t =>
      t.gpr .r0 = 1 ∧ t.mem = controlMem s.mem (State.addr base) (parameterInitValues (s.gpr .r1)) := by
  rw [Generation.initializeState, WP.seq_iff]
  refine WP.mono (budget_ok s h ptr) ?_
  rintro u ⟨ptrU, bitsU, wrU, memU⟩
  rw [WP.seq_iff]
  refine WP.mono (width_ok u (h.congr wrU) ptrU) ?_
  rintro v ⟨ptrV, zeroV, widthV, wrV, memV⟩
  rw [WP.seq_iff]
  refine WP.mono (entropy_ok v (h.congr (wrV.trans wrU)) ptrV zeroV) ?_
  rintro z ⟨ptrZ, zeroZ, widthZ, wrZ, memZ⟩
  refine WP.mono (request_ok z (h.congr (wrZ.trans (wrV.trans wrU))) ptrZ zeroZ) ?_
  rintro t ⟨result, memT⟩
  refine ⟨result, ?_⟩
  rw [memT, memZ, memV, memU, widthZ, widthV, bitsU]
  rfl

end VG.Proof.Ffdh.Arm

end

end

/-! The native 32-bit halves encode the shared 64-bit controller values. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem shiftedPair (x : BitVec 32) :
    ((x >>> 26) ++ (x <<< 6) : BitVec 64).toNat = x.toNat * 64 := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (x <<< 6).isLt]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [show 2 ^ 6 = 64 by rfl, show 2 ^ 32 = 2 ^ 26 * 64 by rfl, Nat.mul_mod_mul_right]
  have := Nat.mod_add_div x.toNat (2 ^ 26)
  omega_using []

theorem zeroHigh (x : BitVec 32) :
    ((0 : BitVec 32) ++ x : BitVec 64) = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt, Nat.shiftLeft_eq]
  have hx64 : x.toNat < 2 ^ 64 := by have := x.isLt; omega_using []
  simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx64]

theorem keyInitValues_words (m : Mem) (B : Addr) (k : BitVec 32) :
    Spec.Rsa.wordsAt (controlMem m B (keyInitValues k)) B 4 =
      [128, 128, BitVec.ofNat 64 k.toNat, BitVec.ofNat 64 k.toNat] := by
  rw [controlMem_words]
  simp only [keyInitValues, zeroHigh]
  rfl

theorem parameterInitValues_words (m : Mem) (B : Addr) (bits : BitVec 32)
    (bound : bits.toNat ≤ 8192) :
    Spec.Rsa.wordsAt (controlMem m B (parameterInitValues bits)) B 4 =
      [BitVec.ofNat 64 (Spec.Ffdh.parameterAttempts bits.toNat),
       BitVec.ofNat 64 ((bits.toNat + 7) / 8),
       BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy bits.toNat),
       BitVec.ofNat 64 (512 * ((bits.toNat + 7) / 8))] := by
  rw [controlMem_words]
  have squareBound := Nat.mul_le_mul bound bound
  have square : (bits * bits).toNat = bits.toNat * bits.toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega_using [squareBound])]
  have width : ((bits + 7) >>> 3).toNat = (bits.toNat + 7) / 8 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add]
    simp only [show (7 : BitVec 32).toNat = 7 from rfl, show 2 ^ 3 = 8 from rfl,
      Nat.mod_eq_of_lt (by omega_using [bound] : bits.toNat + 7 < 2 ^ 32)]
  have widthBound : (bits.toNat + 7) / 8 ≤ 1024 := by omega_using [bound]
  have entropy : (((bits + 7) >>> 3) + (((bits + 7) >>> 3) <<< 15)).toNat =
      32769 * ((bits.toNat + 7) / 8) := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, width]
    have shiftBound : (bits.toNat + 7) / 8 * 2 ^ 15 < 2 ^ 32 := by omega_using [bound]
    rw [Nat.mod_eq_of_lt shiftBound, Nat.mod_eq_of_lt (by omega_using [bound])]
    omega_using []
  have request : (((bits + 7) >>> 3) <<< 9).toNat = 512 * ((bits.toNat + 7) / 8) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, width, Nat.mod_eq_of_lt (by omega_using [bound])]
    omega_using []
  have budget : (((bits * bits) >>> 26) ++ ((bits * bits) <<< 6) : BitVec 64) =
      BitVec.ofNat 64 (Spec.Ffdh.parameterAttempts bits.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [shiftedPair, square, BitVec.toNat_ofNat]
    simp only [Spec.Ffdh.parameterAttempts, Nat.mod_eq_of_lt (by omega_using [squareBound] : bits.toNat * bits.toNat * 64 < 2 ^ 64)]
  simp only [parameterInitValues, zeroHigh, budget, width, entropy, request, Spec.Ffdh.parameterEntropy]

end VG.Proof.Ffdh.Arm
