module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Prepare
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Constants
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedGeometry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentReady
import VerifiedGarbage.Proof.Mont.RangeCover
public import VerifiedGarbage.Impl.RsaKeyGen.X86.PrepareHeader
public import VerifiedGarbage.Impl.RsaKeyGen.X86.HeaderRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Header
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderStore
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.MillerRabin.Contract
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowWord
import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Impl.RsaKeyGen.X86.InverseLift
public import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialWord
public import VerifiedGarbage.TCB.X86.Isa
import Mathlib.Data.Int.Basic
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Impl.RsaKeyGen.X86.MontInverse
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `RsaKeyGen.X86.PrepareMetadata`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.Prepare`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.PreparedR2Frame`, which this module and modules that import it used -/

section

/-! # Fast R² setup retains the saved c-1 and the prepared exponent -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PreparedR2
open VG VG.Proof.Mont VG.Proof.MillerRabin.X86

theorem preserve {g : Geometry} (v : g.Valid) {s t : Mem} (F : WorkspaceFrame g (ranges g) s t)
    {j : Nat} (index : j = 5 ∨ j = 27) :
    val32 t g.W (g.array j) g.words = val32 s g.W (g.array j) g.words := by
  apply F.val32 (v.arrayFit (by omega_using [index]))
  intro r mem
  simp only [ranges, coreRanges, phaseRanges, montWrites, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at mem
  rcases index with rfl | rfl <;>
    rcases mem with ((rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl <;>
    simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
      VG.Proof.Mont.X86.accLen, VG.Impl.Bignum.X86.PublicContext.modulus, VG.Impl.Mont.X86.words] <;> omega_using []

end VG.Proof.RsaKeyGen.X86.PreparedR2

end

end

/-! ### `RsaKeyGen.X86.PrepareHeader`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.HeaderRead`, which only this module used -/

section

/-! # Pointer initialization preserves the scalar metadata and inverse -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.Proof.Mont

theorem read64_write {base : Addr} {m : Mem} {d e : Nat} {v : BitVec 64}
    (apart : d + 8 ≤ e ∨ e + 8 ≤ d) (readFit : d + 8 ≤ 2 ^ 64) (writeFit : e + 8 ≤ 2 ^ 64) :
    (m.writeW (off base e) v).readW (off base d) 64 = m.readW (off base d) 64 :=
  Mem.readW_writeW_sep (Offset.sep base apart readFit writeFit) (by decide)

theorem pointers_read64 (indices : List Nat) {base : Addr} {p : BitVec 32} {w d : Nat} {m : Mem}
    (bound : ∀ i ∈ indices, i < 8) (fit : d + 8 ≤ 2 ^ 64)
    (apart : d + 8 ≤ 64 ∨ 128 ≤ d) :
    (indices.foldl (pointerMemory base p w) m).readW (off base d) 64 = m.readW (off base d) 64 := by
  induction indices generalizing m with
  | nil => rfl
  | cons i indices ih =>
    rw [List.foldl_cons, ih (fun j mem => bound j (List.mem_cons_of_mem _ mem))]
    unfold pointerMemory
    apply read64_write _ fit
    · have := bound i (List.mem_cons_self ..)
      omega_using [this]
    · have := bound i (List.mem_cons_self ..)
      omega_using [apart, this]

theorem header_width {base : Addr} {p : BitVec 32} {w : Nat} {m : Mem} :
    (headerMemory base p w m).readW (off base 48) 64 = 0#32 ++ BitVec.ofNat 32 w := by
  unfold headerMemory
  rw [pointers_read64 _ (fun _ mem => List.mem_range.mp mem) (by decide) (by decide),
    read64_write (by decide) (by decide) (by decide), Mem.readW_writeW_self64]

theorem header_stride {base : Addr} {p : BitVec 32} {w : Nat} {m : Mem} :
    (headerMemory base p w m).readW (off base 224) 64 =
      0#32 ++ BitVec.ofNat 32 (VG.Impl.Bignum.X86.PublicContext.stride w) := by
  unfold headerMemory
  rw [pointers_read64 _ (fun _ mem => List.mem_range.mp mem) (by decide) (by decide),
    Mem.readW_writeW_self64]

theorem pointers_read64_at (indices : List Nat) {base : Addr} {p : BitVec 32} {w j : Nat} {m : Mem}
    (bound : ∀ i ∈ indices, i < 8) (index : j < 8) :
    (indices.foldl (pointerMemory base p w) m).readW (off base (64 + 8 * j)) 64 =
      if j ∈ indices then 0#32 ++ (p + BitVec.ofNat 32 (VG.Impl.Bignum.X86.PublicContext.slot w j))
      else m.readW (off base (64 + 8 * j)) 64 := by
  induction indices generalizing m with
  | nil => rfl
  | cons i indices ih =>
    rw [List.foldl_cons, ih (fun k mem => bound k (List.mem_cons_of_mem _ mem))]
    by_cases tail : j ∈ indices
    · simp only [tail, ite_true, List.mem_cons, or_true]
    · rw [ite_eq_right tail]
      by_cases same : j = i
      · subst i
        simp only [List.mem_cons, true_or, ite_true, pointerMemory, Mem.readW_writeW_self64]
      · simp only [List.mem_cons, same, false_or, tail, ite_false]
        unfold pointerMemory
        apply read64_write
        · omega_using [same]
        · omega_using [index]
        · have := bound i (List.mem_cons_self ..)
          omega_using [this]

theorem header_pointer {base : Addr} {p : BitVec 32} {w j : Nat} {m : Mem} (index : j < 8) :
    (headerMemory base p w m).readW (off base (64 + 8 * j)) 64 =
      0#32 ++ (p + BitVec.ofNat 32 (VG.Impl.Bignum.X86.PublicContext.slot w j)) := by
  unfold headerMemory
  rw [pointers_read64_at _ (fun _ mem => List.mem_range.mp mem) index, ite_eq_left (List.mem_range.mpr index)]

end VG.Proof.RsaKeyGen.X86.Header

end

end

/-! ### `RsaKeyGen.X86.HeaderFrame`, which this module and modules that import it used -/

section

/-! # Public header initialization preserves arguments, the inverse and all arrays -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.Proof.Mont

def ranges : List (Nat × Nat) := [(48, 8), (64, 64), (224, 8)]

theorem pointers_frame (indices : List Nat) {base : Addr} {p : BitVec 32} {w : Nat} {m : Mem}
    (bound : ∀ i ∈ indices, i < 8) :
    Outs base ranges m (indices.foldl (pointerMemory base p w) m) := by
  induction indices generalizing m with
  | nil => exact Outs.refl _ _ _
  | cons i indices ih =>
    rw [List.foldl_cons]
    have first : Outs base ranges m (pointerMemory base p w m i) :=
      Outs.of_outside ((writeW_outside _ base _ (by have := bound i (by simp); omega_using [this])).mono
        (by omega_using []) (by have := bound i (by simp); omega_using [this]))
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    exact first.trans (ih (fun j mem => bound j (List.mem_cons_of_mem _ mem)))

theorem header_frame {base : Addr} {p : BitVec 32} {w : Nat} {m : Mem} :
    Outs base ranges m (headerMemory base p w m) := by
  have width : Outs base ranges m (m.writeW (off base 48) (0#32 ++ BitVec.ofNat 32 w)) :=
    Outs.of_outside (writeW_outside _ base _ (by decide)) (List.mem_cons_self ..)
  have stride : Outs base ranges (m.writeW (off base 48) (0#32 ++ BitVec.ofNat 32 w))
      ((m.writeW (off base 48) (0#32 ++ BitVec.ofNat 32 w)).writeW (off base 224)
        (0#32 ++ BitVec.ofNat 32 (VG.Impl.Bignum.X86.PublicContext.stride w))) :=
    Outs.of_outside (writeW_outside _ base _ (by decide))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  exact (width.trans stride).trans (pointers_frame (List.range 8) (fun _ mem => List.mem_range.mp mem))

end VG.Proof.RsaKeyGen.X86.Header

end

end

/-! ### `RsaKeyGen.X86.HeaderRt`, which only this module used -/

section

/-! # The run-time header writes `Header.code`'s memory for the width at byte 4 -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.HeaderRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.HeaderRt
open VG.Proof.RsaKeyGen.X86.Header (headerMemory pointerMemory storePair_ok)
open VG.Impl.Mont.X86 (sc)

theorem pointers_ok {w : Nat} (k : Nat) : ∀ (n : Nat) {s : State} {base : Addr} {size : Nat}
    (_ : Scr s base size) (_ : 64 + 8 * (k + n) ≤ size) (_ : s.gpr .edx = 0#32)
    (_ : s.gpr .eax = s.gpr .edi + BitVec.ofNat 32 (slot w k))
    (_ : s.gpr .ecx = BitVec.ofNat 32 (stride w)),
    WP isa (.block ((List.range' k n).flatMap pointer)) s fun t =>
      t.mem = (List.range' k n).foldl (pointerMemory base (s.gpr .edi) w) s.mem ∧ Keeps [.eax] s t
  | 0, _, _, _, _, _, _, _, _ => WP.block_nil ⟨rfl, Keeps.refl _ _⟩
  | n + 1, s, base, size, scratch, fit, zero, eax, ecx => by
    rw [List.range'_succ, List.flatMap_cons]
    unfold pointer
    refine WP.block_append (WP.block_append (WP.mono (storePair_ok scratch (offset := 64 + 8 * k) (by omega_using [fit]))
      fun a ⟨M, _, K⟩ => ?_))
    refine wp_addS rfl fun b B _ => WP.block_nil ?_
    have Kb : Keeps [.eax] s b := (K.mono (by decide)).widen B.keeps
    have ih := pointers_ok (w := w) (k + 1) n (s := b) (scratch.of_keeps Kb (by decide)) (by omega_using [fit])
      (by rw [Kb.1 .edx (by decide)]; exact zero)
      (by
        rw [B.gpr, K.1 .eax (by decide), K.1 .ecx (by decide), eax, ecx, BitVec.add_assoc, ← BitVec.ofNat_add, Kb.1 .edi (by decide)]
        congr 2
        simp only [slot, stride, Nat.succ_mul]
        omega_using [])
      (by rw [Kb.1 .ecx (by decide)]; exact ecx)
    refine WP.mono ih fun t ⟨Mt, Kt⟩ => ⟨?_, Kb.trans Kt⟩
    rw [Mt, Kb.1 .edi (by decide), B.mem, M, eax, zero, List.foldl_cons]
    rfl

theorem code_ok {s : State} {base : Addr} {size w : Nat} (scratch : Scr s base size) (fit : 256 ≤ size)
    (bound : w ≤ 128) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa (.block code) s fun t =>
      t.mem = headerMemory base (s.gpr .edi) w s.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  unfold code
  simp only [List.cons_append]
  refine wp_movS (readSrc_sc scratch (d := 4) (by omega_using [fit])) fun a A _ => wp_movS rfl fun b B _ =>
    VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun c C => wp_movS rfl fun d D _ => ?_
  have Kd : Keeps [.eax, .ecx, .edx] s d :=
    (((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps
  have zero : d.gpr .edx = 0#32 := D.gpr
  have width : d.gpr .eax = BitVec.ofNat 32 w := by
    rw [D.other .eax (by decide), C.gpr, B.gpr, A.gpr, len]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_using [bound]
  have Md : d.mem = s.mem := by rw [D.mem, C.mem, B.mem, A.mem]
  show WP isa (.block ([.store (sc 48) .eax, .store (sc (48 + 4)) .edx] ++ _)) d _
  refine WP.block_append (WP.mono (storePair_ok (scratch.of_keeps Kd (by decide)) (offset := 48) (by omega_using [fit]))
    fun e ⟨Me, _, Ke⟩ => ?_)
  refine wp_addS rfl fun f F _ => wp_movS rfl fun h H _ => ?_
  have Kh : Keeps [.eax, .ecx, .edx] s h := ((Kd.widen Ke).widen F.keeps).widen H.keeps
  have strideF : f.gpr .ecx = BitVec.ofNat 32 (stride w) := by
    rw [F.gpr, Ke.1 .ecx (by decide), D.other .ecx (by decide), C.other .ecx (by decide), B.other .ecx (by decide),
      A.gpr, len]
    apply BitVec.eq_of_toNat_eq
    have sixteen : (16 : BitVec 32).toNat = 16 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, stride, sixteen]
    omega_using []
  have zeroH : h.gpr .edx = 0#32 := by
    rw [H.other .edx (by decide), F.other .edx (by decide), Ke.1 .edx (by decide)]; exact zero
  show WP isa (.block ([.store (sc 224) .eax, .store (sc (224 + 4)) .edx] ++ _)) h _
  refine WP.block_append (WP.mono (storePair_ok (scratch.of_keeps Kh (by decide)) (offset := 224) (by omega_using [fit]))
    fun i ⟨Mi, _, Ki⟩ => ?_)
  refine wp_movS rfl fun j J _ => wp_addS rfl fun l Lr _ => ?_
  have Kl : Keeps [.eax, .ecx, .edx] s l := ((Kh.widen Ki).widen J.keeps).widen Lr.keeps
  have edi : l.gpr .edi = s.gpr .edi := Kl.1 .edi (by decide)
  have eaxL : l.gpr .eax = l.gpr .edi + BitVec.ofNat 32 (slot w 0) := by
    rw [Lr.gpr, J.gpr, edi, Ki.1 .edi (by decide), Kh.1 .edi (by decide),
      show slot w 0 = 256 by simp [slot, VG.Impl.Bignum.hdrBytes]]
    rfl
  have ecxL : l.gpr .ecx = BitVec.ofNat 32 (stride w) := by
    rw [Lr.other .ecx (by decide), J.other .ecx (by decide), Ki.1 .ecx (by decide), H.other .ecx (by decide)]
    exact strideF
  have zeroL : l.gpr .edx = 0#32 := by
    rw [Lr.other .edx (by decide), J.other .edx (by decide), Ki.1 .edx (by decide)]; exact zeroH
  rw [List.range_eq_range']
  refine WP.mono (pointers_ok 0 8 (scratch.of_keeps Kl (by decide)) (by omega_using [fit]) zeroL eaxL ecxL)
    fun t ⟨Mt, Kt⟩ => ⟨?_, Kl.widen Kt⟩
  have strideH : h.gpr .eax = BitVec.ofNat 32 (stride w) := by rw [H.gpr]; exact strideF
  rw [Mt, edi, Lr.mem, J.mem, Mi, strideH, zeroH, H.mem, F.mem, Me, width, zero, Md]
  unfold headerMemory
  rw [List.range_eq_range']

end VG.Proof.RsaKeyGen.X86.HeaderRt

end

end

/-! ### `RsaKeyGen.X86.HeaderLayout`, which only this module used -/

section

/-! # The initialized header satisfies the existing Montgomery layout contract -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.X86 VG.Proof.Mont VG.Impl.Bignum.X86.PublicContext

theorem zeroHigh (x : BitVec 32) : 0#32 ++ x = x.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  have := x.isLt
  omega_using []

theorem width_eq {base : Addr} {p : BitVec 32} {w : Nat} {m : Mem} (bound : w < 2 ^ 32) :
    Proof.Rsa.Mont.wOf (headerMemory base p w m) base = w := by
  change ((headerMemory base p w m).readW (off base 48) 64).toNat = w
  rw [header_width, zeroHigh]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using [bound]

theorem slot_eq (w j : Nat) : slot w j = Proof.Rsa.Mont.arrAt w j := by
  unfold slot stride VG.Impl.Bignum.hdrBytes Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes
  simp only [Nat.mul_add]

theorem layout {base : Addr} {p : BitVec 32} {w wsLen : Nat} {m : Mem}
    (baseEq : p.setWidth 64 = base) (positive : 2 ≤ w) (bound : w < 2 ^ 31)
    (fit : Proof.Rsa.Mont.arrAt w 8 ≤ 8 * wsLen) (nowrap : base.toNat + 8 * wsLen ≤ 2 ^ 32) :
    Proof.Rsa.Mont.Layout (headerMemory base p w m) base wsLen := by
  unfold Proof.Rsa.Mont.Layout
  rw [width_eq (by omega_using [bound])]
  refine ⟨positive, bound, fit, ?_⟩
  intro j index
  change (headerMemory base p w m).readW (off base (8 * (8 + j))) 64 = _
  rw [show 8 * (8 + j) = 64 + 8 * j by omega_using [], header_pointer index, zeroHigh]
  change addr p (slot w j) = _
  rw [addr_eq, baseEq, slot_eq]
  have pNat : p.toNat = base.toNat := by
    rw [← baseEq, BitVec.toNat_setWidth]
    have := p.isLt
    omega_using []
  have offset : slot w j < Proof.Rsa.Mont.arrAt w 8 := by
    rw [← slot_eq]
    unfold slot stride
    have := Nat.mul_lt_mul_of_pos_right index (by omega_using [] : 0 < 8 * w + 16)
    omega_using [this]
  omega_using [fit, nowrap, pNat, offset]

end VG.Proof.RsaKeyGen.X86.Header

end

end

/-! ### `RsaKeyGen.X86.InverseLift`, which only this module used -/

section

/-! # Execute the three-product inverse lift without memory accesses -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/InverseLift.lean`, which only this module imported.
section

/-! # A one-step negative-inverse lift expressed in native-word parts -/

section
namespace VG.Proof.RsaKeyGen

theorem inverse_lift_identity {b c x k q y : Int}
    (inverse : c * x + 1 = b * k) (split : x * k = b * q + y) :
    c * (x + b * y) + 1 = b * b * (k * k - c * q) := by
  grind

theorem inverse_lift_dvd {b c x k q y : Int}
    (inverse : c * x + 1 = b * k) (split : x * k = b * q + y) :
    b * b ∣ c * (x + b * y) + 1 :=
  ⟨k * k - c * q, inverse_lift_identity inverse split⟩

theorem inverse_lift_nat {b c x : Nat} (inverse : (c * x + 1) % b = 0) :
    (c * (x + b * (x * ((c * x + 1) / b) % b)) + 1) % (b * b) = 0 := by
  let k := (c * x + 1) / b
  have eq₁ : c * x + 1 = b * k := by
    have := Nat.div_add_mod (c * x + 1) b
    rw [inverse, Nat.add_zero] at this
    exact this.symm
  have eq₂ : x * k = b * (x * k / b) + x * k % b := (Nat.div_add_mod (x * k) b).symm
  have I : (c : Int) * x + 1 = (b : Int) * k := by
    simpa only [Int.natCast_add, Int.natCast_mul, Int.natCast_one] using congrArg (fun n : Nat => (n : Int)) eq₁
  have S : (x : Int) * k = (b : Int) * (x * k / b : Nat) + (x * k % b : Nat) := by
    simpa only [Int.natCast_add, Int.natCast_mul] using congrArg (fun n : Nat => (n : Int)) eq₂
  have D : ((b * b : Nat) : Int) ∣ ((c * (x + b * (x * k % b)) + 1 : Nat) : Int) := by
    simpa only [Int.natCast_add, Int.natCast_mul, Int.natCast_one] using inverse_lift_dvd I S
  exact Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp D)

end VG.Proof.RsaKeyGen
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.InverseLift
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.InverseLift

def highCarry (a x : BitVec 32) : BitVec 32 :=
  BitVec.ofNat 32 (a.toNat * x.toNat / 2 ^ 32) +
    Trial.carryWord (Trial.carry (BitVec.ofNat 32 (a.toNat * x.toNat)) 1)

def upper (a b x : BitVec 32) : BitVec 32 :=
  BitVec.ofNat 32 (x.toNat *
    (BitVec.ofNat 32 (b.toNat * x.toNat) + highCarry a x).toNat)

theorem code_ok (s : State) :
    WP isa (.block code) s fun t =>
      t.gpr .eax = upper (s.gpr .ebx) (s.gpr .esi) (s.gpr .ecx) ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ebp] s t := by
  unfold code
  refine wp_movS rfl fun a A _ => wp_mul fun b B => wp_addS rfl fun c C cfC =>
    wp_adcS rfl cfC fun d D _ => ?_
  have Kd : Keeps [.eax, .edx] s d :=
    (((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps
  have high : d.gpr .edx = highCarry (s.gpr .ebx) (s.gpr .ecx) := by
    rw [D.gpr, C.other .edx (by decide), B.edx, A.gpr, A.other .ecx (by decide)]
    change _ + 0#32 + _ = _
    rw [BitVec.add_zero, B.eax, A.gpr, A.other .ecx (by decide)]
    rfl
  refine wp_movS rfl fun e E _ => wp_movS rfl fun f F _ => wp_mul fun h H =>
    wp_addS rfl fun i I _ => wp_movS rfl fun j J _ => wp_movS rfl fun k K _ =>
    wp_mul fun t T => WP.block_nil ?_
  have keep : Keeps [.eax, .edx, .ebp] s t :=
    (((((((Kd.mono (by decide)).widen E.keeps).widen F.keeps).widen H.keeps).widen I.keeps).widen
      J.keeps).widen K.keeps).widen T.keeps
  refine ⟨?_, ?_, keep⟩
  · rw [T.eax, K.gpr, J.other .ecx (by decide), I.other .ecx (by decide),
      H.other .ecx (by decide) (by decide), F.other .ecx (by decide), E.other .ecx (by decide),
      Kd.1 .ecx (by decide), K.other .ebp (by decide), J.gpr, I.gpr, H.eax, F.gpr,
      E.other .esi (by decide), Kd.1 .esi (by decide), F.other .ecx (by decide),
      E.other .ecx (by decide), Kd.1 .ecx (by decide), H.other .ebp (by decide) (by decide),
      F.other .ebp (by decide), E.gpr, high]
    rfl
  · rw [T.mem, K.mem, J.mem, I.mem, H.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

theorem highCarry_toNat (a x : BitVec 32) :
    (highCarry a x).toNat = (a.toNat * x.toNat + 1) / 2 ^ 32 := by
  have product := Nat.mul_le_mul (show a.toNat ≤ 2 ^ 32 - 1 by have := a.isLt; omega_using [])
    (show x.toNat ≤ 2 ^ 32 - 1 by have := x.isLt; omega_using [])
  have split := Nat.div_add_mod (a.toNat * x.toNat) (2 ^ 32)
  have remainder := Nat.mod_lt (a.toNat * x.toNat) (by decide : 0 < 2 ^ 32)
  unfold highCarry
  rw [BitVec.toNat_add, Trial.carryWord_toNat, Trial.carry_toNat]
  simp only [BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
  omega_using [product]

theorem upper_toNat (a b x : BitVec 32) :
    (upper a b x).toNat =
      x.toNat * ((a.toNat * x.toNat + 1) / 2 ^ 32 + b.toNat * x.toNat) % 2 ^ 32 := by
  unfold upper
  rw [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat, highCarry_toNat]
  rw [Nat.mod_add_mod, Nat.mul_mod_mod]
  congr 2
  omega_using []

theorem upper_inverse (a b x : BitVec 32)
    (inverse : (a.toNat * x.toNat + 1) % 2 ^ 32 = 0) :
    ((a.toNat + 2 ^ 32 * b.toNat) * (x.toNat + 2 ^ 32 * (upper a b x).toNat) + 1) % 2 ^ 64 = 0 := by
  have rearrange : (a.toNat + 2 ^ 32 * b.toNat) * x.toNat + 1 =
      a.toNat * x.toNat + 1 + 2 ^ 32 * (b.toNat * x.toNat) := by grind
  have full : ((a.toNat + 2 ^ 32 * b.toNat) * x.toNat + 1) % 2 ^ 32 = 0 := by
    rw [rearrange, Nat.add_mul_mod_self_left]
    exact inverse
  have result := VG.Proof.RsaKeyGen.inverse_lift_nat full
  rw [rearrange, Nat.add_mul_div_left _ _ (by decide)] at result
  rw [upper_toNat]
  exact result

theorem inverse_ok (s : State)
    (inverse : ((s.gpr .ebx).toNat * (s.gpr .ecx).toNat + 1) % 2 ^ 32 = 0) :
    WP isa (.block code) s fun t =>
      (((s.gpr .ebx).toNat + 2 ^ 32 * (s.gpr .esi).toNat) *
        ((t.gpr .ecx).toNat + 2 ^ 32 * (t.gpr .eax).toNat) + 1) % 2 ^ 64 = 0 ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ebp] s t :=
  WP.mono (code_ok s) fun t ⟨value, mem, keep⟩ =>
    ⟨by rw [value, keep.1 .ecx (by decide)]; exact upper_inverse _ _ _ inverse, mem, keep⟩

end VG.Proof.RsaKeyGen.X86.InverseLift

end

end

/-! # A fresh candidate reaches the existing prepared Montgomery contract -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/HeaderContext.lean`, which only this module imported.
section

/-! # The public header prepares the native callable Miller–Rabin context -/

section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86

theorem low_word (m : Mem) (base : Addr) (d : Nat) : w32 m base d = (word m base d).toNat % 2 ^ 32 := by
  rw [word_eq_w32, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (m.readW (off base d) 32).isLt]

/-- The context and frame of any code that writes the header's memory. -/
theorem context_of {g : Geometry} (v : g.Valid) {s t : State} (scratch : Scr s g.W g.L) {rs : List Reg}
    (K : Keeps rs s t) (edi : .edi ∉ rs) (M : t.mem = headerMemory g.W (s.gpr .edi) g.w s.mem) :
    Context g t ∧ Outs g.W ranges s.mem t.mem := by
  have wBound : g.w < 2 ^ 32 := by have := v.maxWidth; omega
  have strideBound : VG.Impl.Bignum.X86.PublicContext.stride g.w < 2 ^ 32 := by
    have := v.maxWidth
    unfold VG.Impl.Bignum.X86.PublicContext.stride
    omega
  have baseBound : g.W.toNat < 2 ^ 32 := by have := scratch.nowrap; have := v.headerFit; omega
  refine ⟨⟨⟨K.2.2 ▸ scratch.wr, scratch.nowrap⟩, ?_, ?_, ?_, ?_⟩, M ▸ header_frame⟩
  · rw [PtrAt, K.1 .edi edi, scratch.edi_toNat, Nat.add_zero, Nat.mod_eq_of_lt baseBound]
  · rw [M, low_word, VG.Proof.Mont.word, header_width, zeroHigh, BitVec.toNat_setWidth_of_le (by decide),
      BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt wBound]
  · rw [M, low_word, VG.Proof.Mont.word, header_stride, zeroHigh, BitVec.toNat_setWidth_of_le (by decide),
      BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt strideBound]
    rfl
  · intro j index
    rw [M, low_word, VG.Proof.Mont.word, header_pointer index, zeroHigh, BitVec.toNat_setWidth_of_le (by decide),
      Nat.mod_eq_of_lt (s.gpr .edi + BitVec.ofNat 32 (VG.Impl.Bignum.X86.PublicContext.slot g.w j)).isLt,
      BitVec.toNat_add, BitVec.toNat_ofNat, scratch.edi_toNat, Prepared.slot_eq]
    omega

end VG.Proof.RsaKeyGen.X86.Header
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/InverseSetup.lean`, which only this module imported.
section

/-! # Complete the prepared workspace's 64-bit negative inverse -/

section
namespace VG.Proof.RsaKeyGen.X86.InverseLift
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.RsaKeyGen.X86.InverseLift

theorem setup_ok {s : State} {base : Addr} {size mo inv : Nat}
    (scratch : Scr s base size) (modulus : mo + 8 ≤ size) (slot : inv + 8 ≤ size)
    (inverse : (w32 s.mem base mo * w32 s.mem base inv + 1) % 2 ^ 32 = 0) :
    WP isa (.block (setup mo inv)) s fun t =>
      ((w32 s.mem base mo + 2 ^ 32 * w32 s.mem base (mo + 4)) *
        (w32 s.mem base inv + 2 ^ 32 * w32 t.mem base (inv + 4)) + 1) % 2 ^ 64 = 0 ∧
      Outside base (inv + 4) 4 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold setup
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc scratch (by omega)) fun a A _ => ?_
  have Sa := scratch.of_keeps A.keeps (by decide)
  refine wp_movS (readSrc_sc Sa (by omega)) fun b B _ => ?_
  have Kb : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s b := (A.keeps.mono (by decide)).widen B.keeps
  have Sb := scratch.of_keeps Kb (by decide)
  refine wp_movS (readSrc_sc Sb (by omega)) fun c C _ => ?_
  have lo : c.gpr .ebx = s.mem.readW (off base mo) 32 := by
    rw [C.other .ebx (by decide), B.other .ebx (by decide), A.gpr]
  have hi : c.gpr .esi = s.mem.readW (off base (mo + 4)) 32 := by
    rw [C.other .esi (by decide), B.gpr, A.mem]
  have ix : c.gpr .ecx = s.mem.readW (off base inv) 32 := by
    rw [C.gpr, B.mem, A.mem]
  refine WP.block_append (WP.mono (inverse_ok c (by rw [lo, ix]; exact inverse)) fun d ⟨value, mem, Kd⟩ => ?_)
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s d := (Kb.widen C.keeps).widen Kd
  have Sd := scratch.of_keeps K (by decide)
  refine wp_storeS (Sd.ea (by omega)) (Sd.write (by omega)) fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, K.widen (T.keeps [])⟩
  · rw [T.mem, w32_write_self]
    rw [Kd.1 .ecx (by decide), lo, hi, ix] at value
    exact value
  · rw [T.mem, mem, C.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)

end VG.Proof.RsaKeyGen.X86.InverseLift
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/MontInverse.lean`, which only this module imported.
section

/-! # The compact prepared kernel receives the reviewed full 64-bit inverse -/

section
namespace VG.Proof.RsaKeyGen.X86.MontInverse
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.MontInverse

theorem code_ok {s : State} {base : Addr} {size modulus inverse : Nat} (scratch : Scr s base size)
    (modFit : modulus + 8 ≤ size) (invFit : inverse + 8 ≤ size)
    (apart : inverse + 8 ≤ modulus ∨ modulus + 8 ≤ inverse) (odd : w32 s.mem base modulus % 2 = 1) :
    WP isa (code modulus inverse) s fun t =>
      ((word t.mem base modulus).toNat * (word t.mem base inverse).toNat + 1) % 2 ^ 64 = 0 ∧
      Outside base inverse 8 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.seq (WP.mono (VG.Proof.Mont.X86.Dynamic.setupInverse_ok scratch (by omega) (by omega) odd)
    fun a ⟨inverseA, Oa, Ka⟩ => ?_)
  have low : (w32 a.mem base modulus * w32 a.mem base inverse + 1) % 2 ^ 32 = 0 := by
    rw [Oa.w32 (by omega) (by have := scratch.nowrap; omega)]
    exact inverseA
  refine WP.mono (InverseLift.setup_ok (scratch.of_keeps Ka (by decide)) modFit invFit low)
    fun t ⟨inverseT, Ot, Kt⟩ => ?_
  refine ⟨?_, (Oa.mono (by omega) (by omega)).trans (Ot.mono (by omega) (by omega)), ?_⟩
  · rw [word_eq_w32, word_eq_w32,
      Ot.w32 (d := modulus) (by omega) (by have := scratch.nowrap; omega),
      Ot.w32 (d := modulus + 4) (by omega) (by have := scratch.nowrap; omega),
      Ot.w32 (d := inverse) (by omega) (by have := scratch.nowrap; omega)]
    exact inverseT
  · exact (Ka.mono (by decide)).trans Kt

end VG.Proof.RsaKeyGen.X86.MontInverse
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PrepareHeader
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen.X86.PreparedR2

def ranges : List (Nat × Nat) := Header.ranges ++ [(56, 8)]
def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

/-- The header written by any code that writes `Header.code`'s memory, then the inverse. -/
theorem codeWith_ok {hdr : List Instr} {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat}
    {p : BitVec 32} (scratch : Scr s g.W g.L) (caller : Caller g capacity p s) (length : g.L = 8 * capacity)
    (candidate : val32 s.mem g.W (g.array 0) g.words = c) (odd : c % 2 = 1)
    (header : WP isa (.block hdr) s fun t =>
      t.mem = Header.headerMemory g.W (s.gpr .edi) g.w s.mem ∧ Keeps [.eax, .ecx, .edx] s t) :
    WP isa (.seq (.block hdr) (VG.Impl.RsaKeyGen.X86.MontInverse.code (g.array 0) 56)) s fun t =>
      Ready g c capacity p t ∧ Outs g.W ranges s.mem t.mem ∧ Keeps clob s t ∧
      word t.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
  refine WP.seq (WP.mono header fun a ⟨Ma, Ka⟩ => ?_)
  obtain ⟨Ca, Oa⟩ := Header.context_of v scratch Ka (by decide) Ma
  have Sa := scratch.of_keeps Ka (by decide)
  have candidateA : val32 a.mem g.W (g.array 0) g.words = c := by
    rw [Oa.val32 (fun r mem => by
      simp only [Header.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
      have h := v.arrayHeader 0
      rcases mem with rfl | rfl | rfl <;> right <;> omega_using [h])
      (by have := scratch.nowrap; have := v.arrayFit (j := 0) (by decide); omega_arith)]
    exact candidate
  have oddLow : w32 a.mem g.W (g.array 0) % 2 = 1 := by
    rw [← LowWord.parity _ _ _ g.words (by have := v.minWidth; unfold Geometry.words; omega_using [this]), candidateA]
    exact odd
  have callerA := caller.keepOuts Ka (by decide) Oa (fun r mem => by
    simp only [Header.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    have := v.headerFit
    rcases mem with rfl | rfl | rfl <;> omega_using [this])
  have widthA : Proof.Rsa.Mont.wOf a.mem g.W = g.w := by
    rw [Ma]
    exact Header.width_eq (by have := v.maxWidth; omega_using [this])
  have layoutA : Proof.Rsa.Mont.Layout a.mem g.W capacity := by
    rw [Ma]
    apply Header.layout scratch.edi (by have := v.minWidth; omega_using [this]) (by have := v.maxWidth; omega_using [this])
    · rw [← length]
      have fit := v.arraysFit
      unfold Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes at *
      omega_using [fit]
    · rw [← length]
      exact scratch.nowrap
  refine WP.mono (MontInverse.code_ok Sa
    (by have := v.arrayFit (j := 0) (by decide); have := v.minWidth; unfold Geometry.words at *; omega_arith)
    (by have := v.headerFit; omega_using [this]) (Or.inl (by have := v.arrayHeader 0; omega_using [this])) oddLow)
    fun t ⟨inverse, Ot, Kt⟩ => ?_
  have St := Sa.of_keeps Kt (by decide)
  have Ct : Context g t := by
    refine ⟨Ca.ws.of_keeps Kt, ?_, ?_, ?_, ?_⟩
    · rw [PtrAt, Kt.1 .edi (by decide)]; exact Ca.base
    · rw [Ot.w32 (by decide) (by decide)]; exact Ca.width
    · rw [Ot.w32 (by decide) (by decide)]; exact Ca.stride
    · intro j hj
      rw [Ot.w32 (by omega_using []) (by omega_using [hj])]; exact Ca.pointers j hj
  have Mt : Modulus g c t.mem := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (word t.mem g.W 48).toNat = g.w
      rw [Ot.word (by decide) (by decide)]
      exact widthA
    · intro j hj
      change word t.mem g.W (8 * Proof.Rsa.Mont.arrWord j) = _
      rw [Ot.word (Or.inr (by unfold Proof.Rsa.Mont.arrWord; omega_using [])) (by unfold Proof.Rsa.Mont.arrWord; omega_using [hj])]
      simpa only [widthA, Geometry.array, VG.Proof.Mont.word, VG.Proof.Mont.off, Proof.Rsa.Mont.wordAt] using layoutA.2.2.2 j hj
    · rw [Ot.val32 (Or.inr (by have := v.arrayHeader 0; omega_using [this]))
        (by have := scratch.nowrap; have := v.arrayFit (j := 0) (by decide); omega_arith)]
      exact candidateA
    · exact inverse
  refine ⟨⟨Ct, Mt, callerA.keepOuts Kt (by decide) (Outs.of_outside Ot (List.mem_singleton_self _))
    (fun r mem => by obtain rfl := List.mem_singleton.mp mem; have := v.headerFit; omega_using [this]), St⟩, ?_, ?_, ?_⟩
  · exact (Oa.mono (fun r mem => List.mem_append_left _ mem)).trans
      (Outs.of_outside Ot (List.mem_append_right _ (List.mem_singleton_self _)))
  · exact (Ka.mono (by unfold clob; decide)).trans Kt
  · rw [Ot.word (by decide) (by decide), Ma]
    change (Header.headerMemory g.W (s.gpr .edi) g.w s.mem).readW (off g.W 224) 64 = _
    rw [Header.header_stride, Header.zeroHigh]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, VG.Impl.Bignum.X86.PublicContext.stride]
    have := v.maxWidth
    omega_using [this]

theorem code_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (scratch : Scr s g.W g.L) (caller : Caller g capacity p s) (length : g.L = 8 * capacity)
    (candidate : val32 s.mem g.W (g.array 0) g.words = c) (odd : c % 2 = 1) :
    WP isa (VG.Impl.RsaKeyGen.X86.PrepareHeader.code g.w) s fun t =>
      Ready g c capacity p t ∧ Outs g.W ranges s.mem t.mem ∧ Keeps clob s t ∧
      word t.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
  unfold VG.Impl.RsaKeyGen.X86.PrepareHeader.code
  rw [Prepared.slot_eq]
  exact codeWith_ok v scratch caller length candidate odd
    (WP.mono (Header.code_ok scratch v.headerFit) fun _ ⟨M, K⟩ => ⟨M, K.mono (by decide)⟩)

/-- `HeaderRt.prepare`: the header at the width that header byte 4 gives. -/
theorem prepareRt_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (scratch : Scr s g.W g.L) (caller : Caller g capacity p s) (length : g.L = 8 * capacity)
    (candidate : val32 s.mem g.W (g.array 0) g.words = c) (odd : c % 2 = 1)
    (len : s.mem.readW (off g.W 4) 32 = BitVec.ofNat 32 (8 * g.w)) :
    WP isa VG.Impl.RsaKeyGen.X86.HeaderRt.prepare s fun t =>
      Ready g c capacity p t ∧ Outs g.W ranges s.mem t.mem ∧ Keeps clob s t ∧
      word t.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
  have base : g.array 0 = 256 := by
    simp [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  unfold VG.Impl.RsaKeyGen.X86.HeaderRt.prepare
  rw [← base]
  exact codeWith_ok v scratch caller length candidate odd
    (HeaderRt.code_ok scratch v.headerFit v.maxWidth len)

end VG.Proof.RsaKeyGen.X86.PrepareHeader

end

end

/-! # Complete candidate preparation reuses all expensive state across witnesses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Prepare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

def ranges (g : Geometry) : List (Nat × Nat) :=
  PrepareHeader.ranges ++ PreparedR2.ranges g ++ Constants.ranges g ++ Exponent.preparedRanges g

theorem code_full_okAt {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) (bound : g.w ≤ 64) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) {e : Nat} (I : Input g c capacity p s e) (positive : 1 ≤ e) (eLt : e < 64 * g.w) :
    WP isa (VG.Impl.RsaKeyGen.X86.Prepare.codeAt e g.w name mont) s fun t =>
      Data g c capacity p t ∧ Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧ Keeps clob s t ∧
      WorkspaceFrame g (ranges g) s.mem t.mem := by
  unfold VG.Impl.RsaKeyGen.X86.Prepare.codeAt
  rw [Prepared.slot_eq, Prepared.slot_eq, Prepared.slot_eq]
  refine WP.seq (WP.mono (PrepareHeader.code_ok v I.scratch I.caller length I.candidate I.odd)
    fun a ⟨A, Oa, Ka, strideA⟩ => ?_)
  have minusA : val32 a.mem g.W (g.array 5) g.words = c - 1 := by
    rw [Oa.val32 (fun r mem => by
      simp only [PrepareHeader.ranges, Header.ranges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      have := v.arrayHeader 5
      rcases mem with (rfl | rfl | rfl) | rfl <;> right <;> omega_using [this])
      (by have := I.scratch.nowrap; have := v.arrayFit (j := 5) (by decide); omega_arith)]
    exact I.minusOne
  refine WP.seq (WP.mono (PreparedR2.code_okAt verified noSp stack v length A bound I.odd positive eLt I.top)
    fun b ⟨B, r2B, Fb, Kb, Wb⟩ => ?_)
  have strideB : word b.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
    change b.mem.readW (off g.W 224) 64 = _
    rw [Wb.read64 (by have := v.headerFit; omega_using [this]) (fun r mem => by
      simp only [PreparedR2.ranges, PreparedR2.coreRanges, PreparedR2.phaseRanges, montWrites, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with ((rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl <;>
        exact Or.inl (by have := v.arrayHeader 1; simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []))]
    exact strideA
  have minusB := (PreparedR2.preserve v Wb (j := 5) (Or.inl rfl)).trans minusA
  refine WP.seq (WP.mono (Constants.code_ok verified noSp stack v length B I.odd (by have := I.large; omega_using [this]) r2B)
    fun d ⟨D, oneD, minusD, Wd, Fd, Kd⟩ => ?_)
  have strideD : word d.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
    change d.mem.readW (off g.W 224) 64 = _
    rw [Wd.read64 (by have := v.headerFit; omega_using [this]) (fun r mem => by
      simp only [Constants.ranges, montWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with (rfl | rfl | rfl) | (rfl | rfl) <;> exact Or.inl (by have := v.arrayHeader 1; simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []))]
    exact strideB
  have minusSaved := (Constants.preserve v Wd (j := 5) (Or.inr (Or.inl rfl))).trans minusB
  have r2D := (Constants.preserve v Wd (j := 4) (Or.inl rfl)).trans r2B
  refine WP.mono (Exponent.ready_ok v D minusSaved I.odd I.large) fun t ⟨T, exponentT, markerT, Ot, Kt⟩ => ?_
  have Fa : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem a.mem :=
    (workspaceGlobalFrame Oa (fun r mem => by
      simp only [PrepareHeader.ranges, Header.ranges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      have := v.headerFit
      rcases mem with (rfl | rfl | rfl) | rfl <;> omega_using [this])).mono (fun r mem => List.mem_append_left _ mem)
  have Ft : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) d.mem t.mem :=
    (workspaceGlobalFrame Ot (fun r mem => by
      simp only [Exponent.preparedRanges, Exponent.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
      have srcFit := Prepared.paddedFit v (j := 0) (by decide)
      have outFit := Prepared.paddedFit v (j := 27) (by decide)
      have := v.headerFit
      rcases mem with rfl | rfl | rfl <;>
        simp only [VG.Impl.RsaKeyGen.X86.Exponent.markerOffset] <;> omega_arith)).mono
      (fun r mem => List.mem_append_left _ mem)
  have Wa : WorkspaceFrame g PrepareHeader.ranges s.mem a.mem := WorkspaceFrame.of_outs I.scratch.nowrap Oa
  have Wt : WorkspaceFrame g (Exponent.preparedRanges g) d.mem t.mem := WorkspaceFrame.of_outs I.scratch.nowrap Ot
  have allWrites : WorkspaceFrame g (ranges g) s.mem t.mem :=
    (((Wa.mono (fun _ mem => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ mem)))).trans
      (Wb.mono (fun _ mem => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ mem))))).trans
      (Wd.mono (fun _ mem => List.mem_append_left _ (List.mem_append_right _ mem)))).trans
      (Wt.mono (fun _ mem => List.mem_append_right _ mem))
  refine ⟨⟨T, ?_, ?_, ?_, exponentT, markerT, ?_⟩, ((Fa.trans Fb).trans Fd).trans Ft, ?_, allWrites⟩
  · exact (Exponent.prepared_preserve v Ot (j := 4) (Or.inl rfl)).trans r2D
  · exact (Exponent.prepared_preserve v Ot (j := 9) (Or.inr (Or.inr (Or.inl rfl)))).trans oneD
  · exact (Exponent.prepared_preserve v Ot (j := 10) (Or.inr (Or.inr (Or.inr rfl)))).trans minusD
  · rw [Ot.word (fun r mem => by
      simp only [Exponent.preparedRanges, Exponent.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · right; decide
      · left; have := v.arrayHeader 0; omega
      · left; have := v.arrayHeader 27; omega) (by decide)]
    exact strideD
  · exact (((Ka.mono (by unfold clob PrepareHeader.clob; decide)).widen Kb).widen Kd).widen Kt

end VG.Proof.RsaKeyGen.X86.Prepare

end

end

/-! # Preparation preserves candidate arguments and the entropy cursor -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Prepare
open VG VG.Proof.Mont VG.Proof.MillerRabin.X86

def protectedHeader (d bytes : Nat) : Prop :=
  d + bytes ≤ 48 ∨ 128 ≤ d ∧ d + bytes ≤ 136 ∨ 144 ≤ d ∧ d + bytes ≤ 224

theorem ranges_apart {g : Geometry} {d bytes : Nat} (safe : protectedHeader d bytes)
    {r : Nat × Nat} (mem : r ∈ ranges g) : d + bytes ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  simp only [ranges, PrepareHeader.ranges, Header.ranges, PreparedR2.ranges,
    PreparedR2.coreRanges, PreparedR2.phaseRanges, Constants.ranges, montWrites,
    Exponent.preparedRanges, Exponent.ranges, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at mem
  repeat' first
    | (rcases mem with mem | mem)
    | (rcases mem with rfl)
  all_goals
    simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
      VG.Impl.RsaKeyGen.X86.Exponent.markerOffset]
    unfold protectedHeader at safe
    omega_using [safe]

theorem metadata32 {g : Geometry} (v : g.Valid) {m m' : Mem}
    (W : WorkspaceFrame g (ranges g) m m') {d : Nat} (safe : protectedHeader d 4) :
    m'.readW (off g.W d) 32 = m.readW (off g.W d) 32 := by
  apply W.read32 (by have := v.headerFit; unfold protectedHeader at safe; omega_using [safe, this])
  exact fun _ mem => ranges_apart safe mem

end VG.Proof.RsaKeyGen.X86.Prepare

end

end

/-! # Candidate preparation retains every input needed by the blinded loop -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidatePrepare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen

structure Input (P : MillerRabinLoop.Parameters) (s : State) : Prop where
  prepare : Prepare.Input P.g P.candidate P.capacity P.p s P.seed
  readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen
  entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy
  randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand
  randLength : w32 s.mem P.g.W 32 = P.randLen
  used : w32 s.mem P.g.W 152 = P.start

structure Ready (P : MillerRabinLoop.Parameters) (s : State) : Prop where
  prepared : Prepare.Data P.g P.candidate P.capacity P.p s
  readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen
  entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy
  randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand
  randLength : w32 s.mem P.g.W 32 = P.randLen
  used : w32 s.mem P.g.W 152 = P.start

theorem code_ok {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (bound : P.g.w ≤ 64) {s : State} (I : Input P s) :
    WP isa (VG.Impl.RsaKeyGen.X86.Prepare.codeAt P.seed P.g.w name mont) s fun t =>
      Ready P t ∧ WorkspaceFrame P.g (Prepare.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 80]) s.mem t.mem ∧ Keeps Prepare.clob s t := by
  refine WP.mono (Prepare.code_full_okAt verified noSp stack v.geometry bound v.length I.prepare v.seedPos v.seedLt)
    fun t ⟨T, F, K, W⟩ => ?_
  refine ⟨⟨T, ?_, ?_, ?_, ?_, ?_⟩, W, F, K⟩
  · rw [K.2.1, K.2.2]; exact I.readable
  · rw [frame_bytesAt F (by
      intro r mem
      simp only [List.mem_append, List.mem_singleton] at mem
      rcases mem with rfl | rfl
      · exact v.randSeparate
      · exact v.randStackFar.sub_right (below_sub (by decide) v.low)) (by have := v.randLenFit; omega_using [this])]
    exact I.entropy
  · rw [Prepare.metadata32 v.geometry W (d := 28) (by unfold Prepare.protectedHeader; omega_using [])]
    exact I.randPtr
  · rw [w32, Prepare.metadata32 v.geometry W (d := 32) (by unfold Prepare.protectedHeader; omega_using [])]
    exact I.randLength
  · rw [w32, Prepare.metadata32 v.geometry W (d := 152) (by unfold Prepare.protectedHeader; omega_using [])]
    exact I.used

end VG.Proof.RsaKeyGen.X86.CandidatePrepare
