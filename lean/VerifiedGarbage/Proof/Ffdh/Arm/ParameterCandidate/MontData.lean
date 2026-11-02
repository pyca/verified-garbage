module

public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.Omega

/-! Montgomery data independent of the current scratch registers. RSA's
key-array operations may use r0 for an array pointer while preserving the
modulus, inverse, and immutable part of the Montgomery header. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (Layout wOf numAt wordAt arrAt arrWord)

structure MontData (base : BitVec 32) (capacity w : Nat) (m : Mem) : Prop where
  layout : Layout m (State.addr base) capacity
  width : wOf m (State.addr base) = w
  inverse : ((word m (State.addr base) (arrAt w 0)).toNat *
    (wordAt m (State.addr base) VG.Proof.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0
  modulus : 1 < numAt m (State.addr base) w 0

theorem MontData.of_ready {s : State} {base : BitVec 32} {capacity w : Nat}
    (h : ArithmeticReady base capacity w s) : MontData base capacity w s.mem :=
  ⟨h.layout, h.width, h.inverse, h.modulus⟩

theorem numAt_lowWord (m : Mem) (base : Addr) (w j : Nat) (positive : 0 < w) :
    numAt m base w j % 2 ^ 64 = (word m base (arrAt w j)).toNat := by
  have split : numAt m base w j = (word m base (arrAt w j)).toNat +
      2 ^ 64 * wordsVal m base (arrAt w j + 8) (w - 1) := by
    unfold numAt
    rw [read_eq_wordsVal]
    exact congrArg (fun n => wordsVal m base (arrAt w j) n) (show w = (w - 1) + 1 by omega)
  rw [split, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (word m base (arrAt w j)).isLt]

theorem MontData.after_reads {base : BitVec 32} {capacity w : Nat} {m m' : Mem}
    (h : MontData base capacity w m)
    (readHeader : ∀ d, d + 8 ≤ 128 →
      m'.readW (off (State.addr base) d) 64 = m.readW (off (State.addr base) d) 64)
    (numberEq : numAt m' (State.addr base) w 0 = numAt m (State.addr base) w 0) :
    MontData base capacity w m' ∧ numAt m' (State.addr base) w 0 = numAt m (State.addr base) w 0 := by
  have wmin : 2 ≤ w := h.width ▸ h.layout.1
  have widthEq : wOf m' (State.addr base) = wOf m (State.addr base) := by
    unfold wOf wordAt
    rw [readHeader (8 * VG.Proof.Rsa.Mont.wWord) (by decide)]
  have layout' : Layout m' (State.addr base) capacity := by
    unfold Layout
    rw [widthEq]
    refine ⟨h.layout.1, h.layout.2.1, h.layout.2.2.1, ?_⟩
    intro j hj
    unfold wordAt
    rw [readHeader (8 * arrWord j) (by simp only [arrWord]; omega)]
    exact h.layout.2.2.2 j hj
  have wordEq : word m' (State.addr base) (arrAt w 0) = word m (State.addr base) (arrAt w 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [← numAt_lowWord m' (State.addr base) w 0 (by omega),
      ← numAt_lowWord m (State.addr base) w 0 (by omega), numberEq]
  refine ⟨⟨layout', widthEq.trans h.width, ?_, ?_⟩, numberEq⟩
  · rw [wordEq]
    unfold wordAt
    rw [readHeader (8 * VG.Proof.Rsa.Mont.minvWord) (by decide)]
    exact h.inverse
  · rw [numberEq]
    exact h.modulus

theorem MontData.after_value {base : BitVec 32} {capacity w : Nat} {m m' : Mem} {regions : List Region}
    (h : MontData base capacity w m) (frame : Frame regions m m')
    (header : ∀ r ∈ regions, (⟨State.addr base, 128⟩ : Region).Disjoint r)
    (numberEq : numAt m' (State.addr base) w 0 = numAt m (State.addr base) w 0) :
    MontData base capacity w m' ∧ numAt m' (State.addr base) w 0 = numAt m (State.addr base) w 0 :=
  h.after_reads (fun _ bound => frame.readW (r := ⟨State.addr base, 128⟩)
    (Offset.contains_base _ bound (by omega)) header (by decide)) numberEq

theorem MontData.after_frame {base : BitVec 32} {capacity w : Nat} {m m' : Mem} {regions : List Region}
    (h : MontData base capacity w m) (frame : Frame regions m m')
    (header : ∀ r ∈ regions, (⟨State.addr base, 128⟩ : Region).Disjoint r)
    (modulus : ∀ r ∈ regions,
      (⟨off (State.addr base) (arrAt w 0), 8 * w⟩ : Region).Disjoint r) :
    MontData base capacity w m' ∧ numAt m' (State.addr base) w 0 = numAt m (State.addr base) w 0 := by
  have wmax : w < 2 ^ 31 := h.width ▸ h.layout.2.1
  have numberEq : numAt m' (State.addr base) w 0 = numAt m (State.addr base) w 0 := by
    unfold numAt
    rw [frame.read (r := ⟨off (State.addr base) (arrAt w 0), 8 * w⟩)
      (Region.contains_self _ _) modulus (by omega)]
  exact h.after_value frame header numberEq

theorem MontData.ready {s : State} {base : BitVec 32} {capacity w : Nat}
    (h : MontData base capacity w s.mem) (workspace : Workspace s base (8 * capacity))
    (ptr : s.gpr .r0 = base) (stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (stackSep : (⟨State.addr s.sp, 4⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) : ArithmeticReady base capacity w s :=
  ⟨workspace, h.layout, h.width, ptr, h.inverse, h.modulus, stackRead, stackSep, saved⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
