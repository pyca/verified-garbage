module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Frame
import VerifiedGarbage.Proof.Framework.Offset

/-! # Exact word updates in the persistent parameter-search frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def FrameWords (mem : Mem) (base : Addr) (words : Nat → BitVec 32) : Prop :=
  ∀ i < 37, mem.readW (off base (4 * i)) 32 = words i

def frameUpdate (words : Nat → BitVec 32) (i : Nat) (value : BitVec 32) : Nat → BitVec 32 :=
  fun j => if j = i then value else words j

theorem FrameWords.write {mem : Mem} {base : Addr} {words : Nat → BitVec 32}
    (R : FrameWords mem base words) {i : Nat} (hi : i < 37) (v : BitVec 32) :
    FrameWords (mem.writeW (off base (4 * i)) v) base (frameUpdate words i v) := by
  intro j hj
  by_cases equal : j = i
  · subst j
    simp only [frameUpdate, ite_true, Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide), R j hj]
    exact (ite_eq_right equal).symm

theorem FrameWords.same {s t : Mem} {base : Addr} {words : Nat → BitVec 32}
    (R : FrameWords s base words) (eq : t = s) : FrameWords t base words := eq ▸ R

theorem SearchFrame.readWord {s : State} {base : Addr} {words : Nat → BitVec 32}
    (F : SearchFrame s base) (R : FrameWords s.mem base words) {i : Nat} (hi : i < 37) :
    readSrc s (.mem (frameSlot i)) = some (words i) := by rw [F.readSlot hi, R i hi]
end VG.Proof.Dsa.X86.Generation
