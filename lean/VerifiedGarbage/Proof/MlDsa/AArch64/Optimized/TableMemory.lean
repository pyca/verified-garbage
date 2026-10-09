import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

/-- The expanded immutable table as 32-bit little-endian words. -/
def ExpandedWords (m : Mem) (p : Addr) : Prop :=
  ∀ k < 976, m.readW (p+BitVec.ofNat 64 (4*k)) 32 = BitVec.ofNat 32 expandedVals[k]!

def ordinaryRoot (k : Nat) : Int := (zetaTab k : Int)
def innerRoot (u gap g _e : Nat) : Int :=
  ordinaryRoot (if gap=4 then 8+u else if gap=2 then 16+2*u+g else 32+4*u+g)
def tailRoot (u g len e : Nat) : Int :=
  ordinaryRoot (if len=2 then 64+8*u+2*g+e/2 else 128+16*u+4*g+e)

theorem ordinaryRoot_range (k : Nat) : 0 ≤ ordinaryRoot k ∧ ordinaryRoot k < 8380417 := by
  have h : zetaTab k < 8380417 := Nat.mod_lt _ (by decide)
  unfold ordinaryRoot
  omega

theorem reciprocal_nat_word (n : Nat) :
    BitVec.ofNat 32 (n*2^31/8380417) = BitVec.ofInt 32 (reciprocal (n : Int)) := by
  rw [←BitVec.ofInt_natCast,Int.natCast_ediv,Int.natCast_mul]
  rfl

theorem ExpandedWords.vector {m : Mem} {p : Addr} (h : ExpandedWords m p)
    {k e : Nat} (hk : k+4≤976) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (4*k)) 16) e = BitVec.ofNat 32 expandedVals[k+e]! := by
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,
    BitVec.add_assoc,←BitVec.ofNat_add,←Nat.mul_add]
  exact h _ (by omega)

theorem ExpandedWords.root_vector {m : Mem} {p : Addr} (h : ExpandedWords m p)
    {u off g b e : Nat} (ho : off%4=0) (hb : b%4=0)
    (hbound : 480*u+off+32*g+b+16≤3904) (he : e<4) :
    vword (m.read (rootAddress p u off g b) 16) e =
      BitVec.ofNat 32 expandedVals[120*u+off/4+8*g+b/4+e]! := by
  have hi : 480*u+off+32*g+b = 4*(120*u+off/4+8*g+b/4) := by omega
  rw [rootAddress,hi]
  exact h.vector (by omega) he

theorem ExpandedWords.hoisted {m : Mem} {p : Addr} (h : ExpandedWords m p) :
    HoistedTable m p ordinaryRoot := by
  refine ⟨fun i _ => ordinaryRoot_range (i+1),?_⟩
  intro g hg e he
  have haddr : 3840+16*g=4*(960+4*g) := by omega
  rw [haddr,h.vector (by omega) he]
  have hi : 2*g+e/2 < 8 := by omega
  have hv := TableConstants.hoisted_values hi
  by_cases hm : e%2=0
  · rw [ite_eq_left hm]
    have idx : 960+4*g+e=960+2*(2*g+e/2) := by omega
    rw [idx,hv.1]
    rfl
  · rw [ite_eq_right hm]
    have idx : 960+4*g+e=960+2*(2*g+e/2)+1 := by omega
    rw [idx,hv.2,reciprocal_nat_word]
    rfl

theorem ExpandedWords.row {m : Mem} {p : Addr} (h : ExpandedWords m p)
    {u off g e root : Nat} (ho : off%4=0) (he : e<4)
    (hbound : 480*u+off+32*g+32≤3904)
    (hv : expandedVals[120*u+off/4+8*g+e]! =zetaTab root ∧
      expandedVals[120*u+off/4+8*g+e+4]! =zetaTab root*2^31/8380417) :
    vword (m.read (rootAddress p u off g 0) 16) e=BitVec.ofInt 32 (ordinaryRoot root) ∧
    vword (m.read (rootAddress p u off g 16) 16) e=BitVec.ofInt 32 (reciprocal (ordinaryRoot root)) := by
  constructor
  · rw [h.root_vector ho (by decide) (by omega) he]
    simp only [Nat.zero_div,Nat.add_zero]
    rw [hv.1]
    rfl
  · rw [h.root_vector ho (by decide) (by omega) he]
    rw [show 16/4=4 by decide,show 120*u+off/4+8*g+4+e=120*u+off/4+8*g+e+4 by omega,
      hv.2,reciprocal_nat_word]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized
