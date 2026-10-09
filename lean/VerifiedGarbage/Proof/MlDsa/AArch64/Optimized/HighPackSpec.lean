import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackMath
import VerifiedGarbage.Proof.MlDsa.Pack.Bits

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.Spec.MlDsa
open VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Pack
open VG.Proof.MlKem (digits take_drop_eq)

def packWidth (g : Nat) : Nat := if g=261888 then 4 else 6

def highCoefficients (g : Nat) (p : Poly) : Vector Nat n :=
  p.map fun a => (highBits g a).toNat

theorem highCoefficients_bound {g : Nat} (hg : IsG g) (p : Poly) :
    ∀ a ∈ (highCoefficients g p).toList, a<2^(packWidth g) := by
  intro a ha
  simp only [highCoefficients,Vector.toList_map,List.mem_map] at ha
  obtain ⟨r,_,rfl⟩ := ha
  rw [highBits_eq (mem_of_isG hg),Int.toNat_natCast]
  have h := Nat.mod_lt (hbF g r.val) (show 0<hbM g by rcases hg with rfl | rfl <;> decide)
  rcases hg with rfl | rfl
  · change _ < 16 at h ⊢; exact h
  · change _ < 44 at h
    change _ < 64
    omega

theorem packWidth_eq {g : Nat} (hg : IsG g) :
    bitlen (hbM g-1)=packWidth g := by rcases hg with rfl | rfl <;> rfl

/-- The fused packer's output is the original SimpleBitPack of HighBits. -/
def highPacked (g : Nat) (p : Poly) : List Byte :=
  simpleBitPack (highCoefficients g p) (hbM g-1)

theorem highPacked_length {g : Nat} (hg : IsG g) (p : Poly) :
    (highPacked g p).length=32*packWidth g := by
  rw [highPacked,simpleBitPack_eq,packWidth_eq hg]
  exact pack_length _ _ (by simp [n])

/-- Each sixteen-coefficient output block agrees byte for byte with the
existing bit-level specification, for both parameter choices. -/
theorem highPacked_group {g : Nat} (hg : IsG g) (p : Poly)
    {j t : Nat} (hj : j<16) (ht : t<2*packWidth g) :
    (highPacked g p)[(2*packWidth g)*j+t]! =
      BitVec.ofNat 8 (digits (packWidth g)
        ((List.range 16).map fun i => (highCoefficients g p).toList.getD (16*j+i) 0) / 2^(8*t)) := by
  rw [highPacked,simpleBitPack_eq,packWidth_eq hg]
  have hlen : (highCoefficients g p).toList.length=256 := by simp [n]
  have hshape : packWidth g*16=8*(2*packWidth g) := by omega
  have hk : (2*packWidth g)*j+t<32*packWidth g := by
    rcases hg with rfl | rfl
    · change t<8 at ht
      change 8*j+t<128
      omega
    · change t<12 at ht
      change 12*j+t<192
      omega
  rw [pack_group (by rcases hg with rfl | rfl <;> decide) hshape hlen
    (highCoefficients_bound hg p) ht hk]
  rw [take_drop_eq _ 0 (by rw [hlen]; omega)]

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
