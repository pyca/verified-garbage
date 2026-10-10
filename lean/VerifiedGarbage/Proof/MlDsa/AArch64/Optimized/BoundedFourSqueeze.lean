import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Call
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.BoundedFour

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def rateR (p : Addr) : Region := ⟨p,136⟩
def Rate136 (m : Mem) (p : Addr) (A : Spec.Sha3.State) : Prop :=
 ∀i<17,m.readW (outAddr p i) 64=A[i]!
theorem rate_contains (p : Addr) {i : Nat} (hi : i<17) :
 (rateR p).Contains (outAddr p i) 8 := Offset.contains_base p (by omega) (by omega)

theorem Rate136.byte {m : Mem} {p : Addr} {A : Spec.Sha3.State} (h : Rate136 m p A)
    {j : Nat} (hj : j < 136) : m (p+BitVec.ofNat 64 j) = Proof.Sha3.byteOf A j := by
  have hw := h (j/8) (by omega)
  have he := congrArg (fun v : BitVec 64 => v.extractLsb' (8*(j%8)) 8) hw
  change (m.read (outAddr p (j/8)) 8).extractLsb' (8*(j%8)) 8 = _ at he
  rw [Mem.extractLsb'_read m _ (by omega)] at he
  rw [outAddr,BitVec.add_assoc,← BitVec.ofNat_add,
    show 8*(j/8)+j%8 = j by omega] at he
  exact he
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
