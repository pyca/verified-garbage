import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotBankField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFirstLoop

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64

def dotMemoryWord (m : Mem) (a b : Addr) (count off e : Nat) : BitVec 32 :=
  centeredDot (fun k => vword (m.read (a+BitVec.ofNat 64 (1024*k+off)) 16) e)
    (fun k => vword (m.read (b+BitVec.ofNat 64 (1024*k+off)) 16) e) count

def dotMemoryBank (m : Mem) (a b : Addr) (count : Nat) : Vector (BitVec 128) 8 :=
  Vector.ofFn fun j => ofVWords (dotMemoryWord m a b count (16*j.val) 0)
    (dotMemoryWord m a b count (16*j.val) 1) (dotMemoryWord m a b count (16*j.val) 2)
    (dotMemoryWord m a b count (16*j.val) 3)

theorem dotMemoryBank_eq (s : State) (count : Nat) :
    dotMemoryBank s.mem (s.gpr .x13) (s.gpr .x14) count=dotBankValues s count := rfl

namespace Inverse

def dotPassMem (m : Mem) (p a b : Addr) (count : Nat) : Nat → Mem
  | 0 => m
  | u+1 => let prior := dotPassMem m p a b count u
           writeBank (fiveValues u (dotMemoryBank prior
             (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) count))
             (p+BitVec.ofNat 64 (128*u)) 16 prior

theorem dotPass_frame {m : Mem} {p a b : Addr} {count u : Nat} (hu : u≤8) :
    Frame [⟨p,1024⟩] m (dotPassMem m p a b count u) := by
  induction u with
  | zero => exact Frame.refl _ _
  | succ u ih =>
    simp only [dotPassMem]
    apply writeBank_frame _ _ _ (r:=⟨p,1024⟩) (by simp) ?_ (ih (by omega))
    intro i
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact VG.Offset.contains_base p (by omega) (by omega)

end Inverse
end VG.Proof.MlDsa.AArch64.Optimized
