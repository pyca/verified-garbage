module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Header
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.RangeCover

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
      Outs.of_outside ((writeW_outside _ base _ (by have := bound i (by simp); omega)).mono
        (by omega) (by have := bound i (by simp); omega))
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
