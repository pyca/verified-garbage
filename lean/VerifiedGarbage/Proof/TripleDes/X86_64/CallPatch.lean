module

public import VerifiedGarbage.Spec.TripleDes.Cbc
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified

/-!
# Triple DES's modes on x86-64: the call's return address

The modes call the block function, whose return address the call stores
below the stack pointer (`hole`), which no buffer of the modes overlaps
(`Clear`): what the modes' contracts say of the data and the IV holds of the
memory with that hole patched (`Verified.of_inline_ct`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64

theorem patch_mem {H : Region} {b : State} {hv : Mem} {u : Nat → BitVec 64} {p : Addr} {n : Nat}
    (hb : ∀ i < n, ¬ H.Contains (p + BitVec.ofNat 64 i) 1) :
    ∀ i < n, (b.patch H hv u).mem (p + BitVec.ofNat 64 i) = b.mem (p + BitVec.ofNat 64 i) :=
  fun i hi => by simp only [State.patch, overlay, hb i hi, ite_false]

theorem bytesAt_congr {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = m' (p + BitVec.ofNat 64 i)) :
    Spec.TripleDes.bytesAt m p n = Spec.TripleDes.bytesAt m' p n := by
  simp only [Spec.TripleDes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem cbcBlocksAt_congr {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < 8 * n, m (p + BitVec.ofNat 64 i) = m' (p + BitVec.ofNat 64 i)) :
    Spec.TripleDes.cbcBlocksAt m p n = Spec.TripleDes.cbcBlocksAt m' p n := by
  simp only [Spec.TripleDes.cbcBlocksAt, Spec.TripleDes.blocksAt, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [Function.comp_apply, Spec.TripleDes.blockAt]
  refine congrArg Vector.toList (congrArg Vector.ofFn (funext fun j => ?_))
  rw [Offset.add_add]
  exact h _ (by have := j.isLt; omega)

end VG.Proof.TripleDes.X86_64
