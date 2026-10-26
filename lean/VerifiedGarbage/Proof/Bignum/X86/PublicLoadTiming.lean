module

public import VerifiedGarbage.Proof.Bignum.X86.PublicPair
import VerifiedGarbage.Proof.Bignum.X86.LoadBE
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! # Importing an integer preserves public call geometry and has a public trace -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86

def loadArgument (i j n out : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.mem (PublicFn.argument i)), .mov .ecx (.mem (PublicFn.argument j))]) (loadBE n out)

theorem loadArgument_ok {base : Addr} {bytes len n out i j : Nat} {args : Nat → BitVec 32} {s : State}
    (H : PublicInputs base bytes len args s) (hi : i < 10) (hj : j < 10)
    (length : args j = BitVec.ofNat 32 len) (hn : 0 < n) (hlen : len ≤ 8 * n)
    (bound : out + 8 * n ≤ bytes) (fit : (args i).toNat + len ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr (args i)) len)
    (apart : Region.Disjoint ⟨byteAddr (args i), len⟩ ⟨base, bytes⟩) :
    WP isa (loadArgument i j n out) s fun t =>
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ Outside base 0 bytes s.mem t.mem := by
  unfold loadArgument
  refine WP.seq (WP.mono (argumentPair_ok (c := BitVec.ofNat 32 len) (by decide) (by decide)
    (H.stack i hi).readSrc (by rw [← length]; exact (H.stack j hj).readSrc)) fun u ⟨P, C, M, K⟩ => ?_)
  refine WP.mono (loadBE_ok (H.scratch.of_keeps K (by decide)) hn bound (by have := H.lower; omega) hlen
    (by rw [P]; exact fit) C (by rw [P, K.2.1, K.2.2]; exact read)
    (by rw [P]; exact apart.sub_right (Offset.sub_base base bound))) fun t ⟨_, O, Kt⟩ => ?_
  exact ⟨(K.mono (by decide)).trans Kt, by rw [← M]; exact O.mono (by omega) (by omega)⟩

theorem loadArgument_trace (i j n out : Nat) (p c : BitVec 32) :
    RelCT isa (fun s t => VG.X86.Taint.Agree argumentTaint s t ∧
      readSrc s (.mem (PublicFn.argument i)) = some p ∧
      readSrc t (.mem (PublicFn.argument i)) = some p ∧
      readSrc s (.mem (PublicFn.argument j)) = some c ∧
      readSrc t (.mem (PublicFn.argument j)) = some c)
      (loadArgument i j n out) (fun _ _ => True) :=
  ((VG.RelCT.seq (loadArguments_relCT i j p c) (loadBE_relCT n out))).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

theorem loadArgument_relCT (base : Addr) (bytes len n out i j : Nat) (args : Nat → BitVec 32)
    (hi : i < 10) (hj : j < 10) (length : args j = BitVec.ofNat 32 len)
    (hn : 0 < n) (hlen : len ≤ 8 * n) (bound : out + 8 * n ≤ bytes)
    (fit : (args i).toNat + len ≤ 2 ^ 32)
    (apart : Region.Disjoint ⟨byteAddr (args i), len⟩ ⟨base, bytes⟩) :
    RelCT isa (fun s t => PublicPair base bytes len args s t ∧
      InRegions (s.rd ++ s.wr) (byteAddr (args i)) len ∧
      InRegions (t.rd ++ t.wr) (byteAddr (args i)) len)
      (loadArgument i j n out) (PublicPair base bytes len args) := by
  intro s t tr ur sf tf ⟨H, Rs, Rt⟩ E F
  have Trace := (loadArgument_trace i j n out (args i) (args j) _ _ _ _ _ _
    ⟨H.agree, (H.left.stack i hi).readSrc, (H.right.stack i hi).readSrc,
      (H.left.stack j hj).readSrc, (H.right.stack j hj).readSrc⟩ E F).1
  obtain ⟨Ks, Os⟩ := wp_result (loadArgument_ok H.left hi hj length hn hlen bound fit Rs apart) E
  obtain ⟨Kt, Ot⟩ := wp_result (loadArgument_ok H.right hi hj length hn hlen bound fit Rt apart) F
  exact ⟨Trace, H.keep Ks Kt (by decide) (by decide) Os Ot⟩

end VG.Proof.Bignum.X86
