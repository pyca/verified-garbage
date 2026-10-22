module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ForceWitness
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Subspace
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset

/-! Shape the stored witness and restore the generation workspace pointer. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86

theorem force_stored_witness {s : State} {base : Addr} {bytes len candidate : Nat}
    (scr : Scr s base bytes) (hlen : 2 ≤ len) (fit : Layout.witness + len ≤ bytes)
    (bits : Spec.RsaKeyGen.bitLength (candidate - 1) = 8 * len)
    (bad : ¬ (2 ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off base Layout.witness) len) ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off base Layout.witness) len) < candidate - 1)) :
    WP isa (forceStoredWitness len) s fun t =>
      Spec.RsaKeyGen.witness (candidate - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off base Layout.witness) len)) =
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (off base Layout.witness) len), false) ∧
      Frame [⟨off base Layout.witness, len⟩] s.mem t.mem ∧ Keeps [.eax, .ebx] s t := by
  let dst := s.gpr .edi + BitVec.ofNat 32 Layout.witness
  have inBounds : Layout.witness < bytes := by omega
  have address : byteAddr dst = off base Layout.witness := scr.ea inBounds
  have pointerFit := workspace_pointer_fits scr fit (by omega)
  unfold forceStoredWitness
  refine WP.seq (wp_addS rfl fun a A _ => WP.block_nil ?_)
  have read : ∀ i < len, InRegions (a.rd ++ a.wr) (off (byteAddr dst) i) 1 := by
    intro i hi
    rw [A.rd, A.wr, address]
    change InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 Layout.witness + BitVec.ofNat 64 i) 1
    rw [Offset.add_add]
    exact scr.read (by omega)
  have write : ∀ i < len, InRegions a.wr (off (byteAddr dst) i) 1 := by
    intro i hi
    rw [A.wr, address]
    change InRegions s.wr (base + BitVec.ofNat 64 Layout.witness + BitVec.ofNat 64 i) 1
    rw [Offset.add_add]
    exact scr.write (by omega)
  have work := force_witness_spec (dst := dst) (candidate := candidate) hlen pointerFit A.gpr read write bits (by
    rw [A.mem, address]; exact bad)
  refine WP.seq (WP.mono work fun u ⟨value, F, K⟩ => ?_)
  refine wp_subS rfl fun t T _ => WP.block_nil ?_
  have restored : t.gpr .edi = s.gpr .edi := by
    rw [T.gpr, K.1 .edi (by decide), A.gpr, BitVec.add_sub_cancel]
  refine ⟨?_, ?_, ?_⟩
  · rw [T.mem]
    rw [A.mem, address] at value
    exact value
  · rw [T.mem, ← A.mem]
    rw [address] at F
    exact F
  · refine ⟨?_, ?_, ?_⟩
    · intro r hr
      by_cases di : r = .edi
      · subst di; exact restored
      · rw [T.other r di, K.1 r hr, A.other r di]
    · rw [T.rd, K.2.1, A.rd]
    · rw [T.wr, K.2.2, A.wr]

end VG.Proof.Dsa.X86.Generation
