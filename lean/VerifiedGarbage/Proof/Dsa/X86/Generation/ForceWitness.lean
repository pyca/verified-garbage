module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ClearByte
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ForceByte
public import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
public import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! The forced branch reuses the shared big-endian witness mathematics. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem force_witness {s : State} {dst : BitVec 32} {len : Nat}
    (hlen : 2 ≤ len) (fit : dst.toNat + len ≤ 2 ^ 32) (pointer : s.gpr .edi = dst)
    (read : ∀ i < len, InRegions (s.rd ++ s.wr) (off (byteAddr dst) i) 1)
    (write : ∀ i < len, InRegions s.wr (off (byteAddr dst) i) 1) :
    WP isa (forceWitness len) s fun t =>
      t.mem = (s.mem.writeW (byteAddr dst) (s.mem (byteAddr dst) &&& (127 : Byte))).writeW
        (off (byteAddr dst) (len - 1)) (s.mem (off (byteAddr dst) (len - 1)) ||| (2 : Byte)) ∧
      Keeps [.eax, .ebx] s t := by
  have address : s.ea (at_ .edi 0) = byteAddr dst := by
    simp only [State.ea, at_, BitVec.add_zero, pointer, byteAddr]
  unfold forceWitness
  refine WP.seq (WP.mono (clear_byte (r := .edi) 127 (by decide) address
    (by simpa only [off, BitVec.add_zero] using read 0 (by omega))
    (by simpa only [off, BitVec.add_zero] using write 0 (by omega))) fun u ⟨memory, K⟩ => ?_)
  simp only [List.cons_append, List.nil_append]
  refine wp_movS rfl fun v V _ => wp_addS rfl fun w W _ => ?_
  have lastPtr : w.gpr .ebx = dst + BitVec.ofNat 32 (len - 1) := by
    rw [W.gpr, V.gpr, K.1 .edi (by decide), pointer]
  have lastAddress : w.ea (at_ .ebx 0) = off (byteAddr dst) (len - 1) := by
    simp only [State.ea, at_, BitVec.add_zero, lastPtr]
    exact byteAddr_add (by omega)
  refine WP.mono (force_byte (r := .ebx) 2 (by decide) lastAddress
    (by rw [W.rd, W.wr, V.rd, V.wr, K.2.1, K.2.2]; exact read _ (by omega))
    (by rw [W.wr, V.wr, K.2.2]; exact write _ (by omega))) fun t ⟨lastMemory, L⟩ => ?_
  refine ⟨?_, (((K.mono (by decide)).trans (V.keeps.mono (by decide))).trans
    (W.keeps.mono (by decide))).trans (L.mono (by decide))⟩
  rw [lastMemory, W.mem, V.mem, memory]
  rw [WriteBytes.writeW8_apply, ite_eq_right ?_]
  simpa only [off, BitVec.add_zero] using Offset.add_ofNat_ne (byteAddr dst)
    (by omega : len - 1 < 2 ^ 64) (by decide : 0 < 2 ^ 64) (by omega : len - 1 ≠ 0)

theorem force_witness_spec {s : State} {dst : BitVec 32} {len candidate : Nat}
    (hlen : 2 ≤ len) (fit : dst.toNat + len ≤ 2 ^ 32) (pointer : s.gpr .edi = dst)
    (read : ∀ i < len, InRegions (s.rd ++ s.wr) (off (byteAddr dst) i) 1)
    (write : ∀ i < len, InRegions s.wr (off (byteAddr dst) i) 1)
    (bits : Spec.RsaKeyGen.bitLength (candidate - 1) = 8 * len)
    (bad : ¬ (2 ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr dst) len) ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr dst) len) < candidate - 1)) :
    WP isa (forceWitness len) s fun t =>
      Spec.RsaKeyGen.witness (candidate - 1) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr dst) len)) =
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (byteAddr dst) len), false) ∧
      Frame [⟨byteAddr dst, len⟩] s.mem t.mem ∧ Keeps [.eax, .ebx] s t := by
  refine WP.mono (force_witness hlen fit pointer read write) fun t ⟨memory, K⟩ => ⟨?_, ?_, K⟩
  · rw [memory, VG.Proof.Dsa.Generation.forcedWitness_memory s.mem (byteAddr dst) hlen (by omega)]
    exact VG.Proof.Dsa.Generation.forcedWitnessBytes_spec
      (by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using hlen)
      (by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using bits) bad
  · rw [memory]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    simpa only [off, BitVec.add_zero] using
      Offset.contains_base (byteAddr dst) (d := 0) (n := 1) (k := len) (by omega) (by decide)

end VG.Proof.Dsa.X86.Generation
