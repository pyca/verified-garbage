module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.DrawCopy
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Subspace
public import VerifiedGarbage.Proof.Bignum.X86.CopyRead
public import VerifiedGarbage.Proof.Bignum.CopyOctets
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Reuse the existing buffer-copy proof for padded RSA-compatible witness draws. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86

theorem draw_copy {s : State} {base : Addr} {bytes len drawBytes : Nat} {src : BitVec 32}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (positive : 0 < len) (length : len ≤ drawBytes) (upper : len ≤ 384)
    (source : s.gpr .esi = src) (sourceFit : src.toNat + drawBytes ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr src) drawBytes)
    (apart : Region.Disjoint ⟨byteAddr src, drawBytes⟩ ⟨base, bytes⟩) :
    WP isa (drawCopy len drawBytes) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base Layout.witness) len =
        Spec.Rsa.bytesAt s.mem (off (byteAddr src) (drawBytes - len)) len ∧
      t.gpr .esi = src + BitVec.ofNat 32 drawBytes ∧
      Frame [⟨off base Layout.witness, len⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .esi] s t := by
  let skipped := src + BitVec.ofNat 32 (drawBytes - len)
  let dst := s.gpr .edi + BitVec.ofNat 32 Layout.witness
  have skipFit : src.toNat + (drawBytes - len) < 2 ^ 32 := by omega
  have suffixAddress : byteAddr skipped = off (byteAddr src) (drawBytes - len) := byteAddr_add skipFit
  have skippedNat : skipped.toNat = src.toNat + (drawBytes - len) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := drawBytes - len) (by omega), Nat.mod_eq_of_lt skipFit]
  have bufferFit : Layout.witness + len ≤ bytes := by unfold Layout.witness; omega
  have bufferAddress : byteAddr dst = off base Layout.witness := scr.ea (by change 26624 < bytes; omega)
  have destinationFit := workspace_pointer_fits scr bufferFit positive
  have suffixRead : InRegions (s.rd ++ s.wr) (byteAddr skipped) len := by
    rw [suffixAddress]
    apply Covers.one read
    exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  have bufferWrite : InRegions s.wr (byteAddr dst) len := by
    rw [bufferAddress]
    exact ⟨_, scr.wr, Offset.contains_base base bufferFit (by decide)⟩
  have sep : Region.Disjoint ⟨byteAddr skipped, len⟩ ⟨byteAddr dst, len⟩ := by
    rw [suffixAddress, bufferAddress]
    exact (apart.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base base bufferFit)
  unfold drawCopy
  refine WP.seq (wp_addS rfl fun a A _ => wp_movS rfl fun b B _ =>
    wp_addS rfl fun c C _ => wp_movS rfl fun d D _ => WP.block_nil ?_)
  have K : Keeps [.eax, .ebx, .ecx, .esi] s d :=
    (((A.keeps.mono (by decide)).trans (B.keeps.mono (by decide))).trans
      (C.keeps.mono (by decide))).trans (D.keeps.mono (by decide))
  have memory : d.mem = s.mem := D.mem.trans (C.mem.trans (B.mem.trans A.mem))
  refine WP.mono (copyBuffers_ok positive (by omega) (by rw [skippedNat]; omega) destinationFit
    (by rw [K.2.1, K.2.2]; exact suffixRead) (by rw [K.2.2]; exact bufferWrite) sep
    (by rw [D.other _ (by decide), C.other _ (by decide), B.other _ (by decide), A.gpr, source])
    (by rw [D.other _ (by decide), C.gpr, B.gpr, A.other _ (by decide)]) D.gpr)
    fun t ⟨copy, _, next, F, Kt⟩ => ?_
  refine ⟨?_, ?_, ?_, K.trans (Kt.mono (by decide))⟩
  · have value := VG.Proof.Bignum.bytesAt_eq_of_read copy
    rw [bufferAddress, suffixAddress, memory] at value
    exact value
  · rw [next]
    change src + BitVec.ofNat 32 (drawBytes - len) + BitVec.ofNat 32 len = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.sub_add_cancel length]
  · rw [bufferAddress, memory] at F
    exact F

end VG.Proof.Dsa.X86.Generation
