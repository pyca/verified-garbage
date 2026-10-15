module

public import VerifiedGarbage.Proof.Dsa.X86.DigestPadFill
public import VerifiedGarbage.Proof.Dsa.DomainShape

/-! # Leading zero padding preserves the selected digest integer -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG

theorem paddedBytes_eq (mem : Mem) (source : Addr) (len : Nat) (hl : len ≤ 32) :
    (List.range 32).map (paddedByte mem source len) =
      List.replicate (32 - len) 0 ++ Spec.Rsa.bytesAt mem source len := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_append, List.length_replicate, Spec.Rsa.bytesAt]
    simp only [List.length_map, List.length_range]
    omega
  · intro i hi hj
    have H : i < 32 := by simpa only [List.length_map, List.length_range] using hi
    simp only [List.getElem_map, List.getElem_range, paddedByte]
    by_cases low : i < 32 - len
    · rw [ite_eq_left low, List.getElem_append_left (by simpa only [List.length_replicate] using low)]
      simp only [List.getElem_replicate]
    · rw [ite_eq_right low, List.getElem_append_right (by simp only [List.length_replicate]; omega)]
      simp only [List.length_replicate, Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]

theorem decodeBE_zero_prefix (n : Nat) (bytes : List Byte) :
    Spec.Dsa.decodeBE (List.replicate n 0 ++ bytes) = Spec.Dsa.decodeBE bytes := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, VG.Proof.Dsa.decodeBE_zero_cons, ih]

theorem digestPadFill_value {s t : VG.X86.State} {base : Addr} {size len : Nat} {source : BitVec 32}
    (hs : VG.Proof.Mont.X86.Scr s base size) (space : VG.Impl.Dsa.X86.DigestPad.output + 32 ≤ size)
    (hp : s.gpr .esi = source) (hl : len ≤ 32) (fits : source.toNat + len ≤ 2 ^ 32)
    (read : ∀ i < len, InRegions (s.rd ++ s.wr) (source.setWidth 64 + BitVec.ofNat 64 i) 1)
    (apart : Region.Disjoint ⟨source.setWidth 64, len⟩ ⟨base, size⟩)
    {trace : List Leak} (E : Exec VG.X86.isa (.block (VG.Impl.Dsa.X86.DigestPad.fill len)) s trace t) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (VG.Proof.Mont.off base VG.Impl.Dsa.X86.DigestPad.output) 32) =
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (source.setWidth 64) len) := by
  obtain ⟨Bytes, _, _⟩ := wp_result (digestPadPrefix_ok hs space hp hl fits read apart 32 (Nat.le_refl _)) E
  rw [Bytes, paddedBytes_eq _ _ _ hl, decodeBE_zero_prefix]

end VG.Proof.Dsa.X86
