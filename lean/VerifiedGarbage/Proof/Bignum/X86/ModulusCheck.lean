module

public import VerifiedGarbage.Proof.Bignum.X86.ModulusRead
public import VerifiedGarbage.Proof.Bignum.X86.ModulusBounds
public import VerifiedGarbage.Proof.Bignum.X86.ModulusFinish

/-! # i686 modulus validation agrees with the shared RSA specification -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem modulusCheck_ok (s : State) {k : Nat}
    (hk : 64 ≤ k) (hk' : k ≤ 1024) (fit : (s.gpr .esi).toNat + k ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr (s.gpr .esi)) k)
    (count : s.gpr .ecx = BitVec.ofNat 32 k) :
    WP isa (.block modulusCheck) s fun t =>
      t.zf = some (Spec.Rsa.modulusValid
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (s.gpr .esi)) k)) k) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .edx, .ebp] s t := by
  unfold modulusCheck
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (modulusRead_ok s (by omega) fit read count)
    fun u ⟨first, last, M, K⟩ => ?_)
  have byteNat (b : Byte) : (b.setWidth 32).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
  have firstNat : (u.gpr .eax).toNat = (s.mem (byteAddr (s.gpr .esi))).toNat := by rw [first, byteNat]
  have lastNat : (u.gpr .edx).toNat =
      (s.mem (byteAddr (s.gpr .esi) + BitVec.ofNat 64 (k - 1))).toNat := by rw [last, byteNat]
  have countNat : (u.gpr .ecx).toNat = k := by
    rw [K.1 .ecx (by decide), count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.block_append (WP.mono (modulusBounds_ok u (by rw [countNat]; exact hk)
    (by rw [countNat]; exact hk')) fun v ⟨low, top, Mv, Kv⟩ => ?_)
  refine WP.mono (modulusFinish_ok v) fun t ⟨Z, Mt, Kt⟩ => ?_
  refine ⟨?_, Mt.trans (Mv.trans M),
    ((K.mono (by decide)).trans (Kv.mono (by decide))).trans (Kt.mono (by decide))⟩
  rw [Z, low, top, Kv.1 .edx (by decide), modulusCheck_value _ _ _
    (by rw [firstNat]; exact (s.mem _).isLt) (by rw [countNat]; exact hk) (by rw [countNat]; exact hk'),
    firstNat, lastNat, countNat]
  rw [modulusValid_iff (bytesAt_length _ _ _) hk hk']
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, BitVec.add_zero]

end VG.Proof.Bignum.X86
