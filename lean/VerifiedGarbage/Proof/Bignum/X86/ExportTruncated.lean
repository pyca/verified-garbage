module

public import VerifiedGarbage.Proof.Bignum.X86.ExportBE

/-! # Big-endian export of the low bytes of a native-word array -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem storeBE_truncated_ok {s : State} {base : Addr} {bytes src w len : Nat}
    (hs : Scr s base bytes) (hl : 0 < len) (hlen : len ≤ 4 * w)
    (ho : src + 4 * w ≤ bytes) (hc : s.gpr .ecx = BitVec.ofNat 32 len)
    (dstFit : (s.gpr .ebx).toNat + len ≤ 2 ^ 32)
    (write : InRegions s.wr (byteAddr (s.gpr .ebx)) len)
    (sep : Region.Disjoint ⟨off base src, len⟩ ⟨byteAddr (s.gpr .ebx), len⟩) :
    WP isa (storeBE src) s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr (s.gpr .ebx)) len =
        Spec.Rsa.i2osp (val32 s.mem base src w % 2 ^ (8 * len)) len ∧
      Frame [⟨byteAddr (s.gpr .ebx), len⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .esi, .ecx] s t := by
  refine WP.mono (storeBE_read_ok hs hl (by omega) hc dstFit write sep) fun t ⟨V, F, K⟩ => ?_
  have eq : (s.mem.read (off base src) (4 * w)).toNat = val32 s.mem base src w := by
    rw [read_eq_val32]
  rw [read_prefix s.mem _ hlen, BitVec.toNat_setWidth, eq] at V
  exact ⟨V, F, K⟩
end VG.Proof.Bignum.X86
