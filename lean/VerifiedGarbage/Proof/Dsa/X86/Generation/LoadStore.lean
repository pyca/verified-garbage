module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86.LoadBE
import VerifiedGarbage.Proof.Bignum.X86.ExportBE
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Framework.Offset

/-! # Big-endian bytes of `scratch` into arrays of 32-bit words, and back -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation (loadS storeS)

/-- The `len` big-endian bytes at `scratch + src` into the `2 k` words at
`scratch + o`. -/
theorem loadS_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {k o src len : Nat}
    (hk : 0 < k) (ho : o + 8 * k ≤ size) (hl : 0 < len) (hlen : len ≤ 8 * k) (hsrc : src + len ≤ size)
    (hsep : src + len ≤ o ∨ o + 8 * k ≤ src) :
    WP isa (loadS k o src len) s fun t =>
      val32 t.mem base o (2 * k) = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base src) len) ∧
      Outside base o (8 * k) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nw := hs.nowrap
  have sl := hs.size_lt
  unfold loadS
  refine WP.seq (scr_ok fun s₁ e₁ g₁ m₁ rd₁ wr₁ _ => wp_movi fun s₂ u₂ => WP.block_nil ?_)
  have hs₂ : Scr s₂ base size := Scr.of_eq hs (by rw [u₂.other _ (by decide), g₁ _ (by decide)])
    (by rw [u₂.other _ (by decide), g₁ _ (by decide)]) (by rw [u₂.wr, wr₁])
  have esi₂ : s₂.gpr .esi = s.gpr .edi + BitVec.ofNat 32 src := by rw [u₂.other _ (by decide), e₁]
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, m₁]
  have srcW := Scr.wide hs (d := src) (by omega)
  have K₂ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s s₂ :=
    ⟨fun r hr => by rw [u₂.other r (by simp_all), g₁ r (by simp_all)], by rw [u₂.rd, rd₁], by rw [u₂.wr, wr₁]⟩
  refine WP.mono (VG.Proof.Bignum.X86.loadBE_ok hs₂ hk ho hl hlen
    (by rw [esi₂, Scr.toNat_add hs (by omega)]; omega) u₂.gpr
    (by rw [esi₂, VG.Proof.Bignum.X86.byteAddr, srcW, u₂.rd, u₂.wr, rd₁, wr₁]; exact hs.read hsrc)
    (by rw [esi₂, VG.Proof.Bignum.X86.byteAddr, srcW]
        exact Offset.disjoint base (by omega) (by omega) (by omega))) fun t ⟨V, O, K⟩ => ?_
  rw [esi₂, VG.Proof.Bignum.X86.byteAddr, srcW, m₂, wordsVal_eq_val32] at V
  rw [m₂] at O
  exact ⟨by rw [V, decodeBE_os2ip], O, K₂.trans K⟩

/-- The `2 n` words at `scratch + o`, as `len` big-endian bytes at
`scratch + dst`. -/
theorem storeS_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o dst len n : Nat}
    (hl : 0 < len) (hlen : len ≤ 8 * n) (ho : o + 8 * n ≤ size) (hd : dst + len ≤ size)
    (hsep : o + len ≤ dst ∨ dst + len ≤ o) (fit : val32 s.mem base o (2 * n) < 2 ^ (8 * len)) :
    WP isa (storeS o dst len) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base dst) len = Spec.Dsa.encodeBE len (val32 s.mem base o (2 * n)) ∧
      Frame [⟨off base dst, len⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx] s t := by
  have nw := hs.nowrap
  have sl := hs.size_lt
  unfold storeS
  refine WP.seq (scr_ok fun s₁ e₁ g₁ m₁ rd₁ wr₁ _ => wp_movi fun s₂ u₂ => WP.block_nil ?_)
  have hs₂ : Scr s₂ base size := Scr.of_eq hs (by rw [u₂.other _ (by decide), g₁ _ (by decide)])
    (by rw [u₂.other _ (by decide), g₁ _ (by decide)]) (by rw [u₂.wr, wr₁])
  have ebx₂ : s₂.gpr .ebx = s.gpr .edi + BitVec.ofNat 32 dst := by rw [u₂.other _ (by decide), e₁]
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, m₁]
  have dstW := Scr.wide hs (d := dst) (by omega)
  have K₂ : Keeps [.eax, .ebx, .esi, .ecx] s s₂ :=
    ⟨fun r hr => by rw [u₂.other r (by simp_all), g₁ r (by simp_all)], by rw [u₂.rd, rd₁], by rw [u₂.wr, wr₁]⟩
  refine WP.mono (VG.Proof.Bignum.X86.storeBE_ok hs₂ (n := n) hl hlen ho u₂.gpr
    (by rw [m₂, wordsVal_eq_val32]; exact fit)
    (by rw [ebx₂, Scr.toNat_add hs (by omega)]; omega)
    (by rw [ebx₂, VG.Proof.Bignum.X86.byteAddr, dstW, u₂.wr, wr₁]; exact hs.write hd)
    (by rw [ebx₂, VG.Proof.Bignum.X86.byteAddr, dstW]
        exact Offset.disjoint base (by omega) (by omega) (by omega))) fun t ⟨V, F, K⟩ => ?_
  rw [ebx₂, VG.Proof.Bignum.X86.byteAddr, dstW, m₂, wordsVal_eq_val32] at V
  rw [ebx₂, VG.Proof.Bignum.X86.byteAddr, dstW, m₂] at F
  exact ⟨by rw [V, encodeBE_i2osp], F, K₂.trans K⟩

end VG.Proof.Dsa.X86.Generation
