module

import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
import VerifiedGarbage.Proof.Bignum.X86.CopyRead
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # Copies of bytes into `scratch` -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)
open VG.Proof.Bignum.X86 (byteAddr)

/-- Equal reads are equal bytes. -/
theorem bytesAt_of_read {m m' : Mem} {a b : Addr} {n : Nat} (h : m'.read b n = m.read a n) :
    Spec.Rsa.bytesAt m' b n = Spec.Rsa.bytesAt m a n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  rw [← Mem.extractLsb'_read m' b hi, ← Mem.extractLsb'_read m a hi, h]

/-- `n` bytes from `scratch + src` to `scratch + dst`. -/
theorem copyS_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dst src n : Nat}
    (hn : 0 < n) (hd : dst + n ≤ size) (hsrc : src + n ≤ size) (apart : dst + n ≤ src ∨ src + n ≤ dst) :
    WP isa (copyS dst src n) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base dst) n = Spec.Rsa.bytesAt s.mem (off base src) n ∧
      Frame [⟨off base dst, n⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx] s t := by
  have nw := hs.nowrap
  have sl := hs.size_lt
  unfold copyS copyTo
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine scr_ok fun s₁ e₁ g₁ m₁ rd₁ wr₁ _ => scr_ok fun s₂ e₂ g₂ m₂ rd₂ wr₂ _ => wp_movi fun s₃ u₃ =>
    WP.block_nil ?_
  have edi₂ : s₂.gpr .edi = s.gpr .edi := by rw [g₂ _ (by decide), g₁ _ (by decide)]
  have srcW := Scr.wide hs (d := src) (by omega)
  have dstW := Scr.wide hs (d := dst) (by omega)
  have srcN := Scr.toNat_add hs (d := src) (by omega)
  have dstN := Scr.toNat_add hs (d := dst) (by omega)
  refine WP.mono (VG.Proof.Bignum.X86.copyBuffers_ok (src := s.gpr .edi + BitVec.ofNat 32 src)
    (dst := s.gpr .edi + BitVec.ofNat 32 dst) hn (by omega) (by rw [srcN]; omega) (by rw [dstN]; omega)
    ?_ ?_ ?_ ?_ ?_ ?_) fun t ⟨R, _, _, F, K⟩ => ?_
  · simp only [byteAddr, srcW, u₃.rd, u₃.wr, rd₂, wr₂, rd₁, wr₁]; exact hs.read (by omega)
  · simp only [byteAddr, dstW, u₃.wr, wr₂, wr₁]; exact hs.write (by omega)
  · simp only [byteAddr, srcW, dstW]; exact Offset.disjoint base (by omega) (by omega) (by omega)
  · rw [u₃.other _ (by decide), g₂ _ (by decide), e₁]
  · rw [u₃.other _ (by decide), e₂, g₁ _ (by decide)]
  · rw [u₃.gpr]
  simp only [byteAddr, srcW, dstW, u₃.mem, m₂, m₁] at R F
  refine ⟨bytesAt_of_read R, F, ?_⟩
  refine ⟨fun r hr => ?_, by rw [K.2.1, u₃.rd, rd₂, rd₁], by rw [K.2.2, u₃.wr, wr₂, wr₁]⟩
  rw [K.1 r hr, u₃.other r (by simp_all), g₂ r (by simp_all), g₁ r (by simp_all)]

/-- `n` bytes from the address in the word at `scratch + w` (a range of a
readable region apart from `scratch`) to `scratch + dst`. -/
theorem copyIn_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w dst n : Nat} {S : BitVec 32}
    (hw : w + 4 ≤ size) (hS : s.mem.readW (off base w) 32 = S) {R : Region} (hR : R ∈ s.rd)
    (hRs : R.Disjoint ⟨base, size⟩) (hRl : R.len ≤ 2 ^ 32) {o : Nat} (hSo : S.setWidth 64 = R.base + BitVec.ofNat 64 o)
    (ho : o + n ≤ R.len) (hSn : S.toNat + n ≤ 2 ^ 32)
    (hn : 0 < n) (hd : dst + n ≤ size) :
    WP isa (copyTo [.mov .esi (.mem (sc w))] dst n) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base dst) n = Spec.Rsa.bytesAt s.mem (R.base + BitVec.ofNat 64 o) n ∧
      Frame [⟨off base dst, n⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx] s t := by
  have nw := hs.nowrap
  have sl := hs.size_lt
  unfold copyTo
  refine WP.seq ?_
  simp only [List.cons_append, List.nil_append]
  refine ld_ok hs hw fun s₁ u₁ => scr_ok fun s₂ e₂ g₂ m₂ rd₂ wr₂ _ => wp_movi fun s₃ u₃ => WP.block_nil ?_
  have dstW := Scr.wide hs (d := dst) (by omega)
  have dstN := Scr.toNat_add hs (d := dst) (by omega)
  have sub : Region.Sub ⟨S.setWidth 64, n⟩ R := by rw [hSo]; exact Offset.sub_base _ ho
  refine WP.mono (VG.Proof.Bignum.X86.copyBuffers_ok (src := S)
    (dst := s.gpr .edi + BitVec.ofNat 32 dst) hn (by omega) hSn (by rw [dstN]; omega)
    ?_ ?_ ?_ ?_ ?_ ?_) fun t ⟨Rd, _, _, F, K⟩ => ?_
  · simp only [byteAddr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]
    rw [hSo]
    exact ⟨R, List.mem_append_left _ hR, Offset.contains_base _ ho (by omega)⟩
  · simp only [byteAddr, dstW, u₃.wr, wr₂, u₁.wr]; exact hs.write (by omega)
  · simp only [byteAddr, dstW]
    exact (hRs.sub_left sub).sub_right (Offset.sub_base base hd)
  · rw [u₃.other _ (by decide), g₂ _ (by decide), u₁.gpr, hS]
  · rw [u₃.other _ (by decide), e₂, u₁.other _ (by decide)]
  · rw [u₃.gpr]
  simp only [byteAddr, dstW, u₃.mem, m₂, u₁.mem] at Rd F
  refine ⟨?_, F, ?_⟩
  · rw [bytesAt_of_read Rd, hSo]
  · refine ⟨fun r hr => ?_, by rw [K.2.1, u₃.rd, rd₂, u₁.rd], by rw [K.2.2, u₃.wr, wr₂, u₁.wr]⟩
    rw [K.1 r hr, u₃.other r (by simp_all), g₂ r (by simp_all), u₁.other r (by simp_all)]

end VG.Proof.Dsa.X86.Generation
