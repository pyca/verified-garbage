module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ProductGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DispatchIO
import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductCorrect
import VerifiedGarbage.Proof.Rsa.WordRanges
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # Shared key arithmetic reuses the established paired product kernels -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Key (widths)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem product_ok {s : State} {B : Addr} {Z n N : Nat} {left right : Width} {out a b : Loc}
    (h : Ws s B Z n N)
    (L : ProductGeometry Z (left.words n) (right.words n) (out.offset n) (a.offset n) (b.offset n)) :
    WP isa (product left right out a b) s fun t => Ws t B Z n N ∧
      Outs B (productRanges (left.words n) (right.words n) (out.offset n)) s.mem t.mem ∧
      val32 t.mem B (out.offset n) (left.words n + right.words n + 2) =
        val32 s.mem B (a.offset n) (left.words n) * val32 s.mem B (b.offset n) (right.words n) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  let w := n / 4
  have size := h.size
  have width := h.width
  have bounds : 4 ≤ w ∧ w ≤ 64 := by unfold w; omega
  have sized : n = 4 * w := by unfold w; omega
  unfold product
  refine WP.seq (h.bytes_ok .modulus .eax fun u Ku mu count => ?_)
  change (u.gpr .eax).toNat = 4 * n at count
  refine wp_shr (by decide) fun v V _ => WP.block_nil ?_
  have K : Keeps [.eax] s v := Ku.trans V.keeps
  have memory : v.mem = s.mem := V.mem.trans mu
  have hv := h.keep K (by rw [memory]; exact Outside.refl _ _ _ _)
  have selected : v.gpr .eax = BitVec.ofNat 32 w := by
    apply BitVec.eq_of_toNat_eq
    rw [V.gpr, BitVec.toNat_ushiftRight, count, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : w < 2 ^ 32)]
    unfold w
    omega
  refine dispatchIO_ok (by omega) widths ?_ ?_ selected ?_
  · exact List.mem_map.mpr ⟨w - 4, List.mem_range.mpr (by omega), by omega⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    have H := List.mem_range.mp hi
    omega
  · intro x Kx mx
    have hx := hv.keep Kx (by rw [mx]; exact Outside.refl _ _ _ _)
    rw [← sized]
    refine WP.mono (VG.Proof.RsaKeyGen.X86.Product.correct hx.old.workspace L.toLayout)
      fun t ⟨O, value, Kt⟩ => ?_
    have before : x.mem = s.mem := mx.trans memory
    rw [before] at O value
    have frame : Outs B (productRanges (left.words n) (right.words n) (out.offset n)) s.mem t.mem :=
      VG.Proof.Rsa.outs_cover O (by
        intro region member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ⟨(128, 28), List.mem_cons_self .., Nat.le_refl _, by decide⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩)
    have keep : Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t :=
      (K.mono (by decide)).trans ((Kx.mono (by decide)).trans (Kt.mono (by decide)))
    refine ⟨h.keep keep (VG.Proof.Rsa.X86.KeyRt.outs_outside frame ?_), frame, value, keep⟩
    intro region member
    simp only [productRanges, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · have head := h.hdr_le
      unfold VG.Impl.Rsa.X86.Keys.hdr at head
      omega
    · exact L.out_bound

end VG.Proof.RsaKeyGen.X86.KeyRuntime
