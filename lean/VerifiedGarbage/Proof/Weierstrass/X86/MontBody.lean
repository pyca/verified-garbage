import VerifiedGarbage.Proof.Weierstrass.X86.MontMul
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareBody

/-! # Selecting the x86 P-256 square from public operand pointers -/
namespace VG.Proof.Weierstrass.X86.Mont
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

theorem square_pointer_eq {s : State} {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (pa : Ptr s .edi a) (pb : Ptr s .esi b) (he : (s.gpr .edi - s.gpr .esi == 0) = true) : a = b := by
  have h : s.gpr .edi - s.gpr .esi = 0 := by simpa only [beq_iff_eq] using he
  have h' := BitVec.sub_eq_iff_eq_add.mp h
  have hz : ∀ x : BitVec 32, (0 : BitVec 32) + x = x := BitVec.zero_add
  rw [hz, pa, pb] at h'
  have h'' := congrArg (fun x : BitVec 32 => x - s.gpr .ebp) h'
  rw [BitVec.add_comm (s.gpr .ebp), BitVec.add_sub_cancel,
    BitVec.add_comm (s.gpr .ebp), BitVec.add_sub_cancel] at h''
  have hnat := congrArg BitVec.toNat h''
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hnat

theorem mulBody_ok {s : State} {base : Addr} {k m pa pb : Nat} (hb : Bx s base 8192)
    (hM : MulOk k m) (hpa : Ptr s .edi pa) (hpb : Ptr s .esi pb)
    (hL : MulLayB k 8192 pa pb (own k)) (hB : val32 s.mem base pb (2 * k) < m) :
    WP isa (mulBody k m) s fun u =>
      Outside base (own k) (24 * k + 4) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .edi] s u ∧
      val32 u.mem base (own k + 4 * (2 * k)) (2 * k + 1) < 2 * m ∧
      ∃ U, 2 ^ (32 * (2 * k)) * val32 u.mem base (own k + 4 * (2 * k)) (2 * k + 1) =
        val32 s.mem base pa (2 * k) * val32 s.mem base pb (2 * k) + U * m := by
  have hk := hM.k0
  have general : WP isa (.block (rowsF k m (2 * k))) s fun u =>
      Outside base (own k) (24 * k + 4) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .edi] s u ∧
      val32 u.mem base (own k + 4 * (2 * k)) (2 * k + 1) < 2 * m ∧
      ∃ U, 2 ^ (32 * (2 * k)) * val32 u.mem base (own k + 4 * (2 * k)) (2 * k + 1) =
        val32 s.mem base pa (2 * k) * val32 s.mem base pb (2 * k) + U * m :=
    WP.mono (rowsF_ok hb hM hpa hpb hL hB (2 * k) (by omega) (by omega))
      fun _ ⟨O, K, H, E⟩ => ⟨O.mono (by omega) (by omega), K.mono (by decide), H, E⟩
  unfold mulBody
  split
  next he =>
    obtain ⟨rfl, rfl⟩ := he
    refine WP.seq (wp_cmp fun t R _ Z => ?_)
    apply WP.block_nil
    refine WP.ite (s.gpr .edi - s.gpr .esi == 0) Z (fun h => ?_) (fun _ => ?_)
    · have hpaFit := hL.pa; have hpbFit := hL.pb
      have ho : own 4 = 3840 := rfl
      have hab := square_pointer_eq (by omega : pa < 2 ^ 32) (by omega : pb < 2 ^ 32) hpa hpb h
      subst pa
      have K := R.keeps []
      refine WP.mono (squareBody_ok (hb.of_keeps K (by decide))
        (hpb.of_keeps K (by decide) (by decide)) hpbFit (by rw [R.mem]; exact hB))
        fun u ⟨O, K', H, E⟩ => ?_
      rw [R.mem] at O E
      exact ⟨O, (K.mono (by decide)).trans K', H, E⟩
    · have K := R.keeps []
      refine WP.mono (rowsF_ok (hb.of_keeps K (by decide)) hM
        (hpa.of_keeps K (by decide) (by decide)) (hpb.of_keeps K (by decide) (by decide)) hL
        (by rw [R.mem]; exact hB) 8 (by decide) (by decide)) fun u ⟨O, K', H, E⟩ => ?_
      rw [R.mem] at O E
      exact ⟨O.mono (by omega) (by omega), (K.mono (by decide)).widen K' (by decide), H, E⟩
  next _ => exact general

end VG.Proof.Weierstrass.X86.Mont
