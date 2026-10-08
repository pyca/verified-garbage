import VerifiedGarbage.Impl.Weierstrass.X86.NafPrep
import VerifiedGarbage.Proof.Mont.X86.Chain

/-! One word of the public NAF residual's in-place right shift. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem nafRotateBit (x : BitVec 32) :
    ((x &&& (1 : BitVec 32)).rotateRight 1).toNat = 2^31*(x.toNat%2) := by
  have h : x &&& (1 : BitVec 32) = BitVec.ofNat 32 (x.toNat%2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and,BitVec.toNat_ofNat]
    change x.toNat &&& 1 = (x.toNat%2)%2^32
    rw [Nat.and_one_is_mod]
    omega
  rw [h]
  have hm : x.toNat%2=0 ∨ x.toNat%2=1 := by omega
  rcases hm with hm | hm <;> rw [hm] <;> rfl

theorem nafShiftWord_value (lo hi : BitVec 32) :
    (lo >>> 1 + (hi &&& (1 : BitVec 32)).rotateRight 1).toNat =
      (lo.toNat/2+2^31*hi.toNat)%2^32 := by
  rw [BitVec.toNat_add,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,nafRotateBit]
  omega

theorem nafShiftWord_ok {s : State} {base : Addr} {size work i : Nat}
    (hs : Scr s base size) (ha : work+4*(i+1)+4≤size) :
    WP isa (.block (Naf.shiftWord work i)) s fun u =>
      w32 u.mem base (work+4*i) =
        (w32 s.mem base (work+4*i)/2+2^31*w32 s.mem base (work+4*(i+1)))%2^32 ∧
      Keeps [.eax,.edx] s u ∧ Outside base (work+4*i) 4 s.mem u.mem := by
  have hn := hs.nowrap
  unfold Naf.shiftWord
  refine wp_movS (readSrc_sc hs (by omega)) fun s₁ U₁ _ => ?_
  refine wp_shr (by decide) fun s₂ U₂ _ => ?_
  have K₂ : Keeps [.eax,.edx] s s₂ :=
    (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  refine wp_movS (readSrc_sc (hs.of_keeps K₂ (by decide)) ha) fun s₃ U₃ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₄ U₄ => ?_
  refine wp_ror (by decide) fun s₅ U₅ => ?_
  refine wp_addS rfl fun s₆ U₆ _ => ?_
  have K : Keeps [.eax,.edx] s s₆ :=
    (((K₂.trans (U₃.keeps.mono (by decide))).trans (U₄.keeps.mono (by decide))).trans
      (U₅.keeps.mono (by decide))).trans (U₆.keeps.mono (by decide))
  have hs₆ := hs.of_keeps K (by decide)
  refine wp_storeS (hs₆.ea (by omega)) (hs₆.write (by omega)) fun u U₇ => WP.block_nil ?_
  refine ⟨?_,K.trans (U₇.keeps _),?_⟩
  · rw [U₇.mem,w32_write_self,U₆.gpr,U₅.other _ (by decide),U₄.other _ (by decide),
      U₃.other _ (by decide),U₂.gpr,U₁.gpr,U₅.gpr,U₄.gpr,U₃.gpr,U₂.mem,U₁.mem]
    exact nafShiftWord_value _ _
  · rw [U₇.mem,U₆.mem,U₅.mem,U₄.mem,U₃.mem,U₂.mem,U₁.mem]
    exact writeW32_outside _ _ _ (by omega)

end VG.Proof.Weierstrass.X86
