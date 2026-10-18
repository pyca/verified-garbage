module

public import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
public import VerifiedGarbage.Proof.Bignum.ExponentWords

/-! # Save a validated exponent and derive the public limb count -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem saveExponent_frame {s : State} {base : Addr} {bytes : Nat}
    (hs : Scr s base bytes) (hb : 136 ≤ bytes) :
    WP isa (.block PublicFn.saveExponent) s fun t =>
      Outside base 128 8 s.mem t.mem ∧ Keeps [] s t := by
  unfold PublicFn.saveExponent
  refine wp_storeS (hs.ea (by omega)) (hs.write (by omega)) fun u A => ?_
  have hu := hs.of_keeps (A.keeps []) (by decide)
  refine wp_storeS (hu.ea (by omega)) (hu.write (by omega)) fun t B => WP.block_nil ?_
  have Oa : Outside base 128 4 s.mem u.mem := by rw [A.mem]; exact writeW32_outside _ _ _ (by decide)
  have Ob : Outside base 132 4 u.mem t.mem := by rw [B.mem]; exact writeW32_outside _ _ _ (by decide)
  exact ⟨(Oa.mono (by omega) (by omega)).trans (Ob.mono (by omega) (by omega)),
    (A.keeps []).trans (B.keeps [])⟩

theorem saveExponent_ok {s : State} {base : Addr} {bytes e : Nat}
    (hs : Scr s base bytes) (hb : 136 ≤ bytes) (he : e < 2 ^ 33)
    (lo : s.gpr .ebx = BitVec.ofNat 32 (e % 2 ^ 32))
    (hi : s.gpr .edx = BitVec.ofNat 32 (exponentHigh e)) :
    WP isa (.block PublicFn.saveExponent) s fun t =>
      val32 t.mem base 128 2 = e ∧ Outside base 128 8 s.mem t.mem ∧ Keeps [] s t := by
  unfold PublicFn.saveExponent
  refine wp_storeS (hs.ea (by omega)) (hs.write (by omega)) fun u A => ?_
  have hu := hs.of_keeps (A.keeps []) (by decide)
  refine wp_storeS (hu.ea (by omega)) (hu.write (by omega)) fun t B => WP.block_nil ?_
  have Oa : Outside base 128 4 s.mem u.mem := by rw [A.mem]; exact writeW32_outside _ _ _ (by decide)
  have Ob : Outside base 132 4 u.mem t.mem := by rw [B.mem]; exact writeW32_outside _ _ _ (by decide)
  refine ⟨?_, (Oa.mono (by omega) (by omega)).trans (Ob.mono (by omega) (by omega)),
    (A.keeps []).trans (B.keeps [])⟩
  have low : w32 t.mem base 128 = e % 2 ^ 32 := by
    rw [Outside.w32 Ob (.inl (by decide)) (by decide), A.mem, w32_write_self, lo, BitVec.toNat_ofNat,
      Nat.mod_mod]
  have high : w32 t.mem base 132 = e / 2 ^ 32 := by
    rw [B.mem, w32_write_self, A.gpr, hi, BitVec.toNat_ofNat]
    unfold exponentHigh
    omega
  simp only [val32, Nat.mul_zero, Nat.add_zero]
  change w32 t.mem base 128 + 2 ^ 32 * w32 t.mem base 132 = e
  rw [low, high]
  omega

theorem widthArgs_ok {s : State} {len : Nat} (bound : len ≤ 1024)
    (count : readSrc s (.mem (PublicFn.argument 3)) = some (BitVec.ofNat 32 len)) :
    WP isa (.block PublicFn.widthArgs) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.modulusWords len) ∧
      t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold PublicFn.widthArgs
  refine wp_movS count fun u A _ => ?_
  refine wp_addS rfl fun v B _ => ?_
  refine wp_shr (by decide) fun t C _ => WP.block_nil ?_
  refine ⟨?_, C.mem.trans (B.mem.trans A.mem), (A.keeps.trans B.keeps).trans C.keeps⟩
  rw [C.gpr, B.gpr, A.gpr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Spec.Rsa.modulusWords, show (7 : BitVec 32).toNat = 7 from rfl]
  omega

end VG.Proof.Bignum.X86
