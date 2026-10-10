import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned

/-! ## `InvRedSumMath` -/

section

/-! # Appending a sign word after a bounded unsigned product -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.Proof.Mont

theorem add_top_mod {A V top sign : Nat} (hA : 0 < A) (hV : V < A) :
    V + A * ((top + sign) % 2 ^ 32) = (V + A * top + A * sign) % (A * 2 ^ 32) := by
  rw [Nat.add_assoc, ← Nat.mul_add, Nat.mod_mul, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hV, Nat.add_mul_div_left _ _ hA, Nat.div_eq_of_lt hV, Nat.zero_add]

theorem row_bound {m : Mem} {base : Addr} {acc tmp modulus n : Nat}
    (h : val32 m base acc (n + 2) < 2 ^ (32 * (n + 1))) :
    val32 m base acc (n + 2) + w32 m base tmp * val32 m base modulus n < 2 ^ (32 * (n + 2)) := by
  have P := product_bound m base tmp modulus n
  have E : 2 ^ (32 * (n + 2)) = 2 ^ 32 * 2 ^ (32 * (n + 1)) := pow32_succ (n + 1)
  rw [E]
  omega

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvRedWord` -/

section

/-! # The quotient and sign-extension words of a divstep reduction -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem quotientWord_ok {s : State} {base : Addr} {size src dst : Nat} (minv : BitVec 32)
    (hs : Scr s base size) (ha : src + 4 ≤ size) (hd : dst + 4 ≤ size) :
    WP isa (.block (quotientWord src dst minv)) s fun u =>
      w32 u.mem base dst = w32 s.mem base src * minv.toNat % 2 ^ 32 ∧
      Keeps [.eax, .ecx, .edx] s u ∧ Outside base dst 4 s.mem u.mem := by
  have hn := hs.nowrap
  unfold quotientWord
  refine wp_movS (readSrc_sc hs ha) fun s₁ U₁ _ => ?_
  refine wp_movS rfl fun s₂ U₂ _ => ?_
  refine wp_mul fun s₃ U₃ => ?_
  have K : Keeps [.eax, .ecx, .edx] s s₃ :=
    ((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans (U₃.keeps.mono (by decide))
  have hs₃ := hs.of_keeps K (by decide)
  refine wp_storeS (hs₃.ea (by omega)) (hs₃.write hd) fun u U₄ => WP.block_nil ?_
  refine ⟨?_, K.trans (U₄.keeps _), ?_⟩
  · rw [U₄.mem, w32_write_self, U₃.eax, U₂.other _ (by decide), U₁.gpr, U₂.gpr,
      BitVec.toNat_ofNat]
  · rw [U₄.mem, U₃.mem, U₂.mem, U₁.mem]
    exact writeW32_outside _ _ _ (by omega)

theorem addSignWord_ok {s : State} {base : Addr} {size dst : Nat}
    (hs : Scr s base size) (hd : dst + 4 ≤ size) :
    WP isa (.block (addSignWord dst)) s fun u =>
      w32 u.mem base dst = (w32 s.mem base dst + (s.gpr .esi).toNat) % 2 ^ 32 ∧
      Keeps [.eax] s u ∧ Outside base dst 4 s.mem u.mem := by
  have hn := hs.nowrap
  unfold addSignWord
  refine wp_movS (readSrc_sc hs hd) fun s₁ U₁ _ => ?_
  refine wp_addS rfl fun s₂ U₂ _ => ?_
  have K := U₁.keeps.trans U₂.keeps
  have hs₂ := hs.of_keeps K (by decide)
  refine wp_storeS (hs₂.ea (by omega)) (hs₂.write hd) fun u U₃ => WP.block_nil ?_
  refine ⟨?_, K.trans (U₃.keeps _), ?_⟩
  · rw [U₃.mem, w32_write_self, U₂.gpr, U₁.gpr, U₁.other _ (by decide), BitVec.toNat_add]
  · rw [U₃.mem, U₂.mem, U₁.mem]
    exact writeW32_outside _ _ _ (by omega)

end VG.Proof.Weierstrass.X86.Inv

end
