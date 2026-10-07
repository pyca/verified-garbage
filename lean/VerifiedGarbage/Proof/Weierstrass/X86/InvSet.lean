import VerifiedGarbage.Impl.Weierstrass.X86.InvCfg
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedMath

/-! # Loading the divstep matrix and its initial state -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem setWord_ok {s : State} {base : Addr} {size dst : Nat} (x : BitVec 32)
    (hs : Scr s base size) (hd : dst + 4 ≤ size) :
    WP isa (.block (setWord dst x)) s fun u =>
      w32 u.mem base dst = x.toNat ∧ Keeps [.eax] s u ∧ Outside base dst 4 s.mem u.mem := by
  have hn := hs.nowrap
  unfold setWord
  refine wp_movS rfl fun s₁ U₁ _ => ?_
  have hs₁ := hs.of_keeps U₁.keeps (by decide)
  refine wp_storeS (hs₁.ea (by omega)) (hs₁.write hd) fun u U₂ => WP.block_nil ?_
  refine ⟨?_, U₁.keeps.trans (U₂.keeps _), ?_⟩
  · rw [U₂.mem, w32_write_self, U₁.gpr]
  · rw [U₂.mem, U₁.mem]
    exact writeW32_outside _ _ _ (by omega)

theorem word32_at (m : Mem) (base : Addr) (d n j : Nat) (hj : j < n) :
    w32 m base (d + 4 * j) = val32 m base d n / 2 ^ (32 * j) % 2 ^ 32 := by
  have E := val32_append m base d j (n - j)
  rw [show j + (n - j) = n by omega] at E
  rw [E, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (val32_lt _ _ _ _), Nat.zero_add]
  have hn : n - j = (n - j - 1) + 1 := by omega
  rw [hn, ← low32]

theorem setMatrix_ok {s : State} {base : Addr} {size dst : Nat}
    (hs : Scr s base size) (hd : dst + 16 ≤ size) :
    WP isa (.block (setConst 2 dst (1 + 2 ^ 96))) s fun u =>
      w32 u.mem base dst = 1 ∧ w32 u.mem base (dst + 4) = 0 ∧
      w32 u.mem base (dst + 8) = 0 ∧ w32 u.mem base (dst + 12) = 1 ∧
      Keeps [.eax] s u ∧ Outside base dst 16 s.mem u.mem := by
  refine WP.mono (setConst_ok hs hd (by decide)) fun u ⟨V, K, O⟩ => ?_
  rw [wordsVal_eq_val32] at V
  have W := fun j (hj : j < 4) => word32_at u.mem base dst 4 j hj
  have W₀ := W 0 (by decide); have W₁ := W 1 (by decide)
  have W₂ := W 2 (by decide); have W₃ := W 3 (by decide)
  simp only [Nat.reduceMul, Nat.add_zero, V] at W₀ W₁ W₂ W₃
  exact ⟨W₀, W₁, W₂, W₃, K, O⟩

end VG.Proof.Weierstrass.X86.Inv
