module
import VerifiedGarbage.Proof.Weierstrass.X86.InvSetWord
import VerifiedGarbage.Proof.Weierstrass.X86.InvMatrix

public import VerifiedGarbage.Impl.Weierstrass.X86.InvCfg
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedMath
import VerifiedGarbage.Proof.Mont.X86.Ops
import VerifiedGarbage.Proof.Weierstrass.X86.InvShift
public import VerifiedGarbage.Proof.Weierstrass.X86.InvLinear
import VerifiedGarbage.Proof.Divstep.Tc32Words
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import VerifiedGarbage.Impl.Weierstrass.X86
public import VerifiedGarbage.Impl.Weierstrass.X86.InvMemory
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.BitVec
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! ## `InvSet` -/

@[expose] public section

section

/-! # Loading the divstep matrix and its initial state -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont


end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvInitWords` -/

section

/-! # Zero-extending the inputs and initializing a coefficient to one -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem copyPad_ok {s : State} {base : Addr} {size dst src : Nat}
    (hs : Scr s base size) (hd : dst + 36 ≤ size) (ha : src + 32 ≤ size)
    (sep : dst ≤ src ∨ src + 32 ≤ dst) :
    WP isa (.block (copyPad dst src)) s fun z =>
      val32 z.mem base dst 9 = val32 s.mem base src 8 ∧
      Keeps [.eax] s z ∧ Outside base dst 36 s.mem z.mem := by
  have hn := hs.nowrap
  unfold copyPad
  refine WP.block_append (WP.mono (copy_ok 8 hs (by omega) ha sep) fun s₁ ⟨V₁, K₁, O₁⟩ => ?_)
  refine WP.mono (zeros_ok (hs.of_keeps K₁ (by decide)) (acc := dst + 32) (k := 1) (by omega))
    fun z ⟨O₂, V₂, K₂⟩ => ⟨?_, K₁.trans K₂, ?_⟩
  · simp only [val32, Nat.mul_zero, Nat.add_zero] at V₂
    rw [val32_succ, O₂.val32 (by omega) (by omega), V₁]
    change _ + 2 ^ (32 * 8) * w32 z.mem base (dst + 32) = _
    rw [V₂, Nat.mul_zero, Nat.add_zero]
  · intro x hx
    rw [O₂ x (by omega), O₁ x (by omega)]

theorem one8_ok {s : State} {base : Addr} {size dst : Nat}
    (hs : Scr s base size) (hd : dst + 32 ≤ size) :
    WP isa (.block (one8 dst)) s fun z =>
      val32 z.mem base dst 8 = 1 ∧ Keeps [.eax] s z ∧ Outside base dst 32 s.mem z.mem := by
  have hn := hs.nowrap
  unfold one8
  refine WP.block_append (WP.mono (zeros_ok hs hd) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  refine WP.mono (setWord_ok 1 (hs.of_keeps K₁ (by decide)) (by omega))
    fun z ⟨V₂, K₂, O₂⟩ => ⟨?_, K₁.trans K₂, ?_⟩
  · have Vtail : val32 s₁.mem base (dst + 4) 7 = 0 := by
      change w32 s₁.mem base dst + 2 ^ 32 * val32 s₁.mem base (dst + 4) 7 = 0 at V₁
      omega
    change w32 z.mem base dst + 2 ^ 32 * val32 z.mem base (dst + 4) 7 = 1
    rw [V₂, O₂.val32 (by omega) (by omega), Vtail]
    rfl
  · intro x hx
    rw [O₂ x (by omega), O₁ x hx]

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvSignedShift` -/

section

/-! # Exact division of a signed matrix row by the batch scale -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem shrSigned_ok {s : State} {base : Addr} {size dst src n : Nat}
    (hs : Scr s base size) (hn : 1 ≤ n) (ha : src + 4 * n ≤ size) (hd : dst + 4 * n ≤ size)
    (sep : dst + 4 * n ≤ src ∨ src + 4 * n ≤ dst) {y z : Int}
    (hy : (val32 s.mem base src n : Int) % ((2 ^ (32 * n) : Nat) : Int) =
      y % ((2 ^ (32 * n) : Nat) : Int))
    (hy1 : -((2 ^ (32 * (n - 1)) * 2 ^ 31 : Nat) : Int) ≤ y)
    (hy2 : y < ((2 ^ (32 * (n - 1)) * 2 ^ 31 : Nat) : Int)) (hz : y = 2 ^ 30 * z) :
    WP isa (.block (shr30 dst src n)) s fun u =>
      (val32 u.mem base dst n : Int) % ((2 ^ (32 * n) : Nat) : Int) =
        z % ((2 ^ (32 * n) : Nat) : Int) ∧
      Keeps [.eax, .ebx, .ecx] s u ∧ Outside base dst (4 * n) s.mem u.mem := by
  refine WP.mono (shr30_ok hs hn ha hd sep) fun u ⟨V, K, O⟩ => ⟨?_, K, O⟩
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hy1 hy2 ⊢
  have Q : 2 ^ (32 * (j + 1)) = 2 * (2 ^ (32 * j) * 2 ^ 31) := by
    rw [pow32_succ, show (2 : Nat) ^ 32 = 2 * 2 ^ 31 from rfl]
    ring
  simp only [sext32, Nat.add_sub_cancel, sign32, Q] at V
  rw [Q] at hy ⊢
  exact Divstep.W32.shr_nat (c := 2 ^ 30) (B := 2 ^ 32) rfl rfl
    (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
    (by have := val32_lt s.mem base src (j + 1); rw [Q] at this; exact this) hy hy1 hy2 hz V

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvHalf` -/

section

/-! # Updating a full-width signed divstep value from one matrix row -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem fHalf_ok {s : State} {base : Addr} {size u v acc a b tmp dst k p : Nat} {cu cv f g : Int}
    (hs : Scr s base size) (L : LinearLay size u v acc a b tmp (k + 2) k)
    (hd : dst + 4 * (k + 2) ≤ size)
    (sep : dst + 4 * (k + 2) ≤ acc ∨ acc + 4 * (k + 2) ≤ dst)
    (hu : s.mem.readW (off base u) 32 = BitVec.ofInt 32 cu)
    (hv : s.mem.readW (off base v) 32 = BitVec.ofInt 32 cv)
    (huv : |cu| + |cv| ≤ 2 ^ 30)
    (hf : (val32 s.mem base a (k + 2) : Int) % 2 ^ (32 * (k + 2)) = f % 2 ^ (32 * (k + 2)))
    (hg : (val32 s.mem base b (k + 2) : Int) % 2 ^ (32 * (k + 2)) = g % 2 ^ (32 * (k + 2)))
    (hfb : |f| ≤ p) (hgb : |g| ≤ p) (hp : p < 2 ^ (32 * (k + 1)))
    (hdiv : 2 ^ 30 ∣ cu * f + cv * g) :
    WP isa (.block (linear u v acc a b tmp (k + 2) k ++ shr30 dst acc (k + 2))) s fun z =>
      (val32 z.mem base dst (k + 2) : Int) % 2 ^ (32 * (k + 2)) =
        ((cu * f + cv * g) / 2 ^ 30) % 2 ^ (32 * (k + 2)) ∧ Keeps clob s z ∧
      Unch base [(acc, 4 * (k + 2 + 2)), (tmp, 4 * (k + 1)), (dst, 4 * (k + 2))] s.mem z.mem := by
  refine WP.block_append (WP.mono (linear_ok hs L) fun s₁ ⟨O₁, K₁, V₁⟩ => ?_)
  rw [hu, hv, Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv),
    Divstep.W32.cong_comb hf hg] at V₁
  obtain ⟨lo, hi⟩ := Divstep.W32.comb_range huv hfb hgb hp
  have ha := L.acc_bound
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (shrSigned_ok hs₁ (dst := dst) (src := acc) (by omega) (by omega) hd sep
    (by exact_mod_cast V₁) (by simpa only [show k + 2 - 1 = k + 1 by omega] using lo)
    (by simpa only [show k + 2 - 1 = k + 1 by omega] using hi) (Int.mul_ediv_cancel' hdiv).symm)
    fun z ⟨V, K, O⟩ => ⟨?_, K₁.trans (K.mono (by decide)), ?_⟩
  · exact_mod_cast V
  · intro x hx
    rw [O x (hx (dst, 4 * (k + 2)) (by simp)), O₁ x (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hx (acc, 4 * (k + 2 + 2)) (by simp)
      · exact hx (tmp, 4 * (k + 1)) (by simp))]

end VG.Proof.Weierstrass.X86.Inv

end
