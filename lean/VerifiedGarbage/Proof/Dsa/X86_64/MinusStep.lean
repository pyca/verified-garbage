module
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # Borrow propagation when forming DSA modulus-minus constants -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- After `j` words of `modulusMinus`'s loop: `Y_j + amount = N_j + 2^(64 j) c`. -/
structure MinusInv (s₀ : State) (B : Addr) (Z eN eY amount : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eY (8 * j) s₀.mem t.mem
  val : ∃ c : Bool, t.gpr .rbp = mask c ∧
    wv t.mem B eY j + amount = wv s₀.mem B eN j + 2 ^ (64 * j) * c.toNat

theorem minusStep_ok {s₀ : State} {B : Addr} {Z w eN eY amount : Nat}
    (hbx : s₀.gpr .rbx = off B eY) (hsi : s₀.gpr .rsi = off B eN) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hY : eY + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z)
    (hsep : eY + 8 * w ≤ eN ∨ eN + 8 * w ≤ eY) {j : Nat} (hj : j < w) {t : State}
    (hI : MinusInv s₀ B Z eN eY amount j t) :
    WP isa (.block (([cfFromRbp, .mov .rax (.mem (ix .rsi .r14)), .alu .sbb .rax (.imm 0),
        .store (ix .rbx .r14) .rax, cfToRbp] : List Instr) ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ MinusInv s₀ B Z eN eY amount (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B eY := (hI.keep.gpr (by decide)).trans hbx
  have tsi : t.gpr .rsi = off B eN := (hI.keep.gpr (by decide)).trans hsi
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = mask c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (off B (eY + 8 * j)) r ∧
        r.toNat + c.toNat = (word t.mem B (eN + 8 * j)).toNat + 2 ^ 64 * c'.toNat) ?_ rfl)
    fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 tbx hI.r14, addr0 tsi hI.r14, hbp, cf_mask, sx0,
      hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega_arith), hI.scr.st (show eY + 8 * j + 8 ≤ Z by omega_arith)]
    refine ⟨_, rfl, _, rfl, ?_⟩
    have := sbb_toNat (word t.mem B (eN + 8 * j)) 0 c
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero, Nat.zero_add] at this ⊢
    exact this
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_arith) (by omega_arith)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hx : word t.mem B (eN + 8 * j) = word s₀.mem B (eN + 8 * j) := hI.out.word (by omega_arith) (by omega_arith)
  rw [hx] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨c', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · have hlow : wv t.mem B eY j = wv (t.mem.writeW (off B (eY + 8 * j)) r) B eY j :=
      ((writeW_outside t.mem B r (by omega_arith)).wv (Or.inl (by omega_arith)) (by omega_arith)).symm
    rw [hm', hm]
    simp only [wv]
    rw [← hlow, word_writeW_self, pow64_succ]
    grind

end VG.Proof.Dsa.X86_64
