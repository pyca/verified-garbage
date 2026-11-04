module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Cached
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH's context on x86-64: the public scalar width -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Cached
open VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Spec.RsaKeyGen (bitLength)

theorem shr_one_div (x j : Nat) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 (x / 2 ^ j) >>> 1 = BitVec.ofNat 64 (x / 2 ^ (j + 1)) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : x / 2 ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  have h2 : x / 2 ^ (j + 1) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
    Nat.shiftRight_eq_div_pow, Nat.pow_one, Nat.div_div_eq_div_mul, ← Nat.pow_succ]

/-- `rcx := ` the bit length of the nonzero byte in `rax`. -/
theorem byteBits_ok {s : State} {b : Byte} (hb : b ≠ 0) (hax : s.gpr .rax = b.setWidth 64) :
    WP isa Precompute.byteBits s fun t => t.gpr .rcx = BitVec.ofNat 64 (bitLength b.toNat) ∧
      t.mem = s.mem ∧ Keep [.rax, .rcx] s t := by
  have hb0 : b.toNat ≠ 0 := fun h => hb (BitVec.eq_of_toNat_eq h)
  have hbl := KeyScalar.bitLength_bounds hb0
  have hlt : b.toNat < 256 := b.isLt
  have hpos : 1 ≤ bitLength b.toNat := by
    by_contra h; have : bitLength b.toNat = 0 := by omega
    rw [this] at hbl; omega
  unfold Precompute.byteBits
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.mem = s.mem)
    (by xrun) rfl) fun s₁ ⟨⟨hcx₁, hm₁⟩, k₁⟩ => ?_)
  let Inv : Nat → State → Prop := fun j t => t.gpr .rax = BitVec.ofNat 64 (b.toNat / 2 ^ j) ∧
    t.gpr .rcx = BitVec.ofNat 64 j ∧ t.mem = s.mem ∧ Keep [.rax, .rcx] s t
  refine wp_upto (a := 0) (N := bitLength b.toNat) hpos Inv (fun j _ hj t ⟨hat, hct, hmt, kt⟩ => ?_)
    (fun t h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩)
    ⟨by rw [(k₁.gpr (by decide)).trans hax]; apply BitVec.eq_of_toNat_eq; simp,
      hcx₁, hm₁, k₁.mono (by decide)⟩
  have hz : (BitVec.ofNat 64 (b.toNat / 2 ^ (j + 1)) == 0) = decide (j + 1 = bitLength b.toNat) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h
      have h' : b.toNat / 2 ^ (j + 1) = 0 := by
        have := congrArg BitVec.toNat h
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))] at this
      rw [Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)] at h'
      by_contra hne
      have : 2 ^ (bitLength b.toNat - 1) ≥ 2 ^ (j + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · intro h
      rw [h, Nat.div_eq_of_lt hbl.2]; rfl
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t' => t'.gpr .rax = BitVec.ofNat 64 (b.toNat / 2 ^ (j + 1)) ∧
      t'.gpr .rcx = BitVec.ofNat 64 (j + 1) ∧ t'.mem = t.mem ∧ t'.zf = some (decide (j + 1 = bitLength b.toNat)))
    (by xrun [hat, hct, shr_one_div _ _ (by omega : b.toNat < 2 ^ 64), ofNat_add_one, BitVec.and_self, hz]) rfl)
    fun t' ⟨⟨ha', hc', hm', hz'⟩, k'⟩ => ⟨hz', ha', hc', hm'.trans hmt, (kt.trans k').mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.Cached
