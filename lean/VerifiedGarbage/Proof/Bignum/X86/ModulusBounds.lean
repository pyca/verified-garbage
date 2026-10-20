module

public import VerifiedGarbage.Impl.Bignum.X86.ModulusCheck
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Leading-byte and minimum-modulus checks on i686 -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem rotate_threshold (k : BitVec 32) (hk : 64 ≤ k.toNat) (hk' : k.toNat ≤ 1024) :
    (k - 64).rotateRight 24 = (k - 64) <<< 8 := by
  have high : (k - 64) >>> 24 = (0 : BitVec 32) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
    simp only [show (64 : BitVec 32).toNat = 64 from rfl,
      show (0 : BitVec 32).toNat = 0 from rfl]
    omega
  rw [BitVec.rotateRight_def]
  change (k - 64) >>> 24 ||| (k - 64) <<< 8 = _
  rw [high]
  exact BitVec.zero_or

theorem modulusBounds_ok (s : State) (hk : 64 ≤ (s.gpr .ecx).toNat)
    (hk' : (s.gpr .ecx).toNat ≤ 1024) :
    WP isa (.block modulusBounds) s fun t =>
      t.gpr .ebx = (s.gpr .eax - 1) >>> 31 ∧
      t.gpr .ebp = ((((s.gpr .ecx - 64) <<< 8) + s.gpr .eax) - 128) >>> 31 ∧
      t.mem = s.mem ∧ Keeps [.ebx, .ebp] s t := by
  unfold modulusBounds
  refine wp_movS rfl fun s₁ u₁ _ => ?_
  refine wp_subS rfl fun s₂ u₂ _ => ?_
  refine wp_shr (by decide) fun s₃ u₃ _ => ?_
  refine wp_movS rfl fun s₄ u₄ _ => ?_
  refine wp_subS rfl fun s₅ u₅ _ => ?_
  refine wp_ror (by decide) fun s₆ u₆ => ?_
  refine wp_addS rfl fun s₇ u₇ _ => ?_
  refine wp_subS rfl fun s₈ u₈ _ => ?_
  refine wp_shr (by decide) fun t u₉ _ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [u₉.other .ebx (by decide), u₈.other .ebx (by decide), u₇.other .ebx (by decide),
      u₆.other .ebx (by decide), u₅.other .ebx (by decide), u₄.other .ebx (by decide),
      u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [u₉.gpr, u₈.gpr, u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr,
      u₃.other .ecx (by decide), u₂.other .ecx (by decide), u₁.other .ecx (by decide),
      u₆.other .eax (by decide), u₅.other .eax (by decide), u₄.other .eax (by decide),
      u₃.other .eax (by decide), u₂.other .eax (by decide), u₁.other .eax (by decide),
      rotate_threshold _ hk hk']
  · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · exact ((((((((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen
      u₄.keeps).widen u₅.keeps).widen u₆.keeps).widen u₇.keeps).widen u₈.keeps).widen u₉.keeps

end VG.Proof.Bignum.X86
