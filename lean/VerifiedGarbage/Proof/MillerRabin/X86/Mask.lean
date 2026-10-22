module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageMemory
public import VerifiedGarbage.Proof.MillerRabin.Math
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
public import VerifiedGarbage.Proof.Mont.X86.WordOps

/-! # The selection mask reuses the existing four-bit equality proof -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Mont.X86 VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem mask_ok {σ s : State} {base : Addr} {bytes w d j : Nat}
    (h : Stage base bytes w σ s) (hf : arrAt w 28 ≤ bytes) (hd : d < 16) (hj : j < 16)
    (digit : s.mem.readW (off base sV) 32 >>> 28 = BitVec.ofNat 32 d) :
    WP isa (.block (maskJ j)) s fun t =>
      t.gpr .esi = cmask (decide (d = j)) ∧ Stage base bytes w σ t ∧
      t.mem = s.mem ∧ Keeps [.eax, .esi] s t := by
  have fit : sV + 4 ≤ bytes := Nat.le_trans (by decide : 216 ≤ 256) (Nat.le_trans (Nat.le_add_right _ _) hf)
  unfold maskJ
  refine wp_movS (readSrc_sc h.context.ws fit) fun s₁ U₁ _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₂ U₂ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₃ U₃ => wp_subS rfl fun s₄ U₄ _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₅ U₅ => ?_
  refine wp_movS rfl fun s₆ U₆ _ => wp_subS rfl fun t U₇ _ => WP.block_nil ?_
  have K : Keeps [.eax, .esi] s t :=
    ((((((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans
      (U₃.keeps.mono (by decide))).trans (U₄.keeps.mono (by decide))).trans
      (U₅.keeps.mono (by decide))).trans (U₆.keeps.mono (by decide))).trans
      (U₇.keeps.mono (by decide))
  have mem : t.mem = s.mem := by rw [U₇.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  refine ⟨?_, h.of_registers K mem, mem, K⟩
  have bit : s₅.gpr .eax = BitVec.ofNat 32 (decide (d = j)).toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [U₅.gpr, U₄.gpr, U₃.gpr, U₂.gpr, U₁.gpr, digit]
    simp only [ite_eq_right (by decide : AluOp.xor ≠ AluOp.and)]
    rw [VG.Proof.MillerRabin.Math.mask_eq d hd j hj, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by cases decide (d = j) <;> decide)).symm
  rw [U₇.gpr, U₆.gpr, U₆.other .eax (by decide), bit]
  cases decide (d = j) <;> rfl

end VG.Proof.MillerRabin.X86
