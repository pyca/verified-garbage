module

public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Load
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.SetupP
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.LoopP
public import VerifiedGarbage.Impl.AesGcm.X86_64.Prepared
import Mathlib.Tactic.SplitIfs

/-! # Converting the cached powers in place at key setup -/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.Prepared
open VG VG.X86_64
open VG.Spec.Gcm (Block blockAt ctxH hpow PowersRepr PreparedPowersRepr)
open VG.Proof.Gcm.X86_64.Stitch (in_sub_int in_rdwr storesK_ok)
open VG.Proof.Gcm.X86_64.StitchZP (hInvF ones cvtPair_ok consts_ok vinsSelf_ok)
open VG.Proof.Gcm.X86_64.StitchZR (preparedPower_eq)
open VG.Impl.Gcm.X86_64.Pclmul (revMask xInv poly)
open VG.Impl.AesGcm.X86_64.Prepared (pair)
open VG.Proof.Gcm.X86_64.Pclmul (const_ok)

/-- One conversion changes only its 32 bytes and temporary vector registers. -/
theorem pair_ok (k : Nat) (s : State) {n : Nat}
    (hin : InRegions s.wr (s.gpr .rdi) n) (hw : (s.gpr .rdi).toNat + n ≤ 2 ^ 64) (hk : 256 + 32 * (k + 1) ≤ n)
    (m0 : ∀ l < 2, s.lane .xmm0 l = revMask)
    (c8 : ∀ l < 2, s.lane .xmm8 l = xInv) (c9 : ∀ l < 2, s.lane .xmm9 l = ones) :
    WP isa (.block (pair k)) s fun s' =>
      (∀ l < 2, s'.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (256+32*k+16*l)) 128 =
        hInvF (blockAt s.mem (s.gpr .rdi + BitVec.ofNat 64 (272+32*k-16*l)))) ∧
      Frame [⟨s.gpr .rdi + BitVec.ofNat 64 (256+32*k), 32⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .xmm7 → r ≠ .xmm10 → r ≠ .xmm12 → ∀ l < 2, s'.lane r l = s.lane r l) := by
  rw [pair, WP.block_append_iff]
  refine WP.mono (cvtPair_ok (2*k+1) .xmm12 (by decide) (by decide) (by decide) (by decide) s m0 c8 c9
    (in_sub_int (in_rdwr hin) (by omega)) (in_sub_int (in_rdwr hin) (by omega))) fun s₁ ⟨v0, v1, f₁⟩ => ?_
  refine WP.mono (storesK_ok .rdi [.xmm12] (8+k) s₁ (fun j hj => by
    rw [f₁.gpr, f₁.wr]; exact in_sub_int hin (by simp only [List.length_singleton] at hj; omega))
    (by rw [f₁.gpr]; simp only [List.length_singleton]; omega)) fun s' ⟨v, f, g, rd, wr, lanes⟩ => ?_
  rw [f₁.gpr, f₁.mem] at f
  have eo : 32*(8+k) = 256+32*k := by omega
  simp only [List.length_singleton, Nat.mul_one, eo] at f
  refine ⟨fun l hl => ?_, f, by rw [g, f₁.gpr], by rw [rd, f₁.rd], by rw [wr, f₁.wr],
    fun r h7 h10 h12 l hl => by rw [lanes, f₁.lane r (by simp [h7, h10, h12]) l hl]⟩
  have e := v 0 (by simp) l hl
  rw [f₁.gpr, Nat.add_zero, eo] at e
  rw [e]
  simp only [List.getElem_cons_zero]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · rw [v0, BitVec.ofInt_natCast, show 256+16*(2*k+1) = 272+32*k-16*0 by omega]
  · rw [v1, BitVec.ofInt_natCast, show 240+16*(2*k+1) = 272+32*k-16*1 by omega]

end VG.Proof.Gcm.X86_64.Prepared
