module

public import VerifiedGarbage.Proof.MlKem.AArch64.Shared
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
import VerifiedGarbage.Proof.Framework.Range

/-! # Copying `n` words through `x9` (`Kem16.copyN`), as `KeyGen.copy_ok` copies 32 bytes -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.Sha3 (bytesAt)

/-- The `n` words at `S + so` copied to `D + dO`, through `x9`. -/
theorem copyN_ok {n : Nat} {S D : Addr} {sb db : Reg} {so dO : Nat} (hn : 8 * n < 2 ^ 64) (hs9 : sb ≠ .x9) (hd9 : db ≠ .x9)
    (hso : so % 8 = 0 ∧ so + 8 * n ≤ 32768) (hdo : dO % 8 = 0 ∧ dO + 8 * n ≤ 32768)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, 8 * n⟩ ⟨D + BitVec.ofNat 64 dO, 8 * n⟩)
    {s : State} (hS : s.gpr sb = S) (hD : s.gpr db = D)
    (hin : Covers [⟨S + BitVec.ofNat 64 so, 8 * n⟩] (s.rd ++ s.wr))
    (hout : Covers [⟨D + BitVec.ofNat 64 dO, 8 * n⟩] s.wr) :
    WP isa (.block (Impl.MlKem.AArch64.Kem16.copyN n sb so db dO)) s fun s' => Keep [.x9] s s' ∧
      Frame [⟨D + BitVec.ofNat 64 dO, 8 * n⟩] s.mem s'.mem ∧
      bytesAt s'.mem (D + BitVec.ofNat 64 dO) (8 * n) = bytesAt s.mem (S + BitVec.ofNat 64 so) (8 * n) := by
  have n9s : sb ∉ [Reg.x9] := by simpa using hs9
  have n9d : db ∉ [Reg.x9] := by simpa using hd9
  refine WP.mono (wp_range_flatMap (M := isa) (N := n) (fun k (s' : State) => Keep [.x9] s s' ∧
      Frame [⟨D + BitVec.ofNat 64 dO, 8 * n⟩] s.mem s'.mem ∧
      ∀ i < 8 * k, s'.mem (D + BitVec.ofNat 64 (dO + i)) = s.mem (S + BitVec.ofNat 64 (so + i)))
    (fun k s₁ hk ⟨k₁, f₁, b₁⟩ => ?_) n (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩) fun s' ⟨k', f', b'⟩ =>
      ⟨k', f', ?_⟩
  · refine wp_ldrx (a := S + BitVec.ofNat 64 (so + 8 * k)) ⟨by omega, by omega⟩ (by rw [k₁.get sb n9s, hS])
      (by rw [k₁.rd, k₁.wr]; exact in_R (A := fun _ => S) (b := 0) hin (k := 8 * k) (by omega) hn)
      fun s₂ h₂ e₂ => wp_strx (a := D + BitVec.ofNat 64 (dO + 8 * k)) ⟨by omega, by omega⟩
      (by rw [h₂.get db n9d, k₁.get db n9d, hD])
      (by rw [h₂.wr, k₁.wr]; exact in_R (A := fun _ => D) (b := 0) hout (k := 8 * k) (by omega) hn)
      fun s₃ h₃ => wp_nil ?_
    have m₃ : s₃.mem = s₁.mem.writeW (D + BitVec.ofNat 64 (dO + 8 * k))
        (s₁.mem.readW (S + BitVec.ofNat 64 (so + 8 * k)) 64) := by
      rw [h₃.mem, e₂, h₂.mem]
    refine ⟨((k₁.trans h₂.keep).trans h₃.keep).mono, ?_, fun i hi => ?_⟩
    · rw [m₃]
      exact f₁.writeW (List.mem_singleton_self _) _ (by
        rw [← ptr_add]; exact contains_off (by omega) hn)
    · rw [m₃]
      rcases (by omega : i < 8 * k ∨ 8 * k ≤ i) with hi' | hi'
      · rw [writeW64_off _ _ _ _ (sep_off D (a := dO + i) (n := 1) (b := dO + 8 * k) (k := 8) (by omega)
          (by omega) (by omega) _ (by rw [BitVec.sub_self]; decide))]
        exact b₁ i hi'
      · rw [show D + BitVec.ofNat 64 (dO + i) = D + BitVec.ofNat 64 (dO + 8 * k) + BitVec.ofNat 64 (i - 8 * k) by
          rw [ptr_add, show dO + 8 * k + (i - 8 * k) = dO + i by omega], writeW64_byte _ _ _ (by omega),
          readW64_byte _ _ (by omega), ptr_add, show so + 8 * k + (i - 8 * k) = so + i by omega]
        refine f₁ _ fun r hr hc => ?_
        rw [List.mem_singleton.mp hr] at hc
        exact hsep _ (R.contains (A := fun _ => S) (b := 0) (k := i) (n := 1) (by omega) hn) hc
  · refine List.ext_getElem (by simp only [bytesAt_length]) fun i h₁ _ => ?_
    rw [bytesAt_length] at h₁
    rw [bytesAt_getElem, bytesAt_getElem, ptr_add, ptr_add]
    exact b' i (by omega)


end VG.Proof.MlKem.AArch64.KeyGen
