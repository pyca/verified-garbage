module

import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchR
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec
public import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The keystream of the blocks after the last group, eight at a time

`ks_ok`: `StitchR.ks j` encrypts the next eight counters, in both lanes of
`ymm3`–`ymm6` (`Vaes.ctrs_ok`, `Vaes.aesG_ok`), and stores their keystream to
`scratch + 32 j`, as `Stitch.batch_ok` does without the data.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchR

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Proof.Gcm.X86_64.Stitch (SPre nb nr kp pp cb ciph sch addr_eq aregs_ok in_sub_int storesK_ok)
open VG.Proof.Aes.X86_64.Vaes (ctrs_ok aesG_ok two YFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq st)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq)
open VG.Spec.Gcm (Block blockAt inc32)

theorem ks_ok {s₀ : State} (hp : SPre s₀) (j : Nat) (hj : 32 * j + 128 ≤ 1024) {c : Nat} {s : State}
    (hctr : ∀ l < 2, s.lane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀))
    (hmsk : ∀ l < 2, s.lane .xmm0 l = revMask) (hinc : ∀ l < 2, s.lane .xmm15 l = two)
    (hK : Keys (nr s₀) (sch s₀) s) (hrsi : s.gpr .rsi = s₀.gpr .rsi)
    (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr s₀))
    (h11 : s.gpr .r11 = pp s₀) (hwr : s.wr = s₀.wr) :
    WP isa (Impl.Gcm.X86_64.StitchR.ks j) s fun s' =>
      (∀ i < 8, blockAt s'.mem (pp s₀ + BitVec.ofNat 64 (32 * j + 16 * i)) =
        ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀))) ∧
      (∀ l < 2, s'.lane .xmm14 l = Nat.repeat inc32 (c + 8 + l) (cb s₀)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ≠ .xmm13 → x ≠ .xmm14 → x ∉ aregs → ∀ l < 2, s'.lane x l = s.lane x l) ∧
      Frame [⟨pp s₀ + BitVec.ofNat 64 (32 * j), 128⟩] s.mem s'.mem := by
  obtain ⟨hnd, h13, hx⟩ := aregs_ok
  have hwp := hp.wrap_p
  refine WP.seq (WP.mono (ctrs_ok .xmm14 .xmm0 .xmm15 (by decide) (by decide) aregs s (cb s₀) c hnd hx
    hctr hmsk hinc) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_)
  have hK₁ : Keys (nr s₀) (sch s₀) s₁ := YFrame.of_keys hK f₁
  refine WP.seq (WP.mono (aesG_ok .xmm13 aregs hnd h13 hp.rounds (fun _ => []) [] (fun _ h => absurd h List.not_mem_nil)
    (fun _ _ => True) (fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, YFrame.refl _ _⟩) (fun _ _ _ _ _ => trivial) s₁ hK₁
    trivial (by rw [f₁.gpr, hrsi]; simp) (by rw [f₁.gpr, hr10])) fun s₂ ⟨e₂, _, f₂⟩ => ?_)
  have ks : ∀ k (h : k < aregs.length), ∀ l < 2, XBinOp.eval .pshufb (s₂.lane aregs[k] l) revMask =
      ciph s₀ (Nat.repeat inc32 (c + 2 * k + l) (cb s₀)) := fun k h l hl =>
    (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) l hl, e₁ k h l hl])).symm
  have h11₂ : s₂.gpr .r11 = pp s₀ := by rw [f₂.gpr, f₁.gpr, h11]
  have hwr₂ : s₂.wr = s₀.wr := by rw [f₂.wr, f₁.wr, hwr]
  refine WP.mono (storesK_ok .r11 aregs j s₂ (fun k hk => by
      rw [hwr₂, h11₂]; exact in_sub_int hp.p_in (by simp [aregs] at hk; omega))
    (by rw [h11₂]; simp [aregs]; omega)) fun s₃ ⟨sv, fr, g₃, rd₃, wr₃, l₃⟩ => ?_
  rw [h11₂, show 32 * aregs.length = 128 from rfl] at fr
  rw [h11₂] at sv
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂] at fr
  refine ⟨fun i hi => ?_, fun l hl => ?_, by rw [g₃, f₂.gpr, f₁.gpr], by rw [rd₃, f₂.rd, f₁.rd],
    by rw [wr₃, f₂.wr, f₁.wr], fun x h13' h14 hr l hl => ?_, fr⟩
  · have hk : i / 2 < aregs.length := by simp [aregs]; omega
    have := sv (i / 2) hk (i % 2) (by omega)
    rw [show 32 * (j + i / 2) + 16 * (i % 2) = 32 * j + 16 * i by omega] at this
    rw [blockAt_eq, this, ks (i / 2) hk (i % 2) (by omega), show c + 2 * (i / 2) + i % 2 = c + i by omega]
  · rw [l₃, f₂.lane _ (by simp [aregs]) l hl, c₁ l hl]; simp [aregs]
  · rw [l₃, f₂.lane _ (by simp [h13', hr]) l hl, f₁.lane _ (by simp [h14, hr]) l hl]

end VG.Proof.Gcm.X86_64.StitchR
