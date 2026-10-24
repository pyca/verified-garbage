module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessFallback
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFallbackWord
import VerifiedGarbage.Proof.RsaKeyGen.WitnessBits32

/-! # Native fallback produces exactly the reviewed forced witness -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessFallback
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessFallback

theorem codeAt_ok {s : State} {base : Addr} {size k src : Nat} (scratch : Scr s base size)
    (positive : 2 ≤ k) (fit : src + 4 * k ≤ size) {uniform : Bool} (mask : s.gpr .eax = cmask uniform) :
    WP isa (.block (codeAt k src)) s fun t =>
      val32 t.mem base src k =
        (if uniform then val32 s.mem base src k else (val32 s.mem base src k ||| 2) % 2 ^ (32 * k - 1)) ∧
      Outside base src (4 * k) s.mem t.mem ∧ Keeps [.ecx] s t := by
  unfold codeAt
  refine WP.block_append (WP.mono (low_ok (uniform := uniform) scratch (by omega) mask) fun a ⟨low, Oa, Ka⟩ => ?_)
  refine WP.mono (high_ok (uniform := uniform) (scratch.of_keeps Ka (by decide)) (by omega)
    (by rw [Ka.1 .eax (by decide)]; exact mask)) fun t ⟨top, Ot, Kt⟩ => ?_
  have lowSame : w32 t.mem base src = w32 a.mem base src := Ot.w32 (by omega) (by have := scratch.nowrap; omega)
  have topSame : w32 a.mem base (src + 4 * k - 4) = w32 s.mem base (src + 4 * k - 4) :=
    Oa.w32 (by omega) (by have := scratch.nowrap; omega)
  refine ⟨?_, (Oa.mono (by omega) (by omega)).trans (Ot.mono (by omega) (by omega)), Ka.trans Kt⟩
  cases uniform
  · simp at low top
    change val32 t.mem base src k = (val32 s.mem base src k ||| 2) % 2 ^ (32 * k - 1)
    apply VG.Proof.RsaKeyGen.val32_witness_fallback (by omega)
    · rw [lowSame, low]
    · rw [show src + 4 * (k - 1) = src + 4 * k - 4 by omega, top, topSame]
    · intro j first last
      exact (Ot.w32 (by omega) (by have := scratch.nowrap; omega)).trans
        (Oa.w32 (by omega) (by have := scratch.nowrap; omega))
  · simp at low top
    change val32 t.mem base src k = val32 s.mem base src k
    apply val32_congr
    intro j hj
    by_cases first : j = 0
    · subst j
      simpa only [Nat.mul_zero, Nat.add_zero] using lowSame.trans low
    · by_cases last : j = k - 1
      · subst j
        rw [show src + 4 * (k - 1) = src + 4 * k - 4 by omega]
        exact top.trans topSame
      · exact (Ot.w32 (by omega) (by have := scratch.nowrap; omega)).trans
          (Oa.w32 (by omega) (by have := scratch.nowrap; omega))

theorem code_ok {s : State} {base : Addr} {size w src : Nat} (scratch : Scr s base size)
    (positive : 0 < w) (fit : src + 8 * w ≤ size) {uniform : Bool} (mask : s.gpr .eax = cmask uniform) :
    WP isa (.block (code w src)) s fun t =>
      val32 t.mem base src (2 * w) =
        (if uniform then val32 s.mem base src (2 * w) else (val32 s.mem base src (2 * w) ||| 2) % 2 ^ (64 * w - 1)) ∧
      Outside base src (8 * w) s.mem t.mem ∧ Keeps [.ecx] s t := by
  have h := codeAt_ok (k := 2 * w) (src := src) scratch (by omega) (by omega) mask
  rw [show 32 * (2 * w) - 1 = 64 * w - 1 by omega, show 4 * (2 * w) = 8 * w by omega] at h
  exact h

end VG.Proof.RsaKeyGen.X86.WitnessFallback
