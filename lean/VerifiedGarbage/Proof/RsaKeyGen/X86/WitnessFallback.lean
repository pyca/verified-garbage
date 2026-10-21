module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessFallback
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFallbackWord
import VerifiedGarbage.Proof.RsaKeyGen.WitnessBits32
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Native fallback produces exactly the reviewed forced witness -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessFallback
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessFallback

theorem code_ok {s : State} {base : Addr} {size w src : Nat} (scratch : Scr s base size)
    (positive : 0 < w) (fit : src + 8 * w ≤ size) {uniform : Bool} (mask : s.gpr .eax = cmask uniform) :
    WP isa (.block (code w src)) s fun t =>
      val32 t.mem base src (2 * w) =
        (if uniform then val32 s.mem base src (2 * w) else (val32 s.mem base src (2 * w) ||| 2) % 2 ^ (64 * w - 1)) ∧
      Outside base src (8 * w) s.mem t.mem ∧ Keeps [.ecx] s t := by
  unfold code
  refine WP.block_append (WP.mono (low_ok (uniform := uniform) scratch (by omega) mask) fun a ⟨low, Oa, Ka⟩ => ?_)
  refine WP.mono (high_ok (uniform := uniform) (scratch.of_keeps Ka (by decide)) (by omega)
    (by rw [Ka.1 .eax (by decide)]; exact mask)) fun t ⟨top, Ot, Kt⟩ => ?_
  have lowSame : w32 t.mem base src = w32 a.mem base src := Ot.w32 (by omega) (by have := scratch.nowrap; omega)
  have topSame : w32 a.mem base (src + 8 * w - 4) = w32 s.mem base (src + 8 * w - 4) :=
    Oa.w32 (by omega) (by have := scratch.nowrap; omega)
  refine ⟨?_, (Oa.mono (by omega) (by omega)).trans (Ot.mono (by omega) (by omega)), Ka.trans Kt⟩
  cases uniform
  · simp at low top
    change val32 t.mem base src (2 * w) = (val32 s.mem base src (2 * w) ||| 2) % 2 ^ (64 * w - 1)
    rw [show 64 * w - 1 = 32 * (2 * w) - 1 by omega]
    apply VG.Proof.RsaKeyGen.val32_witness_fallback (by omega)
    · rw [lowSame, low]
    · rw [show src + 4 * (2 * w - 1) = src + 8 * w - 4 by omega, top, topSame]
    · intro j first last
      exact (Ot.w32 (by omega) (by have := scratch.nowrap; omega)).trans
        (Oa.w32 (by omega) (by have := scratch.nowrap; omega))
  · simp at low top
    change val32 t.mem base src (2 * w) = val32 s.mem base src (2 * w)
    apply val32_congr
    intro j hj
    by_cases first : j = 0
    · subst j
      simpa only [Nat.mul_zero, Nat.add_zero] using lowSame.trans low
    · by_cases last : j = 2 * w - 1
      · subst j
        rw [show src + 4 * (2 * w - 1) = src + 8 * w - 4 by omega]
        exact top.trans topSame
      · exact (Ot.w32 (by omega) (by have := scratch.nowrap; omega)).trans
          (Oa.w32 (by omega) (by have := scratch.nowrap; omega))

end VG.Proof.RsaKeyGen.X86.WitnessFallback
