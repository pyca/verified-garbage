module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Impl.RsaKeyGen.X86.FastR2
public import VerifiedGarbage.Proof.Mont.X86.PowerStep

import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.WordConst
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Mont.X86.PowerLoop
import VerifiedGarbage.Proof.Mont.X86.Instr
/-! # Short doubling leaves the prepared multiplier's modulus and caller intact -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/FastR2Seed.lean`, which only this module imported.
section

/-! # A power of two at most the odd modulus is a reduced residue: the top bit for a full-width candidate -/

section
namespace VG.Proof.RsaKeyGen.X86.FastR2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.FastR2

theorem seedAt_lt {e m : Nat} (positive : 1 ≤ e) (odd : m % 2 = 1) (top : 2 ^ e ≤ m) : 2 ^ e < m := by
  have even : 2 ^ e % 2 = 0 := by
    rw [show e = (e - 1) + 1 by omega, Nat.pow_succ, Nat.mul_mod_left]
  omega

theorem seed_lt {n m : Nat} (positive : 0 < n) (odd : m % 2 = 1)
    (top : 2 ^ (64 * n - 1) ≤ m) : 2 ^ (64 * n - 1) < m :=
  seedAt_lt (by omega) odd top

theorem seedAt_ok {s : State} {base : Addr} {size n e out : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (below : e < 64 * n) (fit : out + 8 * n ≤ size) :
    WP isa (seedAt n e out) s fun t => wordsVal t.mem base out n = 2 ^ e ∧
      Outside base out (8 * n) s.mem t.mem ∧ Keeps [.eax, .ebp, .edx] s t := by
  refine WP.mono (VG.Proof.Mont.X86.setConstW_ok scratch (by omega) (by omega)
    (show 2 ^ e < 2 ^ (32 * (2 * n)) from
      Nat.pow_lt_pow_right (by decide) (by omega))) fun t ⟨value, K, O⟩ => ?_
  exact ⟨by rw [wordsVal_eq_val32]; exact value, by simpa only [show 4 * (2 * n) = 8 * n by omega] using O, K⟩

theorem seed_ok {s : State} {base : Addr} {size n out : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (fit : out + 8 * n ≤ size) :
    WP isa (seed n out) s fun t => wordsVal t.mem base out n = 2 ^ (64 * n - 1) ∧
      Outside base out (8 * n) s.mem t.mem ∧ Keeps [.eax, .ebp, .edx] s t :=
  seedAt_ok scratch positive (by omega) fit

end VG.Proof.RsaKeyGen.X86.FastR2
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/FastR2Doubles.lean`, which only this module imported.
section

/-! # The short doubling phase computes 2^n R modulo the candidate -/

section
namespace VG.Proof.RsaKeyGen.X86.FastR2
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont VG.Impl.RsaKeyGen.X86.FastR2

theorem doublesAt_ok {s : State} {base : Addr} {size m e acc out : Nat} {M : Mod}
    (scratch : Scr s base size) (modulus : Modulus M size m s.mem base)
    (layout : OpLay M size acc out out out)
    (apart : out + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ out)
    (bound : M.n ≤ 64) (odd : m % 2 = 1) (positive : 1 ≤ e) (below : e < 64 * M.n) (top : 2 ^ e ≤ m) :
    WP isa (doublesAt M e acc out) s fun t =>
      wordsVal t.mem base out M.n = 2 ^ M.n * 2 ^ (64 * M.n) % m ∧
      Modulus M size m t.mem base ∧
      Outs base [(out, 8 * M.n), (M.tmp, 8 * M.n), (acc, accLen M)] s.mem t.mem ∧
      Keeps powerClob s t := by
  refine WP.seq (WP.mono (seedAt_ok scratch modulus.n0 below layout.o_le) fun a ⟨Va, Oa, Ka⟩ => ?_)
  refine WP.seq (wp_movS rfl fun b B _ => WP.block_nil ?_)
  have Kb : Keeps powerClob s b := (Ka.mono (by decide)).widen B.keeps
  have Mb : Modulus M size m b.mem base := by
    refine ⟨modulus.n0, modulus.mo, modulus.tmp, modulus.sep, ?_⟩
    rw [B.mem, wordsVal_eq_val32,
      Oa.val32 (by omega) (by have := scratch.nowrap; have := modulus.mo; omega), ← wordsVal_eq_val32]
    exact modulus.val
  refine WP.mono (doubleLoop_ok (scratch.of_keeps Kb (by decide)) Mb layout apart
    (by rw [B.mem, Va]; exact seedAt_lt positive odd top) (by omega) (by omega) B.gpr)
    fun t T => ?_
  refine ⟨?_, T.modulus, ?_, Kb.trans T.keeps⟩
  · rw [T.value, B.mem, Va, ← Nat.pow_add, ← Nat.pow_add]
    have npos := modulus.n0
    rw [show M.n + 64 * M.n - e + e = M.n + 64 * M.n by omega]
  · have Oab : Outside base out (8 * M.n) s.mem b.mem := B.mem ▸ Oa
    exact (Outs.of_outside Oab (List.mem_cons_self ..)).trans T.mem

theorem doubles_ok {s : State} {base : Addr} {size m acc out : Nat} {M : Mod}
    (scratch : Scr s base size) (modulus : Modulus M size m s.mem base)
    (layout : OpLay M size acc out out out)
    (apart : out + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ out)
    (bound : M.n ≤ 64) (odd : m % 2 = 1) (top : 2 ^ (64 * M.n - 1) ≤ m) :
    WP isa (doubles M acc out) s fun t =>
      wordsVal t.mem base out M.n = 2 ^ M.n * 2 ^ (64 * M.n) % m ∧
      Modulus M size m t.mem base ∧
      Outs base [(out, 8 * M.n), (M.tmp, 8 * M.n), (acc, accLen M)] s.mem t.mem ∧
      Keeps powerClob s t :=
  doublesAt_ok scratch modulus layout apart bound odd (by have := modulus.n0; omega)
    (by have := modulus.n0; omega) top

end VG.Proof.RsaKeyGen.X86.FastR2
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PreparedR2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem doublesAt_ready {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) (bound : g.w ≤ 64) (odd : c % 2 = 1)
    {e : Nat} (positive : 1 ≤ e) (eLt : e < 64 * g.w) (top : 2 ^ e ≤ c) :
    WP isa (VG.Impl.RsaKeyGen.X86.FastR2.doublesAt (modulus g.w) e (g.array 2) (g.array 6)) s fun t =>
      Ready g c capacity p t ∧
      val32 t.mem g.W (g.array 6) g.words = 2 ^ g.w * 2 ^ (64 * g.w) % c ∧
      Outs g.W (phaseRanges g) s.mem t.mem ∧ Keeps VG.Proof.Mont.X86.Dynamic.powerClob s t := by
  have apart := g.arrayBefore (i := 0) (j := 6) (by decide)
  have apart' : g.array 6 + 8 * g.w ≤ (modulus g.w).mo ∨
      (modulus g.w).mo + 8 * g.w ≤ g.array 6 := by
    right
    change slot g.w 0 + 8 * g.w ≤ g.array 6
    rw [Prepared.slot_eq]
    unfold Geometry.words at apart
    omega
  refine WP.mono (FastR2.doublesAt_ok S.scratch (Prepared.dynamicModulus v S.modulus)
    (Prepared.layout v) apart' bound odd positive eLt top) fun t ⟨value, _, O, K⟩ => ?_
  change Outs g.W [(g.array 6, 8 * g.w), ((modulus g.w).tmp, 8 * g.w),
    (g.array 2, accLen (modulus g.w))] s.mem t.mem at O
  change Outs g.W [(g.array 6, 8 * g.w), (slot g.w 1, 8 * g.w),
    (g.array 2, accLen (modulus g.w))] s.mem t.mem at O
  rw [Prepared.slot_eq] at O
  have F := WorkspaceFrame.of_outs S.scratch.nowrap O
  refine ⟨⟨Prepared.keepRanges v S.context K (by decide) O (fun _ mem => phase_header g mem),
    S.modulus.keep v F (fun r mem => Or.inl (by have := phase_header g mem; omega))
      (fun r mem => Or.inl (phase_candidate g mem)),
    S.caller.keepOuts K (by decide) O (fun r mem => phase_fits v mem),
    S.scratch.of_keeps K (by decide)⟩, ?_, O, K⟩
  unfold Geometry.words
  rw [← wordsVal_eq_val32]
  exact value

theorem doubles_ready {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) (bound : g.w ≤ 64) (odd : c % 2 = 1)
    (top : 2 ^ (64 * g.w - 1) ≤ c) :
    WP isa (VG.Impl.RsaKeyGen.X86.FastR2.doubles (modulus g.w) (g.array 2) (g.array 6)) s fun t =>
      Ready g c capacity p t ∧
      val32 t.mem g.W (g.array 6) g.words = 2 ^ g.w * 2 ^ (64 * g.w) % c ∧
      Outs g.W (phaseRanges g) s.mem t.mem ∧ Keeps VG.Proof.Mont.X86.Dynamic.powerClob s t :=
  doublesAt_ready v S bound odd (e := 64 * g.w - 1) (by have := v.minWidth; omega) (by have := v.minWidth; omega) top

end VG.Proof.RsaKeyGen.X86.PreparedR2
