module

import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnXVerified
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnXVerified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Mont.X86_64.Blocks
meta import VerifiedGarbage.Proof.Mont.X86_64.CsubS
meta import VerifiedGarbage.Proof.Mont.X86_64.Friendly
meta import VerifiedGarbage.Proof.Mont.X86_64.Ops
meta import VerifiedGarbage.Proof.Mont.X86_64.Round
meta import VerifiedGarbage.Proof.Mont.X86_64.Sparse
meta import VerifiedGarbage.Proof.Mont.X86_64.SparseX
meta import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Proof.Mont.X86_64.WideOps
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnB
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnN
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd

/-! # Shared BrainpoolP512r1 Montgomery multiplication on x86-64 -/

@[expose] public section
namespace VG.Proof.Weierstrass.X86_64.Mont.Wide8

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64.Mont
open VG.Impl.Weierstrass.X86_64.Mont.Wide8 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Impl.Weierstrass.Mont (numAt Keeps Modulus)

theorem fn8_x64 (M : Modulus) (hk : M.k = 8) (hR : M.R = (2 ^ 64) ^ 8) {code : Prog isa}
    (hmx : code.allInstrs (fun i => !loadsMxcsr i) = true)
    (hok : ∀ {s : State} {base : Addr} {Z : Nat}, Scr s base Z → 4096 ≤ Z →
      argOf s .rsi + 64 ≤ 3584 → argOf s .rdx + 64 ≤ 3584 → argOf s .rcx + 64 ≤ 3584 →
      wordsVal s.mem base (argOf s .rcx) 8 < M.m →
      WP isa code s fun s' =>
        wordsVal s'.mem base (argOf s .rsi) 8 < M.m ∧
        wordsVal s'.mem base (argOf s .rsi) 8 * (2 ^ 64) ^ 8 % M.m =
          wordsVal s.mem base (argOf s .rdx) 8 * wordsVal s.mem base (argOf s .rcx) 8 % M.m ∧
        KeepRegs fnClob s s' ∧
        ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 64 ≤ ofs base x) →
          (ofs base x < tmp ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x)
    (s : State) (hs : (mulX64 M).pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (mulX64 M).post s s' := by
  obtain ⟨⟨hrd, hwr, hret, hnw, ho, ha, hb⟩, hB⟩ := hs
  have hscr : Scr s (s.gpr .rdi) 8192 := ⟨rfl, by rw [hwr]; simp, hnw⟩
  simp only [Impl.Weierstrass.Mont.Fits, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes,
    hk] at ho ha hb
  suffices hwp : WP isa code s fun s' => gprPreserved s s' ∧ (mulX64 M).post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
  simp only [argNum, numAt_eq, hk] at hB
  refine WP.mono (hok hscr (by decide) ho ha hb hB) fun s' ⟨hlt, heq, k, hmem⟩ => ?_
  refine ⟨⟨fun r hr => k.gpr r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ?_⟩,
    by simp only [argNum, numAt_eq, hk]; exact hlt, by simp only [argNum, numAt_eq, hk, hR]; exact heq, ?_⟩
  · refine Mem.readW_congr fun i hi => hmem _ (Or.inr ?_) (Or.inr ?_) <;>
    · have hx := hret (s.gpr .rsp + BitVec.ofNat 64 i) (by
        simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
      simp only [Region.Contains, Nat.not_le] at hx
      simp only [ofs, argOf]; omega
  · intro i hi hown ho'
    have e1 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
    have e2 : Impl.Weierstrass.Mont.ownAt M.k = 3584 := by rw [hk]; rfl
    have e3 : tmp = 4032 := rfl
    rw [e1] at hi
    rw [e2] at hown
    rw [hk] at ho'
    have h64 : i < 2 ^ 64 := by omega
    refine hmem _ ?_ ?_
    · rw [ofs_off0 _ h64]; exact ho'
    · rw [ofs_off0 _ h64, e3]; omega


def curve (order : Bool) : Modulus :=
  if order then Impl.Weierstrass.Mont.brainpoolp512r1n else Impl.Weierstrass.Mont.brainpoolp512r1p

theorem curve_k (order : Bool) : (curve order).k = 8 := by cases order <;> rfl

theorem curve_m (order : Bool) : (curve order).m = modulus order := by cases order <;> rfl

theorem curve_R (order : Bool) : (curve order).R = (2 ^ 64) ^ 8 := by
  exact (Nat.pow_mul 2 64 (curve order).k).trans
    (congrArg (HPow.hPow (2 ^ 64)) (curve_k order))

theorem fn_x64 (order : Bool) : ∀ s, (mulX64 (curve order)).pre s →
    ∃ t s', Exec isa (fn order) s t s' ∧ abiPreserved s s' ∧ (mulX64 (curve order)).post s s' :=
  fn8_x64 (curve order) (curve_k order) (curve_R order) (by cases order <;> decide +kernel)
    fun hs hZ ho ha hb hB => by
      rw [curve_m] at hB ⊢
      exact WP.mono (fn_ok order hs hZ ho ha hb hB) fun _ h => h

theorem fn_ct (order : Bool) : ConstantTime isa (mulX64 (curve order)).pre
    (mulX64 (curve order)).pub (fn order) := by
  cases order <;> exact ct_zext (M := curve _) (fun _ h => h.1)
    (VG.Taint.constantTime (A := X86_64.taint) τ₁ (fun _ _ _ _ h => h)
      (by taint_decide))

theorem verified (order : Bool) : Verified X86_64.target (fn order) ((curve order).mulContract X86_64.abi) :=
  Verified.of_correct (fn_x64 order) (fn_ct order)
    (mul_implies (curve order) (by rw [curve_k]; decide) (by cases order <;> decide +kernel))

end VG.Proof.Weierstrass.X86_64.Mont.Wide8
