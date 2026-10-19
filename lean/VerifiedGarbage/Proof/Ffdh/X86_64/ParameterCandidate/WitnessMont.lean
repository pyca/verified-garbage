module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Math

/-! # FFDH parameter candidates on x86-64: prepare a witness for the shared round -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem witnessMont_ok (M : Mont) {s : State} {B : Addr} {Z w N a : Nat} {mi : BitVec 64}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w) (ho : N % 2 = 1) (hN : 1 < N)
    (ha : wv s.mem B (slot w aXm) w = a) :
    WP isa (M.mm aXm aXm aR2) s fun t =>
      ModulusReady t B Z w mi N ∧ wv t.mem B (slot w aXm) w = a % N * 2 ^ (64 * w) % N ∧
      Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))] s.mem t.mem ∧
      Keep mmRegs s t := by
  have hw : w < 2 ^ 31 := by have := hd.w128; omega
  have hR : Nat.Coprime (2 ^ (64 * w)) N := coprime_pow2 ho _
  refine WP.mono (M.mm_ok h.good hd.z (by have := hd.w4; omega) hw
    (o := aXm) (a := aXm) (b := aR2) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) h.inv
    (by rw [h.r2, h.n]; exact Nat.mod_lt _ (by omega))) fun t ⟨hg, hlt, hv, hs, k⟩ => ?_
  have hf : Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))] s.mem t.mem :=
    Frm.of_arrays hs (by simp)
  rw [h.n] at hlt hv
  rw [ha, h.r2] at hv
  refine ⟨h.of_frm hd hf k hg.rdi (by rng_disj) (by rng_disj) (by rng_disj), ?_, hf, k⟩
  rw [← Nat.mod_eq_of_lt hlt, Nat.mod_mul_mod]
  refine mont_cancel hR ?_
  rw [hv, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]

end VG.Proof.Ffdh.X86_64.ParameterCandidate
