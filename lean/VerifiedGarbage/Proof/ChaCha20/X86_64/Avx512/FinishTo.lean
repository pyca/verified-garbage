import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Finish
import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512To

/-!
# ChaCha20 on x86-64 with AVX-512: the sixteen blocks, out of place

`finishTo` is `finish` loading the input from `r8` (region 3 of `Sym`),
which it never writes: each doubleword of the output is the one of the input
XORed with the keystream's (`finishTo_ok`).
-/

namespace VG.Proof.ChaCha20.X86_64.Avx512

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Spec.ChaCha20 (Word stateAt serialize)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx2 (plus)

def finishToCheck : Bool :=
  match Sym.initSrc.run finishTo with
  | some σ => (List.range 256).all fun i => σ.mem 2 i == .xor (.mem 3 i) (outT (i % 16) (i / 16))
  | none => false

theorem finishToCheck_eq : finishToCheck = true := by decide +kernel

theorem finishTo_run : ∃ σ, Sym.initSrc.run finishTo = some σ ∧
    ∀ i < 256, σ.mem 2 i = .xor (.mem 3 i) (outT (i % 16) (i / 16)) := by
  have e := finishToCheck_eq
  unfold finishToCheck at e
  split at e
  · rename_i σ h
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at e
    exact ⟨σ, h, e⟩
  · cases e

theorem finishTo_ok {s : State} (hc : Ctx s) (hs : SrcOk s) (hi : Incs s.mem (s.gpr .rcx)) {vs : Nat → CState}
    (hz : ZH vs s) :
    WP isa (.block finishTo) s fun s' =>
      (∀ k < 1024, s'.mem (s.gpr .rsi + BitVec.ofNat 64 k) = s.mem (s.gpr .r8 + BitVec.ofNat 64 k) ^^^
        (serialize (plus vs (stateAt s.mem (s.gpr .rdi)) (k / 64))).getD (k % 64) 0) ∧
      Frame (wregs s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨σ, hr, hm⟩ := finishTo_run
  refine WP.mono (srun_ok hc finishTo (SRel.initSrc hs) hr) fun s' h => ⟨fun k hk => ?_, h.frame, h.gpr,
    h.rd, h.wr⟩
  have d := h.mem 2 (k / 4) (by decide) (by simp only [bsize]; omega)
  rw [hm _ (by omega)] at d
  simp only [T.eval, regn, baseR] at d
  rw [show k / 4 % 16 = k % 64 / 4 by omega, show k / 4 / 16 = k / 64 by omega] at d
  rw [byte_dword s'.mem, byte_dword s.mem, d, BitVec.extractLsb'_xor,
    serialize_getD _ (Nat.mod_lt _ (by decide)), outT_eval hz hi (by omega) (by omega),
    show k % 64 % 4 = k % 4 by omega]

end VG.Proof.ChaCha20.X86_64.Avx512
