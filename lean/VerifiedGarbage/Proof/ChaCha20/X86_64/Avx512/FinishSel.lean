module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Finish
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.SymSel

/-!
# ChaCha20 on x86-64 with AVX-512: the sixteen blocks, from either buffer

`finishSel` is `finish` with each block of the input loaded by `selXor`:
each doubleword of the output is the input's (`T.inp`) XORed with the
keystream's (`finishSel_ok`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Spec.ChaCha20 (Word stateAt serialize)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx2 (plus)

def finishSelCheck : Bool :=
  match Sym.init.runPieces finishSel with
  | some σ => (List.range 256).all fun i => σ.mem 2 i == .xor (.inp i) (outT (i % 16) (i / 16))
  | none => false

theorem finishSelCheck_eq : finishSelCheck = true := by decide +kernel

theorem finishSel_run : ∃ σ, Sym.init.runPieces finishSel = some σ ∧
    ∀ i < 256, σ.mem 2 i = .xor (.inp i) (outT (i % 16) (i / 16)) := by
  have e := finishSelCheck_eq
  unfold finishSelCheck at e
  split at e
  · rename_i σ h
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at e
    exact ⟨σ, h, e⟩
  · cases e

/-- Byte `k` of the pass's input. -/
theorem inpW_byte (s : State) (k : Nat) :
    (inpW s (k / 4)).extractLsb' (8 * (k % 4)) 8 =
      if 64 * (k / 64) + 64 ≤ (s.gpr .r10).toNat then s.mem (s.gpr .r8 + BitVec.ofNat 64 k)
      else s.mem (s.gpr .rsi + BitVec.ofNat 64 k) := by
  simp only [inpW, show k / 4 / 16 = k / 64 by omega]
  split
  · rw [byte_dword s.mem (s.gpr .r8)]
  · rw [byte_dword s.mem (s.gpr .rsi)]

theorem finishSel_ok {s : State} (hc : Ctx s) (hs : SelOk s) (hi : Incs s.mem (s.gpr .rcx))
    {vs : Nat → CState} (hz : ZH vs s) :
    WP isa (pieces finishSel) s fun s' =>
      (∀ k < 1024, s'.mem (s.gpr .rsi + BitVec.ofNat 64 k) =
        (if 64 * (k / 64) + 64 ≤ (s.gpr .r10).toNat then s.mem (s.gpr .r8 + BitVec.ofNat 64 k)
          else s.mem (s.gpr .rsi + BitVec.ofNat 64 k)) ^^^
        (serialize (plus vs (stateAt s.mem (s.gpr .rdi)) (k / 64))).getD (k % 64) 0) ∧
      Frame (wregs s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨σ, hr, hm⟩ := finishSel_run
  refine WP.mono (runPieces_ok hc hs finishSel (SRel.init s) hr) fun s' h => ⟨fun k hk => ?_, h.frame, h.gpr,
    h.rd, h.wr⟩
  have d := h.mem 2 (k / 4) (by decide) (by simp only [bsize]; omega)
  rw [hm _ (by omega)] at d
  simp only [T.eval, regn, baseR] at d
  rw [show k / 4 % 16 = k % 64 / 4 by omega, show k / 4 / 16 = k / 64 by omega] at d
  rw [byte_dword s'.mem, d, BitVec.extractLsb'_xor, inpW_byte,
    serialize_getD _ (Nat.mod_lt _ (by decide)), outT_eval hz hi (by omega) (by omega),
    show k % 64 % 4 = k % 4 by omega]

end VG.Proof.ChaCha20.X86_64.Avx512
