module

public import VerifiedGarbage.Spec.RsaPkcs1Enc.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc.Pc

open VG VG.AArch64

/-- `pre`, the only buffer `vg_rsa_pkcs1_encrypt_precomputed` reads beyond
`vg_rsa_pkcs1_encrypt`'s. -/
def preX (s : State) : List Region := [⟨stackArg s 4, (stackArg s 5).toNat * 8⟩]

/-- The layout of a call of `vg_rsa_pkcs1_encrypt_precomputed` from `s`: 48
bytes of stack arguments. -/
abbrev layP (P : Nat) (s : State) : Lay := lay P s (preX s) 48

/-- The shared contract's precondition, as `encK`'s with `pre`. -/
theorem pre_of {P : Nat} {s : State}
    (h : (Spec.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (P + 1088)).pre s) :
    (layP P s).Ok ∧
      s.rd = [(layP P s).N, (layP P s).E, (layP P s).MSG, (layP P s).PS] ++ preX s ++ [(layP P s).ARGS] ∧
      s.wr = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩] ∧
      (stackArg s 5).toNat = Spec.Rsa.precomputedWords (s.gpr .x3).toNat ∧ P + 1088 ≤ s.sp.toNat := by
  sig_pre [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, AArch64.abi,
    AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  obtain ⟨hsp, hsp2, hrd, hwr, oN, oE, oM, oP, oS, oQ, oA, nS, eS, mS, pS, sQ, sA, kO, kN, kE, kM, kP, kS, kQ, -,
    bO, bN, bE, bM, bP, bS, bQ, kv, olk, el1, elk, mlk, plk, slk, pl⟩ := h
  have eO : (layP P s).OUT = ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ := by simp only [Lay.OUT, lay, olk]
  have eA : (layP P s).ARGS = ⟨stackArgAddr s 0, 48⟩ := by simp only [Lay.ARGS, lay_args]; rfl
  have eK : (layP P s).STK = ⟨s.sp - BitVec.ofNat 64 (P + 1087 + 1), P + 1087 + 1⟩ := by
    show (⟨(layP P s).Q - BitVec.ofNat 64 P, P + 1088⟩ : Region) = _
    rw [lay_stk P s (preX s) 48]
  have hQ : (layP P s).Q.toNat = s.sp.toNat - 1088 := toNat_sub_k (by omega)
  have hA32 : Region.Sub ⟨stackArgAddr s 0, 32⟩ ⟨stackArgAddr s 0, 48⟩ := Region.sub_prefix (by decide)
  refine ⟨⟨eO ▸ oN, eO ▸ oE, eO ▸ oM, eO ▸ oP, eO ▸ oS, by rw [eA, eO]; exact oA, nS, eS, mS, pS,
    by rw [eA]; exact sA, by rw [eK, eO]; exact kO, eK ▸ kN, eK ▸ kE, eK ▸ kM, eK ▸ kP, eK ▸ kS,
    by simp only [lay]; omega, bN, bE, bM, bP, bS, by omega, by simp only [lay] at hQ ⊢; omega, kv, olk, el1,
    elk, mlk, plk, slk, by simp [lay], by simp [lay], by simp only [lay] at hQ ⊢; omega, ?_, ?_, ?_, ?_⟩,
    ?_, hwr, pl, hsp⟩
  · intro R hR; simp only [lay, preX, List.mem_singleton] at hR; subst hR; rw [eO]; exact oQ.symm
  · intro R hR; simp only [lay, preX, List.mem_singleton] at hR; subst hR; exact sQ.symm
  · intro R hR; simp only [lay, preX, List.mem_singleton] at hR; subst hR; rw [eK]; exact kQ
  · intro R hR; simp only [lay, preX, List.mem_singleton] at hR; subst hR; exact bQ
  · rw [hrd]
    simp only [Lay.N, Lay.E, Lay.MSG, Lay.PS, Lay.ARGS, lay_args, preX, List.cons_append, List.nil_append]
    rfl

end VG.Proof.RsaPkcs1Enc.AArch64.Enc.Pc
