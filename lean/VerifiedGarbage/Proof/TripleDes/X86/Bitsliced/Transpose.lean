module

public import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.Machine
public import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.SboxLit
public import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Bitslice.Table
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.Machine
meta import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
meta import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
meta import VerifiedGarbage.Proof.Framework.Bitslice.Table

/-!
# The transposition of the bitsliced state on x86 (32-bit)

As on ARMv7 (`Proof/TripleDes/Arm/Bitsliced/Transpose.lean`): the
transposition (`transpose`) only moves and XORs bits of the 64 state words
and masks them with constants: the lane domain evaluates it on words of
atoms (bit `t` of word `i` is atom `32 i + t`), and the check that bit `p`
of word `32 h + j` is then atom `32 (32 h + p) + j` proves that it
transposes each half of any 64 words (`transposeW`).
-/

-- separate module: builds in parallel with `Pass`, which does not import it

@[expose] public section

namespace VG.Proof.TripleDes.X86.Bitsliced

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.TripleDes.X86.Bitslice

/-- Each half of 64 words of 32 bits, transposed: bit `b` of word `32 h + j`
is bit `j` of word `32 h + b`. -/
def transposeW (W : Nat → BitVec 32) : Nat → BitVec 32 := fun j =>
  ofBits 32 fun b => (W (32 * (j / 32) + b)).getLsbD (j % 32)

def transEnv : Env (Nat × Nat) :=
  { reg := fun _ => none,
    slot := fun k => if spills ≤ k ∧ k < spills + 64 then some (inWordW 32 (k - spills)) else none }

def transPost (e : Env (Nat × Nat)) : Bool :=
  (List.range 64).all fun j =>
    e.slot (spills + j) == some (outWordW 32 (fun p => [32 * (32 * (j / 32) + p) + j % 32]))

theorem transpose_check :
    check (lanes 32 11) varsCfg (fun _ => none) (instrs transposeProg.lit) transEnv transPost = true := by
  lit_decide

theorem transpose_code : instrs transposeProg.lit = transpose := by
  rw [← transposeProg.lit_eq]; rfl

theorem transpose_kept : ((instrs transposeProg.lit).all fun i => i.dst != some .esp) = true := by
  lit_decide

theorem transpose_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa transpose s = some s' ∧ (∀ j < 64, words s' j = transposeW (words s) j) ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [stR s] s.mem s'.mem := by
  have hrel : Rel (LaneRel 11 (assign (words s) (2 ^ 11))) varsCfg (fun _ => none) transEnv s := by
    refine ⟨(fun r a h => by cases h), (fun k a hk hsl => ?_),
      (fun _ _ hk => by simp [varsCfg] at hk)⟩
    simp only [transEnv] at hsl
    split at hsl
    · rename_i hk'
      cases hsl
      have hw : s.mem.readW (wordAddr (s.gpr varsCfg.base) k) 32 = words s (k - spills) := by
        rw [words, fw, show spills + (k - spills) = k by omega_using [hk']]; rfl
      rw [hw]
      exact inWordW_rel (words s) (by omega_using [hk'])
    · cases hsl
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ transpose_check
  have hk := transpose_kept
  rw [transpose_code] at he hk
  obtain ⟨s', hs', p⟩ := run lanes_sound (varsCfg_ok h) hrel he
  refine ⟨s', hs', fun j hj => ?_, p.base, p.other _ (by rw [hk]; exact Bool.noConfusion), p.rd, p.wr, p.frame⟩
  have hpj := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
  have hs := p.rel.slot (spills + j) _ (by simp only [varsCfg]; omega_using [hj]) (beq_iff_eq.mp hpj)
  have bits := outWordW_rel (fun q hq a ha => by simp at ha; omega_using [hj, hq, ha]) hs
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have hsj : words s' j = s'.mem.readW (wordAddr (s'.gpr varsCfg.base) (spills + j)) 32 := rfl
  rw [hsj, bits b hb]
  simp only [xorBits_cons, xorBits_nil, Bool.xor_false, transposeW, getLsbD_ofBits, hb,
    decide_true, Bool.true_and]
  exact bitOf_word (words s) (32 * (j / 32) + b) (j % 32) (Nat.mod_lt _ (by decide))

end VG.Proof.TripleDes.X86.Bitsliced
