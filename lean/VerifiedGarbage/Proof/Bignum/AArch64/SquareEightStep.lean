module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightReady
import Mathlib.Tactic.SplitIfs

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64.SquareEight

def step (ps : List (Nat × Nat)) (q : Nat) : List Instr :=
  addPair lows[q % 2]! highs[q % 2]! ++ product ps (q + 2)

/-- Consume one scheduled product, then refill its registers with the product
needed two additions later. The other pending product remains intact. -/
theorem step_ok {s t : State} {ps : List (Nat × Nat)} {q : Nat}
    (hps : ∀ i < ps.length, ps[i]!.1 < 8 ∧ ps[i]!.2 < 8)
    (hq : q < ps.length) (hqueue : Queue s ps q t) (hk : Keep workRegs s t)
    (h7 : t.gpr .x7 = 0) (hb : accValue t + pairValue s ps q < 2 ^ 192) :
    WP isa (.block (step ps q)) t fun u =>
      Queue s ps (q + 1) u ∧ accValue u = accValue t + pairValue s ps q ∧
        u.mem = t.mem ∧ Keep workRegs t u := by
  have hr := hqueue.1 hq
  have hv := ready_value hr
  have hd := registers_disjoint ⟨q % 2, by omega⟩ ⟨0, by decide⟩
  have hab : accValue t + (t.gpr lows[q % 2]!).toNat +
      2 ^ 64 * (t.gpr highs[q % 2]!).toNat < 2 ^ 192 := by omega
  apply WP.block_append
  refine WP.mono (addPair_ok hd.2.2.2.2.2.2.1 h7 hab) fun v ⟨⟨ha, hm⟩, ka⟩ => ?_
  refine WP.mono (product_optional_ok (j := q + 2) hps) fun u ⟨⟨hp, hpm⟩, kp⟩ => ?_
  have kas : Keep workRegs t v := ka.mono (by simp [workRegs])
  have kps := kp.mono (productRegs_subset (q + 2))
  have hi := inputs_keep ((hk.trans kas).mono (by simp))
  have hn := accumulator_not_product ⟨(q + 2) % 2, by omega⟩
  refine ⟨⟨?_, ?_⟩, ?_, hpm.trans hm, (kas.trans kps).mono (by simp)⟩
  · intro h
    have hna := product_not_accumulator ⟨(q + 1) % 2, by omega⟩
    have hra := ready_keep (hqueue.2 h) ka hna.1 hna.2
    have hne : (⟨(q + 1) % 2, by omega⟩ : Fin 2) ≠ ⟨(q + 2) % 2, by omega⟩ := by
      intro he
      have heq : (q + 1) % 2 = (q + 2) % 2 := congrArg Fin.val he
      omega
    have hnp := other_product_preserved _ _ hne
    exact ready_keep hra kp hnp.1 hnp.2
  · intro h
    have h' : q + 2 < ps.length := by omega
    have hh := ready_source (hps (q + 2) h').1 (hps (q + 2) h').2 hi (hp h')
    simpa only [Nat.add_assoc] using hh
  · have hac := acc_keep kp hn.1 hn.2.1 hn.2.2
    omega

end VG.Proof.Bignum.AArch64.SquareEight
