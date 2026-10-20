module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightProducts
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightWord

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64.SquareEight

def pairValue (s : State) (ps : List (Nat × Nat)) (j : Nat) : Nat :=
 (s.gpr inputs[ps[j]!.1]!).toNat * (s.gpr inputs[ps[j]!.2]!).toNat

theorem ready_value {s t : State} {ps : List (Nat × Nat)} {j : Nat} (h : PairReady s ps j t) :
    (t.gpr lows[j % 2]!).toNat + 2 ^ 64 * (t.gpr highs[j % 2]!).toNat = pairValue s ps j :=
  productWord_value h.1 h.2

theorem ready_source {s u t : State} {ps : List (Nat × Nat)} {j : Nat}
    (ha : ps[j]!.1 < 8) (hb : ps[j]!.2 < 8)
    (hi : ∀ i < 8, u.gpr inputs[i]! = s.gpr inputs[i]!) (h : PairReady u ps j t) :
    PairReady s ps j t := by
  unfold PairReady at h ⊢
  rw [hi _ ha, hi _ hb] at h
  exact h

theorem ready_keep {s t u : State} {ps : List (Nat × Nat)} {j : Nat} {rs : List Reg}
    (h : PairReady s ps j t) (hk : Keep rs t u)
    (hl : lows[j % 2]! ∉ rs) (hh : highs[j % 2]! ∉ rs) : PairReady s ps j u :=
  ⟨(hk.gpr _ hl).trans h.1, (hk.gpr _ hh).trans h.2⟩

theorem acc_keep {s t : State} {rs : List Reg} (hk : Keep rs s t)
    (h19 : .x19 ∉ rs) (h20 : .x20 ∉ rs) (h21 : .x21 ∉ rs) : accValue t = accValue s := by
  unfold accValue
  rw [hk.gpr _ h19, hk.gpr _ h20, hk.gpr _ h21]

theorem accumulator_not_product : ∀ (j : Fin 2),
    .x19 ∉ [lows[j.val]!, highs[j.val]!] ∧ .x20 ∉ [lows[j.val]!, highs[j.val]!] ∧
      .x21 ∉ [lows[j.val]!, highs[j.val]!] := by decide

theorem product_not_accumulator : ∀ (j : Fin 2),
    lows[j.val]! ∉ [.x19, .x20, .x21] ∧ highs[j.val]! ∉ [.x19, .x20, .x21] := by decide

def Queue (s : State) (ps : List (Nat × Nat)) (q : Nat) (t : State) : Prop :=
 (q < ps.length → PairReady s ps q t) ∧
 (q + 1 < ps.length → PairReady s ps (q + 1) t)

/-- Issue the first two independent products before the first carry chain. -/
theorem queue_init_ok {s : State} {ps : List (Nat × Nat)}
    (hps : ∀ i < ps.length, ps[i]!.1 < 8 ∧ ps[i]!.2 < 8) :
    WP isa (.block (product ps 0 ++ product ps 1)) s fun t =>
      Queue s ps 0 t ∧ accValue t = accValue s ∧ t.mem = s.mem ∧ Keep workRegs s t := by
  apply WP.block_append
  refine WP.mono (product_optional_ok (j := 0) hps) fun u ⟨⟨hu, hum⟩, ku⟩ => ?_
  refine WP.mono (product_optional_ok (j := 1) hps) fun t ⟨⟨ht, htm⟩, kt⟩ => ?_
  have hi := inputs_keep (ku.mono (productRegs_subset 0))
  have hn0 := accumulator_not_product ⟨0, by decide⟩
  have hn1 := accumulator_not_product ⟨1, by decide⟩
  refine ⟨⟨?_, ?_⟩, (acc_keep kt hn1.1 hn1.2.1 hn1.2.2).trans
    (acc_keep ku hn0.1 hn0.2.1 hn0.2.2), htm.trans hum, ?_⟩
  · intro h
    have hd := other_product_preserved ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
    exact ready_keep (hu h) kt hd.1 hd.2
  · intro h
    exact ready_source (hps 1 h).1 (hps 1 h).2 hi (ht h)
  · exact (ku.mono (productRegs_subset 0)).trans (kt.mono (productRegs_subset 1)) |>.mono (by simp)

end VG.Proof.Bignum.AArch64.SquareEight
