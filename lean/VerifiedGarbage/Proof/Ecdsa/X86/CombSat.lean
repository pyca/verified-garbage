import VerifiedGarbage.Proof.Ecdsa.X86.CombContract

/-! # A concrete witness for the comb signing contract -/
namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86

@[irreducible] def combSatMem : Mem := fun a =>
  if (a - 0x100000).toNat < 8 * p256W.length then constMem 0x100000 p256W a else satMem a

theorem combSatMem_held : ∀ i < p256W.length,
    combSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p256W.getD i 0 := by
  intro i hi
  have hl := p256W_length
  have hm : combSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 =
      (constMem 0x100000 p256W).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 := by
    apply Mem.readW_congr
    intro j hj
    have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x100000).toNat = 8 * i + j := by
      rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    unfold combSatMem
    rw [e, ite_eq_left (show 8 * i + j < 8 * p256W.length by omega)]
  exact hm.trans (constMem_held 0x100000 p256W (by omega) i hi)

def combSatState : State := { satState with
  mem := combSatMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩, ⟨0x100000, 151552⟩]
  syms := fun _ => 0x100000 }

theorem combSat_arg (j : Nat) (hj : j < 5) : arg combSatState j = arg satState j := by
  have outside : ∀ j < 5, ∀ b < 4,
      151552 ≤ (argAddr satState j + BitVec.ofNat 64 b - 0x100000).toNat := by decide
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change combSatMem (argAddr satState j + BitVec.ofNat 64 b) = satMem (argAddr satState j + BitVec.ofNat 64 b)
  unfold combSatMem
  rw [ite_eq_right (by have := outside j hj b (by omega); rw [p256W_length]; omega)]

theorem combSat_spec : combSignSpec.pre combSatState := by
  have a0 : arg combSatState 0 = 0x1000 := (combSat_arg 0 (by decide)).trans (by decide)
  have a1 : arg combSatState 1 = 0x2000 := (combSat_arg 1 (by decide)).trans (by decide)
  have a2 : arg combSatState 2 = 0x3000 := (combSat_arg 2 (by decide)).trans (by decide)
  have a3 : arg combSatState 3 = 0x4000 := (combSat_arg 3 (by decide)).trans (by decide)
  have a4 : arg combSatState 4 = 0x8000 := (combSat_arg 4 (by decide)).trans (by decide)
  have held : ∀ i < p256W.length, combSatState.mem.readW
      ((combSatState.syms "VG_P256_COMB").setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = p256W.getD i 0 :=
    combSatMem_held
  generalize e : combSatState = s
  sig_pre [combSignSpec, Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.signContract,
    Spec.Ecdsa.Instance.signSig, Spec.P256.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p256Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  refine ⟨by decide, by decide, ?_, held, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p256W_length]; rfl
  · rw [p256W_length]; decide
  · rw [p256W_length]
    intro r hr
    change r ∈ [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩, ⟨0x20004, 20⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · rw [p256W_length]; exact Region.disjoint_of_sep (by decide)
  · rw [p256W_length]; exact Region.disjoint_of_sep (by decide)
  · rw [a0, a1, a2, a3, a4]
    refine ⟨rfl, rfl, ?_⟩
    repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

end VG.Proof.Ecdsa.X86
