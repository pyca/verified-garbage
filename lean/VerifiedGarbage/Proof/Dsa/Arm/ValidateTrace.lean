module

public import VerifiedGarbage.Proof.Dsa.Arm.CoreTrace
import VerifiedGarbage.Proof.Dsa.Arm.ValidateOps
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# DSA on 32-bit ARM: the checks' traces

As the arithmetic's (`CoreTrace.lean`): the checks read their operands
through pointers that are the same in both runs, and compute masks without
branching on them.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest)

/-- Code from `r12` and `r10` public, from code from `r12` public. -/
theorem relCT_T10 {c : Prog isa} {Q : State → State → Prop} (H : RelCT isa (VG.Arm.Taint.Agree T0) c Q) :
    RelCT isa (VG.Arm.Taint.Agree T10) c Q :=
  H.mono (fun _ _ A => agree_weaken rfl A) fun _ _ h => h

theorem ptrEq_slot {s₁ s₂ u₁ u₂ : State} {base : Addr} {n i : Nat} {p : Pointer} (hp : PtrOk p)
    (he : PtrEq base s₁ s₂ p) (hi : i < 12) (hn : n ≤ 48)
    (R₁ : Rest coreClob s₁ u₁) (O₁ : Outside base (slot n i) (8 * n) s₁.mem u₁.mem)
    (R₂ : Rest coreClob s₂ u₂) (O₂ : Outside base (slot n i) (8 * n) s₂.mem u₂.mem) : PtrEq base u₁ u₂ p := by
  unfold PtrEq
  rw [pointerValue_keep (R₁.gpr .r12 (by decide)) (Outs.of_slot O₁ hi hn) arith_hdr hp,
    pointerValue_keep (R₂.gpr .r12 (by decide)) (Outs.of_slot O₂ hi hn) arith_hdr hp]
  exact he

theorem range_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ len n : Nat} {modulus : Field} {input : Pointer}
    (hs₁ : Ws s₁ base size₁) (hs₂ : Ws s₂ base size₂) (hz₁ : 4960 ≤ size₁) (hz₂ : 4960 ≤ size₂) (w : Width len n)
    (Rq₁ : Ready s₁ base (.input modulus) len) (Rq₂ : Ready s₂ base (.input modulus) len)
    (Ri₁ : Ready s₁ base input len) (hem : PtrEq base s₁ s₂ (.input modulus)) (hei : PtrEq base s₁ s₂ input)
    (aboveOne : Bool) :
    SameTrace isa (Validate.range len modulus input aboveOne) s₁ s₂ := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  unfold Validate.range
  dsimp only
  rw [← w.n_eq]
  refine SameTrace.seq (load_trace hs₁ hs₂ (by omega) (by omega) Rq₁.ok hem)
    (loadSlot_ok (i := 0) hs₁ hz₁ w (by decide) Rq₁) (loadSlot_ok (i := 0) hs₂ hz₂ w (by decide) Rq₂)
    fun u₁ u₂ ⟨w₁, _, R₁, O₁⟩ ⟨w₂, _, R₂, O₂⟩ => ?_
  refine loadThen_trace w₁ w₂ (by omega) (by omega) Ri₁.ok (ptrEq_slot Ri₁.ok hei (by decide) n48 R₁ O₁ R₂ O₂)
    (relCT_T10 ((RelCT.seq (Q := VG.Arm.Taint.Agree T0) (checkRange_relCT _ _ _ _) ?_).mono (fun _ _ h => h) fun _ _ _ => trivial))
  cases aboveOne
  · exact RelCT.block_nil fun _ _ h => h
  · exact lowerTwo_relCT n

theorem zero_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ len : Nat} {input : Pointer}
    (hs₁ : Ws s₁ base size₁) (hs₂ : Ws s₂ base size₂) (hz₁ : 4960 ≤ size₁) (hz₂ : 4960 ≤ size₂)
    (hp : PtrOk input) (hei : PtrEq base s₁ s₂ input) (want : Bool) :
    SameTrace isa (Validate.zero len input want) s₁ s₂ := by
  unfold Validate.zero
  exact loadThen_trace hs₁ hs₂ (by omega) (by omega) hp hei
    (relCT_T10 ((checkZero_relCT _ _ _ want).mono (fun _ _ h => h) fun _ _ _ => trivial))

theorem isOne_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ len : Nat} {input : Pointer}
    (hs₁ : Ws s₁ base size₁) (hs₂ : Ws s₂ base size₂) (hz₁ : 4960 ≤ size₁) (hz₂ : 4960 ≤ size₂)
    (hp : PtrOk input) (hei : PtrEq base s₁ s₂ input) :
    SameTrace isa (Validate.isOne len input) s₁ s₂ := by
  unfold Validate.isOne
  exact loadThen_trace hs₁ hs₂ (by omega) (by omega) hp hei
    (relCT_T10 ((RelCT.seq (setConst_relCT _ _ _) (relCT_T10 (equalAcc_relCT _ _ _))).mono
      (fun _ _ h => h) fun _ _ _ => trivial))

theorem equalValues_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ len n : Nat} {a b : Pointer}
    (hs₁ : Ws s₁ base size₁) (hs₂ : Ws s₂ base size₂) (hz₁ : 4960 ≤ size₁) (hz₂ : 4960 ≤ size₂) (w : Width len n)
    (Ra₁ : Ready s₁ base a len) (Ra₂ : Ready s₂ base a len) (Rb₁ : Ready s₁ base b len)
    (hea : PtrEq base s₁ s₂ a) (heb : PtrEq base s₁ s₂ b) :
    SameTrace isa (Validate.equalValues len a b) s₁ s₂ := by
  unfold Validate.equalValues
  dsimp only
  rw [← w.n_eq]
  exact SameTrace.assoc (twoLoads_trace hs₁ hs₂ hz₁ hz₂ w Ra₁ Ra₂ Rb₁ hea heb
    ((equalAcc_relCT _ _ _).mono (fun _ _ h => h) fun _ _ _ => trivial))

theorem minus_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ len n m₁ m₂ amount output : Nat} {modulus : Field}
    (P₁ : OpPre s₁ base size₁ len n m₁ modulus) (P₂ : OpPre s₂ base size₂ len n m₂ modulus)
    (hem : PtrEq base s₁ s₂ (.input modulus)) :
    SameTrace isa (Validate.minus len modulus amount output) s₁ s₂ := by
  unfold Validate.minus
  dsimp only
  rw [← P₁.w.n_eq]
  refine SameTrace.seq (setup_trace P₁ P₂ hem) (setup_ok P₁.ws P₁.hz P₁.w P₁.R P₁.hm P₁.hm1 P₁.hodd)
    (setup_ok P₂.ws P₂.hz P₁.w P₂.R P₂.hm P₂.hm1 P₂.hodd) fun u₁ u₂ ⟨c₁, _⟩ ⟨c₂, _⟩ => ?_
  exact SameTrace.of_relCT (RelCT.seq (modulusMinus_relCT _ _) (store_relCT _ _)) (agree0 c₁.ws c₂.ws)

end VG.Proof.Dsa.Arm
