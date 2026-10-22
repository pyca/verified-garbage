module

public import VerifiedGarbage.Proof.Dsa.Arm.Key.Frame
public import VerifiedGarbage.Impl.Dsa.Arm.RandomSign

/-!
# DSA key generation's frame on 32-bit ARM: the saved words

As the randomized signer's (`RandomCall.lean`): the callee-saved registers
and the register arguments, in their slots of the frame.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign

/-- The callee-saved registers and the register arguments, in their slots. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  (∀ i < 9, slot m (rBase s₀) (4 * i) = s₀.gpr (savedRegs.getD i .r0)) ∧
    slot m (rBase s₀) oOut = s₀.gpr .r0 ∧ slot m (rBase s₀) oOutLen = s₀.gpr .r1 ∧
    slot m (rBase s₀) oUsedPtr = s₀.gpr .r2 ∧ slot m (rBase s₀) oKey = s₀.gpr .r3

theorem Saved.of_slots {s₀ : State} {m m' : Mem} (h : Saved s₀ m)
    (he : ∀ d, d + 4 ≤ 36 ∨ 96 ≤ d → d + 4 ≤ 112 → slot m' (rBase s₀) d = slot m (rBase s₀) d) : Saved s₀ m' :=
  ⟨fun i hi => (he _ (.inl (by omega)) (by omega)).trans (h.1 i hi), (he _ (by decide) (by decide)).trans h.2.1,
    (he _ (by decide) (by decide)).trans h.2.2.1, (he _ (by decide) (by decide)).trans h.2.2.2.1,
    (he _ (by decide) (by decide)).trans h.2.2.2.2⟩

/-- Memory changed only in ranges of `[36, 96)` keeps the saved words. -/
theorem Saved.of_outs {s₀ : State} {m m' : Mem} {rs : List (Nat × Nat)} (h : Saved s₀ m)
    (ho : Outs (rBase s₀) rs m m') (hrs : ∀ r ∈ rs, 36 ≤ r.1 ∧ r.1 + r.2 ≤ 96) : Saved s₀ m' :=
  h.of_slots fun d hd hd' => slot_outs ho (fun r hr => by have := hrs r hr; omega) (by omega)

/-- Slots below the ranges that changed. -/
theorem outs_low {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {e : Nat}
    (hrs : ∀ r ∈ rs, e ≤ r.1) {d : Nat} (hd : d + 4 ≤ e) (hd' : d + 4 < 2 ^ 64) : slot m' B d = slot m B d :=
  slot_outs h (fun r hr => .inl (Nat.le_trans hd (hrs r hr))) hd'

theorem one_beq {k : Nat} (hk : k < 2 ^ 32) : (BitVec.ofNat 32 k - 1 == 0) = decide (k = 1) := by
  by_cases h : k = 1
  · subst h; rfl
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl,
      show (0 : BitVec 32).toNat = 0 from rfl] at this
    omega

theorem rBytes_frame {m m' : Mem} {p : Addr} {n : Nat} {rs : List Region}
    (frame : Frame rs m m') (sep : ∀ r ∈ rs, (Region.mk p n).Disjoint r) (bound : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  exact frame.bytes sep bound (List.mem_range.mp hi)

end VG.Proof.Dsa.Arm.Key
