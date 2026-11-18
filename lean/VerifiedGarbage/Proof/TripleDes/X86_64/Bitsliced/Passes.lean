module

public import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Pass
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! ### `TripleDes.X86_64.Bitsliced.Keys`, which only this module used -/

section

/-!
# The keys of the three passes

Pass `p` (counted down from 3) reads the round keys at `passA d p S + r δ`:
these are the round keys, in DES's order for the pass's direction, of the
component of the schedule `S` that TDEA uses in that pass (`passComp`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.Impl.TripleDes.X86_64.Bitslice VG.Spec.TripleDes
open VG.Proof.TripleDes (roundKey componentSchedule_readW)

/-- The component of the schedule and the direction of pass `p`. -/
def passComp : Direction → Nat → Nat × Direction
  | .encrypt, 3 => (0, .encrypt)
  | .encrypt, 2 => (1, .decrypt)
  | .encrypt, _ => (2, .encrypt)
  | .decrypt, 3 => (2, .decrypt)
  | .decrypt, 2 => (1, .encrypt)
  | .decrypt, _ => (0, .decrypt)

/-- The schedule word that is round `r`'s key of pass `p`. -/
def passIdx (d : Direction) (p r : Nat) : Nat :=
  16 * (passComp d p).1 + if (passComp d p).2 = .encrypt then r else 15 - r

theorem passIdx_lt : ∀ d : Direction, ∀ p, 1 ≤ p → p ≤ 3 → ∀ r < 16, passIdx d p r < 48 := by
  intro d p h1 h3 r hr
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> first | omega | (simp [passIdx, passComp]; omega_arith)

theorem passAddr_eq : ∀ d : Direction, ∀ p, 1 ≤ p → p ≤ 3 → ∀ r < 16,
    BitVec.ofNat 64 (passKey d p).1 + BitVec.ofNat 64 r * BitVec.ofInt 64 (passKey d p).2 =
      BitVec.ofNat 64 (8 * passIdx d p r) := by
  intro d p h1 h3
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> first | omega | decide

theorem keyAt_pass (m : Mem) (S : Addr) (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {r : Nat}
    (hr : r < 16) :
    keyAt m (passA d p S) (passD d p) r =
      roundKey (componentSchedule (scheduleAt m S) (passComp d p).1) (passComp d p).2 r := by
  simp only [keyAt, passA, passD, roundKey]
  have hc : (passComp d p).1 < 3 := by
    cases d <;> (rcases hp with ⟨h1, h3⟩; rcases p with _ | _ | _ | _ | p) <;> first | omega | decide
  have hi : (if (passComp d p).2 = .encrypt then r else 15 - r) < 16 := by split <;> omega_arith
  rw [componentSchedule_readW m S _ _ hc hi, BitVec.add_assoc, passAddr_eq d p hp.1 hp.2 r hr]
  rfl

/-- The key words of the passes are apart from the scratch buffer. -/
theorem passKeys_apart {s : State} {S : Addr} (hS : ∀ i < 48, Apart s (S + BitVec.ofNat 64 (8 * i)))
    (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {r : Nat} (hr : r < 16) :
    Apart s (passA d p S + BitVec.ofNat 64 r * passD d p) := by
  simp only [passA, passD]
  rw [BitVec.add_assoc, passAddr_eq d p hp.1 hp.2 r hr]
  exact hS _ (passIdx_lt d p hp.1 hp.2 r hr)

end VG.Proof.TripleDes.X86_64.Bitsliced

end

end


/-!
# The three passes

The loop of passes, counted down from 3 in `passSlot`, does to the state
words what three DES passes (`passW`) do, with the components and
directions of TDEA (`passComp`), in every lane.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (passW pairs swapW)

/-- The first `n` passes, with the schedule `K`. -/
def chain {w : Nat} (d : Direction) (K : Schedule) : Nat → (Nat → BitVec w) → Nat → BitVec w
  | 0, W => W
  | n + 1, W => passW (componentSchedule K (passComp d (3 - n)).1) (passComp d (3 - n)).2 (chain d K n W)

structure PassesInv (d : Direction) (s₀ : State) (p : Nat) (s : State) : Prop where
  room : Room s
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  pos : 1 ≤ p
  le : p ≤ 3
  words : ∀ x < 64, words s x = chain d (scheduleAt s₀.mem (sl s₀ schedSlot)) (3 - p) (words s₀) x
  count : sl s passSlot = BitVec.ofNat 64 p
  misc : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ stepSlot → x ≠ roundSlot → x ≠ passSlot →
    sl s x = sl s₀ x
  frame : Frame [scratchR s₀] s₀.mem s.mem

structure PassesPost (d : Direction) (s₀ s : State) : Prop where
  room : Room s
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  words : ∀ x < 64, words s x = chain d (scheduleAt s₀.mem (sl s₀ schedSlot)) 3 (words s₀) x
  misc : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ stepSlot → x ≠ roundSlot → x ≠ passSlot →
    sl s x = sl s₀ x
  frame : Frame [scratchR s₀] s₀.mem s.mem

theorem passes_ok (d : Direction) {s₀ : State}
    (hS : ∀ i < 48, Apart s₀ (sl s₀ schedSlot + BitVec.ofNat 64 (8 * i)))
    (p₀ : Nat) (s₁ : State) (hs₁ : PassesInv d s₀ p₀ s₁) :
    WP isa (.loop (pass d) .ne) s₁ (PassesPost d s₀) := by
  refine WP.loop (M := isa) (PassesInv d s₀) ?_ p₀ s₁ hs₁
  intro p s hs
  let S := sl s₀ schedSlot
  have hS' : sl s schedSlot = S := hs.misc _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have hp : 1 ≤ p ∧ p ≤ 3 := ⟨hs.pos, hs.le⟩
  have hk : ∀ r < 16, Apart s (passA d p (sl s schedSlot) + BitVec.ofNat 64 r * passD d p) := by
    intro r hr
    rw [hS']
    exact (passKeys_apart hS d hp hr).congr hs.rcx hs.rd hs.wr
  apply WP.mono (pass_ok d hp hs.room hs.count hk)
  intro s' q
  have keys : ∀ r < 16, keyAt s.mem (passA d p (sl s schedSlot)) (passD d p) r =
      VG.Proof.TripleDes.roundKey (componentSchedule (scheduleAt s₀.mem S) (passComp d p).1)
        (passComp d p).2 r := by
    intro r hr
    have e := (passKeys_apart hS d hp hr).readW hs.frame
    simp only [keyAt, hS']
    rw [e, ← keyAt_pass s₀.mem S d hp hr]; rfl
  have words' : ∀ x < 64, words s' x = chain d (scheduleAt s₀.mem S) (3 - p + 1) (words s₀) x := by
    intro x hx
    rw [q.words x hx, pairs_keys_congr 8 (fun r hr => keys r (by omega_using [hr]))]
    simp only [chain, show 3 - (3 - p) = p by omega_using [hp]]
    exact swapW_congr (pairs_congr _ 8 hs.words) x hx
  have misc' : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ stepSlot → x ≠ roundSlot → x ≠ passSlot →
      sl s' x = sl s₀ x := fun x hx a b c d e => (q.misc x hx a b c d e).trans (hs.misc x hx a b c d e)
  have frame' : Frame [scratchR s₀] s₀.mem s'.mem := by
    have := q.frame
    rw [show scratchR s = scratchR s₀ by simp only [scratchR, hs.rcx]] at this
    exact hs.frame.trans this
  have cntv : sl s passSlot - 1 = BitVec.ofNat 64 (p - 1) := by rw [hs.count]; exact cnt_sub p hs.pos
  by_cases h1 : p = 1
  · subst h1
    left
    refine ⟨?_, q.room, q.rcx.trans hs.rcx, q.rsp.trans hs.rsp, q.rd.trans hs.rd, q.wr.trans hs.wr,
      words', misc', frame'⟩
    show s'.zf.map (!·) = some false
    rw [q.zf, cntv]; rfl
  · right
    refine ⟨?_, p - 1, by omega_using [hp], ⟨q.room, q.rcx.trans hs.rcx, q.rsp.trans hs.rsp, q.rd.trans hs.rd,
      q.wr.trans hs.wr, by omega_using [hp, h1], by omega_using [hp], ?_, ?_, misc', frame'⟩⟩
    · show s'.zf.map (!·) = some true
      rw [q.zf, cntv]
      have : (BitVec.ofNat 64 (p - 1) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        have z : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_ofNat] at this
        rw [z, Nat.mod_eq_of_lt (by omega_using [hp])] at this
        omega_using [hp, h1, this]
      rw [this]; rfl
    · rw [show 3 - (p - 1) = 3 - p + 1 by omega_using [hp]]; exact words'
    · rw [q.count, cntv]

/-- Three passes, in every lane: TDEA between IP and FP. -/
theorem chain_lane {w : Nat} (d : Direction) (K : Schedule) (W : Nat → BitVec w) {b : Nat}
    (hb : b < w) :
    VG.Proof.TripleDes.Bitslice.ipLane (chain d K 3 W) b =
      match d with
      | .encrypt => VG.Proof.TripleDes.desCore (componentSchedule K 2) .encrypt
          (VG.Proof.TripleDes.desCore (componentSchedule K 1) .decrypt
            (VG.Proof.TripleDes.desCore (componentSchedule K 0) .encrypt
              (VG.Proof.TripleDes.Bitslice.ipLane W b)))
      | .decrypt => VG.Proof.TripleDes.desCore (componentSchedule K 0) .decrypt
          (VG.Proof.TripleDes.desCore (componentSchedule K 1) .encrypt
            (VG.Proof.TripleDes.desCore (componentSchedule K 2) .decrypt
              (VG.Proof.TripleDes.Bitslice.ipLane W b))) := by
  cases d <;> simp only [chain, VG.Proof.TripleDes.Bitslice.pass_lane _ _ _ hb] <;> rfl

end VG.Proof.TripleDes.X86_64.Bitsliced
