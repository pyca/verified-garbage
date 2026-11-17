module

public import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Frame rules that assume nothing of a released frame (ARMv7)

Temporary: the frame rules `WP.frame` and `WP.alloc` restated so that the
postcondition holds whatever memory `m` that differs from the body's only in
the frame, and whatever unknowns `u`, the state has once the frame is
released, while the proofs move to them; they then replace the rules of
`Frame.lean` and `Call.lean`.
-/

@[expose] public section

namespace VG.Arm

/-- A byte of a region apart from a frame is what it was once the frame's
bytes are lost. -/
theorem lost_byte {F R : Region} {m m' : Mem} (f : Frame [F] m m') (hd : R.Disjoint F) {i : Nat}
    (hi : i < R.len) : m' (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) := by
  refine f _ fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  refine hd _ ?_ hc
  simp only [Region.Contains]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega_using [hi, this]

/-- A frame of the words `rs`, popped into `r`: its body runs from
`pushed rs s`, and the pop leads to `popped r (4 * rs.length) s₂`, of which
the postcondition may rely on nothing the frame's bytes hold, nor on the
unknowns: it holds whatever memory `m` that differs from the body's only in
the frame, and whatever unknowns `u`, the state then has. (A frame's bytes
are below the stack pointer once it is released, where a signal handler may
overwrite them.) -/
theorem WP.frameLost {rs : List Reg} {r : Reg} {body : Prog isa} {s : State} {Q : State → Prop}
    (hrs : regList rs = true) (hn : 4 * rs.length ≤ s.sp.toNat) (hlt : 4 * rs.length < 256)
    (hb : WP isa body (pushed rs s) fun s₂ => ∀ m u,
      Frame [⟨State.addr (s.sp - BitVec.ofNat 32 (4 * rs.length)), 4 * rs.length⟩] s₂.mem m →
        Q { popped r (4 * rs.length) s₂ with mem := m, unknowns := u }) :
    WP isa (.frame (.push rs) body (.pop r (4 * rs.length))) s Q :=
  WP.frame hrs hn hlt (WP.mono hb fun _ h => h _ _ (Frame.refl _ _))

/-- Reserve a positive, encodable, ABI-aligned stack buffer and release it:
its body runs from `allocated bytes s`, and the `free` leads to
`freed bytes s₂`, of which the postcondition may rely on nothing the frame's
bytes hold, nor on the unknowns (as `WP.frameLost`'s). -/
theorem WP.allocLost {bytes : Nat} {body : Prog isa} {s : State} {Q : State → Prop}
    (hn : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0 ∧ encodable (BitVec.ofNat 32 bytes) = true)
    (hsp : bytes ≤ s.sp.toNat)
    (hb : WP isa body (allocated bytes s) fun s₂ => ∀ m u,
      Frame [⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩] s₂.mem m →
        Q { freed bytes s₂ with mem := m, unknowns := u }) :
    WP isa (.frame (.alloc bytes) body (.free bytes)) s Q :=
  WP.alloc hn hsp (WP.mono hb fun _ h => h _ _ (Frame.refl _ _))

end VG.Arm
