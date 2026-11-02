module

import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Locals
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Body

/-!
# Argon2 on RISC-V: the derivation's frame

`restore_ok`: the body's last instructions give the return address and the
caller's registers back, from the frame; `frames_ok`: the frame's push and
pop around a body that ends so give the caller's stack pointer back.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.Impl.Argon2.RISCV64.Derive (savedSlots argSlots restoreSlots)

/-- What the body ends with, for the frame's pop to restore the caller's
state. -/
structure BodyDone (s₀ t : State) : Prop where
  sp : t.sp = E s₀
  wr : t.wr = (entry s₀).wr
  regs : ∀ r ∈ preserved, t.gpr r = s₀.gpr r
  ra : t.gpr .ra = s₀.gpr .ra

theorem restore_ok {s₀ : State} (hp : DPre s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block Impl.Argon2.RISCV64.Derive.restore) s fun t =>
      BodyDone s₀ t ∧ t.mem = s.mem := by
  have sub : ∀ p ∈ restoreSlots, p ∈ savedSlots ++ argSlots := by decide
  have bounds : ∀ p ∈ restoreSlots, p.2 + 8 ≤ 120 := by decide
  rw [show Impl.Argon2.RISCV64.Derive.restore = Spill.restoreCode .s3 restoreSlots from rfl]
  refine WP.mono (Spill.restore_wp (b := .s3) (B := E s₀) (g := s₀.gpr) (by have := E_al hp; omega) h.s3
    (by decide) (by decide) (fun p hp' => loc_in' h (by have := bounds p hp'; omega))
    (fun p hp' => h.saved hp (sub p hp'))) fun t ut => ⟨⟨?_, ?_, fun r hr => ?_, ?_⟩, ut.mem⟩
  · rw [ut.sp, h.sp]
  · rw [ut.wr, h.wr]
  · refine ut.gpr_of ?_
    by_cases hm : r ∈ restoreSlots.map Prod.fst
    · exact .inl hm
    · refine .inr ?_
      have hu : r ∈ untouched := by revert hm; revert hr; revert r; decide
      exact h.keep r hu
  · exact ut.gpr (.ra, Impl.Argon2.RISCV64.Derive.raOff) (by decide)

theorem frames_ok {s₀ : State} (hp : DPre s₀) {Q : Mem → Prop}
    (hb : WP isa Impl.Argon2.RISCV64.Derive.body (entry s₀) fun t => BodyDone s₀ t ∧ Q t.mem) :
    WP isa Impl.Argon2.RISCV64.Derive.derive s₀ fun u => abiPreserved s₀ u ∧ Q u.mem := by
  refine WP.alloc (by decide) hp.sp_lo (hb.mono fun t ⟨d, q⟩ => ?_)
  refine ⟨⟨d.regs, ?_, d.ra⟩, q⟩
  show t.sp + BitVec.ofNat 64 320 = _
  rw [d.sp, BitVec.sub_add_cancel]

end VG.Proof.Argon2.RISCV64.Derive
