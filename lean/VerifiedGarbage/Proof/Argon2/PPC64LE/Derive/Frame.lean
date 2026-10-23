module

public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Locals
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc

/-!
# Argon2 on PPC64LE: the derivation's frame

`restore_ok`: the body's last instructions give the return address and the
caller's registers back, from the frame; `frames_ok`: the frame's push and
pop around a body that ends so give the caller's stack pointer back.
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_ld)
open VG.Impl.Argon2.PPC64LE.Derive (ld savedSlots argSlots restoreSlots)

/-- What the body ends with, for the frame's pop to restore the caller's
state. -/
structure BodyDone (s₀ t : State) : Prop where
  sp : t.sp = E s₀
  wr : t.wr = (entry s₀).wr
  regs : ∀ r ∈ preserved, t.gpr r = s₀.gpr r
  lr : t.lr = s₀.lr

theorem restore_ok {s₀ : State} (hp : DPre s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block Impl.Argon2.PPC64LE.Derive.restore) s fun t =>
      BodyDone s₀ t ∧ t.mem = s.mem := by
  have sub : ∀ p ∈ restoreSlots, p ∈ savedSlots ++ argSlots := by decide
  have bounds : ∀ p ∈ restoreSlots, 112 ≤ p.2 ∧ p.2 + 8 ≤ 144 := by decide
  refine wp_ld (a := E s₀ + BitVec.ofNat 64 104) (by decide) (by rw [h.r30]; rfl)
    (loc_in' h (by decide) (by decide)) fun a ua => ?_
  refine MdStream.PPC64LE.WP.cons exec_mtlr ?_
  rw [show restoreSlots.map (fun (r, d) => Instr.load .d r .r30 d) =
    Spill.restoreCode .r30 restoreSlots from rfl, ← List.append_nil (Spill.restoreCode _ _)]
  refine Spill.restore_ok (B := E s₀) (g := s₀.gpr) (by decide)
    (by show a.gpr .r30 = _; rw [ua.other _ (by decide), h.r30]) (by decide) (by decide)
    (fun p hp' => by
      show InRegions (a.rd ++ a.wr) _ _
      rw [ua.rd, ua.wr]
      exact loc_in' h (by have := bounds p hp'; omega) (by have := bounds p hp'; omega))
    (fun p hp' => by
      show a.mem.readW _ _ = _
      rw [ua.mem]
      exact h.saved hp (sub p hp')) fun t ut => WP.block_nil ⟨⟨?_, ?_, fun r hr => ?_, ?_⟩, ?_⟩
  · rw [ut.sp]; show a.sp = _; rw [ua.sp, h.sp]
  · rw [ut.wr]; show a.wr = _; rw [ua.wr, h.wr]
  · refine ut.gpr_of ?_
    by_cases hm : r ∈ restoreSlots.map Prod.fst
    · exact .inl hm
    · refine .inr ?_
      have hu : r ∈ untouched := by revert hm; revert hr; revert r; decide
      have h0 : r ≠ .r0 := fun e => by subst e; exact absurd hu (by decide)
      show a.gpr r = _
      rw [ua.other _ h0, h.keep r hu]
  · rw [ut.lr]; show a.gpr .r0 = _; rw [ua.gpr]; exact h.lr hp
  · rw [ut.mem]; show a.mem = _; rw [ua.mem]

theorem frames_ok {s₀ : State} (hp : DPre s₀) {Q : Mem → Prop}
    (hb : WP isa Impl.Argon2.PPC64LE.Derive.body (entry s₀) fun t => BodyDone s₀ t ∧ Q t.mem) :
    WP isa Impl.Argon2.PPC64LE.Derive.derive s₀ fun u => abiPreserved s₀ u ∧ Q u.mem := by
  refine WP.alloc (by decide) (by have := hp.sp_lo; show 336 ≤ _; omega) (hb.mono fun t ⟨d, q⟩ => ?_)
  refine ⟨⟨d.regs, ?_, d.lr⟩, q⟩
  show t.sp + BitVec.ofNat 64 336 = _
  rw [d.sp, BitVec.sub_add_cancel]

end VG.Proof.Argon2.PPC64LE.Derive
