module

import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Reduce
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillLoops
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.MemoryInit
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Initial
import VerifiedGarbage.Proof.Argon2.Iterations
import VerifiedGarbage.Proof.Argon2.FinalReduction
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Locals
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Body

/-!
# Argon2 on RISC-V: the derivation is correct

`body_ok`: the body computes the parameters and H₀, initializes and fills
the memory, and writes the tag (`Spec.Argon2.derive`) to `out`; `correct`:
the whole function, in its frame, keeps the ABI's registers too.
-/

@[expose] public section

/-!
# Argon2 on RISC-V: the derivation's frame

`restore_ok`: the body's last instructions give the return address and the
caller's registers back, from the frame; `frames_ok`: the frame's push and
pop around a body that ends so give the caller's stack pointer back.
-/

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

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Spec.Blake2 (bytesAt)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem body_ok : WP isa Impl.Argon2.RISCV64.Derive.body (entry s₀) fun t => BodyDone s₀ t ∧
    bytesAt t.mem (outP s₀) (outL s₀) =
      Spec.Argon2.derive (prm s₀) (pwB s₀) (saltB s₀) (secB s₀) (adB s₀) := by
  unfold Impl.Argon2.RISCV64.Derive.body
  refine WP.seq ?_
  rw [← List.append_nil Impl.Argon2.RISCV64.Derive.parameters, ← List.append_assoc]
  refine setup_ok hp fun s₁ i₁ _ => parameters_ok hp i₁ fun s₂ i₂ p₂ => WP.block_nil ?_
  refine WP.seq ((code_ok hp i₂ p₂).mono fun s₃ ⟨i₃, p₃, b₃⟩ => ?_)
  refine WP.seq ((memoryInit_ok hp i₃ p₃ b₃).mono fun s₄ ⟨i₄, p₄, m₄⟩ => ?_)
  refine WP.seq ((passes_ok hp (st := Spec.Argon2.initMemory (prm s₀)
    (Spec.Argon2.initialHash (prm s₀) (pwB s₀) (saltB s₀) (secB s₀) (adB s₀))) ⟨i₄, p₄, m₄⟩).mono
    fun s₅ f₅ => ?_)
  rw [show itersN s₀ = (prm s₀).passes from rfl, Proof.Argon2.iterations_fill] at f₅
  refine WP.seq ((reduce_ok hp f₅.inv f₅.pr f₅.mem).mono fun s₆ ⟨i₆, _, b₆⟩ => ?_)
  refine WP.seq ((finalOutput_ok hp i₆).mono fun s₇ ⟨i₇, o₇⟩ => ?_)
  refine (restore_ok hp i₇).mono fun t ⟨d, m⟩ => ⟨d, ?_⟩
  rw [m, o₇, b₆, Spec.Argon2.derive, Proof.Argon2.finish_reduction]
  rfl

theorem correct :
    WP isa Impl.Argon2.RISCV64.Derive.derive s₀ fun t => abiPreserved s₀ t ∧ deriveRV.post s₀ t :=
  frames_ok hp (Q := fun m => bytesAt m (outP s₀) (outL s₀) =
    Spec.Argon2.derive (prm s₀) (pwB s₀) (saltB s₀) (secB s₀) (adB s₀)) (body_ok hp)

end

end VG.Proof.Argon2.RISCV64.Derive
