import VerifiedGarbage.Proof.Ed25519.X86_64.FieldWide

/-!
# Ed25519 field programs on the wide scratch, with bounds

`field_liftB` lifts a field program's proof on the narrow scratch (4096 bytes)
to the wide one (8192), with bounds on the memory before and after; and
`wp_and` joins two postconditions of the same code.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr Outside Op clob F fe)

variable {fld : Arith} [EdArith fld]

/-- Two postconditions of the same code (which runs deterministically). -/
theorem wp_and {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁)
    (h₂ : WP isa c s Q₂) : WP isa c s fun t => Q₁ t ∧ Q₂ t := by
  obtain ⟨t₁, s₁, e₁, q₁⟩ := h₁
  obtain ⟨t₂, s₂, e₂, q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, s₁, e₁, q₁, q₂⟩

/-- `field_lift`, with bounds before and after. -/
theorem field_liftB {s : State} {base : Addr} (hs : Scratch s base) (code : List Instr)
    (f : Env → Env) (Pre Post : Mem → Prop) (hpre : Pre s.mem)
    (correct : ∀ t, Scr t base → Pre t.mem → WP isa (.block code) t fun u =>
      Keep base t u ∧ env u.mem base = f (env t.mem base) ∧ Post u.mem) :
    WP isa (.block code) s fun t => Keep base s t ∧ env t.mem base = f (env s.mem base) ∧
      Post t.mem := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega⟩
  obtain ⟨tr, t, he, hk, hv, hp⟩ := correct narrow hn hpre
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, ⟨hk.gpr, rfl, rfl, hk.mem⟩, hv, hp⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

end VG.Proof.Ed25519.X86_64
