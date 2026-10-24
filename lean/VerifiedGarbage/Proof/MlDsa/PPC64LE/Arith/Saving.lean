module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Arith
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA on PPC64LE: the frames saving `r14` and `r15`

`saving body` pushes a frame saving `r14`, then one saving `r15`, runs
`body`, and pops them (`Impl/MlDsa/PPC64LE/Arith.lean`). The body runs with
our caller's registers and permissions, the stack pointer 96 bytes down,
and memory changed only below the stack pointer (`body_state`); if it keeps
the other preserved registers, the pops restore `r14`, `r15` and the stack
pointer (`saving_ok`), and memory is as the body left it.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Arith

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Arith

/-- What the body may assume of the state it starts in. -/
structure BodyStart (s₀ s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  sp : s.sp = s₀.sp - 96
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  lr : s.lr = s₀.lr
  frame : Frame [below s₀.sp 96] s₀.mem s.mem

theorem frame_slot_sub (sp : Addr) {a : Nat} (ha : a = 48 ∨ a = 96) :
    Region.Sub ⟨sp - BitVec.ofNat 64 a + 32, 16⟩ (below sp 96) := by
  rcases ha with rfl | rfl <;> exact fun x hx => by simp only [Region.Contains] at hx ⊢; bv_omega

/-- The state the body starts in. -/
theorem body_state {s₀ : State} :
    BodyStart s₀ (framed .r15 (framed .r14 s₀)) := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, ?_⟩
  · show s₀.sp - 48 - 48 = s₀.sp - 96
    bv_omega
  · show Frame _ s₀.mem ((((s₀.mem.write (s₀.sp - 48) 8 s₀.sp).write (s₀.sp - 48 + 32) 8 (s₀.gpr .r14)).write
      (s₀.sp - 48 - 48) 8 (s₀.sp - 48)).write (s₀.sp - 48 - 48 + 32) 8 (s₀.gpr .r15))
    have c : ∀ d : Nat, d + 8 ≤ 96 → (below s₀.sp 96).Contains (s₀.sp - 96 + BitVec.ofNat 64 d) 8 := fun d hd =>
      Offset.contains_base _ hd (by omega)
    have e1 : s₀.sp - 48 = s₀.sp - 96 + BitVec.ofNat 64 48 := by bv_omega
    have e2 : s₀.sp - 48 + 32 = s₀.sp - 96 + BitVec.ofNat 64 80 := by bv_omega
    have e3 : s₀.sp - 48 - 48 = s₀.sp - 96 + BitVec.ofNat 64 0 := by bv_omega
    have e4 : s₀.sp - 48 - 48 + 32 = s₀.sp - 96 + BitVec.ofNat 64 32 := by bv_omega
    rw [e4, e3, e2, e1]
    exact ((((Frame.refl _ _).write (List.mem_singleton_self _) _ (c 48 (by omega))).write
      (List.mem_singleton_self _) _ (c 80 (by omega))).write (List.mem_singleton_self _) _ (c 0 (by omega))).write
      (List.mem_singleton_self _) _ (c 32 (by omega))

/-- `saving body`: the pops restore `r14`, `r15` and the stack pointer. -/
theorem saving_ok {body : Prog isa} {s₀ : State} {P : Mem → Prop}
    (hsp : 96 ≤ s₀.sp.toNat) (hd : ∀ R ∈ s₀.wr, (below s₀.sp 96).Disjoint R)
    (hn : sdepth body + 96 < 2 ^ 64)
    (hb : WP isa body (framed .r15 (framed .r14 s₀)) fun s' =>
      (∀ r ∈ preserved, r ≠ .r14 → r ≠ .r15 → s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧ P s'.mem) :
    WP isa (saving body) s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧
      s'.lr = s₀.lr ∧ P s'.mem := by
  have hsp1 : 48 ≤ (s₀.sp - 48).toNat := by bv_omega
  refine WP.frameRegAny (r := .r14) (by omega) (fun R hR => (hd R hR).sub_left (frame_slot_sub s₀.sp (.inl rfl)))
    ?_ (by simp only [sdepth, Instr.frameBytes]; omega)
  refine WP.frameRegAny (r := .r15) hsp1 (fun R hR => ?_) (WP.mono hb fun s' ⟨hk, hlr, hP⟩ => ?_) (by omega)
  · have : (framed .r14 s₀).sp = s₀.sp - 48 := rfl
    rw [this, show s₀.sp - 48 - 48 = s₀.sp - BitVec.ofNat 64 96 by bv_omega]
    exact (hd R hR).sub_left (frame_slot_sub s₀.sp (.inr rfl))
  · refine ⟨fun r hr => ?_, rfl, hlr, hP⟩
    simp only [State.write]
    by_cases h14 : r = .r14
    · subst h14; simp
    · by_cases h15 : r = .r15
      · subst h15; simp [framed]
      · simp only [h14, h15, ite_false]; exact hk r hr h14 h15

end VG.Proof.MlDsa.PPC64LE.Arith
