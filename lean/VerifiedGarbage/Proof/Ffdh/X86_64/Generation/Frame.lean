module
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Proof.Framework.Mem


/-! # Private outgoing stack frames for generation controllers -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64

def allocated (bytes : Nat) (s : State) : State :=
  { s.setReg .rsp (s.gpr .rsp - BitVec.ofNat 64 bytes) with
    wr := ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr }

def freed (bytes : Nat) (s : State) : State :=
  { s.setReg .rsp (s.gpr .rsp + BitVec.ofNat 64 bytes) with wr := s.wr.tail }

theorem allocated_rsp (bytes : Nat) (s : State) :
    (allocated bytes s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes := rfl

theorem allocated_reg (bytes : Nat) (s : State) (r : Reg) (hr : r ≠ .rsp) :
    (allocated bytes s).gpr r = s.gpr r := ite_eq_right hr

theorem allocated_mem (bytes : Nat) (s : State) : (allocated bytes s).mem = s.mem := rfl

theorem freed_rsp (bytes : Nat) (s : State) :
    (freed bytes s).gpr .rsp = s.gpr .rsp + BitVec.ofNat 64 bytes := rfl

theorem freed_reg (bytes : Nat) (s : State) (r : Reg) (hr : r ≠ .rsp) :
    (freed bytes s).gpr r = s.gpr r := ite_eq_right hr

theorem freed_mem (bytes : Nat) (s : State) : (freed bytes s).mem = s.mem := rfl

theorem frame_alloc {bytes : Nat} {s : State} {body : Prog isa} {Q : State → Prop}
    (hpos : 0 < bytes) (hsmall : bytes < 4096) (halign : bytes % 8 = 0)
    (hroom : bytes ≤ (s.gpr .rsp).toNat)
    (hbody : WP isa body (allocated bytes s) fun t =>
      t.gpr .rsp = (allocated bytes s).gpr .rsp ∧
      t.wr = (allocated bytes s).wr ∧ Q (freed bytes t)) :
    WP isa (.frame (.alloc bytes) body (.free bytes)) s Q := by
  obtain ⟨tr, t, he, hsp, hw, hq⟩ := hbody
  have hpush : isa.push (.alloc bytes) s = some (allocated bytes s) := by
    simp only [isa, push, hpos, hsmall, halign, hroom, and_self, ite_true, allocated]
  have hpop : isa.pop (.free bytes) (allocated bytes s) t = some (freed bytes t) := by
    simp only [isa, pop, hpos, hsmall, halign, hsp, hw, allocated, State.setReg,
      List.head?_cons, and_self, ite_true, freed]
  exact ⟨_, _, Exec.frame hpush he hpop, hq⟩

private theorem allocated_some {bytes : Nat} {s t : State}
    (h : isa.push (.alloc bytes) s = some t) : t = allocated bytes s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

theorem frame_alloc_ct {bytes : Nat} {P : State → State → Prop} {body : Prog isa}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocated bytes s ∧ b = allocated bytes t)
      body (fun _ _ => True)) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) (fun _ _ => True) := by
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain rfl := allocated_some p₁
      obtain rfl := allocated_some p₂
      obtain ⟨he, _⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨by simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using he, trivial⟩

end VG.Proof.Ffdh.X86_64.Generation
