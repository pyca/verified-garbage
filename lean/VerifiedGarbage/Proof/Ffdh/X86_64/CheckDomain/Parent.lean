module
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Setup

import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH domain validation on x86-64: the outer workspace -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure Parent (p : CdP) (s : State) : Prop where
  base : Base p s
  outer : Outer s p.B p.Z p.w
  g : word s.mem p.B (8 * sG) = off p.dp p.k
  q : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k)

theorem Work.parent {p : CdP} {mi : BitVec 64} {s : State} (h : Work p mi s)
    (hd : s.gpr .rdi = p.B) : Parent p s := by
  have hk := h.base.k1
  have hk' := h.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  exact ⟨h.base, Outer.of_mem h.mem hd (room_k hk h.base.hZ) (by omega) (by omega), h.g, h.q⟩

theorem Parent.keep {p : CdP} {s t : State} {rs : List Reg} (h : Parent p s)
    (hm : t.mem = s.mem) (k : Keep rs s t) (hd : t.gpr .rdi = s.gpr .rdi) : Parent p t :=
  ⟨h.base.keep (by rw [hm]; exact InScr.refl _ _ _) k (fun _ _ => by rw [hm]),
    ⟨h.outer.scr.congr k.2.2, hd.trans h.outer.rdi, by rw [hm]; exact h.outer.hw,
      fun j hj => by rw [hm]; exact h.outer.harr j hj, h.outer.room, h.outer.w2, h.outer.w28⟩, by rw [hm]; exact h.g, by rw [hm]; exact h.q⟩

/-- Changes to outer arrays preserve its public header and the input domain. -/
theorem Parent.array {p : CdP} {s t : State} {rs : List (Nat × Nat)} {regs : List Reg}
    (h : Parent p s) (hf : Frm p.B rs s.mem t.mem)
    (hr : ∀ r ∈ rs, 256 ≤ r.1 ∧ r.1 + r.2 ≤ p.Z)
    (k : Keep regs s t) (hd : t.gpr .rdi = s.gpr .rdi) :
    Parent p t ∧ InScr p.B p.Z s.mem t.mem ∧
      (∀ i < 32, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) := by
  have hi : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (fun r he => (hr r he).2)
  have hh : ∀ i < 32, word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi =>
    hf.word_eq (fun r he => Or.inl (by have := (hr r he).1; omega)) (by omega)
  refine ⟨⟨h.base.keep hi k ?_, h.outer.of_frm hf (fun r he => by have := hr r he; omega) k.2.2 hd, (hh _ (by decide)).trans h.g, (hh _ (by decide)).trans h.q⟩, hi, hh⟩
  intro e he
  simp only [CdP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> exact hh _ (by dsimp only; decide)

/-- View the outer arrays as a generic Montgomery workspace; its inverse is unused here. -/
theorem Parent.good {p : CdP} {s : State} (h : Parent p s) :
    Good s p.B p.Z p.w (word s.mem p.B (8 * sMinv)) ∧ slot p.w 8 ≤ p.Z :=
  ⟨⟨h.outer.scr, h.outer.rdi, ⟨h.outer.hw, rfl, h.outer.harr⟩⟩,
    by have := h.outer.room; unfold inner at this; omega⟩

end VG.Proof.Ffdh.X86_64.CheckDomain
