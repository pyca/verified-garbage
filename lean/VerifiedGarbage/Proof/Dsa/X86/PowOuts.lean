module

public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! # Memory that changes in given ranges and in the stack of a call

`OutsS base sp rs m m'`: `m'` agrees with `m` but on the ranges `rs` of
offsets from `base` and on the 96 bytes below `sp`, which a call of
`vg_rsa_mont_mul_at` uses (a frame of 36 bytes of arguments, the return
address and the callee's 56). The working space lies apart from those bytes
(`CallRoom`), so its numbers keep their values (`OutsS.val32`), and so does a
context (`Context.outsS_keep`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.Pow

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Dynamic

/-- `m'` agrees with `m` but on the ranges `rs` of offsets from `base` and on
the 96 bytes below `sp`, which a call of `vg_rsa_mont_mul_at` uses. -/
def OutsS (base : Addr) (sp : BitVec 32) (rs : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ x, (∀ r ∈ rs, ofs base x < r.1 ∨ r.1 + r.2 ≤ ofs base x) → ¬ (below sp 96).Contains x 1 → m' x = m x

namespace OutsS

variable {base : Addr} {sp : BitVec 32} {rs rs' : List (Nat × Nat)} {m₁ m₂ m₃ : Mem}

theorem refl (base : Addr) (sp : BitVec 32) (rs : List (Nat × Nat)) (m : Mem) : OutsS base sp rs m m :=
  fun _ _ _ => rfl

theorem trans (h₁ : OutsS base sp rs m₁ m₂) (h₂ : OutsS base sp rs m₂ m₃) : OutsS base sp rs m₁ m₃ :=
  fun x hx hz => (h₂ x hx hz).trans (h₁ x hx hz)

theorem of_outs (h : Outs base rs m₁ m₂) : OutsS base sp rs m₁ m₂ := fun x hx _ => h x hx

/-- Changes within some ranges, as changes within ranges covering them. -/
theorem widen (h : OutsS base sp rs m₁ m₂)
    (hr : ∀ y : Nat, (∀ r ∈ rs', y < r.1 ∨ r.1 + r.2 ≤ y) → ∀ r ∈ rs, y < r.1 ∨ r.1 + r.2 ≤ y) :
    OutsS base sp rs' m₁ m₂ :=
  fun x hx hz => h x (hr _ hx) hz

/-- The stack a call uses is past the working space. -/
theorem zone_ofs {size : Nat} (R : CallRoom sp base size) {x : Addr} (hx : (below sp 96).Contains x 1) :
    size ≤ ofs base x := by
  have h96 := R.low
  have hsp := sp.isLt
  by_contra hc
  have hcx : (⟨base, size⟩ : Region).Contains x 1 := by
    simp only [Region.Contains, ofs] at hc ⊢; omega
  exact R.apart x hx hcx

/-- A number in the working space keeps its value. -/
theorem val32 {m m' : Mem} {size : Nat} (h : OutsS base sp rs m m') (R : CallRoom sp base size)
    (hn : base.toNat + size ≤ 2 ^ 32) {d k : Nat} (hd : ∀ r ∈ rs, d + 4 * k ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (hs : d + 4 * k ≤ size) : VG.Proof.Mont.val32 m' base d k = VG.Proof.Mont.val32 m base d k :=
  val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => h _ (fun r hr => by
    have := hd r hr
    rw [ofs_off base (by omega)]; omega) fun hz => by
      have := zone_ofs R hz
      rw [ofs_off base (by omega)] at this; omega)

theorem wordsVal {m m' : Mem} {size : Nat} (h : OutsS base sp rs m m') (R : CallRoom sp base size)
    (hn : base.toNat + size ≤ 2 ^ 32) {d k : Nat} (hd : ∀ r ∈ rs, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (hs : d + 8 * k ≤ size) : VG.Proof.Mont.wordsVal m' base d k = VG.Proof.Mont.wordsVal m base d k := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  exact h.val32 R hn (fun r hr => by have := hd r hr; omega) (by omega)

theorem readW32 {m m' : Mem} {size : Nat} (h : OutsS base sp rs m m') (R : CallRoom sp base size)
    (hn : base.toNat + size ≤ 2 ^ 32) {d : Nat} (hd : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (hs : d + 4 ≤ size) : m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  Mem.readW_congr fun i hi => h _ (fun r hr => by
    have := hd r hr
    rw [ofs_off base (by omega)]; omega) fun hz => by
      have := zone_ofs R hz
      rw [ofs_off base (by omega)] at this; omega

end OutsS

/-- Preserve the arithmetic context across writes to ranges apart from its
modulus and inverse, and to the stack below `esp`. -/
theorem Context.outsS_keep {n size m : Nat} {base : Addr} {s t : State}
    (h : Context n m base size s) (R : CallRoom (s.gpr .esp) base size) {regs : List Reg}
    {ranges : List (Nat × Nat)} (K : Keeps regs s t) (hdi : .edi ∉ regs) (hsp : .esp ∉ regs)
    (O : OutsS base (s.gpr .esp) ranges s.mem t.mem)
    (hm : ∀ r ∈ ranges, slot n 0 + 8 * n ≤ r.1 ∨ r.1 + r.2 ≤ slot n 0)
    (hi : ∀ r ∈ ranges, 4 ≤ r.1) : Context n m base size t := by
  have nw := h.scr.nowrap
  refine ⟨h.scr.of_keeps K hdi hsp, h.size_le, ?_, h.gt_one, ?_⟩
  · refine ⟨h.modulus.n0, h.modulus.mo, h.modulus.tmp, h.modulus.sep, ?_⟩
    change VG.Proof.Mont.wordsVal t.mem base (slot n 0) n = m
    rw [O.wordsVal R nw (fun r hr => by have := hm r hr; omega)
      (by have := h.modulus.mo; change slot n 0 + 8 * n ≤ size at this; omega)]
    exact h.modulus.val
  · have same := O.val32 R nw (d := 0) (k := 1) (fun r hr => Or.inl (by have := hi r hr; omega))
      (by have := h.size_le; have := slot_header n 9; simp only [contextBytes] at *; omega)
    have word : w32 t.mem base 0 = w32 s.mem base 0 := by
      simpa only [VG.Proof.Mont.val32, Nat.mul_zero, Nat.add_zero] using same
    rw [word]; exact h.inverse

end VG.Proof.Dsa.X86.Pow
