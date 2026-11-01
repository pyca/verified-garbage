module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.MlKem.PolyContract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers

/-!
# ML-KEM on RISC-V: the buffers of the top-level functions

As on PPC64LE (`Proof/MlKem/PPC64LE/Lay.lean`). The top-level functions work
on a few buffers (`Lay`): `scratch` (buffer 0), the 1168 bytes below the stack
pointer (buffer 1), and their arguments; the contracts make them pairwise
disjoint (`Lay.Ok`). A region is `l` bytes at offset `o` of buffer `i`
(`Lay.R`), and two regions are disjoint when a computation on the offsets
says so (`sepB`, decided by the kernel), so what a call writes and what the
proofs keep track of are lists of triples `(i, o, l)`.

A state `s` in which the functions run their parts is `Ctx`: `s11` points to
`scratch`, and the stack pointer is the one of buffer 1. `Kept rs s s'` says
what a part changes.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64

open VG VG.RISCV64
open VG.Spec.MlKem

/-- Buffers: their pointers and sizes. -/
structure Lay where
  ptr : Nat → Addr
  sizes : List Nat

/-- Whether the regions `a` and `b` (buffer, offset, length) are within
their buffers and apart. -/
def sepB (sz : List Nat) (a b : Nat × Nat × Nat) : Bool :=
  a.1 < sz.length && b.1 < sz.length && a.2.1 + a.2.2 ≤ sz.getD a.1 0 && b.2.1 + b.2.2 ≤ sz.getD b.1 0 &&
    (a.1 != b.1 || a.2.1 + a.2.2 ≤ b.2.1 || b.2.1 + b.2.2 ≤ a.2.1)

/-- `a` is apart from every region of `W`. -/
def sepAll (sz : List Nat) (a : Nat × Nat × Nat) (W : List (Nat × Nat × Nat)) : Bool := W.all (sepB sz a)

namespace Lay

variable (L : Lay)

abbrev size (i : Nat) : Nat := L.sizes.getD i 0

/-- `l` bytes at offset `o` of buffer `i`. -/
abbrev R (i o l : Nat) : Region := ⟨L.ptr i + BitVec.ofNat 64 o, l⟩

/-- The regions of the triples `W`. -/
abbrev RL (W : List (Nat × Nat × Nat)) : List Region := W.map fun w => L.R w.1 w.2.1 w.2.2

/-- The buffers fit in the address space and are pairwise disjoint. -/
structure Ok : Prop where
  fit : ∀ i < L.sizes.length, (L.ptr i).toNat + L.size i ≤ 2 ^ 64
  disj : ∀ i < L.sizes.length, ∀ j < L.sizes.length, i ≠ j →
    (⟨L.ptr i, L.size i⟩ : Region).Disjoint ⟨L.ptr j, L.size j⟩

variable {L}

theorem R_sub {i o l : Nat} (h : o + l ≤ L.size i) : Region.Sub (L.R i o l) ⟨L.ptr i, L.size i⟩ :=
  Offset.sub_base _ h

theorem disj (hL : L.Ok) {i o l j o' l' : Nat} (h : sepB L.sizes (i, o, l) (j, o', l') = true) :
    (L.R i o l).Disjoint (L.R j o' l') := by
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hla⟩, hlb⟩, hs⟩ := h
  by_cases e : i = j
  · subst e
    have hf : (L.ptr i).toNat + L.sizes.getD i 0 ≤ 2 ^ 64 := hL.fit i ha
    have hs' : o + l ≤ o' ∨ o' + l' ≤ o := by
      rcases hs with (hs | hs) | hs
      · exact absurd rfl hs
      · exact .inl hs
      · exact .inr hs
    have := (L.ptr i).isLt
    exact Offset.disjoint _ hs' (by omega) (by omega)
  · exact ((hL.disj _ ha _ hb e).sub_left (R_sub hla)).sub_right (R_sub hlb)

theorem disjAll (hL : L.Ok) {i o l : Nat} {W : List (Nat × Nat × Nat)} (h : sepAll L.sizes (i, o, l) W = true) :
    ∀ r ∈ L.RL W, (L.R i o l).Disjoint r := by
  intro r hr
  obtain ⟨⟨j, o', l'⟩, hw, rfl⟩ := List.mem_map.mp hr
  exact disj hL (List.all_eq_true.mp h _ hw)

/-- A part of a buffer the state may access. -/
theorem covers {i o l : Nat} {ws : List Region} (hin : ⟨L.ptr i, L.size i⟩ ∈ ws) (h : o + l ≤ L.size i) :
    Covers [L.R i o l] ws :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, hin, o, rfl, h⟩

theorem polyIs_keep (hL : L.Ok) {W : List (Nat × Nat × Nat)} {m m' : Mem} (hf : Frame (L.RL W) m m')
    {i o : Nat} (h : sepAll L.sizes (i, o, 1024) W = true) {f : Poly}
    (hp : PolyIs m (L.ptr i + BitVec.ofNat 64 o) f) : PolyIs m' (L.ptr i + BitVec.ofNat 64 o) f :=
  polyIs_frame hf (disjAll hL h) hp

theorem bytes_keep (hL : L.Ok) {W : List (Nat × Nat × Nat)} {m m' : Mem} (hf : Frame (L.RL W) m m')
    {i o l : Nat} (h : sepAll L.sizes (i, o, l) W = true) (hl : l ≤ 2 ^ 64) :
    Spec.Sha3.bytesAt m' (L.ptr i + BitVec.ofNat 64 o) l = Spec.Sha3.bytesAt m (L.ptr i + BitVec.ofNat 64 o) l :=
  bytesAt_frame hf (disjAll hL h) hl

theorem dword_keep (hL : L.Ok) {W : List (Nat × Nat × Nat)} {m m' : Mem} (hf : Frame (L.RL W) m m')
    {i o : Nat} (h : sepAll L.sizes (i, o, 8) W = true) :
    m'.readW (L.ptr i + BitVec.ofNat 64 o) 64 = m.readW (L.ptr i + BitVec.ofNat 64 o) 64 :=
  hf.readW (Region.contains_self _ _) (disjAll hL h) (by decide)

/-- `Ok` from the disjointness of the buffers `i < j`. -/
theorem ok_of (hfit : ∀ i < L.sizes.length, (L.ptr i).toNat + L.size i ≤ 2 ^ 64)
    (hd : ∀ i < L.sizes.length, ∀ j < L.sizes.length, i < j →
      (⟨L.ptr i, L.size i⟩ : Region).Disjoint ⟨L.ptr j, L.size j⟩) : L.Ok := by
  refine ⟨hfit, fun i hi j hj hij => ?_⟩
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact hd i hi j hj h
  · exact (hd j hj i hi h).symm

end Lay

/-! ## What changes -/

/-- `s'` differs from `s` only in memory within `rs` and in registers that
are not callee-saved. -/
structure Kept (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem Kept.refl (rs : List Region) (s : State) : Kept rs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Kept.trans {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : Kept rs s₁ s₂) (h₂ : Kept rs s₂ s₃) :
    Kept rs s₁ s₃ :=
  ⟨fun r hr => by rw [h₂.cs r hr, h₁.cs r hr], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], h₁.frame.trans h₂.frame⟩

theorem Kept.mono {rs rs' : List Region} {s s' : State} (h : Kept rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Kept rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.mono hs⟩

/-- The same, for regions given by triples. -/
theorem Kept.monoL {L : Lay} {W W' : List (Nat × Nat × Nat)} {s s' : State} (h : Kept (L.RL W) s s')
    (hs : ∀ w ∈ W, w ∈ W') : Kept (L.RL W') s s' :=
  h.mono fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact List.mem_map.mpr ⟨w, hs w hw, rfl⟩

/-- A state that differs only in registers other than the callee-saved ones. -/
structure Only (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Only.kept {s s' : State} (h : Only s s') (rs : List Region) : Kept rs s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, by rw [h.mem]; exact Frame.refl _ _⟩

theorem Only.trans {s₁ s₂ s₃ : State} (h₁ : Only s₁ s₂) (h₂ : Only s₂ s₃) : Only s₁ s₃ :=
  ⟨fun r hr => by rw [h₂.cs r hr, h₁.cs r hr], by rw [h₂.mem, h₁.mem], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], by rw [h₂.sp, h₁.sp]⟩

theorem Kept.only {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : Kept rs s₁ s₂) (h₂ : Only s₂ s₃) :
    Kept rs s₁ s₃ := h₁.trans (h₂.kept rs)

/-! ## The setting of the parts -/

/-- `s` runs a part of a top-level function: `scratch` (buffer 0, writable,
of which the parts use the first 32768 bytes) in `s11`, and the 1168 bytes
below the stack pointer (buffer 1), the stack pointer 16-byte aligned and
`scratch` 8-byte aligned. -/
structure Ctx (L : Lay) (s : State) : Prop where
  ok : L.Ok
  sz0 : 32768 ≤ L.size 0
  sz1 : L.size 1 = 1168
  len : 2 ≤ L.sizes.length
  s11 : s.gpr .s11 = L.ptr 0
  sp1168 : 1168 ≤ s.sp.toNat
  al : s.sp.toNat % 16 = 0
  al0 : (L.ptr 0).toNat % 8 = 0
  sp : L.ptr 1 = s.sp - BitVec.ofNat 64 1168
  cw : (⟨L.ptr 0, L.size 0⟩ : Region) ∈ s.wr

theorem Ctx.bel {L : Lay} {s : State} (h : Ctx L s) : below s.sp 1168 = L.R 1 0 1168 := by
  simp only [below, Lay.R, h.sp, BitVec.add_zero]

theorem Ctx.kept {L : Lay} {s s' : State} (h : Ctx L s) {rs : List Region} (hk : Kept rs s s') : Ctx L s' :=
  ⟨h.ok, h.sz0, h.sz1, h.len, by rw [hk.cs .s11 (by decide), h.s11], by rw [hk.sp]; exact h.sp1168,
    by rw [hk.sp]; exact h.al, h.al0, by rw [hk.sp]; exact h.sp, by rw [hk.wr]; exact h.cw⟩

theorem Ctx.only {L : Lay} {s s' : State} (h : Ctx L s) (hk : Only s s') : Ctx L s' := h.kept (hk.kept [])

/-- A part of `scratch` the state may write. -/
theorem Ctx.cs {L : Lay} {s : State} (h : Ctx L s) {o l : Nat} (hl : o + l ≤ 32768) :
    Covers [L.R 0 o l] s.wr := Lay.covers h.cw (Nat.le_trans hl h.sz0)

theorem Ctx.fit {L : Lay} {s : State} (h : Ctx L s) : (L.ptr 0).toNat + 32768 ≤ 2 ^ 64 := by
  have := h.ok.fit 0 (by have := h.len; omega); have := h.sz0; omega

theorem Ctx.disj {L : Lay} {s : State} (h : Ctx L s) {a b : Nat × Nat × Nat} (hs : sepB L.sizes a b = true) :
    (L.R a.1 a.2.1 a.2.2).Disjoint (L.R b.1 b.2.1 b.2.2) := Lay.disj h.ok hs

end VG.Proof.MlKem.RISCV64
