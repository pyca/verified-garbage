module

import VerifiedGarbage.Proof.MillerRabin.X86.Pointer
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Rsa.MontContract

/-! # Runtime geometry and read-only metadata of a prepared i686 round -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.Mont (arrAt hdrBytes)

structure Geometry where
  W : Addr
  L : Nat
  w : Nat

structure Geometry.Valid (g : Geometry) : Prop where
  minWidth : 4 ≤ g.w
  maxWidth : g.w ≤ 128
  arraysFit : arrAt g.w 28 ≤ g.L

def Geometry.array (g : Geometry) (j : Nat) : Nat := arrAt g.w j

def Geometry.words (g : Geometry) : Nat := 2 * g.w

structure Context (g : Geometry) (s : State) : Prop where
  ws : Ws s g.W g.L
  base : PtrAt s g.W .edi 0
  width : w32 s.mem g.W 48 = g.w
  stride : w32 s.mem g.W 224 = 8 * (g.w + 2)
  pointers : ∀ j < 8, w32 s.mem g.W (64 + 8 * j) = (g.W.toNat + g.array j) % 2 ^ 32

theorem Geometry.Valid.arrayFit {g : Geometry} (v : g.Valid) {j : Nat} (index : j < 28) :
    g.array j + 4 * g.words ≤ g.L := by
  have step := Nat.mul_le_mul_right (8 * (g.w + 2)) index
  have fit := v.arraysFit
  unfold Geometry.array Geometry.words arrAt hdrBytes at *
  rw [Nat.succ_mul] at step
  omega

theorem Geometry.Valid.arrayHeader {g : Geometry} (_ : g.Valid) (j : Nat) : 256 ≤ g.array j := by
  unfold Geometry.array arrAt hdrBytes
  omega

theorem Geometry.Valid.headerFit {g : Geometry} (v : g.Valid) : 256 ≤ g.L := by
  exact Nat.le_trans (Nat.le_add_right 256 (28 * (8 * (g.w + 2)))) v.arraysFit

theorem Context.ptr {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (j : Nat) (index : j < 28) (r : Reg) (notBase : .edi ≠ r) (notTmp : .edx ≠ r) :
    WP isa (.block (VG.Impl.MillerRabin.X86.ptr r j)) s fun t =>
      PtrAt t g.W r (g.array j) ∧ t.mem = s.mem ∧ Keeps [r, .edx] s t :=
  ptr_ok C.ws C.base (by omega) (by
    change g.array j < g.L
    have fit := v.arrayFit index
    have positive := v.minWidth
    unfold Geometry.words at fit
    omega) (by have := v.headerFit; omega) C.stride C.pointers r notBase notTmp

theorem Context.keepOutside {g : Geometry} {s t : State} (C : Context g s)
    {rs : List Reg} (K : Keeps rs s t) (base : .edi ∉ rs) {d n : Nat}
    (O : Outside g.W d n s.mem t.mem) (header : 256 ≤ d) : Context g t := by
  refine ⟨C.ws.of_keeps K, ?_, ?_, ?_, ?_⟩
  · rw [PtrAt, K.1 .edi base]; exact C.base
  · rw [O.w32 (by omega) (by decide)]; exact C.width
  · rw [O.w32 (by omega) (by decide)]; exact C.stride
  · intro j index
    rw [O.w32 (by omega) (by omega)]; exact C.pointers j index

/-- Scratch words occupy the gaps in the read-only prepared header. -/
def scratchWord (d : Nat) : Prop :=
  d = 8 ∨ d = 12 ∨ d = 184 ∨ d = 188 ∨ d = 208 ∨ d = 212 ∨
    d = 232 ∨ d = 236 ∨ d = 240 ∨ d = 244

theorem Context.keepScalar {g : Geometry} {s t : State} (C : Context g s)
    {rs : List Reg} (K : Keeps rs s t) (base : .edi ∉ rs) {d : Nat}
    (O : Outside g.W d 4 s.mem t.mem) (scratch : scratchWord d) : Context g t := by
  have gap : d + 4 ≤ 48 ∨ 128 ≤ d ∧ d + 4 ≤ 224 ∨ 228 ≤ d := by
    unfold scratchWord at scratch
    omega
  refine ⟨C.ws.of_keeps K, ?_, ?_, ?_, ?_⟩
  · rw [PtrAt, K.1 .edi base]; exact C.base
  · rw [O.w32 (by omega) (by decide)]; exact C.width
  · rw [O.w32 (by omega) (by decide)]; exact C.stride
  · intro j index
    rw [O.w32 (by omega) (by omega)]; exact C.pointers j index

theorem Context.keepMem {g : Geometry} {s t : State} (C : Context g s)
    {rs : List Reg} (K : Keeps rs s t) (base : .edi ∉ rs) (M : t.mem = s.mem) : Context g t :=
  C.keepOutside K base (d := 256) (n := 0) (by rw [M]; exact Outside.refl _ _ _ _) (by decide)

theorem Geometry.arrayBefore (g : Geometry) {i j : Nat} (index : i < j) :
    g.array i + 4 * g.words ≤ g.array j := by
  have step := Nat.mul_le_mul_right (8 * (g.w + 2)) index
  unfold Geometry.array Geometry.words arrAt hdrBytes
  rw [Nat.succ_mul] at step
  omega

theorem Geometry.arraysApart (g : Geometry) (a b : Nat) :
    g.array a = g.array b ∨ g.array a + 4 * g.words ≤ g.array b ∨ g.array b + 4 * g.words ≤ g.array a := by
  by_cases same : a = b
  · exact Or.inl (by rw [same])
  · have step {i j : Nat} (h : i < j) : g.array i + 4 * g.words ≤ g.array j := by
      have scaled := Nat.mul_le_mul_right (8 * (g.w + 2)) h
      unfold Geometry.array Geometry.words arrAt hdrBytes
      rw [Nat.succ_mul] at scaled
      omega
    rcases Nat.lt_or_gt_of_ne same with before | after
    · exact Or.inr (Or.inl (step before))
    · exact Or.inr (Or.inr (step after))

end VG.Proof.MillerRabin.X86
