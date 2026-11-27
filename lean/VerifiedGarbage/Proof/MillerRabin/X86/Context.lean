module

public import VerifiedGarbage.Impl.MillerRabin.X86.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.MillerRabin.X86.Scale
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! ### `MillerRabin.X86.Pointer`, which this module and modules that import it used -/

section

/-! # Runtime prepared array pointers on i686 -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.Mont (arrAt hdrBytes)

theorem ptr_ok {s : State} {W : Addr} {L w j : Nat} (hw : Ws s W L)
    (base : PtrAt s W .edi 0) (index : j < 32) (arrayFit : arrAt w j < L)
    (headerFit : 228 ≤ L) (stride : w32 s.mem W 224 = 8 * (w + 2))
    (pointers : ∀ k < 8, w32 s.mem W (64 + 8 * k) = (W.toNat + arrAt w k) % 2 ^ 32)
    (r : Reg) (notBase : .edi ≠ r) (notTmp : .edx ≠ r) :
    WP isa (.block (ptr r j)) s fun t =>
      PtrAt t W r (arrAt w j) ∧ t.mem = s.mem ∧ Keeps [r, .edx] s t := by
  have nowrap := hw.nowrap
  unfold ptr
  split
  · rename_i short
    refine wp_movS (readSrc_ptr hw base (d := 64 + 8 * j) (by omega_using [headerFit, short])) fun t T _ => WP.block_nil ?_
    refine ⟨?_, T.mem, T.keeps.mono (by simp)⟩
    rw [PtrAt, T.gpr, Nat.zero_add]
    exact pointers j short
  · rename_i long
    simp only [List.cons_append, List.nil_append]
    refine wp_movS (readSrc_ptr hw base (d := 224) (by omega_using [headerFit])) fun a A _ => ?_
    refine wp_movS rfl fun b B _ => ?_
    have value : (b.gpr .edx).toNat = 8 * (w + 2) := by
      rw [B.other .edx notTmp, A.gpr, Nat.zero_add]; exact stride
    refine WP.block_append (WP.mono (scaleIndex_ok b r .edx notTmp j index B.gpr) fun c ⟨R, M, K⟩ => ?_)
    refine wp_addS rfl fun d D _ => wp_addS rfl fun t T _ => WP.block_nil ?_
    have baseVal : (s.gpr .edi).toNat = W.toNat := by
      rw [base, Nat.add_zero, Nat.mod_eq_of_lt (by omega_using [arrayFit, nowrap])]
    have ediC : c.gpr .edi = s.gpr .edi := by
      rw [K.1 .edi (by simpa using notBase), B.other .edi notBase, A.other .edi (by decide)]
    refine ⟨?_, T.mem.trans (D.mem.trans (M.trans (B.mem.trans A.mem))), ?_⟩
    · rw [PtrAt, T.gpr, D.gpr, R, ediC, BitVec.toNat_add, BitVec.toNat_add,
        BitVec.toNat_mul, BitVec.toNat_ofNat, show (256 : BitVec 32).toNat = 256 from rfl, value, baseVal]
      rw [Nat.mod_eq_of_lt (a := j) (by omega_using [index])]
      unfold arrAt hdrBytes at arrayFit ⊢
      omega_using []
    · exact (((A.keeps.mono (by simp)).widen B.keeps (by simp)).trans (K.mono (by simp))).trans
        ((D.keeps.mono (by simp)).trans (T.keeps.mono (by simp)))

end VG.Proof.MillerRabin.X86

end

end

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
  omega_using [step, fit]

theorem Geometry.Valid.arrayHeader {g : Geometry} (_ : g.Valid) (j : Nat) : 256 ≤ g.array j := by
  unfold Geometry.array arrAt hdrBytes
  omega_using []

theorem Geometry.Valid.headerFit {g : Geometry} (v : g.Valid) : 256 ≤ g.L := by
  exact Nat.le_trans (Nat.le_add_right 256 (28 * (8 * (g.w + 2)))) v.arraysFit

theorem Context.ptr {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (j : Nat) (index : j < 28) (r : Reg) (notBase : .edi ≠ r) (notTmp : .edx ≠ r) :
    WP isa (.block (VG.Impl.MillerRabin.X86.ptr r j)) s fun t =>
      PtrAt t g.W r (g.array j) ∧ t.mem = s.mem ∧ Keeps [r, .edx] s t :=
  ptr_ok C.ws C.base (by omega_using [index]) (by
    change g.array j < g.L
    have fit := v.arrayFit index
    have positive := v.minWidth
    unfold Geometry.words at fit
    omega_using [fit, positive]) (by have := v.headerFit; omega_using [this]) C.stride C.pointers r notBase notTmp

theorem Context.keepOutside {g : Geometry} {s t : State} (C : Context g s)
    {rs : List Reg} (K : Keeps rs s t) (base : .edi ∉ rs) {d n : Nat}
    (O : Outside g.W d n s.mem t.mem) (header : 256 ≤ d) : Context g t := by
  refine ⟨C.ws.of_keeps K, ?_, ?_, ?_, ?_⟩
  · rw [PtrAt, K.1 .edi base]; exact C.base
  · rw [O.w32 (by omega_using [header]) (by decide)]; exact C.width
  · rw [O.w32 (by omega_using [header]) (by decide)]; exact C.stride
  · intro j index
    rw [O.w32 (by omega_using [header, index]) (by omega_using [index])]; exact C.pointers j index

/-- Scratch words occupy the gaps in the read-only prepared header. -/
def scratchWord (d : Nat) : Prop :=
  d = 8 ∨ d = 12 ∨ d = 184 ∨ d = 188 ∨ d = 208 ∨ d = 212 ∨
    d = 232 ∨ d = 236 ∨ d = 240 ∨ d = 244

theorem Context.keepScalar {g : Geometry} {s t : State} (C : Context g s)
    {rs : List Reg} (K : Keeps rs s t) (base : .edi ∉ rs) {d : Nat}
    (O : Outside g.W d 4 s.mem t.mem) (scratch : scratchWord d) : Context g t := by
  have gap : d + 4 ≤ 48 ∨ 128 ≤ d ∧ d + 4 ≤ 224 ∨ 228 ≤ d := by
    unfold scratchWord at scratch
    omega_using [scratch]
  refine ⟨C.ws.of_keeps K, ?_, ?_, ?_, ?_⟩
  · rw [PtrAt, K.1 .edi base]; exact C.base
  · rw [O.w32 (by omega_using [gap]) (by decide)]; exact C.width
  · rw [O.w32 (by omega_using [gap]) (by decide)]; exact C.stride
  · intro j index
    rw [O.w32 (by omega_using [gap, index]) (by omega_using [index])]; exact C.pointers j index

theorem Context.keepMem {g : Geometry} {s t : State} (C : Context g s)
    {rs : List Reg} (K : Keeps rs s t) (base : .edi ∉ rs) (M : t.mem = s.mem) : Context g t :=
  C.keepOutside K base (d := 256) (n := 0) (by rw [M]; exact Outside.refl _ _ _ _) (by decide)

theorem Geometry.arrayBefore (g : Geometry) {i j : Nat} (index : i < j) :
    g.array i + 4 * g.words ≤ g.array j := by
  have step := Nat.mul_le_mul_right (8 * (g.w + 2)) index
  unfold Geometry.array Geometry.words arrAt hdrBytes
  rw [Nat.succ_mul] at step
  omega_using [step]

theorem Geometry.arraysApart (g : Geometry) (a b : Nat) :
    g.array a = g.array b ∨ g.array a + 4 * g.words ≤ g.array b ∨ g.array b + 4 * g.words ≤ g.array a := by
  by_cases same : a = b
  · exact Or.inl (by rw [same])
  · have step {i j : Nat} (h : i < j) : g.array i + 4 * g.words ≤ g.array j := by
      have scaled := Nat.mul_le_mul_right (8 * (g.w + 2)) h
      unfold Geometry.array Geometry.words arrAt hdrBytes
      rw [Nat.succ_mul] at scaled
      omega_using [scaled]
    rcases Nat.lt_or_gt_of_ne same with before | after
    · exact Or.inr (Or.inl (step before))
    · exact Or.inr (Or.inr (step after))

end VG.Proof.MillerRabin.X86
