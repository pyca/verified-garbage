module

import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86.Arithmetic
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath
import VerifiedGarbage.Proof.Dsa.X86.Reduce
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Dsa.X86.Bytes
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! ### `Dsa.X86.CoreLoad`, which this module and modules that import it used -/

section

/-! # Verified component loading for DSA arithmetic calls -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

/-- Reassociating a sequence, for a lemma about its first two parts. -/
theorem wp_seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a b) c) s Q) : WP isa (.seq a (.seq b c)) s Q := by
  obtain ⟨t, s', he, hq⟩ := h
  cases he with
  | seq h₁ h₂ => cases h₁ with
    | seq h₁₁ h₁₂ => exact ⟨_, _, .seq h₁₁ (.seq h₁₂ h₂), hq⟩

/-- Every register but `edi` and `esp`: the shape checks' loops use them all. -/
def shapeClob : List Reg := [.esi, .eax, .ebx, .ecx, .edx, .ebp]

/-- What loading a component writes: its pointer and the loop's registers. -/
def loadClob : List Reg := [.esi, .eax, .ebx, .edx, .ebp]

structure ReadableComponent (s : State) (base : Addr) (p : Pointer) (len : Nat) : Prop where
  fits : (pointerValue base s p).toNat + len ≤ 2 ^ 32
  reads : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr)
    ((pointerValue base s p).setWidth 64 + BitVec.ofNat 64 d) 4

theorem coreLoad_ok {s : State} {base : Addr} {size len n out : Nat} {p : Pointer}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (ho : out + 8 * n ≤ size) (h4 : 4 ≤ len) (hlen : len ≤ 8 * n) (hw4 : len % 4 = 0)
    (hr : ReadableComponent s base p len)
    (hd : Region.Disjoint ⟨(pointerValue base s p).setWidth 64, len⟩ ⟨off base out, 8 * n⟩) :
    WP isa (Core.load n len out p) s fun t =>
      wordsVal t.mem base out n = Spec.Dsa.decodeBE
        (Spec.Rsa.bytesAt s.mem ((pointerValue base s p).setWidth 64) len) ∧
      Keeps loadClob s t ∧ Outside base out (8 * n) s.mem t.mem := by
  unfold Core.load
  refine WP.seq (WP.mono (pointer_ok hs hz p) fun u ⟨Pu, Ku, Mu⟩ => ?_)
  have hu := hs.of_keeps Ku (by decide)
  refine WP.mono (loadComponent_ok hu ho (by rw [Pu]; exact hr.fits) h4 hlen hw4
    (by intro d h; rw [Pu, Ku.2.1, Ku.2.2]; exact hr.reads d h)
    (by rw [Pu]; exact hd)) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨?_, (Ku.mono (by decide)).widen Kt, ?_⟩
  · rw [Vt, Mu, Pu]
  · rw [Mu] at Ot
    exact Ot

theorem coreLoadSlot_ok {s : State} {base : Addr} {size len n m i : Nat} {p : Pointer}
    (h : Context n m base size s) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hi : i < 9) (hi0 : i ≠ 0) (h4 : 4 ≤ len) (hlen : len ≤ 8 * n) (hw4 : len % 4 = 0)
    (hr : ReadableComponent s base p len)
    (hd : Region.Disjoint ⟨(pointerValue base s p).setWidth 64, len⟩ ⟨off base (slot n i), 8 * n⟩) :
    WP isa (Core.load n len (slot n i) p) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n i) n = Spec.Dsa.decodeBE
        (Spec.Rsa.bytesAt s.mem ((pointerValue base s p).setWidth 64) len) ∧
      Keeps loadClob s t ∧ Outside base (slot n i) (8 * n) s.mem t.mem := by
  have bound := slot_bound (n := n) hi
  have sep := slot_sep (n := n) hi0
  simp only [stride] at bound sep
  refine WP.mono (coreLoad_ok h.scr hz (by have := h.size_le; omega_using [bound, this]) h4 hlen hw4 hr hd)
    fun t ⟨V, K, O⟩ => ⟨?_, V, K, O⟩
  apply h.outside_keep K (by decide) (by decide) O
  · omega_using [sep]
  · have := slot_header n i
    omega_using [this]

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.Arithmetic`, which this module and modules that import it used -/

section

/-! # Products and sums of ordinary DSA residues -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Impl.Dsa.X86

def productRanges (n : Nat) : List (Nat × Nat) :=
  [(slot n 7, 8 * n), (slot n 6, 8 * n), (slot n 1, 8 * n), (slot n 2, 16 * n + 4)]

theorem ordinaryMul_ok {n size m : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (hr2 : wordsVal s.mem base (slot n 4) n = 2 ^ (128 * n) % m) :
    WP isa (ordinaryMul n) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n * wordsVal s.mem base (slot n 8) n % m ∧
      Outs base (productRanges n) s.mem t.mem ∧ Keeps clob s t := by
  unfold ordinaryMul
  refine WP.seq (WP.mono (context_mul_ok h (o := 7) (a := 5) (b := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hr2]; exact Nat.mod_lt _ (by have := h.gt_one; omega_using [this]))) fun u ⟨cu, Ku, ltu, Vu⟩ => ?_)
  have Au : wordsVal u.mem base (slot n 7) n = wordsVal s.mem base (slot n 5) n * 2 ^ (64 * n) % m :=
    mont_encode h.coprime ltu (by rw [Vu, hr2])
  have Bu := context_slot_val h (i := 8) (by decide) (by decide) (by decide) (by decide) Ku
  refine WP.mono (context_mul_ok cu (o := 6) (a := 8) (b := 7)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ltu)
    fun t ⟨ct, Kt, ltt, Vt⟩ => ?_
  refine ⟨ct, ?_, ?_, (OpKeep.keeps Ku).trans (OpKeep.keeps Kt)⟩
  · have v := VG.Proof.Dsa.mont_scale (out := wordsVal t.mem base (slot n 6) n)
      (input := wordsVal s.mem base (slot n 8) n) (c := wordsVal s.mem base (slot n 5) n)
      h.coprime (by rw [Vt, Au, Bu])
    rw [Nat.mod_eq_of_lt ltt, Nat.mul_comm] at v
    exact v
  · have ou : Outs base (productRanges n) s.mem u.mem := Ku.mem.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [productRanges, contextMod, accLen, words] <;> omega_using [])
    have ot : Outs base (productRanges n) u.mem t.mem := Kt.mem.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [productRanges, contextMod, accLen, words] <;> omega_using [])
    exact ou.trans ot

theorem ordinaryAdd_ok {n size m : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (ha : wordsVal s.mem base (slot n 5) n < m)
    (hb : wordsVal s.mem base (slot n 8) n < m) :
    WP isa (ordinaryAdd n) s fun t =>
      Context n m base size t ∧ OpKeep (contextMod n) base (slot n 2) (slot n 6) s t ∧
      wordsVal t.mem base (slot n 6) n =
        (wordsVal s.mem base (slot n 5) n + wordsVal s.mem base (slot n 8) n) % m :=
  WP.mono (context_add_ok h (o := 6) (a := 5) (b := 8) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by omega_using [ha, hb])) fun _ ⟨c, K, V, _⟩ => ⟨c, K, V⟩

end VG.Proof.Dsa.X86

end

end

/-! # Persistent operands across arithmetic-context updates -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem pointerValue_keep {s t : State} {base : Addr} {prefixBytes : Nat} {rs : List Reg}
    (K : Keeps rs s t) (hdi : .edi ∉ rs) (O : Outside base 0 prefixBytes s.mem t.mem)
    (hp : prefixBytes ≤ 8192) (p : Pointer) : pointerValue base t p = pointerValue base s p := by
  have field (f : Field) : t.mem.readW (off base (VG.Impl.Dsa.X86.Layout.field f)) 32 =
      s.mem.readW (off base (VG.Impl.Dsa.X86.Layout.field f)) 32 := by
    have fb := VG.Proof.Dsa.X86.Layout.field_bounds f
    have ub : VG.Impl.Dsa.X86.Layout.field f + 4 ≤ 8256 := fb.2
    apply BitVec.eq_of_toNat_eq
    exact O.w32 (by omega_using [hp, fb]) (by omega_using [ub])
  cases p with
  | input f => exact field f
  | «local» offset => simp only [pointerValue, K.1 _ hdi]
  | signatureS => simp only [pointerValue, field]

theorem ReadableComponent.keep {s t : State} {base : Addr} {prefixBytes len : Nat} {rs : List Reg} {p : Pointer}
    (R : ReadableComponent s base p len) (K : Keeps rs s t) (hdi : .edi ∉ rs)
    (O : Outside base 0 prefixBytes s.mem t.mem) (hp : prefixBytes ≤ 8192) : ReadableComponent t base p len := by
  have P := pointerValue_keep K hdi O hp p
  exact ⟨by rw [P]; exact R.fits, by rw [P, K.2.1, K.2.2]; exact R.reads⟩

theorem componentBytes_keep {s t : State} {base : Addr} {prefixBytes len : Nat} {rs : List Reg} {p : Pointer}
    (K : Keeps rs s t) (hdi : .edi ∉ rs) (O : Outside base 0 prefixBytes s.mem t.mem)
    (hp : prefixBytes ≤ 8192)
    (far : ∀ i < len, prefixBytes ≤ ofs base ((pointerValue base s p).setWidth 64 + BitVec.ofNat 64 i)) :
    Spec.Rsa.bytesAt t.mem ((pointerValue base t p).setWidth 64) len =
      Spec.Rsa.bytesAt s.mem ((pointerValue base s p).setWidth 64) len := by
  rw [pointerValue_keep K hdi O hp p]
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  exact O _ (.inr (by simpa only [Nat.zero_add] using far i (List.mem_range.mp hi)))

/-- An operand whose bytes lie outside the shared arithmetic prefix. -/
structure OperandReady (s : State) (base : Addr) (n : Nat) (p : Pointer) (len : Nat) : Prop
    extends ReadableComponent s base p len where
  apart : Region.Disjoint ⟨(pointerValue base s p).setWidth 64, len⟩ ⟨base, contextBytes n⟩

theorem OperandReady.keep {s t : State} {base : Addr} {n len : Nat} {rs : List Reg} {p : Pointer}
    (R : OperandReady s base n p len) (K : Keeps rs s t) (hdi : .edi ∉ rs)
    (O : Outside base 0 (contextBytes n) s.mem t.mem) (hn : n ≤ 48) : OperandReady t base n p len := by
  have hp : contextBytes n ≤ 8192 := Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn) (by decide)
  exact ⟨R.toReadableComponent.keep K hdi O hp, by rw [pointerValue_keep K hdi O hp p]; exact R.apart⟩

theorem OperandReady.slot {s : State} {base : Addr} {n len i : Nat} {p : Pointer}
    (R : OperandReady s base n p len) (hi : i < 9) :
    Region.Disjoint ⟨(pointerValue base s p).setWidth 64, len⟩ ⟨off base (slot n i), 8 * n⟩ := by
  have b := slot_bound (n := n) hi
  simp only [stride] at b
  exact R.apart.sub_right (Offset.sub_base base (by omega_using [b]))

theorem OperandReady.bytes {s t : State} {base : Addr} {n len : Nat} {rs : List Reg} {p : Pointer}
    (R : OperandReady s base n p len) (K : Keeps rs s t) (hdi : .edi ∉ rs)
    (O : Outside base 0 (contextBytes n) s.mem t.mem) (hn : n ≤ 48) :
    Spec.Rsa.bytesAt t.mem ((pointerValue base t p).setWidth 64) len =
      Spec.Rsa.bytesAt s.mem ((pointerValue base s p).setWidth 64) len := by
  refine componentBytes_keep K hdi O (Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn) (by decide)) ?_
  intro i hi
  have ilt : i < 2 ^ 64 := by have := R.fits; omega_using [hi, this]
  have inside : (⟨(pointerValue base s p).setWidth 64, len⟩ : Region).Contains
      ((pointerValue base s p).setWidth 64 + BitVec.ofNat 64 i) 1 := Offset.contains_base _ (by omega_using [hi]) ilt
  have outside := R.apart _ inside
  change ¬ (ofs base ((pointerValue base s p).setWidth 64 + BitVec.ofNat 64 i) + 1 ≤ contextBytes n) at outside
  omega_using [outside]

theorem slotOutside_whole {s t : State} {base : Addr} {n i : Nat}
    (O : Outside base (slot n i) (8 * n) s.mem t.mem) (hi : i < 9) :
    Outside base 0 (contextBytes n) s.mem t.mem := by
  have b := slot_bound (n := n) hi
  simp only [stride] at b
  exact O.mono (by omega_using []) (by omega_using [b])

theorem slotOutside_val {s t : State} {base : Addr} {n i j : Nat}
    (O : Outside base (slot n i) (8 * n) s.mem t.mem) (hij : j ≠ i)
    (hb : slot n j + 8 * n ≤ 2 ^ 64) :
    wordsVal t.mem base (slot n j) n = wordsVal s.mem base (slot n j) n := by
  have sep := slot_sep (n := n) hij
  simp only [stride] at sep
  exact O.wordsVal (by omega_using [sep]) hb

theorem resultKeep_whole {n : Nat} {base : Addr} {s t : State}
    (K : OpKeep (contextMod n) base (slot n 2) (slot n 6) s t) :
    Outside base 0 (contextBytes n) s.mem t.mem := by
  have b1 := slot_bound (n := n) (i := 1) (by decide)
  have b2 := slot_bound (n := n) (i := 2) (by decide)
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  simp only [stride] at b1 b2 b6
  intro x hx
  apply K.mem x
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    simp only [contextMod, accLen, VG.Impl.Mont.X86.words] <;> omega_arith

end VG.Proof.Dsa.X86
