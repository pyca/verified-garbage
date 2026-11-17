module

public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Dsa.X86.SaveArgument
import VerifiedGarbage.Proof.Dsa.X86.Layout
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Dsa.X86.SavedFrame

/-! ### `Dsa.X86.HeaderFrame`, which this module and modules that import it used -/

section

/-! # Disjoint fields in the saved argument header -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem field_separate {f other : Field} (h : f ≠ other) :
    Layout.field f + 4 ≤ Layout.field other ∨ Layout.field other + 4 ≤ Layout.field f := by
  cases f <;> cases other <;> simp_all [Layout.field]

theorem field_keep {s t : State} {base : Addr} {f other : Field}
    (O : Outside base (Layout.field f) 4 s.mem t.mem) (h : other ≠ f) :
    pointerValue base t (.input other) = pointerValue base s (.input other) := by
  have B := VG.Proof.Dsa.X86.Layout.field_bounds other
  have H := O.val32 (k := 1) (field_separate h) (by have : Layout.saved = 8256 := rfl; omega_using [B, this])
  apply BitVec.eq_of_toNat_eq
  simpa only [val32, w32, pointerValue, Nat.mul_zero, Nat.add_zero] using H

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.KeyPointers`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.KeyPointerStep`, which this module and modules that import it used -/

section

/-! # Advancing and saving a packed-key component pointer -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem addPointer_ok {s : State} {base : Addr} {size : Nat} (length dest : Field)
    (hs : Scr s base size) (hz : Layout.saved ≤ size) :
    WP isa (.block (Entry.addPointer length dest)) s fun t =>
      t.gpr .eax = s.gpr .eax + pointerValue base s (.input length) ∧
      pointerValue base t (.input dest) = s.gpr .eax + pointerValue base s (.input length) ∧
      Keeps [.eax] s t ∧ Outside base (Layout.field dest) 4 s.mem t.mem := by
  have B := VG.Proof.Dsa.X86.Layout.field_bounds dest
  have L := VG.Proof.Dsa.X86.Layout.field_bounds length
  unfold Entry.addPointer
  refine wp_addS (readSrc_sc hs (by omega_using [hz, L])) fun u su _ => ?_
  have hu := hs.of_keeps su.keeps (by decide)
  refine wp_storeS (hu.ea (by omega_using [hz, B])) (hu.write (by omega_using [hz, B])) fun t ut => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [ut.gpr, su.gpr]; rfl
  · change t.mem.readW (off base (Layout.field dest)) 32 = _
    rw [ut.mem, Mem.readW_writeW_self32, su.gpr]; rfl
  · exact su.keeps.trans (ut.keeps [.eax])
  · rw [ut.mem, su.mem]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega_using [hz, B, this])

end VG.Proof.Dsa.X86

end

end

/-! # Unpacking the p, q, g, y, and x pointers from a packed key -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem keyPointers_ok {s : State} {base : Addr} {size : Nat} {key plen qlen : BitVec 32}
    (hs : Scr s base size) (hz : Layout.saved ≤ size)
    (hp : pointerValue base s (.input .p) = key)
    (hpl : pointerValue base s (.input .pLen) = plen)
    (hql : pointerValue base s (.input .qLen) = qlen) :
    WP isa (.block Entry.keyPointers) s fun t =>
      pointerValue base t (.input .q) = key + plen ∧
      pointerValue base t (.input .g) = key + plen + qlen ∧
      pointerValue base t (.input .y) = key + plen + qlen + plen ∧
      pointerValue base t (.input .x) = key + plen + qlen + plen + plen ∧
      Keeps [.eax] s t ∧
      Outs base [(Layout.field .q, 4), (Layout.field .g, 4), (Layout.field .y, 4), (Layout.field .x, 4)] s.mem t.mem := by
  have B := VG.Proof.Dsa.X86.Layout.field_bounds .p
  unfold Entry.keyPointers
  simp only [List.append_assoc, List.singleton_append]
  refine wp_movS (readSrc_sc hs (by omega_using [hz, B])) fun u U _ => ?_
  have hu := hs.of_keeps U.keeps (by decide)
  refine WP.block_append (WP.mono (addPointer_ok .pLen .q hu hz) fun s1 ⟨A1, V1, K1, O1⟩ => ?_)
  have P0 : pointerValue base u (.input .pLen) = plen := by simpa only [pointerValue, U.mem] using hpl
  have Q1 : pointerValue base s1 (.input .qLen) = qlen := by
    rw [field_keep O1 (by decide)]
    simpa only [pointerValue, U.mem] using hql
  have X1 : s1.gpr .eax = key + plen := by rw [A1, P0, U.gpr]; exact congrArg (· + plen) hp
  refine WP.block_append (WP.mono (addPointer_ok .qLen .g (hu.of_keeps K1 (by decide)) hz)
    fun s2 ⟨A2, V2, K2, O2⟩ => ?_)
  have X2 : s2.gpr .eax = key + plen + qlen := by rw [A2, X1, Q1]
  have P2 : pointerValue base s2 (.input .pLen) = plen := by
    rw [field_keep O2 (by decide), field_keep O1 (by decide), P0]
  have K12 := K1.trans K2
  refine WP.block_append (WP.mono (addPointer_ok .pLen .y (hu.of_keeps K12 (by decide)) hz)
    fun s3 ⟨A3, V3, K3, O3⟩ => ?_)
  have X3 : s3.gpr .eax = key + plen + qlen + plen := by rw [A3, X2, P2]
  have P3 : pointerValue base s3 (.input .pLen) = plen := by rw [field_keep O3 (by decide), P2]
  refine WP.mono (addPointer_ok .pLen .x (hu.of_keeps (K12.trans K3) (by decide)) hz)
    fun t ⟨_, V4, K4, O4⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, U.keeps.trans (((K12).trans K3).trans K4), ?_⟩
  · rw [field_keep O4 (by decide), field_keep O3 (by decide), field_keep O2 (by decide), V1, P0, U.gpr]
    exact congrArg (· + plen) hp
  · rw [field_keep O4 (by decide), field_keep O3 (by decide), V2, X1, Q1]
  · rw [field_keep O4 (by decide), V3, X2, P2]
  · rw [V4, X3, P3]
  · rw [U.mem] at O1
    exact (((Outs.of_outside O1 (by simp)).trans (Outs.of_outside O2 (by simp))).trans
      (Outs.of_outside O3 (by simp))).trans (Outs.of_outside O4 (by simp))

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.EntryFrame`, which this module and modules that import it used -/

section

/-! # Precise header frames for packed-key pointer installation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def keyPointerRanges : List (Nat × Nat) :=
  [(Layout.field .q, 4), (Layout.field .g, 4), (Layout.field .y, 4), (Layout.field .x, 4)]

theorem keyPointerFrame_header {base : Addr} {m m' : Mem} (O : Outs base keyPointerRanges m m') :
    Outside base 8192 64 m m' := by
  intro a ha
  apply O a
  intro pair hp
  simp only [keyPointerRanges, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp only [Layout.field] <;> omega_using [ha]

theorem keyPointerFrame_field {base : Addr} {s t : State} {f : Field}
    (O : Outs base keyPointerRanges s.mem t.mem) (hf : f ∉ [.q, .g, .y, .x]) :
    pointerValue base t (.input f) = pointerValue base s (.input f) := by
  have B := VG.Proof.Dsa.X86.Layout.field_bounds f
  have H : val32 t.mem base (Layout.field f) 1 = val32 s.mem base (Layout.field f) 1 := by
    apply O.val32
    · intro pair hp
      simp only [keyPointerRanges, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact field_separate (f := f) (other := .q) (by intro he; subst f; exact hf (by simp))
      · exact field_separate (f := f) (other := .g) (by intro he; subst f; exact hf (by simp))
      · exact field_separate (f := f) (other := .y) (by intro he; subst f; exact hf (by simp))
      · exact field_separate (f := f) (other := .x) (by intro he; subst f; exact hf (by simp))
    · have H : Layout.saved = 8256 := rfl
      omega_using [B, H]
  apply BitVec.eq_of_toNat_eq
  simpa only [val32, w32, pointerValue, Nat.mul_zero, Nat.add_zero] using H

theorem saved_header {base : Addr} {m m' : Mem} {regs : Reg → BitVec 32}
    (O : Outside base 8192 64 m m') (S : Saved m (off base) regs Entry.savedRegisters) :
    Saved m' (off base) regs Entry.savedRegisters := by
  intro pair hp
  have B := saved_bounds hp
  have H := O.val32 (d := pair.2) (k := 1) (.inr (by omega_using [B])) (by omega_using [B])
  have V : m'.readW (off base pair.2) 32 = m.readW (off base pair.2) 32 := by
    apply BitVec.eq_of_toNat_eq
    simpa only [val32, w32, Nat.mul_zero, Nat.add_zero] using H
  exact V.trans (S pair hp)

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.SaveArguments`, which this module and modules that import it used -/

section

/-! # Installing a list of stack arguments into distinct persistent fields -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem saveArguments_ok (args : List (Nat × Field)) {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hz : Layout.saved ≤ size) (distinct : (args.map Prod.snd).Nodup)
    (inputs : ∀ a ∈ args, StackArgument s base size a.1) :
    WP isa (.block (Entry.saveArguments args)) s fun t =>
      (∀ a ∈ args, pointerValue base t (.input a.2) = stackValue s a.1) ∧
      (∀ f, f ∉ args.map Prod.snd → pointerValue base t (.input f) = pointerValue base s (.input f)) ∧
      Keeps [.eax] s t ∧ Outside base 8192 64 s.mem t.mem := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨by simp, by simp, Keeps.refl _ _, Outside.refl _ _ _ _⟩
  | cons a args ih =>
    have D : a.2 ∉ args.map Prod.snd ∧ (args.map Prod.snd).Nodup := by
      simpa only [List.map_cons, List.nodup_cons] using distinct
    have A := inputs a List.mem_cons_self
    have B := VG.Proof.Dsa.X86.Layout.field_bounds a.2
    have hi : Layout.field a.2 + 4 ≤ 8256 := B.2
    change WP isa (.block (Entry.saveArgument a.1 a.2 ++ Entry.saveArguments args)) s _
    refine WP.block_append (WP.mono (saveArgument_ok a.2 hs hz A.readSrc) fun u ⟨V, K, O⟩ => ?_)
    have Oheader : Outside base 8192 64 s.mem u.mem := O.mono B.1 (by omega_using [hi])
    have Owhole : Outside base 0 size s.mem u.mem := O.mono (Nat.zero_le _) (by omega_using [hz, B])
    refine WP.mono (ih (hs.of_keeps K (by decide)) D.2
      (fun b hb => (inputs b (List.mem_cons_of_mem _ hb)).keep K (by decide))) fun t ⟨Values, Other, Keep, Frame⟩ => ?_
    refine ⟨?_, ?_, K.trans Keep, Oheader.trans Frame⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [Other b.2 D.1, V]
      · rw [Values b hb]
        exact (inputs b (List.mem_cons_of_mem _ hb)).value_keep K (by decide) Owhole
    · intro f hf
      have H : f ≠ a.2 ∧ f ∉ args.map Prod.snd := by
        simpa only [List.map_cons, List.mem_cons, not_or] using hf
      rw [Other f H.2]
      exact field_keep O H.1

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.OpenScratch`, which this module and modules that import it used -/

section

/-! # Establishing the arithmetic workspace while preserving the caller ABI -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem openScratch_precise {s : State} {base : Addr} {size arg : Nat} {ptr : BitVec 32}
    (read : readSrc s (.mem (Entry.argument arg)) = some ptr)
    (hb : ptr.setWidth 64 = base) (hf : ptr.toNat + size ≤ 2 ^ 32) (hz : 8272 ≤ size)
    (hw : (⟨base, size⟩ : Region) ∈ s.wr) (stk : StkOk (s.gpr .esp) base size) :
    WP isa (.block (Entry.openScratch arg)) s fun t =>
      Scr t base size ∧ Saved t.mem (off base) s.gpr Entry.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧ Outside base 0 8272 s.mem t.mem := by
  unfold Entry.openScratch
  simp only [List.singleton_append]
  refine wp_movS read fun u U _ => ?_
  refine WP.block_append (WP.mono (entrySave_precise (base := base) (size := size) (by rw [U.gpr]; exact hb)
    (by rw [U.gpr]; exact hf) hz (by rw [U.wr]; exact hw)) fun v ⟨G, Rd, Wr, S, F⟩ => ?_)
  refine wp_movS rfl fun t T _ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [T.gpr, G, U.gpr]; exact hb
    · rw [T.wr, Wr, U.wr]; exact hw
    · rw [← hb, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans ptr.isLt (by decide))]
      exact hf
    · rw [T.other _ (by decide), G, U.other _ (by decide)]
      exact stk
  · intro p hp
    rw [T.mem, S p hp]
    have H : p.1 ≠ .eax := by
      simp only [Entry.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    exact U.other _ H
  · refine ⟨?_, ?_, ?_⟩
    · intro reg hr
      rw [T.other reg (by intro H; subst reg; exact hr (by simp)), G]
      exact U.other reg (by intro H; subst reg; exact hr (by simp))
    · rw [T.rd, Rd, U.rd]
    · rw [T.wr, Wr, U.wr]
  · intro a ha
    rw [T.mem]
    have H : ¬ InRegions [⟨base, 8272⟩] a 1 := by
      simp only [InRegions, List.mem_singleton, exists_eq_left, Region.Contains]
      change ¬ (ofs base a + 1 ≤ 8272)
      omega_using [ha]
    exact (F a (by intro reg hreg hcontains; exact H ⟨reg, hreg, hcontains⟩)).trans (congrFun U.mem a)

end VG.Proof.Dsa.X86

end

end

/-! # Complete cdecl argument installation and packed-key pointer expansion -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem installArguments_precise (args : List (Nat × Field)) {s : State} {base : Addr}
    {size scratchArg keyArg pLenArg qLenArg : Nat} {ptr : BitVec 32}
    (read : readSrc s (.mem (Entry.argument scratchArg)) = some ptr)
    (hb : ptr.setWidth 64 = base) (hf : ptr.toNat + size ≤ 2 ^ 32) (hz : 8272 ≤ size)
    (hw : (⟨base, size⟩ : Region) ∈ s.wr) (stk : StkOk (s.gpr .esp) base size)
    (distinct : (args.map Prod.snd).Nodup)
    (inputs : ∀ a ∈ args, StackArgument s base size a.1)
    (fields : ∀ a ∈ args, a.2 ∉ [.q, .g, .y, .x])
    (keyMem : (keyArg, .p) ∈ args) (pLenMem : (pLenArg, .pLen) ∈ args) (qLenMem : (qLenArg, .qLen) ∈ args) :
    WP isa (.block (Entry.openScratch scratchArg ++ Entry.saveArguments args ++ Entry.keyPointers)) s fun t =>
      Scr t base size ∧ Saved t.mem (off base) s.gpr Entry.savedRegisters ∧
      (∀ a ∈ args, pointerValue base t (.input a.2) = stackValue s a.1) ∧
      pointerValue base t (.input .q) = stackValue s keyArg + stackValue s pLenArg ∧
      pointerValue base t (.input .g) = stackValue s keyArg + stackValue s pLenArg + stackValue s qLenArg ∧
      pointerValue base t (.input .y) = stackValue s keyArg + stackValue s pLenArg + stackValue s qLenArg + stackValue s pLenArg ∧
      pointerValue base t (.input .x) = stackValue s keyArg + stackValue s pLenArg + stackValue s qLenArg + stackValue s pLenArg + stackValue s pLenArg ∧
      Keeps [.eax, .edi] s t ∧ Outside base 0 8272 s.mem t.mem := by
  have savedSize : Layout.saved ≤ size := by change 8256 ≤ size; omega_using [hz]
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (openScratch_precise read hb hf hz hw stk) fun s1 ⟨Sc1, S1, K1, O1⟩ => ?_)
  refine WP.block_append (WP.mono (saveArguments_ok args Sc1 savedSize distinct
    (fun a ha => (inputs a ha).keep K1 (by decide))) fun s2 ⟨Values, _, K2, O2⟩ => ?_)
  have Sc2 := Sc1.of_keeps K2 (by decide)
  have Original (a : Nat × Field) (ha : a ∈ args) : pointerValue base s2 (.input a.2) = stackValue s a.1 :=
    (Values a ha).trans ((inputs a ha).value_keep K1 (by decide) (O1.mono (Nat.le_refl _) (by omega_using [hz])))
  refine WP.mono (keyPointers_ok (key := stackValue s keyArg) (plen := stackValue s pLenArg) (qlen := stackValue s qLenArg)
    Sc2 savedSize (Original (keyArg, .p) keyMem) (Original (pLenArg, .pLen) pLenMem) (Original (qLenArg, .qLen) qLenMem))
    fun t ⟨Q, G, Y, X, K3, O3⟩ => ?_
  have Oheader := keyPointerFrame_header O3
  refine ⟨Sc2.of_keeps K3 (by decide), saved_header Oheader (saved_header O2 S1), ?_, Q, G, Y, X,
    K1.trans ((K2.trans K3).mono (by decide)), ?_⟩
  · intro a ha
    exact (keyPointerFrame_field O3 (fields a ha)).trans (Original a ha)
  · exact O1.trans ((O2.trans Oheader).mono (by omega_using []) (by omega_using []))

theorem installArguments_ok (args : List (Nat × Field)) {s : State} {base : Addr}
    {size scratchArg keyArg pLenArg qLenArg : Nat} {ptr : BitVec 32}
    (read : readSrc s (.mem (Entry.argument scratchArg)) = some ptr)
    (hb : ptr.setWidth 64 = base) (hf : ptr.toNat + size ≤ 2 ^ 32) (hz : 8272 ≤ size)
    (hw : (⟨base, size⟩ : Region) ∈ s.wr) (stk : StkOk (s.gpr .esp) base size)
    (distinct : (args.map Prod.snd).Nodup)
    (inputs : ∀ a ∈ args, StackArgument s base size a.1)
    (fields : ∀ a ∈ args, a.2 ∉ [.q, .g, .y, .x])
    (keyMem : (keyArg, .p) ∈ args) (pLenMem : (pLenArg, .pLen) ∈ args) (qLenMem : (qLenArg, .qLen) ∈ args) :
    WP isa (.block (Entry.openScratch scratchArg ++ Entry.saveArguments args ++ Entry.keyPointers)) s fun t =>
      Scr t base size ∧ Saved t.mem (off base) s.gpr Entry.savedRegisters ∧
      (∀ a ∈ args, pointerValue base t (.input a.2) = stackValue s a.1) ∧
      pointerValue base t (.input .q) = stackValue s keyArg + stackValue s pLenArg ∧
      pointerValue base t (.input .g) = stackValue s keyArg + stackValue s pLenArg + stackValue s qLenArg ∧
      pointerValue base t (.input .y) = stackValue s keyArg + stackValue s pLenArg + stackValue s qLenArg + stackValue s pLenArg ∧
      pointerValue base t (.input .x) = stackValue s keyArg + stackValue s pLenArg + stackValue s qLenArg + stackValue s pLenArg + stackValue s pLenArg ∧
      Keeps [.eax, .edi] s t ∧ Outside base 0 size s.mem t.mem :=
  WP.mono (installArguments_precise args read hb hf hz hw stk distinct inputs fields keyMem pLenMem qLenMem)
    fun _ ⟨S,V,A,Q,G,Y,X,K,O⟩ => ⟨S,V,A,Q,G,Y,X,K,O.mono (Nat.le_refl _) (by omega_using [hz])⟩

end VG.Proof.Dsa.X86
