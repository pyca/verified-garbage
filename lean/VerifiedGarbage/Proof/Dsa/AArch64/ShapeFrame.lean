module

public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeMasks
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
import Mathlib.Order.RelClasses
import VerifiedGarbage.Proof.Dsa.Layout
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Framework.Contract

/-! # Memory changed by the public DSA domain-shape check -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def shapeRanges : List (Nat × Nat) := [(176, 8), (352, 16)]

theorem shape_field_sep (f : Field) (h1 : f ≠ .digestPrefixLen) (h2 : f ≠ .mask) :
    (f.offset + 8 ≤ 176 ∨ 184 ≤ f.offset) ∧ (f.offset + 8 ≤ 352 ∨ 368 ≤ f.offset) := by
  cases f <;> simp_all [Field.offset]

theorem shape_field {mem mem' : Mem} {B : Addr} (hf : Frm B shapeRanges mem mem')
    (f : Field) (h1 : f ≠ .digestPrefixLen) (h2 : f ≠ .mask) :
    word mem' B f.offset = word mem B f.offset := by
  have hs := shape_field_sep f h1 h2
  apply hf.word_eq _ (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))
  intro r hr
  simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.1
  · exact hs.2

theorem shape_source {s t : State} {B p : Addr} {Z : Nat} {bytes : List Byte} {rs : List Reg}
    (hf : Frm B shapeRanges s.mem t.mem) (hk : Keep rs s t) (hZ : 368 ≤ Z)
    (hs : Src s B Z p bytes) : Src t B Z p bytes := by
  apply hs.congrK _ hk
  apply InScr.of_frm hf
  intro r hr
  simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> omega

theorem shape_outside {mem mem' : Mem} {B : Addr} {d : Nat}
    (hf : Outside B d 8 mem mem') (hd : d = 176 ∨ d = 352 ∨ d = 360) :
    Frm B shapeRanges mem mem' := by
  intro x hx
  apply hf x
  have hfirst := hx (176, 8) (by simp [shapeRanges])
  have hsecond := hx (352, 16) (by simp [shapeRanges])
  rcases hd with rfl | rfl | rfl <;> omega

/-- Either of the check's word stores lies in the same small mutation frame. -/
theorem shape_store {mem : Mem} {B : Addr} {d : Nat} (v : BitVec 64)
    (hd : d = 176 ∨ d = 352 ∨ d = 360) : Frm B shapeRanges mem (mem.writeW (off B d) v) := by
  intro x hx
  apply writeW_outside mem B v (by rcases hd with rfl | rfl | rfl <;> decide) x
  have hfirst := hx (176, 8) (by simp [shapeRanges])
  have hsecond := hx (352, 16) (by simp [shapeRanges])
  rcases hd with rfl | rfl | rfl <;> omega

theorem shapeP_context {s : State} {B : Addr} {Z width : Nat} {head : Byte}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 width) (h9 : s.gpr .x10 = head.zeroExtend 64) :
    WP isa (.block shapeP) s fun t =>
      word t.mem B 176 = BitVec.ofNat 64 width ∧ word t.mem B Field.mask.offset = mask (decide (128 ≤ head.toNat)) ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  refine WP.mono (shapeP_ok hs hdi hZ h8 h9) fun t ⟨htm, hk⟩ => ?_
  refine ⟨?_, ?_, ?_, hk⟩
  · rw [htm, (writeW_outside _ B _ (d := Field.mask.offset) (by decide)).word (Or.inl (by decide)) (by decide)]
    exact word_writeW_self _ _ _ _
  · rw [htm, word_writeW_self]
  · rw [htm]
    exact (shape_store _ (Or.inl rfl)).trans (shape_store _ (Or.inr (Or.inr rfl)))

theorem shapeQ_context {s : State} {B : Addr} {Z width : Nat} {head : Byte} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 width) (h9 : s.gpr .x10 = head.zeroExtend 64)
    (hm : word s.mem B Field.mask.offset = mask valid) :
    WP isa (.block shapeQ) s fun t =>
      word t.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 width ∧
      word t.mem B Field.mask.offset = mask (decide (128 ≤ head.toNat) && valid) ∧
      word t.mem B 176 = word s.mem B 176 ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  refine WP.mono (shapeQ_ok hs hdi hZ h8 h9 hm) fun t ⟨htm, hk⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, hk⟩
  · rw [htm, (writeW_outside _ B _ (d := Field.mask.offset) (by decide)).word (Or.inl (by decide)) (by decide)]
    exact word_writeW_self _ _ _ _
  · rw [htm, word_writeW_self]
  · rw [htm, (writeW_outside _ B _ (d := Field.mask.offset) (by decide)).word (Or.inl (by decide)) (by decide),
      (writeW_outside _ B _ (d := Field.digestPrefixLen.offset) (by decide)).word (Or.inl (by decide)) (by decide)]
  · rw [htm]
    exact (shape_store _ (Or.inr (Or.inl rfl))).trans (shape_store _ (Or.inr (Or.inr rfl)))

end VG.Proof.Dsa.AArch64
