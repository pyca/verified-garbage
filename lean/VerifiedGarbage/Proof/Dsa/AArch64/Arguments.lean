module

public import VerifiedGarbage.Proof.Dsa.AArch64.CallHeader
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! # Preparing the three operand bindings of a DSA arithmetic call -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def argumentRanges : List (Nat × Nat) := [(128, 48)]

theorem call_argument_frame {mem mem' : Mem} {B : Addr} {sp sl : Nat}
    (hf : Frm B (callRanges sp sl) mem mem') (hsp : 16 ≤ sp ∧ sp ≤ 21) (hsl : 16 ≤ sl ∧ sl ≤ 21) :
    Frm B argumentRanges mem mem' := by
  intro x hx
  apply hf x
  intro r hr
  have h := hx (128, 48) (List.mem_singleton_self _)
  simp only [callRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> omega

theorem call_word {mem mem' : Mem} {B : Addr} {sp sl i : Nat}
    (hf : Frm B (callRanges sp sl) mem mem') (_hsp : sp < 32) (_hsl : sl < 32)
    (hi : i < 32) (h1 : i ≠ sp) (h2 : i ≠ sl) :
    word mem' B (8 * i) = word mem B (8 * i) := by
  apply hf.word_eq _ (by omega)
  intro r hr
  simp only [callRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> omega

/-- All six call-header words, expressed using the original saved fields. -/
def Arguments (mem original : Mem) (B : Addr) (a b output : Operand) : Prop :=
  word mem B (8 * arg) = pointerValue original B a.pointer ∧
  word mem B (8 * argLen) = word original B a.length.offset ∧
  word mem B (8 * arg2) = pointerValue original B b.pointer ∧
  word mem B (8 * arg2Len) = word original B b.length.offset ∧
  word mem B (8 * result) = pointerValue original B output.pointer ∧
  word mem B (8 * resultLen) = word original B output.length.offset

/-- Setting up a power, product or sum call preserves its selected child
and all saved pointers and lengths. -/
theorem arguments_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (ho : 256 ≤ o) (hhi : o + slot wx 8 ≤ Z)
    (a b output : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hout : pointerFits output.pointer) :
    WP isa (.block (Core.operand arg argLen a ++ Core.operand arg2 arg2Len b ++
      Core.operand result resultLen output)) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Arguments t.mem s.mem B a b output ∧
      (∀ f : Field, word t.mem B f.offset = word s.mem B f.offset) ∧
      Frm B argumentRanges s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  have hn := hg.scr.nowrap
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (operand_context hg hZ a ha (by decide) (by decide) (by decide) (by decide) (by decide))
    fun u ⟨hgu, hua, hual, hfieldsu, hfu, hku⟩ => ?_
  have hchildu := call_ready child hfu (by decide) (by decide) ho (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (operand_context hgu hZ b hb (by decide) (by decide) (by decide) (by decide) (by decide))
    fun v ⟨hgv, hvb, hvbl, hfieldsv, hfv, hkv⟩ => ?_
  have hchildv := call_ready hchildu hfv (by decide) (by decide) ho (by omega)
  have hfieldsv' : ∀ f : Field, word v.mem B f.offset = word s.mem B f.offset :=
    fun f => (hfieldsv f).trans (hfieldsu f)
  rw [pointerValue_congr hfieldsu] at hvb
  rw [hfieldsu b.length] at hvbl
  have hva := (call_word hfv (by decide) (by decide) (by decide) (by decide) (by decide)).trans hua
  have hval := (call_word hfv (by decide) (by decide) (by decide) (by decide) (by decide)).trans hual
  refine WP.mono (operand_context hgv hZ output hout (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨hgt, hto, htol, hfieldst, hft, hkt⟩ => ?_
  rw [pointerValue_congr hfieldsv'] at hto
  rw [hfieldsv' output.length] at htol
  refine ⟨hgt, call_ready hchildv hft (by decide) (by decide) ho (by omega), ?_,
    fun f => (hfieldst f).trans (hfieldsv' f), ?_, ((hku.trans hkv).trans hkt).mono (by decide)⟩
  · exact ⟨(call_word hft (by decide) (by decide) (by decide) (by decide) (by decide)).trans hva,
      (call_word hft (by decide) (by decide) (by decide) (by decide) (by decide)).trans hval,
      (call_word hft (by decide) (by decide) (by decide) (by decide) (by decide)).trans hvb,
      (call_word hft (by decide) (by decide) (by decide) (by decide) (by decide)).trans hvbl, hto, htol⟩
  · exact ((call_argument_frame hfu (by decide) (by decide)).trans
      (call_argument_frame hfv (by decide) (by decide))).trans
      (call_argument_frame hft (by decide) (by decide))

end VG.Proof.Dsa.AArch64
