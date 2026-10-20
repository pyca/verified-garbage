module

public import VerifiedGarbage.Proof.Dsa.X86_64.CallHeader
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core

/-! # Changes permitted while initializing one DSA child -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def initRanges (o wx : Nat) : List (Nat × Nat) := [(128, 16), (o, slot wx 8)]

theorem init_call_frame {B : Addr} {o wx : Nat} {mem mem' : Mem}
    (hf : Frm B (callRanges arg argLen) mem mem') : Frm B (initRanges o wx) mem mem' := by
  apply hf.widen
  intro r hr
  simp only [callRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact ⟨(128, 16), by simp [initRanges], by decide⟩

theorem init_child_frame {B : Addr} {o wx d n : Nat} {mem mem' : Mem}
    (hf : Outside (off B o) d n mem mem') (hd : d + n ≤ slot wx 8)
    (ho : o + slot wx 8 ≤ 2 ^ 64) : Frm B (initRanges o wx) mem mem' := by
  have hslot : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  apply (Frm.of_outside_off hf (by omega) (by omega)).widen
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact ⟨(o, slot wx 8), by simp [initRanges], by simp only; omega⟩

theorem init_source {s t : State} {B p : Addr} {Z o wx : Nat} {bytes : List Byte} {rs : List Reg}
    (hf : Frm B (initRanges o wx) s.mem t.mem) (hk : Keep rs s t)
    (hZ : 144 ≤ Z) (hhi : o + slot wx 8 ≤ Z) (hs : Src s B Z p bytes) : Src t B Z p bytes := by
  apply hs.congrK _ hk
  apply InScr.of_frm hf
  intro r hr
  simp only [initRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only <;> omega

theorem init_word {B : Addr} {o wx d : Nat} {mem mem' : Mem}
    (hf : Frm B (initRanges o wx) mem mem') (hd : d + 8 ≤ o)
    (ha : d + 8 ≤ 128 ∨ 144 ≤ d) (ho : o < 2 ^ 64) : word mem' B d = word mem B d := by
  apply hf.word_eq _ (by omega)
  intro r hr
  simp only [initRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ha
  · exact Or.inl hd

/-- Initializing a disjoint child preserves an already initialized modulus. -/
theorem init_ready {B : Addr} {o wx other ow m : Nat} {mi : BitVec 64} {mem mem' : Mem}
    (hf : Frm B (initRanges o wx) mem mem') (hready : ChildReady mem B other ow m mi)
    (hlo : 144 ≤ other) (hhi : other + slot ow 8 ≤ 2 ^ 64)
    (hsep : other + slot ow 8 ≤ o ∨ o + slot wx 8 ≤ other) : ChildReady mem' B other ow m mi := by
  have hslot : 256 ≤ slot ow 8 := by unfold slot hdrBytes; omega
  have he : ∀ d, d + 8 ≤ slot ow 8 → word mem' (off B other) d = word mem (off B other) d := by
    intro d hd
    rw [word_off, word_off]
    apply hf.word_eq _ (by omega)
    intro r hr
    simp only [initRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right; omega
    · rcases hsep with hsep | hsep
      · left; omega
      · right; omega
  have hn := slot_le (w := ow) (show VG.Impl.Bignum.X86_64.Public.aN < 8 by decide)
  refine ⟨hready.header.of_words (fun i hi => he _ (by omega)), ?_, ?_⟩
  · rw [wv_congr (m := mem) (m' := mem') (fun i hi => he _ (by omega))]
    exact hready.modulus
  · rw [he _ (by omega)]
    exact hready.inverse

end VG.Proof.Dsa.X86_64
