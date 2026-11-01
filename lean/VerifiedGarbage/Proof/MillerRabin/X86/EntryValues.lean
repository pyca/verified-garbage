module

public import VerifiedGarbage.Proof.MillerRabin.X86.EntryMemory
public import VerifiedGarbage.Proof.MillerRabin.X86.Modulus
public import VerifiedGarbage.Proof.MillerRabin.X86.Data
public import VerifiedGarbage.Proof.MillerRabin.X86.TableMath
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryValues
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic
import VerifiedGarbage.Proof.Mont.X86.Compact.Prepared

/-! # The prepared contract supplies the round's native-word initial values -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.Mont

def initialValues (s : State) (j : Nat) : Nat := numAt s.mem (wsOf s) (geometry s).w j

theorem Entry.context {s t : State} (E : Entry s)
    (mem : t.mem = (entered s).mem) (workspace : (⟨wsOf s, lenOf s⟩ : Region) ∈ t.wr)
    (base : PtrAt t (wsOf s) .edi 0) : Context (geometry s) t := by
  have v := E.valid
  have header : 256 ≤ lenOf s := v.headerFit
  have layout := E.layout.2.1
  have widthBound := v.maxWidth
  refine ⟨⟨?_, ?_⟩, base, ?_, ?_, ?_⟩
  · exact workspace
  · change (wsOf s).toNat + lenOf s ≤ 2 ^ 32
    rw [E.ws_toNat]; exact E.bound
  · change w32 t.mem (wsOf s) 48 = (geometry s).w
    rw [mem, E.pushed_w32 (by omega), show 48 = 8 * 6 from rfl, Compact.header_low]
    change (geometry s).w % 2 ^ 32 = (geometry s).w
    exact Nat.mod_eq_of_lt (by omega)
  · change w32 t.mem (wsOf s) 224 = 8 * ((geometry s).w + 2)
    rw [mem, E.pushed_w32 (by omega), show 224 = 8 * 28 from rfl, Compact.header_low]
    have stride : wordAt s.mem (wsOf s) 28 = BitVec.ofNat 64 (8 * ((geometry s).w + 2)) := E.layout.2.2.2.2.2
    rw [stride, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · intro j index
    change w32 t.mem (wsOf s) (64 + 8 * j) = _
    rw [mem, E.pushed_w32 (by omega)]
    exact Compact.layout_pointer_low layout index

theorem Entry.modulus {s t : State} (E : Entry s) (mem : t.mem = (entered s).mem) :
    Modulus (geometry s) (initialValues s 0) t.mem := by
  have v := E.valid
  have header : 256 ≤ lenOf s := v.headerFit
  have candidateFit := v.arrayFit (j := 0) (by decide)
  change (geometry s).array 0 + 4 * (geometry s).words ≤ lenOf s at candidateFit
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (t.mem.readW (off (wsOf s) 48) 64).toNat = _
    rw [mem, E.pushed_read (by omega)]
    rfl
  · intro j index
    change t.mem.readW (off (wsOf s) (8 * arrWord j)) 64 = _
    rw [mem, E.pushed_read (by unfold arrWord; omega)]
    exact E.layout.2.1.2.2.2 j index
  · change val32 t.mem (wsOf s) ((geometry s).array 0) (geometry s).words = _
    rw [mem, E.pushed_val32 candidateFit]
    exact (Compact.numAt_val32 _ _ _ _).symm
  · change ((t.mem.readW (off (wsOf s) ((geometry s).array 0)) 64).toNat *
      (t.mem.readW (off (wsOf s) 56) 64).toNat + 1) % 2 ^ 64 = 0
    rw [mem, E.pushed_read (by have := v.minWidth; unfold Geometry.words at candidateFit; omega),
      E.pushed_read (by omega)]
    exact E.prepared.2.2.1

theorem Entry.data {s t : State} (E : Entry s)
    (mem : t.mem = (entered s).mem) (workspace : (⟨wsOf s, lenOf s⟩ : Region) ∈ t.wr)
    (base : PtrAt t (wsOf s) .edi 0) :
    Data (geometry s) (initialValues s) initialArrays (fun _ => 0) [] t := by
  refine ⟨E.context mem workspace base, ?_, by simp⟩
  intro j known
  have bound : j < 28 := by
    change j ∈ [0, 5, 9, 10, 27] at known
    simp only [List.mem_cons, List.not_mem_nil, or_false] at known
    rcases known with rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨bound, ?_⟩
  change val32 t.mem (wsOf s) ((geometry s).array j) (geometry s).words = _
  rw [mem, E.pushed_val32 (E.valid.arrayFit bound)]
  exact (Compact.numAt_val32 _ _ _ _).symm

end VG.Proof.MillerRabin.X86
