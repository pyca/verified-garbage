module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HeaderWord

/-! Each compact array pointer is a complete zero-extended native address. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Spec.Rsa.Mont (arrAt)

theorem compact_header_pointer {s : State} {base : Addr} {bytes w j : Nat}
    (h : Scr s base bytes) (head : 256 ≤ bytes) (index : j < 8)
    (fit : arrAt w j + 1 ≤ bytes) (zero : s.gpr .edx = 0) :
    WP isa (.block (compactHeaderPointer w j)) s fun t =>
      Scr t base bytes ∧ Outside base (64 + 8 * j) 8 s.mem t.mem ∧
      word t.mem base (64 + 8 * j) = off base (arrAt w j) ∧
      t.gpr .edx = 0 ∧ Keeps [.eax] s t := by
  have nowrap := h.nowrap
  have offsetSmall : arrAt w j < 2 ^ 32 := by omega
  unfold compactHeaderPointer
  simp only [List.cons_append, List.nil_append]
  refine wp_movS rfl fun a A _ => wp_addS rfl fun b B _ => ?_
  have ptr : (b.gpr .eax).toNat = base.toNat + arrAt w j := by
    rw [B.gpr, BitVec.toNat_add, A.gpr, h.edi_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt offsetSmall, Nat.mod_eq_of_lt (by omega)]
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  have mem : b.mem = s.mem := B.mem.trans A.mem
  have hb := h.of_keeps K (by decide)
  have zb : b.gpr .edx = 0 := (K.1 .edx (by decide)).trans zero
  refine WP.mono (store_header_word hb (offset := 64 + 8 * j) (by omega) zb) ?_
  rintro t ⟨ht, F, value, K'⟩
  rw [mem] at F
  rw [ptr] at value
  refine ⟨ht, F, ?_, (K'.1 .edx (by simp)).trans zb, K.trans (K'.mono (by simp))⟩
  apply BitVec.eq_of_toNat_eq
  rw [value]
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show arrAt w j < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]

end VG.Proof.Dsa.X86.Generation
