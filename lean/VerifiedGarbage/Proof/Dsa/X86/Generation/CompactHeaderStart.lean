module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HeaderWord

/-! Initialize the public limb count and compact stride before its pointers. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem compact_header_start {s : State} {base : Addr} {bytes w : Nat}
    (h : Scr s base bytes) (head : 256 ≤ bytes) (width : w ≤ 128) :
    WP isa (.block (compactHeaderStart w)) s fun t =>
      Scr t base bytes ∧ Outside base 0 256 s.mem t.mem ∧
      (word t.mem base 48).toNat = w ∧ (word t.mem base 224).toNat = 8 * (w + 2) ∧
      t.gpr .edx = 0 ∧ Keeps [.eax, .edx] s t := by
  unfold compactHeaderStart
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS rfl fun a A _ => wp_movS rfl fun b B _ => ?_
  have Kb : Keeps [.eax, .edx] s b := (A.keeps.mono (by decide)).trans (B.keeps.mono (by decide))
  have mem : b.mem = s.mem := B.mem.trans A.mem
  have hb := h.of_keeps Kb (by decide)
  refine WP.block_append (WP.mono (store_header_word hb (offset := 48) (by omega)
    (by rw [B.other .edx (by decide), A.gpr])) ?_)
  rintro c ⟨hc, F, count, Kc⟩
  rw [B.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at count
  rw [mem] at F
  refine wp_movS rfl fun d D _ => ?_
  have hd := hc.of_keeps D.keeps (by decide)
  have zero : d.gpr .edx = 0 := by rw [D.other .edx (by decide), Kc.1 .edx (by simp), B.other .edx (by decide), A.gpr]
  refine WP.mono (store_header_word hd (offset := 224) (by omega) zero) ?_
  rintro t ⟨ht, F', stride, Kt⟩
  rw [D.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at stride
  rw [D.mem] at F'
  refine ⟨ht, (F.mono (by omega) (by omega)).trans (F'.mono (by omega) (by omega)), ?_, stride,
    (Kt.1 .edx (by simp)).trans zero,
    ((Kb.trans (Kc.mono (by simp))).trans (D.keeps.mono (by decide))).trans (Kt.mono (by simp))⟩
  rw [F'.word (by omega) (by omega)]
  exact count

end VG.Proof.Dsa.X86.Generation
