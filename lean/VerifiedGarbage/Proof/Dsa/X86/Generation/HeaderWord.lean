module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.CompactHeader
public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.Words32

/-! Two native stores initialize one shared word without touching its neighbors. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem store_header_pair {s : State} {base : Addr} {bytes offset : Nat}
    (h : Scr s base bytes) (fit : offset + 8 ≤ bytes) :
    WP isa (.block (storeHeaderWord offset)) s fun t =>
      Scr t base bytes ∧ Outside base offset 8 s.mem t.mem ∧
      (word t.mem base offset).toNat = (s.gpr .eax).toNat + 2 ^ 32 * (s.gpr .edx).toNat ∧ Keeps [] s t := by
  have nowrap := h.nowrap
  unfold storeHeaderWord
  refine wp_storeS (h.ea (by omega)) (h.write (by omega)) fun u U => ?_
  have hu := h.of_keeps (U.keeps []) (by simp)
  refine wp_storeS (hu.ea (by omega)) (hu.write fit) fun t T => WP.block_nil ?_
  have first : Outside base offset 4 s.mem u.mem := by
    rw [U.mem]
    exact writeW32_outside _ _ _ (by omega)
  have second : Outside base (offset + 4) 4 u.mem t.mem := by
    rw [T.mem]
    exact writeW32_outside _ _ _ (by omega)
  have K : Keeps [] s t := (U.keeps []).trans (T.keeps [])
  refine ⟨h.of_keeps K (by simp), (first.mono (by omega) (by omega)).trans (second.mono (by omega) (by omega)), ?_, K⟩
  rw [word_eq_w32, second.w32 (by omega) (by omega), U.mem, w32_write_self]
  have high : w32 t.mem base (offset + 4) = (s.gpr .edx).toNat := by
    rw [T.mem, w32_write_self, congrFun U.gpr .edx]
  rw [high]

theorem store_header_word {s : State} {base : Addr} {bytes offset : Nat}
    (h : Scr s base bytes) (fit : offset + 8 ≤ bytes) (zero : s.gpr .edx = 0) :
    WP isa (.block (storeHeaderWord offset)) s fun t =>
      Scr t base bytes ∧ Outside base offset 8 s.mem t.mem ∧
      (word t.mem base offset).toNat = (s.gpr .eax).toNat ∧ Keeps [] s t := by
  refine WP.mono (store_header_pair h fit) ?_
  rintro t ⟨ht, F, value, K⟩
  rw [zero] at value
  change (word t.mem base offset).toNat = (s.gpr .eax).toNat + 2 ^ 32 * 0 at value
  rw [Nat.mul_zero, Nat.add_zero] at value
  exact ⟨ht, F, value, K⟩

end VG.Proof.Dsa.X86.Generation
