module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.TrialTable
public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.RsaKeyGen.Table32

/-! The native initializer writes exactly the shared packed table. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.RsaKeyGen

theorem trial_table {s : State} {base : Addr} {size offset : Nat} (ws : Scr s base size) :
    ∀ count, count ≤ 512 → offset + 4 * count ≤ size →
    WP isa (.block (trialTable offset count)) s fun t =>
      (∀ i < count, w32 t.mem base (offset + 4 * i) = tabWord32 i) ∧
      Outside base offset (4 * count) s.mem t.mem ∧ Keeps [.eax] s t
  | 0, _, _ => WP.block_nil ⟨fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  | count + 1, countBound, fits => by
    have nowrap := ws.nowrap
    rw [trialTable, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (trial_table ws count (by omega) (by omega)) ?_)
    rintro u ⟨values, frame, K⟩
    unfold trialTableStore
    refine wp_movS rfl fun v V _ => ?_
    have Kv := K.trans V.keeps
    have wv := ws.of_keeps Kv (by decide)
    refine wp_storeS (wv.ea (by omega)) (wv.write (by omega)) fun t T => WP.block_nil ?_
    have changed : Outside base (offset + 4 * count) 4 u.mem t.mem := by
      rw [T.mem, V.mem]
      exact writeW32_outside _ _ _ (by omega)
    refine ⟨?_, (frame.mono (by omega) (by omega)).trans (changed.mono (by omega) (by omega)),
      Kv.trans (T.keeps _)⟩
    intro i hi
    by_cases old : i < count
    · rw [changed.w32 (by omega) (by omega)]
      exact values i old
    · have eq : i = count := by omega
      subst i
      rw [T.mem, w32_write_self, V.gpr, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (VG.Proof.RsaKeyGen.tabWord32_lt (by omega))]

end VG.Proof.Dsa.X86.Generation
