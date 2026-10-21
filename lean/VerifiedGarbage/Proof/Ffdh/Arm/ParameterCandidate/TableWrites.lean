module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! The complete RSA-prime table uses the same entries as RSA's sieve. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem tableEntry_small {i : Nat} (bound : i < 1024) : VG.Impl.RsaKeyGen.tabEntry i < 2^16 := by
  have := (VG.Proof.RsaKeyGen.tabEntry_facts bound).2.2
  omega

theorem tableWrites_ok {s : State} {base : BitVec 32} {size offset : Nat}
    (space : Workspace s base size) (ptr : s.gpr .r11 = base + BitVec.ofNat 32 offset) :
    ∀ count, count ≤ 1024 → offset + 4 * count ≤ size →
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrites count)) s fun t =>
      (∀ j < count, w32 t.mem (State.addr base) (offset + 4 * j) = VG.Impl.RsaKeyGen.tabEntry j) ∧
      Outside (State.addr base) offset (4 * count) s.mem t.mem ∧ Rest [.r1] s t
  | 0, _, _ => WP.block_nil ⟨by intro j hj; omega, Outside.refl _ _ _ _, Rest.refl _ _⟩
  | count + 1, bounded, fit => by
    rw [VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrites, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.append (tableWrites_ok space ptr count (by omega) (by omega)) ?_
    rintro u ⟨values, outside, rest⟩
    have small := tableEntry_small (i := count) (by omega)
    refine wp_movw fun v moved => ?_
    have kept : Rest [.r1] s v := rest.trans (moved.rest (by simp))
    have address : State.addr (v.gpr .r11 + BitVec.ofNat 32 (4 * count)) =
        off (State.addr base) (offset + 4 * count) := by
      rw [kept.gpr .r11 (by simp), ptr, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact VG.Arm.addr_add (by have := space.nowrap; omega)
    refine wp_str (by omega) address ((space.congr kept.wr).write (by omega)) fun t store => WP.block_nil ?_
    have changed : Outside (State.addr base) (offset + 4 * count) 4 u.mem t.mem := by
      rw [store.mem, moved.mem]
      exact writeW32_outside _ _ _ (by have := space.nowrap; omega)
    refine ⟨?_, (outside.mono (Nat.le_refl _) (by omega)).trans (changed.mono (by omega) (by omega)),
      kept.trans (store.rest _)⟩
    intro j hj
    by_cases earlier : j < count
    · rw [changed.w32 (by omega) (by have := space.nowrap; omega)]
      exact values j earlier
    · have same : j = count := by omega
      subst j
      rw [store.mem, moved.gpr, w32_write_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : VG.Impl.RsaKeyGen.tabEntry count < 2 ^ 16),
        Nat.mod_eq_of_lt (by omega : VG.Impl.RsaKeyGen.tabEntry count < 2 ^ 32)]

end VG.Proof.Ffdh.Arm.ParameterCandidate
