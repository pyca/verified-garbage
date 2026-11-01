module

public import VerifiedGarbage.Proof.AesCcm.RISCV64.Entry

/-!
# AES-CCM on RISC-V: the exit

Untrusted: everything here is checked by Lean. `restore` reloads the return
address and our caller's registers from the slots the entry filled at
`W + 128` (`exit_wp`), `s1`, the base, last.
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesCcm.RISCV64
open VG.RISCV64.Spill (Saved restoreCode restore_wp)

/-- The slots `restore` reloads, in its order. -/
abbrev restoreL : List (Reg × Nat) := (.ra, raO) :: saved

theorem restore_code : restore = restoreCode .s1 restoreL := rfl

theorem restoreL_sub : ∀ p ∈ restoreL, p ∈ savedL := by decide

theorem other_of_preserved : ∀ r ∈ preserved, r ∉ restoreL.map Prod.fst → r ∈ otherRegs := by decide

/-- `restore`: our caller's registers and return address back, for `s₀` the
state at the entry. -/
theorem exit_wp {c : Cx} (L : Lay c) {s₀ s : State} (E : Env c s) (sv : Saved c.W s₀.gpr savedL s.mem)
    (hsp : s.sp = s₀.sp) (ho : ∀ r ∈ otherRegs, s.gpr r = s₀.gpr r) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .a0 = s.gpr .a0 := by
  rw [restore_code]
  refine WP.mono (restore_wp (b := .s1) (B := c.W) L.wal E.s1 (by decide) (by decide) (fun p hp => by
      have := savedL_bound p (restoreL_sub p hp)
      exact E.perm.wR (by omega)) (sv.sub restoreL_sub)) fun s' R => ?_
  refine ⟨⟨fun r hr => ?_, by rw [R.sp, hsp], R.gpr (.ra, raO) List.mem_cons_self⟩, R.mem,
    R.other _ (by decide)⟩
  by_cases hs : r ∈ restoreL.map Prod.fst
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
    exact R.gpr p hp
  · rw [R.other r hs, ho r (other_of_preserved r hr hs)]

end VG.Proof.AesCcm.RISCV64
