module

public import VerifiedGarbage.Proof.X448.Arm.Save
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.Arm.Carry
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# X448 on ARMv7: restoring the callee-saved registers

Each incoming register value is loaded from its designated working-space word.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

theorem saved_inj : ∀ i < 8, ∀ j < 8, saved[i]! = saved[j]! → i = j := by decide

theorem saved_mem : ∀ i < 8, saved[i]! ∈ saved := by decide

theorem restoreL_ok {L : List Reg} (hinj : ∀ i < 8, ∀ j < 8, L[i]! = L[j]! → i = j)
    (hmem : ∀ i < 8, L[i]! ∈ L) (h0 : .r0 ∉ L) {s : State} {base : Addr} (hs : Scr s base)
    {g : Reg → BitVec 32} (hsv : SavedL L base g s.mem) :
    WP isa (.block ((List.range 8).map (fun i => ld (L[i]!) (4 * i)))) s fun t =>
      (∀ i < 8, t.gpr (L[i]!) = g (L[i]!)) ∧ t.mem = s.mem ∧ Keeps L s t := by
  let inv := fun (n : Nat) (t : State) =>
    (∀ i < n, t.gpr (L[i]!) = g (L[i]!)) ∧ t.mem = s.mem ∧ Keeps L s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block [ld (L[n]!) (4 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tv, tm, tk⟩
    have ea : State.addr (t.gpr .r0 + BitVec.ofNat 32 (4 * n)) = off base (4 * n) := by
      rw [tk.1 _ h0]; exact hs.ea (by omega_using [hn])
    have hr : InRegions (t.rd ++ t.wr) (off base (4 * n)) 4 := by
      rw [tk.2.1, tk.2.2]; exact hs.read (by omega_using [hn])
    refine VG.Proof.X25519.Arm.wp_ldr (by omega_using [hn]) ea hr fun u hu => WP.block_nil ⟨?_, hu.mem.trans tm,
      tk.trans (rest_keeps (hu.rest (hmem n hn)))⟩
    intro i hi
    by_cases he : i = n
    · subst i; rw [hu.gpr, tm]; exact hsv n hn
    · rw [hu.other _ (fun h => he (hinj i (by omega_using [hn, hi]) n hn h))]
      exact tv i (by omega_using [hi, he])
  rw [List.map_eq_flatMap]
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, rfl, Keeps.refl _ _⟩

theorem restore_ok {s : State} {base : Addr} (hs : Scr s base) {g : Reg → BitVec 32}
    (hsv : Saved base g s.mem) :
    WP isa (.block ((List.range 8).map (fun i => ld (saved[i]!) (4 * i)))) s fun t =>
      (∀ i < 8, t.gpr (saved[i]!) = g (saved[i]!)) ∧ t.mem = s.mem ∧ Keeps saved s t :=
  restoreL_ok saved_inj saved_mem (by decide) hs hsv

theorem savedL_inj : ∀ i < 8, ∀ j < 8, savedL[i]! = savedL[j]! → i = j := by decide

theorem savedL_mem : ∀ i < 8, savedL[i]! ∈ savedL := by decide

end VG.Proof.X448.Arm
