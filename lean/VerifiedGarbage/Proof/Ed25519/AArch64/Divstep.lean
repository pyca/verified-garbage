module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Ends
public import VerifiedGarbage.Proof.Ed25519.AArch64.Field
public import VerifiedGarbage.Proof.Mont.AArch64.Ops
public import VerifiedGarbage.Proof.X25519.Invert
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Ed25519 and X25519 on AArch64: the inversion by divsteps

Untrusted: everything here is checked by Lean. `Divstep.invert` leaves
`[slot 15] ≡ [slot 2]^(p - 2)` (`invert_ok`): `init` sets up the invariant
(`Inv.init_ok`), each of the ten batches keeps it (`Inv.batch_ok`, `loop_ok`),
and `finish` leaves `±u` by the sign of `f` (`Inv.finish_ok`). That this is
`x^(p - 2)` (`f = ±1` after 590 divsteps, and Fermat) is `Sound`, proven in
`DivstepSound`, the one module that imports the algebra it takes.
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Divstep

open VG VG.AArch64 VG.Proof.Ed25519.AArch64 VG.Proof.Ed25519.AArch64.Inv VG.Spec.X25519
open VG.Proof.Mont.AArch64 (KeepRegs)
open VG.Impl.Ed25519.AArch64.Divstep (G U V DSAVE X1SAVE batch init finish)
open VG.Impl.Ed25519.AArch64.Divstep renaming F → oF

variable {large : Bool}

instance : NeZero Spec.X25519.P := ⟨by decide⟩

/-- The divsteps are sound modulo `p`: after `590` of them from `x < p`, with
`2⁵⁹⁰ f ≡ x 2⁵⁹⁰ u` (and `u ≡ 0` if `x = 0`), `±u` by the sign of `f` is
`x^(p - 2)`. `DivstepSound.lean`. -/
class Sound : Prop where
  sound : ∀ {x U R : Nat}, x < P →
    2 ^ 590 * (dsI x 10).2.1 ≡ x * 2 ^ 590 * U [ZMOD P] →
    (x = 0 → (U : Int) ≡ 0 [ZMOD P]) →
    (R : Int) % P = (if (dsI x 10).2.1 < 0 then -(U : Int) else U) % P →
    VG.Proof.X25519.toFe R = VG.Proof.X25519.invert (VG.Proof.X25519.toFe x)

/-- The ten batches. -/
theorem loop_ok {s : State} {base : Addr} (hs : Scr s base large) {x : Nat} (hx : x < P)
    (h : RInv x 0 (word s.mem base DSAVE) (fe s.mem base oF) (fe s.mem base G) (fe s.mem base U)
      (fe s.mem base V))
    (hc : s.gpr .x20 = BitVec.ofNat 64 10) :
    WP isa (.loop (.block batch) (.nonzero .x .x20)) s fun t =>
      RInv x 10 (word t.mem base DSAVE) (fe t.mem base oF) (fe t.mem base G) (fe t.mem base U)
        (fe t.mem base V) ∧ Outside base 192 296 s.mem t.mem ∧ KeepRegs batchRegs s t := by
  refine WP.loop (M := isa) (fun k t => 1 ≤ k ∧ k ≤ 10 ∧
    RInv x (10 - k) (word t.mem base DSAVE) (fe t.mem base oF) (fe t.mem base G) (fe t.mem base U)
      (fe t.mem base V) ∧ t.gpr .x20 = BitVec.ofNat 64 k ∧ Outside base 192 296 s.mem t.mem ∧
    KeepRegs batchRegs s t) ?_ 10 s ⟨by decide, le_rfl, by exact h, hc, Outside.refl _ _ _ _,
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  intro k t ⟨hk, hk10, ht, tc, tO, tk⟩
  refine WP.mono (batch_ok (scr_of hs tk (by decide)) hx (i := 10 - k) (by omega) ht
    (by rw [tc, show 10 - (10 - k) = k by omega])) fun u ⟨ui, uc, uO, uk⟩ => ?_
  rw [show 10 - (10 - k + 1) = k - 1 by omega] at uc
  have hev : isa.eval (.nonzero .x .x20) u = some (BitVec.ofNat 64 (k - 1) != 0) := by
    simp [eval, read_x, uc]
  by_cases hk1 : k = 1
  · subst hk1
    refine .inl ⟨by rw [hev]; rfl, ?_, tO.trans uO, tk.trans uk⟩
    simpa using ui
  · refine .inr ⟨?_, k - 1, by omega, by omega, by omega,
      by rw [show 10 - (k - 1) = 10 - k + 1 by omega]; exact ui, uc, tO.trans uO, tk.trans uk⟩
    rw [hev]
    apply congrArg some
    apply bne_iff_ne.mpr
    intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k - 1 < 2 ^ 64),
      show (0 : BitVec 64).toNat = 0 from rfl] at this
    omega

theorem sv_neg {X : Nat} (h : X < 2 ^ 256) : sv X < 0 ↔ 2 ^ 255 ≤ X := by
  unfold sv; split <;> omega

/-- `[slot 15] = [slot 2]^(p - 2)`. -/
theorem invert_ok [Sound] {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa VG.Impl.Ed25519.AArch64.Divstep.invert s fun t =>
      env t.mem base 15 = VG.Proof.X25519.invert (env s.mem base 2) ∧
      KeepRegs (.x19 :: VG.Proof.Mont.AArch64.clob 4 ++ ([.x2, .x20] : List Reg)) s t ∧
      t.gpr .x1 = s.gpr .x1 ∧ Outside base 192 512 s.mem t.mem := by
  refine WP.seq (WP.mono (init_ok hs) fun a ⟨ai, a20, aX, aO, ak⟩ => ?_)
  have hx : fe s.mem base 128 % P < P := Nat.mod_lt _ (by decide)
  refine WP.seq (WP.mono (loop_ok (scr_of hs ak (by decide)) hx ai a20) fun b ⟨bi, bO, bk⟩ => ?_)
  refine WP.mono (finish_ok (scr_of (scr_of hs ak (by decide)) bk (by decide))) fun t ⟨tv, t1, tO, tk⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [env, AArch64.F]
    have e2 : VG.Proof.X25519.toFe (fe s.mem base (VG.Impl.Ed25519.AArch64.offset 2)) =
        VG.Proof.X25519.toFe (fe s.mem base 128 % P) :=
      Fin.ext (by simp only [VG.Proof.X25519.toFe_val, Nat.mod_mod]; rfl)
    rw [e2]
    refine Sound.sound hx bi.cu bi.z ?_
    rw [show VG.Impl.Ed25519.AArch64.offset 15 = 544 from rfl, tv, ← bi.f]
    simp only [sv_neg bi.fl]
  · exact ((ak.trans bk).trans tk).mono (by decide)
  · rw [t1, bO.word (by decide) (by decide)]
    exact aX
  · exact ((aO.mono (by decide) (by decide)).trans (bO.mono (by decide) (by decide))).trans
      (tO.mono (by decide) (by decide))

end VG.Proof.Ed25519.AArch64.Divstep
