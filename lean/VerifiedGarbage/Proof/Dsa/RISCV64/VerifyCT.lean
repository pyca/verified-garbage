module

public import VerifiedGarbage.Proof.Dsa.RISCV64.CTBase
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Dsa.RISCV64.CTKey
public import VerifiedGarbage.Proof.Dsa.RISCV64.CTParams
import VerifiedGarbage.Proof.Dsa.RISCV64.CTBodyA
import VerifiedGarbage.Proof.Dsa.RISCV64.CTBodyB
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTBase
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTKey
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTParams
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTBodyA
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTBodyB
meta import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody

-- separate module: the taint checks of every level cost more than their imports, and `VerifyVerified`
-- states the result without them

/-!
# DSA verification on RISC-V: constant time

`verify_ct`: two runs from states that satisfy the contract and agree on its
public data (the arguments' registers, the stack's arguments, the key's
public part and the result) leak the same trace. Each level of `verify`'s
lists (`CTBase.lean`) is checked by the taint analysis between its cuts, from
the registers there (`CTKey.lean`, `CTParams.lean`, `CTBody*.lean`), and its
branches by their levels (`rel_ite_at`), from the innermost (`body_rel`) out.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.Taint VG.Impl.Dsa.RISCV64 VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_taint)
open VG.Proof.Bignum.RISCV64 (At chain_cons chain_start at_zero_inv)

/-! ## Each level's phase -/

theorem front0 : ∀ v s, C0 v s → WP isa (.block Verify.entry) s (P0 v) := fun _ _ h => front_P0 h

theorem atTF {n : Nat} (hn : FT.take n = (TF Verify.entry).take n) {v : VD} {u : State} (h : At C0 FT n v u) :
    At C0 (TF Verify.entry) n v u :=
  at_mono (fun _ _ h => h) hn h

/-- What verification's public data satisfies throughout. -/
abbrev GV (v : VD) : Prop := KY v ∧ VB v

theorem gC0 : ∀ v s, C0 v s → GV v := by
  rintro _ s ⟨-, rfl⟩
  exact ⟨Nat.le_refl _, rfl, rfl⟩

theorem onX1 : ∀ v u, ΦX1 v u → SX1 v u := fun _ _ h => semX1 front0 ⟨atTF rfl h.1, h.2⟩
theorem onX2 : ∀ v u, ΦX2 v u → SX2 v u := fun _ _ h => semX2 onX1 h
theorem onR0 : ∀ v u, ΦR0 v u → P1 v u := fun _ _ h => semR0 onX2 h
theorem onR1 : ∀ v u, ΦR1 v u → P1 v u ∧ v.p % 2 = 1 := fun _ _ h => semR1 onR0 h
theorem onR2 : ∀ v u, ΦR2 v u → SR2 v u := fun _ _ h => semR2 onR1 h
theorem onR3 : ∀ v u, ΦR3 v u → SR3 v u := fun _ _ h => semR3 onR2 h

theorem gX1 : ∀ v u, ΦX1 v u → GV v := fun _ _ h => at_pure (G := GV) gC0 h.1
theorem gX2 : ∀ v u, ΦX2 v u → GV v := fun _ _ h => at_pure (G := GV) gX1 h.1
theorem gR0 : ∀ v u, ΦR0 v u → GV v := fun _ _ h => at_pure (G := GV) gX2 h.1
theorem gR1 : ∀ v u, ΦR1 v u → GV v := fun _ _ h => at_pure (G := GV) gR0 h.1
theorem gR2 : ∀ v u, ΦR2 v u → GV v := fun _ _ h => at_pure (G := GV) gR1 h.1
theorem gR3 : ∀ v u, ΦR3 v u → GV v := fun _ _ h => at_pure (G := GV) gR2 h.1
theorem gK : ∀ v u, ΦK v u → GV v := fun _ _ h => at_pure (G := GV) gR3 h.1

theorem onK : ∀ v u, ΦK v u → SK v u := fun _ _ h => semK onR3 (fun _ _ h => (gR3 _ _ h).1) h
theorem onB : ∀ v u, ΦB v u → SB v u := fun _ _ h => semB onK (fun _ _ h => (gK _ _ h).2) h

/-! ## The levels' relations -/

theorem pinsB0 {Φ : VD → State → Prop} (hsem : ∀ v u, Φ v u → SB v u) : Pins (At Φ FB 0) [.s6, .s11, .ra] :=
  pins_at_fix fixB (fun _ => rfl) fun _ _ h => ⟨[], _, .block rfl, (hsem _ _ h).1.1.base.fixB⟩

/-- `body`, from a level whose states are in `body`'s phase. -/
theorem body_rel' {Φ : VD → State → Prop} (runB : ∀ v s, Φ v s → WP isa (Code.seqL FB) s fun _ => True)
    (hsem : ∀ v u, Φ v u → SB v u) : RelCT isa (Two Φ) Verify.body fun _ _ => True := by
  refine chain_start (chain_cons runB (m := 1) (by decide) (two_taint _ (pinsB0 hsem) (by taint_decide)) ?_)
  refine chain_cons runB (m := 9) (by decide) (two_taint _ (pinsB1 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 50) (by decide) (two_taint _ (pinsB9 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 53) (by decide) (two_taint _ (pinsB50 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 63) (by decide) (two_taint _ (pinsB53 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 104) (by decide) (two_taint _ (pinsB63 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 106) (by decide) (two_taint _ (pinsB104 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 108) (by decide) (two_taint _ (pinsB106 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 154) (by decide) (two_taint _ (pinsB108 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 157) (by decide) (two_taint _ (pinsB154 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 161) (by decide) (two_taint _ (pinsB157 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 171) (by decide) (two_taint _ (pinsB161 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 215) (by decide) (two_taint _ (pinsB171 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 225) (by decide) (two_taint _ (pinsB215 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 288) (by decide) (two_taint _ (pinsB225 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 291) (by decide) (two_taint _ (pinsB288 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 297) (by decide) (two_taint _ (pinsB291 hsem) (by taint_decide)) ?_
  exact two_taint _ (pinsB297 hsem) (by taint_decide)

theorem body_rel : RelCT isa (Two ΦB) Verify.body fun _ _ => True := body_rel' runB onB

theorem K_rel : RelCT isa (Two ΦK) RK fun _ _ => True := by
  refine chain_start (chain_cons runK (m := 1) (by decide) (two_taint _ (pinsK_0 onK) (by taint_decide)) ?_)
  refine chain_cons runK (m := 28) (by decide) (two_taint _ (pinsK_1 onK) (by taint_decide)) ?_
  refine chain_cons runK (m := 29) (by decide)
    (rel_ite_at hFKy (zeroEy onK) (eo_rel runEy fun _ _ h => semEy onK h) nil_rel) ?_
  exact chain_cons runK (m := 30) (by decide) (rel_ite_at hFK (zeroK onK) body_rel fail_rel) nil_rel

theorem R3_rel : RelCT isa (Two ΦR3) R3 fun _ _ => True := by
  refine chain_start (chain_cons runR3 (m := 2) (by decide) (two_taint _ (pinsR3_0 onR3) (by taint_decide)) ?_)
  refine chain_cons runR3 (m := 18) (by decide) (two_taint _ (pinsR3_2 onR3) (by taint_decide)) ?_
  refine chain_cons runR3 (m := 45) (by decide) (two_taint _ (pinsR3_18 onR3) (by taint_decide)) ?_
  refine chain_cons runR3 (m := 46) (by decide)
    (rel_ite_at hFR3g (zeroEg onR3) (eo_rel runEg fun _ _ h => semEg onR3 h) nil_rel) ?_
  exact chain_cons runR3 (m := 47) (by decide) (rel_ite_at hFR3 (zeroR3 onR3) K_rel fail_rel) nil_rel

theorem R2_rel : RelCT isa (Two ΦR2) R2 fun _ _ => True := by
  refine chain_start (chain_cons runR2 (m := 2) (by decide) (two_taint _ (pinsR2_0 onR2) (by taint_decide)) ?_)
  refine chain_cons runR2 (m := 10) (by decide) (two_taint _ (pinsR2_2 onR2) (by taint_decide)) ?_
  refine chain_cons runR2 (m := 23) (by decide) (two_taint _ (pinsR2_10 onR2) (by taint_decide)) ?_
  exact chain_cons runR2 (m := 24) (by decide) (rel_ite_at hFR2 (zeroR2 onR2) R3_rel fail_rel) nil_rel

theorem R1_rel : RelCT isa (Two ΦR1) R1 fun _ _ => True :=
  chain_start (chain_cons runR1 (m := 1) (by decide) (relR1 onR1)
    (chain_cons runR1 (m := 2) (by decide) (rel_ite_at hFR1 (zeroR1 onR1) R2_rel fail_rel) nil_rel))

theorem R0_rel : RelCT isa (Two ΦR0) R0 fun _ _ => True :=
  chain_start (chain_cons runR0 (m := 1) (by decide) (relR0 onR0)
    (chain_cons runR0 (m := 2) (by decide) (rel_ite_at hFR0 (zeroR0 onR0) R1_rel fail_rel) nil_rel))

theorem X2_rel : RelCT isa (Two ΦX2) X2 fun _ _ => True :=
  chain_start (chain_cons runX2 (m := 12) (by decide) (two_taint _ (pinsX2_0 onX2) (by taint_decide))
    (chain_cons runX2 (m := 13) (by decide) (rel_ite_at hFX2 (zeroX2 onX2) R0_rel fail_rel) nil_rel))

theorem X1_rel : RelCT isa (Two ΦX1) X1 fun _ _ => True := by
  refine chain_start (chain_cons runX1 (m := 2) (by decide) (two_taint _ (pinsX1_0 onX1) (by taint_decide)) ?_)
  refine chain_cons runX1 (m := 4) (by decide) (two_taint _ (pinsX1_2 onX1) (by taint_decide)) ?_
  refine chain_cons runX1 (m := 5) (by decide) (two_taint _ (pinsX1_4 onX1) (by taint_decide)) ?_
  exact chain_cons runX1 (m := 6) (by decide) (rel_ite_at hFX1 (zeroX1 onX1) X2_rel fail_rel) nil_rel

theorem verify_rel : RelCT isa (Two C0) Verify.verify fun _ _ => True := by
  refine chain_start (chain_cons runT (m := 1) (by decide) ?_ ?_)
  · refine RelCT.mono (P := Two C0)
      (VG.Proof.Bignum.RISCV64.RelCT.seqL_single (entry_rel.mono (fun _ _ h => h) fun _ _ _ => trivial))
      (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨a, at_zero_inv h₁, at_zero_inv h₂, hsp⟩) fun _ _ h => h
  refine chain_cons runT (m := 2) (by decide) (two_taint _ (pins_mono (pinsT1 front0) fun _ _ h => atTF rfl h) (by taint_decide)) ?_
  refine chain_cons runT (m := 4) (by decide) (two_taint _ (pins_mono (pinsT2 front0) fun _ _ h => atTF rfl h) (by taint_decide)) ?_
  refine chain_cons runT (m := 5) (by decide) (two_taint _ (pins_mono (pinsT4 front0) fun _ _ h => atTF rfl h) (by taint_decide)) ?_
  refine chain_cons runT (m := 6) (by decide) (rel_ite_at hFT (fun v s₁ s₂ h₁ h₂ => zeroT front0 v s₁ s₂ (atTF rfl h₁) (atTF rfl h₂)) X1_rel fail_rel) ?_
  exact two_taint _ pinsT6 (by taint_decide)

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (·.toNat) = l₂.map (·.toNat) → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]

/-- Runs that agree on the contract's public data have the same public data `vdOf`. -/
theorem vdOf_eq {s t : State} (hs : vContract.pre s) (hp : vContract.pub s t) : vdOf s = vdOf t := by
  obtain ⟨-, e0, e1, e2, e3, e4, -, e6, e7, sa0, sa1, hl⟩ := hp
  have hk := hs.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨e, -⟩ := List.append_inj' hl rfl
  simp only [Spec.Dsa.publicBytesLeak, bytesAt_take] at e
  have e := map_toNat_inj e
  rw [← e0, ← e1, ← e2, ← e3, Nat.min_eq_right (by omega)] at e
  simp only [vdOf, layOf, ← e0, ← e2, ← e3, ← e4, ← e6, ← e7, ← sa0, ← sa1, e]

theorem verify_ct : ConstantTime isa vContract.pre vContract.pub Verify.verify :=
  RelCT.constantTime (verify_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨vdOf s, ⟨hs, rfl⟩, ⟨ht, (vdOf_eq hs hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.RISCV64.CT
