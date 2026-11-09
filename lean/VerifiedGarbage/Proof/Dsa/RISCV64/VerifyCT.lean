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
  refine chain_cons runB (m := 169) (by decide) (two_taint _ (pinsB161 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 330) (by decide) (two_taint _ (pinsB169 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 341) (by decide) (two_taint _ (pinsB330 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 344) (by decide) (two_taint _ (pinsB341 hsem) (by taint_decide)) ?_
  refine chain_cons runB (m := 350) (by decide) (two_taint _ (pinsB344 hsem) (by taint_decide)) ?_
  exact two_taint _ (pinsB350 hsem) (by taint_decide)

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

end VG.Proof.Dsa.RISCV64.CT
