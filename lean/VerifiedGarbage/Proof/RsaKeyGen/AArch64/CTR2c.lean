module

public import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.Setup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.Store
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-!
# A candidate on AArch64: constant time of `R² mod c`

`r2_ct` (`Proof/Bignum/AArch64/CTR2.lean`) relates runs with the same
modulus; a candidate `c` is secret, but its top bit is set, so `R² mod c`
always takes long division (`r2dFast_ct`), whose timing depends on the
working space alone (`r2c_ct`). The runs agree on the working space (`Ws`),
`-c⁻¹` and `c` differing.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero eval_nonzero)

/-- The layout of the working space `L` with `-m⁻¹ = mi`. -/
abbrev lay (L : Ws) (mi : BitVec 64) : Lay := ⟨L.B, L.Z, L.w, mi⟩

/-- `Φ` fixes the registers `rs` to values of the public data. -/
theorem pins_of {α : Type} {Φ : α → State → Prop} (rs : List Reg) (f : α → Reg → BitVec 64)
    (h : ∀ a s, Φ a s → ∀ r ∈ rs, s.gpr r = f a r) : Pins Φ rs :=
  fun a _ _ h₁ h₂ r hr => (h a _ h₁ r hr).trans (h a _ h₂ r hr).symm

theorem pins_nil' {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

/-! ## `R² mod c` for a candidate -/

/-- A predicate of `R2Pub` for some `-m⁻¹` and some `m` with its top bit set. -/
def Up (X : R2Pub → State → Prop) (L : Ws) (s : State) : Prop :=
  ∃ mi N, X ⟨lay L mi, N⟩ s ∧ 2 ^ (64 * L.w - 1) ≤ N

theorem up_post {X Y : R2Pub → State → Prop} {c : Prog isa} (h : ∀ p s, X p s → WP isa c s (Y p)) :
    ∀ L s, Up X L s → WP isa c s (Up Y L) :=
  fun _ _ ⟨mi, N, hx, hi⟩ => WP.mono (h _ _ hx) fun _ ht => ⟨mi, N, ht, hi⟩

/-- The top word of `m` with its top bit set. -/
theorem top63 {p : R2Pub} {s : State} (h : R2Pre p s) (hi : 2 ^ (64 * p.L.w - 1) ≤ p.N) :
    2 ^ 63 ≤ p.top ∧ p.top < 2 ^ 64 ∧ p.top.log2 = 63 := by
  obtain ⟨-, -, hT1, -⟩ := h.top
  have hw := h.2.1
  have e : 2 ^ 63 * 2 ^ (64 * (p.L.w - 1)) = 2 ^ (64 * p.L.w - 1) := by rw [← Nat.pow_add]; congr 1; omega
  have hT : 2 ^ 63 ≤ p.top := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by rw [e]; exact hi)
  exact ⟨hT, hT1, Nat.le_antisymm (Nat.lt_succ_iff.mp ((Nat.log2_lt (by omega)).mpr hT1))
    ((Nat.le_log2 (by omega)).mpr hT)⟩

theorem pins_up {X : R2Pub → State → Prop} (h : ∀ p s, X p s → R2Pre p s) : Pins (Up X) [.x0] :=
  pins_of _ (fun L _ => L.B) fun _ _ ⟨_, _, hx, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (h _ _ hx).1.1.x0

/-- After `fastTest`, for a candidate: its top bit, 1. -/
theorem up_eval {L : Ws} {s : State} (h : Up R2u L s) : isa.eval (.zero .x .x3) s = some false := by
  obtain ⟨_, _, ⟨hr, h3⟩, hi⟩ := h
  rw [eval_zero, h3, decide_eq_true (top63 hr hi).1]; rfl

/-- `R² mod c` leaks the same in runs that agree on the working space, for
moduli with their top bit set. -/
theorem r2c_ct (M : Mont) : RelCT isa (Two (Up R2Pre)) (seqs (r2Steps M.mm)) fun _ _ => True := by
  show RelCT isa (Two (Up R2Pre)) (R2Div.choice (seqs (r2StepsOld M.mm))) _
  unfold R2Div.choice
  rw [fastTest_eq]
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (two_piece (Ψ := Up R2t) _ (pins_up fun _ _ h => h) (by taint_decide) (up_post fun _ _ h => r2t_ok h))
    (two_piece (Ψ := Up R2u) [.x12, .x9] (pins_of _ (fun L r => match r with
        | .x12 => BitVec.ofNat 64 L.w | _ => off L.B (slot L.w aN)) fun _ _ ⟨_, _, ⟨_, h12, h9⟩, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h12
      · exact h9) (by taint_decide) (up_post fun _ _ h => r2u_ok h)))) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [up_eval h₁, up_eval h₂]) (RelCT.of_false ?_) ?_
  · rintro _ _ ⟨_, ⟨h, he⟩, -⟩
    rw [up_eval h] at he
    exact absurd he (by decide)
  · exact two_map id (fun _ _ ⟨⟨_, _, ⟨hr, _⟩, hi⟩, _⟩ => hr.fpre (top63 hr hi).1) r2dFast_ct

end VG.Proof.RsaKeyGen.AArch64
