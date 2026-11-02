module

public import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsCT
public import VerifiedGarbage.Proof.Dsa.RISCV64.ValidateFn
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Flat
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsCT
meta import VerifiedGarbage.Proof.Dsa.RISCV64.ValidateFn
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Flat
meta import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the taint checks of its levels cost more than their imports, and `ValidateVerified`
-- states the result without them

/-!
# DSA public key validation on RISC-V: constant time

`vg_dsa_validate_public_key` (`Prevalidated.validate`) runs `Params.entry`,
then `checkKey` with the status 1 or 0, then `restore`. Its public data is
`vdP` (`ParamsCT.lean`), with the key's `3 p_len + q_len` octets, all public.
Its levels are verification's (`CTBase.lean`) up to y's check, whose passing
side is the status 1: their lists start with the same programs, so their
cuts' registers, branches and phases are verification's (`atL`, `pinsL`,
`zeroL`, `relL`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_taint)
open VG.Proof.Bignum.RISCV64 (At chain_cons chain_start at_zero_inv)

/-! ## The levels -/

/-- On entry. -/
def C0k (v : VD) (s : State) : Prop := vkContract.pre s ∧ vdP s = v

theorem frontK : ∀ v s, C0k v s → WP isa (.block Params.entry) s (P0 v) := by
  rintro _ s ⟨h, rfl⟩
  exact pfront_P0 (playOf_ok_of h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1) h.1 h.2.1 h.2.2.1 h.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.1 (by have := h.2.2.2.2.2.2.1; omega)

/-- The public octets name y. -/
theorem kyC0k : ∀ v s, C0k v s → KY v := by
  rintro _ s ⟨h, rfl⟩
  show 3 * (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ (s.gpr .a1).toNat
  have := h.2.2.2.2.2.2.1
  omega

abbrev RKk : Prog isa := andThen (.seq (.block ptrY) checkElem) ok1 fail0
abbrev R3k : Prog isa := .seq setupP (andThen (.seq (.block ptrG) checkElem) RKk fail0)
abbrev R2k : Prog isa := andThen pModQ R3k fail0
abbrev R1k : Prog isa := andThen (.block (ptrQ ++ odd)) R2k fail0
abbrev R0k : Prog isa := odds R2k fail0
abbrev X2k : Prog isa :=
  .seq (.block [.addi .a3 .a1 0, .shift .sll .d .t3 .a1 32, .load .d .t4 .s6 hLens, .add .t4 .t4 .t3,
    .store .d .t4 .s6 hLens]) (andThen pairs R0k fail0)
abbrev X1k : Prog isa := .seq (.block [.addi .a2 .a1 0]) (andThen (.seq (.block ptrQ) bytesBits) X2k fail0)

abbrev FTk : List (Prog isa) := Code.flat Prevalidated.validate
abbrev FX1k : List (Prog isa) := Code.flat X1k
abbrev FX2k : List (Prog isa) := Code.flat X2k
abbrev FR0k : List (Prog isa) := Code.flat R0k
abbrev FR1k : List (Prog isa) := Code.flat R1k
abbrev FR2k : List (Prog isa) := Code.flat R2k
abbrev FR3k : List (Prog isa) := Code.flat R3k
abbrev FKk : List (Prog isa) := Code.flat RKk

abbrev ΦX1k (v : VD) (u : State) : Prop := At C0k FTk 5 v u ∧ u.gpr .a0 = 0
abbrev ΦX2k (v : VD) (u : State) : Prop := At ΦX1k FX1k 5 v u ∧ u.gpr .a0 = 0
abbrev ΦR0k (v : VD) (u : State) : Prop := At ΦX2k FX2k 12 v u ∧ u.gpr .a0 = 0
abbrev ΦR1k (v : VD) (u : State) : Prop := At ΦR0k FR0k 1 v u ∧ u.gpr .a0 = 0
abbrev ΦR2k (v : VD) (u : State) : Prop := At ΦR1k FR1k 1 v u ∧ u.gpr .a0 = 0
abbrev ΦR3k (v : VD) (u : State) : Prop := At ΦR2k FR2k 23 v u ∧ u.gpr .a0 = 0
abbrev ΦEgk (v : VD) (u : State) : Prop := At ΦR3k FR3k 45 v u ∧ u.gpr .a0 = 0
abbrev ΦKk (v : VD) (u : State) : Prop := At ΦR3k FR3k 46 v u ∧ u.gpr .a0 = 0
abbrev ΦEyk (v : VD) (u : State) : Prop := At ΦKk FKk 28 v u ∧ u.gpr .a0 = 0

theorem hFTk : (FTk.drop 5).take 1 = [.ite (.zero .a0) X1k fail0] := rfl
theorem hFX1k : (FX1k.drop 5).take 1 = [.ite (.zero .a0) X2k fail0] := rfl
theorem hFX2k : (FX2k.drop 12).take 1 = [.ite (.zero .a0) R0k fail0] := rfl
theorem hFR0k : (FR0k.drop 1).take 1 = [.ite (.zero .a0) R1k fail0] := rfl
theorem hFR1k : (FR1k.drop 1).take 1 = [.ite (.zero .a0) R2k fail0] := rfl
theorem hFR2k : (FR2k.drop 23).take 1 = [.ite (.zero .a0) R3k fail0] := rfl
theorem hFR3gk : (FR3k.drop 45).take 1 = [.ite (.zero .a0) elemOrder (.block [])] := rfl
theorem hFR3k : (FR3k.drop 46).take 1 = [.ite (.zero .a0) RKk fail0] := rfl
theorem hFKyk : (FKk.drop 28).take 1 = [.ite (.zero .a0) elemOrder (.block [])] := rfl
theorem hFKk : (FKk.drop 29).take 1 = [.ite (.zero .a0) ok1 fail0] := rfl

theorem runTk : ∀ v s, C0k v s → WP isa (Code.seqL FTk) s fun _ => True := fun _ s h =>
  let ⟨tr, t, e, _⟩ := validate_correct s h.1
  ⟨tr, t, exec_flat.mp e, trivial⟩

theorem runX1k : ∀ v s, ΦX1k v s → WP isa (Code.seqL FX1k) s fun _ => True := run_then runTk hFTk
theorem runX2k : ∀ v s, ΦX2k v s → WP isa (Code.seqL FX2k) s fun _ => True := run_then runX1k hFX1k
theorem runR0k : ∀ v s, ΦR0k v s → WP isa (Code.seqL FR0k) s fun _ => True := run_then runX2k hFX2k
theorem runR1k : ∀ v s, ΦR1k v s → WP isa (Code.seqL FR1k) s fun _ => True := run_then runR0k hFR0k
theorem runR2k : ∀ v s, ΦR2k v s → WP isa (Code.seqL FR2k) s fun _ => True := run_then runR1k hFR1k
theorem runR3k : ∀ v s, ΦR3k v s → WP isa (Code.seqL FR3k) s fun _ => True := run_then runR2k hFR2k
theorem runEgk : ∀ v s, ΦEgk v s → WP isa (Code.seqL FE) s fun _ => True := run_then runR3k hFR3gk
theorem runKk : ∀ v s, ΦKk v s → WP isa (Code.seqL FKk) s fun _ => True := run_then runR3k hFR3k
theorem runEyk : ∀ v s, ΦEyk v s → WP isa (Code.seqL FE) s fun _ => True := run_then runKk hFKyk

theorem onX1k : ∀ v u, ΦX1k v u → SX1 v u := fun _ _ h => semX1 frontK ⟨atL rfl h.1, h.2⟩
theorem onX2k : ∀ v u, ΦX2k v u → SX2 v u := fun _ _ h => semX2 onX1k ⟨atL rfl h.1, h.2⟩
theorem onR0k : ∀ v u, ΦR0k v u → P1 v u := fun _ _ h => semR0 onX2k ⟨atL rfl h.1, h.2⟩
theorem onR1k : ∀ v u, ΦR1k v u → P1 v u ∧ v.p % 2 = 1 := fun _ _ h => semR1 onR0k ⟨atL rfl h.1, h.2⟩
theorem onR2k : ∀ v u, ΦR2k v u → SR2 v u := fun _ _ h => semR2 onR1k ⟨atL rfl h.1, h.2⟩
theorem onR3k : ∀ v u, ΦR3k v u → SR3 v u := fun _ _ h => semR3 onR2k ⟨atL rfl h.1, h.2⟩

theorem kyX1k : ∀ v u, ΦX1k v u → KY v := fun _ _ h => at_pure (G := KY) kyC0k h.1
theorem kyX2k : ∀ v u, ΦX2k v u → KY v := fun _ _ h => at_pure (G := KY) kyX1k h.1
theorem kyR0k : ∀ v u, ΦR0k v u → KY v := fun _ _ h => at_pure (G := KY) kyX2k h.1
theorem kyR1k : ∀ v u, ΦR1k v u → KY v := fun _ _ h => at_pure (G := KY) kyR0k h.1
theorem kyR2k : ∀ v u, ΦR2k v u → KY v := fun _ _ h => at_pure (G := KY) kyR1k h.1
theorem kyR3k : ∀ v u, ΦR3k v u → KY v := fun _ _ h => at_pure (G := KY) kyR2k h.1

theorem onKk : ∀ v u, ΦKk v u → SK v u := fun _ _ h => semK onR3k kyR3k ⟨atL rfl h.1, h.2⟩

/-! ## The levels' relations -/

theorem Kk_rel : RelCT isa (Two ΦKk) RKk fun _ _ => True := by
  refine chain_start (chain_cons runKk (m := 1) (by decide)
    (two_taint _ (pinsL rfl (pinsK_0 onKk)) (by taint_decide)) ?_)
  refine chain_cons runKk (m := 28) (by decide) (two_taint _ (pinsL rfl (pinsK_1 onKk)) (by taint_decide)) ?_
  refine chain_cons runKk (m := 29) (by decide) (rel_ite_at hFKyk (zeroL rfl (zeroEy onKk))
    (eo_rel runEyk fun _ _ h => semEy onKk ⟨atL rfl h.1, h.2⟩) nil_rel) ?_
  exact chain_cons runKk (m := 30) (by decide) (rel_ite_at hFKk (zeroL rfl (zeroK onKk)) ok_rel fail_rel) nil_rel

theorem R3k_rel : RelCT isa (Two ΦR3k) R3k fun _ _ => True := by
  refine chain_start (chain_cons runR3k (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsR3_0 onR3k)) (by taint_decide)) ?_)
  refine chain_cons runR3k (m := 18) (by decide) (two_taint _ (pinsL rfl (pinsR3_2 onR3k)) (by taint_decide)) ?_
  refine chain_cons runR3k (m := 45) (by decide) (two_taint _ (pinsL rfl (pinsR3_18 onR3k)) (by taint_decide)) ?_
  refine chain_cons runR3k (m := 46) (by decide) (rel_ite_at hFR3gk (zeroL rfl (zeroEg onR3k))
    (eo_rel runEgk fun _ _ h => semEg onR3k ⟨atL rfl h.1, h.2⟩) nil_rel) ?_
  exact chain_cons runR3k (m := 47) (by decide) (rel_ite_at hFR3k (zeroL rfl (zeroR3 onR3k)) Kk_rel fail_rel)
    nil_rel

theorem R2k_rel : RelCT isa (Two ΦR2k) R2k fun _ _ => True := by
  refine chain_start (chain_cons runR2k (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsR2_0 onR2k)) (by taint_decide)) ?_)
  refine chain_cons runR2k (m := 10) (by decide) (two_taint _ (pinsL rfl (pinsR2_2 onR2k)) (by taint_decide)) ?_
  refine chain_cons runR2k (m := 23) (by decide) (two_taint _ (pinsL rfl (pinsR2_10 onR2k)) (by taint_decide)) ?_
  exact chain_cons runR2k (m := 24) (by decide) (rel_ite_at hFR2k (zeroL rfl (zeroR2 onR2k)) R3k_rel fail_rel)
    nil_rel

theorem R1k_rel : RelCT isa (Two ΦR1k) R1k fun _ _ => True :=
  chain_start (chain_cons runR1k (m := 1) (by decide) (relL rfl rfl (relR1 onR1k))
    (chain_cons runR1k (m := 2) (by decide) (rel_ite_at hFR1k (zeroL rfl (zeroR1 onR1k)) R2k_rel fail_rel)
      nil_rel))

theorem R0k_rel : RelCT isa (Two ΦR0k) R0k fun _ _ => True :=
  chain_start (chain_cons runR0k (m := 1) (by decide) (relL rfl rfl (relR0 onR0k))
    (chain_cons runR0k (m := 2) (by decide) (rel_ite_at hFR0k (zeroL rfl (zeroR0 onR0k)) R1k_rel fail_rel)
      nil_rel))

theorem X2k_rel : RelCT isa (Two ΦX2k) X2k fun _ _ => True :=
  chain_start (chain_cons runX2k (m := 12) (by decide)
    (two_taint _ (pinsL rfl (pinsX2_0 onX2k)) (by taint_decide))
    (chain_cons runX2k (m := 13) (by decide) (rel_ite_at hFX2k (zeroL rfl (zeroX2 onX2k)) R0k_rel fail_rel)
      nil_rel))

theorem X1k_rel : RelCT isa (Two ΦX1k) X1k fun _ _ => True := by
  refine chain_start (chain_cons runX1k (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsX1_0 onX1k)) (by taint_decide)) ?_)
  refine chain_cons runX1k (m := 4) (by decide) (two_taint _ (pinsL rfl (pinsX1_2 onX1k)) (by taint_decide)) ?_
  refine chain_cons runX1k (m := 5) (by decide) (two_taint _ (pinsL rfl (pinsX1_4 onX1k)) (by taint_decide)) ?_
  exact chain_cons runX1k (m := 6) (by decide) (rel_ite_at hFX1k (zeroL rfl (zeroX1 onX1k)) X2k_rel fail_rel)
    nil_rel

theorem s6_keptk : ∀ i ∈ instrs (seg FTk 1 6), dstOf i ≠ some .s6 := by
  have h : (instrs (seg FTk 1 6)).all (fun i => dstOf i != some .s6) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem pinsTk6 : Pins (At C0k FTk 6) [.s6] :=
  pins_fix (fun v => [(.s6, v.L.S)]) (fun _ => rfl) fun v u ⟨s₀, t, h₀, e⟩ => by
    rw [take_split FTk (n := 1) (m := 6) (by decide)] at e
    obtain ⟨_, _, u₁, -, e₁, e₂⟩ := exec_seqL_append.mp e
    have h₁ : u₁.gpr .s6 = v.L.S := (at_sem (Φ := C0k) (F := FTk) (n := 1) (M := P0)
      (fun _ _ h => WP.of_flat (c := .block Params.entry) rfl (frontK _ _ h)) ⟨s₀, _, h₀, e₁⟩).1.regs.s6
    exact ⟨(Exec.gpr_callFree s6_keptk e₂ rfl).trans h₁, trivial⟩

theorem validate_rel : RelCT isa (Two C0k) Prevalidated.validate fun _ _ => True := by
  refine chain_start (chain_cons runTk (m := 1) (by decide)
    (two_taint _ (pins_mono (pins_a4 fun _ _ h => h.2) fun _ _ h => at_zero_inv h) (by taint_decide)) ?_)
  refine chain_cons runTk (m := 2) (by decide) (two_taint _ (pinsL rfl (pinsT1 frontK)) (by taint_decide)) ?_
  refine chain_cons runTk (m := 4) (by decide) (two_taint _ (pinsL rfl (pinsT2 frontK)) (by taint_decide)) ?_
  refine chain_cons runTk (m := 5) (by decide) (two_taint _ (pinsL rfl (pinsT4 frontK)) (by taint_decide)) ?_
  refine chain_cons runTk (m := 6) (by decide) (rel_ite_at hFTk (zeroL rfl (zeroT frontK)) X1k_rel fail_rel) ?_
  exact two_taint _ pinsTk6 (by taint_decide)

/-- The key's public octets are all of them. -/
theorem leak_all {s : State} (hs : vkContract.pre s) :
    Spec.Dsa.publicBytesLeak (s.gpr .a2).toNat (s.gpr .a3).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) =
      (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat).map (·.toNat) := by
  have := hs.2.2.2.2.2.2.1
  rw [Spec.Dsa.publicBytesLeak, List.take_of_length_le (by rw [VG.Proof.Bignum.bytesAt_length]; omega)]

theorem validate_ct : ConstantTime isa vkContract.pre vkContract.pub Prevalidated.validate :=
  RelCT.constantTime (validate_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨vdP s, ⟨hs, rfl⟩, ⟨ht, (vdP_eq hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1
      ((List.map_inj_right fun _ _ h => BitVec.eq_of_toNat_eq h).mp
        ((leak_all hs).symm.trans (hp.2.2.2.2.2.2.2.trans (leak_all ht))))).symm⟩, hp.1⟩)
    fun _ _ h => h)

end VG.Proof.Dsa.RISCV64.CT
