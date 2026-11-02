module

public import VerifiedGarbage.Proof.Dsa.RISCV64.CTBase
public import VerifiedGarbage.Proof.Dsa.RISCV64.CTKey
public import VerifiedGarbage.Proof.Dsa.RISCV64.CTParams
public import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFront
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn
import VerifiedGarbage.Proof.Framework.Flat
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTBase
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTKey
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTParams
meta import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFront
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn
meta import VerifiedGarbage.Proof.Framework.Flat
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA domain checks on RISC-V: constant time

`vg_dsa_check_parameters` (`Params.checkParameters`) runs `Params.entry`,
then `checkParams` with the status 1 or 0, then `restore`. Its public data
(`vdP`) is the domain's octets with no signature or digest; `pfront_P0`
gives verification's phase `P0` after `Params.entry`, which
`vg_dsa_validate_public_key` shares (`ValidateCT.lean`). Its levels are
verification's (`CTBase.lean`) up to g's check, whose passing side is the
status 1 (`ok_rel`): their lists start with the same programs, so their
cuts' registers, branches and phases are verification's (`atL`, `pinsL`,
`zeroL`, `relL`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_taint)
open VG.Proof.Bignum.RISCV64 (At chain_cons chain_start at_zero_inv)

/-! ## Lists with the same first programs -/

theorem atL {α : Type} {Φ : α → State → Prop} {F F' : List (Prog isa)} {n : Nat} (hF : F'.take n = F.take n)
    {a : α} {u : State} (h : At Φ F' n a u) : At Φ F n a u :=
  at_mono (fun _ _ h => h) hF h

theorem pinsL {α : Type} {Φ : α → State → Prop} {F F' : List (Prog isa)} {n : Nat} {rs : List Reg}
    (hF : F'.take n = F.take n) (h : Pins (At Φ F n) rs) : Pins (At Φ F' n) rs :=
  pins_mono h fun _ _ h => atL hF h

theorem zeroL {α : Type} {Φ : α → State → Prop} {F F' : List (Prog isa)} {n : Nat} (hF : F'.take n = F.take n)
    (hz : ∀ a s₁ s₂, At Φ F n a s₁ → At Φ F n a s₂ → (s₁.gpr .a0 == 0) = (s₂.gpr .a0 == 0)) :
    ∀ a s₁ s₂, At Φ F' n a s₁ → At Φ F' n a s₂ → (s₁.gpr .a0 == 0) = (s₂.gpr .a0 == 0) :=
  fun a _ _ h₁ h₂ => hz a _ _ (atL hF h₁) (atL hF h₂)

theorem relL {α : Type} {Φ : α → State → Prop} {F F' : List (Prog isa)} {n m : Nat} (hF : F'.take n = F.take n)
    (hs : seg F' n m = seg F n m) (h : RelCT isa (Two (At Φ F n)) (seg F n m) fun _ _ => True) :
    RelCT isa (Two (At Φ F' n)) (seg F' n m) fun _ _ => True := by
  rw [hs]
  exact h.mono (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨a, atL hF h₁, atL hF h₂, hsp⟩) fun _ _ h => h

/-- The passing side of the checks: 1 into `a0`. -/
abbrev ok1 : Prog isa := .block [.li .a0 1]

theorem ok_rel {α : Type} {Ψ : α → State → Prop} : RelCT isa (Two Ψ) ok1 fun _ _ => True :=
  two_taint [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)

/-! ## The entry -/

/-- A call's public data, for the domain's or the key's octets at `a0` (`a1`
of them) and `scratch` at `a4`. -/
def vdP (s : State) : VD :=
  ⟨playOf s, s.gpr .a0, 0, 0, 0, Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat, (s.gpr .a1).toNat, 0,
    false, none⟩

theorem src_nil {s : State} {L : Lay} {D : Addr} {n : Nat} (hn : n = 0) : Src s L D n :=
  ⟨fun _ h => absurd (hn ▸ h) (Nat.not_lt_zero _), fun _ h => absurd (hn ▸ h) (Nat.not_lt_zero _)⟩

/-- `Params.entry` leaves `P0`. -/
theorem pfront_P0 {s : State} (hL : (playOf s).Ok) (hrd : s.rd = [⟨s.gpr .a0, (s.gpr .a1).toNat⟩])
    (hwr : s.wr = [⟨s.gpr .a4, (s.gpr .a5).toNat * 8⟩])
    (dPS : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint ⟨s.gpr .a4, (s.gpr .a5).toNat * 8⟩)
    (nw : (s.gpr .a4).toNat + (s.gpr .a5).toNat * 8 ≤ 2 ^ 64) (alS : (s.gpr .a4).toNat % 8 = 0)
    (hkn : 2 * (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ (s.gpr .a1).toNat) :
    WP isa (.block Params.entry) s (P0 (vdP s)) := by
  have hZ := hL.z256
  refine WP.mono (pfront_ok_of hL hwr nw alS) fun t ⟨F, k⟩ => ?_
  have hK : Src t (playOf s) (s.gpr .a0) (s.gpr .a1).toNat := psrc_of hrd dPS (Nat.le_refl _) k.2.1 k.2.2
  exact ⟨⟨hL, F.regs, F.scr, hK, src_nil rfl, src_nil (Nat.zero_min _),
    hK.bytes F.out (by simp only [playOf] at hZ ⊢; omega), (by simp only [vdP, playOf]; omega),
    (fun h => nomatch h), fun _ h => nomatch h⟩, F.lens.trans (congrArg _ (Nat.zero_min _).symm)⟩

/-- Runs that agree on `a0` to `a5` and on the octets at `a0` have the same public data `vdP`. -/
theorem vdP_eq {s t : State} (e0 : s.gpr .a0 = t.gpr .a0) (e1 : s.gpr .a1 = t.gpr .a1)
    (e2 : s.gpr .a2 = t.gpr .a2) (e3 : s.gpr .a3 = t.gpr .a3) (e4 : s.gpr .a4 = t.gpr .a4)
    (e5 : s.gpr .a5 = t.gpr .a5)
    (hb : Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .a0) (t.gpr .a1).toNat) :
    vdP s = vdP t := by
  simp only [vdP, playOf]
  rw [hb, e0, e1, e2, e3, e4, e5]

/-- `a4` is public. -/
theorem pins_a4 {Φ : VD → State → Prop} (h : ∀ v s, Φ v s → vdP s = v) : Pins Φ [.a4] := by
  intro v s₁ s₂ h₁ h₂ r hr
  rw [List.mem_singleton] at hr
  subst hr
  exact congrArg (fun v : VD => v.L.S) ((h _ _ h₁).trans (h _ _ h₂).symm)

/-! ## `vg_dsa_check_parameters`'s levels -/

/-- On entry. -/
def C0c (v : VD) (s : State) : Prop := pcContract.pre s ∧ vdP s = v

theorem frontC : ∀ v s, C0c v s → WP isa (.block Params.entry) s (P0 v) := by
  rintro _ s ⟨h, rfl⟩
  exact pfront_P0 (playOf_ok h) h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1
    (by have := h.2.2.2.2.2.2.1; omega)

abbrev R3c : Prog isa := .seq setupP (andThen (.seq (.block ptrG) checkElem) ok1 fail0)
abbrev R2c : Prog isa := andThen pModQ R3c fail0
abbrev R1c : Prog isa := andThen (.block (ptrQ ++ odd)) R2c fail0
abbrev R0c : Prog isa := odds R2c fail0
abbrev X2c : Prog isa :=
  .seq (.block [.addi .a3 .a1 0, .shift .sll .d .t3 .a1 32, .load .d .t4 .s6 hLens, .add .t4 .t4 .t3,
    .store .d .t4 .s6 hLens]) (andThen pairs R0c fail0)
abbrev X1c : Prog isa := .seq (.block [.addi .a2 .a1 0]) (andThen (.seq (.block ptrQ) bytesBits) X2c fail0)

abbrev FTc : List (Prog isa) := Code.flat Params.checkParameters
abbrev FX1c : List (Prog isa) := Code.flat X1c
abbrev FX2c : List (Prog isa) := Code.flat X2c
abbrev FR0c : List (Prog isa) := Code.flat R0c
abbrev FR1c : List (Prog isa) := Code.flat R1c
abbrev FR2c : List (Prog isa) := Code.flat R2c
abbrev FR3c : List (Prog isa) := Code.flat R3c

abbrev ΦX1c (v : VD) (u : State) : Prop := At C0c FTc 5 v u ∧ u.gpr .a0 = 0
abbrev ΦX2c (v : VD) (u : State) : Prop := At ΦX1c FX1c 5 v u ∧ u.gpr .a0 = 0
abbrev ΦR0c (v : VD) (u : State) : Prop := At ΦX2c FX2c 12 v u ∧ u.gpr .a0 = 0
abbrev ΦR1c (v : VD) (u : State) : Prop := At ΦR0c FR0c 1 v u ∧ u.gpr .a0 = 0
abbrev ΦR2c (v : VD) (u : State) : Prop := At ΦR1c FR1c 1 v u ∧ u.gpr .a0 = 0
abbrev ΦR3c (v : VD) (u : State) : Prop := At ΦR2c FR2c 23 v u ∧ u.gpr .a0 = 0
abbrev ΦEgc (v : VD) (u : State) : Prop := At ΦR3c FR3c 45 v u ∧ u.gpr .a0 = 0

theorem hFTc : (FTc.drop 5).take 1 = [.ite (.zero .a0) X1c fail0] := rfl
theorem hFX1c : (FX1c.drop 5).take 1 = [.ite (.zero .a0) X2c fail0] := rfl
theorem hFX2c : (FX2c.drop 12).take 1 = [.ite (.zero .a0) R0c fail0] := rfl
theorem hFR0c : (FR0c.drop 1).take 1 = [.ite (.zero .a0) R1c fail0] := rfl
theorem hFR1c : (FR1c.drop 1).take 1 = [.ite (.zero .a0) R2c fail0] := rfl
theorem hFR2c : (FR2c.drop 23).take 1 = [.ite (.zero .a0) R3c fail0] := rfl
theorem hFR3gc : (FR3c.drop 45).take 1 = [.ite (.zero .a0) elemOrder (.block [])] := rfl
theorem hFR3c : (FR3c.drop 46).take 1 = [.ite (.zero .a0) ok1 fail0] := rfl

theorem runTc : ∀ v s, C0c v s → WP isa (Code.seqL FTc) s fun _ => True := fun _ s h =>
  let ⟨tr, t, e, _⟩ := checkParameters_correct s h.1
  ⟨tr, t, exec_flat.mp e, trivial⟩

theorem runX1c : ∀ v s, ΦX1c v s → WP isa (Code.seqL FX1c) s fun _ => True := run_then runTc hFTc
theorem runX2c : ∀ v s, ΦX2c v s → WP isa (Code.seqL FX2c) s fun _ => True := run_then runX1c hFX1c
theorem runR0c : ∀ v s, ΦR0c v s → WP isa (Code.seqL FR0c) s fun _ => True := run_then runX2c hFX2c
theorem runR1c : ∀ v s, ΦR1c v s → WP isa (Code.seqL FR1c) s fun _ => True := run_then runR0c hFR0c
theorem runR2c : ∀ v s, ΦR2c v s → WP isa (Code.seqL FR2c) s fun _ => True := run_then runR1c hFR1c
theorem runR3c : ∀ v s, ΦR3c v s → WP isa (Code.seqL FR3c) s fun _ => True := run_then runR2c hFR2c
theorem runEgc : ∀ v s, ΦEgc v s → WP isa (Code.seqL FE) s fun _ => True := run_then runR3c hFR3gc

theorem onX1c : ∀ v u, ΦX1c v u → SX1 v u := fun _ _ h => semX1 frontC ⟨atL rfl h.1, h.2⟩
theorem onX2c : ∀ v u, ΦX2c v u → SX2 v u := fun _ _ h => semX2 onX1c ⟨atL rfl h.1, h.2⟩
theorem onR0c : ∀ v u, ΦR0c v u → P1 v u := fun _ _ h => semR0 onX2c ⟨atL rfl h.1, h.2⟩
theorem onR1c : ∀ v u, ΦR1c v u → P1 v u ∧ v.p % 2 = 1 := fun _ _ h => semR1 onR0c ⟨atL rfl h.1, h.2⟩
theorem onR2c : ∀ v u, ΦR2c v u → SR2 v u := fun _ _ h => semR2 onR1c ⟨atL rfl h.1, h.2⟩
theorem onR3c : ∀ v u, ΦR3c v u → SR3 v u := fun _ _ h => semR3 onR2c ⟨atL rfl h.1, h.2⟩

/-! ## The levels' relations -/

theorem R3c_rel : RelCT isa (Two ΦR3c) R3c fun _ _ => True := by
  refine chain_start (chain_cons runR3c (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsR3_0 onR3c)) (by taint_decide)) ?_)
  refine chain_cons runR3c (m := 18) (by decide) (two_taint _ (pinsL rfl (pinsR3_2 onR3c)) (by taint_decide)) ?_
  refine chain_cons runR3c (m := 45) (by decide) (two_taint _ (pinsL rfl (pinsR3_18 onR3c)) (by taint_decide)) ?_
  refine chain_cons runR3c (m := 46) (by decide) (rel_ite_at hFR3gc (zeroL rfl (zeroEg onR3c))
    (eo_rel runEgc fun _ _ h => semEg onR3c ⟨atL rfl h.1, h.2⟩) nil_rel) ?_
  exact chain_cons runR3c (m := 47) (by decide) (rel_ite_at hFR3c (zeroL rfl (zeroR3 onR3c)) ok_rel fail_rel)
    nil_rel

theorem R2c_rel : RelCT isa (Two ΦR2c) R2c fun _ _ => True := by
  refine chain_start (chain_cons runR2c (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsR2_0 onR2c)) (by taint_decide)) ?_)
  refine chain_cons runR2c (m := 10) (by decide) (two_taint _ (pinsL rfl (pinsR2_2 onR2c)) (by taint_decide)) ?_
  refine chain_cons runR2c (m := 23) (by decide) (two_taint _ (pinsL rfl (pinsR2_10 onR2c)) (by taint_decide)) ?_
  exact chain_cons runR2c (m := 24) (by decide) (rel_ite_at hFR2c (zeroL rfl (zeroR2 onR2c)) R3c_rel fail_rel)
    nil_rel

theorem R1c_rel : RelCT isa (Two ΦR1c) R1c fun _ _ => True :=
  chain_start (chain_cons runR1c (m := 1) (by decide) (relL rfl rfl (relR1 onR1c))
    (chain_cons runR1c (m := 2) (by decide) (rel_ite_at hFR1c (zeroL rfl (zeroR1 onR1c)) R2c_rel fail_rel)
      nil_rel))

theorem R0c_rel : RelCT isa (Two ΦR0c) R0c fun _ _ => True :=
  chain_start (chain_cons runR0c (m := 1) (by decide) (relL rfl rfl (relR0 onR0c))
    (chain_cons runR0c (m := 2) (by decide) (rel_ite_at hFR0c (zeroL rfl (zeroR0 onR0c)) R1c_rel fail_rel)
      nil_rel))

theorem X2c_rel : RelCT isa (Two ΦX2c) X2c fun _ _ => True :=
  chain_start (chain_cons runX2c (m := 12) (by decide)
    (two_taint _ (pinsL rfl (pinsX2_0 onX2c)) (by taint_decide))
    (chain_cons runX2c (m := 13) (by decide) (rel_ite_at hFX2c (zeroL rfl (zeroX2 onX2c)) R0c_rel fail_rel)
      nil_rel))

theorem X1c_rel : RelCT isa (Two ΦX1c) X1c fun _ _ => True := by
  refine chain_start (chain_cons runX1c (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsX1_0 onX1c)) (by taint_decide)) ?_)
  refine chain_cons runX1c (m := 4) (by decide) (two_taint _ (pinsL rfl (pinsX1_2 onX1c)) (by taint_decide)) ?_
  refine chain_cons runX1c (m := 5) (by decide) (two_taint _ (pinsL rfl (pinsX1_4 onX1c)) (by taint_decide)) ?_
  exact chain_cons runX1c (m := 6) (by decide) (rel_ite_at hFX1c (zeroL rfl (zeroX1 onX1c)) X2c_rel fail_rel)
    nil_rel

theorem s6_keptc : ∀ i ∈ instrs (seg FTc 1 6), dstOf i ≠ some .s6 := by
  have h : (instrs (seg FTc 1 6)).all (fun i => dstOf i != some .s6) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem pinsTc6 : Pins (At C0c FTc 6) [.s6] :=
  pins_fix (fun v => [(.s6, v.L.S)]) (fun _ => rfl) fun v u ⟨s₀, t, h₀, e⟩ => by
    rw [take_split FTc (n := 1) (m := 6) (by decide)] at e
    obtain ⟨_, _, u₁, -, e₁, e₂⟩ := exec_seqL_append.mp e
    have h₁ : u₁.gpr .s6 = v.L.S := (at_sem (Φ := C0c) (F := FTc) (n := 1) (M := P0)
      (fun _ _ h => WP.of_flat (c := .block Params.entry) rfl (frontC _ _ h)) ⟨s₀, _, h₀, e₁⟩).1.regs.s6
    exact ⟨(Exec.gpr_callFree s6_keptc e₂ rfl).trans h₁, trivial⟩

theorem check_rel : RelCT isa (Two C0c) Params.checkParameters fun _ _ => True := by
  refine chain_start (chain_cons runTc (m := 1) (by decide)
    (two_taint _ (pins_mono (pins_a4 fun _ _ h => h.2) fun _ _ h => at_zero_inv h) (by taint_decide)) ?_)
  refine chain_cons runTc (m := 2) (by decide) (two_taint _ (pinsL rfl (pinsT1 frontC)) (by taint_decide)) ?_
  refine chain_cons runTc (m := 4) (by decide) (two_taint _ (pinsL rfl (pinsT2 frontC)) (by taint_decide)) ?_
  refine chain_cons runTc (m := 5) (by decide) (two_taint _ (pinsL rfl (pinsT4 frontC)) (by taint_decide)) ?_
  refine chain_cons runTc (m := 6) (by decide) (rel_ite_at hFTc (zeroL rfl (zeroT frontC)) X1c_rel fail_rel) ?_
  exact two_taint _ pinsTc6 (by taint_decide)

theorem check_ct : ConstantTime isa pcContract.pre pcContract.pub Params.checkParameters :=
  RelCT.constantTime (check_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨vdP s, ⟨hs, rfl⟩, ⟨ht, (vdP_eq hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1
      ((List.map_inj_right fun _ _ h => BitVec.eq_of_toNat_eq h).mp hp.2.2.2.2.2.2.2)).symm⟩, hp.1⟩)
    fun _ _ h => h)

end VG.Proof.Dsa.RISCV64.CT
