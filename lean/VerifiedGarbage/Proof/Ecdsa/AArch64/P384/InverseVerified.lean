module

import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.AArch64.P384Literals
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
meta import VerifiedGarbage.Proof.Framework.Pratt
meta import VerifiedGarbage.Impl.Ecdsa.P384.AArch64
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P384Literals
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64.Cfg

/-!
# `vg_p384_inv_mod_p` and `_n` on AArch64: `Verified`

The facts of `Impl.Weierstrass.Inverse.p384`'s contracts for AArch64, by name
(`invK`): `ws` in `x0`, the modulus and a number below it at their offsets.
`invFn_ok` and `invBody_ok` (`Proof/Ecdsa/AArch64/Fixed.lean`) give the power
in `ACC`'s slot, `x19` restored, the other callee-saved registers kept, and
every byte of `ws` kept but those of `chainWc`: `ACC`'s slot and the own
working space (`keeps_of_unch`). The contracts decode a number `x` as
`x R^(m-2)`, the proofs as `x R⁻¹` (`toM`): they agree as `R R^(m-2) = 1`
modulo `p` and `n`, which the kernel computes (`dec_eq`). Constant time by
taint tracking, `x0` and `sp` public.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.P384.Inverse

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P384

/-- P-384's curve of `Proof/Weierstrass/InverseContract.lean`. -/
abbrev C : Impl.Weierstrass.Inverse.Curve := Impl.Weierstrass.Inverse.p384

/-- The inversion modulo `m`, at `modAt`, of the number at `inAt`, on AArch64. -/
def invK (m : Nat) [NeZero m] (modAt inAt : Nat) : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .x0, 8192⟩] ∧ (s.gpr .x0).toNat + 8192 ≤ 2 ^ 64 ∧
    C.num (s.gpr .x0) s.mem modAt = m ∧ C.num (s.gpr .x0) s.mem inAt < m
  post s s' := C.num (s.gpr .x0) s'.mem C.outAt < m ∧
    C.dec m (C.num (s.gpr .x0) s'.mem C.outAt) =
      Spec.Weierstrass.pow (C.dec m (C.num (s.gpr .x0) s.mem inAt)) (m - 2) ∧
    C.Keeps (s.gpr .x0) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.sp = s₂.sp

/-- The number at an offset below `2³²` is the one `wordsVal` reads. -/
theorem num_eq (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) : C.num ws m o = wordsVal m ws o C.k := by
  unfold Impl.Weierstrass.Inverse.Curve.num Impl.Weierstrass.Mont.numAt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  exact read_eq_wordsVal m ws C.k o

/-- The contracts' decoding is the proofs' `toM` modulo any `m` with
`R R^(m-2) = 1`, which `powMod` computes. -/
theorem dec_eq {m : Nat} [NeZero m] (h1 : 1 < m) (he : m - 2 < 2 ^ 400)
    (h : 2 ^ (64 * C.k) * Pratt.powMod m 400 (2 ^ (64 * C.k)) (m - 2) % m = 1) (x : Nat) :
    C.dec m x = toM m (2 ^ (64 * C.k)) x := by
  have hp : Spec.Weierstrass.pow (Fin.ofNat m (2 ^ (64 * C.k))) (m - 2) =
      Fin.ofNat m (Pratt.powMod m 400 (2 ^ (64 * C.k)) (m - 2)) := by
    rw [pow_eq_npow, ← ofNat_pow', Pratt.powMod_eq m h1 _ _ _ he, ofNat_mod]
  have hR : Fin.ofNat m (2 ^ (64 * C.k)) * Fin.ofNat m (Pratt.powMod m 400 (2 ^ (64 * C.k)) (m - 2)) = 1 := by
    rw [← ofNat_mul', ← ofNat_mod, h]; rfl
  have hr := mul_rinv (m := m) ⟨_, hR⟩
  have : Fin.ofNat m (Pratt.powMod m 400 (2 ^ (64 * C.k)) (m - 2)) = rinv m (2 ^ (64 * C.k)) := by
    -- Hide `2 ^ 384` and the like from `grind`'s arithmetic, which would
    -- evaluate it.
    clear h he hp
    generalize 2 ^ (64 * C.k) = R at hR hr ⊢
    grind
  unfold Impl.Weierstrass.Inverse.Curve.dec toM
  rw [hp, this]

theorem dec_eq_p (x : Nat) : C.dec Spec.P384.p x = toM Spec.P384.p (2 ^ (64 * C.k)) x :=
  dec_eq (by decide +kernel) (by decide +kernel) (by decide +kernel) x

theorem dec_eq_n (x : Nat) : C.dec Spec.P384.n x = toM Spec.P384.n (2 ^ (64 * C.k)) x :=
  dec_eq (by decide +kernel) (by decide +kernel) (by decide +kernel) x

/-- The curve's prime and order, as the contracts name them: equal without
evaluating them. -/
theorem curve_p : p384.C.p = Spec.P384.p := by simp only [p384, Spec.P384.curve]
theorem curve_n : p384.C.n = Spec.P384.n := by simp only [p384, Spec.P384.curve]

/-- What the functions write, as offsets: `ACC`'s slot (the result's), the
working slots with `x19`, and the temporary area. -/
theorem chainWc_eq : chainWc p384 = [(1456, 48), (3400, 440), (4048, 48)] := by decide +kernel

theorem keeps_of_unch {ws : Addr} {m m' : Mem} (hu : Unch ws (chainWc p384) m m') : C.Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  show (ws + BitVec.ofNat 64 i - ws).toNat < _ ∨ _ ≤ (ws + BitVec.ofNat 64 i - ws).toNat
  rw [Mem.sub_ofNat_toNat ws (by omega)]
  simp only [Impl.Weierstrass.Inverse.Curve.Own, Impl.Weierstrass.Inverse.Curve.slot,
    Impl.Weierstrass.Inverse.Curve.tmpAt, Impl.Weierstrass.Inverse.Curve.workAt,
    Impl.Weierstrass.Inverse.Curve.workLen, Impl.Weierstrass.Inverse.Curve.outAt, C,
    Impl.Weierstrass.Inverse.p384] at hown hp
  rw [chainWc_eq] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> dsimp only <;> omega

/-- `vg_p384_inv_mod_p`'s contract, by name. -/
abbrev pK : Contract isa := invK Spec.P384.p C.pAt C.zAt
/-- `vg_p384_inv_mod_n`'s contract, by name. -/
abbrev nK : Contract isa := invK Spec.P384.n C.nAt C.xAt

theorem inverse_ne : p384.inverse ≠ none := Option.some_ne_none _

/-- The contract's postcondition, from the proofs' facts modulo `m₀ = m`. -/
theorem post_of {m : Nat} [NeZero m] {inAt : Nat} (hin : inAt < 2 ^ 32)
    (hdec : ∀ x, C.dec m x = toM m (2 ^ (64 * C.k)) x) {ws : Addr} {mem mem' : Mem} {m₀ : Nat} [NeZero m₀]
    (hm₀ : m = m₀) (lt : wordsVal mem' ws C.outAt C.k < m₀)
    (v : toM m₀ (2 ^ (64 * C.k)) (wordsVal mem' ws C.outAt C.k) =
      toM m₀ (2 ^ (64 * C.k)) (wordsVal mem ws inAt C.k) ^ (m₀ - 2))
    (U : Unch ws (chainWc p384) mem mem') :
    C.num ws mem' C.outAt < m ∧
      C.dec m (C.num ws mem' C.outAt) = Spec.Weierstrass.pow (C.dec m (C.num ws mem inAt)) (m - 2) ∧
      C.Keeps ws mem mem' := by
  subst hm₀
  refine ⟨by rw [num_eq _ _ (by decide)]; exact lt, ?_, keeps_of_unch U⟩
  rw [num_eq _ _ (by decide), num_eq _ _ hin, hdec, hdec, pow_eq_npow]
  exact v

theorem p_correct (hI : InvSounds) (s : State) (hs : pK.pre s) :
    ∃ t s', Exec isa (p384.invFn p384.pPowI) s t s' ∧ abiPreserved s s' ∧ pK.post s s' := by
  obtain ⟨-, hwr, hfit, hm, hz⟩ := hs
  have hc := (p384_ok hI).toBaseCfgOk
  have hS : Scr s (s.gpr .x0) size := ⟨rfl, by rw [hwr]; simp, hfit, by decide⟩
  have em : wordsVal s.mem (s.gpr .x0) (p384.sl MP) p384.n = C.num (s.gpr .x0) s.mem C.pAt := by
    rw [num_eq _ _ (by decide)]; rfl
  have ez : wordsVal s.mem (s.gpr .x0) (p384.sl RZ) p384.n = C.num (s.gpr .x0) s.mem C.zAt := by
    rw [num_eq _ _ (by decide)]; rfl
  rw [← em, ← curve_p] at hm
  rw [← ez, ← curve_p] at hz
  have hM := modOkA_inv hc (modP_of hc hm) (.inl rfl) rfl rfl
  have := hc.p_ge
  obtain ⟨t, s', he, K, U, lt, v⟩ := invFn_ok hc inverse_ne hS (body := p384.pPowI)
    (R := fun _ m' => wordsVal m' (s.gpr .x0) (p384.sl ACC) p384.n < p384.C.p ∧
      toM p384.C.p (2 ^ (64 * p384.n)) (wordsVal m' (s.gpr .x0) (p384.sl ACC) p384.n) =
        toM p384.C.p (2 ^ (64 * p384.n)) (wordsVal s.mem (s.gpr .x0) (p384.sl RZ) p384.n) ^ (p384.C.p - 2))
    (fun u hu hU => invBody_ok hc inverse_ne hc.sound_p (invLayP hc) hc.inv_p (by omega)
      (unitMod_pow_two hc.p_odd _) rfl rfl rfl rfl (b := RZ) rfl (by decide) (by decide) (jm := MP) rfl
      (by decide) (by decide) hS hM hz hu hU)
  have hk : p384.n = C.k := rfl
  have hacc : p384.sl ACC = C.outAt := rfl
  have hin : p384.sl RZ = C.zAt := rfl
  rw [hk, hacc] at lt v
  rw [hin] at v
  exact ⟨t, s', he, ⟨fun r hr => K.gpr r (by revert r; decide), K.sp, Exec.preservedV he
    (show (p384.invFn p384.pPowI).allInstrs keepsV = true by lit_decide)⟩,
    post_of (by decide) dec_eq_p curve_p.symm lt v U⟩

theorem n_correct (hI : InvSounds) (s : State) (hs : nK.pre s) :
    ∃ t s', Exec isa (p384.invFn p384.nPowI) s t s' ∧ abiPreserved s s' ∧ nK.post s s' := by
  obtain ⟨-, hwr, hfit, hm, hx⟩ := hs
  have hc := (p384_ok hI).toBaseCfgOk
  have hS : Scr s (s.gpr .x0) size := ⟨rfl, by rw [hwr]; simp, hfit, by decide⟩
  have em : wordsVal s.mem (s.gpr .x0) (p384.sl MN) p384.n = C.num (s.gpr .x0) s.mem C.nAt := by
    rw [num_eq _ _ (by decide)]; rfl
  have ex : wordsVal s.mem (s.gpr .x0) (p384.sl KM) p384.n = C.num (s.gpr .x0) s.mem C.xAt := by
    rw [num_eq _ _ (by decide)]; rfl
  rw [← em, ← curve_n] at hm
  rw [← ex, ← curve_n] at hx
  have hM := modOkA_inv hc (modN_of hc hm) (.inr rfl) rfl rfl
  have := hc.n_ge
  have hf : p384.fastN = true := rfl
  obtain ⟨t, s', he, K, U, lt, v⟩ := invFn_ok hc inverse_ne hS (body := p384.nPowI)
    (R := fun _ m' => wordsVal m' (s.gpr .x0) (p384.sl ACC) p384.n < p384.C.n ∧
      toM p384.C.n (2 ^ (64 * p384.n)) (wordsVal m' (s.gpr .x0) (p384.sl ACC) p384.n) =
        toM p384.C.n (2 ^ (64 * p384.n)) (wordsVal s.mem (s.gpr .x0) (p384.sl KM) p384.n) ^ (p384.C.n - 2))
    (fun u hu hU => by
      rw [Cfg.nPowI, ite_eq_left_iff.mpr (fun h => absurd hf h)]
      exact invBody_ok hc inverse_ne (hc.inv_n hf).1 (invLayN hc) (hc.inv_n hf).2 (by omega)
        (unitMod_pow_two hc.n_odd _) rfl rfl rfl rfl (b := KM) rfl (by decide) (by decide) (jm := MN) rfl
        (by decide) (by decide) hS hM hx hu hU)
  have hk : p384.n = C.k := rfl
  have hacc : p384.sl ACC = C.outAt := rfl
  have hin : p384.sl KM = C.xAt := rfl
  rw [hk, hacc] at lt v
  rw [hin] at v
  exact ⟨t, s', he, ⟨fun r hr => K.gpr r (by revert r; decide), K.sp, Exec.preservedV he
    (show (p384.invFn p384.nPowI).allInstrs keepsV = true by lit_decide)⟩,
    post_of (by decide) dec_eq_n curve_n.symm lt v U⟩

theorem agree {m : Nat} [NeZero m] {modAt inAt : Nat} (s₁ s₂ : State) (_ : (invK m modAt inAt).pre s₁)
    (_ : (invK m modAt inAt).pre s₂) (h : (invK m modAt inAt).pub s₁ s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x0]) s₁ s₂ :=
  ⟨h.2, fun r hr => by
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.1⟩

/-- Constant time by taint tracking, `x0` and `sp` public. -/
theorem p_ct : ConstantTime isa pK.pre pK.pub (p384.invFn p384.pPowI) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0]) agree (by taint_decide)

theorem n_ct : ConstantTime isa nK.pre nK.pub (p384.invFn p384.nPowI) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0]) agree (by taint_decide)

/-- The memory of `satState`: P-384's `p` and `n` at `ws + 64` and
`ws + 112` for `ws = 0x1000`, zeros elsewhere. -/
@[irreducible] def satMem : Mem := fun a =>
  if 0x1040 ≤ a.toNat ∧ a.toNat < 0x1070 then BitVec.ofNat 8 (Spec.P384.p >>> (8 * (a.toNat - 0x1040)))
  else if 0x1070 ≤ a.toNat ∧ a.toNat < 0x10a0 then BitVec.ofNat 8 (Spec.P384.n >>> (8 * (a.toNat - 0x1070)))
  else 0

/-- A state satisfying the preconditions. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | _ => 0
  sp := 0x10000
  mem := satMem
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem sat_p : C.num 0x1000 satMem C.pAt = Spec.P384.p ∧ C.num 0x1000 satMem C.zAt < Spec.P384.p :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem sat_n : C.num 0x1000 satMem C.nAt = Spec.P384.n ∧ C.num 0x1000 satMem C.xAt < Spec.P384.n :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem p_implies : pK.Implies (C.invPContract AArch64.abi) where
  pre s h := by
    sig_pre [Impl.Weierstrass.Inverse.Curve.invPContract, Impl.Weierstrass.Inverse.Curve.invContract,
      Impl.Weierstrass.Inverse.sig, AArch64.abi, AArch64.argRegs, stackBelow] at h
    exact h
  post s s' _ h := by
    sig_post [Impl.Weierstrass.Inverse.Curve.invPContract, Impl.Weierstrass.Inverse.Curve.invContract,
      Impl.Weierstrass.Inverse.sig, AArch64.abi, AArch64.argRegs]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Impl.Weierstrass.Inverse.Curve.invPContract, Impl.Weierstrass.Inverse.Curve.invContract,
      Impl.Weierstrass.Inverse.sig, AArch64.abi, AArch64.argRegs] at h
    exact ⟨h.2, h.1⟩
  sat := ⟨satState, by
    sig_pre [Impl.Weierstrass.Inverse.Curve.invPContract, Impl.Weierstrass.Inverse.Curve.invContract,
      Impl.Weierstrass.Inverse.sig, AArch64.abi, AArch64.argRegs, stackBelow]
    exact ⟨by decide, sat_p⟩⟩

theorem n_implies : nK.Implies (C.invNContract AArch64.abi) where
  pre s h := by
    sig_pre [Impl.Weierstrass.Inverse.Curve.invNContract, Impl.Weierstrass.Inverse.Curve.invContract,
      Impl.Weierstrass.Inverse.sig, AArch64.abi, AArch64.argRegs, stackBelow] at h
    exact h
  post s s' _ h := by
    sig_post [Impl.Weierstrass.Inverse.Curve.invNContract, Impl.Weierstrass.Inverse.Curve.invContract,
      Impl.Weierstrass.Inverse.sig, AArch64.abi, AArch64.argRegs]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Impl.Weierstrass.Inverse.Curve.invNContract, Impl.Weierstrass.Inverse.Curve.invContract,
      Impl.Weierstrass.Inverse.sig, AArch64.abi, AArch64.argRegs] at h
    exact ⟨h.2, h.1⟩
  sat := ⟨satState, by
    sig_pre [Impl.Weierstrass.Inverse.Curve.invNContract, Impl.Weierstrass.Inverse.Curve.invContract,
      Impl.Weierstrass.Inverse.sig, AArch64.abi, AArch64.argRegs, stackBelow]
    exact ⟨by decide, sat_n⟩⟩

/-- `vg_p384_inv_mod_p` on AArch64. -/
theorem p_verified (hI : InvSounds) :
    Verified AArch64.target (p384.invFn p384.pPowI) (C.invPContract AArch64.abi) :=
  Verified.of_correct (p_correct hI) p_ct p_implies

/-- `vg_p384_inv_mod_n` on AArch64. -/
theorem n_verified (hI : InvSounds) :
    Verified AArch64.target (p384.invFn p384.nPowI) (C.invNContract AArch64.abi) :=
  Verified.of_correct (n_correct hI) n_ct n_implies

end VG.Proof.Ecdsa.AArch64.P384.Inverse
