module

import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.InvFnX
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Inv
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.InverseLit
public import VerifiedGarbage.Impl.Ecdsa.P192.X86_64
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.Lit
import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.InvFnX
meta import VerifiedGarbage.Proof.Framework.Pratt
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.InverseLit
meta import VerifiedGarbage.Impl.Ecdsa.P192.X86_64
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare

/-!
# `vg_p192_inv_mod_p` and `_n` on x86-64: `Verified`

The facts of `Impl.Weierstrass.Inverse.p192`'s contracts for x86-64, by name
(`invK`): `ws` in `rdi`, the modulus and a number below it at their offsets.
`invFn_ok` and `invP_ok` (`invN_ok`) give the power in `ACC`'s slot, the
callee-saved registers restored, and every byte of `ws` kept but those of
`ACC`'s slot and of `pwW`, the own working space (`inv_correct`). The
contracts decode a number `x` as `x R^(m-2)`, the proofs as `x R⁻¹` (`toM`):
they agree as `R R^(m-2) = 1` modulo `p` and `n`, which the kernel computes
(`dec_eq`). Constant time by taint tracking, `rdi` and `rsp` public.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.P192.Inverse

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64

/-- P-192's curve of `Proof/Weierstrass/InverseContract.lean`. -/
abbrev C : Impl.Weierstrass.Inverse.Curve := Impl.Weierstrass.Inverse.p192

/-- The configuration of the functions, which have no `_adx` forms. -/
abbrev cfg (_ : Bool) : Cfg := p192

/-- The inversion modulo `m`, at `modAt`, of the number at `inAt`, on x86-64. -/
def invK (m : Nat) [NeZero m] (modAt inAt : Nat) : Contract isa where
  pre s :=
    let ws : Region := ⟨s.gpr .rdi, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [ws] ∧ ret.Disjoint ws ∧ (s.gpr .rdi).toNat + 8192 ≤ 2 ^ 64 ∧
      C.num (s.gpr .rdi) s.mem modAt = m ∧ C.num (s.gpr .rdi) s.mem inAt < m
  post s s' := C.num (s.gpr .rdi) s'.mem C.outAt < m ∧
    C.dec m (C.num (s.gpr .rdi) s'.mem C.outAt) =
      Spec.Weierstrass.pow (C.dec m (C.num (s.gpr .rdi) s.mem inAt)) (m - 2) ∧
    C.Keeps (s.gpr .rdi) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi

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

theorem dec_eq_p (x : Nat) : C.dec Spec.P192.p x = toM Spec.P192.p (2 ^ (64 * C.k)) x :=
  dec_eq (by decide +kernel) (by decide +kernel) (by decide +kernel) x

theorem dec_eq_n (x : Nat) : C.dec Spec.P192.n x = toM Spec.P192.n (2 ^ (64 * C.k)) x :=
  dec_eq (by decide +kernel) (by decide +kernel) (by decide +kernel) x

theorem cfg_ok (hI : InvSounds) (adx : Bool) : BaseCfgOk (cfg adx) := p192_ok hI

theorem cfg_n (adx : Bool) : (cfg adx).n = 4 := rfl
theorem cfg_C (adx : Bool) : (cfg adx).C = Spec.P192.curve := rfl
theorem cfg_sl (adx : Bool) (i : Nat) : (cfg adx).sl i = p192.sl i := rfl
theorem cfg_fastN (adx : Bool) : (cfg adx).fastN = true := rfl

/-- What the functions write, as offsets: `ACC`'s slot (the result's) and the
own working space. -/
theorem pwW_eq (adx : Bool) : pwW (cfg adx) = [(992, 32), (1024, 32), (128, 32), (2296, 320)] := by
  show pwW p192 = _; decide

theorem keeps_of_unch {ws : Addr} {m m' : Mem} (adx : Bool) (hu : Unch ws (pwW (cfg adx)) m m') :
    C.Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  show (ws + BitVec.ofNat 64 i - ws).toNat < _ ∨ _ ≤ (ws + BitVec.ofNat 64 i - ws).toNat
  rw [Mem.sub_ofNat_toNat ws (by omega)]
  simp only [Impl.Weierstrass.Inverse.Curve.Own, Impl.Weierstrass.Inverse.Curve.slot,
    Impl.Weierstrass.Inverse.Curve.tmpAt, Impl.Weierstrass.Inverse.Curve.workAt,
    Impl.Weierstrass.Inverse.Curve.workLen, Impl.Weierstrass.Inverse.Curve.outAt, C,
    Impl.Weierstrass.Inverse.p192] at hown hp
  rw [pwW_eq] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> dsimp only <;> omega

theorem mxcsrP (adx : Bool) : ((cfg adx).invFn (cfg adx).pPowI).allInstrs (fun i => !loadsMxcsr i) = true := by
  show invP.allInstrs _ = true; lit_decide

theorem mxcsrN (adx : Bool) : ((cfg adx).invFn (cfg adx).nPowI).allInstrs (fun i => !loadsMxcsr i) = true := by
  show invN.allInstrs _ = true; lit_decide

theorem hvP (adx : Bool) : (cfg adx).pPowI.allInstrs (fun i => !KeepReg.writesVec i) = true := by
  show bodyP.allInstrs _ = true; lit_decide

theorem hvN (adx : Bool) : (cfg adx).nPowI.allInstrs (fun i => !KeepReg.writesVec i) = true := by
  show bodyN.allInstrs _ = true; lit_decide

theorem hncP (adx : Bool) : (cfg adx).pPowI.noCalls = true := by
  show bodyP.noCalls = true; lit_decide

theorem hncN (adx : Bool) : (cfg adx).nPowI.noCalls = true := by
  show bodyN.noCalls = true; lit_decide

/-- The callee-saved registers come back: the function is `invFnX` at four
words (`invFnX_gpr`). -/
theorem saved_of {body : Prog isa} (adx : Bool)
    (hv : body.allInstrs (fun i => !KeepReg.writesVec i) = true) (hn : body.noCalls = true)
    {s s' : State} {t : List Leak} (he : Exec isa ((cfg adx).invFn body) s t s') :
    ∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s.gpr r := by
  have h4 : (cfg adx).n < 6 := by rw [cfg_n]; decide
  rw [show (cfg adx).invFn body = Cfg.invFnX body from ite_eq_left_of_eq_true _ _ (eq_true h4)] at he
  intro r hr
  exact invFnX_gpr hv hn he r (by
    simp only [Cfg.saved, Cfg.invKeptX, List.map_cons, List.map_nil] at hr ⊢; exact hr)

/-- From what `invFn_ok` gives: the ABI's registers and return address, and
the result's facts. -/
theorem finish {code : Prog isa} (hmx : code.allInstrs (fun i => !loadsMxcsr i) = true) (adx : Bool)
    {m : Nat} [NeZero m] {modAt : Nat} {s : State} (hwr : s.wr = [⟨s.gpr .rdi, 8192⟩])
    (hret : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 8192⟩) {inAt : Nat} (hin : inAt < 2 ^ 32)
    (hdec : ∀ x, C.dec m x = toM m (2 ^ (64 * C.k)) x) {t : List Leak} {s' : State}
    (he : Exec isa code s t s') (hnc : code.noCalls = true)
    (sv : ∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s.gpr r)
    (K : KeepRegs (invClob (cfg adx).n) s s') (U : Unch (s.gpr .rdi) (pwW (cfg adx)) s.mem s'.mem)
    {m₀ : Nat} [NeZero m₀] (hm₀ : m = m₀)
    (lt : wordsVal s'.mem (s.gpr .rdi) ((cfg adx).sl ACC) (cfg adx).n < m₀)
    (v : toM m₀ (2 ^ (64 * (cfg adx).n)) (wordsVal s'.mem (s.gpr .rdi) ((cfg adx).sl ACC) (cfg adx).n) =
      toM m₀ (2 ^ (64 * (cfg adx).n)) (wordsVal s.mem (s.gpr .rdi) inAt (cfg adx).n) ^ (m₀ - 2)) :
    abiPreserved s s' ∧ (invK m modAt inAt).post s s' := by
  subst hm₀
  have hn := cfg_n adx
  have hk : (cfg adx).n = C.k := by rw [hn]; rfl
  have hacc : (cfg adx).sl ACC = C.outAt := by rw [cfg_sl]; rfl
  rw [hk, hacc] at lt v
  refine ⟨abiPreserved_of_exec hmx he ⟨fun r hr => ?_, ?_⟩, ?_, ?_, keeps_of_unch adx U⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sv _ (by decide)
    · exact sv _ (by decide)
    · exact K.gpr _ (by rw [hn]; decide)
    · exact sv _ (by decide)
    · exact sv _ (by decide)
    · exact sv _ (by decide)
    · exact sv _ (by decide)
  · have F := (Exec.regions he hnc).2.2
    rw [hwr] at F
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r rfl; exact hret) (by decide)
  · show C.num _ _ C.outAt < m
    rw [num_eq _ _ (by decide)]; exact lt
  · show C.dec m (C.num _ _ C.outAt) = Spec.Weierstrass.pow (C.dec m (C.num _ _ inAt)) (m - 2)
    rw [num_eq _ _ (by decide), num_eq _ _ hin, hdec, hdec, pow_eq_npow]
    exact v

/-- The curve's prime and order, as the contracts name them: equal without
evaluating them. -/
theorem curve_p : Spec.P192.curve.p = Spec.P192.p := by simp only [Spec.P192.curve]
theorem curve_n : Spec.P192.curve.n = Spec.P192.n := by simp only [Spec.P192.curve]

/-- `vg_p192_inv_mod_p`'s contract, by name. -/
abbrev pK : Contract isa := invK Spec.P192.p C.pAt C.zAt
/-- `vg_p192_inv_mod_n`'s contract, by name. -/
abbrev nK : Contract isa := invK Spec.P192.n C.nAt C.xAt

theorem p_correct (hI : InvSounds) (adx : Bool) (s : State) (hs : pK.pre s) :
    ∃ t s', Exec isa ((cfg adx).invFn (cfg adx).pPowI) s t s' ∧ abiPreserved s s' ∧ pK.post s s' := by
  obtain ⟨-, hwr, hret, hfit, hm, hz⟩ := hs
  have hc := cfg_ok hI adx
  have hS : Scr s (s.gpr .rdi) size := ⟨rfl, by rw [hwr]; simp, hfit⟩
  have hn := cfg_n adx
  have hk : (cfg adx).n = C.k := by rw [cfg_n]; rfl
  have em : wordsVal s.mem (s.gpr .rdi) ((cfg adx).sl MP) (cfg adx).n = C.num (s.gpr .rdi) s.mem C.pAt := by
    rw [hk, cfg_sl, num_eq _ _ (by decide)]; rfl
  have ez : wordsVal s.mem (s.gpr .rdi) ((cfg adx).sl RZ) (cfg adx).n = C.num (s.gpr .rdi) s.mem C.zAt := by
    rw [hk, cfg_sl, num_eq _ _ (by decide)]; rfl
  rw [← em, ← curve_p, ← cfg_C adx] at hm
  rw [← ez, ← curve_p, ← cfg_C adx] at hz
  obtain ⟨t, s', he, K, U, lt, v⟩ := invPFnX_ok hc (by omega) (by omega) hS
    (modP_of hc hm) hz
  have sv := saved_of adx (hvP adx) (hncP adx) he
  have hnc : ((cfg adx).invFn (cfg adx).pPowI).noCalls = true := by
    show invP.noCalls = true; lit_decide
  rw [cfg_C] at lt v
  have hrz : (cfg adx).sl RZ = C.zAt := by rw [cfg_sl]; rfl
  rw [hrz] at v
  exact ⟨t, s', he, finish (mxcsrP adx) adx hwr hret (by decide) dec_eq_p he hnc sv K U curve_p.symm lt v⟩

theorem n_correct (hI : InvSounds) (adx : Bool) (s : State) (hs : nK.pre s) :
    ∃ t s', Exec isa ((cfg adx).invFn (cfg adx).nPowI) s t s' ∧ abiPreserved s s' ∧ nK.post s s' := by
  obtain ⟨-, hwr, hret, hfit, hm, hx⟩ := hs
  have hc := cfg_ok hI adx
  have hS : Scr s (s.gpr .rdi) size := ⟨rfl, by rw [hwr]; simp, hfit⟩
  have hn := cfg_n adx
  have hk : (cfg adx).n = C.k := by rw [cfg_n]; rfl
  have em : wordsVal s.mem (s.gpr .rdi) ((cfg adx).sl MN) (cfg adx).n = C.num (s.gpr .rdi) s.mem C.nAt := by
    rw [hk, cfg_sl, num_eq _ _ (by decide)]; rfl
  have ex : wordsVal s.mem (s.gpr .rdi) ((cfg adx).sl KM) (cfg adx).n = C.num (s.gpr .rdi) s.mem C.xAt := by
    rw [hk, cfg_sl, num_eq _ _ (by decide)]; rfl
  rw [← em, ← curve_n, ← cfg_C adx] at hm
  rw [← ex, ← curve_n, ← cfg_C adx] at hx
  obtain ⟨t, s', he, K, U, lt, v⟩ := invNFnX_ok hc (by omega) (by omega)
    (cfg_fastN adx) hS (modN_of hc hm) hx
  have sv := saved_of adx (hvN adx) (hncN adx) he
  have hnc : ((cfg adx).invFn (cfg adx).nPowI).noCalls = true := by
    show invN.noCalls = true; lit_decide
  rw [cfg_C] at lt v
  have hkm : (cfg adx).sl KM = C.xAt := by rw [cfg_sl]; rfl
  rw [hkm] at v
  exact ⟨t, s', he, finish (mxcsrN adx) adx hwr hret (by decide) dec_eq_n he hnc sv K U curve_n.symm lt v⟩

theorem agree {m : Nat} [NeZero m] {modAt inAt : Nat} (s₁ s₂ : State) (_ : (invK m modAt inAt).pre s₁)
    (_ : (invK m modAt inAt).pre s₂) (h : (invK m modAt inAt).pub s₁ s₂) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rsp]) s₁ s₂ :=
  Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2
    · exact h.1

/-- Constant time by taint tracking, `rdi` and `rsp` public. -/
theorem p_ct (adx : Bool) : ConstantTime isa pK.pre pK.pub ((cfg adx).invFn (cfg adx).pPowI) := by
  show ConstantTime isa _ _ invP
  exact VG.Taint.constantTime (A := X86_64.taint) (Taint.ofRegs [.rdi, .rsp]) agree (by taint_decide)

theorem n_ct (adx : Bool) : ConstantTime isa nK.pre nK.pub ((cfg adx).invFn (cfg adx).nPowI) := by
  show ConstantTime isa _ _ invN
  exact VG.Taint.constantTime (A := X86_64.taint) (Taint.ofRegs [.rdi, .rsp]) agree (by taint_decide)

/-- The memory of `satState`: P-192's `p` and `n` at `ws + 64` and
`ws + 96` for `ws = 0x1000`, zeros elsewhere. -/
@[irreducible] def satMem : Mem := fun a =>
  if 0x1040 ≤ a.toNat ∧ a.toNat < 0x1060 then BitVec.ofNat 8 (Spec.P192.p >>> (8 * (a.toNat - 0x1040)))
  else if 0x1060 ≤ a.toNat ∧ a.toNat < 0x1080 then BitVec.ofNat 8 (Spec.P192.n >>> (8 * (a.toNat - 0x1060)))
  else 0

/-- A state satisfying the preconditions. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem sat_p : C.num 0x1000 satMem C.pAt = Spec.P192.p ∧ C.num 0x1000 satMem C.zAt < Spec.P192.p :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem sat_n : C.num 0x1000 satMem C.nAt = Spec.P192.n ∧ C.num 0x1000 satMem C.xAt < Spec.P192.n :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem p_implies : pK.Implies (C.invPContract X86_64.abi) where
  pre s h := by
    sig_pre [Impl.Weierstrass.Inverse.Curve.invPContract, Impl.Weierstrass.Inverse.Curve.invContract,
      Impl.Weierstrass.Inverse.sig, X86_64.abi, X86_64.argRegs, stackBelow] at h
    exact h
  post s s' _ h := by
    sig_post [Impl.Weierstrass.Inverse.Curve.invPContract, Impl.Weierstrass.Inverse.Curve.invContract,
      Impl.Weierstrass.Inverse.sig, X86_64.abi, X86_64.argRegs]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Impl.Weierstrass.Inverse.Curve.invPContract, Impl.Weierstrass.Inverse.Curve.invContract,
      Impl.Weierstrass.Inverse.sig, X86_64.abi, X86_64.argRegs] at h
    exact h
  sat := ⟨satState, by
    sig_pre [Impl.Weierstrass.Inverse.Curve.invPContract, Impl.Weierstrass.Inverse.Curve.invContract,
      Impl.Weierstrass.Inverse.sig, X86_64.abi, X86_64.argRegs, stackBelow]
    exact ⟨Region.disjoint_of_sep (by decide), by decide, sat_p⟩⟩

theorem n_implies : nK.Implies (C.invNContract X86_64.abi) where
  pre s h := by
    sig_pre [Impl.Weierstrass.Inverse.Curve.invNContract, Impl.Weierstrass.Inverse.Curve.invContract,
      Impl.Weierstrass.Inverse.sig, X86_64.abi, X86_64.argRegs, stackBelow] at h
    exact h
  post s s' _ h := by
    sig_post [Impl.Weierstrass.Inverse.Curve.invNContract, Impl.Weierstrass.Inverse.Curve.invContract,
      Impl.Weierstrass.Inverse.sig, X86_64.abi, X86_64.argRegs]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Impl.Weierstrass.Inverse.Curve.invNContract, Impl.Weierstrass.Inverse.Curve.invContract,
      Impl.Weierstrass.Inverse.sig, X86_64.abi, X86_64.argRegs] at h
    exact h
  sat := ⟨satState, by
    sig_pre [Impl.Weierstrass.Inverse.Curve.invNContract, Impl.Weierstrass.Inverse.Curve.invContract,
      Impl.Weierstrass.Inverse.sig, X86_64.abi, X86_64.argRegs, stackBelow]
    exact ⟨Region.disjoint_of_sep (by decide), by decide, sat_n⟩⟩

/-- `vg_p192_inv_mod_p` (`adx` false) and `vg_p192_inv_mod_p_adx` on x86-64. -/
theorem p_verified (hI : InvSounds) (adx : Bool) :
    Verified X86_64.target ((cfg adx).invFn (cfg adx).pPowI) (C.invPContract X86_64.abi) :=
  Verified.of_correct (p_correct hI adx) (p_ct adx) p_implies

/-- `vg_p192_inv_mod_n` (`adx` false) and `vg_p192_inv_mod_n_adx` on x86-64. -/
theorem n_verified (hI : InvSounds) (adx : Bool) :
    Verified X86_64.target ((cfg adx).invFn (cfg adx).nPowI) (C.invNContract X86_64.abi) :=
  Verified.of_correct (n_correct hI adx) (n_ct adx) n_implies

end VG.Proof.Ecdsa.X86_64.P192.Inverse
