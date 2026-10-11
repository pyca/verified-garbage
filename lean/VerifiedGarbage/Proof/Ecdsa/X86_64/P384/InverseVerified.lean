import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.VerifiedAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.InverseLit
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Spec.Weierstrass.Inverse

/-!
# `vg_p384_inv_mod_p` and `_n` on x86-64: `Verified`

The facts of `Spec.Weierstrass.Inverse.p384`'s contracts for x86-64, by name
(`invK`): `ws` in `rdi`, the modulus and a number below it at their offsets.
`invFn_ok` and `invP_ok` (`invN_ok`) give the power in `ACC`'s slot, the
callee-saved registers restored, and every byte of `ws` kept but those of
`ACC`'s slot and of `pwW`, the own working space (`inv_correct`). The
contracts decode a number `x` as `x R^(m-2)`, the proofs as `x R⁻¹` (`toM`):
they agree as `R R^(m-2) = 1` modulo `p` and `n`, which the kernel computes
(`dec_eq`). Constant time by taint tracking, `rdi` and `rsp` public.
-/

namespace VG.Proof.Ecdsa.X86_64.P384.Inverse

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P384

/-- P-384's curve of `Spec/Weierstrass/Inverse.lean`. -/
abbrev C : Spec.Weierstrass.Inverse.Curve := Spec.Weierstrass.Inverse.p384

/-- The configuration of the functions (`adx` false) or their `_adx` forms. -/
abbrev cfg (adx : Bool) : Cfg := if adx then p384x else p384

/-- The inversion modulo `m`, at `modAt`, of the number at `inAt`, on x86-64. -/
def invK (m : Nat) [NeZero m] (modAt inAt : Nat) : Contract isa where
  pre s :=
    let ws : Region := ⟨s.gpr .rdi, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [ws] ∧ ret.Disjoint ws ∧ (s.gpr .rdi).toNat + 8192 ≤ 2 ^ 64 ∧
      C.num (s.gpr .rdi) s.mem modAt = m ∧ C.num (s.gpr .rdi) s.mem inAt < m
  post s s' := C.num (s.gpr .rdi) s'.mem C.outAt < m ∧
    C.dec m (C.num (s.gpr .rdi) s'.mem C.outAt) =
      Weierstrass.pow (C.dec m (C.num (s.gpr .rdi) s.mem inAt)) (m - 2) ∧
    C.Keeps (s.gpr .rdi) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi

/-- The number at an offset below `2³²` is the one `wordsVal` reads. -/
theorem num_eq (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) : C.num ws m o = wordsVal m ws o 6 := by
  unfold Spec.Weierstrass.Inverse.Curve.num Spec.Weierstrass.Mont.numAt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  exact read_eq_wordsVal m ws 6 o

/-- The contracts' decoding is the proofs' `toM` modulo any `m` with
`R R^(m-2) = 1`, which `powMod` computes. -/
theorem dec_eq {m : Nat} [NeZero m] (h1 : 1 < m) (he : m - 2 < 2 ^ 400)
    (h : 2 ^ (64 * C.k) * Pratt.powMod m 400 (2 ^ (64 * C.k)) (m - 2) % m = 1) (x : Nat) :
    C.dec m x = toM m (2 ^ (64 * C.k)) x := by
  have hp : Weierstrass.pow (Fin.ofNat m (2 ^ (64 * C.k))) (m - 2) =
      Fin.ofNat m (Pratt.powMod m 400 (2 ^ (64 * C.k)) (m - 2)) := by
    rw [pow_eq_npow, ← ofNat_pow', Pratt.powMod_eq m h1 _ _ _ he, ofNat_mod]
  have hR : Fin.ofNat m (2 ^ (64 * C.k)) * Fin.ofNat m (Pratt.powMod m 400 (2 ^ (64 * C.k)) (m - 2)) = 1 := by
    rw [← ofNat_mul', ← ofNat_mod, h]; rfl
  have hr := mul_rinv (m := m) ⟨_, hR⟩
  have : Fin.ofNat m (Pratt.powMod m 400 (2 ^ (64 * C.k)) (m - 2)) = rinv m (2 ^ (64 * C.k)) := by
    grind
  unfold Spec.Weierstrass.Inverse.Curve.dec toM
  rw [hp, this]

theorem dec_eq_p (x : Nat) : C.dec Spec.P384.curve.p x = toM Spec.P384.curve.p (2 ^ (64 * C.k)) x :=
  dec_eq (by decide +kernel) (by decide +kernel) (by decide +kernel) x

theorem dec_eq_n (x : Nat) : C.dec Spec.P384.curve.n x = toM Spec.P384.curve.n (2 ^ (64 * C.k)) x :=
  dec_eq (by decide +kernel) (by decide +kernel) (by decide +kernel) x

theorem cfg_ok (hI : InvSounds) (adx : Bool) : CfgOk (cfg adx) := by
  cases adx
  · exact p384_ok hI
  · exact p384x_ok hI

theorem cfg_n (adx : Bool) : (cfg adx).n = 6 := by cases adx <;> rfl
theorem cfg_C (adx : Bool) : (cfg adx).C = Spec.P384.curve := by cases adx <;> rfl
theorem cfg_sl (adx : Bool) (i : Nat) : (cfg adx).sl i = p384.sl i := by cases adx <;> rfl
theorem cfg_fastN (adx : Bool) : (cfg adx).fastN = true := by cases adx <;> rfl

/-- What the functions write, as offsets: `ACC`'s slot (the result's) and the
own working space. -/
theorem pwW_eq (adx : Bool) : pwW (cfg adx) = [(1456, 48), (1504, 48), (4048, 48), (3400, 448)] := by
  cases adx <;> decide

theorem keeps_of_unch {ws : Addr} {m m' : Mem} (adx : Bool) (hu : Unch ws (pwW (cfg adx)) m m') :
    C.Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Spec.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  show (ws + BitVec.ofNat 64 i - ws).toNat < _ ∨ _ ≤ (ws + BitVec.ofNat 64 i - ws).toNat
  rw [Mem.sub_ofNat_toNat ws (by omega)]
  simp only [Spec.Weierstrass.Inverse.Curve.Own, Spec.Weierstrass.Inverse.Curve.slot,
    Spec.Weierstrass.Inverse.Curve.tmpAt, Spec.Weierstrass.Inverse.Curve.workAt,
    Spec.Weierstrass.Inverse.Curve.workLen, Spec.Weierstrass.Inverse.Curve.outAt, C,
    Spec.Weierstrass.Inverse.p384] at hown hp
  rw [pwW_eq] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> dsimp only <;> omega

theorem mxcsrP (adx : Bool) : ((cfg adx).invFn (cfg adx).pPowI).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases adx
  · show invP.allInstrs _ = true; lit_decide
  · show invPAdx.allInstrs _ = true; lit_decide

theorem mxcsrN (adx : Bool) : ((cfg adx).invFn (cfg adx).nPowI).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases adx
  · show invN.allInstrs _ = true; lit_decide
  · show invNAdx.allInstrs _ = true; lit_decide

/-- From what `invFn_ok` gives: the ABI's registers and return address, and
the result's facts. -/
theorem finish {code : Prog isa} (hmx : code.allInstrs (fun i => !loadsMxcsr i) = true) (adx : Bool)
    {m : Nat} [NeZero m] {s : State} (hwr : s.wr = [⟨s.gpr .rdi, 8192⟩])
    (hret : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 8192⟩) {inAt : Nat} (hin : inAt < 2 ^ 32)
    (hdec : ∀ x, C.dec m x = toM m (2 ^ (64 * C.k)) x) {t : List Leak} {s' : State}
    (he : Exec isa code s t s') (hnc : code.noCalls = true)
    (sv : ∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s.gpr r)
    (K : KeepRegs (invClob (cfg adx).n) s s') (U : Unch (s.gpr .rdi) (pwW (cfg adx)) s.mem s'.mem)
    (lt : wordsVal s'.mem (s.gpr .rdi) ((cfg adx).sl ACC) (cfg adx).n < m)
    (v : toM m (2 ^ (64 * (cfg adx).n)) (wordsVal s'.mem (s.gpr .rdi) ((cfg adx).sl ACC) (cfg adx).n) =
      toM m (2 ^ (64 * (cfg adx).n)) (wordsVal s.mem (s.gpr .rdi) inAt (cfg adx).n) ^ (m - 2)) :
    abiPreserved s s' ∧ (invK m 0 inAt).post s s' := by
  have hn := cfg_n adx
  have hacc : (cfg adx).sl ACC = C.outAt := by rw [cfg_sl]; rfl
  rw [hn, hacc] at lt v
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
  · show C.dec m (C.num _ _ C.outAt) = Weierstrass.pow (C.dec m (C.num _ _ inAt)) (m - 2)
    rw [num_eq _ _ (by decide), num_eq _ _ hin, hdec, hdec, pow_eq_npow]
    exact v

end VG.Proof.Ecdsa.X86_64.P384.Inverse
