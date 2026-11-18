module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Hash
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Hash
meta import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.VerifiedAll
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.CombAll
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.CombAll
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Main
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP512r1.PPC64LE
meta import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP512r1.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP512r1
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.TCombI
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
public import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.BrainpoolP512r1.PPC64LE.Comb
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1.Window
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.Ecdsa.Verify
public import VerifiedGarbage.Spec.BrainpoolP512r1
public import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Spec.Ecdsa.Generic
meta import VerifiedGarbage.Spec.Ecdsa.Verify
meta import VerifiedGarbage.Spec.BrainpoolP512r1
meta import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Ecdsa.Verify.PPC64LE.BrainpoolP512r1.Contract`, which only this module used -/

section

/-!
# ECDSA verification over brainpoolP512r1 on PPC64LE: the contract the proof is written against

The facts of `Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP512r1.inst` for PPC64LE, by name:
`vg_ecdsa_brainpoolp512r1_verify(public, digest, sig, scratch)`, with the arguments in
`r3`–`r6` and the result in `r3` (ELFv2). Only the pointers are public here:
the proof shows that nothing else affects timing, although the contract
would let the contents of the three buffers.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP512r1

open VG VG.PPC64LE Spec.Weierstrass Spec.Ecdsa

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.BrainpoolP512r1.curve (bytesAt m pk 129) (hashToInt Spec.BrainpoolP512r1.curve (bytesAt m digest 64)) (bytesAt m sig 128)

def verifyPPC : Contract PPC64LE.isa where
  pre s :=
    let pk : Region := ⟨s.gpr .r3, 129⟩
    let digest : Region := ⟨s.gpr .r4, 64⟩
    let sig : Region := ⟨s.gpr .r5, 128⟩
    let scratch : Region := ⟨s.gpr .r6, 8192⟩
    s.rd = [pk, digest, sig] ∧ s.wr = [scratch] ∧ pk.Disjoint scratch ∧ digest.Disjoint scratch ∧
      sig.Disjoint scratch ∧ (s.gpr .r3).toNat + 129 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 64 ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + 8192 ≤ 2 ^ 64
  post s s' := s'.gpr .r3 = if vf s.mem (s.gpr .r3) (s.gpr .r4) (s.gpr .r5) then 1 else 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6

end VG.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP512r1

end

end

/-!
# ECDSA verification over brainpoolP512r1 on PPC64LE: `Verified`

`vg_ecdsa_brainpoolp512r1_verify` with `[u]G` by the comb with the addition inlined
(`combI_ok`), from its table, a constant (`abi.withConsts brainpoolp512r1CombConsts`),
and `[v]Q` by the three-bit windows for any `a`, as P-256's
(`Proof/Ecdsa/Verify/PPC64LE/Verified.lean`, `Verified.lean`): `combPts_ok`,
`pointsBrainpoolP512r1` as `PtsOk` states; `verify_ppc`, from `verifyWith_ok`;
`verify_ct`: the time depends only on the pointers and the table's address
(`taint_decide` with `vectorTaintSym` on the code's literal).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP512r1

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdsa.Verify.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdsa.Verify.PPC64LE Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.Point (tmv)
open VG.Proof.Weierstrass.PPC64LE.TComb (TableMem)
open VG.Impl.Ecdh.PPC64LE (PX PY)
open VG.Impl.Ecdsa.Verify.PPC64LE (U V UX UY UZ RM')

theorem pointsBrainpoolP512r1_eq : pointsBrainpoolP512r1 =
    .seq (bits (brainpoolp512r1.sl U) (bitsAt brainpoolp512r1.n 0) (8 * brainpoolp512r1.n)) (.seq
      (.block (VG.Impl.Mont.PPC64LE.setConst brainpoolp512r1.n (brainpoolp512r1.sl EM) (brainpoolp512r1.mont brainpoolp512r1.C.b)))
      (.seq mulGeneratorBrainpoolP512r1 (.seq (.block (Cfg.save brainpoolp512r1)) (.seq (bits (brainpoolp512r1.sl V) (bitsAt brainpoolp512r1.n 0) (8 * brainpoolp512r1.n))
        (.seq (WindowA.Cfg.mul3top brainpoolp512r1 PX PY B3P) (Cfg.sum brainpoolp512r1)))))) := rfl

set_option exponentiation.threshold 1024 in
/-- `[u]G + [v]Q` by the comb and windows, with the comb's table at `T`. -/
theorem combPts_ok (hC : Law Spec.BrainpoolP512r1.curve) {s₀ : State} {T : Addr}
    (ht : TableMem s₀ T brainpoolp512r1CombWords) (sym : s₀.syms brainpoolp512r1Comb.tsym = T)
    (hd : Region.Disjoint ⟨T, 8 * brainpoolp512r1CombWords.length⟩ ⟨s₀.gpr .r6, 8192⟩) :
    PtsOk brainpoolp512r1 s₀ pointsBrainpoolP512r1 := by
  rw [pointsBrainpoolP512r1_eq]
  refine CombWin.pts_ok brainpoolp512r1_ok (by decide) hC (E := Window.BrainpoolP512r1.kit.E) (by decide)
    (fun {s k} K sy hk bits => ?_)
    fun {s k P} K _ g hP bits hk => WP.mono (Window.BrainpoolP512r1.mul_ok hC ⟨K.ws,
      ⟨K.fixed.ap, K.fixed.b3p, K.fixed.zero, K.fixed.onep⟩, ⟨g.rep, g.x, g.y, g.z⟩, hP, bits,
      Nat.lt_trans hk (by decide)⟩) fun s₆ ⟨k₆, U₆, R₆⟩ => ⟨k₆, U₆, ⟨R₆.rep, R₆.x, R₆.y, R₆.z⟩⟩
  obtain ht₂ : TableMem s T brainpoolp512r1CombWords :=
    ht.unch (by rw [K.rk.rd, K.rk.wr]) K.whole (by decide) hd
  obtain ht' : TableMem s T (TComb.tableWords brainpoolp512r1Comb Spec.BrainpoolP512r1.curve VG.Impl.BrainpoolP512r1.comb7) := by
    rw [Proof.BrainpoolP512r1.PPC64LE.comb_words_eq]; exact ht₂
  obtain hd' : Region.Disjoint ⟨T, 8 * (TComb.tableWords brainpoolp512r1Comb Spec.BrainpoolP512r1.curve VG.Impl.BrainpoolP512r1.comb7).length⟩
      ⟨s₀.gpr .r6, 8192⟩ := by
    rw [Proof.BrainpoolP512r1.PPC64LE.comb_words_eq]; exact hd
  exact WP.mono (TComb.combI_ok brainpoolp512r1Comb (Proof.BrainpoolP512r1.PPC64LE.comb_config hC) hC
    brainpoolp512r1_ok.onG K.ws ht' (by rw [sy, sym]) hd'
    (Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) (by decide))) K.fixed.zero (fun i hi => bits i hi) K.fixed.ap K.fixed.b3p)
    fun s₃ ⟨k₃, U₃, L₃, R₃⟩ => ⟨k₃, U₃.cover Proof.BrainpoolP512r1.PPC64LE.comb_writes_cover, L₃, R₃⟩


theorem pre_of {s : State} (h : verifyPPC.pre s) : VPre brainpoolp512r1 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x1000, 129⟩, ⟨0x2000, 64⟩, ⟨0x3000, 128⟩]
  wr := [⟨0x8000, 8192⟩]

/-- `verifyPPC` states `verifyContract`'s facts by name. -/
theorem verifyPPC_implies : verifyPPC.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP512r1.inst PPC64LE.abi) :=
  { pre := by
      sig_implies_pre [Spec.Ecdsa.BrainpoolP512r1.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
    post := by
      intro s s' _ h
      sig_post [Spec.Ecdsa.BrainpoolP512r1.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
      simp only [verifyPPC, vf, Spec.BrainpoolP512r1.curve] at h
      revert h
      split <;> rename_i hv <;> simp only [hv, ite_true, ite_false, Bool.false_eq_true] <;>
        exact fun h => by rw [h]; rfl
    pub := by
      sig_implies_pub [Spec.Ecdsa.BrainpoolP512r1.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
    sat := by
      sig_implies_sat [Spec.Ecdsa.BrainpoolP512r1.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
        [satState] using satState }

/-- The verification's contract with the comb's table, as the proof states it. -/
def vPC : Contract isa := Tab.withTable verifyPPC brainpoolp512r1CombConsts brainpoolp512r1Comb.tsym

theorem verify_ppc (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (s : State) (hs : vPC.pre s) :
    ∃ t s', Exec isa verifyBrainpoolP512r1 s t s' ∧ abiPreserved s s' ∧ vPC.post s s' := by
  obtain ⟨hp, hk⟩ := hs
  obtain ⟨t, s', he, K, hpost⟩ :=
    CombWin.verify_ok brainpoolp512r1_ok hL (fun ht sym hd => combPts_ok hL ht sym hd) (pre_of hp) hk
  exact ⟨t, s', he, K, Tab.post_intro hpost⟩

theorem verify_ct : ConstantTime isa vPC.pre vPC.pub verifyBrainpoolP512r1 :=
  VG.Taint.constantTime (A := vectorTaintSym [brainpoolp512r1Comb.tsym]) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5, h6⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact sy⟩)
    (by taint_decide)

/-- The memory of the witness with the table: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def vSatMem : Mem := constMem 0x100000 brainpoolp512r1CombWords

theorem vSatMem_held : ∀ i < brainpoolp512r1CombWords.length,
    vSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = brainpoolp512r1CombWords.getD i 0 := by
  unfold vSatMem
  exact constMem_held _ _ (by rw [Proof.BrainpoolP512r1.PPC64LE.comb_words_length]; omega_using [])

/-- A state satisfying the precondition with the table. -/
def vSatC : State :=
  { satState with mem := vSatMem, rd := satState.rd ++ [⟨0x100000, 606208⟩], syms := fun _ => 0x100000 }

theorem combConsts_eq : brainpoolp512r1CombConsts = [(brainpoolp512r1Comb.tsym, brainpoolp512r1CombWords)] := rfl

theorem vSat : (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP512r1.inst (abi.withConsts brainpoolp512r1CombConsts)).pre vSatC := by
  have hl := Proof.BrainpoolP512r1.PPC64LE.comb_words_length
  have held := vSatMem_held
  rw [combConsts_eq]
  obtain ⟨W, eW⟩ : ∃ W, brainpoolp512r1CombWords = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : vSatC = s
  sig_pre [Spec.Ecdsa.BrainpoolP512r1.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig, Spec.BrainpoolP512r1.curve,
    Spec.Ecdsa.scratchWords, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x8000, 8192⟩] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem vPC_implies :
    vPC.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP512r1.inst (abi.withConsts brainpoolp512r1CombConsts)) :=
  Tab.implies verifyPPC_implies ⟨vSatC, vSat⟩

theorem verify_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified PPC64LE.target verifyBrainpoolP512r1
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP512r1.inst (PPC64LE.abi.withConsts brainpoolp512r1CombConsts)) :=
  Verified.of_correct (verify_ppc hL) verify_ct vPC_implies

/-- A state satisfying `verifyHashContract`'s precondition with the table, with an empty hash. -/
def hSatC : State :=
  let h := Hash.hashSatState 64
  { h with mem := vSatMem, rd := h.rd ++ [⟨0x100000, 606208⟩], syms := fun _ => 0x100000 }

theorem verifyHash_sat :
    ∃ s, (Spec.Ecdsa.BrainpoolP512r1.inst.verifyHashContract (PPC64LE.abi.withConsts brainpoolp512r1CombConsts) 112).pre s := by
  refine ⟨hSatC, ?_⟩
  have hl := Proof.BrainpoolP512r1.PPC64LE.comb_words_length
  have held := vSatMem_held
  rw [combConsts_eq]
  obtain ⟨W, eW⟩ : ∃ W, brainpoolp512r1CombWords = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : hSatC = s
  sig_pre [Spec.Ecdsa.Instance.verifyHashContract, Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.BrainpoolP512r1.inst,
    Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords, PPC64LE.abi, PPC64LE.argRegs, Abi.withConsts, Abi.constRegions,
    Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨by decide, rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_,
    Region.disjoint_of_sep (by decide), by decide, rfl, rfl, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide⟩
  change r ∈ [⟨0x8000, 8192⟩] at hr
  obtain rfl := List.mem_singleton.mp hr
  exact Region.disjoint_of_sep (by decide)

/-- `vg_ecdsa_p256_verify`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash
(`Hash.verifyHash_verified_cons`). -/
theorem verifyHash_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified PPC64LE.target
      (Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false verifyBrainpoolP512r1)
      (Spec.Ecdsa.BrainpoolP512r1.inst.verifyHashContract (PPC64LE.abi.withConsts brainpoolp512r1CombConsts) 112) :=
  Hash.verifyHash_verified_cons Proof.Ecdsa.Verify.brainpoolP512r1_len (by decide)
    (verify_verified hL) (by taint_decide) verifyHash_sat

end VG.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP512r1
