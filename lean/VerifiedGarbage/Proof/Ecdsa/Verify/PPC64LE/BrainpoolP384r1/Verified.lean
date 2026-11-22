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
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.PPC64LE
meta import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP384r1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP384r1.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP384r1
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP384r1
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP384r1
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
public import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.BrainpoolP384r1.PPC64LE.Comb
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP384r1.Window
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.Ecdsa.Verify
public import VerifiedGarbage.Spec.BrainpoolP384r1
public import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Spec.Ecdsa.Generic
meta import VerifiedGarbage.Spec.Ecdsa.Verify
meta import VerifiedGarbage.Spec.BrainpoolP384r1
meta import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Ecdsa.Verify.PPC64LE.BrainpoolP384r1.Contract`, which only this module used -/

section

/-!
# ECDSA verification over brainpoolP384r1 on PPC64LE: the contract the proof is written against

The facts of `Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP384r1.inst` for PPC64LE, by name:
`vg_ecdsa_brainpoolp384r1_verify(public, digest, sig, scratch)`, with the arguments in
`r3`–`r6` and the result in `r3` (ELFv2). Only the pointers are public here:
the proof shows that nothing else affects timing, although the contract
would let the contents of the three buffers.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP384r1

open VG VG.PPC64LE Spec.Weierstrass Spec.Ecdsa

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.BrainpoolP384r1.curve (bytesAt m pk 97) (hashToInt Spec.BrainpoolP384r1.curve (bytesAt m digest 48)) (bytesAt m sig 96)

def verifyPPC : Contract PPC64LE.isa where
  pre s :=
    let pk : Region := ⟨s.gpr .r3, 97⟩
    let digest : Region := ⟨s.gpr .r4, 48⟩
    let sig : Region := ⟨s.gpr .r5, 96⟩
    let scratch : Region := ⟨s.gpr .r6, 8192⟩
    s.rd = [pk, digest, sig] ∧ s.wr = [scratch] ∧ pk.Disjoint scratch ∧ digest.Disjoint scratch ∧
      sig.Disjoint scratch ∧ (s.gpr .r3).toNat + 97 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 48 ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + 96 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + 8192 ≤ 2 ^ 64
  post s s' := s'.gpr .r3 = if vf s.mem (s.gpr .r3) (s.gpr .r4) (s.gpr .r5) then 1 else 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6

end VG.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP384r1

end

end

/-!
# ECDSA verification over brainpoolP384r1 on PPC64LE: `Verified`

`vg_ecdsa_brainpoolp384r1_verify` with `[u]G` by the comb, from its table, a
constant (`abi.withConsts brainpoolp384r1CombConsts`), and `[v]Q` by the windows for any
`a`, as P-256's (`Proof/Ecdsa/Verify/PPC64LE/Verified.lean`, `Verified.lean`):
`combPts_ok`, `pointsBrainpoolP384r1` as `PtsOk` states; `verify_ppc`, from
`verifyWith_ok`; `verify_ct`: the time depends only on the pointers and the
table's address (`taint_decide` with `vectorTaintSym` on the code's literal).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP384r1

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdsa.Verify.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdsa.Verify.PPC64LE Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.Point (tmv)
open VG.Proof.Weierstrass.PPC64LE.TComb (TableMem)
open VG.Impl.Ecdh.PPC64LE (PX PY)
open VG.Impl.Ecdsa.Verify.PPC64LE (U V UX UY UZ RM')

theorem pointsBrainpoolP384r1_eq : pointsBrainpoolP384r1 =
    .seq (bits (brainpoolp384r1.sl U) (bitsAt brainpoolp384r1.n 0) (8 * brainpoolp384r1.n)) (.seq
      (.block (VG.Impl.Mont.PPC64LE.setConst brainpoolp384r1.n (brainpoolp384r1.sl EM) (brainpoolp384r1.mont brainpoolp384r1.C.b)))
      (.seq mulGeneratorBrainpoolP384r1 (.seq (.block (Cfg.save brainpoolp384r1)) (.seq (bits (brainpoolp384r1.sl V) (bitsAt brainpoolp384r1.n 0) (8 * brainpoolp384r1.n))
        (.seq (brainpoolp384r1.winCall (WindowA.Cfg.mul brainpoolp384r1 PX PY B3P)) (Cfg.sum brainpoolp384r1)))))) := rfl

set_option exponentiation.threshold 512 in
/-- `[u]G + [v]Q` by the comb and windows, with the comb's table at `T`. -/
theorem combPts_ok (hC : Law Spec.BrainpoolP384r1.curve) {s₀ : State} {T : Addr}
    (ht : TableMem s₀ T brainpoolp384r1CombWords) (sym : s₀.syms brainpoolp384r1Comb.tsym = T)
    (hd : Region.Disjoint ⟨T, 8 * brainpoolp384r1CombWords.length⟩ ⟨s₀.gpr .r6, 8192⟩) :
    PtsOk brainpoolp384r1 s₀ pointsBrainpoolP384r1 := by
  rw [pointsBrainpoolP384r1_eq]
  refine CombWin.kit_pts_ok Window.BrainpoolP384r1.kit (by decide) (Or.inr ⟨rfl, rfl⟩) (by decide) hC
    fun {s k} K sy hk bits => ?_
  obtain ht₂ : TableMem s T brainpoolp384r1CombWords :=
    ht.unch (by rw [K.rk.rd, K.rk.wr]) K.whole (by decide) hd
  obtain ht' : TableMem s T (TComb.tableWords brainpoolp384r1Comb Spec.BrainpoolP384r1.curve VG.Impl.BrainpoolP384r1.comb7) := by
    rw [Proof.BrainpoolP384r1.PPC64LE.comb_words_eq]; exact ht₂
  obtain hd' : Region.Disjoint ⟨T, 8 * (TComb.tableWords brainpoolp384r1Comb Spec.BrainpoolP384r1.curve VG.Impl.BrainpoolP384r1.comb7).length⟩
      ⟨s₀.gpr .r6, 8192⟩ := by
    rw [Proof.BrainpoolP384r1.PPC64LE.comb_words_eq]; exact hd
  exact WP.mono (TComb.comb_ok brainpoolp384r1Comb (Proof.BrainpoolP384r1.PPC64LE.comb_config hC) hC
    brainpoolp384r1_ok.onG K.ws ht' (by rw [sy, sym]) hd'
    hk K.fixed.zero (fun i hi => bits i hi) K.fixed.ap K.fixed.b3p)
    fun s₃ ⟨k₃, U₃, L₃, R₃⟩ => ⟨k₃, U₃.cover Proof.BrainpoolP384r1.PPC64LE.comb_writes_cover, L₃, R₃⟩


theorem pre_of {s : State} (h : verifyPPC.pre s) : VPre brainpoolp384r1 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x1000, 97⟩, ⟨0x2000, 48⟩, ⟨0x3000, 96⟩]
  wr := [⟨0x8000, 8192⟩]

/-- `verifyPPC` states `verifyContract`'s facts by name. -/
theorem verifyPPC_implies : verifyPPC.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP384r1.inst PPC64LE.abi) :=
  { pre := by
      sig_implies_pre [Spec.Ecdsa.BrainpoolP384r1.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.BrainpoolP384r1.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
    post := by
      intro s s' _ h
      sig_post [Spec.Ecdsa.BrainpoolP384r1.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.BrainpoolP384r1.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
      simp only [verifyPPC, vf, Spec.BrainpoolP384r1.curve] at h
      revert h
      split <;> rename_i hv <;> simp only [hv, ite_true, ite_false, Bool.false_eq_true] <;>
        exact fun h => by rw [h]; rfl
    pub := by
      sig_implies_pub [Spec.Ecdsa.BrainpoolP384r1.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.BrainpoolP384r1.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
    sat := by
      sig_implies_sat [Spec.Ecdsa.BrainpoolP384r1.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.BrainpoolP384r1.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
        [satState] using satState }

/-- The verification's contract with the comb's table, as the proof states it. -/
def vPC : Contract isa := Tab.withTable verifyPPC brainpoolp384r1CombConsts brainpoolp384r1Comb.tsym

theorem verify_ppc (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) (s : State) (hs : vPC.pre s) :
    ∃ t s', Exec isa verifyBrainpoolP384r1 s t s' ∧ abiPreserved s s' ∧ vPC.post s s' := by
  obtain ⟨hp, hk⟩ := hs
  obtain ⟨t, s', he, K, hpost⟩ :=
    CombWin.verify_ok brainpoolp384r1_ok hL (fun ht sym hd => combPts_ok hL ht sym hd) (pre_of hp) hk
  exact ⟨t, s', he, K, Tab.post_intro hpost⟩

theorem verify_ct : ConstantTime isa vPC.pre vPC.pub verifyBrainpoolP384r1 :=
  VG.Taint.constantTime (A := vectorTaintSym [brainpoolp384r1Comb.tsym]) (Taint.ofRegs [.r3, .r4, .r5, .r6])
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
@[irreducible] def vSatMem : Mem := constMem 0x100000 brainpoolp384r1CombWords

theorem vSatMem_held : ∀ i < brainpoolp384r1CombWords.length,
    vSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = brainpoolp384r1CombWords.getD i 0 := by
  unfold vSatMem
  exact constMem_held _ _ (by rw [Proof.BrainpoolP384r1.PPC64LE.comb_words_length]; omega_using [])

/-- A state satisfying the precondition with the table. -/
def vSatC : State :=
  { satState with mem := vSatMem, rd := satState.rd ++ [⟨0x100000, 337920⟩], syms := fun _ => 0x100000 }

theorem combConsts_eq : brainpoolp384r1CombConsts = [(brainpoolp384r1Comb.tsym, brainpoolp384r1CombWords)] := rfl

theorem vSat : (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP384r1.inst (abi.withConsts brainpoolp384r1CombConsts)).pre vSatC := by
  have hl := Proof.BrainpoolP384r1.PPC64LE.comb_words_length
  have held := vSatMem_held
  rw [combConsts_eq]
  obtain ⟨W, eW⟩ : ∃ W, brainpoolp384r1CombWords = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : vSatC = s
  sig_pre [Spec.Ecdsa.BrainpoolP384r1.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig, Spec.BrainpoolP384r1.curve,
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
    vPC.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP384r1.inst (abi.withConsts brainpoolp384r1CombConsts)) :=
  Tab.implies verifyPPC_implies ⟨vSatC, vSat⟩

theorem verify_verified (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) :
    Verified PPC64LE.target verifyBrainpoolP384r1
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP384r1.inst (PPC64LE.abi.withConsts brainpoolp384r1CombConsts)) :=
  Verified.of_correct (verify_ppc hL) verify_ct vPC_implies

/-- A state satisfying `verifyHashContract`'s precondition with the table, with an empty hash. -/
def hSatC : State :=
  let h := Hash.hashSatState 48
  { h with mem := vSatMem, rd := h.rd ++ [⟨0x100000, 337920⟩], syms := fun _ => 0x100000 }

theorem verifyHash_sat :
    ∃ s, (Spec.Ecdsa.BrainpoolP384r1.inst.verifyHashContract (PPC64LE.abi.withConsts brainpoolp384r1CombConsts) 112).pre s := by
  refine ⟨hSatC, ?_⟩
  have hl := Proof.BrainpoolP384r1.PPC64LE.comb_words_length
  have held := vSatMem_held
  rw [combConsts_eq]
  obtain ⟨W, eW⟩ : ∃ W, brainpoolp384r1CombWords = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : hSatC = s
  sig_pre [Spec.Ecdsa.Instance.verifyHashContract, Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.BrainpoolP384r1.inst,
    Spec.BrainpoolP384r1.curve, Spec.Ecdsa.scratchWords, PPC64LE.abi, PPC64LE.argRegs, Abi.withConsts, Abi.constRegions,
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
theorem verifyHash_verified (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) :
    Verified PPC64LE.target
      (Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP384r1.inst.curve.len false verifyBrainpoolP384r1)
      (Spec.Ecdsa.BrainpoolP384r1.inst.verifyHashContract (PPC64LE.abi.withConsts brainpoolp384r1CombConsts) 112) :=
  Hash.verifyHash_verified_cons Proof.Ecdsa.Verify.brainpoolP384r1_len (by decide)
    (verify_verified hL) (by taint_decide) verifyHash_sat

end VG.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP384r1
