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
public import VerifiedGarbage.Impl.Ecdsa.Verify.P224.PPC64LE
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P224.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P224.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P224.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import VerifiedGarbage.Spec.Ecdsa.P224
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
public import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.P224.PPC64LE.Comb
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224.Window
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.Ecdsa.Verify
public import VerifiedGarbage.Spec.P224
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Spec.Ecdsa.Generic
meta import VerifiedGarbage.Spec.Ecdsa.Verify
meta import VerifiedGarbage.Spec.P224
meta import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Ecdsa.Verify.PPC64LE.P224.Contract`, which only this module used -/

section

/-!
# ECDSA verification over P-224 on PPC64LE: the contract the proof is written against

The facts of `Proof.Ecdsa.verifyContract Spec.Ecdsa.P224.inst` for PPC64LE, by name:
`vg_ecdsa_p224_verify(public, digest, sig, scratch)`, with the arguments in
`r3`–`r6` and the result in `r3` (ELFv2). Only the pointers are public here:
the proof shows that nothing else affects timing, although the contract
would let the contents of the three buffers.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE.P224

open VG VG.PPC64LE Spec.Weierstrass Spec.Ecdsa

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.P224.curve (bytesAt m pk 57) (hashToInt Spec.P224.curve (bytesAt m digest 28)) (bytesAt m sig 56)

def verifyPPC : Contract PPC64LE.isa where
  pre s :=
    let pk : Region := ⟨s.gpr .r3, 57⟩
    let digest : Region := ⟨s.gpr .r4, 28⟩
    let sig : Region := ⟨s.gpr .r5, 56⟩
    let scratch : Region := ⟨s.gpr .r6, 8192⟩
    s.rd = [pk, digest, sig] ∧ s.wr = [scratch] ∧ pk.Disjoint scratch ∧ digest.Disjoint scratch ∧
      sig.Disjoint scratch ∧ (s.gpr .r3).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 28 ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + 56 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + 8192 ≤ 2 ^ 64
  post s s' := s'.gpr .r3 = if vf s.mem (s.gpr .r3) (s.gpr .r4) (s.gpr .r5) then 1 else 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6

end VG.Proof.Ecdsa.Verify.PPC64LE.P224

end

end

/-!
# ECDSA verification over P-521 on PPC64LE: `Verified`

`vg_ecdsa_p224_verify` with `[u]G` by the comb (`comb_ok`), from its table, a constant (`abi.withConsts p224CombConsts`),
and `[v]Q` by the four-bit windows, as P-256's
(`Proof/Ecdsa/Verify/PPC64LE/Verified.lean`, `Verified.lean`): `combPts_ok`,
`pointsP224` as `PtsOk` states; `verify_ppc`, from `verifyWith_ok`;
`verify_ct`: the time depends only on the pointers and the table's address
(`taint_decide` with `vectorTaintSym` on the code's literal).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE.P224

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdsa.Verify.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdsa.Verify.PPC64LE Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.Point (tmv)
open VG.Proof.Weierstrass.PPC64LE.TComb (TableMem)
open VG.Impl.Ecdh.PPC64LE (PX PY)
open VG.Impl.Ecdsa.Verify.PPC64LE (U V UX UY UZ RM')

theorem pointsP224_eq : pointsP224 =
    .seq (bits (p224.sl U) (bitsAt p224.n 0) (8 * p224.n)) (.seq
      (.block (VG.Impl.Mont.PPC64LE.setConst p224.n (p224.sl EM) (p224.mont p224.C.b)))
      (.seq mulGeneratorP224 (.seq (.block (Cfg.save p224)) (.seq (bits (p224.sl V) (bitsAt p224.n 0) (8 * p224.n))
        (.seq (p224.winCall (Window.Cfg.mul p224 PX PY EM)) (Cfg.sum p224)))))) := rfl

/-- `[u]G + [v]Q` by the comb and windows, with the comb's table at `T`. -/
theorem combPts_ok (hC : Law Spec.P224.curve) {s₀ : State} {T : Addr}
    (ht : TableMem s₀ T p224CombWords) (sym : s₀.syms p224Comb.tsym = T)
    (hd : Region.Disjoint ⟨T, 8 * p224CombWords.length⟩ ⟨s₀.gpr .r6, 8192⟩) :
    PtsOk p224 s₀ pointsP224 := by
  rw [pointsP224_eq]
  refine CombWin.kit_pts_ok Window.P224.kit (by decide) (Or.inl ⟨rfl, rfl⟩) (by decide) hC
    fun {s k} K sy hk bits => ?_
  obtain ht₂ : TableMem s T p224CombWords :=
    ht.unch (by rw [K.rk.rd, K.rk.wr]) K.whole (by decide) hd
  obtain ht' : TableMem s T (TComb.tableWords p224Comb Spec.P224.curve VG.Impl.P224.p224Comb7x32) := by
    rw [Proof.P224.PPC64LE.comb_words_eq]; exact ht₂
  obtain hd' : Region.Disjoint ⟨T, 8 * (TComb.tableWords p224Comb Spec.P224.curve VG.Impl.P224.p224Comb7x32).length⟩
      ⟨s₀.gpr .r6, 8192⟩ := by
    rw [Proof.P224.PPC64LE.comb_words_eq]; exact hd
  exact WP.mono (TComb.comb_ok p224Comb (Proof.P224.PPC64LE.comb_config hC) hC
    p224_ok.onG K.ws ht' (by rw [sy, sym]) hd'
    hk K.fixed.zero (fun i hi => bits i (by
      have : i < 8 * Spec.P224.curve.len := hi
      exact Nat.lt_of_lt_of_le this (by decide))) K.fixed.ap K.fixed.b3p)
    fun s₃ ⟨k₃, U₃, L₃, R₃⟩ => ⟨k₃, U₃.cover Proof.P224.PPC64LE.comb_writes_cover, L₃, R₃⟩


/-- The tables of constants the verification reads: the comb's, and the
setup's (`Cfg.constsK`). -/
abbrev vK : List (String × List (BitVec 64)) := p224CombConsts ++ p224.constsK

theorem vK_eq : vK = [(p224Comb.tsym, p224CombWords), (p224.constSym, p224.constTbl)] := rfl

theorem pre_of {s : State} (h : verifyPPC.pre (stripConsts vK s)) (hk : ConstsOk vK 0 s) :
    VPre p224 s (constRegs vK s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨hk.rd_strip h1, h2, h3, h4, h5, h6, h7, h8, h9, fun _ =>
    tbl_of_consts hk (List.mem_append_right _ (List.mem_singleton_self _)) (hk.disjoint_wr
      (List.mem_append_right _ (List.mem_singleton_self _)) (by
        show (⟨s.gpr .r6, size⟩ : Region) ∈ (stripConsts vK s).wr
        rw [h2]; exact List.mem_singleton_self _))⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 28⟩, ⟨0x3000, 56⟩]
  wr := [⟨0x8000, 8192⟩]

/-- `verifyPPC` states `verifyContract`'s facts by name. -/
theorem verifyPPC_implies : verifyPPC.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.P224.inst PPC64LE.abi) :=
  { pre := by
      sig_implies_pre [Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.P224.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
    post := by
      intro s s' _ h
      sig_post [Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.P224.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
      simp only [verifyPPC, vf, Spec.P224.curve] at h
      revert h
      split <;> rename_i hv <;> simp only [hv, ite_true, ite_false, Bool.false_eq_true] <;>
        exact fun h => by rw [h]; rfl
    pub := by
      sig_implies_pub [Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.P224.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
    sat := by
      sig_implies_sat [Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.P224.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
        [satState] using satState }


/-- The verification's contract with its tables, as the proof states it. -/
abbrev vPC : Contract isa := verifyPPC.withTables vK

theorem verify_ppc (hL : Weierstrass.Law Spec.P224.curve) (s : State) (hs : vPC.pre s) :
    ∃ t s', Exec isa verifyP224 s t s' ∧ abiPreserved s s' ∧ vPC.post s s' := by
  obtain ⟨hp, hk⟩ := hs
  obtain ⟨t, s', he, K, hpost⟩ :=
    CombWin.verify_okK p224_ok hL (fun ht sym hd => combPts_ok hL ht sym hd) (pre_of hp hk) hk
      (List.mem_append_left _ (List.mem_singleton_self _))
  exact ⟨t, s', he, K, hpost⟩

theorem verify_ct : ConstantTime isa vPC.pre vPC.pub verifyP224 :=
  VG.Taint.constantTime (A := vectorTaintSym [p224Comb.tsym, p224.constSym]) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5, h6⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6⟩, fun n hn => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl
        · exact sy _ (List.mem_append_left _ (List.mem_singleton_self _))
        · exact sy _ (List.mem_append_right _ (List.mem_singleton_self _))⟩)
    (by taint_decide)

/-- The memory of the witnesses with the tables: the comb's at `0x100000`,
the setup's at `0x200000` (irreducible: unfolding it in a definitional check
would evaluate the tables). -/
@[irreducible] def vSatMem2 : Mem := constMem2 0x100000 p224CombWords 0x200000 p224.constTbl

theorem vSatMem2_held₁ : ∀ i < p224CombWords.length,
    vSatMem2.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p224CombWords.getD i 0 := by
  unfold vSatMem2
  exact constMem2_held₁ _ _ _ _ (by rw [Proof.P224.PPC64LE.comb_words_length]; decide) (by rw [constTbl_length]; decide)

theorem vSatMem2_held₂ : ∀ i < p224.constTbl.length,
    vSatMem2.readW (0x200000 + BitVec.ofNat 64 (8 * i)) 64 = p224.constTbl.getD i 0 := by
  unfold vSatMem2
  exact constMem2_held₂ _ _ _ _ (by rw [constTbl_length]; decide)

/-- The addresses of the witnesses' tables. -/
def vSyms (n : String) : Addr := if n = p224.constSym then 0x200000 else 0x100000

/-- A state satisfying the precondition with the tables. -/
def vSatC : State where
  gpr := satState.gpr
  lr := satState.lr
  sp := satState.sp
  mem := vSatMem2
  rd := satState.rd ++ [⟨0x100000, 8 * 16384⟩, ⟨0x200000, 8 * (17 * 4)⟩]
  wr := satState.wr
  syms := vSyms

theorem vSat : (Proof.Ecdsa.verifyContract Spec.Ecdsa.P224.inst (abi.withConsts vK)).pre vSatC := by
  have hl₁ := Proof.P224.PPC64LE.comb_words_length
  have hl₂ := constTbl_length p224
  have held₁ := vSatMem2_held₁
  have held₂ := vSatMem2_held₂
  have hs₁ : vSyms p224Comb.tsym = 0x100000 := by simp only [vSyms]; decide
  have hs₂ : vSyms p224.constSym = 0x200000 := by simp only [vSyms, ite_true]
  rw [vK_eq]
  obtain ⟨W₁, eW₁⟩ : ∃ W, p224CombWords = W := ⟨_, rfl⟩
  obtain ⟨W₂, eW₂⟩ : ∃ W, p224.constTbl = W := ⟨_, rfl⟩
  rw [eW₁] at hl₁ held₁ ⊢
  rw [eW₂] at hl₂ held₂ ⊢
  generalize e : vSatC = s
  sig_pre [Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig, Spec.P224.curve,
    Spec.Ecdsa.scratchWords, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl₁, hl₂]
  refine ⟨rfl, fun i hi => ?_, fun i hi => ?_, by decide, fun r hr => ?_, by decide, fun r hr => ?_, by decide,
    by decide, ?_⟩
  · show vSatMem2.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = _
    exact held₁ i (by rw [hl₁]; exact hi)
  · show vSatMem2.readW (0x200000 + BitVec.ofNat 64 (8 * i)) 64 = _
    exact held₂ i (by rw [hl₂]; exact hi)
  · change r ∈ satState.wr at hr
    simp only [satState, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl <;> exact Region.disjoint_of_sep (by decide)
  · change r ∈ satState.wr at hr
    simp only [satState, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem vPC_implies :
    vPC.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.P224.inst (abi.withConsts vK)) :=
  withTables_implies verifyPPC_implies ⟨vSatC, vSat⟩

theorem verify_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified PPC64LE.target verifyP224 (Proof.Ecdsa.verifyContract Spec.Ecdsa.P224.inst (PPC64LE.abi.withConsts vK)) :=
  Verified.of_correct (verify_ppc hL) verify_ct vPC_implies

/-- A state satisfying `verifyHashContract`'s precondition with the tables, with an empty hash. -/
def hSatC : State :=
  let h := Hash.hashSatState 28
  { h with mem := vSatMem2, rd := h.rd ++ [⟨0x100000, 8 * 16384⟩, ⟨0x200000, 8 * (17 * 4)⟩], syms := vSyms }

theorem verifyHash_sat :
    ∃ s, (Spec.Ecdsa.P224.inst.verifyHashContract (PPC64LE.abi.withConsts vK) 112).pre s := by
  refine ⟨hSatC, ?_⟩
  have hl₁ := Proof.P224.PPC64LE.comb_words_length
  have hl₂ := constTbl_length p224
  have held₁ := vSatMem2_held₁
  have held₂ := vSatMem2_held₂
  rw [vK_eq]
  obtain ⟨W₁, eW₁⟩ : ∃ W, p224CombWords = W := ⟨_, rfl⟩
  obtain ⟨W₂, eW₂⟩ : ∃ W, p224.constTbl = W := ⟨_, rfl⟩
  rw [eW₁] at hl₁ held₁ ⊢
  rw [eW₂] at hl₂ held₂ ⊢
  generalize e : hSatC = s
  sig_pre [Spec.Ecdsa.Instance.verifyHashContract, Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.P224.inst,
    Spec.P224.curve, Spec.Ecdsa.scratchWords, PPC64LE.abi, PPC64LE.argRegs, Abi.withConsts, Abi.constRegions,
    Abi.constsHeld, stackBelow]
  subst e
  rw [hl₁, hl₂]
  refine ⟨by decide, rfl, fun i hi => ?_, fun i hi => ?_, by decide, fun r hr => ?_, Region.disjoint_of_sep (by decide),
    by decide, fun r hr => ?_, Region.disjoint_of_sep (by decide), by decide, by decide, ?_⟩
  · show vSatMem2.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = _
    exact held₁ i (by rw [hl₁]; exact hi)
  · show vSatMem2.readW (0x200000 + BitVec.ofNat 64 (8 * i)) 64 = _
    exact held₂ i (by rw [hl₂]; exact hi)
  · change r ∈ [⟨0x8000, 8192⟩] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact Region.disjoint_of_sep (by decide)
  · change r ∈ [⟨0x8000, 8192⟩] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

/-- `vg_ecdsa_p224_verify`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash
(`Hash.verifyHash_verified_cons`). -/
theorem verifyHash_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified PPC64LE.target
      (Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false verifyP224)
      (Spec.Ecdsa.P224.inst.verifyHashContract (PPC64LE.abi.withConsts vK) 112) :=
  Hash.verifyHash_verified_cons Proof.Ecdsa.Verify.p224_len (by decide)
    (verify_verified hL) (by taint_decide) verifyHash_sat

end VG.Proof.Ecdsa.Verify.PPC64LE.P224
