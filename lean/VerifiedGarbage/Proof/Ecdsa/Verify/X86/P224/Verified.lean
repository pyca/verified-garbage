module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombCT
public import VerifiedGarbage.Proof.Ecdsa.X86.P224.Comb
public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Hash
public import VerifiedGarbage.Impl.Ecdsa.X86.VerifyHash
public import VerifiedGarbage.Impl.Ecdsa.Verify.P224.X86
public import VerifiedGarbage.Spec.Ecdsa.P224
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P224.Lit
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Ecdsa.X86.P224.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.P224.Comb
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Hash
meta import VerifiedGarbage.Impl.Ecdsa.X86.VerifyHash
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P224.X86
meta import VerifiedGarbage.Spec.Ecdsa.P224
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P224.Lit
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Ecdsa.X86.P224.CombLit
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find

/-!
# ECDSA verification over P-224 on x86 (32-bit): `Verified`

`verifyComb_ok` for P-224 with its comb (`p224Comb`: `[u]G` by the
comb, `[v]Q` by the ladder) gives the postcondition, and `verifyComb_ct` the
constant time, in the pointers alone, from the taint checks of the stages.
The proof is against `vLocal`, whose arguments' slots are readable, and
moves to the shared contract, which makes them writable and holds the
comb's tables, by `Verified.narrowTo`; `verifyHash_verified` is the
function that takes the hash function's output.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86.P224

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdsa.X86.P224
open VG.Impl.Ecdsa.Verify.X86 VG.Proof.Ecdsa.Verify.X86

def vFrontCode : Prog isa := Impl.Ecdsa.Verify.X86.Cfg.combFront p224Comb
def vMidCode : Prog isa := Impl.Ecdsa.Verify.X86.Cfg.combMid p224Comb
def vFinalCode : Prog isa := Impl.Ecdsa.Verify.X86.Cfg.tail p224Comb
def vBitsCode : Prog isa :=
  Impl.Weierstrass.X86.bits (p224Comb.sl U) (bitsAt p224Comb.n 0) (8 * p224Comb.n)
def vLadderCode : Prog isa :=
  .seq (.block (Impl.Ecdsa.Verify.X86.Cfg.save p224Comb))
    (.seq (Impl.Weierstrass.X86.bits (p224Comb.sl V) (bitsAt p224Comb.n 0) (8 * p224Comb.n))
      (.seq (Impl.Weierstrass.X86.ladder (Impl.Ecdh.X86.Cfg.ladderQ p224Comb) p224Comb.SP)
        (Impl.Ecdsa.Verify.X86.Cfg.sum p224Comb)))
materialize_code vFrontCode
materialize_code vMidCode
materialize_code vFinalCode
materialize_code vBitsCode
materialize_code vLadderCode

/-- The taint checks of the stages of verification around its points. -/
theorem stagesCT : VerifyStagesCT p224Comb where
  front := by
    change RelCT isa _ vFrontCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)
  mid := by
    change RelCT isa _ vMidCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)
  final := by
    change RelCT isa _ vFinalCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)

/-- The taint checks of `[u]G + [v]Q` around the comb. -/
theorem ladderCT : VerifyLadderCT p224Comb where
  bits := by
    change RelCT isa _ vBitsCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)
  ladder := by
    change RelCT isa _ vLadderCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)

/-- No instruction writes `esp`, and the calls use 20 bytes of stack. -/
theorem verify_sp : SpOk verifyP224 p224Comb.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem verifyBody_sp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.verifyCombBody p224Comb) p224Comb.stk :=
  SpOk.right (a := p224Comb.tableAddr) verify_sp

theorem gMul_sp : SpOk p224Comb.gMul 20 :=
  SpOk.left (SpOk.right (a := p224Comb.signPrep) (SpOk.right (a := p224Comb.tableAddr) signComb_sp))

theorem verify_ok (hC : Weierstrass.Law Spec.P224.curve) {s₀ : State}
    (hp : VCombPre p224Comb s₀) :
    WP isa verifyP224 s₀ fun s' => abiPreserved s₀ s' ∧ VPost p224Comb s₀ s' :=
  verifyComb_ok (d := p224d) (p224Comb_ok) hC (p224Comb_tables hC) rfl p224Comb_shape rfl
    gMul_sp verifyBody_sp hp

theorem verify_ct (hC : Weierstrass.Law Spec.P224.curve) :
    ConstantTime isa (VCombPre p224Comb) (VCombPubL p224d) verifyP224 :=
  verifyComb_ct (d := p224d) (p224Comb_ok) hC (p224Comb_tables hC) rfl p224Comb_shape rfl
    (p224Comb_gMul hC) stagesCT ladderCT gMul_sp verifyBody_sp

abbrev vSpec : Contract isa :=
  Proof.Ecdsa.verifyContract Spec.Ecdsa.P224.inst (X86.abi.withConsts p224Comb.combConsts) 20

def vLocal : Contract isa where
  pre := VCombPre p224Comb
  post := VPost p224Comb
  pub := VCombPubL p224d

def vRd (s : State) : List Region := [⟨ptr s 0, 57⟩, ⟨ptr s 1, 28⟩, ⟨ptr s 2, 56⟩, ⟨argAddr s 0, 16⟩] ++
  Abi.constRegions (fun n => (s.syms n).setWidth 64) p224Comb.combConsts

def vWr (s : State) : List Region := [⟨ptr s 3, 8192⟩]

theorem v_pre {s : State} (h : vSpec.pre s) :
    vLocal.pre (s.withRegions (vRd s) (vWr s)) := by
  sig_pre [vSpec, Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract,
    Proof.Ecdsa.verifySig, Spec.P224.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p224Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
  obtain ⟨lo, sp, _drop, held, fit, dw, _ret, st, -, _take, wr,
    ps, _pa, ds, _da, ss, _sia, sa, _rp, _rd, _rsi, rs, _ra,
    spk, sdg, ssi, _ss, _sa, fp, fd, fsi, fs⟩ := h
  have hb : below (s.gpr .esp) 20 = ⟨(s.gpr .esp).setWidth 64 - 20#64, 20⟩ := by
    unfold below
    rw [VG.X86.Taint.sub_setWidth lo]
  rw [← hb] at st spk sdg ssi
  have h4 := VG.Proof.Weierstrass.X86.below_le_sub (sp := s.gpr .esp) (a := 4) (b := 20) (by decide) lo
  refine ⟨⟨rfl, rfl, ps, ds, ss, sa.symm, rs, fp, fd, fsi, fs, sp, lo, _ss⟩, ?_, ?_, ?_, ?_⟩
  · change TblsHeld p224Comb (s.withRegions (vRd s) (vWr s))
      (below (s.gpr .esp) 20 :: vWr s)
    simp only [TblsHeld, p224Comb_consts, Abi.constRegions_cons, Abi.constRegions_nil,
      Sig.forall_mem_const_single]
    simp only [Abi.constsHeld, List.mem_singleton, forall_eq, State.withRegions_mem]
    change (∀ i < p224W.length, s.mem.readW ((s.syms "VG_P224_COMB").setWidth 64 +
      BitVec.ofNat 64 (8 * i)) 64 = p224W.getD i 0) ∧
      ((s.syms "VG_P224_COMB").setWidth 64).toNat + 8 * p224W.length ≤ 2 ^ 32 ∧
      ∀ r ∈ below (s.gpr .esp) 20 :: vWr s,
        Region.Disjoint ⟨(s.syms "VG_P224_COMB").setWidth 64, 8 * p224W.length⟩ r
    refine ⟨held, ?_, ?_⟩
    · simp only [BitVec.toNat_setWidth]; omega_using [fit]
    · intro r hr
      simp only [vWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact st
      · exact dw _ (by rw [wr]; simp [ptr])
  · exact spk.symm.sub_right h4
  · exact sdg.symm.sub_right h4
  · exact ssi.symm.sub_right h4

theorem v_regions {s : State} (h : vSpec.pre s) :
    s.rd = [⟨ptr s 0, 57⟩, ⟨ptr s 1, 28⟩, ⟨ptr s 2, 56⟩] ++ Abi.constRegions (fun n => (s.syms n).setWidth 64) p224Comb.combConsts ∧
    s.wr = [⟨ptr s 3, 8192⟩, ⟨argAddr s 0, 16⟩] := by
  sig_pre [vSpec, Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract,
    Proof.Ecdsa.verifySig, Spec.P224.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p224Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
  obtain ⟨_, _, hd, _, _, _, _, _, _, ht, hw, _⟩ := h
  refine ⟨?_, hw⟩
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]
  simp only [p224Comb_consts, Abi.constRegions_cons, Abi.constRegions_nil, ptr]

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0x4000, 0x8000` at `0x20004`. -/
def satMem : Mem := fun a =>
  if a = 0x20005 then 0x10 else if a = 0x20009 then 0x20 else if a = 0x2000d then 0x30 else
  if a = 0x20011 then 0x40 else if a = 0x20015 then 0x80 else 0

/-- The arguments, before the tables. -/
def satBase : State where
  gpr r := match r with
    | .esp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := []
  wr := []

/-- The tables at `0x100000`, over `satMem`. -/
@[irreducible] def vSatMem : Mem := tblMem p224W 151552 satMem

theorem vSatMem_held : ∀ i < p224W.length,
    vSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p224W.getD i 0 := by
  unfold vSatMem
  exact tblMem_held satMem (by rw [p224W_length]) (by decide)

/-- The arguments and the tables: a witness's memory and symbols. -/
def vSatTbl : State := { satBase with mem := vSatMem, syms := fun _ => 0x100000 }

theorem vSat_arg (j : Nat) (hj : j < 5) : arg vSatTbl j = arg satBase j := by
  have outside : ∀ j < 5, ∀ b < 4,
      151552 ≤ (argAddr satBase j + BitVec.ofNat 64 b - 0x100000).toNat := by decide
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change vSatMem (argAddr satBase j + BitVec.ofNat 64 b) = satMem (argAddr satBase j + BitVec.ofNat 64 b)
  unfold vSatMem tblMem
  rw [ite_eq_right (by have := outside j hj b (by omega_using [hb]); omega_using [this])]

/-- A state satisfying the precondition. -/
def vSatState : State := { vSatTbl with
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 28⟩, ⟨0x3000, 56⟩, ⟨0x100000, 151552⟩]
  wr := [⟨0x4000, 8192⟩, ⟨0x20004, 16⟩] }

theorem vSat_spec : vSpec.pre vSatState := by
  have a0 : arg vSatState 0 = 0x1000 := (vSat_arg 0 (by decide)).trans (by decide)
  have a1 : arg vSatState 1 = 0x2000 := (vSat_arg 1 (by decide)).trans (by decide)
  have a2 : arg vSatState 2 = 0x3000 := (vSat_arg 2 (by decide)).trans (by decide)
  have a3 : arg vSatState 3 = 0x4000 := (vSat_arg 3 (by decide)).trans (by decide)
  have held : ∀ i < p224W.length, vSatState.mem.readW
      ((vSatState.syms "VG_P224_COMB").setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = p224W.getD i 0 :=
    vSatMem_held
  generalize e : vSatState = s
  sig_pre [vSpec, Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract,
    Proof.Ecdsa.verifySig, Spec.P224.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p224Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  refine ⟨by decide, by decide, ?_, held, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p224W_length]; rfl
  · rw [p224W_length]; decide
  · rw [p224W_length]
    intro r hr
    change r ∈ [⟨0x4000, 8192⟩, ⟨0x20004, 16⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · rw [p224W_length]; exact Region.disjoint_of_sep (by decide)
  · rw [p224W_length]; exact Region.disjoint_of_sep (by decide)
  · rw [a0, a1, a2, a3]
    refine ⟨rfl, rfl, ?_⟩
    repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

theorem verify_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified X86.target verifyP224 vSpec := by
  have hs : ∃ s, vSpec.pre s := ⟨vSatState, vSat_spec⟩
  have sl : ∃ s, vLocal.pre s := ⟨_, v_pre vSat_spec⟩
  have hv : Verified X86.target verifyP224 vLocal := Verified.of_correct (k := vLocal)
    (fun s h => by obtain ⟨tr, t, e, a, p⟩ := verify_ok hL h; exact ⟨tr, t, e, a, p⟩)
    (verify_ct hL) (.refl sl)
  refine Verified.narrowTo hv vRd vWr (fun _ h => v_pre h) ?_ ?_ ?_ ?_ hs
  · intro s h a n ⟨r, hr, hc⟩
    obtain ⟨rd, wr⟩ := v_regions h
    refine ⟨r, ?_, hc⟩
    rw [rd, wr]
    simp only [vRd, vWr] at hr
    generalize Abi.constRegions (fun n => (s.syms n).setWidth 64) p224Comb.combConsts = C at hr ⊢
    simp only [List.cons_append, List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | h | rfl <;> simp [h]
  · intro s h a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    rw [(v_regions h).2]
    simp only [vWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r
    exact List.mem_cons_self ..
  · intro s t _ h
    sig_post [vSpec, Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract,
    Proof.Ecdsa.verifySig, Spec.P224.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts]
    have er : (t.gpr .edx ++ t.gpr .eax).setWidth 32 = t.gpr .eax := BitVec.setWidth_append_eq_right
    rw [er]
    simpa only [vLocal, VPost, State.withRegions_mem, State.withRegions_gpr,
      arg_withRegions, ptr, show p224Comb.C = Spec.P224.curve from rfl,
      Spec.P224.curve, Nat.reduceMul, Nat.reduceAdd] using h
  · intro s t _ _ h
    sig_pub [vSpec, Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract,
    Proof.Ecdsa.verifySig, Spec.P224.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p224Comb_consts, Abi.withConsts] at h
    obtain ⟨he, hy, _inputs, a0, a1, a2, a3⟩ := h
    refine ⟨he, ?_, hy⟩
    intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega_using [hj]
    rcases hj' with rfl | rfl | rfl | rfl
    · exact a0
    · exact a1
    · exact a2
    · exact a3

/-- A state satisfying `verifyHashContract`'s precondition: the tables, with five arguments,
`0x3000` bytes of hash at `0x2000`. -/
def vHashSatState : State := { vSatTbl with
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 0x3000⟩, ⟨0x4000, 56⟩, ⟨0x100000, 151552⟩]
  wr := [⟨0x8000, 8192⟩, ⟨0x20004, 20⟩] }

theorem vHashSat_pre :
    (Spec.Ecdsa.P224.inst.verifyHashContract (X86.abi.withConsts p224Comb.combConsts)
      (20 + Impl.Ecdsa.X86.VerifyHash.frameBytes)).pre vHashSatState := by
  have a0 : arg vHashSatState 0 = 0x1000 := (vSat_arg 0 (by decide)).trans (by decide)
  have a1 : arg vHashSatState 1 = 0x2000 := (vSat_arg 1 (by decide)).trans (by decide)
  have a2 : arg vHashSatState 2 = 0x3000 := (vSat_arg 2 (by decide)).trans (by decide)
  have a3 : arg vHashSatState 3 = 0x4000 := (vSat_arg 3 (by decide)).trans (by decide)
  have a4 : arg vHashSatState 4 = 0x8000 := (vSat_arg 4 (by decide)).trans (by decide)
  have held : ∀ i < p224W.length, vHashSatState.mem.readW
      ((vHashSatState.syms "VG_P224_COMB").setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = p224W.getD i 0 :=
    vSatMem_held
  generalize e : vHashSatState = s
  sig_pre [Spec.Ecdsa.P224.inst, Spec.Ecdsa.Instance.verifyHashContract,
    Spec.Ecdsa.Instance.verifyHashSig, Spec.P224.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p224Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  refine ⟨by decide, by decide, ?_, held, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p224W_length]; rfl
  · rw [p224W_length]; decide
  · rw [p224W_length]
    intro r hr
    change r ∈ [⟨0x8000, 8192⟩, ⟨0x20004, 20⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · rw [p224W_length]; exact Region.disjoint_of_sep (by decide)
  · rw [p224W_length]; exact Region.disjoint_of_sep (by decide)
  · decide
  · rw [a0, a1, a2, a3, a4]
    refine ⟨rfl, rfl, ?_⟩
    repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

/-- `vg_ecdsa_p224_verify`, taking the hash function's output: the comb's
verification, run on the `len` bytes of the hash, in a frame of `frameBytes`
more bytes of stack (`Hash.verifyHash_verifiedC`, for its table). -/
theorem verifyHash_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified X86.target
      (Impl.Ecdsa.X86.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false verifyP224)
      (Spec.Ecdsa.P224.inst.verifyHashContract (X86.abi.withConsts p224Comb.combConsts)
        (20 + Impl.Ecdsa.X86.VerifyHash.frameBytes)) :=
  Hash.verifyHash_verifiedC Proof.Ecdsa.Verify.p224_len (by decide) (verify_verified hL)
    verify_sp.1 verify_sp.2 (by taint_decide) ⟨_, vHashSat_pre⟩

end VG.Proof.Ecdsa.Verify.X86.P224
