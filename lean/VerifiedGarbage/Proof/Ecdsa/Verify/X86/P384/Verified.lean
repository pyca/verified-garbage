module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombCT
public import VerifiedGarbage.Proof.Ecdsa.X86.P384.Comb
public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Hash
public import VerifiedGarbage.Impl.Ecdsa.X86.VerifyHash
public import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombCallTaint
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P384.Lit
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Ecdsa.X86.P384.CombLit
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P384
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.P384.Comb
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Hash
meta import VerifiedGarbage.Impl.Ecdsa.X86.VerifyHash
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86
meta import VerifiedGarbage.Spec.Ecdsa.P384
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombCallTaint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P384.Lit
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Ecdsa.X86.P384.CombLit
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P384
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.X86.SseTaintMono
meta import VerifiedGarbage.Proof.Framework.X86.SseTaintMono

/-!
# ECDSA verification over P-384 on x86 (32-bit): `Verified`

`verifyComb_ok` for P-384 with its comb (`p384Comb`: `[u]G` by the
comb, `[v]Q` by ECDH's windows) gives the postcondition, and `verifyComb_ct` the
constant time, in the pointers alone, from the taint checks of the stages.
The proof is against `vLocal`, whose arguments' slots are readable, and
moves to the shared contract, which makes them writable and holds the
comb's tables, by `Verified.narrowTo`; `verifyHash_verified` is the
function that takes the hash function's output.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86.P384

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdsa.X86.P384
open VG.Impl.Ecdsa.Verify.X86 VG.Proof.Ecdsa.Verify.X86

def vFrontCode : Prog isa := Impl.Ecdsa.Verify.X86.Cfg.combFront p384Comb
def vMidCode : Prog isa := Impl.Ecdsa.Verify.X86.Cfg.combMid p384Comb
def vFinalCode : Prog isa := Impl.Ecdsa.Verify.X86.Cfg.tail p384Comb
def vBitsCode : Prog isa :=
  Impl.Weierstrass.X86.bits (p384Comb.sl U) (bitsAt p384Comb.n 0) (8 * p384Comb.n)
def vLadderCode : Prog isa :=
  .seq (.block (Impl.Ecdsa.Verify.X86.Cfg.save p384Comb))
    (.seq (Impl.Weierstrass.X86.bits (p384Comb.sl V) (bitsAt p384Comb.n 0) (8 * p384Comb.n))
      (.seq (p384Comb.ecdhMul Impl.Ecdh.X86.PX Impl.Ecdh.X86.PY)
        (Impl.Ecdsa.Verify.X86.Cfg.sum p384Comb)))
materialize_code vFrontCode
materialize_code vMidCode
materialize_code vFinalCode
materialize_code vBitsCode
materialize_code vLadderCode

/-- The taint checks of the stages of verification around its points. -/
theorem stagesCT : VerifyStagesCT p384Comb where
  front := by
    change RelCT isa _ vFrontCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)
  mid := by
    change RelCT isa _ vMidCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)
  final := by
    change RelCT isa _ vFinalCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)

/-! The field functions modulo `p`, analysed once from what is public on
entry to their calls from the windows (`τWin`), in place of each call. -/

taint_summary mulSum : sseTaint { τWin with room := 24 }
  (Impl.Weierstrass.X86.Mont.mulFn Impl.Weierstrass.Mont.p384p.k Impl.Weierstrass.Mont.p384p.m)
taint_summary addSum : sseTaint { τWin with room := 24 }
  (Impl.Weierstrass.X86.Mont.addFn Impl.Weierstrass.Mont.p384p.k Impl.Weierstrass.Mont.p384p.m)
taint_summary subSum : sseTaint { τWin with room := 24 }
  (Impl.Weierstrass.X86.Mont.subFn Impl.Weierstrass.Mont.p384p.k Impl.Weierstrass.Mont.p384p.m)

/-! The same functions, from their calls within the windows' function
(`vg_<curve>_window`), one return address deeper. -/

taint_summary mulSumW : sseTaint { τWin with room := 24, stk := [none, some 16, none] }
  (Impl.Weierstrass.X86.Mont.mulFn Impl.Weierstrass.Mont.p384p.k Impl.Weierstrass.Mont.p384p.m)
taint_summary addSumW : sseTaint { τWin with room := 24, stk := [none, some 16, none] }
  (Impl.Weierstrass.X86.Mont.addFn Impl.Weierstrass.Mont.p384p.k Impl.Weierstrass.Mont.p384p.m)
taint_summary subSumW : sseTaint { τWin with room := 24, stk := [none, some 16, none] }
  (Impl.Weierstrass.X86.Mont.subFn Impl.Weierstrass.Mont.p384p.k Impl.Weierstrass.Mont.p384p.m)

/-- The taint checks of `[u]G + [v]Q` around the comb. -/
theorem ladderCT : VerifyLadderCT p384Comb where
  bits := by
    change RelCT isa _ vBitsCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)
  ladder := by
    change RelCT isa _ vLadderCode _
    obtain ⟨_, hc⟩ : ∃ h, (sseTaint.check (scratchArgτ 4 false p384Comb.stk) vLadderCode h).isSome = true := by
      taint_decide_sum [mulSum, addSum, subSum, mulSumW, addSumW, subSumW]
    exact RelCT.taint (A := sseTaint) _ (fun _ _ h => h) hc

/-- No instruction writes `esp`, and the calls use 24 bytes of stack. -/
theorem verify_sp : SpOk verifyP384 p384Comb.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem verifyBody_sp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.verifyCombBody p384Comb) p384Comb.stk :=
  SpOk.right (a := p384Comb.tableAddr) verify_sp

theorem gMul_sp : SpOk p384Comb.gMul p384Comb.stk :=
  SpOk.left (SpOk.right (a := p384Comb.signPrep) (SpOk.right (a := p384Comb.tableAddr) signComb_sp))

/-- The order of the base point is below `2^(8 len)`. -/
theorem nEnc : p384Comb.C.n < 2 ^ (8 * p384Comb.C.len) := by decide +kernel

theorem verify_ok (hC : Weierstrass.Law Spec.P384.curve) {s₀ : State}
    (hp : VCombPre p384Comb s₀) :
    WP isa verifyP384 s₀ fun s' => abiPreserved s₀ s' ∧ VPost p384Comb s₀ s' :=
  verifyComb_ok (d := p384d) (p384Comb_ok) hC nEnc (p384Comb_tables hC) rfl p384Comb_shape rfl
    gMul_sp verifyBody_sp hp

theorem verify_ct (hC : Weierstrass.Law Spec.P384.curve) :
    ConstantTime isa (VCombPre p384Comb) (VCombPubL p384d) verifyP384 :=
  verifyComb_ct (d := p384d) (p384Comb_ok) hC nEnc (p384Comb_tables hC) rfl p384Comb_shape rfl
    (p384Comb_gMul hC) stagesCT ladderCT gMul_sp verifyBody_sp

abbrev vSpec : Contract isa :=
  Proof.Ecdsa.verifyContract Spec.Ecdsa.P384.inst (X86.abi.withConsts p384Comb.combConsts) 24

def vLocal : Contract isa where
  pre := VCombPre p384Comb
  post := VPost p384Comb
  pub := VCombPubL p384d

def vRd (s : State) : List Region := [⟨ptr s 0, 97⟩, ⟨ptr s 1, 48⟩, ⟨ptr s 2, 96⟩, ⟨argAddr s 0, 16⟩] ++
  Abi.constRegions (fun n => (s.syms n).setWidth 64) p384Comb.combConsts

def vWr (s : State) : List Region := [⟨ptr s 3, 8192⟩]

theorem v_pre {s : State} (h : vSpec.pre s) :
    vLocal.pre (s.withRegions (vRd s) (vWr s)) := by
  sig_pre [vSpec, Spec.Ecdsa.P384.inst, Proof.Ecdsa.verifyContract,
    Proof.Ecdsa.verifySig, Spec.P384.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p384Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
  obtain ⟨lo, sp, _drop, held, fit, dw, _ret, st, -, _take, wr,
    ps, _pa, ds, _da, ss, _sia, sa, _rp, _rd, _rsi, rs, _ra,
    spk, sdg, ssi, _ss, _sa, fp, fd, fsi, fs⟩ := h
  have hb : below (s.gpr .esp) 24 = ⟨(s.gpr .esp).setWidth 64 - 24#64, 24⟩ := by
    unfold below
    rw [VG.X86.Taint.sub_setWidth lo]
  rw [← hb] at st spk sdg ssi
  have h4 := VG.Proof.Weierstrass.X86.below_le_sub (sp := s.gpr .esp) (a := 4) (b := 24) (by decide) lo
  refine ⟨⟨rfl, rfl, ps, ds, ss, sa.symm, rs, fp, fd, fsi, fs, sp, lo, _ss⟩, ?_, ?_, ?_, ?_⟩
  · change TblsHeld p384Comb (s.withRegions (vRd s) (vWr s))
      (below (s.gpr .esp) 24 :: vWr s)
    simp only [TblsHeld, p384Comb_consts, Abi.constRegions_cons, Abi.constRegions_nil,
      Sig.forall_mem_const_single]
    simp only [Abi.constsHeld, List.mem_singleton, forall_eq, State.withRegions_mem]
    change (∀ i < p384W.length, s.mem.readW ((s.syms "VG_P384_COMB").setWidth 64 +
      BitVec.ofNat 64 (8 * i)) 64 = p384W.getD i 0) ∧
      ((s.syms "VG_P384_COMB").setWidth 64).toNat + 8 * p384W.length ≤ 2 ^ 32 ∧
      ∀ r ∈ below (s.gpr .esp) 24 :: vWr s,
        Region.Disjoint ⟨(s.syms "VG_P384_COMB").setWidth 64, 8 * p384W.length⟩ r
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
    s.rd = [⟨ptr s 0, 97⟩, ⟨ptr s 1, 48⟩, ⟨ptr s 2, 96⟩] ++ Abi.constRegions (fun n => (s.syms n).setWidth 64) p384Comb.combConsts ∧
    s.wr = [⟨ptr s 3, 8192⟩, ⟨argAddr s 0, 16⟩] := by
  sig_pre [vSpec, Spec.Ecdsa.P384.inst, Proof.Ecdsa.verifyContract,
    Proof.Ecdsa.verifySig, Spec.P384.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p384Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
  obtain ⟨_, _, hd, _, _, _, _, _, _, ht, hw, _⟩ := h
  refine ⟨?_, hw⟩
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]
  simp only [p384Comb_consts, Abi.constRegions_cons, Abi.constRegions_nil, ptr]

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
@[irreducible] def vSatMem : Mem := tblMem p384W 337920 satMem

theorem vSatMem_held : ∀ i < p384W.length,
    vSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p384W.getD i 0 := by
  unfold vSatMem
  exact tblMem_held satMem (by rw [p384W_length]) (by decide)

/-- The arguments and the tables: a witness's memory and symbols. -/
def vSatTbl : State := { satBase with mem := vSatMem, syms := fun _ => 0x100000 }

theorem vSat_arg (j : Nat) (hj : j < 5) : arg vSatTbl j = arg satBase j := by
  have outside : ∀ j < 5, ∀ b < 4,
      337920 ≤ (argAddr satBase j + BitVec.ofNat 64 b - 0x100000).toNat := by decide
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change vSatMem (argAddr satBase j + BitVec.ofNat 64 b) = satMem (argAddr satBase j + BitVec.ofNat 64 b)
  unfold vSatMem tblMem
  rw [ite_eq_right (by have := outside j hj b (by omega_using [hb]); omega_using [this])]

/-- A state satisfying the precondition. -/
def vSatState : State := { vSatTbl with
  rd := [⟨0x1000, 97⟩, ⟨0x2000, 48⟩, ⟨0x3000, 96⟩, ⟨0x100000, 337920⟩]
  wr := [⟨0x4000, 8192⟩, ⟨0x20004, 16⟩] }

theorem vSat_spec : vSpec.pre vSatState := by
  have a0 : arg vSatState 0 = 0x1000 := (vSat_arg 0 (by decide)).trans (by decide)
  have a1 : arg vSatState 1 = 0x2000 := (vSat_arg 1 (by decide)).trans (by decide)
  have a2 : arg vSatState 2 = 0x3000 := (vSat_arg 2 (by decide)).trans (by decide)
  have a3 : arg vSatState 3 = 0x4000 := (vSat_arg 3 (by decide)).trans (by decide)
  have held : ∀ i < p384W.length, vSatState.mem.readW
      ((vSatState.syms "VG_P384_COMB").setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = p384W.getD i 0 :=
    vSatMem_held
  generalize e : vSatState = s
  sig_pre [vSpec, Spec.Ecdsa.P384.inst, Proof.Ecdsa.verifyContract,
    Proof.Ecdsa.verifySig, Spec.P384.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p384Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  refine ⟨by decide, by decide, ?_, held, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p384W_length]; rfl
  · rw [p384W_length]; decide
  · rw [p384W_length]
    intro r hr
    change r ∈ [⟨0x4000, 8192⟩, ⟨0x20004, 16⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · rw [p384W_length]; exact Region.disjoint_of_sep (by decide)
  · rw [p384W_length]; exact Region.disjoint_of_sep (by decide)
  · rw [a0, a1, a2, a3]
    refine ⟨rfl, rfl, ?_⟩
    repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

theorem verify_verified (hL : Weierstrass.Law Spec.P384.curve) :
    Verified X86.target verifyP384 vSpec := by
  have hs : ∃ s, vSpec.pre s := ⟨vSatState, vSat_spec⟩
  have sl : ∃ s, vLocal.pre s := ⟨_, v_pre vSat_spec⟩
  have hv : Verified X86.target verifyP384 vLocal := Verified.of_correct (k := vLocal)
    (fun s h => by obtain ⟨tr, t, e, a, p⟩ := verify_ok hL h; exact ⟨tr, t, e, a, p⟩)
    (verify_ct hL) (.refl sl)
  refine Verified.narrowTo hv vRd vWr (fun _ h => v_pre h) ?_ ?_ ?_ ?_ hs
  · intro s h a n ⟨r, hr, hc⟩
    obtain ⟨rd, wr⟩ := v_regions h
    refine ⟨r, ?_, hc⟩
    rw [rd, wr]
    simp only [vRd, vWr] at hr
    generalize Abi.constRegions (fun n => (s.syms n).setWidth 64) p384Comb.combConsts = C at hr ⊢
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
    sig_post [vSpec, Spec.Ecdsa.P384.inst, Proof.Ecdsa.verifyContract,
    Proof.Ecdsa.verifySig, Spec.P384.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts]
    have er : (t.gpr .edx ++ t.gpr .eax).setWidth 32 = t.gpr .eax := BitVec.setWidth_append_eq_right
    rw [er]
    simpa only [vLocal, VPost, State.withRegions_mem, State.withRegions_gpr,
      arg_withRegions, ptr, show p384Comb.C = Spec.P384.curve from rfl,
      Spec.P384.curve, Nat.reduceMul, Nat.reduceAdd] using h
  · intro s t _ _ h
    sig_pub [vSpec, Spec.Ecdsa.P384.inst, Proof.Ecdsa.verifyContract,
    Proof.Ecdsa.verifySig, Spec.P384.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p384Comb_consts, Abi.withConsts] at h
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
  rd := [⟨0x1000, 97⟩, ⟨0x2000, 0x3000⟩, ⟨0x4000, 96⟩, ⟨0x100000, 337920⟩]
  wr := [⟨0x8000, 8192⟩, ⟨0x20004, 20⟩] }

theorem vHashSat_pre :
    (Spec.Ecdsa.P384.inst.verifyHashContract (X86.abi.withConsts p384Comb.combConsts)
      (24 + Impl.Ecdsa.X86.VerifyHash.frameBytes)).pre vHashSatState := by
  have a0 : arg vHashSatState 0 = 0x1000 := (vSat_arg 0 (by decide)).trans (by decide)
  have a1 : arg vHashSatState 1 = 0x2000 := (vSat_arg 1 (by decide)).trans (by decide)
  have a2 : arg vHashSatState 2 = 0x3000 := (vSat_arg 2 (by decide)).trans (by decide)
  have a3 : arg vHashSatState 3 = 0x4000 := (vSat_arg 3 (by decide)).trans (by decide)
  have a4 : arg vHashSatState 4 = 0x8000 := (vSat_arg 4 (by decide)).trans (by decide)
  have held : ∀ i < p384W.length, vHashSatState.mem.readW
      ((vHashSatState.syms "VG_P384_COMB").setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = p384W.getD i 0 :=
    vSatMem_held
  generalize e : vHashSatState = s
  sig_pre [Spec.Ecdsa.P384.inst, Spec.Ecdsa.Instance.verifyHashContract,
    Spec.Ecdsa.Instance.verifyHashSig, Spec.P384.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p384Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  refine ⟨by decide, by decide, ?_, held, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p384W_length]; rfl
  · rw [p384W_length]; decide
  · rw [p384W_length]
    intro r hr
    change r ∈ [⟨0x8000, 8192⟩, ⟨0x20004, 20⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · rw [p384W_length]; exact Region.disjoint_of_sep (by decide)
  · rw [p384W_length]; exact Region.disjoint_of_sep (by decide)
  · decide
  · rw [a0, a1, a2, a3, a4]
    refine ⟨rfl, rfl, ?_⟩
    repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

/-- `vg_ecdsa_p384_verify`, taking the hash function's output: the comb's
verification, run on the `len` bytes of the hash, in a frame of `frameBytes`
more bytes of stack (`Hash.verifyHash_verifiedC`, for its table). -/
theorem verifyHash_verified (hL : Weierstrass.Law Spec.P384.curve) :
    Verified X86.target
      (Impl.Ecdsa.X86.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false verifyP384)
      (Spec.Ecdsa.P384.inst.verifyHashContract (X86.abi.withConsts p384Comb.combConsts)
        (24 + Impl.Ecdsa.X86.VerifyHash.frameBytes)) :=
  Hash.verifyHash_verifiedC Proof.Ecdsa.Verify.p384_len (by decide) (verify_verified hL)
    verify_sp.1 verify_sp.2 (by taint_decide) ⟨_, vHashSat_pre⟩

end VG.Proof.Ecdsa.Verify.X86.P384
