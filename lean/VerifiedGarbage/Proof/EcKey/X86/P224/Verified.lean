module

public import VerifiedGarbage.Proof.EcKey.X86.CombCT
public import VerifiedGarbage.Proof.Ecdsa.X86.P224.Comb
public import VerifiedGarbage.Spec.EcKey.P224
public import VerifiedGarbage.Impl.EcKey.P224.X86
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.EcKey.X86.P224.Lit
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.EcKey.X86.CombCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.P224.Comb
meta import VerifiedGarbage.Spec.EcKey.P224
meta import VerifiedGarbage.Impl.EcKey.P224.X86
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.EcKey.X86.P224.Lit
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find

/-!
# P-224 public keys on x86 (32-bit): `Verified`

`publicKeyComb_ok` for P-224 with its comb (`p224Comb`) gives the
postcondition, and `publicKeyComb_ct` the constant time, from the taint
checks of the stages around the comb. The proof is against `pkLocal`, whose
arguments' slots are readable, and moves to the shared contract, which makes
them writable and holds the comb's tables, by `Verified.narrowTo`.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86.P224

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Impl.EcKey.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdsa.X86.P224
open VG.Impl.EcKey.X86 (Args.publicKey)

def pkPrepCode : Prog isa := p224Comb.prepareWith Args.publicKey
def pkTailCode : Prog isa := .seq p224Comb.pPow (Impl.EcKey.X86.Cfg.middle p224Comb)
materialize_code pkPrepCode
materialize_code pkTailCode

/-- The taint checks of the stages of the public key around the comb. -/
theorem pkCT : PkStagesCT p224Comb where
  prep := by
    change RelCT isa _ pkPrepCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)
  tail := by
    change RelCT isa _ pkTailCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)

/-- No instruction writes `esp`, and the calls use 20 bytes of stack. -/
theorem pk_sp : SpOk publicKeyP224 p224Comb.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem pk_ok (hC : Weierstrass.Law Spec.P224.curve) {s₀ : State}
    (hp : PkCombPre p224Comb s₀) :
    WP isa publicKeyP224 s₀ fun s' => abiPreserved s₀ s' ∧ PkPost p224Comb s₀ s' :=
  publicKeyComb_ok (d := p224d) (p224Comb_ok) hC (p224Comb_tables hC) rfl p224Comb_shape
    (PkCombSp.of (d := p224d) rfl pk_sp) hp

theorem pk_ct (hC : Weierstrass.Law Spec.P224.curve) :
    ConstantTime isa (PkCombPre p224Comb) (PkCombPub p224d) publicKeyP224 :=
  publicKeyComb_ct (d := p224d) (p224Comb_ok) hC (p224Comb_tables hC) rfl p224Comb_shape
    (p224Comb_gMul hC) pkCT (PkCombSp.of (d := p224d) rfl pk_sp).g

abbrev pkSpec : Contract isa :=
  Spec.EcKey.P224.inst.publicKeyContract (X86.abi.withConsts p224Comb.combConsts) 20

def pkLocal : Contract isa where
  pre := PkCombPre p224Comb
  post := PkPost p224Comb
  pub := PkCombPub p224d

def pkRd (s : State) : List Region := [⟨ptr s 1, 28⟩, ⟨argAddr s 0, 12⟩] ++
  Abi.constRegions (fun n => (s.syms n).setWidth 64) p224Comb.combConsts

def pkWr (s : State) : List Region := [⟨ptr s 0, 57⟩, ⟨ptr s 2, 8192⟩]

theorem pk_pre {s : State} (h : pkSpec.pre s) :
    pkLocal.pre (s.withRegions (pkRd s) (pkWr s)) := by
  sig_pre [pkSpec, Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p224Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
  obtain ⟨lo, sp, _drop, held, fit, dw, _ret, st, -, _take, wr,
    od, os, oa, ds, _da, sa, ro, _rd, rs, _ra, _so, sd, _ss, _sa, fo, fd, fs⟩ := h
  have hb : below (s.gpr .esp) 20 = ⟨(s.gpr .esp).setWidth 64 - 20#64, 20⟩ := by
    unfold below
    rw [VG.X86.Taint.sub_setWidth lo]
  rw [← hb] at st sd
  have h4 := VG.Proof.Weierstrass.X86.below_le_sub (sp := s.gpr .esp) (a := 4) (b := 20) (by decide) lo
  refine ⟨⟨rfl, rfl, os, od, ds, oa.symm, sa.symm, ro, rs, fo, fd, fs, sp, lo, _so, _ss⟩, ?_, ?_⟩
  · change TblsHeld p224Comb (s.withRegions (pkRd s) (pkWr s))
      (below (s.gpr .esp) 20 :: pkWr s)
    simp only [TblsHeld, p224Comb_consts, Abi.constRegions_cons, Abi.constRegions_nil,
      Sig.forall_mem_const_single]
    simp only [Abi.constsHeld, List.mem_singleton, forall_eq, State.withRegions_mem]
    change (∀ i < p224W.length, s.mem.readW ((s.syms "VG_P224_COMB").setWidth 64 +
      BitVec.ofNat 64 (8 * i)) 64 = p224W.getD i 0) ∧
      ((s.syms "VG_P224_COMB").setWidth 64).toNat + 8 * p224W.length ≤ 2 ^ 32 ∧
      ∀ r ∈ below (s.gpr .esp) 20 :: pkWr s,
        Region.Disjoint ⟨(s.syms "VG_P224_COMB").setWidth 64, 8 * p224W.length⟩ r
    refine ⟨held, ?_, ?_⟩
    · simp only [BitVec.toNat_setWidth]; omega_using [fit]
    · intro r hr
      simp only [pkWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact st
      · exact dw _ (by rw [wr]; simp [ptr])
      · exact dw _ (by rw [wr]; simp [ptr])
  · exact sd.symm.sub_right h4

theorem pk_regions {s : State} (h : pkSpec.pre s) :
    s.rd = [⟨ptr s 1, 28⟩] ++ Abi.constRegions (fun n => (s.syms n).setWidth 64) p224Comb.combConsts ∧
    s.wr = [⟨ptr s 0, 57⟩, ⟨ptr s 2, 8192⟩, ⟨argAddr s 0, 12⟩] := by
  sig_pre [pkSpec, Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p224Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
  obtain ⟨_, _, hd, _, _, _, _, _, _, ht, hw, _⟩ := h
  refine ⟨?_, hw⟩
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]
  simp only [p224Comb_consts, Abi.constRegions_cons, Abi.constRegions_nil, ptr]

/-- Memory holding the arguments `0x1000, 0x2000, 0x8000` at `0x20004`. -/
def satMem : Mem := fun a =>
  if a = 0x20005 then 0x10 else if a = 0x20009 then 0x20 else if a = 0x2000d then 0x80 else 0

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
@[irreducible] def pkSatMem : Mem := tblMem p224W 151552 satMem

theorem pkSatMem_held : ∀ i < p224W.length,
    pkSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p224W.getD i 0 := by
  unfold pkSatMem
  exact tblMem_held satMem (by rw [p224W_length]) (by decide)

/-- A state satisfying the precondition. -/
def pkSatState : State := { satBase with
  mem := pkSatMem
  rd := [⟨0x2000, 28⟩, ⟨0x100000, 151552⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x8000, 8192⟩, ⟨0x20004, 12⟩]
  syms := fun _ => 0x100000 }

theorem pkSat_arg (j : Nat) (hj : j < 3) : arg pkSatState j = arg satBase j := by
  have outside : ∀ j < 3, ∀ b < 4,
      151552 ≤ (argAddr satBase j + BitVec.ofNat 64 b - 0x100000).toNat := by decide
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change pkSatMem (argAddr satBase j + BitVec.ofNat 64 b) = satMem (argAddr satBase j + BitVec.ofNat 64 b)
  unfold pkSatMem tblMem
  rw [ite_eq_right (by have := outside j hj b (by omega_using [hb]); omega_using [this])]

theorem pkSat_spec : pkSpec.pre pkSatState := by
  have a0 : arg pkSatState 0 = 0x1000 := (pkSat_arg 0 (by decide)).trans (by decide)
  have a1 : arg pkSatState 1 = 0x2000 := (pkSat_arg 1 (by decide)).trans (by decide)
  have a2 : arg pkSatState 2 = 0x8000 := (pkSat_arg 2 (by decide)).trans (by decide)
  have held : ∀ i < p224W.length, pkSatState.mem.readW
      ((pkSatState.syms "VG_P224_COMB").setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = p224W.getD i 0 :=
    pkSatMem_held
  generalize e : pkSatState = s
  sig_pre [pkSpec, Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p224Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  refine ⟨by decide, by decide, ?_, held, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p224W_length]; rfl
  · rw [p224W_length]; decide
  · rw [p224W_length]
    intro r hr
    change r ∈ [⟨0x1000, 57⟩, ⟨0x8000, 8192⟩, ⟨0x20004, 12⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · rw [p224W_length]; exact Region.disjoint_of_sep (by decide)
  · rw [p224W_length]; exact Region.disjoint_of_sep (by decide)
  · rw [a0, a1, a2]
    refine ⟨rfl, rfl, ?_⟩
    repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

theorem pk_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified X86.target publicKeyP224 pkSpec := by
  have hs : ∃ s, pkSpec.pre s := ⟨pkSatState, pkSat_spec⟩
  have sl : ∃ s, pkLocal.pre s := ⟨_, pk_pre pkSat_spec⟩
  have hv : Verified X86.target publicKeyP224 pkLocal := Verified.of_correct (k := pkLocal)
    (fun s h => by obtain ⟨tr, t, e, a, p⟩ := pk_ok hL h; exact ⟨tr, t, e, a, p⟩)
    (pk_ct hL) (.refl sl)
  refine Verified.narrowTo hv pkRd pkWr (fun _ h => pk_pre h) ?_ ?_ ?_ ?_ hs
  · intro s h a n ⟨r, hr, hc⟩
    obtain ⟨rd, wr⟩ := pk_regions h
    refine ⟨r, ?_, hc⟩
    rw [rd, wr]
    simp only [pkRd, pkWr] at hr
    generalize Abi.constRegions (fun n => (s.syms n).setWidth 64) p224Comb.combConsts = C at hr ⊢
    simp only [List.cons_append, List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with rfl | rfl | h | rfl | rfl <;> simp [h]
  · intro s h a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    rw [(pk_regions h).2]
    simp only [pkWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · intro s t _ h
    sig_post [pkSpec, Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts]
    have er : (t.gpr .edx ++ t.gpr .eax).setWidth 32 = t.gpr .eax := BitVec.setWidth_append_eq_right
    rw [er]
    simp only [pkLocal, PkPost, dk, State.withRegions_mem, State.withRegions_gpr,
      arg_withRegions, ptr, show p224Comb.C = Spec.P224.curve from rfl,
      Spec.P224.curve, Nat.reduceMul, Nat.reduceAdd] at h
    dsimp only [p224Comb, p224, Spec.P224.curve, Spec.EcKey.bytesAt, Spec.Ecdsa.bytesAt] at h ⊢
    generalize hq : Spec.EcKey.publicKey _ _ = q at h ⊢
    rcases q with _ | _ | ⟨x, y⟩ <;> exact h
  · intro s t _ _ h
    sig_pub [pkSpec, Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p224Comb_consts, Abi.withConsts] at h
    obtain ⟨he, hy, a0, a1, a2⟩ := h
    refine ⟨he, ?_, hy⟩
    intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega_using [hj]
    rcases hj' with rfl | rfl | rfl
    · exact a0
    · exact a1
    · exact a2

end VG.Proof.EcKey.X86.P224
