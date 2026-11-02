module

import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.PublicKey
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Sha512OK
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed25519.WholeLocal
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Comb
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.PublicKey
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Ed25519.WholeLocal
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Whole
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Impl.Ed25519.PPC64LE.Comb
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts

/-!
# `vg_ed25519_public_key` on PPC64LE, with its frame as an argument, verified

The code meets `publicKeyContract` under `abi.withConsts combConsts` (the
comb's table, which `vg_ed25519_scalar_base` reads) with the frame as one more
argument (`Sig.scratchContract`), and 48 bytes of stack for the callees'
frames: the proof against the contract's facts by register (`pkC`: `pkR`
without the table, and what the table adds), which it implies
(`consts_implies`), and a state satisfying it, with the table at `0x100000`
(`tblMem`). Only the pointers and the table's address are public: the
pointers stay in `r20`–`r23`, which no function called writes, so the taint
analysis (`taint_decide`, under `vectorTaintSym`) sees them public
throughout, callees included.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole
open VG.Spec.Ed25519 (bytesAt)
open VG.Impl.Ed25519.PPC64LE (combSym combWords combConsts)
open VG.Proof.Ed25519.PPC64LE (combWords_length TBL tbl_of_consts rd_of_consts consts_implies base_ok)

/-- The contract by register: `out` in `r3`, `seed` in `r4`, `scratch` in `r5`, the frame in `r6`;
without the comb's table. -/
def pkR : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 32⟩
    let seed : Region := ⟨s.gpr .r4, 32⟩
    let sc : Region := ⟨s.gpr .r5, 8192⟩
    let fr : Region := ⟨s.gpr .r6, 144⟩
    s.rd = [seed] ∧ s.wr = [out, sc, fr] ∧ out.Disjoint seed ∧ out.Disjoint sc ∧ out.Disjoint fr ∧
      seed.Disjoint sc ∧ seed.Disjoint fr ∧ sc.Disjoint fr ∧ 48 ≤ s.sp.toNat ∧
      (below s.sp 48).Disjoint out ∧ (below s.sp 48).Disjoint seed ∧ (below s.sp 48).Disjoint sc ∧
      (below s.sp 48).Disjoint fr
  post s s' := bytesAt s'.mem (s.gpr .r3) 32 = Spec.Ed25519.publicKey (bytesAt s.mem (s.gpr .r4) 32)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

/-- `pkR` with the comb's table (`abi.withConsts`): `pkR` for the state without it, and what the table
adds. -/
def pkC : Contract isa where
  pre s := pkR.pre (stripConsts combConsts s) ∧ ConstsOk combConsts 48 s
  post := pkR.post
  pub s₁ s₂ := pkR.pub s₁ s₂ ∧ s₁.syms combSym = s₂.syms combSym

/-- The stack the contract reserves. -/
theorem below_reserved (s : State) : below s.sp 48 ∈ PPC64LE.abi.reserved 48 s := by
  show _ ∈ stackBelow s.sp 48
  rw [stackBelow_pos _ (by decide)]; simp

theorem pk_ok (B : BaseOk) (s : State) (hs : pkC.pre s) :
    ∃ t s', Exec isa publicKey s t s' ∧ abiPreserved s s' ∧ pkC.post s s' := by
  obtain ⟨⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp] at *
  obtain ⟨-, tfit, words, twr, tres⟩ := tbl_of_consts hk
  have hrd : s.rd = [⟨s.gpr .r4, 32⟩, TBL (s.syms combSym)] := rd_of_consts hk a
  have tW : ∀ r ∈ pkW s, (TBL (s.syms combSym)).Disjoint r := fun r hr => by
    simp only [pkW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact tres _ (below_reserved s)
  obtain ⟨t, s', he, hg, hsp, hlr, hq⟩ :=
    publicKey_wp sha512OK B ⟨hrd, b, c, d, e, f, g, h, i, j, k, l, m, tfit, words, tW⟩
  exact ⟨t, s', he, ⟨hg, hsp, hlr⟩, hq⟩

theorem pk_ct : ConstantTime isa pkC.pre pkC.pub publicKey :=
  VG.Taint.constantTime (A := vectorTaintSym [combSym]) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun s₁ s₂ _ _ ⟨⟨p3, p4, p5, p6, psp⟩, hsy⟩ => ⟨⟨psp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption⟩, fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

/-- A state satisfying the precondition, without the table. -/
def pkSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x4000 | .r6 => 0x8000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8000, 144⟩]

theorem pkR_implies : pkR.Implies (Sig.scratchContract PPC64LE.abi Spec.Ed25519.publicKeySig "frame" .u8 144
    (Curry.const (fun _ => True) _) (Proof.Ed25519.WholeLocal.publicKeyPost PPC64LE.abi.ptrBits) true 48) := by
  sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed25519.publicKeySig,
    Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.publicKeyPost, pkR, PPC64LE.abi, PPC64LE.argRegs]
    [pkSat] using pkSat

/-- The comb's table at `0x100000`. -/
@[irreducible] def tblMem : Mem := constMem 0x100000 combWords

theorem tblMem_held : ∀ i < combWords.length,
    tblMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  have h := constMem_held 0x100000 combWords (by rw [combWords_length]; decide)
  unfold tblMem
  exact h

/-- `pkSat` with the table. -/
def pkSatC : State :=
  { pkSat with mem := tblMem, rd := pkSat.rd ++ [⟨0x100000, 49152⟩], syms := fun _ => 0x100000 }

theorem pkC_sat : (Sig.scratchContract (PPC64LE.abi.withConsts combConsts) Spec.Ed25519.publicKeySig "frame"
    .u8 144 (Curry.const (fun _ => True) _) (Proof.Ed25519.WholeLocal.publicKeyPost PPC64LE.abi.ptrBits) true
    48).pre pkSatC := by
  have hl := combWords_length
  have held := tblMem_held
  rw [show combConsts = [(combSym, combWords)] from rfl]
  generalize combWords = W' at hl held ⊢
  generalize e : pkSatC = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed25519.publicKeySig,
    Spec.Ed25519.scratchWords, PPC64LE.abi, PPC64LE.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 32⟩ : Region), ⟨0x4000, 8192⟩, ⟨0x8000, 144⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem pkC_implies : pkC.Implies (Sig.scratchContract (PPC64LE.abi.withConsts combConsts)
    Spec.Ed25519.publicKeySig "frame" .u8 144 (Curry.const (fun _ => True) _)
    (Proof.Ed25519.WholeLocal.publicKeyPost PPC64LE.abi.ptrBits) true 48) :=
  consts_implies (kR := pkR) pkR_implies (fun _ _ h => h) (fun _ _ h => h) ⟨pkSatC, pkC_sat⟩

theorem publicKey_verified :
    Verified PPC64LE.target publicKey (Sig.scratchContract (PPC64LE.abi.withConsts combConsts)
      Spec.Ed25519.publicKeySig "frame" .u8 144 (Curry.const (fun _ => True) _)
      (Proof.Ed25519.WholeLocal.publicKeyPost PPC64LE.abi.ptrBits) true 48) :=
  Verified.of_correct (pk_ok base_ok) pk_ct pkC_implies

/-- A state satisfying `vg_ed25519_public_key`'s precondition, without the frame. -/
def pkFrameSat : State := { pkSatC with wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩] }

theorem pkFrameSat_pre : ∃ s, (Spec.Ed25519.publicKeyContract (PPC64LE.abi.withConsts combConsts)
    (48 + 176)).pre s := by
  refine ⟨pkFrameSat, ?_⟩
  have hl := combWords_length
  have held := tblMem_held
  rw [show combConsts = [(combSym, combWords)] from rfl]
  generalize combWords = W' at hl held ⊢
  generalize e : pkFrameSat = s
  sig_pre [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig, Spec.Ed25519.scratchWords, PPC64LE.abi,
    PPC64LE.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 32⟩ : Region), ⟨0x4000, 8192⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

/-- In its frame of 176 bytes, whose first 136 it zeroes before returning. -/
theorem publicKey_framed :
    Verified PPC64LE.target publicKeyCode
      (Spec.Ed25519.publicKeyContract (PPC64LE.abi.withConsts combConsts) (48 + 176)) :=
  Verified.stackScratchWipedC (c₀ := (combSym, combWords)) (cs := []) (sig := Spec.Ed25519.publicKeySig)
    (nm := "frame") (e := .u8) (n := 144) (pre := Curry.const (fun _ => True) _)
    (post := Proof.Ed25519.WholeLocal.publicKeyPost PPC64LE.abi.ptrBits) (wa := true) (stack := 48) (bytes := 176)
    (words := 17) publicKey_verified (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Ed25519.WholeLocal.publicKeyPost_local _)
    (Proof.Ed25519.WholeLocal.publicKeyPostOut_local _) pkFrameSat_pre

end VG.Proof.Ed25519.PPC64LE.Whole
