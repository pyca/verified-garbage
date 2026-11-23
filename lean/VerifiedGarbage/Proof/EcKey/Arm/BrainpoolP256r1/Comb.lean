module

public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.ArmComb
public import VerifiedGarbage.Proof.EcKey.Arm.Main
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.CombGenerator
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.CombLit
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
public import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.ArmComb
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.MulContract
meta import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP256r1.Lit
public import VerifiedGarbage.Impl.EcKey.BrainpoolP256r1.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Lit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.EcKey.Arm.Main
meta import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP256r1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Verified
meta import VerifiedGarbage.Impl.EcKey.BrainpoolP256r1.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.BrainpoolP256r1
public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Spec.BrainpoolP256r1
meta import VerifiedGarbage.Spec.EcKey.Generic
meta import VerifiedGarbage.TCB.Arm.Isa
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `EcKey.Arm.BrainpoolP256r1.Verified`, which only this module used -/

section

/-! ### `EcKey.Arm.BrainpoolP256r1.Contract`, which this module and modules that import it used -/

section

/-!
# brainpoolP256r1 public keys on 32-bit ARM: the contract the proof is written against

The facts of `Spec.EcKey.BrainpoolP256r1.inst.publicKeyContract` for 32-bit ARM, by
name: `vg_ec_brainpoolp256r1_public_key(out, d, scratch)`, with the arguments in
`r0`–`r2` (AAPCS), the result in `r0` (the low word of `r1:r0`).
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm.BrainpoolP256r1

open VG VG.Arm Spec.Weierstrass Spec.EcKey

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.BrainpoolP256r1.curve) :=
  publicKey Spec.BrainpoolP256r1.curve (ofBytes (bytesAt m d 32))

def pkArm : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 65⟩
    let d : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let scratch : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      (s.gpr .r0).toNat + 65 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32
  post s s' :=
    match pk s.mem (State.addr (s.gpr .r1)) with
    | some (.affine x y) => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 65 = encodePoint (.affine x y)
    | _ => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 65 = List.replicate 65 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2

end VG.Proof.EcKey.Arm.BrainpoolP256r1

end

end

/-!
# brainpoolP256r1 public keys on 32-bit ARM: `Verified`

`publicKey_ok` for brainpoolP256r1 (`brainpoolp256r1_ok`, and `Law` for its group law, which the
registration file supplies) gives the contract's postcondition; `r4`–`r11`
and `lr` are restored and `sp` kept. Constant time by taint tracking from
the arguments' registers: the only branches are on loop counters, and every
address is `r12` (`scratch`) or `lr` (`out`) plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm.BrainpoolP256r1

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.BrainpoolP256r1 Spec.Weierstrass

theorem post_of {u : Bool} {s s' : State} (h : PkPost (brainpoolp256r1With u) s s') : pkArm.post s s' := by
  unfold PkPost at h
  simp only [pkArm, BitVec.setWidth_append_eq_right]
  revert h
  generalize hq : pk s.mem (State.addr (s.gpr .r1)) = q
  rw [show Spec.EcKey.publicKey (brainpoolp256r1With u).C (dk (brainpoolp256r1With u) s) = pk s.mem (State.addr (s.gpr .r1)) from rfl,
    hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

end VG.Proof.EcKey.Arm.BrainpoolP256r1

end

end

/-!
# brainpoolP256r1 public keys on 32-bit ARM with the generator comb

`vg_ec_brainpoolp256r1_public_key` with `[d]G` by the comb signing uses: the contract
with the comb's table, its constant time, and `Verified`.
-/

@[expose] public section
namespace VG.Proof.EcKey.Arm.BrainpoolP256r1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm.TComb
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.BrainpoolP256r1 VG.Proof.EcKey.Arm

/-- The tables the public key reads: the comb's, and the setup's constants. -/
abbrev combPkK (u : Bool) : List (String × List (BitVec 64)) := brainpoolp256r1CombConsts ++ (brainpoolp256r1With u).constsK

abbrev combPkSpec (u : Bool) : Contract isa :=
  Spec.EcKey.BrainpoolP256r1.inst.publicKeyContract (abi.withConsts (combPkK u))

def combPkPre (u : Bool) (s : State) : Prop :=
  PkPre (brainpoolp256r1With u) s (constRegs (combPkK u) s) ∧ ConstsOk (combPkK u) 0 s

theorem combPk_pre {u : Bool} {s : State} (h : (combPkSpec u).pre s) : combPkPre u s := by
  have hp : (Spec.EcKey.BrainpoolP256r1.inst.publicKeyContract abi).pre (stripConsts (combPkK u) s) ∧
      ConstsOk (combPkK u) 0 s := pre_consts.mp h
  obtain ⟨h₁, hk⟩ := hp
  sig_pre [Spec.EcKey.BrainpoolP256r1.inst,Spec.EcKey.Instance.publicKeyContract,Spec.EcKey.Instance.publicKeySig,
    Spec.BrainpoolP256r1.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,Loc.val,State.addr] at h₁
  obtain ⟨_sp,rd,wr,_od,os,ds,fo,fd,fs⟩ := h₁
  refine ⟨⟨hk.rd_strip rd,wr,os,ds,fo,fd,fs,fun _ => tbl_of_consts hk
    (List.mem_append_right _ (List.mem_singleton_self _)) ?_⟩,hk⟩
  rw [wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem combPk_ok (hC : Law Spec.BrainpoolP256r1.curve) {u : Bool} {s₀ : State} (hp : combPkPre u s₀) :
    WP isa (publicKeyBrainpoolP256r1CombWith u) s₀ fun t => PkKeep (brainpoolp256r1With u) s₀ t ∧ PkPost (brainpoolp256r1With u) s₀ t := by
  have member : (brainpoolp256r1Comb.tsym,brainpoolp256r1CombWords)∈combPkK u := List.mem_cons_self
  have ht := tableMem_of_consts hp.2 member
  have hd := table_disjoint_of_consts hp.2 member
    (show (⟨ptr s₀ .r2,8192⟩ : Region)∈s₀.wr by rw [hp.1.wr]; simp)
  exact publicKeyWith_ok (brainpoolp256r1With_ok u) hC hp.1 fun _ S sy => comb_generator_stage hC S sy ht rfl hd

def combPkPub (u : Bool) (s t : State) : Prop :=
  pkArm.pub s t ∧ s.syms brainpoolp256r1Comb.tsym=t.syms brainpoolp256r1Comb.tsym ∧ s.syms (brainpoolp256r1With u).constSym=t.syms (brainpoolp256r1With u).constSym

/-- The taint analysis's start, and the tables' addresses, agree in the two states. -/
theorem combPk_agree {u : Bool} {s t : State} (h : combPkPub u s t) :
    VG.Arm.Taint.Agree (Taint.ofRegs [.r0,.r1,.r2]) s t ∧
      ∀ n ∈ [brainpoolp256r1Comb.tsym,(brainpoolp256r1With u).constSym], s.syms n = t.syms n := by
  obtain ⟨⟨_,h0,h1,h2⟩,sy,sy'⟩ := h
  refine ⟨Taint.agree_ofRegs (fun r hr => ?_),fun n hn => ?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    exacts [h0,h1,h2]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl|rfl
    exacts [sy,sy']

theorem combPk_ct : ConstantTime isa (combPkPre false) (combPkPub false) publicKeyBrainpoolP256r1Comb :=
  VG.Taint.constantTime (A := taintSym [brainpoolp256r1Comb.tsym,(brainpoolp256r1With false).constSym]) (Taint.ofRegs [.r0,.r1,.r2])
    (fun _ _ _ _ h => combPk_agree h) (by native_taint_decide)

theorem combPkU_ct : ConstantTime isa (combPkPre true) (combPkPub true) publicKeyBrainpoolP256r1CombU :=
  VG.Taint.constantTime (A := taintSymU [brainpoolp256r1Comb.tsym,(brainpoolp256r1With true).constSym]) (Taint.ofRegs [.r0,.r1,.r2])
    (fun _ _ _ _ h => combPk_agree h) (by taint_decide)

open VG.Proof.BrainpoolP256r1.Arm in
/-- A state satisfying the precondition without the tables, which it holds
in `constMem`: the comb's at `0x100000`, then the setup's constants at
`0x125000`. -/
def combPkSat (u : Bool) : State := {combSatState with
  gpr := fun r => match r with | .r0 => 0x10000 | .r1 => 0x12000 | _ => 0
  mem := constMem ((0x100000 : BitVec 32).setWidth 64) (brainpoolp256r1CombWords ++ (brainpoolp256r1With u).constTbl)
  rd := [⟨0x12000,32⟩]
  wr := [⟨0x10000,65⟩,⟨0,8192⟩]
  syms := fun n => if n = (brainpoolp256r1With u).constSym then 0x125000 else 0x100000 }

open VG.Proof.BrainpoolP256r1.Arm in
theorem combPk_sat (u : Bool) : ∃ s, (combPkSpec u).pre s :=
  sat_consts (s := combPkSat u)
    (by
      cases u <;>
      (sig_pre [Spec.EcKey.BrainpoolP256r1.inst,Spec.EcKey.Instance.publicKeyContract,Spec.EcKey.Instance.publicKeySig,
    Spec.BrainpoolP256r1.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,Loc.val,State.addr,combPkSat,combSatState]
       sig_and_intros
       all_goals first
         | rfl
         | decide
         | exact Region.disjoint_of_sep (by decide)))
    (constsOk_two _ (T := 0x100000) (T₂ := 0x125000) (by cases u <;> decide) (by cases u <;> decide)
      (by rw [comb_words_length]; decide) rfl (by cases u <;> decide) (by decide) (by decide)
      (by rw [comb_words_length]; cases u <;> decide) (by cases u <;> decide)
      (by rw [comb_words_length]; cases u <;> decide) (by cases u <;> decide))

def combPkLocal (u : Bool) : Contract isa where
  pre := combPkPre u
  post := PkPost (brainpoolp256r1With u)
  pub := combPkPub u

theorem combPkWith_verified (hC : Weierstrass.Law Spec.BrainpoolP256r1.curve) (u : Bool)
    (hct : ConstantTime isa (combPkPre u) (combPkPub u) (publicKeyBrainpoolP256r1CombWith u)) :
    Verified Arm.target (publicKeyBrainpoolP256r1CombWith u) (combPkSpec u) := by
  refine Verified.of_correct (k := combPkLocal u) (fun s hs => ?_) hct
    ⟨fun _ h => combPk_pre h,?_,?_,combPk_sat u⟩
  · obtain ⟨tr,t,exec,keep,post⟩ := combPk_ok hC hs
    exact ⟨tr,t,exec,VG.Proof.Ecdsa.Arm.abi_of_saved keep.saved keep.sp,post⟩
  · intro s t _ post
    sig_post [combPkSpec,Spec.EcKey.BrainpoolP256r1.inst,Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig,Spec.BrainpoolP256r1.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,Abi.withConsts]
    dsimp only [combPkLocal] at post
    have pp := post_of (u := u) post
    simp only [pkArm,pk,Spec.BrainpoolP256r1.curve,State.addr] at pp
    revert pp
    generalize Spec.EcKey.publicKey _ _=q
    rcases q with _|_|⟨x,y⟩ <;> exact id
  · intro s t _ _ pub
    obtain ⟨pub, sy⟩ := pub_consts.mp pub
    sig_pub [Spec.EcKey.BrainpoolP256r1.inst,Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig,Spec.BrainpoolP256r1.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr] at pub
    obtain ⟨sp,h0,h1,h2⟩ := pub
    exact ⟨⟨sp,h0,h1,h2⟩,symAddr_eq_iff.mp (sy (brainpoolp256r1Comb.tsym, brainpoolp256r1CombWords) List.mem_cons_self),
      symAddr_eq_iff.mp (sy ((brainpoolp256r1With u).constSym, (brainpoolp256r1With u).constTbl) (List.mem_cons_of_mem _ (List.mem_singleton_self _)))⟩

theorem combPk_verified (hC : Weierstrass.Law Spec.BrainpoolP256r1.curve) :
    Verified Arm.target publicKeyBrainpoolP256r1Comb (combPkSpec false) :=
  combPkWith_verified hC false combPk_ct

theorem combPkU_verified (hC : Weierstrass.Law Spec.BrainpoolP256r1.curve) :
    Verified Arm.target publicKeyBrainpoolP256r1CombU (combPkSpec true) :=
  combPkWith_verified hC true combPkU_ct

end VG.Proof.EcKey.Arm.BrainpoolP256r1
