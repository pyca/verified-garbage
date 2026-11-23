module

public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.EcKey.P192
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.Ecdsa.P192.ArmComb
public import VerifiedGarbage.Proof.EcKey.Arm.Main
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Verified
public import VerifiedGarbage.Proof.Ecdsa.Arm.P192.CombGenerator
import VerifiedGarbage.Proof.Ecdsa.Arm.P192.CombLit
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
public import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P192.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.P192.ArmComb
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.MulContract
meta import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.EcKey.Arm.P192.Lit
public import VerifiedGarbage.Impl.EcKey.P192.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Lit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.EcKey.Arm.Main
meta import VerifiedGarbage.Proof.EcKey.Arm.P192.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Verified
meta import VerifiedGarbage.Impl.EcKey.P192.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Spec.EcKey.P192
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.P192
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Spec.EcKey.Generic
meta import VerifiedGarbage.Spec.P192
meta import VerifiedGarbage.TCB.Arm.Isa
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `EcKey.Arm.P192.Verified`, which only this module used -/

section

/-! ### `EcKey.Arm.P192.Contract`, which this module and modules that import it used -/

section

/-!
# P-192 public keys on 32-bit ARM: the contract the proof is written against

The facts of `Spec.EcKey.P192.inst.publicKeyContract` for 32-bit ARM, by
name: `vg_ec_p192_public_key(out, d, scratch)`, with the arguments in
`r0`–`r2` (AAPCS), the result in `r0` (the low word of `r1:r0`).
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm.P192

open VG VG.Arm Spec.Weierstrass Spec.EcKey

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.P192.curve) :=
  publicKey Spec.P192.curve (ofBytes (bytesAt m d 24))

def pkArm : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 49⟩
    let d : Region := ⟨State.addr (s.gpr .r1), 24⟩
    let scratch : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      (s.gpr .r0).toNat + 49 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 24 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32
  post s s' :=
    match pk s.mem (State.addr (s.gpr .r1)) with
    | some (.affine x y) => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 49 = encodePoint (.affine x y)
    | _ => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 49 = List.replicate 49 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2

end VG.Proof.EcKey.Arm.P192

end

end

/-!
# P-192 public keys on 32-bit ARM: `Verified`

`publicKey_ok` for P-192 (`p192_ok`, and `Law` for its group law, which the
registration file supplies) gives the contract's postcondition; `r4`–`r11`
and `lr` are restored and `sp` kept. Constant time by taint tracking from
the arguments' registers: the only branches are on loop counters, and every
address is `r12` (`scratch`) or `lr` (`out`) plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm.P192

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P192 Spec.Weierstrass

theorem post_of {u : Bool} {s s' : State} (h : PkPost (p192With u) s s') : pkArm.post s s' := by
  unfold PkPost at h
  simp only [pkArm, BitVec.setWidth_append_eq_right]
  revert h
  generalize hq : pk s.mem (State.addr (s.gpr .r1)) = q
  rw [show Spec.EcKey.publicKey (p192With u).C (dk (p192With u) s) = pk s.mem (State.addr (s.gpr .r1)) from rfl,
    hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

end VG.Proof.EcKey.Arm.P192

end

end

/-!
# P-192 public keys on 32-bit ARM with the generator comb

`vg_ec_p192_public_key` with `[d]G` by the comb signing uses: the contract
with the comb's table, its constant time, and `Verified`.
-/

@[expose] public section
namespace VG.Proof.EcKey.Arm.P192
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm.TComb
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P192 VG.Proof.EcKey.Arm

/-- The tables the public key reads: the comb's, and the setup's constants. -/
abbrev combPkK (u : Bool) : List (String × List (BitVec 64)) := p192CombConsts ++ (p192With u).constsK

abbrev combPkSpec (u : Bool) : Contract isa :=
  Spec.EcKey.P192.inst.publicKeyContract (abi.withConsts (combPkK u))

def combPkPre (u : Bool) (s : State) : Prop :=
  PkPre (p192With u) s (constRegs (combPkK u) s) ∧ ConstsOk (combPkK u) 0 s

theorem combPk_pre {u : Bool} {s : State} (h : (combPkSpec u).pre s) : combPkPre u s := by
  have hp : (Spec.EcKey.P192.inst.publicKeyContract abi).pre (stripConsts (combPkK u) s) ∧
      ConstsOk (combPkK u) 0 s := pre_consts.mp h
  obtain ⟨h₁, hk⟩ := hp
  sig_pre [Spec.EcKey.P192.inst,Spec.EcKey.Instance.publicKeyContract,Spec.EcKey.Instance.publicKeySig,
    Spec.P192.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,Loc.val,State.addr] at h₁
  obtain ⟨_sp,rd,wr,_od,os,ds,fo,fd,fs⟩ := h₁
  refine ⟨⟨hk.rd_strip rd,wr,os,ds,fo,fd,fs,fun _ => tbl_of_consts hk
    (List.mem_append_right _ (List.mem_singleton_self _)) ?_⟩,hk⟩
  rw [wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem combPk_ok (hC : Law Spec.P192.curve) {u : Bool} {s₀ : State} (hp : combPkPre u s₀) :
    WP isa (publicKeyP192CombWith u) s₀ fun t => PkKeep (p192With u) s₀ t ∧ PkPost (p192With u) s₀ t := by
  have member : (p192Comb.tsym,p192CombWords)∈combPkK u := List.mem_cons_self
  have ht := tableMem_of_consts hp.2 member
  have hd := table_disjoint_of_consts hp.2 member
    (show (⟨ptr s₀ .r2,8192⟩ : Region)∈s₀.wr by rw [hp.1.wr]; simp)
  exact publicKeyWith_ok (p192With_ok u) hC hp.1 fun _ S sy => comb_generator_stage hC S sy ht rfl hd

def combPkPub (u : Bool) (s t : State) : Prop :=
  pkArm.pub s t ∧ s.syms p192Comb.tsym=t.syms p192Comb.tsym ∧ s.syms (p192With u).constSym=t.syms (p192With u).constSym

/-- The taint analysis's start, and the tables' addresses, agree in the two states. -/
theorem combPk_agree {u : Bool} {s t : State} (h : combPkPub u s t) :
    VG.Arm.Taint.Agree (Taint.ofRegs [.r0,.r1,.r2]) s t ∧
      ∀ n ∈ [p192Comb.tsym,(p192With u).constSym], s.syms n = t.syms n := by
  obtain ⟨⟨_,h0,h1,h2⟩,sy,sy'⟩ := h
  refine ⟨Taint.agree_ofRegs (fun r hr => ?_),fun n hn => ?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    exacts [h0,h1,h2]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl|rfl
    exacts [sy,sy']

theorem combPk_ct : ConstantTime isa (combPkPre false) (combPkPub false) publicKeyP192Comb :=
  VG.Taint.constantTime (A := taintSym [p192Comb.tsym,(p192With false).constSym]) (Taint.ofRegs [.r0,.r1,.r2])
    (fun _ _ _ _ h => combPk_agree h) (by native_taint_decide)

theorem combPkU_ct : ConstantTime isa (combPkPre true) (combPkPub true) publicKeyP192CombU :=
  VG.Taint.constantTime (A := taintSymU [p192Comb.tsym,(p192With true).constSym]) (Taint.ofRegs [.r0,.r1,.r2])
    (fun _ _ _ _ h => combPk_agree h) (by taint_decide)

/-- The comb's table at `0x100000`, then the setup's constants. -/
@[irreducible] def combPkMem (u : Bool) : Mem := constMem 0x100000 (p192CombWords ++ (p192With u).constTbl)

open VG.Proof.P192.Arm in
def combPkSat (u : Bool) : State := {combSatState with
  gpr := fun r => match r with | .r0 => 0x10000 | .r1 => 0x12000 | _ => 0
  mem := combPkMem u
  rd := [⟨0x12000,24⟩,⟨0x100000,86016⟩,⟨0x115000,408⟩]
  wr := [⟨0x10000,49⟩,⟨0,8192⟩]
  syms := fun n => if n = (p192With u).constSym then 0x115000 else 0x100000 }

open VG.Proof.P192.Arm in
theorem combPk_sat (u : Bool) : (combPkSpec u).pre (combPkSat u) := by
  obtain ⟨held₁, held₂⟩ := constMem_held₂ 0x100000 p192CombWords (p192With u).constTbl
    (by rw [comb_words_length, constTbl_length]; cases u <;> decide)
  have hl := constTbl_length (p192With u)
  obtain ⟨W, eW⟩ : ∃ W, (p192With u).constTbl = W := ⟨_, rfl⟩
  have hk : combPkK u = [(p192Comb.tsym,p192CombWords),((p192With u).constSym, W)] := by rw [← eW]; rfl
  have hs₁ : (combPkSat u).syms "VG_P192_COMB" = 0x100000 := by cases u <;> decide
  have hs₂ : (combPkSat u).syms (p192With u).constSym = 0x115000 := by cases u <;> decide
  rw [comb_words_length, show (0x100000 : Addr) + BitVec.ofNat 64 (8 * 10752) = 0x115000 by decide] at held₂
  have hmem : (combPkSat u).mem = constMem 0x100000 (p192CombWords ++ (p192With u).constTbl) := by
    show combPkMem u = _; unfold combPkMem; rfl
  show (combPkSpec u).pre _
  unfold combPkSpec
  rw [hk]
  rw [eW] at hl held₁ held₂ hmem
  generalize eqs : combPkSat u = s
  sig_pre [combPkSpec,Spec.EcKey.P192.inst,Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig,Spec.P192.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,
    Loc.val,State.addr,Abi.withConsts,Abi.constRegions_cons,Abi.constRegions_nil,
    Abi.constsHeld,stackBelow]
  subst s
  simp only [hmem, comb_words_length, hl]
  sig_and_intros
  all_goals try exact Region.disjoint_of_sep (by cases u <;> decide)
  all_goals try (intro r hr; change r∈[⟨0x10000,49⟩,⟨0,8192⟩] at hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl <;> exact Region.disjoint_of_sep (by cases u <;> decide))
  all_goals try (intro i hi; rw [hs₁, show BitVec.setWidth 64 (1048576 : BitVec 32) = (1048576 : Addr) by decide]; exact held₁ i (by rw [comb_words_length]; exact hi))
  all_goals try (intro i hi; rw [hs₂, show BitVec.setWidth 64 (1134592 : BitVec 32) = (1134592 : Addr) by decide]; exact held₂ i (by rw [hl]; exact hi))
  all_goals try (cases u <;> decide)
  all_goals rfl

def combPkLocal (u : Bool) : Contract isa where
  pre := combPkPre u
  post := PkPost (p192With u)
  pub := combPkPub u

theorem combPkWith_verified (hC : Weierstrass.Law Spec.P192.curve) (u : Bool)
    (hct : ConstantTime isa (combPkPre u) (combPkPub u) (publicKeyP192CombWith u)) :
    Verified Arm.target (publicKeyP192CombWith u) (combPkSpec u) := by
  refine Verified.of_correct (k := combPkLocal u) (fun s hs => ?_) hct
    ⟨fun _ h => combPk_pre h,?_,?_,⟨combPkSat u,combPk_sat u⟩⟩
  · obtain ⟨tr,t,exec,keep,post⟩ := combPk_ok hC hs
    exact ⟨tr,t,exec,VG.Proof.Ecdsa.Arm.abi_of_saved keep.saved keep.sp,post⟩
  · intro s t _ post
    sig_post [combPkSpec,Spec.EcKey.P192.inst,Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig,Spec.P192.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,Abi.withConsts]
    dsimp only [combPkLocal] at post
    have pp := post_of (u := u) post
    simp only [pkArm,pk,Spec.P192.curve,State.addr] at pp
    revert pp
    generalize Spec.EcKey.publicKey _ _=q
    rcases q with _|_|⟨x,y⟩ <;> exact id
  · intro s t _ _ pub
    obtain ⟨pub, sy⟩ := pub_consts.mp pub
    sig_pub [Spec.EcKey.P192.inst,Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig,Spec.P192.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr] at pub
    obtain ⟨sp,h0,h1,h2⟩ := pub
    exact ⟨⟨sp,h0,h1,h2⟩,symAddr_eq_iff.mp (sy (p192Comb.tsym, p192CombWords) List.mem_cons_self),
      symAddr_eq_iff.mp (sy ((p192With u).constSym, (p192With u).constTbl) (List.mem_cons_of_mem _ (List.mem_singleton_self _)))⟩

theorem combPk_verified (hC : Weierstrass.Law Spec.P192.curve) :
    Verified Arm.target publicKeyP192Comb (combPkSpec false) :=
  combPkWith_verified hC false combPk_ct

theorem combPkU_verified (hC : Weierstrass.Law Spec.P192.curve) :
    Verified Arm.target publicKeyP192CombU (combPkSpec true) :=
  combPkWith_verified hC true combPkU_ct

end VG.Proof.EcKey.Arm.P192
