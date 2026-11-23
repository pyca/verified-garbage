module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Hash
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Hash
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Main
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.ArmComb
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.CT
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.CT
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP512r1.Contract
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.CombGenerator
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.CombLit
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombCorrect
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
public import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.ArmComb
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Main
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP512r1.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.CombGenerator
meta import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
meta import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
meta import VerifiedGarbage.Proof.Weierstrass.Arm.TCombCorrect
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# ECDSA verification over brainpoolP512r1 on 32-bit ARM with the generator comb

`vg_ecdsa_brainpoolp512r1_verify` with `[u]G` by the comb signing uses (`[v]Q` stays
the ladder): the contract with the comb's table, its constant
time, and `Verified`.
-/

@[expose] public section

-- Powers of two up to `2^512` are evaluated.
set_option exponentiation.threshold 512
namespace VG.Proof.Ecdsa.Verify.Arm.BrainpoolP512r1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Impl.Ecdsa.Verify.Arm (U)
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.BrainpoolP512r1 VG.Proof.Ecdsa.Verify.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass.Arm.TComb
open VG.Proof.Mont VG.Proof.Mont.Arm

/-- The tables verification reads: the comb's, and the setup's constants. -/
abbrev combVerifyK (um : Bool) : List (String × List (BitVec 64)) := brainpoolp512r1CombConsts ++ (brainpoolp512r1With um).constsK

abbrev combVerifySpec (um : Bool) : Contract isa :=
  Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP512r1.inst (abi.withConsts (combVerifyK um))

def combVerifyPre (um : Bool) (s : State) : Prop :=
  VPre (brainpoolp512r1With um) s (constRegs (combVerifyK um) s) ∧ ConstsOk (combVerifyK um) 0 s

theorem combVerify_pre {um : Bool} {s : State} (h : (combVerifySpec um).pre s) : combVerifyPre um s := by
  have hp : (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP512r1.inst abi).pre (stripConsts (combVerifyK um) s) ∧
      ConstsOk (combVerifyK um) 0 s := pre_consts.mp h
  obtain ⟨h₁, hk⟩ := hp
  sig_pre [Spec.Ecdsa.BrainpoolP512r1.inst,Proof.Ecdsa.verifyContract,Proof.Ecdsa.verifySig,
    Spec.BrainpoolP512r1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,Loc.val,State.addr] at h₁
  obtain ⟨_sp,rd,wr,ps,ds,ss,fp,fd,fs,fc⟩ := h₁
  refine ⟨⟨hk.rd_strip rd,wr,ps,ds,ss,fp,fd,fs,fc,tbl_of_consts hk
    (List.mem_append_right _ (List.mem_singleton_self _)) ?_⟩,hk⟩
  rw [wr]; exact List.mem_singleton_self _

/-- Verification's `[u]G` by the comb, as `verifyWith_ok` and `verifyHead_ok` ask. -/
theorem comb_generatorWP (hC : Law Spec.BrainpoolP512r1.curve) {um : Bool} {s₀ : State} (hp : combVerifyPre um s₀) :
    ∀ s, Mid (brainpoolp512r1With um) s₀ (ptr s₀ .r3) s → s.syms = s₀.syms →
      GeneratorWP (brainpoolp512r1With um) (verifyGeneratorBrainpoolP512r1With um) s₀ (ptr s₀ .r3)
        (sv (brainpoolp512r1With um) (ptr s₀ .r3) s U)
        (fun j X Y Z => Rep (brainpoolp512r1With um).C X Y Z
          (Spec.Weierstrass.mul (sv (brainpoolp512r1With um) (ptr s₀ .r3) s U >>> j) (Spec.Weierstrass.G (brainpoolp512r1With um).C)))
        s.syms false := by
  have member : (brainpoolp512r1Comb.tsym,brainpoolp512r1CombWords)∈combVerifyK um := List.mem_cons_self
  have ht := tableMem_of_consts hp.2 member
  have hd := table_disjoint_of_consts hp.2 member
    (show (⟨ptr s₀ .r3,8192⟩ : Region)∈s₀.wr by rw [hp.1.wr]; simp)
  intro s M syms
  intro u hs hf F _ _ _ _ _ _ _ kv keep unch syu
  have frame : Frame [⟨ptr s₀ .r3,8192⟩] s₀.mem u.mem := outside_frame
    (unch.outside (o := 0) (n := 8192) (by simp)) (Nat.le_refl _)
  have hu := ht.of_frame (by rw [keep.rd,keep.wr]) frame
    (by simpa only [List.mem_singleton,forall_eq] using hd)
  have k_eq : sv (brainpoolp512r1With um) (ptr s₀ .r3) u K=sv (brainpoolp512r1With um) (ptr s₀ .r3) s U := kv rfl
  -- The table of `u`'s bits, from `K`'s slot.
  refine WP.seq (WP.mono_syms (tbl_bits_ok (brainpoolp512r1With_ok um) hs hf (i := K) (j := 0) (by decide) (by decide))
    fun u₂ ⟨b₂,k₂,O₂⟩ sy₂ => ?_)
  have hs₂ := hs.of_rest k₂ (by decide)
  have hf₂ := hf.of_rest k₂
  have F₂ := F.unch (brainpoolp512r1With_ok um).n10 hs.nowrap (W := [(bitsAt (brainpoolp512r1With um).n 0,64*(brainpoolp512r1With um).n)])
    (fun w hw => Or.inr (by rw [List.mem_singleton.mp hw]; cases um <;> decide)) O₂.unch
  have hu₂ := hu.of_frame (by rw [k₂.rd,k₂.wr]) (outside_frame O₂ (size := 8192) (by cases um <;> decide))
    (by simpa only [List.mem_singleton,forall_eq] using hd)
  have bits : ∀ i<512,u₂.mem (off (ptr s₀ .r3) (bitsAt (brainpoolp512r1With um).n 0+i))=
      if (sv (brainpoolp512r1With um) (ptr s₀ .r3) s U).testBit i then 1 else 0 := fun i hi => by
    rw [b₂ i hi]
    simp only [sv] at k_eq
    rw [k_eq]
  have mul := comb_generator_ok hC hs₂ hf₂ F₂ hu₂ (by rw [sy₂,syu,syms]; rfl)
    (hd.sub_right (Region.sub_prefix (by decide))) (k := sv (brainpoolp512r1With um) (ptr s₀ .r3) s U)
    (VG.Proof.Mont.wordsVal_lt _ _ _ _) bits
  refine WP.mono mul fun t ⟨R,U',Mo,L,Rp⟩ => ⟨(k₂.mono (by decide)).trans R,
    (O₂.unch.trans U').mono fun w hw => ?_,Mo,L,by simpa only [Nat.shiftRight_zero] using Rp⟩
  rcases List.mem_append.mp hw with h|h
  · rw [List.mem_singleton.mp h]
    exact List.mem_append_right _ (by simp [genX])
  · exact h

theorem combVerify_ok (hC : Law Spec.BrainpoolP512r1.curve) {um : Bool} {s₀ : State} (hp : combVerifyPre um s₀) :
    WP isa (verifyBrainpoolP512r1CombWith um) s₀ fun t => VKeep s₀ t ∧ VPost (brainpoolp512r1With um) s₀ t :=
  verifyWith_ok (brainpoolp512r1With_ok um) hC hp.1 (a0₁ := false) nofun (comb_generatorWP hC hp)

/-- What timing may depend on: the pointers and the table's address, and
the key and the signature (`VPub`), which the contract lets it depend on. -/
def combVerifyPub (um : Bool) (s t : State) : Prop :=
  (verifyArm.pub s t ∧ s.syms brainpoolp512r1Comb.tsym = t.syms brainpoolp512r1Comb.tsym ∧
    s.syms (brainpoolp512r1With um).constSym = t.syms (brainpoolp512r1With um).constSym) ∧ VPub (brainpoolp512r1With um) s t

/-- `vg_brainpoolp512r1_mul_public`'s pieces and the two parts of verification around
its call, in sequence: what the taint analysis checks. -/
def ctPiecesWith (um : Bool) : Prog isa :=
  pieces (pubPieces (brainpoolp512r1With um) ++
    [verifyHead (brainpoolp512r1With um) (verifyGeneratorBrainpoolP512r1With um), verifyTail (brainpoolp512r1With um)])

def ctPieces : Prog isa := ctPiecesWith false

def ctPiecesU : Prog isa := ctPiecesWith true

materialize_code ctPieces
materialize_code ctPiecesU

theorem pubLeaves : PubLeaves (brainpoolp512r1With false) := by
  apply PubLeaves.of_checks (A := VG.Arm.taint) (τ := VG.Arm.Taint.ofRegs)
    (fun _ _ _ h => VG.Arm.Taint.agree_ofRegs h) (L := ctPieces) (extra := [_, _]) rfl <;>
    native_taint_decide

theorem pubLeavesU : PubLeaves (brainpoolp512r1With true) := by
  apply PubLeaves.of_checks (A := VG.Arm.taintU) (τ := VG.Arm.Taint.ofRegs)
    (fun _ _ _ h => VG.Arm.Taint.agree_ofRegs h) (L := ctPiecesU) (extra := [_, _]) rfl <;>
    taint_decide

/-- Verification is constant time but in the key and the signature, given the
taint analysis's checks of its parts. -/
theorem combVerifyWith_ct (hC : Law Spec.BrainpoolP512r1.curve) (um : Bool) (L : PubLeaves (brainpoolp512r1With um))
    (hhead : RelCT isa (fun x y => combVerifyPre um x ∧ combVerifyPre um y ∧ combVerifyPub um x y)
      (verifyHead (brainpoolp512r1With um) (verifyGeneratorBrainpoolP512r1With um)) fun _ _ => True)
    (htail : LeafCT [.r12] (verifyTail (brainpoolp512r1With um))) :
    ConstantTime isa (combVerifyPre um) (combVerifyPub um) (verifyBrainpoolP512r1CombWith um) :=
  verifyWith_ct (brainpoolp512r1With_ok um) hC rfl (fun _ _ _ _ h => h.2)
    (fun _ hp => verifyHead_ok (brainpoolp512r1With_ok um) hC hp.1 (a0₁ := false) nofun (comb_generatorWP hC hp))
    hhead htail L

theorem combVerify_ct (hC : Law Spec.BrainpoolP512r1.curve) :
    ConstantTime isa (combVerifyPre false) (combVerifyPub false) verifyBrainpoolP512r1Comb :=
  combVerifyWith_ct hC false pubLeaves
    (RelCT.taint (A := taintSym [brainpoolp512r1Comb.tsym, (brainpoolp512r1With false).constSym]) (c := piece ctPieces 26)
      (Taint.ofRegs [.r0, .r1, .r2, .r3])
      (fun _ _ h => ⟨Taint.agree_ofRegs (by
        obtain ⟨⟨⟨_, h0, h1, h2, h3⟩, _⟩, _⟩ := h.2.2
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        exacts [h0, h1, h2, h3]), fun n hn => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl
        exacts [h.2.2.1.2.1, h.2.2.1.2.2]⟩) (by native_taint_decide))
    (LeafCT.check (p := piece ctPieces 27) (by native_taint_decide))

theorem combVerifyU_ct (hC : Law Spec.BrainpoolP512r1.curve) :
    ConstantTime isa (combVerifyPre true) (combVerifyPub true) verifyBrainpoolP512r1CombU :=
  combVerifyWith_ct hC true pubLeavesU
    (RelCT.taint (A := taintSymU [brainpoolp512r1Comb.tsym, (brainpoolp512r1With true).constSym]) (c := piece ctPiecesU 26)
      (Taint.ofRegs [.r0, .r1, .r2, .r3])
      (fun _ _ h => ⟨Taint.agree_ofRegs (by
        obtain ⟨⟨⟨_, h0, h1, h2, h3⟩, _⟩, _⟩ := h.2.2
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        exacts [h0, h1, h2, h3]), fun n hn => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl
        exacts [h.2.2.1.2.1, h.2.2.1.2.2]⟩) (by taint_decide))
    (LeafCT.checkU (p := piece ctPiecesU 27) (by taint_decide))

open VG.Proof.BrainpoolP512r1.Arm in
/-- A state satisfying the precondition without the tables, which it holds
in `constMem`: the comb's at `0x100000`, then the setup's constants at
`0x194000`. -/
def combVerifyBase (um : Bool) : State := {combSatState with
  gpr := fun r => match r with | .r0 => 0x10000 | .r1 => 0x12000 | .r2 => 0x14000 | _ => 0
  mem := constMem ((0x100000 : BitVec 32).setWidth 64) (brainpoolp512r1CombWords ++ (brainpoolp512r1With um).constTbl)
  rd := [⟨0x10000,129⟩,⟨0x12000,64⟩,⟨0x14000,128⟩]
  wr := [⟨0,8192⟩]
  syms := fun n => if n = (brainpoolp512r1With um).constSym then 0x194000 else 0x100000 }

/-- `combVerifyBase` with the tables' regions. -/
abbrev combVerifySat (um : Bool) : State :=
  { combVerifyBase um with rd := (combVerifyBase um).rd ++ constRegs (combVerifyK um) (combVerifyBase um) }

theorem combVerifyBase_regs (um : Bool) :
    constRegs (combVerifyK um) (combVerifyBase um) = [⟨0x100000, 8 * brainpoolp512r1CombWords.length⟩, ⟨0x194000, 8 * (17 * 8)⟩] :=
  constRegs_two (brainpoolp512r1With um) (T := 0x100000) (T₂ := 0x194000) (by cases um <;> decide) (by cases um <;> decide)

open VG.Proof.BrainpoolP512r1.Arm in
theorem combVerify_sat (um : Bool) : (combVerifySpec um).pre (combVerifySat um) :=
  pre_consts_append
    (by
      cases um <;>
      (sig_pre [Spec.Ecdsa.BrainpoolP512r1.inst,Proof.Ecdsa.verifyContract,Proof.Ecdsa.verifySig,
    Spec.BrainpoolP512r1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,Loc.val,State.addr,combVerifyBase,combSatState]
       sig_and_intros
       all_goals first
         | rfl
         | decide
         | exact Region.disjoint_of_sep (by decide)))
    (constsOk_two _ (T := 0x100000) (T₂ := 0x194000) (by cases um <;> decide) (by cases um <;> decide)
      (by rw [comb_words_length]; decide) rfl (by cases um <;> decide) (by decide) (by decide)
      (by rw [comb_words_length]; cases um <;> decide) (by cases um <;> decide)
      (by rw [comb_words_length]; cases um <;> decide) (by cases um <;> decide))

def combVerifyLocal (um : Bool) : Contract isa where
  pre := combVerifyPre um
  post := VPost (brainpoolp512r1With um)
  pub := combVerifyPub um

theorem combVerifyWith_verified (hC : Weierstrass.Law Spec.BrainpoolP512r1.curve) (um : Bool)
    (hct : ConstantTime isa (combVerifyPre um) (combVerifyPub um) (verifyBrainpoolP512r1CombWith um)) :
    Verified Arm.target (verifyBrainpoolP512r1CombWith um) (combVerifySpec um) := by
  refine Verified.of_correct (k := combVerifyLocal um) (fun s hs => ?_) hct
    ⟨fun _ h => combVerify_pre h,?_,?_,⟨combVerifySat um,combVerify_sat um⟩⟩
  · obtain ⟨tr,t,exec,keep,post⟩ := combVerify_ok hC hs
    exact ⟨tr,t,exec,VG.Proof.Ecdsa.Arm.abi_of_saved keep.saved keep.sp,post⟩
  · intro s t _ post
    sig_post [combVerifySpec,Spec.Ecdsa.BrainpoolP512r1.inst,Proof.Ecdsa.verifyContract,
      Proof.Ecdsa.verifySig,Spec.BrainpoolP512r1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,Abi.withConsts]
    rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
    exact post
  · intro s t _ _ pub
    obtain ⟨pub, sy⟩ := pub_consts.mp pub
    sig_pub [Spec.Ecdsa.BrainpoolP512r1.inst,Proof.Ecdsa.verifyContract,
      Proof.Ecdsa.verifySig,Spec.BrainpoolP512r1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr] at pub
    obtain ⟨sp,inputs,h0,h1,h2,h3⟩ := pub
    exact ⟨⟨⟨sp,h0,h1,h2,h3⟩,symAddr_eq_iff.mp (sy (brainpoolp512r1Comb.tsym, brainpoolp512r1CombWords) List.mem_cons_self),
      symAddr_eq_iff.mp (sy ((brainpoolp512r1With um).constSym, (brainpoolp512r1With um).constTbl)
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)))⟩,VPub.of_leak h3 rfl rfl inputs⟩

theorem combVerify_verified (hC : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target verifyBrainpoolP512r1Comb (combVerifySpec false) :=
  combVerifyWith_verified hC false (combVerify_ct hC)

theorem combVerifyU_verified (hC : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target verifyBrainpoolP512r1CombU (combVerifySpec true) :=
  combVerifyWith_verified hC true (combVerifyU_ct hC)

/-- `combVerifySat`'s 100 bytes below `sp + 4` are free. -/
theorem hash_sat (um : Bool) :
    ∃ s, (Spec.Ecdsa.BrainpoolP512r1.inst.verifyHashContract (Arm.abi.withConsts (combVerifyK um)) 96).pre s := by
  cases um <;>
  exact VG.Proof.Ecdsa.Verify.Arm.Hash.hashSat_cons (by decide) (combVerify_sat _) (by decide) (by decide) fun r hr => by
    simp only [combVerifyBase_regs, List.mem_append] at hr
    rw [VG.Proof.BrainpoolP512r1.Arm.comb_words_length] at hr
    simp only [combVerifyBase, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with ((rfl | rfl | rfl) | rfl | rfl) | rfl <;> exact Region.disjoint_of_sep (by decide)

/-- `vg_ecdsa_brainpoolp512r1_verify`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash (`verifyHash_verified_cons`). -/
theorem verifyHash_verified (hC : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false verifyBrainpoolP512r1Comb)
      (Spec.Ecdsa.BrainpoolP512r1.inst.verifyHashContract (Arm.abi.withConsts (combVerifyK false)) 96) :=
  VG.Proof.Ecdsa.Verify.Arm.Hash.verifyHash_verified_cons Proof.Ecdsa.Verify.brainpoolP512r1_len (by decide) (combVerify_verified hC)
    ⟨_, by taint_decide⟩ (hash_sat false)

/-- `vg_ecdsa_brainpoolp512r1_verify_umaal`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash (`verifyHash_verified_cons`). -/
theorem verifyHashU_verified (hC : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false verifyBrainpoolP512r1CombU)
      (Spec.Ecdsa.BrainpoolP512r1.inst.verifyHashContract (Arm.abi.withConsts (combVerifyK true)) 96) :=
  VG.Proof.Ecdsa.Verify.Arm.Hash.verifyHash_verified_cons Proof.Ecdsa.Verify.brainpoolP512r1_len (by decide) (combVerifyU_verified hC)
    ⟨_, by taint_decide⟩ (hash_sat true)

end VG.Proof.Ecdsa.Verify.Arm.BrainpoolP512r1
