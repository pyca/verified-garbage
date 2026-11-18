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
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Front
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.ArmComb
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Main
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
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.CombGenerator
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.CombLit
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
public import VerifiedGarbage.Proof.BrainpoolP512r1.Arm.Comb
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombScan
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
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
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Front
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Main
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP512r1.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.CombGenerator
meta import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
meta import VerifiedGarbage.Proof.BrainpoolP512r1.Arm.Comb
meta import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
meta import VerifiedGarbage.Proof.Weierstrass.Arm.TCombScan
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

abbrev combVerifySpec : Contract isa :=
  Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP512r1.inst (abi.withConsts brainpoolp512r1CombConsts)

def combVerifyPre (um : Bool) (s : State) : Prop :=
  VPre (brainpoolp512r1With um) s (constRegs brainpoolp512r1CombConsts s) ∧ ConstsOk brainpoolp512r1CombConsts 0 s

theorem verify_spec_pre {um : Bool} {s : State}
    (h : (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP512r1.inst abi).pre s) : VPre (brainpoolp512r1With um) s := by
  sig_pre [Spec.Ecdsa.BrainpoolP512r1.inst,Proof.Ecdsa.verifyContract,Proof.Ecdsa.verifySig,
    Spec.BrainpoolP512r1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,Loc.val,State.addr] at h
  obtain ⟨_sp,rd,wr,ps,ds,ss,fp,fd,fs,fc⟩ := h
  exact ⟨rd,wr,ps,ds,ss,fp,fd,fs,fc⟩

theorem combVerify_pre {um : Bool} {s : State} (h : combVerifySpec.pre s) : combVerifyPre um s := by
  have hp : (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP512r1.inst abi).pre (stripConsts brainpoolp512r1CombConsts s) ∧
      ConstsOk brainpoolp512r1CombConsts 0 s := pre_consts.mp h
  have p := verify_spec_pre (um := um) hp.1
  refine ⟨⟨?_,p.wr,p.pk_sc,p.dg_sc,p.sig_sc,p.pk_fit,p.dg_fit,p.sig_fit,p.sc_fit⟩,hp.2⟩
  rw [← List.take_append_drop (s.rd.length-brainpoolp512r1CombConsts.length) s.rd,hp.2.1]
  exact congrArg (fun rs => rs++constRegs brainpoolp512r1CombConsts s) p.rd

/-- Verification's `[u]G` by the comb, as `verifyWith_ok` and `verifyHead_ok` ask. -/
theorem comb_generatorWP (hC : Law Spec.BrainpoolP512r1.curve) {um : Bool} {s₀ : State} (hp : combVerifyPre um s₀) :
    ∀ s, Mid (brainpoolp512r1With um) s₀ (ptr s₀ .r3) s → s.syms = s₀.syms →
      GeneratorWP (brainpoolp512r1With um) (verifyGeneratorBrainpoolP512r1With um) s₀ (ptr s₀ .r3)
        (sv (brainpoolp512r1With um) (ptr s₀ .r3) s U)
        (fun j X Y Z => Rep (brainpoolp512r1With um).C X Y Z
          (Spec.Weierstrass.mul (sv (brainpoolp512r1With um) (ptr s₀ .r3) s U >>> j) (Spec.Weierstrass.G (brainpoolp512r1With um).C)))
        s.syms false := by
  have member : (brainpoolp512r1Comb.tsym,brainpoolp512r1CombWords)∈brainpoolp512r1CombConsts := List.mem_singleton_self _
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
  (verifyArm.pub s t ∧ s.syms brainpoolp512r1Comb.tsym = t.syms brainpoolp512r1Comb.tsym) ∧ VPub (brainpoolp512r1With um) s t

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
    (RelCT.taint (A := taintSym [brainpoolp512r1Comb.tsym]) (c := piece ctPieces 26) (Taint.ofRegs [.r0, .r1, .r2, .r3])
      (fun _ _ h => ⟨Taint.agree_ofRegs (by
        obtain ⟨⟨⟨_, h0, h1, h2, h3⟩, _⟩, _⟩ := h.2.2
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        exacts [h0, h1, h2, h3]), fun n hn => by
        obtain rfl := List.mem_singleton.mp hn
        exact h.2.2.1.2⟩) (by native_taint_decide))
    (LeafCT.check (p := piece ctPieces 27) (by native_taint_decide))

theorem combVerifyU_ct (hC : Law Spec.BrainpoolP512r1.curve) :
    ConstantTime isa (combVerifyPre true) (combVerifyPub true) verifyBrainpoolP512r1CombU :=
  combVerifyWith_ct hC true pubLeavesU
    (RelCT.taint (A := taintSymU [brainpoolp512r1Comb.tsym]) (c := piece ctPiecesU 26) (Taint.ofRegs [.r0, .r1, .r2, .r3])
      (fun _ _ h => ⟨Taint.agree_ofRegs (by
        obtain ⟨⟨⟨_, h0, h1, h2, h3⟩, _⟩, _⟩ := h.2.2
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        exacts [h0, h1, h2, h3]), fun n hn => by
        obtain rfl := List.mem_singleton.mp hn
        exact h.2.2.1.2⟩) (by taint_decide))
    (LeafCT.checkU (p := piece ctPiecesU 27) (by taint_decide))

open VG.Proof.BrainpoolP512r1.Arm in
def combVerifySat : State := {combSatState with
  gpr := fun r => match r with | .r0 => 0x10000 | .r1 => 0x12000 | .r2 => 0x14000 | _ => 0
  rd := [⟨0x10000,129⟩,⟨0x12000,64⟩,⟨0x14000,128⟩,⟨0x100000,606208⟩]
  wr := [⟨0,8192⟩] }

open VG.Proof.BrainpoolP512r1.Arm in
theorem combVerify_sat : combVerifySpec.pre combVerifySat := by
  have held := combSat_held
  generalize eqs : combVerifySat=s
  sig_pre [combVerifySpec,Spec.Ecdsa.BrainpoolP512r1.inst,Proof.Ecdsa.verifyContract,
    Proof.Ecdsa.verifySig,Spec.BrainpoolP512r1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
    Loc.val,State.addr,brainpoolp512r1CombConsts,Abi.withConsts,Abi.constRegions_cons,Abi.constRegions_nil,
    Abi.constsHeld,stackBelow]
  subst s
  rw [comb_words_length]
  rw [comb_words_length] at held
  refine ⟨by decide,by decide,held,by decide,?_,by decide,by decide,?_⟩
  · intro r hr
    change r∈[⟨0,8192⟩] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

def combVerifyLocal (um : Bool) : Contract isa where
  pre := combVerifyPre um
  post := VPost (brainpoolp512r1With um)
  pub := combVerifyPub um

theorem combVerifyWith_verified (hC : Weierstrass.Law Spec.BrainpoolP512r1.curve) (um : Bool)
    (hct : ConstantTime isa (combVerifyPre um) (combVerifyPub um) (verifyBrainpoolP512r1CombWith um)) :
    Verified Arm.target (verifyBrainpoolP512r1CombWith um) combVerifySpec := by
  refine Verified.of_correct (k := combVerifyLocal um) (fun s hs => ?_) hct
    ⟨fun _ h => combVerify_pre h,?_,?_,⟨combVerifySat,combVerify_sat⟩⟩
  · obtain ⟨tr,t,exec,keep,post⟩ := combVerify_ok hC hs
    exact ⟨tr,t,exec,VG.Proof.Ecdsa.Arm.abi_of_saved keep.saved keep.sp,post⟩
  · intro s t _ post
    sig_post [combVerifySpec,Spec.Ecdsa.BrainpoolP512r1.inst,Proof.Ecdsa.verifyContract,
      Proof.Ecdsa.verifySig,Spec.BrainpoolP512r1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,Abi.withConsts]
    rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
    exact post
  · intro s t _ _ pub
    sig_pub [combVerifySpec,Spec.Ecdsa.BrainpoolP512r1.inst,Proof.Ecdsa.verifyContract,
      Proof.Ecdsa.verifySig,Spec.BrainpoolP512r1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,brainpoolp512r1CombConsts,Abi.withConsts] at pub
    obtain ⟨sp,sy,inputs,h0,h1,h2,h3⟩ := pub
    exact ⟨⟨⟨sp,h0,h1,h2,h3⟩,sy⟩,VPub.of_leak h3 rfl rfl inputs⟩

theorem combVerify_verified (hC : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target verifyBrainpoolP512r1Comb combVerifySpec :=
  combVerifyWith_verified hC false (combVerify_ct hC)

theorem combVerifyU_verified (hC : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target verifyBrainpoolP512r1CombU combVerifySpec :=
  combVerifyWith_verified hC true (combVerifyU_ct hC)

/-- `combVerifySat`'s 100 bytes below `sp + 4` are free. -/
theorem hash_sat : ∃ s, (Spec.Ecdsa.BrainpoolP512r1.inst.verifyHashContract (Arm.abi.withConsts brainpoolp512r1CombConsts) 96).pre s :=
  VG.Proof.Ecdsa.Verify.Arm.Hash.hashSat_cons (by decide) combVerify_sat (by decide) (by decide) fun r hr => by
    simp only [combVerifySat, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)

/-- `vg_ecdsa_brainpoolp512r1_verify`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash (`verifyHash_verified_cons`). -/
theorem verifyHash_verified (hC : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false verifyBrainpoolP512r1Comb)
      (Spec.Ecdsa.BrainpoolP512r1.inst.verifyHashContract (Arm.abi.withConsts brainpoolp512r1CombConsts) 96) :=
  VG.Proof.Ecdsa.Verify.Arm.Hash.verifyHash_verified_cons Proof.Ecdsa.Verify.brainpoolP512r1_len (by decide) (combVerify_verified hC)
    ⟨_, by taint_decide⟩ hash_sat

/-- `vg_ecdsa_brainpoolp512r1_verify_umaal`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash (`verifyHash_verified_cons`). -/
theorem verifyHashU_verified (hC : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false verifyBrainpoolP512r1CombU)
      (Spec.Ecdsa.BrainpoolP512r1.inst.verifyHashContract (Arm.abi.withConsts brainpoolp512r1CombConsts) 96) :=
  VG.Proof.Ecdsa.Verify.Arm.Hash.verifyHash_verified_cons Proof.Ecdsa.Verify.brainpoolP512r1_len (by decide) (combVerifyU_verified hC)
    ⟨_, by taint_decide⟩ hash_sat

end VG.Proof.Ecdsa.Verify.Arm.BrainpoolP512r1
