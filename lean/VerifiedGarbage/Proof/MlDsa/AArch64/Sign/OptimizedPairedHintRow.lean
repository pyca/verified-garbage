module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRoots
public import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.PairedConsts
public import VerifiedGarbage.Proof.MlDsa.PairedResponseContract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedMaskSemantic
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedEntry
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSatMemory
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableMemory
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalCheck
public import VerifiedGarbage.Proof.MlDsa.Round.Ones
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckSlot
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSpecFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintPacked
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPassOutput
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckCoverage
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedMaskInvariant
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedAbi
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCoordinates
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckSource
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedRawField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSpecPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemoryCorrect
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Order.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZStoredField
public import VerifiedGarbage.Proof.MlDsa.ResponseHintContract
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Response
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintWord
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLoop
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Data.List.Lemmas
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedResponse
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseK
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintDecompose
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLowState
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZ
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintState
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedHints
import VerifiedGarbage.Proof.MlKem.Arith

/-! ### `MlDsa.AArch64.Optimized.PairedHintCallTiming`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.PairedHVerified`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.ResponseHintSpec`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem highBits_small {g : Nat} (hg : IsG g) (r : Zq) :
    0≤highBits g r ∧ highBits g r<44 := by
  rw [VG.Proof.MlDsa.Round.highBits_eq (mem_of_isG hg)]
  rcases hg with rfl | rfl <;>
    simp only [VG.Proof.MlDsa.Round.hbM,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88,q] <;> omega_using []

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

end

/-! ## From `PairedHAllFields.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/PairedHStoredField.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Optimized.Response

theorem hPass_stored_field {m : Mem} {work challenge secret out aux : Addr} {u e g : Nat}
    (hu : u<8) (he : e<4) (hg : IsG g) (i : Fin 2 × Fin 8) (c : CheckConstants)
    (hgamma : vword c.gamma e=BitVec.ofNat 32 g)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g)
    (flags count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,count⟩
    coeffAt (finalPassData true work out aux c d 8).mem
      (pairPolyPtr out i.1.val) (4*u+32*i.2.val+e)=
      BitVec.ofNat 32 (pairedHintPoly m challenge secret out aux g i.1.val)[4*u+32*i.2.val+e]!.toNat := by
  dsimp only
  have hk : 4*u+32*i.2.val+e<n := by change 4*u+32*i.2.val+e<256; omega
  have hr := rawFinal_field hu hc hs i.1 (Inverse.positiveReduced_is hp.1)
    (Inverse.positiveReduced_is (hp.2 i.1.val i.1.isLt)) i.2 he
  rw [←checkAddr_coeff _ out u i he,
    finalPass_read_written true work out aux c _ (by decide : 8≤8) hu i ho hd]
  simp only [checkOutput,ite_true,laneVector_word _ he]
  rw [firstPass_checkInput_read hu i ho.symm,firstPass_checkInput_read hu i ha.symm,
    checkAddr_coeff _ _ _ _ he,checkAddr_coeff _ _ _ _ he,hgamma]
  have hpj := hy i.1.val i.1.isLt _ hk
  have hhigh : (coeffAt m (pairPolyPtr aux i.1.val) (4*u+32*i.2.val+e)).toInt=
      highBits g (responseHintBase m (pairPolyPtr out i.1.val) (pairPolyPtr aux i.1.val) g (4*u+32*i.2.val+e)) := by
    have hb := highBits_small hg (responseHintBase m (pairPolyPtr out i.1.val) (pairPolyPtr aux i.1.val) g (4*u+32*i.2.val+e))
    have hi := BitVec.toInt_eq_toNat_cond (coeffAt m (pairPolyPtr aux i.1.val) (4*u+32*i.2.val+e))
    omega
  rw [hintWord_raw_field hg _ _ _ _ hr.1 hr.2.1 hpj.1 hhigh,hr.2.2,
    getElem!_pos (pairedHintPoly m challenge secret out aux g i.1.val) (4*u+32*i.2.val+e) hk]
  simp only [pairedHintPoly,Vector.getElem_ofFn]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/PairedHintSpecPre.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

structure HintSpecPre (s : State) : Prop where
  rd : s.rd=[⟨s.gpr .x0,1024⟩,⟨s.gpr .x1,2048⟩,⟨s.gpr .x3,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]
  wr : s.wr=[⟨s.gpr .x2,2048⟩,⟨s.gpr .x4,2176⟩]
  table : PairedTable.Artifact s.mem (s.syms "VG_MLDSA_INV_PAIR")
  tableSep : ∀r∈s.wr,(⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint r
  commonData : (⟨s.gpr .x0,1024⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩
  commonWork : (⟨s.gpr .x0,1024⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  secretData : (⟨s.gpr .x1,2048⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩
  secretWork : (⟨s.gpr .x1,2048⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  auxData : (⟨s.gpr .x3,2048⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩
  dataWork : (⟨s.gpr .x2,2048⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  auxWork : (⟨s.gpr .x3,2048⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  products : pairedProductsReduced s.mem (s.gpr .x0) (s.gpr .x1)
  decomposed : ∀j<2,ResponseDecomposed s.mem (pairPolyPtr (s.gpr .x2) j) (pairPolyPtr (s.gpr .x3) j) ((s.gpr .x5).setWidth 32).toNat
  bound : (s.gpr .x6).setWidth 32=(s.gpr .x5).setWidth 32
  gamma : ((s.gpr .x5).setWidth 32).toNat∈gamma2s
  tableAl : (s.syms "VG_MLDSA_INV_PAIR").toNat%64=0

theorem pairedHint_pre {s : State}
    (h : (pairedHintContract (abi.withConsts pairedConsts)).pre s) : HintSpecPre s := by
  sig_pre [pairedHintContract,pairedHintSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow] at h
  obtain ⟨hdrop,hheld,_,hsep,hal,htake,hwr,hcd,hcw,hsd,hsw,had,haw,hdw,_,_,_,_,_,hprod,hgamma,hbound,hdecomp⟩ := h
  refine ⟨?_,hwr,?_,hsep,hcd,hcw,hsd,hsw,had.symm,haw,hdw,hprod,hdecomp,hbound,hgamma,hal⟩
  · rw [←List.take_append_drop (s.rd.length-1) s.rd,htake,hdrop]
    rfl
  · intro i hi
    refine (hheld i hi).trans ?_
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [PairedTable.expandedWords_length]; exact hi),
      Option.getD_some,getElem!_pos _ _ (by rw [PairedTable.expandedWords_length]; exact hi)]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/PairedHintOrder.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.Spec.MlDsa

def sumN (n : Nat) (f : Nat → Nat) : Nat := ((List.range n).map f).sum

theorem sumN_succ (n : Nat) (f : Nat → Nat) : sumN (n+1) f=sumN n f+f n := by
  simp [sumN,List.range_succ]

theorem sumN_add (n : Nat) (f g : Nat → Nat) :
    sumN n (fun i => f i+g i)=sumN n f+sumN n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumN_succ,ih]; omega_using []

theorem sumN_swap (m n : Nat) (f : Nat → Nat → Nat) :
    sumN m (fun i => sumN n (f i))=sumN n (fun j => sumN m (fun i => f i j)) := by
  induction m with
  | zero => simp [sumN]
  | succ m ih => simp only [sumN_succ,ih,sumN_add]

theorem sumN_append (m n : Nat) (f : Nat → Nat) :
    sumN (m+n) f=sumN m f+sumN n (fun i => f (m+i)) := by
  induction n with
  | zero => simp [sumN]
  | succ n ih => rw [show m+(n+1)=(m+n)+1 by omega_using [],sumN_succ,ih,sumN_succ]; omega_using []

theorem sumN_blocks (m n : Nat) (f : Nat → Nat) :
    sumN m (fun i => sumN n (fun j => f (n*i+j)))=sumN (n*m) f := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [sumN_succ,ih,Nat.mul_succ,sumN_append]

theorem pairedHintSum_order (f : Nat → Nat → Nat) :
    sumN 4 (fun e => sumN 8 (fun u => sumN 2 (fun p => sumN 8 (fun j => f p (4*u+32*j+e)))))=
      sumN 2 (fun p => sumN 256 (f p)) := by
  rw [sumN_swap 4 8]
  conv_lhs => arg 2; ext u; rw [sumN_swap 4 2]
  rw [sumN_swap 8 2]
  apply congrArg (sumN 2)
  funext p
  conv_lhs => arg 2; ext u; rw [sumN_swap 4 8]
  rw [sumN_swap 8 8]
  have he : (fun j => sumN 8 (fun u => sumN 4 (fun e => f p (4*u+32*j+e))))=
      (fun j => sumN 32 (fun k => f p (32*j+k))) := by
    funext j
    rw [←sumN_blocks 8 4 (fun k => f p (32*j+k))]
    congr 1
    funext u
    congr 1
    funext e
    congr 1
    omega_using []
  rw [he,sumN_blocks 8 32]

theorem sumN_four (f : Nat → Nat) : sumN 4 f=f 0+f 1+f 2+f 3 := by
  change f 0+(f 1+(f 2+(f 3+0)))=f 0+f 1+f 2+f 3
  omega_using []

theorem map_finRange_nat (n : Nat) (f : Nat → Nat) :
    (List.finRange n).map (fun i => f i.val)=(List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hi
    simp

theorem allChecks_sum (f : Nat → Nat → Nat) :
    (allChecks.map fun i => f i.1.val i.2.val).sum=sumN 2 (fun p => sumN 8 (f p)) := by
  simp only [allChecks,List.map_flatMap,List.map_map]
  simp only [List.flatMap, List.sum_flatten,List.map_map]
  simp only [Function.comp_def,map_finRange_nat,sumN]
  rw [map_finRange_nat 2 (fun p => ((List.range 8).map (f p)).sum)]

theorem onesTo_sum (h : Vector Bool n) (i : Nat) :
    VG.Proof.MlDsa.Round.onesTo h i=sumN i (fun j => h[j]!.toNat) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [VG.Proof.MlDsa.Round.onesTo_succ,ih,sumN_succ]

theorem hintOnes_pair_sum (f : Nat → Vector Bool n) :
    hintOnes ((List.range 2).map f)=sumN 2 (fun p => sumN 256 (fun k => (f p)[k]!.toNat)) := by
  unfold hintOnes sumN
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  have h := VG.Proof.MlDsa.Round.hintOnes_onesTo (f p)
  rw [onesTo_sum] at h
  simpa only [Function.comp_def,hintOnes,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,n,sumN] using h

end VG.Proof.MlDsa.AArch64.Optimized.Paired
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/PairedCheckCount.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response

/-- The hint counter adds exactly the vector emitted by this check. -/
theorem checkStep_count (raw : BitVec 128) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) {e : Nat} (he : e<4) :
    vword (checkStep true raw out aux c d).count e=vword d.count e+
      vword (checkOutput true raw (d.mem.read out 16) (d.mem.read aux 16) c) e := by
  simp only [checkStep,checkOutput,ite_true,laneVector_word _ he]

def hintSum (v : Values) (out aux : Addr) (c : CheckConstants) (m : Mem) (e : Nat)
    (js : List (Fin 2 × Fin 8)) : BitVec 32 :=
  (js.map fun i => vword (checkOutput true ((v i.1)[i.2.val])
    (m.read (checkAddr out i) 16) (m.read (checkAddr aux i) 16) c) e).sum

/-- The count of a check sequence is the sum of its original-input outputs. -/
theorem checkRun_count (v : Values) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) (js : List (Fin 2 × Fin 8)) (hn : js.Nodup)
    (ha : ∀i∈js,∀j∈js,Mem.Sep (checkAddr aux i) 16 (checkAddr out j) 16)
    {e : Nat} (he : e<4) :
    vword (checkRun true v out aux c d js).count e=vword d.count e+hintSum v out aux c d.mem e js := by
  induction js generalizing d with
  | nil =>
    simp only [checkRun,hintSum,List.map_nil,List.sum_nil]
    exact (BitVec.add_zero _).symm
  | cons i js ih =>
    have hn' := List.nodup_cons.mp hn
    rw [checkRun,ih _ hn'.2 (fun j hj k hk => ha j (List.mem_cons_of_mem _ hj) k (List.mem_cons_of_mem _ hk)),
      checkStep_count _ _ _ _ _ he]
    have hread (j : Fin 2 × Fin 8) (hj : j∈js) :
        checkOutput true ((v j.1)[j.2.val])
          ((checkStep true ((v i.1)[i.2.val]) (checkAddr out i) (checkAddr aux i) c d).mem.read (checkAddr out j) 16)
          ((checkStep true ((v i.1)[i.2.val]) (checkAddr out i) (checkAddr aux i) c d).mem.read (checkAddr aux j) 16) c=
        checkOutput true ((v j.1)[j.2.val]) (d.mem.read (checkAddr out j) 16) (d.mem.read (checkAddr aux j) 16) c := by
      have ho := checkAddr_sep out (i:=j) (j:=i) (by intro h; subst i; exact hn'.1 hj)
      simp only [checkStep]
      rw [Mem.read_write_sep ho (by decide),Mem.read_write_sep (ha j (List.mem_cons_of_mem _ hj) i (by simp)) (by decide)]
    have hs : hintSum v out aux c
        (checkStep true ((v i.1)[i.2.val]) (checkAddr out i) (checkAddr aux i) c d).mem e js=
        hintSum v out aux c d.mem e js := by
      unfold hintSum
      apply congrArg (fun xs : List (BitVec 32) => xs.sum)
      apply List.map_congr_left
      intro j hj
      rw [hread j hj]
    simp only [checkAddr] at hs ⊢
    rw [hs]
    simp only [hintSum,List.map_cons,List.sum_cons,checkAddr,BitVec.add_assoc]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem hPass_all_fields {m : Mem} {work challenge secret out aux : Addr} {g : Nat}
    (hg : IsG g) (c : CheckConstants)
    (hgamma : ∀e<4,vword c.gamma e=BitVec.ofNat 32 g)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g)
    (flags count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,count⟩
    HintIs (finalPassData true work out aux c d 8).mem out 2
      ((List.range 2).map fun j => pairedHintPoly m challenge secret out aux g j) := by
  dsimp only
  refine ⟨by simp,?_⟩
  intro j hj k hk
  obtain ⟨heq,hu,hi,he⟩ := paired_coordinate hk
  have hv := hPass_stored_field hu he hg (⟨j,hj⟩,⟨k/32,hi⟩) c (hgamma _ he)
    hc hs ho ha hd hp hy flags count
  have hv' : coeffAt (finalPassData true work out aux c
      ⟨firstPassMem m work challenge secret 8,flags,count⟩ 8).mem (pairPolyPtr out j) k=
      BitVec.ofNat 32 (pairedHintPoly m challenge secret out aux g j)[k]!.toNat := by
    simpa only [←heq] using hv
  have hpointer : ∀mm:Mem,coeffAt mm out (256*j+k)=coeffAt mm (pairPolyPtr out j) k := by
    intro mm
    simp only [coeffAt,pairPolyPtr,BitVec.add_assoc,←BitVec.ofNat_add]
    rw [show 4*(256*j+k)=1024*j+4*k by omega_arith]
  rw [hpointer,hv']
  have hj' : j<((List.range 2).map fun j => pairedHintPoly m challenge secret out aux g j).length := by simpa using hj
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj',Option.getD_some,
    List.getElem_map,List.getElem_range]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHintFrame.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

theorem pairedCoeff_frame {rs : List Region} {m m' : Mem} {p : Addr}
    (hf : Frame rs m m') (hd : ∀r∈rs,(⟨p,2048⟩:Region).Disjoint r)
    {j k : Nat} (hj : j<2) (hk : k<n) :
    coeffAt m' (pairPolyPtr p j) k=coeffAt m (pairPolyPtr p j) k := by
  apply VG.Proof.MlDsa.Verify.coeffAt_congr _ hk
  apply VG.Proof.MlKem.bytes_frame hf _ (by decide)
  intro r hr
  exact (hd r hr).sub_left (Offset.sub_base _ (by omega_arith))

theorem pairedHintBase_frame {rs : List Region} {m m' : Mem} {out aux : Addr}
    (hf : Frame rs m m') (ho : ∀r∈rs,(⟨out,2048⟩:Region).Disjoint r)
    (ha : ∀r∈rs,(⟨aux,2048⟩:Region).Disjoint r) (g : Nat)
    {j k : Nat} (hj : j<2) (hk : k<n) :
    responseHintBase m' (pairPolyPtr out j) (pairPolyPtr aux j) g k=
      responseHintBase m (pairPolyPtr out j) (pairPolyPtr aux j) g k := by
  rw [responseHintBase,pairedCoeff_frame hf ho hj hk,pairedCoeff_frame hf ha hj hk]
  rfl

structure HintEntryFrame (s : State) (m : Mem) : Prop where
  products : pairedProductsReduced m (s.gpr .x0) (s.gpr .x1)
  decomposed : ∀j<2,ResponseDecomposed m (pairPolyPtr (s.gpr .x2) j)
    (pairPolyPtr (s.gpr .x3) j) ((s.gpr .x5).setWidth 32).toNat
  product : ∀j<2,pairedProduct m (s.gpr .x0) (s.gpr .x1) j=pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j
  hints : ∀j<2,pairedHintPoly m (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) ((s.gpr .x5).setWidth 32).toNat j=
    pairedHintPoly s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) ((s.gpr .x5).setWidth 32).toNat j

theorem hintEntry_frame {s : State} {m : Mem} (h : HintSpecPre s)
    (hf : Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem m) : HintEntryFrame s m := by
  have sep {p : Addr} {len : Nat} (hd : (⟨p,len⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩) :
      ∀r∈[⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩],(⟨p,len⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hd.sub_right (Offset.sub_base _ (by decide))
  have hc := sep h.commonWork
  have hs := sep h.secretWork
  have ho := sep h.dataWork
  have ha := sep h.auxWork
  refine ⟨pairedProductsReduced_frame hf hc hs h.products,?_,fun j hj => pairedProduct_frame hf hc hs hj,?_⟩
  · intro j hj k hk
    rw [pairedCoeff_frame hf ho hj hk,pairedCoeff_frame hf ha hj hk,pairedHintBase_frame hf ho ha _ hj hk]
    exact h.decomposed j hj k hk
  · intro j hj
    apply Vector.ext
    intro k hk
    simp only [pairedHintPoly,Vector.getElem_ofFn]
    rw [pairedProduct_frame hf hc hs hj,pairedHintBase_frame hf ho ha _ hj hk]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHLaneNorm.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem hLane_norm {m : Mem} {work challenge secret out : Addr} {u e B : Nat}
    (hu : u<8) (he : e<4) (i : Fin 2 × Fin 8) (c : CheckConstants)
    (hlower : vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (hp : pairedProductsReduced m challenge secret) :
    passMask true work out c (firstPassMem m work challenge secret 8) u i e=0 ↔
      normZq (pairedProduct m challenge secret i.1.val)[4*u+32*i.2.val+e]!<B := by
  have hr := rawFinal_field hu hc hs i.1 (Inverse.positiveReduced_is hp.1)
    (Inverse.positiveReduced_is (hp.2 i.1.val i.1.isLt)) i.2 he
  simp only [passMask,checkMask,ite_true,hlower,hwidth]
  rw [hMask_zero ⟨hr.1,hr.2.1⟩ hB hB',hr.2.2]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHintFinishSemantic.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response

private theorem fourCount_nat (a b c d : BitVec 32)
    (ha : a.toNat≤128) (hb : b.toNat≤128) (hc : c.toNat≤128) (hd : d.toNat≤128) :
    (a+b+c+d).toNat=a.toNat+b.toNat+c.toNat+d.toNat := by
  simp only [BitVec.toNat_add]
  rw [Nat.mod_eq_of_lt (by omega_arith),Nat.mod_eq_of_lt (by omega_arith),Nat.mod_eq_of_lt (by omega_arith)]

private theorem pack_success (lo : BitVec 32) (P : Prop) [Decidable P] :
    (lo.setWidth 64 ||| ((if P then (1 : BitVec 64) else 0) <<< 32))=
      BitVec.ofNat 64 (lo.toNat+(if P then 4294967296 else 0)) := by
  apply BitVec.eq_of_toNat_eq
  have hlo := lo.isLt
  by_cases hp : P
  · simp only [ite_eq_left hp]
    change (lo.setWidth 64 ||| ((1#32).setWidth 64 <<< 32)).toNat=_
    rw [packedWords_nat]
    simp only [BitVec.toNat_ofNat,show (1#32).toNat=1 by decide,Nat.one_mul]
    exact (Nat.mod_eq_of_lt (by omega_arith)).symm
  · simp only [ite_eq_right hp]
    change (lo.setWidth 64 ||| ((0#32).setWidth 64 <<< 32)).toNat=_
    rw [packedWords_nat]
    simp only [BitVec.toNat_ofNat,show (0#32).toNat=0 by decide,Nat.zero_mul]
    exact (Nat.mod_eq_of_lt (by omega_arith)).symm

theorem hintFinish_packed (counts flags : BitVec 128) (P : Prop) [Decidable P]
    (hb : ∀e<4,(vword counts e).toNat≤128)
    (hf : finishValue flags=if P then 1 else 0) :
    hintFinishValue counts flags=BitVec.ofNat 64
      (sumN 4 (fun e => (vword counts e).toNat)+(if P then 4294967296 else 0)) := by
  have h0 := hb 0 (by decide)
  have h1 := hb 1 (by decide)
  have h2 := hb 2 (by decide)
  have h3 := hb 3 (by decide)
  have hs : sumN 4 (fun e => (vword counts e).toNat)=
      (vword counts 0).toNat+(vword counts 1).toNat+(vword counts 2).toNat+(vword counts 3).toNat := by
    exact sumN_four _
  have hsum : (vword counts 0+vword counts 1+vword counts 2+vword counts 3).toNat=
      sumN 4 (fun e => (vword counts e).toNat) := by
    rw [hs]
    exact fourCount_nat _ _ _ _ h0 h1 h2 h3
  unfold hintFinishValue
  rw [hf,pack_success,hsum]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHOutputField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem hOutput_field {m : Mem} {work challenge secret out aux : Addr} {u e g : Nat}
    (hu : u<8) (he : e<4) (hg : IsG g) (i : Fin 2 × Fin 8) (c : CheckConstants)
    (hgamma : vword c.gamma e=BitVec.ofNat 32 g)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g) :
    let mem := firstPassMem m work challenge secret 8
    (vword (checkOutput true
      ((Inverse.rawFinalValues (readPair mem (work+BitVec.ofNat 64 (16*u)) 128 i.1))[i.2.val])
      (mem.read (checkAddr (out+BitVec.ofNat 64 (16*u)) i) 16)
      (mem.read (checkAddr (aux+BitVec.ofNat 64 (16*u)) i) 16) c) e).toNat=
      (pairedHintPoly m challenge secret out aux g i.1.val)[4*u+32*i.2.val+e]!.toNat := by
  dsimp only
  have h := hPass_stored_field hu he hg i c hgamma hc hs ho ha hd hp hy 0 0
  dsimp only at h
  rw [←checkAddr_coeff _ out u i he,
    finalPass_read_written true work out aux c _ (by decide : 8≤8) hu i ho hd] at h
  rw [h,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
  have hb := (pairedHintPoly m challenge secret out aux g i.1.val)[4*u+32*i.2.val+e]!.toNat_le
  omega_arith

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHintAccess.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

private theorem accessRegion {p : Addr} {len : Nat} {rs : List Region}
    (h : (⟨p,len⟩:Region)∈rs) {off : Nat} (ho : off+16≤len) (hl : len<2^64) :
    InRegions rs (p+BitVec.ofNat 64 off) 16 :=
  ⟨_,h,Offset.contains_base p ho (by omega_arith)⟩

theorem HintSpecPre.access {s : State} (h : HintSpecPre s) : EntryAccess s := by
  constructor
  · intro off ho
    exact accessRegion (by rw [h.rd]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.rd]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.rd]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)

theorem pairedHint_machine {s : State} (h : HintSpecPre s) :
    WP isa (selected .h) s fun t =>
      ∃a u,Arguments s a ∧ Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem a.mem ∧
        Prepared a u ∧ CheckSetup true a u ∧ Keep entryRegs s t ∧
        let d := finalPassData true (s.gpr .x4) (s.gpr .x2) (s.gpr .x3) (constantsAt u) (dataAt u) 8
        t.mem=d.mem ∧ t.gpr .x0=dataReturn .h d := by
  have htw := h.tableSep (⟨s.gpr .x4,2176⟩:Region) (by rw [h.wr]; simp)
  have htd := h.tableSep (⟨s.gpr .x2,2048⟩:Region) (by rw [h.wr]; simp)
  exact selected_check_ok true h.access h.table.words
    (htw.sub_right (Region.sub_prefix (by decide)))
    (htw.sub_right (Offset.sub_base _ (by decide))) htd
    (h.dataWork.symm.sub_left (Offset.sub_base _ (by decide))) (by
      intro _ off ho
      exact accessRegion (by rw [h.rd]; simp) ho (by decide))

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHintContractTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedHint_public {s t : State}
    (h : (pairedHintContract (abi.withConsts pairedConsts)).pub s t) :
    Taint.AgreeS ["VG_MLDSA_INV_PAIR"] (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4]) s t := by
  sig_pub [pairedHintContract,pairedHintSig,abi,argRegs,Abi.withConsts,pairedConsts_eq] at h
  obtain ⟨hsp,htable,h0,h1,h2,h3,h4,_hgamma⟩ := h
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hsp ?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl <;> with_reducible assumption
  · intro name hn
    have he : name="VG_MLDSA_INV_PAIR" := by simpa only [List.mem_singleton] using hn
    subst name
    exact htable

theorem pairedHint_contract_ct : ConstantTime isa
    (pairedHintContract (abi.withConsts pairedConsts)).pre
    (pairedHintContract (abi.withConsts pairedConsts)).pub (selected .h) := by
  intro s t tr1 tr2 s' t' _ _ hp he hf
  exact h_ct s t tr1 tr2 s' t' trivial trivial (pairedHint_public hp) he hf

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedPassCount.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def passHintSum (work out aux : Addr) (c : CheckConstants) (m : Mem) (e : Nat) : Nat → BitVec 32
  | 0 => 0
  | n+1 => passHintSum work out aux c m e n+
      hintSum (fun p => Inverse.rawFinalValues (readPair m (work+BitVec.ofNat 64 (16*n)) 128 p))
        (out+BitVec.ofNat 64 (16*n)) (aux+BitVec.ofNat 64 (16*n)) c m e allChecks

/-- The final counter includes exactly the original-input hint outputs from
all completed slices, with no dependence on earlier output writes. -/
theorem finalPass_count (work out aux : Addr) (c : CheckConstants) (d : CheckData)
    {n : Nat} (hn : n≤8)
    (hw : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩) {e : Nat} (he : e<4) :
    vword (finalPassData true work out aux c d n).count e=
      vword d.count e+passHintSum work out aux c d.mem e n := by
  induction n with
  | zero => exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [finalPass_step true work out aux c d (by omega_arith) hw,
      checkRun_count _ _ _ _ _ _ allChecks_nodup
        (fun i _ j _ => ha.sep (checkAddr_contains aux (by omega_arith) i) (checkAddr_contains out (by omega_arith) j)) he,
      ih (by omega_arith)]
    have hs : hintSum
        (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*n)) 128 p))
        (out+BitVec.ofNat 64 (16*n)) (aux+BitVec.ofNat 64 (16*n)) c
        (finalPassData true work out aux c d n).mem e allChecks=
      hintSum
        (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*n)) 128 p))
        (out+BitVec.ofNat 64 (16*n)) (aux+BitVec.ofNat 64 (16*n)) c d.mem e allChecks := by
      unfold hintSum
      apply congrArg (fun xs : List (BitVec 32) => xs.sum)
      apply List.map_congr_left
      intro i _
      rw [finalPass_read_future true work out aux c d (Nat.le_refl n) (by omega_arith) i,
        finalPass_read_aux true work out aux c d (by omega_arith) (by omega_arith) i ha]
    rw [hs,passHintSum]
    exact BitVec.add_assoc _ _ _

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHintPreIntro.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedHint_pre_intro {s : State} (h : HintSpecPre s)
    (held : ∀i<512,s.mem.readW (s.syms "VG_MLDSA_INV_PAIR"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (fitTable : (s.syms "VG_MLDSA_INV_PAIR").toNat+4096≤2^64)
    (fit0 : (s.gpr .x0).toNat+1024≤2^64) (fit1 : (s.gpr .x1).toNat+2048≤2^64)
    (fit2 : (s.gpr .x2).toNat+2048≤2^64)
    (fit3 : (s.gpr .x3).toNat+2048≤2^64)
    (fit4 : (s.gpr .x4).toNat+2176≤2^64) :
    (pairedHintContract (abi.withConsts pairedConsts)).pre s := by
  sig_pre [pairedHintContract,pairedHintSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow]
  exact ⟨by rw [h.rd]; rfl,held,fitTable,h.tableSep,h.tableAl,by rw [h.rd]; rfl,h.wr,
    h.commonData,h.commonWork,h.secretData,h.secretWork,
    h.auxData.symm,h.dataWork,h.auxWork,fit0,fit1,fit2,fit3,fit4,h.products,h.gamma,h.bound,h.decomposed⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHNormComplete.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

theorem hPass_norm_complete {m : Mem} {work challenge secret out aux : Addr} {B : Nat}
    (c : CheckConstants)
    (hlower : ∀e<4,vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : ∀e<4,vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret) (count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,0,count⟩
    (∀e<4,vword (finalPassData true work out aux c d 8).flags e=0) ↔
      normRq ((List.range 2).map fun j => pairedProduct m challenge secret j)<B := by
  dsimp only
  rw [paired_norm_iff _ (by omega_arith),←checkCoverage]
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  rw [finalPass_flag_zero_iff true work out aux c _ (by decide : 8≤8) ho he]
  have hz : vword (0 : BitVec 128) e=0 := by simp [vword]
  simp only [hz,true_and]
  apply forall_congr'
  intro u
  apply forall_congr'
  intro hu
  apply forall_congr'
  intro i
  exact hLane_norm hu he i c (hlower e he) (hwidth e he) hB hB' hc hs hp

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedCountBound.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response

theorem checkOutput_bit (raw low high : BitVec 128) (c : CheckConstants)
    {e : Nat} (he : e<4) : (vword (checkOutput true raw low high c) e).toNat≤1 := by
  simp only [checkOutput,ite_true,laneVector_word _ he]
  exact hintWord_bit _ _ _

/-- A bounded list of bits has an exact natural sum in its 32-bit accumulator. -/
theorem bitSum_value (xs : List (BitVec 32)) (hl : xs.length≤128)
    (hb : ∀x∈xs,x.toNat≤1) :
    xs.sum.toNat=(xs.map BitVec.toNat).sum ∧ xs.sum.toNat≤xs.length := by
  induction xs with
  | nil => exact ⟨rfl,Nat.le_refl _⟩
  | cons x xs ih =>
    have hx := hb x (by simp)
    have ht := ih (by simp only [List.length_cons] at hl; omega_arith)
      (fun y hy => hb y (List.mem_cons_of_mem _ hy))
    have hn : x.toNat+xs.sum.toNat<2^32 := by simp only [List.length_cons] at hl; omega_arith
    simp only [List.sum_cons,List.map_cons,BitVec.toNat_add,Nat.mod_eq_of_lt hn]
    exact ⟨by rw [ht.1],by simp only [List.length_cons]; omega_arith⟩

theorem hintSum_bound (v : Values) (out aux : Addr) (c : CheckConstants) (m : Mem)
    {e : Nat} (he : e<4) : (hintSum v out aux c m e allChecks).toNat≤16 := by
  unfold hintSum
  have h := bitSum_value
    (allChecks.map fun i => vword (checkOutput true ((v i.1)[i.2.val])
      (m.read (checkAddr out i) 16) (m.read (checkAddr aux i) 16) c) e)
    (by rw [List.length_map]; decide)
    (by intro x hx; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact checkOutput_bit _ _ _ _ he)
  exact h.2

/-- Eight paired slices accumulate at most 128 hints in each SIMD lane. -/
theorem passHintSum_bound (work out aux : Addr) (c : CheckConstants) (m : Mem)
    {e n : Nat} (he : e<4) (hn : n≤8) :
    (passHintSum work out aux c m e n).toNat≤16*n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have hp := ih (by omega_arith)
    have hs := hintSum_bound
      (fun p => Inverse.rawFinalValues (readPair m (work+BitVec.ofNat 64 (16*n)) 128 p))
      (out+BitVec.ofNat 64 (16*n)) (aux+BitVec.ofNat 64 (16*n)) c m he
    rw [passHintSum,BitVec.toNat_add,Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHintSat.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

def hintSatWith (m : Mem) : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 8192 else if r=.x2 then 12288
    else if r=.x3 then 16384 else if r=.x4 then 20480 else if r=.x5 then 95232
    else if r=.x6 then 95232 else 0
  sp := 131072
  syms _ := 65536
  mem := m
  rd := [⟨4096,1024⟩,⟨8192,2048⟩,⟨16384,2048⟩,⟨65536,4096⟩]
  wr := [⟨12288,2048⟩,⟨20480,2176⟩]

theorem hintSatWith_pre (m : Mem)
    (held : ∀i<512,m.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (hprod : pairedProductsReduced m 4096 8192)
    (hdata : ∀j<2,ResponseDecomposed m (pairPolyPtr 12288 j) (pairPolyPtr 16384 j) 95232) :
    (pairedHintContract (abi.withConsts pairedConsts)).pre (hintSatWith m) := by
  apply pairedHint_pre_intro (s:=hintSatWith m) ?_ held (by dsimp only [hintSatWith]; decide) (by dsimp only [hintSatWith]; decide) (by dsimp only [hintSatWith]; decide) (by dsimp only [hintSatWith]; decide) (by dsimp only [hintSatWith]; decide) (by dsimp only [hintSatWith]; decide)
  refine ⟨rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,hprod,hdata,rfl,by dsimp only [hintSatWith]; decide,by dsimp only [hintSatWith]; try decide⟩
  · intro i hi
    refine (held i hi).trans ?_
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [PairedTable.expandedWords_length]; exact hi),
      Option.getD_some,getElem!_pos _ _ (by rw [PairedTable.expandedWords_length]; exact hi)]
  · intro r hr
    change r∈[⟨12288,2048⟩,⟨20480,2176⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact Region.disjoint_of_sep (by dsimp only [hintSatWith]; decide)
  all_goals exact Region.disjoint_of_sep (by dsimp only [hintSatWith]; decide)

def hintSat : State := hintSatWith pairedSatMem

theorem pairedHint_sat : (pairedHintContract (abi.withConsts pairedConsts)).pre hintSat := by
  apply hintSatWith_pre pairedSatMem pairedSat_held
  · refine ⟨pairedSat_positive (by decide : 4096≤32768),?_⟩
    intro j hj
    change PositiveReduced pairedSatMem (8192+BitVec.ofNat 64 (1024*j))
    rw [show (8192:BitVec 64)=BitVec.ofNat 64 8192 by rfl,←BitVec.ofNat_add]
    exact pairedSat_positive (by omega_arith)
  · intro j hj i hi
    have hl : coeffAt pairedSatMem (pairPolyPtr 12288 j) i=0 := by
      change coeffAt pairedSatMem (12288+BitVec.ofNat 64 (1024*j)) i=0
      rw [show (12288:BitVec 64)=BitVec.ofNat 64 12288 by rfl,←BitVec.ofNat_add]
      exact pairedSat_coeff_zero (by omega_arith) hi
    have hh : coeffAt pairedSatMem (pairPolyPtr 16384 j) i=0 := by
      change coeffAt pairedSatMem (16384+BitVec.ofNat 64 (1024*j)) i=0
      rw [show (16384:BitVec 64)=BitVec.ofNat 64 16384 by rfl,←BitVec.ofNat_add]
      exact pairedSat_coeff_zero (by omega_arith) hi
    simp only [responseHintBase,hl,hh]
    decide

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHCountField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem hintSum_field {m : Mem} {work challenge secret out aux : Addr} {u e g : Nat}
    (hu : u<8) (he : e<4) (hg : IsG g) (c : CheckConstants)
    (hgamma : vword c.gamma e=BitVec.ofNat 32 g)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g) :
    let mem := firstPassMem m work challenge secret 8
    (hintSum (fun p => Inverse.rawFinalValues (readPair mem (work+BitVec.ofNat 64 (16*u)) 128 p))
      (out+BitVec.ofNat 64 (16*u)) (aux+BitVec.ofNat 64 (16*u)) c mem e allChecks).toNat=
      sumN 2 (fun p => sumN 8 (fun j => (pairedHintPoly m challenge secret out aux g p)[4*u+32*j+e]!.toNat)) := by
  dsimp only
  unfold hintSum
  rw [(bitSum_value _ (by rw [List.length_map]; decide)
    (by intro x hx; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact checkOutput_bit _ _ _ _ he)).1]
  simp only [List.map_map,Function.comp_def]
  have hm := List.map_congr_left (l:=allChecks) (fun i _ =>
    hOutput_field hu he hg i c hgamma hc hs ho ha hd hp hy)
  rw [hm]
  exact allChecks_sum (fun p j => (pairedHintPoly m challenge secret out aux g p)[4*u+32*j+e]!.toNat)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHCountPass.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem passHintSum_field {m : Mem} {work challenge secret out aux : Addr} {e g n : Nat}
    (hn : n≤8) (he : e<4) (hg : IsG g) (c : CheckConstants)
    (hgamma : vword c.gamma e=BitVec.ofNat 32 g)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g) :
    (passHintSum work out aux c (firstPassMem m work challenge secret 8) e n).toNat=
      sumN n (fun u => sumN 2 (fun p => sumN 8
        (fun j => (pairedHintPoly m challenge secret out aux g p)[4*u+32*j+e]!.toNat))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpbound := passHintSum_bound work out aux c (firstPassMem m work challenge secret 8) he (by omega_arith : n≤8)
    have hsbound := hintSum_bound
      (fun p => Inverse.rawFinalValues (readPair (firstPassMem m work challenge secret 8)
        (work+BitVec.ofNat 64 (16*n)) 128 p))
      (out+BitVec.ofNat 64 (16*n)) (aux+BitVec.ofNat 64 (16*n)) c
      (firstPassMem m work challenge secret 8) he
    rw [passHintSum,BitVec.toNat_add,Nat.mod_eq_of_lt (by omega_arith),ih (by omega_arith),sumN_succ]
    rw [hintSum_field (by omega_arith) he hg c hgamma hc hs ho ha hd hp hy]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHCountComplete.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem hPass_count_complete {m : Mem} {work challenge secret out aux : Addr} {g : Nat}
    (hg : IsG g) (c : CheckConstants)
    (hgamma : ∀e<4,vword c.gamma e=BitVec.ofNat 32 g)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g)
    (flags : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,0⟩
    sumN 4 (fun e => (vword (finalPassData true work out aux c d 8).count e).toNat)=
      hintOnes ((List.range 2).map fun j => pairedHintPoly m challenge secret out aux g j) := by
  dsimp only
  rw [hintOnes_pair_sum,←pairedHintSum_order]
  unfold sumN at *
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  have he' := List.mem_range.mp he
  rw [finalPass_count work out aux c _ (by decide : 8≤8) ho hd he']
  have hz : vword (0 : BitVec 128) e=0 := by simp [vword]
  rw [hz]
  change (0+(passHintSum work out aux c (firstPassMem m work challenge secret 8) e 8)).toNat=_
  have hv := passHintSum_field (n:=8) (by decide : 8≤8) he' hg c (hgamma e he') hc hs ho ha hd hp hy
  have hzadd := congrArg BitVec.toNat (BitVec.zero_add (passHintSum work out aux c (firstPassMem m work challenge secret 8) e 8))
  exact hzadd.trans hv

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHReturnSemantic.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Optimized.Response

theorem hPass_return {m : Mem} {work challenge secret out aux : Addr} {g : Nat}
    (hg : IsG g) (c : CheckConstants)
    (hgamma : ∀e<4,vword c.gamma e=BitVec.ofNat 32 g)
    (hlower : ∀e<4,vword c.lower e=BitVec.ofNat 32 (g-1))
    (hwidth : ∀e<4,vword c.width e=BitVec.ofNat 32 (2*g-1))
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,0,0⟩
    let result := finalPassData true work out aux c d 8
    hintFinishValue result.count result.flags=BitVec.ofNat 64
      (hintOnes ((List.range 2).map fun j => pairedHintPoly m challenge secret out aux g j)+
        if normRq ((List.range 2).map fun j => pairedProduct m challenge secret j)<g then 4294967296 else 0) := by
  dsimp only
  have hgb : 1≤g ∧ g≤524288 := by rcases hg with rfl|rfl <;> decide
  have hnorm := hPass_norm_complete (aux:=aux) c hlower hwidth hgb.1 hgb.2 hc hs ho hp 0
  dsimp only at hnorm
  have hfinish : finishValue (finalPassData true work out aux c
      ⟨firstPassMem m work challenge secret 8,0,0⟩ 8).flags=
      if normRq ((List.range 2).map fun j => pairedProduct m challenge secret j)<g then 1 else 0 := by
    rw [finishValue_accept _ (finalPass_masks _ _ _ _ _ _ _ (by intro e he; left; simp [vword])),hnorm]
    split <;> simp_all only
  have hbound : ∀e<4,(vword (finalPassData true work out aux c
      ⟨firstPassMem m work challenge secret 8,0,0⟩ 8).count e).toNat≤128 := by
    intro e he
    rw [finalPass_count work out aux c _ (by decide : 8≤8) ho hd he]
    have hz : vword (0 : BitVec 128) e=0 := by simp [vword]
    rw [hz]
    have hb := passHintSum_bound work out aux c (firstPassMem m work challenge secret 8) he (by decide : 8≤8)
    exact (congrArg BitVec.toNat (BitVec.zero_add _)).trans_le hb
  rw [hintFinish_packed _ _ _ hbound hfinish]
  have hcount := hPass_count_complete hg c hgamma hc hs ho ha hd hp hy 0
  dsimp only at hcount
  rw [hcount]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHFunctional.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

structure HResult (s t : State) : Prop where
  keep : Keep entryRegs s t
  fields : HintIs t.mem (s.gpr .x2) 2 ((List.range 2).map fun j =>
    pairedHintPoly s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) (Round.arg32 s .x5) j)
  ret : t.gpr .x0=BitVec.ofNat 64
    (hintOnes ((List.range 2).map fun j => pairedHintPoly s.mem (s.gpr .x0) (s.gpr .x1)
      (s.gpr .x2) (s.gpr .x3) (Round.arg32 s .x5) j)+
      if normRq ((List.range 2).map fun j => pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j)<Round.arg32 s .x5
      then 4294967296 else 0)

theorem pairedHint_functional {s : State} (h : HintSpecPre s) :
    WP isa (selected .h) s (HResult s) := by
  refine WP.mono (pairedHint_machine h) fun t ⟨a,u,ha,hf,hp,hl,ht,hmem,hret⟩ => ?_
  have hg : Round.IsG (Round.arg32 s .x5) := by
    simpa [or_comm,gamma2s,Round.IsG,VG.Impl.MlDsa.AArch64.Round.g32,
      VG.Impl.MlDsa.AArch64.Round.g88,Round.arg32] using h.gamma
  have hgb : 1≤Round.arg32 s .x5 := by rcases hg with hv|hv <;> rw [hv] <;> decide
  have hframe := hintEntry_frame h hf
  have hdata : dataAt u=⟨firstPassMem a.mem (s.gpr .x4) (s.gpr .x0) (s.gpr .x1) 8,0,0⟩ := by
    unfold dataAt
    rw [hp.mem,ha.work,ha.common,ha.secret,hl.flags,hl.count rfl]
  have hgamma : ∀e<4,vword (constantsAt u).gamma e=BitVec.ofNat 32 (Round.arg32 s .x5) := by
    intro e he
    change vword (u.v .v11) e=_
    rw [hl.gamma rfl e he,ha.gamma]
    simp only [Round.arg32,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have hlower : ∀e<4,vword (constantsAt u).lower e=BitVec.ofNat 32 (Round.arg32 s .x5-1) := by
    intro e he
    change vword (u.v .v9) e=_
    rw [hl.lower e he,ha.bound,h.bound]
    exact bound_sub_one _ hgb
  have hwidth : ∀e<4,vword (constantsAt u).width e=BitVec.ofNat 32 (2*Round.arg32 s .x5-1) := by
    intro e he
    change vword (u.v .v10) e=_
    rw [hl.width e he,ha.bound,h.bound]
    exact bound_width _ hgb
  have hc := h.commonWork.sub_right (Region.sub_prefix (by decide : 2048≤2176))
  have hs := h.secretWork.sub_right (Region.sub_prefix (by decide : 2048≤2176))
  have ho := h.dataWork.symm.sub_left (Region.sub_prefix (by decide : 2048≤2176))
  have hx := h.auxWork.symm.sub_left (Region.sub_prefix (by decide : 2048≤2176))
  have hfields := hPass_all_fields hg (constantsAt u) hgamma hc hs ho hx h.auxData hframe.products hframe.decomposed 0 0
  have hvalue := hPass_return hg (constantsAt u) hgamma hlower hwidth hc hs ho hx h.auxData hframe.products hframe.decomposed
  dsimp only at hfields hvalue
  have hhints : ((List.range 2).map fun j => pairedHintPoly a.mem (s.gpr .x0) (s.gpr .x1)
      (s.gpr .x2) (s.gpr .x3) (Round.arg32 s .x5) j)=
      ((List.range 2).map fun j => pairedHintPoly s.mem (s.gpr .x0) (s.gpr .x1)
      (s.gpr .x2) (s.gpr .x3) (Round.arg32 s .x5) j) := by
    apply List.map_congr_left
    intro j hj
    exact hframe.hints j (List.mem_range.mp hj)
  have hproducts : ((List.range 2).map fun j => pairedProduct a.mem (s.gpr .x0) (s.gpr .x1) j)=
      ((List.range 2).map fun j => pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j) := by
    apply List.map_congr_left
    intro j hj
    exact hframe.product j (List.mem_range.mp hj)
  rw [hdata] at hmem hret
  refine ⟨ht,?_,?_⟩
  · rw [hmem,←hhints]
    exact hfields
  · rw [hret]
    change Response.hintFinishValue _ _=_
    rw [hvalue,hhints,hproducts]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedHint_post {s t : State} (h : HResult s t) :
    (pairedHintContract (abi.withConsts pairedConsts)).post s t := by
  sig_post [pairedHintContract,pairedHintSig,abi,argRegs,Abi.withConsts,pairedConsts_eq]
  exact ⟨h.fields,h.ret⟩

theorem pairedHint_correct (s : State)
    (h : (pairedHintContract (abi.withConsts pairedConsts)).pre s) :
    ∃tr t,Exec isa (selected .h) s tr t ∧ abiPreserved s t ∧
      (pairedHintContract (abi.withConsts pairedConsts)).post s t := by
  obtain ⟨tr,t,he,hr⟩ := pairedHint_functional (pairedHint_pre h)
  exact ⟨tr,t,he,entryKeep_abi hr.keep,pairedHint_post hr⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

/-- Exact paired hint generation, all-path hint outputs/counts and strict
product norm, with the original ABI and public-input timing policy. -/
theorem pairedHint_verified : Verified target (selected .h)
    (pairedHintContract (abi.withConsts pairedConsts)) :=
  ⟨pairedHint_correct,pairedHint_contract_ct,⟨hintSat,pairedHint_sat⟩⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

end


/-! ## From `PairedHintCall.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedHint_callee (S : Nat) :
    CalleeOk S (selected .h) (pairedHintContract (abi.withConsts pairedConsts)) := by
  refine CalleeOk.of_ct pairedHint_verified.1 pairedHint_verified.2.1 (by lit_decide) (fun _ _ h => h) ?_
  change 0≤S
  exact Nat.zero_le _

abbrev pairedHintArgs (c secret y high work : Ptr) (gamma : Nat) : List (Reg × Arg) :=
  [(.x0,.ptr c),(.x1,.ptr secret),(.x2,.ptr y),(.x3,.ptr high),(.x4,.ptr work),
    (.x5,.imm gamma),(.x6,.imm gamma)]

structure PairedHintReady (c secret y high work : Ptr) (gamma : Nat) (s : State) : Prop where
  cFit : (pa s c).toNat+1024≤2^64
  secretFit : (pa s secret).toNat+2048≤2^64
  yFit : (pa s y).toNat+2048≤2^64
  highFit : (pa s high).toNat+2048≤2^64
  workFit : (pa s work).toNat+2176≤2^64
  held : ∀i<512,s.mem.readW (s.syms "VG_MLDSA_INV_PAIR"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0
  tableFit : (s.syms "VG_MLDSA_INV_PAIR").toNat+4096≤2^64
  tableApart : ∀r∈[⟨pa s y,2048⟩,⟨pa s work,2176⟩],
    (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint r
  cY : (⟨pa s c,1024⟩:Region).Disjoint ⟨pa s y,2048⟩
  cWork : (⟨pa s c,1024⟩:Region).Disjoint ⟨pa s work,2176⟩
  secretY : (⟨pa s secret,2048⟩:Region).Disjoint ⟨pa s y,2048⟩
  secretWork : (⟨pa s secret,2048⟩:Region).Disjoint ⟨pa s work,2176⟩
  yWork : (⟨pa s y,2048⟩:Region).Disjoint ⟨pa s work,2176⟩
  yHigh : (⟨pa s y,2048⟩:Region).Disjoint ⟨pa s high,2048⟩
  highWork : (⟨pa s high,2048⟩:Region).Disjoint ⟨pa s work,2176⟩
  products : pairedProductsReduced s.mem (pa s c) (pa s secret)
  gammaOk : gamma∈gamma2s
  data : ∀j<2,ResponseDecomposed s.mem (pairPolyPtr (pa s y) j) (pairPolyPtr (pa s high) j) gamma
  readable : Covers ([⟨pa s c,1024⟩,⟨pa s secret,2048⟩,⟨pa s high,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]++
    [⟨pa s y,2048⟩,⟨pa s work,2176⟩]) (s.rd++s.wr)
  writable : Covers [⟨pa s y,2048⟩,⟨pa s work,2176⟩] s.wr
  tableAligned : (s.syms "VG_MLDSA_INV_PAIR").toNat%64=0

theorem pairedHintAt_pre {s s1 : State} {c secret y high work : Ptr} {gamma : Nat}
    (h : PairedHintReady c secret y high work gamma s)
    (h1 : Args (pairedHintArgs c secret y high work gamma) s s1) (hy : s1.syms=s.syms) :
    (pairedHintContract (abi.withConsts pairedConsts)).pre
      (s1.callEntry.withRegions [⟨pa s c,1024⟩,⟨pa s secret,2048⟩,⟨pa s high,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]
        [⟨pa s y,2048⟩,⟨pa s work,2176⟩]) := by
  have hg : s1.gpr .x5=BitVec.ofNat 64 gamma := h1.imm (by simp [pairedHintArgs])
  have hb : s1.gpr .x6=BitVec.ofNat 64 gamma := h1.imm (by simp [pairedHintArgs])
  have hg32 := imm32 (v:=gamma) (by have hg := VG.Proof.MlDsa.AArch64.Round.isG_of_mem h.gammaOk; rcases hg with rfl|rfl <;> decide)
  sig_pre [pairedHintContract,pairedHintSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow]
  simp only [hy,Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.r4 h1,Args.mem h1,Arg.val,hg,hb,hg32]
  exact ⟨True.intro,h.held,h.tableFit,h.tableApart _ (by simp),h.tableApart _ (by simp),h.tableAligned,True.intro,True.intro,h.cY,h.cWork,h.secretY,h.secretWork,
    h.yHigh,h.yWork,h.highWork,h.cFit,h.secretFit,h.yFit,h.highFit,h.workFit,h.products,h.gammaOk,True.intro,h.data⟩

theorem pairedHintArgs_ok {c secret y high work : Ptr} {gamma : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (hy : (Arg.ptr y).Ok)
    (hu : (Arg.ptr high).Ok) (hw : (Arg.ptr work).Ok) :
    ∀x∈pairedHintArgs c secret y high work gamma,x.2.Ok ∧ x.1∈argRegs := by
  simp only [pairedHintArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨hc,by simp⟩
  · exact ⟨hs,by simp⟩
  · exact ⟨hy,by simp⟩
  · exact ⟨hu,by simp⟩
  · exact ⟨hw,by simp⟩
  · exact ⟨True.intro,by simp⟩
  · exact ⟨True.intro,by simp⟩

theorem pairedHintAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State}
    {c secret y high work : Ptr} {gamma : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (hy : (Arg.ptr y).Ok)
    (hu : (Arg.ptr high).Ok) (hw : (Arg.ptr work).Ok)
    (h : PairedHintReady c secret y high work gamma s) :
    WP isa (callAt nm (selected .h) (pairedHintArgs c secret y high work gamma)) s fun t =>
      Post S s t [⟨pa s y,2048⟩,⟨pa s work,2176⟩] ∧
      HintIs t.mem (pa s y) 2 ((List.range 2).map fun j => pairedHintPoly s.mem (pa s c) (pa s secret) (pa s y) (pa s high) gamma j) ∧
      t.gpr .x0=BitVec.ofNat 64 (hintOnes ((List.range 2).map fun j => pairedHintPoly s.mem (pa s c) (pa s secret) (pa s y) (pa s high) gamma j)+
        if normRq ((List.range 2).map fun j => pairedProduct s.mem (pa s c) (pa s secret) j)<gamma then 4294967296 else 0) := by
  refine WP.mono (callAtSyms_ok hS (pairedHint_callee S) (pairedHintArgs_ok hc hs hy hu hw) (by simp)
    (fun s1 h1 hy => pairedHintAt_pre h h1 hy) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  have hg : s1.gpr .x5=BitVec.ofNat 64 gamma := h1.imm (by simp [pairedHintArgs])
  have hg32 := imm32 (v:=gamma) (by have hg := VG.Proof.MlDsa.AArch64.Round.isG_of_mem h.gammaOk; rcases hg with rfl|rfl <;> decide)
  sig_post [pairedHintContract,pairedHintSig,abi,argRegs,pairedConsts_eq,Abi.withConsts] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.mem h1,hg,hg32] at hq
  exact hq

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHintCallTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedHintAt_tr {S : Nat} {nm : String} {c secret out high work : Ptr} {gamma : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (ho : (Arg.ptr out).Ok)
    (hu : (Arg.ptr high).Ok) (hw : (Arg.ptr work).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x y,Q x y → PairedHintReady c secret out high work gamma x ∧ PairedHintReady c secret out high work gamma y ∧
      pa x c=pa y c ∧ pa x secret=pa y secret ∧ pa x out=pa y out ∧ pa x high=pa y high ∧
      pa x work=pa y work ∧ x.sp=y.sp ∧ x.syms "VG_MLDSA_INV_PAIR"=y.syms "VG_MLDSA_INV_PAIR") :
    RelCT isa Q (callAt nm (selected .h) (pairedHintArgs c secret out high work gamma)) fun _ _ => True := by
  refine callAtSyms_tr (pairedHint_callee S) (pairedHintArgs_ok hc hs ho hu hw) (by simp)
    fun x y x1 y1 hp h1 h2 hy1 hy2 => ?_
  obtain ⟨rx,ry,ec,es,eo,eu,ew,esp,et⟩ := hQ x y hp
  refine ⟨[⟨pa x c,1024⟩,⟨pa x secret,2048⟩,⟨pa x high,2048⟩,⟨x.syms "VG_MLDSA_INV_PAIR",4096⟩],
    [⟨pa x out,2048⟩,⟨pa x work,2176⟩],pairedHintAt_pre rx h1 hy1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [ec,es,eo,eu,ew,et]
    exact pairedHintAt_pre ry h2 hy2
  · sig_pub [pairedHintContract,pairedHintSig,abi,argRegs,Abi.withConsts,pairedConsts_eq]
    rw [hy1,hy2,Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,
      Args.r3 h1,Args.r3 h2,Args.r4 h1,Args.r4 h2,Args.sp h1,Args.sp h2]
    have h5x : x1.gpr .x5=BitVec.ofNat 64 gamma := h1.imm (by simp [pairedHintArgs])
    have h5y : y1.gpr .x5=BitVec.ofNat 64 gamma := h2.imm (by simp [pairedHintArgs])
    rw [h5x,h5y]
    exact ⟨esp,et,ec,es,eo,eu,ew,rfl⟩
  · rw [ec,es,eo,eu,ew,et]; exact ry.readable
  · rw [eo,ew]; exact ry.writable

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

end

/-! ### `MlDsa.AArch64.Sign.OptimizedHintRow`, which only this module used -/

section

/-! ## From `OptimizedHintCheck.lean` -/

@[expose] public section

/-! ## From `OptimizedHintRow.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc callAt)
open VG.Proof.MlDsa.AArch64.Optimized

/-- The response hint is unchanged when low/high decomposition is kept separately. -/
theorem hintRow_value (p : Params) (σ : State) (κ i : Nat) :
    Vector.zipWith (fun ci fi=>makeHint p.γ₂ (-ci) (fi+ci))
      (CT0v p σ κ i) (W'v p σ κ i) = Hv p σ κ i := by
  apply Vector.ext
  intro j hj
  simp only [Hv,VG.Proof.MlDsa.Sign.hF,VG.Proof.MlDsa.Sign.w''F,
    neg,add,Vector.getElem_zipWith,Vector.getElem_map]

end VG.Proof.MlDsa.AArch64.Sign

end

end

end


/-! ## From `OptimizedPairedHintLayout.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.AArch64.Optimized

theorem pairedHintReady_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) (roots : PairedRoots S s) {c secret y high work : Ptr} {gamma : Nat}
    (hc : inB (rbs++wbs) c 1024=true) (hs : inB (rbs++wbs) secret 2048=true)
    (hh : inB (rbs++wbs) high 2048=true)
    (hy : inB (rbs++wbs) y 2048=true) (hw : inB (rbs++wbs) work 2176=true)
    (hwy : inB wbs y 2048=true) (hww : inB wbs work 2176=true)
    (hcy : sepB rbs wbs c 1024 y 2048=true) (hcw : sepB rbs wbs c 1024 work 2176=true)
    (hsy : sepB rbs wbs secret 2048 y 2048=true) (hsw : sepB rbs wbs secret 2048 work 2176=true)
    (hyw : sepB rbs wbs y 2048 work 2176=true)
    (hyh : sepB rbs wbs y 2048 high 2048=true) (hhw : sepB rbs wbs high 2048 work 2176=true)
    (hprod : pairedProductsReduced s.mem (pa s c) (pa s secret))
    (hdata : ∀j<2,ResponseDecomposed s.mem (pairPolyPtr (pa s y) j) (pairPolyPtr (pa s high) j) gamma)
    (hg : gamma∈gamma2s) :
    Paired.PairedHintReady c secret y high work gamma s := by
  refine ⟨L.nwp hc,L.nwp hs,L.nwp hy,L.nwp hh,L.nwp hw,roots.held,roots.fit,?_,L.disj hcy,L.disj hcw,
    L.disj hsy,L.disj hsw,L.disj hyw,L.disj hyh,L.disj hhw,hprod,hg,hdata,?_,?_,roots.aligned⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact roots.apart_write (L.inW hwy)
    · exact roots.apart_write (L.inW hww)
  · exact Covers.cons (L.cR hc) (Covers.cons (L.cR hs)
      (Covers.cons (L.cR hh) (Covers.cons roots.readable (Covers.cons (L.cR hy) (L.cR hw)))))
  · exact Covers.cons (L.cW hwy) (L.cW hww)

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedPairedHintField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr callAt)
open VG.Proof.MlDsa.AArch64.Optimized

theorem pairedHintPoly_field {m : Mem} {c secret low high : Addr} {gamma j : Nat} {f ch sk : Poly}
    (hg : gamma∈gamma2s) (hc : PosPolyIs m c ch) (hs : PosPolyIs m (pairPolyPtr secret j) sk)
    (hl : SignedPolyIs m (pairPolyPtr low j) (f.map fun r=>ofInt (lowBits gamma r)) (-(gamma:Int)) gamma)
    (hh : NatPolyIs m (pairPolyPtr high j) (f.map fun r=>(highBits gamma r).toNat)) :
    pairedHintPoly m c secret low high gamma j=
      Vector.zipWith (fun ci fi=>makeHint gamma (-ci) (fi+ci)) (nttInv (multiplyNTT ch sk)) f := by
  have hg' := VG.Proof.MlDsa.AArch64.Round.isG_of_mem hg
  apply Vector.ext
  intro i hi
  rw [pairedHintPoly,Vector.getElem_ofFn,Vector.getElem_zipWith,pairedProduct,hc.value,hs.value]
  rw [Response.responseHintBase_parts hg' (Response.hintLow_exact hg' hl i hi) (Response.hintHigh_exact hh i hi)]
  simp only [getElem!_pos f i hi,getElem!_pos (nttInv (multiplyNTT ch sk)) i hi]

theorem pairedHintAt_field_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {c secret low high work : Ptr} {g : Nat} {f sk : Nat → Poly} {ch : Poly}
    (hc : inB (rbs++wbs) c 1024=true) (hs : inB (rbs++wbs) secret 2048=true)
    (hl : inB (rbs++wbs) low 2048=true) (hh : inB (rbs++wbs) high 2048=true)
    (hw : inB (rbs++wbs) work 2176=true) (h : Paired.PairedHintReady c secret low high work g s)
    (hch : PosPolyIs s.mem (pa s c) ch)
    (hsk : ∀j<2,PosPolyIs s.mem (pairPolyPtr (pa s secret) j) (sk j))
    (hlo : ∀j<2,SignedPolyIs s.mem (pairPolyPtr (pa s low) j)
      ((f j).map fun r=>ofInt (lowBits g r)) (-(g:Int)) g)
    (hhi : ∀j<2,NatPolyIs s.mem (pairPolyPtr (pa s high) j) ((f j).map fun r=>(highBits g r).toNat)) :
    WP isa (callAt "vg_mldsa_fused_pair_h" (VG.Impl.MlDsa.AArch64.Optimized.Paired.selected .h)
      (Paired.pairedHintArgs c secret low high work g)) s fun t =>
      let hints := (List.range 2).map fun j => Vector.zipWith (fun ci fi=>makeHint g (-ci) (fi+ci))
        (nttInv (multiplyNTT ch (sk j))) (f j)
      PPostB S s t [(low,2048),(work,2176)] ∧ t.gpr .x24=s.gpr .x24 ∧
      HintIs t.mem (pa s low) 2 hints ∧
      t.gpr .x0=BitVec.ofNat 64 (hintOnes hints+
        if normRq ((List.range 2).map fun j => nttInv (multiplyNTT ch (sk j)))<g then 4294967296 else 0) := by
  refine WP.mono (Paired.pairedHintAt_ok L.s64 (ptr_ok (L.ptrBs hc)) (ptr_ok (L.ptrBs hs))
    (ptr_ok (L.ptrBs hl)) (ptr_ok (L.ptrBs hh)) (ptr_ok (L.ptrBs hw)) h) fun t ⟨hp,hout,hret⟩ => ?_
  have he : ((List.range 2).map fun j=>pairedHintPoly s.mem (pa s c) (pa s secret) (pa s low) (pa s high) g j)=
      (List.range 2).map (fun j=>Vector.zipWith (fun ci fi=>makeHint g (-ci) (fi+ci)) (nttInv (multiplyNTT ch (sk j))) (f j)) := by
    apply List.map_congr_left
    intro j hj
    exact pairedHintPoly_field h.gammaOk hch (hsk j (List.mem_range.mp hj)) (hlo j (List.mem_range.mp hj)) (hhi j (List.mem_range.mp hj))
  have ep : ((List.range 2).map fun j=>pairedProduct s.mem (pa s c) (pa s secret) j)=
      (List.range 2).map (fun j=>nttInv (multiplyNTT ch (sk j))) := by
    apply List.map_congr_left
    intro j hj
    simp only [pairedProduct,hch.value,(hsk j (List.mem_range.mp hj)).value]
  rw [he] at hout hret
  rw [ep] at hret
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),hout,hret⟩

theorem hintIs_pair {m : Mem} {a : Addr} {f : Nat → Vector Bool n}
    (h : HintIs m a 2 ((List.range 2).map f)) {j : Nat} (hj : j<2) :
    HintIs m (pairPolyPtr a j) 1 [f j] := by
  refine ⟨rfl,?_⟩
  intro i hi k hk
  have ei : i=0 := by omega_using [hi]
  subst i
  have he := h.2 j hj k hk
  simp only [Nat.mul_zero,Nat.zero_add,List.getD_cons_zero] at *
  rw [VG.Proof.MlDsa.Sign.getD_range f hj (Vector.replicate n false)] at he
  have addr : pairPolyPtr a j+BitVec.ofNat 64 (4*k)=a+BitVec.ofNat 64 (4*(256*j+k)) := by
    simp only [pairPolyPtr,BitVec.add_assoc,←BitVec.ofNat_add]
    congr 2
    omega_using []
  simpa only [coeffAt,addr] using he

theorem hintOnes_pair (f : Nat → Vector Bool n) :
    hintOnes ((List.range 2).map f)=hintOnes [f 0]+hintOnes [f 1] := by
  simp only [List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,List.nil_append]
  simp only [hintOnes,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedPairedHintRow.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized

def pairedHintWrites (i : Nat) : List (Ptr × Nat) := [(hP i,2048),(t1P,2176)]

def pairedHintRowChk (p : Params) (i : Nat) : Bool :=
  inB (sgB p) cP 1024 && inB (sgB p) (t0P p i) 2048 && inB (sgB p) (hP i) 2048 &&
  inB (sgB p) (wP p i) 2048 && inB (sgB p) t1P 2176 &&
  inB (sgW p) (hP i) 2048 && inB (sgW p) t1P 2176 &&
  sepB (sgR p) (sgW p) cP 1024 (hP i) 2048 && sepB (sgR p) (sgW p) cP 1024 t1P 2176 &&
  sepB (sgR p) (sgW p) (t0P p i) 2048 (hP i) 2048 && sepB (sgR p) (sgW p) (t0P p i) 2048 t1P 2176 &&
  sepB (sgR p) (sgW p) (hP i) 2048 t1P 2176 &&
  sepB (sgR p) (sgW p) (hP i) 2048 (wP p i) 2048 && sepB (sgR p) (sgW p) (wP p i) 2048 t1P 2176 &&
  decide (p.γ₂∈gamma2s)

theorem pairedHintRowChk_ok {p : Params} (hp : Ok3 p) : ∀i<p.k,i+1<p.k → pairedHintRowChk p i=true := by
  rcases hp with rfl|rfl|rfl <;> decide

theorem pairedHint_inputs {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hi : i+1<p.k) (h : PositiveIH p S σ t i s) :
    (∀j<2,PosPolyIs s.mem (pairPolyPtr (pa s (t0P p i)) j) (T0v p σ (i+j))) ∧
    (∀j<2,SignedPolyIs s.mem (pairPolyPtr (pa s (hP i)) j)
      ((W'v p σ (p.ℓ*t) (i+j)).map fun r=>ofInt (lowBits p.γ₂ r)) (-(p.γ₂:Int)) p.γ₂) ∧
    (∀j<2,NatPolyIs s.mem (pairPolyPtr (pa s (wP p i)) j)
      ((W'v p σ (p.ℓ*t) (i+j)).map fun r=>(highBits p.γ₂ r).toNat)) := by
  refine ⟨?_,?_,?_⟩
  · intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc] using h.1.b.l.k.d.t0 (i+j) (by omega_using [hi, hj])
  · intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc,R0v,W'v,VG.Proof.MlDsa.Sign.r0F] using h.1.low j (by omega_using [hi, hj])
  · intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc,WHighv] using h.1.high (i+j) (by omega_using [hi, hj])

theorem pairedHint_ready {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i+1<p.k) (roots : PairedRoots S s) (h : PositiveIH p S σ t i s) :
    Paired.PairedHintReady cP (t0P p i) (hP i) (wP p i) t1P p.γ₂ s := by
  have checks := pairedHintRowChk_ok hp i (by omega_using [hi]) hi
  simp only [pairedHintRowChk,Bool.and_eq_true,decide_eq_true_eq] at checks
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc,hs⟩,hl⟩,hh⟩,hw⟩,hwl⟩,hww⟩,hcl⟩,hcw⟩,hsl⟩,hsw⟩,hlw⟩,hlh⟩,hhw⟩,hg⟩ := checks
  obtain ⟨hsk,hlo,hhi⟩ := pairedHint_inputs hi h
  refine pairedHintReady_layout h.1.b.l.st.lay roots hc hs hh hl hw hwl hww hcl hcw hsl hsw hlw hlh hhw
    ⟨h.1.b.c.bound,fun j hj => (hsk j hj).bound⟩ (fun j hj=>?_) hg
  have hg' := VG.Proof.MlDsa.AArch64.Round.isG_of_mem hg
  exact Response.responseDecomposed_parts hg' _ (Response.hintLow_exact hg' (hlo j hj)) (Response.hintHigh_exact (hhi j hj))

theorem pairedHintRow_ok {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i+1<p.k) (roots : PairedRoots S s) (h : PositiveIH p S σ t i s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.hintPairRow p i) s fun a =>
      PPostB S s a (pairedHintWrites i) ∧ a.gpr .x24=s.gpr .x24 ∧
      HintIs a.mem (pa s (hP i)) 2 ((List.range 2).map fun j=>Hv p σ (p.ℓ*t) (i+j)) ∧
      a.gpr .x0=BitVec.ofNat 64 (hintOnes ((List.range 2).map fun j=>Hv p σ (p.ℓ*t) (i+j))+
        if normRq ((List.range 2).map fun j=>CT0v p σ (p.ℓ*t) (i+j))<p.γ₂ then 4294967296 else 0) := by
  have checks := pairedHintRowChk_ok hp i (by omega_using [hi]) hi
  simp only [pairedHintRowChk,Bool.and_eq_true,decide_eq_true_eq] at checks
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc,hs⟩,hl⟩,hh⟩,hw⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩ := checks
  obtain ⟨hsk,hlo,hhi⟩ := pairedHint_inputs hi h
  refine WP.mono (pairedHintAt_field_layout h.1.b.l.st.lay hc hs hl hh hw
    (pairedHint_ready hp hi roots h) h.1.b.c hsk hlo hhi) fun a ⟨ha,h24,hints,ret⟩ => ?_
  change HintIs a.mem _ 2 ((List.range 2).map fun j=>Vector.zipWith _ (CT0v p σ (p.ℓ*t) (i+j)) (W'v p σ (p.ℓ*t) (i+j))) at hints
  change a.gpr .x0=BitVec.ofNat 64 (hintOnes ((List.range 2).map fun j=>Vector.zipWith _
    (CT0v p σ (p.ℓ*t) (i+j)) (W'v p σ (p.ℓ*t) (i+j)))+_) at ret
  simp only [hintRow_value] at hints ret
  exact ⟨ha,h24,hints,ret⟩

end VG.Proof.MlDsa.AArch64.Sign

end
