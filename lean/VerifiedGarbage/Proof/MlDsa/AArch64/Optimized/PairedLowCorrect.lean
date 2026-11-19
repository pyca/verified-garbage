module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.PairedConsts
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSaved
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemoryCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Arith
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Fin.Basic
import VerifiedGarbage.Proof.MlDsa.Sign.Iter
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedEntryAccess
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedKernelReady
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableMemory
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.InstancePriority
public import VerifiedGarbage.Proof.MlDsa.FusedInverseContract
import VerifiedGarbage.TCB.AArch64.Simd
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.PairedTable
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalMemory
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InnerBank
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalLoad
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstMemory
public import VerifiedGarbage.Proof.MlDsa.Arith.Representation
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemoryCorrect
import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Proof.MlDsa.ResponseZContract
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedEntryAccess
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `MlDsa.AArch64.Optimized.PairedCheckSlot`, which this module and modules that import it used -/

section

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/PairedCheckOutput.lean`, which only this module imported.
section

/-! ## From `PairedCheckRead.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- A check sequence preserves any untouched vector, independently of flags. -/
theorem checkRun_read_other (hint : Bool) (v : Values) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) (js : List (Fin 2 × Fin 8)) (a : Addr)
    (hs : ∀i∈js,Mem.Sep a 16 (out+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)) 16) :
    (checkRun hint v out aux c d js).mem.read a 16=d.mem.read a 16 := by
  induction js generalizing d with
  | nil => rfl
  | cons i js ih =>
    change (checkRun hint v out aux c (checkStep hint ((v i.1)[i.2.val])
      (out+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val))
      (aux+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)) c d) js).mem.read a 16=_
    rw [ih _ (fun j hj => hs j (List.mem_cons_of_mem _ hj))]
    exact Mem.read_write_sep (hs i (by simp)) (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedCheckOutput.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (laneVector reduceWord hintWord)

def checkOutput (hint : Bool) (raw low high : BitVec 128) (c : CheckConstants) : BitVec 128 :=
  laneVector fun e => if hint then
    hintWord (vword c.gamma e) (reduceWord (vword raw e)+vword low e) (vword high e)
    else reduceWord (vword raw e+vword low e)

theorem checkStep_read_self (hint : Bool) (raw : BitVec 128) (out aux : Addr)
    (c : CheckConstants) (d : CheckData) :
    (checkStep hint raw out aux c d).mem.read out 16=
      checkOutput hint raw (d.mem.read out 16) (d.mem.read aux 16) c := by
  have hm : (checkStep hint raw out aux c d).mem =
      d.mem.write out 16 (checkOutput hint raw (d.mem.read out 16) (d.mem.read aux 16) c) := by
    cases hint <;> simp only [checkStep,checkOutput,Bool.false_eq_true,ite_false,ite_true]
  rw [hm]
  exact Mem.readW_writeW_self d.mem out 16
    (checkOutput hint raw (d.mem.read out 16) (d.mem.read aux 16) c) (by decide)

/-- Once a vector is checked, the remaining distinct checks preserve its output. -/
theorem checkRun_head_output (hint : Bool) (v : Values) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) (i : Fin 2 × Fin 8) (js : List (Fin 2 × Fin 8))
    (hs : ∀j∈js,Mem.Sep (out+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)) 16
      (out+BitVec.ofNat 64 (1024*j.1.val+128*j.2.val)) 16) :
    (checkRun hint v out aux c d (i::js)).mem.read (out+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)) 16=
      checkOutput hint ((v i.1)[i.2.val])
        (d.mem.read (out+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)) 16)
        (d.mem.read (aux+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)) 16) c := by
  rw [checkRun,checkRun_read_other _ _ _ _ _ _ _ _ hs,checkStep_read_self]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def checkAddr (base : Addr) (i : Fin 2 × Fin 8) : Addr :=
  base+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)

theorem checkAddr_sep (base : Addr) {i j : Fin 2 × Fin 8} (hne : j≠i) :
    Mem.Sep (checkAddr base i) 16 (checkAddr base j) 16 := by
  have hd : j.1.val≠i.1.val ∨ j.2.val≠i.2.val := by
    by_contra h
    simp only [not_or,not_not] at h
    exact hne (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
  exact Offset.sep base (by omega_using [hd]) (by omega_using []) (by omega_using [])

/-- Every checked vector has exactly its prescribed output, using its original
inputs; arbitrary earlier and later disjoint stores cannot alter the result. -/
theorem checkRun_read_slot (hint : Bool) (v : Values) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) (js : List (Fin 2 × Fin 8)) (i : Fin 2 × Fin 8)
    (hi : i∈js) (hn : js.Nodup)
    (hs : ∀j∈js,j≠i → Mem.Sep (checkAddr out i) 16 (checkAddr out j) 16)
    (ha : ∀j∈js,Mem.Sep (checkAddr aux i) 16 (checkAddr out j) 16) :
    (checkRun hint v out aux c d js).mem.read (checkAddr out i) 16=
      checkOutput hint ((v i.1)[i.2.val]) (d.mem.read (checkAddr out i) 16)
        (d.mem.read (checkAddr aux i) 16) c := by
  induction js generalizing d with
  | nil => simp at hi
  | cons j js ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases he : j=i
    · subst j
      exact checkRun_head_output hint v out aux c d i js
        (fun j hj => hs j (List.mem_cons_of_mem _ hj) (by intro he; subst j; exact hn'.1 hj))
    · have hit : i∈js := (List.mem_cons.mp hi).resolve_left (Ne.symm he)
      simp only [checkRun]
      rw [ih _ hit hn'.2 (fun k hk => hs k (List.mem_cons_of_mem _ hk))
        (fun k hk => ha k (List.mem_cons_of_mem _ hk))]
      have ho : (checkStep hint ((v j.1)[j.2.val]) (checkAddr out j) (checkAddr aux j) c d).mem.read
          (checkAddr out i) 16=d.mem.read (checkAddr out i) 16 :=
        Mem.read_write_sep (hs j (by simp) he) (by decide)
      have haux : (checkStep hint ((v j.1)[j.2.val]) (checkAddr out j) (checkAddr aux j) c d).mem.read
          (checkAddr aux i) 16=d.mem.read (checkAddr aux i) 16 :=
        Mem.read_write_sep (ha j (by simp)) (by decide)
      simp only [checkAddr] at ho haux ⊢
      rw [ho,haux]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedWordTiming`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlDsa.AArch64.Round

structure WordPublic (s t : State) : Prop where
  sp : s.sp=t.sp
  args : ∀r∈([.x0,.x1,.x2,.x3,.x4] : List Reg),s.gpr r=t.gpr r
  gamma : (s.gpr .x5).setWidth 32=(t.gpr .x5).setWidth 32
  table : s.syms "VG_MLDSA_INV_PAIR"=t.syms "VG_MLDSA_INV_PAIR"

def bodyPublicRegs : List Reg := [.x0,.x1,.x13,.x14,.x15,.x16]

structure BodyPublic (s t : State) : Prop where
  sp : s.sp=t.sp
  regs : ∀r∈bodyPublicRegs,s.gpr r=t.gpr r
  gamma : (s.gpr .x17).setWidth 32=(t.gpr .x17).setWidth 32

theorem body_word_ct : ConstantTime isa (fun _ => True) BodyPublic
    (VG.Impl.MlDsa.AArch64.Round.zext .x17
      (VG.Impl.MlDsa.AArch64.Round.onGamma .x17 .x7 kernelPaired)) := by
  apply zext_ct (τ := Taint.ofRegs (.x17::bodyPublicRegs)) ?_ (by taint_decide)
  intro s t hp
  have h := agree_zext (gr := .x17) (rs := bodyPublicRegs) hp.sp hp.gamma hp.regs
  exact ⟨h.1,fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩

theorem prolog_ct : ConstantTime isa (fun _ => True)
    (Taint.AgreeS ["VG_MLDSA_INV_PAIR"] (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4])) (.block pro) :=
  VG.Taint.constantTime (A := taintS ["VG_MLDSA_INV_PAIR"])
    (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4]) (fun _ _ _ _ h => h) (by taint_decide)

/-- Only the low32 bits of gamma are public under the u32 ABI. -/
theorem r0_word_ct : ConstantTime isa EntryAccess WordPublic (selected .r0) := by
  intro s t tr₁ tr₂ s' t' hs ht hp he₁ he₂
  change Exec isa (.seq (.block pro) _) s tr₁ s' at he₁
  change Exec isa (.seq (.block pro) _) t tr₂ t' at he₂
  cases he₁ with
  | seq e₁ f₁ =>
    cases he₂ with
    | seq e₂ f₂ =>
      obtain ⟨_,a,ea,hka,arga,ta,_,_,_⟩ := prolog_ok s hs.save
      obtain ⟨_,b,eb,hkb,argb,tb,_,_,_⟩ := prolog_ok t ht.save
      obtain ⟨_,hstate₁⟩ := Exec.det e₁ ea
      rw [hstate₁] at f₁
      obtain ⟨_,hstate₂⟩ := Exec.det e₂ eb
      rw [hstate₂] at f₂
      have hp₁ := prolog_ct _ _ _ _ _ _ trivial trivial
        (show Taint.AgreeS ["VG_MLDSA_INV_PAIR"] (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4]) s t from
          ⟨VG.Proof.MlKem.AArch64.agree_of hp.sp hp.args,by
            intro name hn
            have he : name="VG_MLDSA_INV_PAIR" := by simpa only [List.mem_singleton] using hn
            subst name; exact hp.table⟩) e₁ e₂
      have hbody : BodyPublic a b := by
        refine ⟨hka.sp.trans (hp.sp.trans hkb.sp.symm),?_,?_⟩
        · intro r hr
          simp only [bodyPublicRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
          · rw [arga.work,argb.work]; exact hp.args .x4 (by decide)
          · rw [ta,tb]; exact hp.table
          · rw [arga.common,argb.common]; exact hp.args .x0 (by decide)
          · rw [arga.secret,argb.secret]; exact hp.args .x1 (by decide)
          · rw [arga.data,argb.data]; exact hp.args .x2 (by decide)
          · rw [arga.aux,argb.aux]; exact hp.args .x3 (by decide)
        · rw [arga.gamma,argb.gamma]; exact hp.gamma
      have hp₂ := body_word_ct _ _ _ _ _ _ trivial trivial hbody f₁ f₂
      rw [hp₁,hp₂]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

/-! ### `MlDsa.PairedResponseContract`, which this module and modules that import it used -/

section

/-! ### `MlDsa.ResponseHintContract`, which this module and modules that import it used -/

section

/-!
# ML-DSA: the contract of the response hint and its norm

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

/-- Reconstruct the field coefficient represented by its signed low part and high part. -/
def responseHintBase (m : Mem) (low high : Addr) (g i : Nat) : Zq :=
  ofInt ((coeffAt m low i).toInt+2*(g:Int)*(coeffAt m high i).toNat)

/-- Inputs are an exact decomposition, including the special high-zero boundary. -/
def ResponseDecomposed (m : Mem) (low high : Addr) (g : Nat) : Prop :=
  ∀i<n,(coeffAt m low i).toInt=lowBits g (responseHintBase m low high g i) ∧
    (coeffAt m high i).toNat=(highBits g (responseHintBase m low high g i)).toNat

end VG.Proof.MlDsa

end

end

/-!
# ML-DSA: the contract of the paired response checks

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

/-- Polynomial j in a contiguous pair. -/
def pairPolyPtr (p : Addr) (j : Nat) : Addr := p+BitVec.ofNat 64 (1024*j)

/-- Compose the existing NTT product and inverse-transform specifications. -/
def pairedProduct (m : Mem) (challenge secret : Addr) (j : Nat) : Poly :=
  nttInv (multiplyNTT (polyAt m challenge) (polyAt m (pairPolyPtr secret j)))

def pairedProductsReduced (m : Mem) (challenge secret : Addr) : Prop :=
  PositiveReduced m challenge ∧ ∀j<2,PositiveReduced m (pairPolyPtr secret j)

def pairedZSig : Sig where
  params := [("challenge",.array false .u32 256),("secret",.array false .u32 512),
    ("y",.array true .u32 512),("unused",.int .u64 true),
    ("work",.array true .u64 272),("unused_gamma",.int .u32 false),("bound",.int .u32 false)]
  ret := some .u32

/-- Both response sums are written on every path. The unused scalar argument
has no memory footprint, so callers may pass the work-buffer address there. -/
def pairedZContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  pairedZSig.contract A
    (pre := fun c secret y _unused _work _gamma bound m =>
      pairedProductsReduced m c secret ∧ (∀j<2,Reduced m (pairPolyPtr y j)) ∧
      1≤bound.toNat ∧ bound.toNat≤524288)
    (post := fun c secret y _unused _work _gamma bound m m' r =>
      (∀j<2,CenteredReduced m' (pairPolyPtr y j) ∧
        signedPolyAt m' (pairPolyPtr y j)=add (polyAt m (pairPolyPtr y j)) (pairedProduct m c secret j)) ∧
      r=if normRq ((List.range 2).map fun j => add (polyAt m (pairPolyPtr y j)) (pairedProduct m c secret j))<bound.toNat then 1 else 0)
    (writeArgs := true) (stack := stack)

def pairedLowSig : Sig where
  params := [("challenge",.array false .u32 256),("secret",.array false .u32 512),
    ("w",.array true .u32 512),("low",.array true .u32 512),
    ("work",.array true .u64 272),("gamma2",.int .u32 true),("bound",.int .u32 false)]
  ret := some .u32

def pairedDifference (m : Mem) (c secret w : Addr) (j : Nat) : Poly :=
  sub (polyAt m (pairPolyPtr w j)) (pairedProduct m c secret j)

def pairedLowPoly (g : Nat) (f : Poly) : Poly := f.map fun x => ofInt (lowBits g x)

/-- Exact high and signed low parts are written even when either polynomial
fails its norm bound. No per-polynomial early return is permitted by timing. -/
def pairedLowContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  pairedLowSig.contract A
    (pre := fun c secret w _low _work gamma2 bound m =>
      pairedProductsReduced m c secret ∧ (∀j<2,Reduced m (pairPolyPtr w j)) ∧
      gamma2.toNat∈gamma2s ∧ 1≤bound.toNat ∧ bound.toNat≤524288)
    (post := fun c secret w low _work gamma2 bound m m' r =>
      (∀j<2,∀i<n,
        (coeffAt m' (pairPolyPtr w j) i).toNat=(highBits gamma2.toNat (pairedDifference m c secret w j)[i]!).toNat ∧
        (coeffAt m' (pairPolyPtr low j) i).toInt=lowBits gamma2.toNat (pairedDifference m c secret w j)[i]!) ∧
      r=if normRq ((List.range 2).map fun j => pairedLowPoly gamma2.toNat (pairedDifference m c secret w j))<bound.toNat then 1 else 0)
    (writeArgs := true) (stack := stack)

def pairedHintSig : Sig where
  params := [("challenge",.array false .u32 256),("secret",.array false .u32 512),
    ("low",.array true .u32 512),("high",.array false .u32 512),
    ("work",.array true .u64 272),("gamma2",.int .u32 true),("bound",.int .u32 false)]
  ret := some .u64

def pairedHintPoly (m : Mem) (c secret low high : Addr) (g j : Nat) : Vector Bool n :=
  Vector.ofFn fun i =>
    let ct := (pairedProduct m c secret j)[i.val]!
    makeHint g (-ct) (responseHintBase m (pairPolyPtr low j) (pairPolyPtr high j) g i.val+ct)

/-- Return the total hint count in low32 and strict norm success in high32.
All 512 hints are exact on both acceptance and rejection. -/
def pairedHintContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  pairedHintSig.contract A
    (pre := fun c secret low high _work gamma2 bound m =>
      pairedProductsReduced m c secret ∧ gamma2.toNat∈gamma2s ∧ bound=gamma2 ∧
      ∀j<2,ResponseDecomposed m (pairPolyPtr low j) (pairPolyPtr high j) gamma2.toNat)
    (post := fun c secret low high _work gamma2 _bound m m' r =>
      let hints := (List.range 2).map fun j => pairedHintPoly m c secret low high gamma2.toNat j
      HintIs m' low 2 hints ∧
      r=BitVec.ofNat 64 (hintOnes hints+
        if normRq ((List.range 2).map fun j => pairedProduct m c secret j)<gamma2.toNat then 4294967296 else 0))
    (writeArgs := true) (stack := stack)

end VG.Proof.MlDsa

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedCheckFlags`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response

def checkMask (hint : Bool) (raw low : BitVec 128) (c : CheckConstants) (e : Nat) : BitVec 32 :=
  normMask (reduceWord (if hint then vword raw e else vword raw e+vword low e))
    (vword c.lower e) (vword c.width e)

theorem checkStep_flag (hint : Bool) (raw : BitVec 128) (out aux : Addr)
    (c : CheckConstants) (d : CheckData) {e : Nat} (he : e<4) :
    vword (checkStep hint raw out aux c d).flags e=
      vword d.flags e ||| checkMask hint raw (d.mem.read out 16) c e := by
  simp only [checkStep,checkMask,laneVector_word _ he]

theorem checkStep_flag_zero (hint : Bool) (raw : BitVec 128) (out aux : Addr)
    (c : CheckConstants) (d : CheckData) {e : Nat} (he : e<4) :
    vword (checkStep hint raw out aux c d).flags e=0 ↔
      vword d.flags e=0 ∧ checkMask hint raw (d.mem.read out 16) c e=0 := by
  rw [checkStep_flag _ _ _ _ _ _ he]
  exact BitVec.or_eq_zero_iff

/-- Acceptance of a distinct-vector check sequence is exactly acceptance
of every original coefficient check and the incoming accumulator. -/
theorem checkRun_flag_zero_iff (hint : Bool) (v : Values) (out aux : Addr)
    (c : CheckConstants) (d : CheckData) (js : List (Fin 2 × Fin 8))
    (hn : js.Nodup) {e : Nat} (he : e<4) :
    vword (checkRun hint v out aux c d js).flags e=0 ↔
      vword d.flags e=0 ∧ ∀i∈js,
        checkMask hint ((v i.1)[i.2.val]) (d.mem.read (checkAddr out i) 16) c e=0 := by
  induction js generalizing d with
  | nil => simp only [checkRun,List.not_mem_nil,false_implies,implies_true,and_true]
  | cons i js ih =>
    have hn' := List.nodup_cons.mp hn
    rw [checkRun,ih _ hn'.2,checkStep_flag_zero _ _ _ _ _ _ he]
    have hread (j : Fin 2 × Fin 8) (hj : j∈js) :
        (checkStep hint ((v i.1)[i.2.val]) (checkAddr out i) (checkAddr aux i) c d).mem.read
          (checkAddr out j) 16=d.mem.read (checkAddr out j) 16 :=
      Mem.read_write_sep (checkAddr_sep out (by intro h; subst i; exact hn'.1 hj)) (by decide)
    have ht : (∀j∈js,checkMask hint ((v j.1)[j.2.val])
        ((checkStep hint ((v i.1)[i.2.val]) (checkAddr out i) (checkAddr aux i) c d).mem.read
          (checkAddr out j) 16) c e=0) ↔
        ∀j∈js,checkMask hint ((v j.1)[j.2.val]) (d.mem.read (checkAddr out j) 16) c e=0 := by
      constructor <;> intro h j hj <;> simpa only [hread j hj] using h j hj
    simp only [checkAddr] at ht ⊢
    rw [ht]
    simp only [List.mem_cons,forall_eq_or_imp,and_assoc]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedRawField`, which this module and modules that import it used -/

section

/-! ## From `PairedProductBankField.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Each paired input bank is exactly the previously verified product bank. -/
theorem valuesAt_productValues (m : Mem) (a b : Addr) (u : Nat) (poly : Fin 2) :
    valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) poly =
      Inverse.productValues m a (b+BitVec.ofNat 64 (1024*poly.val)) u := by
  apply Vector.ext
  intro j hj
  apply vec_ext
  intro e he
  exact (valuesAt_coeff m a b u poly ⟨j,hj⟩ he).trans
    (Inverse.productValues_word m a (b+BitVec.ofNat 64 (1024*poly.val)) u ⟨j,hj⟩ he).symm

/-- The paired five-layer transform preserves the exact field meaning and
its signed 32q bound for either polynomial. -/
theorem fiveValues_field {m : Mem} {a b : Addr} {u : Nat} {poly : Fin 2} {f g : Poly}
    (hu : u<8) (hf : PosPolyIs m a f)
    (hg : PosPolyIs m (b+BitVec.ofNat 64 (1024*poly.val)) g) :
    BankBound (Inverse.fiveValues u
      (valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) poly)) 268173344 ∧
    InnerBankField u (Inverse.fiveValues u
      (valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) poly))
      (InverseTraversal.run (InverseTraversal.localSlice u) (Representation.product true f g)) := by
  rw [valuesAt_productValues]
  exact Inverse.fiveValues_field _ _ hu (Inverse.productValues_bound hf hg hu)
    (Inverse.productValues_field hf hg hu)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedFinalBankField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- The strided final-pass bank contains the complete first-five-layer field
result, with the signed range needed by the remaining inverse layers. -/
theorem firstPass_finalBank_field {m : Mem} {p a b : Addr} {u : Nat} (hu : u<8)
    (ha : (⟨a,1024⟩ : Region).Disjoint ⟨p,2048⟩)
    (hb : (⟨b,2048⟩ : Region).Disjoint ⟨p,2048⟩) (poly : Fin 2) {f g : Poly}
    (hf : PosPolyIs m a f) (hg : PosPolyIs m (b+BitVec.ofNat 64 (1024*poly.val)) g) :
    BankBound (readPair (firstPassMem m p a b 8) (p+BitVec.ofNat 64 (16*u)) 128 poly) 268173344 ∧
    ∀j : Fin 8, ∀e<4,
      ofInt (vword ((readPair (firstPassMem m p a b 8) (p+BitVec.ofNat 64 (16*u)) 128 poly)[j.val]) e).toInt =
      (InverseTraversal.run InverseTraversal.localSchedule (Representation.product true f g))[32*j.val+4*u+e]! := by
  rw [firstPass_finalBank hu ha hb poly]
  constructor
  · intro j e he
    simp only [Vector.getElem_ofFn]
    exact (fiveValues_field j.isLt hf hg).1 ⟨u,hu⟩ e he
  · intro j e he
    simp only [Vector.getElem_ofFn]
    have hv := (fiveValues_field j.isLt hf hg).2 ⟨u,hu⟩ e he
    have hi : 32*j.val+4*u+e<n := by change 32*j.val+4*u+e<256; omega_using [hu, he]
    rw [Inverse.local_coordinate _ hi]
    have hd : (32*j.val+4*u+e)/32=j.val := by omega_using [hu, he]
    rw [hd]
    exact hv

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedRawField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- The complete paired transform yields the ordinary inverse pointwise
product in the strict signed interval expected by the fused checks. -/
theorem rawFinal_field {m : Mem} {p a b : Addr} {u : Nat} (hu : u<8)
    (ha : (⟨a,1024⟩ : Region).Disjoint ⟨p,2048⟩)
    (hb : (⟨b,2048⟩ : Region).Disjoint ⟨p,2048⟩) (poly : Fin 2) {f g : Poly}
    (hf : PosPolyIs m a f) (hg : PosPolyIs m (b+BitVec.ofNat 64 (1024*poly.val)) g)
    (i : Fin 8) {e : Nat} (he : e<4) :
    let v := Inverse.rawFinalValues (readPair (firstPassMem m p a b 8) (p+BitVec.ofNat 64 (16*u)) 128 poly);
    -8380417<(vword v[i.val] e).toInt ∧ (vword v[i.val] e).toInt<2*8380417 ∧
      ofInt (vword v[i.val] e).toInt=(nttInv (multiplyNTT f g))[4*u+32*i.val+e]! := by
  dsimp only
  have hbank := firstPass_finalBank_field hu ha hb poly hf hg
  have hv := Inverse.rawFinalValues_field _
    (InverseTraversal.run InverseTraversal.localSchedule (Representation.product true f g)) hu hbank.1
    (fun j e he => by simpa only [Traversal.loc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hbank.2 j e he) i he
  refine ⟨hv.1,hv.2.1,hv.2.2.trans ?_⟩
  have hk : 4*u+32*i.val+e<n := by change 4*u+32*i.val+e<256; omega_using [hu, he]
  have hu' : (4*u+32*i.val+e)%32/4=u := by omega_using [hu, he]
  have hcoord := InverseTraversal.strided_coordinate
    (InverseTraversal.run InverseTraversal.localSchedule (Representation.product true f g)) hk
  rw [hu'] at hcoord
  rw [←hcoord,←map_mul_get _ _ hk,InverseTraversal.traversal_montgomery]
  change (Representation.inverse true (Representation.product true f g))[_]! = _
  rw [Representation.inverse_product]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedMaskInvariant`, which this module and modules that import it used -/

section

/-! ## From `PairedFinishSemantic.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response

def FlagMasks (v : BitVec 128) : Prop := ∀e<4,vword v e=0 ∨ vword v e= -1

theorem flag_lanes_zero (v : BitVec 128) :
    (∀e<4,vword v e=0) ↔ vword v 0=0 ∧ vword v 1=0 ∧ vword v 2=0 ∧ vword v 3=0 := by
  constructor
  · intro h
    exact ⟨h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide)⟩
  · rintro ⟨h0,h1,h2,h3⟩ e he
    rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega_using [he]) with rfl | rfl | rfl | rfl <;>
      with_reducible assumption

/-- Exact success-bit reduction for the four SIMD rejection-mask lanes. -/
theorem finishValue_accept (v : BitVec 128) (hv : FlagMasks v) :
    finishValue v= @ite _ (∀e<4,vword v e=0) (Classical.propDecidable _) 1 0 := by
  rw [flag_lanes_zero,finishValue]
  rcases hv 0 (by decide) with h0 | h0 <;>
    rcases hv 1 (by decide) with h1 | h1 <;>
    rcases hv 2 (by decide) with h2 | h2 <;>
    rcases hv 3 (by decide) with h3 | h3 <;>
    rw [h0,h1,h2,h3] <;> simp

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedMaskInvariant.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response

theorem mask_or_closed {a b : BitVec 32} (ha : a=0 ∨ a= -1) (hb : b=0 ∨ b= -1) :
    a|||b=0 ∨ a|||b= -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem normMask_closed (x lo width : BitVec 32) : normMask x lo width=0 ∨ normMask x lo width= -1 := by
  unfold normMask
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem checkStep_masks (hint : Bool) (raw : BitVec 128) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) (hd : FlagMasks d.flags) : FlagMasks (checkStep hint raw out aux c d).flags := by
  intro e he
  rw [checkStep_flag _ _ _ _ _ _ he]
  exact mask_or_closed (hd e he) (normMask_closed _ _ _)

theorem checkRun_masks (hint : Bool) (v : Values) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) (js : List (Fin 2 × Fin 8)) (hd : FlagMasks d.flags) :
    FlagMasks (checkRun hint v out aux c d js).flags := by
  induction js generalizing d with
  | nil => exact hd
  | cons i js ih => exact ih _ (checkStep_masks _ _ _ _ _ _ hd)

theorem finalPass_masks (hint : Bool) (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) (n : Nat) (hd : FlagMasks d.flags) :
    FlagMasks (finalPassData hint work out aux c d n).flags := by
  induction n with
  | zero => exact hd
  | succ n ih => exact checkRun_masks _ _ _ _ _ _ _ ih

theorem lowPair_masks (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) (hd : FlagMasks d.flags) :
    FlagMasks (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).flags := by
  intro e he
  rw [lowPair_flag _ _ _ _ _ _ _ _ _ he]
  exact mask_or_closed (mask_or_closed (hd e he) (normMask_closed _ _ _)) (normMask_closed _ _ _)

theorem lowRun_masks (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (hd : FlagMasks d.flags) :
    FlagMasks (lowRun g v out aux c d is).flags := by
  induction is generalizing d with
  | nil => exact hd
  | cons i is ih => exact ih _ (lowPair_masks _ _ _ _ _ _ _ _ _ hd)

theorem lowPass_masks (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) (n : Nat) (hd : FlagMasks d.flags) :
    FlagMasks (lowPassData g work out aux c d n).flags := by
  induction n with
  | zero => exact hd
  | succ n ih => exact lowRun_masks _ _ _ _ _ _ _ ih

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedSatMemory`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

def pairedSatMem : Mem := constMem 65536 expandedWords

theorem pairedSat_held : ∀i<512,pairedSatMem.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0 := by
  intro i hi
  exact constMem_held 65536 expandedWords (by rw [PairedTable.expandedWords_length]; decide)
    i (by rw [PairedTable.expandedWords_length]; exact hi)

theorem pairedSat_coeff_zero {p : Nat} (hp : p≤32768) {i : Nat} (hi : i<n) :
    coeffAt pairedSatMem (BitVec.ofNat 64 p) i=0 := by
  simp only [pairedSatMem,coeffAt,Mem.readW,BitVec.setWidth_eq]
  rw [Mem.read_eq_of_bytes (v := (0#32)) ?_]
  · rfl
  · intro j hj
    have ha : ¬ ((BitVec.ofNat 64 p+BitVec.ofNat 64 (4*i)+BitVec.ofNat 64 j)-65536).toNat<8*expandedWords.length := by
      rw [PairedTable.expandedWords_length]
      have hi' : i<256 := hi
      simp only [BitVec.toNat_sub,BitVec.toNat_add,BitVec.toNat_ofNat,
        show (65536:BitVec 64).toNat=65536 by decide]
      omega_using [hp, hj, hi']
    simp only [constMem,ha,ite_false]
    simp

theorem pairedSat_reduced {p : Nat} (hp : p≤32768) : Reduced pairedSatMem (BitVec.ofNat 64 p) := by
  intro i hi
  rw [pairedSat_coeff_zero hp hi]
  decide

theorem pairedSat_positive {p : Nat} (hp : p≤32768) : PositiveReduced pairedSatMem (BitVec.ofNat 64 p) := by
  intro i hi
  rw [pairedSat_coeff_zero hp hi]
  decide

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedSpecFrame`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

theorem positiveReduced_frame {rs : List Region} {m m' : Mem} {p : Addr}
    (hf : Frame rs m m') (hd : ∀r∈rs,(⟨p,1024⟩:Region).Disjoint r)
    (hp : PositiveReduced m p) : PositiveReduced m' p := by
  intro i hi
  rw [VG.Proof.MlDsa.Verify.coeffAt_congr (VG.Proof.MlKem.bytes_frame hf hd (by decide)) hi]
  exact hp i hi

theorem pairedProduct_frame {rs : List Region} {m m' : Mem} {challenge secret : Addr}
    (hf : Frame rs m m')
    (hc : ∀r∈rs,(⟨challenge,1024⟩:Region).Disjoint r)
    (hs : ∀r∈rs,(⟨secret,2048⟩:Region).Disjoint r) {j : Nat} (hj : j<2) :
    pairedProduct m' challenge secret j=pairedProduct m challenge secret j := by
  have hp : ∀r∈rs,(⟨pairPolyPtr secret j,1024⟩:Region).Disjoint r := by
    intro r hr
    exact (hs r hr).sub_left (Offset.sub_base secret (by omega_using [hj]))
  rw [pairedProduct,VG.Proof.MlDsa.Verify.polyAt_frame hf hc,
    VG.Proof.MlDsa.Verify.polyAt_frame hf hp]
  rfl

theorem pairedProductsReduced_frame {rs : List Region} {m m' : Mem} {challenge secret : Addr}
    (hf : Frame rs m m')
    (hc : ∀r∈rs,(⟨challenge,1024⟩:Region).Disjoint r)
    (hs : ∀r∈rs,(⟨secret,2048⟩:Region).Disjoint r)
    (hp : pairedProductsReduced m challenge secret) : pairedProductsReduced m' challenge secret := by
  refine ⟨positiveReduced_frame hf hc hp.1,?_⟩
  intro j hj
  apply positiveReduced_frame hf _ (hp.2 j hj)
  intro r hr
  exact (hs r hr).sub_left (Offset.sub_base secret (by omega_using [hj]))

theorem pairedDifference_frame {rs : List Region} {m m' : Mem} {challenge secret out : Addr}
    (hf : Frame rs m m')
    (hc : ∀r∈rs,(⟨challenge,1024⟩:Region).Disjoint r)
    (hs : ∀r∈rs,(⟨secret,2048⟩:Region).Disjoint r)
    (ho : ∀r∈rs,(⟨out,2048⟩:Region).Disjoint r) {j : Nat} (hj : j<2) :
    pairedDifference m' challenge secret out j=pairedDifference m challenge secret out j := by
  have hp : ∀r∈rs,(⟨pairPolyPtr out j,1024⟩:Region).Disjoint r := by
    intro r hr
    exact (ho r hr).sub_left (Offset.sub_base out (by omega_using [hj]))
  rw [pairedDifference,VG.Proof.MlDsa.Verify.polyAt_frame hf hp,
    pairedProduct_frame hf hc hs hj]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedSpecPre`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedConsts_eq : pairedConsts=[("VG_MLDSA_INV_PAIR",expandedWords)] := rfl

structure ZSpecPre (s : State) : Prop where
  rd : s.rd=[⟨s.gpr .x0,1024⟩,⟨s.gpr .x1,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]
  wr : s.wr=[⟨s.gpr .x2,2048⟩,⟨s.gpr .x4,2176⟩]
  table : PairedTable.Artifact s.mem (s.syms "VG_MLDSA_INV_PAIR")
  tableSep : ∀r∈s.wr,(⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint r
  commonData : (⟨s.gpr .x0,1024⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩
  commonWork : (⟨s.gpr .x0,1024⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  secretData : (⟨s.gpr .x1,2048⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩
  secretWork : (⟨s.gpr .x1,2048⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  dataWork : (⟨s.gpr .x2,2048⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  products : pairedProductsReduced s.mem (s.gpr .x0) (s.gpr .x1)
  data : ∀j<2,Reduced s.mem (pairPolyPtr (s.gpr .x2) j)
  boundLow : 1≤((s.gpr .x6).setWidth 32).toNat
  boundHigh : ((s.gpr .x6).setWidth 32).toNat≤524288
  tableAl : (s.syms "VG_MLDSA_INV_PAIR").toNat%64=0

theorem pairedZ_pre {s : State}
    (h : (pairedZContract (abi.withConsts pairedConsts)).pre s) : ZSpecPre s := by
  sig_pre [pairedZContract,pairedZSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow] at h
  obtain ⟨hdrop,hheld,_,hsep,hal,htake,hwr,hcd,hcw,hsd,hsw,hdw,_,_,_,_,hprod,hdata,hbl,hbh⟩ := h
  refine ⟨?_,hwr,?_,hsep,hcd,hcw,hsd,hsw,hdw,hprod,hdata,hbl,hbh,hal⟩
  · rw [←List.take_append_drop (s.rd.length-1) s.rd,htake,hdrop]
    rfl
  · intro i hi
    refine (hheld i hi).trans ?_
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [PairedTable.expandedWords_length]; exact hi),
      Option.getD_some,getElem!_pos _ _ (by rw [PairedTable.expandedWords_length]; exact hi)]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedAbi`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.PairedEntry`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.PairedKernel`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlKem.AArch64 (Keep)

def kernelRegs : List Reg := [.x0,.x1,.x2,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16]

theorem checkKernel_ok (hint : Bool) (g : Nat) {s₀ s : State}
    {gr : List Reg} {vr : List VReg}
    (hf : CallFrame gr vr s₀ s) (hs : Saved s.mem (s.gpr .x0) s₀.v)
    (ha : KernelAccess s) (ht : PairedTable.Words s.mem (s.gpr .x1))
    (hdw : (⟨s.gpr .x1,4096⟩:Region).Disjoint ⟨s.gpr .x0,2048⟩)
    (hdd : (⟨s.gpr .x1,4096⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (hsd : (⟨s.gpr .x0+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (haux : hint=true → ∀off,off+16≤2048 → InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 off) 16) :
    WP isa (kernel (if hint then .h else .z) g) s fun t =>
      ∃u,Prepared s u ∧ CheckSetup hint s u ∧
        Keep (gr++kernelRegs) s₀ t ∧
        let d := finalPassData hint (s.gpr .x0) (s.gpr .x15) (s.gpr .x16) (constantsAt u) (dataAt u) 8
        t.mem=d.mem ∧ t.gpr .x0=dataReturn (if hint then .h else .z) d := by
  apply checkKernel_wp
  refine WP.seq (WP.mono (firstKernel_access_ok ha ht hdw) fun b ⟨hb,hq,h0,h1,_,_,hm⟩ => ?_)
  have hq' : ∀e<4,vword (b.v .v31) e=8380417#32 := by
    intro e he
    rw [hq.qv]
    exact HighPack.repeatedWord_lane 8380417 he
  refine WP.seq (WP.mono (checkMiddle_ok hint g b hq') fun u ⟨hu,hum,hu0,hu2,hu12,hc⟩ => ?_)
  have huf := ((hf.trans (CallFrame.ofKeepWide hb)).trans hu)
  have hu2' : u.gpr .x2=s.gpr .x0 := by rw [hu2,h0]; bv_omega_arith
  have hu1 : u.gpr .x1=s.gpr .x1+BitVec.ofNat 64 3840 := by
    rw [hu.gpr .x1 (by decide),h1]
    rfl
  have hu15 : u.gpr .x15=s.gpr .x15 :=
    (hu.gpr .x15 (by decide)).trans (hb.get .x15 (by decide))
  have hu16 : u.gpr .x16=s.gpr .x16 :=
    (hu.gpr .x16 (by decide)).trans (hb.get .x16 (by decide))
  have huframe : Frame [⟨s.gpr .x0,2048⟩] s.mem u.mem := by
    rw [hum,hm]; exact firstPass_frame (by decide)
  have htu : PairedTable.Words u.mem (s.gpr .x1) :=
    tableWords_frame ht huframe (by simpa only [List.mem_singleton,forall_eq] using hdw)
  have hsu : Saved u.mem (s.gpr .x0) s₀.v := hs.workFrame huframe
  have hac : CheckSetup hint s u := by
    refine ⟨hc.ready,hc.flags,hc.count,?_,?_,?_⟩
    · simpa only [hb.get .x17 (by decide)] using hc.gamma
    · simpa only [hb.get .x8 (by decide)] using hc.lower
    · simpa only [hb.get .x8 (by decide)] using hc.width
  refine WP.mono (finalKernel_ok hint huf hsu hu2' ?_ ?_ htu ?_ hu1 hu12 hc.ready ?_ ?_ ?_)
    fun t ⟨hkeep,htm,htv⟩ => ?_
  · simpa only [hu15] using hsd
  · intro p hp
    simp only [hu.rd,hu.wr,hb.rd,hb.wr,BitVec.add_assoc,←BitVec.ofNat_add]
    apply ha.workRead
    obtain ⟨i,rfl⟩ := (extraSlots_mem _ _).mp hp
    omega_using []
  · simpa only [hu15] using hdd
  · simpa only [hu.rd,hu.wr,hb.rd,hb.wr] using ha.table
  · intro i hi p j
    simp only [hu.rd,hu.wr,hb.rd,hb.wr,hu2',BitVec.add_assoc,←BitVec.ofNat_add]
    exact ha.workRead _ (by omega_using [hi])
  · intro i hi p j
    simp only [hu.rd,hu.wr,hb.rd,hb.wr,hu15,hu16,BitVec.add_assoc,←BitVec.ofNat_add]
    exact ⟨ha.dataRead _ (by omega_using [hi]),fun h => haux h _ (by omega_using [hi]),ha.dataWrite _ (by omega_using [hi])⟩
  · refine ⟨u,⟨hum.trans hm,hu2',hu15,hu16⟩,hac,?_,?_,?_⟩
    · refine hkeep.mono ?_
      intro r hr
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,middleRegs,finalGprs,
        kernelRegs] at hr ⊢
      grind
    · simpa only [hu15,hu16] using htm
    · simpa only [hu15,hu16] using htv

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlKem.AArch64 (Keep)

def entryRegs : List Reg := [.x0,.x1,.x2,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17]

theorem selected_check_eq (hint : Bool) :
    selected (if hint then .h else .z)=.seq (.block pro) (kernel (if hint then .h else .z) 0) := by
  cases hint <;> rfl

/-- Whole z/h entry, including argument remapping, saved vectors, all inverse
and response iterations, combined result, and ABI restoration. -/
theorem selected_check_ok (hint : Bool) {s : State}
    (ha : EntryAccess s) (ht : PairedTable.Words s.mem (s.syms "VG_MLDSA_INV_PAIR"))
    (hdw : (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint ⟨s.gpr .x4,2048⟩)
    (hds : (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint ⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩)
    (hdd : (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩)
    (hsd : (⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩)
    (haux : hint=true → ∀off,off+16≤2048 → InRegions (s.rd++s.wr) (s.gpr .x3+BitVec.ofNat 64 off) 16) :
    WP isa (selected (if hint then .h else .z)) s fun t =>
      ∃a u,Arguments s a ∧ Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem a.mem ∧
        Prepared a u ∧ CheckSetup hint a u ∧ Keep entryRegs s t ∧
        let d := finalPassData hint (s.gpr .x4) (s.gpr .x2) (s.gpr .x3) (constantsAt u) (dataAt u) 8
        t.mem=d.mem ∧ t.gpr .x0=dataReturn (if hint then .h else .z) d := by
  rw [selected_check_eq]
  refine WP.seq (WP.mono (prolog_ok s ha.save) fun a ⟨hk,args,hta,_,hs,hframe⟩ => ?_)
  have ht' : PairedTable.Words a.mem (a.gpr .x1) := by
    rw [hta]
    exact tableWords_frame ht hframe (by simpa only [List.mem_singleton,forall_eq] using hds)
  have hs' : Saved a.mem (a.gpr .x0) s.v := by rw [args.work]; exact hs
  refine WP.mono (checkKernel_ok hint 0 (CallFrame.ofKeepWide hk) hs' (ha.kernel hk args hta)
    ht' ?_ ?_ ?_ ?_) fun t ⟨u,hu,hc,hkt,hm,hv⟩ => ?_
  · simpa only [hta,args.work] using hdw
  · simpa only [hta,args.data] using hdd
  · simpa only [args.work,args.data] using hsd
  · simpa only [hk.rd,hk.wr,args.aux] using haux
  · refine ⟨a,u,args,hframe,hu,hc,hkt.mono (by decide),?_,?_⟩
    · simpa only [args.work,args.data,args.aux] using hm
    · simpa only [args.work,args.data,args.aux] using hv

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem entryKeep_abi {s t : State} (h : Keep entryRegs s t) : abiPreserved s t := by
  refine ⟨?_,h.sp,h.vcs⟩
  intro r hr
  apply h.gpr r
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedLowKernel`, which only this module used -/

section

/-! ## `PairedLowKernel` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlKem.AArch64 (Keep)

theorem pairedLowKernel_ok (g : Nat) (hg : VG.Proof.MlDsa.AArch64.Round.IsG g) {s₀ s : State}
    {gr : List Reg} {vr : List VReg}
    (hf : CallFrame gr vr s₀ s) (hs : Saved s.mem (s.gpr .x0) s₀.v)
    (ha : KernelAccess s) (ht : PairedTable.Words s.mem (s.gpr .x1))
    (hdw : (⟨s.gpr .x1,4096⟩:Region).Disjoint ⟨s.gpr .x0,2048⟩)
    (hdd : (⟨s.gpr .x1,4096⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (hsd : (⟨s.gpr .x0+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (hda : (⟨s.gpr .x1,4096⟩:Region).Disjoint ⟨s.gpr .x16,2048⟩)
    (hsa : (⟨s.gpr .x0+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x16,2048⟩)
    (haw : ∀off,off+16≤2048 → InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 off) 16) :
    WP isa (kernelPaired g) s fun t =>
      ∃u,Prepared s u ∧ LowSetup g s u ∧
        Keep (gr++kernelRegs) s₀ t ∧
        let d := lowPassData g (s.gpr .x0) (s.gpr .x15) (s.gpr .x16) (lowConstantsAt u) (dataAt u) 8
        t.mem=d.mem ∧ t.gpr .x0=dataReturn .r0 d := by
  apply lowKernel_wp
  refine WP.seq (WP.mono (firstKernel_access_ok ha ht hdw) fun b ⟨hb,hq,h0,h1,_,_,hm⟩ => ?_)
  have hq' : ∀e<4,vword (b.v .v31) e=8380417#32 := by
    intro e he
    rw [hq.qv]
    exact HighPack.repeatedWord_lane 8380417 he
  refine WP.seq (WP.mono (lowMiddle_ok g hg b hq') fun u ⟨hu,hum,hu0,hu2,hu12,hc⟩ => ?_)
  have huf := ((hf.trans (CallFrame.ofKeepWide hb)).trans hu)
  have hu2' : u.gpr .x2=s.gpr .x0 := by rw [hu2,h0]; bv_omega
  have hu1 : u.gpr .x1=s.gpr .x1+BitVec.ofNat 64 3840 := by
    rw [hu.gpr .x1 (by decide),h1]
    rfl
  have hu15 : u.gpr .x15=s.gpr .x15 :=
    (hu.gpr .x15 (by decide)).trans (hb.get .x15 (by decide))
  have hu16 : u.gpr .x16=s.gpr .x16 :=
    (hu.gpr .x16 (by decide)).trans (hb.get .x16 (by decide))
  have huframe : Frame [⟨s.gpr .x0,2048⟩] s.mem u.mem := by
    rw [hum,hm]; exact firstPass_frame (by decide)
  have htu : PairedTable.Words u.mem (s.gpr .x1) :=
    tableWords_frame ht huframe (by simpa only [List.mem_singleton,forall_eq] using hdw)
  have hsu : Saved u.mem (s.gpr .x0) s₀.v := hs.workFrame huframe
  have hac : LowSetup g s u := by
    refine ⟨hc.ready,hc.flags,hc.scale,?_,?_⟩
    · simpa only [hb.get .x8 (by decide)] using hc.lower
    · simpa only [hb.get .x8 (by decide)] using hc.width
  refine WP.mono (lowKernel_ok g hg huf hsu hu2' ?_ ?_ ?_ htu ?_ ?_ hu1 hu12 hc.ready ?_ ?_ ?_)
    fun t ⟨hkeep,htm,htv⟩ => ?_
  · simpa only [hu15] using hsd
  · intro p hp
    simp only [hu.rd,hu.wr,hb.rd,hb.wr,BitVec.add_assoc,←BitVec.ofNat_add]
    apply ha.workRead
    obtain ⟨i,rfl⟩ := (extraSlots_mem _ _).mp hp
    omega_arith
  · simpa only [hu16] using hsa
  · simpa only [hu15] using hdd
  · simpa only [hu16] using hda
  · simpa only [hu.rd,hu.wr,hb.rd,hb.wr] using ha.table
  · intro i hi p j
    simp only [hu.rd,hu.wr,hb.rd,hb.wr,hu2',BitVec.add_assoc,←BitVec.ofNat_add]
    exact ha.workRead _ (by omega_arith)
  · intro v hv i
    simp only [hu.rd,hu.wr,hb.rd,hb.wr,hu15,hu16,BitVec.add_assoc,←BitVec.ofNat_add]
    have hi0 : lowOff i≤1792 := by unfold lowOff; omega_arith
    refine ⟨ha.dataRead _ (by omega_arith),ha.dataRead _ (by omega_arith),ha.dataWrite _ (by omega_arith),
      ha.dataWrite _ (by omega_arith),haw _ (by omega_arith),haw _ (by omega_arith)⟩
  · refine ⟨u,⟨hum.trans hm,hu2',hu15,hu16⟩,hac,?_,?_,?_⟩
    · refine hkeep.mono ?_
      intro r hr
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,middleRegs,finalGprs,
        kernelRegs] at hr ⊢
      grind
    · simpa only [hu15,hu16] using htm
    · simpa only [hu15,hu16] using htv

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowEntry` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlKem.AArch64 (Keep)

theorem selected_low_ok {s : State} (hg : IsG (arg32 s .x5))
    (ha : EntryAccess s) (ht : PairedTable.Words s.mem (s.syms "VG_MLDSA_INV_PAIR"))
    (hdw : (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint ⟨s.gpr .x4,2048⟩)
    (hds : (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint ⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩)
    (hdd : (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩)
    (hsd : (⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩)
    (hda : (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint ⟨s.gpr .x3,2048⟩)
    (hsa : (⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x3,2048⟩)
    (haw : ∀off,off+16≤2048 → InRegions s.wr (s.gpr .x3+BitVec.ofNat 64 off) 16) :
    WP isa (selected .r0) s fun t =>
      ∃a b u,Arguments s a ∧ Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem a.mem ∧
        Keep [.x17,.x7] a b ∧ b.mem=a.mem ∧ Prepared b u ∧ LowSetup (arg32 s .x5) b u ∧
        Keep entryRegs s t ∧
        let d := lowPassData (arg32 s .x5) (s.gpr .x4) (s.gpr .x2) (s.gpr .x3) (lowConstantsAt u) (dataAt u) 8
        t.mem=d.mem ∧ t.gpr .x0=dataReturn .r0 d := by
  change WP isa (.seq (.block pro) (VG.Impl.MlDsa.AArch64.Round.zext .x17
    (VG.Impl.MlDsa.AArch64.Round.onGamma .x17 .x7 kernelPaired))) s _
  refine WP.seq (WP.mono (prolog_ok s ha.save) fun a ⟨hk,args,hta,_,hs,hframe⟩ => ?_)
  have hga : arg32 a .x17=arg32 s .x5 := by unfold arg32; rw [args.gamma]
  apply zext_ok
  have hz := zextS_keep .x17 a
  refine onGamma_ok (by decide) (by rw [zextS_toNat,hga]; exact hg) fun g hge b hkb hmb => ?_
  have he : g=arg32 s .x5 := by rw [zextS_toNat,hga] at hge; exact hge.symm
  rw [he]
  have hb : Keep [.x17,.x7] a b := (hz.trans hkb).mono
  have hbm : b.mem=a.mem := hmb.trans (zextS_mem _ _)
  have ht' : PairedTable.Words b.mem (b.gpr .x1) := by
    rw [hbm,hb.get .x1 (by decide),hta]
    exact tableWords_frame ht hframe (by simpa only [List.mem_singleton,forall_eq] using hds)
  have hs' : Saved b.mem (b.gpr .x0) s.v := by
    rw [hbm,hb.get .x0 (by decide),args.work]; exact hs
  refine WP.mono (pairedLowKernel_ok _ hg (CallFrame.ofKeepWide (hk.trans hb)) hs'
    ((ha.kernel hk args hta).gamma hb) ht' ?_ ?_ ?_ ?_ ?_ ?_)
    fun t ⟨u,hu,hc,hkt,hm,hv⟩ => ?_
  · simpa only [hb.get .x1 (by decide),hb.get .x0 (by decide),hta,args.work] using hdw
  · simpa only [hb.get .x1 (by decide),hb.get .x15 (by decide),hta,args.data] using hdd
  · simpa only [hb.get .x0 (by decide),hb.get .x15 (by decide),args.work,args.data] using hsd
  · simpa only [hb.get .x1 (by decide),hb.get .x16 (by decide),hta,args.aux] using hda
  · simpa only [hb.get .x0 (by decide),hb.get .x16 (by decide),args.work,args.aux] using hsa
  · simpa only [hb.wr,hk.wr,hb.get .x16 (by decide),args.aux] using haw
  · refine ⟨a,b,u,args,hframe,hb,hbm,hu,hc,hkt.mono (by decide),?_,?_⟩
    · simpa only [hb.get .x0 (by decide),hb.get .x15 (by decide),hb.get .x16 (by decide),args.work,args.data,args.aux] using hm
    · simpa only [hb.get .x0 (by decide),hb.get .x15 (by decide),hb.get .x16 (by decide),args.work,args.data,args.aux] using hv

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowSpecPre` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

structure LowSpecPre (s : State) : Prop where
  rd : s.rd=[⟨s.gpr .x0,1024⟩,⟨s.gpr .x1,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]
  wr : s.wr=[⟨s.gpr .x2,2048⟩,⟨s.gpr .x3,2048⟩,⟨s.gpr .x4,2176⟩]
  table : PairedTable.Artifact s.mem (s.syms "VG_MLDSA_INV_PAIR")
  tableSep : ∀r∈s.wr,(⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint r
  commonData : (⟨s.gpr .x0,1024⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩
  commonAux : (⟨s.gpr .x0,1024⟩:Region).Disjoint ⟨s.gpr .x3,2048⟩
  commonWork : (⟨s.gpr .x0,1024⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  secretData : (⟨s.gpr .x1,2048⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩
  secretAux : (⟨s.gpr .x1,2048⟩:Region).Disjoint ⟨s.gpr .x3,2048⟩
  secretWork : (⟨s.gpr .x1,2048⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  dataAux : (⟨s.gpr .x2,2048⟩:Region).Disjoint ⟨s.gpr .x3,2048⟩
  dataWork : (⟨s.gpr .x2,2048⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  auxWork : (⟨s.gpr .x3,2048⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  products : pairedProductsReduced s.mem (s.gpr .x0) (s.gpr .x1)
  data : ∀j<2,Reduced s.mem (pairPolyPtr (s.gpr .x2) j)
  gamma : ((s.gpr .x5).setWidth 32).toNat∈gamma2s
  boundLow : 1≤((s.gpr .x6).setWidth 32).toNat
  boundHigh : ((s.gpr .x6).setWidth 32).toNat≤524288
  tableAl : (s.syms "VG_MLDSA_INV_PAIR").toNat%64=0

theorem pairedLow_pre {s : State}
    (h : (pairedLowContract (abi.withConsts pairedConsts)).pre s) : LowSpecPre s := by
  sig_pre [pairedLowContract,pairedLowSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow] at h
  obtain ⟨hdrop,hheld,_,hsep,hal,htake,hwr,hcd,hca,hcw,hsd,hsa,hsw,hda,hdw,haw,_,_,_,_,_,hprod,hdata,hgamma,hbl,hbh⟩ := h
  refine ⟨?_,hwr,?_,hsep,hcd,hca,hcw,hsd,hsa,hsw,hda,hdw,haw,hprod,hdata,hgamma,hbl,hbh,hal⟩
  · rw [←List.take_append_drop (s.rd.length-1) s.rd,htake,hdrop]
    rfl
  · intro i hi
    refine (hheld i hi).trans ?_
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [PairedTable.expandedWords_length]; exact hi),
      Option.getD_some,getElem!_pos _ _ (by rw [PairedTable.expandedWords_length]; exact hi)]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowAccess` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

private theorem accessRegion {p : Addr} {len : Nat} {rs : List Region}
    (h : (⟨p,len⟩:Region)∈rs) {off : Nat} (ho : off+16≤len) (hl : len<2^64) :
    InRegions rs (p+BitVec.ofNat 64 off) 16 :=
  ⟨_,h,Offset.contains_base p ho (by omega_arith)⟩

theorem LowSpecPre.access {s : State} (h : LowSpecPre s) : EntryAccess s := by
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

theorem pairedLow_machine {s : State} (h : LowSpecPre s) :
    WP isa (selected .r0) s fun t =>
      ∃a b u,Arguments s a ∧ Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem a.mem ∧
        Keep [.x17,.x7] a b ∧ b.mem=a.mem ∧ Prepared b u ∧ LowSetup (Round.arg32 s .x5) b u ∧
        Keep entryRegs s t ∧
        let d := lowPassData (Round.arg32 s .x5) (s.gpr .x4) (s.gpr .x2) (s.gpr .x3) (lowConstantsAt u) (dataAt u) 8
        t.mem=d.mem ∧ t.gpr .x0=dataReturn .r0 d := by
  have htw := h.tableSep (⟨s.gpr .x4,2176⟩:Region) (by rw [h.wr]; simp)
  have htd := h.tableSep (⟨s.gpr .x2,2048⟩:Region) (by rw [h.wr]; simp)
  have hta := h.tableSep (⟨s.gpr .x3,2048⟩:Region) (by rw [h.wr]; simp)
  refine selected_low_ok ?_ h.access h.table.words
    (htw.sub_right (Region.sub_prefix (by decide)))
    (htw.sub_right (Offset.sub_base _ (by decide))) htd
    (h.dataWork.symm.sub_left (Offset.sub_base _ (by decide))) hta
    (h.auxWork.symm.sub_left (Offset.sub_base _ (by decide))) ?_
  · simpa [or_comm,VG.Proof.MlDsa.gamma2s,Round.IsG,VG.Impl.MlDsa.AArch64.Round.g32,VG.Impl.MlDsa.AArch64.Round.g88,Round.arg32] using h.gamma
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowRunHigh` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowHighOutput_read_eq (g : Nat) {m m' : Mem} (out : Addr) (raw : BitVec 128)
    (hm : m'.read out 16=m.read out 16) : lowHighOutput g m' out raw=lowHighOutput g m out raw := by
  simp only [lowHighOutput,lowInputValues,hm]

/-- Every pair's high output uses its original input, regardless of its position. -/
theorem lowRun_read_high (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (i : LowIndex) (h : Fin 2)
    (hi : i∈is) (hn : is.Nodup) (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowRun g v out aux c d is).mem.read (lowAddr out i h) 16=
      lowHighOutput g d.mem (lowAddr out i h) (lowHalfValue v i h) := by
  induction is generalizing d with
  | nil => simp at hi
  | cons j is ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases he : j=i
    · subst j
      rw [lowRun,lowRun_read_slot_other _ _ _ _ _ _ _ _ _ hn'.1 hd]
      exact lowPair_read_high _ _ _ _ _ _ _ _ hd
    · have hit : i∈is := (List.mem_cons.mp hi).resolve_left (Ne.symm he)
      rw [lowRun,ih _ hit hn'.2]
      exact lowHighOutput_read_eq _ _ _ (lowPair_other_input g v out aux c d (Ne.symm he) h hd)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowRunLow` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowRun_read_aux_other (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (i : LowIndex) (h : Fin 2)
    (hn : i∉is) (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowRun g v out aux c d is).mem.read (lowAddr aux i h) 16=d.mem.read (lowAddr aux i h) 16 := by
  apply lowRun_read_other
  intro j hj
  have hnij : i≠j := by intro he; subst j; exact hn hj
  have h0 := hd.symm.sep (lowAddr_contains_base aux i h) (lowAddr_contains_base out j 0)
  have h1 := hd.symm.sep (lowAddr_contains_base aux i h) (lowAddr_contains_base out j 1)
  have h2 := lowAddr_sep (h:=h) (k:=0) aux (Or.inl hnij)
  have h3 := lowAddr_sep (h:=h) (k:=1) aux (Or.inl hnij)
  simpa only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] using
    And.intro h0 (And.intro h1 (And.intro h2 h3))

theorem lowLowOutput_read_eq (g : Nat) {m m' : Mem} (out : Addr) (raw : BitVec 128) (c : LowConstants)
    (hm : m'.read out 16=m.read out 16) : lowLowOutput g m' out raw c=lowLowOutput g m out raw c := by
  simp only [lowLowOutput,lowInputValues,hm]

/-- Every pair's signed low output uses its original input, including rejection. -/
theorem lowRun_read_low (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (i : LowIndex) (h : Fin 2)
    (hi : i∈is) (hn : is.Nodup) (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowRun g v out aux c d is).mem.read (lowAddr aux i h) 16=
      lowLowOutput g d.mem (lowAddr out i h) (lowHalfValue v i h) c := by
  induction is generalizing d with
  | nil => simp at hi
  | cons j is ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases he : j=i
    · subst j
      rw [lowRun,lowRun_read_aux_other _ _ _ _ _ _ _ _ _ hn'.1 hd]
      exact lowPair_read_low _ _ _ _ _ _ _ _
    · have hit : i∈is := (List.mem_cons.mp hi).resolve_left (Ne.symm he)
      rw [lowRun,ih _ hit hn'.2]
      exact lowLowOutput_read_eq _ _ _ _ (lowPair_other_input g v out aux c d (Ne.symm he) h hd)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowPassHigh` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem shifted_disjoint (out aux : Addr) (d : Addr)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (⟨out+d,2048⟩ : Region).Disjoint ⟨aux+d,2048⟩ := by
  intro a hx hy
  exact hd (a-d)
    (by simpa only [Region.Contains,BitVec.sub_sub,BitVec.add_comm] using hx)
    (by simpa only [Region.Contains,BitVec.sub_sub,BitVec.add_comm] using hy)

/-- The complete r0 pass writes the original-input high result at every slot. -/
theorem lowPass_read_high (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) {n k : Nat} (hn : n≤8) (hk : k<n) (i : LowIndex) (h : Fin 2)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowPassData g work out aux c d n).mem.read (lowAddr (out+BitVec.ofNat 64 (16*k)) i h) 16=
      lowHighOutput g d.mem (lowAddr (out+BitVec.ofNat 64 (16*k)) i h)
        (lowHalfValue (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*k)) 128 p)) i h) := by
  induction n with
  | zero => omega_arith
  | succ n ih =>
    by_cases he : k=n
    · subst k
      rw [lowPass_step g work out aux c d (by omega_arith) ho ha,
        lowRun_read_high _ _ _ _ _ _ _ _ _ (allLow_mem i) allLow_nodup (shifted_disjoint out aux _ hd)]
      exact lowHighOutput_read_eq _ _ _
        (lowPass_read_future g work out aux c d (Nat.le_refl n) (by omega_arith) i h hd)
    · rw [lowPassData,lowRun_read_other _ _ _ _ _ _ _ _ ?_]
      · exact ih (by omega_arith) (by omega_arith)
      · intro j _
        have h0 := lowSlice_sep out (by omega_arith : n<8) (by omega_arith : k<8) he i j h 0
        have h1 := lowSlice_sep out (by omega_arith : n<8) (by omega_arith : k<8) he i j h 1
        have h2 := hd.sep (lowAddr_contains out (by omega_arith : k<8) i h) (lowAddr_contains aux (by omega_arith : n<8) j 0)
        have h3 := hd.sep (lowAddr_contains out (by omega_arith : k<8) i h) (lowAddr_contains aux (by omega_arith : n<8) j 1)
        simpa only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] using
          And.intro h0 (And.intro h1 (And.intro h2 h3))

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowPassLow` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- The complete r0 pass writes the original-input signed low result at every slot. -/
theorem lowPass_read_low (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) {n k : Nat} (hn : n≤8) (hk : k<n) (i : LowIndex) (h : Fin 2)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowPassData g work out aux c d n).mem.read (lowAddr (aux+BitVec.ofNat 64 (16*k)) i h) 16=
      lowLowOutput g d.mem (lowAddr (out+BitVec.ofNat 64 (16*k)) i h)
        (lowHalfValue (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*k)) 128 p)) i h) c := by
  induction n with
  | zero => omega_arith
  | succ n ih =>
    by_cases he : k=n
    · subst k
      rw [lowPass_step g work out aux c d (by omega_arith) ho ha,
        lowRun_read_low _ _ _ _ _ _ _ _ _ (allLow_mem i) allLow_nodup (shifted_disjoint out aux _ hd)]
      exact lowLowOutput_read_eq _ _ _ _
        (lowPass_read_future g work out aux c d (Nat.le_refl n) (by omega_arith) i h hd)
    · rw [lowPassData,lowRun_read_other _ _ _ _ _ _ _ _ ?_]
      · exact ih (by omega_arith) (by omega_arith)
      · intro j _
        have h0 := hd.symm.sep (lowAddr_contains aux (by omega_arith : k<8) i h) (lowAddr_contains out (by omega_arith : n<8) j 0)
        have h1 := hd.symm.sep (lowAddr_contains aux (by omega_arith : k<8) i h) (lowAddr_contains out (by omega_arith : n<8) j 1)
        have h2 := lowSlice_sep aux (by omega_arith : n<8) (by omega_arith : k<8) he i j h 0
        have h3 := lowSlice_sep aux (by omega_arith : n<8) (by omega_arith : k<8) he i j h 1
        simpa only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] using
          And.intro h0 (And.intro h1 (And.intro h2 h3))

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowCoordinates` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

def lowCoeff (u : Nat) (i : LowIndex) (h : Fin 2) (e : Nat) : Nat :=
  4*u+64*i.2.val+32*h.val+e

theorem lowCoeff_lt {u e : Nat} (hu : u<8) (he : e<4) (i : LowIndex) (h : Fin 2) :
    lowCoeff u i h e<n := by unfold lowCoeff n; omega_arith

/-- The paired strided vector lane names exactly its contiguous polynomial coefficient. -/
theorem lowAddr_coeff (m : Mem) (base : Addr) (u : Nat) (i : LowIndex) (h : Fin 2)
    {e : Nat} (he : e<4) :
    vword (m.read (lowAddr (base+BitVec.ofNat 64 (16*u)) i h) 16) e=
      coeffAt m (base+BitVec.ofNat 64 (1024*i.1.val)) (lowCoeff u i h e) := by
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he]
  simp only [lowAddr,lowOff,lowCoeff,coeffAt,BitVec.add_assoc,←BitVec.ofNat_add]
  rw [show 16*u+(1024*i.1.val+256*i.2.val+128*h.val)+4*e=
    1024*i.1.val+4*(4*u+64*i.2.val+32*h.val+e) by omega_arith]

theorem lowCoeff_rawIndex (u : Nat) (i : LowIndex) (h : Fin 2) (e : Nat) :
    4*u+32*(2*i.2.val+h.val)+e=lowCoeff u i h e := by unfold lowCoeff; omega_arith

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowSemantics` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

/-- Exact high part for signed raw inverse outputs, before any memory framing. -/
theorem subHighReduced_spec {g : Nat} (hg : IsG g) {a b : BitVec 32}
    (ha : a.toNat<Spec.MlDsa.q) (bl : -8380417<b.toInt) (bh : b.toInt<2*8380417) :
    (lowHighWord g (Inverse.signCorrected (Response.reduceWord (a-b)))).toNat=
      (highBits g (ofInt ((a.toNat:Int)-b.toInt))).toNat := by
  have hc := Response.subInput_word ha bl bh
  have cb : (Inverse.signCorrected (Response.reduceWord (a-b))).toNat<Spec.MlDsa.q := by
    rw [hc]; exact (ofInt ((a.toNat:Int)-b.toInt)).isLt
  rw [lowHighWord_eq hg cb]
  exact Response.subHigh_word hg ha bl bh

/-- The paired rejection flag uses the same strict norm bound as the specification. -/
theorem subLowReduced_norm {g B : Nat} (hg : IsG g) {a b : BitVec 32}
    (ha : a.toNat<Spec.MlDsa.q) (bl : -8380417<b.toInt) (bh : b.toInt<2*8380417)
    (hB : 1≤B) (hB' : B≤524288) :
    let c := Inverse.signCorrected (Response.reduceWord (a-b))
    Response.normMask (Response.reduceWord (c-lowHighWord g c*BitVec.ofNat 32 (2*g)))
      (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1))=
      if normZq (ofInt (lowBits g (ofInt ((a.toNat:Int)-b.toInt))))<B then 0 else -1 := by
  dsimp only
  have hc := Response.subInput_word ha bl bh
  have cb : (Inverse.signCorrected (Response.reduceWord (a-b))).toNat<Spec.MlDsa.q := by
    rw [hc]; exact (ofInt ((a.toNat:Int)-b.toInt)).isLt
  rw [lowReduced_eq hg cb]
  exact Response.subLow_norm hg ha bl bh hB hB'

def lowInputField (m : Mem) (addr : Addr) (raw : BitVec 128) (e : Nat) : Zq :=
 ofInt (((vword (m.read addr 16) e).toNat:Int)-(vword raw e).toInt)

theorem lowInputValues_high {g : Nat} (hg : IsG g) {m : Mem} {addr : Addr} {raw : BitVec 128} {e : Nat}
    (ha : (vword (m.read addr 16) e).toNat<Spec.MlDsa.q)
    (bl : -8380417<(vword raw e).toInt) (bh : (vword raw e).toInt<2*8380417) :
    (lowHighWord g (lowInputValues m addr raw e)).toNat=(highBits g (lowInputField m addr raw e)).toNat :=
  subHighReduced_spec hg ha bl bh

theorem lowInputValues_low {g : Nat} (hg : IsG g) {m : Mem} {addr : Addr} {raw : BitVec 128} {e : Nat}
    (ha : (vword (m.read addr 16) e).toNat<Spec.MlDsa.q)
    (bl : -8380417<(vword raw e).toInt) (bh : (vword raw e).toInt<2*8380417) :
    let a := lowInputValues m addr raw e
    (Response.reduceWord (a-lowHighWord g a*BitVec.ofNat 32 (2*g))).toInt=
      lowBits g (lowInputField m addr raw e) :=
  subLowReduced_spec hg ha bl bh

theorem lowInputValues_norm {g B : Nat} (hg : IsG g) {m : Mem} {addr : Addr} {raw : BitVec 128} {e : Nat}
    (ha : (vword (m.read addr 16) e).toNat<Spec.MlDsa.q)
    (bl : -8380417<(vword raw e).toInt) (bh : (vword raw e).toInt<2*8380417)
    (hB : 1≤B) (hB' : B≤524288) :
    let a := lowInputValues m addr raw e
    Response.normMask (Response.reduceWord (a-lowHighWord g a*BitVec.ofNat 32 (2*g)))
      (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1))=
      if normZq (ofInt (lowBits g (lowInputField m addr raw e)))<B then 0 else -1 :=
  subLowReduced_norm hg ha bl bh hB hB'
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowFieldValues` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Optimized.Response

/-- Each high output is the specification's decomposition of the difference. -/
theorem lowHighOutput_field {g : Nat} (hg : IsG g) {m : Mem} {out : Addr} {raw : BitVec 128}
    {e : Nat} (he : e<4) (ha : (vword (m.read out 16) e).toNat<q)
    (hb : -8380417<(vword raw e).toInt ∧ (vword raw e).toInt<2*8380417) :
    (vword (lowHighOutput g m out raw) e).toNat=(highBits g (lowInputField m out raw e)).toNat := by
  rw [lowHighOutput,laneVector_word _ he]
  exact lowInputValues_high hg ha hb.1 hb.2

/-- Each low output has the exact signed low-bits representative, on all paths. -/
theorem lowLowOutput_field {g : Nat} (hg : IsG g) {m : Mem} {out : Addr} {raw : BitVec 128}
    {c : LowConstants} {e : Nat} (he : e<4) (hs : vword c.scale e=BitVec.ofNat 32 (2*g))
    (ha : (vword (m.read out 16) e).toNat<q)
    (hb : -8380417<(vword raw e).toInt ∧ (vword raw e).toInt<2*8380417) :
    (vword (lowLowOutput g m out raw c) e).toInt=lowBits g (lowInputField m out raw e) := by
  rw [lowLowOutput,laneVector_word _ he,hs]
  exact lowInputValues_low hg ha hb.1 hb.2

/-- The r0 machine mask is zero exactly when the strict low-bits norm passes. -/
theorem lowMask_zero {g B : Nat} (hg : IsG g) {m : Mem} {out : Addr} {raw : BitVec 128}
    {c : LowConstants} {e : Nat}
    (hs : vword c.scale e=BitVec.ofNat 32 (2*g))
    (hl : vword c.lower e=BitVec.ofNat 32 (B-1))
    (hw : vword c.width e=BitVec.ofNat 32 (2*B-1))
    (ha : (vword (m.read out 16) e).toNat<q)
    (hb : -8380417<(vword raw e).toInt ∧ (vword raw e).toInt<2*8380417)
    (hB : 1≤B) (hB' : B≤524288) :
    lowMask g m out raw c e=0 ↔ normZq (ofInt (lowBits g (lowInputField m out raw e)))<B := by
  rw [lowMask,hs,hl,hw,lowInputValues_norm hg ha hb.1 hb.2 hB hB']
  split
  · rename_i h
    exact ⟨fun _ => h,fun _ => rfl⟩
  · rename_i h
    exact ⟨fun hz => False.elim ((by decide : (-1 : BitVec 32)≠0) hz),fun hx => False.elim (h hx)⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowDifference` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- A raw inverse lane subtracts to exactly the shared paired difference. -/
theorem lowInputField_difference (m : Mem) (challenge secret out : Addr)
    {u e : Nat} (hu : u<8) (he : e<4) (i : LowIndex) (h : Fin 2) (raw : BitVec 128)
    (hr : ofInt (vword raw e).toInt=(pairedProduct m challenge secret i.1.val)[lowCoeff u i h e]!) :
    lowInputField m (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) raw e=
      (pairedDifference m challenge secret out i.1.val)[lowCoeff u i h e]! := by
  have hk := lowCoeff_lt hu he i h
  rw [lowInputField,lowAddr_coeff _ _ _ _ _ he,ofInt_sub,ofInt_nat_eq,
    ←polyAt_get _ _ hk,hr,pairedDifference,sub_get _ _ hk]
  rfl

/-- The raw paired inverse lane has the shared product value and strict range. -/
theorem lowHalf_raw_field {m : Mem} {work challenge secret : Addr} {u e : Nat}
    (hu : u<8) (he : e<4) (i : LowIndex) (h : Fin 2)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (hp : pairedProductsReduced m challenge secret) :
    let raw := lowHalfValue (fun p => Inverse.rawFinalValues
      (readPair (firstPassMem m work challenge secret 8) (work+BitVec.ofNat 64 (16*u)) 128 p)) i h;
    -8380417<(vword raw e).toInt ∧ (vword raw e).toInt<2*8380417 ∧
      ofInt (vword raw e).toInt=(pairedProduct m challenge secret i.1.val)[lowCoeff u i h e]! := by
  have hv := rawFinal_field hu hc hs i.1 (Inverse.positiveReduced_is hp.1)
    (Inverse.positiveReduced_is (hp.2 i.1.val i.1.isLt))
    ⟨2*i.2.val+h.val,by omega_arith⟩ he
  simpa only [lowHalfValue,pairedProduct,pairPolyPtr,lowCoeff_rawIndex] using hv

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowFirstFrame` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

theorem firstPass_lowInput_read {m : Mem} {work challenge secret out : Addr} {u : Nat}
    (hu : u<8) (i : LowIndex) (h : Fin 2)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨work,2048⟩) :
    (firstPassMem m work challenge secret 8).read (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) 16=
      m.read (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) 16 := by
  exact (firstPass_frame (m:=m) (a:=challenge) (b:=secret) (by decide : 8≤8)).read
    (lowAddr_contains out hu i h)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

theorem firstPass_lowInputField {m : Mem} {work challenge secret out : Addr} {u : Nat}
    (hu : u<8) (i : LowIndex) (h : Fin 2) (raw : BitVec 128) (e : Nat)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨work,2048⟩) :
    lowInputField (firstPassMem m work challenge secret 8) (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) raw e=
      lowInputField m (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) raw e := by
  rw [lowInputField,firstPass_lowInput_read hu i h hd]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowLaneField` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

/-- Exact high and low field values after the initial inverse pass. -/
theorem lowLane_field {m : Mem} {work challenge secret out : Addr} {u e g : Nat}
    (hu : u<8) (he : e<4) (hg : IsG g) (i : LowIndex) (h : Fin 2) (c : LowConstants)
    (hscale : vword c.scale e=BitVec.ofNat 32 (2*g))
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨out,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) :
    let mem := firstPassMem m work challenge secret 8
    let addr := lowAddr (out+BitVec.ofNat 64 (16*u)) i h
    let raw := lowHalfValue (fun p => Inverse.rawFinalValues (readPair mem (work+BitVec.ofNat 64 (16*u)) 128 p)) i h
    (vword (lowHighOutput g mem addr raw) e).toNat=
        (highBits g (pairedDifference m challenge secret out i.1.val)[lowCoeff u i h e]!).toNat ∧
      (vword (lowLowOutput g mem addr raw c) e).toInt=
        lowBits g (pairedDifference m challenge secret out i.1.val)[lowCoeff u i h e]! := by
  dsimp only
  have hr := lowHalf_raw_field hu he i h hc hs hp
  have hb : (vword ((firstPassMem m work challenge secret 8).read
      (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) 16) e).toNat<q := by
    rw [firstPass_lowInput_read hu i h ho,lowAddr_coeff _ _ _ _ _ he]
    exact hy i.1.val i.1.isLt _ (lowCoeff_lt hu he i h)
  have hv := lowInputField_difference m challenge secret out hu he i h _ hr.2.2
  constructor
  · rw [lowHighOutput_field hg he hb ⟨hr.1,hr.2.1⟩,firstPass_lowInputField hu i h _ e ho,hv]
  · rw [lowLowOutput_field hg he hscale hb ⟨hr.1,hr.2.1⟩,firstPass_lowInputField hu i h _ e ho,hv]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowStoredField` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem lowPass_stored_field {m : Mem} {work challenge secret out aux : Addr} {u e g : Nat}
    (hu : u<8) (he : e<4) (hg : IsG g) (i : LowIndex) (h : Fin 2) (c : LowConstants)
    (hscale : vword c.scale e=BitVec.ofNat 32 (2*g))
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (flags count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,count⟩
    let result := (lowPassData g work out aux c d 8).mem
    (coeffAt result (pairPolyPtr out i.1.val) (lowCoeff u i h e)).toNat=
        (highBits g (pairedDifference m challenge secret out i.1.val)[lowCoeff u i h e]!).toNat ∧
      (coeffAt result (pairPolyPtr aux i.1.val) (lowCoeff u i h e)).toInt=
        lowBits g (pairedDifference m challenge secret out i.1.val)[lowCoeff u i h e]! := by
  dsimp only
  have hv := lowLane_field hu he hg i h c hscale hc hs ho.symm hp hy
  constructor
  · rw [pairPolyPtr,←lowAddr_coeff _ out u i h he,
      lowPass_read_high g work out aux c _ (by decide : 8≤8) hu i h ho ha hd]
    exact hv.1
  · rw [pairPolyPtr,←lowAddr_coeff _ aux u i h he,
      lowPass_read_low g work out aux c _ (by decide : 8≤8) hu i h ho ha hd]
    exact hv.2

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

end


/-! ## `PairedLowAllFields` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem lowPass_all_fields {m : Mem} {work challenge secret out aux : Addr} {g : Nat}
    (hg : IsG g) (c : LowConstants)
    (hscale : ∀e<4,vword c.scale e=BitVec.ofNat 32 (2*g))
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (flags count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,count⟩
    let result := (lowPassData g work out aux c d 8).mem
    ∀j<2,∀k<n,
      (coeffAt result (pairPolyPtr out j) k).toNat=
          (highBits g (pairedDifference m challenge secret out j)[k]!).toNat ∧
        (coeffAt result (pairPolyPtr aux j) k).toInt=
          lowBits g (pairedDifference m challenge secret out j)[k]! := by
  dsimp only
  intro j hj k hk
  have hkn : k<256 := hk
  have hu : k%32/4<8 := by omega_using []
  have hi : k/64<4 := by omega_using [hkn]
  have hh : k%64/32<2 := by omega_using []
  have he : k%4<4 := by omega_using []
  have hv := lowPass_stored_field hu he hg (⟨j,hj⟩,⟨k/64,hi⟩) ⟨k%64/32,hh⟩ c
    (hscale _ he) hc hs ho ha hd hp hy flags count
  have hidx : lowCoeff (k%32/4) (⟨j,hj⟩,⟨k/64,hi⟩) ⟨k%64/32,hh⟩ (k%4)=k := by
    change 4*(k%32/4)+64*(k/64)+32*(k%64/32)+k%4=k
    have hm : k%64%32=k%32 := Nat.mod_mod_of_dvd k (by decide : 32∣64)
    have hm4 : k%32%4=k%4 := Nat.mod_mod_of_dvd k (by decide : 4∣32)
    omega_using []
  simpa only [hidx] using hv

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowContractTiming` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedLow_public {s t : State}
    (h : (pairedLowContract (abi.withConsts pairedConsts)).pub s t) : WordPublic s t := by
  sig_pub [pairedLowContract,pairedLowSig,abi,argRegs,Abi.withConsts,pairedConsts_eq] at h
  obtain ⟨hsp,htable,h0,h1,h2,h3,h4,h5⟩ := h
  refine ⟨hsp,?_,h5,htable⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl <;> with_reducible assumption

theorem pairedLow_contract_ct : ConstantTime isa
    (pairedLowContract (abi.withConsts pairedConsts)).pre
    (pairedLowContract (abi.withConsts pairedConsts)).pub (selected .r0) := by
  intro s t tr1 tr2 s' t' hs ht hp he hf
  exact r0_word_ct s t tr1 tr2 s' t' (pairedLow_pre hs).access (pairedLow_pre ht).access
    (pairedLow_public hp) he hf

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowEntryFrame` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

structure LowEntryFrame (s : State) (m : Mem) : Prop where
  products : pairedProductsReduced m (s.gpr .x0) (s.gpr .x1)
  data : ∀j<2,Reduced m (pairPolyPtr (s.gpr .x2) j)
  difference : ∀j<2,pairedDifference m (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j=
    pairedDifference s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j

theorem lowEntry_frame {s : State} {m : Mem} (h : LowSpecPre s)
    (hf : Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem m) : LowEntryFrame s m := by
  have hc : ∀r∈[⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩],(⟨s.gpr .x0,1024⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.commonWork.sub_right (Offset.sub_base _ (by decide))
  have hs : ∀r∈[⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩],(⟨s.gpr .x1,2048⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.secretWork.sub_right (Offset.sub_base _ (by decide))
  have ho : ∀r∈[⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩],(⟨s.gpr .x2,2048⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.dataWork.sub_right (Offset.sub_base _ (by decide))
  refine ⟨pairedProductsReduced_frame hf hc hs h.products,?_,fun j hj => pairedDifference_frame hf hc hs ho hj⟩
  intro j hj
  apply VG.Proof.MlDsa.Verify.reduced_frame hf _ (h.data j hj)
  intro r hr
  exact (ho r hr).sub_left (Offset.sub_base _ (by omega_using [hj]))

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowCoverage` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.Spec.MlDsa

/-- The paired SIMD traversal covers exactly all coefficients of both polynomials. -/
theorem lowCoverage (P : Nat → Nat → Prop) :
    (∀e<4,∀u<8,∀i:LowIndex,∀h:Fin 2,P i.1.val (lowCoeff u i h e)) ↔
      ∀j<2,∀k<n,P j k := by
  constructor
  · intro hall j hj k hk
    have hkn : k<256 := hk
    have hu : k%32/4<8 := by omega_using []
    have hi : k/64<4 := by omega_using [hkn]
    have hh : k%64/32<2 := by omega_using []
    have he : k%4<4 := by omega_using []
    have hv := hall _ he _ hu (⟨j,hj⟩,⟨k/64,hi⟩) ⟨k%64/32,hh⟩
    have hidx : lowCoeff (k%32/4) (⟨j,hj⟩,⟨k/64,hi⟩) ⟨k%64/32,hh⟩ (k%4)=k := by
      change 4*(k%32/4)+64*(k/64)+32*(k%64/32)+k%4=k
      have hm : k%64%32=k%32 := Nat.mod_mod_of_dvd k (by decide : 32∣64)
      have hm4 : k%32%4=k%4 := Nat.mod_mod_of_dvd k (by decide : 4∣32)
      omega_using []
    simpa only [hidx] using hv
  · intro hall e he u hu i h
    exact hall i.1.val i.1.isLt _ (lowCoeff_lt hu he i h)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowLaneNorm` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem lowLane_norm {m : Mem} {work challenge secret out : Addr} {u e g B : Nat}
    (hu : u<8) (he : e<4) (hg : IsG g) (i : LowIndex) (h : Fin 2) (c : LowConstants)
    (hscale : vword c.scale e=BitVec.ofNat 32 (2*g))
    (hlower : vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨out,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) :
    let mem := firstPassMem m work challenge secret 8
    let addr := lowAddr (out+BitVec.ofNat 64 (16*u)) i h
    let raw := lowHalfValue (fun p => Inverse.rawFinalValues (readPair mem (work+BitVec.ofNat 64 (16*u)) 128 p)) i h
    lowMask g mem addr raw c e=0 ↔
      normZq (ofInt (lowBits g (pairedDifference m challenge secret out i.1.val)[lowCoeff u i h e]!))<B := by
  dsimp only
  have hr := lowHalf_raw_field hu he i h hc hs hp
  have hb : (vword ((firstPassMem m work challenge secret 8).read
      (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) 16) e).toNat<q := by
    rw [firstPass_lowInput_read hu i h ho,lowAddr_coeff _ _ _ _ _ he]
    exact hy i.1.val i.1.isLt _ (lowCoeff_lt hu he i h)
  have hv := lowInputField_difference m challenge secret out hu he i h _ hr.2.2
  rw [lowMask_zero hg hscale hlower hwidth hb ⟨hr.1,hr.2.1⟩ hB hB',
    firstPass_lowInputField hu i h _ e ho,hv]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowNormRq` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- The shared paired norm is exactly the strict low-bits check on all coefficients. -/
theorem pairedLow_norm_iff (m : Mem) (challenge secret out : Addr) (g B : Nat) (hB : 0<B) :
    normRq ((List.range 2).map fun j => pairedLowPoly g (pairedDifference m challenge secret out j))<B ↔
      ∀j<2,∀k<n,normZq (ofInt (lowBits g (pairedDifference m challenge secret out j)[k]!))<B := by
  rw [VG.Proof.MlDsa.Sign.normRq_lt_iff _ hB]
  simp only [List.forall_mem_map,List.mem_range]
  apply forall_congr'
  intro j
  apply forall_congr'
  intro _
  rw [VG.Proof.MlDsa.Round.normRq_lt]
  apply forall_congr'
  intro k
  apply forall_congr'
  intro hk
  rw [pairedLowPoly,getElem!_eq _ hk,Vector.getElem_map,getElem!_eq _ hk]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowNormComplete` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem lowPass_norm_complete {m : Mem} {work challenge secret out aux : Addr} {g B : Nat}
    (hg : IsG g) (c : LowConstants)
    (hscale : ∀e<4,vword c.scale e=BitVec.ofNat 32 (2*g))
    (hlower : ∀e<4,vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : ∀e<4,vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,0,count⟩
    (∀e<4,vword (lowPassData g work out aux c d 8).flags e=0) ↔
      normRq ((List.range 2).map fun j => pairedLowPoly g (pairedDifference m challenge secret out j))<B := by
  dsimp only
  rw [pairedLow_norm_iff _ _ _ _ _ _ (by omega_using [hB]),←lowCoverage]
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  rw [lowPass_flag_zero_iff _ _ _ _ _ _ (by decide : 8≤8) ho ha hd he]
  have hz : vword (0 : BitVec 128) e=0 := by simp [vword]
  simp only [hz,true_and]
  apply forall_congr'
  intro u
  apply forall_congr'
  intro hu
  apply forall_congr'
  intro i
  rw [lowPassAccept,lowPairAccept_halves]
  apply forall_congr'
  intro h
  exact lowLane_norm hu he hg i h c (hscale e he) (hlower e he) (hwidth e he)
    hB hB' hc hs ho.symm hp hy

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowReturnComplete` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem lowPass_return_complete {m : Mem} {work challenge secret out aux : Addr} {g B : Nat}
    (hg : IsG g) (c : LowConstants)
    (hscale : ∀e<4,vword c.scale e=BitVec.ofNat 32 (2*g))
    (hlower : ∀e<4,vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : ∀e<4,vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,0,count⟩
    Response.finishValue (lowPassData g work out aux c d 8).flags =
      if normRq ((List.range 2).map fun j => pairedLowPoly g (pairedDifference m challenge secret out j))<B then 1 else 0 := by
  dsimp only
  have hz : FlagMasks (0 : BitVec 128) := by
    intro e he
    exact Or.inl (by simp [vword])
  rw [finishValue_accept _ (lowPass_masks _ _ _ _ _ _ _ hz)]
  have hn := lowPass_norm_complete hg c hscale hlower hwidth hB hB' hc hs ho ha hd hp hy count
  dsimp only at hn
  rw [hn]
  by_cases h : normRq ((List.range 2).map fun j => pairedLowPoly g (pairedDifference m challenge secret out j))<B
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowEntryState` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)

theorem preparedLow_data {s a b u : State} (ha : Arguments s a)
    (hk : Keep [.x17,.x7] a b) (hm : b.mem=a.mem)
    (hp : Prepared b u) (hl : LowSetup (Round.arg32 s .x5) b u) :
    dataAt u=⟨firstPassMem a.mem (s.gpr .x4) (s.gpr .x0) (s.gpr .x1) 8,0,u.v .v14⟩ := by
  unfold dataAt
  rw [hp.mem,hm,hk.get .x0 (by decide),hk.get .x13 (by decide),hk.get .x14 (by decide),
    ha.work,ha.common,ha.secret,hl.flags]

theorem bound_sub_one (w : BitVec 32) (hw : 1≤w.toNat) :
    w-1=BitVec.ofNat 32 (w.toNat-1) := by
  have h := BitVec.ofNat_sub_ofNat_of_le (w:=32) w.toNat 1 (by decide) hw
  simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.ofNat_eq_ofNat] using h

theorem bound_width (w : BitVec 32) (hw : 1≤w.toNat) :
    w+(w-1)=BitVec.ofNat 32 (2*w.toNat-1) := by
  rw [bound_sub_one w hw]
  have he : w=BitVec.ofNat 32 w.toNat := by simp
  conv => lhs; lhs; rw [he]
  rw [←BitVec.ofNat_add]
  congr 1
  omega_using []

theorem preparedLow_constants {s a b u : State} (ha : Arguments s a)
    (hk : Keep [.x17,.x7] a b) (hl : LowSetup (Round.arg32 s .x5) b u)
    (hB : 1≤Round.arg32 s .x6) :
    (∀e<4,vword (lowConstantsAt u).scale e=BitVec.ofNat 32 (2*Round.arg32 s .x5)) ∧
    (∀e<4,vword (lowConstantsAt u).lower e=BitVec.ofNat 32 (Round.arg32 s .x6-1)) ∧
    (∀e<4,vword (lowConstantsAt u).width e=BitVec.ofNat 32 (2*Round.arg32 s .x6-1)) := by
  refine ⟨hl.scale,?_,?_⟩
  · intro e he
    change vword (u.v .v9) e=_
    rw [hl.lower e he,hk.get .x8 (by decide),ha.bound]
    exact bound_sub_one _ hB
  · intro e he
    change vword (u.v .v10) e=_
    rw [hl.width e he,hk.get .x8 (by decide),ha.bound]
    exact bound_width _ hB

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowFunctional` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

structure LowResult (s t : State) : Prop where
  keep : Keep entryRegs s t
  fields : ∀j<2,∀i<n,
    (coeffAt t.mem (pairPolyPtr (s.gpr .x2) j) i).toNat=
      (highBits (Round.arg32 s .x5) (pairedDifference s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j)[i]!).toNat ∧
    (coeffAt t.mem (pairPolyPtr (s.gpr .x3) j) i).toInt=
      lowBits (Round.arg32 s .x5) (pairedDifference s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j)[i]!
  ret : t.gpr .x0=if normRq ((List.range 2).map fun j => pairedLowPoly (Round.arg32 s .x5)
    (pairedDifference s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j))<Round.arg32 s .x6 then 1 else 0

theorem pairedLow_functional {s : State} (h : LowSpecPre s) :
    WP isa (selected .r0) s (LowResult s) := by
  refine WP.mono (pairedLow_machine h) fun t ⟨a,b,u,ha,hf,hk,hm,hp,hl,ht,hmem,hret⟩ => ?_
  have hg : Round.IsG (Round.arg32 s .x5) := by
    simpa [or_comm,gamma2s,Round.IsG,VG.Impl.MlDsa.AArch64.Round.g32,
      VG.Impl.MlDsa.AArch64.Round.g88,Round.arg32] using h.gamma
  have hframe := lowEntry_frame h hf
  obtain ⟨hscale,hlower,hwidth⟩ := preparedLow_constants ha hk hl h.boundLow
  have hdata := preparedLow_data ha hk hm hp hl
  have hc := h.commonWork.sub_right (Region.sub_prefix (by decide : 2048≤2176))
  have hs := h.secretWork.sub_right (Region.sub_prefix (by decide : 2048≤2176))
  have ho := h.dataWork.symm.sub_left (Region.sub_prefix (by decide : 2048≤2176))
  have hx := h.auxWork.symm.sub_left (Region.sub_prefix (by decide : 2048≤2176))
  have hfields := lowPass_all_fields hg (lowConstantsAt u) hscale hc hs ho hx h.dataAux
    hframe.products hframe.data 0 (u.v .v14)
  have hvalue := lowPass_return_complete hg (lowConstantsAt u) hscale hlower hwidth h.boundLow h.boundHigh
    hc hs ho hx h.dataAux hframe.products hframe.data (u.v .v14)
  dsimp only at hfields hvalue
  rw [hdata] at hmem hret
  refine ⟨ht,?_,?_⟩
  · intro j hj i hi
    rw [hmem]
    have hv := hfields j hj i hi
    rw [hframe.difference j hj] at hv
    exact hv
  · change t.gpr .x0=_
    rw [hret]
    change Response.finishValue _=_
    rw [hvalue]
    have he : ((List.range 2).map fun j => pairedLowPoly (Round.arg32 s .x5)
        (pairedDifference a.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j))=
        ((List.range 2).map fun j => pairedLowPoly (Round.arg32 s .x5)
        (pairedDifference s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j)) := by
      apply List.map_congr_left
      intro j hj
      rw [hframe.difference j (List.mem_range.mp hj)]
    rw [he]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowCorrect` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedLow_post {s t : State} (h : LowResult s t) :
    (pairedLowContract (abi.withConsts pairedConsts)).post s t := by
  sig_post [pairedLowContract,pairedLowSig,abi,argRegs,Abi.withConsts,pairedConsts_eq]
  refine ⟨h.fields,?_⟩
  rw [h.ret]
  split <;> rfl

theorem pairedLow_correct (s : State)
    (h : (pairedLowContract (abi.withConsts pairedConsts)).pre s) :
    ∃tr t,Exec isa (selected .r0) s tr t ∧ abiPreserved s t ∧
      (pairedLowContract (abi.withConsts pairedConsts)).post s t := by
  obtain ⟨tr,t,he,hr⟩ := pairedLow_functional (pairedLow_pre h)
  exact ⟨tr,t,he,entryKeep_abi hr.keep,pairedLow_post hr⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowPreIntro` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedLow_pre_intro {s : State} (h : LowSpecPre s)
    (held : ∀i<512,s.mem.readW (s.syms "VG_MLDSA_INV_PAIR"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (fitTable : (s.syms "VG_MLDSA_INV_PAIR").toNat+4096≤2^64)
    (fit0 : (s.gpr .x0).toNat+1024≤2^64) (fit1 : (s.gpr .x1).toNat+2048≤2^64)
    (fit2 : (s.gpr .x2).toNat+2048≤2^64) (fit3 : (s.gpr .x3).toNat+2048≤2^64)
    (fit4 : (s.gpr .x4).toNat+2176≤2^64) :
    (pairedLowContract (abi.withConsts pairedConsts)).pre s := by
  sig_pre [pairedLowContract,pairedLowSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow]
  exact ⟨by rw [h.rd]; rfl,held,fitTable,h.tableSep,h.tableAl,by rw [h.rd]; rfl,h.wr,
    h.commonData,h.commonAux,h.commonWork,h.secretData,h.secretAux,h.secretWork,
    h.dataAux,h.dataWork,h.auxWork,fit0,fit1,fit2,fit3,fit4,h.products,h.data,h.gamma,h.boundLow,h.boundHigh⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowSat` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

def lowSatWith (m : Mem) : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 8192 else if r=.x2 then 12288
    else if r=.x3 then 16384 else if r=.x4 then 20480 else if r=.x5 then 95232
    else if r=.x6 then 1 else 0
  sp := 131072
  syms _ := 65536
  mem := m
  rd := [⟨4096,1024⟩,⟨8192,2048⟩,⟨65536,4096⟩]
  wr := [⟨12288,2048⟩,⟨16384,2048⟩,⟨20480,2176⟩]

theorem lowSatWith_pre (m : Mem)
    (held : ∀i<512,m.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (hprod : pairedProductsReduced m 4096 8192)
    (hdata : ∀j<2,Reduced m (pairPolyPtr 12288 j)) :
    (pairedLowContract (abi.withConsts pairedConsts)).pre (lowSatWith m) := by
  apply pairedLow_pre_intro (s:=lowSatWith m) ?_ held (by dsimp only [lowSatWith]; decide) (by dsimp only [lowSatWith]; decide) (by dsimp only [lowSatWith]; decide) (by dsimp only [lowSatWith]; decide) (by dsimp only [lowSatWith]; decide) (by dsimp only [lowSatWith]; decide)
  refine ⟨rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hprod,hdata,by dsimp only [lowSatWith]; decide,by dsimp only [lowSatWith]; decide,by dsimp only [lowSatWith]; decide,by dsimp only [lowSatWith]; try decide⟩
  · intro i hi
    refine (held i hi).trans ?_
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [PairedTable.expandedWords_length]; exact hi),
      Option.getD_some,getElem!_pos _ _ (by rw [PairedTable.expandedWords_length]; exact hi)]
  · intro r hr
    change r∈[⟨12288,2048⟩,⟨16384,2048⟩,⟨20480,2176⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl <;> exact Region.disjoint_of_sep (by dsimp only [lowSatWith]; decide)
  all_goals exact Region.disjoint_of_sep (by dsimp only [lowSatWith]; decide)

def lowSat : State := lowSatWith pairedSatMem

theorem pairedLow_sat : (pairedLowContract (abi.withConsts pairedConsts)).pre lowSat := by
  apply lowSatWith_pre pairedSatMem pairedSat_held
  · refine ⟨pairedSat_positive (by decide : 4096≤32768),?_⟩
    intro j hj
    change PositiveReduced pairedSatMem (8192+BitVec.ofNat 64 (1024*j))
    rw [show (8192:BitVec 64)=BitVec.ofNat 64 8192 by rfl,←BitVec.ofNat_add]
    exact pairedSat_positive (by omega_using [hj])
  · intro j hj
    change Reduced pairedSatMem (12288+BitVec.ofNat 64 (1024*j))
    rw [show (12288:BitVec 64)=BitVec.ofNat 64 12288 by rfl,←BitVec.ofNat_add]
    exact pairedSat_reduced (by omega_using [hj])

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowVerified` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

/-- Exact selected batched low-part kernel, including all-path outputs,
strict norm return, restored ABI, and the shared public-input timing policy. -/
theorem pairedLow_verified : Verified target (selected .r0)
    (pairedLowContract (abi.withConsts pairedConsts)) :=
  ⟨pairedLow_correct,pairedLow_contract_ct,⟨lowSat,pairedLow_sat⟩⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowCall` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedLow_callee (S : Nat) : CalleeOk S (selected .r0)
    (pairedLowContract (abi.withConsts pairedConsts)) :=
  CalleeOk.of_ct pairedLow_verified.1 pairedLow_verified.2.1 (by lit_decide) (fun _ _ h => h) (Nat.zero_le _)

abbrev pairedLowArgs (c secret out low work : Ptr) (g B : Nat) : List (Reg × Arg) :=
  [(.x0,.ptr c),(.x1,.ptr secret),(.x2,.ptr out),(.x3,.ptr low),(.x4,.ptr work),(.x5,.imm g),(.x6,.imm B)]

structure PairedLowReady (c secret out low work : Ptr) (g B : Nat) (s : State) : Prop where
  cFit : (pa s c).toNat+1024≤2^64
  secretFit : (pa s secret).toNat+2048≤2^64
  outFit : (pa s out).toNat+2048≤2^64
  lowFit : (pa s low).toNat+2048≤2^64
  workFit : (pa s work).toNat+2176≤2^64
  held : ∀i<512,s.mem.readW (s.syms "VG_MLDSA_INV_PAIR"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0
  tableFit : (s.syms "VG_MLDSA_INV_PAIR").toNat+4096≤2^64
  tableApart : ∀r∈[⟨pa s out,2048⟩,⟨pa s low,2048⟩,⟨pa s work,2176⟩],
    (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint r
  cOut : (⟨pa s c,1024⟩:Region).Disjoint ⟨pa s out,2048⟩
  cLow : (⟨pa s c,1024⟩:Region).Disjoint ⟨pa s low,2048⟩
  cWork : (⟨pa s c,1024⟩:Region).Disjoint ⟨pa s work,2176⟩
  secretOut : (⟨pa s secret,2048⟩:Region).Disjoint ⟨pa s out,2048⟩
  secretLow : (⟨pa s secret,2048⟩:Region).Disjoint ⟨pa s low,2048⟩
  secretWork : (⟨pa s secret,2048⟩:Region).Disjoint ⟨pa s work,2176⟩
  outLow : (⟨pa s out,2048⟩:Region).Disjoint ⟨pa s low,2048⟩
  outWork : (⟨pa s out,2048⟩:Region).Disjoint ⟨pa s work,2176⟩
  lowWork : (⟨pa s low,2048⟩:Region).Disjoint ⟨pa s work,2176⟩
  products : pairedProductsReduced s.mem (pa s c) (pa s secret)
  canonical : ∀j<2,Reduced s.mem (pairPolyPtr (pa s out) j)
  gamma : g∈gamma2s
  boundPos : 1≤B
  boundMax : B≤524288
  readable : Covers [⟨pa s c,1024⟩,⟨pa s secret,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩,
    ⟨pa s out,2048⟩,⟨pa s low,2048⟩,⟨pa s work,2176⟩] (s.rd++s.wr)
  writable : Covers [⟨pa s out,2048⟩,⟨pa s low,2048⟩,⟨pa s work,2176⟩] s.wr
  tableAligned : (s.syms "VG_MLDSA_INV_PAIR").toNat%64=0

theorem PairedLowReady.gamma_lt {c secret out low work : Ptr} {g B : Nat} {s : State}
    (h : PairedLowReady c secret out low work g B s) : g<2^32 := by
  have hg := VG.Proof.MlDsa.AArch64.Round.isG_of_mem h.gamma
  rcases hg with rfl|rfl <;> decide

theorem pairedLowAt_pre {s s1 : State} {c secret out low work : Ptr} {g B : Nat}
    (h : PairedLowReady c secret out low work g B s)
    (h1 : Args (pairedLowArgs c secret out low work g B) s s1) (hy : s1.syms=s.syms) :
    (pairedLowContract (abi.withConsts pairedConsts)).pre
      (s1.callEntry.withRegions [⟨pa s c,1024⟩,⟨pa s secret,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]
        [⟨pa s out,2048⟩,⟨pa s low,2048⟩,⟨pa s work,2176⟩]) := by
  sig_pre [pairedLowContract,pairedLowSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow]
  have h5 : s1.gpr .x5=BitVec.ofNat 64 g := h1.imm (by simp [pairedLowArgs])
  have h6 : s1.gpr .x6=BitVec.ofNat 64 B := h1.imm (by simp [pairedLowArgs])
  simp only [hy,Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.r4 h1,h5,h6,
    Args.mem h1,Arg.val]
  have hg : ((BitVec.ofNat 64 g).setWidth 32).toNat=g := by have := h.gamma_lt; bv_omega_arith
  have hB : ((BitVec.ofNat 64 B).setWidth 32).toNat=B := by have := h.boundMax; bv_omega_arith
  rw [hg,hB]
  exact ⟨trivial,h.held,h.tableFit,h.tableApart _ (by simp),h.tableApart _ (by simp),h.tableApart _ (by simp),h.tableAligned,
    trivial,trivial,h.cOut,h.cLow,h.cWork,h.secretOut,h.secretLow,h.secretWork,h.outLow,h.outWork,h.lowWork,
    h.cFit,h.secretFit,h.outFit,h.lowFit,h.workFit,h.products,h.canonical,h.gamma,h.boundPos,h.boundMax⟩

theorem pairedLowArgs_ok {c secret out low work : Ptr} {g B : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (ho : (Arg.ptr out).Ok)
    (hl : (Arg.ptr low).Ok) (hw : (Arg.ptr work).Ok) :
    ∀x∈pairedLowArgs c secret out low work g B,x.2.Ok ∧ x.1∈argRegs := by
  simp only [pairedLowArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨hc,by simp⟩
  · exact ⟨hs,by simp⟩
  · exact ⟨ho,by simp⟩
  · exact ⟨hl,by simp⟩
  · exact ⟨hw,by simp⟩
  · exact ⟨trivial,by simp⟩
  · exact ⟨trivial,by simp⟩

def PairedLowPost (g B : Nat) (m m' : Mem) (c secret out low : Addr) (r : BitVec 32) : Prop :=
  (∀j<2,∀i<n,
    (coeffAt m' (pairPolyPtr out j) i).toNat=(highBits g (pairedDifference m c secret out j)[i]!).toNat ∧
    (coeffAt m' (pairPolyPtr low j) i).toInt=lowBits g (pairedDifference m c secret out j)[i]!) ∧
  r=if normRq ((List.range 2).map fun j => pairedLowPoly g (pairedDifference m c secret out j))<B then 1 else 0

theorem pairedLowAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State}
    {c secret out low work : Ptr} {g B : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (ho : (Arg.ptr out).Ok)
    (hl : (Arg.ptr low).Ok) (hw : (Arg.ptr work).Ok)
    (h : PairedLowReady c secret out low work g B s) :
    WP isa (callAt nm (selected .r0) (pairedLowArgs c secret out low work g B)) s fun t =>
      Post S s t [⟨pa s out,2048⟩,⟨pa s low,2048⟩,⟨pa s work,2176⟩] ∧
      PairedLowPost g B s.mem t.mem (pa s c) (pa s secret) (pa s out) (pa s low) ((t.gpr .x0).setWidth 32) := by
  refine WP.mono (callAtSyms_ok hS (pairedLow_callee S)
    (pairedLowArgs_ok hc hs ho hl hw) (by simp)
    (fun s1 h1 hy => pairedLowAt_pre h h1 hy) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ?_
  sig_post [pairedLowContract,pairedLowSig,abi,argRegs,Abi.withConsts,pairedConsts_eq] at hq
  have h5 : s1.gpr .x5=BitVec.ofNat 64 g := h1.imm (by simp [pairedLowArgs])
  have h6 : s1.gpr .x6=BitVec.ofNat 64 B := h1.imm (by simp [pairedLowArgs])
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,h5,h6,Args.mem h1] at hq
  have hg : ((BitVec.ofNat 64 g).setWidth 32).toNat=g := by have := h.gamma_lt; bv_omega_arith
  have hB : ((BitVec.ofNat 64 B).setWidth 32).toNat=B := by have := h.boundMax; bv_omega_arith
  simpa only [PairedLowPost,Arg.val,hg,hB] using And.intro hP hq

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowCallTiming` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedLowAt_tr {S : Nat} {nm : String} {c secret out low work : Ptr} {g B : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (ho : (Arg.ptr out).Ok)
    (hl : (Arg.ptr low).Ok) (hw : (Arg.ptr work).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x y,Q x y → PairedLowReady c secret out low work g B x ∧ PairedLowReady c secret out low work g B y ∧
      pa x c=pa y c ∧ pa x secret=pa y secret ∧ pa x out=pa y out ∧ pa x low=pa y low ∧
      pa x work=pa y work ∧ x.sp=y.sp ∧ x.syms "VG_MLDSA_INV_PAIR"=y.syms "VG_MLDSA_INV_PAIR") :
    RelCT isa Q (callAt nm (selected .r0) (pairedLowArgs c secret out low work g B)) fun _ _=>True := by
  refine callAtSyms_tr (pairedLow_callee S) (pairedLowArgs_ok hc hs ho hl hw) (by simp)
    fun x y x1 y1 hp h1 h2 hy1 hy2 => ?_
  obtain ⟨rx,ry,ec,es,eo,el,ew,esp,et⟩ := hQ x y hp
  refine ⟨[⟨pa x c,1024⟩,⟨pa x secret,2048⟩,⟨x.syms "VG_MLDSA_INV_PAIR",4096⟩],
    [⟨pa x out,2048⟩,⟨pa x low,2048⟩,⟨pa x work,2176⟩],
    pairedLowAt_pre rx h1 hy1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [ec,es,eo,el,ew,et]
    exact pairedLowAt_pre ry h2 hy2
  · sig_pub [pairedLowContract,pairedLowSig,abi,argRegs,Abi.withConsts,pairedConsts_eq]
    have h5x : x1.gpr .x5=BitVec.ofNat 64 g := h1.imm (by simp [pairedLowArgs])
    have h5y : y1.gpr .x5=BitVec.ofNat 64 g := h2.imm (by simp [pairedLowArgs])
    rw [hy1,hy2,Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,
      Args.r3 h1,Args.r3 h2,Args.r4 h1,Args.r4 h2,h5x,h5y,Args.sp h1,Args.sp h2]
    exact ⟨esp,et,ec,es,eo,el,ew,rfl⟩
  · rw [ec,es,eo,el,ew,et]; exact ry.readable
  · rw [eo,el,ew]; exact ry.writable

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowField` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem PairedLowPost.field {g B : Nat} {m m' : Mem} {c secret out low : Addr}
    {r : BitVec 32} {f : Nat → Poly}
    (hp : PairedLowPost g B m m' c secret out low r)
    (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    (hf : ∀j<2,pairedDifference m c secret out j=f j) :
    (∀j<2,NatPolyIs m' (pairPolyPtr out j) ((f j).map fun x=>(highBits g x).toNat) ∧
      SignedPolyIs m' (pairPolyPtr low j) (pairedLowPoly g (f j)) (-(g:Int)) g) ∧
    r=if normRq ((List.range 2).map fun j=>pairedLowPoly g (f j))<B then 1 else 0 := by
  refine ⟨?_,?_⟩
  · intro j hj
    refine ⟨?_,⟨?_,?_⟩⟩
    · apply Vector.ext
      intro i hi
      simp only [natPolyAt,Vector.getElem_ofFn,Vector.getElem_map]
      rw [(hp.1 j hj i hi).1,hf j hj,getElem!_eq _ hi]
    · intro i hi
      rw [(hp.1 j hj i hi).2]
      exact Response.lowBits_bounds hg _
    · intro i hi
      rw [(hp.1 j hj i hi).2,hf j hj]
      simp only [pairedLowPoly,getElem!_eq _ hi,Vector.getElem_map]
  · rw [hp.2]
    have he : ((List.range 2).map fun j=>pairedLowPoly g (pairedDifference m c secret out j))=
        ((List.range 2).map fun j=>pairedLowPoly g (f j)) := by
      apply List.map_congr_left
      intro j hj
      rw [hf j (List.mem_range.mp hj)]
    rw [he]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
