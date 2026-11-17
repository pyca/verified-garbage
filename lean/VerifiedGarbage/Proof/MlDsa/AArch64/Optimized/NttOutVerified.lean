module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.StaticCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryTraversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Traversal
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.NttTable
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.MlDsa.Contract

/-! ### `MlDsa.AArch64.Optimized.NttVerified`, which this module and modules that import it used -/

section

/-! ### `MlDsa.PositiveNttContract`, which this module and modules that import it used -/

section

/-!
# ML-DSA: the contract of NTTs with positive representatives

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

Separate internal transform contracts. They retain the standard NTT field
value while explicitly allowing positive representatives below three times q.
The canonical `nttContract`, `Reduced`, and `PolyIs` contracts are unchanged.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

/-- Internal positive representatives, not canonical residues. -/
def PositivePolyIs (m : Mem) (p : Addr) (f : Poly) : Prop :=
  (∀ i<n, (coeffAt m p i).toNat<3*q) ∧ polyAt m p=f

def positiveNttSig : Sig where
  params := [("f",.array true .u32 256)]

def positiveNttContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  positiveNttSig.contract A
    (pre := fun f m => Reduced m f)
    (post := fun f m m' _ => PositivePolyIs m' f (ntt (polyAt m f)))
    (writeArgs := true) (stack := stack)

def positiveNttOutSig : Sig where
  params := [("out",.array true .u32 256),("f",.array false .u32 256)]

/-- Separate source and destination; callers needing exact aliasing use the
in-place helper. No initial destination contents are required. -/
def positiveNttOutContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  positiveNttOutSig.contract A
    (pre := fun _out f m => Reduced m f)
    (post := fun out f m m' _ => PositivePolyIs m' out (ntt (polyAt m f)))
    (writeArgs := true) (stack := stack)

end VG.Proof.MlDsa

end

end

/-! ## From `NttContract.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def positiveNttK : Contract isa where
  pre s := expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED") ∈ s.rd++s.wr ∧
    outputRegion (s.gpr .x0) ∈ s.wr ∧
    (expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")).Disjoint (outputRegion (s.gpr .x0)) ∧
    ExpandedArtifact s.mem (s.syms "VG_MLDSA_NTT_EXPANDED") ∧ Reduced s.mem (s.gpr .x0)
  post s t := PositivePolyIs t.mem (s.gpr .x0) (ntt (polyAt s.mem (s.gpr .x0)))
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.sp=t.sp ∧
    s.syms "VG_MLDSA_NTT_EXPANDED"=t.syms "VG_MLDSA_NTT_EXPANDED"

theorem positiveNtt_correct (s : State) (hp : positiveNttK.pre s) :
    ∃ trace t, Exec isa staticNtt s trace t ∧ abiPreserved s t ∧ positiveNttK.post s t := by
  obtain ⟨htr,hw,hsep,ht,hred⟩ := hp
  obtain ⟨tr,t,he,hk,hf,hm⟩ := staticNtt_words_ok ht htr hw hsep
  have hv := nttMemory_field (m := s.mem) (p := s.gpr .x0) ⟨hred,rfl⟩
  rw [← hm] at hv
  refine ⟨tr,t,he,⟨?_,hk.sp,hk.vcs⟩,hv.bound,hv.value⟩
  intro r hr
  apply hk.gpr r
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem positiveNtt_ct : ConstantTime isa positiveNttK.pre positiveNttK.pub staticNtt := by
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply staticNtt_ct s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hp.2.1 ?_,?_⟩
  · intro r hr
    have he : r=.x0 := by simpa only [List.mem_singleton] using hr
    subst r; exact hp.1
  · intro name hn
    have he : name="VG_MLDSA_NTT_EXPANDED" := by simpa only [List.mem_singleton] using hn
    subst name; exact hp.2.2

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `NttSat.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def nttSat : State where
  gpr r := if r=.x0 then 4096 else 0
  sp := 131072
  syms _ := 65536
  mem := constMem 65536 staticNttWords
  rd := [⟨65536,3904⟩]
  wr := [⟨4096,1024⟩]

theorem nttSat_held : ∀ i<488,
    nttSat.mem.readW (65536+BitVec.ofNat 64 (8*i)) 64=staticNttWords.getD i 0 := by
  intro i hi
  dsimp only [nttSat]
  exact constMem_held 65536 staticNttWords (by rw [TableConstants.staticNttWords_length]; decide)
    i (by rw [TableConstants.staticNttWords_length]; exact hi)

theorem nttSat_reduced : Reduced nttSat.mem 4096 := by
  intro i hi
  simp only [nttSat,coeffAt,Mem.readW,BitVec.setWidth_eq]
  rw [Mem.read_eq_of_bytes (v := (0#32)) ?_]
  · decide
  · intro j hj
    have ha : ¬ ((4096+BitVec.ofNat 64 (4*i)+BitVec.ofNat 64 j)-65536).toNat<8*staticNttWords.length := by
      rw [TableConstants.staticNttWords_length]
      have hi' : i<256 := hi
      simp only [BitVec.toNat_sub,BitVec.toNat_add,BitVec.toNat_ofNat,show (4096:BitVec 64).toNat=4096 by decide,
        show (65536:BitVec 64).toNat=65536 by decide]
      omega_using [hj, hi']
    simp only [constMem,ha,ite_false]
    simp

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `NttVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem nttConsts_eq : nttConsts=[("VG_MLDSA_NTT_EXPANDED",staticNttWords)] := rfl

theorem positiveNtt_pre {s : State}
    (h : (positiveNttContract (abi.withConsts nttConsts)).pre s) : positiveNttK.pre s := by
  sig_pre [positiveNttContract,positiveNttSig,abi,argRegs,nttConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,TableConstants.staticNttWords_length,stackBelow] at h
  obtain ⟨hd,held,_,hsep,_,ht,hw,_,hred⟩ := h
  have hrd : s.rd=[expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")] := by
    rw [← List.take_append_drop (s.rd.length-1) s.rd,ht,hd]
    rfl
  refine ⟨by rw [hrd]; simp,by rw [hw]; simp [outputRegion],?_,?_,hred⟩
  · exact hsep _ (by rw [hw]; simp [outputRegion])
  · intro i hi
    have hh := held i hi
    have eq (xs : List (BitVec 64)) (j : Nat) (hj : j<xs.length) : xs.getD j 0=xs[j]! := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some,getElem!_pos xs j hj]
    exact hh.trans (eq _ _ (by rw [TableConstants.staticNttWords_length]; exact hi))

 theorem positiveNtt_spec_pre {s : State}
    (hrd : s.rd=[expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")])
    (hwr : s.wr=[outputRegion (s.gpr .x0)])
    (held : ∀ i<488,s.mem.readW (s.syms "VG_MLDSA_NTT_EXPANDED"+BitVec.ofNat 64 (8*i)) 64=
      staticNttWords.getD i 0)
    (hfit : (s.syms "VG_MLDSA_NTT_EXPANDED").toNat+3904≤2^64)
    (hsep : (expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")).Disjoint (outputRegion (s.gpr .x0)))
    (hal : (s.syms "VG_MLDSA_NTT_EXPANDED").toNat%64=0)
    (hpfit : (s.gpr .x0).toNat+1024≤2^64) (hred : Reduced s.mem (s.gpr .x0)) :
    (positiveNttContract (abi.withConsts nttConsts)).pre s := by
  sig_pre [positiveNttContract,positiveNttSig,abi,argRegs,nttConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,TableConstants.staticNttWords_length,stackBelow]
  refine ⟨by rw [hrd]; rfl,held,hfit,?_,hal,by rw [hrd]; rfl,hwr,hpfit,hred⟩
  intro r hr
  rw [hwr] at hr
  have he := List.mem_singleton.mp hr
  subst r
  exact hsep

theorem positiveNtt_sat : (positiveNttContract (abi.withConsts nttConsts)).pre nttSat := by
  exact positiveNtt_spec_pre rfl rfl nttSat_held (by decide)
    (Region.disjoint_of_sep (by decide)) (by decide) (by decide) nttSat_reduced

/-- A separate positive-output contract: no canonical-output claim is used. -/
theorem positiveNtt_verified : Verified target staticNtt
    (positiveNttContract (abi.withConsts nttConsts)) := by
  refine Verified.of_correct positiveNtt_correct positiveNtt_ct
    { pre := fun _ h => positiveNtt_pre h,post := ?_,pub := ?_,sat := ⟨nttSat,positiveNtt_sat⟩ }
  · intro s t _ h
    sig_post [positiveNttContract,positiveNttSig,abi,argRegs,Abi.withConsts,nttConsts_eq]
    exact h
  · intro s t _ _ h
    sig_pub [positiveNttContract,positiveNttSig,abi,argRegs,Abi.withConsts,nttConsts_eq] at h
    exact ⟨h.2.2,h.1,h.2.1⟩

end VG.Proof.MlDsa.AArch64.Optimized

end

end

end

/-! ## From `MemoryOut.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- A disjoint source polynomial is unchanged throughout the outer pass. -/
theorem outerOutPass_source {m : Mem} {p src : Addr} {z : Nat → Int} {u : Nat}
    (hu : u≤8) (hd : (polyRegion src).Disjoint (polyRegion p))
    {k : Nat} (hk : k<n) :
    coeffAt (outerOutPassMem m p src z u) src k=coeffAt m src k := by
  have hf : Frame [outputRegion p] m (outerOutPassMem m p src z u) :=
    outerOutPass_frame (fun v hv i => outer_contains p (by omega_using [hu, hv]) i)
  exact coeffAt_frame hf (by intro r hr; have he := List.mem_singleton.mp hr; subst r; exact hd) hk

/-- The next source bank equals the corresponding in-place input bank. -/
theorem outerOutPass_bank {m : Mem} {p src : Addr} {z : Nat → Int} {u : Nat}
    (hu : u<8) (hd : (polyRegion src).Disjoint (polyRegion p)) :
    readBank (outerOutPassMem m p src z u) (coeffAddr src (4*u)) 128 =
      readBank (outerPassMem m src z u) (coeffAddr src (4*u)) 128 := by
  apply Vector.ext
  intro i hi
  apply vec_ext
  intro e he
  rw [readBank_coeff _ src (4*u) 32 ⟨i,hi⟩ he,
    readBank_coeff _ src (4*u) 32 ⟨i,hi⟩ he]
  have hk : 4*u+32*i+e<n := by change 4*u+32*i+e<256; omega_using [hu, hi, he]
  rw [outerOutPass_source (by omega_using [hu]) hd hk,
    outerPass_untouched m src z (by omega_using [hu]) hk (by omega_using [hu, he])]

/-- Every completed slice agrees word-for-word with the in-place reference. -/
theorem outerOutPass_processed {m : Mem} {p src : Addr} {z : Nat → Int}
    (hd : (polyRegion src).Disjoint (polyRegion p)) {u k : Nat}
    (hu : u≤8) (hk : k<n) (hprocessed : k%32/4<u) :
    coeffAt (outerOutPassMem m p src z u) p k=
      coeffAt (outerPassMem m src z u) src k := by
  induction u with
  | zero => omega
  | succ u ih =>
    have hp (a : Addr) : a+BitVec.ofNat 64 (16*u)=coeffAddr a (4*u) := by
      simp only [coeffAddr,show 4*(4*u)=16*u by omega_using []]
    simp only [outerOutPassMem,outerPassMem,outerOutMemStep,outerMemStep,hp]
    rw [outerOutPass_bank (by omega_using [hu]) hd]
    by_cases he : k%32/4=u
    · have ki : k/32<8 := by change k<256 at hk; omega_using [hk]
      have ke : k=4*u+32*(k/32)+k%4 := by omega_using [he]
      rw [ke,writeBank_coeff_at (start := 4*u) (step := 32) (e := k%4) _ _ p (by decide) (by omega_using [hu]) ⟨k/32,ki⟩ (by omega_using []),
        writeBank_coeff_at (start := 4*u) (step := 32) (e := k%4) _ _ src (by decide) (by omega_using [hu]) ⟨k/32,ki⟩ (by omega_using [])]
    · have hout : ∀ i : Fin 8, ¬(4*u+32*i.val≤k ∧ k<4*u+32*i.val+4) := by
        intro i; omega_using [hu, he]
      rw [writeBank_coeff_outside (step := 32) _ _ p (by omega_using [hu]) hk hout,
        writeBank_coeff_outside (step := 32) _ _ src (by omega_using [hu]) hk hout]
      exact ih (by omega_using [hu]) (by omega_using [hprocessed, he])

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `MemoryOutTraversal.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- The separate-source outer pass stores exactly the reference field result. -/
theorem outerOutPass_field {m : Mem} {p src : Addr} {w : Poly}
    (h : PolyIs m src w) (hd : (polyRegion src).Disjoint (polyRegion p)) :
    SignedPolyIs (outerOutPassMem m p src ordinaryRoot 8) p
      (Traversal.run Traversal.outerSchedule w) (-(15*8380417)) (15*8380417) := by
  apply (outerPass_all h).congr
  intro k hk
  exact outerOutPass_processed hd (by decide) hk (by omega_using [])

/-- A disjoint-source optimized transform implements the standard NTT. -/
theorem outMemory_field_disjoint {m : Mem} {p src : Addr} {w : Poly}
    (h : PolyIs m src w) (hd : (polyRegion src).Disjoint (polyRegion p)) :
    PosPolyIs (outMemory m p src ordinaryRoot innerRoot tailRoot) p (ntt w) := by
  have ho := outerOutPass_field h hd
  have hi := fivePassMem_field (by simpa only [Int.neg_mul] using ho)
  simpa only [outMemory,Traversal.traversal_ntt] using hi

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `NttOutContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def positiveNttOutK : Contract isa where
  pre s := expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED") ∈ s.rd++s.wr ∧
    outputRegion (s.gpr .x0) ∈ s.wr ∧
    outputRegion (s.gpr .x1) ∈ s.rd++s.wr ∧
    (outputRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0)) ∧
    (expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")).Disjoint (outputRegion (s.gpr .x0)) ∧
    ExpandedArtifact s.mem (s.syms "VG_MLDSA_NTT_EXPANDED") ∧ Reduced s.mem (s.gpr .x1)
  post s t := PositivePolyIs t.mem (s.gpr .x0) (ntt (polyAt s.mem (s.gpr .x1)))
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧ s.sp=t.sp ∧
    s.syms "VG_MLDSA_NTT_EXPANDED"=t.syms "VG_MLDSA_NTT_EXPANDED"

theorem positiveNttOut_correct (s : State) (hp : positiveNttOutK.pre s) :
    ∃ trace t, Exec isa outNtt s trace t ∧ abiPreserved s t ∧ positiveNttOutK.post s t := by
  obtain ⟨htr,hw,hr,hio,hsep,ht,hred⟩ := hp
  obtain ⟨tr,t,he,hk,hf,hm⟩ := outNtt_words_ok ht htr hr hw hsep
  have hv := outMemory_field_disjoint (m := s.mem) (p := s.gpr .x0) ⟨hred,rfl⟩ hio
  rw [← hm] at hv
  refine ⟨tr,t,he,⟨?_,hk.sp,hk.vcs⟩,hv.bound,hv.value⟩
  intro r hr
  apply hk.gpr r
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem positiveNttOut_ct : ConstantTime isa positiveNttOutK.pre positiveNttOutK.pub outNtt := by
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply outNtt_ct s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hp.2.2.1 ?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.1
    · exact hp.2.1
  · intro name hn
    have he : name="VG_MLDSA_NTT_EXPANDED" := by simpa only [List.mem_singleton] using hn
    subst name; exact hp.2.2.2

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `NttOutVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem positiveNttOut_pre {s : State}
    (h : (positiveNttOutContract (abi.withConsts nttConsts)).pre s) : positiveNttOutK.pre s := by
  sig_pre [positiveNttOutContract,positiveNttOutSig,abi,argRegs,nttConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,TableConstants.staticNttWords_length,stackBelow] at h
  obtain ⟨hd,held,_,hsep,_,ht,hw,hio,_,_,hred⟩ := h
  have hrd : s.rd=[outputRegion (s.gpr .x1),expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")] := by
    rw [← List.take_append_drop (s.rd.length-1) s.rd,ht,hd]
    rfl
  refine ⟨by rw [hrd]; simp,by rw [hw]; simp [outputRegion],by rw [hrd]; simp,
    hio.symm,?_,?_,hred⟩
  · exact hsep _ (by rw [hw]; simp [outputRegion])
  · intro i hi
    have eq (xs : List (BitVec 64)) (j : Nat) (hj : j<xs.length) : xs.getD j 0=xs[j]! := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some,getElem!_pos xs j hj]
    exact (held i hi).trans (eq _ _ (by rw [TableConstants.staticNttWords_length]; exact hi))

theorem positiveNttOut_spec_pre {s : State}
    (hrd : s.rd=[outputRegion (s.gpr .x1),expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")])
    (hwr : s.wr=[outputRegion (s.gpr .x0)])
    (held : ∀ i<488,s.mem.readW (s.syms "VG_MLDSA_NTT_EXPANDED"+BitVec.ofNat 64 (8*i)) 64=
      staticNttWords.getD i 0)
    (hfit : (s.syms "VG_MLDSA_NTT_EXPANDED").toNat+3904≤2^64)
    (hsep : (expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")).Disjoint (outputRegion (s.gpr .x0)))
    (hal : (s.syms "VG_MLDSA_NTT_EXPANDED").toNat%64=0)
    (hio : (outputRegion (s.gpr .x0)).Disjoint (outputRegion (s.gpr .x1)))
    (hpfit : (s.gpr .x0).toNat+1024≤2^64) (hsfit : (s.gpr .x1).toNat+1024≤2^64)
    (hred : Reduced s.mem (s.gpr .x1)) :
    (positiveNttOutContract (abi.withConsts nttConsts)).pre s := by
  sig_pre [positiveNttOutContract,positiveNttOutSig,abi,argRegs,nttConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,TableConstants.staticNttWords_length,stackBelow]
  refine ⟨by rw [hrd]; rfl,held,hfit,?_,hal,by rw [hrd]; rfl,hwr,hio,hpfit,hsfit,hred⟩
  intro r hr
  rw [hwr] at hr
  have he := List.mem_singleton.mp hr
  subst r
  exact hsep

def nttOutSat : State := { nttSat with
  gpr := fun r => if r=.x0 then 8192 else if r=.x1 then 4096 else 0
  rd := [⟨4096,1024⟩,⟨65536,3904⟩]
  wr := [⟨8192,1024⟩] }

theorem positiveNttOut_sat : (positiveNttOutContract (abi.withConsts nttConsts)).pre nttOutSat := by
  apply positiveNttOut_spec_pre (s:=nttOutSat) rfl rfl
  · simpa only [nttOutSat,show nttSat.syms "VG_MLDSA_NTT_EXPANDED"=65536 from rfl] using nttSat_held
  · decide
  · exact Region.disjoint_of_sep (by decide)
  · decide
  · exact Region.disjoint_of_sep (by decide)
  · decide
  · decide
  · simpa only [nttOutSat,nttSat,show (Reg.x1=Reg.x0)=False from propext (by decide),ite_false,ite_true] using nttSat_reduced

theorem positiveNttOut_verified : Verified target outNtt
    (positiveNttOutContract (abi.withConsts nttConsts)) := by
  refine Verified.of_correct positiveNttOut_correct positiveNttOut_ct
    { pre := fun _ h => positiveNttOut_pre h,post := ?_,pub := ?_,sat := ⟨nttOutSat,positiveNttOut_sat⟩ }
  · intro s t _ h
    sig_post [positiveNttOutContract,positiveNttOutSig,abi,argRegs,Abi.withConsts,nttConsts_eq]
    exact h
  · intro s t _ _ h
    sig_pub [positiveNttOutContract,positiveNttOutSig,abi,argRegs,Abi.withConsts,nttConsts_eq] at h
    exact ⟨h.2.2.1,h.2.2.2,h.1,h.2.1⟩

end VG.Proof.MlDsa.AArch64.Optimized

end
