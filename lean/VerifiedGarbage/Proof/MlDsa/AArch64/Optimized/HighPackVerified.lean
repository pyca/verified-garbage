import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.HighPack
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackLoop
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Spec.MlDsa.HighPack
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts

/-! ## From `HighPackTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64

/-- Coefficients stay secret; only the two buffer addresses are public. -/
theorem pack4_ct :
    ConstantTime isa (fun _ => True) (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1]))
      (Impl.MlDsa.AArch64.Optimized.HighPack.code 261888) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem pack6_ct :
    ConstantTime isa (fun _ => True) (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1]))
      (Impl.MlDsa.AArch64.Optimized.HighPack.code 95232) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized.HighPack

end

/-! ## From `HighPackCode.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Arith (polyRegion)
open VG.Proof.MlKem.AArch64 (Keep)

structure CodePost (g : Nat) (s t : State) : Prop where
  keep : Keep [.x0,.x1,.x9,.x11] s t
  frame : Frame [⟨s.gpr .x1,32*packWidth g⟩] s.mem t.mem
  bytes : VG.Spec.Sha3.bytesAt t.mem (s.gpr .x1) (32*packWidth g)=
    highPacked g (polyAt s.mem (s.gpr .x0))

/-- Complete correctness of the exact selected packing function, including
setup, fixed-count loop, output frame, and callee-saved registers. -/
theorem code_ok {g : Nat} (hg : IsG g) (s : State)
    (hr : Reduced s.mem (s.gpr .x0))
    (hsep : (polyRegion (s.gpr .x0)).Disjoint ⟨s.gpr .x1,32*packWidth g⟩)
    (hin : ∀ j<16, ∀ k<4, InRegions (s.rd++s.wr)
      ((s.gpr .x0+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 (16*k)) 16)
    (hw8 : ∀ j<16, InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 ((2*packWidth g)*j)) 8)
    (hw4 : ∀ j<16, packWidth g=6 → InRegions s.wr
      ((s.gpr .x1+BitVec.ofNat 64 ((2*packWidth g)*j))+8) 4) :
    WP isa (Impl.MlDsa.AArch64.Optimized.HighPack.code g) s (CodePost g s) := by
  rw [code_eq]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (setup_ready s hg) fun a ha => ?_
  let u := a.write .x .x11 16
  refine WP.block_cons_iff.mpr ⟨u,rfl,WP.block_nil_iff.mpr ?_⟩
  have um : u.mem=s.mem := ha.1.mem
  have ur : u.rd=s.rd := ha.1.rd
  have uw : u.wr=s.wr := ha.1.wr
  have up : u.sp=s.sp := ha.1.sp
  have ug (r : Reg) (h9 : r≠.x9) (h11 : r≠.x11) : u.gpr r=s.gpr r := by
    change (if r=.x11 then 16 else a.gpr r)=s.gpr r
    rw [ite_eq_right h11,ha.1.gpr r h9]
  have initial : LoopState u (s.gpr .x0) (s.gpr .x1) g 0 u := by
    refine ⟨by decide,ha.2.sameVectors rfl,?_,Frame.refl _ _,?_,?_,rfl,
      fun _ _ _ _ _ => rfl,fun _ _ => rfl,rfl,rfl,rfl⟩
    · intro i hi; omega
    · simpa only [Nat.mul_zero,BitVec.add_zero] using ug .x0 (by decide) (by decide)
    · simpa only [Nat.mul_zero,BitVec.add_zero] using ug .x1 (by decide) (by decide)
  refine WP.mono (loop_ok hg (by decide) initial (by rw [um]; exact hr) hsep
    (fun j hj k hk => by rw [ur,uw]; exact hin j hj k hk)
    (fun j hj => by rw [uw]; exact hw8 j hj)
    (fun j hj hw => by rw [uw]; exact hw4 j hj hw)) fun t ht => ?_
  refine ⟨?_,?_,?_⟩
  · refine ⟨?_,ht.rd.trans ur,ht.wr.trans uw,ht.sp.trans up,?_⟩
    · intro r hn
      have hh : r≠.x0 ∧ r≠.x1 ∧ r≠.x9 ∧ r≠.x11 := by simpa using hn
      rw [ht.gpr r hh.1 hh.2.1 hh.2.2.1 hh.2.2.2,ug r hh.2.2.1 hh.2.2.2]
    · intro r hr
      have htemp : r∉groupTemps := by
        simp only [preservedV,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hc : r∉[VReg.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23,.v28,.v29,.v24,.v25] := by
        simp only [preservedV,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [ht.vec r htemp]
      change (a.v r).extractLsb' 0 64=(s.v r).extractLsb' 0 64
      rw [ha.1.vec r hc]
  · simpa only [um] using ht.frame
  · simpa only [um] using ht.output_bytes hg

end VG.Proof.MlDsa.AArch64.Optimized.HighPack

end

/-! ## From `HighPackContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Arith (polyRegion)

def packK (g : Nat) : Contract isa where
  pre s := s.rd=[polyRegion (s.gpr .x0)] ∧ s.wr=[⟨s.gpr .x1,32*packWidth g⟩] ∧
    (polyRegion (s.gpr .x0)).Disjoint ⟨s.gpr .x1,32*packWidth g⟩ ∧ Reduced s.mem (s.gpr .x0)
  post s t := VG.Spec.Sha3.bytesAt t.mem (s.gpr .x1) (32*packWidth g)=highPacked g (polyAt s.mem (s.gpr .x0))
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧ s.sp=t.sp

/-- The public two-buffer precondition supplies every bounded load/store
permission required by the full packing function. -/
theorem contract_wp {g : Nat} (hg : IsG g) {s : State} (hp : (packK g).pre s) :
    WP isa (Impl.MlDsa.AArch64.Optimized.HighPack.code g) s (CodePost g s) := by
  obtain ⟨hrd,hwr,hsep,hr⟩ := hp
  refine code_ok hg s hr hsep ?_ ?_ ?_
  · intro j hj k hk
    rw [hrd,Offset.add_add]
    exact ⟨polyRegion (s.gpr .x0),List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega) (by omega)⟩
  · intro j hj
    rw [hwr]
    refine ⟨⟨s.gpr .x1,32*packWidth g⟩,List.mem_singleton_self _,Offset.contains_base _ ?_ ?_⟩
    · rcases hg with rfl | rfl
      · change 8*j+8≤128; omega
      · change 12*j+8≤192; omega
    · rcases hg with rfl | rfl
      · change 8*j<2^64; omega
      · change 12*j<2^64; omega
  · intro j hj hw
    rw [hwr,hw]
    change InRegions [⟨s.gpr .x1,192⟩]
      ((s.gpr .x1+BitVec.ofNat 64 (12*j))+BitVec.ofNat 64 8) 4
    rw [Offset.add_add]
    exact ⟨⟨s.gpr .x1,192⟩,List.mem_singleton_self _,Offset.contains_base _ (by omega) (by omega)⟩

/-- The measured function preserves the calling convention without stack
saves: its complete clobber set consists of caller-saved registers. -/
theorem pack_correct {g : Nat} (hg : IsG g) (s : State) (hp : (packK g).pre s) :
    ∃ trace t, Exec isa (Impl.MlDsa.AArch64.Optimized.HighPack.code g) s trace t ∧
      abiPreserved s t ∧ (packK g).post s t := by
  obtain ⟨trace,t,he,ht⟩ := contract_wp hg hp
  refine ⟨trace,t,he,⟨?_,ht.keep.sp,ht.keep.vcs⟩,ht.bytes⟩
  intro r hr
  apply ht.keep.gpr r
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Only buffer addresses and stack pointer are public; coefficients remain secret. -/
theorem pack_ct {g : Nat} (hg : IsG g) :
    ConstantTime isa (packK g).pre (packK g).pub (Impl.MlDsa.AArch64.Optimized.HighPack.code g) := by
  have h : ConstantTime isa (fun _ => True) (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1]))
      (Impl.MlDsa.AArch64.Optimized.HighPack.code g) := by
    rcases hg with rfl | rfl
    · exact pack4_ct
    · exact pack6_ct
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply h s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  exact VG.Proof.MlKem.AArch64.agree_of hp.2.2 (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.1
    · exact hp.2.1)

end VG.Proof.MlDsa.AArch64.Optimized.HighPack

end

/-! ## From `HighPackVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Round (hbM)

/-- Explicit non-overlapping buffers containing the zero polynomial. -/
def packSat (g : Nat) : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000,1024⟩]
  wr := [⟨0x2000,32*packWidth g⟩]

/-- Fully verified fused packing helper: semantic correctness, ABI,
constant-time execution, and a satisfiable shared contract. -/
theorem pack_verified {g : Nat} (hg : IsG g) :
    Verified AArch64.target (Impl.MlDsa.AArch64.Optimized.HighPack.code g)
      (highPackContract g AArch64.abi) := by
  refine Verified.of_correct (pack_correct hg) (pack_ct hg) ?_
  refine { pre := ?_,post := ?_,pub := ?_,sat := ?_ }
  · rcases hg with rfl | rfl <;>
      (intro s h
       sig_pre [highPackContract,highPackSig,packK,packWidth,AArch64.abi,AArch64.argRegs] at h
       sig_split h
       sig_reduce [highPackContract,highPackSig,packK,packWidth,AArch64.abi,AArch64.argRegs]
       exact ⟨by assumption,by assumption,by assumption,h⟩)
  · rcases hg with rfl | rfl <;>
      sig_implies_post [highPackContract,highPackSig,packK,packWidth,highPacked,highCoefficients,hbM,AArch64.abi,AArch64.argRegs]
  · rcases hg with rfl | rfl <;>
      sig_implies_pub [highPackContract,highPackSig,packK,AArch64.abi,AArch64.argRegs]
  · refine ⟨packSat g,?_⟩
    rcases hg with rfl | rfl <;>
      sig_pre [highPackContract,highPackSig,AArch64.abi,AArch64.argRegs] <;> sig_and_intros
    all_goals first
      | rfl
      | exact Region.disjoint_of_sep (by decide)
      | exact fun i _ => by rw [VG.Proof.MlDsa.AArch64.Pack.coeffAt_zero]; decide
      | decide

end VG.Proof.MlDsa.AArch64.Optimized.HighPack

end
