module

public import VerifiedGarbage.Proof.MlDsa.CommitTailContract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailBody
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailPro
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Parity
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedCommitment
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Top
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry

/-! ### `MlDsa.AArch64.Sign.CommitTailVerified`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Sign.CommitTailCorrect`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Sign.CommitTailEpi`, which only this module used -/

section

/-! ## From `CommitTailRestoreV.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_ldrq)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Restores every nonvolatile vector from the untouched save area. -/
theorem restoreV_ok {σ s : State} (hs : Saved σ s.mem) (hptr : s.gpr .x3=σ.gpr .x3)
    (hin : ∀i<8, InRegions (s.rd++s.wr) (σ.gpr .x3+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block restore) s fun t => RegKeep [] s t ∧ t.mem=s.mem ∧
      ∀i<8,t.v (vreg (8+i))=σ.v (vreg (8+i)) := by
  unfold restore
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M:=isa)
    (fun k t => RegKeep [] s t ∧ t.mem=s.mem ∧ ∀i<k,t.v (vreg (8+i))=σ.v (vreg (8+i)))
    (fun k t hk ht => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,fun _ h => by omega⟩
  refine wp_ldrq ⟨by omega_using [],by omega_using [hk]⟩ (by rw [ht.1.gpr .x3 (by simp),hptr])
    (by rw [ht.1.rd,ht.1.wr]; exact hin k hk) fun u hu => WP.block_nil_iff.mpr ?_
  refine ⟨(ht.1.trans (RegKeep.vupd hu)).mono (by simp),hu.mem.trans ht.2.1,?_⟩
  intro i hi
  by_cases he : i=k
  · subst i
    rw [hu.v,ht.2.1,hs.vec k hk]
  · have hne : vreg (8+i)≠vreg (8+k) := by
      rw [ne_eq,vreg_inj (8+i) (by omega_using [hk, hi]) (8+k) (by omega_using [hk])]; omega_using [he]
    rw [hu.get _ hne]
    exact ht.2.2 i (by omega_using [hi, he])

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailRestoreG.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_ldr)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

private theorem saved_mem : ∀i<4,saved[i]!∈saved := by decide
private theorem saved_inj : ∀i<4,∀j<4,saved[i]! =saved[j]! ↔ i=j := by decide

/-- Restores all four scalar saves, including the incoming return address. -/
theorem restoreG_ok {σ s : State} (hs : Saved σ s.mem) (hptr : s.gpr .x3=σ.gpr .x3)
    (hin : ∀i<4, InRegions (s.rd++s.wr) (σ.gpr .x3+BitVec.ofNat 64 (128+8*i)) 8) :
    WP isa (.block ((List.range 4).map fun i => .ldr .x saved[i]! .x3 (128+8*i))) s fun t =>
      RegKeep saved s t ∧ t.mem=s.mem ∧ t.v=s.v ∧
      ∀i<4,t.gpr saved[i]! =σ.gpr saved[i]! := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M:=isa)
    (fun k t => RegKeep saved s t ∧ t.mem=s.mem ∧ t.v=s.v ∧
      ∀i<k,t.gpr saved[i]! =σ.gpr saved[i]!)
    (fun k t hk ht => ?_) 4 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,rfl,fun _ h => by omega⟩
  refine wp_ldr ⟨by omega_using [],by omega_using [hk]⟩ (by rw [ht.1.gpr .x3 (by decide),hptr])
    (by rw [ht.1.rd,ht.1.wr]; exact hin k hk) fun u hu => WP.block_nil_iff.mpr ?_
  refine ⟨(ht.1.trans (RegKeep.upd hu)).mono ?_,hu.mem.trans ht.2.1,hu.vec.trans ht.2.2.1,?_⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hr
    · rcases List.mem_singleton.mp hr with rfl
      exact saved_mem k hk
  · intro i hi
    by_cases he : i=k
    · subst i
      rw [hu.gpr,ht.2.1,hs.regs k hk]
    · have hne : saved[i]!≠saved[k]! := by
        rw [ne_eq,saved_inj i (by omega_using [hk, hi]) k hk]; exact he
      rw [hu.other _ hne]
      exact ht.2.2.2 i (by omega_using [hi, he])

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailEpi.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_mov)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- The outer helper restores its captured nonvolatile vectors and scalar
registers without changing any result or workspace bytes. -/
theorem epi_ok {σ s : State} (hs : Saved σ s.mem) (hptr : s.gpr .x19=σ.gpr .x3)
    (hv : ∀i<8, InRegions (s.rd++s.wr) (σ.gpr .x3+BitVec.ofNat 64 (16*i)) 16)
    (hg : ∀i<4, InRegions (s.rd++s.wr) (σ.gpr .x3+BitVec.ofNat 64 (128+8*i)) 8) :
    WP isa (.block epi) s fun t =>
      RegKeep (.x3::saved) s t ∧ t.mem=s.mem ∧
      (∀i<8,t.v (vreg (8+i))=σ.v (vreg (8+i))) ∧
      (∀i<4,t.gpr saved[i]! =σ.gpr saved[i]!) := by
  unfold epi
  change WP isa (.block (Impl.MlKem.AArch64.mov .x3 .x19 ::
    (restore ++ (List.range 4).map fun i => .ldr .x saved[i]! .x3 (128+8*i)))) s _
  refine wp_mov fun a ha => ?_
  rw [WP.block_append_iff]
  refine WP.mono (restoreV_ok (by rw [ha.mem]; exact hs) (ha.gpr.trans hptr)
    (fun i hi => by rw [ha.rd,ha.wr]; exact hv i hi)) fun b ⟨hb,hmb,hvb⟩ => ?_
  refine WP.mono (restoreG_ok (by rw [hmb,ha.mem]; exact hs)
    ((hb.gpr .x3 (by simp)).trans (ha.gpr.trans hptr))
    (fun i hi => by rw [hb.rd,hb.wr,ha.rd,ha.wr]; exact hg i hi))
    fun t ⟨ht,hmt,hvt,hgt⟩ => ?_
  refine ⟨(((RegKeep.upd ha).trans hb).trans ht).mono (by simp),
    hmt.trans (hmb.trans ha.mem),?_,hgt⟩
  intro i hi
  rw [hvt]
  exact hvb i hi

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Original ABI state is restored after the shared-lane computation. -/
theorem finish_ok {σ s : State} {wlen olen : Nat} (hp : Pre wlen olen σ)
    (hs : BodyPost wlen olen σ s) :
    WP isa (.block epi) s fun t => abiPreserved σ t ∧ Frame (writes σ olen) σ.mem t.mem ∧
      Spec.Sha3.bytesAt t.mem (σ.gpr .x2) olen=Spec.MlDsa.H
        (Spec.Sha3.bytesAt σ.mem (σ.gpr .x0) 64++Spec.Sha3.bytesAt σ.mem (σ.gpr .x1) wlen) olen ∧
      Proof.MlDsa.PolyIs t.mem (σ.gpr .x6) (Spec.MlDsa.toRq (Spec.MlDsa.bitUnpack
        (Spec.MlDsa.H (seedBytes σ.mem (σ.gpr .x4) (σ.gpr .x5)) 640) 524287 524288)) := by
  obtain ⟨hk,hsv,hf,h19,hh,hm⟩ := hs
  refine WP.mono (epi_ok hsv h19 (fun i hi => by
    rw [hk.rd,hk.wr]; exact hp.readWork _ _ (by omega_using [hi])) (fun i hi => by
    rw [hk.rd,hk.wr]; exact hp.readWork _ _ (by omega_using [hi]))) fun t ⟨ht,hmt,hv,hg⟩ => ?_
  refine ⟨⟨?_,ht.sp.trans hk.sp,?_⟩,?_,?_,?_⟩
  · intro r hr
    simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact hg 0 (by decide)
      | exact hg 1 (by decide)
      | exact hg 2 (by decide)
      | exact hg 3 (by decide)
      | exact (ht.gpr _ (by decide)).trans (hk.gpr _ (by decide))
  · intro r hr
    simp only [preservedV,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 0 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 1 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 2 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 3 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 4 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 5 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 6 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 7 (by decide))
  · rw [hmt]; exact hf
  · rw [hmt]; exact hh
  · rw [hmt]; exact hm

/-- Complete measured commitment-plus-mask helper, including save/restore. -/
theorem raw_ok (σ : State) {wlen olen : Nat} (hp : Pre wlen olen σ) :
    WP isa (code wlen olen) σ fun t => abiPreserved σ t ∧ Frame (writes σ olen) σ.mem t.mem ∧
      Spec.Sha3.bytesAt t.mem (σ.gpr .x2) olen=Spec.MlDsa.H
        (Spec.Sha3.bytesAt σ.mem (σ.gpr .x0) 64++Spec.Sha3.bytesAt σ.mem (σ.gpr .x1) wlen) olen ∧
      Proof.MlDsa.PolyIs t.mem (σ.gpr .x6) (Spec.MlDsa.toRq (Spec.MlDsa.bitUnpack
        (Spec.MlDsa.H (seedBytes σ.mem (σ.gpr .x4) (σ.gpr .x5)) 640) 524287 524288)) := by
  obtain ⟨tf,s,hf,hs⟩ := front_ok hp.toFrontPre
  obtain ⟨tb,t,hb,ht⟩ := body_ok hp hs
  obtain ⟨te,u,he,hu⟩ := finish_ok hp ht
  cases hf with
  | seq hf0 hf1 =>
    cases hb with
    | seq hb0 hb1 =>
      exact ⟨_,_,Exec.seq hf0 (Exec.seq hf1 (Exec.seq hb0 (Exec.seq hb1 he))),hu⟩

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

end

/-! ## From `CommitTailContract.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64 VG.Spec.MlDsa

def kernel (wlen olen : Nat) : Contract isa where
  pre := Pre wlen olen
  post s t := Spec.Sha3.bytesAt t.mem (s.gpr .x2) olen=H
    (Spec.Sha3.bytesAt s.mem (s.gpr .x0) 64++Spec.Sha3.bytesAt s.mem (s.gpr .x1) wlen) olen ∧
    PolyIs t.mem (s.gpr .x6) (toRq (bitUnpack (H (seedBytes s.mem (s.gpr .x4) (s.gpr .x5)) 640) 524287 524288))
  pub := VG.AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x6])

theorem correct (s : State) {wlen olen : Nat} (hp : (kernel wlen olen).pre s) :
    ∃tr t,Exec isa (Impl.MlDsa.AArch64.Sign.CommitTail.code wlen olen) s tr t ∧
      abiPreserved s t ∧ (kernel wlen olen).post s t := by
  obtain ⟨tr,t,he,habi,_,hhash,hmask⟩ := raw_ok s hp
  exact ⟨tr,t,he,habi,hhash,hmask⟩

theorem shared_pre {s : State} {wlen olen : Nat} (hw : wlen=768 ∨ wlen=1024)
    (ho : olen=48 ∨ olen=64) (h : (commitTailContract AArch64.abi wlen olen).pre s) :
    Pre wlen olen s := by
  sig_pre [commitTailContract,commitTailSig,AArch64.abi,AArch64.argRegs] at h
  sig_split h
  have hrd : s.rd=[⟨s.gpr .x0,64⟩,⟨s.gpr .x1,wlen⟩,⟨s.gpr .x4,64⟩] := by with_reducible assumption
  have hwr : s.wr=[⟨s.gpr .x2,olen⟩,⟨s.gpr .x3,2048⟩,⟨s.gpr .x6,1024⟩] := by with_reducible assumption
  refine ⟨⟨hw,?_,?_,?_,?_,?_,?_,?_⟩,ho,?_,?_,?_,?_,?_,?_⟩
  · intro d n hn
    exact ⟨⟨s.gpr .x0,64⟩,by rw [hrd]; simp,Offset.contains_base _ hn (by omega_using [hn])⟩
  · intro d n hn
    exact ⟨⟨s.gpr .x1,wlen⟩,by rw [hrd]; simp,Offset.contains_base _ hn (by rcases hw with rfl|rfl <;> omega_using [hn])⟩
  · intro d n hn
    exact ⟨⟨s.gpr .x4,64⟩,by rw [hrd]; simp,Offset.contains_base _ hn (by omega_using [hn])⟩
  · intro d n hn
    exact ⟨⟨s.gpr .x3,2048⟩,by rw [hwr]; simp,Offset.contains_base _ hn (by omega_using [hn])⟩
  · with_reducible assumption
  · with_reducible assumption
  · exact Region.Disjoint.symm (by with_reducible assumption)
  · intro d n hn
    exact ⟨⟨s.gpr .x2,olen⟩,by rw [hwr]; simp,Offset.contains_base _ hn (by rcases ho with rfl|rfl <;> omega_using [hn])⟩
  · exact ⟨⟨s.gpr .x6,1024⟩,by rw [hwr]; simp,by simp [Region.Contains]⟩
  · intro d n hn
    exact ⟨⟨s.gpr .x3,2048⟩,by rw [hwr]; simp,Offset.contains_base _ hn (by omega_using [hn])⟩
  · with_reducible assumption
  · exact Region.Disjoint.symm (by with_reducible assumption)
  · with_reducible assumption

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64 VG.Spec.MlDsa

def satState (wlen olen : Nat) : State where
  gpr r := match r with
    | .x0=>0x1000 | .x1=>0x2000 | .x2=>0x3000 | .x3=>0x4000
    | .x4=>0x6000 | .x6=>0x7000 | _=>0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000,64⟩,⟨0x2000,wlen⟩,⟨0x6000,64⟩]
  wr := [⟨0x3000,olen⟩,⟨0x4000,2048⟩,⟨0x7000,1024⟩]

theorem implies {wlen olen : Nat} (hw : wlen=768 ∨ wlen=1024) (ho : olen=48 ∨ olen=64) :
    (kernel wlen olen).Implies (commitTailContract AArch64.abi wlen olen) := by
  refine { pre := fun _ h => shared_pre hw ho h, post := ?_,pub := ?_,sat := ?_ }
  · sig_implies_post [commitTailContract,commitTailSig,kernel,seedBytes,commitTailSeed,AArch64.abi,AArch64.argRegs]
  · intro s t _ _ h
    sig_pub [commitTailContract,commitTailSig,AArch64.abi,AArch64.argRegs] at h
    sig_split h
    refine ⟨by with_reducible assumption,?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> with_reducible assumption
  · refine ⟨satState wlen olen,?_⟩
    rcases hw with rfl|rfl <;> rcases ho with rfl|rfl
    all_goals
      sig_pre [commitTailContract,commitTailSig,AArch64.abi,AArch64.argRegs]
      sig_and_intros
    all_goals first | rfl | exact Region.disjoint_of_sep (by decide) | decide

theorem verified65 : Verified AArch64.target
    (Impl.MlDsa.AArch64.Sign.CommitTail.code 768 48) (commitTailContract AArch64.abi 768 48) :=
  Verified.of_correct (fun s hp => correct s hp) (fun s t l r a b _ _ hp hs ht => code65_ct s t l r a b trivial trivial hp hs ht)
    (implies (.inl rfl) (.inl rfl))

theorem verified87 : Verified AArch64.target
    (Impl.MlDsa.AArch64.Sign.CommitTail.code 1024 64) (commitTailContract AArch64.abi 1024 64) :=
  Verified.of_correct (fun s hp => correct s hp) (fun s t l r a b _ _ hp hs ht => code87_ct s t l r a b trivial trivial hp hs ht)
    (implies (.inr rfl) (.inr rfl))

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

end

end


/-! ## From `CommitTailCall.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64 VG.Spec.MlDsa

theorem callee65 {S : Nat} (hS : S<2^64) :
    CalleeOk S (Impl.MlDsa.AArch64.Sign.CommitTail.code 768 48)
      (commitTailContract AArch64.abi 768 48 S) :=
  CalleeOk.of_verified hS verified65 (by omega_using []) (by
    have h : (Impl.MlDsa.AArch64.Sign.CommitTail.code 768 48).aarch64Depth=0 := by decide
    rw [h]; omega_using [])

theorem callee87 {S : Nat} (hS : S<2^64) :
    CalleeOk S (Impl.MlDsa.AArch64.Sign.CommitTail.code 1024 64)
      (commitTailContract AArch64.abi 1024 64 S) :=
  CalleeOk.of_verified hS verified87 (by omega_using []) (by
    have h : (Impl.MlDsa.AArch64.Sign.CommitTail.code 1024 64).aarch64Depth=0 := by decide
    rw [h]; omega_using [])

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CachedHashPre.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc Arg)
open VG.Impl.MlDsa.AArch64.Sign.Cached (hashArgs)

def hashReads (p : Params) (s : State) : List Region :=
  [⟨pa s (.x26,0),64⟩,⟨pa s (sc oW1),p.k*w1Len p⟩,⟨pa s (sc oMS),64⟩]
def hashWrites (p : Params) (s : State) : List Region :=
  [⟨pa s (sc oCT),cLen p⟩,⟨pa s t1P,2048⟩,⟨pa s t4P,1024⟩]

theorem hash_pre {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87) {S : Nat} {s s1 : State}
    (L : Lay S (sgR p) (sgW p) s) (h1 : Args (hashArgs p) s s1) :
    (commitTailContract abi (p.k*w1Len p) (cLen p) S).pre
      (s1.callEntry.withRegions (hashReads p s) (hashWrites p s)) := by
  sig_pre [commitTailContract,commitTailSig,AArch64.abi,VG.AArch64.argRegs]
  rw [h1.ptr (r:=.x0) (p:=(.x26,0)) (by simp [hashArgs]),
    h1.ptr (r:=.x1) (p:=sc oW1) (by simp [hashArgs]),
    h1.ptr (r:=.x2) (p:=sc oCT) (by simp [hashArgs]),
    h1.ptr (r:=.x3) (p:=t1P) (by simp [hashArgs]),
    h1.ptr (r:=.x4) (p:=sc oMS) (by simp [hashArgs]),
    h1.ptr (r:=.x6) (p:=t4P) (by simp [hashArgs]),Args.sp h1]
  simp only [hashReads,hashWrites]
  and_intros
  all_goals first
    | with_reducible rfl
    | exact True.intro
    | exact wfP_of (Lay.spS L)
    | exact resv fun _ hr=>by
        rw [stackBelow_mem hr]
        refine conj_cons (L.stkD (p:=(.x26,0)) (l:=64) (by rcases hp with rfl|rfl <;> decide)) ?_
        refine conj_cons (L.stkD (p:=sc oW1) (l:=p.k*w1Len p) (by rcases hp with rfl|rfl <;> decide)) ?_
        refine conj_cons (L.stkD (p:=sc oCT) (l:=cLen p) (by rcases hp with rfl|rfl <;> decide)) ?_
        refine conj_cons (L.stkD (p:=t1P) (l:=2048) (by rcases hp with rfl|rfl <;> decide)) ?_
        refine conj_cons (L.stkD (p:=sc oMS) (l:=64) (by rcases hp with rfl|rfl <;> decide)) ?_
        exact conj_cons (L.stkD (p:=t4P) (l:=1024) (by rcases hp with rfl|rfl <;> decide)) conj_nil
    | exact Lay.disj L (by rcases hp with rfl|rfl <;> decide)
    | exact (Lay.disj L (by rcases hp with rfl|rfl <;> decide)).symm
    | exact Lay.nwp L (by rcases hp with rfl|rfl <;> decide)

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedHashGlue.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc Arg glue)
open VG.Impl.MlDsa.AArch64.Sign.Cached (hashArgs)
open VG.Proof.MlKem.AArch64 (Only wp_nil)

/-- The nonce lives in x9, which these seven argument moves preserve. -/
theorem hashGlue_ok (p : Params) (s : State) :
    WP isa (.block (glue (hashArgs p))) s (Args (hashArgs p) s) := by
  simp only [hashArgs,glue,Arg.instrs]
  refine lea_ok (by decide) 0 fun s0 h0 e0 => ?_
  refine lea_ok (by decide) oW1 fun s1 h1 e1 => ?_
  refine lea_ok (by decide) oCT fun s2 h2 e2 => ?_
  refine lea_ok (by decide) t1P.2 fun s3 h3 e3 => ?_
  refine lea_ok (by decide) oMS fun s4 h4 e4 => ?_
  refine lea_ok (by decide) 0 fun s5 h5 e5 => ?_
  refine lea_ok (by decide) t4P.2 fun s6 h6 e6 => ?_
  have h := (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6
  apply wp_nil
  refine ⟨⟨?_,h.mem⟩,h.keep.mono (by decide)⟩
  simp only [List.mem_cons,List.not_mem_nil,forall_eq_or_imp,false_implies,implies_true,and_true,
    Arg.val,pa]
  and_intros
  · rw [h6.get .x0 (by decide),h5.get .x0 (by decide),h4.get .x0 (by decide),
      h3.get .x0 (by decide),h2.get .x0 (by decide),h1.get .x0 (by decide),e0]
  · rw [h6.get .x1 (by decide),h5.get .x1 (by decide),h4.get .x1 (by decide),
      h3.get .x1 (by decide),h2.get .x1 (by decide),e1,h0.get .x28 (by decide)]
  · rw [h6.get .x2 (by decide),h5.get .x2 (by decide),h4.get .x2 (by decide),
      h3.get .x2 (by decide),e2,h1.get .x28 (by decide),h0.get .x28 (by decide)]
  · rw [h6.get .x3 (by decide),h5.get .x3 (by decide),h4.get .x3 (by decide),e3,
      h2.get .x28 (by decide),h1.get .x28 (by decide),h0.get .x28 (by decide)]
  · rw [h6.get .x4 (by decide),h5.get .x4 (by decide),e4,h3.get .x28 (by decide),
      h2.get .x28 (by decide),h1.get .x28 (by decide),h0.get .x28 (by decide)]
  · rw [h6.get .x5 (by decide),e5,h4.get .x9 (by decide),h3.get .x9 (by decide),
      h2.get .x9 (by decide),h1.get .x9 (by decide),h0.get .x9 (by decide)]
  · rw [e6,h5.get .x28 (by decide),h4.get .x28 (by decide),h3.get .x28 (by decide),
      h2.get .x28 (by decide),h1.get .x28 (by decide),h0.get .x28 (by decide)]

end VG.Proof.MlDsa.AArch64.Sign.Cached

end

/-! ## From `CachedHashCall.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Sign.Cached (hashArgs)
open VG.Impl.MlDsa.AArch64.Call (callAt)

/-- Caller rule for the measured argument moves, including the nonce in x9. -/
theorem hashCall_ok {p : Params} {S : Nat} (hS : S<2^64)
    {n : String} {c : Prog isa} {k : Contract isa} (C : CalleeOk S c k)
    {s : State} {rd wr : List Region}
    (hpre : ∀ s1, Args (hashArgs p) s s1 → k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd++wr) (s.rd++s.wr)) (hw : Covers wr s.wr) :
    WP isa (callAt n c (hashArgs p)) s fun s' => Post S s s' wr ∧
      ∃ s1, Args (hashArgs p) s s1 ∧
        k.post (s1.callEntry.withRegions rd wr) (s'.withRegions rd wr) := by
  refine WP.seq (WP.mono (hashGlue_ok p s) fun s1 h1 => ?_)
  have k1 := h1.2
  refine WP.callFV C.correct (hpre s1 h1) (by rw [k1.rd,k1.wr]; exact hc)
    (by rw [k1.wr]; exact hw)
    (fun s' hrd hwr hsp hf hcs hvcs hpost => ?_) (by have := C.fd; omega_using [hS, this])
  refine ⟨⟨hrd.trans k1.rd,hwr.trans k1.wr,hsp.trans k1.sp,
    fun r hr h30 => by rw [hcs r hr h30,k1.gpr r (argRegs_pres r hr)],?_,
    fun r hr => (hvcs r hr).trans (k1.vcs r hr)⟩,s1,h1,hpost⟩
  rw [h1.1.2,k1.sp] at hf
  exact Frame.below_mono hf C.fd hS

theorem hash_cov {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} {s : State} (L : Lay S (sgR p) (sgW p) s) :
    Covers (hashReads p s ++ hashWrites p s) (s.rd++s.wr) ∧
    Covers (hashWrites p s) s.wr := by
  have hr : Covers (hashReads p s) (s.rd++s.wr) := by
    apply Covers.cons (L.cR (p:=(.x26,0)) (l:=64) (by rcases hp with rfl|rfl <;> decide))
    apply Covers.cons (L.cR (p:=Impl.MlDsa.AArch64.Call.sc Impl.MlDsa.AArch64.Sign.oW1)
      (l:=p.k*w1Len p) (by rcases hp with rfl|rfl <;> decide))
    exact L.cR (by rcases hp with rfl|rfl <;> decide)
  have hw : Covers (hashWrites p s) s.wr := by
    apply Covers.cons (L.cW (p:=Impl.MlDsa.AArch64.Call.sc Impl.MlDsa.AArch64.Sign.oCT)
      (l:=cLen p) (by rcases hp with rfl|rfl <;> decide))
    apply Covers.cons (L.cW (p:=Impl.MlDsa.AArch64.Sign.t1P) (l:=2048)
      (by rcases hp with rfl|rfl <;> decide))
    exact L.cW (by rcases hp with rfl|rfl <;> decide)
  exact ⟨Covers.append_left hr (Covers.right hw),hw⟩

theorem hashReady_ok {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) {s : State} (L : Lay S (sgR p) (sgW p) s) :
    WP isa (callAt (if p.ℓ=5 then "vg_mldsa_commit_tail65" else "vg_mldsa_commit_tail87")
      (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*w1Len p) (cLen p)) (hashArgs p)) s
      (fun s' => Post S s s' (hashWrites p s) ∧
        ∃ s1, Args (hashArgs p) s s1 ∧
          (commitTailContract abi (p.k*w1Len p) (cLen p) S).post
            (s1.callEntry.withRegions (hashReads p s) (hashWrites p s))
            (s'.withRegions (hashReads p s) (hashWrites p s))) := by
  have C : CalleeOk S (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*w1Len p) (cLen p))
      (commitTailContract abi (p.k*w1Len p) (cLen p) S) := by
    rcases hp with rfl|rfl
    · exact CommitTail.callee65 hS
    · exact CommitTail.callee87 hS
  exact hashCall_ok hS C (fun _ h1 => hash_pre hp L h1)
    (hash_cov hp L).1 (hash_cov hp L).2

end VG.Proof.MlDsa.AArch64.Sign.Cached

end
