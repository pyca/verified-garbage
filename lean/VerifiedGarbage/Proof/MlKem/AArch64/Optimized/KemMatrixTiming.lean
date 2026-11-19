module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixCall
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.BeginTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Last
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Env
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.Framework.Offset
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.BeginTiming
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import VerifiedGarbage.TCB.Axioms
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastStart
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastStart
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.RegSet
meta import VerifiedGarbage.Proof.Framework.RegSet
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Sums
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Sums

/-! ### `MlKem.AArch64.Paired.LastTiming`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Paired.FullTiming`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Paired.FullPrefix`, which this module and modules that import it used -/

section

/-! # Complete singleton stream and vector parser entry for relational timing -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Proof.MlKem

structure LastInput (sb ss off : Nat) (p seed out table : Addr) (s : State) : Prop where
 ptr : s.gpr .x28+BitVec.ofNat 64 ss=p
 seedPtr : s.gpr .x28+BitVec.ofNat 64 sb=seed
 outPtr : s.gpr .x28+BitVec.ofNat 64 off=out
 readable : ∀j<4,InRegions (s.rd++s.wr) (seed+BitVec.ofNat 64 (8*j)) 8
 separate : (Region.mk seed 32).Disjoint ⟨p,2048⟩
 context : SingleContext p out table s
 symbol : s.syms "VG_MLKEM_REJ_SHUFFLE"=table

def fullPrefix (sha3 : Bool) (sb ss off a k : Nat) : Prog isa :=
 .seq (.seq (.block (Impl.MlKem.AArch64.Paired.fullInit sb ss a k))
   (.loop (singleBody sha3) (.nonzero .x .x22))) (.block (fullPrep off))
def fullPrefixRegs : List Reg := fullStartRegs++prepRegs

structure FullPrefixPostW (w16 : Bool) (B : Nat→Byte) (p out : Addr) (s t : State) : Prop where
 keep : Keep fullPrefixRegs s t
 entry : Rej8.EntryW w16 [] 280 B (p+400) out t
 pointer : t.gpr .x19=p
 tablePtr : t.gpr .x16=s.syms "VG_MLKEM_REJ_SHUFFLE"

theorem fullPrefix_ok {w16 : Bool} {s initial : State} {p seed out table : Addr} {sb ss off a k : Nat}
    (hss : ss<4096) (hsb : sb+32≤32768) (h8 : sb%8=0) (hoff : off<65536)
    (hk : 0<k) (hk256 : k≤256)
    (h : LastInput sb ss off p seed out table s) (hp : s.gpr .x19=p)
    (sv : Noise.Saved p initial s.mem) :
    WP isa (fullPrefix sha3 sb ss off a k) s (FullPrefixPostW w16 (xofByte (seedBytes s.mem seed a k)) p out s) := by
  refine WP.seq (WP.mono_syms (fullStart_ok (sha3 := sha3) (a:=a) (k:=k) hss hsb h8 hp h.ptr h.seedPtr h.readable h.context.scratch h.separate sv)
    fun u ⟨ku,fu,_,_,u19,_,_,bu⟩ sy => ?_)
  have cu := h.context.frame ku.rd ku.wr (fu.mono (by simp [fullWrites]))
  refine WP.mono (fullPrep_ok (w16 := w16) hoff u19 (by rw [ku.get .x28]; exact h.outPtr)
    cu.scratch cu.output cu.apart (fun i hi => bu.xof hk hk256 hi)
    (by rw [sy,h.symbol]; exact cu.artifact) (by rw [sy,h.symbol]; exact cu.readable)
    (by rw [sy,h.symbol]; exact cu.tableScratch) (by rw [sy,h.symbol]; exact cu.tableOut)) fun t ⟨kt,_,et,tablePtr⟩ => ?_
  exact ⟨ku.trans kt,et,(kt.get .x19).trans u19,by rw [tablePtr,sy]⟩

theorem fullPrefix_ct {sb ss off a k : Nat} (hss : ss<4096) : ConstantTime isa (fun _=>True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19,.x28])) (fullPrefix sha3 sb ss off a k) := by
  cases sha3
  · by_cases ho : off<4096
    · -- The call of the paired Keccak by its summary (`X2Sums.erased`).
      obtain ⟨hc, h⟩ : ∃ hc, (VectorTaint.taint.check (VectorTaint.ofRegs [.x19,.x28])
          (Code.eraseOff (fullPrefix false 0 0 0 0 1)) hc).isSome = true := by
        taint_decide_sum [VG.Proof.Sha3.AArch64.Neon.X2Sums.erased]
      exact vct_eraseOff_eq [.x19,.x28]
        (by simp only [fullPrefix,fullInit_eq hss,fullInit_eq (by decide : 0<4096),fullPrep,fullEntry,
          Impl.MlKem.AArch64.ptrTo,ite_eq_left hss,ite_eq_left ho]; rfl) h
    · -- The call of the paired Keccak by its summary (`X2Sums.erased`).
      obtain ⟨hc, h⟩ : ∃ hc, (VectorTaint.taint.check (VectorTaint.ofRegs [.x19,.x28])
          (Code.eraseOff (fullPrefix false 0 0 4096 0 1)) hc).isSome = true := by
        taint_decide_sum [VG.Proof.Sha3.AArch64.Neon.X2Sums.erased]
      exact vct_eraseOff_eq [.x19,.x28]
        (by simp only [fullPrefix,fullInit_eq hss,fullInit_eq (by decide : 0<4096),fullPrep,fullEntry,
          Impl.MlKem.AArch64.ptrTo,ite_eq_left hss,ite_eq_right ho]; rfl) h
  · by_cases ho : off<4096
    · apply ct_eraseOff_eq [.x19,.x28]
        (d := Code.eraseOff (fullPrefix true 0 0 0 0 1))
        (by simp only [fullPrefix,fullInit_eq hss,fullInit_eq (by decide : 0<4096),fullPrep,fullEntry,
          Impl.MlKem.AArch64.ptrTo,ite_eq_left hss,ite_eq_left ho]; rfl)
      taint_decide
    · apply ct_eraseOff_eq [.x19,.x28]
        (d := Code.eraseOff (fullPrefix true 0 0 4096 0 1))
        (by simp only [fullPrefix,fullInit_eq hss,fullInit_eq (by decide : 0<4096),fullPrep,fullEntry,
          Impl.MlKem.AArch64.ptrTo,ite_eq_left hss,ite_eq_right ho]; rfl)
      taint_decide
end VG.Proof.MlKem.AArch64.Paired

end

end

/-! # Singleton fallback timing depends only on the shared matrix seed -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Proof.MlKem

def fullSuffix (w16 : Bool := false) : Prog isa := .seq (.block [.logic .and .x .x24 .x24 .x0])
  (.seq (Rej8.zeroSuffix w16) (.block [.ldr .x .x22 .x19 1848,.ldr .x .x23 .x19 1856]))

theorem fullSuffix_ct (w16 : Bool) : ConstantTime isa (fun _=>True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x3,.x4,.x19])) (fullSuffix w16) := by
  cases w16 <;> exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x3,.x4,.x19]) (fun _ _ _ _ h=>h) (by taint_decide)

theorem fullFinish_entry_relCT {w16 : Bool} {s u : State} {B : Nat→Byte} {p out : Addr}
    (ps : Rej8.EntryW w16 [] 280 B (p+400) out s) (pu : Rej8.EntryW w16 [] 280 B (p+400) out u)
    (sp : s.sp=u.sp) (p19 : s.gpr .x19=u.gpr .x19) (t16 : s.gpr .x16=u.gpr .x16) :
    RelCT isa (fun t v=>t=s ∧ v=u) (fullFinish w16) (fun _ _=>True) := by
  let R := fun t v : State=>Rej8.PostW w16 [] 280 B out s t ∧ Rej8.PostW w16 [] 280 B out u v
  have parse : RelCT isa (fun t v=>t=s ∧ v=u) (Impl.MlKem.AArch64.Rej8.rejLoop w16) R :=
    Rej8.segment_relCT ps pu sp t16 (by decide) (by decide)
  refine RelCT.seq parse ?_
  intro t v tr ur t' v' h et ev
  have hsp := h.1.keep.sp.trans (sp.trans h.2.keep.sp.symm)
  have h3 : t.gpr .x3=v.gpr .x3 := h.1.acc.x3.trans h.2.acc.x3.symm
  have h4 : t.gpr .x4=v.gpr .x4 := BitVec.eq_of_toNat_eq (h.1.acc.x4.trans h.2.acc.x4.symm)
  have h19 : t.gpr .x19=v.gpr .x19 := by rw [h.1.keep.get .x19,h.2.keep.get .x19,p19]
  exact ⟨fullSuffix_ct w16 t v tr ur t' v' trivial trivial (agree_of hsp (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl; exact h3; exact h4; exact h19)) et ev,trivial⟩

theorem LastInput.full_wp {w16 : Bool} {s initial : State} {p seed out table : Addr} {sb ss off a k : Nat}
    (h : LastInput sb ss off p seed out table s)
    (hss : ss<4096) (hsb : sb+32≤32768) (h8 : sb%8=0) (hoff : off<65536)
    (hk : 0<k) (hk256 : k≤256) (hp : s.gpr .x19=p) (sv : Noise.Saved p initial s.mem) :
    WP isa (fullSampleCode sha3 sb ss off a k w16) s (FullPostW w16 (xofByte (seedBytes s.mem seed a k)) p out initial s) :=
  fullSampleCode_ok (sha3 := sha3) hss hsb h8 hoff hk hk256 hp h.ptr h.seedPtr h.outPtr h.readable
    h.context.scratch h.context.output h.separate h.context.apart sv
    (by rw [h.symbol]; exact h.context.artifact) (by rw [h.symbol]; exact h.context.readable)
    (by rw [h.symbol]; exact h.context.tableScratch) (by rw [h.symbol]; exact h.context.tableOut)

theorem fullSampleCode_relCT {w16 : Bool} {s u initialS initialU : State} {p seed out table : Addr} {sb ss off a k : Nat}
    (hss : ss<4096) (hsb : sb+32≤32768) (h8 : sb%8=0) (hoff : off<65536)
    (hk : 0<k) (hk256 : k≤256)
    (ps : LastInput sb ss off p seed out table s) (pu : LastInput sb ss off p seed out table u)
    (s19 : s.gpr .x19=p) (u19 : u.gpr .x19=p)
    (svs : Noise.Saved p initialS s.mem) (svu : Noise.Saved p initialU u.mem)
    (sp : s.sp=u.sp) (base : s.gpr .x28=u.gpr .x28)
    (seedEq : seedBytes s.mem seed a k=seedBytes u.mem seed a k) :
    RelCT isa (fun t v=>t=s ∧ v=u) (fullSampleCode sha3 sb ss off a k w16)
      (fun t v=>FullPostW w16 (xofByte (seedBytes s.mem seed a k)) p out initialS s t ∧
        FullPostW w16 (xofByte (seedBytes u.mem seed a k)) p out initialU u v) := by
  let R := fun t v : State=>FullPrefixPostW w16 (xofByte (seedBytes s.mem seed a k)) p out s t ∧
    FullPrefixPostW w16 (xofByte (seedBytes u.mem seed a k)) p out u v ∧
    t.syms=s.syms ∧ v.syms=u.syms
  have prelude : RelCT isa (fun t v=>t=s ∧ v=u) (fullPrefix sha3 sb ss off a k) R := by
    intro t v tr ur t' v' h et ev
    rcases h with ⟨ht,hv⟩; subst t; subst v
    exact ⟨fullPrefix_ct (sha3 := sha3) hss s u tr ur t' v' trivial trivial (agree_of sp (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl; exact s19.trans u19.symm; exact base)) et ev,
      exec_post (fullPrefix_ok (sha3 := sha3) hss hsb h8 hoff hk hk256 ps s19 svs) et,
      exec_post (fullPrefix_ok (sha3 := sha3) hss hsb h8 hoff hk hk256 pu u19 svu) ev,Exec.syms et,Exec.syms ev⟩
  have grouped : RelCT isa (fun t v=>t=s ∧ v=u) (.seq (fullPrefix sha3 sb ss off a k) (fullFinish w16)) (fun _ _=>True) := by
    refine RelCT.seq prelude ?_
    intro t v tr ur t' v' h et ev
    have t16 : t.gpr .x16=v.gpr .x16 := by
      rw [h.1.tablePtr,h.2.1.tablePtr,ps.symbol,pu.symbol]
    exact fullFinish_entry_relCT h.1.entry (by rw [seedEq]; exact h.2.1.entry)
      (h.1.keep.sp.trans (sp.trans h.2.1.keep.sp.symm)) (h.1.pointer.trans h.2.1.pointer.symm)
      t16 t v tr ur t' v' ⟨rfl,rfl⟩ et ev
  have trace : RelCT isa (fun t v=>t=s ∧ v=u) (fullSampleCode sha3 sb ss off a k w16) (fun _ _=>True) :=
    RelCT.assoc (RelCT.assoc grouped)
  intro t v tr ur t' v' h et ev
  rcases h with ⟨ht,hv⟩; subst t; subst v
  exact ⟨(trace s u tr ur t' v' ⟨rfl,rfl⟩ et ev).1,
    exec_post (ps.full_wp hss hsb h8 hoff hk hk256 s19 svs) et,
    exec_post (pu.full_wp hss hsb h8 hoff hk hk256 u19 svu) ev⟩

end VG.Proof.MlKem.AArch64.Paired

end

end

/-! # The odd final matrix entry has public-seed-only timing -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/LastPrepare.lean`, which only this module imported.
section

/-! # Shared-seed timing for the first singleton rejection pass -/
section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Proof.MlKem

structure LastPreparedW (w16 : Bool) (B : Nat→Byte) (p out table : Addr) (s t : State) : Prop where
 keep : Keep prepareRegs s t
 env : Rej8.EnvW w16 168 B (p+400) out t
 constants : Rej8.Constants t
 pointer : t.gpr .x19=p
 tablePtr : t.gpr .x16=table

theorem lastPrepare_ok {w16 : Bool} {s : State} {p seed out table : Addr} {sb ss off a k : Nat}
    (hss : ss<65536) (hsb : sb+32≤32768) (h8 : sb%8=0) (hk : 0<k) (hk256 : k≤256)
    (h : LastInput sb ss off p seed out table s) :
    WP isa (prepareCode sha3 sb ss a a k) s (LastPreparedW w16 (xofByte (seedBytes s.mem seed a k)) p out table s) := by
  refine WP.seq (WP.mono_syms (start_ok (sha3 := sha3) (a:=a) (b:=a) (k:=k) hss hsb h8
    h.ptr h.seedPtr h.readable h.context.scratch h.separate)
    fun u ⟨ku,fu,_,u19,_,_,bu,_⟩ sy => ?_)
  have cu := h.context.frame ku.rd ku.wr (fu.mono (by simp [fullWrites]))
  refine WP.mono_syms (Rej8.constants_ok u (by
    rw [u19]; exact Noise.inScratch cu.scratch (by decide) (by decide)))
    fun v ⟨kv,cv,mv,tv⟩ syv => ?_
  have fv : Frame [⟨p+1408,8⟩] u.mem v.mem := by
    rw [mv,u19]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 8)
  have fvBig : Frame (fullWrites p out) u.mem v.mem := fv.sub (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨p,2048⟩,by simp [fullWrites],Offset.sub_base p (by decide)⟩)
  have ctv := cu.frame kv.rd kv.wr fvBig
  have v19 : v.gpr .x19=p := (kv.get .x19).trans u19
  have v28 : v.gpr .x28=s.gpr .x28 := (kv.get .x28).trans (ku.get .x28)
  have v16 : v.gpr .x16=table := by rw [tv,syv,sy,h.symbol]
  have stream : ∀i<504,v.mem ((p+400)+BitVec.ofNat 64 i)=xofByte (seedBytes s.mem seed a k) i := by
    intro i hi
    have hd : ∀r∈[Region.mk (p+1408) 8],(Region.mk (p+400) 504).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact Offset.disjoint p (d := 400) (e := 1408) (n := 504) (k := 8) (by decide) (by decide) (by decide)
    exact (fv.bytes hd (by change 504≤2^64; decide) hi).trans (bu.xof hk hk256 hi)
  have ready : Rej8.TableReady v out :=
    ⟨by rw [v16]; exact ctv.artifact,by rw [v16]; exact ctv.readable,by rw [v16]; exact ctv.tableOut⟩
  have env := rejection_envW (w16 := w16) (off := 400) (N := 168) (by decide) (by decide)
    ctv.scratch ctv.output ctv.apart stream (fun _ hm => ready.read hm)
    (fun _ hm => ready.artifact.vector hm) (fun _ hm => ready.disjoint hm)
  exact ⟨ku.trans kv,env,cv,v19,v16⟩

end VG.Proof.MlKem.AArch64.Paired
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/LastStartTiming.lean`, which only this module imported.
section

section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Proof.MlKem

theorem lastStart_relCT {w16 : Bool} {s u : State} {p seed out table : Addr} {sb ss off a k : Nat}
    (hss : ss<65536) (hsb : sb+32≤32768) (h8 : sb%8=0) (hoff : off<65536)
    (hk : 0<k) (hk256 : k≤256)
    (ps : LastInput sb ss off p seed out table s) (pu : LastInput sb ss off p seed out table u)
    (sp : s.sp=u.sp) (base : s.gpr .x28=u.gpr .x28)
    (seedEq : seedBytes s.mem seed a k=seedBytes u.mem seed a k) :
    RelCT isa (fun t v=>t=s ∧ v=u) (lastStartCode sha3 sb ss a k off w16)
      (fun t v=>LastStartPostW w16 (xofByte (seedBytes s.mem seed a k)) p out table s t ∧
        LastStartPostW w16 (xofByte (seedBytes u.mem seed a k)) p out table u v) := by
  let R := fun t v : State=>LastPreparedW w16 (xofByte (seedBytes s.mem seed a k)) p out table s t ∧
    LastPreparedW w16 (xofByte (seedBytes u.mem seed a k)) p out table u v
  have start : RelCT isa (fun t v=>t=s ∧ v=u) (prepareCode sha3 sb ss a a k) R := by
    intro t v tr ur t' v' h et ev
    rcases h with ⟨ht,hv⟩; subst t; subst v
    exact ⟨prepare_ct (sha3 := sha3) sb ss a a k s u tr ur t' v' trivial trivial
      (agree_of sp (by intro r hr; rw [List.mem_singleton.mp hr]; exact base)) et ev,
      exec_post (lastPrepare_ok (sha3 := sha3) hss hsb h8 hk hk256 ps) et,
      exec_post (lastPrepare_ok (sha3 := sha3) hss hsb h8 hk hk256 pu) ev⟩
  have grouped : RelCT isa (fun t v=>t=s ∧ v=u)
      (.seq (prepareCode sha3 sb ss a a k) (Impl.MlKem.AArch64.Paired.reject 400 off .x22 w16)) (fun _ _=>True) := by
    refine RelCT.seq start ?_
    intro t v tr ur t' v' h et ev
    have ht28 := h.1.keep.get .x28
    have hv28 := h.2.keep.get .x28
    have rr := reject_relCT (by decide) hoff (by decide : Reg.x22≠.x3 ∧ Reg.x22≠.x4)
      (by rw [h.1.pointer,ht28,ps.outPtr]; exact h.1.env)
      (by rw [h.2.pointer,hv28,pu.outPtr]; rw [seedEq]; exact h.2.env)
      h.1.constants h.2.constants
      (h.1.keep.sp.trans (sp.trans h.2.keep.sp.symm)) (h.1.pointer.trans h.2.pointer.symm)
      (by rw [ht28,hv28,base]) (h.1.tablePtr.trans h.2.tablePtr.symm)
      t v tr ur t' v' ⟨rfl,rfl⟩ et ev
    exact ⟨rr.1,trivial⟩
  have trace : RelCT isa (fun t v=>t=s ∧ v=u) (lastStartCode sha3 sb ss a k off w16) (fun _ _=>True) :=
    RelCT.assoc (RelCT.assoc grouped)
  intro t v tr ur t' v' h et ev
  rcases h with ⟨ht,hv⟩; subst t; subst v
  exact ⟨(trace s u tr ur t' v' ⟨rfl,rfl⟩ et ev).1,
    exec_post (lastStart_ok (sha3 := sha3) hss hsb h8 hoff hk hk256 ps.ptr ps.seedPtr ps.outPtr ps.readable ps.separate ps.context ps.symbol) et,
    exec_post (lastStart_ok (sha3 := sha3) hss hsb h8 hoff hk hk256 pu.ptr pu.seedPtr pu.outPtr pu.readable pu.separate pu.context pu.symbol) ev⟩

end VG.Proof.MlKem.AArch64.Paired
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Proof.MlKem

def lastTail (sha3 : Bool) (sb ss a k off : Nat) (w16 : Bool := false) : Prog isa :=
 .seq (.ite (.zero .x .x22) (fullSampleCode sha3 sb ss off a k w16) (.block []))
  (.block (Impl.MlKem.AArch64.Paired.saved.zipIdx.reverse.map fun (r,i)=>.ldr .x r .x19 (1800+8*i)))

theorem LastInput.afterStart {w16 : Bool} {s t : State} {p seed out table : Addr} {sb ss off a k : Nat}
    (h : LastInput sb ss off p seed out table s)
    (ht : LastStartPostW w16 (xofByte (seedBytes s.mem seed a k)) p out table s t)
    (sy : t.syms=s.syms) : LastInput sb ss off p seed out table t :=
  ⟨by rw [ht.keep.get .x28]; exact h.ptr,by rw [ht.keep.get .x28]; exact h.seedPtr,
   by rw [ht.keep.get .x28]; exact h.outPtr,by rw [ht.keep.rd,ht.keep.wr]; exact h.readable,
   h.separate,ht.context,by rw [sy]; exact h.symbol⟩

theorem LastStartPostW.seed {w16 : Bool} {s t : State} {p seed out table : Addr} {a k : Nat}
    (h : LastStartPostW w16 (xofByte (seedBytes s.mem seed a k)) p out table s t)
    (hs : (Region.mk seed 32).Disjoint ⟨p,2048⟩)
    (ho : (Region.mk seed 32).Disjoint (polyRegion out)) :
    seedBytes t.mem seed a k=seedBytes s.mem seed a k := by
  unfold seedBytes
  rw [bytesAt_frame h.frame (by
    intro r hr; simp only [fullWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl; exact hs; exact ho) (by decide : 32≤2^64)]

theorem last_exec {w16 : Bool} {sb ss a k off : Nat} {s t : State} {tr : List Leak}
    (h : Exec isa (lastCode sha3 sb ss a k off w16) s tr t) :
    Exec isa (.seq (lastStartCode sha3 sb ss a k off w16) (lastTail sha3 sb ss a k off w16)) s tr t := by
  obtain ⟨_,_,_,rfl,ei,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,es,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,ec,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,er,h⟩ := seq_parts h
  have ee := Exec.seq (Exec.seq ei (Exec.seq es (Exec.seq ec er))) h
  simpa only [lastStartCode,lastTail,List.append_assoc] using ee

theorem lastCode_relCT {w16 : Bool} {s u : State} {p seed out table : Addr} {sb ss off a k : Nat}
    (hss : ss<4096) (hsb : sb+32≤32768) (h8 : sb%8=0) (hoff : off<65536)
    (hk : 0<k) (hk256 : k≤256)
    (ps : LastInput sb ss off p seed out table s) (pu : LastInput sb ss off p seed out table u)
    (ho : (Region.mk seed 32).Disjoint (polyRegion out))
    (sp : s.sp=u.sp) (base : s.gpr .x28=u.gpr .x28)
    (seedEq : seedBytes s.mem seed a k=seedBytes u.mem seed a k) :
    RelCT isa (fun t v=>t=s ∧ v=u) (lastCode sha3 sb ss a k off w16) (fun _ _=>True) := by
  let R := fun t v : State=>LastStartPostW w16 (xofByte (seedBytes s.mem seed a k)) p out table s t ∧
    LastStartPostW w16 (xofByte (seedBytes u.mem seed a k)) p out table u v ∧ t.syms=s.syms ∧ v.syms=u.syms
  have start : RelCT isa (fun t v=>t=s ∧ v=u) (lastStartCode sha3 sb ss a k off w16) R := by
    intro t v tr ur t' v' h et ev
    have hh := lastStart_relCT (sha3 := sha3) (by omega_using [hss]) hsb h8 hoff hk hk256 ps pu sp base seedEq
      t v tr ur t' v' h et ev
    rcases h with ⟨ht,hv⟩; subst t; subst v
    exact ⟨hh.1,hh.2.1,hh.2.2,Exec.syms et,Exec.syms ev⟩
  have branch : RelCT isa R (.ite (.zero .x .x22) (fullSampleCode sha3 sb ss off a k w16) (.block []))
      (fun t v=>t.sp=v.sp ∧ t.gpr .x19=v.gpr .x19) := by
    refine RelCT.ite ?_ ?_ (RelCT.block_nil ?_)
    · intro t v h
      have ht := h.1.flag
      have hv := h.2.1.flag
      rw [seedEq] at ht
      have hx := BitVec.eq_of_toNat_eq (ht.trans hv.symm)
      change some (t.gpr .x22==0)=some (v.gpr .x22==0)
      rw [hx]
    · intro t v tr ur t' v' h et ev
      have ht := h.1.1
      have hv := h.1.2.1
      have hh := fullSampleCode_relCT (sha3 := sha3) hss hsb h8 hoff hk hk256
        (ps.afterStart ht h.1.2.2.1) (pu.afterStart hv h.1.2.2.2) ht.ptr hv.ptr ht.saved hv.saved
        (ht.keep.sp.trans (sp.trans hv.keep.sp.symm))
        (by rw [ht.keep.get .x28,hv.keep.get .x28,base])
        (by rw [ht.seed ps.separate ho,hv.seed pu.separate ho,seedEq])
        t v tr ur t' v' ⟨rfl,rfl⟩ et ev
      exact ⟨hh.1,hh.2.1.keep.sp.trans ((ht.keep.sp.trans (sp.trans hv.keep.sp.symm)).trans hh.2.2.keep.sp.symm),
        hh.2.1.ptr.trans hh.2.2.ptr.symm⟩
    · intro t v h
      exact ⟨h.1.1.keep.sp.trans (sp.trans h.1.2.1.keep.sp.symm),h.1.1.ptr.trans h.1.2.1.ptr.symm⟩
  have grouped : RelCT isa (fun t v=>t=s ∧ v=u)
      (.seq (lastStartCode sha3 sb ss a k off w16) (lastTail sha3 sb ss a k off w16)) (fun _ _=>True) := by
    refine RelCT.seq start (RelCT.seq branch ?_)
    intro t v tr ur t' v' h et ev
    exact ⟨restore_ct t v tr ur t' v' trivial trivial
      (agree_of h.1 (by intro r hr; rw [List.mem_singleton.mp hr]; exact h.2)) et ev,trivial⟩
  intro t v tr ur t' v' h et ev
  exact grouped t v tr ur t' v' h (last_exec (sha3 := sha3) et) (last_exec (sha3 := sha3) ev)

end VG.Proof.MlKem.AArch64.Paired

end

end

/-! # Public-seed timing of the optimized encryption matrix -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Spec.MlKem
open VG.Proof.MlKem
variable {P : KemLay} {L : Layout}

theorem pair_input {s₀ s : State} (hp : Pre P L s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : KB P L s₀ s) (tb : MatrixTable P L s₀ s) :
    Paired.BeginInput SB SS (AH+1024*e) (AH+1024*(e+1))
      (sA L s₀ SS) (sA L s₀ SB) (aP L s₀ e) (aP L s₀ (e+1))
      (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have hw := hp.wf
  refine ⟨e28 h SS,e28 h SB,e28 h _,e28 h _,?_,
    sdisj hp (by lom) (by lom) (by decide),pair_context hp he h tb,rfl⟩
  intro j hj
  rw [ptr_add]
  exact in_R (cov_sr hp h (o:=SB) (l:=32) (by lom)) (k:=8*j) (by omega_using [hj]) (by omega_using [])

theorem last_input {s₀ s : State} (hp : Pre P L s₀) {e : Nat} (he : e<P.k*P.k)
    (h : KB P L s₀ s) (tb : MatrixTable P L s₀ s) :
    Paired.LastInput SB SS (AH+1024*e) (sA L s₀ SS) (sA L s₀ SB) (aP L s₀ e)
      (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have hw := hp.wf
  refine ⟨e28 h SS,e28 h SB,e28 h _,?_,
    sdisj hp (by lom) (by lom) (by decide),singleton_context hp he h tb,rfl⟩
  intro j hj
  rw [ptr_add]
  exact in_R (cov_sr hp h (o:=SB) (l:=32) (by lom)) (k:=8*j) (by omega_using [hj]) (by omega_using [])

end VG.Proof.MlKem.AArch64.Kem
