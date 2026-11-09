module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
public import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.OuterBlocks
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native

theorem orZero {w : Nat} (x : BitVec w) : x ||| (0 : BitVec w)=x := BitVec.or_zero
theorem zeroOr {w : Nat} (x : BitVec w) : (0 : BitVec w) ||| x=x := BitVec.zero_or

def scanWords {w : Nat} : List (BitVec w) → Nat → Nat → BitVec w → BitVec w
  | [],_,_,acc => acc
  | x::xs,k,d,acc => scanWords xs (k+1) d (acc ||| if d=k then x else 0)

theorem scan_outside {w : Nat} (xs : List (BitVec w)) (k d : Nat) (acc : BitVec w)
    (outside : d<k ∨ k+xs.length≤d) : scanWords xs k d acc=acc := by
  induction xs generalizing k acc with
  | nil => rfl
  | cons x xs ih =>
    have ne : d≠k := by simp only [List.length_cons] at outside; omega_arith
    simp only [scanWords,ne,ite_false,orZero]
    exact ih (k+1) acc (by simp only [List.length_cons] at outside; omega_arith)

theorem scan_selected {w : Nat} (xs : List (BitVec w)) (k d : Nat) (acc : BitVec w)
    (lo : k≤d) (hi : d<k+xs.length) :
    scanWords xs k d acc=acc ||| xs.getD (d-k) 0 := by
  induction xs generalizing k acc with
  | nil => simp only [List.length_nil,Nat.add_zero] at hi; omega_arith
  | cons x xs ih =>
    by_cases eq : d=k
    · subst d
      simp only [scanWords,ite_true,Nat.sub_self,List.getD_cons_zero]
      exact scan_outside xs (k+1) k (acc ||| x) (Or.inl (by omega_arith))
    · have hdk : k+1≤d := by omega_arith
      have hlen : d<k+1+xs.length := by simp only [List.length_cons] at hi; omega_arith
      have index : d-k=(d-(k+1))+1 := by omega_arith
      simp only [scanWords,eq,ite_false,orZero,index,List.getD_cons_succ]
      exact ih (k+1) acc hdk hlen

theorem scan_sixteen {w : Nat} (xs : List (BitVec w)) (len : xs.length=16)
    (d : Nat) (bound : d≤16) (identity : BitVec w) :
    scanWords xs 1 d (if d=0 then identity else 0)=if d=0 then identity else xs.getD (d-1) 0 := by
  by_cases zero : d=0
  · subst d
    simp only [ite_true]
    exact scan_outside xs 1 0 identity (Or.inl (by decide))
  · simp only [zero,ite_false]
    rw [scan_selected xs 1 d 0 (by omega_arith) (by omega_arith),zeroOr]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64

def scanVectorCode (acc : VReg) (offset : Nat) : List Instr := [
  .ldrq .v18 .x17 offset,
  .vop (.logic .and .v18 .v18 .v17),
  .vop (.logic .orr acc acc .v18)]

theorem scan_vector_ok (s : State) (acc : VReg) (offset : Nat)
    (ha : acc≠.v18) (c : Prop) [Decidable c]
    (mask : s.v .v17=if c then BitVec.allOnes 128 else 0)
    (aligned : offset%16=0 ∧ offset<4096*16)
    (region : InRegions (s.rd++s.wr) (s.gpr .x17+BitVec.ofNat 64 offset) 16) :
    WP isa (.block (scanVectorCode acc offset)) s fun t =>
      t.v acc=s.v acc ||| (if c then s.mem.read (s.gpr .x17+BitVec.ofNat 64 offset) 16 else 0) ∧
      VKeep [] [.v18,acc] s t := by
  unfold scanVectorCode
  apply wp_ldrq aligned region
  apply wp_vop (d:=.v18) (x:=s.mem.read (s.gpr .x17+BitVec.ofNat 64 offset) 16 &&& s.v .v17) (by simp [VOp.eval,RegUpd.v_setV])
  apply wp_vop (d:=acc) (x:=s.v acc ||| (s.mem.read (s.gpr .x17+BitVec.ofNat 64 offset) 16 &&& s.v .v17)) (by simp [VOp.eval,RegUpd.v_setV,ha])
  apply WP.block_nil
  constructor
  · simp only [RegUpd.v_setV,ite_true,ha,ite_false,mask]
    by_cases hc : c
    · simp only [hc,ite_true,BitVec.and_allOnes]
    · simp [hc]
  · exact ((VKeep.setV s .v18 _).mono (by simp) (by simp)).trans
      (((VKeep.setV _ .v18 _).mono (by simp) (by simp)).trans
        ((VKeep.setV _ acc _).mono (by simp) (by simp)))

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64

def readVectors (m : Mem) (p : Addr) (d : Nat) : Nat → List (BitVec 128)
  | 0 => []
  | n+1 => m.read (p+BitVec.ofNat 64 d) 16::readVectors m p (d+16) n

def scanVectors : List VReg → Nat → List Instr
  | [],_ => []
  | r::rs,d => scanVectorCode r d++scanVectors rs (d+16)

def ScanReadable (s : State) (size : Nat) : Prop :=
  ∀d,d+16≤size → InRegions (s.rd++s.wr) (s.gpr .x17+BitVec.ofNat 64 d) 16

theorem scan_vectors_ok (c : Prop) [Decidable c] : ∀(rs : List VReg) {s : State} {d size : Nat},
    rs.Nodup → (∀r∈rs,r≠VReg.v18 ∧ r≠VReg.v17) → d+16*rs.length≤size → d%16=0 → size≤65536 →
    ScanReadable s size → s.v .v17=(if c then BitVec.allOnes 128 else 0) →
    WP isa (.block (scanVectors rs d)) s fun t =>
      rs.map t.v=List.zipWith (fun x y => x ||| if c then y else 0) (rs.map s.v)
        (readVectors s.mem (s.gpr .x17) d rs.length) ∧ VKeep [] (.v18::rs) s t
  | [],s,_,_,_,_,_,_,_,_,_ => by
    exact WP.block_nil ⟨rfl,VKeep.refl _ _ s⟩
  | r::rs,s,d,size,nd,apart,hd,hd16,enc,readable,mask => by
    have nr := (List.nodup_cons.mp nd).1
    have ha := apart r (by simp)
    rw [scanVectors,WP.block_append_iff]
    refine WP.mono (scan_vector_ok s r d ha.1 c mask (by constructor <;> simp only [List.length_cons] at hd <;> omega_arith)
      (readable d (by simp only [List.length_cons] at hd; omega_arith))) fun u ⟨e,ku⟩ => ?_
    have readableU : ScanReadable u size := by
      intro j hj
      rw [ku.rd,ku.wr,ku.gpr .x17 (by simp)]
      exact readable j hj
    have maskU : u.v .v17=(if c then BitVec.allOnes 128 else 0) :=
      (ku.v .v17 (by simp [ha.2.symm])).trans mask
    refine WP.mono (scan_vectors_ok c rs (List.nodup_cons.mp nd).2
      (fun x hx => apart x (List.mem_cons_of_mem r hx))
      (by simp only [List.length_cons] at hd; omega_arith) (by omega_arith) enc readableU maskU)
      fun t ⟨rest,kt⟩ => ?_
    have keptR : t.v r=u.v r := kt.v r (by simp [ha.1,nr])
    have restOld : rs.map u.v=rs.map s.v := List.map_congr_left fun x hx =>
      ku.v x (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; exact ⟨(apart x (List.mem_cons_of_mem r hx)).1,fun e => nr (e ▸ hx)⟩)
    have keptP : u.gpr .x17=s.gpr .x17 := ku.gpr .x17 (by simp)
    rw [ku.mem,keptP,restOld] at rest
    refine ⟨?_,(ku.mono (by simp) (by
        intro a h
        rcases List.mem_cons.mp h with h|h
        · subst a; exact List.mem_cons_self
        · have e := List.mem_singleton.mp h
          subst a; exact List.mem_cons_of_mem _ (List.mem_cons_self))).trans
      (kt.mono (by simp) (by
        intro a h
        rcases List.mem_cons.mp h with h|h
        · subst a; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))⟩
    simp only [List.map_cons,List.length_cons,readVectors,List.zipWith_cons_cons,keptR,e,rest]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64

def scanMaskCode (k : Nat) : List Instr := [
  .movz .x .x4 k 0,
  .subs .x .x4 .x2 .x4,
  .subImm .x .x16 .x3 1,
  .cselc .x .x4 .x16 .x3 .eq,
  .vop (.dup .d2 .v17 .x4)]

theorem scan_mask_ok (s : State) (k : Nat) (hk : k<65536) (hz : s.gpr .x3=0) :
    WP isa (.block (scanMaskCode k)) s fun t =>
      t.gpr .x4=(if s.gpr .x2=BitVec.ofNat 64 k then BitVec.allOnes 64 else 0) ∧
      t.v .v17=(if s.gpr .x2=BitVec.ofNat 64 k then BitVec.allOnes 128 else 0) ∧
      Keeps [.x4,.x16] s t ∧ (∀r,r≠.v17 → t.v r=s.v r) := by
  have subWord (x y : Word) : addCarry x (~~~y) true=x-y := by
    change x+~~~y+1#64=x-y
    rw [BitVec.add_assoc,←BitVec.neg_eq_not_add]
    exact BitVec.add_neg_eq_sub
  have zf (u : State) (x y : Word) : (u.addWithCarry .x .x4 x (~~~y) true).zf=decide (x=y) := by
    change decide (addCarry x (~~~y) true=0#64)=decide (x=y)
    rw [subWord]
    apply decide_eq_decide.mpr
    rw [BitVec.sub_eq_iff_eq_add,BitVec.zero_add]
  have imm : (BitVec.ofNat 16 k).setWidth 64=BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hk]
  apply WP.of_runBlock
  simp only [scanMaskCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    Nat.mul_zero,Nat.reduceLT,VOp.eval,Option.map_some,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.gpr_setV,
    RegUpd.zf_write,CondCode.holds,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
    BitVec.shiftLeft_zero,BitVec.natCast_eq_ofNat,imm,hz,zf,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,⟨?_,?_,?_,?_,?_⟩,?_⟩
  · by_cases hc : s.gpr .x2=BitVec.ofNat 64 k <;> simp only [hc,decide_true,decide_false,ite_true,ite_false] <;> rfl
  · by_cases hc : s.gpr .x2=BitVec.ofNat 64 k <;> simp only [hc,decide_true,decide_false,ite_true,ite_false] <;> rfl
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setV,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,hr.1,hr.2,ite_false]
  · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry,RegUpd.mem_setV]
  · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry,RegUpd.rd_setV]
  · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry,RegUpd.wr_setV]
  · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry,RegUpd.sp_setV]
  · intro r hr
    simp only [RegUpd.v_setV,hr,ite_false,RegUpd.v_write ]
    rfl

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Ed25519.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native

def lookupAccs : List VReg := [.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7,.v16]
def lookupEntryOffset (k : Nat) : Nat := 216*(k-1)
def lookupEntryCode (k : Nat) : List Instr := scanMaskCode k++
  ([.addImm .x .x17 .x26 (lookupEntryOffset k)]++scanVectors lookupAccs 0)

def lookupEntriesCode : List Instr := ((List.range 16).map (fun i => lookupEntryCode (i+1))).flatten

theorem lookupEntries_source : lookupEntriesCode=(outerBlock142.drop 90).take 528 := by lit_decide

structure LookupTableReadable (s : State) (table : Addr) : Prop where
  reg : s.gpr .x26=table
  read : ∀d,d+16≤3456 → InRegions (s.rd++s.wr) (table+BitVec.ofNat 64 d) 16

theorem lookup_pointer_ok (s : State) (d : Nat) (hd : d<4096) :
    WP isa (.block [.addImm .x .x17 .x26 d]) s fun t =>
      t.gpr .x17=s.gpr .x26+BitVec.ofNat 64 d ∧ Keeps [.x17] s t ∧ t.v=s.v := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,hd,
    RegUpd.gpr_write,BitVec.setWidth_eq,ite_true,Option.some.injEq,exists_eq_left']
  exact ⟨True.intro,⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),rfl,rfl,rfl,rfl⟩,rfl⟩

private theorem lookup_index_eq (d k : Nat) (hd : d≤16) (hk : k≤16) :
    (BitVec.ofNat 64 d=BitVec.ofNat 64 k) ↔ d=k := by
  constructor
  · intro e
    have h := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_arith : d<2^64),
      Nat.mod_eq_of_lt (by omega_arith : k<2^64)] at h
    exact h
  · intro e; rw [e]

theorem lookup_entry_ok {s : State} {table : Addr} {d : Nat} (k : Nat)
    (hk : 1≤k ∧ k≤16) (hd : d≤16) (digit : s.gpr .x2=BitVec.ofNat 64 d) (zero : s.gpr .x3=0)
    (ht : LookupTableReadable s table) :
    WP isa (.block (lookupEntryCode k)) s fun t =>
      lookupAccs.map t.v=List.zipWith (fun x y => x ||| if d=k then y else 0) (lookupAccs.map s.v)
        (readVectors s.mem (table+BitVec.ofNat 64 (lookupEntryOffset k)) 0 9) ∧
      VKeep [.x4,.x16,.x17] (.v17::.v18::lookupAccs) s t := by
  rw [lookupEntryCode,WP.block_append_iff]
  refine WP.mono (scan_mask_ok s k (by omega_arith) zero) fun u ⟨_,mask,ku,vec⟩ => ?_
  have km : VKeep [.x4,.x16] [.v17] s u :=
    ⟨ku.gpr,ku.mem,ku.rd,ku.wr,ku.sp,fun r hr => vec r (by simpa only [List.mem_singleton] using hr)⟩
  rw [digit] at mask
  simp only [lookup_index_eq d k hd hk.2] at mask
  rw [WP.block_append_iff]
  refine WP.mono (lookup_pointer_ok u (lookupEntryOffset k) (by dsimp only [lookupEntryOffset]; omega_arith))
    fun v ⟨pointer,kv,vvec⟩ => ?_
  have frame : VKeep [.x4,.x16,.x17] [.v17] s v :=
    (km.mono (by simp) (by simp)).trans
      ⟨fun r hr => kv.gpr r (by simp_all),kv.mem,kv.rd,kv.wr,kv.sp,fun r _ => congrFun vvec r⟩
  have p : v.gpr .x17=table+BitVec.ofNat 64 (lookupEntryOffset k) := by
    rw [pointer,ku.gpr .x26 (by decide),ht.reg]
  have readable : ScanReadable v 144 := by
    intro j hj
    rw [frame.rd,frame.wr,p,VG.Offset.add_ofNat_add_ofNat]
    exact ht.read (lookupEntryOffset k+j) (by dsimp only [lookupEntryOffset]; omega_arith)
  have vm : v.v .v17=(if d=k then BitVec.allOnes 128 else 0) := by rw [vvec]; exact mask
  refine WP.mono (scan_vectors_ok (d=k) lookupAccs (by decide) (by decide)
    (by decide) (by decide) (by decide) readable vm) fun t ⟨values,kt⟩ => ?_
  have old : lookupAccs.map v.v=lookupAccs.map s.v := List.map_congr_left fun r hr =>
    frame.v r ((by decide : ∀r∈lookupAccs,r∉[VReg.v17]) r hr)
  rw [frame.mem,p,old] at values
  exact ⟨values,(frame.mono (by simp) (by simp)).trans (kt.mono (by simp) (by intro a ha; exact List.mem_cons_of_mem .v17 ha))⟩

end VG.Proof.Weierstrass.AArch64.P521Native
