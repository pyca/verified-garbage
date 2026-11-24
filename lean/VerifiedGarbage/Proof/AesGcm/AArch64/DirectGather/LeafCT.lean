module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contract

import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.LoopCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.FragmentLoop
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.Guard
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.Setup
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Steps
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Gcm.Compose
public import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortSeal
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.FinishSpec
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.FinishCT
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.FragmentCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather

/-! Permissions and memory agreement for the short gather frame. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.AArch64 VG.Proof.AesGcm.AArch64.Gather
open VG.Impl.AesGcm.AArch64.DirectGather

/-- The largest bounded record body uses 752 stack bytes. Input slices may
be disjoint, or a single descriptor may name the destination itself. -/
abbrev boundedStack (s : State) : Region := ⟨s.sp - 752,752⟩

structure BoundedLay (s : State) (extraReads : List Region := []) : Prop where
  rd : s.rd = [kR .plain s,nR s,aR s,dsR s] ++ lsR s ++ (argR s :: extraReads)
  wr : s.wr = [dR s,tgR s]
  kd : (kR .plain s).Disjoint (dR s)
  dsDst : (dsR s).Disjoint (dR s)
  dt : (dR s).Disjoint (tgR s)
  da : (dR s).Disjoint (argR s)
  bk : (boundedStack s).Disjoint (kR .plain s)
  bn : (boundedStack s).Disjoint (nR s)
  ba : (boundedStack s).Disjoint (aR s)
  bds : (boundedStack s).Disjoint (dsR s)
  bl : ∀ r ∈ lsR s, (boundedStack s).Disjoint r
  barg : (boundedStack s).Disjoint (argR s)
  bd : (boundedStack s).Disjoint (dR s)
  bt : (boundedStack s).Disjoint (tgR s)
  w₁ : 752 ≤ s.sp.toNat
  hR : (s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14
  hgl : gl s (Cnt s) = L s
  ods : (Src s).toNat + Cnt s*16 ≤ 2^64
  source : (∀ r ∈ lsR s, r.Disjoint (dR s)) ∨
    (Cnt s = 1 ∧ sb s.mem (Src s) 0 = Dst s)

theorem BoundedLay.ofGather {s : State} (l : Gather.Lay .plain s) : BoundedLay s := by
  obtain ⟨rd,wr,kd,_,_,_,_,_,dsDst,_,ls,dt,da,_,_,_,_,_,_,sa,_⟩ := l.pre
  have sub : (boundedStack s).Sub (stkR s) := Offset.sub_below _ (by decide) (by decide)
  exact ⟨rd,wr,kd,dsDst,dt,da,l.bk.sub_left sub,l.bn.sub_left sub,l.ba.sub_left sub,l.bds.sub_left sub,
    fun r hr => (l.bl r hr).sub_left sub,sa.sub_left sub,l.bd.sub_left sub,l.bt.sub_left sub,
    Nat.le_trans (by decide) l.w₁,l.hR,l.hgl,l.ods, Or.inl fun r hr => (ls r hr).1⟩

theorem stackArg_contains (s : State) (i : Nat) (hi : i < 3) :
    (argR s).Contains (stackArgAddr s i) 8 := by
  change (⟨s.sp + BitVec.ofNat 64 (8*0),24⟩ : Region).Contains (s.sp + BitVec.ofNat 64 (8*i)) 8
  simp only [Nat.mul_zero,BitVec.add_zero]
  exact Offset.contains_base _ (by omega) (by omega)

namespace Compact

/-- Size of a bounded gather frame, within the existing ABI's stack allowance. -/
abbrev base (size : Fin 753) (s : State) := s.sp - BitVec.ofNat 64 size.val
abbrev scratch (size : Fin 753) (s : State) : Region := ⟨base size s,size.val⟩

theorem scratch_sub (size : Fin 753) (s : State) : (scratch size s).Sub (boundedStack s) :=
  Offset.sub_below _ (b := 752) (by have := size.isLt; omega) (by have := size.isLt; omega)

theorem scratchArg (size : Fin 753) (s : State) (i : Nat) :
    base size s + BitVec.ofNat 64 (size.val + 8*i) = stackArgAddr s i := by
  unfold base stackArgAddr
  rw [← Offset.add_add,BitVec.sub_add_cancel]

structure LocalMem (size : Fin 753) (s t : State) : Prop where
  frame : Frame [scratch size s] s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = scratch size s :: s.wr

theorem LocalMem.agree {size : Fin 753} {s t : State} (h : LocalMem size s t) {r : Region} (hd : (boundedStack s).Disjoint r)
    {x : Addr} (hx : r.Contains x 1) : t.mem x = s.mem x :=
  h.frame x fun q hq hy => by
    simp only [List.mem_singleton] at hq
    exact hd x (scratch_sub size s _ (hq ▸ hy)) hx

theorem LocalMem.descriptors {size : Fin 753} {s t : State} (h : LocalMem size s t) {extra : List Region} (l : BoundedLay s extra) :
    ∀ r ∈ Sig.descRegion 64 (Src s) (Cnt s) :: lsR s, ∀ a, r.Contains a 1 → s.mem a = t.mem a := by
  intro r hr a ha
  rcases List.mem_cons.mp hr with rfl|hr
  · exact (h.agree l.bds ha).symm
  · exact (h.agree (l.bl r hr) ha).symm

theorem LocalMem.read {size : Fin 753} {s t : State} (h : LocalMem size s t) :
    Covers (s.rd ++ s.wr) (t.rd ++ t.wr) := by
  rw [h.rd,h.wr]
  exact Covers.append (Covers.refl _) (Covers.of_mem fun _ hr => List.mem_cons_of_mem _ hr)

theorem LocalMem.arg {size : Fin 753} {s t : State} (h : LocalMem size s t) {extra : List Region} (l : BoundedLay s extra) (i : Nat) (hi : i < 3) :
    t.mem.readW (base size s + BitVec.ofNat 64 (size.val+8*i)) 64 = stackArg s i := by
  rw [scratchArg]
  change t.mem.read _ 8 = s.mem.read _ 8
  apply h.frame.read (r := argR s)
  · exact stackArg_contains s i hi
  · intro q hq
    simp only [List.mem_singleton] at hq
    subst q
    apply Region.Disjoint.sub_right _ (scratch_sub size s)
    exact l.barg.symm
  · decide

theorem LocalMem.argRead {size : Fin 753} {s t : State} (h : LocalMem size s t) {extra : List Region} (l : BoundedLay s extra) (i : Nat) (hi : i < 3) :
    InRegions (t.rd ++ t.wr) (base size s + BitVec.ofNat 64 (size.val+8*i)) 8 := by
  rw [scratchArg,h.rd]
  exact ⟨argR s, List.mem_append_left _ (by rw [l.rd]; simp),stackArg_contains s i hi⟩

theorem LocalMem.scratchWr {size : Fin 753} {s t : State} (h : LocalMem size s t) : Covers [scratch size s] t.wr :=
  Covers.of_mem fun r hr => by rw [h.wr]; exact List.mem_cons.mpr (.inl (List.mem_singleton.mp hr))


end Compact

abbrev size : Fin 753 := ⟨shortWork,by decide⟩
abbrev base (s : State) := s.sp - BitVec.ofNat 64 shortWork
abbrev scratch (s : State) : Region := ⟨base s,shortWork⟩
abbrev LocalMem := Compact.LocalMem size
abbrev scratch_sub := Compact.scratch_sub size
abbrev scratchArg := Compact.scratchArg size
abbrev blocks (s : State) := (L s+15)/16
abbrev textOff (s : State) := authO+112-16*blocks s

theorem descriptors_lt {s : State} {extra : List Region} (l : BoundedLay s extra) : 16 * Cnt s < 2^64 := by
  have bound := l.ods
  apply Nat.lt_of_not_ge
  intro h
  have eq : Cnt s * 16 = 2^64 := by omega
  apply l.bds (s.sp-752) (by simp [Region.Contains])
  change (((s.sp-752) - Src s).toNat + 1 ≤ Cnt s * 16)
  rw [eq]
  have := ((s.sp-752) - Src s).isLt
  omega

structure Cursors (s t : State) : Prop where
  d : t.gpr .x2 = Dst s
  auth : t.gpr .x3 = base s + BitVec.ofNat 64 (textOff s)
  key : t.gpr .x1 = base s + 16
  ds : t.gpr .x6 = Src s
  n : t.gpr .x7 = s.gpr .x7

/-- The same loop writes the caller's ciphertext and the padded GHASH slot for
either bounded layout. Its proof only needs the ordered keystream and output offsets. -/
theorem Compact.loopPre {size : Fin 753} {s t : State} {ko ao : Nat}
    {extra : List Region} (l : BoundedLay s extra) (h : Compact.LocalMem size s t)
    (dst : t.gpr .x2 = Dst s) (tagged : t.gpr .x3 = Compact.base size s + BitVec.ofNat 64 ao)
    (keystream : t.gpr .x1 = Compact.base size s + BitVec.ofNat 64 ko)
    (ds : t.gpr .x6 = Src s) (num : t.gpr .x7 = s.gpr .x7)
    (split : ko + L s ≤ ao) (high : ao + L s ≤ size.val) : Fragment.LoopPre t := by
  have ag := h.descriptors l
  have listEq := (Proof.AesGcm.listed_congr_le (Nat.le_refl _) ag).1
  have same := Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) ag
  have ht : Fragment.total t = L s := by
    simpa only [Fragment.total,Fragment.gl,Fragment.ds,Fragment.num,ds,num] using same.trans l.hgl
  let key : Region := ⟨Compact.base size s + BitVec.ofNat 64 ko,L s⟩
  let auth : Region := ⟨Compact.base size s + BitVec.ofNat 64 ao,L s⟩
  have keySub : key.Sub (Compact.scratch size s) := Offset.sub_base _ (by omega)
  have authSub : auth.Sub (Compact.scratch size s) := Offset.sub_base _ high
  have kApart : key.Disjoint auth :=
    Offset.disjoint _ (.inl split) (by have := size.isLt; omega) (by have := size.isLt; omega)
  have ed : Fragment.dout t = dR s := by simp only [Fragment.dout,dst,ht,dR]
  have ea : Fragment.gout t = auth := by simp only [Fragment.gout,tagged,ht,auth]
  have er : Fragment.readRegions t = dsR s :: key :: lsR s := by
    simp only [Fragment.readRegions,Fragment.descR,Fragment.stream,Fragment.num,num,keystream,ht,
      Fragment.ds,ds,listEq,dsR,Nat.mul_comm 16,key]
  have eo : Fragment.outRegions t = [dR s,auth] := by rw [Fragment.outRegions,ed,ea]
  have wr := l.wr
  have rd := l.rd
  have ro (r : Region) (hr : r ∈ dsR s :: lsR s) :
      r ∈ s.rd ∧ (Compact.scratch size s).Disjoint r := by
    rcases List.mem_cons.mp hr with rfl|hr
    · exact ⟨by rw [rd]; simp,l.bds.sub_left (Compact.scratch_sub size s)⟩
    · exact ⟨by rw [rd]; simp [hr],(l.bl _ hr).sub_left (Compact.scratch_sub size s)⟩
  have sd := l.bd.sub_left (Compact.scratch_sub size s)
  refine ⟨ht ▸ (by have := size.isLt; omega),by simpa [Fragment.num,num] using descriptors_lt l,?_,?_,?_,?_,?_⟩
  · rw [er,h.rd,h.wr]
    apply Covers.of_sub
    intro a ha
    by_cases e : a = key
    · subst a; exact ⟨Compact.scratch size s,by simp,ko,rfl,by change ko+L s ≤ size.val; omega⟩
    · have ra := (ro _ (by simpa [e] using ha)).1
      exact ⟨a,List.mem_append_left _ ra,0,by simp,by simp⟩
  · rw [eo,h.wr,wr]
    apply Covers.of_sub
    intro a ha
    rcases List.mem_cons.mp ha with rfl|ha
    · exact ⟨dR s,by simp,0,by simp,by simp⟩
    · obtain rfl := List.mem_singleton.mp ha
      exact ⟨Compact.scratch size s,by simp,ao,rfl,high⟩
  · intro r hr q hq
    rw [eo] at hq
    rcases List.mem_cons.mp hr with rfl|hr
    · change (⟨t.gpr .x6,16*Fragment.num t⟩ : Region).Disjoint q
      rw [ds,Fragment.num,num,Nat.mul_comm 16]
      rcases List.mem_cons.mp hq with rfl|hq
      · exact l.dsDst
      · obtain rfl := List.mem_singleton.mp hq
        exact ((l.bds.sub_left (Compact.scratch_sub size s)).sub_left authSub).symm
    · obtain rfl := List.mem_singleton.mp hr
      rw [show Fragment.stream t = key by simp only [Fragment.stream,ht,keystream,key]]
      rcases List.mem_cons.mp hq with rfl|hq
      · exact sd.sub_left keySub
      · simpa only [List.mem_singleton.mp hq] using kApart
  · intro i hi
    have mem : (Fragment.curBuf t i).reg (Fragment.curBuf t i).src ∈ lsR s := by
      have ix : i < Cnt s := by simpa only [Fragment.num,num,Cnt] using hi
      simpa only [Fragment.curBuf,Fragment.ds,Fragment.Buffers.reg,ds,listEq,lsR] using
        Gather.slice_mem t.mem (Src s) ix
    rcases l.source with apart | ⟨count,addr⟩
    · exact Or.inr fun r hr => by
        rw [eo] at hr
        rcases List.mem_cons.mp hr with rfl|hr
        · exact apart _ mem
        · obtain rfl := List.mem_singleton.mp hr
          exact (((l.bl _ mem).sub_left (Compact.scratch_sub size s)).sub_left authSub).symm
    · have one : Fragment.num t = 1 := by simpa only [Fragment.num,num,Cnt] using count
      have hz : i = 0 := by omega
      subst i
      refine Or.inl ⟨rfl,?_⟩
      have descBytes : ∀ j < Cnt s*16, s.mem (Src s + BitVec.ofNat 64 j) = t.mem (Src s + BitVec.ofNat 64 j) := by
        intro j hj
        exact ag _ (List.mem_cons_self ..) _ (Offset.contains_base _ (by omega) (by have := l.ods; omega))
      have samePtr := Gather.sb_agree (e₁ := s) (e₂ := t) descBytes (i := 0) (by omega)
      simpa [Fragment.curBuf,Fragment.gl,Fragment.ds,ds,dst,Fragment.off,Spec.Gcm.gatheredLen,Sig.listed]
        using samePtr.symm.trans addr
  · rw [ed,ea]; exact (sd.sub_left authSub).symm

theorem loopPre {s t : State} {extra : List Region} (l : BoundedLay s extra) (h : LocalMem s t) (p : Cursors s t)
    (hn : L s ≤ 96) : Fragment.LoopPre t := by
  apply Compact.loopPre (ko := 16) (ao := textOff s) l h p.d p.auth p.key p.ds p.n
  · change 16 + L s ≤ 336-16*((L s+15)/16); omega
  · change 336-16*((L s+15)/16)+L s ≤ 368; omega

end VG.Proof.AesGcm.AArch64.DirectGather

/-! Framing and scrubbing the short gather path. The caller selects this leaf
only for a standard nonce, one AAD block, and at most six ciphertext blocks. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.AArch64 VG.Impl.AesGcm.AArch64.DirectGather VG.Proof.AesGcm.AArch64.Gather
open VG.AArch64.Scrub VG.Impl.Scrub.AArch64

abbrev recordWithin (limit : Nat) (s : State) := NL s = 12 ∧ AL s ≤ 16 ∧ L s ≤ limit

abbrev shortRecord := recordWithin 96

def layoutRecordContract (pre : State → Prop) (limit : Nat) : Contract isa where
  pre s := pre s ∧ recordWithin limit s
  post := gatherPost
  pub := gatherPub

abbrev boundedRecordContract := layoutRecordContract (gatherPre .plain)
abbrev sharedBoundedContract := layoutRecordContract BoundedLay
abbrev shortContract := boundedRecordContract 96

private def shortSat : State :=
  { gatherSat with
    gpr := fun r => if r = .x3 then 12 else gatherSat.gpr r
    rd := [⟨0x1000,256⟩,⟨0x2000,12⟩,⟨0x3000,0⟩,⟨0x4000,0⟩,⟨0x9000,24⟩] }

theorem boundSat_pre (limit : Nat) : ∃ s, (boundedRecordContract limit).pre s := by
  have h : ∃ s, (Proof.AesGcm.sealGatherRoundsContract AArch64.abi 2592).pre s ∧ s = shortSat := by
    refine ⟨shortSat, ?_, rfl⟩
    sig_pre [Proof.AesGcm.sealGatherRoundsContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre,
      AArch64.abi, AArch64.argRegs, Gather.stackArgs_three, List.append_eq]
    simp [shortSat, gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    sig_and_intros <;> first | rfl | decide | exact Region.disjoint_of_sep (by decide)
  obtain ⟨s,hp,rfl⟩ := h
  exact ⟨shortSat, gatherPre_of_spec hp, by decide +kernel, by decide +kernel, Nat.zero_le _⟩

abbrev rawLeaf : Prog isa := .frame (.alloc shortWork) shortBody (.free shortWork)

abbrev leafFrame (bytes : Nat) (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 bytes,bytes⟩

theorem leafPost_frame {bytes : Nat} (hb : bytes ≤ 752) {s t : State} {extra : List Region} (l : BoundedLay s extra)
    (hq : gatherPost s t) {m : Mem} (fr : Frame [leafFrame bytes s] t.mem m) {v : State} (hm : v.mem = m) :
    gatherPost s v := by
  have sub : (leafFrame bytes s).Sub (boundedStack s) := Offset.sub_below _ (b := 752) hb (by omega)
  have d := bytesAt_frame fr (p := Dst s) (n := L s) (by
    simpa only [List.mem_singleton,forall_eq] using (l.bd.sub_left sub).symm) (Nat.le_of_lt (stackArg s 1).isLt)
  have tg := bytesAt_frame fr (p := Tg s) (n := 16) (by
    simpa only [List.mem_singleton,forall_eq] using (l.bt.sub_left sub).symm) (by decide)
  unfold gatherPost at hq ⊢
  rwa [hm,d,tg]

theorem shortSide : scrubSide rawLeaf shortWork 0 Impl.AesGcm.AArch64.Fn.own [] = true := by lit_decide

theorem keepsV_of_gatherSide {c : Prog isa} {bytes : Nat}
    (side : scrubSide c bytes 0 Impl.AesGcm.AArch64.Fn.own [] = true) :
    c.allInstrs keepsV = true := by
  simp only [scrubSide,Bool.and_eq_true] at side
  rw [Code.allInstrs_eq,List.all_eq_true]
  intro i hi
  have hi := List.all_eq_true.mp ((Code.allInstrs_eq _ _).symm.trans side.1.2) i hi
  simp only [sideI,Bool.and_eq_true] at hi
  have vk := hi.2
  unfold keepsV
  cases v : vdstOf i with
  | none => rfl
  | some w =>
    simp only [vkeeps,v] at vk
    cases w <;> first | rfl | contradiction

/-- The bounded direct paths share the public memory layout, stack allocation,
    ABI, timing and cleanup obligations. Only their inner bodies differ. -/
theorem boundedRaw_verified {limit bytes : Nat} (body : Prog isa)
    (size : 0 < bytes ∧ bytes ≤ 752 ∧ bytes % 16 = 0)
    (side : scrubSide (.frame (.alloc bytes) body (.free bytes)) bytes 0 Impl.AesGcm.AArch64.Fn.own [] = true)
    (correct : ∀ s, BoundedLay s → NL s = 12 → AL s ≤ 16 → L s ≤ limit →
      WP isa body (allocated bytes s) fun t => gatherPost s t ∧
        (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp - BitVec.ofNat 64 bytes)
    (timing : ∀ {a b}, BoundedLay a → BoundedLay b →
      recordWithin limit a → recordWithin limit b → gatherPub a b →
      RelCT isa (Eq2 (allocated bytes a) (allocated bytes b)) body TT) :
    Verified target (.frame (.alloc bytes) body (.free bytes)) (sharedBoundedContract limit) := by
  obtain ⟨sat,hp,hr⟩ := boundSat_pre limit
  refine ⟨?_,ct_of ?_,⟨sat,BoundedLay.ofGather (Gather.lay hp),hr⟩⟩
  · intro s ⟨hp,hn,ha,hl⟩
    have l := hp
    apply WP.withPreservedV (hc := keepsV_of_gatherSide side)
    refine WP.alloc ⟨size.1,by omega,size.2.2⟩ (by have := l.w₁; omega) ((correct s l hn ha hl).mono ?_)
    intro t ⟨out,g,sp⟩ m u hf
    exact ⟨⟨g,by change t.sp + BitVec.ofNat 64 bytes = s.sp; rw [sp,BitVec.sub_add_cancel]⟩,
      leafPost_frame size.2.1 l out hf rfl⟩
  · intro a b pa pb pub
    apply RelCT.alloc (P := Eq2 a b) (R := TT)
    exact (timing pa.1 pb.1 pa.2 pb.2 pub).mono
      (by rintro x y ⟨_,_,⟨rfl,rfl⟩,rfl,rfl⟩; exact ⟨rfl,rfl⟩) (fun _ _ h => h)

theorem boundedLeaf_verified {limit bytes : Nat} (body : Prog isa)
    (size : 0 < bytes ∧ bytes ≤ 752 ∧ bytes % 16 = 0)
    (side : scrubSide (.frame (.alloc bytes) body (.free bytes)) bytes 0 Impl.AesGcm.AArch64.Fn.own [] = true)
    (correct : ∀ s, BoundedLay s → NL s = 12 → AL s ≤ 16 → L s ≤ limit →
      WP isa body (allocated bytes s) fun t => gatherPost s t ∧
        (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp - BitVec.ofNat 64 bytes)
    (timing : ∀ {a b}, BoundedLay a → BoundedLay b →
      recordWithin limit a → recordWithin limit b → gatherPub a b →
      RelCT isa (Eq2 (allocated bytes a) (allocated bytes b)) body TT) :
    VerifiedScrubbed target (scrubAll bytes 0 Impl.AesGcm.AArch64.Fn.own
       (.frame (.alloc bytes) body (.free bytes))) (sharedBoundedContract limit) 0 := by
  let raw := Code.frame (.alloc bytes) body (.free bytes)
  have h : Verified target raw (sharedBoundedContract limit) := boundedRaw_verified body size side correct timing
  have hk : ScrubAllOk (sharedBoundedContract limit) bytes 0 := by
    refine ⟨fun s hs => by have := hs.1.w₁; omega,fun s t v hs out hm _ =>
      leafPost_frame size.2.1 hs.1 out (m := v.mem) ?_ rfl,fun _ _ hp => hp.2.2.2.2.2.2.2.2.1⟩
    intro a h
    exact hm a fun bad => h _ (List.mem_singleton_self _) (by change (a-(leafFrame bytes s).base).toNat+1 ≤ bytes; exact bad)
  obtain ⟨wf,kp,dit,rb⟩ := keeps_of_side side
  refine ⟨Verified.scrubAllOfV h hk side,?_, fun ty _ h => by cases ty <;> cases h⟩
  simp only [scrubSide,Nat.ne_of_gt size.1,↓reduceIte,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at side
  refine noResidue_scrubAll wf kp h ⟨size.1,by omega,size.2.2⟩ hk.sp side.1.1.1.1.1.2 dit ?_ rb
  intro a b _ n hn
  exact False.elim (List.not_mem_nil (of_decide_eq_true (List.all_eq_true.mp side.1.1.1.1.2 n hn)))

end VG.Proof.AesGcm.AArch64.DirectGather

/-! Prepare the authenticated-data prefix in the compact frame. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.AArch64 VG.Proof.AesGcm.AArch64.Gather VG.Impl.AesGcm.AArch64.DirectGather
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros)
open VG.WriteBytes

abbrev aadBytes (s : State) := bytesAt s.mem (Ad s) (AL s)
abbrev ghBase (s : State) := base s + BitVec.ofNat 64 authO
abbrev aadOff (s : State) := authO+96-16*blocks s

structure Header (s t : State) (len : Nat := L s) : Prop extends LocalMem s t where
  sp : t.sp = base s
  saved : SavedAt t.mem (base s) s
  x19 : t.gpr .x19 = base s
  x21 : t.gpr .x21 = K s
  x22 : t.gpr .x22 = s.gpr .x1
  x23 : t.gpr .x23 = Nn s
  x24 : t.gpr .x24 = BitVec.ofNat 64 (AL s)
  x25 : t.gpr .x25 = BitVec.ofNat 64 (16*((len+15)/16))
  x26 : t.gpr .x26 = BitVec.ofNat 64 len
  x6 : t.gpr .x6 = Src s
  x7 : t.gpr .x7 = s.gpr .x7

theorem enteredShort {s : State} (l : BoundedLay s) (hn : L s ≤ 96) :
    WP isa (.block shortSetup) (allocated shortWork s) fun t => Header s t ∧ t.gpr .x4 = Ad s := by
  let a := allocated shortWork s
  have localA : LocalMem s a := ⟨Frame.refl _ _,rfl,rfl⟩
  refine WP.mono (shortSetup_ok a hn localA.scratchWr (localA.argRead l 1 (by decide))
    (by simpa only [a,allocated,base,Nat.mul_one,L,BitVec.ofNat_toNat,BitVec.setWidth_eq] using localA.arg l 1 (by decide))) ?_
  intro t ⟨b,k,r,n,al,len,ceil,other,saved,fr,sp,rd,wr⟩
  have localT : LocalMem s t := ⟨fr.sub (fun q hq => by
    obtain rfl := List.mem_singleton.mp hq
    exact ⟨_,List.mem_singleton_self _, Offset.sub_base (base s) (by decide)⟩),rd,wr⟩
  exact ⟨⟨localT,sp,saved,b,k,r,n,(by simpa only [a,allocated,AL,BitVec.ofNat_toNat,BitVec.setWidth_eq] using al),ceil,len,other _ (by decide),other _ (by decide)⟩,
    other _ (by decide)⟩

theorem aadInput {s : State} (hn : L s ≤ 96) :
    aadOff s = authO + (96-16*blocks s) := by
  unfold aadOff authO blocks
  omega

/-- The zeroed input after filling the AAD slot. The following bytes form
the padded ciphertext slot, and the last 16 bytes will hold the lengths. -/
theorem paddedAad {m : Mem} {G : Addr} {k b : Nat} (aad : List Byte)
    (hb : b ≤ k) (hal : aad.length ≤ 16) (hs : 16*(k+2) < 2^64)
    (hz : bytesAt m G (16*(k+2)) = zeros (16*(k+2))) :
    bytesAt (writeBytes m (G + BitVec.ofNat 64 (16*(k-b))) aad) G (16*(k+2)) =
      zeros (16*(k-b)) ++ aad ++ zeros (16-aad.length) ++ zeros (16*b) ++ zeros 16 := by
  rw [Proof.AesCcm.bytesAt_writeBytes_at _ _ _ (by omega) hs, hz]
  simp only [zeros,List.take_replicate,List.drop_replicate,List.replicate_append_replicate,List.append_assoc]
  rw [Nat.min_eq_left (by omega)]
  congr 2
  congr 1
  omega

theorem zeroAad_layout {s : State} {m : Mem} (hn : L s ≤ 96) (hal : AL s ≤ 16)
    (hz : bytesAt m (ghBase s) 128 = zeros 128) :
    bytesAt (writeBytes m (base s + BitVec.ofNat 64 (aadOff s)) (aadBytes s)) (ghBase s) 128 =
      zeros (16*(6-blocks s)) ++ aadBytes s ++ zeros (16-AL s) ++ zeros (16*blocks s) ++ zeros 16 := by
  have bound : blocks s ≤ 6 := by unfold blocks; omega
  have al : (aadBytes s).length = AL s := Proof.AesCcm.length_bytesAt _ _ _
  rw [aadInput hn,← Offset.add_add,show 96-16*blocks s = 16*(6-blocks s) by omega]
  simpa only [al] using paddedAad (G := ghBase s) (k := 6) (b := blocks s)
    (aadBytes s) bound (by rw [al]; exact hal) (by decide) hz


abbrev aadLayout (s : State) := zeros (16*(6-blocks s)) ++ aadBytes s ++
  zeros (16-AL s) ++ zeros (16*blocks s) ++ zeros 16

theorem Header.advance {s t u : State} {len : Nat} (h : Header s t len) {d n : Nat}
    (f : Frame [⟨base s + BitVec.ofNat 64 d,n⟩] t.mem u.mem)
    (low : 216 ≤ d) (high : d+n ≤ shortWork)
    (g : ∀ r, r ∉ loopRegs → u.gpr r = t.gpr r) (sp : u.sp = t.sp)
    (rd : u.rd = t.rd) (wr : u.wr = t.wr) : Header s u len := by
  have subF : Frame [scratch s] t.mem u.mem := f.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_singleton_self _,Offset.sub_base _ high⟩
  refine ⟨⟨h.frame.trans subF,rd.trans h.rd,wr.trans h.wr⟩,sp.trans h.sp,h.saved.frame f ?_,
    (g _ (by decide)).trans h.x19,(g _ (by decide)).trans h.x21,(g _ (by decide)).trans h.x22,
    (g _ (by decide)).trans h.x23,(g _ (by decide)).trans h.x24,(g _ (by decide)).trans h.x25,
    (g _ (by decide)).trans h.x26,(g _ (by decide)).trans h.x6,(g _ (by decide)).trans h.x7⟩
  intro r hr; obtain rfl := List.mem_singleton.mp hr
  exact Offset.disjoint _ (.inl low) (by decide) (by change d+n ≤ 368 at high; omega)

/-- After setup and AAD absorption, only the short frame has changed. -/
theorem fillShort {s a : State} {len : Nat} (hn : len ≤ 96) (hal : AL s ≤ 16)
    (ba : (scratch s).Disjoint (aR s)) (ar : Covers [aR s] (s.rd ++ s.wr))
    (ha : Header s a len) (a4 : a.gpr .x4 = Ad s) :
    WP isa (.seq (.block shortZero) shortAad) a fun t =>
      Header s t len ∧ bytesAt t.mem (ghBase s) 128 =
        zeros (16*(6-(len+15)/16)) ++ aadBytes s ++ zeros (16-AL s) ++
        zeros (16*((len+15)/16)) ++ zeros 16 := by
  refine WP.seq ((shortZero_ok a ha.x19 ha.scratchWr).mono ?_)
  intro z ⟨zm,zg,zsp,zrd,zwr⟩
  have fz : Frame [⟨ghBase s,128⟩] a.mem z.mem := by
    rw [zm]; apply writeBytes_frame
    simpa using Region.contains_self (ghBase s) 128
  have hz := ha.advance fz (by decide) (by decide) (fun r _ => congrFun zg r) zsp zrd zwr
  have z0 : bytesAt z.mem (ghBase s) 128 = zeros 128 := by
    rw [zm]; exact bytesAt_writeBytes_self _ _ (List.replicate 128 0) (by simp)
  have z4 := (congrFun zg .x4).trans a4
  have al : (aadBytes s).length = AL s := Proof.AesCcm.length_bytesAt _ _ _
  have b6 : ((len+15)/16) ≤ 6 := by omega
  have asub : (⟨base s + BitVec.ofNat 64 ((authO+96-16*((len+15)/16))), AL s⟩ : Region).Sub (scratch s) :=
    Offset.sub_base _ (by change 224+96-16*((len+15)/16)+AL s ≤ 368; omega)
  have ad : bytesAt z.mem (z.gpr .x4) (AL s) = aadBytes s := by
    rw [z4]; exact bytesAt_frame hz.frame (by simpa only [List.mem_singleton,forall_eq] using
      ba.symm) (by omega)
  refine (shortAad_ok b6 z hz.x19 hz.x25 hz.x24 ?_).mono ?_
  · rw [z4]
    exact ⟨by omega,ar.trans hz.toLocalMem.read,
      covers_off hz.scratchWr (by change 224+96-16*((len+15)/16)+AL s ≤ 368; omega) (by decide),
      (ba.sub_left asub).symm⟩
  · intro t ⟨tm,tg,tsp,trd,twr⟩
    rw [ad] at tm
    have f : Frame [⟨base s+BitVec.ofNat 64 ((authO+96-16*((len+15)/16))),AL s⟩] z.mem t.mem := by
      rw [tm]; apply writeBytes_frame
      rw [al]; exact Region.contains_self _ _
    refine ⟨hz.advance f (by change 216 ≤ 224+96-16*((len+15)/16); omega)
      (by change 224+96-16*((len+15)/16)+AL s ≤ 368; omega) tg tsp trd twr,?_⟩
    rw [tm]
    have bound : (len+15)/16 ≤ 6 := by omega
    have address : authO+96-16*((len+15)/16) = authO+(96-16*((len+15)/16)) := by unfold authO; omega
    rw [address,← Offset.add_add,show 96-16*((len+15)/16) = 16*(6-((len+15)/16)) by omega]
    simpa only [al] using paddedAad (G := ghBase s) (k := 6) (b := ((len+15)/16))
      (aadBytes s) bound (by rw [al]; exact hal) (by decide) z0

theorem prefixShort {s : State} (l : BoundedLay s) (hn : L s ≤ 96) (hal : AL s ≤ 16) :
    WP isa (.seq (.block shortSetup) (.seq (.block shortZero) shortAad)) (allocated shortWork s)
      fun t => Header s t ∧ bytesAt t.mem (ghBase s) 128 = aadLayout s := by
  refine WP.seq ((enteredShort l hn).mono fun a ⟨ha,a4⟩ => fillShort hn hal
    (l.ba.sub_left (scratch_sub s)) ?_ ha a4)
  exact Covers.left (Covers.of_mem (fun r hr => by rw [l.rd,List.mem_singleton.mp hr]; simp))

end VG.Proof.AesGcm.AArch64.DirectGather

/-! Reconstruct the authenticated input after the fragment loop wrote the
ciphertext into its slot. The preceding AAD and trailing padding stay intact. -/

public section
namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.AArch64 VG.Proof.AesGcm.AArch64.Gather
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros padLen)

theorem fillSlot {m m' : Mem} {G : Addr} {dst : Region} {width : Nat} (small : width ≤ 2^64) (pre post ct : List Byte)
    (f : Frame [dst,⟨G+BitVec.ofNat 64 pre.length,ct.length⟩] m m')
    (hd : (⟨G,width⟩ : Region).Disjoint dst)
    (hs : pre.length+ct.length+post.length = width)
    (before : bytesAt m G width = pre ++ zeros ct.length ++ post)
    (filled : bytesAt m' (G+BitVec.ofNat 64 pre.length) ct.length = ct) :
    bytesAt m' G width = pre ++ ct ++ post := by
  have left : bytesAt m' G pre.length = pre := by
    rw [bytesAt_frame f (by
      intro r hr; rcases List.mem_cons.mp hr with rfl|hr
      · apply hd.sub_left; simpa using (Offset.sub_base G (d := 0) (n := pre.length) (k := width) (by omega))
      · obtain rfl := List.mem_singleton.mp hr
        exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)) (by omega),
      Proof.AesCcm.bytesAt_prefix _ _ (show pre.length ≤ width by omega),before,List.append_assoc,List.take_left]
  have right : bytesAt m' (G+BitVec.ofNat 64 (pre.length+ct.length)) post.length = post := by
    rw [bytesAt_frame f (by
      intro r hr; rcases List.mem_cons.mp hr with rfl|hr
      · exact hd.sub_left (Offset.sub_base _ (Nat.le_of_eq hs))
      · obtain rfl := List.mem_singleton.mp hr
        exact Offset.disjoint _ (.inr (Nat.le_refl _)) (by omega) (by omega)) (by omega),
      Proof.Cmac.Stream.bytesAt_offset _ _ (Nat.le_of_eq hs),before]
    rw [show pre.length+ct.length = (pre ++ zeros ct.length).length by simp [zeros], List.drop_left,List.take_length]
  rw [← hs,Proof.Cmac.Stream.bytesAt_append,Proof.Cmac.Stream.bytesAt_append,left,filled,right]

abbrev shortBlocks (len : Nat) := (len+15)/16
abbrev textOffset (len : Nat) := Impl.AesGcm.AArch64.DirectGather.authO + 112 - 16 * shortBlocks len
abbrev aadLayoutFor (s : State) (len : Nat) :=
  zeros (16*(6-shortBlocks len)) ++ aadBytes s ++ zeros (16-AL s) ++ zeros (16*shortBlocks len) ++ zeros 16

theorem authFilledFor {s : State} {m m' : Mem} {len : Nat} {dst : Region} (apart : (scratch s).Disjoint dst)
    (hn : len ≤ 96) (hal : AL s ≤ 16) (ct : List Byte) (hlen : ct.length = len)
    (f : Frame [dst,⟨base s + BitVec.ofNat 64 (textOffset len),len⟩] m m')
    (b : bytesAt m (ghBase s) 128 = (aadLayoutFor s len))
    (v : bytesAt m' (base s + BitVec.ofNat 64 (textOffset len)) len = ct) :
    bytesAt m' (ghBase s) 112 = zeros (16*(6-(shortBlocks len))) ++ aadBytes s ++ zeros (16-AL s) ++ ct ++
      zeros (padLen len) := by
  let pre := zeros (16*(6-(shortBlocks len))) ++ aadBytes s ++ zeros (16-AL s)
  have ha := Proof.AesCcm.length_bytesAt s.mem (Ad s) (AL s)
  change (aadBytes s).length = AL s at ha
  have hc : shortBlocks len ≤ 6 := by unfold shortBlocks; omega
  have hp : pre.length = 112-16*(shortBlocks len) := by simp [pre,zeros,ha]; omega
  have pad : len + padLen len = 16 * (shortBlocks len) := by unfold padLen shortBlocks; omega
  have u := fillSlot (width := 112) (by decide) (m := m) (m' := m') (G := ghBase s) (dst := dst)
    pre (zeros (padLen len)) ct
  have pos : ghBase s + BitVec.ofNat 64 pre.length = base s + BitVec.ofNat 64 (textOffset len) := by
    rw [hp,ghBase,Offset.add_add]
    congr 2
    unfold textOffset VG.Impl.AesGcm.AArch64.DirectGather.authO; omega
  apply u
  · simpa only [pos,hlen] using f
  · exact apart.sub_left (Offset.sub_base _ (by decide))
  · simp [hp,hlen,zeros]; omega
  · rw [Proof.AesCcm.bytesAt_prefix _ _ (show 112 ≤ 128 by decide),b]
    have eq : (aadLayoutFor s len) = (pre ++ zeros ct.length ++ zeros (padLen len)) ++ zeros 16 := by
      change (pre ++ zeros (16*(shortBlocks len))) ++ zeros 16 = _
      rw [List.append_assoc pre (zeros ct.length),show zeros ct.length ++ zeros (padLen len) = zeros (16*(shortBlocks len)) by
        rw [zeros,zeros,zeros,List.replicate_append_replicate,hlen,pad]]
    rw [eq,List.take_left']
    simp [hp,zeros,hlen]; omega
  · simpa only [pos,hlen] using v

theorem authFilled {s : State} {m m' : Mem} (l : BoundedLay s)
    (hn : L s ≤ 96) (hal : AL s ≤ 16) (ct : List Byte) (hlen : ct.length = L s)
    (f : Frame [dR s,⟨base s + BitVec.ofNat 64 (textOff s),L s⟩] m m')
    (b : bytesAt m (ghBase s) 128 = aadLayout s)
    (v : bytesAt m' (base s + BitVec.ofNat 64 (textOff s)) (L s) = ct) :
    bytesAt m' (ghBase s) 112 = zeros (16*(6-blocks s)) ++ aadBytes s ++ zeros (16-AL s) ++ ct ++
      zeros (padLen (L s)) :=
  authFilledFor (l.bd.sub_left (scratch_sub s)) hn hal ct hlen f b v

end VG.Proof.AesGcm.AArch64.DirectGather

/-! The seven AES lanes of short gather sealing use one round key at a time. -/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.DirectGather.Counters

open VG VG.AArch64
open VG.Impl.Gcm.AArch64.Stitch (breg)
open VG.Proof.Aes.AArch64.Aese
open VG.Proof.Gcm.AArch64.Stitch (breg_inj breg_ne_K kp sch)
open VG.Spec.Aes (addRoundKey roundKey cipher)

abbrev lanes := (List.range 7).map breg
abbrev roundVecs := VReg.v30 :: lanes

def roundCode (i : Nat) : List Instr :=
  .ldrq .v30 .x21 (16 * i) :: lanes.flatMap fun r =>
    [Instr.vop (.aese r .v30), .vop (.aesmc r r)]

def CanLoadKeys (nr : Nat) (s : State) : Prop :=
  ∀ i ≤ nr, InRegions (s.rd ++ s.wr) (s.gpr .x21 + BitVec.ofNat 64 (16 * i)) 16

theorem lane_mem {i : Nat} (hi : i < 7) : breg i ∈ lanes :=
  List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem load_frame (s : State) (v : BitVec 128) : VFrame roundVecs s (s.setV .v30 v) :=
  ⟨rfl,rfl,rfl,rfl,rfl,fun _ hr => setV_v_of_ne _ _ (fun e => hr (e ▸ List.mem_cons_self))⟩

theorem roundCode_ok {nr r : Nat} (hn : nr ≤ 14) (hr : r < nr)
    {s₀ s : State} (hk : CanLoadKeys nr s₀) (hf : VFrame roundVecs s₀ s)
    {x : VReg → Spec.Aes.State} (hI : RInv lanes (sch nr s₀) x r s) :
    WP isa (.block (roundCode r)) s fun t => RInv lanes (sch nr s₀) x (r + 1) t ∧ VFrame roundVecs s₀ t := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x21 + BitVec.ofNat 64 (16*r)) 16 := by
    rw [hf.rd,hf.wr,hf.gpr]; exact hk r (Nat.le_of_lt hr)
  unfold roundCode
  rw [WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by omega) hin, ?_⟩
  let key := s.mem.readW (s.gpr .x21 + BitVec.ofNat 64 (16*r)) 128
  have hkey : KeyIs key (roundKey (sch nr s₀) r) := by
    dsimp [key]; rw [hf.mem,hf.gpr]; exact keyIs_readW _ _ (by omega)
  have h30 : VReg.v30 ∉ lanes := by decide
  refine (each_ok _ (fun v k => aesMixColumns (aesMapBytes aesSbox (aesShiftRows (v ^^^ k))))
    .v30 (fun b t _ => rnd_run _ b t) lanes (s.setV .v30 key) (by decide) h30).mono fun t ⟨h, f⟩ => ?_
  refine ⟨fun b hb => ?_, (hf.trans (load_frame s key)).trans (f.mono (fun _ h => List.mem_cons_of_mem _ h))⟩
  have hne : b ≠ .v30 := fun e => h30 (e ▸ hb)
  rw [h b hb, setV_v_self, setV_v_of_ne _ _ hne]
  exact round_st hkey (hI b hb)

theorem rounds_ok {nr : Nat} (hn : nr ≤ 14) {s : State}
    (hk : CanLoadKeys nr s) (x : VReg → Spec.Aes.State)
    (hI : RInv lanes (sch nr s) x 0 s) :
    WP isa (.block ((List.range (nr - 1)).flatMap roundCode)) s fun t =>
      RInv lanes (sch nr s) x (nr-1) t ∧ VFrame roundVecs s t :=
  wp_range_flatMap (M := isa) (fun i t => RInv lanes (sch nr s) x i t ∧ VFrame roundVecs s t)
    (fun i _ hi ⟨h, f⟩ => roundCode_ok hn (by omega) hk f h) (nr-1) (Nat.le_refl _) s
    ⟨hI, VFrame.refl _ _⟩

def aese7 : List Instr := lanes.map fun r => Instr.vop (.aese r .v30)

theorem aese7_ok (s : State) : WP isa (.block aese7) s fun t =>
    (∀ b ∈ lanes, t.v b = aesMapBytes aesSbox (aesShiftRows (s.v b ^^^ s.v .v30))) ∧ VFrame lanes s t :=
  each_ok (fun b => [.vop (.aese b .v30)]) (fun v k => aesMapBytes aesSbox (aesShiftRows (v ^^^ k)))
    .v30 (fun _ _ _ => rfl) lanes s (by decide) (by decide)

def storeLane (base i : Nat) : List Instr :=
  let r := breg i
  [.vop (.logic .eor r r .v30), .strq r .x19 (base + 16 * i)]

def blockAddr (s : State) (base i : Nat) : Addr := s.gpr .x19 + BitVec.ofNat 64 (base + 16*i)

structure Stored (base i : Nat) (s t : State) : Prop where
  bytes : ∀ j < i, ∀ k < 16, t.mem (blockAddr s base j + BitVec.ofNat 64 k) =
    vbyte (s.v (breg j) ^^^ s.v .v30) k
  frame : Frame [⟨blockAddr s base 0,112⟩] s.mem t.mem
  pending : ∀ j, i ≤ j → j < 7 → t.v (breg j) = s.v (breg j)
  vecs : ∀ r ∉ lanes, t.v r = s.v r
  gpr : t.gpr = s.gpr
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem stores_ok {base : Nat} (s : State) (hb : base % 16 = 0) (hm : base + 112 ≤ 65536)
    (hw : ∀ i < 7, InRegions s.wr (blockAddr s base i) 16) :
    WP isa (.block ((List.range 7).flatMap (storeLane base))) s (Stored base 7 s) := by
  refine wp_range_flatMap (M := isa) (Stored base · s) (fun i u hi h => ?_) 7 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, fun _ _ _ => rfl, fun _ _ => rfl,
      rfl,rfl,rfl,rfl⟩
  have hin : InRegions u.wr (u.gpr .x19 + BitVec.ofNat 64 (base + 16*i)) 16 := by rw [h.wr,h.gpr]; exact hw i hi
  rw [storeLane, WP.block_cons_iff]
  refine ⟨_, (rfl : exec (.vop (.logic .eor (breg i) (breg i) .v30)) u =
    some (u.setV (breg i) (u.v (breg i) ^^^ u.v .v30))), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_strq (by constructor <;> omega) hin, WP.block_nil ?_⟩
  have addrEq : u.gpr .x19 + BitVec.ofNat 64 (base+16*i) = blockAddr s base i := by rw [h.gpr]; rfl
  have key := h.vecs .v30 (by decide)
  refine ⟨fun j hj k hk => ?_, ?_, fun j hj hj' => ?_, fun r hr => ?_, h.gpr,h.sp,h.rd,h.wr⟩
  · dsimp only
    rw [RegUpd.gpr_setV, RegUpd.mem_setV, addrEq, setV_v_self, key, h.pending _ (Nat.le_refl _) hi]
    by_cases e : j = i
    · subst j; exact Proof.AesGcm.AArch64.Stitch.write16_at _ _ _ hk
    · rw [Mem.write_apply, h.bytes j (by omega) k hk]
      simp only [blockAddr, Offset.add_add, Offset.add_sub_add_left, BitVec.toNat_sub, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show base + 16*j + k < 2^64 by omega),
        Nat.mod_eq_of_lt (show base + 16*i < 2^64 by omega)]
      omega
  · dsimp only; rw [RegUpd.gpr_setV,RegUpd.mem_setV,addrEq]
    apply h.frame.trans
    refine (Frame.refl _ _).write (List.mem_singleton_self _) _ ?_
    simp only [blockAddr,Nat.mul_zero,Nat.add_zero]
    rw [← Offset.add_add]
    exact Offset.contains_base _ (by omega) (by omega)
  · dsimp only
    rw [setV_v_of_ne _ _ (fun e => by have := breg_inj j (by omega) i (by omega) e; omega)]
    exact h.pending _ (by omega) hj'
  · dsimp only; rw [setV_v_of_ne _ _ (show r ≠ breg i from fun e => hr (e.symm ▸ lane_mem hi)),h.vecs r hr]


def lastCode (base nr : Nat) : List Instr :=
  [.ldrq .v30 .x21 (16*(nr-1))] ++ aese7 ++ [.ldrq .v30 .x21 (16*nr)] ++
    (List.range 7).flatMap (storeLane base)

structure BatchOut (base : Nat) (s t : State) (byteAt : Nat → Nat → Byte) : Prop where
  bytes : ∀ j < 7, ∀ k < 16, t.mem (blockAddr s base j + BitVec.ofNat 64 k) = byteAt j k
  frame : Frame [⟨blockAddr s base 0,112⟩] s.mem t.mem
  vecs : ∀ r ∉ roundVecs, t.v r = s.v r
  gpr : t.gpr = s.gpr
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem lastCode_ok {base nr : Nat} (hn : nr ≤ 14) {s₀ s : State} (hk : CanLoadKeys nr s₀)
    (hb : base % 16 = 0) (hm : base + 112 ≤ 65536)
    (hw : ∀ i < 7, InRegions s₀.wr (blockAddr s₀ base i) 16)
    (hf : VFrame roundVecs s₀ s) {x : VReg → Spec.Aes.State}
    (hI : RInv lanes (sch nr s₀) x (nr-1) s) :
    WP isa (.block (lastCode base nr)) s fun t =>
      BatchOut base s₀ t (fun j k => (cipher nr (sch nr s₀) (x (breg j))).getD k 0) := by
  have hin {u : State} (hf : VFrame roundVecs s₀ u) (i : Nat) (hi : i ≤ nr) :
      InRegions (u.rd ++ u.wr) (u.gpr .x21 + BitVec.ofNat 64 (16*i)) 16 := by
    rw [hf.rd,hf.wr,hf.gpr]; exact hk i hi
  unfold lastCode
  rw [List.append_assoc, List.append_assoc, List.singleton_append, WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by omega) (hin hf _ (by omega)), ?_⟩
  let K₁ := s.mem.readW (s.gpr .x21 + BitVec.ofNat 64 (16*(nr-1))) 128
  have key₁ : KeyIs K₁ (roundKey (sch nr s₀) (nr-1)) := by
    dsimp [K₁]; rw [hf.gpr,hf.mem]; exact keyIs_readW _ _ (by omega)
  rw [WP.block_append_iff]
  refine (aese7_ok (s.setV .v30 K₁)).mono fun u ⟨ea,fa⟩ => ?_
  have fu := (hf.trans (load_frame s K₁)).trans (fa.mono (fun _ h => List.mem_cons_of_mem .v30 h))
  rw [List.singleton_append, WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by omega) (hin fu _ (Nat.le_refl _)), ?_⟩
  let K₂ := u.mem.readW (u.gpr .x21 + BitVec.ofNat 64 (16*nr)) 128
  have key₂ : KeyIs K₂ (roundKey (sch nr s₀) nr) := by
    dsimp [K₂]; rw [fu.gpr,fu.mem]; exact keyIs_readW _ _ (by omega)
  have ff := fu.trans (load_frame u K₂)
  refine (stores_ok (u.setV .v30 K₂) hb hm (fun i hi => by
    unfold blockAddr; rw [ff.wr,ff.gpr]; exact hw i hi)).mono fun t h => ?_
  have ba : blockAddr (u.setV .v30 K₂) base = blockAddr s₀ base := by unfold blockAddr; rw [ff.gpr]
  refine ⟨fun j hj k hkt => ?_, by rw [← ba,← ff.mem]; exact h.frame,
    fun r hr => (h.vecs r (fun hm => hr (List.mem_cons_of_mem _ hm))).trans (ff.v _ hr),
    h.gpr.trans ff.gpr,h.sp.trans ff.sp,h.rd.trans ff.rd,h.wr.trans ff.wr⟩
  have hh := h.bytes j hj k hkt
  rw [ba, setV_v_self, setV_v_of_ne _ _ (breg_ne_K j), ea _ (lane_mem hj),
    setV_v_self, setV_v_of_ne _ _ (breg_ne_K j), ← getD_st _ hkt,
    last_st key₁ key₂ (hI _ (lane_mem hj))] at hh
  exact hh


def seedCode : List Instr := [.ldr .x .x9 .x23 0, .ldr .w .x10 .x23 8,
  .vop (.ins .d2 .v31 0 .x9), .vop (.ins .s4 .v31 2 .x10)]

def seedVec (s : State) : BitVec 128 :=
  setLane (setLane (s.v .v31) 64 0 (s.mem.readW (s.gpr .x23) 64)) 32 2
    (s.mem.readW (s.gpr .x23 + BitVec.ofNat 64 8) 32)

abbrev seedRegs : List Reg := [.x9,.x10,.x12]
abbrev seedVecs := VReg.v31 :: lanes

theorem seed_ok (s : State)
    (h₀ : InRegions (s.rd ++ s.wr) (s.gpr .x23 + BitVec.ofNat 64 0) 8)
    (h₈ : InRegions (s.rd ++ s.wr) (s.gpr .x23 + BitVec.ofNat 64 8) 4) :
    WP isa (.block seedCode) s fun t => t.v .v31 = seedVec s ∧ Fr seedRegs seedVecs s t := by
  rw [seedCode, WP.block_cons_iff]
  refine ⟨_, exec_ldr_x (by decide) h₀, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_ldr_w (n := .x23) (t := .x10) (off := 8) (s := s.write .x .x9 (s.mem.readW (s.gpr .x23 + BitVec.ofNat 64 0) 64)) (by decide) (by simpa only [RegUpd.rd_write, RegUpd.wr_write, RegUpd.gpr_write, reduceCtorEq, ite_false] using h₈), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_,rfl,?_⟩
  rw [WP.block_cons_iff]; refine ⟨_,rfl,WP.block_nil ?_⟩
  refine ⟨?_, ⟨fun r hr => ?_, fun r hr => ?_, rfl,rfl,rfl,rfl⟩⟩
  · simp [State.setV,State.write,seedVec]
  · have h9 : r ≠ .x9 := fun e => hr (e ▸ by decide)
    have h10 : r ≠ .x10 := fun e => hr (e ▸ by decide)
    simp [State.setV,State.write,h9,h10]
  · have h31 : r ≠ .v31 := fun e => hr (e ▸ List.mem_cons_self)
    simp [State.setV,State.write,h31]

def countCode (i : Nat) : List Instr :=
  let r := breg i
  [.vop (.logic .orr r .v31 .v31), .movz .w .x12 (BitVec.ofNat 16 (256*(i+1))) 1,
   .vop (.ins .s4 r 3 .x12)]

def countWord (i : Nat) : BitVec 32 :=
  (BitVec.ofNat 16 (256*(i+1))).setWidth 32 <<< 16

theorem count_ok (s : State) (i : Nat) :
    WP isa (.block (countCode i)) s fun t =>
      t.v (breg i) = setLane (s.v .v31) 32 3 (countWord i) ∧ Fr [.x12] [breg i] s t := by
  rw [countCode, WP.block_cons_iff]; refine ⟨_,rfl,?_⟩
  rw [WP.block_cons_iff]; refine ⟨_,rfl,?_⟩
  rw [WP.block_cons_iff]; refine ⟨_,rfl,WP.block_nil ?_⟩
  refine ⟨?_, ⟨fun r hr => ?_, fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · simp [State.setV,State.write,countWord]
  · simp only [List.mem_singleton] at hr
    simp [State.setV,State.write,hr]
  · simp only [List.mem_singleton] at hr
    simp [State.setV,State.write,hr]

theorem counts_ok (s : State) :
    WP isa (.block ((List.range 7).flatMap countCode)) s fun t =>
      (∀ j < 7, t.v (breg j) = setLane (s.v .v31) 32 3 (countWord j)) ∧ Fr seedRegs lanes s t := by
  refine wp_range_flatMap (M := isa) (fun i t =>
    (∀ j < i, t.v (breg j) = setLane (s.v .v31) 32 3 (countWord j)) ∧ Fr seedRegs lanes s t)
    (fun i u hi ⟨he,hf⟩ => ?_) 7 (Nat.le_refl _) s ⟨fun _ h => absurd h (Nat.not_lt_zero _), Fr.refl _ _ _⟩
  refine (count_ok u i).mono fun t ⟨ht,ft⟩ => ⟨fun j hj => ?_, hf.trans (ft.mono ?_ ?_)⟩
  · by_cases e : j = i
    · subst j; rw [ht,hf.v .v31 (by decide)]
    · rw [ft.v _ (by simpa using (fun h => e (breg_inj j (by omega) i (by omega) h) : breg j ≠ breg i))]
      exact he _ (by omega)
  · intro r hr; obtain rfl := List.mem_singleton.mp hr; decide
  · intro r hr; obtain rfl := List.mem_singleton.mp hr; exact lane_mem hi


abbrev nonce (s : State) : List Byte := Spec.Aes.bytesAt s.mem (s.gpr .x23) 12
abbrev jZero (s : State) := Spec.Gcm.ofBytes (nonce s ++ [0,0,0,1])

theorem jZero_eq (s : State) (H : Spec.Gcm.Block) : jZero s = Spec.Gcm.j0 H (nonce s) :=
  (Proof.Gcm.j0_12 _ (Proof.Cmac.bytesAt_length _ _ _)).symm

theorem jZero_low (s : State) : (jZero s).extractLsb' 0 32 = 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [jZero, Spec.Gcm.ofBytes, List.foldl_append, List.foldl_cons, List.foldl_nil, BitVec.toNat_ofNat,
    BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  change ((256 * (256 * (256 * (256 * Proof.Aes.beVal (nonce s) + 0) + 0) + 0) + 1) % 2^128) % 2^32 = 1
  omega

/-- The first twelve bytes of the template come from the two permitted nonce loads,
including the four-byte load at offset eight. -/
theorem seed_byte (s : State) {k : Nat} (hk : k < 12) :
    vbyte (seedVec s) k = s.mem (s.gpr .x23 + BitVec.ofNat 64 k) := by
  by_cases h : k < 8
  · rw [← Mem.extractLsb'_read s.mem (s.gpr .x23) (n := 8) h]
    apply BitVec.eq_of_getLsbD_eq; intro t ht
    simp only [vbyte, seedVec, setLane, Mem.readW, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
      BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_allOnes, Nat.mul_zero, BitVec.shiftLeft_zero]
    simp (disch := omega) only [decide_eq_true, Bool.not_true, Bool.not_false,
      Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.false_or, Bool.or_false]
  · have e : s.gpr .x23 + BitVec.ofNat 64 k =
        s.gpr .x23 + BitVec.ofNat 64 8 + BitVec.ofNat 64 (k-8) := by
      rw [Offset.add_add, Nat.add_sub_of_le (by omega)]
    rw [e, ← Mem.extractLsb'_read s.mem _ (n := 4) (by omega : k-8 < 4)]
    apply BitVec.eq_of_getLsbD_eq; intro t ht
    simp only [vbyte, seedVec, setLane, Mem.readW, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
      BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_allOnes]
    simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.not_true, Bool.not_false,
      Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.false_or, Bool.or_false]
    congr 1
    omega

theorem count_state (s : State) {i : Nat} (hi : i < 7) :
    st (setLane (seedVec s) 32 3 (countWord i)) = Proof.Aes.ctrState (jZero s) i := by
  apply st_ext; intro k hk
  rw [getD_st _ hk, Proof.Aes.ctrState, getD_ofFn hk, Proof.Aes.ctrBlock_byte _ _ hk, vbyte_setLane _ _ hk]
  by_cases h : k < 12
  · rw [ite_eq_left h, ite_eq_left h, seed_byte _ h, jZero, Proof.Aes.toBytes_ofBytes (by simp [nonce,Spec.Aes.bytesAt]) hk]
    have h' : k < (nonce s).length := by simpa [nonce,Spec.Aes.bytesAt] using h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h', ← List.getD_eq_getElem?_getD]
    exact (Proof.Gcm.getD_bytesAt' _ _ h).symm
  · rw [ite_eq_right h, ite_eq_right h, jZero_low, show countWord i = rev32 (1 + BitVec.ofNat 32 i) from
        (by decide : ∀ j < 7, countWord j = rev32 (1 + BitVec.ofNat 32 j)) i hi,
      rev32_byte _ (by omega)]
    congr 2
    omega


/-- The mask and six blocks of keystream, as encryptions of the successive
GCM counter blocks. The frame includes only their 112-byte destination. -/
structure KeysOut (base nr : Nat) (s t : State) : Prop where
  bytes : ∀ j < 7, ∀ k < 16, t.mem (blockAddr s base j + BitVec.ofNat 64 k) =
    (cipher nr (sch nr s) (Proof.Aes.ctrState (jZero s) j)).getD k 0
  frame : Frame [⟨blockAddr s base 0,112⟩] s.mem t.mem
  gpr : ∀ r ∉ seedRegs, t.gpr r = s.gpr r
  vecs : ∀ r ∉ VReg.v31 :: roundVecs, t.v r = s.v r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem shortKeys_ok {base nr : Nat} (s : State) (hn : nr ≤ 14)
    (h₀ : InRegions (s.rd ++ s.wr) (s.gpr .x23 + BitVec.ofNat 64 0) 8)
    (h₈ : InRegions (s.rd ++ s.wr) (s.gpr .x23 + BitVec.ofNat 64 8) 4)
    (hk : CanLoadKeys nr s) (hb : base % 16 = 0) (hm : base + 112 ≤ 65536)
    (hw : ∀ i < 7, InRegions s.wr (blockAddr s base i) 16) :
    WP isa (Impl.AesGcm.AArch64.DirectGather.shortKeys base nr) s (KeysOut base nr s) := by
  change WP isa (.block (seedCode ++ (List.range 7).flatMap countCode ++
    (List.range (nr-1)).flatMap roundCode ++ lastCode base nr)) s _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine (seed_ok s h₀ h₈).mono fun u ⟨seed,fs⟩ => ?_
  rw [WP.block_append_iff]
  refine (counts_ok u).mono fun v ⟨lanesReady,fc⟩ => ?_
  have f := fs.trans (fc.mono (fun _ h => h) (fun _ h => List.mem_cons_of_mem _ h))
  let x := fun r => st (v.v r)
  have hx : ∀ j < 7, x (breg j) = Proof.Aes.ctrState (jZero s) j := by
    intro j hj
    dsimp [x]
    rw [lanesReady _ hj, seed, count_state _ hj]
  have keys : CanLoadKeys nr v := fun i hi => by
    rw [f.rd,f.wr,f.gpr _ (by decide : Reg.x21 ∉ seedRegs)]; exact hk _ hi
  have hsch : sch nr v = sch nr s := by unfold Proof.Gcm.AArch64.Stitch.sch Proof.Gcm.AArch64.Stitch.kp; rw [f.mem, f.gpr _ (by decide)]
  have ba : blockAddr v base = blockAddr s base := by unfold blockAddr; rw [f.gpr _ (by decide)]
  rw [WP.block_append_iff]
  refine (rounds_ok hn keys x (fun _ _ => rfl)).mono fun t ⟨hi,ft⟩ => ?_
  refine (lastCode_ok hn keys hb hm (fun i hi => by rw [f.wr,ba]; exact hw i hi) ft hi).mono fun z hz => ?_
  refine ⟨fun j hj k hkt => ?_, ?_, fun r hr => ?_, fun r hr => ?_, hz.sp.trans f.sp, hz.rd.trans f.rd,
    hz.wr.trans f.wr⟩
  · rw [← ba,hz.bytes j hj k hkt,hx j hj,hsch]
  · rw [← f.mem,← ba]; exact hz.frame
  · rw [hz.gpr,f.gpr r hr]
  · have hrv : r ∉ roundVecs := fun h => hr (List.mem_cons_of_mem _ h)
    have hrs : r ∉ seedVecs := fun h => by
      rcases List.mem_cons.mp h with e | hl
      · exact hr (List.mem_cons.mpr (.inl e))
      · exact hrv (List.mem_cons_of_mem _ hl)
    rw [hz.vecs _ hrv,f.v _ hrs]

open VG.Spec.Gcm (aesWith toBytes blockAt inc32)
open VG.Proof.Gcm (ksByte)

/-- Block zero is the tag mask. -/
theorem KeysOut.mask {base nr : Nat} {s t : State} (h : KeysOut base nr s t) :
    blockAt t.mem (blockAddr s base 0) = aesWith nr (sch nr s) (jZero s) := by
  apply Proof.Aes.block_ext; intro k hk
  rw [Proof.Aes.toBytes_blockAt _ _ hk, h.bytes 0 (by decide) k hk, aesWith,
    Proof.Aes.toBytes_ofBytes (by simp) hk, Proof.Aes.getD_eq _ hk, List.getD_eq_getElem?_getD,
    Vector.getElem?_toList, Vector.getElem?_eq_getElem hk, Option.getD_some]
  rfl

/-- The following 96 bytes are the keystream starting at inc32(J₀). -/
theorem KeysOut.stream {base nr : Nat} {s t : State} (h : KeysOut base nr s t) {n : Nat} (hn : n < 96) :
    t.mem (blockAddr s base 1 + BitVec.ofNat 64 n) = ksByte (aesWith nr (sch nr s)) (inc32 (jZero s)) n := by
  have ha : blockAddr s base 1 + BitVec.ofNat 64 n =
      blockAddr s base (n / 16 + 1) + BitVec.ofNat 64 (n % 16) := by
    simp only [blockAddr,Offset.add_add]
    congr 2
    omega
  have ht : n % 16 < 16 := Nat.mod_lt _ (by decide)
  rw [ha,h.bytes _ (by omega) _ ht,ksByte,aesWith,Proof.Aes.toBytes_ofBytes (by simp) ht,
    Proof.Aes.getD_eq _ ht,List.getD_eq_getElem?_getD,Vector.getElem?_toList,Vector.getElem?_eq_getElem ht,
    Option.getD_some,Proof.Aes.ctrState,Proof.Gcm.repeat_add]
  rfl

end VG.Proof.AesGcm.AArch64.DirectGather.Counters

/-! The short-record key stream uses the original gather key and nonce, even
after initialization writes to the local frame. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.AArch64 VG.Proof.AesGcm.AArch64.Gather VG.Impl.AesGcm.AArch64.DirectGather
open VG.Proof.Gcm.AArch64.Stitch (sch kp)
open VG.Spec.Gcm (blockAt inc32 aesWith)
open VG.Spec.Aes (bytesAt)

structure KeysPhaseOut (o s t : State) : Prop where
  mask : blockAt t.mem (base o) = shortCipher o (shortJ0 o)
  stream : ∀ j < 96, t.mem (base o+16#64+BitVec.ofNat 64 j) = Proof.Gcm.ksByte (shortCipher o) (inc32 (shortJ0 o)) j
  frame : Frame [⟨base o,112⟩] s.mem t.mem
  mem : LocalMem o t
  gpr : Others [.x9,.x10,.x12,.x13,.x14] s t
  sp : t.sp = s.sp

theorem KeysPhaseOut.saved {o s t : State} (h : KeysPhaseOut o s t) (hs : SavedAt s.mem (base o) o) :
    SavedAt t.mem (base o) o :=
  hs.frame h.frame (by simpa only [List.mem_singleton, forall_eq] using
    (Offset.disjoint_base (base o) (d := 128) (n := 88) (k := 112) (by decide) (by decide)))

theorem KeysPhaseOut.auth {o s t : State} (h : KeysPhaseOut o s t) :
    bytesAt t.mem (base o+224#64) 112 = bytesAt s.mem (base o+224#64) 112 :=
  bytesAt_frame h.frame (by simpa only [List.mem_singleton, forall_eq] using
    (Offset.disjoint_base (base o) (d := 224) (n := 112) (k := 112) (by decide) (by decide))) (by decide)

theorem shortKeysPhaseFor (o s : State) (rounds : VG.Proof.AesGcm.AArch64.rounds (o.gpr .x1))
    (readNonce : Covers [nR o] (o.rd ++ o.wr)) (readKeys : Covers [kR .plain o] (o.rd ++ o.wr))
    (bn : (scratch o).Disjoint (nR o)) (bk : (scratch o).Disjoint (kR .plain o)) (m : LocalMem o s) (hn : NL o = 12)
    (x19 : s.gpr .x19 = base o) (x21 : s.gpr .x21 = K o) (x22 : s.gpr .x22 = o.gpr .x1)
    (x23 : s.gpr .x23 = Nn o) :
    WP isa (Impl.Gcm.AArch64.Stitch.byRounds (shortKeys streamO)) s (KeysPhaseOut o s) := by
  let N := (o.gpr .x1).toNat
  have hN : N ≤ 14 := by rcases rounds with e|e|e <;> simp [N,e]
  refine Stitch.byRoundsG_ok rounds (by simpa using x22) ?_
  intro u ug um _ usp urd uwr
  have k : u.gpr .x21 = K o := (ug _ (by decide) (by decide)).trans x21
  have n : u.gpr .x23 = Nn o := (ug _ (by decide) (by decide)).trans x23
  have w : u.gpr .x19 = base o := (ug _ (by decide) (by decide)).trans x19
  have nc : Covers [⟨Nn o,12⟩] (u.rd ++ u.wr) := by
    rw [urd,uwr,← hn]; exact readNonce.trans m.read
  have kc : Covers [⟨K o,256⟩] (u.rd ++ u.wr) := by
    rw [urd,uwr]; exact readKeys.trans m.read
  have wc : Covers [scratch o] u.wr := uwr ▸ m.scratchWr
  have keys : Counters.CanLoadKeys N u := by
    intro i hi; rw [k]; exact in_off kc (by omega) (by decide)
  have kw (j : Nat) : Counters.blockAddr u streamO j = base o + BitVec.ofNat 64 (16*j) := by
    simp only [Counters.blockAddr,w,streamO,Nat.zero_add]
  refine (Counters.shortKeys_ok u hN (by rw [n]; exact in_off nc (by decide) (by decide))
    (by rw [n]; exact in_off nc (by decide) (by decide)) keys (by decide) (by decide)
    (fun i hi => by rw [kw]; exact in_off wc (by change 16*i+16 ≤ 368; omega) (by decide))).mono ?_
  intro t h
  have kSub : Region.Sub ⟨K o,16*(N+1)⟩ (kR .plain o) := by
    intro x hx; change (x-K o).toNat+1 ≤ 256; change (x-K o).toNat+1 ≤ 16*(N+1) at hx; omega
  have ks : aesWith N (sch N u) = shortCipher o := by
    unfold sch kp
    rw [um,k,bytesAt_frame m.frame (by
      simpa only [List.mem_singleton, forall_eq] using (bk.symm.sub_left kSub))
      (by omega)]
    rfl
  have ns : Counters.jZero u = shortJ0 o := by
    unfold Counters.jZero Counters.nonce shortJ0
    rw [um,n,Proof.Gcm.j0_12 _ (by rw [Proof.Cmac.bytesAt_length,hn]), ← hn]
    rw [bytesAt_frame m.frame (by
      simpa only [List.mem_singleton, forall_eq] using bn.symm)
      (Nat.le_of_lt (o.gpr .x3).isLt)]
  have wf : Frame [⟨base o,112⟩] s.mem t.mem := by
    simpa only [kw, Nat.mul_zero, BitVec.add_zero, um] using h.frame
  have allW : Frame [scratch o] s.mem t.mem := wf.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, fun a ha => by
      change (a-base o).toNat+1 ≤ 368; change (a-base o).toNat+1 ≤ 112 at ha; omega⟩
  refine ⟨?_, ?_, wf, ⟨m.frame.trans allW, h.rd.trans (urd.trans m.rd), h.wr.trans (uwr.trans m.wr)⟩, ?_, h.sp.trans usp⟩
  · simpa only [kw,Nat.mul_zero,BitVec.add_zero,ks,ns] using h.mask
  · intro j hj; simpa only [kw,ks,ns] using h.stream hj
  · intro r hr
    have hs : r ∉ Counters.seedRegs := fun e => hr (by simpa [Counters.seedRegs] using
      (List.mem_append_left [.x13,.x14] e))
    exact (h.gpr _ hs).trans (ug _ (fun e => hr (by simp [e])) (fun e => hr (by simp [e])))

theorem shortKeysPhase (o s : State) (l : BoundedLay o) (m : LocalMem o s) (hn : NL o = 12)
    (x19 : s.gpr .x19 = base o) (x21 : s.gpr .x21 = K o) (x22 : s.gpr .x22 = o.gpr .x1)
    (x23 : s.gpr .x23 = Nn o) :
    WP isa (Impl.Gcm.AArch64.Stitch.byRounds (shortKeys streamO)) s (KeysPhaseOut o s) := by
  apply shortKeysPhaseFor o s l.hR _ _ (l.bn.sub_left (scratch_sub o)) (l.bk.sub_left (scratch_sub o)) m hn x19 x21 x22 x23
  all_goals exact Covers.left (Covers.of_mem (fun r hr => by rw [l.rd,List.mem_singleton.mp hr]; simp))

end VG.Proof.AesGcm.AArch64.DirectGather

/-! The short record body, from the original gather arguments to its ciphertext and tag. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.AArch64 VG.Proof.AesGcm.AArch64.Gather VG.Impl.AesGcm.AArch64.DirectGather
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt ctxH inc32 gctr)

/-- The fragment loop's initialized cursors and the data it reads. -/
structure Ready (o t : State) : Prop extends Header o t, Cursors o t where
  mask : blockAt t.mem (base o) = shortCipher o (shortJ0 o)
  stream : ∀ j < 96, t.mem (base o+16+BitVec.ofNat 64 j) =
    Proof.Gcm.ksByte (shortCipher o) (inc32 (shortJ0 o)) j
  input : bytesAt t.mem (ghBase o) 128 = aadLayout o

theorem readyShort {o s : State} (l : BoundedLay o) (iv : NL o = 12) (hn : L o ≤ 96)
    (h : Header o s) (input : bytesAt s.mem (ghBase o) 128 = aadLayout o) :
    WP isa (.seq (Impl.Gcm.AArch64.Stitch.byRounds (shortKeys streamO)) (.block shortPointers)) s (Ready o) := by
  have hc : blocks o ≤ 6 := by unfold blocks; omega
  refine WP.seq ((shortKeysPhase o s l h.toLocalMem iv h.x19 h.x21 h.x22 h.x23).mono ?_)
  intro k hk
  have sp := hk.sp.trans h.sp
  have k19 := (hk.gpr .x19 (by decide)).trans h.x19
  have k25 := (hk.gpr .x25 (by decide)).trans h.x25
  refine (shortPointers_ok hc k k19 k25 (by rw [sp]; exact hk.mem.argRead l 0 (by decide))).mono ?_
  intro t ⟨key,dst,auth,g,m,ts,tr,tw⟩
  have reg (r : Reg) (a : r ∉ [.x1,.x2,.x3]) (b : r ∉ [.x9,.x10,.x12,.x13,.x14]) :=
    (g r a).trans (hk.gpr r b)
  have header : Header o t := ⟨⟨m ▸ hk.mem.frame,tr.trans hk.mem.rd,tw.trans hk.mem.wr⟩,ts.trans sp,
    m ▸ hk.saved h.saved,(g _ (by decide)).trans k19,
    (reg _ (by decide) (by decide)).trans h.x21,(reg _ (by decide) (by decide)).trans h.x22,
    (reg _ (by decide) (by decide)).trans h.x23,(reg _ (by decide) (by decide)).trans h.x24,
    (g _ (by decide)).trans k25,(reg _ (by decide) (by decide)).trans h.x26,
    (reg _ (by decide) (by decide)).trans h.x6,(reg _ (by decide) (by decide)).trans h.x7⟩
  refine ⟨header,⟨dst.trans (by rw [sp]; exact hk.mem.arg l 0 (by decide)),auth,key,header.x6,header.x7⟩,
    m ▸ hk.mask, m ▸ hk.stream,?_⟩
  rw [m,bytesAt_frame hk.frame (by simpa only [List.mem_singleton,forall_eq,ghBase,authO] using
    (Offset.disjoint_base (base o) (d := 224) (n := 128) (k := 112) (by decide) (by decide))) (by decide),input]

theorem loopFinish {o s t : State} (l : BoundedLay o) (hn : L o ≤ 96) (al : AL o ≤ 16)
    (h : Ready o s) (p : Fragment.AtDesc s (Fragment.num s) t) :
    ShortFinishPre o t (base o) (6-blocks o) ∧ Frame [scratch o,dR o] s.mem t.mem := by
  have ag := h.toLocalMem.descriptors l
  have gl : Fragment.total s = L o := by
    simpa only [Fragment.total,Fragment.gl,Fragment.ds,Fragment.num,h.ds,h.n] using
      (Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) ag).trans l.hgl
  have plain : Fragment.pt s (Fragment.num s) = pt o (Cnt o) := by
    simpa only [Fragment.pt,Fragment.ds,Fragment.num,h.ds,h.n] using
      Proof.AesGcm.gathered_congr_le (Nat.le_refl _) ag
  let slot : Region := ⟨base o+BitVec.ofNat 64 (textOff o),L o⟩
  have f : Frame [dR o,slot] s.mem t.mem := by
    simpa only [Fragment.outRegions,Fragment.dout,Fragment.gout,gl,h.d,h.auth] using p.frame
  have slotSub : slot.Sub (scratch o) := Offset.sub_base _ (by
    change 224+112-16*blocks o+L o ≤ 368
    unfold blocks; omega)
  have ds := l.bd.sub_left (scratch_sub o)
  have ts := l.bt.sub_left (scratch_sub o)
  have small : Frame [scratch o,dR o] s.mem t.mem := f.sub fun r hr => by
    rcases List.mem_cons.mp hr with rfl|hr
    · exact ⟨_,by simp,fun _ => id⟩
    · exact ⟨_,List.mem_cons_self ..,List.mem_singleton.mp hr ▸ slotSub⟩
  have whole := (h.frame.mono (fun r hr => List.mem_cons.mpr (.inl (List.mem_singleton.mp hr)))).trans small
  have hashSub : Region.Sub ⟨K o+240#64,16⟩ (kR .plain o) := Offset.sub_base _ (by decide)
  have wr := l.wr
  have kd := l.kd
  have dt := l.dt
  have da := l.da
  have sa := l.barg
  let g (r : Reg) (hr : r ∉ Fragment.loopRegs) := p.gpr r hr
  have kc : Covers [kR .plain o] (t.rd ++ t.wr) := Covers.of_mem fun r hr => by
    rw [p.rd,h.rd,l.rd,List.mem_singleton.mp hr]; simp
  have hkey : Covers [⟨K o+240#64,16⟩] (t.rd ++ t.wr) := covers_off kc (by decide) (by decide)
  have ct := p.gctr (shortCipher o) (inc32 (shortJ0 o)) (fun j hj => by
    change j < Fragment.total s at hj; rw [gl] at hj
    simpa only [Fragment.off,h.key] using h.stream j (by omega))
  change bytesAt t.mem _ (Fragment.total s) = _ ∧ bytesAt t.mem _ (Fragment.total s) = _ at ct
  rw [h.d,h.auth,gl,plain] at ct
  have apart {r : Region} (a : (boundedStack o).Disjoint r) (b : r.Disjoint (dR o)) :
      ∀ q ∈ [scratch o,dR o], r.Disjoint q := by
    intro q hq; rcases List.mem_cons.mp hq with rfl|hq
    · exact (a.sub_left (scratch_sub o)).symm
    · exact List.mem_singleton.mp hq ▸ b
  have args : t.mem.readW (base o+384) 64 = Tg o := by
    rw [whole.readW (r := argR o) (by
      have e := scratchArg o 2
      change base o + 384 = stackArgAddr o 2 at e
      rw [e]; exact stackArg_contains o 2 (by decide))
      (apart sa da.symm) (by decide)]
    change o.mem.readW (base o + BitVec.ofNat 64 (shortWork+8*2)) 64 = _
    rw [scratchArg]; rfl
  have hc : blocks o ≤ 6 := by unfold blocks; omega
  refine ⟨⟨(g _ (by decide)).trans h.x19,(g _ (by decide)).trans h.x21,
    (g _ (by decide)).trans h.x24,(g _ (by decide)).trans h.x26,p.sp.trans h.sp,
    h.saved.frame f ?_,p.wr ▸ h.scratchWr,hkey,?_,?_,args,(l.bk.sub_left (scratch_sub o)).symm.sub_left hashSub,
    ds.symm,ts.symm,dt,al,?_,?_,ct.1,?_⟩,small⟩
  · intro r hr; rcases List.mem_cons.mp hr with rfl|hr
    · exact ds.sub_left (Offset.sub_base _ (by decide))
    · obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint _ (.inl (by change 128+88 ≤ 224+112-16*blocks o; omega)) (by decide)
        (by change 224+112-16*blocks o+L o ≤ 2^64; omega)
  · rw [p.rd,p.wr]; exact h.toLocalMem.argRead l 2 (by decide)
  · rw [p.wr,h.wr,wr]; exact ⟨tgR o,by simp,Region.contains_self _ _⟩
  · apply blockAt_frame whole
    exact fun r hr => (apart l.bk kd r hr).sub_left hashSub
  · rw [blockAt_frame f (by
      intro r hr; rcases List.mem_cons.mp hr with rfl|hr
      · exact ds.sub_left (by simpa using (Offset.sub_base (base o) (d := 0) (n := 16) (k := shortWork) (by decide)))
      · obtain rfl := List.mem_singleton.mp hr
        exact Offset.base_disjoint (base o) (by change 16 ≤ 224+112-16*blocks o; omega)
          (by change 224+112-16*blocks o+L o ≤ 2^64; omega)), h.mask]
  · exact authFilled l hn al _ (Proof.AesCcm.length_bytesAt _ _ _) f h.input (ct.2.trans ct.1.symm)


theorem shortBody_ok (hash : HashEightOk) (s : State) (l : BoundedLay s) (iv : NL s = 12) (al : AL s ≤ 16)
    (hn : L s ≤ 96) :
    WP isa shortBody (allocated shortWork s) fun t => gatherPost s t ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = base s := by
  have front := prefixShort l hn al
  unfold shortBody
  refine WP.seq ((WP.seq_iff.mp front).mono (fun _ w => WP.seq ((WP.seq_iff.mp w).mono (fun _ w => WP.seq (w.mono ?_)))))
  intro q ⟨header,input⟩
  have key := readyShort l iv hn header input
  refine WP.seq ((WP.seq_iff.mp key).mono (fun _ w => WP.seq (w.mono ?_)))
  intro t ready
  refine WP.seq ((Fragment.shortLoop_ok t (loopPre l ready.toLocalMem ready.toCursors hn)).mono ?_)
  intro z done
  have h := (loopFinish l hn al ready done).1
  exact (shortFinish_ok hash s z (base s) _ h).mono fun _ ⟨post,abi,sp,_,_,_⟩ => ⟨post,abi,sp⟩

end VG.Proof.AesGcm.AArch64.DirectGather

/-! The public lengths select the AES round count, the AAD layout, and each
descriptor's loop bounds. The two traces also share the tag output address. -/
public section
namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.AArch64 VG.Impl.AesGcm.AArch64.DirectGather VG.Proof.AesGcm.AArch64.Gather
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint ct_of)

theorem descriptorBytes_agree {a b u v : State} {extra : List Region} (la : BoundedLay a extra)
    (pub : gatherPub a b) (ds : u.gpr .x6 = Src a) (n : u.gpr .x7 = a.gpr .x7)
    (left : ∀ {x}, (dsR a).Contains x 1 → u.mem x = a.mem x)
    (right : ∀ {x}, (dsR b).Contains x 1 → v.mem x = b.mem x) :
    ∀ i < 16*Fragment.num u, u.mem (Fragment.off (Fragment.ds u) i) =
      v.mem (Fragment.off (Fragment.ds u) i) := by
  obtain ⟨_,_,_,_,_,_,q6,q7,_,_,_,_,_,descs⟩ := pub
  intro i hi
  have lim := descriptors_lt la
  have hi' : i < Cnt a * 16 := by simpa only [Fragment.num,n,Cnt,Nat.mul_comm] using hi
  have A : (dsR a).Contains (Src a + BitVec.ofNat 64 i) 1 := Offset.contains_base (Src a) (by omega : i+1 ≤ Cnt a*16) (by omega)
  have B : (dsR b).Contains (Src a + BitVec.ofNat 64 i) 1 := by
    change (dsR a).Contains (Src a + BitVec.ofNat 64 i) 1 at A
    simpa only [dsR,Src,Cnt,← q7,← q6] using A
  simp only [Fragment.off,Fragment.ds,ds]
  exact (left A).trans ((descs i hi').trans (right B).symm)

theorem shortBody_rel (hash : HashEightOk) {a b : State} (la : BoundedLay a) (lb : BoundedLay b)
    (ra : shortRecord a) (rb : shortRecord b) (pub : gatherPub a b) :
    RelCT isa (Eq2 (allocated shortWork a) (allocated shortWork b)) shortBody TT := by
  have originalPub := pub
  obtain ⟨q0,q1,q2,_,q4,q5,q6,q7,qsp,_,d,len,tag,_⟩ := pub
  obtain ⟨ai,aa,an⟩ := ra
  obtain ⟨bi,ba,bn⟩ := rb
  have w : base a = base b := by simp only [base,qsp]
  have blocksEq : blocks a = blocks b := by simp only [blocks,L,len]
  have al : AL a = AL b := congrArg BitVec.toNat q5
  have preRel : RelCT isa (Eq2 (allocated shortWork a) (allocated shortWork b))
      (.seq (.block shortSetup) (.seq (.block shortZero) shortAad)) TT := by
    refine rel_seq (rel_taint [] w (by agree_tac []) ⟨_,by taint_decide⟩) (enteredShort la an) (enteredShort lb bn) ?_
    intro u v ⟨p,p4⟩ ⟨q,q4'⟩
    exact rel_taint [.x4,.x19,.x24,.x25] (p.sp.trans (w.trans q.sp.symm))
      (by agree_tac [p4,q4',Ad,q4,p.x19,q.x19,p.x24,q.x24,p.x25,q.x25,al,w,blocksEq]) ⟨_,by taint_decide⟩
  unfold shortBody
  apply VG.RelCT.assoc
  apply VG.RelCT.assoc
  refine rel_seq (Fast.RelCT.assoc' preRel) (VG.WP.assoc' (prefixShort la an aa))
    (VG.WP.assoc' (prefixShort lb bn ba)) ?_
  intro e f ⟨p,pin⟩ ⟨q,qin⟩
  apply VG.RelCT.assoc
  refine rel_seq (rel_taint [.x19,.x21,.x22,.x23,.x25] (p.sp.trans (w.trans q.sp.symm))
    (by agree_tac [p.x19,q.x19,p.x21,q.x21,p.x22,q.x22,p.x23,q.x23,p.x25,q.x25,K,Nn,q0,q1,q2,w,blocksEq])
    ⟨_,by taint_decide⟩) (readyShort la ai an p pin) (readyShort lb bi bn q qin) ?_
  intro u v hu hv
  have preU := loopPre la hu.toLocalMem hu.toCursors an
  have preV := loopPre lb hv.toLocalMem hv.toCursors bn
  have lp : Fragment.LoopPub u v := by
    refine ⟨hu.sp.trans (w.trans hv.sp.symm),hu.ds.trans (q6.trans hv.ds.symm),
      congrArg BitVec.toNat (hu.n.trans (q7.trans hv.n.symm)),?_,hu.d.trans (d.trans hv.d.symm),?_,?_⟩
    · rw [hu.key,hv.key,w]
    · rw [hu.auth,hv.auth,textOff,textOff,blocksEq,w]
    · exact descriptorBytes_agree la originalPub hu.ds hu.n (hu.toLocalMem.agree la.bds) (hv.toLocalMem.agree lb.bds)
  refine rel_seq (Fragment.shortLoop_rel preU preV lp) (Fragment.shortLoop_ok u preU) (Fragment.shortLoop_ok v preV) ?_
  intro x y hx hy
  have aFin := (loopFinish la an aa hu hx).1
  have bFin := (loopFinish lb bn ba hv hy).1
  exact shortFinish_rel hash aFin (w ▸ bFin) q0 tag

/-- The public gather entry supplies the disjoint case of the shared leaf. -/
theorem BoundedLay.forGather {c : Prog isa} {lim : Nat}
    (v : VerifiedScrubbed target c (sharedBoundedContract lim) 0) :
    VerifiedScrubbed target c (boundedRecordContract lim) 0 := by
  have pre : ∀ {s}, (boundedRecordContract lim).pre s → (sharedBoundedContract lim).pre s :=
    fun h => ⟨BoundedLay.ofGather (Gather.lay h.1),h.2⟩
  refine ⟨⟨fun s hp => v.verified.1 s (pre hp),?_,boundSat_pre lim⟩,?_,fun ty _ h => by cases ty <;> cases h⟩
  · intro a b τ υ a' b' pa pb pub
    exact v.verified.2.1 a b τ υ a' b' (pre pa) (pre pb) pub
  · intro a b τ υ a' b' pa pb pub
    exact v.noResidue a b τ υ a' b' (pre pa) (pre pb) pub

theorem shortLeaf_verified (hash : HashEightOk) : VerifiedScrubbed target shortLeaf shortContract 0 :=
  BoundedLay.forGather (boundedLeaf_verified shortBody (by decide) shortSide (shortBody_ok hash) (shortBody_rel hash))

end VG.Proof.AesGcm.AArch64.DirectGather
