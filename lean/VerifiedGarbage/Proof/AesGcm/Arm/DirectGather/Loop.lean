module

public import VerifiedGarbage.Impl.AesGcm.Arm.DirectGather
public import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.AesGcm.Arm.Flush
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcm.Arm.CTCrypt
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.AesGcm.Arm.DirectGather
public import VerifiedGarbage.Proof.AesGcm.Arm.Gather.LoopCT
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

@[expose] public section

/-! Continue the AES counter stream across an out-of-place source fragment.
A partial first block consumes only the bytes left in the saved keystream block. -/


namespace VG.Proof.AesGcm.Arm.DirectGather

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)
open VG.Proof.Gcm (Ctr xorKs)
open VG.Impl.AesGcm.Arm.DirectGather

structure In (c st w sp k7 k8 : BitVec 32) (R P : Nat) (S D : BitVec 32) (n : Nat) (s : State) : Prop where
  env : Env c st w sp k7 k8 s
  src : DataOk st w sp s S n
  data : DataW c st w sp k7 k8 s D n
  mode : CrMode true c st w sp S D n
  r4 : s.gpr .r4 = S
  r2 : s.gpr .r2 = D
  r5 : s.gpr .r5 = BitVec.ofNat 32 n
  r6 : s.gpr .r6 = BitVec.ofNat 32 (P%16)
  r8 : s.gpr .r8 = BitVec.ofNat 32 R
  rounds : R=10 ∨ R=12 ∨ R=14


variable {c st w sp k7 k8 : BitVec 32} {R P n : Nat} {S D : BitVec 32} {s : State} {icb : Block}

private theorem emptyHead {t : State} (h : In c st w sp k7 k8 R P S D n s)
    (zero : n=0 ∨ P%16=0) (k : Keeps s t)
    (reg : ∀ r, r ≠ .r3 → r ≠ .r12 → t.gpr r = s.gpr r) :
    WP isa (.block [.mov .r6 (.reg .r2)]) t
      (CrMidG true c st w sp k7 k8 R icb P S D n s.mem 0) := by
  refine WP.of_runBlock ⟨_,by arun [],?_⟩
  have other (r : Reg) (hr : r ≠ .r6) (h3 : r ≠ .r3) (h12 : r ≠ .r12) :
      (t.setReg .r6 (t.gpr .r2)).gpr r = s.gpr r := by rw [gpr_setReg,ite_eq_right hr,reg r h3 h12]
  refine ⟨h.env.keep (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl <;> exact other _ (by decide) (by decide) (by decide))
      k.sp k.rd k.wr,Nat.zero_le _,?_,?_,?_,h.rounds,h.data.of_eq k.rd k.wr,?_,?_,?_,?_,?_,?_,h.src.of_eq k.rd k.wr,h.mode⟩
  · rw [other _ (by decide) (by decide) (by decide),h.r4,add_ofNat_zero]
  · rw [other _ (by decide) (by decide) (by decide),h.r5,Nat.sub_zero]
  · rw [other _ (by decide) (by decide) (by decide),h.r8]
  · intro hc; simpa only [mem_setReg,k.mem,Nat.add_zero] using hc
  · intro _; rfl
  · rw [mem_setReg,k.mem]
  · simpa only [Nat.sub_zero,Nat.add_zero] using zero
  · rw [mem_setReg,k.mem]; exact Frame.refl _ _
  · intro _; simp only [gpr_setReg,ite_true,reg .r2 (by decide) (by decide),h.r2,add_ofNat_zero]

abbrev remainCode : Prog isa := .seq (.block [addI .r1 .r10 64,.dp .add .r1 .r1 (.reg .r6),
  .dp .sub .r5 .r5 (.reg .r3)]) (xorLoopG true)

private theorem consume {t : State} {k : Nat} (L : Lay c st w sp) (h : In c st w sp k7 k8 R P S D n s)
    (hP : P%16 ≠ 0) (hk : k = min (16-P%16) n) (pos : 0 < k)
    (pre : Keeps s t) (reg : ∀ r, r ≠ .r3 → r ≠ .r12 → t.gpr r = s.gpr r)
    (h3 : t.gpr .r3 = BitVec.ofNat 32 k) :
    WP isa (.seq remainCode (.block [.mov .r6 (.reg .r2)])) t
      (CrMidG true c st w sp k7 k8 R icb P S D n s.mem k) := by
  have hk16 : P%16+k ≤ 16 := by have := Nat.mod_lt P (by decide : 0 < 16); omega
  have hkn : k ≤ n := by omega
  have len := h.data.ok.lt32
  obtain ⟨u,run,r1,r5,other,keep⟩ : ∃ u, runBlock isa [addI .r1 .r10 64,.dp .add .r1 .r1 (.reg .r6),
      .dp .sub .r5 .r5 (.reg .r3)] t = some u ∧ u.gpr .r1 = st+BitVec.ofNat 32 (64+P%16) ∧
      u.gpr .r5 = BitVec.ofNat 32 (n-k) ∧ (∀ r, r ≠ .r1 → r ≠ .r5 → u.gpr r = t.gpr r) ∧ Keeps t u := by
    refine ⟨_,by arun [],?_,?_,?_,?_⟩
    · simp [gpr_setReg,reg .r10 (by decide) (by decide),reg .r6 (by decide) (by decide),
        h.env.r10,h.r6,add32_ofNat_assoc]
    · simp [gpr_setReg,reg .r5 (by decide) (by decide),h.r5,h3,ofNat_sub32 hkn len]
    · intro r a b; simp [gpr_setReg,a,b]
    · exact ⟨rfl,rfl,rfl,rfl⟩
  have same := pre.trans keep
  have g (r : Reg) (a : r ≠ .r1) (b : r ≠ .r5) (c : r ≠ .r3) (d : r ≠ .r12) :=
    (other r a b).trans (reg r c d)
  have eK := L.stA (d := 64+P%16) (by omega)
  have lp : LoopPre u (st+BitVec.ofNat 32 (64+P%16)) D k := by
    refine ⟨r1,(g _ (by decide) (by decide) (by decide) (by decide)).trans h.r2,
      (other _ (by decide) (by decide)).trans h3,pos,by omega,?_,?_,?_,?_,?_⟩
    · rw [L.stN (by omega)]; have := L.sw; omega
    · have := h.data.ok.fit; omega
    · rw [same.rd,same.wr,eK]; exact covers_left (h.env.perm.stC (by omega))
    · rw [same.wr]; exact (h.data.take hkn).wr
    · rw [eK]; exact ((h.data.take hkn).ok.st.sub_right (Lay.stSub (by omega))).symm
  have xs : XSrc true u S D k := ⟨(g _ (by decide) (by decide) (by decide) (by decide)).trans h.r4,
    by have := h.src.fit; omega, by rw [same.rd,same.wr]; exact covers_prefix h.src.rd hkn,
    h.mode.1.imp id (fun hd => (hd.sub_left (Region.sub_prefix hkn)).sub_right (Region.sub_prefix hkn))⟩
  refine WP.seq (WP.seq (WP.of_runBlock ⟨u,run,(xorLoopG_ok u lp xs).mono ?_⟩))
  intro z ⟨mz,z4,_,z2,_,gz,rd,wr,sp'⟩
  rw [eK,same.mem] at mz
  have hxl := length_xorBytes s.mem (State.addr S) (State.addr st+BitVec.ofNat 64 (64+P%16)) k
  have fw : Frame [⟨State.addr D,k⟩] s.mem z.mem := by rw [mz]; exact writeBytes_frame' _ hxl
  have gr (r : Reg) (hr : r ∈ [Reg.r7,.r8,.r9,.r10,.r11]) : z.gpr r = s.gpr r := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl <;>
      exact (gz _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (g _ (by decide) (by decide) (by decide) (by decide))
  let v := z.setReg .r6 (z.gpr .r2)
  have hv (r : Reg) (hr : r ∈ [Reg.r7,.r8,.r9,.r10,.r11]) : v.gpr r = s.gpr r := by
    have ne : r ≠ .r6 := by intro eq; subst r; simp at hr
    rw [show v.gpr r = z.gpr r by simp [v,gpr_setReg,ne],gr r hr]
  have rdv := rd.trans same.rd
  have wrv := wr.trans same.wr
  refine WP.of_runBlock ⟨v,by arun [v],h.env.keep hv (sp'.trans same.sp) rdv wrv,hkn,?_,?_,?_,
    h.rounds,h.data.of_eq rdv wrv,?_,?_,?_,?_,?_,?_,h.src.of_eq rdv wrv,h.mode⟩
  · simpa only [v,gpr_setReg,reduceCtorEq,ite_false,xsrc,ite_true] using z4
  · rw [show v.gpr .r5 = z.gpr .r5 by rfl,gz _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),r5]
  · exact (hv .r8 (by simp)).trans h.r8
  · intro hc
    apply (hc.head hP hk16).congr
    all_goals apply blockAt_frame fw; intro q hq; obtain rfl := List.mem_singleton.mp hq
    all_goals exact ((h.data.take hkn).ok.st.sub_right (Lay.stSub (by decide))).symm
  · intro hc
    have e := bytesAt_writeBytes_self s.mem (State.addr D)
      (xorBytes s.mem (State.addr S) (State.addr st+BitVec.ofNat 64 (64+P%16)) k) (by rw [hxl]; omega)
    rw [hxl] at e
    rw [show v.mem = z.mem by rfl,mz,e,xorBytes]
    have a := Proof.Gcm.ctr_head hc hP (d := bytesAt s.mem (State.addr S) k) (by rw [length_bytesAt]; exact hk16)
    rw [length_bytesAt,add_ofNat_assoc] at a
    exact a
  · apply bytesAt_frame fw _ (by omega)
    intro q hq; obtain rfl := List.mem_singleton.mp hq
    rcases h.mode.1 with rfl | hd
    · exact (split_disj hkn h.data.ok.lt).symm
    exact (hd.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix hkn)
  · by_cases e : k=n
    · left; omega
    · right; omega
  · exact fw.sub fun q hq => ⟨_,List.mem_append_left _ (List.mem_cons_self ..),
      List.mem_singleton.mp hq ▸ Region.sub_prefix hkn⟩
  · exact fun _ => z2

abbrev headLen (P n : Nat) := if P%16 = 0 then 0 else min (16-P%16) n

theorem head_ok (L : Lay c st w sp) (h : In c st w sp k7 k8 R P S D n s)
    (hz : s.z = decide (P%16 = 0)) :
    WP isa head s (CrMidG true c st w sp k7 k8 R icb P S D n s.mem (headLen P n)) := by
  refine WP.seq (WP.ite (P%16=0) (eval_eq' hz) (fun z => WP.block_nil ?_) (fun z => ?_))
  · have eq : P%16=0 := by simpa using z
    simpa only [headLen,eq,ite_true] using emptyHead (icb := icb) h (.inr eq) ⟨rfl,rfl,rfl,rfl⟩ (fun _ _ _ => rfl)
  · have part : P%16 ≠ 0 := by simpa using z
    have less := Nat.mod_lt P (by decide : 0 < 16)
    refine WP.seq ((minLen_ok s h.r6 h.r5 (by omega) h.data.ok.lt32).mono ?_)
    intro m ⟨r3,reg,kp⟩
    let k := min (16-P%16) n
    obtain ⟨t,run,flag,g,mem,rd,wr,sp'⟩ := cmp0_ok m .r3 r3 (by have := h.data.ok.lt32; omega)
    have keep := kp.trans (show Keeps m t from ⟨mem,rd,wr,sp'⟩)
    have regs (r : Reg) (h3 : r ≠ .r3) (h12 : r ≠ .r12) := (congrFun g r).trans (reg r h3 h12)
    refine WP.seq (WP.of_runBlock ⟨t,run,WP.ite (k=0) (eval_eq' flag) (fun zero => WP.block_nil ?_) (fun nz => ?_)⟩)
    · have eq : k=0 := by simpa using zero
      have len : n=0 := by dsimp [k] at eq; omega
      simpa only [headLen,ite_eq_right part,len,Nat.min_zero] using emptyHead (icb := icb) h (.inl len) keep regs
    · have ne : k≠0 := by simpa using nz
      have consumed := consume (icb := icb) L h part (k := k) rfl (by omega) keep regs ((congrFun g .r3).trans r3)
      simpa only [headLen,ite_eq_right part] using WP.seq_iff.mp consumed

theorem piece_ok (L : Lay c st w sp) (h : In c st w sp k7 k8 R P S D n s)
    (hz : s.z = decide (P%16=0)) :
    WP isa piece s (CrOutG true c st w sp k7 k8 R icb P S D n s.mem) :=
  WP.seq ((head_ok L h hz).mono fun _ mid => cryptTo_from_ok L mid)

end VG.Proof.AesGcm.Arm.DirectGather

/-! All control flow and addresses in the fragment head are functions of public
lengths and buffer pointers. The CTR body shares its timing proof with open-to. -/

namespace VG.Proof.AesGcm.Arm.DirectGather
open VG VG.Arm VG.Impl.AesGcm.Arm.DirectGather

def PieceIn (c st w sp k7 k8 : BitVec 32) (R P : Nat) (S D : BitVec 32) (n : Nat) (s : State) :=
  In c st w sp k7 k8 R P S D n s ∧ s.z = decide (P%16=0)

theorem piece_ct {c st w sp k7 k8 S D : BitVec 32} {R P n : Nat} (L : Lay c st w sp) :
    CT (PieceIn c st w sp k7 k8 R P S D n) piece := by
  apply CT.seq (J := CrMG true c st w sp k8 R S D n (P%16) (headLen P n))
  · apply CT.seq (J := fun _ => True)
    · apply CT.ite (decide (P%16=0)) (fun _ h => h.2) (fun _ => CT.skip)
      intro _
      apply CT.taint [.r2,.r4,.r5,.r6,.r10] _ (h := _) (by taint_decide)
      intro a b x y r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl
      · exact x.1.r2.trans y.1.r2.symm
      · exact x.1.r4.trans y.1.r4.symm
      · exact x.1.r5.trans y.1.r5.symm
      · exact x.1.r6.trans y.1.r6.symm
      · exact x.1.env.r10.trans y.1.env.r10.symm
    · intro s ⟨h,z⟩
      exact (WP.seq_iff.mp (head_ok (icb := 0) L h z)).mono fun _ _ => trivial
    · exact CT.taint [] (fun _ _ _ _ _ h => by simp at h) (h := _) (by taint_decide)
  · intro s ⟨h,z⟩
    exact (head_ok (icb := 0) L h z).mono fun _ a => ⟨k7,0,P,s.mem,rfl,a⟩
  · exact cryptTo_from_ct L

end VG.Proof.AesGcm.Arm.DirectGather

/-! Load a descriptor and append its ciphertext to the current output prefix. -/

namespace VG.Proof.AesGcm.Arm.DirectGather
open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.Impl.AesGcm.Arm.DirectGather
open VG.Spec.Gcm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Ctr)
open VG.Proof.AesGcm.Arm.Gather (sb sl gl_succ pt_succ)

abbrev wordAt (s : State) (p : BitVec 32) (off : Nat) : BitVec 32 :=
  s.mem.readW (State.addr (p+BitVec.ofNat 32 off)) 32

structure Loaded (s t : State) (src w dst : BitVec 32) (p : Nat) : Prop where
  r4 : t.gpr .r4 = wordAt s src 0
  r5 : t.gpr .r5 = wordAt s src 4
  r7 : t.gpr .r7 = src + 8
  r2 : t.gpr .r2 = dst + BitVec.ofNat 32 p
  r6 : t.gpr .r6 = BitVec.ofNat 32 (p%16)
  z : t.z = decide ((wordAt s src 4).toNat=0)
  mem : t.mem = s.mem.writeW (State.addr (w+260#32)) (BitVec.ofNat 32 p + wordAt s src 4)
  kept : ∀ r ∈ [Reg.r8,.r9,.r10,.r11], t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem pieceArgs_ok (s : State) {src w dst : BitVec 32} {p : Nat} (bound : p < 2^32)
    (h7 : s.gpr .r7 = src) (hw : s.gpr .r11 = w) (off : wordAt s w 260 = BitVec.ofNat 32 p)
    (out : wordAt s s.sp 8 = dst)
    (d0 : InRegions (s.rd++s.wr) (State.addr src) 4)
    (d4 : InRegions (s.rd++s.wr) (State.addr (src+4#32)) 4)
    (wrd : InRegions (s.rd++s.wr) (State.addr (w+260#32)) 4)
    (www : InRegions s.wr (State.addr (w+260#32)) 4)
    (arg : InRegions (s.rd++s.wr) (State.addr (s.sp+8#32)) 4) :
    WP isa (.block pieceArgs) s (Loaded s · src w dst p) := by
  change s.mem.readW _ 32 = _ at off out
  have mask := and15 (BitVec.ofNat 32 p)
  rw [toNat32 bound] at mask
  refine WP.of_runBlock ⟨_,by arun [BitVec.add_zero,pieceArgs,rO,h7,hw,d0,d4,wrd,www,arg,off,out],?_⟩
  constructor
  · simp [wordAt,gpr_setReg,gpr_subFlags,Mem.readW]
  · simp [wordAt,gpr_setReg,gpr_subFlags,Mem.readW]
  · simp [gpr_setReg,gpr_subFlags]
  · simp [gpr_setReg,gpr_subFlags]
  · simp [gpr_setReg,gpr_subFlags,mask]
  · have z := z_cmp (wordAt s src 4).isLt (by decide : 0<2^32)
    simpa only [z_subFlags,wordAt,BitVec.ofNat_toNat,BitVec.setWidth_eq,Mem.readW] using z
  · simp [wordAt,Mem.readW,Mem.writeW,mem_subFlags]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> rfl
  all_goals rfl

theorem advance_ok (s : State) {w : BitVec 32} {n : Nat} (pos : 0<n) (bound : n<2^32)
    (hw : s.gpr .r11=w) (count : wordAt s w 256=BitVec.ofNat 32 n)
    (rd : InRegions (s.rd++s.wr) (State.addr (w+256#32)) 4)
    (wr : InRegions s.wr (State.addr (w+256#32)) 4) :
    WP isa (.block advance) s fun t => t.z=decide (n-1=0) ∧
      t.mem=s.mem.writeW (State.addr (w+256#32)) (BitVec.ofNat 32 (n-1)) ∧
      (∀ r, r ≠ .r0 → t.gpr r=s.gpr r) ∧ t.sp=s.sp ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  change s.mem.readW _ 32 = _ at count
  refine WP.of_runBlock ⟨_,by arun [advance,rO,hw,count,rd,wr],?_,?_,?_,?_,?_,?_⟩
  · change (BitVec.ofNat 32 n - BitVec.ofNat 32 1 == 0) = _
    rw [ofNat_sub32 pos bound]; exact z_cmp0 (by omega)
  · simp [Mem.writeW,ofNat_sub32 pos bound]
  · intro r hr; simp [gpr_setReg,gpr_subFlags,hr]
  all_goals rfl

end VG.Proof.AesGcm.Arm.DirectGather

/-! The descriptor walk maintains a single counter stream and the ciphertext
of all completed descriptors. Workspace metadata records the public byte and
descriptor counts. -/

namespace VG.Proof.AesGcm.Arm.DirectGather

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.Impl.AesGcm.Arm.DirectGather
open VG.Spec.Gcm (Block blockAt gathered gatheredLen gctr inc32)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Ctr)
open VG.Proof.AesGcm.Arm.Gather (sb sl gl_succ pt_succ slice_mem gl_mono)

/-- Stable addresses, original fragment memory and initial data counter. -/
structure Stream where
  c : BitVec 32
  st : BitVec 32
  w : BitVec 32
  sp : BitVec 32
  src : BitVec 32
  dst : BitVec 32
  count : Nat
  rounds : Nat
  orig : State
  icb : Block

namespace Stream
abbrev pos (a : Stream) (i : Nat) := gatheredLen 32 a.orig.mem (State.addr a.src) i
abbrev plain (a : Stream) (i : Nat) := gathered 32 a.orig.mem (State.addr a.src) i
abbrev cursor (a : Stream) (i : Nat) := a.src + BitVec.ofNat 32 (8*i)
abbrev output (a : Stream) (i : Nat) := a.dst + BitVec.ofNat 32 (a.pos i)
abbrev roundsW (a : Stream) := BitVec.ofNat 32 a.rounds
abbrev cipher (a : Stream) := ciphOf a.orig.mem (State.addr a.c) a.rounds
abbrev dstR (a : Stream) : Region := ⟨State.addr a.dst,a.pos a.count⟩
abbrev dsR (a : Stream) : Region := ⟨State.addr a.src,8*a.count⟩
abbrev ctrR (a : Stream) : Region := ⟨State.addr a.st+48#64,32⟩
abbrev workR (a : Stream) : Region := ⟨State.addr a.w+512,2048⟩
abbrev countR (a : Stream) : Region := ⟨State.addr a.w+256,8⟩
abbrev changes (a : Stream) := [a.dstR,a.ctrR,a.workR,below a.sp,below12 a.sp,a.countR]
abbrev safe (a : Stream) (r : Region) := ∀ q ∈ a.changes, r.Disjoint q
abbrev counter (a : Stream) (m : Mem) (i : Nat) := Ctr m (State.addr a.st+48#64) (State.addr a.st+64#64)
  a.cipher a.icb (a.pos i)
end Stream

structure LoopLayout (a : Stream) : Prop where
  machine : Lay a.c a.st a.w a.sp
  rounds : a.rounds=10 ∨ a.rounds=12 ∨ a.rounds=14
  descFit : a.src.toNat+a.count*8 ≤ 2^32
  lenBound : a.pos a.count < 2^32
  dest : DataW a.c a.st a.w a.sp 0 a.roundsW a.orig a.dst (a.pos a.count)
  descriptors : Covers [a.dsR] (a.orig.rd++a.orig.wr)
  descSafe : a.safe a.dsR
  sources : ∀ i<a.count, DataOk a.st a.w a.sp a.orig (sb a.orig.mem a.src i) (sl a.orig.mem a.src i)
  srcSafe : ∀ i<a.count, a.safe ⟨State.addr (sb a.orig.mem a.src i),sl a.orig.mem a.src i⟩
  ctxSafe : a.safe ⟨State.addr a.c,256⟩
  stackArg : InRegions (a.orig.rd++a.orig.wr) (State.addr (a.sp+8#32)) 4
  stackSafe : a.safe ⟨State.addr (a.sp+8#32),4⟩
  dstAddr : wordAt a.orig a.sp 8=a.dst
  belowFit : 12 ≤ a.sp.toNat
  belowCtx : (below12 a.sp).Disjoint ⟨State.addr a.c,256⟩
  belowSt : (below12 a.sp).Disjoint ⟨State.addr a.st,80⟩
  belowW : (below12 a.sp).Disjoint ⟨State.addr a.w,2560⟩
  belowDst : (below12 a.sp).Disjoint a.dstR
  belowSrc : ∀ i<a.count, (below12 a.sp).Disjoint ⟨State.addr (sb a.orig.mem a.src i),sl a.orig.mem a.src i⟩

structure Cursor (a : Stream) (i left : Nat) (s : State) : Prop where
  env : Env a.c a.st a.w a.sp (a.cursor i) a.roundsW s
  offset : wordAt s a.w 260 = BitVec.ofNat 32 (a.pos i)
  count : wordAt s a.w 256 = BitVec.ofNat 32 left
  ctr : a.counter s.mem i
  encrypted : bytesAt s.mem (State.addr a.dst) (a.pos i) = gctr a.cipher a.icb (a.plain i)
  frame : Frame a.changes a.orig.mem s.mem
  rd : s.rd = a.orig.rd
  wr : s.wr = a.orig.wr

abbrev At (a : Stream) (i : Nat) := Cursor a i (a.count-i)

namespace LoopLayout
variable {a : Stream} (l : LoopLayout a) {i : Nat} {s : State}
include l

theorem cumulative (hi : i < a.count) :
    a.pos i + sl a.orig.mem a.src i ≤ a.pos a.count := by
  rw [←gl_succ l.descFit hi]
  exact gl_mono _ _ l.descFit (by omega) (Nat.le_refl _)

theorem destAddr (hi : i < a.count) (hn : 0 < sl a.orig.mem a.src i) :
    State.addr (a.output i) = State.addr a.dst + BitVec.ofNat 64 (a.pos i) :=
  l.dest.ok.addr (by have := l.cumulative hi; omega)

theorem dataAt (hi : i < a.count) (hn : 0 < sl a.orig.mem a.src i) :
    DataW a.c a.st a.w a.sp (a.cursor (i+1)) a.roundsW a.orig (a.output i) (sl a.orig.mem a.src i) := by
  have x := l.dest.sub (l.cumulative hi) hn
  exact ⟨x.ok,x.wr,x.ctx⟩

theorem destSub (hi : i < a.count) (hn : 0 < sl a.orig.mem a.src i) :
    (⟨State.addr (a.output i),sl a.orig.mem a.src i⟩ : Region).Sub a.dstR := by
  rw [l.destAddr hi hn]
  exact Offset.sub_base _ (l.cumulative hi)

theorem mode (hi : i<a.count) (hn : 0<sl a.orig.mem a.src i) :
    CrMode true a.c a.st a.w a.sp (sb a.orig.mem a.src i) (a.output i) (sl a.orig.mem a.src i) := by
  refine ⟨.inr ((l.srcSafe i hi a.dstR (List.mem_cons_self ..)).sub_right (l.destSub hi hn)),
    l.belowFit,l.belowCtx,l.belowSt,l.belowW,l.belowSrc i hi,l.belowDst.sub_right (l.destSub hi hn)⟩

theorem metaSafe {d : Nat} (low : 256≤d) (high : d+4≤264) :
    ∀ q ∈ [a.dstR,a.ctrR,a.workR,below a.sp,below12 a.sp],
      (⟨State.addr a.w+BitVec.ofNat 64 d,4⟩ : Region).Disjoint q := by
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl
  · exact l.dest.ok.w.symm.sub_left (Lay.wSub (by omega))
  · exact (l.machine.sb.sub_right (Lay.bSub (by omega) (by omega))).symm.sub_right (Lay.stSub (by decide))
  · exact Offset.disjoint _ (e := 512) (.inl (by omega)) (by omega) (by decide)
  · exact l.machine.kw.symm.sub_left (Lay.wSub (by omega))
  · exact l.belowW.symm.sub_left (Lay.wSub (by omega))

theorem metaSt {d : Nat} (low : 256≤d) (high : d+4≤264) {o : Nat} (stHigh : o+16≤80) :
    (⟨State.addr a.st+BitVec.ofNat 64 o,16⟩ : Region).Disjoint ⟨State.addr a.w+BitVec.ofNat 64 d,4⟩ :=
  (l.machine.sb.sub_right (Lay.bSub (by omega) (by omega))).sub_left (Lay.stSub stHigh)

theorem entry (hi : i<a.count) (u : At a i s) :
    WP isa (.block pieceArgs) s (Loaded s · (a.cursor i) a.w a.dst (a.pos i)) := by
  have dw := l.descFit
  have hp := l.cumulative hi
  have pfit := l.lenBound
  have e0 := Gather.descA0 dw hi
  have e4 := Gather.descA dw hi 4 (by decide)
  have read (d : Nat) (hd : d+4 ≤ 8*a.count) :
      InRegions (s.rd++s.wr) (State.addr a.src+BitVec.ofNat 64 d) 4 := by
    rw [u.rd,u.wr]
    exact l.descriptors _ _ ⟨_,List.mem_singleton_self _,Offset.contains_base _ hd (by omega)⟩
  refine pieceArgs_ok s (by omega) u.env.r7 u.env.r11 u.offset ?_ ?_ ?_ ?_ ?_ ?_
  · unfold wordAt
    rw [u.env.sp,u.frame.readW (Region.contains_self _ _) l.stackSafe (by decide)]
    exact l.dstAddr
  · rw [←e0]; exact read _ (by omega)
  · change InRegions _ (State.addr (a.src+BitVec.ofNat 32 (8*i)+BitVec.ofNat 32 4)) 4
    rw [←e4,add_ofNat_assoc]
    exact read _ (by omega)
  · rw [l.machine.wA (d:=260) (by decide)]; exact u.env.perm.wR (by decide)
  · rw [l.machine.wA (d:=260) (by decide)]; exact u.env.perm.wW (by decide)
  · rw [u.env.sp,u.rd,u.wr]; exact l.stackArg

theorem entrySource (hi : i<a.count) (u : At a i s) :
    wordAt s (a.cursor i) 0 = sb a.orig.mem a.src i ∧
    wordAt s (a.cursor i) 4 = BitVec.ofNat 32 (sl a.orig.mem a.src i) := by
  have sub (d : Nat) (hd : d+4 ≤ 8*a.count) :
      (⟨State.addr a.src+BitVec.ofNat 64 d,4⟩ : Region).Sub a.dsR := Offset.sub_base _ hd
  have same (d : Nat) (hd : d+4≤8*a.count) : s.mem.readW (State.addr a.src+BitVec.ofNat 64 d) 32 =
      a.orig.mem.readW (State.addr a.src+BitVec.ofNat 64 d) 32 :=
    u.frame.readW (Region.contains_self _ _) (fun q hq => (l.descSafe q hq).sub_left (sub d hd)) (by decide)
  simp only [wordAt,sb,sl,add_ofNat_zero,BitVec.ofNat_toNat,BitVec.setWidth_eq,Stream.cursor]
  rw [←Gather.descA0 l.descFit hi,←Gather.descA l.descFit hi 4 (by decide),add_ofNat_assoc]
  exact ⟨same _ (by omega),same _ (by omega)⟩

abbrev iterFrame (a : Stream) (i : Nat) :=
  crFrameG true a.st a.w a.sp (a.output i) (sl a.orig.mem a.src i)

theorem frameSub (hi : i<a.count) (hn : 0<sl a.orig.mem a.src i) {m m' : Mem} (f : Frame (iterFrame a i) m m') :
    Frame a.changes m m' := f.sub fun q hq => by
  change q ∈ [_,_,_,_] ++ [_] at hq
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with (rfl|rfl|rfl|rfl)|rfl
  · exact ⟨a.dstR,List.mem_cons_self ..,l.destSub hi hn⟩
  all_goals exact ⟨_,by simp [Stream.changes,Stream.ctrR,Stream.workR,below],fun _ => id⟩

theorem ctx (u : At a i s) : ciphOf s.mem (State.addr a.c) a.rounds = a.cipher :=
  ciph_frame u.frame l.ctxSafe l.rounds

theorem metaFrame {m : Mem} (val : BitVec 32) {d : Nat} (low : 256≤d) (high : d+4≤264) :
    Frame [⟨State.addr a.w+BitVec.ofNat 64 d,4⟩] m (m.writeW (State.addr (a.w+BitVec.ofNat 32 d)) val) := by
  rw [l.machine.wA (by omega)]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) val (Region.contains_self _ _)

omit l in
theorem extendMeta {m m' : Mem} {d : Nat} (lo : 256≤d) (hi : d+4≤264)
    (f : Frame [⟨State.addr a.w+BitVec.ofNat 64 d,4⟩] m m') : Frame a.changes m m' :=
  f.sub fun q hq => ⟨a.countR,by simp [Stream.changes],List.mem_singleton.mp hq ▸ Offset.sub _ lo (by omega)⟩

theorem keepCtr {m m' : Mem} {d : Nat} {p : Nat} (lo : 256≤d) (hi : d+4≤264)
    (f : Frame [⟨State.addr a.w+BitVec.ofNat 64 d,4⟩] m m')
    (hc : Ctr m (State.addr a.st+48#64) (State.addr a.st+64#64) a.cipher a.icb p) :
    Ctr m' (State.addr a.st+48#64) (State.addr a.st+64#64) a.cipher a.icb p := by
  apply hc.congr
  all_goals apply blockAt_frame f; intro q hq; obtain rfl := List.mem_singleton.mp hq
  all_goals exact l.metaSt lo hi (by decide)

theorem keepCt {m m' : Mem} {d p : Nat} (lo : 256≤d) (hi : d+4≤264) (hp : p≤a.pos a.count)
    (f : Frame [⟨State.addr a.w+BitVec.ofNat 64 d,4⟩] m m') :
    bytesAt m' (State.addr a.dst) p = bytesAt m (State.addr a.dst) p :=
  bytesAt_frame f (fun q hq => List.mem_singleton.mp hq ▸
    ((l.dest.ok.w.sub_right (Lay.wSub (by omega))).sub_left (Region.sub_prefix hp))) (by have := l.lenBound; omega)

theorem metaRead {m m' : Mem} {d e : Nat} (hd : 256≤d) (he : 256≤e) (dd : d+4≤264) (ee : e+4≤264)
    (apart : d+4≤e ∨ e+4≤d) (f : Frame [⟨State.addr a.w+BitVec.ofNat 64 e,4⟩] m m') :
    m'.readW (State.addr (a.w+BitVec.ofNat 32 d)) 32 = m.readW (State.addr (a.w+BitVec.ofNat 32 d)) 32 := by
  rw [l.machine.wA (by omega)]
  exact f.readW (Region.contains_self _ _) (fun q hq => List.mem_singleton.mp hq ▸
    Offset.disjoint _ apart (by omega) (by omega)) (by decide)

omit l in
theorem nextEnv {s u : State} {i : Nat} (h : At a i s) (v : Loaded s u (a.cursor i) a.w a.dst (a.pos i)) :
    Env a.c a.st a.w a.sp (a.cursor (i+1)) a.roundsW u := by
  refine ⟨?_,(v.kept _ (by simp)).trans h.env.r8,(v.kept _ (by simp)).trans h.env.r9,
    (v.kept _ (by simp)).trans h.env.r10,(v.kept _ (by simp)).trans h.env.r11,v.sp.trans h.env.sp,
    h.env.perm.of_eq v.rd v.wr⟩
  rw [v.r7]
  change a.src + BitVec.ofNat 32 (8*i) + BitVec.ofNat 32 8 = _
  rw [add32_ofNat_assoc]
  congr 2

private theorem select_ok {s : State} {S D : BitVec 32} {p n : Nat} {k7 : BitVec 32}
    (h : In a.c a.st a.w a.sp k7 a.roundsW a.rounds p S D n s) (nz : n≠0) (z : s.z=decide (n=0)) :
    WP isa nonempty s (CrOutG true a.c a.st a.w a.sp k7 a.roundsW a.rounds a.icb p S D n s.mem) := by
  refine WP.ite false (eval_eq' (by simpa only [nz,decide_false] using z)) (by simp) (fun _ => ?_)
  obtain ⟨t,run,tz,tg,tm,rd,wr,sp⟩ := cmp0_ok s .r6 h.r6 (by omega)
  refine WP.seq (WP.of_runBlock ⟨t,run,?_⟩)
  have pre : In a.c a.st a.w a.sp k7 a.roundsW a.rounds p S D n t := by
    refine ⟨h.env.keep (fun _ _ => by rw [tg]) sp rd wr,h.src.of_eq rd wr,h.data.of_eq rd wr,h.mode,?_,?_,?_,?_,?_,h.rounds⟩
    all_goals rw [tg]; first | exact h.r4 | exact h.r2 | exact h.r5 | exact h.r6 | exact h.r8
  simpa only [tm] using piece_ok (icb := a.icb) l.machine pre tz

private theorem cryptMeta {m m' : Mem} {d : Nat} (low : 256≤d) (high : d+4≤264) (hi : i<a.count)
    (hn : 0<sl a.orig.mem a.src i) (f : Frame (iterFrame a i) m m') :
    m'.readW (State.addr (a.w+BitVec.ofNat 32 d)) 32 = m.readW (State.addr (a.w+BitVec.ofNat 32 d)) 32 := by
  rw [l.machine.wA (by omega)]
  apply f.readW (Region.contains_self _ _) _ (by decide)
  intro q hq
  change q ∈ [_,_,_,_] ++ [_] at hq
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with (rfl|rfl|rfl|rfl)|rfl
  · exact (l.metaSafe low high _ (List.mem_cons_self ..)).sub_right (l.destSub hi hn)
  all_goals exact l.metaSafe low high _ (by simp [Stream.ctrR,Stream.workR])

private theorem ciphertext {u z : State} (hi : i<a.count) (hn : 0<sl a.orig.mem a.src i)
    (part : Frame (iterFrame a i) u.mem z.mem)
    (prior : bytesAt u.mem (State.addr a.dst) (a.pos i) = gctr a.cipher a.icb (a.plain i))
    (fresh : bytesAt z.mem (State.addr (a.output i)) (sl a.orig.mem a.src i) =
      Proof.Gcm.xorKs a.cipher a.icb (a.pos i) (bytesAt a.orig.mem (State.addr (sb a.orig.mem a.src i)) (sl a.orig.mem a.src i))) :
    bytesAt z.mem (State.addr a.dst) (a.pos (i+1)) = gctr a.cipher a.icb (a.plain (i+1)) := by
  have le : a.pos i ≤ a.pos a.count := by have := l.cumulative hi; omega
  have sub : (⟨State.addr a.dst,a.pos i⟩ : Region).Sub a.dstR := Region.sub_prefix le
  have unchanged : bytesAt z.mem (State.addr a.dst) (a.pos i) = bytesAt u.mem (State.addr a.dst) (a.pos i) := by
    apply bytesAt_frame part _ (by have := l.lenBound; omega)
    intro q hq
    change q ∈ [_,_,_,_] ++ [_] at hq
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with (rfl|rfl|rfl|rfl)|rfl
    · rw [l.destAddr hi hn]; exact Offset.base_disjoint _ (Nat.le_refl _) (by have := l.cumulative hi; have := l.lenBound; omega)
    · exact (l.dest.ok.st.sub_left sub).sub_right (Lay.stSub (by decide))
    · exact (l.dest.ok.w.sub_left sub).sub_right (Lay.wSub (by decide))
    · exact l.dest.ok.stk.symm.sub_left sub
    · exact l.belowDst.symm.sub_left sub
  rw [l.destAddr hi hn] at fresh
  change bytesAt _ _ (gatheredLen _ _ _ (i+1)) = gctr _ _ (gathered _ _ _ (i+1))
  rw [gl_succ l.descFit hi,pt_succ l.descFit hi,Proof.Cmac.Stream.bytesAt_append,
    Proof.Gcm.gctr_append,Proof.Gcm.length_gathered,unchanged,prior,fresh]

theorem filled (hi : i<a.count) (h : At a i s) {u : State} (d : Loaded s u (a.cursor i) a.w a.dst (a.pos i)) :
    WP isa nonempty u (Cursor a (i+1) (a.count-i)) := by
  let n := sl a.orig.mem a.src i
  have src := l.entrySource hi h
  have nr : (wordAt s (a.cursor i) 4).toNat = n := by
    rw [src.2,toNat32 (by exact (a.orig.mem.readW _ 32).isLt)]
  have next := nextEnv h d
  have su : Frame [⟨State.addr a.w+260#64,4⟩] s.mem u.mem := by
    rw [d.mem]; exact l.metaFrame _ (d := 260) (by decide) (by decide)
  have frame := h.frame.trans (extendMeta (a := a) (by decide : 256≤260) (by decide) su)
  have ctr := l.keepCtr (by decide : 256≤260) (by decide) su h.ctr
  have hp := l.cumulative hi
  have ct := (l.keepCt (by decide : 256≤260) (by decide) (by omega : a.pos i ≤ a.pos a.count) su).trans h.encrypted
  have posEq : a.pos (i+1)=a.pos i+n := gl_succ l.descFit hi
  have newOff : wordAt u a.w 260 = BitVec.ofNat 32 (a.pos (i+1)) := by
    unfold wordAt
    rw [d.mem,Mem.readW_writeW_self32,src.2,BitVec.ofNat_add_ofNat,posEq]
  have count : wordAt u a.w 256 = BitVec.ofNat 32 (a.count-i) :=
    (l.metaRead (d:=256) (e:=260) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)) su).trans h.count
  by_cases zero : n=0
  · refine WP.ite true (eval_eq' (by rw [d.z,nr,zero]; rfl)) (fun _ => WP.block_nil ?_) (by simp)
    have p : a.pos (i+1)=a.pos i := by rw [posEq,zero,Nat.add_zero]
    have pt : a.plain (i+1)=a.plain i := by
      unfold Stream.plain; rw [pt_succ l.descFit hi,show sl a.orig.mem a.src i=0 from zero]; simp [bytesAt]
    exact ⟨next,newOff,count,by simpa only [Stream.counter,p] using ctr,by simpa only [p,pt] using ct,
      frame,d.rd.trans h.rd,d.wr.trans h.wr⟩
  · have pos : 0<n := by omega
    have du := d.rd.trans h.rd
    have wu := d.wr.trans h.wr
    have pre : In a.c a.st a.w a.sp (a.cursor (i+1)) a.roundsW a.rounds (a.pos i)
        (sb a.orig.mem a.src i) (a.output i) n u :=
      ⟨next,(l.sources i hi).of_eq du wu,(l.dataAt hi pos).of_eq du wu,l.mode hi pos,d.r4.trans src.1,
        d.r2,d.r5.trans src.2,d.r6,next.r8,l.rounds⟩
    have cu := ciph_frame frame l.ctxSafe l.rounds
    refine (WP.with_rdwr (l.select_ok pre zero (by rw [d.z,nr]))).mono ?_
    intro z ⟨co,zrd,zwr,_⟩
    have ci := co.ctr (by simpa only [cu,Stream.cipher] using ctr)
    have ans := co.out (by simpa only [cu,Stream.cipher] using ctr)
    rw [cu,bytesAt_frame frame (l.srcSafe i hi) (by have := (l.sources i hi).lt; omega)] at ans
    exact ⟨co.env,(l.cryptMeta (d:=260) (by decide) (by decide) hi pos co.frame).trans newOff,
      (l.cryptMeta (d:=256) (by decide) (by decide) hi pos co.frame).trans count,
      by simpa only [Stream.counter,posEq,cu,Stream.cipher] using ci,l.ciphertext hi pos co.frame ct ans,
      frame.trans (l.frameSub hi pos co.frame),zrd.trans du,zwr.trans wu⟩

theorem advanced (hi : i<a.count) (h : Cursor a (i+1) (a.count-i) s) :
    WP isa (.block advance) s fun u => At a (i+1) u ∧ u.z=decide (i+1=a.count) := by
  have fit := l.descFit
  refine (advance_ok s (show 0<a.count-i by omega) (by omega) h.env.r11 h.count ?_ ?_).mono ?_
  · rw [l.machine.wA (d:=256) (by decide)]; exact h.env.perm.wR (by decide)
  · rw [l.machine.wA (d:=256) (by decide)]; exact h.env.perm.wW (by decide)
  intro u ⟨z,m,g,sp,rd,wr⟩
  have f : Frame [⟨State.addr a.w+256#64,4⟩] s.mem u.mem := by
    rw [m]; exact l.metaFrame _ (d:=256) (by decide) (by decide)
  refine ⟨⟨h.env.keep (by intro r hr; apply g; intro e; subst r; simp at hr) sp rd wr,
    (l.metaRead (d:=260) (e:=256) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)) f).trans h.offset,
    ?_,l.keepCtr (by decide : 256≤256) (by decide) f h.ctr,
    (l.keepCt (by decide : 256≤256) (by decide) (gl_mono _ _ l.descFit (by omega) (Nat.le_refl _)) f).trans h.encrypted,
    h.frame.trans (extendMeta (a:=a) (by decide : 256≤256) (by decide) f),rd.trans h.rd,wr.trans h.wr⟩,?_⟩
  · unfold wordAt; rw [m,Mem.readW_writeW_self32]; congr 1
  · rw [z]; congr 1; apply propext; omega

abbrev iter := Code.seq (.block pieceArgs) (.seq nonempty (.block advance))

theorem iteration (hi : i<a.count) (h : At a i s) :
    WP isa iter s fun u => At a (i+1) u ∧ u.z=decide (i+1=a.count) :=
  WP.seq ((l.entry hi h).mono fun _ d => WP.seq ((l.filled hi h d).mono fun _ x => l.advanced hi x))

theorem walk (h : At a 0 s) (pos : 0<a.count) : WP isa (.loop iter .ne) s (At a a.count) := by
  refine WP.loop (M:=isa) (c:=.ne) (fun left t => ∃ i, left = a.count-i ∧ i<a.count ∧ At a i t) ?_ _ _ ⟨0,rfl,pos,h⟩
  rintro _ t ⟨i,rfl,hi,before⟩
  refine (l.iteration hi before).mono fun u ⟨after,z⟩ => ?_
  have ev := eval_ne' z
  by_cases last : i+1=a.count
  · left; exact ⟨by rw [ev]; simp [last],last ▸ after⟩
  · right; exact ⟨by rw [ev]; simp [last],a.count-(i+1),by omega,i+1,rfl,by omega,after⟩

abbrev test := [Instr.ldr .r0 .r11 rO,.cmp .r0 (imm 0)]

theorem test_ok (h : At a 0 s) :
    WP isa (.block test) s fun t => At a 0 t ∧ t.z=decide (a.count=0) := by
  have count := h.count
  change s.mem.readW (State.addr (a.w+256#32)) 32 = BitVec.ofNat 32 (a.count-0) at count
  rw [Nat.sub_zero] at count
  have rd : InRegions (s.rd++s.wr) (State.addr (a.w+256#32)) 4 := by
    rw [l.machine.wA (d:=256) (by decide)]; exact h.env.perm.wR (by decide)
  refine WP.of_runBlock ⟨_,by arun [test,rO,h.env.r11,count,rd],?_,?_⟩
  · exact ⟨h.env.keep (fun r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl <;> rfl) rfl rfl rfl,h.offset,h.count,h.ctr,h.encrypted,h.frame,h.rd,h.wr⟩
  · exact z_cmp (by have := l.descFit; omega) (by decide)

theorem pieces_ok (h : At a 0 s) : WP isa pieces s (At a a.count) := by
  refine WP.seq ((l.test_ok h).mono fun t ⟨state,z⟩ => WP.ite (a.count=0) (eval_eq' z) (fun ht => ?_) (fun hf => ?_))
  · have eq : a.count=0 := by simpa using ht
    exact WP.block_nil (eq ▸ state)
  · have ne : a.count≠0 := by simpa using hf
    exact l.walk state (by omega)

end LoopLayout
end VG.Proof.AesGcm.Arm.DirectGather

/-! The descriptor values and public lengths determine the entire loop trace. -/


namespace VG.Proof.AesGcm.Arm.DirectGather
open VG VG.Arm VG.Impl.AesGcm.Arm VG.Impl.AesGcm.Arm.DirectGather
open VG.Proof.AesGcm.Arm.Gather (sb sl Eq2 TT rel_seq rel_taint rel_skip rel_ite)

/-- Values driving both traces between and within the descriptors. -/
structure Same (a b : Stream) : Prop where
  c : a.c=b.c
  st : a.st=b.st
  w : a.w=b.w
  sp : a.sp=b.sp
  src : a.src=b.src
  dst : a.dst=b.dst
  rounds : a.rounds=b.rounds
  count : a.count=b.count
  pointers : ∀ i<a.count, sb a.orig.mem a.src i=sb b.orig.mem b.src i
  lens : ∀ i<a.count, sl a.orig.mem a.src i=sl b.orig.mem b.src i
  argFit : a.sp.toNat+12 ≤ 2^32
  argLeft : ∀ r ∈ a.orig.wr, Region.Disjoint ⟨State.addr a.sp,12⟩ r
  argRight : ∀ r ∈ b.orig.wr, Region.Disjoint ⟨State.addr b.sp,12⟩ r
  argSafeLeft : a.safe ⟨State.addr a.sp,12⟩
  argSafeRight : b.safe ⟨State.addr b.sp,12⟩
  argBytes : ∀ j<12, a.orig.mem (State.addr a.sp+BitVec.ofNat 64 j)=b.orig.mem (State.addr b.sp+BitVec.ofNat 64 j)
  pos : ∀ i≤a.count, a.pos i=b.pos i

namespace LoopLayout
variable {a b : Stream} (l : LoopLayout a) (k : LoopLayout b) (eq : Same a b)
variable {i : Nat} {s t : State}

include l in
private theorem source_pre (hi : i<a.count) (s0 : At a i s) {u : State}
    (d : Loaded s u (a.cursor i) a.w a.dst (a.pos i)) (hn : 0<sl a.orig.mem a.src i) :
    In a.c a.st a.w a.sp (a.cursor (i+1)) a.roundsW a.rounds (a.pos i)
        (sb a.orig.mem a.src i) (a.output i) (sl a.orig.mem a.src i) u := by
  have src := l.entrySource hi s0
  have next := nextEnv s0 d
  have rd := d.rd.trans s0.rd
  have wr := d.wr.trans s0.wr
  exact ⟨next,(l.sources i hi).of_eq rd wr,(l.dataAt hi hn).of_eq rd wr,l.mode hi hn,
    d.r4.trans src.1,d.r2,d.r5.trans src.2,d.r6,next.r8,l.rounds⟩

private theorem cmp_pre {R P n : Nat} {c st w sp k7 k8 D S : BitVec 32} {s : State}
    (h : In c st w sp k7 k8 R P S D n s) :
    WP isa (.block [.cmp .r6 (imm 0)]) s (PieceIn c st w sp k7 k8 R P S D n) := by
  obtain ⟨t,run,flag,g,_,rd,wr,sp⟩ := cmp0_ok s .r6 h.r6 (by omega)
  refine WP.of_runBlock ⟨t,run,?_⟩
  unfold PieceIn
  refine ⟨⟨h.env.keep (fun _ _ => by rw [g]) sp rd wr,h.src.of_eq rd wr,
    h.data.of_eq rd wr,h.mode,?_,?_,?_,?_,?_,h.rounds⟩,flag⟩
  all_goals rw [g]; first | exact h.r4 | exact h.r2 | exact h.r5 | exact h.r6 | exact h.r8

include l k eq
theorem nonempty_rel (hi : i<a.count) (hs : At a i s) (ht : At b i t) {u v : State}
    (d : Loaded s u (a.cursor i) a.w a.dst (a.pos i)) (e : Loaded t v (b.cursor i) b.w b.dst (b.pos i)) :
    RelCT isa (Eq2 u v) nonempty TT := by
  have hj := eq.count ▸ hi
  have sa := (l.entrySource hi hs).2
  have sb' := (k.entrySource hj ht).2
  have len := eq.lens i hi
  have p := eq.pos i (by omega)
  have za := d.z
  have zb := e.z
  rw [sa,toNat32 (by exact (a.orig.mem.readW _ 32).isLt)] at za
  rw [sb',toNat32 (by exact (b.orig.mem.readW _ 32).isLt),←len] at zb
  refine rel_ite (eval_eq' za) (eval_eq' zb) (fun _ => rel_skip) fun notZero => ?_
  have nz : sl a.orig.mem a.src i≠0 := by simpa using notZero
  have in1 := l.source_pre hi hs d (by omega)
  have in2 := k.source_pre hj ht e (by omega)
  have in2' : In a.c a.st a.w a.sp (a.cursor (i+1)) a.roundsW a.rounds (a.pos i)
    (sb a.orig.mem a.src i) (a.output i) (sl a.orig.mem a.src i) v := by
    rw [eq.pointers i hi,len]
    simpa only [Stream.cursor,Stream.roundsW,Stream.output,eq.c,eq.st,eq.w,eq.sp,eq.src,eq.rounds,eq.dst,p] using in2
  refine rel_seq (rel_taint [.r6] (by simp [d.r6,e.r6,p]) ⟨_,by taint_decide⟩)
    (cmp_pre in1) (cmp_pre in2') ?_
  intro x y h1 h2
  exact RelCT.mono (piece_ct l.machine) (by rintro _ _ ⟨rfl,rfl⟩; exact ⟨h1,h2⟩) (fun _ _ _ => trivial)

theorem iter_rel (hi : i<a.count) (hs : At a i s) (ht : At b i t) :
    RelCT isa (Eq2 s t) iter TT := by
  have hj := eq.count ▸ hi
  have ptr : a.cursor i=b.cursor i := by rw [Stream.cursor,Stream.cursor,eq.src]
  have pub : VG.Arm.Taint.Agree (argTaint [.r7,.r11] 12) s t := by
    apply agree_argTaint
    · intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · rw [hs.env.r7,ht.env.r7,ptr]
      · rw [hs.env.r11,ht.env.r11,eq.w]
    · rw [hs.env.sp,ht.env.sp,eq.sp]
    · rw [hs.env.sp,hs.wr]; exact ⟨eq.argFit,eq.argLeft⟩
    · rw [ht.env.sp,ht.wr]; exact ⟨eq.sp ▸ eq.argFit,eq.argRight⟩
    · intro j hj
      have ca := hs.frame.bytes (R:=⟨State.addr a.sp,12⟩) eq.argSafeLeft (by decide : 12 ≤ 2^64) hj
      have cb := ht.frame.bytes (R:=⟨State.addr b.sp,12⟩) eq.argSafeRight (by decide : 12 ≤ 2^64) hj
      simp only [VG.Arm.Taint.argByte,hs.env.sp,ht.env.sp]
      exact ca.trans ((eq.argBytes j hj).trans cb.symm)
  refine rel_seq (RelCT.taint (A:=taint) (argTaint [.r7,.r11] 12)
    (fun _ _ h => by obtain ⟨rfl,rfl⟩ := h; exact pub) (hc:=_) (by taint_decide))
    (l.entry hi hs) (k.entry hj ht) ?_
  intro x y dx dy
  refine rel_seq (l.nonempty_rel k eq hi hs ht dx dy) (l.filled hi hs dx) (k.filled hj ht dy) ?_
  intro z v hz hv
  exact rel_taint [.r11] (by simp [hz.env.r11,hv.env.r11,eq.w]) ⟨_,by taint_decide⟩

theorem walk_rel (hs : At a 0 s) (ht : At b 0 t) (pos : 0<a.count) :
    RelCT isa (Eq2 s t) (.loop iter .ne) TT := by
  refine (RelCT.loop (Q:=TT) (fun n u v => ∃ i, n=a.count-i ∧ i<a.count ∧ At a i u ∧ At b i v)
    (fun n => ?_) (a.count-0)).mono
    (by rintro _ _ ⟨rfl,rfl⟩; exact ⟨0,rfl,pos,hs,ht⟩) (fun _ _ _ => trivial)
  refine RelCT.exists_ fun i => ?_
  by_cases hin : n=a.count-i ∧ i<a.count
  · obtain ⟨rfl,hi⟩ := hin
    have body : RelCT isa (fun u v => At a i u ∧ At b i v) iter TT := by
      intro u v tu tv z w h ez ew
      exact l.iter_rel k eq hi h.1 h.2 _ _ _ _ _ _ ⟨rfl,rfl⟩ ez ew
    refine (body.wp fun _ _ ⟨ha,hb⟩ => ⟨l.iteration hi ha,k.iteration (eq.count ▸ hi) hb⟩).mono
      (fun _ _ h => h.2.2) ?_
    rintro z w ⟨_,uz,vw⟩
    have ev := eval_ne' uz.2
    have ev' := eval_ne' vw.2
    rw [←eq.count] at ev'
    refine ⟨by rw [ev,ev'],fun _ => trivial,fun cont => ?_⟩
    rw [ev] at cont
    have next : i+1<a.count := by simp at cont; omega
    exact ⟨a.count-(i+1),by omega,i+1,rfl,next,uz.1,vw.1⟩
  · exact RelCT.of_false fun _ _ h => hin ⟨h.1,h.2.1⟩

theorem pieces_rel (hs : At a 0 s) (ht : At b 0 t) : RelCT isa (Eq2 s t) pieces TT := by
  refine rel_seq (rel_taint [.r11] (by simp [hs.env.r11,ht.env.r11,eq.w]) ⟨_,by taint_decide⟩)
    (l.test_ok hs) (k.test_ok ht) ?_
  intro u v ⟨x,z⟩ ⟨y,z'⟩
  rw [←eq.count] at z'
  refine rel_ite (eval_eq' z) (eval_eq' z') (fun _ => rel_skip) (fun nz => ?_)
  have pos : a.count≠0 := by simpa using nz
  exact l.walk_rel k eq x y (by omega)

end LoopLayout
end VG.Proof.AesGcm.Arm.DirectGather
