module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.OutputFrame
public import VerifiedGarbage.Proof.Bignum.AArch64.Store
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Cut
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Bignum.Octets

/-! ### `Ffdh.AArch64.Cached.MaskOutputLoop`, which only this module used -/

section

/-! A fixed-length scalar mask preserves success bytes and zeroes failure bytes. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.WriteBytes (writeW8_apply)

structure MaskOutputInv (s₀ : State) (op : Addr) (c : Bool) (j : Nat) (t : State) : Prop where
  keep : Keep [.x1, .x2, .x3] s₀ t
  x1 : t.gpr .x1 = op + BitVec.ofNat 64 j
  bytes : ∀ i < j, t.mem (op + BitVec.ofNat 64 i) = if c then s₀.mem (op + BitVec.ofNat 64 i) else 0
  frame : ∀ x, (∀ i < j, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s₀.mem x

theorem maskOutputByte_ok {t : State} {op : Addr} {j : Nat} {c : Bool} (h1 : t.gpr .x1 = op + BitVec.ofNat 64 j)
    (h15 : t.gpr .x15 = mask c) (hwr : InRegions t.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa (.block [.ldrb .x3 .x1 0, .logic .and .x .x3 .x3 .x15, .strb .x3 .x1 0, .addImm .x .x1 .x1 1,
      .subImm .x .x2 .x2 1]) t fun u =>
      (u.mem = t.mem.write (op + BitVec.ofNat 64 j) 1 (if c then t.mem (op + BitVec.ofNat 64 j) else 0) ∧
        u.gpr .x1 = op + BitVec.ofNat 64 (j + 1) ∧ u.gpr .x2 = t.gpr .x2 - BitVec.ofNat 64 1) ∧
      Keep [.x1, .x2, .x3] t u := by
  have hrd : InRegions (t.rd ++ t.wr) (op + BitVec.ofNat 64 j) 1 :=
    let ⟨r, hr, hc⟩ := hwr; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [h1, h15, hrd, hwr, VG.Proof.MlKem.AArch64.read_one]
  congr 1
  cases c
  · simp [mask]
  · rw [show mask true = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    have := (t.mem (op + BitVec.ofNat 64 j)).isLt
    simp

theorem maskOutputStep_ok {s₀ t : State} {op : Addr} {len j : Nat} {c : Bool} (hl : len < 2 ^ 31) (hj : j < len)
    (h15 : s₀.gpr .x15 = mask c) (hwr : ∀ i < len, InRegions s₀.wr (op + BitVec.ofNat 64 i) 1)
    (hI : MaskOutputInv s₀ op c j t) :
    WP isa (.block [.ldrb .x3 .x1 0, .logic .and .x .x3 .x3 .x15, .strb .x3 .x1 0, .addImm .x .x1 .x1 1,
      .subImm .x .x2 .x2 1]) t fun u => MaskOutputInv s₀ op c (j + 1) u ∧ u.gpr .x2 = t.gpr .x2 - BitVec.ofNat 64 1 := by
  have k₀ := hI.keep
  refine WP.mono (maskOutputByte_ok hI.x1 ((k₀.gpr .x15 (by decide)).trans h15) (by rw [k₀.wr]; exact hwr j hj))
    fun u ⟨⟨hm, h1, h2⟩, k⟩ => ⟨⟨(k₀.trans k).mono (by decide), h1, ?_, ?_⟩, h2⟩
  · have hw8 : ∀ (m : Mem) (a : Addr) (v : BitVec 8), m.write a 1 v = m.writeW a v := fun _ _ _ => rfl
    intro i hi
    rw [hm, hw8, writeW8_apply]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, hI.frame _ fun i' hi' => out_ne (by omega_using [hl, hj]) (by omega_using [hl, hj, hi']) (by omega_using [hi'])]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega_using [hl, hj, hi]) (by omega_using [hl, hj]) (by omega_using [hij])))]
      exact hI.bytes i (by omega_using [hi, hij])
  · have hw8 : ∀ (m : Mem) (a : Addr) (v : BitVec 8), m.write a 1 v = m.writeW a v := fun _ _ _ => rfl
    intro x hx
    rw [hm, hw8, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega_using [])))]
    exact hI.frame x fun i hi => hx i (by omega_using [hi])

theorem maskOutputLoop_ok {s : State} {out : Addr} {k : Nat} {c : Bool}
 (positive : 0<k) (size : k<2^31) (pointer : s.gpr .x1=out) (count : s.gpr .x2=BitVec.ofNat 64 k)
 (maskValue : s.gpr .x15=mask c) (writable : ∀ i<k,InRegions s.wr (out+BitVec.ofNat 64 i) 1) :
 WP isa (countLoop .x2 [.ldrb .x3 .x1 0,.logic .and .x .x3 .x3 .x15,.strb .x3 .x1 0,.addImm .x .x1 .x1 1]) s fun t =>
 Spec.Rsa.bytesAt t.mem out k=(if c then Spec.Rsa.bytesAt s.mem out k else List.replicate k 0) ∧
 Outside out 0 k s.mem t.mem ∧ Keep [.x1,.x2,.x3] s t := by
 refine WP.mono (wp_countdown (N:=k) (by omega_using [size]) (by omega_using [positive]) (MaskOutputInv s out c)
  (fun j hj t inv _ =>maskOutputStep_ok size hj maskValue writable inv)
  ⟨Keep.refl _ _,by simpa only [show BitVec.ofNat 64 0=0#64 from rfl,BitVec.add_zero] using pointer,
   fun _ h =>by omega,fun _ _ =>rfl⟩ count) ?_
 intro t inv
 refine ⟨?_,?_,inv.keep⟩
 · cases c
   · change Spec.Rsa.bytesAt t.mem out k=List.replicate k 0
     apply List.ext_getElem
     · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range,List.length_replicate]
     · intro i hi _
       have bound : i<k := by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi
       simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range,List.getElem_replicate]
       simpa using inv.bytes i bound
   · change Spec.Rsa.bytesAt t.mem out k=Spec.Rsa.bytesAt s.mem out k
     apply List.ext_getElem
     · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range]
     · intro i hi _
       have bound : i<k := by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi
       simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range]
       simpa using inv.bytes i bound
 · intro x hx
   apply inv.frame x
   intro i hi eq
   subst x
   rw [show ofs out (out+BitVec.ofNat 64 i)=i from Mem.sub_ofNat_toNat _ (by omega_using [size, hi])] at hx
   omega_using [hi, hx]

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Serialize both outputs with the same success mask and return exactly 1 or 3. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/MaskX.lean`, which only this module imported.
section

/-! Mask the private output according to the final 0/1 public-result predicate. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem maskX_ok {s : State} {B out : Addr} {Z k : Nat} {c : Bool}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B) (positive : 0<k) (size : k<2^31)
 (pointer : word s.mem B (8*sX)=out) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (flag : word s.mem B (8*sTmp)=BitVec.ofNat 64 c.toNat)
 (writable : ∀ i<k,InRegions s.wr (out+BitVec.ofNat 64 i) 1)
 (outside : ∀ i<k,Z≤ofs B (out+BitVec.ofNat 64 i)) :
 WP isa Generate.maskX s fun t =>
 Spec.Rsa.bytesAt t.mem out k=(if c then Spec.Rsa.bytesAt s.mem out k else List.replicate k 0) ∧
 t.gpr .x15=mask c ∧ Outside out 0 k s.mem t.mem ∧
 (∀ q,ofs B q<Z→t.mem q=s.mem q) ∧ Keep [.x1,.x2,.x3,.x7,.x15] s t := by
 have neg : (0#64 : Addr)-BitVec.ofNat 64 c.toNat=mask c := by cases c <;>rfl
 unfold Generate.maskX
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x1,.x2,.x3,.x7,.x15] (Q:=fun a =>a.gpr .x1=out ∧
  a.gpr .x2=BitVec.ofNat 64 k ∧ a.gpr .x15=mask c ∧ a.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [base,hdr_enc (show sX<32 by decide),hdr_enc (show sLen<32 by decide),hdr_enc (show sTmp<32 by decide),
    scratch.ld (d:=8*sX) (by unfold sX;omega_using [room]),scratch.ld (d:=8*sLen) (by unfold sLen;omega_using [room]),
    scratch.ld (d:=8*sTmp) (by unfold sTmp;omega_using [room]),pointer,length,flag,neg]
   exact neg
 · rintro a ⟨⟨ptrA,countA,maskA,memA⟩,restA⟩
   refine WP.mono (maskOutputLoop_ok positive size ptrA countA maskA
    (fun i hi =>by rw [restA.wr];exact writable i hi)) ?_
   rintro t ⟨bytes,frame,rest⟩
   have fullFrame : Outside out 0 k s.mem t.mem := by rw [←memA];exact frame
   refine ⟨by rw [memA] at bytes;exact bytes,(rest.gpr .x15 (by decide)).trans maskA,fullFrame,?_,
    (restA.trans rest).mono (by simp)⟩
   intro q hq
   exact fullFrame q (Or.inr (by have sep : k≤ofs out q :=le_ofs_of_sep outside hq;omega_using [sep]))

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem finish_ok {s : State} {B xp yp : Addr} {Z w k : Nat} {mi : BitVec 64} {c : Bool}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (words : w=(k+7)/8) (positive : 0<k) (size : k<2^31)
 (x : word s.mem B (8*sX)=xp) (y : word s.mem B (8*sY)=yp) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (flag : word s.mem B (8*sTmp)=BitVec.ofNat 64 c.toNat)
 (writeX : ∀ i<k,InRegions s.wr (xp+BitVec.ofNat 64 i) 1)
 (writeY : ∀ i<k,InRegions s.wr (yp+BitVec.ofNat 64 i) 1)
 (outsideX : ∀ i<k,Z≤ofs B (xp+BitVec.ofNat 64 i))
 (outsideY : ∀ i<k,Z≤ofs B (yp+BitVec.ofNat 64 i))
 (separate : ∀ i<k,k≤ofs yp (xp+BitVec.ofNat 64 i)) :
 WP isa Generate.finish s fun t =>
 t.gpr .x0=(if c then 1#64 else 3#64) ∧
 Spec.Rsa.bytesAt t.mem xp k=(if c then Spec.Rsa.bytesAt s.mem xp k else List.replicate k 0) ∧
 Spec.Rsa.bytesAt t.mem yp k=Spec.Rsa.i2osp (if c then wv s.mem B (slot w 6) w else 0) k ∧
 Frame [⟨xp,k⟩,⟨yp,k⟩] s.mem t.mem ∧ Keep (.x0::mmRegs) s t := by
 have room256 : 256≤Z := by unfold slot hdrBytes at room;omega_using [room]
 have yRoom := Nat.le_trans (slot_le (w:=w) (show 6<8 by decide)) room
 have wPositive : 0<w := by rw [words];omega_using [positive]
 unfold Generate.finish
 simp only [seqs]
 rw [WP.seq_iff]
 refine WP.mono (maskX_ok good.scr room256 good.x0 positive size x length flag writeX outsideX) ?_
 rintro a ⟨bytesX,maskA,frameA,sameA,restA⟩
 have headerA (i : Nat) (hi : i<32) : word a.mem B (8*i)=word s.mem B (8*i) :=
  workspace_word (by have := good.scr.nowrap;omega_using [this]) sameA (by have := hdr_lt_slot w 8 hi;omega_using [room256, hi])
 have goodA : Good a B Z w mi :=
  ⟨good.scr.congr restA.wr,(restA.gpr .x0 (by decide)).trans good.x0,
   (headerA sW (by decide)).trans good.hdr.hw,(headerA sMinv (by decide)).trans good.hdr.hminv,
   fun i hi =>(headerA (sArr i) (by unfold sArr;omega_using [hi])).trans (good.hdr.harr i hi)⟩
 have arrayA : wv a.mem B (slot w 6) w=wv s.mem B (slot w 6) w := by
  apply wv_congr
  intro i hi
  exact workspace_word (by have := good.scr.nowrap;omega_using [this]) sameA (by omega_using [yRoom, hi])
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x8,.x1,.x9] (Q:=fun b =>b.gpr .x8=off B (slot w 6) ∧
  b.gpr .x1=yp+BitVec.ofNat 64 k ∧ b.gpr .x9=BitVec.ofNat 64 k ∧ b.mem=a.mem) ?_ rfl rfl rfl) ?_
 · brun [goodA.x0,hdr_enc (show sArr 6<32 by decide),hdr_enc (show sY<32 by decide),hdr_enc (show sLen<32 by decide),
    header_read goodA room (show sArr 6<32 by decide),header_read goodA room (show sY<32 by decide),
    header_read goodA room (show sLen<32 by decide),goodA.hdr.harr 6 (by decide),
    (headerA sY (by decide)).trans y,(headerA sLen (by decide)).trans length]
 · rintro b ⟨⟨srcB,dstB,countB,memB⟩,restB⟩
   have before := restA.trans restB
   rw [WP.seq_iff]
   refine WP.mono (storeBE_ok (good.scr.congr before.wr) srcB dstB countB
    ((restB.gpr .x15 (by decide)).trans maskA) (by omega_using [positive]) size words (by omega_using [yRoom])
    (fun i hi =>by rw [before.wr];exact writeY i hi) outsideY) ?_
   rintro d ⟨bytesY,storeFrame,_,_,restD⟩
   have frameD : Outside yp 0 k b.mem d.mem := by
    intro q hq
    apply storeFrame q
    intro i hi eq
    subst q
    rw [show ofs yp (yp+BitVec.ofNat 64 i)=i from Mem.sub_ofNat_toNat _ (by omega_using [size, hi])] at hq
    omega_using [room, words, positive, size, x, y, length, flag, room256, yRoom, wPositive, maskA, arrayA, srcB, dstB, countB, hi, hq]
   have sameD (q : Addr) (hq : ofs B q<Z) : d.mem q=s.mem q := by
    rw [frameD q (Or.inr (by have sep : k≤ofs yp q :=le_ofs_of_sep outsideY hq;omega_using [sep])),memB]
    exact sameA q hq
   have flagD : word d.mem B (8*sTmp)=BitVec.ofNat 64 c.toNat :=
    (workspace_word (by have := good.scr.nowrap;omega_using [this]) sameD
     (by have := hdr_lt_slot w 8 (show sTmp<32 by decide);omega_using [room, this])).trans flag
   have xD : Spec.Rsa.bytesAt d.mem xp k=(if c then Spec.Rsa.bytesAt s.mem xp k else List.replicate k 0) := by
    rw [←bytesX]
    apply List.ext_getElem
    · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range]
    · intro i hi _
      have bound : i<k := by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi
      simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range]
      rw [frameD _ (Or.inr (by have := separate i bound;omega_using [this])),memB]
   have yD : Spec.Rsa.bytesAt d.mem yp k=Spec.Rsa.i2osp (if c then wv s.mem B (slot w 6) w else 0) k := by
    change (List.range k).map (fun i =>d.mem (yp+BitVec.ofNat 64 i))=_
    rw [bytesY,memB,arrayA]
   have total := before.trans restD
   have ret : (3#64 : Addr)-(BitVec.ofNat 64 c.toNat <<< 1)=(if c then 1#64 else 3#64) := by cases c <;>rfl
   refine WP.mono (WP.keep [.x9,.x0] (Q:=fun t =>t.gpr .x0=(if c then 1#64 else 3#64) ∧ t.mem=d.mem) ?_ rfl rfl rfl) ?_
   · brun [(total.gpr .x0 (by simp)).trans good.x0,hdr_enc (show sTmp<32 by decide),flagD,
      (good.scr.congr total.wr).ld (d:=8*sTmp) (by have := hdr_lt_slot w 8 (show sTmp<32 by decide);omega_using [room, this]),ret]
     exact ret
   · rintro t ⟨⟨status,mem⟩,rest⟩
     have lastFrame : Outside yp 0 k a.mem d.mem := by rw [←memB];exact frameD
     exact ⟨status,by rw [mem];exact xD,by rw [mem];exact yD,
      by rw [mem];exact (outside_frame_member frameA (by simp)).trans (outside_frame_member lastFrame (by simp)),
      (total.trans rest).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
