module

public import VerifiedGarbage.Proof.Bignum.X86_64.PdMain
public import VerifiedGarbage.Impl.Rsa.X86_64.WordIO
public import VerifiedGarbage.Impl.Rsa.X86_64.Compare8
import VerifiedGarbage.Proof.Bignum.X86_64.WordIOLoad
import VerifiedGarbage.Proof.Bignum.X86_64.PcMain
import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.WordIOBytes
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.X86_64.Cmp

/-! ### `Bignum.X86_64.Compare8`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Compare8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Compare8
open VG.Proof.Bignum VG.Proof.MlKem.X86_64

structure Chain (s : State) (B : Addr) (Z eX eN j : Nat) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax,.rbp,.r14] s t
  mem : t.mem=s.mem
  index : t.gpr .r14=BitVec.ofNat 64 j
  val : ∃ (c : Bool) (d : Nat),t.cf=some c ∧ d<2^(64*(j+i)) ∧
    d+wv s.mem B eN (j+i)=wv s.mem B eX (j+i)+2^(64*(j+i))*c.toNat

theorem addr_word {b r B : Addr} {e j : Nat}
    (hb : b=off B e) (hr : r=BitVec.ofNat 64 j) (i : Nat) :
    b+r*BitVec.ofNat 64 8+BitVec.ofInt 64 (8*(i:Int))=off B (e+8*(j+i)) := by
  rw [hb,hr,ofNat_mul8,show (8*(i:Int))=((8*i:Nat):Int) by rw [Int.natCast_mul]; rfl,BitVec.ofInt_natCast]
  simp only [off,BitVec.add_assoc,BitVec.ofNat_add_ofNat]
  congr 2
  omega_using []

theorem one_ok {s t : State} {B : Addr} {Z eX eN w j i : Nat}
    (hbx : s.gpr .rbx=off B eX) (h10 : s.gpr .r10=off B eN)
    (hX : eX+8*w≤Z) (hN : eN+8*w≤Z) (hji : j+i<w)
    (h : Chain s B Z eX eN j i t) :
    WP isa (.block (one i)) t (Chain s B Z eX eN j (i+1)) := by
  obtain ⟨c,d,hcf,hd,hval⟩ := h.val
  have bx := (h.keep.gpr (by decide)).trans hbx
  have r10 := (h.keep.gpr (by decide)).trans h10
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem=t.mem ∧ ∃ c' : Bool,u.cf=some c' ∧
    ∃ r : BitVec 64,r.toNat+(word t.mem B (eN+8*(j+i))).toNat+c.toNat =
      (word t.mem B (eX+8*(j+i))).toNat+2^64*c'.toNat) ?_ rfl)
    fun u ⟨⟨hm,c',hcf',r,he⟩,ku⟩ => ?_
  · xrun [one,State.ea,ix,addr_word bx h.index i,addr_word r10 h.index i,
      h.scr.ld (show eX+8*(j+i)+8≤Z by omega_using [hX, hji]),h.scr.ld (show eN+8*(j+i)+8≤Z by omega_using [hN, hji]),hcf]
    exact ⟨_,sbb_toNat _ _ _⟩
  · rw [h.mem] at he
    refine ⟨h.scr.congr ku.2.2,(h.keep.trans ku).mono (by decide),hm.trans h.mem,
      (ku.gpr (by decide)).trans h.index,c',d+2^(64*(j+i))*r.toNat,hcf',?_,?_⟩
    · have hb := Nat.mul_le_mul_left (2^(64*(j+i))) (show r.toNat+1≤2^64 from r.isLt)
      rw [show j+(i+1)=(j+i)+1 by omega_using [],pow64_succ]
      rw [Nat.mul_add,Nat.mul_one] at hb
      omega_using [hd, hb]
    · rw [show j+(i+1)=(j+i)+1 by omega_using []]
      simp only [wv]
      rw [pow64_succ]
      grind

theorem words_ok {s : State} {B : Addr} {Z eX eN w j : Nat}
    (hbx : s.gpr .rbx=off B eX) (h10 : s.gpr .r10=off B eN)
    (hX : eX+8*w≤Z) (hN : eN+8*w≤Z) (n : Nat) :
    ∀ i t,j+i+n≤w → Chain s B Z eX eN j i t →
      WP isa (.block (words i n)) t (Chain s B Z eX eN j (i+n)) := by
  induction n with
  | zero => intro i t _ h; exact WP.block_nil h
  | succ n ih =>
    intro i t hn h
    unfold words
    rw [WP.block_append_iff]
    refine WP.mono (one_ok hbx h10 hX hN (by omega_using [hn]) h) fun u hu => ?_
    simpa only [Nat.add_assoc,Nat.add_comm 1 n] using ih (i+1) u (by omega_using [hn]) hu

theorem block8_ok {s t : State} {B : Addr} {Z w eX eN j : Nat}
    (hbx : s.gpr .rbx=off B eX) (h10 : s.gpr .r10=off B eN)
    (h12 : s.gpr .r12=BitVec.ofNat 64 w) (hw : w<2^31)
    (hX : eX+8*w≤Z) (hN : eN+8*w≤Z) (hj : j+8≤w)
    (h : CmpInv s B Z eX eN j t) :
    WP isa (.block block8) t fun u => u.zf=some (decide (j+8=w)) ∧ CmpInv s B Z eX eN (j+8) u := by
  obtain ⟨c,d,hbp,hd,hval⟩ := h.val
  unfold block8
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (WP.keep [.rbp] (Q := fun a => a.cf=some c ∧ a.mem=t.mem)
    (by xrun [cfFromRbp,hbp,cf_mask]) rfl) fun a ⟨⟨hcf,hm⟩,ka⟩ => ?_
  rw [WP.block_append_iff]
  have hc : Chain s B Z eX eN j 0 a := ⟨h.scr.congr ka.2.2,(h.keep.trans ka).mono (by decide),
    hm.trans h.mem,(ka.gpr (by decide)).trans h.r14,c,d,hcf,hd,hval⟩
  refine WP.mono (words_ok hbx h10 hX hN 8 0 a (by omega_using [hj]) hc) fun b hb => ?_
  obtain ⟨c',d',hcf',hd',hv'⟩ := hb.val
  have hadd : BitVec.ofNat 64 j+8=BitVec.ofNat 64 (j+8) := by rw [BitVec.ofNat_add]; rfl
  refine WP.mono (WP.keep [.rbp,.r14] (Q := fun u => u.mem=b.mem ∧
    u.gpr .rbp=mask c' ∧ u.gpr .r14=BitVec.ofNat 64 (j+8) ∧ u.zf=some (decide (j+8=w))) ?_ rfl)
    fun u ⟨⟨hu,hbp',h14,hz⟩,ku⟩ =>
      ⟨hz,hb.scr.congr ku.2.2,(hb.keep.trans ku).mono (by decide),hu.trans hb.mem,h14,c',d',hbp',hd',hv'⟩
  xrun [cfToRbp,hcf',hb.index,(hb.keep.gpr (by decide)).trans h12,hadd,
    ofNat_sub_beq (show j+8<2^64 by omega_using [hw, hj]) (show w<2^64 by omega_using [hw]),mask]
  rfl

theorem loop8_ok {s : State} {B : Addr} {Z w eX eN : Nat} (hs : Scr s B Z)
    (hbx : s.gpr .rbx=off B eX) (h10 : s.gpr .r10=off B eN)
    (h12 : s.gpr .r12=BitVec.ofNat 64 w) (hbp : s.gpr .rbp=mask false)
    (hw : 1≤w) (hw' : w<2^31) (h8 : w%8=0) (hX : eX+8*w≤Z) (hN : eN+8*w≤Z) :
    WP isa loop8 s fun t => t.gpr .rbp=mask (decide (wv s.mem B eX w < wv s.mem B eN w)) ∧
      t.mem=s.mem ∧ Keep [.rax,.rbp,.r14] s t := by
  unfold loop8
  refine WP.seq (WP.mono (WP.keep [.r14] (Q := fun a => a.gpr .r14=0 ∧ a.mem=s.mem)
    (by xrun) rfl) fun a ⟨⟨h14,hm⟩,ka⟩ => ?_)
  refine wp_upto (a := 0) (N := w/8) (by omega_using [hw, h8]) (fun j t => CmpInv s B Z eX eN (8*j) t) ?_ ?_ ?_
  · intro j _ hj t h
    refine WP.mono (block8_ok hbx h10 h12 hw' hX hN (by omega_using [hj]) h) fun u ⟨hz,hu⟩ => ?_
    have hn : 8*j+8=8*(j+1) := by omega_using []
    rw [hn] at hu
    refine ⟨?_,hu⟩
    rw [hz]
    exact congrArg some (decide_eq_decide.mpr (by omega_using [h8]))
  · intro t h
    have hn : 8*(w/8)=w := by omega_using [h8]
    rw [hn] at h
    obtain ⟨c,d,hc,hd,hv⟩ := h.val
    exact ⟨by rw [hc,lt_of_borrow hd hv],h.mem,h.keep⟩
  · exact ⟨hs.congr ka.2.2,ka.mono (by decide),hm,h14,
      false,0,(ka.gpr (by decide)).trans hbp,Nat.one_pos,rfl⟩

theorem code_ok {s : State} {B : Addr} {Z w eX eN : Nat} (hs : Scr s B Z)
    (hbx : s.gpr .rbx=off B eX) (h10 : s.gpr .r10=off B eN)
    (h12 : s.gpr .r12=BitVec.ofNat 64 w) (hbp : s.gpr .rbp=mask false)
    (hw : 1≤w) (hw' : w<2^31) (hX : eX+8*w≤Z) (hN : eN+8*w≤Z) :
    WP isa code s fun t => t.gpr .rbp=mask (decide (wv s.mem B eX w < wv s.mem B eN w)) ∧
      t.mem=s.mem ∧ Keep [.rax,.rbp,.r14] s t := by
  unfold code
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun a => a.zf=some (decide (w%8=0)) ∧ a.mem=s.mem)
    (by
      xrun [h12,sx0,show BitVec.signExtend 64 (7:BitVec 32)=7 from rfl]
      simp only [sub_beq_zero,VG.Proof.Bignum.X86_64.and7_eq w (by omega_using [hw'])]) rfl)
    fun a ⟨⟨hz,hm⟩,ka⟩ => ?_)
  refine WP.ite (decide (w%8=0)) (by simp [eval,hz]) ?_ ?_
  · intro h8
    refine WP.mono (loop8_ok (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hbx)
      ((ka.gpr (by decide)).trans h10) ((ka.gpr (by decide)).trans h12)
      ((ka.gpr (by decide)).trans hbp) hw hw' (of_decide_eq_true h8) hX hN)
      fun t ⟨hv,ht,kt⟩ => ⟨by simpa only [hm] using hv,ht.trans hm,(ka.trans kt).mono (by decide)⟩
  · intro _
    refine WP.mono (cmpLoop_ok (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hbx)
      ((ka.gpr (by decide)).trans h10) ((ka.gpr (by decide)).trans h12)
      ((ka.gpr (by decide)).trans hbp) hw hw' hX hN)
      fun t ⟨hv,ht,kt⟩ => ⟨by simpa only [hm] using hv,ht.trans hm,(ka.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.Compare8

end

end

/-! ### `Bignum.X86_64.WordIOStore`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Bignum.X86_64.WordIO
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.WordIO
open VG.Proof.Bignum VG.Proof.MlKem.X86_64

theorem masked_digit (m : Mem) (B : Addr) (ed w : Nat) {j : Nat} (hj : j<w) (c : Bool) :
    word m B (ed+8*j) &&& mask c =
      BitVec.ofNat 64 ((if c then wv m B ed w else 0) / 256^(8*j)) := by
  apply BitVec.eq_of_toNat_eq
  rw [and_mask_toNat,word_of_wv _ _ _ _ hj,BitVec.toNat_ofNat,pow256]
  cases c <;> simp

theorem store_step {s t : State} {B out : Addr} {Z ed k w : Nat} {c : Bool}
    (hs : Scr s B Z) (hbx : s.gpr .rbx = off B ed) (hcx : s.gpr .rcx = BitVec.ofNat 64 k)
    (h15 : s.gpr .r15 = mask c) (hk : k=8*w) (hk' : k<2^31) (hed : ed+8*w≤Z)
    (hout : InRegions s.wr out k) (hsep : ∀ i<k, Z≤ofs B (out+BitVec.ofNat 64 i))
    {j : Nat} (hj : j<w) (h : SInv s out k (if c then wv s.mem B ed w else 0) (8*j) t) :
    WP isa (.block [.mov .rax (.mem (atByte .rbx .rdx)), .alu .and .rax (.reg .r15), .bswap .rax,
      .alu .sub .r14 (.imm 8), .store (at0 .r14) .rax,
      .alu .add .rdx (.imm 8), .alu .cmp .rdx (.reg .rcx)]) t fun u =>
      u.zf=some (decide (j+1=w)) ∧ SInv s out k (if c then wv s.mem B ed w else 0) (8*(j+1)) u := by
  have hn := hs.nowrap
  let Y := if c then wv s.mem B ed w else 0
  have hwd : word t.mem B (ed+8*j) = word s.mem B (ed+8*j) := by
    apply Mem.readW_congr
    intro b hb
    apply h.frame
    intro z hz he
    have hsep' := hsep (k-1-z) (by omega_arith)
    rw [← he,ofs_off B (by omega_arith)] at hsep'
    omega_arith
  have hread : InRegions (t.rd ++ t.wr) (off B (ed+8*j)) 8 := by
    rw [h.rd,h.wr]; exact hs.ld (by omega_arith)
  have hwrite : InRegions t.wr (out+BitVec.ofNat 64 (k-8*(j+1))) 8 := by
    rw [h.wr]; exact VG.CallLay.inRegions_sub hout (by omega_arith) (by omega_arith)
  have hptr : out+BitVec.ofNat 64 (k-8*j)-8 = out+BitVec.ofNat 64 (k-8*(j+1)) := by
    rw [BitVec.sub_eq_iff_eq_add,BitVec.add_assoc,
      show (8:BitVec 64)=BitVec.ofNat 64 8 from rfl,BitVec.ofNat_add_ofNat]
    congr 2; omega_arith
  have hadd : BitVec.ofNat 64 (8*j)+8 = BitVec.ofNat 64 (8*(j+1)) := by
    rw [show (8:BitVec 64)=BitVec.ofNat 64 8 from rfl,BitVec.ofNat_add_ofNat]; congr 1
  have haddr : off B ed+BitVec.ofNat 64 (8*j)=off B (ed+8*j) := by
    simp only [off,BitVec.add_assoc,BitVec.ofNat_add_ofNat]
  have hz : (BitVec.ofNat 64 (8*(j+1)) == BitVec.ofNat 64 k)=decide (j+1=w) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,decide_eq_true_eq]
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 8*(j+1)<2^64 by omega_arith),
        Nat.mod_eq_of_lt (show k<2^64 by omega_arith)] at this
      omega_arith
    · intro he; congr 1; omega_arith
  refine WP.mono (WP.keep [.rax,.rdx,.r14] (Q := fun u =>
    u.mem=t.mem.writeW (out+BitVec.ofNat 64 (k-8*(j+1))) (bswap64 (BitVec.ofNat 64 (Y/256^(8*j)))) ∧
    u.gpr .rdx=BitVec.ofNat 64 (8*(j+1)) ∧ u.gpr .r14=out+BitVec.ofNat 64 (k-8*(j+1)) ∧
    u.zf=some (decide (j+1=w))) ?_ rfl) fun u ⟨⟨hm,hdx,h14,hzf⟩,ku⟩ => ?_
  · xrun [eab,ea0,h.rdx,h.r14,(h.keep.gpr (by decide)).trans hbx,
      (h.keep.gpr (by decide)).trans hcx,(h.keep.gpr (by decide)).trans h15,haddr,hread,
      hwd,masked_digit _ _ _ _ hj c,hptr,hwrite,hadd,sub_beq_zero,hz]
    rfl
  · refine ⟨hzf,ku.2.2.trans h.wr,ku.2.1.trans h.rd,(h.keep.trans ku).mono (by decide),hdx,h14,
      (fun hbad => by omega_arith),?_,?_⟩
    · intro z hzz
      rw [hm]
      have hd : ((out+BitVec.ofNat 64 (k-1-z))-(out+BitVec.ofNat 64 (k-8*(j+1)))).toNat =
          k-1-z-(k-8*(j+1)) := VG.Offset.sub_toNat out (by omega_arith) (by omega_arith)
      change (if ((out+BitVec.ofNat 64 (k-1-z))-(out+BitVec.ofNat 64 (k-8*(j+1)))).toNat<8 then
        (bswap64 (BitVec.ofNat 64 (Y/256^(8*j)))).extractLsb'
          (8*((out+BitVec.ofNat 64 (k-1-z))-(out+BitVec.ofNat 64 (k-8*(j+1)))).toNat) 8
        else t.mem (out+BitVec.ofNat 64 (k-1-z))) = _
      rw [hd]
      by_cases hzold : z<8*j
      · rw [ite_eq_right (by omega_arith)]; exact h.bytes z hzold
      · rw [ite_eq_left (by omega_arith),bswap_byte _ (by omega_arith),extract_nat _ (by omega_arith),Nat.div_div_eq_div_mul,
          ← Nat.pow_add]
        congr 3; omega_arith
    · intro x hx
      rw [hm]
      apply Eq.trans (Mem.write_apply ?_) (h.frame x (fun z hz => hx z (by omega_arith)))
      intro hin
      let b := (x-(out+BitVec.ofNat 64 (k-8*(j+1)))).toNat
      have hb : b<8 := hin
      have he : x = out+BitVec.ofNat 64 (k-8*(j+1)+b) := by
        rw [BitVec.ofNat_add,← BitVec.add_assoc]
        change x = (out+BitVec.ofNat 64 (k-8*(j+1)))+BitVec.ofNat 64 b
        simp only [b,BitVec.ofNat_toNat,BitVec.setWidth_eq]
        rw [BitVec.add_comm (out+BitVec.ofNat 64 (k-8*(j+1))) _,BitVec.sub_add_cancel]
      apply hx (8*(j+1)-1-b) (by omega_arith)
      rw [he]
      congr 2; omega_arith

theorem storeWords_ok {s : State} {B out : Addr} {Z ed k w : Nat} {c : Bool}
    (hs : Scr s B Z) (hbx : s.gpr .rbx = off B ed) (hsi : s.gpr .rsi = out)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 k) (h15 : s.gpr .r15 = mask c)
    (hk : k=8*w) (hk1 : 0<k) (hk' : k<2^31) (hed : ed+8*w≤Z)
    (hout : InRegions s.wr out k) (hsep : ∀ i<k, Z≤ofs B (out+BitVec.ofNat 64 i)) :
    WP isa storeWords s fun t =>
      (List.range k).map (fun i => t.mem (out+BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B ed w else 0) k ∧
      (∀ x, (∀ i<k, x≠out+BitVec.ofNat 64 i) → t.mem x=s.mem x) ∧
      t.wr=s.wr ∧ t.rd=s.rd ∧ Keep [.rax,.rdx,.rbp,.r14] s t := by
  unfold storeWords
  refine WP.seq (WP.mono (WP.keep [.r14,.rdx] (Q := fun t => t.gpr .r14=out+BitVec.ofNat 64 k ∧
    t.gpr .rdx=0 ∧ t.mem=s.mem) (by xrun [hsi,hcx]) rfl) fun a ⟨⟨h14,hdx,hm⟩,ka⟩ => ?_)
  refine wp_upto (a := 0) (N := w) (by omega_arith)
    (fun j t => SInv s out k (if c then wv s.mem B ed w else 0) (8*j) t) ?_ ?_ ?_
  · intro j _ hj t h
    exact store_step hs hbx hcx h15 hk hk' hed hout hsep hj h
  · intro t h
    refine ⟨?_,?_,h.wr,h.rd,h.keep⟩
    · apply List.ext_getElem (by simp [Spec.Rsa.i2osp])
      intro i hi _
      have hik : i<k := by simpa using hi
      simp only [List.getElem_map,List.getElem_range,Spec.Rsa.i2osp]
      have hb := h.bytes (k-1-i) (by omega_arith)
      rwa [show k-1-(k-1-i)=i by omega_arith] at hb
    · intro x hx
      exact h.frame x (fun i hi => hx _ (by omega_arith))
  · exact ⟨ka.2.2,ka.2.1,ka.mono (by decide),hdx,by simpa using h14,
      (fun hbad => by omega_arith),(fun i hi => by omega_arith),fun x _ => by rw [hm]⟩

theorem store_ok {s : State} {B out : Addr} {Z ed k w : Nat} {c : Bool}
    (hs : Scr s B Z) (hbx : s.gpr .rbx = off B ed) (hsi : s.gpr .rsi = out)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 k) (h15 : s.gpr .r15 = mask c)
    (hk1 : 1≤k) (hk' : k<2^31) (hw : w=(k+7)/8) (hed : ed+8*w≤Z)
    (hout : InRegions s.wr out k) (hsep : ∀ i<k, Z≤ofs B (out+BitVec.ofNat 64 i)) :
    WP isa store s fun t =>
      (List.range k).map (fun i => t.mem (out+BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B ed w else 0) k ∧
      (∀ x, (∀ i<k, x≠out+BitVec.ofNat 64 i) → t.mem x=s.mem x) ∧
      t.wr=s.wr ∧ t.rd=s.rd ∧ Keep [.rax,.rdx,.rbp,.r14] s t := by
  unfold store
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun a => a.zf=some (decide (k%8=0)) ∧ a.mem=s.mem)
    (by
      xrun [lengthTest,hcx,sx7,sx0]
      simp only [sub_beq_zero,and7_eq k (by omega_arith)]) rfl) fun a ⟨⟨hz,hm⟩,ka⟩ => ?_)
  have hr : InRegions a.wr out k := by rw [ka.2.2]; exact hout
  refine WP.ite (decide (k%8=0)) (by simp [eval,hz]) ?_ ?_
  · intro h8
    have h8 := of_decide_eq_true h8
    refine WP.mono (storeWords_ok (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hbx)
      ((ka.gpr (by decide)).trans hsi) ((ka.gpr (by decide)).trans hcx)
      ((ka.gpr (by decide)).trans h15) (by omega_arith) (by omega_arith) hk' hed hr hsep)
      fun t ⟨hv,ho,hw',hr',kt⟩ => ⟨by simpa only [hm] using hv,
        fun x hx => (ho x hx).trans (congrFun hm x),hw'.trans ka.2.2,hr'.trans ka.2.1,
        (ka.trans kt).mono (by decide)⟩
  · intro _
    refine WP.mono (storeBE_ok (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hbx)
      ((ka.gpr (by decide)).trans hsi) ((ka.gpr (by decide)).trans hcx)
      ((ka.gpr (by decide)).trans h15) hk1 hk' hw hed
      (fun i hi => VG.CallLay.inRegions_sub hr (by omega_arith) (by omega_arith)) hsep)
      fun t ⟨hv,ho,hw',hr',kt⟩ => ⟨by simpa only [hm] using hv,
        fun x hx => (ho x hx).trans (congrFun hm x),hw'.trans ka.2.2,hr'.trans ka.2.1,
        (ka.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.WordIO

end

end

@[expose] public section

namespace VG.Proof.Bignum.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

def wordIn : List (Prog isa) :=
  [.block [.mov .rsi (.mem (hdr sIn)), .mov .rcx (.mem (hdr sK)), .mov .rbx (.mem (hdr (sArr aX)))], VG.Impl.Rsa.X86_64.WordIO.load]

theorem wordLoadArr_ok {s : State} {B : Addr} {Z k : Nat} {p : Addr} {bs : List Byte} {j : Nat} (hs : Scr s B Z)
    (hspan : InRegions (s.rd ++ s.wr) p k) (hj : j < 8) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hsrc : Src s B Z p bs) (hk : bs.length = k) (hk1 : 1 ≤ k)
    (hk' : k < 2 ^ 31) (hsi : s.gpr .rsi = p) (hcx : s.gpr .rcx = BitVec.ofNat 64 k)
    (hbx : s.gpr .rbx = off B (slot ((k + 7) / 8) j)) :
    WP isa VG.Impl.Rsa.X86_64.WordIO.load s fun t =>
      wv t.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) = Spec.Rsa.os2ip bs ∧
      Arrays B ((k + 7) / 8) [j] s.mem t.mem ∧ Keep [.rax, .rdx, .rbp, .r14] s t := by
  have := slot_le (w := (k + 7) / 8) hj
  refine WP.mono (WordIO.load_ok hs hsi hcx hbx hk hk1 hk' rfl (by omega_arith) hspan
    (fun i hi => hsrc.val i (by omega_arith)) (fun i hi => Or.inr (by have := hsrc.out i (by omega_arith); omega_arith)))
    fun t ⟨h1, h2, h3⟩ => ⟨h1, Arrays.of_outside (List.mem_singleton_self j) h2 (Nat.le_refl _) (by omega_arith), h3⟩

theorem wordIn_ok {s : State} {B : Addr} {Z k : Nat} {ip : Addr} {xb : List Byte} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 9 ≤ k) (hk : k < 2 ^ 31)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hIn : word s.mem B (8 * sIn) = ip)
    (hb : ∀ j < 8, word s.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)) (hx : Src s B Z ip xb)
    (hxl : xb.length = k) (hspan : InRegions (s.rd ++ s.wr) ip k) :
    WP isa (seqs wordIn) s fun t => wv t.mem B (slot ((k + 7) / 8) aX) ((k + 7) / 8) = Spec.Rsa.os2ip xb ∧
      Arrays B ((k + 7) / 8) [aX] s.mem t.mem ∧ Keep [.rax, .rcx, .rdx, .rbx, .rsi, .rbp, .r14] s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0 := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have eK : sK = 18 := rfl
  have eIn : sIn = 21 := rfl
  have eAX : sArr aX = 9 := rfl
  unfold wordIn
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = ip ∧
      t.gpr .rcx = BitVec.ofNat 64 k ∧ t.gpr .rbx = off B (slot ((k + 7) / 8) aX) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sIn) (by omega_arith), hs.ld (d := 8 * sK) (by omega_arith),
      hs.ld (d := 8 * sArr aX) (by omega_arith), hIn, hK, hb aX (by decide)]) rfl)
    fun t₁ ⟨⟨hsi, hcx, hbx, hm₁⟩, k₁⟩ => ?_)
  rw [seqs_one]
  refine WP.mono (wordLoadArr_ok (hs.congr k₁.2.2) (by rw [k₁.2.1, k₁.2.2]; exact hspan) (by decide) hZ
    (hx.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁) hxl (by omega_arith) hk hsi hcx hbx)
    fun t ⟨hv, ha, k₂⟩ => ⟨hv, by rw [hm₁] at ha; exact ha, (k₁.trans k₂).mono (by decide)⟩

theorem wordSetup_ok {s : State} {B : Addr} {Z k : Nat} {op ep ip : Addr} {L : Nat} {eb xb : List Byte} {N R : Nat}
    (h : PdPre s B Z k op ep ip L eb xb N R) :
    WP isa (seqs (wordIn ++ restStepsWith VG.Impl.Rsa.X86_64.Compare8.code)) s fun t => ∃ minv,
      SetupOut t B Z ((k + 7) / 8) minv N (Spec.Rsa.os2ip xb) ∧ Frm B (pdAll ((k + 7) / 8)) s.mem t.mem ∧
      Keep mmRegs s t ∧ wv t.mem B (slot ((k + 7) / 8) aR2) ((k + 7) / 8) = R := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hZ := h.z
  have hs := h.scr
  have hn := hs.nowrap
  have hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega_arith
  -- The input.
  refine wp_seqs_append (by simp [wordIn]) (by simp [restStepsWith])
    (WP.mono (wordIn_ok hs h.rdi hZ (by omega_arith) (by omega_arith) h.hK h.hIn h.hb h.x h.xl h.inSpan) fun t₁ ⟨hX₁, ha₁, k₁⟩ => ?_)
  have f₁ : Frm B (pdAll ((k + 7) / 8)) s.mem t₁.mem := Frm.of_arrays ha₁ (by simp [pdAll])
  -- The mask, `-m⁻¹` and 1.
  refine WP.mono (setupRestWith_ok VG.Impl.Rsa.X86_64.Compare8.code @Compare8.code_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans h.rdi) hZ (by omega_arith) (by omega_arith)
      (by rw [ha₁.hslot (by decide)]; exact h.hW) (fun j hj => by rw [ha₁.hslot (by unfold sArr; omega_arith)]; exact h.hb j hj)
      (by rw [ha₁.wv_of_not_mem (by decide) (by decide) hn']; exact h.n) hX₁ h.odd)
      fun t₂ ⟨minv, so, f₂', k₂⟩ => ⟨minv, so, f₁.trans (f₂'.mono (by simp [pdAll])), (k₁.trans k₂).mono (by decide), ?_⟩
  rw [f₂'.wv_eq (fun r hr => by
      have := hdr_lt_slot ((k + 7) / 8) aR2 (show 31 < 32 by decide)
      have := slot_sep (w := (k + 7) / 8) (show aR2 ≠ aOne by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [sMinv, sMask, sFn] at * <;> omega_arith)
      (by have := slot_le (w := (k + 7) / 8) (show aR2 < 8 by decide); omega_arith),
    ha₁.wv_of_not_mem (by decide) (by decide) hn']
  exact h.r

def wordOutStepsArr (j : Nat) : List (Prog isa) := [
  .block [.mov .rbx (.mem (hdr (sArr j))), .mov .rsi (.mem (hdr sOut)), .mov .rcx (.mem (hdr sK)),
    .mov .r15 (.mem (hdr sMask))],
  VG.Impl.Rsa.X86_64.WordIO.store,
  .block ([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] ++ exit)]

theorem wordOutPhaseArr_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64} {Y : Nat} {out : Addr} {c : Bool}
    {j : Nat} (hj : j < 8)
    (hg : Good s B Z ((k + 7) / 8) minv) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hY : wv s.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) = Y)
    (hO : word s.mem B (8 * sOut) = out) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hM : word s.mem B (8 * sMask) = mask c)
    (hout : InRegions s.wr out k)
    (hsep : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j)) :
    WP isa (seqs (wordOutStepsArr j)) s fun t =>
      (List.range k).map (fun i => t.mem (out + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp (if c then Y else 0) k ∧
      t.gpr .rax = BitVec.ofNat 64 c.toNat ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧
      Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h0 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0' := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_arith)
  unfold wordOutStepsArr
  refine WP.seq (WP.mono (WP.keep [.rbx, .rsi, .rcx, .r15] (Q := fun t =>
      t.gpr .rbx = off B (slot ((k + 7) / 8) j) ∧ t.gpr .rsi = out ∧ t.gpr .rcx = BitVec.ofNat 64 k ∧
      t.gpr .r15 = mask c ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr j) (by unfold sArr; omega_arith), hl sOut (by decide), hl sK (by decide),
      hl sMask (by decide), hg.hdr.harr j hj, hO, hK, hM]) rfl)
    fun t₁ ⟨⟨hbx, hsi, hcx, h15, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  refine WP.seq (WP.mono (WordIO.store_ok hs₁ hbx hsi hcx h15 hk1 hk' rfl
    (by have := slot_le (w := (k + 7) / 8) hj; omega_arith)
    (by rw [k₁.2.2]; exact hout) hsep) fun t₂ ⟨hb₂, hf₂, hwr₂, hrd₂, k₂⟩ => ?_)
  rw [hm₁, hY] at hb₂
  have hw₂ : ∀ i < 32, word t₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    apply Mem.readW_congr
    intro b hb
    rw [hf₂ _ (scr_ne_out hsep (d := 8 * i) (i := b) (by omega_arith) (by omega_arith)), hm₁]
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [hrd₂, hwr₂, k₁.2.1, k₁.2.2]; exact hl i hi
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi)
  rw [exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 c.toNat ∧ t.gpr .rbx = word s.mem B (8 * 0) ∧
      t.gpr .rbp = word s.mem B (8 * 1) ∧ t.gpr .r12 = word s.mem B (8 * 2) ∧
      t.gpr .r13 = word s.mem B (8 * 3) ∧ t.gpr .r14 = word s.mem B (8 * 4) ∧
      t.gpr .r15 = word s.mem B (8 * 5) ∧ t.mem = t₂.mem) (by
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ sMask (by decide), hw₂ sMask (by decide), hM, mask_and1,
      hl₂ 0 (by decide), hl₂ 1 (by decide), hl₂ 2 (by decide), hl₂ 3 (by decide), hl₂ 4 (by decide),
      hl₂ 5 (by decide), hw₂ 0 (by decide), hw₂ 1 (by decide), hw₂ 2 (by decide), hw₂ 3 (by decide),
      hw₂ 4 (by decide), hw₂ 5 (by decide)]) rfl)
    fun t ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm⟩, k₃⟩ => ⟨by rw [hm]; exact hb₂, hax, ?_,
      fun x hx => by rw [hm, hf₂ x hx, hm₁], ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem wordOutPhase_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64} {Y : Nat} {out : Addr} {c : Bool}
    (hg : Good s B Z ((k + 7) / 8) minv) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hY : wv s.mem B (slot ((k + 7) / 8) aY) ((k + 7) / 8) = Y)
    (hO : word s.mem B (8 * sOut) = out) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hM : word s.mem B (8 * sMask) = mask c)
    (hout : InRegions s.wr out k)
    (hsep : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j)) :
    WP isa (seqs (wordOutStepsArr aY)) s fun t =>
      (List.range k).map (fun i => t.mem (out + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp (if c then Y else 0) k ∧
      t.gpr .rax = BitVec.ofNat 64 c.toNat ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧
      Keep mmRegs s t :=
  wordOutPhaseArr_ok (by decide) hg hZ hk1 hk' hY hO hK hM hout hsep


end VG.Proof.Bignum.X86_64
