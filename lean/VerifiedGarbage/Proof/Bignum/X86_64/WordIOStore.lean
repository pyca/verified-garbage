import VerifiedGarbage.Proof.Bignum.X86_64.WordIOLoad
import VerifiedGarbage.Proof.Bignum.X86_64.Store

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
    have hsep' := hsep (k-1-z) (by omega)
    rw [← he,ofs_off B (by omega)] at hsep'
    omega
  have hread : InRegions (t.rd ++ t.wr) (off B (ed+8*j)) 8 := by
    rw [h.rd,h.wr]; exact hs.ld (by omega)
  have hwrite : InRegions t.wr (out+BitVec.ofNat 64 (k-8*(j+1))) 8 := by
    rw [h.wr]; exact VG.CallLay.inRegions_sub hout (by omega) (by omega)
  have hptr : out+BitVec.ofNat 64 (k-8*j)-8 = out+BitVec.ofNat 64 (k-8*(j+1)) := by
    rw [BitVec.sub_eq_iff_eq_add,BitVec.add_assoc,
      show (8:BitVec 64)=BitVec.ofNat 64 8 from rfl,BitVec.ofNat_add_ofNat]
    congr 2; omega
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
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 8*(j+1)<2^64 by omega),
        Nat.mod_eq_of_lt (show k<2^64 by omega)] at this
      omega
    · intro he; congr 1; omega
  refine WP.mono (WP.keep [.rax,.rdx,.r14] (Q := fun u =>
    u.mem=t.mem.writeW (out+BitVec.ofNat 64 (k-8*(j+1))) (bswap64 (BitVec.ofNat 64 (Y/256^(8*j)))) ∧
    u.gpr .rdx=BitVec.ofNat 64 (8*(j+1)) ∧ u.gpr .r14=out+BitVec.ofNat 64 (k-8*(j+1)) ∧
    u.zf=some (decide (j+1=w))) ?_ rfl) fun u ⟨⟨hm,hdx,h14,hzf⟩,ku⟩ => ?_
  · xrun [eab,ea0,h.rdx,h.r14,(h.keep.gpr (by decide)).trans hbx,
      (h.keep.gpr (by decide)).trans hcx,(h.keep.gpr (by decide)).trans h15,haddr,hread,
      hwd,masked_digit _ _ _ _ hj c,hptr,hwrite,hadd,sub_beq_zero,hz]
    rfl
  · refine ⟨hzf,ku.2.2.trans h.wr,ku.2.1.trans h.rd,(h.keep.trans ku).mono (by decide),hdx,h14,
      (fun hbad => by omega),?_,?_⟩
    · intro z hzz
      rw [hm]
      have hd : ((out+BitVec.ofNat 64 (k-1-z))-(out+BitVec.ofNat 64 (k-8*(j+1)))).toNat =
          k-1-z-(k-8*(j+1)) := VG.Offset.sub_toNat out (by omega) (by omega)
      change (if ((out+BitVec.ofNat 64 (k-1-z))-(out+BitVec.ofNat 64 (k-8*(j+1)))).toNat<8 then
        (bswap64 (BitVec.ofNat 64 (Y/256^(8*j)))).extractLsb'
          (8*((out+BitVec.ofNat 64 (k-1-z))-(out+BitVec.ofNat 64 (k-8*(j+1)))).toNat) 8
        else t.mem (out+BitVec.ofNat 64 (k-1-z))) = _
      rw [hd]
      by_cases hzold : z<8*j
      · rw [ite_eq_right (by omega)]; exact h.bytes z hzold
      · rw [ite_eq_left (by omega),bswap_byte _ (by omega),extract_nat _ (by omega),Nat.div_div_eq_div_mul,
          ← Nat.pow_add]
        congr 3; omega
    · intro x hx
      rw [hm]
      apply Eq.trans (Mem.write_apply ?_) (h.frame x (fun z hz => hx z (by omega)))
      intro hin
      let b := (x-(out+BitVec.ofNat 64 (k-8*(j+1)))).toNat
      have hb : b<8 := hin
      have he : x = out+BitVec.ofNat 64 (k-8*(j+1)+b) := by
        rw [BitVec.ofNat_add,← BitVec.add_assoc]
        change x = (out+BitVec.ofNat 64 (k-8*(j+1)))+BitVec.ofNat 64 b
        simp only [b,BitVec.ofNat_toNat,BitVec.setWidth_eq]
        rw [BitVec.add_comm (out+BitVec.ofNat 64 (k-8*(j+1))) _,BitVec.sub_add_cancel]
      apply hx (8*(j+1)-1-b) (by omega)
      rw [he]
      congr 2; omega

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
  refine wp_upto (a := 0) (N := w) (by omega)
    (fun j t => SInv s out k (if c then wv s.mem B ed w else 0) (8*j) t) ?_ ?_ ?_
  · intro j _ hj t h
    exact store_step hs hbx hcx h15 hk hk' hed hout hsep hj h
  · intro t h
    refine ⟨?_,?_,h.wr,h.rd,h.keep⟩
    · apply List.ext_getElem (by simp [Spec.Rsa.i2osp])
      intro i hi _
      have hik : i<k := by simpa using hi
      simp only [List.getElem_map,List.getElem_range,Spec.Rsa.i2osp]
      have hb := h.bytes (k-1-i) (by omega)
      rwa [show k-1-(k-1-i)=i by omega] at hb
    · intro x hx
      exact h.frame x (fun i hi => hx _ (by omega))
  · exact ⟨ka.2.2,ka.2.1,ka.mono (by decide),hdx,by simpa using h14,
      (fun hbad => by omega),(fun i hi => by omega),fun x _ => by rw [hm]⟩

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
      simp only [sub_beq_zero,and7_eq k (by omega)]) rfl) fun a ⟨⟨hz,hm⟩,ka⟩ => ?_)
  have hr : InRegions a.wr out k := by rw [ka.2.2]; exact hout
  refine WP.ite (decide (k%8=0)) (by simp [eval,hz]) ?_ ?_
  · intro h8
    have h8 := of_decide_eq_true h8
    refine WP.mono (storeWords_ok (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hbx)
      ((ka.gpr (by decide)).trans hsi) ((ka.gpr (by decide)).trans hcx)
      ((ka.gpr (by decide)).trans h15) (by omega) (by omega) hk' hed hr hsep)
      fun t ⟨hv,ho,hw',hr',kt⟩ => ⟨by simpa only [hm] using hv,
        fun x hx => (ho x hx).trans (congrFun hm x),hw'.trans ka.2.2,hr'.trans ka.2.1,
        (ka.trans kt).mono (by decide)⟩
  · intro _
    refine WP.mono (storeBE_ok (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hbx)
      ((ka.gpr (by decide)).trans hsi) ((ka.gpr (by decide)).trans hcx)
      ((ka.gpr (by decide)).trans h15) hk1 hk' hw hed
      (fun i hi => VG.CallLay.inRegions_sub hr (by omega) (by omega)) hsep)
      fun t ⟨hv,ho,hw',hr',kt⟩ => ⟨by simpa only [hm] using hv,
        fun x hx => (ho x hx).trans (congrFun hm x),hw'.trans ka.2.2,hr'.trans ka.2.1,
        (ka.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.WordIO
