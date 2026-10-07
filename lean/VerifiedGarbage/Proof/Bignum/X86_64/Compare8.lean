import VerifiedGarbage.Impl.Rsa.X86_64.Compare8
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Cmp

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
  omega

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
      h.scr.ld (show eX+8*(j+i)+8≤Z by omega),h.scr.ld (show eN+8*(j+i)+8≤Z by omega),hcf]
    exact ⟨_,sbb_toNat _ _ _⟩
  · rw [h.mem] at he
    refine ⟨h.scr.congr ku.2.2,(h.keep.trans ku).mono (by decide),hm.trans h.mem,
      (ku.gpr (by decide)).trans h.index,c',d+2^(64*(j+i))*r.toNat,hcf',?_,?_⟩
    · have hb := Nat.mul_le_mul_left (2^(64*(j+i))) (show r.toNat+1≤2^64 from r.isLt)
      rw [show j+(i+1)=(j+i)+1 by omega,pow64_succ]
      rw [Nat.mul_add,Nat.mul_one] at hb
      omega
    · rw [show j+(i+1)=(j+i)+1 by omega]
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
    refine WP.mono (one_ok hbx h10 hX hN (by omega) h) fun u hu => ?_
    simpa only [Nat.add_assoc,Nat.add_comm 1 n] using ih (i+1) u (by omega) hu

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
  refine WP.mono (words_ok hbx h10 hX hN 8 0 a (by omega) hc) fun b hb => ?_
  obtain ⟨c',d',hcf',hd',hv'⟩ := hb.val
  have hadd : BitVec.ofNat 64 j+8=BitVec.ofNat 64 (j+8) := by rw [BitVec.ofNat_add]; rfl
  refine WP.mono (WP.keep [.rbp,.r14] (Q := fun u => u.mem=b.mem ∧
    u.gpr .rbp=mask c' ∧ u.gpr .r14=BitVec.ofNat 64 (j+8) ∧ u.zf=some (decide (j+8=w))) ?_ rfl)
    fun u ⟨⟨hu,hbp',h14,hz⟩,ku⟩ =>
      ⟨hz,hb.scr.congr ku.2.2,(hb.keep.trans ku).mono (by decide),hu.trans hb.mem,h14,c',d',hbp',hd',hv'⟩
  xrun [cfToRbp,hcf',hb.index,(hb.keep.gpr (by decide)).trans h12,hadd,
    ofNat_sub_beq (show j+8<2^64 by omega) (show w<2^64 by omega),mask]
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
  refine wp_upto (a := 0) (N := w/8) (by omega) (fun j t => CmpInv s B Z eX eN (8*j) t) ?_ ?_ ?_
  · intro j _ hj t h
    refine WP.mono (block8_ok hbx h10 h12 hw' hX hN (by omega) h) fun u ⟨hz,hu⟩ => ?_
    have hn : 8*j+8=8*(j+1) := by omega
    rw [hn] at hu
    refine ⟨?_,hu⟩
    rw [hz]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · intro t h
    have hn : 8*(w/8)=w := by omega
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
      simp only [sub_beq_zero,VG.Proof.Bignum.X86_64.and7_eq w (by omega)]) rfl)
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
