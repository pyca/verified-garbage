import VerifiedGarbage.Impl.Rsa.X86_64.WordIO
import VerifiedGarbage.Proof.Bignum.X86_64.WordIOBytes
import VerifiedGarbage.Proof.Framework.CallLay

namespace VG.Proof.Bignum.X86_64.WordIO
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.WordIO
open VG.Proof.Bignum VG.Proof.MlKem.X86_64

theorem ea0 (s : State) (r : Reg) : s.ea (at0 r) = s.gpr r := by simp [State.ea,at0]
theorem eab (s : State) (r i : Reg) : s.ea (atByte r i) = s.gpr r+s.gpr i := by
  simp [State.ea,atByte]

structure Inv (s : State) (B : Addr) (Z ed k : Nat) (src : Addr) (bs : List Byte)
    (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax,.rdx,.rbp,.r14] s t
  dx : t.gpr .rdx = BitVec.ofNat 64 (8*j)
  ptr : t.gpr .r14 = src + BitVec.ofNat 64 (k-8*j)
  words : ∀ q < j, word t.mem B (ed+8*q) = BitVec.ofNat 64 (Spec.Rsa.os2ip bs / 256^(8*q))
  out : Outside B ed (8*j) s.mem t.mem

theorem step {s t : State} {B src : Addr} {Z ed k w : Nat} {bs : List Byte}
    (hbx : s.gpr .rbx = off B ed) (hcx : s.gpr .rcx = BitVec.ofNat 64 k)
    (hk : k = 8*w) (hk' : k < 2^31) (hl : bs.length = k) (hed : ed+8*w ≤ Z)
    (hsrc : InRegions (s.rd ++ s.wr) src k)
    (hb : ∀ i (hi : i < k), s.mem (src+BitVec.ofNat 64 i) = bs[i]'(by omega))
    (hsep : ∀ i < k, ofs B (src+BitVec.ofNat 64 i) < ed ∨ ed+8*w ≤ ofs B (src+BitVec.ofNat 64 i))
    {j : Nat} (hj : j < w) (h : Inv s B Z ed k src bs j t) :
    WP isa (.block [.alu .sub .r14 (.imm 8), .mov .rax (.mem (at0 .r14)), .bswap .rax,
      .store (atByte .rbx .rdx) .rax, .alu .add .rdx (.imm 8), .alu .cmp .rdx (.reg .rcx)]) t
      fun u => u.zf = some (decide (j+1=w)) ∧ Inv s B Z ed k src bs (j+1) u := by
  have hn := h.scr.nowrap
  have hread : InRegions (t.rd ++ t.wr) (src+BitVec.ofNat 64 (k-8*(j+1))) 8 := by
    rw [h.keep.2.1,h.keep.2.2]
    exact VG.CallLay.inRegions_sub hsrc (by omega) (by omega)
  have hbytes : ∀ i (hi : i < bs.length), t.mem (src+BitVec.ofNat 64 i) = bs[i] := by
    intro i hi
    rw [h.out _ (by have := hsep i (by omega); omega)]
    exact hb i (by omega)
  have hdigit := read_digit (q := j) (by omega) hbytes
  rw [hl] at hdigit
  have hptr : src+BitVec.ofNat 64 (k-8*j)-8 = src+BitVec.ofNat 64 (k-8*(j+1)) := by
    rw [BitVec.sub_eq_iff_eq_add, BitVec.add_assoc,
      show (8:BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]
    congr 2; omega
  have hadd : BitVec.ofNat 64 (8*j)+8 = BitVec.ofNat 64 (8*(j+1)) := by
    rw [show (8:BitVec 64) = BitVec.ofNat 64 8 from rfl,BitVec.ofNat_add_ofNat]
    congr 1
  have haddr : (off B ed)+BitVec.ofNat 64 (8*j) = off B (ed+8*j) := by
    simp only [off,BitVec.add_assoc,BitVec.ofNat_add_ofNat]
  have hz : (BitVec.ofNat 64 (8*(j+1)) == BitVec.ofNat 64 k) = decide (j+1=w) := by
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
    u.mem = t.mem.writeW (off B (ed+8*j)) (BitVec.ofNat 64 (Spec.Rsa.os2ip bs / 256^(8*j))) ∧
    u.gpr .rdx = BitVec.ofNat 64 (8*(j+1)) ∧
    u.gpr .r14 = src+BitVec.ofNat 64 (k-8*(j+1)) ∧ u.zf = some (decide (j+1=w))) ?_ rfl)
    fun u ⟨⟨hm,hdx,h14,hzf⟩,ku⟩ => ?_
  · xrun [ea0,eab,h.ptr,hptr,hread,hdigit,h.dx,
      (h.keep.gpr (by decide)).trans hbx,(h.keep.gpr (by decide)).trans hcx,haddr,
      h.scr.st (show ed+8*j+8≤Z by omega),hadd,sub_beq_zero,hz]
  · refine ⟨hzf,h.scr.congr ku.2.2,(h.keep.trans ku).mono (by decide),hdx,h14,?_,?_⟩
    · intro q hq
      rw [hm]
      by_cases he : q=j
      · subst q; exact word_writeW_self _ _ _ _
      · rw [(writeW_outside t.mem B _ (show ed+8*j+8≤2^64 by omega)).word (by omega) (by omega)]
        exact h.words q (by omega)
    · rw [hm]
      intro x hx
      rw [writeW_outside t.mem B _ (show ed+8*j+8≤2^64 by omega) x (by omega)]
      exact h.out x (by omega)

theorem loadWords_ok {s : State} {B src : Addr} {Z ed k w : Nat} {bs : List Byte}
    (hs : Scr s B Z) (hsi : s.gpr .rsi = src) (hcx : s.gpr .rcx = BitVec.ofNat 64 k)
    (hbx : s.gpr .rbx = off B ed) (hk : k = 8*w) (hk1 : 0 < k) (hk' : k < 2^31)
    (hl : bs.length = k) (hed : ed+8*w ≤ Z) (hsrc : InRegions (s.rd ++ s.wr) src k)
    (hb : ∀ i (hi : i < k), s.mem (src+BitVec.ofNat 64 i) = bs[i]'(by omega))
    (hsep : ∀ i < k, ofs B (src+BitVec.ofNat 64 i) < ed ∨ ed+8*w ≤ ofs B (src+BitVec.ofNat 64 i)) :
    WP isa loadWords s fun t => wv t.mem B ed w = Spec.Rsa.os2ip bs ∧
      Outside B ed (8*w) s.mem t.mem ∧ Keep [.rax,.rdx,.rbp,.r14] s t := by
  unfold loadWords
  refine WP.seq (WP.mono (WP.keep [.r14,.rdx] (Q := fun t => t.gpr .r14 = src+BitVec.ofNat 64 k ∧
    t.gpr .rdx = 0 ∧ t.mem = s.mem) (by xrun [hsi,hcx]) rfl) fun a ⟨⟨h14,hdx,hm⟩,ka⟩ => ?_)
  refine wp_upto (a := 0) (N := w) (by omega) (Inv s B Z ed k src bs) ?_ ?_ ?_
  · intro j _ hj t h
    exact step hbx hcx hk hk' hl hed hsrc hb hsep hj h
  · intro t h
    refine ⟨?_,h.out,h.keep⟩
    rw [wv_digits w h.words,Nat.mod_eq_of_lt]
    have hlt := VG.Proof.Rsa.lt_of_os2ip bs
    rw [hl,hk,pow256] at hlt
    exact hlt
  · exact ⟨hs.congr ka.2.2,ka.mono (by decide),hdx,by simpa using h14,
      fun q hq => by omega,by rw [hm]; exact Outside.refl _ _ _ _⟩

theorem load_ok {s : State} {B src : Addr} {Z ed k w : Nat} {bs : List Byte}
    (hs : Scr s B Z) (hsi : s.gpr .rsi = src) (hcx : s.gpr .rcx = BitVec.ofNat 64 k)
    (hbx : s.gpr .rbx = off B ed) (hl : bs.length = k) (hk1 : 1 ≤ k) (hk' : k < 2^31)
    (hw : w = (k+7)/8) (hed : ed+8*w ≤ Z) (hsrc : InRegions (s.rd ++ s.wr) src k)
    (hb : ∀ i (hi : i < k), s.mem (src+BitVec.ofNat 64 i) = bs[i]'(by omega))
    (hsep : ∀ i < k, ofs B (src+BitVec.ofNat 64 i) < ed ∨ ed+8*w ≤ ofs B (src+BitVec.ofNat 64 i)) :
    WP isa load s fun t => wv t.mem B ed w = Spec.Rsa.os2ip bs ∧
      Outside B ed (8*w) s.mem t.mem ∧ Keep [.rax,.rdx,.rbp,.r14] s t := by
  unfold load
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun a => a.zf = some (decide (k%8=0)) ∧ a.mem=s.mem)
    (by
      xrun [lengthTest,hcx,sx7,sx0]
      simp only [sub_beq_zero,and7_eq k (by omega)]) rfl) fun a ⟨⟨hz,hm⟩,ka⟩ => ?_)
  have hr : InRegions (a.rd ++ a.wr) src k := by rw [ka.2.1,ka.2.2]; exact hsrc
  have hb' : ∀ i (hi : i<k), a.mem (src+BitVec.ofNat 64 i) = bs[i]'(by omega) :=
    fun i hi => by rw [hm]; exact hb i hi
  refine WP.ite (decide (k%8=0)) (by simp [eval,hz]) ?_ ?_
  · intro h8
    have h8 := of_decide_eq_true h8
    refine WP.mono (loadWords_ok (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hsi)
      ((ka.gpr (by decide)).trans hcx) ((ka.gpr (by decide)).trans hbx)
      (by omega) (by omega) hk' hl hed hr hb' hsep) fun t ⟨hv,ho,kt⟩ =>
      ⟨hv,by rw [← hm]; exact ho,(ka.trans kt).mono (by decide)⟩
  · intro _
    refine WP.mono (loadBE_ok (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hsi)
      ((ka.gpr (by decide)).trans hcx) ((ka.gpr (by decide)).trans hbx) hl hk1 hk' hw hed
      (fun i hi => VG.CallLay.inRegions_sub hr (by omega) (by omega)) hb' hsep)
      fun t ⟨hv,ho,kt⟩ => ⟨hv,by rw [← hm]; exact ho,(ka.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.WordIO
