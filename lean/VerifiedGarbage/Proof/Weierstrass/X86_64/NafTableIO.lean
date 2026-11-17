module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Naf
public import VerifiedGarbage.Proof.Mont.X86_64.Csub
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectPass
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Mont.X86_64.Words

/-! ### `Weierstrass.X86_64.NafCopy`, which this module and modules that import it used -/

section

/-! Direct copies of public Jacobian table entries. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont

private theorem ea_congr {s t : State} (h : t.gpr=s.gpr) (m : MemOp) : t.ea m=s.ea m := by
  simp only [State.ea,h]

theorem nafCopyPiece_ok {s : State} {base : Addr} {size a o : Nat} {src dst : MemOp}
    (hs : Scr s base size) (ha : a+16≤size) (ho : o+16≤size)
    (ea : s.ea src=off base a) (eo : s.ea dst=off base o) (r : XReg) :
    WP isa (.block [.movdquLoad r src,.movdquStore dst r]) s fun t =>
      t.mem.readW (off base o) 128=s.mem.readW (off base a) 128 ∧
      Outside base o 16 s.mem t.mem ∧ t.gpr=s.gpr ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  have hr : InRegions (s.rd++s.wr) (off base a) 16 :=
    ⟨_,List.mem_append_right _ hs.wr,hs.contains ha (by decide)⟩
  have hw : InRegions s.wr (off base o) 16 := ⟨_,hs.wr,hs.contains ho (by decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.load128,State.store128,
    ea,hr,ite_true,Option.map_some,RegUpd.wr_setXmm,ea_congr (RegUpd.gpr_setXmm ..),eo,hw,
    RegUpd.xmm_setXmm_self,RegUpd.mem_setXmm,Option.some.injEq,exists_eq_left']
  exact ⟨Mem.readW_writeW_self (n:=16) _ _ _ (by decide),
    writeW128_out s.mem base (s.mem.readW (off base a) 128) (by have:=hs.nowrap; omega_using [ho, this]),rfl,rfl,trivial⟩

theorem nafCopyPieces_ok {base : Addr} {size a o : Nat} {src dst : Nat → MemOp} :
    ∀ n (s : State), Scr s base size → a+16*n≤size → o+16*n≤size →
      (o+16*n≤a ∨ a+16*n≤o) →
      (∀ i<n,s.ea (src i)=off base (a+16*i)) →
      (∀ i<n,s.ea (dst i)=off base (o+16*i)) →
    WP isa (.block (Naf.copyPieces n src dst)) s fun t =>
      (∀ i<n,t.mem.readW (off base (o+16*i)) 128=s.mem.readW (off base (a+16*i)) 128) ∧
      Outside base o (16*n) s.mem t.mem ∧ t.gpr=s.gpr ∧ t.rd=s.rd ∧ t.wr=s.wr
  | 0,s,_,_,_,_,_,_ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _),
      Outside.refl _ _ _ _,rfl,rfl,rfl⟩
  | n+1,s,hs,ha,ho,hd,ea,eo => by
    rw [Naf.copyPieces,List.range_succ,List.flatMap_append,List.flatMap_singleton,WP.block_append_iff]
    refine WP.mono (nafCopyPieces_ok n s hs (by omega_using [ha]) (by omega_using [ho]) (by omega_using [hd])
      (fun i hi => ea i (by omega_using [hi])) (fun i hi => eo i (by omega_using [hi]))) fun u ⟨eu,ou,gu,ru,wu⟩ => ?_
    have su : Scr u base size := ⟨by rw [gu]; exact hs.rdi,wu ▸ hs.wr,hs.nowrap⟩
    refine WP.mono (nafCopyPiece_ok su (a:=a+16*n) (o:=o+16*n) (by omega_using [ha]) (by omega_using [ho])
      (by rw [ea_congr gu]; exact ea n (by omega_using []))
      (by rw [ea_congr gu]; exact eo n (by omega_using [])) (selAcc n)) fun t ⟨et,ot,gt,rt,wt⟩ => ?_
    refine ⟨fun i hi => ?_,(ou.mono (Nat.le_refl _) (by omega_using [])).trans (ot.mono (by omega_using []) (by omega_using [])),
      gt.trans gu,rt.trans ru,wt.trans wu⟩
    by_cases he : i=n
    · subst i
      rw [et,ou.read128 (by omega_using [hd]) (by have:=hs.nowrap; omega_using [ha, this])]
    · rw [ot.read128 (by omega_using [he]) (by have:=hs.nowrap; omega_using [ho, hi, this]),eu i (by omega_using [hi, he])]

theorem nafCopy_words {mem mem' : Mem} {base : Addr} {n a o : Nat}
    (h : ∀ c<n,mem'.readW (off base (o+16*c)) 128=mem.readW (off base (a+16*c)) 128) :
    ∀ i<2*n,word mem' base (o+8*i)=word mem base (a+8*i) := by
  intro i hi
  obtain ⟨c,q,hq,rfl⟩ : ∃ c q,q<2 ∧ i=2*c+q :=
    ⟨i/2,i%2,Nat.mod_lt _ (by decide),by omega_using []⟩
  have e := readW_extract mem' (off base (o+16*c)) (w:=128) (k:=8*q) (n:=8) (by omega_using [hq])
  rw [show 8*8=64 from rfl,off,Offset.add_add,
    show o+16*c+8*q=o+8*(2*c+q) from by omega_using []] at e
  rw [VG.Proof.Mont.word,off,←e,h c (by omega_using [hi])]
  have e2 := readW_extract mem (off base (a+16*c)) (w:=128) (k:=8*q) (n:=8) (by omega_using [hq])
  rw [show 8*8=64 from rfl,off,Offset.add_add] at e2
  rw [e2,VG.Proof.Mont.word,off,show a+16*c+8*q=a+8*(2*c+q) from by omega_using []]

private theorem words_eq_of_words {m m' : Mem} {base : Addr} : ∀ n a o,
    (∀ i<n,word m' base (o+8*i)=word m base (a+8*i)) →
    wordsVal m' base o n=wordsVal m base a n
  | 0,_,_,_ => rfl
  | n+1,a,o,h => by
    have h0 := h 0 (by omega_using [])
    simp only [Nat.mul_zero,Nat.add_zero] at h0
    rw [wordsVal,wordsVal,h0,words_eq_of_words n (a+8) (o+8) (fun i hi => ?_)]
    have he := h (i+1) (by omega_using [hi])
    simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm 8] using he

/-- A field of `w` words at an 8-byte-aligned offset `d` of the copied pieces. -/
theorem nafCopy_fieldAt {mem mem' : Mem} {base : Addr} {n a o d w : Nat}
    (h : ∀ c<n,mem'.readW (off base (o+16*c)) 128=mem.readW (off base (a+16*c)) 128)
    (hd : d%8=0) (hj : d+8*w≤16*n) : wordsVal mem' base (o+d) w=wordsVal mem base (a+d) w := by
  apply words_eq_of_words
  intro i hi
  rw [show o+d+8*i=o+8*(d/8+i) from by omega_using [hd],show a+d+8*i=a+8*(d/8+i) from by omega_using [hd]]
  exact nafCopy_words h _ (by omega_using [hj, hi])

/-- A word of a copied 16-byte piece. -/
theorem nafCopy_word {mem mem' : Mem} {base : Addr} {a o d q : Nat}
    (h : mem'.readW (off base (o+d)) 128=mem.readW (off base (a+d)) 128) (hq : q<2) :
    word mem' base (o+d+8*q)=word mem base (a+d+8*q) := by
  have e := readW_extract mem' (off base (o+d)) (w:=128) (k:=8*q) (n:=8) (by omega_using [hq])
  rw [show 8*8=64 from rfl,off,Offset.add_add] at e
  rw [VG.Proof.Mont.word,off,←e,h]
  have e2 := readW_extract mem (off base (a+d)) (w:=128) (k:=8*q) (n:=8) (by omega_using [hq])
  rw [show 8*8=64 from rfl,off,Offset.add_add] at e2
  rw [e2,VG.Proof.Mont.word,off]

/-- Copies of 16-byte pieces at offsets `p i` (multiples of 8, which may
overlap, as the last piece of an entry of an odd number of words does) of an
`L`-byte range: every word that a piece covers is copied. -/
theorem nafCopyPiecesAt_ok {base : Addr} {size a o L : Nat} {p : Nat → Nat} {src dst : Nat → MemOp} :
    ∀ m (s : State), Scr s base size → a+L≤size → o+L≤size → (o+L≤a ∨ a+L≤o) →
      (∀ i<m,p i%8=0 ∧ p i+16≤L) →
      (∀ i<m,s.ea (src i)=off base (a+p i)) →
      (∀ i<m,s.ea (dst i)=off base (o+p i)) →
    WP isa (.block (Naf.copyPieces m src dst)) s fun t =>
      (∀ k,(∃ i<m,p i≤8*k ∧ 8*k<p i+16) → word t.mem base (o+8*k)=word s.mem base (a+8*k)) ∧
      Outside base o L s.mem t.mem ∧ t.gpr=s.gpr ∧ t.rd=s.rd ∧ t.wr=s.wr
  | 0,s,_,_,_,_,_,_,_ => WP.block_nil ⟨fun _ ⟨_,h,_⟩ => absurd h (Nat.not_lt_zero _),
      Outside.refl _ _ _ _,rfl,rfl,rfl⟩
  | m+1,s,hs,ha,ho,hd,hp,ea,eo => by
    rw [Naf.copyPieces,List.range_succ,List.flatMap_append,List.flatMap_singleton,WP.block_append_iff]
    refine WP.mono (nafCopyPiecesAt_ok m s hs ha ho hd (fun i hi => hp i (by omega_using [hi]))
      (fun i hi => ea i (by omega_using [hi])) (fun i hi => eo i (by omega_using [hi]))) fun u ⟨eu,ou,gu,ru,wu⟩ => ?_
    have su : Scr u base size := ⟨by rw [gu]; exact hs.rdi,wu ▸ hs.wr,hs.nowrap⟩
    have hpm := hp m (by omega_using [])
    refine WP.mono (nafCopyPiece_ok su (a:=a+p m) (o:=o+p m) (by omega_using [ha, hpm]) (by omega_using [ho, hpm])
      (by rw [ea_congr gu]; exact ea m (by omega_using []))
      (by rw [ea_congr gu]; exact eo m (by omega_using [])) (selAcc m)) fun t ⟨et,ot,gt,rt,wt⟩ => ?_
    refine ⟨fun k ⟨i,hi,hk⟩ => ?_,ou.trans (ot.mono (by omega_using []) (by omega_using [hpm])),
      gt.trans gu,rt.trans ru,wt.trans wu⟩
    have hw := hs.nowrap
    have hpi := hp i hi
    have hsa : word u.mem base (a+8*k)=word s.mem base (a+8*k) :=
      ou.word (by omega_using [hd, hk, hpi]) (by omega_using [ha, hk, hw, hpi])
    by_cases hc : p m≤8*k ∧ 8*k<p m+16
    · have e := nafCopy_word (q:=(8*k-p m)/8) et (by omega_using [hc])
      rw [show o+p m+8*((8*k-p m)/8)=o+8*k by omega_using [hpm, hc],
        show a+p m+8*((8*k-p m)/8)=a+8*k by omega_using [hpm, hc]] at e
      rw [e,hsa]
    · have hi' : i<m := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h|h
        · exact h
        · subst h; exact absurd hk hc
      have ho' : o+8*k+8≤o+p m ∨ o+p m+16≤o+8*k := by
        rcases Nat.lt_or_ge (8*k) (p m) with h|h
        · exact Or.inl (by omega_using [hpm, h])
        · exact Or.inr (by have := Nat.not_lt.mp (fun h' => hc ⟨h,h'⟩); omega_using [this])
      rw [ot.word ho' (by omega_using [ho, hk, hw, hpi]),eu k ⟨i,hi',hk⟩]

/-- `w` words from word `d` on, each of them covered by a copied piece. -/
theorem nafCopyAt_wordsAt {mem mem' : Mem} {base : Addr} {m a o d w : Nat} {p : Nat → Nat}
    (h : ∀ k,(∃ i<m,p i≤8*k ∧ 8*k<p i+16) → word mem' base (o+8*k)=word mem base (a+8*k))
    (hc : ∀ k,d≤k → k<d+w → ∃ i<m,p i≤8*k ∧ 8*k<p i+16) :
    wordsVal mem' base (o+8*d) w=wordsVal mem base (a+8*d) w := by
  apply words_eq_of_words
  intro i hi
  rw [show o+8*d+8*i=o+8*(d+i) from by omega_using [],show a+8*d+8*i=a+8*(d+i) from by omega_using []]
  exact h _ (hc _ (by omega_using []) (by omega_using [hi]))

/-- The pieces of a Jacobian entry of `n` words (`Naf.pieceOff`) are words
of the entry. -/
theorem pieceOff_ok {n : Nat} (hn : 0<n) (i : Nat) :
    Naf.pieceOff n i%8=0 ∧ Naf.pieceOff n i+16≤24*n := by
  unfold Naf.pieceOff
  split <;> omega_arith

/-- They cover its `3 n` words. -/
theorem pieceOff_cover {n k : Nat} (hk : k<3*n) :
    ∃ i<(3*n+1)/2,Naf.pieceOff n i≤8*k ∧ 8*k<Naf.pieceOff n i+16 := by
  by_cases h : k/2+1<(3*n+1)/2
  · exact ⟨k/2,by omega_using [h],by simp only [Naf.pieceOff,h,ite_true]; omega_using []⟩
  · refine ⟨(3*n+1)/2-1,by omega_using [hk],?_⟩
    simp only [Naf.pieceOff,show ¬((3*n+1)/2-1+1<(3*n+1)/2) by omega_using [],ite_false]
    omega_using [hk, h]

/-- Coordinate `j` of a Jacobian point of `n` words, copied in `Naf.pieceOff`'s pieces. -/
theorem nafCopyAt_coord {mem mem' : Mem} {base : Addr} {n a o j : Nat}
    (h : ∀ k,(∃ i<(3*n+1)/2,Naf.pieceOff n i≤8*k ∧ 8*k<Naf.pieceOff n i+16) →
      word mem' base (o+8*k)=word mem base (a+8*k))
    (hj : j<3) : wordsVal mem' base (o+8*n*j) n=wordsVal mem base (a+8*n*j) n := by
  apply words_eq_of_words
  intro i hi
  obtain rfl|rfl|rfl : j=0∨j=1∨j=2 := by omega_using [hj]
  · rw [show o+8*n*0+8*i=o+8*i by omega_using [],show a+8*n*0+8*i=a+8*i by omega_using []]
    exact h _ (pieceOff_cover (by omega_using [hi]))
  · rw [show o+8*n*1+8*i=o+8*(n+i) by omega_using [],show a+8*n*1+8*i=a+8*(n+i) by omega_using []]
    exact h _ (pieceOff_cover (by omega_using [hi]))
  · rw [show o+8*n*2+8*i=o+8*(2*n+i) by omega_using [],show a+8*n*2+8*i=a+8*(2*n+i) by omega_using []]
    exact h _ (pieceOff_cover (by omega_using [hi]))

end VG.Proof.Weierstrass.X86_64

end

end

/-! ### `Weierstrass.X86_64.NafAddress`, which this module and modules that import it used -/

section

/-! Bounds and addresses of the eight public odd-multiple table entries. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.X25519.X86_64

theorem stridedAddress_ok (s : State) {base : Addr} {d tbl j : Nat}
    (hb : s.gpr .rdi=base) (hj : s.gpr .rax=BitVec.ofNat 64 j) (ht : tbl<2^31) (hn : d<2^32) :
    WP isa (.block (Naf.stridedAddress d tbl)) s fun t =>
      t.gpr .rdx=off base (tbl+d*j) ∧ Keeps [.rax,.rcx,.rdx] s t := by
  apply WP.of_runBlock
  simp only [Naf.stridedAddress,runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,readSrc32,
    execAlu,execMul,State.setReg32,imm32_sext ht,hj,hb,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags,Option.map_some,Option.bind_some,ite_true,ite_false,reduceCtorEq,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · have hm : BitVec.ofNat 64 ((BitVec.ofNat 64 j).toNat*((BitVec.ofNat 32 d).setWidth 64).toNat)=
        BitVec.ofNat 64 (d*j) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat,BitVec.toNat_setWidth,Nat.mod_eq_of_lt hn]
      rw [Nat.mod_mul_mod,Nat.mul_comm j,Nat.mod_eq_of_lt (show d<2^64 by omega_using [hn])]
    change base+BitVec.ofNat 64 tbl+BitVec.ofNat 64 ((BitVec.ofNat 64 j).toNat*
      ((BitVec.ofNat 32 d).setWidth 64).toNat)=_
    rw [hm,Offset.add_add]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.gpr_setFlags,
      hr.1,hr.2.1,hr.2.2,ite_false]

theorem nafAddress_ok (s : State) {base : Addr} {n tbl j : Nat}
    (hb : s.gpr .rdi=base) (hj : s.gpr .rax=BitVec.ofNat 64 j) (ht : tbl<2^31) (hn : 24*n<2^32) :
    WP isa (.block (Naf.tableAddress n tbl)) s fun t =>
      t.gpr .rdx=off base (tbl+24*n*j) ∧ Keeps [.rax,.rcx,.rdx] s t :=
  stridedAddress_ok s hb hj ht hn

theorem nafIndex_ok (s : State) {a : Nat} (ha : 1≤a) (ha' : a≤15)
    (hr : s.gpr .r8=BitVec.ofNat 64 a) :
    WP isa (.block [.mov .rax (.reg .r8),.alu .sub .rax (.imm 1),.shift .shr .rax 1]) s fun t =>
      t.gpr .rax=BitVec.ofNat 64 ((a-1)/2) ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,execAlu,execShift,
    Option.map_some,Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags,hr,ite_true,and_self,
    show 1≤1 ∧ 1≤63 from by decide,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r h => ?_,rfl,rfl,rfl⟩
  · rw [show (1 : BitVec 32).signExtend 64=BitVec.ofNat 64 1 from by decide,
      BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) ha]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
    omega_using [ha']
  · simp only [List.mem_singleton] at h
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.gpr_setFlags,h,ite_false]

end VG.Proof.Weierstrass.X86_64

end

end

/-! Reading and writing public Jacobian table entries, with exact memory frames. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.X25519.X86_64

theorem nafPublicEntry_ok {K : WinCfg} {s : State} {base : Addr} {size a : Nat}
    (hs : Scr s base size) (ha : 1≤a) (ha' : a≤15) (h8 : s.gpr .r8=BitVec.ofNat 64 a)
    (hn : K.M.n=4 ∨ K.M.n=6 ∨ K.M.n=9)
    (ht : K.tbl<2^31) (hT : K.tbl+192*K.M.n≤size) (hE : K.E.x+24*K.M.n≤size)
    (hSep : K.E.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.E.x) :
    WP isa (.block (Naf.publicEntry K)) s fun t =>
      (∀ j<3,wordsVal t.mem base (K.E.x+8*K.M.n*j) K.M.n=
        wordsVal s.mem base (K.tbl+24*K.M.n*((a-1)/2)+8*K.M.n*j) K.M.n) ∧
      KeepRegs [.rax,.rcx,.rdx] s t ∧ Outside base K.E.x (24*K.M.n) s.mem t.mem := by
  have hi := Nat.mul_le_mul_left (24*K.M.n) (show (a-1)/2+1≤8 by omega_using [ha'])
  rw [Nat.mul_add,Nat.mul_one] at hi
  have hn0 : 0<K.M.n := by omega_using [hn]
  rw [Naf.publicEntry,List.append_assoc,WP.block_append_iff]
  refine WP.mono (nafIndex_ok s ha ha' h8) fun u ⟨iu,ku⟩ => ?_
  have su := hs.of_keeps ku (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (nafAddress_ok u su.rdi iu ht (by omega_using [hn])) fun v ⟨av,kv⟩ => ?_
  have sv := su.of_keeps kv (by decide)
  refine WP.mono (nafCopyPiecesAt_ok (a:=K.tbl+24*K.M.n*((a-1)/2)) (o:=K.E.x) (L:=24*K.M.n)
    ((3*K.M.n+1)/2) v sv (by omega_using [hT, hi]) (by omega_using [hE]) (by omega_using [hSep, hi]) (fun i _ => pieceOff_ok hn0 i)
    (fun i _ => by rw [ea_tblAt,av]; unfold off; rw [Offset.add_add])
    (fun i _ => by rw [ea_sc,sv.rdi])) fun t ⟨et,ot,gt,rt,wt⟩ => ?_
  refine ⟨fun j hj => ?_,⟨fun r hr => ?_,rt.trans (kv.2.2.1.trans ku.2.2.1),
    wt.trans (kv.2.2.2.trans ku.2.2.2)⟩,?_⟩
  · rw [nafCopyAt_coord et hj,kv.2.1,ku.2.1]
  · rw [gt,kv.1 r hr,ku.1 r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; exact fun he => hr (Or.inl he))]
  · rw [kv.2.1,ku.2.1] at ot
    exact ot

theorem nafTableStore_ok {K : WinCfg} {s : State} {base : Addr} {size j : Nat}
    (hs : Scr s base size) (hj : j<8) (hc : s.gpr .rbx=BitVec.ofNat 64 j)
    (hn : K.M.n=4 ∨ K.M.n=6 ∨ K.M.n=9)
    (ht : K.tbl<2^31) (hT : K.tbl+192*K.M.n≤size) (hR : K.R.x+24*K.M.n≤size)
    (hSep : K.R.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.R.x) :
    WP isa (.block (Naf.tableStore K)) s fun t =>
      (∀ i<3,wordsVal t.mem base (K.tbl+24*K.M.n*j+8*K.M.n*i) K.M.n=
        wordsVal s.mem base (K.R.x+8*K.M.n*i) K.M.n) ∧
      KeepRegs [.rax,.rcx,.rdx] s t ∧ Outside base (K.tbl+24*K.M.n*j) (24*K.M.n) s.mem t.mem := by
  have hi := Nat.mul_le_mul_left (24*K.M.n) (show j+1≤8 by omega_using [hj])
  rw [Nat.mul_add,Nat.mul_one] at hi
  have hn0 : 0<K.M.n := by omega_using [hn]
  rw [Naf.tableStore,List.append_assoc,WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov .rax (.reg .rbx)]) s (fun u =>
      u.gpr .rax=BitVec.ofNat 64 j ∧ Keeps [.rax] s u) by
    apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,Option.map_some,
      RegUpd.gpr_setReg,ite_true,hc,Option.some.injEq,exists_eq_left']
    refine ⟨trivial,fun r hr => ?_,rfl,rfl,rfl⟩
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg,hr,ite_false]) fun u ⟨iu,ku⟩ => ?_
  have su := hs.of_keeps ku (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (nafAddress_ok u su.rdi iu ht (by omega_using [hn])) fun v ⟨av,kv⟩ => ?_
  have sv := su.of_keeps kv (by decide)
  refine WP.mono (nafCopyPiecesAt_ok (a:=K.R.x) (o:=K.tbl+24*K.M.n*j) (L:=24*K.M.n)
    ((3*K.M.n+1)/2) v sv (by omega_using [hR]) (by omega_using [hT, hi]) (by omega_using [hSep, hi]) (fun i _ => pieceOff_ok hn0 i)
    (fun i _ => by rw [ea_sc,sv.rdi])
    (fun i _ => by rw [ea_tblAt,av]; unfold off; rw [Offset.add_add])) fun t ⟨et,ot,gt,rt,wt⟩ => ?_
  refine ⟨fun i hi => ?_,⟨fun r hr => ?_,rt.trans (kv.2.2.1.trans ku.2.2.1),
    wt.trans (kv.2.2.2.trans ku.2.2.2)⟩,?_⟩
  · rw [nafCopyAt_coord et hi,kv.2.1,ku.2.1]
  · rw [gt,kv.1 r hr,ku.1 r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; exact fun he => hr (Or.inl he))]
  · rw [kv.2.1,ku.2.1] at ot
    exact ot

end VG.Proof.Weierstrass.X86_64
