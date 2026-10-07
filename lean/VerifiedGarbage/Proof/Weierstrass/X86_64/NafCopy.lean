import VerifiedGarbage.Impl.Weierstrass.X86_64.Naf
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectPass
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafArith

/-! Direct copies of public Jacobian table entries. -/
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
    writeW128_out s.mem base (s.mem.readW (off base a) 128) (by have:=hs.nowrap; omega),rfl,rfl,trivial⟩

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
    refine WP.mono (nafCopyPieces_ok n s hs (by omega) (by omega) (by omega)
      (fun i hi => ea i (by omega)) (fun i hi => eo i (by omega))) fun u ⟨eu,ou,gu,ru,wu⟩ => ?_
    have su : Scr u base size := ⟨by rw [gu]; exact hs.rdi,wu ▸ hs.wr,hs.nowrap⟩
    refine WP.mono (nafCopyPiece_ok su (a:=a+16*n) (o:=o+16*n) (by omega) (by omega)
      (by rw [ea_congr gu]; exact ea n (by omega))
      (by rw [ea_congr gu]; exact eo n (by omega)) (selAcc n)) fun t ⟨et,ot,gt,rt,wt⟩ => ?_
    refine ⟨fun i hi => ?_,(ou.mono (Nat.le_refl _) (by omega)).trans (ot.mono (by omega) (by omega)),
      gt.trans gu,rt.trans ru,wt.trans wu⟩
    by_cases he : i=n
    · subst i
      rw [et,ou.read128 (by omega) (by have:=hs.nowrap; omega)]
    · rw [ot.read128 (by omega) (by have:=hs.nowrap; omega),eu i (by omega)]

theorem nafCopy_words {mem mem' : Mem} {base : Addr} {n a o : Nat}
    (h : ∀ c<n,mem'.readW (off base (o+16*c)) 128=mem.readW (off base (a+16*c)) 128) :
    ∀ i<2*n,word mem' base (o+8*i)=word mem base (a+8*i) := by
  intro i hi
  obtain ⟨c,q,hq,rfl⟩ : ∃ c q,q<2 ∧ i=2*c+q :=
    ⟨i/2,i%2,Nat.mod_lt _ (by decide),by omega⟩
  have e := readW_extract mem' (off base (o+16*c)) (w:=128) (k:=8*q) (n:=8) (by omega)
  rw [show 8*8=64 from rfl,off,Offset.add_add,
    show o+16*c+8*q=o+8*(2*c+q) from by omega] at e
  rw [VG.Proof.Mont.word,off,←e,h c (by omega)]
  have e2 := readW_extract mem (off base (a+16*c)) (w:=128) (k:=8*q) (n:=8) (by omega)
  rw [show 8*8=64 from rfl,off,Offset.add_add] at e2
  rw [e2,VG.Proof.Mont.word,off,show a+16*c+8*q=a+8*(2*c+q) from by omega]

private theorem words_eq_of_words {m m' : Mem} {base : Addr} : ∀ n a o,
    (∀ i<n,word m' base (o+8*i)=word m base (a+8*i)) →
    wordsVal m' base o n=wordsVal m base a n
  | 0,_,_,_ => rfl
  | n+1,a,o,h => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero,Nat.add_zero] at h0
    rw [wordsVal,wordsVal,h0,words_eq_of_words n (a+8) (o+8) (fun i hi => ?_)]
    have he := h (i+1) (by omega)
    simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm 8] using he

/-- A field of `w` words at an 8-byte-aligned offset `d` of the copied pieces. -/
theorem nafCopy_fieldAt {mem mem' : Mem} {base : Addr} {n a o d w : Nat}
    (h : ∀ c<n,mem'.readW (off base (o+16*c)) 128=mem.readW (off base (a+16*c)) 128)
    (hd : d%8=0) (hj : d+8*w≤16*n) : wordsVal mem' base (o+d) w=wordsVal mem base (a+d) w := by
  apply words_eq_of_words
  intro i hi
  rw [show o+d+8*i=o+8*(d/8+i) from by omega,show a+d+8*i=a+8*(d/8+i) from by omega]
  exact nafCopy_words h _ (by omega)

/-- A word of a copied 16-byte piece. -/
theorem nafCopy_word {mem mem' : Mem} {base : Addr} {a o d q : Nat}
    (h : mem'.readW (off base (o+d)) 128=mem.readW (off base (a+d)) 128) (hq : q<2) :
    word mem' base (o+d+8*q)=word mem base (a+d+8*q) := by
  have e := readW_extract mem' (off base (o+d)) (w:=128) (k:=8*q) (n:=8) (by omega)
  rw [show 8*8=64 from rfl,off,Offset.add_add] at e
  rw [VG.Proof.Mont.word,off,←e,h]
  have e2 := readW_extract mem (off base (a+d)) (w:=128) (k:=8*q) (n:=8) (by omega)
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
    refine WP.mono (nafCopyPiecesAt_ok m s hs ha ho hd (fun i hi => hp i (by omega))
      (fun i hi => ea i (by omega)) (fun i hi => eo i (by omega))) fun u ⟨eu,ou,gu,ru,wu⟩ => ?_
    have su : Scr u base size := ⟨by rw [gu]; exact hs.rdi,wu ▸ hs.wr,hs.nowrap⟩
    have hpm := hp m (by omega)
    refine WP.mono (nafCopyPiece_ok su (a:=a+p m) (o:=o+p m) (by omega) (by omega)
      (by rw [ea_congr gu]; exact ea m (by omega))
      (by rw [ea_congr gu]; exact eo m (by omega)) (selAcc m)) fun t ⟨et,ot,gt,rt,wt⟩ => ?_
    refine ⟨fun k ⟨i,hi,hk⟩ => ?_,ou.trans (ot.mono (by omega) (by omega)),
      gt.trans gu,rt.trans ru,wt.trans wu⟩
    have hw := hs.nowrap
    have hpi := hp i hi
    have hsa : word u.mem base (a+8*k)=word s.mem base (a+8*k) :=
      ou.word (by omega) (by omega)
    by_cases hc : p m≤8*k ∧ 8*k<p m+16
    · have e := nafCopy_word (q:=(8*k-p m)/8) et (by omega)
      rw [show o+p m+8*((8*k-p m)/8)=o+8*k by omega,
        show a+p m+8*((8*k-p m)/8)=a+8*k by omega] at e
      rw [e,hsa]
    · have hi' : i<m := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h|h
        · exact h
        · subst h; exact absurd hk hc
      have ho' : o+8*k+8≤o+p m ∨ o+p m+16≤o+8*k := by
        rcases Nat.lt_or_ge (8*k) (p m) with h|h
        · exact Or.inl (by omega)
        · exact Or.inr (by have := Nat.not_lt.mp (fun h' => hc ⟨h,h'⟩); omega)
      rw [ot.word ho' (by omega),eu k ⟨i,hi',hk⟩]

/-- The pieces of a Jacobian entry of `n` words (`Naf.pieceOff`) are words
of the entry. -/
theorem pieceOff_ok {n : Nat} (hn : 0<n) (i : Nat) :
    Naf.pieceOff n i%8=0 ∧ Naf.pieceOff n i+16≤24*n := by
  unfold Naf.pieceOff
  split <;> omega

/-- They cover its `3 n` words. -/
theorem pieceOff_cover {n k : Nat} (hk : k<3*n) :
    ∃ i<(3*n+1)/2,Naf.pieceOff n i≤8*k ∧ 8*k<Naf.pieceOff n i+16 := by
  by_cases h : k/2+1<(3*n+1)/2
  · exact ⟨k/2,by omega,by simp only [Naf.pieceOff,h,ite_true]; omega⟩
  · refine ⟨(3*n+1)/2-1,by omega,?_⟩
    simp only [Naf.pieceOff,show ¬((3*n+1)/2-1+1<(3*n+1)/2) by omega,ite_false]
    omega

/-- Coordinate `j` of a Jacobian point of `n` words, copied in `Naf.pieceOff`'s pieces. -/
theorem nafCopyAt_coord {mem mem' : Mem} {base : Addr} {n a o j : Nat}
    (h : ∀ k,(∃ i<(3*n+1)/2,Naf.pieceOff n i≤8*k ∧ 8*k<Naf.pieceOff n i+16) →
      word mem' base (o+8*k)=word mem base (a+8*k))
    (hj : j<3) : wordsVal mem' base (o+8*n*j) n=wordsVal mem base (a+8*n*j) n := by
  apply words_eq_of_words
  intro i hi
  obtain rfl|rfl|rfl : j=0∨j=1∨j=2 := by omega
  · rw [show o+8*n*0+8*i=o+8*i by omega,show a+8*n*0+8*i=a+8*i by omega]
    exact h _ (pieceOff_cover (by omega))
  · rw [show o+8*n*1+8*i=o+8*(n+i) by omega,show a+8*n*1+8*i=a+8*(n+i) by omega]
    exact h _ (pieceOff_cover (by omega))
  · rw [show o+8*n*2+8*i=o+8*(2*n+i) by omega,show a+8*n*2+8*i=a+8*(2*n+i) by omega]
    exact h _ (pieceOff_cover (by omega))

end VG.Proof.Weierstrass.X86_64
