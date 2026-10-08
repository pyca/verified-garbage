import VerifiedGarbage.Impl.Weierstrass.X86.Naf
import VerifiedGarbage.Proof.Weierstrass.X86.TCombScan
import VerifiedGarbage.Proof.Framework.X86.SseDword

/-! Direct copies of public Jacobian table entries. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Weierstrass.X86
open VG.Proof.Mont.X86 VG.Proof.Mont

private theorem ea_congr {s t : State} (h : t.gpr=s.gpr) (m : MemOp) : t.ea m=s.ea m := by
  simp only [State.ea,h]

theorem nafCopyPiece_ok {s : State} {base : Addr} {size a o : Nat} {src dst : MemOp}
    (hs : Scr s base size) (ha : a+16≤size) (ho : o+16≤size)
    (ea : s.ea src=off base a) (eo : s.ea dst=off base o) (r : XReg) :
    WP isa (.block [.movdquLoad r src,.movdquStore dst r]) s fun t =>
      t.mem.readW (off base o) 128=s.mem.readW (off base a) 128 ∧
      Outside base o 16 s.mem t.mem ∧ t.gpr=s.gpr ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  have hr : InRegions (s.rd++s.wr) (off base a) 16 :=
    hs.read ha
  have hw : InRegions s.wr (off base o) 16 := hs.write ho
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
    have su : Scr u base size := hs.of_eq (congrFun gu .edi) (congrFun gu .esp) wu
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

theorem nafCopy_field {mem mem' : Mem} {base : Addr} {n a o j : Nat}
    (h : ∀ c<n,mem'.readW (off base (o+16*c)) 128=mem.readW (off base (a+16*c)) 128)
    (hj : 2*j+2≤n) : wordsVal mem' base (o+32*j) 4=wordsVal mem base (a+32*j) 4 := by
  apply words_eq_of_words
  intro i hi
  rw [show o+32*j+8*i=o+8*(4*j+i) from by omega,
    show a+32*j+8*i=a+8*(4*j+i) from by omega]
  exact nafCopy_words h _ (by omega)

theorem nafCopy_coord {mem mem' : Mem} {base : Addr} {a o j : Nat}
    (h : ∀ c<6,mem'.readW (off base (o+16*c)) 128=mem.readW (off base (a+16*c)) 128)
    (hj : j<3) : wordsVal mem' base (o+32*j) 4=wordsVal mem base (a+32*j) 4 :=
  nafCopy_field h (by omega)

end VG.Proof.Weierstrass.X86
