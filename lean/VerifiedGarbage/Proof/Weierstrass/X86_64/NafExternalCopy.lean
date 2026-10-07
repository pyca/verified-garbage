import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCopy
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelect

/-! Public copies from a read-only table outside the scratch allocation. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont

theorem nafExternalPiece_ok {s : State} {base X : Addr} {size o : Nat} {src dst : MemOp}
    (hs : Scr s base size) (ho : o+16≤size)
    (ea : s.ea src=X) (eo : s.ea dst=off base o)
    (hr : InRegions (s.rd++s.wr) X 16) (r : XReg) :
    WP isa (.block [.movdquLoad r src,.movdquStore dst r]) s fun t =>
      t.mem.readW (off base o) 128=s.mem.readW X 128 ∧
      Outside base o 16 s.mem t.mem ∧ t.gpr=s.gpr ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  have hw : InRegions s.wr (off base o) 16 := ⟨_,hs.wr,hs.contains ho (by decide)⟩
  have ed : (s.setXmm r (s.mem.readW X 128)).ea dst=s.ea dst := rfl
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.load128,State.store128,
    ea,hr,ite_true,Option.map_some,RegUpd.wr_setXmm,ed,eo,hw,
    RegUpd.xmm_setXmm_self,RegUpd.mem_setXmm,Option.some.injEq,exists_eq_left']
  exact ⟨Mem.readW_writeW_self (n:=16) _ _ _ (by decide),
    writeW128_out s.mem base (s.mem.readW X 128) (by have:=hs.nowrap; omega),rfl,rfl,trivial⟩

theorem nafExternalPieces_ok {base X : Addr} {size o : Nat} {src dst : Nat → MemOp} :
    ∀ n (s : State), Scr s base size → o+16*n≤size →
      (∀ i<n,s.ea (src i)=off X (16*i)) →
      (∀ i<n,s.ea (dst i)=off base (o+16*i)) →
      (∀ i<n,InRegions (s.rd++s.wr) (off X (16*i)) 16) →
      (∀ i<n,∀ b<16,size≤ofs base (off X (16*i)+BitVec.ofNat 64 b)) →
    WP isa (.block (Naf.copyPieces n src dst)) s fun t =>
      (∀ i<n,t.mem.readW (off base (o+16*i)) 128=s.mem.readW (off X (16*i)) 128) ∧
      Outside base o (16*n) s.mem t.mem ∧ t.gpr=s.gpr ∧ t.rd=s.rd ∧ t.wr=s.wr
  | 0,s,_,_,_,_,_,_ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _),
      Outside.refl _ _ _ _,rfl,rfl,rfl⟩
  | n+1,s,hs,ho,ea,eo,hr,hout => by
    rw [Naf.copyPieces,List.range_succ,List.flatMap_append,List.flatMap_singleton,WP.block_append_iff]
    refine WP.mono (nafExternalPieces_ok n s hs (by omega)
      (fun i hi => ea i (by omega)) (fun i hi => eo i (by omega))
      (fun i hi => hr i (by omega)) (fun i hi => hout i (by omega))) fun u ⟨eu,ou,gu,ru,wu⟩ => ?_
    have su : Scr u base size := ⟨by rw [gu]; exact hs.rdi,wu ▸ hs.wr,hs.nowrap⟩
    have eac (m : MemOp) : u.ea m=s.ea m := by simp only [State.ea,gu]
    refine WP.mono (nafExternalPiece_ok su (X:=off X (16*n)) (src:=src n) (dst:=dst n) (o:=o+16*n) (by omega)
      (by rw [eac]; exact ea n (by omega)) (by rw [eac]; exact eo n (by omega))
      (by rw [ru,wu]; exact hr n (by omega)) (selAcc n)) fun t ⟨et,ot,gt,rt,wt⟩ => ?_
    refine ⟨fun i hi => ?_,(ou.mono (Nat.le_refl _) (by omega)).trans (ot.mono (by omega) (by omega)),
      gt.trans gu,rt.trans ru,wt.trans wu⟩
    by_cases he : i=n
    · subst i
      rw [et]
      exact Mem.readW_congr fun b hb => ou _ (Or.inr (by
        have := hout n (by omega) b (by omega); omega))
    · rw [ot.read128 (by omega) (by have:=hs.nowrap; omega),eu i (by omega)]

theorem nafExternalCopy_words {mem mem' : Mem} {base X : Addr} {n o : Nat}
    (h : ∀ c<n,mem'.readW (off base (o+16*c)) 128=mem.readW (off X (16*c)) 128) :
    ∀ i<2*n,word mem' base (o+8*i)=word mem X (8*i) := by
  intro i hi
  obtain ⟨c,q,hq,rfl⟩ : ∃ c q,q<2 ∧ i=2*c+q :=
    ⟨i/2,i%2,Nat.mod_lt _ (by decide),by omega⟩
  have e := readW_extract mem' (off base (o+16*c)) (w:=128) (k:=8*q) (n:=8) (by omega)
  rw [show 8*8=64 from rfl,off,Offset.add_add,
    show o+16*c+8*q=o+8*(2*c+q) from by omega] at e
  rw [VG.Proof.Mont.word,off,←e,h c (by omega)]
  have e2 := readW_extract mem (off X (16*c)) (w:=128) (k:=8*q) (n:=8) (by omega)
  rw [show 8*8=64 from rfl,off,Offset.add_add] at e2
  rw [e2,VG.Proof.Mont.word,off,show 16*c+8*q=8*(2*c+q) from by omega]

theorem nafExternalCopy_field {mem mem' : Mem} {base X : Addr} {n o j : Nat}
    (h : ∀ c<n,mem'.readW (off base (o+16*c)) 128=mem.readW (off X (16*c)) 128)
    (hj : 2*j+2≤n) : wordsVal mem' base (o+32*j) 4=wordsVal mem X (32*j) 4 := by
  apply wordsVal_congr₂
  intro i hi
  rw [show o+32*j+8*i=o+8*(4*j+i) from by omega,show 32*j+8*i=8*(4*j+i) from by omega]
  exact nafExternalCopy_words h _ (by omega)

/-- A field of `w` words at an 8-byte-aligned offset `d` of the copied pieces. -/
theorem nafExternalCopy_fieldAt {mem mem' : Mem} {base X : Addr} {n o d w : Nat}
    (h : ∀ c<n,mem'.readW (off base (o+16*c)) 128=mem.readW (off X (16*c)) 128)
    (hd : d%8=0) (hj : d+8*w≤16*n) : wordsVal mem' base (o+d) w=wordsVal mem X d w := by
  apply wordsVal_congr₂
  intro i hi
  rw [show o+d+8*i=o+8*(d/8+i) from by omega,show d+8*i=8*(d/8+i) from by omega]
  exact nafExternalCopy_words h _ (by omega)

end VG.Proof.Weierstrass.X86_64
