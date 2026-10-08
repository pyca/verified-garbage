import VerifiedGarbage.Proof.P256.EcdhJac.StoreWords
import VerifiedGarbage.Proof.P256.EcdhJac.Frame

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Impl.P256.EcdhJac (entryAddr storeEntry selectedWord)

theorem entryAddr_ok {base : Addr} {s : State} {m : Nat}
    (hs : s.gpr .x0=base) (hm : 1≤m) (h19 : s.gpr .x19=BitVec.ofNat 64 m) :
    WP isa (.block entryAddr) s fun t =>
      t.gpr .x16=off base (2816+160*(m-1)) ∧ Keeps [.x1,.x2,.x16] s t := by
  apply WP.of_runBlock
  simp only [entryAddr,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    show (1:Nat)<4096 by decide,show VG.Impl.P256.EcdhJac.K.tbl=2816 from rfl,
    show (2816:Nat)<4096 by decide,show 16*0<64 by decide,ite_true,
    RegUpd.gpr_write,BitVec.setWidth_eq,Size.bits,reduceCtorEq,ite_false,h19,hs,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rw [BitVec.ofNat_sub_ofNat_of_le m 1 (by decide) hm]
    change base+BitVec.ofNat 64 2816+BitVec.ofNat 64 (m-1)*BitVec.ofNat 64 160=off base (2816+160*(m-1))
    rw [←BitVec.ofNat_mul]
    simp only [off,BitVec.ofNat_add,BitVec.add_assoc,Nat.mul_comm]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]

/-- Store all five selected coordinates to the public construction index. -/
theorem storeEntry_ok {base : Addr} {s : State} {m : Nat}
    (hs : Scr s base 8192) (hm : 1≤m) (hm16 : m≤16)
    (h19 : s.gpr .x19=BitVec.ofNat 64 m) :
    WP isa (.block storeEntry) s fun t =>
      (∀i<20,word t.mem base (2816+160*(m-1)+8*i)=word s.mem base (selectedWord i)) ∧
      KeepRegs [.x1,.x2,.x16] s t ∧ Outside base (2816+160*(m-1)) 160 s.mem t.mem := by
  rw [storeEntry,WP.block_append_iff]
  refine WP.mono (entryAddr_ok hs.x0 hm h19) fun a ⟨pa,ka⟩ => ?_
  have ha := hs.of_keeps ka (by decide)
  refine WP.mono (tableStoreWords_ok (n:=20) ha pa (by omega)
    (by intro i hi; change (if i<12 then 704+8*i else 5400+8*(i-12))+8≤8192; split <;> omega)
    (by intro i hi; change (if i<12 then 704+8*i else 5400+8*(i-12))%8=0; split <;> omega)
    (by intro i hi; change 2816+160*(m-1)+8*20≤(if i<12 then 704+8*i else 5400+8*(i-12)) ∨ (if i<12 then 704+8*i else 5400+8*(i-12))+8≤2816+160*(m-1); split <;> omega) 20 (by omega)) fun t ⟨vals,kt,ot⟩ => ?_
  refine ⟨?_,(Keeps.regs ka).trans (kt.mono (by simp)),?_⟩
  · simpa only [ka.mem] using vals
  · simpa only [ka.mem] using ot


theorem storePoint_ok {base : Addr} {s : State} {m : Nat} {Q : Spec.Weierstrass.Point C}
    (hs : Scr s base 8192) (hm : 1≤m) (hm16 : m≤16)
    (h19 : s.gpr .x19=BitVec.ofNat 64 m) (hq : JPt base s selectedSlot Q) :
    WP isa (.block storeEntry) s fun t =>
      Frame base buildWork s t ∧ Outside base (2816+160*(m-1)) 160 s.mem t.mem ∧
      JPt base t (entrySlot m) Q ∧ t.gpr .x19=s.gpr .x19 := by
  refine WP.mono (storeEntry_ok hs hm hm16 h19) fun t ⟨hv,hk,ho⟩ => ⟨?_,ho,?_,hk.gpr _ (by decide)⟩
  · exact ⟨hk.mono (by decide),ho.unch.cover (by
      intro w hw; rw [List.mem_singleton.mp hw]
      exact ⟨(2816,2560),by simp [buildWork],by omega,by omega⟩)⟩
  · apply hq.congr
    intro c hc
    apply wordsVal_of_words₂
    intro i hi
    have h := hv (4*c+i) (by omega)
    have dst : 2816+160*(m-1)+8*(4*c+i)=entrySlot m c+8*i := by unfold entrySlot; omega
    have src : selectedWord (4*c+i)=selectedSlot c+8*i := by
      change (if 4*c+i<12 then 704+8*(4*c+i) else 5400+8*(4*c+i-12))=
        (if c<3 then 704+32*c else 5400+32*(c-3))+8*i
      split <;> split <;> omega
    simpa only [dst,src] using h

end VG.Proof.P256.EcdhJac
