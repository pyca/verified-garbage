module

public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Body
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Cipher
import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Constants
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The serial Camellia core meets the existing cipher and workspace contract -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.Impl.Camellia.AArch64.Serial
open VG.Proof.Modes.AArch64 (ScrIn coreRegion bufRegion)

theorem crypt_wp {s : State} {B : Addr} {k : Nat × List (BitVec 64)}
    (hB : s.gpr .x5 = B) (hs : ScrIn s B core.total) (ready : Ready s.mem B k)
    (hx1 : s.gpr .x1 = BitVec.ofNat 64 k.1) :
    WP isa core.crypt s fun t => t.gpr .x5 = B ∧
      t.gpr .x23 = s.gpr .x23 ∧ t.gpr .x24 = s.gpr .x24 ∧
      Ready t.mem B k ∧ t.gpr .x1 = BitVec.ofNat 64 k.1 ∧
      Frame [coreRegion core B] s.mem t.mem ∧
      Spec.Aes.bytesAt t.mem (B+BitVec.ofNat 64 768) 16 =
        Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (B+BitVec.ofNat 64 768) 16) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have readable : InRegions (s.rd ++ s.wr) (s.gpr .x5) 256 := by
    rw [hB]
    exact ⟨_,List.mem_append_right _ hs.wr,by
      change (⟨B,3344⟩ : Region).Contains B 256
      simp [Region.Contains]⟩
  have bytes : ∀ j < 256, s.mem (s.gpr .x5+BitVec.ofNat 64 j) = Spec.Camellia.sbox1Table.getD j 0 := by
    rw [hB]; exact ready.sbox
  change WP isa (.seq (.block (constants ++ loadBlock)) cryptBody) s _
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (constants_wp s readable bytes) fun a ⟨ac,amask,atab,ag,am,ard,awr,_⟩ => ?_
  have abase : a.gpr .x5 = B := (ag _ (by decide)).trans hB
  have ar : ∀ off ∈ [256,264,768,776], InRegions (a.rd ++ a.wr) (a.gpr .x5+BitVec.ofNat 64 off) 8 := by
    intro off hoff
    have bound : off+8 ≤ 3344 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff; omega
    rw [ard,awr,abase]
    exact ⟨_,List.mem_append_right _ hs.wr,VG.Offset.contains_base B bound (by omega)⟩
  obtain ⟨c,ce,cv,cg,cm,crd,cwr,_,cvec⟩ := loadBlock_run a ar
  refine WP.of_runBlock ⟨c,ce,?_⟩
  have cbase : c.gpr .x5 = B := (cg _ (by decide)).trans abase
  have cmem : c.mem = s.mem := cm.trans am
  have crd' : c.rd = s.rd := crd.trans ard
  have cwr' : c.wr = s.wr := cwr.trans awr
  have cctx : Context c := by
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [Constants,cvec] using ac
    · refine ⟨by rw [cvec]; exact amask.1,?_,?_⟩
      · rw [cg _ (by decide)]; exact amask.2.1
      · rw [cg _ (by decide)]; exact amask.2.2
    · simpa only [Table,cvec] using atab
    · intro j hj
      rw [crd',cwr',cbase]
      exact ⟨_,List.mem_append_right _ hs.wr,VG.Offset.contains_base B
        (by omega : 256+8*j+8 ≤ 3344) (by omega)⟩
  have cx1 : c.gpr .x1 = BitVec.ofNat 64 k.1 :=
    (cg _ (by decide)).trans ((ag _ (by decide)).trans hx1)
  have ak : keyWord a = keyWord s := by
    funext j
    simp only [keyWord,am,ag .x5 (by decide)]
  have ck : keyWord c = keyWord s := by
    funext j
    simp only [keyWord,cmem,cg .x5 (by decide),ag .x5 (by decide)]
  let m := Spec.Camellia.decodeBlock (Spec.Camellia.blockAt s.mem (B+BitVec.ofNat 64 768))
  have initial : halves c = ((m >>> 64).setWidth 64 ^^^ keyWord c 0,m.setWidth 64 ^^^ keyWord c 1) := by
    rw [cv,ck,ak,am,abase]
    have d := decoded_halves s.mem (B+BitVec.ofNat 64 768)
    rw [VG.Offset.add_add] at d
    rw [show (m >>> 64).setWidth 64 = _ from d.1,show m.setWidth 64 = _ from d.2]
  refine WP.mono (body_wp ready.rounds cx1 cctx
    (by rw [cwr',cbase]; exact ⟨_,hs.wr,VG.Offset.contains_base B (by decide : 768+8 ≤ 3344) (by decide)⟩)
    (by rw [cwr',cbase]; exact ⟨_,hs.wr,VG.Offset.contains_base B (by decide : 776+8 ≤ 3344) (by decide)⟩)
    m initial) fun t ⟨tg,tf,to,trd,twr⟩ => ?_
  have frame : Frame [bufRegion core B] s.mem t.mem := by
    change Frame [⟨B+BitVec.ofNat 64 768,16⟩] s.mem t.mem
    simpa only [cbase,cmem] using tf
  have rt : Ready t.mem B k := ready.frame frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact Or.inr (fun _ h => h))
  refine ⟨(tg _ (by decide)).trans cbase,?_,?_,rt,?_,?_,?_,trd.trans crd',twr.trans cwr'⟩
  · exact (tg _ (by decide)).trans ((cg _ (by decide)).trans (ag _ (by decide)))
  · exact (tg _ (by decide)).trans ((cg _ (by decide)).trans (ag _ (by decide)))
  · exact (tg _ (by decide)).trans cx1
  · refine frame.sub (fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨_,List.mem_cons_self,VG.Offset.sub_base B (by decide : 768+16 ≤ 3152)⟩
  · rw [cbase,ck] at to
    rw [cipher_eq_words hB ready]
    exact to

end VG.Proof.Camellia.AArch64.Serial
