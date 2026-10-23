module

import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Prepared
public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Load
public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Block
public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Rounds
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Sm4.AArch64.ModeCore
public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.State
public import VerifiedGarbage.Spec.Sm4.Ctr

/-! # Correctness of the single-block SM4 core -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.Impl.Sm4.AArch64.Serial
open VG.Proof.Modes.AArch64 (ScrIn coreRegion bufRegion)

theorem crypt_wp {s : State} {B : Addr} {k : Spec.Sm4.Schedule}
    (hB : s.gpr .x5 = B) (hs : ScrIn s B core.total) (ready : Ready s.mem B k) :
    WP isa core.crypt s fun t => t.gpr .x5 = B ∧
      t.gpr .x23 = s.gpr .x23 ∧ t.gpr .x24 = s.gpr .x24 ∧ Ready t.mem B k ∧
      Frame [coreRegion core B] s.mem t.mem ∧
      Spec.Aes.bytesAt t.mem (B+BitVec.ofNat 64 768) 16 =
        Spec.Sm4.cipher k (Spec.Aes.bytesAt s.mem (B+BitVec.ofNat 64 768) 16) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have readable : InRegions (s.rd ++ s.wr) (s.gpr .x5) 256 := by
    rw [hB]
    exact ⟨_,List.mem_append_right _ hs.wr,by
      change (⟨B,3264⟩ : Region).Contains B 256
      simp [Region.Contains]⟩
  have bytes : ∀ j < 256, s.mem (s.gpr .x5+BitVec.ofNat 64 j) = Spec.Sm4.sbox.getD j 0 := by
    rw [hB]; exact ready.sbox
  change WP isa (.block (loadSbox ++ quarterConstants ++ loadBlock ++ (List.range 32).flatMap round ++ storeBlock)) s _
  rw [WP.block_append_iff,WP.block_append_iff,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (loadSbox_ok s readable bytes) fun a ⟨atab,ae⟩ => ?_
  obtain ⟨b,be,bc,bg,bm,brd,bwr,_,bvec⟩ := quarterConstants_run a
  refine WP.of_runBlock ⟨b,be,?_⟩
  have ab : a.gpr = s.gpr := by rw [ae]
  have am : a.mem = s.mem := by rw [ae]
  have ard : a.rd = s.rd := by rw [ae]
  have awr : a.wr = s.wr := by rw [ae]
  have bbase : b.gpr .x5 = B := (bg _ (by decide)).trans (by rw [ab]; exact hB)
  have bmem : b.mem = s.mem := bm.trans am
  have btab : Table b := atab.of_rows (fun j hj => by
    have hn := VG.AArch64.Tbl.treg_ne8 j hj
    exact bvec _ hn.2.2.2.2.1 hn.2.2.2.2.2.1 hn.2.2.2.2.2.2.1)
  have br : ∀ i < 4, InRegions (b.rd ++ b.wr) (b.gpr .x5+BitVec.ofNat 64 (768+4*i)) 4 := by
    intro i hi
    rw [brd,bwr,ard,awr,bbase]
    exact ⟨_,List.mem_append_right _ hs.wr,VG.Offset.contains_base B
      (by omega : 768+4*i+4 ≤ 3264) (by omega)⟩
  obtain ⟨c,ce,cw,cg,cm,crd,cwr,_,cvec⟩ := loads_run b 4 (by decide) br
  refine WP.of_runBlock ⟨c,ce,?_⟩
  have ck : ∀ r, r ∉ written → c.gpr r = b.gpr r := by
    intro r hr
    exact cg r (fun j hj he => hr (he ▸ wordReg_mem j hj))
  have cbase : c.gpr .x5 = B := (ck _ (by decide)).trans bbase
  have cmem : c.mem = s.mem := cm.trans bmem
  have cc : Constants c := by simpa only [Constants,cvec] using bc
  have ct : Table c := by simpa only [Table,cvec] using btab
  have cr : ∀ i < 32, InRegions (c.rd ++ c.wr) (c.gpr .x5+BitVec.ofNat 64 (256+4*i)) 4 := by
    intro i hi
    rw [crd,cwr,brd,bwr,ard,awr,cbase]
    exact ⟨_,List.mem_append_right _ hs.wr,VG.Offset.contains_base B
      (by omega : 256+4*i+4 ≤ 3264) (by omega)⟩
  obtain ⟨d,de,dw,dc,dt,dg,dm,drd,dwr,_⟩ :=
    rounds_run c 32 (by decide) cc ct cr
  refine WP.of_runBlock ⟨d,de,?_⟩
  have dbase : d.gpr .x5 = B := (dg _ (by decide)).trans cbase
  have dmem : d.mem = s.mem := dm.trans cmem
  let init := VG.Proof.Sm4.ofBlock (Spec.Sm4.blockAt s.mem (B+BitVec.ofNat 64 768))
  let z := VG.Proof.Sm4.quads .enc (fun i => k.getD i 0) 8 init
  have initial : ∀ w < 4, words c w = init w := by
    intro w hw
    rw [cw w hw,bmem,bbase,← VG.Offset.add_add B 768 (4*w),readBE_word _ _ w hw]
    rfl
  have dwords : ∀ w < 4, words d w = z w := by
    intro w hw
    rw [dw w hw]
    have h := steps_congr
      (fun i => c.mem.readW (c.gpr .x5+BitVec.ofNat 64 (256+4*i)) 32)
      (fun i => k.getD i 0) 32 (words c) init
      (fun i hi => by rw [cmem,cbase]; exact ready.keys i hi) initial w hw
    rw [h]
    change steps (fun i => k.getD i 0) (4*8) init w = z w
    rw [steps_quads]
  have dr : ∀ i < 4, InRegions d.wr (d.gpr .x5+BitVec.ofNat 64 (768+4*i)) 4 := by
    intro i hi
    rw [dwr,cwr,bwr,awr,dbase]
    exact ⟨_,hs.wr,VG.Offset.contains_base B (by omega : 768+4*i+4 ≤ 3264) (by omega)⟩
  obtain ⟨e,ee,ew,eg,ef,erd,ewr,_,_⟩ := stores_run d 4 (by decide) dr
  refine WP.of_runBlock ⟨e,ee,?_⟩
  have ek : ∀ r, r ∉ written → e.gpr r = d.gpr r := by
    intro r hr
    exact eg r (fun j hj he => hr (he ▸ wordReg_mem (3-j) (by omega)))
  have output : Spec.Aes.bytesAt e.mem (B+BitVec.ofNat 64 768) 16 = (VG.Proof.Sm4.outBlock z).toList := by
    apply stored_bytes
    intro i hi
    rw [VG.Offset.add_add]
    rw [← dbase,ew i hi,dwords (3-i) (by omega)]
  have frame : Frame [bufRegion core B] s.mem e.mem := by
    change Frame [⟨B+BitVec.ofNat 64 768,16⟩] s.mem e.mem
    simpa only [dbase,dmem] using ef
  have finalReady : Ready e.mem B k := ready.frame frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact Or.inr (fun _ h => h))
  refine ⟨(ek _ (by decide)).trans dbase,?_,?_,finalReady,?_,?_,?_,?_⟩
  · rw [ek _ (by decide),dg _ (by decide),ck _ (by decide),bg _ (by decide),ab]
  · rw [ek _ (by decide),dg _ (by decide),ck _ (by decide),bg _ (by decide),ab]
  · exact frame.sub (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨_,List.mem_cons_self,VG.Offset.sub_base B (by decide : 768+16 ≤ 3168)⟩)
  · rw [output,VG.Proof.Sm4.cipher_bytes]
  · exact erd.trans (drd.trans (crd.trans (brd.trans ard)))
  · exact ewr.trans (dwr.trans (cwr.trans (bwr.trans awr)))

end VG.Proof.Sm4.AArch64.Serial
