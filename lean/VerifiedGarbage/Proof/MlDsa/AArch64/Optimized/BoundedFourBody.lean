import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSelectMachine

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorBody)

def bodyValues (η : Nat) (s : State) : List Zq :=
 accepted η (nibbles (s.mem (s.gpr .x2)) (s.mem (s.gpr .x2+1)))

theorem sourceValues_loaded {η : Nat} {s a : State}
    (hv : a.v .v0=loadedVector s.mem (s.gpr .x2)) : sourceValues η a=bodyValues η s := by
  unfold sourceValues bodyValues sourceNibble
  rw [hv]
  have h:=loadedVector_nibbles s.mem (s.gpr .x2)
  simp only [List.range,List.range.loop,List.map_cons,List.map_nil] at h
  rw [h]

theorem vectorBody_eq (η : Nat) : vectorBody true η=
    ([.ldr .w .x6 .x2 0,.vop (.dup .s4 .v0 .x6)] : List Instr)++
    (selectCode η++(([.strq .v1 .x3 0] : List Instr)++
    (advanceCore++([.subs .x .x8 .x4 .x16,.cselc .x .x8 .x5 .x0 .hs] : List Instr)))) := by
  simp only [vectorBody,selectCode,extractCode,acceptCode,maskCode,advanceCore,
    ite_true,List.append_assoc,List.cons_append,List.nil_append]

structure BodyPost (η : Nat) (s t : State) (p : Addr) (L : List Zq) (bytes : Nat) : Prop where
 keep : Keep bodyRegs s t
 frame : Frame [polyR p] s.mem t.mem
 vectors : ∀r,r∉bodyVecs→t.v r=s.v r
 stored : Stored t.mem p (L++bodyValues η s)
 input : t.gpr .x2=s.gpr .x2+2
 output : t.gpr .x3=coeffAddr p (L++bodyValues η s).length
 remaining : t.gpr .x4=BitVec.ofNat 64 (256-(L++bodyValues η s).length)
 remainingBytes : t.gpr .x5=BitVec.ofNat 64 (bytes-2)
 guard : t.gpr .x8=if (L++bodyValues η s).length≤252 then BitVec.ofNat 64 (bytes-2) else 0

theorem vectorBody_ok {η : Nat} (hη : η=2∨η=4) {s : State} {table p : Addr}
    {L : List Zq} {bytes : Nat} (hC : Consts η table s) (hT : TableAt s.mem table)
    (hR : ∀m<16,InRegions (s.rd++s.wr) (table+BitVec.ofNat 64 (64*m)) 16 ∧
      InRegions (s.rd++s.wr) (table+BitVec.ofNat 64 (64*m)+32) 8)
    (hi : InRegions (s.rd++s.wr) (s.gpr .x2) 4)
    (hL : L.length≤252) (hN : 2≤bytes) (hS : Stored s.mem p L)
    (h3 : s.gpr .x3=coeffAddr p L.length)
    (h4 : s.gpr .x4=BitVec.ofNat 64 (256-L.length))
    (h5 : s.gpr .x5=BitVec.ofNat 64 bytes)
    (hW : InRegions s.wr (coeffAddr p L.length) 16) :
    WP isa (.block (vectorBody true η)) s fun t=>BodyPost η s t p L bytes := by
  rw [vectorBody_eq,WP.block_append_iff]
  refine WP.mono (loadDup_ok s hi) fun a ⟨hak,ham,hav0,hav⟩=>?_
  have hCa : Consts η table a:=hC.keep hak (by decide) (fun r hr=>hav r (by
    simp only [constantVecs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide))
  rw [WP.block_append_iff]
  refine WP.mono (selectCode_ok hη hCa (by rw [ham]; exact hT)
    (fun m hm=>by rw [hak.rd,hak.wr]; exact hR m hm)) fun b ⟨hbk,hbm,hcount,hvals,hbv⟩=>?_
  have hAB : sourceValues η a=bodyValues η s:=sourceValues_loaded hav0
  rw [hAB] at hcount hvals
  have hA : (bodyValues η s).length≤4:=by rw [←hAB]; exact sourceValues_length _ _
  have hbk' : Keep [.x6,.x7,.x13] s b:=(hak.trans hbk).mono (by decide)
  have hbmem : b.mem=s.mem:=hbm.trans ham
  have hbvec (r : VReg) (hr : r∉bodyVecs) : b.v r=s.v r := by
    rw [hbv r hr,hav r (by intro he; subst r; exact hr (by decide))]
  rw [WP.block_append_iff]
  refine WP.mono (storeAccepted_ok (s := b) (p := p) (L := L) (A := bodyValues η s) (by omega) hA (by rw [hbmem]; exact hS)
    (by rw [hbk'.gpr .x3 (by decide)]; exact h3)
    (by rw [hbk'.wr]; exact hW) hvals) fun c ⟨hck,hcg,hcv,hcf,hcs⟩=>?_
  have hck' : Keep [.x6,.x7,.x13] s c:=(hbk'.trans hck).mono (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (advanceCore_ok (s := c) (c := (bodyValues η s).length) (r := 256-L.length) (n := bytes) hA (by omega) hN
    (by rw [hcg]; exact hcount)
    (by rw [hck'.gpr .x4 (by decide)]; exact h4)
    (by rw [hck'.gpr .x5 (by decide)]; exact h5))
    fun d ⟨⟨⟨hd2,hd3,hd4,hd5,hdmem⟩,hdk⟩,hdvec⟩=>?_
  have hdk' : Keep bodyRegs s d:=(hck'.trans hdk).mono (by decide)
  refine WP.mono (guard_ok
    (by rw [hdk'.gpr .x16 (by decide)]; exact hC.four)
    (by rw [hdk'.gpr .x0 (by decide)]; exact hC.zero)) fun t ⟨htk,htv,ht8⟩=>?_
  refine ⟨(hdk'.trans htk.keep).mono (by decide),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [htk.mem,hdmem,←hbmem]; exact hcf
  · intro r hr
    rw [htv,hdvec,hcv,hbvec r hr]
  · rw [htk.mem,hdmem]; exact hcs
  · rw [htk.get .x2,hd2,hck'.gpr .x2 (by decide)]
  · rw [htk.get .x3,hd3,hck'.gpr .x3 (by decide),h3,List.length_append]
    exact VG.Proof.MlDsa.Arith.coeffAddr_add p L.length (bodyValues η s).length
  · rw [htk.get .x4,hd4,List.length_append]
    congr 1; omega
  · rw [htk.get .x5,hd5]
  · rw [ht8,hd4,hd5,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),List.length_append]
    by_cases he : L.length+(bodyValues η s).length≤252
    · rw [ite_eq_left (by omega),ite_eq_left he]
    · rw [ite_eq_right (by omega),ite_eq_right he]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
