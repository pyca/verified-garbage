import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourPrefix

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def loadedVector (m : Mem) (p : Addr) : BitVec 128 :=
 let w:=m.readW p 32
 ofVWords w w w w

theorem loadedVector_byte (m : Mem) (p : Addr) {i : Nat} (hi : i<4) :
    vbyte (loadedVector m p) i=m (p+BitVec.ofNat 64 i) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have h32 : 8*i+k<32:=by omega
  simp only [loadedVector,ofVWords,vbyte,BitVec.getLsbD_extractLsb',hk,decide_true,
    Bool.true_and,BitVec.getLsbD_append,h32,ite_true,Mem.readW,BitVec.getLsbD_setWidth]
  rw [getLsbD_read m 4 _ _ (by omega)]
  have hd : (8*i+k)/8=i:=by omega
  have hm : (8*i+k)%8=k:=by omega
  rw [hd,hm]

theorem loadedVector_nibbles (m : Mem) (p : Addr) :
    (List.range 4).map (fun e=>(nibbleWord (loadedVector m p) e).toNat)=
      nibbles (m p) (m (p+1)) := by
  have hw (e : Nat) (he:e<4) :
      (nibbleWord (loadedVector m p) e).toNat=
        if e%2=0 then (m (p+BitVec.ofNat 64 (e/2))).toNat%16
        else (m (p+BitVec.ofNat 64 (e/2))).toNat/16 := by
    rw [nibbleWord_value,loadedVector_byte _ _ (by omega),BitVec.toNat_ofNat]
    have hb:=(m (p+BitVec.ofNat 64 (e/2))).isLt
    split <;> rw [Nat.mod_eq_of_lt (by omega)]
  simp only [List.range,List.range.loop,List.map_cons,List.map_nil]
  rw [hw 0 (by decide),hw 1 (by decide),hw 2 (by decide),hw 3 (by decide)]
  simp only [nibbles,Nat.reduceMod,Nat.reduceDiv,Nat.reduceEqDiff,ite_true,ite_false,
    BitVec.ofNat_eq_ofNat,BitVec.add_zero]

theorem loadDup_ok (s : State) (hin : InRegions (s.rd++s.wr) (s.gpr .x2) 4) :
    WP isa (.block [.ldr .w .x6 .x2 0,.vop (.dup .s4 .v0 .x6)]) s fun t=>
      Keep [.x6] s t ∧ t.mem=s.mem ∧ t.v .v0=loadedVector s.mem (s.gpr .x2) ∧
      (∀r,r≠.v0→t.v r=s.v r) := by
  have hh : WP isa (.block [.ldr .w .x6 .x2 0]) s fun a=>
      (Only [.x6] s a ∧ a.gpr .x6=(s.mem.readW (s.gpr .x2) 32).setWidth 64) ∧ a.v=s.v :=
    WP.keepV (by decide) (wp_ldrw (by decide) (by simp) hin fun a ha hv=>wp_nil ⟨ha,hv⟩)
  change WP isa (.block (([.ldr .w .x6 .x2 0] : List Instr)++[.vop (.dup .s4 .v0 .x6)])) s _
  rw [WP.block_append_iff]
  refine WP.mono hh fun a ⟨⟨ha,hv⟩,hav⟩=>?_
  refine wp_vop (d := .v0) rfl fun t ht=>wp_nil ?_
  refine ⟨(ha.keep.trans ht.chg.keep).mono (by decide),ht.mem.trans ha.mem,?_,?_⟩
  · rw [ht.v,hv]
    simp only [BitVec.setWidth_setWidth_of_le _ (show 32≤64 by decide),BitVec.setWidth_eq]
    rfl
  · intro r hr
    rw [ht.other r hr,hav]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
