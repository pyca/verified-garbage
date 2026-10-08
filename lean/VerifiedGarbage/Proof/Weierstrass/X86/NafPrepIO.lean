import VerifiedGarbage.Proof.Weierstrass.X86.NafAdjust
import VerifiedGarbage.Proof.Weierstrass.X86.Copy

/-! Initialization, digit-byte stores, and the public recoding loop counter. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem nafByte_word (k j : Nat) :
    (BitVec.ofInt 32 (Naf5.digit k j)).setWidth 8=Naf5.byte k j := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth,nafWord_toNat,Naf5.byte_toNat]
  have hb := Naf5.magnitude_le k j
  cases hn : Naf5.negative k j
  · simp only [Bool.false_eq_true,ite_false]; omega
  · have hp := Naf5.negative_magnitude_pos k j hn
    simp only [ite_true]; omega

theorem nafStore_ok {s : State} {base : Addr} {size bits k j : Nat}
    (hs : Scr s base size) (hb : bits+257≤size) (hj : j<257)
    (hc : s.gpr .esi=BitVec.ofNat 32 j)
    (hd : s.gpr .ecx=BitVec.ofInt 32 (Naf5.digit k j)) :
    WP isa (.block (Naf.storeDigit bits)) s fun t =>
      t.mem=s.mem.writeW (off base (bits+j)) (Naf5.byte k j) ∧ Keeps [.ebx] s t := by
  unfold Naf.storeDigit
  refine wp_movS rfl fun s₁ U₁ _ => ?_
  refine wp_addS rfl fun s₂ U₂ _ => ?_
  have K := U₁.keeps.trans U₂.keeps
  have hs₂ := hs.of_keeps K (by decide)
  have haddr : s₂.gpr .ebx=s₂.gpr .edi+BitVec.ofNat 32 j := by
    rw [U₂.gpr,U₁.gpr,U₁.other _ (by decide),hc,K.1 .edi (by decide)]
  refine wp_store8 (r := .cl) (hs₂.ea_reg haddr (d := bits) (by omega))
    (hs₂.write (n := 1) (by omega)) fun t U₃ => WP.block_nil ⟨?_,K.trans (U₃.keeps _)⟩
  rw [U₃.mem,U₂.mem,U₁.mem,Nat.add_comm j bits]
  congr 1
  change (s₂.gpr .ecx).setWidth 8=_
  rw [K.1 .ecx (by decide),hd,nafByte_word]

theorem nafInc_ok (s : State) {j : Nat} (hj : j<257) (hc : s.gpr .esi=BitVec.ofNat 32 j) :
    WP isa (.block [.alu .add .esi (.imm 1),.alu .cmp .esi (.imm 257)]) s fun t =>
      t.gpr .esi=BitVec.ofNat 32 (j+1) ∧ t.cf=some (decide (j+1<257)) ∧ CKeeps [.esi] s t := by
  have he : BitVec.ofNat 32 j+(1 : BitVec 32)=BitVec.ofNat 32 (j+1) := by
    change BitVec.ofNat 32 j+BitVec.ofNat 32 1=_
    rw [BitVec.ofNat_add]
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.cf_arithFlags,
    ite_true,hc,he,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · congr 1
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show j+1<2^32 from by omega)]
    rfl
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

theorem nafInit_ok {s : State} {base : Addr} {size src work : Nat}
    (hs : Scr s base size) (ha : src+32≤size) (hw : work+36≤size)
    (hsep : work≤src ∨ src+32≤work) :
    WP isa (.block (Naf.init src work)) s fun t =>
      val32 t.mem base work 9=val32 s.mem base src 8 ∧ t.gpr .esi=0 ∧
      Keeps [.eax,.esi] s t ∧ Outside base work 36 s.mem t.mem := by
  have hn := hs.nowrap
  rw [Naf.init,WP.block_append_iff]
  refine WP.mono (copy_ok 8 hs (by omega) ha hsep) fun a ⟨va,ka,oa⟩ => ?_
  refine wp_movS rfl fun b ub _ => ?_
  have sb := (hs.of_keeps ka (by decide)).of_keeps ub.keeps (by decide)
  refine wp_storeS (sb.ea (by omega)) (sb.write (by omega)) fun c uc => ?_
  refine wp_movS rfl fun t ut _ => WP.block_nil ?_
  have oc : Outside base (work+32) 4 a.mem c.mem := by
    rw [uc.mem,ub.mem]
    exact writeW32_outside _ _ _ (by omega)
  refine ⟨?_,ut.gpr,?_,?_⟩
  · rw [ut.mem,val32_succ,oc.val32 (by omega) (by omega),va,uc.mem,w32_write_self,ub.gpr]
    exact Nat.add_zero _
  · exact ((ka.mono (by decide)).trans (ub.keeps.mono (by decide))).trans
      ((uc.keeps [.eax,.esi]).trans (ut.keeps.mono (by decide)))
  · rw [ut.mem]
    exact (oa.mono (Nat.le_refl _) (by omega)).trans (oc.mono (by omega) (by omega))

end VG.Proof.Weierstrass.X86
