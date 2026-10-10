import VerifiedGarbage.Proof.Weierstrass.X86.NafAdjust
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.NafSubChain

/-! ## `NafPrepIO` -/

section

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

end

/-! ## `NafPrepStep` -/

section

/-! The public recoder's per-byte invariant, including its scratch residual. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Weierstrass.X86 VG.Proof.Mont.X86 VG.Proof.Mont

def nafPrepClob : List Reg := [.eax,.ebx,.ecx,.edx,.esi]

def nafPrepWrites (bits work : Nat) : List (Nat × Nat) := [(bits,257),(work,36)]

structure NafPrepState (base : Addr) (size bits work k j : Nat) (s : State) : Prop where
  scr : Scr s base size
  value : val32 s.mem base work 9=Naf5.residual k j
  count : s.gpr .esi=BitVec.ofNat 32 j
  digits : ∀ i<j,s.mem (off base (bits+i))=Naf5.byte k i

theorem nafWork_digit {m m' : Mem} {base : Addr} {bits work i : Nat}
    (h : Outside base work 36 m m') (hsep : bits+257≤work ∨ work+36≤bits)
    (hi : i<257) (hb : bits+257≤2^64) :
    m' (off base (bits+i))=m (off base (bits+i)) :=
  h _ (by rw [ofs_off0 base (by omega)]; omega)

theorem nafPrepStep_ok {s : State} {base : Addr} {size bits work k j : Nat}
    (hI : NafPrepState base size bits work k j s) (hb : bits+257≤size)
    (hw : work+36≤size) (hsep : bits+257≤work ∨ work+36≤bits) (hj : j<257)
    (hv : Naf5.residual k j≤2^256) :
    WP isa (Naf.step bits work) s fun t => NafPrepState base size bits work k (j+1) t ∧
      t.cf=some (decide (j+1<257)) ∧ Keeps nafPrepClob s t ∧
      Outs base (nafPrepWrites bits work) s.mem t.mem := by
  have hn := hI.scr.nowrap
  rw [Naf.step]
  refine WP.seq (WP.mono (nafAdjust_ok hI.scr hw hI.value hv) fun a ⟨da,va,ka,oa⟩ => ?_)
  have sa := hI.scr.of_keeps ka (by decide)
  have ca : a.gpr .esi=BitVec.ofNat 32 j := (ka.1 _ (by decide)).trans hI.count
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (nafStore_ok sa hb hj ca da) fun b ⟨mb,kb⟩ => ?_
  have sb := sa.of_keeps kb (by decide)
  have ob : Outside base (bits+j) 1 a.mem b.mem := by
    rw [mb]; exact writeW8_outside _ _ _ (by omega)
  have vb : val32 b.mem base work 9=2*Naf5.residual k (j+1) := by
    rw [ob.val32 (by omega) (by omega),va]
  rw [WP.block_append_iff]
  refine WP.mono (nafShift_ok sb hw) fun c ⟨vc,kc,oc⟩ => ?_
  have sc := sb.of_keeps kc (by decide)
  have cc : c.gpr .esi=BitVec.ofNat 32 j := by
    rw [kc.1 _ (by decide),kb.1 _ (by decide),ca]
  refine WP.mono (nafInc_ok c hj cc) fun t ⟨ct,cf,kt⟩ => ?_
  refine ⟨⟨sc.of_keeps kt.keeps (by decide),?_,ct,?_⟩,cf,?_,?_⟩
  · rw [kt.2.1,vc,vb]; omega
  · intro i hi
    rw [kt.2.1,nafWork_digit oc hsep (by omega) (by omega)]
    by_cases hij : i=j
    · subst i; rw [mb]; exact writeW8_self ..
    · rw [ob _ (by rw [ofs_off0 base (by omega)]; omega),
        nafWork_digit oa hsep (by omega) (by omega)]
      exact hI.digits i (by omega)
  · exact (((ka.mono (by decide)).trans (kb.mono (by decide))).trans
      (kc.mono (by decide))).trans (kt.keeps.mono (by decide))
  · rw [kt.2.1]
    exact ((Outs.of_outside oa (by simp [nafPrepWrites])).trans
      (Outs.of_outside (ob.mono (o' := bits) (n' := 257) (by omega) (by omega)) (by simp [nafPrepWrites]))).trans
      (Outs.of_outside oc (by simp [nafPrepWrites]))

end VG.Proof.Weierstrass.X86

end

/-! ## `NafPrep` -/

section

/-! The bounded public recoding loop produces all 257 width-five NAF digits. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Weierstrass.X86 VG.Proof.Mont.X86 VG.Proof.Mont

theorem nafPrep_ok {s : State} {base : Addr} {size src bits work : Nat}
    (hs : Scr s base size) (hsrc : src+32≤size) (hb : bits+257≤size)
    (hw : work+36≤size) (hsrcWork : work≤src ∨ src+32≤work)
    (hsep : bits+257≤work ∨ work+36≤bits) :
    WP isa (Naf.prep bits src work) s fun t =>
      NafPrepState base size bits work (val32 s.mem base src 8) 257 t ∧
      Keeps nafPrepClob s t ∧ Outs base (nafPrepWrites bits work) s.mem t.mem := by
  let k := val32 s.mem base src 8
  have hk : k<2^256 := val32_lt ..
  let I (m : Nat) (t : State) := NafPrepState base size bits work k (257-m) t ∧
    Keeps nafPrepClob s t ∧ Outs base (nafPrepWrites bits work) s.mem t.mem
  rw [Naf.prep]
  refine WP.seq (WP.mono (nafInit_ok hs hsrc hw hsrcWork) fun a ⟨va,ca,ka,oa⟩ => ?_)
  have ha : NafPrepState base size bits work k 0 a :=
    ⟨hs.of_keeps ka (by decide),va,ca,fun i hi => by omega⟩
  refine WP.loop (M:=isa) (fun m t => 1≤m ∧ m≤257 ∧ I m t) (fun m t ⟨hm,hm',hi⟩ => ?_)
    257 a ⟨by decide,by decide,ha,ka.mono (by decide),?_⟩
  · have hj : 257-m<257 := by omega
    have hv : Naf5.residual k (257-m)≤2^256 := by
      have h := Naf5.residual_bound (Nat.le_of_lt hk) (j:=257-m) (by omega)
      have hp : 2^(256-(257-m))≤2^256 := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.le_trans h hp
    refine WP.mono (nafPrepStep_ok hi.1 hb hw hsep hj hv) fun u ⟨hu,cf,ku,ou⟩ => ?_
    have ki := hi.2.1.trans ku
    have oi := hi.2.2.trans ou
    by_cases hm1 : m=1
    · subst m
      exact Or.inl ⟨cf,hu,ki,oi⟩
    · refine Or.inr ⟨?_,m-1,by omega,by omega,by omega,?_,ki,oi⟩
      · change u.cf=some true
        rw [cf]; exact congrArg some (decide_eq_true (by omega))
      · rw [show 257-(m-1)=257-m+1 from by omega]
        exact hu
  · exact Outs.of_outside oa (by simp [nafPrepWrites])

end VG.Proof.Weierstrass.X86

end
