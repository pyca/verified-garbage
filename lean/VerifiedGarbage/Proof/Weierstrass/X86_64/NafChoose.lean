import VerifiedGarbage.Proof.Weierstrass.X86_64.NafSubtract

/-! Selecting a signed width-five digit from the public scalar's low word. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.X25519.X86_64

def nafOdd (x : BitVec 64) : BitVec 64 :=
  if (x &&& 31).toNat<16 then x &&& 31 else (x &&& 31)-32

def nafRaw (x : BitVec 64) : BitVec 64 := if x &&& 1=0 then 0 else nafOdd x

theorem nafMask (x : BitVec 64) : x &&& 31=BitVec.ofNat 64 (x.toNat%32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ofNat]
  change x.toNat &&& (2^5-1) = (x.toNat%32)%2^64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem nafParity (x : BitVec 64) : x &&& 1=0 ↔ x.toNat%2=0 := by
  rw [←BitVec.toNat_inj]
  change x.toNat &&& 1=0 ↔ x.toNat%2=0
  rw [Nat.and_one_is_mod]

theorem nafRaw_eq {x : BitVec 64} {k j : Nat}
    (hx : x.toNat%32=Naf5.residual k j%32) : nafRaw x=BitVec.ofInt 64 (Naf5.digit k j) := by
  have H : ∀ r : Fin 32,
      (if r.val%2=0 then (0 : BitVec 64) else if r.val<16 then BitVec.ofNat 64 r.val else
        BitVec.ofNat 64 r.val-32) =
      BitVec.ofInt 64 (if r.val%2=0 then 0 else if r.val<16 then (r.val:Int) else (r.val:Int)-32) := by decide
  simp only [nafRaw,nafOdd,nafParity,nafMask,BitVec.toNat_ofNat,hx,Naf5.digit_mod32]
  have hp : x.toNat%2=Naf5.residual k j%32%2 := by omega
  rw [hp,Nat.mod_eq_of_lt (show Naf5.residual k j%32<2^64 from by omega)]
  exact H ⟨Naf5.residual k j%32,Nat.mod_lt _ (by decide)⟩

theorem nafOdd_ok (s : State) :
    WP isa Naf.oddDigit s fun t => t.gpr .rcx=nafOdd (s.gpr .r8) ∧ Keeps [.rcx] s t := by
  rw [Naf.oddDigit]
  refine WP.seq ?_
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.map_some,Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    ite_true,Option.some.injEq,exists_eq_left']
  refine WP.ite (decide ((s.gpr .r8 &&& 31).toNat<16)) ?_ (fun h => ?_) (fun h => ?_)
  · rfl
  · apply WP.block_nil
    refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
    · simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,ite_true,nafOdd,
        of_decide_eq_true h,ite_true]
      rfl
    · simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]
  · apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
      Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
      ite_true,Option.some.injEq,exists_eq_left']
    refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
    · simp only [nafOdd,of_decide_eq_false h,ite_false]
      rfl
    · simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

theorem nafParity_ok (s : State) :
    WP isa (.block [.mov .rcx (.reg .r8),.alu .and .rcx (.imm 1),.alu .test .rcx (.reg .rcx)]) s
      fun t => t.gpr .rcx=s.gpr .r8 &&& 1 ∧ t.zf=some (decide (s.gpr .r8 &&& 1=0)) ∧ Keeps [.rcx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.map_some,Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    RegUpd.zf_arithFlags,BitVec.and_self,ite_true,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · rfl
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

theorem nafAdjust_ok (s : State) (k j : Nat)
    (hv : nafVal5 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12)=Naf5.residual k j)
    (hb : Naf5.residual k j≤2^256) :
    WP isa Naf.adjust s fun t => t.gpr .rcx=BitVec.ofInt 64 (Naf5.digit k j) ∧
      nafVal5 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) (t.gpr .r12)=2*Naf5.residual k (j+1) ∧
      Keeps [.rcx,.rax,.rdx,.r8,.r9,.r10,.r11,.r12] s t := by
  have hx : (s.gpr .r8).toNat%32=Naf5.residual k j%32 := by
    dsimp only [nafVal5] at hv
    omega
  have hd := nafRaw_eq hx
  rw [Naf.adjust]
  refine WP.seq (WP.mono (nafParity_ok s) fun u ⟨hu,hz,ku⟩ => ?_)
  have eu (r : Reg) (hr : r≠.rcx) : u.gpr r=s.gpr r := ku.1 r (by simpa using hr)
  refine WP.ite (decide (s.gpr .r8 &&& 1=0)) hz (fun h => ?_) (fun h => ?_)
  · have h0 := of_decide_eq_true h
    have he : Naf5.residual k j%2=0 := by
      have hp := (nafParity _).mp h0
      omega
    have hn : Naf5.residual k j=2*Naf5.residual k (j+1) := by
      simp only [Naf5.residual_succ,Naf5.next,he,ite_true]
      omega
    apply WP.block_nil
    refine ⟨?_,?_,ku.mono (by simp)⟩
    · rw [hu,h0]
      simpa only [nafRaw,h0,ite_true] using hd
    · rw [eu .r8 (by decide),eu .r9 (by decide),eu .r10 (by decide),eu .r11 (by decide),eu .r12 (by decide),hv,hn]
  · have h0 := of_decide_eq_false h
    refine WP.seq (WP.mono (nafOdd_ok u) fun v ⟨hvx,kv⟩ => ?_)
    have ev (r : Reg) (hr : r≠.rcx) : v.gpr r=s.gpr r :=
      (kv.1 r (by simpa using hr)).trans (eu r hr)
    have hvx' : v.gpr .rcx=BitVec.ofInt 64 (Naf5.digit k j) := by
      rw [hvx,eu .r8 (by decide)]
      simpa only [nafRaw,h0,ite_false] using hd
    have hvv : nafVal5 (v.gpr .r8) (v.gpr .r9) (v.gpr .r10) (v.gpr .r11) (v.gpr .r12)=Naf5.residual k j := by
      rw [ev .r8 (by decide),ev .r9 (by decide),ev .r10 (by decide),ev .r11 (by decide),ev .r12 (by decide)]
      exact hv
    refine WP.mono (subtractDigit_ok v k j hvx' hvv hb) fun t ⟨ht,kt⟩ => ⟨?_,ht,?_⟩
    · rw [kt.1 .rcx (by decide),hvx']
    · exact ((ku.trans kv).mono (by simp)).trans (kt.mono (by simp))

end VG.Proof.Weierstrass.X86_64
