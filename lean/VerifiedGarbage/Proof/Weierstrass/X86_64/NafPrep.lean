import VerifiedGarbage.Proof.Weierstrass.X86_64.NafChoose
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bits
import VerifiedGarbage.Proof.Mont.X86_64.Chain

/-! The public scalar recoder, its byte stores and bounded 257-step loop. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.X25519.X86_64

def nafPrepClob : List Reg := [.rax,.rbx,.rcx,.rdx,.r8,.r9,.r10,.r11,.r12]

/-- What recoding a scalar of `n` words clobbers: the scalar's registers too. -/
def nafPrepClobN (n : Nat) : List Reg := [.rax,.rbx,.rcx,.rdx]++Naf.sregs n

theorem notin_sregs {n : Nat} {r : Reg} (h : r∉[Reg.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp,.rsi]) :
    r∉Naf.sregs n :=
  fun hm => h (List.mem_of_mem_take hm)

/-- Clobbering registers outside the scalar's keeps its value. -/
theorem nafValN_keep {n : Nat} {rs : List Reg} {s t : State} (hk : ∀ r,r∉rs → t.gpr r=s.gpr r)
    (hd : ∀ r∈[Reg.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp,.rsi],r∉rs) : nafValN n t=nafValN n s :=
  regsVal_congr fun r hr => hk r (hd r (List.mem_of_mem_take hr))

theorem notin_clobN {n : Nat} {r : Reg} (h₁ : r∉[Reg.rax,.rbx,.rcx,.rdx])
    (h₂ : r∉[Reg.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp,.rsi]) : r∉nafPrepClobN n := fun h => by
  rcases List.mem_append.mp h with h|h
  · exact h₁ h
  · exact notin_sregs h₂ h

theorem mem_clobN {n : Nat} {r : Reg} {pre : List Reg} (hpre : ∀ q∈pre,q∈[Reg.rax,.rbx,.rcx,.rdx])
    (h : r∈pre++Naf.sregs n) : r∈nafPrepClobN n := by
  rcases List.mem_append.mp h with h|h
  · exact List.mem_append_left _ (hpre r h)
  · exact List.mem_append_right _ h

structure NafPrepState (base : Addr) (size bits k j : Nat) (s : State) : Prop where
  scr : Scr s base size
  value : nafVal5 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12)=Naf5.residual k j
  count : s.gpr .rbx=BitVec.ofNat 64 j
  digits : ∀ i<j,s.mem (off base (bits+i))=Naf5.byte k i

theorem nafByte_word (k j : Nat) :
    (BitVec.ofInt 64 (Naf5.digit k j)).setWidth 8=Naf5.byte k j := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth,nafWord_toNat,Naf5.byte_toNat]
  have hb := Naf5.magnitude_le k j
  cases hn : Naf5.negative k j
  · simp only [Bool.false_eq_true,ite_false]; omega
  · have hp := Naf5.negative_magnitude_pos k j hn
    simp only [ite_true]; omega

theorem nafStore_ok {s : State} {base : Addr} {size bits k j : Nat}
    (hs : Scr s base size) (hb : bits+257≤size) (hj : j<257)
    (hc : s.gpr .rbx=BitVec.ofNat 64 j)
    (hd : s.gpr .rcx=BitVec.ofInt 64 (Naf5.digit k j)) :
    WP isa (.block [.store8 (tbl bits) .rcx]) s fun t =>
      t.mem=s.mem.writeW (off base (bits+j)) (Naf5.byte k j) ∧ KeepRegs [] s t := by
  have hw : InRegions s.wr (off base (bits+j)) 1 :=
    ⟨_,hs.wr,hs.contains (by omega) (by decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.store8,
    ea_tbl hs.rdi hc,hw,hd,nafByte_word,ite_true,Option.some.injEq,exists_eq_left']
  exact ⟨trivial,fun _ _ => rfl,rfl,rfl⟩

theorem nafInc_ok (s : State) {j : Nat} (hj : j<257) (hc : s.gpr .rbx=BitVec.ofNat 64 j) :
    WP isa (.block [.alu .add .rbx (.imm 1),.alu .cmp .rbx (.imm 257)]) s fun t =>
      t.gpr .rbx=BitVec.ofNat 64 (j+1) ∧ t.cf=some (decide (j+1<257)) ∧ Keeps [.rbx] s t := by
  have he : BitVec.ofNat 64 j+(1 : BitVec 32).signExtend 64=BitVec.ofNat 64 (j+1) := by
    change BitVec.ofNat 64 j+BitVec.ofNat 64 1=_
    rw [BitVec.ofNat_add]
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.cf_arithFlags,
    ite_true,hc,he,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · congr 1
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show j+1<2^64 from by omega)]
    rfl
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

theorem nafPrepStep_ok {s : State} {base : Addr} {size bits k j : Nat}
    (hI : NafPrepState base size bits k j s) (hb : bits+257≤size) (hj : j<257)
    (hv : Naf5.residual k j≤2^256) :
    WP isa (Naf.step bits) s fun t => NafPrepState base size bits k (j+1) t ∧
      t.cf=some (decide (j+1<257)) ∧ KeepRegs nafPrepClob s t ∧ Outside base bits 257 s.mem t.mem := by
  rw [Naf.step]
  refine WP.seq (WP.mono (nafAdjust_ok s k j hI.value hv) fun a ⟨da,va,ka⟩ => ?_)
  have sa := hI.scr.of_keeps ka (by decide)
  have ca : a.gpr .rbx=BitVec.ofNat 64 j := (ka.1 _ (by decide)).trans hI.count
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (nafStore_ok sa hb hj ca da) fun b ⟨mb,kb⟩ => ?_
  have sb := sa.of_keepRegs kb (by simp)
  have vb : nafVal5 (b.gpr .r8) (b.gpr .r9) (b.gpr .r10) (b.gpr .r11) (b.gpr .r12)=2*Naf5.residual k (j+1) := by
    rw [kb.gpr .r8 (by simp),kb.gpr .r9 (by simp),kb.gpr .r10 (by simp),
      kb.gpr .r11 (by simp),kb.gpr .r12 (by simp)]
    exact va
  rw [WP.block_append_iff]
  refine WP.mono (nafShift_ok b) fun c ⟨vc,kc⟩ => ?_
  have sc := sb.of_keeps kc (by decide)
  have cc : c.gpr .rbx=BitVec.ofNat 64 j := by
    rw [kc.1 _ (by decide),kb.gpr _ (by simp),ca]
  refine WP.mono (nafInc_ok c hj cc) fun t ⟨ct,cf,kt⟩ => ?_
  have st := sc.of_keeps kt (by decide)
  have mt : t.mem=s.mem.writeW (off base (bits+j)) (Naf5.byte k j) := by
    rw [kt.2.1,kc.2.1,mb,ka.2.1]
  have O := writeW8_outside s.mem base (Naf5.byte k j) (d:=bits+j) (by have:=hI.scr.nowrap; omega)
  refine ⟨⟨st,?_,ct,?_⟩,cf,?_,?_⟩
  · rw [kt.1 .r8 (by decide),kt.1 .r9 (by decide),kt.1 .r10 (by decide),
      kt.1 .r11 (by decide),kt.1 .r12 (by decide),vc,vb]
    omega
  · intro i hi
    rw [mt]
    by_cases hij : i=j
    · subst i; exact writeW8_self ..
    · rw [O _ (by rw [ofs_off0 base (d:=bits+i) (by have:=hI.scr.nowrap; omega)]; omega)]
      exact hI.digits i (by omega)
  · exact ((((VG.Proof.Mont.X86_64.Keeps.regs ka).mono (by decide)).trans (kb.mono (by simp))).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kc).mono (by decide))).trans ((VG.Proof.Mont.X86_64.Keeps.regs kt).mono (by decide))
  · rw [mt]; exact O.mono (by omega) (by omega)

theorem nafPrepInit_ok {s : State} {base : Addr} {size src bits : Nat}
    (hs : Scr s base size) (hsrc : src+32≤size) :
    WP isa (.block (Naf.init src)) s fun t =>
      NafPrepState base size bits (wordsVal s.mem base src 4) 0 t ∧
      KeepRegs nafPrepClob s t ∧ t.mem=s.mem := by
  rw [Naf.init,WP.block_append_iff]
  refine WP.mono (loads_ok [.r8,.r9,.r10,.r11] hs hsrc (by simp [Fresh])) fun a ⟨va,ka⟩ => ?_
  have sa := hs.of_keeps ka (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc32,State.setReg32,
    Option.map_some,
    Option.some.injEq,exists_eq_left']
  refine ⟨⟨?_,?_,rfl,fun i hi => by omega⟩,?_,ka.2.1⟩
  · exact ⟨sa.rdi,sa.wr,sa.nowrap⟩
  · simp only [nafVal5,RegUpd.gpr_setReg,ite_true,ite_false,reduceCtorEq]
    change _+2^256*0=wordsVal s.mem base src 4
    simp only [regsVal,List.length_cons,List.length_nil,Nat.reduceAdd] at va
    omega
  · refine ⟨fun r hr => ?_,ka.2.2.1,ka.2.2.2⟩
    have h12 : r≠.r12 := fun h => hr (h ▸ (by decide))
    have hbx : r≠.rbx := fun h => hr (h ▸ (by decide))
    simp only [RegUpd.gpr_setReg,h12,hbx,ite_false]
    exact ka.1 r (fun h => hr ((by decide : ∀ q∈[Reg.r8,.r9,.r10,.r11],q∈nafPrepClob) r h))

theorem nafPrep_ok {s : State} {base : Addr} {size src bits : Nat}
    (hs : Scr s base size) (hsrc : src+32≤size) (hb : bits+257≤size) :
    WP isa (Naf.prep bits src) s fun t =>
      NafPrepState base size bits (wordsVal s.mem base src 4) 257 t ∧
      KeepRegs nafPrepClob s t ∧ Outside base bits 257 s.mem t.mem := by
  let k := wordsVal s.mem base src 4
  have hk : k<2^256 := wordsVal_lt ..
  let I (m : Nat) (t : State) := NafPrepState base size bits k (257-m) t ∧
    KeepRegs nafPrepClob s t ∧ Outside base bits 257 s.mem t.mem
  rw [Naf.prep]
  refine WP.seq (WP.mono (nafPrepInit_ok (bits:=bits) hs hsrc) fun a ⟨ha,ka,ma⟩ => ?_)
  refine WP.loop (M:=isa) (fun m t => 1≤m ∧ m≤257 ∧ I m t) (fun m t ⟨hm,hm',hi⟩ => ?_)
    257 a ⟨by decide,by decide,ha,ka,?_⟩
  · have hj : 257-m<257 := by omega
    have hv : Naf5.residual k (257-m)≤2^256 := by
      have h := Naf5.residual_bound (Nat.le_of_lt hk) (j:=257-m) (by omega)
      have hp : 2^(256-(257-m))≤2^256 := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.le_trans h hp
    refine WP.mono (nafPrepStep_ok hi.1 hb hj hv) fun u ⟨hu,cf,ku,ou⟩ => ?_
    have ki := hi.2.1.trans ku
    have oi := hi.2.2.trans ou
    by_cases hm1 : m=1
    · subst m
      exact Or.inl ⟨cf,hu,ki,oi⟩
    · refine Or.inr ⟨?_,m-1,by omega,by omega,by omega,?_,ki,oi⟩
      · change u.cf=some true
        rw [cf]; congr 1; exact decide_eq_true (by omega)
      · rw [show 257-(m-1)=257-m+1 from by omega]
        exact hu
  · rw [ma]; exact Outside.refl _ _ _ _

end VG.Proof.Weierstrass.X86_64
