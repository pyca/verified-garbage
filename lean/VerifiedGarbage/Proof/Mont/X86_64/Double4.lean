import VerifiedGarbage.Impl.Mont.X86_64.Double4
import VerifiedGarbage.Proof.Mont.X86_64.OpsReg

/-! Register-only four-limb doubling and its canonical memory result. -/
namespace VG.Proof.Mont.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Proof.Mont
open VG.Proof.X25519.X86_64

private theorem regsVal_four (s : State) :
    regsVal s [.r8,.r9,.r10,.r11]=val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) := by
  simp only [regsVal,val4]
  omega

theorem double4_sum_ok (s : State) :
    WP isa (.block Double4.sum) s fun t =>
      regsVal t [.r8,.r9,.r10,.r11]+2^256*(t.gpr .r12).toNat =
        2*regsVal s [.r8,.r9,.r10,.r11] ∧ Keeps [.r8,.r9,.r10,.r11,.r12] s t := by
  have h := chain_add (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11)
    (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11)
  apply WP.of_runBlock
  simp only [regsVal_four,val4,Double4.sum,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,
    readSrc,readSrc32,State.setReg32,Option.map_some,Option.bind_some,
    RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.cf_setReg,RegUpd.cf_arithFlags,
    ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · simpa only [regsVal_four,val4,BitVec.ofNat_eq_ofNat,
      show (0#32).signExtend 64=0#64 from rfl,
      show (0#32).setWidth 64=0#64 from rfl,BitVec.zero_add,toNat_ofBool,Nat.two_mul] using h
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
      hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2,ite_false]

theorem double4_ok {M : Mod} {s : State} {base : Addr} {size m a o : Nat}
    (hn : M.n=4) (hs : Scr s base size) (hM : ModOkW M size m s.mem base)
    (ha : a+32≤size) (ho : o+32≤size) (hx : wordsVal s.mem base a 4<m) :
    WP isa (.block (double4 M o a)) s fun t =>
      OpKeep M base o s t ∧ wordsVal t.mem base o 4=(2*wordsVal s.mem base a 4)%m := by
  rw [double4,List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (loads_ok [.r8,.r9,.r10,.r11] hs ha (by constructor <;> decide)) fun u ⟨hu,ku⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (double4_sum_ok u) fun v ⟨hv,kv⟩ => ?_
  have hs₁ := hs.of_keeps ku (by decide)
  have hs₂ := hs₁.of_keeps kv (by decide)
  change regsVal u [.r8,.r9,.r10,.r11]=wordsVal s.mem base a 4 at hu
  rw [hu] at hv
  change regsVal v [.r8,.r9,.r10,.r11]+2^256*(v.gpr .r12).toNat=2*wordsVal s.mem base a 4 at hv
  rw [WP.block_append_iff]
  refine WP.mono (csubC_ok hs₂ (M:=M) (m:=m) (ts:=[.r8,.r9,.r10,.r11]) (top:=.r12)
    (by rw [hn]; rfl) hM.n0 (by omega) (by constructor <;> decide) hM.mo
    (by rw [kv.2.1,ku.2.1]; exact hM.val) (by rw [hn]; omega)) fun w ⟨hw,kw⟩ => ?_
  have hs₃ := hs₂.of_keeps kw (by decide)
  refine WP.mono (stores_ok [.r8,.r9,.r10,.r11] hs₃ ho (by decide)) fun t ⟨ht,kt,ot⟩ => ?_
  have kk : KeepRegs [.rax,.rcx,.rdx,.rbp,.r8,.r9,.r10,.r11,.r12] s t :=
    ((Keeps.regs ku).mono (by simp)).trans
      (((Keeps.regs kv).mono (by simp)).trans
        (((Keeps.regs kw).mono (by simp)).trans (kt.mono (by simp))))
  refine ⟨⟨fun r hr => kk.gpr r (fun h => hr ?_),kk.rd,kk.wr,?_⟩,?_⟩
  · rw [hn]
    apply List.mem_append_left
    change r∈[.rax,.rcx,.rdx,.rbp,.r8,.r9,.r10,.r11,.r12,.r13]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    rcases h with h|h|h|h|h|h|h|h|h <;> simp [h]
  · intro x hx _
    rw [hn] at hx
    rw [ot x hx,kw.2.1,kv.2.1,ku.2.1]
  · change wordsVal t.mem base o 4=regsVal w [.r8,.r9,.r10,.r11] at ht
    rw [ht,hw,hn,hv]

end VG.Proof.Mont.X86_64
