import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

private theorem andMask_ok (s : State) :
    WP isa (.block [.logic .and .x .x1 .x1 .x3]) s fun t =>
      t.gpr .x1=s.gpr .x1 &&& s.gpr .x3 ∧ Keeps [.x1] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write_self,
    BitVec.setWidth_eq,Option.some.injEq,exists_eq_left']
  exact ⟨trivial,fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr),rfl,rfl,rfl,rfl⟩

private theorem orWord_ok (s : State) :
    WP isa (.block [.logic .orr .x .x1 .x1 .x2]) s fun t =>
      t.gpr .x1=s.gpr .x1 ||| s.gpr .x2 ∧ Keeps [.x1] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write_self,
    BitVec.setWidth_eq,Option.some.injEq,exists_eq_left']
  exact ⟨trivial,fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr),rfl,rfl,rfl,rfl⟩

private def outOrStep (v y i : Nat) : List Instr :=
  const64 .x1 (wordOf v i) ++
    [.logic .and .x .x1 .x1 .x3,ld .x2 (y+8*i),.logic .orr .x .x1 .x1 .x2,st .x1 (y+8*i)]

private theorem outOrStep_ok {base : Addr} {size v y i : Nat} {s : State}
    (hs : Scr s base size) (hy : y+8*(i+1)≤size) (hy8 : y%8=0) :
    WP isa (.block (outOrStep v y i)) s fun t =>
      t.mem=s.mem.writeW (off base (y+8*i)) ((wordOf v i &&& s.gpr .x3) ||| word s.mem base (y+8*i)) ∧
      KeepRegs [.x1,.x2] s t := by
  rw [outOrStep,WP.block_append_iff]
  refine WP.mono (const64_ok s .x1 _) fun a ⟨a1,ka⟩ => ?_
  rw [←List.singleton_append,WP.block_append_iff]
  refine WP.mono (andMask_ok a) fun b ⟨b1,kb⟩ => ?_
  rw [←List.singleton_append,WP.block_append_iff]
  refine WP.mono (ld_ok ((hs.of_keeps ka (by decide)).of_keeps kb (by decide))
    (d:=y+8*i) (by omega) (by omega) .x2) fun c ⟨c2,kc,_⟩ => ?_
  rw [←List.singleton_append,WP.block_append_iff]
  refine WP.mono (orWord_ok c) fun d ⟨d1,kd⟩ => ?_
  refine WP.mono (st_out ((((hs.of_keeps ka (by decide)).of_keeps kb (by decide)).of_keeps kc (by decide)).of_keeps kd (by decide))
    (o:=y+8*i) (by omega) (by omega) .x1) fun t ⟨mt,kt,_⟩ => ⟨?_,?_⟩
  · rw [mt,d1,kc.gpr _ (by decide),b1,a1,ka.gpr _ (by decide),c2,kd.mem,kc.mem,kb.mem,ka.mem]
  · exact ((((Keeps.regs ka).mono (by simp)).trans ((Keeps.regs kb).mono (by simp))).trans
      ((Keeps.regs kc).mono (by simp))).trans (((Keeps.regs kd).mono (by simp)).trans (kt.mono (by simp)))

private theorem outOrSteps_ok {base : Addr} {size v y : Nat} {M : BitVec 64}
    (hy8 : y%8=0) : ∀ k,∀ (s : State),Scr s base size → s.gpr .x3=M → y+8*k≤size →
    WP isa (.block ((List.range k).flatMap (outOrStep v y))) s fun t =>
      (∀ i<k,word t.mem base (y+8*i)=(wordOf v i &&& M)|||word s.mem base (y+8*i)) ∧
      KeepRegs [.x1,.x2] s t ∧ Outside base y (8*k) s.mem t.mem
  | 0,s,_,_,_ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _),
      ⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Outside.refl _ _ _ _⟩
  | k+1,s,hs,hmask,hk => by
    have hn := hs.nowrap
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,WP.block_append_iff]
    refine WP.mono (outOrSteps_ok hy8 k s hs hmask (by omega)) fun a ⟨ea,ka,oa⟩ => ?_
    refine WP.mono (outOrStep_ok (v:=v) (i:=k) (hs.of_keepRegs ka (by decide)) hk hy8)
      fun t ⟨mt,kt⟩ => ?_
    rw [ka.gpr _ (by decide),hmask] at mt
    have ot : Outside base (y+8*k) 8 a.mem t.mem := by
      rw [mt]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun i hi => ?_,ka.trans kt,
      (oa.mono (Nat.le_refl _) (by omega)).trans (ot.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge i k with h | h
    · rw [ot.word (by omega) (by omega),ea i h]
    · obtain rfl : i=k := by omega
      rw [mt,word_writeW_self,oa.word (by omega) (by omega)]

private theorem outNotMask_ok (s : State) (h7 : s.gpr .x7=0) :
    WP isa (.block [.subImm .x .x4 .x7 1,.logic .eor .x .x3 .x3 .x4]) s fun t =>
      t.gpr .x3= ~~~s.gpr .x3 ∧ Keeps [.x3,.x4] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    BitVec.setWidth_eq,h7,show 1<4096 by decide,ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨by change s.gpr .x3 ^^^ BitVec.allOnes 64 = ~~~s.gpr .x3; exact BitVec.xor_allOnes,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

/-- Normalize the Jacobian ordinate to Montgomery one exactly at infinity. -/
theorem outFix_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hn : 0<K.M.n) (hone : K.one<2^(64*K.M.n))
    (hy : K.A.y+8*K.M.n≤size) (hz : K.A.z+8*K.M.n≤size) (hzero : K.zero+8*K.M.n≤size)
    (hy8 : K.A.y%8=0) (hz8 : K.A.z%8=0) (hzero8 : K.zero%8=0)
    (hy0 : K.A.y+8*K.M.n≤K.zero ∨ K.zero+8*K.M.n≤K.A.y)
    (h0 : wordsVal s.mem base K.zero K.M.n=0) :
    WP isa (.block K.outFix) s fun t =>
      wordsVal t.mem base K.A.y K.M.n=
        (if wordsVal s.mem base K.A.z K.M.n=0 then K.one else wordsVal s.mem base K.A.y K.M.n) ∧
      KeepRegs [.x1,.x2,.x3,.x4,.x7,.x16] s t ∧ Outside base K.A.y (8*K.M.n) s.mem t.mem := by
  rw [TCombCfg.outFix,List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (nzMask_full_ok hs hn hz hz8) fun a ⟨a3,ka,a7⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok (decide (wordsVal s.mem base K.A.z K.M.n≠0)) K.M.n
    (hs.of_keeps ka (by decide)) (by simpa only [mask,decide_eq_true_eq] using a3)
    hy hzero hy hy8 hzero8 hy8 (by omega) (Or.inl (Nat.le_refl _))) fun b ⟨eb,kb,ob⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (outNotMask_ok b (by rw [kb.gpr _ (by decide),a7])) fun c ⟨c3,kc⟩ => ?_
  change WP isa (.block ((List.range K.M.n).flatMap (outOrStep K.one K.A.y))) c _
  have hc : c.gpr .x3= ~~~mask (wordsVal s.mem base K.A.z K.M.n≠0) := by
    rw [c3,kb.gpr _ (by decide),a3]
  refine WP.mono (outOrSteps_ok hy8 K.M.n c
    (((hs.of_keeps ka (by decide)).of_keepRegs kb (by decide)).of_keeps kc (by decide)) hc hy)
    fun t ⟨et,kt,ot⟩ => ⟨?_,?_,?_⟩
  · rw [ka.mem] at eb
    by_cases hZ : wordsVal s.mem base K.A.z K.M.n=0
    · simp only [hZ,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false,ite_true] at eb ⊢
      rw [h0] at eb
      have ew := (wordsVal_eq_zero_iff _ _ _ _).mp eb
      apply wordsVal_of_shifts _ _ _ _ _ hone
      intro i hi
      rw [et i hi,kc.mem,ew i hi]
      simp [mask,hZ,wordOf]
      change _ &&& BitVec.allOnes 64=_
      exact BitVec.and_allOnes
    · simp only [hZ,ne_eq,not_false_eq_true,decide_true,ite_true,ite_false] at eb ⊢
      rw [←eb,←kc.mem]
      apply wordsVal_of_words₂
      intro i hi
      rw [et i hi]
      simp [mask,hZ]
  · exact ((Keeps.regs ka).mono (by sub_regs)).trans ((kb.mono (by sub_regs)).trans
      (((Keeps.regs kc).mono (by sub_regs)).trans (kt.mono (by sub_regs))))
  · intro x hx
    rw [ot x hx,kc.mem,ob x hx,ka.mem]

end VG.Proof.Weierstrass.AArch64
