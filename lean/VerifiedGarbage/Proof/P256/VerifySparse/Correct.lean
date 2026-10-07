import VerifiedGarbage.Proof.P256.VerifySparse.Arithmetic

namespace VG.Proof.P256.VerifySparse
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Proof.Ed25519

private theorem first_value (a : BitVec 64) :
    (Word64.addCarry a 1 false).toNat+(2^64-1)=
      a.toNat+2^64*(!Word64.carryOut a 1 false).toNat := by
  have h := Word64.addCarry_value a 1 false
  cases hc : Word64.carryOut a 1 false <;>
    simp only [hc,Bool.not_false,Bool.not_true,Bool.toNat_true,Bool.toNat_false,
      show (1 : BitVec 64).toNat=1 from rfl] at h ⊢ <;> omega

private theorem first_ok (s : State) (r : Reg) (hr : r≠.x2) :
    WP isa (.block [.movz .x .x2 1 0,.adds .x .x1 r .x2]) s fun t =>
      (t.gpr .x1).toNat+(2^64-1)=(s.gpr r).toNat+2^64*(!t.c).toNat ∧
      Keeps [.x1,.x2] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    show 16*0<64 by decide,ite_true,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,
    RegUpd.c_addWithCarry,BitVec.setWidth_eq,hr,ite_false,reduceCtorEq,
    Option.some.injEq,exists_eq_left']
  refine ⟨first_value _,fun q hq => ?_,rfl,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
  simp only [RegUpd.gpr_write,RegUpd.gpr_addWithCarry,hq.1,hq.2,ite_false]

private def diffs (a b c d : Reg) : List Instr :=
  [.movz .x .x2 1 0,.adds .x .x1 a .x2,
   ld .x2 (Impl.P256.VerifySparse.M.mo+8),.sbcs .x .x3 b .x2,
   .sbcs .x .x4 c .x7,ld .x2 (Impl.P256.VerifySparse.M.mo+24),.sbcs .x .x5 d .x2]

private theorem diffs_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (a b c d : Reg) (hf : Fresh [a,b,c,d])
    (hmo : Impl.P256.VerifySparse.M.mo+32≤size) (hz : s.gpr .x7=0)
    (h0 : word s.mem base Impl.P256.VerifySparse.M.mo = -1)
    (h2 : word s.mem base (Impl.P256.VerifySparse.M.mo+16)=0) :
    WP isa (.block (diffs a b c d)) s fun t =>
      regsVal t (dRegs 4)+wordsVal s.mem base Impl.P256.VerifySparse.M.mo 4=
        regsVal s [a,b,c,d]+2^256*(!t.c).toNat ∧ Keeps [.x1,.x2,.x3,.x4,.x5] s t := by
  have na := hf.2 a (by simp)
  have nb := hf.2 b (by simp)
  have nc := hf.2 c (by simp)
  have nd := hf.2 d (by simp)
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at na nb nc nd
  change WP isa (.block (([.movz .x .x2 1 0,.adds .x .x1 a .x2] : List Instr)++
    ([ld .x2 (Impl.P256.VerifySparse.M.mo+8),.sbcs .x .x3 b .x2] : List Instr)++
    ([.sbcs .x .x4 c .x7] : List Instr)++
    ([ld .x2 (Impl.P256.VerifySparse.M.mo+24),.sbcs .x .x5 d .x2] : List Instr))) s _
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (first_ok s a na.2.2.1) fun s1 ⟨e1,k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (diffR1_ok (hs.of_keeps k1 (by decide)) b .x3 nb.2.2.1 false
    (c:=s1.c) rfl (mo:=Impl.P256.VerifySparse.M.mo+8) (by omega) (by decide)) fun s2 ⟨e2,k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subc_ok s2 .x4 c .x7 false (c:=s2.c) rfl) fun s3 ⟨v3,c3,k3⟩ => ?_
  have z2 : s2.gpr .x7=0 := by rw [k2.gpr _ (by decide),k1.gpr _ (by decide),hz]
  have e3 := sub_borrow (s2.gpr c) (s2.gpr .x7) s2.c
  rw [←v3,←c3,z2] at e3
  have hs3 := ((hs.of_keeps k1 (by decide)).of_keeps k2 (by decide)).of_keeps k3 (by decide)
  refine WP.mono (diffR1_ok hs3 d .x5 nd.2.2.1 false (c:=s3.c) rfl
    (mo:=Impl.P256.VerifySparse.M.mo+24) (by omega) (by decide)) fun t ⟨e4,k4⟩ => ?_
  refine ⟨?_,(((k1.mono (by sub_regs)).trans (k2.mono (by sub_regs))).trans
    (k3.mono (by sub_regs))).trans (k4.mono (by sub_regs))⟩
  have ea : t.gpr .x1=s1.gpr .x1 := by rw [k4.gpr _ (by decide),k3.gpr _ (by decide),k2.gpr _ (by decide)]
  have eb : t.gpr .x3=s2.gpr .x3 := by rw [k4.gpr _ (by decide),k3.gpr _ (by decide)]
  have ec : t.gpr .x4=s3.gpr .x4 := k4.gpr _ (by decide)
  have rb : s1.gpr b=s.gpr b := k1.gpr b (by simp [nb.2.1,nb.2.2.1])
  have rc : s2.gpr c=s.gpr c := by rw [k2.gpr c (by simp [nc.2.2.1,nc.2.2.2.1]),k1.gpr c (by simp [nc.2.1,nc.2.2.1])]
  have rd : s3.gpr d=s.gpr d := by
    rw [k3.gpr d (by simp [nd.2.2.2.2.1]),k2.gpr d (by simp [nd.2.2.1,nd.2.2.2.1]),
      k1.gpr d (by simp [nd.2.1,nd.2.2.1])]
  rw [rb,k1.mem] at e2
  rw [rc] at e3
  change (s3.gpr .x4).toNat+0+(!s2.c).toNat=(s.gpr c).toNat+2^64*(!s3.c).toNat at e3
  rw [rd,k3.mem,k2.mem,k1.mem] at e4
  simp only [dRegs,List.take,regsVal,wordsVal,ea,eb,ec,Nat.mul_zero,Nat.add_zero]
  rw [h0,show Impl.P256.VerifySparse.M.mo+8+8=Impl.P256.VerifySparse.M.mo+16 by omega,h2,
    show Impl.P256.VerifySparse.M.mo+16+8=Impl.P256.VerifySparse.M.mo+24 by omega]
  change (s1.gpr .x1).toNat+2^64*((s2.gpr .x3).toNat+2^64*((s3.gpr .x4).toNat+2^64*(t.gpr .x5).toNat))+
    ((2^64-1)+2^64*((word s.mem base (Impl.P256.VerifySparse.M.mo+8)).toNat+
      2^64*(0+2^64*(word s.mem base (Impl.P256.VerifySparse.M.mo+24)).toNat)))=_
  omega


/-- Sparse conditional subtraction has the ordinary canonical csub contract. -/
theorem correct_ok {s : State} {base : Addr} {size m : Nat} (hs : Scr s base size)
    {ts : List Reg} {top : Reg} (hlen : ts.length=4) (hf : Fresh (top::ts))
    (hmo : Impl.P256.VerifySparse.M.mo+32≤size) (hz : s.gpr .x7=0)
    (h0 : word s.mem base Impl.P256.VerifySparse.M.mo = -1)
    (h2 : word s.mem base (Impl.P256.VerifySparse.M.mo+16)=0)
    (hm : wordsVal s.mem base Impl.P256.VerifySparse.M.mo 4=m)
    (hV : regsVal s ts+2^256*(s.gpr top).toNat<2*m) :
    WP isa (.block (Impl.P256.VerifySparse.correct ts top)) s fun t =>
      regsVal t ts=(regsVal s ts+2^256*(s.gpr top).toNat)%m ∧
      Keeps (.x2::.x17::ts++dRegs 4) s t := by
  rcases ts with _ | ⟨a,ts⟩ <;> simp only [List.length_nil,List.length_cons] at hlen
  · omega
  rcases ts with _ | ⟨b,ts⟩ <;> simp only [List.length_nil,List.length_cons] at hlen
  · omega
  rcases ts with _ | ⟨c,ts⟩ <;> simp only [List.length_nil,List.length_cons] at hlen
  · omega
  rcases ts with _ | ⟨d,ts⟩ <;> simp only [List.length_nil,List.length_cons] at hlen
  · omega
  have ht : ts=[] := by
    cases ts with
    | nil => rfl
    | cons e es => simp only [List.length_cons] at hlen; omega
  subst ts
  have ft := hf.tail
  have ne : ∀ q∈top::[a,b,c,d],q∉[Reg.x1,.x2,.x3,.x4,.x5] := by
    intro q hq hn
    have h := hf.2 q hq
    apply h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn ⊢
    grind
  have nt : top∉[Reg.x1,.x2,.x3,.x4,.x5] := ne top (by simp)
  have nn : ∀q∈[a,b,c,d],q∉[Reg.x2] := by
    intro q hq hn
    exact ne q (by simp [hq]) (by simp only [List.mem_singleton] at hn; simp [hn])
  have code : Impl.P256.VerifySparse.correct [a,b,c,d] top=
      diffs a b c d ++ ([.sbcs .x .x2 top .x7] : List Instr) ++ selectsR [a,b,c,d] (dRegs 4) := by
    simp only [Impl.P256.VerifySparse.correct,diffs,List.getElem!_cons_zero,List.getElem!_cons_succ,
      List.cons_append,List.nil_append]
  rw [code,List.append_assoc,WP.block_append_iff]
  refine WP.mono (diffs_ok hs a b c d ft hmo hz h0 h2) fun s1 ⟨e1,k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (flagR_ok s1 top (by rw [k1.gpr _ (by decide),hz])) fun s2 ⟨flag,k2⟩ => ?_
  have te : s1.gpr top=s.gpr top := k1.gpr _ nt
  rw [te] at flag
  refine WP.mono (selectsR_ok [a,b,c,d] (dRegs 4)
    (decide ((s.gpr top).toNat<(!s1.c).toNat)) rfl ft (dRegs_ok 4 (by decide)).1 flag)
    fun t ⟨et,kt,_⟩ => ?_
  have er : regsVal s2 [a,b,c,d]=regsVal s [a,b,c,d] := by
    exact (regsVal_congr (fun q hq => k2.gpr q (nn q hq))).trans
      (regsVal_congr fun q hq => k1.gpr q (ne q (List.mem_cons_of_mem _ hq)))
  have ed : regsVal s2 (dRegs 4)=regsVal s1 (dRegs 4) :=
    regsVal_congr fun q hq => k2.gpr q (by revert q; decide)
  change Keeps [.x1,.x2,.x3,.x4,.x5] s s1 at k1
  refine ⟨?_,((k1.mono (by unfold dRegs; simp only [List.take]; sub_regs)).trans (k2.mono (by sub_regs))).trans
    (kt.mono (by sub_regs))⟩
  rw [et,er,ed]
  simp only [decide_eq_true_eq]
  rw [hm] at e1
  have ml : m<2^256 := hm ▸ wordsVal_lt s.mem base Impl.P256.VerifySparse.M.mo 4
  have dl : regsVal s1 (dRegs 4)<2^256 := regsVal_lt s1 (dRegs 4)
  exact csub_arith (b:=!s1.c) ml dl hV e1

theorem modulus_words {mem : Mem} {base : Addr} {mo : Nat}
    (hm : wordsVal mem base mo 4=p) :
    word mem base mo = -1 ∧ word mem base (mo+16)=0 := by
  have h0 := (word mem base mo).isLt
  have h1 := (word mem base (mo+8)).isLt
  have h2 := (word mem base (mo+16)).isLt
  have h3 := (word mem base (mo+24)).isLt
  simp only [wordsVal,Nat.mul_zero,Nat.add_zero] at hm
  have e8 : mo+8+8=mo+16 := by omega
  have e16 : mo+8+8+8=mo+24 := by omega
  rw [e16,e8] at hm
  unfold p at hm
  constructor
  · apply BitVec.eq_of_toNat_eq
    change (word mem base mo).toNat=2^64-1
    omega
  · apply BitVec.eq_of_toNat_eq
    change (word mem base (mo+16)).toNat=0
    omega

/-- Fixed P-256 modulus wrapper with the generic csub premise order. -/
theorem correctP_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {M : Mod} (hM : M=Impl.P256.VerifySparse.M)
    {ts : List Reg} {top : Reg} (hlen : ts.length=M.n)
    (_hn : 0<M.n) (_h10 : M.n<10) (hf : Fresh (top::ts))
    (hmo : M.mo+8*M.n≤size) (_hmo8 : M.mo%8=0) (hz : s.gpr .x7=0)
    (hm : wordsVal s.mem base M.mo M.n=p)
    (hV : regsVal s ts+2^(64*M.n)*(s.gpr top).toNat<2*p) :
    WP isa (.block (Impl.P256.VerifySparse.correct ts top)) s fun t =>
      regsVal t ts=(regsVal s ts+2^(64*M.n)*(s.gpr top).toNat)%p ∧
      Keeps (.x2::.x17::ts++dRegs M.n) s t := by
  subst M
  exact correct_ok hs hlen hf hmo hz (modulus_words hm).1 (modulus_words hm).2 hm hV

end VG.Proof.P256.VerifySparse
