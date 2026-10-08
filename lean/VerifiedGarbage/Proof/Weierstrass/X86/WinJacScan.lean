import VerifiedGarbage.Impl.Weierstrass.X86.WinJac
import VerifiedGarbage.Proof.Weierstrass.X86.TCombSelect

/-! Two constant-time scans of the packed Jacobian table. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

theorem tablePtr_ok {s : State} {base : Addr} {size tbl : Nat}
    (hs : Scr s base size) (ht : tbl<size) :
    WP isa (.block (JacWinCfg.tablePtr tbl)) s fun t =>
      (t.gpr .edx).setWidth 64=off base tbl ∧ CKeeps [.edx] s t := by
  apply WP.of_runBlock
  simp only [JacWinCfg.tablePtr,runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,
    execAlu,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,Option.map_some,Option.bind_some,
    ite_true,Option.some.injEq,exists_eq_left']
  refine ⟨hs.ea ht,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hr,ite_false]

/-- Read every entry, retaining entry `a` by masks, or zero for `a = 0`. -/
theorem scanPart_ok (K : TCombCfg) {s : State} {base : Addr} {size tbl a : Nat}
    (hs : Scr s base size) (hn : 1≤K.M.n ∧ K.M.n≤6) (hH : K.H=16)
    (ha : a≤16) (hb : s.gpr .ebx=BitVec.ofNat 32 a)
    (ht : tbl+16*K.M.n*16≤size) (ho : K.E.x+16*K.M.n≤size) :
    WP isa (.block (JacWinCfg.tablePtr tbl ++ K.selPass)) s fun t =>
      (∀ c<K.M.n,t.mem.readW (off base (K.E.x+16*c)) 128=
        accVal s.mem (off base tbl) K.M.n a 16 c) ∧
      Outside base K.E.x (16*K.M.n) s.mem t.mem ∧ KeepRegs [.ecx,.edx] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (tablePtr_ok hs (by omega)) fun u ⟨pu,ku⟩ => ?_
  have hu := hs.of_keeps ku.keeps (by decide)
  have hb' : u.gpr .ebx=BitVec.ofNat 32 a := (ku.1 _ (by decide)).trans hb
  have hr : ∀ e<K.H,∀ c<K.M.n,InRegions (u.rd++u.wr)
      (off base tbl + BitVec.ofNat 64 (16*K.M.n*e+16*c)) 16 := by
    intro e he c hc
    rw [off,Offset.add_add]
    apply hu.read
    rw [hH] at he
    have hm := Nat.mul_le_mul_left (16*K.M.n) (show e+1≤16 by omega)
    rw [Nat.mul_add,Nat.mul_one] at hm
    omega
  have hnw := hs.nowrap
  have hbNat : (off base tbl).toNat=base.toNat+tbl := by
    simp only [off,BitVec.toNat_add,BitVec.toNat_ofNat]
    omega
  refine WP.mono (selPass_ok K hu hn.2 (by rw [hH]; decide) (by omega) hb' pu hr
    (by rw [hbNat,hH]; omega) ho) fun t ⟨et,ot,kt⟩ => ?_
  refine ⟨?_,?_,⟨fun r h => ?_,kt.rd.trans ku.2.2.1,kt.wr.trans ku.2.2.2⟩⟩
  · intro c hc
    rw [et c hc,ku.2.1,hH]
  · rw [ku.2.1] at ot
    exact ot
  · rw [kt.gpr r (by simp only [List.mem_cons,not_or] at h; simpa using h.1),
      ku.1 r (by simp only [List.mem_cons,not_or] at h; simpa using h.2)]

/-- Reassemble four 64-bit words of one selected field coordinate. -/
theorem scan_coord {mem mem' : Mem} {base : Addr} {tbl o n a c : Nat} (ha : a≤16)
    (hc : 4*c+4≤2*n)
    (h : ∀ i<n,mem'.readW (off base (o+16*i)) 128=accVal mem (off base tbl) n a 16 i) :
    wordsVal mem' base (o+32*c) 4=
      if 1≤a then wordsVal mem base (tbl+16*n*(a-1)+32*c) 4 else 0 := by
  have hw := accVal_word h
  by_cases h1 : 1≤a
  · rw [ite_eq_left h1]
    apply wordsVal_congr₂
    intro i hi
    have e := hw (4*c+i) (by omega)
    simp only [h1,ha,and_self,ite_true] at e
    rw [show o+8*(4*c+i)=o+32*c+8*i by omega] at e
    rw [e]
    simp only [VG.Proof.Mont.word,off,Offset.add_add]
    congr 3 <;> omega
  · rw [ite_eq_right h1]
    apply wordsVal_zeros
    intro i hi
    have e := hw (4*c+i) (by omega)
    simp only [h1,false_and,ite_false] at e
    simpa only [show o+8*(4*c+i)=o+32*c+8*i by omega] using e

/-- A packed part of the table, as 256-bit coordinates. -/
theorem selectPart_ok {K : JacWinCfg} {s : State} {base : Addr} {size a : Nat} (cache : Bool)
    (hs : Scr s base size) (ha : a≤16) (hb : s.gpr .ebx=BitVec.ofNat 32 a)
    (ht : K.tbl+2560≤size) (ho : K.T+160≤size) :
    WP isa (.block (K.selectPart cache)) s fun t =>
      (∀ c<(if cache then 2 else 3),
        wordsVal t.mem base (K.T+(if cache then 96 else 0)+32*c) 4=
          if 1≤a then wordsVal s.mem base
            (K.tbl+(if cache then 1536 else 0)+(if cache then 64 else 96)*(a-1)+32*c) 4 else 0) ∧
      Outside base (K.T+(if cache then 96 else 0)) (if cache then 64 else 96) s.mem t.mem ∧
      KeepRegs [.ecx,.edx] s t := by
  rw [JacWinCfg.selectPart]
  have hn : 1≤(K.scan cache).M.n ∧ (K.scan cache).M.n≤6 := by
    cases cache <;> simp [JacWinCfg.scan]
  have hH : (K.scan cache).H=16 := by cases cache <;> rfl
  refine WP.mono (scanPart_ok (K.scan cache) hs hn hH ha hb
    (by cases cache <;> simp only [JacWinCfg.scan,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] <;> omega)
    (by cases cache <;> simp only [JacWinCfg.scan,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] <;> omega))
    fun t ⟨et,ot,kt⟩ => ⟨?_,?_,kt⟩
  · intro c hc
    have h := scan_coord ha (n:=(K.scan cache).M.n) (c:=c)
      (by cases cache <;> simp only [JacWinCfg.scan,Bool.false_eq_true,ite_false,ite_true] at hc ⊢ <;> omega) et
    cases cache <;> simpa only [JacWinCfg.scan,Bool.false_eq_true,ite_false,ite_true,Nat.reduceMul] using h
  · cases cache <;> simpa only [JacWinCfg.scan,Bool.false_eq_true,ite_false,ite_true,Nat.reduceMul] using ot

end VG.Proof.Weierstrass.X86.JWin
