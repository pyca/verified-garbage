import VerifiedGarbage.Impl.Weierstrass.AArch64.Joint
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombPublic

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

/-- Copy an affine generator entry from the read-only table. -/
theorem jointLoadWords_ok {s : State} {base p : Addr} {size dst n : Nat}
    (hs : Scr s base size) (hp : s.gpr .x16=p)
    (hd : dst+8*n≤size) (ha : dst%8=0) (hn : 8*n≤32768)
    (hr : ∀ i<n, InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (8*i)) 8)
    (hout : ∀ i<n, ∀ b<8, size≤ofs base (p+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b)) :
    ∀ k≤n, WP isa (.block (Joint.loadWords dst k)) s fun t =>
      (∀ i<k, word t.mem base (dst+8*i)=word s.mem p (8*i)) ∧
      KeepRegs [.x4] s t ∧ Outside base dst (8*k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _),
      ⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Outside.refl _ _ _ _⟩
  | k+1, hk => by
    rw [Joint.loadWords,List.range_succ,List.flatMap_append,List.flatMap_singleton,
      WP.block_append_iff]
    refine WP.mono (jointLoadWords_ok hs hp hd ha hn hr hout k (by omega)) fun a ⟨ea,ka,oa⟩ => ?_
    have sa := hs.of_keepRegs ka (by decide)
    change WP isa (.block ([.ldr .x .x4 .x16 (8*k)]++[st .x4 (dst+8*k)])) a _
    rw [WP.block_append_iff]
    refine WP.mono (direct_load (p:=p) (by rw [ka.gpr _ (by decide),hp]) (by omega)
      (by rw [ka.rd,ka.wr]; exact hr k (by omega))) fun b ⟨eb,kb,_⟩ => ?_
    have sb := sa.of_keeps kb (by decide)
    refine WP.mono (st_ok sb (d:=dst+8*k) (by omega) (by omega) .x4) fun t et => ?_
    have mt : t.mem=b.mem.writeW (off base (dst+8*k)) (b.gpr .x4) := by rw [et]
    have kt : KeepRegs [] b t := by subst et; exact ⟨fun _ _ => rfl,rfl,rfl,rfl⟩
    have ot : Outside base (dst+8*k) 8 b.mem t.mem := by
      rw [mt]; exact writeW_outside _ _ _ (by have := hs.nowrap; omega)
    have old : word a.mem p (8*k)=word s.mem p (8*k) :=
      Mem.readW_congr fun j hj => oa _ (Or.inr (by
        have := hout k (by omega) j (by omega); dsimp only [off]; omega))
    refine ⟨fun i hi => ?_,ka.trans ((Keeps.regs kb).trans (kt.mono (by simp))),?_⟩
    · rcases Nat.lt_or_ge i k with h | h
      · rw [ot.word (by omega) (by have := hs.nowrap; omega),kb.mem,ea i h]
      · obtain rfl : i=k := by omega
        rw [mt,word_writeW_self,eb,old]
    · refine (oa.mono (Nat.le_refl _) (by omega)).trans ?_
      rw [←kb.mem]
      exact ot.mono (by omega) (by omega)

theorem jointAddress_ok (c : Joint.Cfg) {s : State} {a : Nat} {T : Addr}
    (ha : 1≤a) (h2 : s.gpr .x2=BitVec.ofNat 64 a) (ht : s.syms c.tsym=T) :
    WP isa (.block (Joint.address c)) s fun t =>
      t.gpr .x16=T+BitVec.ofNat 64 (128*(a-1)) ∧ Keeps [.x2,.x16] s t := by
  apply WP.of_runBlock
  simp only [Joint.address,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,Size.bits,h2,
    show 1<4096 by decide,show 7<64 by decide,ite_true,ite_false,reduceCtorEq,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
  · rw [BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) ha]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
    rw [Nat.mul_mod, Nat.mod_mod, ←Nat.mul_mod]
    congr 1
    omega
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

/-- Loading x and y and copying the Montgomery one initializes an affine point. -/
theorem jointFixedLoad_ok (c : Joint.Cfg) {s : State} {base T : Addr} {size a : Nat}
    (hs : Scr s base size) (ha : 1≤a) (h2 : s.gpr .x2=BitVec.ofNat 64 a)
    (ht : s.syms c.tsym=T) (hy : c.K.E.y=c.K.E.x+32)
    (hd : c.K.E.x+64≤size) (hd8 : c.K.E.x%8=0)
    (hz : c.K.E.z+32≤size) (hz8 : c.K.E.z%8=0)
    (hone : c.onep+32≤size) (hone8 : c.onep%8=0)
    (hsep : c.K.E.x+64≤c.K.E.z ∨ c.K.E.z+32≤c.K.E.x)
    (hsep1 : c.K.E.x+64≤c.onep ∨ c.onep+32≤c.K.E.x)
    (hsepz : c.K.E.z≤c.onep ∨ c.onep+32≤c.K.E.z)
    (hr : ∀ i<8, InRegions (s.rd++s.wr)
      (T+BitVec.ofNat 64 (128*(a-1))+BitVec.ofNat 64 (8*i)) 8)
    (hout : ∀ i<8, ∀ b<8, size≤ofs base
      (T+BitVec.ofNat 64 (128*(a-1))+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b)) :
    WP isa (.block (Joint.fixedLoad c)) s fun t =>
      wordsVal t.mem base c.K.E.x 4=wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) 0 4 ∧
      wordsVal t.mem base c.K.E.y 4=wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) 32 4 ∧
      wordsVal t.mem base c.K.E.z 4=wordsVal s.mem base c.onep 4 ∧
      KeepRegs [.x1,.x2,.x4,.x16] s t ∧
      Unch base [(c.K.E.x,64),(c.K.E.z,32)] s.mem t.mem := by
  rw [Joint.fixedLoad,List.append_assoc,WP.block_append_iff]
  refine WP.mono (jointAddress_ok c ha h2 ht) fun b ⟨b16,kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (jointLoadWords_ok (hs.of_keeps kb (by decide)) b16 hd hd8 (by decide)
    (by intro i hi; rw [kb.rd,kb.wr]; exact hr i hi) hout 8 (by decide)) fun d ⟨wd,kd,od⟩ => ?_
  refine WP.mono (copy_ok 4 ((hs.of_keeps kb (by decide)).of_keepRegs kd (by decide))
    hz hone hz8 hone8 hsepz) fun t ⟨zt,kt,ot⟩ => ?_
  have hn := hs.nowrap
  have wx : wordsVal d.mem base c.K.E.x 4=wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) 0 4 := by
    refine wordsVal_of_words₂ _ _ _ fun i hi => ?_
    simpa only [Nat.zero_add,kb.mem] using wd i (by omega)
  have wy : wordsVal d.mem base c.K.E.y 4=wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) 32 4 := by
    refine wordsVal_of_words₂ _ _ _ fun i hi => ?_
    rw [hy]
    have e := wd (4+i) (by omega)
    simpa only [Nat.mul_add,Nat.add_assoc,kb.mem] using e
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [ot.wordsVal (by omega) (by omega),wx]
  · rw [ot.wordsVal (by omega) (by omega),wy]
  · rw [zt,od.wordsVal (by omega) (by omega),kb.mem]
  · exact ((Keeps.regs kb).mono (by sub_regs)).trans
      ((kd.mono (by sub_regs)).trans (kt.mono (by sub_regs)))
  · intro x hx
    have hx0 := hx (c.K.E.x,64) (by simp)
    have hx1 := hx (c.K.E.z,32) (by simp)
    rw [ot x hx1,od x hx0,kb.mem]

end VG.Proof.Weierstrass.AArch64
