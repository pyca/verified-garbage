import VerifiedGarbage.Impl.Weierstrass.X86.WinJac
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Weierstrass.X86.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.X86.NafAdjust
import VerifiedGarbage.Proof.Weierstrass.X86.NafTableIO

/-! ## `WinJacLayout` -/

section

/-! Low field slots and the packed table above the field-call workspace. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

def ro (K : JacWinCfg) : List Nat := [K.S.a,K.S.b3,K.P.x,K.P.y,K.P.z,K.zero]
def temps (K : JacWinCfg) : List Nat := [K.S.t0,K.S.t1,K.S.t2,K.S.t3,K.S.t4,K.S.t5]
def work (K : JacWinCfg) : List Nat := temps K ++
  [K.R.x,K.R.y,K.R.z,K.D.x,K.D.y,K.D.z,K.E.x,K.E.y,K.E.z,K.z2,K.z3,K.neg]
def slots (K : JacWinCfg) : List Nat := ro K ++ work K

def loopW (K : JacWinCfg) (wk : Nat) : List (Nat × Nat) := progW K.M wk (work K)
def allW (K : JacWinCfg) (wk : Nat) : List (Nat × Nat) := loopW K wk ++ [(K.tbl,2560)]

structure Layout (K : JacWinCfg) (size wk : Nat) : Prop where
  n : K.M.n=4
  size_le : size≤8192
  lay : Lay K.M size (·∈slots K)
  nd : (work K).Nodup
  readonly : ∀ x∈ro K,x∉work K
  table : K.tbl+2560≤size
  low : ∀ x∈slots K,x+32≤K.tbl
  tmp : K.M.tmp+32≤K.tbl
  wk_end : wk+256≤K.tbl
  bits : K.bits+260≤K.tbl
  bits_low : ∀ x∈work K,x+32≤K.bits
  bits_tmp : K.M.tmp+32≤K.bits
  bits_wk : wk+256≤K.bits
  J : 2≤K.J ∧ K.J≤52

theorem entry_bounds {K : JacWinCfg} {m c : Nat} (hm : m<16) (hc : c<5) :
    K.tbl≤K.entry m c ∧ K.entry m c+32≤K.tbl+2560 := by
  unfold JacWinCfg.entry
  split <;> omega

theorem entry_apart {K : JacWinCfg} {m n c d : Nat} (hm : m<16) (hn : n<16)
    (hc : c<5) (hd : d<5) (hne : m≠n ∨ c≠d) :
    K.entry m c+32≤K.entry n d ∨ K.entry n d+32≤K.entry m c := by
  unfold JacWinCfg.entry
  split <;> split <;> omega

/-- A field program cannot modify a cached table coordinate above its workspace. -/
theorem field_keep_entry {K : JacWinCfg} {base : Addr} {size wk : Nat} (hL : Layout K size wk)
    {s t : State} {W : List Nat} (hs : Scr s base size) (hk : ProgKeep K.M base wk W s t)
    (hW : ∀ x∈W,x∈work K) {m c : Nat} (hm : m<16) (hc : c<5) :
    wordsVal t.mem base (K.entry m c) 4=wordsVal s.mem base (K.entry m c) 4 := by
  have he := entry_bounds (K:=K) hm hc
  have ht := hL.table
  have hn := hs.nowrap
  apply hk.unch.wordsVal (d:=K.entry m c) (k:=4) (fun w hw => ?_) (by omega)
  simp only [progW,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with ⟨x,hx,rfl⟩ | rfl | rfl | rfl
  · have := hL.low x (List.mem_append_right _ (hW x hx))
    dsimp only
    rw [hL.n]
    omega
  · have := hL.tmp
    dsimp only
    rw [hL.n]
    omega
  · have := hL.wk_end
    dsimp only
    rw [hL.n]
    omega
  · have := hL.size_le
    change _≤8192 ∨ _
    omega

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacScan` -/

section

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

end

/-! ## `WinJacSelect` -/

section

/-! Selection of a complete cached Jacobian entry with two SSE2 scans. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

theorem select_ok {K : JacWinCfg} {s : State} {base : Addr} {size a : Nat}
    (hs : Scr s base size) (ha : a≤16) (hb : s.gpr .ebx=BitVec.ofNat 32 a)
    (ht : K.tbl+2560≤size) (ho : K.T+160≤size) (hsep : K.T+160≤K.tbl) :
    WP isa (.block K.select) s fun t =>
      (∀ c<5,wordsVal t.mem base (K.T+32*c) 4=
        if 1≤a then wordsVal s.mem base (K.entry (a-1) c) 4 else 0) ∧
      Outside base K.T 160 s.mem t.mem ∧ KeepRegs [.ecx,.edx] s t := by
  rw [JacWinCfg.select,WP.block_append_iff]
  refine WP.mono (selectPart_ok false hs ha hb ht ho) fun u ⟨eu,ou,ku⟩ => ?_
  simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at eu ou
  have hu := hs.of_keepRegs ku (by decide)
  refine WP.mono (selectPart_ok true hu ha ((ku.gpr _ (by decide)).trans hb) ht ho)
    fun t ⟨et,ot,kt⟩ => ?_
  simp only [ite_true] at et ot
  have hn := hs.nowrap
  refine ⟨fun c hc => ?_,
    (ou.mono (Nat.le_refl _) (by omega)).trans (ot.mono (by omega) (by omega)),
    ⟨fun r hr => (kt.gpr r hr).trans (ku.gpr r hr),kt.rd.trans ku.rd,kt.wr.trans ku.wr⟩⟩
  by_cases h3 : c<3
  · rw [ot.wordsVal (by omega) (by omega),eu c h3]
    simp only [JacWinCfg.entry,h3,ite_true]
  · have e := et (c-3) (by omega)
    rw [show K.T+96+32*(c-3)=K.T+32*c by omega] at e
    rw [e]
    by_cases h1 : 1≤a
    · simp only [h1,ite_true,JacWinCfg.entry,h3,ite_false]
      exact ou.wordsVal (by omega) (by omega)
    · simp only [h1,ite_false]

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacPoint` -/

section

/-! Cached Jacobian points and their preservation through low-slot field programs. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

structure Cached (C : Curve) (base : Addr) (s : State) (o : Nat → Nat) (Q : Point C) : Prop where
  lt : ∀ c<5,wordsVal s.mem base (o c) 4<C.p
  jac : InvJ C (tmv C 4 base s (o 0)) (tmv C 4 base s (o 1)) (tmv C 4 base s (o 2)) Q
  z : tmv C 4 base s (o 2)≠0
  z2 : tmv C 4 base s (o 3)=tmv C 4 base s (o 2)*tmv C 4 base s (o 2)
  z3 : tmv C 4 base s (o 4)=tmv C 4 base s (o 3)*tmv C 4 base s (o 2)

theorem Cached.congr {C : Curve} {base : Addr} {s t : State} {o p : Nat → Nat} {Q : Point C}
    (h : Cached C base s o Q) (he : ∀ c<5,wordsVal t.mem base (p c) 4=wordsVal s.mem base (o c) 4) :
    Cached C base t p Q := by
  have e : ∀ c<5,tmv C 4 base t (p c)=tmv C 4 base s (o c) := fun c hc => by
    unfold tmv
    rw [he c hc]
  refine ⟨fun c hc => by rw [he c hc]; exact h.lt c hc,?_,?_,?_,?_⟩
  · rw [e 0 (by decide),e 1 (by decide),e 2 (by decide)]; exact h.jac
  · rw [e 2 (by decide)]; exact h.z
  · rw [e 3 (by decide),e 2 (by decide)]; exact h.z2
  · rw [e 4 (by decide),e 3 (by decide),e 2 (by decide)]; exact h.z3


/-- Turn an arithmetic environment into the memory predicate used by table IO. -/
theorem Cached.of_inv {K : JacWinCfg} {C : Curve} {base : Addr} {size : Nat}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hn : K.M.n=4) (hI : Inv K.M base size C.p Sl V E s)
    (hv : ∀ c<5,K.T+32*c∈V)
    {Q : Point C} (hJ : InvJ C (E K.E.x) (E K.E.y) (E K.E.z) Q)
    (hz : E K.E.z≠0) (h2 : E K.z2=E K.E.z*E K.E.z)
    (h3 : E K.z3=E K.z2*E K.E.z) :
    Cached C base s (fun c => K.T+32*c) Q := by
  have ev (c : Nat) (hc : c<5) : tmv C 4 base s (K.T+32*c)=E (K.T+32*c) := by
    simpa only [tmv,hn] using hI.val _ (hv c hc)
  refine ⟨fun c hc => by simpa only [hn] using hI.lt _ (hv c hc),?_,?_,?_,?_⟩
  · rw [ev 0 (by decide),ev 1 (by decide),ev 2 (by decide)]
    exact hJ
  · rw [ev 2 (by decide)]
    exact hz
  · rw [ev 3 (by decide),ev 2 (by decide)]
    exact h2
  · rw [ev 4 (by decide),ev 3 (by decide),ev 2 (by decide)]
    exact h3

def Table (K : JacWinCfg) (C : Curve) (base : Addr) (P : Point C) (M : Nat) (s : State) : Prop :=
  ∀ m,1≤m → m≤M → Cached C base s (K.entry (m-1)) (mul m P)

theorem Table.field_keep {K : JacWinCfg} {C : Curve} {base : Addr} {size wk M : Nat}
    (hL : Layout K size wk) {s t : State} {W : List Nat} (hs : Scr s base size)
    (hk : ProgKeep K.M base wk W s t) (hW : ∀ x∈W,x∈work K)
    {P : Point C} (hT : Table K C base P M s) (hM : M≤16) : Table K C base P M t := by
  intro m h1 hm
  exact (hT m h1 hm).congr fun c hc => field_keep_entry hL hs hk hW (by omega) hc

/-- The selected nonzero magnitude represents the corresponding point,
with both cached powers carried along by the two scans. -/
theorem select_nonzero_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size a : Nat}
    {s : State} (hs : Scr s base size) (ha : 1≤a) (ha16 : a≤16)
    (hb : s.gpr .ebx=BitVec.ofNat 32 a) (ht : K.tbl+2560≤size) (ho : K.T+160≤size)
    (hsep : K.T+160≤K.tbl) {P : Point C} (hT : Table K C base P 16 s) :
    WP isa (.block K.select) s fun t =>
      Cached C base t (fun c => K.T+32*c) (mul a P) ∧
      Outside base K.T 160 s.mem t.mem ∧ KeepRegs [.ecx,.edx] s t := by
  refine WP.mono (select_ok hs ha16 hb ht ho hsep) fun t ⟨et,ot,kt⟩ => ⟨?_,ot,kt⟩
  exact (hT a ha ha16).congr fun c hc => by simpa only [ha,ite_true] using et c hc

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacStore` -/

section

/-! Store each cached Jacobian entry at addresses derived from the public counter. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

theorem entryAddr_ok {K : JacWinCfg} {s : State} {base : Addr} {size j : Nat} (cache : Bool)
    (hs : Scr s base size) (h1 : 1≤j) (h16 : j≤16)
    (hb : s.gpr .esi=BitVec.ofNat 32 j) (ht : K.tbl+2560≤size) :
    WP isa (.block (K.entryAddr cache)) s fun t =>
      (t.gpr .edx).setWidth 64=
        off base (K.tbl+(if cache then 1536 else 0)+(if cache then 64 else 96)*(j-1)) ∧
      CKeeps [.eax,.ecx,.edx] s t := by
  have hj : BitVec.ofNat 32 j-1=BitVec.ofNat 32 (j-1) :=
    BitVec.ofNat_sub_ofNat_of_le j 1 (by decide) h1
  apply WP.of_runBlock
  simp only [JacWinCfg.entryAddr,runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,
    execAlu,execMul,hb,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags,Option.map_some,Option.bind_some,ite_true,ite_false,reduceCtorEq,
    Option.some.injEq,exists_eq_left',hj]
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · cases cache <;>
      simp only [Bool.false_eq_true,ite_false,ite_true,BitVec.toNat_ofNat,Nat.add_zero]
    · rw [show (96 : BitVec 32).toNat=96 from rfl,
        Nat.mod_eq_of_lt (show j-1<2^32 by omega),Nat.mul_comm (j-1),Offset.add_add]
      exact hs.ea (by omega)
    · rw [show (64 : BitVec 32).toNat=64 from rfl,
        Nat.mod_eq_of_lt (show j-1<2^32 by omega),Nat.mul_comm (j-1),Offset.add_add]
      exact hs.ea (by omega)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.gpr_setFlags,
      hr.1,hr.2.1,hr.2.2,ite_false]

theorem storePart_ok {K : JacWinCfg} {s : State} {base : Addr} {size j : Nat} (cache : Bool)
    (hs : Scr s base size) (h1 : 1≤j) (h16 : j≤16)
    (hb : s.gpr .esi=BitVec.ofNat 32 j) (ht : K.tbl+2560≤size) (hT : K.T+160≤K.tbl) :
    WP isa (.block (K.storePart cache)) s fun t =>
      (∀ c<(if cache then 2 else 3),
        wordsVal t.mem base
          (K.tbl+(if cache then 1536 else 0)+(if cache then 64 else 96)*(j-1)+32*c) 4=
        wordsVal s.mem base (K.T+(if cache then 96 else 0)+32*c) 4) ∧
      Outside base (K.tbl+(if cache then 1536 else 0)+(if cache then 64 else 96)*(j-1))
        (if cache then 64 else 96) s.mem t.mem ∧ KeepRegs [.eax,.ecx,.edx] s t := by
  rw [JacWinCfg.storePart,WP.block_append_iff]
  refine WP.mono (entryAddr_ok cache hs h1 h16 hb ht) fun u ⟨pu,ku⟩ => ?_
  have hu := hs.of_keeps ku.keeps (by decide)
  refine WP.mono (nafCopyPieces_ok
    (a:=K.T+(if cache then 96 else 0))
    (o:=K.tbl+(if cache then 1536 else 0)+(if cache then 64 else 96)*(j-1))
    (if cache then 4 else 6) u hu
    (by cases cache <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] <;> omega)
    (by cases cache <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] <;> omega)
    (by cases cache <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] <;> omega)
    (fun i hi => hu.ea (by cases cache <;>
      simp only [Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] at hi ⊢ <;> omega))
    (fun i hi => nafTable_ea hu pu (by cases cache <;>
      simp only [Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] at hi ⊢ <;> omega)))
    fun t ⟨et,ot,gt,rt,wt⟩ => ?_
  refine ⟨fun c hc => ?_,?_,⟨fun r hr => (congrFun gt r).trans (ku.1 r hr),
    rt.trans ku.2.2.1,wt.trans ku.2.2.2⟩⟩
  · rw [nafCopy_field et (by cases cache <;>
      simp only [Bool.false_eq_true,ite_false,ite_true] at hc ⊢ <;> omega),ku.2.1]
  · rw [ku.2.1] at ot
    cases cache <;> exact ot

def storeW (K : JacWinCfg) (m : Nat) : List (Nat × Nat) :=
  [(K.tbl+96*m,96),(K.tbl+1536+64*m,64)]

theorem storeEntry_ok {K : JacWinCfg} {s : State} {base : Addr} {size j : Nat}
    (hs : Scr s base size) (h1 : 1≤j) (h16 : j≤16)
    (hb : s.gpr .esi=BitVec.ofNat 32 j) (ht : K.tbl+2560≤size) (hT : K.T+160≤K.tbl) :
    WP isa (.block K.storeEntry) s fun t =>
      (∀ c<5,wordsVal t.mem base (K.entry (j-1) c) 4=wordsVal s.mem base (K.T+32*c) 4) ∧
      Unch base (storeW K (j-1)) s.mem t.mem ∧ KeepRegs [.eax,.ecx,.edx] s t := by
  rw [JacWinCfg.storeEntry,WP.block_append_iff]
  refine WP.mono (storePart_ok false hs h1 h16 hb ht hT) fun u ⟨eu,ou,ku⟩ => ?_
  simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at eu ou
  have hu := hs.of_keepRegs ku (by decide)
  refine WP.mono (storePart_ok true hu h1 h16 ((ku.gpr _ (by decide)).trans hb) ht hT)
    fun t ⟨et,ot,kt⟩ => ?_
  simp only [ite_true] at et ot
  have hn := hs.nowrap
  refine ⟨fun c hc => ?_,ou.unch.trans ot.unch,
    ⟨fun r hr => (kt.gpr r hr).trans (ku.gpr r hr),kt.rd.trans ku.rd,kt.wr.trans ku.wr⟩⟩
  by_cases h3 : c<3
  · simp only [JacWinCfg.entry,h3,ite_true]
    rw [ot.wordsVal (by omega) (by omega),eu c h3]
  · have e := et (c-3) (by omega)
    rw [show K.T+96+32*(c-3)=K.T+32*c by omega] at e
    simp only [JacWinCfg.entry,h3,ite_false]
    rw [e,ou.wordsVal (by omega) (by omega)]

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacTableStore` -/

section

/-! Extend the table without changing any of its earlier entries. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem store_apart {K : JacWinCfg} {i j c : Nat} (hi : i<16) (hj : j<16) (hc : c<5)
    (hne : i≠j) : ∀ w∈storeW K j,K.entry i c+32≤w.1 ∨ w.1+w.2≤K.entry i c := by
  intro w hw
  simp only [storeW,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl <;> dsimp only <;> unfold JacWinCfg.entry <;> split <;> omega

theorem store_table_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size M : Nat}
    {s : State} (hs : Scr s base size) (hM : M<16)
    (hb : s.gpr .esi=BitVec.ofNat 32 (M+1)) (ht : K.tbl+2560≤size) (hT : K.T+160≤K.tbl)
    {P : Point C} (hOld : Table K C base P M s)
    (hNew : Cached C base s (fun c => K.T+32*c) (mul (M+1) P)) :
    WP isa (.block K.storeEntry) s fun t => Table K C base P (M+1) t ∧
      Unch base (storeW K M) s.mem t.mem ∧ KeepRegs [.eax,.ecx,.edx] s t := by
  refine WP.mono (storeEntry_ok hs (by omega) (by omega) hb ht hT) fun t ⟨et,ot,kt⟩ => ?_
  simp only [Nat.add_sub_cancel] at et ot
  refine ⟨fun m h1 hm => ?_,ot,kt⟩
  by_cases he : m=M+1
  · subst m
    simp only [Nat.add_sub_cancel]
    exact hNew.congr et
  · have hOld' := hOld m h1 (by omega)
    apply hOld'.congr
    intro c hc
    have eb := entry_bounds (K:=K) (m:=m-1) (by omega) hc
    have hn := hs.nowrap
    exact ot.wordsVal (store_apart (by omega) hM hc (by omega)) (by omega)

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacFrame` -/

section

/-! The memory and register frame shared by table construction and the secret loop. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

def clobbers : List Reg := clob++[.esi]

structure Frame (K : JacWinCfg) (C : Curve) (base : Addr) (size wk : Nat) (s₀ s : State) : Prop where
  scr : Scr s base size
  keep : KeepRegs clobbers s₀ s
  unch : Unch base (allW K wk) s₀.mem s.mem
  mod : ModOkW K.M size C.p s.mem base

theorem ro_apart {K : JacWinCfg} {size wk m : Nat} (hL : Layout K size wk)
    (hW : WkOk K.F K.M m size wk (·∈slots K)) {x : Nat} (hx : x∈ro K) :
    ∀ w∈allW K wk,x+8*K.M.n≤w.1 ∨ w.1+w.2≤x := by
  have hxs : x∈slots K := List.mem_append_left _ hx
  intro w hw
  simp only [allW,loopW,progW,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with (⟨y,hy,rfl⟩ | rfl | rfl | rfl) | rfl
  · exact hL.lay.apart x y hxs (List.mem_append_right _ hy) (fun he => hL.readonly x hx (he ▸ hy))
  · exact hL.lay.tmp x hxs
  · exact Or.inl (hW.sl x hxs)
  · have := hL.lay.le x hxs
    have := hL.size_le
    change _≤8192 ∨ _
    omega
  · have := hL.low x hxs
    dsimp only
    rw [hL.n]
    omega

theorem mod_unch {K : JacWinCfg} {base : Addr} {size wk m : Nat} (hL : Layout K size wk)
    (hW : WkOk K.F K.M m size wk (·∈slots K)) {s t : State}
    (hs : Scr s base size) (hM : ModOkW K.M size m s.mem base)
    (hu : Unch base (allW K wk) s.mem t.mem) : ModOkW K.M size m t.mem base := by
  refine ⟨hM.n0,hM.mo,hM.tmp,hM.sep,?_,hM.inv,hM.red⟩
  rw [hu.wordsVal (fun w hw => ?_) (by have := hs.nowrap; have := hM.mo; omega),hM.val]
  simp only [allW,loopW,progW,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with (⟨x,hx,rfl⟩ | rfl | rfl | rfl) | rfl
  · exact (hL.lay.mo x (List.mem_append_right _ hx)).symm
  · exact hM.sep
  · exact Or.inl hW.mo
  · have := hM.mo
    have := hL.size_le
    change _≤8192 ∨ _
    omega
  · have := hW.mo
    have := hL.wk_end
    dsimp only
    rw [hL.n] at *
    omega

theorem Frame.refl {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat} {s : State}
    (hs : Scr s base size) (hm : ModOkW K.M size C.p s.mem base) : Frame K C base size wk s s :=
  ⟨hs,⟨fun _ _ => rfl,rfl,rfl⟩,Unch.refl _ _ _,hm⟩

theorem Frame.next {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s₀ s t : State} (h : Frame K C base size wk s₀ s) (hs : Scr t base size)
    (hk : KeepRegs clobbers s t) (hu : Unch base (allW K wk) s.mem t.mem) :
    Frame K C base size wk s₀ t :=
  ⟨hs,⟨fun r hr => (hk.gpr r hr).trans (h.keep.gpr r hr),hk.rd.trans h.keep.rd,hk.wr.trans h.keep.wr⟩,
    (h.unch.trans hu).mono (fun _ hw => (List.mem_append.mp hw).elim id id),mod_unch hL hW h.scr h.mod hu⟩

theorem Frame.ro {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s₀ s : State} (h : Frame K C base size wk s₀ s) {x : Nat} (hx : x∈ro K) :
    wordsVal s.mem base x K.M.n=wordsVal s₀.mem base x K.M.n :=
  h.unch.wordsVal (ro_apart hL hW hx) (by
    have := h.scr.nowrap
    have := hL.lay.le x (List.mem_append_left _ hx)
    omega)

theorem Frame.bits {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) {s₀ s : State} (h : Frame K C base size wk s₀ s) {i : Nat} (hi : i<260) :
    s.mem (off base (K.bits+i))=s₀.mem (off base (K.bits+i)) := by
  have ht := hL.table
  have hb := hL.bits
  have hn := h.scr.nowrap
  apply h.unch.byte (fun w hw => ?_) (by omega)
  simp only [allW,loopW,progW,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with (⟨x,hx,rfl⟩ | rfl | rfl | rfl) | rfl
  · have := hL.bits_low x hx
    dsimp only
    rw [hL.n]
    omega
  · have := hL.bits_tmp
    dsimp only
    rw [hL.n]
    omega
  · have := hL.bits_wk
    dsimp only
    rw [hL.n]
    omega
  · have := hL.size_le
    change _<8192 ∨ _
    omega
  · dsimp only
    omega

theorem field_allW {K : JacWinCfg} {base : Addr} {wk : Nat} {W : List Nat} {s t : State}
    (hk : ProgKeep K.M base wk W s t) (hw : ∀ x∈W,x∈work K) :
    Unch base (allW K wk) s.mem t.mem :=
  hk.unch.mono fun w h => List.mem_append_left _ (progW_mono hw w h)

theorem Frame.field {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s₀ s t : State} (h : Frame K C base size wk s₀ s) {W : List Nat}
    (hk : ProgKeep K.M base wk W s t) (hw : ∀ x∈W,x∈work K) : Frame K C base size wk s₀ t :=
  h.next hL hW (hk.scr h.scr)
    ⟨fun r hr => hk.gpr r (fun hc => hr (List.mem_append_left _ hc)),hk.rd,hk.wr⟩ (field_allW hk hw)


theorem Frame.keeps {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    {s₀ s t : State} (h : Frame K C base size wk s₀ s) (hk : CKeeps [.esi] s t) :
    Frame K C base size wk s₀ t := by
  refine ⟨h.scr.of_keeps hk.keeps (by decide),
    h.keep.trans ((CKeeps.regs hk).mono (fun _ hr => List.mem_append_right _ hr)),?_,?_⟩
  · rw [hk.2.1]; exact h.unch
  · rw [hk.2.1]; exact h.mod

theorem mov_counter_ok (s : State) (m : Nat) :
    WP isa (.block [.mov .esi (.imm (BitVec.ofNat 32 m))]) s fun t =>
      t.gpr .esi=BitVec.ofNat 32 m ∧ CKeeps [.esi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,
    Option.map_some,RegUpd.gpr_setReg,ite_true,Option.some.injEq,exists_eq_left']
  exact ⟨trivial,fun r hr => by
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg,hr,ite_false],rfl,rfl,rfl⟩

/-- Storing an entry changes only the packed table, within the shared frame. -/
theorem store_allW {K : JacWinCfg} {base : Addr} {wk m : Nat} {s t : State}
    (hm : m<16) (hu : Unch base (storeW K m) s.mem t.mem) :
    Unch base (allW K wk) s.mem t.mem := by
  apply hu.cover
  intro w hw
  refine ⟨(K.tbl,2560),List.mem_append_right _ (List.mem_singleton_self _),?_⟩
  simp only [storeW,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl <;> dsimp only <;> constructor <;> omega

theorem Frame.store {K : JacWinCfg} {C : Curve} {base : Addr} {size wk m : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s₀ s t : State} (h : Frame K C base size wk s₀ s) (hm : m<16)
    (hu : Unch base (storeW K m) s.mem t.mem) (hk : KeepRegs [.eax,.ecx,.edx] s t) :
    Frame K C base size wk s₀ t := by
  apply h.next hL hW (h.scr.of_keepRegs hk (by decide)) ?_ (store_allW hm hu)
  refine ⟨fun r hr => hk.gpr r ?_,hk.rd,hk.wr⟩
  intro he
  apply hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl <;> decide

/-- Compose table growth with the frame needed by subsequent arithmetic. -/
theorem store_framed_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk M : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s₀ s : State} (h : Frame K C base size wk s₀ s) (hM : M<16)
    (hb : s.gpr .esi=BitVec.ofNat 32 (M+1)) {P : Point C}
    (hOld : Table K C base P M s)
    (hNew : Cached C base s (fun c => K.T+32*c) (mul (M+1) P)) :
    WP isa (.block K.storeEntry) s fun t =>
      Table K C base P (M+1) t ∧ Frame K C base size wk s₀ t ∧
      t.gpr .esi=BitVec.ofNat 32 (M+1) := by
  have hT : K.T+160≤K.tbl := by
    have := hL.low K.z3 (by simp [slots,work,JacWinCfg.z3])
    simp only [JacWinCfg.z3] at this
    omega
  refine WP.mono (store_table_ok h.scr hM hb hL.table hT hOld hNew)
    fun t ⟨ht,hu,hk⟩ => ⟨ht,h.store hL hW hM hu hk,(hk.gpr _ (by decide)).trans hb⟩

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacBuildState` -/

section

/-! Invariants shared by the finite-point table construction steps. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

def live (K : JacWinCfg) : List Nat := ro K++[K.E.x,K.E.y,K.E.z,K.z2,K.z3]

theorem live_slots (K : JacWinCfg) : ∀ x∈live K,x∈slots K := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact List.mem_append_left _ hx
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl <;> simp [slots,work]

/-- The table stores leave every initialized arithmetic slot intact. -/
theorem store_slot {K : JacWinCfg} {base : Addr} {size wk m x : Nat} {s t : State}
    (hL : Layout K size wk) (hs : Scr s base size) (hx : x∈slots K)
    (hu : Unch base (storeW K m) s.mem t.mem) :
    wordsVal t.mem base x K.M.n=wordsVal s.mem base x K.M.n := by
  have hl := hL.low x hx
  have hb := hL.lay.le x hx
  have hn := hs.nowrap
  apply hu.wordsVal (fun w hw => ?_) (by omega)
  simp only [storeW,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl <;> dsimp only <;> rw [hL.n] <;> omega

theorem Cached.store {K : JacWinCfg} {C : Curve} {base : Addr} {size wk m : Nat} {s t : State}
    (hL : Layout K size wk) (hs : Scr s base size) (hu : Unch base (storeW K m) s.mem t.mem)
    {Q : Point C} (h : Cached C base s (fun c => K.T+32*c) Q) :
    Cached C base t (fun c => K.T+32*c) Q := by
  apply h.congr
  intro c hc
  have hx : K.T+32*c∈slots K := by
    have : c=0 ∨ c=1 ∨ c=2 ∨ c=3 ∨ c=4 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl <;> simp [slots,work,JacWinCfg.E,JacWinCfg.z2,JacWinCfg.z3]
  simpa only [hL.n] using store_slot hL hs hx hu

/-- Reconstruct only initialized fields; temporary arithmetic slots need no bounds. -/
theorem Frame.inv_cached {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s₀ s : State} (h : Frame K C base size wk s₀ s)
    (hro : ∀ x∈JWin.ro K,wordsVal s₀.mem base x K.M.n<C.p) {Q : Point C}
    (hc : Cached C base s (fun c => K.T+32*c) Q) :
    Inv K.M base size C.p (·∈slots K) (live K) (tmv C K.M.n base s) s := by
  refine ⟨h.scr,h.mod,live_slots K,?_,fun _ _ => rfl⟩
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · rw [h.ro hL hW hx]; exact hro x hx
  · rw [hL.n]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl
    · exact hc.lt 0 (by decide)
    · exact hc.lt 1 (by decide)
    · exact hc.lt 2 (by decide)
    · exact hc.lt 3 (by decide)
    · exact hc.lt 4 (by decide)

structure BuildInv (K : JacWinCfg) (C : Curve) (base : Addr) (size wk : Nat)
    (P : Point C) (s₀ : State) (m : Nat) (s : State) : Prop where
  frame : Frame K C base size wk s₀ s
  table : Table K C base P m s
  point : Cached C base s (fun c => K.T+32*c) (mul m P)
  counter : s.gpr .esi=BitVec.ofNat 32 m

theorem build_store_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk m : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s₀ s : State} (h : Frame K C base size wk s₀ s) (hm : m<16)
    (hb : s.gpr .esi=BitVec.ofNat 32 (m+1)) {P : Point C}
    (ht : Table K C base P m s)
    (hp : Cached C base s (fun c => K.T+32*c) (mul (m+1) P)) :
    WP isa (.block K.storeEntry) s (BuildInv K C base size wk P s₀ (m+1)) := by
  have hT : K.T+160≤K.tbl := by
    have := hL.low K.z3 (by simp [slots,work])
    simp only [JacWinCfg.z3] at this
    omega
  refine WP.mono (store_table_ok h.scr hm hb hL.table hT ht hp)
    fun t ⟨ht,hu,hk⟩ => ⟨h.store hL hW hm hu hk,ht,hp.store hL h.scr hu,
      (hk.gpr _ (by decide)).trans hb⟩

end VG.Proof.Weierstrass.X86.JWin

end
