import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedLoad

/-! The affine generator row supplies an exact public field environment. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

structure FixedSource (base T : Addr) (tsym : String) (size a x y : Nat) (s : State) : Prop where
  symbol : s.syms tsym=T
  read : ∀ i<4,InRegions (s.rd++s.wr) (off (off T (64*(a-1))) (16*i)) 16
  outside : ∀ i<4,∀ b<16,size≤ofs base (off (off T (64*(a-1))) (16*i)+BitVec.ofNat 64 b)
  xval : wordsVal s.mem (off T (64*(a-1))) 0 4=x
  yval : wordsVal s.mem (off T (64*(a-1))) 32 4=y

theorem FixedSource.of_keeps {base T : Addr} {tsym : String} {size a x y : Nat} {s t : State}
    (h : FixedSource base T tsym size a x y s) {rs : List Reg}
    (hk : Keeps rs s t) (hs : t.syms=s.syms) : FixedSource base T tsym size a x y t := by
  refine ⟨by rw [hs]; exact h.symbol,?_,h.outside,?_,?_⟩
  · intro i hi; rw [hk.2.2.1,hk.2.2.2]; exact h.read i hi
  · rw [hk.2.1]; exact h.xval
  · rw [hk.2.1]; exact h.yval

/-- Any bounded scratch write preserves the external affine coordinates. -/
theorem FixedSource.keep {M : Mod} {base T : Addr} {tsym : String} {size a x y : Nat}
    {s t : State} {W : List Nat} (h : FixedSource base T tsym size a x y s)
    (hk : ProgKeep M base W s t) (hs : t.syms=s.syms)
    (hw : ∀ w∈W,w+8*M.n≤size) (htmp : M.tmp+8*M.n≤size) :
    FixedSource base T tsym size a x y t := by
  have ep : ∀ i<4,t.mem.readW (off (off T (64*(a-1))) (16*i)) 128=
      s.mem.readW (off (off T (64*(a-1))) (16*i)) 128 := by
    intro i hi
    apply Mem.readW_congr
    intro b hb
    have ho := h.outside i hi b (by omega)
    apply hk.mem
    · intro w hm; have := hw w hm; exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have ef (j : Nat) (hj : j<2) :
      wordsVal t.mem (off T (64*(a-1))) (32*j) 4=wordsVal s.mem (off T (64*(a-1))) (32*j) 4 := by
    have e := nafExternalCopy_field (mem:=s.mem) (mem':=t.mem)
      (base:=off T (64*(a-1))) (X:=off T (64*(a-1))) (n:=4) (o:=0) (j:=j)
      (by simpa only [Nat.zero_add] using ep) (by omega)
    simpa only [Nat.zero_add] using e
  refine ⟨by rw [hs]; exact h.symbol,?_,h.outside,?_,?_⟩
  · intro i hi; rw [hk.rd,hk.wr]; exact h.read i hi
  · rw [ef 0 (by decide)]; exact h.xval
  · rw [ef 1 (by decide)]; exact h.yval

def fixedLoadEnv (K : WinCfg) (m : Nat) [NeZero m] (E : Nat → Fin m) (x y : Nat) (a : Nat) : Fin m :=
  if a=K.E.x then toM m (2^256) x else if a=K.E.y then toM m (2^256) y
  else if a=K.E.z then toM m (2^256) K.one else E a

theorem jointFixedFields_ok {K : WinCfg} {s : State} {base T : Addr} {size a x y m : Nat}
    [NeZero m] {tsym : String} {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m}
    (hL : Lay K.M size Sl) (hn : K.M.n=4) (hi : Inv K.M base size m Sl V E s)
    (ha : 1≤a) (h8 : s.gpr .r8=BitVec.ofNat 64 a)
    (hS : FixedSource base T tsym size a x y s)
    (hy : K.E.y=K.E.x+32) (hz : K.E.z=K.E.x+64)
    (hD : ∀ v∈jacCoords K.E,Sl v) (hx : x<m) (hyy : y<m) (hOne : K.one<m) :
    WP isa (.block (Joint.fixedLoad K tsym)) s fun t =>
      ProgKeep K.M base (jacCoords K.E) s t ∧
      Inv K.M base size m Sl (jacCoords K.E++V) (fixedLoadEnv K m E x y) t := by
  have bz := hL.le K.E.z (hD _ (by simp [jacCoords]))
  have hR : m<2^256 := by
    have h := wordsVal_lt s.mem base K.M.mo K.M.n
    rw [hi.mod.val,hn] at h
    exact h
  refine WP.mono (jointFixedLoad_ok hi.scr ha h8 hS.symbol hy (by rw [hn,hz] at bz; omega)
    (by rw [hn] at bz; exact bz) (by omega) (Nat.lt_trans hOne hR) hS.read hS.outside)
    fun t ⟨vx,vy,vz,kt,ut⟩ => ?_
  have kp : ProgKeep K.M base (jacCoords K.E) s t := by
    refine ⟨fun r hr => kt.gpr r (fun hh => hr ?_),kt.rd,kt.wr,fun z hz' _ => ut z ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl|rfl <;> simp [clob]
    · intro w hw
      have hx0 := hz' K.E.x (by simp [jacCoords])
      have hx1 := hz' K.E.y (by simp [jacCoords])
      have hx2 := hz' K.E.z (by simp [jacCoords])
      rw [hn] at hx0 hx1 hx2
      rw [hy] at hx1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl <;> dsimp only <;> omega
  have hlt : ∀ v∈jacCoords K.E,wordsVal t.mem base v K.M.n<m := by
    intro v hv
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hv
    rw [hn]
    rcases hv with rfl|rfl|rfl
    · rw [vx,hS.xval]; exact hx
    · rw [vy,hS.yval]; exact hyy
    · rw [vz]; exact hOne
  have it := hi.of_progKeep hL kp hD hlt
  refine ⟨kp,{it with val := ?_}⟩
  intro v hv
  simp only [fixedLoadEnv]
  split
  · subst v; rw [hn,vx,hS.xval]
  · split
    · subst v; rw [hn,vy,hS.yval]
    · split
      · subst v; rw [hn,vz]
      · have hnot : v∉jacCoords K.E := by
          simp_all only [jacCoords,List.mem_cons,List.not_mem_nil,or_false,not_false_eq_true]
        have hv' := (List.mem_append.mp hv).resolve_left hnot
        rw [kp.slot hL hi.scr hD (hi.sl v hv') hnot,hi.val v hv']

theorem fixedLoadEnv_point {K : WinCfg} {C : Curve} {E : Nat → Fe C} {x y : Nat}
    (hy : K.E.y=K.E.x+32) (hz : K.E.z=K.E.x+64)
    (hOne : toM C.p (2^256) K.one=1) {P : Point C}
    (hp : InvJ C (toM C.p (2^256) x) (toM C.p (2^256) y) 1 P) :
    InvJ C (fixedLoadEnv K C.p E x y K.E.x) (fixedLoadEnv K C.p E x y K.E.y)
      (fixedLoadEnv K C.p E x y K.E.z) P ∧ fixedLoadEnv K C.p E x y K.E.z=1 := by
  have hyx : K.E.y≠K.E.x := by omega
  have hzx : K.E.z≠K.E.x := by omega
  have hzy : K.E.z≠K.E.y := by omega
  simpa only [fixedLoadEnv,ite_true,hyx,hzx,hzy,ite_false,hOne,and_true] using hp

end VG.Proof.Weierstrass.X86_64
