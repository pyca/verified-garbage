import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedLoad

/-! The affine generator row supplies an exact public field environment. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

/-- Row `a` of an external table of `16 n`-byte affine entries at symbol `tsym`:
readable, outside the scratch allocation, with coordinates `x` and `y`. -/
structure FixedSource (n : Nat) (base T : Addr) (tsym : String) (size a x y : Nat) (s : State) : Prop where
  symbol : s.syms tsym=T
  read : ∀ i<n,InRegions (s.rd++s.wr) (off (off T (16*n*(a-1))) (16*i)) 16
  outside : ∀ i<n,∀ b<16,size≤ofs base (off (off T (16*n*(a-1))) (16*i)+BitVec.ofNat 64 b)
  xval : wordsVal s.mem (off T (16*n*(a-1))) 0 n=x
  yval : wordsVal s.mem (off T (16*n*(a-1))) (8*n) n=y

theorem FixedSource.of_keeps {n : Nat} {base T : Addr} {tsym : String} {size a x y : Nat} {s t : State}
    (h : FixedSource n base T tsym size a x y s) {rs : List Reg}
    (hk : Keeps rs s t) (hs : t.syms=s.syms) : FixedSource n base T tsym size a x y t := by
  refine ⟨by rw [hs]; exact h.symbol,?_,h.outside,?_,?_⟩
  · intro i hi; rw [hk.2.2.1,hk.2.2.2]; exact h.read i hi
  · rw [hk.2.1]; exact h.xval
  · rw [hk.2.1]; exact h.yval

/-- The external row survives any write confined to scratch, regardless of register clobbers. -/
theorem FixedSource.keep_of_mem {n : Nat} {base T : Addr} {tsym : String} {size a x y : Nat}
    {s t : State} (h : FixedSource n base T tsym size a x y s)
    (hs : t.syms=s.syms) (hr : t.rd=s.rd) (hw : t.wr=s.wr)
    (hmem : ∀ z,size≤ofs base z → t.mem z=s.mem z) :
    FixedSource n base T tsym size a x y t := by
  have ep : ∀ i<n,t.mem.readW (off (off T (16*n*(a-1))) (0+16*i)) 128=
      s.mem.readW (off (off T (16*n*(a-1))) (16*i)) 128 := by
    intro i hi
    rw [Nat.zero_add]
    apply Mem.readW_congr
    intro b hb
    exact hmem _ (h.outside i hi b (by omega))
  have ef (d : Nat) (hd : d%8=0) (hj : d+8*n≤16*n) :
      wordsVal t.mem (off T (16*n*(a-1))) d n=wordsVal s.mem (off T (16*n*(a-1))) d n := by
    simpa only [Nat.zero_add] using nafExternalCopy_fieldAt (o:=0) ep hd hj
  refine ⟨by rw [hs]; exact h.symbol,?_,h.outside,?_,?_⟩
  · intro i hi; rw [hr,hw]; exact h.read i hi
  · rw [ef 0 (by decide) (by omega)]; exact h.xval
  · rw [ef (8*n) (by omega) (by omega)]; exact h.yval

/-- Any bounded scratch write preserves the external affine coordinates. -/
theorem FixedSource.keep {M : Mod} {n : Nat} {base T : Addr} {tsym : String} {size a x y : Nat}
    {s t : State} {W : List Nat} (h : FixedSource n base T tsym size a x y s)
    (hk : ProgKeep M base W s t) (hs : t.syms=s.syms)
    (hw : ∀ w∈W,w+8*M.n≤size) (htmp : M.tmp+8*M.n≤size) :
    FixedSource n base T tsym size a x y t :=
  h.keep_of_mem hs hk.rd hk.wr (fun z hz => hk.mem z
    (fun w hm => Or.inr (Nat.le_trans (hw w hm) hz)) (Or.inr (Nat.le_trans htmp hz)))

def fixedLoadEnv (K : WinCfg) (m : Nat) [NeZero m] (E : Nat → Fin m) (x y : Nat) (a : Nat) : Fin m :=
  if a=K.E.x then toM m (2^(64*K.M.n)) x else if a=K.E.y then toM m (2^(64*K.M.n)) y
  else if a=K.E.z then toM m (2^(64*K.M.n)) K.one else E a

theorem jointFixedFields_ok {K : WinCfg} {s : State} {base T : Addr} {size a x y m : Nat}
    [NeZero m] {tsym : String} {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m}
    (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6) (hi : Inv K.M base size m Sl V E s)
    (ha : 1≤a) (ha' : a≤2^31) (h8 : s.gpr .r8=BitVec.ofNat 64 a)
    (hS : FixedSource K.M.n base T tsym size a x y s)
    (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hD : ∀ v∈jacCoords K.E,Sl v) (hx : x<m) (hyy : y<m) (hOne : K.one<m) :
    WP isa (.block (Joint.fixedLoad K tsym)) s fun t =>
      ProgKeep K.M base (jacCoords K.E) s t ∧
      Inv K.M base size m Sl (jacCoords K.E++V) (fixedLoadEnv K m E x y) t := by
  have bz := hL.le K.E.z (hD _ (by simp [jacCoords]))
  have hR : m<2^(64*K.M.n) := by
    have h := wordsVal_lt s.mem base K.M.mo K.M.n
    rw [hi.mod.val] at h
    exact h
  rw [hz] at bz
  refine WP.mono (jointFixedLoad_ok hi.scr ha ha' (by omega) h8 hS.symbol hy (by omega)
    (by rw [hz]; exact bz) (by omega) (Nat.lt_trans hOne hR) hS.read hS.outside)
    fun t ⟨vx,vy,vz,kt,ut⟩ => ?_
  have kp : ProgKeep K.M base (jacCoords K.E) s t := by
    refine ⟨fun r hr => kt.gpr r (fun hh => hr ?_),kt.rd,kt.wr,fun z hz' _ => ut z ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl|rfl|rfl <;> simp [clob]
    · intro w hw
      have hx0 := hz' K.E.x (by simp [jacCoords])
      have hx1 := hz' K.E.y (by simp [jacCoords])
      have hx2 := hz' K.E.z (by simp [jacCoords])
      rw [hy] at hx1
      rw [hz] at hx2
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl <;> dsimp only <;> omega
  have hlt : ∀ v∈jacCoords K.E,wordsVal t.mem base v K.M.n<m := by
    intro v hv
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl
    · rw [vx,hS.xval]; exact hx
    · rw [vy,hS.yval]; exact hyy
    · rw [vz]; exact hOne
  have it := hi.of_progKeep hL kp hD hlt
  refine ⟨kp,{it with val := ?_}⟩
  intro v hv
  simp only [fixedLoadEnv]
  split
  · subst v; rw [vx,hS.xval]
  · split
    · subst v; rw [vy,hS.yval]
    · split
      · subst v; rw [vz]
      · have hnot : v∉jacCoords K.E := by
          simp_all only [jacCoords,List.mem_cons,List.not_mem_nil,or_false,not_false_eq_true]
        have hv' := (List.mem_append.mp hv).resolve_left hnot
        rw [kp.slot hL hi.scr hD (hi.sl v hv') hnot,hi.val v hv']

theorem fixedLoadEnv_point {K : WinCfg} {C : Curve} {E : Nat → Fe C} {x y : Nat}
    (hn : 0<K.M.n) (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hOne : toM C.p (2^(64*K.M.n)) K.one=1) {P : Point C}
    (hp : InvJ C (toM C.p (2^(64*K.M.n)) x) (toM C.p (2^(64*K.M.n)) y) 1 P) :
    InvJ C (fixedLoadEnv K C.p E x y K.E.x) (fixedLoadEnv K C.p E x y K.E.y)
      (fixedLoadEnv K C.p E x y K.E.z) P ∧ fixedLoadEnv K C.p E x y K.E.z=1 := by
  have hyx : K.E.y≠K.E.x := by omega
  have hzx : K.E.z≠K.E.x := by omega
  have hzy : K.E.z≠K.E.y := by omega
  simpa only [fixedLoadEnv,ite_true,hyx,hzx,hzy,ite_false,hOne,and_true] using hp

end VG.Proof.Weierstrass.X86_64
