module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInvariant
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Mont.X86_64.Wide
public import VerifiedGarbage.Proof.Weierstrass.CombLay
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Impl.Ecdsa.X86_64
public import VerifiedGarbage.Impl.Mont.Mod
public import VerifiedGarbage.Impl.Weierstrass.Slots
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86_64.MulPX
public import VerifiedGarbage.Proof.Mont.X86_64.OpsReg
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
public import VerifiedGarbage.Proof.X25519.X86_64.Step
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Weierstrass.JacAdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCache
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafDigitRead
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafState
public import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCache

/-! ### `Weierstrass.X86_64.NafCachePoint`, which only this module used -/

section

/-! A public cache lookup preserves the point and its Z²/Z³ relationships. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Impl.Weierstrass VG.Proof.Mont.X86_64 VG.Proof.Mont Spec.Weierstrass

def cachedSlots (n : Nat) (p : Pt) (dst : Nat) : List Nat := jacCoords p++[dst,dst+8*n]

end VG.Proof.Weierstrass.X86_64

end

end

/-! ### `Weierstrass.X86_64.NafCacheEntryPoint`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.X86_64.NafCacheNeg`, which this module and modules that import it used -/

section

/-! Negating a selected point leaves its cached powers of Z unchanged. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

def CachedPoint (n : Nat) (C : Curve) (E : Nat → Fe C) (p : Pt) (dst : Nat) (P : Point C) : Prop :=
  InvJ C (E p.x) (E p.y) (E p.z) P ∧ E dst=E p.z*E p.z ∧ E (dst+8*n)=E dst*E p.z

theorem CachedPoint.to_tmv {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv M base size C.p Sl V E s) {p : Pt} {dst : Nat} {P : Point C}
    (hV : ∀ x∈cachedSlots M.n p dst,x∈V) (hP : CachedPoint M.n C E p dst P) :
    CachedPoint M.n C (tmv C M.n base s) p dst P := by
  unfold CachedPoint tmv
  rw [hI.val _ (hV _ (by simp [cachedSlots,jacCoords])),
    hI.val _ (hV _ (by simp [cachedSlots,jacCoords])),
    hI.val _ (hV _ (by simp [cachedSlots,jacCoords])),
    hI.val _ (hV _ (by simp [cachedSlots])),hI.val _ (hV _ (by simp [cachedSlots]))]
  exact hP

end VG.Proof.Weierstrass.X86_64

end

end

/-! ### `Weierstrass.X86_64.NafCacheEntryFields`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.X86_64.NafCacheFields`, which only this module used -/

section

/-! Exact field values after a public lookup of a point and its cached powers. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Impl.Weierstrass VG.Proof.Mont.X86_64 VG.Proof.Mont Spec.Weierstrass

def cachedTransferEnv {F : Type _} (n : Nat) (E : Nat → F) (o q : Pt) (dst src x : Nat) : F :=
  if x=o.x then E q.x else if x=o.y then E q.y else if x=o.z then E q.z
  else if x=dst then E src else if x=dst+8*n then E (src+8*n) else E x

theorem Inv.transferCachedFields {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    {o q : Pt} {dst src : Nat} (hy : o.y=o.x+8*M.n) (hz : o.z=o.x+16*M.n)
    {V : List Nat} {E : Nat → Fin m} {s t : State}
    (hI : Inv M base size m Sl V E s)
    (hD : ∀ x∈cachedSlots M.n o dst,Sl x) (hQ : ∀ x∈cachedSlots M.n q src,x∈V)
    (vx : wordsVal t.mem base o.x M.n=wordsVal s.mem base q.x M.n)
    (vy : wordsVal t.mem base o.y M.n=wordsVal s.mem base q.y M.n)
    (vz : wordsVal t.mem base o.z M.n=wordsVal s.mem base q.z M.n)
    (v2 : wordsVal t.mem base dst M.n=wordsVal s.mem base src M.n)
    (v3 : wordsVal t.mem base (dst+8*M.n) M.n=wordsVal s.mem base (src+8*M.n) M.n)
    (hk : KeepRegs [.rax,.rcx,.rdx] s t)
    (ho : ∀ x,(ofs base x<o.x ∨ o.x+24*M.n≤ofs base x) →
      (ofs base x<dst ∨ dst+16*M.n≤ofs base x) → t.mem x=s.mem x)
    : ProgKeep M base (cachedSlots M.n o dst) s t ∧
    Inv M base size m Sl (cachedSlots M.n o dst++V) (cachedTransferEnv M.n E o q dst src) t := by
  have kp : ProgKeep M base (cachedSlots M.n o dst) s t := by
    refine ⟨fun r hr => hk.gpr r (fun hh => hr ?_),hk.rd,hk.wr,fun x hx _ => ho x ?_ ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl|rfl|rfl <;> simp [clob]
    · have hx0 := hx o.x (by simp [cachedSlots,jacCoords])
      have hx1 := hx o.y (by simp [cachedSlots,jacCoords])
      have hx2 := hx o.z (by simp [cachedSlots,jacCoords])
      rw [hy] at hx1
      rw [hz] at hx2
      omega_using [hx0, hx1, hx2]
    · have hx0 := hx dst (by simp [cachedSlots])
      have hx1 := hx (dst+8*M.n) (by simp [cachedSlots])
      omega_using [hx0, hx1]
  have hlt : ∀ x∈cachedSlots M.n o dst,wordsVal t.mem base x M.n<m := by
    intro x hx
    simp only [cachedSlots,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with (rfl|rfl|rfl)|(rfl|rfl)
    · rw [vx]; exact hI.lt _ (hQ _ (by simp [cachedSlots,jacCoords]))
    · rw [vy]; exact hI.lt _ (hQ _ (by simp [cachedSlots,jacCoords]))
    · rw [vz]; exact hI.lt _ (hQ _ (by simp [cachedSlots,jacCoords]))
    · rw [v2]; exact hI.lt _ (hQ _ (by simp [cachedSlots]))
    · rw [v3]; exact hI.lt _ (hQ _ (by simp [cachedSlots]))
  have hi := hI.of_progKeep hL kp hD hlt
  refine ⟨kp,{hi with val := ?_}⟩
  intro x hx
  simp only [cachedTransferEnv]
  split
  · subst x
    rw [vx,hI.val _ (hQ _ (by simp [cachedSlots,jacCoords]))]
  · split
    · subst x
      rw [vy,hI.val _ (hQ _ (by simp [cachedSlots,jacCoords]))]
    · split
      · subst x
        rw [vz,hI.val _ (hQ _ (by simp [cachedSlots,jacCoords]))]
      · split
        · subst x
          rw [v2,hI.val _ (hQ _ (by simp [cachedSlots]))]
        · split
          · subst x
            rw [v3,hI.val _ (hQ _ (by simp [cachedSlots]))]
          · have hnot : x∉cachedSlots M.n o dst := by
              simp_all only [cachedSlots,jacCoords,List.mem_append,List.mem_cons,
                List.not_mem_nil,or_false,not_false_eq_true,false_or]
            have hv : x∈V := (List.mem_append.mp hx).resolve_left hnot
            rw [kp.slot hL hI.scr hD (hI.sl x hv) hnot,hI.val x hv]

theorem nafCachedFields_ok {K : WinCfg} {base : Addr} {size tbl dst a m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6 ∨ K.M.n=9)
    (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv K.M base size m Sl V E s)
    (h8 : s.gpr .r8=BitVec.ofNat 64 a) (ha : 1≤a) (ha' : a≤15) (hodd : a%2=1)
    (hp : K.tbl<2^31) (hc : tbl<2^31)
    (hP : K.tbl+192*K.M.n≤size) (hC : tbl+128*K.M.n≤size)
    (hD : ∀ x∈cachedSlots K.M.n K.E dst,Sl x)
    (hQ : ∀ x∈cachedSlots K.M.n (K.tblPt ((a-1)/2+1)) (tbl+16*K.M.n*((a-1)/2)),x∈V)
    (hEP : K.E.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.E.x)
    (hEC : K.E.x+24*K.M.n≤tbl ∨ tbl+128*K.M.n≤K.E.x)
    (hDC : dst+16*K.M.n≤tbl ∨ tbl+128*K.M.n≤dst)
    (hDE : dst+16*K.M.n≤K.E.x ∨ K.E.x+24*K.M.n≤dst)
    : WP isa (.block (Naf.cachedEntry K tbl dst)) s fun t =>
      ProgKeep K.M base (cachedSlots K.M.n K.E dst) s t ∧
      Inv K.M base size m Sl (cachedSlots K.M.n K.E dst++V)
        (cachedTransferEnv K.M.n E K.E (K.tblPt ((a-1)/2+1)) dst (tbl+16*K.M.n*((a-1)/2))) t := by
  have hez := hL.le K.E.z (hD _ (by simp [cachedSlots,jacCoords]))
  have hd3 := hL.le (dst+8*K.M.n) (hD _ (by simp [cachedSlots]))
  rw [hz] at hez
  refine WP.mono (nafCachedEntry_ok hI.scr h8 ha ha' hodd hn hp hc hP hC
    (by omega_using [hez]) (by omega_using [hd3]) hEP hEC hDC hDE) fun t ⟨vp,vc,hk,ho⟩ =>
      hI.transferCachedFields hL hy hz hD hQ ?_ ?_ ?_ ?_ ?_ hk ho
  · simpa only [WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_zero,Nat.add_zero] using vp 0 (by decide)
  · simpa only [hy,WinCfg.tblPt,Nat.add_sub_cancel,Nat.mul_one] using vp 1 (by decide)
  · simpa only [hz,WinCfg.tblPt,Nat.add_sub_cancel,show 8*K.M.n*2=16*K.M.n by omega_using []]
      using vp 2 (by decide)
  · simpa only [Nat.mul_zero,Nat.add_zero] using vc 0 (by decide)
  · simpa only [Nat.mul_one] using vc 1 (by decide)

end VG.Proof.Weierstrass.X86_64

end

end


/-! Signed peer lookup keeps exact point coordinates and cached powers. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

def cachedEntryEnv (K : WinCfg) {m : Nat} [NeZero m] (E : Nat → Fin m)
    (tbl dst : Nat) (b : BitVec 8) : Nat → Fin m :=
  let e := cachedTransferEnv K.M.n E K.E (K.tblPt ((nafMagnitude b-1)/2+1))
    dst (tbl+16*K.M.n*((nafMagnitude b-1)/2))
  if b.toNat<128 then e else Function.update e K.E.y (-e K.E.y)

private theorem prefix_keep {M : Mod} {base : Addr} {W : List Nat} {s t : State}
    {rs : List Reg} (hk : Keeps rs s t) (hr : ∀ r∈rs,r∈clob M.n) :
    ProgKeep M base W s t :=
  ⟨fun r h => hk.1 r (fun h' => h (hr r h')),hk.2.2.1,hk.2.2.2,
    fun x _ _ => congrFun hk.2.1 x⟩

theorem nafSignedCachedFields_ok {K : WinCfg} {s : State} {base : Addr} {size tbl dst m : Nat}
    [NeZero m] {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m}
    (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6 ∨ K.M.n=9) (hm : UnitMod m (2^(64*K.M.n)))
    (hi : Inv K.M base size m Sl V E s) {b : BitVec 8}
    (ha : 1≤nafMagnitude b) (ha' : nafMagnitude b≤15) (hodd : nafMagnitude b%2=1)
    (h8 : s.gpr .r8=b.setWidth 64)
    (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hp : K.tbl<2^31) (hc : tbl<2^31)
    (hP : K.tbl+192*K.M.n≤size) (hC : tbl+128*K.M.n≤size)
    (hD : ∀ x∈cachedSlots K.M.n K.E dst,Sl x)
    (hQ : ∀ x∈cachedSlots K.M.n (K.tblPt ((nafMagnitude b-1)/2+1))
      (tbl+16*K.M.n*((nafMagnitude b-1)/2)),x∈V)
    (hEP : K.E.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.E.x)
    (hEC : K.E.x+24*K.M.n≤tbl ∨ tbl+128*K.M.n≤K.E.x)
    (hDC : dst+16*K.M.n≤tbl ∨ tbl+128*K.M.n≤dst)
    (hDE : dst+16*K.M.n≤K.E.x ∨ K.E.x+24*K.M.n≤dst)
    (hZero : K.zero∈V) (heZero : E K.zero=0) (hApart : K.zero∉cachedSlots K.M.n K.E dst) :
    WP isa (Naf.signedCachedEntry K tbl dst) s fun t =>
      ProgKeep K.M base (cachedSlots K.M.n K.E dst) s t ∧
      Inv K.M base size m Sl (cachedSlots K.M.n K.E dst++V) (cachedEntryEnv K E tbl dst b) t := by
  rw [Naf.signedCachedEntry]
  apply WP.seq
  refine WP.mono (nafSign_ok s h8) fun u ⟨hu,ku⟩ => ?_
  have iu := hi.of_keeps ku (by decide)
  have pu : ProgKeep K.M base (cachedSlots K.M.n K.E dst) s u := prefix_keep ku (by simp)
  have hu8 : u.gpr .r8=b.setWidth 64 := (ku.1 .r8 (by simp)).trans h8
  refine WP.ite (decide (b.toNat<128)) hu (fun hb => ?_) (fun hb => ?_)
  · have hpos := of_decide_eq_true hb
    have hmag : u.gpr .r8=BitVec.ofNat 64 (nafMagnitude b) := by
      rw [hu8,nafMagnitude,ite_eq_left hpos]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    refine WP.mono (nafCachedFields_ok hL hn hy hz iu hmag ha ha' hodd hp hc hP hC hD hQ hEP hEC hDC hDE)
      fun t ⟨kt,it⟩ => ⟨pu.trans kt,?_⟩
    simpa only [cachedEntryEnv,ite_eq_left hpos] using it
  · have hneg := of_decide_eq_false hb
    rw [List.append_assoc,WP.block_append_iff]
    refine WP.mono (nafAbs_ok u hu8) fun v ⟨hv,kv⟩ => ?_
    have iv := iu.of_keeps kv (by decide)
    have pv : ProgKeep K.M base (cachedSlots K.M.n K.E dst) u v := prefix_keep kv (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl <;> simp [clob,acc])
    rw [WP.block_append_iff]
    refine WP.mono (nafCachedFields_ok hL hn hy hz iv
      (by rw [nafMagnitude,ite_eq_right hneg]; exact hv) ha ha' hodd hp hc hP hC hD hQ hEP hEC hDC hDE)
      fun w ⟨kw,iw⟩ => ?_
    have hz0 : cachedTransferEnv K.M.n E K.E (K.tblPt ((nafMagnitude b-1)/2+1)) dst (tbl+16*K.M.n*((nafMagnitude b-1)/2)) K.zero=0 := by
      simp only [cachedSlots,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at hApart
      simp only [cachedTransferEnv,hApart.1.1,hApart.1.2.1,hApart.1.2.2,
        hApart.2.1,hApart.2.2,ite_false,heZero]
    have sy : K.E.y∈cachedSlots K.M.n K.E dst++V := by simp [cachedSlots,jacCoords]
    have sz : K.zero∈cachedSlots K.M.n K.E dst++V := List.mem_append_right _ hZero
    have hs : ∀ v∈(FOp.sub K.E.y K.zero K.E.y).out::(FOp.sub K.E.y K.zero K.E.y).ins,Sl v := by
      intro v hv
      simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl|rfl|rfl
      · exact iw.sl _ sy
      · exact iw.sl _ sz
      · exact iw.sl _ sy
    have hr : ∀ v∈(FOp.sub K.E.y K.zero K.E.y).ins,v∈cachedSlots K.M.n K.E dst++V := by
      intro v hv
      simp only [FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl|rfl
      · exact sz
      · exact sy
    refine WP.mono (fop_ok hL hm iw hs hr) fun t ⟨kt,it⟩ => ?_
    refine ⟨(pu.trans pv).trans (kw.trans (progKeep_of_op kt (by simp [cachedSlots,jacCoords,FOp.out]))),?_⟩
    have ie := it.sub (fun v hv => List.mem_cons_of_mem _ hv)
    simpa only [cachedEntryEnv,ite_eq_right hneg,FOp.run,hz0,
      show (0 : Fin m)-cachedTransferEnv K.M.n E K.E (K.tblPt ((nafMagnitude b-1)/2+1)) dst (tbl+16*K.M.n*((nafMagnitude b-1)/2)) K.E.y = -cachedTransferEnv K.M.n E K.E (K.tblPt ((nafMagnitude b-1)/2+1)) dst (tbl+16*K.M.n*((nafMagnitude b-1)/2)) K.E.y from by grind] using ie

end VG.Proof.Weierstrass.X86_64

end

end

/-! The exact lookup environment preserves the point and its cached powers. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

theorem cachedTransferEnv_point {n : Nat} {C : Curve} {E : Nat → Fe C} {o q : Pt} {dst src : Nat}
    (hn : 0<n) (hy : o.y=o.x+8*n) (hz : o.z=o.x+16*n)
    (hDE : dst+16*n≤o.x ∨ o.x+24*n≤dst) {P : Point C}
    (hP : CachedPoint n C E q src P) :
    CachedPoint n C (cachedTransferEnv n E o q dst src) o dst P := by
  have hyx : o.y≠o.x := by omega_using [hn, hy]
  have hzx : o.z≠o.x := by omega_using [hn, hz]
  have hzy : o.z≠o.y := by omega_using [hy, hz, hyx]
  have hd : dst≠o.x ∧ dst≠o.y ∧ dst≠o.z := by omega_using [hy, hz, hDE, hyx]
  have hd' : dst+8*n≠o.x ∧ dst+8*n≠o.y ∧ dst+8*n≠o.z ∧ dst+8*n≠dst := by omega_using [hn, hy, hz, hDE]
  simpa only [CachedPoint,cachedTransferEnv,hyx,hzx,hzy,hd.1,hd.2.1,hd.2.2,
    hd'.1,hd'.2.1,hd'.2.2.1,hd'.2.2.2,ite_false,ite_true] using hP

theorem cachedEntryEnv_point {K : WinCfg} {C : Curve} {E : Nat → Fe C} {tbl dst : Nat}
    {b : BitVec 8} (hn : 0<K.M.n) (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hDE : dst+16*K.M.n≤K.E.x ∨ K.E.x+24*K.M.n≤dst) {P : Point C}
    (hP : CachedPoint K.M.n C E (K.tblPt ((nafMagnitude b-1)/2+1))
      (tbl+16*K.M.n*((nafMagnitude b-1)/2)) P) :
    CachedPoint K.M.n C (cachedEntryEnv K E tbl dst b) K.E dst
      (if b.toNat<128 then P else negPt P) := by
  have h := cachedTransferEnv_point hn hy hz hDE hP
  have hxy : K.E.x≠K.E.y := by omega_using [hn, hy]
  have hzy : K.E.z≠K.E.y := by omega_using [hy, hz, hxy]
  have hd : dst≠K.E.y := by omega_using [hy, hDE, hxy]
  have hd' : dst+8*K.M.n≠K.E.y := by omega_using [hn, hy, hDE]
  unfold cachedEntryEnv
  split
  · exact h
  · simp only [CachedPoint,Function.update_self,Function.update_of_ne hxy,
      Function.update_of_ne hzy,Function.update_of_ne hd,Function.update_of_ne hd']
    exact ⟨h.1.negY,h.2⟩

end VG.Proof.Weierstrass.X86_64

end

end

/-! ### `Weierstrass.X86_64.JointCachedPoint`, which only this module used -/

section

/-! The cached peer lookup represents a nonzero width-five digit of the joint sum. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

theorem jointCachedFast_ok {K : WinCfg} {s : State} {base : Addr} {size tbl dst u j : Nat}
    {C : Curve} {P : Point C}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C}
    (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6 ∨ K.M.n=9) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hi : Inv K.M base size C.p Sl V E s)
    (hmag : FastNaf.magnitude 5 u j≠0)
    (h8 : s.gpr .r8=(FastNaf.byte 5 u j).setWidth 64)
    (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hp : K.tbl<2^31) (hc : tbl<2^31)
    (hP : K.tbl+192*K.M.n≤size) (hC : tbl+128*K.M.n≤size)
    (hD : ∀ x∈cachedSlots K.M.n K.E dst,Sl x)
    (hQ : ∀ x∈cachedSlots K.M.n (K.tblPt ((FastNaf.magnitude 5 u j-1)/2+1))
      (tbl+16*K.M.n*((FastNaf.magnitude 5 u j-1)/2)),x∈V)
    (hEP : K.E.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.E.x)
    (hEC : K.E.x+24*K.M.n≤tbl ∨ tbl+128*K.M.n≤K.E.x)
    (hDC : dst+16*K.M.n≤tbl ∨ tbl+128*K.M.n≤dst)
    (hDE : dst+16*K.M.n≤K.E.x ∨ K.E.x+24*K.M.n≤dst)
    (hZero : K.zero∈V) (heZero : E K.zero=0) (hApart : K.zero∉cachedSlots K.M.n K.E dst)
    (hPoint : CachedPoint K.M.n C E (K.tblPt ((FastNaf.magnitude 5 u j-1)/2+1))
      (tbl+16*K.M.n*((FastNaf.magnitude 5 u j-1)/2)) (mul (FastNaf.magnitude 5 u j) P)) :
    WP isa (Naf.signedCachedEntry K tbl dst) s fun t =>
      ProgKeep K.M base (cachedSlots K.M.n K.E dst) s t ∧
      Inv K.M base size C.p Sl (cachedSlots K.M.n K.E dst++V)
        (cachedEntryEnv K E tbl dst (FastNaf.byte 5 u j)) t ∧
      CachedPoint K.M.n C (cachedEntryEnv K E tbl dst (FastNaf.byte 5 u j)) K.E dst
        (FastNaf.point C P 5 u j) := by
  have he : nafMagnitude (FastNaf.byte 5 u j)=FastNaf.magnitude 5 u j := FastNaf.byte_magnitude 5 u j
  have ha : 1≤nafMagnitude (FastNaf.byte 5 u j) := by rw [he]; omega_using [hmag]
  have ha' : nafMagnitude (FastNaf.byte 5 u j)≤15 := by
    rw [he]
    exact FastNaf.magnitude_le (Or.inl rfl) u j
  have hodd : nafMagnitude (FastNaf.byte 5 u j)%2=1 := by
    rw [he]
    exact (FastNaf.magnitude_odd_or_zero 5 u j).resolve_left hmag
  refine WP.mono (nafSignedCachedFields_ok hL hn hm hi ha ha' hodd h8 hy hz hp hc hP hC
    hD (by rw [he]; exact hQ) hEP hEC hDC hDE hZero heZero hApart) fun t ⟨kt,it⟩ => ?_
  have hpoint := cachedEntryEnv_point (E:=E) (b:=FastNaf.byte 5 u j) (by omega_using [hn]) hy hz hDE
    (by rw [he]; exact hPoint)
  have ep : (if (FastNaf.byte 5 u j).toNat<128 then mul (FastNaf.magnitude 5 u j) P
      else negPt (mul (FastNaf.magnitude 5 u j) P))=FastNaf.point C P 5 u j := by
    rw [FastNaf.point,←FastNaf.byte_negative 5 u j]
    by_cases h : (FastNaf.byte 5 u j).toNat<128
    · simp only [h,ite_true,show ¬128≤(FastNaf.byte 5 u j).toNat from by omega_using [h],decide_false,ite_false,Bool.false_eq_true]
    · simp only [h,ite_false,show 128≤(FastNaf.byte 5 u j).toNat from by omega_using [h],decide_true,ite_true]
  rw [ep] at hpoint
  exact ⟨kt,it,hpoint⟩

end VG.Proof.Weierstrass.X86_64

end

end


/-! Select a cached odd multiple while retaining the accumulator and both scalar streams. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

local macro "jslots" : tactic => `(tactic| plain_simp_names (simp only [jointSlots,jointLive,jointWork,
                   nafSlots,cachedSlots,jacCoords,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,
                   List.not_mem_nil,or_false] at * <;> grind))

structure JointLookupLayout (c : Joint.Cfg) (size : Nat) : Prop where
  layout : JointLayout c size
  exy : c.K.E.y=c.K.E.x+8*c.K.M.n
  exz : c.K.E.z=c.K.E.x+16*c.K.M.n
  tableSmall : c.K.tbl<2^31
  cacheSmall : c.cache<2^31
  tableBound : c.K.tbl+192*c.K.M.n≤size
  cacheBound : c.cache+128*c.K.M.n≤size
  entryTable : c.K.E.x+24*c.K.M.n≤c.K.tbl ∨ c.K.tbl+192*c.K.M.n≤c.K.E.x
  entryCache : c.K.E.x+24*c.K.M.n≤c.cache ∨ c.cache+128*c.K.M.n≤c.K.E.x
  selectedCache : c.selected+16*c.K.M.n≤c.cache ∨ c.cache+128*c.K.M.n≤c.selected
  selectedEntry : c.selected+16*c.K.M.n≤c.K.E.x ∨ c.K.E.x+24*c.K.M.n≤c.selected
  zeroApart : c.K.zero∉cachedSlots c.K.M.n c.K.E c.selected
  accumApart : ∀ x∈jacCoords c.K.R,x∉cachedSlots c.K.M.n c.K.E c.selected

theorem jointStable_live (c : Joint.Cfg) : ∀ x∈jointStableFields c,x∈jointLive c := by
  intro x hx
  simp only [jointStableFields,jointLive,List.mem_append] at hx ⊢
  grind

theorem jointKeeps_prog {M : Mod} {base : Addr} {W : List Nat} {s t : State}
    {rs : List Reg} (hk : Keeps rs s t) (hr : ∀ r∈rs,r∈clob M.n) :
    ProgKeep M base W s t :=
  ⟨fun r h => hk.1 r (fun h' => h (hr r h')),hk.2.2.1,hk.2.2.2,
    fun x _ _ => congrFun hk.2.1 x⟩

theorem jointCachedEntry_ok {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v j : Nat}
    {Q A : Point C} {External : State → Prop} {s : State}
    (hL : JointLookupLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (h : JointCore c C base size Q u v External A s)
    (hExternal : ∀ s t,ProgKeep c.K.M base (jointWork c) s t → t.syms=s.syms → External s → External t)
    (hmag : FastNaf.magnitude 5 v j≠0)
    (h8 : s.gpr .r8=(FastNaf.byte 5 v j).setWidth 64) :
    WP isa (Naf.signedCachedEntry c.K c.cache c.selected) s fun t =>
      ProgKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v External A t ∧
      Inv c.K.M base size C.p (·∈jointSlots c)
        (cachedSlots c.K.M.n c.K.E c.selected++jointLive c) (tmv C c.K.M.n base t) t ∧
      CachedPoint c.K.M.n C (tmv C c.K.M.n base t) c.K.E c.selected (FastNaf.point C Q 5 v j) := by
  have hl := FastNaf.magnitude_le (Or.inl rfl) v j
  have ho := (FastNaf.magnitude_odd_or_zero 5 v j).resolve_left hmag
  have ha : 1≤(FastNaf.magnitude 5 v j-1)/2+1 := by omega_using []
  have hb : (FastNaf.magnitude 5 v j-1)/2+1≤8 := by omega_using [hl]
  have hi : (FastNaf.magnitude 5 v j-1)/2<8 := by omega_using [hl]
  have he : 2*((FastNaf.magnitude 5 v j-1)/2+1)-1=FastNaf.magnitude 5 v j := by omega_using [ho]
  have hd : ∀ x∈cachedSlots c.K.M.n c.K.E c.selected,x∈jointSlots c := by intro x hx; jslots
  have hw : ∀ x∈cachedSlots c.K.M.n c.K.E c.selected,x∈jointWork c := by intro x hx; jslots
  have hq : ∀ x∈cachedSlots c.K.M.n (c.K.tblPt ((FastNaf.magnitude 5 v j-1)/2+1))
      (c.cache+16*c.K.M.n*((FastNaf.magnitude 5 v j-1)/2)),x∈jointLive c := by
    intro x hx
    apply jointStable_live c
    rcases List.mem_append.mp hx with hx|hx
    · exact jointStable_table c ha (by omega_using [hl]) hx
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl
      · exact jointStable_cache2 c hi
      · exact jointStable_cache3 c hi
  have hp : CachedPoint c.K.M.n C (tmv C c.K.M.n base s)
      (c.K.tblPt ((FastNaf.magnitude 5 v j-1)/2+1)) (c.cache+16*c.K.M.n*((FastNaf.magnitude 5 v j-1)/2))
      (mul (FastNaf.magnitude 5 v j) Q) := by
    refine ⟨?_,h.stable.cache2 _ hi,h.stable.cache3 _ hi⟩
    have ht := h.stable.table _ ha hb
    rw [he] at ht
    exact ht
  refine WP.mono_syms (jointCachedFast_ok hL.layout.lay hL.layout.n hm h.field hmag h8
    hL.exy hL.exz hL.tableSmall hL.cacheSmall hL.tableBound hL.cacheBound hd hq
    hL.entryTable hL.entryCache hL.selectedCache hL.selectedEntry
    (by simp [jointLive,winRo]) h.stable.zero hL.zeroApart hp) fun t ⟨kt,it,pt⟩ st => ?_
  have kw := kt.mono hw
  exact ⟨kw,h.of_write hL.layout kt hw hd hL.accumApart
    (it.sub (fun _ hx => List.mem_append_right _ hx)) (hExternal s t kw st h.external),
    it.to_tmv,pt.to_tmv it (fun _ hx => List.mem_append_left _ hx)⟩

end VG.Proof.Weierstrass.X86_64
