import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.DoubleCount
import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfPublic
import VerifiedGarbage.Proof.Weierstrass.Comb

/-! Five in-place doublings with unconditional field execution and conditional point correctness. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.P256.X86_64 VG.Impl.P256.X86_64 Spec.Weierstrass

theorem dbl_self_ok {K : WinCfg} {base : Addr} {size : Nat} {Sl : Nat → Prop}
    (hn : K.M.n=4) (hL : Lay K.M size Sl) (hm : UnitMod Spec.P256.p (2^(64*K.M.n)))
    (hC : Law Spec.P256.curve) (ha : AM3 Spec.P256.curve)
    (hd : (doubleSlots K.S K.R).Nodup) (hSl : ∀ x∈doubleSlots K.S K.R,Sl x)
    {V : List Nat} {E : Nat → Fin Spec.P256.p} {s : State}
    (hI : Inv K.M base size Spec.P256.p Sl V E s)
    (hV : ∀ x∈[K.R.x,K.R.y,K.R.z],x∈V)
    {valid : Prop} {P : Point Spec.P256.curve} (hP : valid → onCurve Spec.P256.curve P=true)
    (hJ : valid → InvJ Spec.P256.curve (E K.R.x) (E K.R.y) (E K.R.z) P) :
    WP isa (Impl.Ecdh.X86_64.Window5.dbl K K.R K.R) s fun t =>
      ProgKeep K.M base (doubleSlots K.S K.R) s t ∧
      Inv K.M base size Spec.P256.p Sl V (doubleHalfEnv K.S K.R E) t ∧
      (valid → InvJ Spec.P256.curve (doubleHalfEnv K.S K.R E K.R.x)
        (doubleHalfEnv K.S K.R E K.R.y) (doubleHalfEnv K.S K.R E K.R.z) (Spec.Weierstrass.add P P)) := by
  simp only [Impl.Ecdh.X86_64.Window5.dbl,BEq.rfl,Bool.and_self,ite_true]
  apply WP.seq
  apply WP.block_nil
  refine WP.mono (doubleHalfPublic_fields_ok hn hL hm hSl hI hV) fun t ⟨kt,it⟩ => ?_
  exact ⟨kt,it.sub (fun _ hx => List.mem_append_right _ hx),fun hv =>
    InvJ.dbl' hC ha (hP hv) (hJ hv) (doubleHalfEnv_run K.S K.R E hd)⟩

theorem doubles_ok {K : WinCfg} {base : Addr} {size j : Nat} {Sl : Nat → Prop}
    (hn : K.M.n=4) (hL : Lay K.M size Sl) (hm : UnitMod Spec.P256.p (2^(64*K.M.n)))
    (hC : Law Spec.P256.curve) (ha : AM3 Spec.P256.curve)
    (hd : (doubleSlots K.S K.R).Nodup) (hSl : ∀ x∈doubleSlots K.S K.R,Sl x)
    {V : List Nat} {E : Nat → Fin Spec.P256.p} {s : State}
    (hI : Inv K.M base size Spec.P256.p Sl V E s)
    (hV : ∀ x∈[K.R.x,K.R.y,K.R.z],x∈V)
    (hj : j<4096) (hc : s.gpr .rbx=BitVec.ofNat 64 j)
    {valid : Prop} {P : Point Spec.P256.curve} (hP : valid → onCurve Spec.P256.curve P=true)
    (hJ : valid → InvJ Spec.P256.curve (E K.R.x) (E K.R.y) (E K.R.z) P) :
    WP isa (Impl.Ecdh.X86_64.Window5.doubles K) s fun t =>
      ∃ E', ProgKeep K.M base (doubleSlots K.S K.R) s t ∧
      Inv K.M base size Spec.P256.p Sl V E' t ∧
      (valid → InvJ Spec.P256.curve (E' K.R.x) (E' K.R.y) (E' K.R.z) (mul 32 P)) := by
  rw [Impl.Ecdh.X86_64.Window5.doubles]
  apply WP.seq
  refine WP.mono (doubles_start_ok s hc) fun a ⟨ca,ka⟩ => ?_
  let I := fun m t => 1≤m ∧ m≤5 ∧ ∃ F : Nat → Fin Spec.P256.p,
    Inv K.M base size Spec.P256.p Sl V F t ∧
    (valid → InvJ Spec.P256.curve (F K.R.x) (F K.R.y) (F K.R.z) (mul (2^(5-m)) P)) ∧
    t.gpr .rbx=BitVec.ofNat 64 (j+4096*m) ∧ CounterKeep K.M base (doubleSlots K.S K.R) s t
  have ia : I 5 a := by
    refine ⟨by decide,by decide,E,hI.of_keeps ka (by decide),?_,ca,.of_keeps ka⟩
    intro hv
    simpa only [Nat.sub_self,Nat.pow_zero,mul_one_pt] using hJ hv
  refine WP.loop (M:=isa) I (fun m u ⟨hm1,hm5,F,iu,ju,cu,ku⟩ => ?_) 5 a ia
  apply WP.seq
  refine WP.mono (dbl_self_ok hn hL hm hC ha hd hSl iu hV
    (fun hv => hC.onCurve_mul (hP hv) _) ju) fun v ⟨kv,iv,jv⟩ => ?_
  have cv : v.gpr .rbx=BitVec.ofNat 64 (j+4096*m) :=
    (kv.gpr _ (by rw [hn]; decide)).trans cu
  refine WP.mono (doubles_tick_ok v hj hm1 hm5 cv) fun t ⟨ct,ft,kt⟩ => ?_
  have it := iv.of_keeps kt (by decide)
  have kst := ku.trans ((CounterKeep.of_progKeep kv).trans (.of_keeps kt))
  have jt : valid → InvJ Spec.P256.curve
      (doubleHalfEnv K.S K.R F K.R.x) (doubleHalfEnv K.S K.R F K.R.y)
      (doubleHalfEnv K.S K.R F K.R.z) (mul (2^(5-(m-1))) P) := by
    intro hv
    have hvj := jv hv
    have he : 5-(m-1)=(5-m)+1 := by omega
    have hp : 2^(5-m)+2^(5-m)=2^(5-(m-1)) := by
      rw [he,Nat.pow_succ]
      omega
    rw [hC.add_mul_mul (hP hv),hp] at hvj
    exact hvj
  by_cases hm0 : m=1
  · subst m
    have ctf : t.gpr .rbx=s.gpr .rbx := by
      simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero,hc] using ct
    refine Or.inl ⟨?_,_,kst.progKeep ctf,it,?_⟩
    · change t.cf.map (!·)=some false
      rw [ft]
      rfl
    · exact jt
  · refine Or.inr ⟨?_,m-1,by omega,by omega,by omega,_,it,jt,ct,kst⟩
    change t.cf.map (!·)=some true
    rw [ft]
    simp only [hm0,decide_false,Option.map_some,Bool.not_false]

end VG.Proof.Ecdh.X86_64.Secret
