import VerifiedGarbage.Proof.Weierstrass.X86.NafPrepStep

/-! The bounded public recoding loop produces all 257 width-five NAF digits. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Weierstrass.X86 VG.Proof.Mont.X86 VG.Proof.Mont

theorem nafPrep_ok {s : State} {base : Addr} {size src bits work : Nat}
    (hs : Scr s base size) (hsrc : src+32≤size) (hb : bits+257≤size)
    (hw : work+36≤size) (hsrcWork : work≤src ∨ src+32≤work)
    (hsep : bits+257≤work ∨ work+36≤bits) :
    WP isa (Naf.prep bits src work) s fun t =>
      NafPrepState base size bits work (val32 s.mem base src 8) 257 t ∧
      Keeps nafPrepClob s t ∧ Outs base (nafPrepWrites bits work) s.mem t.mem := by
  let k := val32 s.mem base src 8
  have hk : k<2^256 := val32_lt ..
  let I (m : Nat) (t : State) := NafPrepState base size bits work k (257-m) t ∧
    Keeps nafPrepClob s t ∧ Outs base (nafPrepWrites bits work) s.mem t.mem
  rw [Naf.prep]
  refine WP.seq (WP.mono (nafInit_ok hs hsrc hw hsrcWork) fun a ⟨va,ca,ka,oa⟩ => ?_)
  have ha : NafPrepState base size bits work k 0 a :=
    ⟨hs.of_keeps ka (by decide),va,ca,fun i hi => by omega⟩
  refine WP.loop (M:=isa) (fun m t => 1≤m ∧ m≤257 ∧ I m t) (fun m t ⟨hm,hm',hi⟩ => ?_)
    257 a ⟨by decide,by decide,ha,ka.mono (by decide),?_⟩
  · have hj : 257-m<257 := by omega
    have hv : Naf5.residual k (257-m)≤2^256 := by
      have h := Naf5.residual_bound (Nat.le_of_lt hk) (j:=257-m) (by omega)
      have hp : 2^(256-(257-m))≤2^256 := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.le_trans h hp
    refine WP.mono (nafPrepStep_ok hi.1 hb hw hsep hj hv) fun u ⟨hu,cf,ku,ou⟩ => ?_
    have ki := hi.2.1.trans ku
    have oi := hi.2.2.trans ou
    by_cases hm1 : m=1
    · subst m
      exact Or.inl ⟨cf,hu,ki,oi⟩
    · refine Or.inr ⟨?_,m-1,by omega,by omega,by omega,?_,ki,oi⟩
      · change u.cf=some true
        rw [cf]; exact congrArg some (decide_eq_true (by omega))
      · rw [show 257-(m-1)=257-m+1 from by omega]
        exact hu
  · exact Outs.of_outside oa (by simp [nafPrepWrites])

end VG.Proof.Weierstrass.X86
