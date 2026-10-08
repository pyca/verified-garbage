import VerifiedGarbage.Proof.Weierstrass.X86.NafShiftWord

/-! The public scalar's nine-word residual is divided by two in place. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem nafShift_arith (j V s t : Nat) (hV : V<2^(32*j)) :
    ((V+2^(32*j)*s+2^(32*j)*2^32*t)/2)%(2^(32*j)*2^32) =
      ((V+2^(32*j)*s)/2)%2^(32*j)+2^(32*j)*((s/2+2^31*t)%2^32) := by
  generalize 2^(32*j)=A at *
  have hA0 : 0<A := by omega
  have e1 : A*2^32*t=2*(A*(2^31*t)) := by
    rw [show (2:Nat)^32=2*2^31 from rfl,Nat.mul_comm A,Nat.mul_assoc,
      Nat.mul_assoc,Nat.mul_left_comm A]
  have e2 : (V+A*s)/A=s := by
    rw [Nat.add_mul_div_left _ _ hA0,Nat.div_eq_of_lt hV,Nat.zero_add]
  rw [e1,Nat.add_mul_div_left _ _ (by decide),Nat.mod_mul,Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ hA0,Nat.div_div_eq_div_mul,Nat.mul_comm 2,
    ←Nat.div_div_eq_div_mul,e2]

theorem nafShiftRows_ok {s : State} {base : Addr} {size work n : Nat}
    (hs : Scr s base size) (ha : work+4*n≤size) :
    ∀ j, j+1≤n → WP isa (.block ((List.range j).flatMap (Naf.shiftWord work))) s fun u =>
      val32 u.mem base work j=val32 s.mem base work (j+1)/2%2^(32*j) ∧
      Keeps [.eax,.edx] s u ∧ Outside base work (4*j) s.mem u.mem
  | 0, _ => WP.block_nil ⟨by simp only [val32,Nat.mul_zero,Nat.pow_zero,Nat.mod_one],
      Keeps.refl _ _,Outside.refl _ _ _ _⟩
  | j+1, hj => by
    have hn := hs.nowrap
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,WP.block_append_iff]
    refine WP.mono (nafShiftRows_ok hs ha j (by omega)) fun s₁ ⟨V₁,K₁,O₁⟩ => ?_
    refine WP.mono (nafShiftWord_ok (hs.of_keeps K₁ (by decide)) (by omega))
      fun u ⟨V₂,K₂,O₂⟩ => ⟨?_,K₁.trans K₂,?_⟩
    · rw [val32_succ,O₂.val32 (by omega) (by omega),V₁,V₂,
        O₁.w32 (by omega) (by omega),O₁.w32 (by omega) (by omega),
        val32_succ s.mem base work (j+1),val32_succ s.mem base work j,pow32_succ,
        Nat.mul_comm (2^32) (2^(32*j))]
      exact (nafShift_arith j _ _ _ (val32_lt _ _ _ _)).symm
    · intro x hx
      rw [O₂ x (by omega),O₁ x (by omega)]

theorem nafShiftTop_ok {s : State} {base : Addr} {size work : Nat}
    (hs : Scr s base size) (ha : work+36≤size) :
    WP isa (.block [.mov .eax (.mem (sc (work+32))),.shift .shr .eax 1,
      .store (sc (work+32)) .eax]) s fun u =>
      w32 u.mem base (work+32)=w32 s.mem base (work+32)/2 ∧
      Keeps [.eax] s u ∧ Outside base (work+32) 4 s.mem u.mem := by
  have hn := hs.nowrap
  refine wp_movS (readSrc_sc hs (by omega)) fun s₁ U₁ _ => ?_
  refine wp_shr (by decide) fun s₂ U₂ _ => ?_
  have K := U₁.keeps.trans U₂.keeps
  have hs₂ := hs.of_keeps K (by decide)
  refine wp_storeS (hs₂.ea (by omega)) (hs₂.write (by omega)) fun u U₃ => WP.block_nil
    ⟨?_,K.trans (U₃.keeps _),?_⟩
  · rw [U₃.mem,w32_write_self,U₂.gpr,U₁.gpr,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  · rw [U₃.mem,U₂.mem,U₁.mem]
    exact writeW32_outside _ _ _ (by omega)

theorem nafShift_ok {s : State} {base : Addr} {size work : Nat}
    (hs : Scr s base size) (ha : work+36≤size) :
    WP isa (.block (Naf.shift work)) s fun u =>
      val32 u.mem base work 9=val32 s.mem base work 9/2 ∧
      Keeps [.eax,.edx] s u ∧ Outside base work 36 s.mem u.mem := by
  have hn := hs.nowrap
  rw [Naf.shift,WP.block_append_iff]
  refine WP.mono (nafShiftRows_ok (n := 9) hs ha 8 (by decide)) fun s₁ ⟨V₁,K₁,O₁⟩ => ?_
  refine WP.mono (nafShiftTop_ok (hs.of_keeps K₁ (by decide)) ha)
    fun u ⟨V₂,K₂,O₂⟩ => ⟨?_,K₁.trans (K₂.mono (by decide)),?_⟩
  · rw [val32_succ,O₂.val32 (by omega) (by omega),V₁,V₂,O₁.w32 (by omega) (by omega)]
    have E := val32_succ s.mem base work 8
    have H := val32_lt s.mem base work 8
    simp only [Nat.reduceAdd,Nat.reduceMul] at E ⊢
    omega
  · exact (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))

end VG.Proof.Weierstrass.X86
