import VerifiedGarbage.Impl.Weierstrass.X86.NafPrep
import VerifiedGarbage.Proof.Mont.X86.Chain

/-! ## `NafShiftWord` -/

section

/-! One word of the public NAF residual's in-place right shift. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem nafRotateBit (x : BitVec 32) :
    ((x &&& (1 : BitVec 32)).rotateRight 1).toNat = 2^31*(x.toNat%2) := by
  have h : x &&& (1 : BitVec 32) = BitVec.ofNat 32 (x.toNat%2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and,BitVec.toNat_ofNat]
    change x.toNat &&& 1 = (x.toNat%2)%2^32
    rw [Nat.and_one_is_mod]
    omega
  rw [h]
  have hm : x.toNat%2=0 ∨ x.toNat%2=1 := by omega
  rcases hm with hm | hm <;> rw [hm] <;> rfl

theorem nafShiftWord_value (lo hi : BitVec 32) :
    (lo >>> 1 + (hi &&& (1 : BitVec 32)).rotateRight 1).toNat =
      (lo.toNat/2+2^31*hi.toNat)%2^32 := by
  rw [BitVec.toNat_add,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,nafRotateBit]
  omega

theorem nafShiftWord_ok {s : State} {base : Addr} {size work i : Nat}
    (hs : Scr s base size) (ha : work+4*(i+1)+4≤size) :
    WP isa (.block (Naf.shiftWord work i)) s fun u =>
      w32 u.mem base (work+4*i) =
        (w32 s.mem base (work+4*i)/2+2^31*w32 s.mem base (work+4*(i+1)))%2^32 ∧
      Keeps [.eax,.edx] s u ∧ Outside base (work+4*i) 4 s.mem u.mem := by
  have hn := hs.nowrap
  unfold Naf.shiftWord
  refine wp_movS (readSrc_sc hs (by omega)) fun s₁ U₁ _ => ?_
  refine wp_shr (by decide) fun s₂ U₂ _ => ?_
  have K₂ : Keeps [.eax,.edx] s s₂ :=
    (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  refine wp_movS (readSrc_sc (hs.of_keeps K₂ (by decide)) ha) fun s₃ U₃ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₄ U₄ => ?_
  refine wp_ror (by decide) fun s₅ U₅ => ?_
  refine wp_addS rfl fun s₆ U₆ _ => ?_
  have K : Keeps [.eax,.edx] s s₆ :=
    (((K₂.trans (U₃.keeps.mono (by decide))).trans (U₄.keeps.mono (by decide))).trans
      (U₅.keeps.mono (by decide))).trans (U₆.keeps.mono (by decide))
  have hs₆ := hs.of_keeps K (by decide)
  refine wp_storeS (hs₆.ea (by omega)) (hs₆.write (by omega)) fun u U₇ => WP.block_nil ?_
  refine ⟨?_,K.trans (U₇.keeps _),?_⟩
  · rw [U₇.mem,w32_write_self,U₆.gpr,U₅.other _ (by decide),U₄.other _ (by decide),
      U₃.other _ (by decide),U₂.gpr,U₁.gpr,U₅.gpr,U₄.gpr,U₃.gpr,U₂.mem,U₁.mem]
    exact nafShiftWord_value _ _
  · rw [U₇.mem,U₆.mem,U₅.mem,U₄.mem,U₃.mem,U₂.mem,U₁.mem]
    exact writeW32_outside _ _ _ (by omega)

end VG.Proof.Weierstrass.X86

end

/-! ## `NafShift` -/

section

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

end

/-! ## `NafSubWord` -/

section

/-! Subtracting a register from one word of the public NAF residual. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem nafSubWord_ok {s : State} {base : Addr} {size work i : Nat}
    (hs : Scr s base size) (ha : work+4*i+4≤size) {r : Reg} (hr : r≠.eax)
    {op : AluOp} {cin : Bool}
    (hop : (op=.sub ∧ cin=false) ∨ (op=.sbb ∧ s.cf=some cin)) :
    WP isa (.block (Naf.subWord op work i r)) s fun u =>
      Outside base (work+4*i) 4 s.mem u.mem ∧
      (∃ c, u.cf=some c ∧ w32 u.mem base (work+4*i)+(s.gpr r).toNat+cin.toNat =
        w32 s.mem base (work+4*i)+2^32*c.toNat) ∧ Keeps [.eax] s u := by
  have hn := hs.nowrap
  unfold Naf.subWord
  refine wp_movS (readSrc_sc hs ha) fun s₁ u₁ cf₁ => ?_
  have hs₁ := hs.of_keeps u₁.keeps (by decide)
  have hx := (s.mem.readW (off base (work+4*i)) 32).isLt
  have hy := (s.gpr r).isLt
  rcases hop with ⟨rfl,rfl⟩ | ⟨rfl,hc⟩
  · refine wp_subS rfl fun s₂ u₂ c₂ => ?_
    have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
    refine wp_storeS (hs₂.ea (by omega)) (hs₂.write ha) fun u m => WP.block_nil
      ⟨?_,⟨_,by rw [m.cf,c₂],?_⟩,(u₁.keeps.trans u₂.keeps).trans (m.keeps _)⟩
    · rw [m.mem,u₂.mem,u₁.mem]; exact writeW32_outside _ _ _ (by omega)
    · rw [m.mem,w32_write_self,u₂.gpr,sub_toNat,u₁.gpr,u₁.other _ hr]
      simp only [w32,Bool.toNat_false]
      by_cases h : (s.mem.readW (off base (work+4*i)) 32).toNat < (s.gpr r).toNat <;>
        simp only [h,decide_true,decide_false,Bool.toNat_true,Bool.toNat_false] <;> omega
  · refine wp_sbbS rfl (by rw [cf₁]; exact hc) fun s₂ u₂ c₂ => ?_
    have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
    refine wp_storeS (hs₂.ea (by omega)) (hs₂.write ha) fun u m => WP.block_nil
      ⟨?_,⟨_,by rw [m.cf,c₂],?_⟩,(u₁.keeps.trans u₂.keeps).trans (m.keeps _)⟩
    · rw [m.mem,u₂.mem,u₁.mem]; exact writeW32_outside _ _ _ (by omega)
    · rw [m.mem,w32_write_self,u₂.gpr,sub3_toNat,u₁.gpr,u₁.other _ hr]
      simp only [w32]
      have := Bool.toNat_le cin
      by_cases h : (s.mem.readW (off base (work+4*i)) 32).toNat < (s.gpr r).toNat+cin.toNat <;>
        simp only [h,decide_true,decide_false,Bool.toNat_true,Bool.toNat_false] <;> omega

end VG.Proof.Weierstrass.X86

end

/-! ## `NafSubChain` -/

section

/-! Borrow propagation through the public scalar's scratch words. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Weierstrass.X86 VG.Proof.Mont.X86 VG.Proof.Mont

/-- Low word followed by k copies of a sign-extension word. -/
def nafDigitVal (d e : BitVec 32) : Nat → Nat
  | 0 => d.toNat
  | k+1 => nafDigitVal d e k + 2^(32*(k+1))*e.toNat

theorem nafSubChain_ok {s : State} {base : Addr} {size work : Nat}
    (hs : Scr s base size) : ∀ k, work+4*(k+1)≤size →
    WP isa (.block (Naf.subWord .sub work 0 .ecx ++
      (List.range k).flatMap fun i => Naf.subWord .sbb work (i+1) .edx)) s fun u =>
      Outside base work (4*(k+1)) s.mem u.mem ∧
      (∃ c, u.cf=some c ∧ val32 u.mem base work (k+1)+nafDigitVal (s.gpr .ecx) (s.gpr .edx) k =
        val32 s.mem base work (k+1)+2^(32*(k+1))*c.toNat) ∧ Keeps [.eax] s u
  | 0, ha => by
    simp only [List.range_zero,List.flatMap_nil,List.append_nil]
    refine WP.mono (nafSubWord_ok hs (by omega) (by decide) (.inl ⟨rfl,rfl⟩))
      fun u ⟨O,⟨c,hc,V⟩,K⟩ => ⟨by simpa using O,⟨c,hc,?_⟩,K⟩
    simpa only [val32,nafDigitVal,Nat.mul_zero,Nat.add_zero,Bool.toNat_false] using V
  | k+1, ha => by
    have hn := hs.nowrap
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,←List.append_assoc,
      WP.block_append_iff]
    refine WP.mono (nafSubChain_ok hs k (by omega)) fun s₁ ⟨O₁,⟨c₁,hc₁,V₁⟩,K₁⟩ => ?_
    refine WP.mono (nafSubWord_ok (hs.of_keeps K₁ (by decide)) ha (by decide) (.inr ⟨rfl,hc₁⟩))
      fun u ⟨O,⟨c,hc,V⟩,K⟩ => ⟨?_,⟨c,hc,?_⟩,K₁.trans K⟩
    · exact (O₁.mono (Nat.le_refl _) (by omega)).trans (O.mono (by omega) (by omega))
    · rw [O₁.w32 (d := work+4*(k+1)) (by omega) (by omega),K₁.1 .edx (by decide)] at V
      rw [val32_succ u.mem base work (k+1),val32_succ s.mem base work (k+1),
        O.val32 (by omega) (by omega),nafDigitVal,pow32_succ (k+1)]
      generalize 2^(32*(k+1))=P at *
      grind

end VG.Proof.Weierstrass.X86

end
