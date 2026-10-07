import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLayout

/-! The even table entries load their already constructed half multiple. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem jacTreeAddress_ok (K : WinCfg) {s : State} {base : Addr} {a : Nat}
    (h0 : s.gpr .x0 = base) (h19 : s.gpr .x19 = BitVec.ofNat 64 (15-2*(a-1)))
    (ha : 1 ≤ a) (ha8 : a ≤ 8) (ht : K.tbl < 4096) :
    WP isa (.block [.movz .x .x17 15 0, .sub .x .x17 .x17 .x19,
      .lsr .x .x17 .x17 1, .movz .x .x2 96 0, .mul .x .x17 .x17 .x2,
      .addImm .x .x16 .x0 K.tbl, .add .x .x16 .x16 .x17]) s fun t =>
      t.gpr .x16 = off base (K.tbl+96*(a-1)) ∧ Keeps [.x2,.x16,.x17] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    BitVec.setWidth_eq,Size.bits,show 16*0<64 from by decide,show 1<64 from by decide,
    ht,ite_true,ite_false,reduceCtorEq,h0,h19,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · simp only [Nat.mul_zero,BitVec.shiftLeft_zero]
    have hs : (15 : BitVec 64) - BitVec.ofNat 64 (15-2*(a-1)) = BitVec.ofNat 64 (2*(a-1)) := by
      change BitVec.ofNat 64 15 - BitVec.ofNat 64 (15-2*(a-1)) = _
      rw [BitVec.ofNat_sub_ofNat_of_le 15 (15-2*(a-1)) (by omega) (by omega)]
      congr 1; omega
    change base + BitVec.ofNat 64 K.tbl + ((15 : BitVec 64) - BitVec.ofNat 64 (15-2*(a-1))) >>> 1 * 96 = _
    rw [hs]
    have hd : BitVec.ofNat 64 (2*(a-1)) >>> 1 = BitVec.ofNat 64 (a-1) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
      omega
    rw [hd]
    simp only [off,BitVec.ofNat_mul,BitVec.ofNat_add,BitVec.add_assoc]
    rw [BitVec.mul_comm]
    rfl
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]

theorem jacTreeFetchWords_ok (K : WinCfg) {s : State} {base : Addr} {size a : Nat}
    (hs : Scr s base size) (h19 : s.gpr .x19 = BitVec.ofNat 64 (15-2*(a-1)))
    (ha : 1 ≤ a) (ha8 : a ≤ 8) (ht : K.tbl < 4096)
    (hd : K.E.x+96 ≤ size) (hd8 : K.E.x%8=0)
    (htbl : K.tbl+96*(a-1)+96 ≤ size)
    (hap : K.E.x+96 ≤ K.tbl+96*(a-1) ∨ K.tbl+96*(a-1)+96 ≤ K.E.x) :
    WP isa (.block (Jacobian.jacTreeFetch K 16)) s fun t =>
      (∀ i < 12, word t.mem base (K.E.x+8*i) =
        word s.mem base (K.tbl+96*(a-1)+8*i)) ∧
      KeepRegs [.x2,.x4,.x16,.x17] s t ∧ Outside base K.E.x 96 s.mem t.mem := by
  rw [Jacobian.jacTreeFetch,WP.block_append_iff]
  refine WP.mono (jacTreeAddress_ok K hs.x0 h19 ha ha8 ht) fun s₁ ⟨h16,k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (jacWords_ok (n := 12) hs₁ h16 hd hd8 htbl hap 12 (Nat.le_refl _))
    fun t ⟨hv,hk,ho⟩ => ⟨?_,?_,?_⟩
  · simpa only [k₁.mem] using hv
  · exact ((Keeps.regs k₁).mono (by sub_regs)).trans (hk.mono (by sub_regs))
  · simpa only [k₁.mem] using ho

theorem jacTreeFetchPoint_ok {K : WinCfg} {base : Addr} {size a : Nat} {C : Spec.Weierstrass.Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hn : K.M.n=4) (hy : K.E.y=K.E.x+32) (hz : K.E.z=K.E.x+64)
    {V : List Nat} {E : Nat → Spec.Weierstrass.Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 (15-2*(a-1))) (ha : 1 ≤ a) (ha8 : a ≤ 8) (ht : K.tbl<4096)
    (hD : ∀ x ∈ [K.E.x,K.E.y,K.E.z], Sl x)
    (hT : ∀ x ∈ [(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z], x ∈ V)
    (hap : K.E.x+96 ≤ K.tbl+96*(a-1) ∨ K.tbl+96*(a-1)+96 ≤ K.E.x)
    {P : Spec.Weierstrass.Point C}
    (hJ : InvJ C (E (Jacobian.tablePt K a).x) (E (Jacobian.tablePt K a).y)
      (E (Jacobian.tablePt K a).z) P) :
    WP isa (.block (Jacobian.jacTreeFetch K 16)) s fun t =>
      ProgKeep K.M base [K.E.x,K.E.y,K.E.z] s t ∧
      Inv K.M base size C.p Sl ([K.E.x,K.E.y,K.E.z]++V) (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t K.E.x) (tmv C K.M.n base t K.E.y)
        (tmv C K.M.n base t K.E.z) P := by
  have hdz := hL.le K.E.z (hD _ (by simp))
  have htz := hL.le (Jacobian.tablePt K a).z (hI.sl _ (hT _ (by simp)))
  have hnw := hI.scr.nowrap
  rw [hn,hz] at hdz
  simp only [Jacobian.tablePt,hn] at htz
  refine WP.mono (jacTreeFetchWords_ok K hI.scr h19 ha ha8 ht (by omega)
    (hAl.sl _ (hD _ (by simp))) (by omega) hap) fun t ⟨hv,hk,ho⟩ => ?_
  have kp : ProgKeep K.M base [K.E.x,K.E.y,K.E.z] s t := by
    refine ⟨fun r hr => hk.gpr r (fun hh => hr ?_),hk.rd,hk.wr,hk.sp,fun x hx _ => ho x ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl | rfl | rfl | rfl <;> simp [clob]
    · have hx₀ := hx K.E.x (by simp)
      have hx₁ := hx K.E.y (by simp)
      have hx₂ := hx K.E.z (by simp)
      rw [hn] at hx₀ hx₁ hx₂
      rw [hy] at hx₁
      rw [hz] at hx₂
      omega
  have vx : wordsVal t.mem base K.E.x K.M.n = wordsVal s.mem base (Jacobian.tablePt K a).x K.M.n := by
    simpa only [hn,Jacobian.tablePt,Nat.mul_zero,Nat.add_zero] using jacWords_coord (c := 0) (by decide) hv
  have vy : wordsVal t.mem base K.E.y K.M.n = wordsVal s.mem base (Jacobian.tablePt K a).y K.M.n := by
    simpa only [hn,hy,Jacobian.tablePt,Nat.mul_one] using jacWords_coord (c := 1) (by decide) hv
  have vz : wordsVal t.mem base K.E.z K.M.n = wordsVal s.mem base (Jacobian.tablePt K a).z K.M.n := by
    simpa only [hn,hz,Jacobian.tablePt,show 32*2=64 from rfl] using jacWords_coord (c := 2) (by decide) hv
  have hlt : ∀ x ∈ [K.E.x,K.E.y,K.E.z], wordsVal t.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vx]; exact hI.lt _ (hT _ (by simp))
    · rw [vy]; exact hI.lt _ (hT _ (by simp))
    · rw [vz]; exact hI.lt _ (hT _ (by simp))
  refine ⟨kp,hI.of_progKeep hL kp hD hlt,?_⟩
  unfold tmv
  rw [vx,vy,vz,hI.val _ (hT _ (by simp)),hI.val _ (hT _ (by simp)),hI.val _ (hT _ (by simp))]
  exact hJ

end VG.Proof.Weierstrass.AArch64
