import VerifiedGarbage.Proof.Weierstrass.X86.InvHalf
import VerifiedGarbage.Proof.Weierstrass.X86.InvLoop
import VerifiedGarbage.Proof.Weierstrass.X86.InvState
import VerifiedGarbage.Proof.Divstep.Word32

/-! ## `InvStart` -/

section

/-! # Initializing the word matrix for a divstep batch -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem batchStart_ok {P : InvCfg} {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (ht : P.tbl + 320 ≤ size) :
    WP isa (.block P.batchStart) s fun u =>
      wordState u.mem base P.sW =
        ⟨s.mem.readW (off base P.sW) 32, s.mem.readW (off base P.sF) 32,
          s.mem.readW (off base P.sG) 32, 1, 0, 0, 1⟩ ∧
      Keeps [.eax] s u ∧ Outside base (P.sW + 4) 24 s.mem u.mem := by
  have hn := hs.nowrap
  have eW : P.sW = P.tbl + 288 := rfl
  have eF : P.sF = P.tbl := rfl
  have eG : P.sG = P.tbl + 36 := rfl
  unfold InvCfg.batchStart
  refine WP.block_append (WP.block_append (WP.mono
    (copy_ok 1 hs (o := P.sW + 4) (a := P.sF) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₁ ⟨F₁, K₁, O₁⟩ => ?_))
  simp only [val32, Nat.mul_zero, Nat.add_zero] at F₁
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (copy_ok 1 hs₁ (o := P.sW + 8) (a := P.sG) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₂ ⟨G₂, K₂, O₂⟩ => ?_
  simp only [val32, Nat.mul_zero, Nat.add_zero] at G₂
  rw [O₁.w32 (by omega_arith) (by omega_arith)] at G₂
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (setMatrix_ok hs₂ (dst := P.sW + 12) (by omega_arith))
    fun u ⟨U, V, Q, R, K₃, O₃⟩ => ⟨?_, (K₁.trans K₂).trans K₃, ?_⟩
  · have D : w32 u.mem base P.sW = w32 s.mem base P.sW := by
      rw [O₃.w32 (by omega_arith) (by omega_arith), O₂.w32 (by omega_arith) (by omega_arith), O₁.w32 (by omega_arith) (by omega_arith)]
    have F : w32 u.mem base (P.sW + 4) = w32 s.mem base P.sF := by
      rw [O₃.w32 (by omega_arith) (by omega_arith), O₂.w32 (by omega_arith) (by omega_arith), F₁]
    have G : w32 u.mem base (P.sW + 8) = w32 s.mem base P.sG := by
      rw [O₃.w32 (by omega_arith) (by omega_arith), G₂]
    simp only [wordState, atWord, Divstep.W32.WSt.mk.injEq, Nat.reduceMul, Nat.add_zero]
    refine ⟨BitVec.eq_of_toNat_eq D, BitVec.eq_of_toNat_eq F, BitVec.eq_of_toNat_eq G,
      BitVec.eq_of_toNat_eq U, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem base (P.sW + 16) = 0
      simpa only [Nat.add_assoc, Nat.reduceAdd] using V
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem base (P.sW + 20) = 0
      simpa only [Nat.add_assoc, Nat.reduceAdd] using Q
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem base (P.sW + 24) = 1
      simpa only [Nat.add_assoc, Nat.reduceAdd] using R
  · intro x hx
    rw [O₃ x (by omega_arith), O₂ x (by omega_arith), O₁ x (by omega_arith)]

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvWords` -/

section

/-! # A thirty-step batch computes the full signed transition matrix -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem low_cong32 {m : Mem} {base : Addr} {d : Nat} {x : Int}
    (h : (val32 m base d 9 : Int) % 2 ^ 288 = x % 2 ^ 288) :
    ((m.readW (off base d) 32).toNat : Int) % 2 ^ 32 = x % 2 ^ 32 := by
  have D : (2 : Int) ^ 32 ∣ 2 ^ 288 := pow_dvd_pow 2 (by decide)
  have E : (w32 m base d : Int) % 2 ^ 32 = (val32 m base d 9 : Int) % 2 ^ 32 := by
    rw [val32, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Int.add_mul_emod_self_left]
  rw [E, ← Int.emod_emod_of_dvd _ D, h, Int.emod_emod_of_dvd _ D]

theorem words_ok {P : InvCfg} {s : State} {base : Addr} {size : Nat} {I : Divstep.W32.IState}
    (hs : Scr s base size) (ht : P.tbl + 320 ≤ size) (hI : StateAt P base I s)
    (hd : |I.d| + 64 < 2 ^ 30) (hf : I.f % 2 = 1) :
    WP isa (.seq (.block P.batchStart) (VG.Impl.Weierstrass.X86.Inv.wordSteps P.sW 30)) s fun z =>
      MatrixAt P base (Divstep.msteps 30 (Divstep.MSt.init I.d I.f I.g)) z ∧
      Keeps wordClob s z ∧ Outside base P.sW 28 s.mem z.mem := by
  have eW : P.sW = P.tbl + 288 := rfl
  refine WP.seq (WP.mono (batchStart_ok hs ht) fun s₁ ⟨V₁, K₁, O₁⟩ => ?_)
  have rel : (wordState s₁.mem base P.sW).rel (Divstep.MSt.init I.d I.f I.g) 32 := by
    rw [V₁]
    refine ⟨hI.d, rfl, rfl, rfl, rfl, low_cong32 hI.f, low_cong32 hI.g⟩
  have matrix := Divstep.W32.wsteps_rel (by decide) rel hd hf 30 (by decide)
  refine WP.mono (wordSteps_ok (hs.of_keeps K₁ (by decide)) (by omega_arith) (by decide) (by decide))
    fun z ⟨V₂, K₂, O₂⟩ => ⟨?_, (K₁.mono (by decide)).trans K₂, ?_⟩
  · rw [← V₂] at matrix
    obtain ⟨D, U, V, Q, R, _, _⟩ := matrix
    exact ⟨D, U, V, Q, R⟩
  · intro x hx
    rw [O₂ x hx, O₁ x (by omega_arith)]

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvCount` -/

section

/-! # The public counter for the outer inversion loop -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem batchEnd_ok {P : InvCfg} {s : State} {base : Addr} {size j : Nat}
    (hs : Scr s base size) (ht : P.tbl + 320 ≤ size) (hj : 1 ≤ j) (hj32 : j < 2 ^ 32)
    (hc : w32 s.mem base P.sCount = j) :
    WP isa (.block P.batchEnd) s fun z =>
      w32 z.mem base P.sCount = j - 1 ∧ z.zf = some (decide (j - 1 = 0)) ∧
      Keeps [.esi] s z ∧ Outside base P.sCount 4 s.mem z.mem := by
  have hn := hs.nowrap
  have ec : P.sCount = P.tbl + 316 := rfl
  unfold InvCfg.batchEnd
  refine wp_movS (readSrc_sc hs (by omega_arith)) fun s₁ U₁ _ => ?_
  have J : s₁.gpr .esi = BitVec.ofNat 32 j := by
    rw [U₁.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32]
    exact hc
  refine wp_decCounter hj J fun s₂ J₂ K₂ M₂ => ?_
  have K := U₁.keeps.trans K₂
  have hs₂ := hs.of_keeps K (by decide)
  refine wp_storeS (hs₂.ea (by omega_arith)) (hs₂.write (by omega_arith)) fun s₃ U₃ => ?_
  have J₃ : s₃.gpr .esi = BitVec.ofNat 32 (j - 1) := by rw [U₃.gpr, J₂]
  refine wp_testCounter (by omega_arith) J₃ fun z F hz => WP.block_nil ⟨?_, hz, ?_, ?_⟩
  · rw [F.mem, U₃.mem, w32_write_self, J₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  · exact (K.trans (U₃.keeps _)).trans (F.keeps _)
  · rw [F.mem, U₃.mem, M₂, U₁.mem]
    exact writeW32_outside _ _ _ (by omega_arith)

end VG.Proof.Weierstrass.X86.Inv

end
