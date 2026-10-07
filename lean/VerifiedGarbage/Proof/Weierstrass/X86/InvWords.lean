import VerifiedGarbage.Proof.Weierstrass.X86.InvStart
import VerifiedGarbage.Proof.Weierstrass.X86.InvLoop
import VerifiedGarbage.Proof.Divstep.Word32

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
  refine WP.mono (wordSteps_ok (hs.of_keeps K₁ (by decide)) (by omega) (by decide) (by decide))
    fun z ⟨V₂, K₂, O₂⟩ => ⟨?_, (K₁.mono (by decide)).trans K₂, ?_⟩
  · rw [← V₂] at matrix
    obtain ⟨D, U, V, Q, R, _, _⟩ := matrix
    exact ⟨D, U, V, Q, R⟩
  · intro x hx
    rw [O₂ x hx, O₁ x (by omega)]

end VG.Proof.Weierstrass.X86.Inv
