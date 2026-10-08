import VerifiedGarbage.Proof.Weierstrass.X86.WinJacPoint
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacStore

/-! Extend the table without changing any of its earlier entries. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem store_apart {K : JacWinCfg} {i j c : Nat} (hi : i<16) (hj : j<16) (hc : c<5)
    (hne : i≠j) : ∀ w∈storeW K j,K.entry i c+32≤w.1 ∨ w.1+w.2≤K.entry i c := by
  intro w hw
  simp only [storeW,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl <;> dsimp only <;> unfold JacWinCfg.entry <;> split <;> omega

theorem store_table_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size M : Nat}
    {s : State} (hs : Scr s base size) (hM : M<16)
    (hb : s.gpr .esi=BitVec.ofNat 32 (M+1)) (ht : K.tbl+2560≤size) (hT : K.T+160≤K.tbl)
    {P : Point C} (hOld : Table K C base P M s)
    (hNew : Cached C base s (fun c => K.T+32*c) (mul (M+1) P)) :
    WP isa (.block K.storeEntry) s fun t => Table K C base P (M+1) t ∧
      Unch base (storeW K M) s.mem t.mem ∧ KeepRegs [.eax,.ecx,.edx] s t := by
  refine WP.mono (storeEntry_ok hs (by omega) (by omega) hb ht hT) fun t ⟨et,ot,kt⟩ => ?_
  simp only [Nat.add_sub_cancel] at et ot
  refine ⟨fun m h1 hm => ?_,ot,kt⟩
  by_cases he : m=M+1
  · subst m
    simp only [Nat.add_sub_cancel]
    exact hNew.congr et
  · have hOld' := hOld m h1 (by omega)
    apply hOld'.congr
    intro c hc
    have eb := entry_bounds (K:=K) (m:=m-1) (by omega) hc
    have hn := hs.nowrap
    exact ot.wordsVal (store_apart (by omega) hM hc (by omega)) (by omega)

end VG.Proof.Weierstrass.X86.JWin
