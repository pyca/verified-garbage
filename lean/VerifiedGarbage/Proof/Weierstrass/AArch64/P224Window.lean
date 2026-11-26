module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
public import VerifiedGarbage.Impl.Ecdsa.P224.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Lit
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-! The P-224 variable-base window call, shared by ECDH and ECDSA verification. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass Spec.Weierstrass

private theorem tmv_mem {C : Curve} {n : Nat} {base : Addr} {s t : State}
    (h : t.mem = s.mem) (x : Nat) : tmv C n base t x = tmv C n base s x := by
  show toM _ _ _ = toM _ _ _
  rw [h]

private theorem fixed_mem {K : WinCfg} {C : Curve} {base : Addr} {s t : State}
    {P : Point C} {k : Nat} (h : t.mem = s.mem) (F : WinFixed K C base s P k) :
    WinFixed K C base t P k := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tmv_mem h]; exact F.a
  · rw [tmv_mem h]; exact F.b
  · rw [h]; exact F.ro_lt
  · rw [h]; exact F.zero
  · rw [tmv_mem h, tmv_mem h, tmv_mem h]; exact F.pt
  · rw [h]; exact F.bits

private theorem window_keeps_lane :
    ∀ i ∈ instrs windowP224, keepsLane .v29 1 i = true := fun i hi =>
  List.all_eq_true.mp (by rw [← Code.allInstrs_eq]; exact (by lit_decide :
    windowP224.allInstrs (keepsLane .v29 1) = true)) i hi

/-- The whole window call has the inline window's contract, including the outer link register. -/
theorem windowCallP224_ok : WindowOk (p224.winCfg RM SS) p224.padd windowCallP224 := by
  intro C base size k hL hA hp hC hM3 P hP hpn hone_lt hone s hs hM hF hk hk8 hpa hr hfar
  rw [windowCallP224]
  refine WP.seq (WP.mono (insOf_ok [(.x30, .v29, 1)] s (by decide) (by decide))
    fun a ⟨ag, am, ar, aw, asp, al, _⟩ => ?_)
  have hsa : Scr a.callEntry base size :=
    ⟨by rw [State.callEntry_gpr _ (by decide), ag]; exact hs.x0,
      by rw [State.callEntry_wr, aw]; exact hs.wr, hs.nowrap, hs.enc⟩
  have ma : a.callEntry.mem = s.mem := (State.callEntry_mem a).trans am
  have hma : ModOkA (p224.winCfg RM SS).M size C.p a.callEntry.mem base := by rw [ma]; exact hM
  have hra : AddReady base (p224.winCfg RM SS).M a.callEntry.mem (p224.winCfg RM SS).S p224.padd := by
    rw [ma]; exact hr
  obtain ⟨trace, b, he, kb, ub, mb, lb, rb⟩ :=
    window_ok hL hA hp hC hM3 hP hpn hone_lt hone hsa hma (fixed_mem ma hF) hk hk8 hpa hra hfar
  have retok : isa.ret a.callEntry b = some b := by
    simp only [isa, ret, kb.gpr .x30 (by decide), ite_true]
  have vb : laneOf b .v29 1 = laneOf a .v29 1 := by
    rw [Exec.lane (by decide) window_keeps_lane he]
    simp only [laneOf, State.callEntry_v]
  refine WP.seq ⟨_, b, Exec.call (call_callEntry a) he retok, ?_⟩
  refine WP.mono (umovOf_ok [(.x30, .v29, 1)] b (by decide) (by decide))
    fun t ⟨tm, tr, tw, tsp, tl, tg⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro r hr'
    by_cases h30 : r = .x30
    · subst r
      rw [tl (.x30, .v29, 1) (by simp), vb]
      exact al (.x30, .v29, 1) (by simp)
    · rw [tg r (by simpa using h30), kb.gpr r hr', State.callEntry_gpr, ag]
      intro hl
      simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | h
      · exact hr' (combClob_mem (by simp))
      · exact hr' (combClob_mem (by simp))
      · exact h30 h
  · rw [tr, kb.rd, State.callEntry_rd, ar]
  · rw [tw, kb.wr, State.callEntry_wr, aw]
  · rw [tsp, kb.sp, State.callEntry_sp, asp]
  · rw [tm, ← ma]; exact ub
  · rw [tm]; exact mb
  · rw [tm]; exact lb
  · rw [tmv_mem tm, tmv_mem tm, tmv_mem tm]; exact rb

end VG.Proof.Weierstrass.AArch64
