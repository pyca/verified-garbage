import VerifiedGarbage.Proof.Weierstrass.X86.WinJacCoZCopy
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacCoZStore
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacBuildInit

/-! Store the second multiple and seed the shared-Z table loop. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem co_init_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    (hn : 17≤C.n) {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity)
    {s₀ s : State} (h : BuildInv K C base size wk P s₀ 1 s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hJP : InvJ C (tmv C K.M.n base s₀ K.P.x) (tmv C K.M.n base s₀ K.P.y) 1 P)
    (hPz : tmv C K.M.n base s₀ K.P.z=1) :
    WP isa (.seq (fprog K.F K.dbluOps)
      (.seq (.block (copy 8 K.D.x K.S.t3++copy 8 K.D.y K.S.t2))
        (.block (([.mov .esi (.imm 2)] : List Instr)++K.storeEntry)))) s
      (CoBuildInv K C base size wk P s₀ 2) := by
  have hi := h.frame.inv_cached hL hW hro h.point
  have tv (x : Nat) (hx : x∈ro K) : tmv C K.M.n base s x=tmv C K.M.n base s₀ x := by
    unfold tmv
    rw [h.frame.ro hL hW hx]
  apply WP.seq
  refine WP.mono (dblu_point_ok hL hW hm hC ha hO hn hP hP0 hi
    (by intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl|rfl <;> simp [live,ro])
    (by rw [tv _ (by simp [ro]),tv _ (by simp [ro])]; exact hJP)
    (by rw [tv _ (by simp [ro])]; exact hPz)) fun a ⟨ka,pa,ta2,ta3,ja⟩ => ?_
  have fa := h.frame.field hL hW ka (fun _ hx => hx)
  have tableA := h.table.field_keep hL h.frame.scr ka (fun _ hx => hx) (by decide)
  have ia := fa.inv_cached hL hW hro pa
  have ia' : Inv K.M base size C.p (·∈slots K) (K.S.t2::K.S.t3::live K)
      (tmv C K.M.n base a) a := by
    refine ⟨ia.scr,ia.mod,?_,?_,fun _ _ => rfl⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|rfl|hx
      · simp [slots,work,temps]
      · simp [slots,work,temps]
      · exact ia.sl x hx
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|rfl|hx
      · exact ta2
      · exact ta3
      · exact ia.lt x hx
  apply WP.seq
  refine WP.mono (copy_shared_ok hL hW ia') fun b ⟨e,kb,ib,dx,dy,ev⟩ => ?_
  have wb : ∀ x∈[K.D.x,K.D.y],x∈work K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> simp [work]
  have fb := fa.field hL hW kb wb
  have tableB := tableA.field_keep hL fa.scr kb wb (by decide)
  have ev4 (x : Nat) (hx : x∈live K) : e x=tmv C 4 base a x := by
    rw [ev x hx,hL.n]
  have pb : Cached C base b (fun c => K.T+32*c) (mul 2 P) := by
    apply Cached.of_inv hL.n ib
    · intro c hc
      have : c=0 ∨ c=1 ∨ c=2 ∨ c=3 ∨ c=4 := by omega
      rcases this with rfl|rfl|rfl|rfl|rfl <;> simp [live,JacWinCfg.E,JacWinCfg.z2,JacWinCfg.z3]
    · rw [ev4 _ (by simp [live]),ev4 _ (by simp [live]),ev4 _ (by simp [live])]
      exact pa.jac
    · rw [ev4 _ (by simp [live])]; exact pa.z
    · rw [ev4 _ (by simp [live]),ev4 _ (by simp [live])]; exact pa.z2
    · rw [ev4 _ (by simp [live]),ev4 _ (by simp [live]),ev4 _ (by simp [live])]; exact pa.z3
  have sb : SharedZ K C base P b := by
    refine ⟨?_,?_⟩
    · intro x hx
      apply ib.lt x
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl <;> simp
    · have vx : tmv C K.M.n base b K.D.x=e K.D.x := ib.val _ (by simp)
      have vy : tmv C K.M.n base b K.D.y=e K.D.y := ib.val _ (by simp)
      have vz : tmv C K.M.n base b K.E.z=e K.E.z := ib.val _ (by simp [live])
      rw [vx,vy,vz,dx,dy,ev _ (by simp [live])]
      exact ja
  rw [WP.block_append_iff]
  refine WP.mono (mov_counter_ok b 2) fun t ⟨ct,kt⟩ => ?_
  apply co_store_ok hL hW (fb.keeps kt) (m:=1) (by decide) ct
  · intro m h1 hm
    exact (tableB m h1 hm).congr fun _ _ => by rw [kt.2.1]
  · exact pb.congr fun _ _ => by rw [kt.2.1]
  · exact sb.keeps kt

end VG.Proof.Weierstrass.X86.JWin
