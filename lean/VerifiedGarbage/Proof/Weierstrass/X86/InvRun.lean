import VerifiedGarbage.Proof.Weierstrass.X86.InvBatch

/-! # The fixed twenty-batch inversion loop -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem run_ok {P : InvCfg} {s : State} {base : Addr} {size p x : Nat}
    (hs : Scr s base size) (L : WorkLay P size) (hp : 0 < p) (hp256 : p < 2 ^ 256)
    (hm : val32 s.mem base P.M.mo 8 = p) (hinv : (p * (minv32 P.M).toNat + 1) % 2 ^ 32 = 0)
    (hI : StateAt P base (Divstep.W32.invRun 30 p (minv32 P.M).toNat x 0) s)
    (hc : w32 s.mem base P.sCount = 20)
    (facts : ∀ k < 20, BatchFacts (Divstep.W32.invRun 30 p (minv32 P.M).toNat x k) p) :
    WP isa (.loop P.batch .ne) s fun z =>
      StateAt P base (Divstep.W32.invRun 30 p (minv32 P.M).toNat x 20) z ∧
      Keeps wordClob s z ∧ Unch base [(P.tbl, 320), (P.M.tmp, 32)] s.mem z.mem := by
  have hn := hs.nowrap
  have hmod := L.mod_bound; have htm := L.tbl_mod; have hmt := L.mod_tmp
  let J := fun j u => Scr u base size ∧
    StateAt P base (Divstep.W32.invRun 30 p (minv32 P.M).toNat x (20 - j)) u ∧
    w32 u.mem base P.sCount = j ∧ Keeps wordClob s u ∧
    Unch base [(P.tbl, 320), (P.M.tmp, 32)] s.mem u.mem
  refine countLoop_ok (Inv := J) (n := 20) ?_ ?_ (by decide) ?_
  · intro j u hj hj20 hJ
    obtain ⟨hu, Iu, Cu, Ku, Ou⟩ := hJ
    have F := facts (20 - j) (by omega)
    have Mu : val32 u.mem base P.M.mo 8 = p := by
      rw [Outs.val32 Ou (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        constructor <;> omega) (by omega), hm]
    refine WP.mono (batch_ok hu L Iu F.delta F.odd F.f F.g F.a F.b hp hp256 Mu hinv hj
      (by omega) Cu F.matrix F.division) fun z ⟨Iz, Cz, Zz, Kz, Oz⟩ => ⟨?_, Zz⟩
    refine ⟨hu.of_keeps Kz (by decide), ?_, Cz, Ku.trans Kz, ?_⟩
    · rw [show 20 - (j - 1) = (20 - j) + 1 by omega, Divstep.W32.invRun]
      exact Iz
    · exact (Ou.trans Oz).mono (by
        intro w hw
        simpa only [List.mem_append, or_self] using hw)
  · intro u hJ
    obtain ⟨_, Iu, _, Ku, Ou⟩ := hJ
    exact ⟨Iu, Ku, Ou⟩
  · exact ⟨hs, hI, hc, Keeps.refl _ _, Unch.refl _ _ _⟩

end VG.Proof.Weierstrass.X86.Inv
