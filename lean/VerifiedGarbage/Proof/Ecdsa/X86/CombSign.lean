import VerifiedGarbage.Proof.Ecdsa.X86.CombPrefix

/-! # The balanced static-address prefix and the comb signing body -/
namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

structure CombSignPre (c : Cfg) (s : State) : Prop extends
    Pre c s (Abi.constRegions (fun n => (s.syms n).setWidth 64) c.combConsts) where
  tbls : TblsHeld c s (below (s.gpr .esp) c.stk :: s.wr)
  d_stack : (dR c s).Disjoint (below (s.gpr .esp) 4)
  digest_stack : (digestR c s).Disjoint (below (s.gpr .esp) 4)
  k_stack : (kR c s).Disjoint (below (s.gpr .esp) 4)

variable {c : Cfg}

theorem CombSignPre.sp4 {s : State} (hp : CombSignPre c s) : 4 ≤ (s.gpr .esp).toNat := by
  have := Cfg.stk_ge c; have := hp.toPre.sp_lo; omega

/-- The complete comb signing function computes the existing specification
and preserves the cdecl ABI, including the return address. -/
theorem signComb_ok (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c)
    (hCo : ∀ d, c.comb = some d → CombOk c d) (ham3 : AM3 c.C)
    {d : CombData} (hcd : c.comb = some d) (hsp₁ : SpOk c.gMul 20) (hsp : SpOk c.signTail c.stk)
    {s₀ : State} (hp : CombSignPre c s₀) :
    WP isa c.signComb s₀ fun s' => abiPreserved s₀ s' ∧ SignPost c s₀ s' := by
  unfold Cfg.signComb Cfg.tableAddr
  rw [hcd]
  refine WP.seq (WP.mono (symFrame_ok d.tsym s₀ hp.sp4) fun s₁ P => ?_)
  have hp₁ := hp.toPre.symAddr P hp.sp4
  have he := P.gpr .esp (by decide)
  have ha : ∀ j < 5, arg s₁ j = arg s₀ j := fun j hj => P.arg hp.sp4 (by have := hp.sp_fit; omega)
  have htbl := hp.tbls.symAddr (Nat.le_trans (by decide) (Cfg.stk_ge c)) hp.toPre.sp_lo P
  have ht : TblMem s₁ ((s₀.syms d.tsym).setWidth 64) (c.combWords d) ∧
      (∀ i < (c.combWords d).length, ∀ b < 8,
        size ≤ ofs (ptr s₁ 4) ((s₀.syms d.tsym).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) ∧
      ∀ r ∈ s₁.wr ++ [below (s₁.gpr .esp) c.stk],
        Region.Disjoint ⟨(s₀.syms d.tsym).setWidth 64, 8 * (c.combWords d).length⟩ r := by
    rw [← P.syms]
    exact tbl_of_held hcd htbl (by rw [hp₁.wr]; simp) (fun r hr => by
      rw [hp₁.rd]; simp only [P.syms] at hr; simp [hr]) (Unch.refl _ _ _)
  refine WP.mono (signCombBody_ok hc hC hT hCo ham3 hp₁ (fun d' hd' => by
    have : d' = d := Option.some.inj (hd'.symm.trans hcd)
    subst d'
    rw [P.addr]; exact ht) hsp₁ hsp) fun s₂ ⟨K, post⟩ => ?_
  have hAbi := K.abi hp₁
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · exact (hAbi.1 r hr).trans (P.gpr r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide))
  · have hr := hAbi.2
    rw [he] at hr
    exact hr.trans (P.ret hp.sp4 (by have := hp.sp_fit; omega))
  · have hd := prefix_bytesAt P hp.d_stack (by have := hp.d_fit; change c.C.len ≤ 2 ^ 64; omega)
    have hh := prefix_bytesAt P hp.digest_stack (by have := hp.digest_fit; change c.C.len ≤ 2 ^ 64; omega)
    have hk := prefix_bytesAt P hp.k_stack (by have := hp.k_fit; change c.C.len ≤ 2 ^ 64; omega)
    simpa only [SignPost, ptr, ha 0 (by decide), ha 1 (by decide), ha 2 (by decide),
      ha 3 (by decide), hd, hh, hk] using post

end VG.Proof.Ecdsa.X86
