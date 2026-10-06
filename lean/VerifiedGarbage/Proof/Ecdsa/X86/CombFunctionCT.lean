import VerifiedGarbage.Proof.Ecdsa.X86.CombBodyCT

/-! # Constant time of the complete comb signing function -/
namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

/-- Public signing inputs are addresses, the stack pointer, and the static
symbol address. Scalar and message bytes need not agree. -/
def CombSignPub (s t : State) : Prop :=
  s.gpr .esp = t.gpr .esp ∧ (∀ j < 5, arg s j = arg t j) ∧ s.syms p256d.tsym = t.syms p256d.tsym

/-- After the balanced prefix, the comb table is available to the body. -/
theorem prefixTables {s t : State} (hp : CombSignPre p256Comb s) (P : SymAddrPost p256d.tsym s t) :
    CombTables t := by
  have hp' := hp.toPre.symAddr P hp.sp_lo
  have held := hp.tbls.symAddr P
  have ht := tbl_of_held (c := p256Comb) (d := p256d) (base := ptr t 4) rfl held
    (by rw [hp'.wr]; simp) (fun r hr => by rw [hp'.rd]; simp only [P.syms] at hr; simp [hr]) (Unch.refl _ _ _)
  simpa only [CombTables, P.addr, P.syms] using ht

theorem signComb_ct (hc : CfgOk p256Comb) (hC : Law p256Comb.C)
    (hT : CombTbls p256Comb) (hd : CombOk p256Comb p256d) (ham3 : AM3 p256Comb.C) :
    ConstantTime isa (CombSignPre p256Comb) CombSignPub signP256Comb := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  have preCT : RelCT isa (fun s t => CombSignPre p256Comb s ∧ CombSignPre p256Comb t ∧ CombSignPub s t)
      p256Comb.tableAddr (fun _ _ => True) := by
    intro s t tr₁ tr₂ s' t' h e₁ e₂
    exact ⟨by rw [symFrame_trace h.1.sp_lo e₁, symFrame_trace h.2.1.sp_lo e₂, h.2.2.1], trivial⟩
  have pre := preCT.wpDep (F := fun s t => SymAddrPost p256d.tsym s t) (by
    intro s t h
    change WP isa (.frame (.symPush .eax p256d.tsym) (.block []) (.pop .ecx 1)) s
      (SymAddrPost p256d.tsym s) ∧ WP isa (.frame (.symPush .eax p256d.tsym) (.block []) (.pop .ecx 1)) t
      (SymAddrPost p256d.tsym t)
    exact ⟨symFrame_ok p256d.tsym s h.1.sp_lo, symFrame_ok p256d.tsym t h.2.1.sp_lo⟩)
  refine pre.seq ?_
  intro s t tr₁ tr₂ s' t' h e₁ e₂
  obtain ⟨_, a, b, ⟨hp, hq, he, ha, hg⟩, P, Q⟩ := h
  have he' : s.gpr .esp = t.gpr .esp := by rw [P.gpr .esp (by decide), Q.gpr .esp (by decide), he]
  have ha' : ∀ j < 5, arg s j = arg t j := by
    intro j hj
    rw [P.arg hp.sp_lo (by have := hp.sp_fit; omega), Q.arg hq.sp_lo (by have := hq.sp_fit; omega), ha j hj]
  exact signCombBody_rel hc hC hT hd ham3 (hp.toPre.symAddr P hp.sp_lo) (hq.toPre.symAddr Q hq.sp_lo)
    (prefixTables hp P) (prefixTables hq Q) he' ha' (by rw [P.addr, Q.addr, hg])
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

end VG.Proof.Ecdsa.X86
