import VerifiedGarbage.Proof.EcKey.X86.CombBodyCT

/-! # The public-key comb function, including its static-address prefix -/
namespace VG.Proof.EcKey.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86
open VG.Impl.EcKey.X86 (Args.publicKey)

structure PkCombPre (c : Cfg) (s : State) : Prop extends
    PkPre c s (Abi.constRegions (fun n => (s.syms n).setWidth 64) c.combConsts) where
  tbls : TblsHeld c s (below (s.gpr .esp) c.stk :: s.wr)
  d_stack : Region.Disjoint ⟨ptr s 1, c.C.len⟩ (below (s.gpr .esp) 4)

variable {c : Cfg}

theorem PkCombPre.sp4 {s : State} (hp : PkCombPre c s) : 4 ≤ (s.gpr .esp).toNat := by
  have := Cfg.stk_ge c; have := hp.toPkPre.sp_lo; omega

theorem PkPre.symAddr {s t : State} {extra : List Region} {name : String}
    (hp : PkPre c s extra) (h : SymAddrPost name s t) (hsp : 4 ≤ (s.gpr .esp).toNat) : PkPre c t extra := by
  have he := h.gpr .esp (by decide)
  have ha : ∀ j < 3, arg t j = arg s j := fun j hj => h.arg hsp (by have := hp.sp_fit; omega)
  have haa : argAddr t 0 = argAddr s 0 := by simp only [argAddr, he]
  exact {
    rd := by simpa only [ptr, ha 1 (by decide), haa, h.rd] using hp.rd
    wr := by simpa only [ptr, ha 0 (by decide), ha 2 (by decide), h.wr] using hp.wr
    out_sc := by simpa only [ptr, ha 0 (by decide), ha 2 (by decide)] using hp.out_sc
    out_d := by simpa only [ptr, ha 0 (by decide), ha 1 (by decide)] using hp.out_d
    d_sc := by simpa only [ptr, ha 1 (by decide), ha 2 (by decide)] using hp.d_sc
    args_out := by simpa only [ptr, haa, ha 0 (by decide)] using hp.args_out
    args_sc := by simpa only [ptr, haa, ha 2 (by decide)] using hp.args_sc
    ret_out := by simpa only [ptr, he, ha 0 (by decide)] using hp.ret_out
    ret_sc := by simpa only [ptr, he, ha 2 (by decide)] using hp.ret_sc
    out_fit := by rw [ha 0 (by decide)]; exact hp.out_fit
    d_fit := by rw [ha 1 (by decide)]; exact hp.d_fit
    sc_fit := by rw [ha 2 (by decide)]; exact hp.sc_fit
    sp_fit := by rw [he]; exact hp.sp_fit
    sp_lo := by rw [he]; exact hp.sp_lo
    stk_out := by simpa only [stkR, ptr, he, ha 0 (by decide)] using hp.stk_out
    stk_sc := by simpa only [stkR, ptr, he, ha 2 (by decide)] using hp.stk_sc }

theorem PkKeep.abi {s₀ s : State} {extra : List Region} (hp : PkPre c s₀ extra) (K : PkKeep c s₀ s) :
    abiPreserved s₀ s := by
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact K.saved (.ebx, 0) (by decide)
    · exact K.saved (.esi, 4) (by decide)
    · exact K.saved (.edi, 8) (by decide)
    · exact K.saved (.ebp, 12) (by decide)
    · exact K.esp
  · exact K.ret hp

theorem pkPrefixTables {s t : State} (hp : PkCombPre p256Comb s) (P : SymAddrPost p256d.tsym s t) :
    PkCombTables t := by
  have hp' := hp.toPkPre.symAddr P hp.sp4
  have held := hp.tbls.symAddr (Nat.le_trans (by decide) (Cfg.stk_ge _)) hp.toPkPre.sp_lo P
  have ht := tbl_of_held (c := p256Comb) (d := p256d) (base := ptr t 2) rfl held
    (by rw [hp'.wr]; simp) (fun r hr => by rw [hp'.rd]; simp only [P.syms] at hr; simp [hr]) (Unch.refl _ _ _)
  simpa only [PkCombTables, P.addr, P.syms] using ht

def pkCombCode : Prog isa := Impl.EcKey.X86.Cfg.publicKeyComb p256Comb
materialize_code pkCombCode

/-- No instruction writes `esp`, and the calls use 20 bytes of stack. -/
theorem pkComb_sp : SpOk pkCombCode p256Comb.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem pkComb_body_sp : SpOk (.seq p256Comb.gMul (.seq p256Comb.pPow (Impl.EcKey.X86.Cfg.middle p256Comb))) 20 :=
  (SpOk.right (a := p256Comb.tableAddr) pkComb_sp).right

theorem pkComb_spG : SpOk p256Comb.gMul 20 := pkComb_body_sp.left

theorem pkComb_spP : SpOk p256Comb.pPow p256Comb.stk := pkComb_body_sp.right.left

theorem pkComb_spO : SpOk (pkOps p256Comb) p256Comb.stk := by
  have h := pkComb_body_sp.right.right
  rw [middle_split] at h
  exact (SpOk.split _ _ _ h).1

theorem pkComb_ok (hC : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) {s₀ : State} (hp : PkCombPre p256Comb s₀) :
    WP isa pkCombCode s₀ fun s' => abiPreserved s₀ s' ∧ PkPost p256Comb s₀ s' := by
  have hCo : ∀ d, p256Comb.comb = some d → CombOk p256Comb d := by
    intro d h; have e : p256d = d := Option.some.inj h; rw [← e]; exact p256Comb_shape
  refine WP.seq (WP.mono (symFrame_ok p256d.tsym s₀ hp.sp4) fun s₁ P => ?_)
  have hp₁ := hp.toPkPre.symAddr P hp.sp4
  have ht := pkPrefixTables hp P
  refine WP.mono (publicKeyCombBody_ok (p256Comb_ok hI) hC (p256Comb_tables hC) hCo p256Comb_am3 hp₁
    (fun d hd => by have e : p256d = d := Option.some.inj hd; subst d; exact ht) pkComb_spG pkComb_spP pkComb_spO)
    fun s₂ ⟨K, post⟩ => ?_
  have ha := K.abi hp₁
  have he := P.gpr .esp (by decide)
  refine ⟨⟨fun r hr => (ha.1 r hr).trans (P.gpr r (by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)), ?_⟩, ?_⟩
  · have ht := ha.2
    rw [he] at ht
    exact ht.trans (P.ret hp.sp4 (by have := hp.sp_fit; omega))
  · have harg : ∀ j < 3, arg s₁ j = arg s₀ j := fun j hj => P.arg hp.sp4 (by have := hp.sp_fit; omega)
    have hd := prefix_bytesAt P hp.d_stack (by have := hp.d_fit; change p256Comb.C.len ≤ 2 ^ 64; omega)
    simpa only [PkPost, dk, ptr, harg 0 (by decide), harg 1 (by decide), hd] using post

def PkCombPub (s t : State) : Prop :=
  s.gpr .esp = t.gpr .esp ∧ (∀ j < 3, arg s j = arg t j) ∧ s.syms p256d.tsym = t.syms p256d.tsym

theorem pkComb_ct (hC : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) : ConstantTime isa (PkCombPre p256Comb) PkCombPub pkCombCode := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  have preCT : RelCT isa (fun s t => PkCombPre p256Comb s ∧ PkCombPre p256Comb t ∧ PkCombPub s t)
      p256Comb.tableAddr (fun _ _ => True) := by
    intro s t tr₁ tr₂ s' t' h e₁ e₂
    exact ⟨by rw [symFrame_trace h.1.sp4 e₁, symFrame_trace h.2.1.sp4 e₂, h.2.2.1], trivial⟩
  have pre := preCT.wpDep (F := fun s t => SymAddrPost p256d.tsym s t) (by
    intro s t h
    change WP isa (.frame (.symPush .eax p256d.tsym) (.block []) (.pop .ecx 1)) s
      (SymAddrPost p256d.tsym s) ∧ WP isa (.frame (.symPush .eax p256d.tsym) (.block []) (.pop .ecx 1)) t
      (SymAddrPost p256d.tsym t)
    exact ⟨symFrame_ok p256d.tsym s h.1.sp4, symFrame_ok p256d.tsym t h.2.1.sp4⟩)
  refine pre.seq ?_
  intro s t tr₁ tr₂ s' t' h e₁ e₂
  obtain ⟨_, a, b, ⟨hp, hq, he, ha, hg⟩, P, Q⟩ := h
  have he' : s.gpr .esp = t.gpr .esp := by rw [P.gpr .esp (by decide), Q.gpr .esp (by decide), he]
  have ha' : ∀ j < 3, arg s j = arg t j := by
    intro j hj
    rw [P.arg hp.sp4 (by have := hp.sp_fit; omega), Q.arg hq.sp4 (by have := hq.sp_fit; omega), ha j hj]
  exact pkCombBody_rel (p256Comb_ok hI) hC (p256Comb_tables hC) p256Comb_shape p256Comb_am3
    (hp.toPkPre.symAddr P hp.sp4) (hq.toPkPre.symAddr Q hq.sp4)
    (pkPrefixTables hp P) (pkPrefixTables hq Q) he' ha' (by rw [P.addr, Q.addr, hg]) pkComb_spG
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

end VG.Proof.EcKey.X86
