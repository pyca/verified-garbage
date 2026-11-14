module

public import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT
public import VerifiedGarbage.Proof.Ecdsa.X86.CombLays
import VerifiedGarbage.Proof.Ecdsa.X86.CombCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombMain
public import VerifiedGarbage.Proof.Ecdsa.X86.CombPrefix

/-! ### `Ecdsa.X86.CombBodyCT`, which only this module used -/

section

/-! # Constant time of the signing body with a fixed-base comb -/

@[expose] public section

namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

/-- Static tables remain readable and outside scratch throughout setup. -/
def CombTables (s : State) : Prop :=
  TblMem s ((s.gpr .eax).setWidth 64) (p256Comb.combWords p256d) ∧
  (∀ i < (p256Comb.combWords p256d).length, ∀ b < 8,
    size ≤ ofs (ptr s 4) ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) ∧
  ∀ r ∈ s.wr ++ [below (s.gpr .esp) p256Comb.stk],
    Region.Disjoint ⟨(s.gpr .eax).setWidth 64, 8 * (p256Comb.combWords p256d).length⟩ r

theorem signCombBody_rel (hc : CfgOk p256Comb) (hC : Law p256Comb.C)
    (hT : CombTbls p256Comb) (hd : CombOk p256Comb p256d) (ham3 : AM3 p256Comb.C)
    {s₀ t₀ : State} {extra₁ extra₂ : List Region}
    (hp : Pre p256Comb s₀ extra₁) (hq : Pre p256Comb t₀ extra₂)
    (ht₁ : CombTables s₀) (ht₂ : CombTables t₀)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 5, arg s₀ j = arg t₀ j)
    (hg : s₀.gpr .eax = t₀.gpr .eax) (hsp : SpOk (p256Comb.signWithMul p256Comb.gMul) 20) :
    RelCT isa (fun s t => s = s₀ ∧ t = t₀) (p256Comb.signWithMul p256Comb.gMul) (fun _ _ => True) := by
  have hspG : SpOk p256Comb.gMul 20 := hsp.right.left
  have hspG' : SpOk p256Comb.gMul p256Comb.stk := ⟨hspG.1, Nat.le_trans hspG.2 (Cfg.stk_ge _)⟩
  have hsp20 : ∀ {u₀ u : State} {extra : List Region}, Pre p256Comb u₀ extra →
      Keep p256Comb u₀ (ptr u₀ 4) u → 20 ≤ (u.gpr .esp).toNat := fun hp k => by
    rw [k.esp]; exact Nat.le_trans (Cfg.stk_ge _) hp.sp_lo
  have prep := signPrep_rel.mono (P' := fun s t => s = s₀ ∧ t = t₀)
    (fun _ _ h => by
      rcases h with ⟨rfl, rfl⟩
      exact argAgree (argWf _ hp rfl rfl) (argWf _ hq rfl rfl)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact he) he ha)
    (fun _ _ _ => trivial)
  have prep' := prep.wp
    (F₁ := fun s => St₁ p256Comb .sign s₀ (ptr s₀ 4) s)
    (F₂ := fun t => St₁ p256Comb .sign t₀ (ptr t₀ 4) t)
    (fun _ _ h => by
      rcases h with ⟨rfl, rfl⟩
      exact ⟨stage₁ hc hp.setup (fun _ h => WP.block_nil h),
        stage₁ hc hq.setup (fun _ h => WP.block_nil h)⟩)
  have hCo : ∀ d, p256Comb.comb = some d → CombOk p256Comb d := by
    intro d h
    have e : p256d = d := Option.some.inj h
    rw [← e]; exact hd
  have multCT : RelCT isa (fun s t => True ∧
      St₁ p256Comb .sign s₀ (ptr s₀ 4) s ∧ St₁ p256Comb .sign t₀ (ptr t₀ 4) t)
      p256Comb.gMul (fun _ _ => True) := by
    intro s t tr₁ tr₂ s' t' h e₁ e₂
    obtain ⟨_, S, T⟩ := h
    obtain ⟨tb₁, ap₁⟩ := S.toKeep.tbls ht₁.1 ht₁.2.2
    obtain ⟨tb₂, ap₂⟩ := T.toKeep.tbls ht₂.1 ht₂.2.2
    have hb : ptr s₀ 4 = ptr t₀ 4 := congrArg (BitVec.setWidth 64) (ha 4 (by decide))
    have T' := T
    rw [← hb] at T'
    exact gMul_rel hc hC hT hd ham3 S.scr T'.scr S.fixed T'.fixed
      (S.k ▸ wordsVal_lt _ _ _ _) (T'.k ▸ wordsVal_lt _ _ _ _) S.t₀ T'.t₀ tb₁ tb₂ ht₁.2.1 ap₁ ap₂
      (hsp20 hp S.toKeep) (hsp20 hq T.toKeep) hg
      (keepCombWf hp S.toKeep) (keepCombWf hq T.toKeep)
      (by rw [S.wr, T.wr, hp.wr, hq.wr]; simp only [outR, scR, ptr, ha 0 (by decide), ha 4 (by decide)])
      (by rw [S.esp, T.esp, he])
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  have functional : ∀ {u₀ u : State} {extra : List Region}, Pre p256Comb u₀ extra → CombTables u₀ →
      St₁ p256Comb .sign u₀ (ptr u₀ 4) u →
      WP isa p256Comb.gMul u (Keep p256Comb u₀ (ptr u₀ 4)) := by
    intro u₀ u extra hp ht S
    refine S.toKeep.withSp hspG' (WP.mono (gMul_ok' hc hC hT hCo ham3 S.scr S.fixed
      (S.k ▸ wordsVal_lt _ _ _ _) S.rx S.ry S.rz S.t₀ ?_ (hsp20 hp S.toKeep) hspG)
      fun _ h f => S.toKeep.gMul hc h.1 h.2.1 f)
    intro d h
    have e : p256d = d := Option.some.inj h
    subst d
    obtain ⟨tb, ap⟩ := S.toKeep.tbls ht.1 ht.2.2
    exact ⟨tb, ht.2.1, ap⟩
  have mult := multCT.wp (F₁ := fun s => Keep p256Comb s₀ (ptr s₀ 4) s)
    (F₂ := fun t => Keep p256Comb t₀ (ptr t₀ 4) t)
    (fun _ _ h => ⟨functional hp ht₁ h.2.1, functional hq ht₂ h.2.2⟩)
  exact prep'.seq (mult.seq (signTail_rel.mono
    (fun _ _ h => keepScratchAgree hp hq h.2.1 h.2.2 he ha) (fun _ _ _ => trivial)))

end VG.Proof.Ecdsa.X86

end

end

/-! ### `Ecdsa.X86.CombSign`, which only this module used -/

section

/-! # The balanced static-address prefix and the comb signing body -/

@[expose] public section

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
  have := Cfg.stk_ge c; have := hp.toPre.sp_lo; omega_arith

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
  have ha : ∀ j < 5, arg s₁ j = arg s₀ j := fun j hj => P.arg hp.sp4 (by have := hp.sp_fit; omega_using [hj, this])
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
    exact hr.trans (P.ret hp.sp4 (by have := hp.sp_fit; omega_using [this]))
  · have hd := prefix_bytesAt P hp.d_stack (by have := hp.d_fit; change c.C.len ≤ 2 ^ 64; omega_using [this])
    have hh := prefix_bytesAt P hp.digest_stack (by have := hp.digest_fit; change c.C.len ≤ 2 ^ 64; omega_using [this])
    have hk := prefix_bytesAt P hp.k_stack (by have := hp.k_fit; change c.C.len ≤ 2 ^ 64; omega_using [this])
    simpa only [SignPost, ptr, ha 0 (by decide), ha 1 (by decide), ha 2 (by decide),
      ha 3 (by decide), hd, hh, hk] using post

end VG.Proof.Ecdsa.X86

end

end


/-! # Constant time of the complete comb signing function -/

@[expose] public section

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
  have hp' := hp.toPre.symAddr P hp.sp4
  have held := hp.tbls.symAddr (Nat.le_trans (by decide) (Cfg.stk_ge _)) hp.toPre.sp_lo P
  have ht := tbl_of_held (c := p256Comb) (d := p256d) (base := ptr t 4) rfl held
    (by rw [hp'.wr]; simp) (fun r hr => by rw [hp'.rd]; simp only [P.syms] at hr; simp [hr]) (Unch.refl _ _ _)
  simpa only [CombTables, P.addr, P.syms] using ht

theorem signComb_ct (hc : CfgOk p256Comb) (hC : Law p256Comb.C)
    (hT : CombTbls p256Comb) (hd : CombOk p256Comb p256d) (ham3 : AM3 p256Comb.C)
    (hsp : SpOk (p256Comb.signWithMul p256Comb.gMul) 20) :
    ConstantTime isa (CombSignPre p256Comb) CombSignPub signP256Comb := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  have preCT : RelCT isa (fun s t => CombSignPre p256Comb s ∧ CombSignPre p256Comb t ∧ CombSignPub s t)
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
  have ha' : ∀ j < 5, arg s j = arg t j := by
    intro j hj
    rw [P.arg hp.sp4 (by have := hp.sp_fit; omega_using [hj, this]), Q.arg hq.sp4 (by have := hq.sp_fit; omega_using [hj, this]), ha j hj]
  exact signCombBody_rel hc hC hT hd ham3 (hp.toPre.symAddr P hp.sp4) (hq.toPre.symAddr Q hq.sp4)
    (prefixTables hp P) (prefixTables hq Q) he' ha' (by rw [P.addr, Q.addr, hg]) hsp
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

end VG.Proof.Ecdsa.X86
