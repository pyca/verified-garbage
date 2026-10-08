import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombBodyCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombFacts

/-! # Verification with the static comb table address -/
namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86

structure VCombPre (c : Cfg) (s : State) : Prop extends
    VPre c s (Abi.constRegions (fun n => (s.syms n).setWidth 64) c.combConsts) where
  tbls : TblsHeld c s (below (s.gpr .esp) c.stk :: s.wr)
  pk_stack : Region.Disjoint ⟨ptr s 0, 1 + 2 * c.C.len⟩ (below (s.gpr .esp) 4)
  dg_stack : Region.Disjoint ⟨ptr s 1, c.C.len⟩ (below (s.gpr .esp) 4)
  sig_stack : Region.Disjoint ⟨ptr s 2, 2 * c.C.len⟩ (below (s.gpr .esp) 4)

variable {c : Cfg}

theorem VCombPre.sp4 {s : State} (hp : VCombPre c s) : 4 ≤ (s.gpr .esp).toNat := by
  have := Cfg.stk_ge c; have := hp.toVPre.sp_lo; omega

theorem VPre.symAddr {s t : State} {extra : List Region} {name : String}
    (hp : VPre c s extra) (h : SymAddrPost name s t) (hsp : 4 ≤ (s.gpr .esp).toNat) : VPre c t extra := by
  have he := h.gpr .esp (by decide)
  have ha : ∀ j < 4, arg t j = arg s j := fun j hj => h.arg hsp (by have := hp.sp_fit; omega)
  have haa : argAddr t 0 = argAddr s 0 := by simp only [argAddr, he]
  exact {
    rd := by simpa only [ptr, ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), haa, h.rd] using hp.rd
    wr := by simpa only [ptr, ha 3 (by decide), h.wr] using hp.wr
    pk_sc := by simpa only [ptr, ha 0 (by decide), ha 3 (by decide)] using hp.pk_sc
    dg_sc := by simpa only [ptr, ha 1 (by decide), ha 3 (by decide)] using hp.dg_sc
    sig_sc := by simpa only [ptr, ha 2 (by decide), ha 3 (by decide)] using hp.sig_sc
    args_sc := by simpa only [ptr, haa, ha 3 (by decide)] using hp.args_sc
    ret_sc := by simpa only [ptr, he, ha 3 (by decide)] using hp.ret_sc
    pk_fit := by rw [ha 0 (by decide)]; exact hp.pk_fit
    dg_fit := by rw [ha 1 (by decide)]; exact hp.dg_fit
    sig_fit := by rw [ha 2 (by decide)]; exact hp.sig_fit
    sc_fit := by rw [ha 3 (by decide)]; exact hp.sc_fit
    sp_fit := by rw [he]; exact hp.sp_fit
    sp_lo := by rw [he]; exact hp.sp_lo
    stk_sc := by simpa only [stkR, ptr, he, ha 3 (by decide)] using hp.stk_sc }

theorem VKeep.abi {s₀ s : State} {extra : List Region} (hp : VPre c s₀ extra) (K : VKeep c s₀ s) :
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

theorem vPrefixTables {s t : State} (hp : VCombPre p256Comb s) (P : SymAddrPost p256d.tsym s t) :
    VCombTables t := by
  have hp' := hp.toVPre.symAddr P hp.sp4
  have held := hp.tbls.symAddr (Nat.le_trans (by decide) (Cfg.stk_ge _)) hp.toVPre.sp_lo P
  have ht := tbl_of_held (c := p256Comb) (d := p256d) (base := ptr t 3) rfl held
    (by rw [hp'.wr]; simp) (fun r hr => by rw [hp'.rd]; simp only [P.syms] at hr; simp [hr]) (Unch.refl _ _ _)
  simpa only [VCombTables, P.addr, P.syms] using ht

def vCombCode : Prog isa := Impl.Ecdsa.Verify.X86.Cfg.verifyComb p256Comb
materialize_code vCombCode

/-- No instruction writes `esp`, and the calls use 20 bytes of stack. -/
theorem vComb_sp : SpOk vCombCode p256Comb.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem vCombBody_sp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.verifyCombBody p256Comb) p256Comb.stk :=
  SpOk.right (a := p256Comb.tableAddr) vComb_sp

theorem vComb_ok (hC : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) {s₀ : State} (hp : VCombPre p256Comb s₀) :
    WP isa vCombCode s₀ fun s' => abiPreserved s₀ s' ∧ VPost p256Comb s₀ s' := by
  have hCo : ∀ d, p256Comb.comb = some d → CombOk p256Comb d := by
    intro d h; have e : p256d = d := Option.some.inj h; rw [← e]; exact p256Comb_shape
  refine WP.seq (WP.mono (symFrame_ok p256d.tsym s₀ hp.sp4) fun s₁ P => ?_)
  have hp₁ := hp.toVPre.symAddr P hp.sp4
  have ht := vPrefixTables hp P
  refine WP.mono (verifyCombBody_ok (p256Comb_ok hI) hC (p256Comb_tables hC) hCo p256Comb_am3 hp₁
    (fun d hd => by have e : p256d = d := Option.some.inj hd; subst d; exact ht) signComb_spG vCombBody_sp)
    fun s₂ ⟨K, post⟩ => ?_
  have ha := K.abi hp₁
  have he := P.gpr .esp (by decide)
  refine ⟨⟨fun r hr => (ha.1 r hr).trans (P.gpr r (by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)), ?_⟩, ?_⟩
  · have ht := ha.2
    rw [he] at ht
    exact ht.trans (P.ret hp.sp4 (by have := hp.sp_fit; omega))
  · have harg : ∀ j < 4, arg s₁ j = arg s₀ j := fun j hj => P.arg hp.sp4 (by have := hp.sp_fit; omega)
    have hpk := prefix_bytesAt P hp.pk_stack (by change 65 ≤ 2 ^ 64; decide)
    have hdg := prefix_bytesAt P hp.dg_stack (by change 32 ≤ 2 ^ 64; decide)
    have hsig := prefix_bytesAt P hp.sig_stack (by change 64 ≤ 2 ^ 64; decide)
    simpa only [VPost, ptr, harg 0 (by decide), harg 1 (by decide), harg 2 (by decide), hpk, hdg, hsig] using post

def VCombPub (s t : State) : Prop :=
  s.gpr .esp = t.gpr .esp ∧ (∀ j < 4, arg s j = arg t j) ∧ s.syms p256d.tsym = t.syms p256d.tsym ∧
    Spec.Ecdsa.bytesAt s.mem (ptr s 0) (1+2*p256Comb.C.len)=Spec.Ecdsa.bytesAt t.mem (ptr t 0) (1+2*p256Comb.C.len) ∧
    Spec.Ecdsa.bytesAt s.mem (ptr s 2) (2*p256Comb.C.len)=Spec.Ecdsa.bytesAt t.mem (ptr t 2) (2*p256Comb.C.len)

theorem vComb_ct (hC : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) : ConstantTime isa (VCombPre p256Comb) VCombPub vCombCode := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  have preCT : RelCT isa (fun s t => VCombPre p256Comb s ∧ VCombPre p256Comb t ∧ VCombPub s t)
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
  obtain ⟨_, a, b, ⟨hp, hq, he, ha, hg, pk, sig⟩, P, Q⟩ := h
  have he' : s.gpr .esp = t.gpr .esp := by rw [P.gpr .esp (by decide), Q.gpr .esp (by decide), he]
  have ha' : ∀ j < 4, arg s j = arg t j := by
    intro j hj
    rw [P.arg hp.sp4 (by have := hp.sp_fit; omega), Q.arg hq.sp4 (by have := hq.sp_fit; omega), ha j hj]
  have hpub : VInputEq p256Comb s t := by
    apply VInputEq.of_bytes
    · have ps := prefix_bytesAt P hp.pk_stack (by change 65≤2^64; decide)
      have pt := prefix_bytesAt Q hq.pk_stack (by change 65≤2^64; decide)
      simpa only [ptr,P.arg (j:=0) hp.sp4 (by have:=hp.sp_fit; omega),
        Q.arg (j:=0) hq.sp4 (by have:=hq.sp_fit; omega),ps,pt] using pk
    · have ps := prefix_bytesAt P hp.sig_stack (by change 64≤2^64; decide)
      have pt := prefix_bytesAt Q hq.sig_stack (by change 64≤2^64; decide)
      simpa only [ptr,P.arg (j:=2) hp.sp4 (by have:=hp.sp_fit; omega),
        Q.arg (j:=2) hq.sp4 (by have:=hq.sp_fit; omega),ps,pt] using sig
  exact vCombBody_rel (p256Comb_ok hI) hC (p256Comb_tables hC) p256Comb_shape p256Comb_am3
    (hp.toVPre.symAddr P hp.sp4) (hq.toVPre.symAddr Q hq.sp4)
    (vPrefixTables hp P) (vPrefixTables hq Q) he' ha' hpub (by rw [P.addr, Q.addr, hg]) signComb_spG vCombBody_sp
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

end VG.Proof.Ecdsa.Verify.X86
