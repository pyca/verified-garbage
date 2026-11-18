module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombCT
public import VerifiedGarbage.Proof.Ecdsa.X86.CombCode
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombCode
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombBodyCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombFacts
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Main
public import VerifiedGarbage.Proof.Ecdsa.X86.CombPrefix
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMain
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafDigitChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafPrepChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafWindowChecks
import VerifiedGarbage.Proof.Ecdsa.X86.CombFinishCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombBodyCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFacts
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Main
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombPrefix
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMain
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafDigitChecks
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafPrepChecks
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafWindowChecks
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFinishCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! # Verification with the static comb table address -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86

def vCombCode : Prog isa := Impl.Ecdsa.Verify.X86.Cfg.verifyComb p256Comb
materialize_code vCombCode

/-- No instruction writes `esp`, and the calls use 20 bytes of stack. -/
theorem vComb_sp : SpOk vCombCode p256Comb.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem vCombBody_sp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.verifyCombBody p256Comb) p256Comb.stk :=
  SpOk.right (a := p256Comb.tableAddr) vComb_sp

/-- The order of P-256's base point is below `2^(8 len)`. -/
theorem p256Comb_nEnc : p256Comb.C.n < 2 ^ (8 * p256Comb.C.len) := by decide +kernel

theorem vComb_ok (hC : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) {s₀ : State} (hp : VCombPre p256Comb s₀) :
    WP isa vCombCode s₀ fun s' => abiPreserved s₀ s' ∧ VPost p256Comb s₀ s' := by
  have hCo : ∀ d, p256Comb.comb = some d → CombOk p256Comb d := by
    intro d h; have e : p256d = d := Option.some.inj h; rw [← e]; exact p256Comb_shape
  refine WP.seq (WP.mono (symFrame_ok p256d.tsym s₀ hp.sp4) fun s₁ P => ?_)
  have hp₁ := hp.toVPre.symAddr P hp.sp4
  have ht := vPrefixTables (d := p256d) rfl hp P
  refine WP.mono (verifyCombBody_ok (p256Comb_ok hI) hC p256Comb_nEnc (p256Comb_tables hC) hCo
    (fun _ => p256Comb_am3) hp₁
    (fun d hd => by have e : p256d = d := Option.some.inj hd; subst d; exact ht) signComb_spG vCombBody_sp)
    fun s₂ ⟨K, post⟩ => ?_
  have ha := K.abi hp₁
  have he := P.gpr .esp (by decide)
  refine ⟨⟨fun r hr => (ha.1 r hr).trans (P.gpr r (by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)), ?_⟩, ?_⟩
  · have ht := ha.2
    rw [he] at ht
    exact ht.trans (P.ret hp.sp4 (by have := hp.sp_fit; omega_using [this]))
  · have harg : ∀ j < 4, arg s₁ j = arg s₀ j := fun j hj => P.arg hp.sp4 (by have := hp.sp_fit; omega_using [hj, this])
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
    rw [P.arg hp.sp4 (by have := hp.sp_fit; omega_using [hj, this]), Q.arg hq.sp4 (by have := hq.sp_fit; omega_using [hj, this]), ha j hj]
  have hpub : VInputEq p256Comb s t := by
    apply VInputEq.of_bytes
    · have ps := prefix_bytesAt P hp.pk_stack (by change 65≤2^64; decide)
      have pt := prefix_bytesAt Q hq.pk_stack (by change 65≤2^64; decide)
      simpa only [ptr,P.arg (j:=0) hp.sp4 (by have:=hp.sp_fit; omega_using [this]),
        Q.arg (j:=0) hq.sp4 (by have:=hq.sp_fit; omega_using [this]),ps,pt] using pk
    · have ps := prefix_bytesAt P hp.sig_stack (by change 64≤2^64; decide)
      have pt := prefix_bytesAt Q hq.sig_stack (by change 64≤2^64; decide)
      simpa only [ptr,P.arg (j:=2) hp.sp4 (by have:=hp.sp_fit; omega_using [this]),
        Q.arg (j:=2) hq.sp4 (by have:=hq.sp_fit; omega_using [this]),ps,pt] using sig
  have hp₁ := hp.toVPre.symAddr P hp.sp4
  have hq₁ := hq.toVPre.symAddr Q hq.sp4
  have ht₁ := vPrefixTables (d := p256d) rfl hp P
  have ht₂ := vPrefixTables (d := p256d) rfl hq Q
  have hg' : s.gpr .eax = t.gpr .eax := by rw [P.addr, Q.addr, hg]
  exact vCombBody_rel (d := p256d) (p256Comb_ok hI) hC p256Comb_nEnc (p256Comb_tables hC) rfl p256Comb_shape
    (fun _ => p256Comb_am3) p256VerifyCT hp₁ hq₁ ht₁ ht₂ he' ha'
    (vPoints_rel (p256Comb_ok hI) hC (p256Comb_tables hC) p256Comb_shape p256Comb_am3 hp₁ hq₁ ht₁ ht₂
      he' ha' hpub hg' signComb_spG)
    signComb_spG vCombBody_sp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

end VG.Proof.Ecdsa.Verify.X86
