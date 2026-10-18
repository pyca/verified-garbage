module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VMain
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: correctness

The frame, the prologues, the checks and `verifyMain`, for the hash
functions the selectors name, whose streaming functions the tables hold:
the registers the ABI keeps whatever `pre` holds, and, if `pre` holds the
values for `n`, `Spec.RsaPss.verify`'s result (`ver_correct`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes)
open VG.Proof.RsaOaep.X86_64 (encStack stkR fb frR wp_alloc freed lenOf fns_of_tab)
open VG.Proof.MlKem.X86_64 (ifp ifn)
open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Proof.HashFns (StreamingOK)

variable {s : State}

/-- What the function's caller sees of the registers and the stack, from a
state in the frame. -/
theorem verEnd_abi (hp : VPre s) {s₂ : State} (he : VEnv s s₂) :
    s₂.gpr .rsp = fb s ∧ s₂.wr = (allocState frameBytes s).wr ∧ abiPreserved s (freed frameBytes s₂) := by
  refine ⟨he.rsp, by rw [he.wr, hp.wr], fun r hr => ?_, ?_, he.mx⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      show s₂.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
      rw [he.rsp, BitVec.sub_add_cancel]
    · show (if r = .rsp then _ else s₂.gpr r) = s.gpr r
      simp only [hr', ↓reduceIte]
      exact he.cs r hr hr'
  · have hsp2 := hp.sp2
    refine Frame.readW he.fr (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := Offset.disjoint_below (s.gpr .rsp) (n := encStack) (d := 0) (k := 8) (by unfold encStack; omega)
      simpa only [stkR, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
    · exact hp.dRS

/-- The result, from a state in the frame: 1 if `verify` holds. -/
def VRes (s : State) (H G : Spec.Mgf1.Hash) (r : BitVec 64) : Prop :=
  VConsistent s → r = if Spec.RsaPss.verify H G (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r8) H.len)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat)
    (Spec.RsaPss.expectedSaltLen (stackArg s 3) ((stackArg s 2).setWidth 32)) then 1 else 0

variable {TH TG : Spec.HashFns.Streaming} {Hh Gh : Spec.Mgf1.Hash} (hTH : StreamingOK TH Hh)
  (hTG : StreamingOK TG Gh)

include hTH hTG in
/-- For the hash functions `Hh` and `Gh` that the selectors name, whose
streaming functions are `TH` and `TG`. -/
theorem ver_body (v : PublicImpl) (hp : VPre s) (fH : VFns s TH 10) (fG : VFns s TG 11)
    (eH : Spec.HashId.mgf1 (vselH s) = some Hh) (eG : Spec.HashId.mgf1 (vselG s) = some Gh) :
    WP isa (verify v.name v.code) s fun s' => abiPreserved s s' ∧ VRes s Hh Gh (s'.gpr .rax) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hDH : TH.S.digestBytes = lenOf (vselH s) := VG.Proof.RsaOaep.X86_64.lenOf_eq hTH eH
  refine wp_alloc (by have := hp.sp1; unfold encStack at this; unfold frameBytes; omega) ?_
  refine verBody_ok v.name v.code hp (fun t he hax hb => ?_) fun t he L R hax hn0 hfit => ?_
  · obtain ⟨h1, h2, h3⟩ := verEnd_abi hp he
    refine ⟨h1, h2, h3, fun _ => ?_⟩
    show t.gpr .rax = _
    rw [hax]
    obtain ⟨k', hk'⟩ : ∃ k', (s.gpr .rsi).toNat = k' + 1 := ⟨(s.gpr .rsi).toNat - 1, by omega⟩
    rw [hk', bytesAt_cons]
    by_cases h0 : s.mem (s.gpr .rdi) = 0
    · rw [h0, Any.verify_zero]; rfl
    · rw [Any.verify_short]; · rfl
      have hn0 : n0v s ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
      rw [VG.Proof.RsaPss.emLength_eq _ h0]
      have hsl : (Spec.RsaPss.expectedSaltLen (stackArg s 3) ((stackArg s 2).setWidth 32)).getD 0 = vsl s := by
        unfold Spec.RsaPss.expectedSaltLen vsl vfixed
        by_cases h : (stackArg s 2).setWidth 32 = 0
        · rw [ifp h, decide_eq_true h]; rfl
        · rw [ifn h, decide_eq_false h]; rfl
      rw [hsl, hTH.len, hDH, List.length_map, List.length_range]
      have hb' : ¬ lenOf (vselH s) + 2 + vsl s ≤ (s.gpr .rsi).toNat - loV (n0v s) := fun h => hb ⟨hn0, h⟩
      unfold loV n0v at hb'
      by_cases h1 : (s.mem (s.gpr .rdi)).toNat = 1
      · rw [ifp h1] at hb' ⊢; omega
      · rw [ifn h1] at hb' ⊢; omega
  · refine WP.mono (verMain_ok hTH hTG v hp fH fG eH eG he L R hax hn0 hfit) fun t' ⟨he', hr⟩ => ?_
    obtain ⟨h1, h2, h3⟩ := verEnd_abi hp he'
    exact ⟨h1, h2, h3, hr⟩

end VG.Proof.RsaPss.X86_64
