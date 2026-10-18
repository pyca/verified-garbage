module

public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPcCheck
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
import VerifiedGarbage.Proof.Bignum.PrivPre

/-!
# `vg_rsa_private_checked_precomputed` on x86-64: correctness

The frame's push, the CRT's arguments and call (`crtArgsP_ok`,
`crtPc_call`), the check (`checkP_ok`) and the pop: `codeP_correct`, for
every implementation of the CRT.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivCheckedPc
open VG.Impl.Rsa.X86_64.PrivChecked (sp lea oM)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa (bytesAt_length' outcome_eq)

/-- The frame: its body runs from `allocState frameBytes s` and ends with
`rsp` and the writable regions as the push left them. -/
theorem wp_allocP {body : Prog isa} {s : State} {Q : State → Prop} (hsp : frameBytes ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (allocState frameBytes s) fun s₂ => s₂.gpr .rsp = fbP s ∧
      s₂.wr = (allocState frameBytes s).wr ∧ Q (freed frameBytes s₂)) :
    WP isa (.frame (.alloc frameBytes) body (.free frameBytes)) s Q := by
  obtain ⟨t, s₂, he, hsp₂, hw, hq⟩ := hb
  have ha : isa.push (.alloc frameBytes) s = some (allocState frameBytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨by decide, by decide, by decide, hsp⟩
  have hf : isa.pop (.free frameBytes) (allocState frameBytes s) s₂ = some (freed frameBytes s₂) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by decide, by decide, by decide, hsp₂, hw, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

theorem bodyP_eq (crtName : String) (crt : Prog isa) (pdName : String) (pd : Prog isa) :
    PrivCheckedPc.body crtName crt pdName pd =
      .seq (.block crtArgs) (.seq (.call crtName crt)
        (seqs (([.block pdArgs, .call pdName pd] : List (Prog isa)) ++ PrivCheckedPc.tail))) := rfl

/-- The return address is outside everything the function writes. -/
theorem retP_frame {s : State} (hp : PreFPc s) {m : Mem} (h : Frame [stkRP s, outR s, scrR s] s.mem m) :
    m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  have hsp2 := hp.sp2
  refine h.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := Offset.disjoint_below (s.gpr .rsp) (n := stackBytesPc) (d := 0) (k := 8)
      (by unfold stackBytesPc; omega)
    simpa only [stkRP, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  · exact hp.dRo
  · exact hp.dRs

theorem codeP_correct (v : CrtImpl) (pdName : String) (s : State) (h : chkPcContract.pre s) :
    ∃ t s', Exec isa (PrivCheckedPc.code v.pcrtName v.pcrt pdName v.pubOp.code) s t s' ∧
      abiPreserved s s' ∧ chkPcContract.post s s' := by
  have hp := preFPc_of h
  have hk2 := hp.k2
  suffices hw : WP isa (PrivCheckedPc.code v.pcrtName v.pcrt pdName v.pubOp.code) s
      fun s' => abiPreserved s s' ∧ chkPcContract.post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  refine wp_allocP (by have := hp.sp1; unfold stackBytesPc at this; unfold frameBytes; omega) ?_
  rw [bodyP_eq]
  refine WP.seq (WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (crtArgsP_ok hp) (by decide +kernel))
    fun t₁ ⟨⟨he₁, _, hargs, hdi, hsi, hdx, hcx, h8, h9⟩, k₁⟩ hmx₁ => ?_)
  refine WP.seq (WP.mono (crtPc_call v hp he₁ hargs hdi hsi hdx hcx h8 h9) fun t₂ ⟨he₂, hcrt, hcs₂, hmx₂⟩ => ?_)
  refine WP.mono (checkP_ok v.pubOp pdName hp he₂)
    fun t₃ ⟨he₃, hck, _, hcs₃, hmx₃⟩ => ?_
  refine ⟨he₃.rsp, by rw [he₃.wr]; rfl, ⟨fun r hr => ?_, retP_frame hp he₃.mem, ?_⟩, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      show t₃.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
      rw [he₃.rsp, BitVec.sub_add_cancel]
    · show (if r = .rsp then _ else t₃.gpr r) = s.gpr r
      simp only [hr', ↓reduceIte]
      rw [hcs₃ r hr, hcs₂ r hr, k₁.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)]
      simp only [allocStateP_gpr, hr', ↓reduceIte]
  · show t₃.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
    rw [hmx₃, hmx₂, hmx₁]; rfl
  · have hfr : (freed frameBytes t₃).gpr .rax = t₃.gpr .rax := rfl
    have hfm : (freed frameBytes t₃).mem = t₃.mem := rfl
    simp only [chkPcContract, hfr, hfm]
    intro hpre
    have hpub := privatePre_public (bytesAt_length' _ _ _)
      (by rw [hp.hprl]; unfold Spec.Rsa.privatePrecomputedWords; omega) hpre
    obtain ⟨hrax, hout⟩ := hck hpub
    exact outcome_eq (bytesAt_length' _ _ _) (by rw [bytesAt_length']) (hcrt hpre) hrax hout

end VG.Proof.Rsa.X86_64
