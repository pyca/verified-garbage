import VerifiedGarbage.Proof.Rsa.X86_64.PrivOutcome

/-!
# `vg_rsa_private_checked` on x86-64: correctness

The frame's push, the CRT's arguments and call (`crtArgs_ok`, `crt_call`),
the check (`check_ok`) and the pop: `code_correct`, for every implementation
of the CRT.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- The state after the frame's pop, from the state `s₂` its body ends in. -/
def freed (bytes : Nat) (s₂ : State) : State :=
  { s₂.setReg .rsp (s₂.gpr .rsp + BitVec.ofNat 64 bytes) with wr := s₂.wr.tail }

/-- The frame: its body runs from `allocState frameBytes s` and ends with
`rsp` and the writable regions as the push left them. -/
theorem wp_alloc {body : Prog isa} {s : State} {Q : State → Prop} (hsp : frameBytes ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (allocState frameBytes s) fun s₂ => s₂.gpr .rsp = fb s ∧
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

theorem body_eq (crtName : String) (crt : Prog isa) (pcName : String) (pc : Prog isa) (pdName : String)
    (pd : Prog isa) :
    body crtName crt pcName pc pdName pd =
      .seq (.block crtArgs) (.seq (.call crtName crt) (seqs (check pcName pc pdName pd))) := rfl

/-- The return address is outside everything the function writes. -/
theorem ret_frame {s : State} (hp : PreF s) {m : Mem} (h : Frame [stkR s, outR s, scrR s] s.mem m) :
    m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  have hsp2 := hp.sp2
  refine h.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := Offset.disjoint_below (s.gpr .rsp) (n := stackBytes) (d := 0) (k := 8)
      (by unfold stackBytes; omega)
    simpa only [stkR, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  · exact hp.dRo
  · exact hp.dRs

theorem code_correct (v : CrtImpl) (pcName pdName : String) (s : State) (h : chkContract.pre s) :
    ∃ t s', Exec isa (code v.name v.code pcName (Precompute.code v.mont.mm) pdName
        (Checked.precomputedChecked v.mont.mm)) s t s' ∧ abiPreserved s s' ∧ chkContract.post s s' := by
  have hp := preF_of h
  have hk2 := hp.k2
  suffices hw : WP isa (code v.name v.code pcName (Precompute.code v.mont.mm) pdName
      (Checked.precomputedChecked v.mont.mm)) s fun s' => abiPreserved s s' ∧ chkContract.post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  refine wp_alloc (by have := hp.sp1; unfold stackBytes at this; unfold frameBytes; omega) ?_
  rw [body_eq]
  refine WP.seq (WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .rdi, .rsi, .r8, .r9] (crtArgs_ok hp) (by decide +kernel))
    fun t₁ ⟨⟨he₁, _, hargs, hdi, hsi, hdx, hcx, h8, h9⟩, k₁⟩ hmx₁ => ?_)
  refine WP.seq (WP.mono (crt_call v hp he₁ hargs hdi hsi hdx hcx h8 h9) fun t₂ ⟨he₂, hcrt, hcs₂, hmx₂⟩ => ?_)
  refine WP.mono (check_ok v.mont pcName pdName v.pcMx v.pdMx v.pcNosp v.pdNosp v.pcDepth v.pdDepth hp he₂)
    fun t₃ ⟨he₃, hrax, hout, _, hcs₃, hmx₃⟩ => ?_
  refine ⟨he₃.rsp, by rw [he₃.wr]; rfl, ⟨fun r hr => ?_, ret_frame hp he₃.mem, ?_⟩, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      show t₃.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
      rw [he₃.rsp, BitVec.sub_add_cancel]
    · show (if r = .rsp then _ else t₃.gpr r) = s.gpr r
      simp only [hr', ↓reduceIte]
      rw [hcs₃ r hr, hcs₂ r hr, k₁.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)]
      simp only [allocState_gpr, hr', ↓reduceIte]
  · show t₃.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
    rw [hmx₃, hmx₂, hmx₁]; rfl
  · have hfr : (freed frameBytes t₃).gpr .rax = t₃.gpr .rax := rfl
    have hfm : (freed frameBytes t₃).mem = t₃.mem := rfl
    simp only [chkContract, hfr, hfm]
    exact outcome_eq (bytesAt_length' _ _ _) (by rw [bytesAt_length']) hcrt hrax hout

end VG.Proof.Rsa.X86_64
