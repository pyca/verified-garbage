import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncTail
import VerifiedGarbage.Proof.Framework.Block

/-!
# RSAES-PKCS1-v1_5 encryption on x86-64: correctness

The frame's push, `EM` (`em_ok`), the call (`callArgs_run`, `pub_call`),
the mask (`tail_ok`) and the pop: `enc_correct`, for every implementation
of `vg_rsa_public_checked`.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- The state after the frame's pop, from the state `s₂` its body ends in. -/
def freed (bytes : Nat) (s₂ : State) : State :=
  { s₂.setReg .rsp (s₂.gpr .rsp + BitVec.ofNat 64 bytes) with wr := s₂.wr.tail }

/-- A frame of `bytes` bytes: its body runs from `allocState bytes s` and
ends with `rsp` and the writable regions as the push left them. -/
theorem wp_alloc {bytes : Nat} {body : Prog isa} {s : State} {Q : State → Prop} (h0 : 0 < bytes)
    (h1 : bytes < 4096) (h8 : bytes % 8 = 0) (hsp : bytes ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (allocState bytes s) fun s₂ => s₂.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes ∧
      s₂.wr = (allocState bytes s).wr ∧ Q (freed bytes s₂)) :
    WP isa (.frame (.alloc bytes) body (.free bytes)) s Q := by
  obtain ⟨t, s₂, he, hsp₂, hw, hq⟩ := hb
  have ha : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨h0, h1, h8, hsp⟩
  have hf : isa.pop (.free bytes) (allocState bytes s) s₂ = some (freed bytes s₂) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨h0, h1, h8, hsp₂, hw, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

/-- Four pieces, then the rest. -/
theorem wp_seq4 {a b c d rest : Prog isa} {s : State} {P Q : State → Prop}
    (h : WP isa (.seq a (.seq b (.seq c d))) s P) (hk : ∀ t, P t → WP isa rest t Q) :
    WP isa (.seq a (.seq b (.seq c (.seq d rest)))) s Q := by
  rw [VG.WP.seq_iff] at h ⊢
  refine WP.mono h fun t₁ h₁ => ?_
  rw [VG.WP.seq_iff] at h₁ ⊢
  refine WP.mono h₁ fun t₂ h₂ => ?_
  rw [VG.WP.seq_iff] at h₂ ⊢
  refine WP.mono h₂ fun t₃ h₃ => ?_
  rw [VG.WP.seq_iff]
  exact WP.mono h₃ hk

theorem body_eq (pubName : String) (pub : Prog isa) :
    body pubName pub = .seq (.block setup) (.seq psLoop (.seq (.block sep) (.seq msgCopy (.seq (.block callArgs)
      (.seq (.call pubName pub) (.seq (.block maskArgs) (.seq maskLoop (.block [.mov .rax (.reg .r11)])))))))) :=
  rfl

/-! ## The result -/

theorem encrypt_eq {nB eB M PS : List Byte} (hm : M.length + 11 ≤ nB.length)
    (hps : PS.length = nB.length - M.length - 3) :
    Spec.RsaPkcs1Enc.encrypt nB eB M PS =
      if PS.all (· != 0) then Spec.Rsa.publicOpChecked nB eB (Spec.RsaPkcs1Enc.encode M PS) else none := by
  simp only [Spec.RsaPkcs1Enc.encrypt, hm, hps, true_and]

theorem freed_mem (bytes : Nat) (t : State) : (freed bytes t).mem = t.mem := rfl
theorem freed_rax (bytes : Nat) (t : State) : (freed bytes t).gpr .rax = t.gpr .rax := rfl

theorem not_mem_of {r : Reg} {L L' : List Reg} (h : r ∉ L') (hs : ∀ x ∈ L, x ∈ L') : r ∉ L :=
  fun hm => h (hs r hm)

theorem pmask_true : pmask true = BitVec.allOnes 64 := rfl
theorem pmask_false : pmask false = 0 := rfl

/-- The postcondition, from the result of the call masked by the zero test
of `PS`. -/
theorem result_ok {s : State} (hp : EPre s) {t t' : State} (h : PostCall s t) (ht : Tail s t t') :
    encK.post s t' := by
  have hn : (nB s).length = kOf s := bytesAt_len _ _ _
  have hM : (msgB s).length = (stackArg s 1).toNat := bytesAt_len _ _ _
  have hPS : (psB s).length = (stackArg s 3).toNat := bytesAt_len _ _ _
  have hml := hp.hml
  have hpl := hp.hpl
  simp only [encK]
  rw [encrypt_eq (by rw [hn, hM]; exact hml) (by rw [hPS, hn, hM]; exact hpl)]
  have hres := h.res
  have hout := ht.out
  rw [ht.rax]
  cases hok : psOk s
  · simp only [psOk] at hok
    simp only [hok, Bool.false_eq_true, ↓reduceIte, pmask_false, show (0 : BitVec 64) = 0#64 from rfl,
      BitVec.and_zero] at hout ⊢
    exact ⟨rfl, hout⟩
  · simp only [psOk] at hok
    simp only [hok, ↓reduceIte, pmask_true, BitVec.and_allOnes] at hout ⊢
    cases hq : Spec.Rsa.publicOpChecked (nB s) (eB s) (Spec.RsaPkcs1Enc.encode (msgB s) (psB s)) with
    | none => rw [hq] at hres; exact ⟨hres.1, hout.trans hres.2⟩
    | some y => rw [hq] at hres; exact ⟨hres.1, hout.trans hres.2⟩

/-! ## The whole function -/

/-- The return address is outside everything the function writes. -/
theorem ret_frame {s : State} (hp : EPre s) {m : Mem} (h : Frame [stkR s, outR s, scrR s] s.mem m) :
    m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  have hsp2 := hp.sp2
  refine h.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := Offset.disjoint_below (s.gpr .rsp) (n := encStack) (d := 0) (k := 8)
      (by unfold encStack frameBytes; omega)
    simpa only [stkR, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  · exact hp.dRo
  · exact hp.dRs

theorem enc_correct (v : PubImpl) (s : State) (h : encK.pre s) :
    ∃ t s', Exec isa (code v.name v.code) s t s' ∧ abiPreserved s s' ∧ encK.post s s' := by
  have hp := ePre_of h
  suffices hw : WP isa (code v.name v.code) s fun s' => abiPreserved s s' ∧ encK.post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  refine wp_alloc (by decide) (by decide) (by decide) (by have := hp.sp1; unfold encStack at this; omega) ?_
  rw [body_eq]
  refine wp_seq4 (WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r10, .r11] (em_ok hp) (by decide +kernel))
    fun t ⟨hpc, k⟩ hmx => (⟨hpc, k, hmx⟩ : PreCall s t ∧ Keep _ (allocState frameBytes s) t ∧ _)) ?_
  intro t₁ ⟨hpc, k₁, hmx₁⟩
  refine WP.seq (WP.mono_mx (by decide +kernel) (callArgs_run hp hpc)
    fun t₂ ⟨hm₂, hdi, hsi, hdx, hcx, h8, h9, k₂⟩ hmx₂ => ?_)
  have hpc₂ : PreCall s t₂ := ⟨(k₂.gpr (by decide)).trans hpc.rsp, k₂.2.1.trans hpc.rd, k₂.2.2.trans hpc.wr,
    hm₂ ▸ hpc.out, hm₂ ▸ hpc.slots, hm₂ ▸ hpc.sZ, hm₂ ▸ hpc.em⟩
  refine WP.seq (WP.mono (pub_call v hp hpc₂ hdi hsi hdx hcx h8 h9) fun t₃ ⟨hpost, hcs₃, hmx₃⟩ => ?_)
  refine WP.mono_mx (by decide +kernel) (tail_ok hp hpost) fun t₄ ht hmx₄ => ?_
  refine ⟨ht.rsp, by rw [ht.wr]; rfl, ⟨fun r hr => ?_, ret_frame hp ht.mem, ?_⟩, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      show t₄.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
      rw [ht.rsp, BitVec.sub_add_cancel]
    · show (if r = .rsp then _ else t₄.gpr r) = s.gpr r
      have hnr : r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [hr', ↓reduceIte]
      rw [ht.keep.gpr (not_mem_of hnr (by decide)), hcs₃ r hr, k₂.gpr (not_mem_of hnr (by decide)),
        k₁.gpr (not_mem_of hnr (by decide))]
      simp only [allocState_gpr, hr', ↓reduceIte]
  · show t₄.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
    rw [hmx₄, hmx₃, hmx₂, hmx₁]; rfl
  · have := result_ok hp hpost ht
    simp only [encK] at this ⊢
    rw [freed_mem, freed_rax]; exact this

end VG.Proof.RsaPkcs1Enc.X86_64
