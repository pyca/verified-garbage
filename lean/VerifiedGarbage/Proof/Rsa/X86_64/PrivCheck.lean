import VerifiedGarbage.Proof.Rsa.X86_64.PrivTail

/-!
# `vg_rsa_private_checked` on x86-64: what follows the CRT

`check_ok` runs everything after the call of the CRT, from any state the
frame allows: whatever `M` holds and whatever the CRT returned (`r₁`), it
releases `M` to `out` (and returns 1) only if `r₁` is odd, `n` is a valid
modulus and the public operation of `M` with `e`, within BoringSSL's
limits, is the input; otherwise `out` is zeros. This is the fault tolerance
of the check: a faulted exponentiation releases nothing that fails it.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem bytes_wo (m : Mem) (base : Addr) {d a n : Nat} (v : BitVec 64) (h : d + 8 ≤ a ∨ a + n ≤ d)
    (ha : a + n ≤ 4096) (hd : d + 8 ≤ 4096) :
    Spec.Rsa.bytesAt (m.writeW (off base d) v) (off base a) n = Spec.Rsa.bytesAt m (off base a) n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact writeW_outside m base v (by omega) _ (by rw [ofs_off base (by omega)]; omega)

theorem words_wo (m : Mem) (base : Addr) {d a n : Nat} (v : BitVec 64) (h : d + 8 ≤ a ∨ a + 8 * n ≤ d)
    (ha : a + 8 * n ≤ 4096) (hd : d + 8 ≤ 4096) :
    Spec.Rsa.wordsAt (m.writeW (off base d) v) (off base a) n = Spec.Rsa.wordsAt m (off base a) n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  show (m.writeW (off base d) v).readW (off (off base a) (8 * i)) 64 = m.readW (off (off base a) (8 * i)) 64
  rw [off_off]
  exact (writeW_outside m base v (by omega)).word (by omega) (by omega)

theorem bytes_wo0 (m : Mem) (base : Addr) {a n : Nat} (v : BitVec 64) (h : 8 ≤ a) (ha : a + n ≤ 4096) :
    Spec.Rsa.bytesAt (m.writeW base v) (off base a) n = Spec.Rsa.bytesAt m (off base a) n := by
  have := bytes_wo m base (d := 0) v (.inl h) ha (by decide)
  simpa only [off, BitVec.add_zero] using this

theorem words_wo0 (m : Mem) (base : Addr) {a n : Nat} (v : BitVec 64) (h : 8 ≤ a) (ha : a + 8 * n ≤ 4096) :
    Spec.Rsa.wordsAt (m.writeW base v) (off base a) n = Spec.Rsa.wordsAt m (off base a) n := by
  have := words_wo m base (d := 0) v (.inl h) ha (by decide)
  simpa only [off, BitVec.add_zero] using this

theorem check_eq (pcName : String) (pc : Prog isa) (pdName : String) (pd : Prog isa) :
    seqs (check pcName pc pdName pd) =
      .seq (.block pcArgs) (.seq (.call pcName pc) (.seq (.block pdArgs) (.seq (.call pdName pd)
        (seqs PrivChecked.tail)))) := rfl

/-- Everything after the CRT, from any state the frame allows: whatever `M`
holds and the CRT returned. -/
theorem check_ok (M : Mont) (pcName pdName : String)
    (pcMx : (Precompute.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (pdMx : (Precomputed.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (pcNosp : NoSp (Precompute.code M.mm)) (pdNosp : NoSp (Checked.precomputedChecked M.mm))
    (pcDepth : (Precompute.code M.mm).depth = 0) (pdDepth : (Checked.precomputedChecked M.mm).depth = 0)
    {s t : State} (hp : PreF s) (he : Env s t) :
    WP isa (seqs (check pcName (Precompute.code M.mm) pdName (Checked.precomputedChecked M.mm))) t fun t' =>
      Env s t' ∧
      t'.gpr .rax = checkResult (t.gpr .rax) (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat) ∧
      Spec.Rsa.bytesAt t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
        (if released (t.gpr .rax) (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
            (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
            (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)
            (Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat)
          then Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat
          else List.replicate (s.gpr .rcx).toNat 0) ∧
      Spec.Rsa.bytesAt t'.mem (off (fb s) oM) (s.gpr .rcx).toNat = List.replicate (s.gpr .rcx).toNat 0 ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  have hk2 := hp.k2
  have hpw := preWords_le hp
  have csk : ∀ {rs : List Reg} {a b : State}, Keep rs a b → (∀ r ∈ calleeSaved, r ∉ rs) →
      ∀ r ∈ calleeSaved, b.gpr r = a.gpr r := fun k h r hr => k.gpr (h r hr)
  rw [check_eq]
  refine WP.seq (WP.mono_mx (by decide +kernel) (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] (pcArgs_ok hp he) rfl)
    fun t₁ ⟨⟨he₁, hm₁, hdi, hsi, hdx, hcx, h8, h9⟩, k₁⟩ hmx₁ => ?_)
  refine WP.seq (WP.mono (pc_call M pcName pcMx pcNosp pcDepth hp he₁ hdi hsi hdx hcx h8 h9)
    fun t₂ ⟨he₂, hpc, hM₂, hR1₂, hcs₂, hmx₂⟩ => ?_)
  refine WP.seq (WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (pdArgs_ok hp he₂) rfl)
    fun t₃ ⟨⟨he₃, hm₃, hdi₃, hsi₃, hdx₃, hcx₃, h8₃, h9₃⟩, k₃⟩ hmx₃ => ?_)
  have hw : ∀ {d : Nat}, d < 4 → word t₃.mem (fb s) (8 * d) =
      [off (fb s) oM, s.gpr .rcx, stackArg s 12, stackArg s 13].getD d 0 := fun {d} hd => by
    rw [hm₃]
    rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 by omega) with rfl | rfl | rfl | rfl
    · simp (disch := decide) only [word_wo, word_self0, Nat.mul_zero]
      rfl
    · simp (disch := decide) only [word_wo, word_writeW_self, Nat.mul_one]; rfl
    · simp (disch := decide) only [word_wo, word_writeW_self]; rfl
    · simp (disch := decide) only [word_writeW_self]; rfl
  refine WP.seq (WP.mono (pd_call M pdName pdMx pdNosp pdDepth hp he₃ (hw (d := 0) (by decide))
    (hw (d := 1) (by decide)) (hw (d := 2) (by decide)) (hw (d := 3) (by decide)) hdi₃ hsi₃ hdx₃ hcx₃ h8₃ h9₃)
    fun t₄ ⟨he₄, hpd, hM₄, hR1₄, hR3₄, hcs₄, hmx₄⟩ => ?_)
  refine WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .r11, .rdi, .rsi, .rcx, .r10, .rdx, .r9, .r8] (tail_ok hp he₄) (by decide +kernel))
    fun t' ⟨⟨hax, hout, hM', he'⟩, k₅⟩ hmx₅ => ⟨he', ?_, ?_, hM',
      fun r hr => by rw [csk k₅ (by decide) r hr, hcs₄ r hr, csk k₃ (by decide) r hr, hcs₂ r hr,
        csk k₁ (by decide) r hr],
      by rw [hmx₅, hmx₄, hmx₃, hmx₂, hmx₁]⟩ <;> clear hM'
  all_goals
    -- The values the tail reads.
    have hr1 : word t₄.mem (fb s) oR1 = t.gpr .rax := by
      rw [hR1₄, hm₃]
      simp (disch := decide) only [word_wo, word_wo0]
      rw [hR1₂, hm₁, word_writeW_self]
    have hr3 : word t₄.mem (fb s) oR3 = t₂.gpr .rax := by
      rw [hR3₄, hm₃]
      simp (disch := decide) only [word_wo, word_wo0, word_writeW_self]
    have hmb : Spec.Rsa.bytesAt t₃.mem (off (fb s) oM) (s.gpr .rcx).toNat =
        Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat := by
      rw [hm₃]
      simp (disch := first | decide | (simp only [oM, oR3, oR1]; omega)) only [bytes_wo, bytes_wo0]
      rw [hM₂, hm₁, bytes_wo _ _ _ (.inl (by decide)) (by unfold oM; omega) (by decide)]
    have hpre : Spec.Rsa.wordsAt t₃.mem (off (fb s) oPre) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) =
        Spec.Rsa.wordsAt t₂.mem (off (fb s) oPre) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) := by
      rw [hm₃]
      simp (disch := first | decide | (simp only [oPre, oR3]; omega)) only [words_wo, words_wo0]
    rw [hr1, hr3] at hax hout
    rw [hM₄, hmb] at hout
    simp only [hmb] at hpd
    have h3 : match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) with
        | some _ => (t₂.gpr .rax).setWidth 32 = 1
        | none => (t₂.gpr .rax).setWidth 32 = 0 := by
      cases hc : Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) <;>
        simp only [hc] at hpc ⊢ <;> exact hpc.1
    have hl := check_logic (r₁ := t.gpr .rax) (r₂ := t₄.gpr .rax) (r₃ := t₂.gpr .rax)
      (eB := Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (mB := Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat)
      (outB := Spec.Rsa.bytesAt t₄.mem (s.gpr .rdi) (s.gpr .rcx).toNat)
      (xB := Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) h3 (fun hs => by
        obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp hs
        rw [hws] at hpc
        have := hpd _ (bytesAt_length' _ _ _) (by rw [hws, hpre, hpc.2])
        cases hpo : Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
            (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
            (Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat) <;>
          simp only [hpo, Spec.Rsa.written] at this ⊢
        · exact this.1
        · exact this)
    first | (rw [hax]; exact hl.1) | (rw [hout]; exact if_congr hl.2 rfl rfl)

end VG.Proof.Rsa.X86_64
