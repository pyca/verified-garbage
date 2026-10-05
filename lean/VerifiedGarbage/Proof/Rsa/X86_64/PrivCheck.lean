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
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

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

/-! ## Bits -/

theorem and1_toNat (x : BitVec 64) : (x &&& 1).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem and1_eq_one (x : BitVec 64) : x &&& 1 = 1 ↔ x.toNat % 2 = 1 := by
  rw [← BitVec.toNat_inj, and1_toNat]; rfl

theorem gOf_eq_one (a b c : BitVec 64) : gOf a b c = 1 ↔ a &&& 1 = 1 ∧ b &&& 1 = 1 ∧ c &&& 1 = 1 := by
  have key : ∀ x : Nat, x % 2 = 1 ↔ x.testBit 0 = true := fun x => by
    rw [Nat.testBit_zero]; simp
  simp only [gOf, and1_eq_one, BitVec.toNat_and, key, Nat.testBit_and, Bool.and_eq_true, and_assoc]

theorem and1_of_setWidth_one {x : BitVec 64} (h : x.setWidth 32 = 1) : x &&& 1 = 1 := by
  rw [and1_eq_one]
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth] at this
  have h2 : x.toNat % 2 = x.toNat % 2 ^ 32 % 2 := (Nat.mod_mod_of_dvd _ (by decide)).symm
  rw [h2, this]; rfl

theorem and1_of_setWidth_zero {x : BitVec 64} (h : x.setWidth 32 = 0) : x &&& 1 ≠ 1 := by
  rw [Ne, and1_eq_one]
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth] at this
  have h2 : x.toNat % 2 = x.toNat % 2 ^ 32 % 2 := (Nat.mod_mod_of_dvd _ (by decide)).symm
  rw [h2, this]; decide

/-! ## The check -/

/-- Whether `M` is released: `r₁` odd, `n` a valid modulus, and the public
operation of `M` (within BoringSSL's limits on `e`) the input. -/
def released (r₁ : BitVec 64) (nB eB xB mB : List Byte) : Prop :=
  r₁ &&& 1 = 1 ∧ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) nB.length ∧ Spec.Rsa.publicOpChecked nB eB mB = some xB

instance (r₁ : BitVec 64) (nB eB xB mB : List Byte) : Decidable (released r₁ nB eB xB mB) := by
  unfold released; infer_instance

/-- What the check returns: 1 if it releases `M`, 2 if `r₁` is odd, `n`
valid and the public operation of `M` succeeds but is not the input, 0
otherwise. -/
def checkResult (r₁ : BitVec 64) (nB eB xB mB : List Byte) : BitVec 64 :=
  if r₁ &&& 1 = 1 ∧ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) nB.length = true ∧
      (Spec.Rsa.publicOpChecked nB eB mB).isSome = true then
    (if Spec.Rsa.publicOpChecked nB eB mB = some xB then 1 else 2)
  else 0

theorem check_eq (pcName : String) (pc : Prog isa) (pdName : String) (pd : Prog isa) :
    seqs (check pcName pc pdName pd) =
      .seq (.block pcArgs) (.seq (.call pcName pc) (.seq (.block pdArgs) (.seq (.call pdName pd)
        (seqs PrivChecked.tail)))) := rfl

theorem bytesAt_length' (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem precompute_isSome (nB : List Byte) :
    (Spec.Rsa.publicPrecompute nB).isSome = Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) nB.length := by
  simp only [Spec.Rsa.publicPrecompute]
  split <;> simp_all

/-- The check's logic: what it returns and whether it releases `M`, from
what the calls returned (`r₂` and `r₃`) and wrote (`outB`). -/
theorem check_logic {r₁ r₂ r₃ : BitVec 64} {nB eB xB mB outB : List Byte}
    (h3 : match Spec.Rsa.publicPrecompute nB with
      | some _ => r₃.setWidth 32 = 1
      | none => r₃.setWidth 32 = 0)
    (h2 : (Spec.Rsa.publicPrecompute nB).isSome = true →
      match Spec.Rsa.publicOpChecked nB eB mB with
      | some y => r₂.setWidth 32 = 1 ∧ outB = y
      | none => r₂.setWidth 32 = 0) :
    result (gOf r₂ r₁ r₃) (decide (outB = xB)) = checkResult r₁ nB eB xB mB ∧
      ((gOf r₂ r₁ r₃ = 1 ∧ outB = xB) ↔ released r₁ nB eB xB mB) := by
  unfold checkResult released result
  rw [← precompute_isSome]
  cases hpc : Spec.Rsa.publicPrecompute nB with
  | none =>
    simp only [hpc] at h3
    have hg : gOf r₂ r₁ r₃ ≠ 1 := fun h => and1_of_setWidth_zero h3 ((gOf_eq_one _ _ _).mp h).2.2
    have hg' : ¬ gOf r₂ r₁ r₃ = 1#64 := hg
    simp [hg']
  | some ws =>
    simp only [hpc] at h3
    have h2 := h2 (by simp [hpc])
    cases hpo : Spec.Rsa.publicOpChecked nB eB mB with
    | none =>
      simp only [hpo] at h2
      have hg : gOf r₂ r₁ r₃ ≠ 1 := fun h => and1_of_setWidth_zero h2 ((gOf_eq_one _ _ _).mp h).1
      have hg' : ¬ gOf r₂ r₁ r₃ = 1#64 := hg
      simp [hg']
    | some y =>
      simp only [hpo] at h2
      obtain ⟨h2, rfl⟩ := h2
      have hg : gOf r₂ r₁ r₃ = 1 ↔ r₁ &&& 1 = 1 := by
        rw [gOf_eq_one]; exact ⟨fun h => h.2.1, fun h => ⟨and1_of_setWidth_one h2, h, and1_of_setWidth_one h3⟩⟩
      by_cases h1 : r₁ &&& 1 = 1
      · have hg1 : gOf r₂ r₁ r₃ = 1#64 := hg.mpr h1
        have h1' : r₁ &&& 1#64 = 1#64 := h1
        simp [hg1, h1']
      · have hg1 : ¬ gOf r₂ r₁ r₃ = 1#64 := fun h => h1 (hg.mp h)
        have h1' : ¬ r₁ &&& 1#64 = 1#64 := h1
        simp [hg1, h1']

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
