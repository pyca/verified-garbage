import VerifiedGarbage.Proof.Rsa.X86_64.PrivCheck
import VerifiedGarbage.Proof.Rsa.Octets

/-!
# `vg_rsa_private_checked` on x86-64: the outcome

What the CRT returns and writes, followed by what the check returns and
releases (`check_ok`), is `privateChecked`'s outcome (`outcome_eq`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- The CRT's result `mB` (returning `rc`), and the check's of it (returning
`r` and writing `outB`), are the checked private operation's. -/
theorem outcome_eq {m m' : Mem} {M out : Addr} {k : Nat} {rc r : BitVec 64}
    {nB eB xB pB qB dPB dQB qInvB : List Byte} (hn : nB.length = k) (hx : xB.length = k)
    (hcrt : Spec.Rsa.written m M k (rc.setWidth 32) (Spec.Rsa.privateCrt nB xB pB qB dPB dQB qInvB))
    (hr : r = checkResult rc nB eB xB (Spec.Rsa.bytesAt m M k))
    (hout : Spec.Rsa.bytesAt m' out k =
      if released rc nB eB xB (Spec.Rsa.bytesAt m M k) then Spec.Rsa.bytesAt m M k else List.replicate k 0) :
    Spec.Rsa.writtenOutcome m' out k (r.setWidth 32) (Spec.Rsa.privateChecked nB eB xB pB qB dPB dQB qInvB) := by
  rw [Proof.Rsa.privateChecked_of_crt (hx.trans hn.symm)]
  cases hc : Spec.Rsa.privateCrt nB xB pB qB dPB dQB qInvB with
  | none =>
    rw [hc] at hcrt
    have h1 := and1_of_setWidth_zero hcrt.1
    have hrel : ¬ released rc nB eB xB (Spec.Rsa.bytesAt m M k) := fun h => h1 h.1
    simp only [checkResult, h1, false_and, ↓reduceIte] at hr
    simp only [hrel, ↓reduceIte] at hout
    exact ⟨by rw [hr]; rfl, hout⟩
  | some y =>
    rw [hc] at hcrt
    obtain ⟨hr1, hy⟩ := hcrt
    obtain ⟨hm, hs⟩ := Proof.Rsa.privateCrt_some hc
    have h1 := and1_of_setWidth_one hr1
    rw [hy] at hr hout
    by_cases he : Spec.Rsa.exponentValid (Spec.Rsa.os2ip eB) = true
    · have hsome := hs eB he
      by_cases hp : Spec.Rsa.publicOpChecked nB eB y = some xB
      · have hrel : released rc nB eB xB y := ⟨h1, hm, hp⟩
        simp only [checkResult, h1, hm, hp, ↓reduceIte] at hr
        simp only [hrel, ↓reduceIte] at hout
        simp only [he, hp, ↓reduceIte]
        exact ⟨by rw [hr]; rfl, hout⟩
      · have hrel : ¬ released rc nB eB xB y := fun h => hp h.2.2
        simp only [checkResult, h1, hm, hsome, hp, and_self, ↓reduceIte] at hr
        simp only [hrel, ↓reduceIte] at hout
        simp only [he, hp, ↓reduceIte]
        exact ⟨by rw [hr]; rfl, hout⟩
    · have hnone : Spec.Rsa.publicOpChecked nB eB y = none := by
        simp only [Spec.Rsa.publicOpChecked, he]; rfl
      have hrel : ¬ released rc nB eB xB y := fun h => by
        have := h.2.2; rw [hnone] at this; cases this
      simp only [checkResult, hnone, Option.isSome_none, Bool.false_eq_true, and_false, ↓reduceIte] at hr
      simp only [hrel, ↓reduceIte] at hout
      simp only [he, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by rw [hr]; rfl, hout⟩

/-! ## Fault tolerance -/

/-- What the check releases passes it: a result 1 means `mB` (of `k` octets)
is below `n` and `mB^e mod n` is the input. -/
theorem checkResult_sound {r₁ : BitVec 64} {nB eB xB mB : List Byte} (hx : xB.length = nB.length)
    (h : checkResult r₁ nB eB xB mB = 1) :
    released r₁ nB eB xB mB ∧ Spec.Rsa.os2ip mB < Spec.Rsa.os2ip nB ∧
      Spec.Rsa.os2ip mB ^ Spec.Rsa.os2ip eB % Spec.Rsa.os2ip nB = Spec.Rsa.os2ip xB := by
  simp only [checkResult] at h
  split at h
  · rename_i hc
    split at h
    · rename_i hp
      exact ⟨⟨hc.1, hc.2.1, hp⟩, Proof.Rsa.publicOpChecked_sound hx hp⟩
    · cases h
  · cases h

/-- The check and the release are correct whatever the CRT left in `M` and
returned: they release `M` (returning 1) only if `M` is below `n` and
`M^e mod n` is the input, and write zeros otherwise; `M` is zeroed either
way. A fault in the CRT's computation (of the result, of its return value,
or of both) is never released. -/
theorem check_faultTolerant (M : Mont) (pcName pdName : String)
    (pcMx : (Precompute.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (pdMx : (Precomputed.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (pcNosp : NoSp (Precompute.code M.mm)) (pdNosp : NoSp (Checked.precomputedChecked M.mm))
    (pcDepth : (Precompute.code M.mm).depth = 0) (pdDepth : (Checked.precomputedChecked M.mm).depth = 0)
    {s t : State} (hp : PreF s) (he : Env s t) :
    WP isa (seqs (PrivChecked.check pcName (Precompute.code M.mm) pdName
        (Checked.precomputedChecked M.mm))) t fun t' =>
      (t'.gpr .rax = 1 →
        Spec.Rsa.bytesAt t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
            Spec.Rsa.bytesAt t.mem (off (fb s) PrivChecked.oM) (s.gpr .rcx).toNat ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (off (fb s) PrivChecked.oM) (s.gpr .rcx).toNat) <
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (off (fb s) PrivChecked.oM) (s.gpr .rcx).toNat) ^
              Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) %
              Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) =
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)) ∧
      (t'.gpr .rax ≠ 1 → Spec.Rsa.bytesAt t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
        List.replicate (s.gpr .rcx).toNat 0) ∧
      Spec.Rsa.bytesAt t'.mem (off (fb s) PrivChecked.oM) (s.gpr .rcx).toNat =
        List.replicate (s.gpr .rcx).toNat 0 :=
  WP.mono (check_ok M pcName pdName pcMx pdMx pcNosp pdNosp pcDepth pdDepth hp he)
    fun t' ⟨_, hax, hout, hM, _⟩ => by
      have hx : (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat).length =
          (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat).length := by
        rw [bytesAt_length', bytesAt_length']
      refine ⟨fun h1 => ?_, fun h1 => ?_, hM⟩
      · obtain ⟨hrel, hs⟩ := checkResult_sound hx (hax ▸ h1)
        simp only [hrel, ↓reduceIte] at hout
        exact ⟨hout, hs⟩
      · have hrel : ¬ released (t.gpr .rax) (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
            (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
            (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)
            (Spec.Rsa.bytesAt t.mem (off (fb s) PrivChecked.oM) (s.gpr .rcx).toNat) := fun h => by
          apply h1
          rw [hax]
          simp only [checkResult, h.1, h.2.1, h.2.2, Option.isSome_some, and_self, ↓reduceIte]
        simp only [hrel, ↓reduceIte] at hout
        exact hout

end VG.Proof.Rsa.X86_64
