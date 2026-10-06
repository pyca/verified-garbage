import VerifiedGarbage.Proof.Rsa.X86_64.PrivCheck

/-!
# `vg_rsa_private_checked` on x86-64: fault tolerance

What the check returns and releases (`check_ok`) passes the check whatever
the CRT left (`check_faultTolerant`, from `checkResult_sound`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## Fault tolerance -/

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
