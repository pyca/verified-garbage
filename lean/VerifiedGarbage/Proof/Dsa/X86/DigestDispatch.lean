module

public import VerifiedGarbage.Proof.Dsa.X86.PublicCompare

/-! # Selecting a digest-prefix specialization using only its public length -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem digestDispatch_ok (signing : Bool) (pLen qLen limit : Nat)
    {s : State} {base : Addr} {size len : Nat} {Q : State → Prop}
    (hs : Scr s base size) (hz : Layout.saved ≤ size) (hl : len ≤ limit) (hb : limit < 2 ^ 32)
    (hv : (pointerValue base s (.input .digestPrefixLen)).toNat = len)
    (body : ∀ t, Keeps [.eax] s t → t.mem = s.mem →
      WP isa (if signing then SignVerify.signBody pLen qLen len else SignVerify.verifyBody pLen qLen len) t Q) :
    WP isa (Entry.digestDispatch signing pLen qLen limit) s Q := by
  induction limit generalizing s with
  | zero =>
    have H : len = 0 := by omega
    simpa only [Entry.digestDispatch, H] using body s (Keeps.refl _ _) rfl
  | succ limit ih =>
    unfold Entry.digestDispatch
    refine WP.seq (WP.mono (publicCompare_ok .digestPrefixLen hs hz hv hb) fun t ⟨Z, K, O⟩ => ?_)
    by_cases H : len = limit + 1
    · refine WP.ite true (by simp only [eval, Z, H, decide_true]) (fun _ => ?_) (fun h => Bool.noConfusion h)
      rw [← H]
      exact body t K O
    · refine WP.ite false (by simp only [eval, Z, H, decide_false]) (fun h => Bool.noConfusion h) (fun _ => ?_)
      apply ih (hs.of_keeps K (by decide)) (by omega) (by omega)
      · simpa only [pointerValue, O] using hv
      · intro u Ku Ou
        exact body u (K.trans Ku) (Ou.trans O)

end VG.Proof.Dsa.X86
