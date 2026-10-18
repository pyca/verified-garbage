module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncodePadding

/-! # Start an encryption encoding and its branchless padding-byte validation -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Proof.RsaPkcs1Sig.X86
open VG.Impl.RsaPkcs1Enc.X86

theorem head_ok {s0 s : State} {k : Nat} (buf : Buf s0 k) (room : 2 ≤ k) (h : W s0 [] s) :
    WP isa (.block head) s fun t => W s0 [0, 2] t ∧ t.gpr .ebx = 0 ∧ Keeps [.eax, .edi, .ebx] s t := by
  unfold head
  rw [WP.block_append_iff]
  refine WP.mono (putBytes_ok buf [0, 2] (by simp; omega) h) ?_
  rintro a ⟨ha, ka⟩
  refine wp_movS rfl fun t T _ => WP.block_nil ?_
  exact ⟨ha.after T.keeps (by decide) T.mem (T.other .edi (by decide)), T.gpr, (ka.mono (by decide)).trans (T.keeps.mono (by decide))⟩

theorem nonzero_padding (bs : List Byte) : bs.all (· != 0) = !hasZero bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.all_cons, hasZero, List.any_cons] at *
    rw [ih]
    by_cases zero : b = 0
    · subst b; simp
    · have neq : (b != 0) = true := bne_iff_ne.mpr zero
      rw [neq, decide_eq_false zero]
      rfl

end VG.Proof.RsaPkcs1Enc.X86
