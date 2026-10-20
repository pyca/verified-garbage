module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # FFDH on x86-64: restore System V's saved registers -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem exit_ok {s₀ s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : 48 ≤ Z) (hSaved : ∀ i < 6, word s.mem B (8 * i) = s₀.gpr (saved.getD i .rax)) :
    WP isa (.block VG.Impl.Bignum.X86_64.Public.exit) s fun t =>
      (∀ r ∈ saved, t.gpr r = s₀.gpr r) ∧ t.mem = s.mem ∧ Keep saved s t := by
  rw [exit_eq]
  refine WP.mono (WP.keep saved (Q := fun t =>
      t.gpr .rbx = s₀.gpr .rbx ∧ t.gpr .rbp = s₀.gpr .rbp ∧ t.gpr .r12 = s₀.gpr .r12 ∧
      t.gpr .r13 = s₀.gpr .r13 ∧ t.gpr .r14 = s₀.gpr .r14 ∧ t.gpr .r15 = s₀.gpr .r15 ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff,
      hs.ld (d := 8 * 0) (by omega), hs.ld (d := 8 * 1) (by omega), hs.ld (d := 8 * 2) (by omega),
      hs.ld (d := 8 * 3) (by omega), hs.ld (d := 8 * 4) (by omega), hs.ld (d := 8 * 5) (by omega),
      hSaved 0 (by decide), hSaved 1 (by decide), hSaved 2 (by decide), hSaved 3 (by decide),
      hSaved 4 (by decide), hSaved 5 (by decide), saved, List.getD_cons_succ, List.getD_cons_zero]) rfl)
    fun t ⟨⟨h0, h1, h2, h3, h4, h5, hm⟩, k⟩ => ⟨?_, hm, k⟩
  intro r hr
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4, h5]

end VG.Proof.Ffdh.X86_64
