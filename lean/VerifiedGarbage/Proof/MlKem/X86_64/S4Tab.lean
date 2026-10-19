module

public import VerifiedGarbage.Proof.MlKem.X86_64.S4Parse
public import VerifiedGarbage.Proof.MlKem.X86_64.S4SqT

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, the table

After the squeezes, the code puts the address of the static of the table of
the sampling, the constants of the vector code and the counts in `r11`
(`tabT_ok`), and writes no memory.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.S4

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4

/-- The static's address to `r11`. -/
theorem tabAddr_ok (s : State) :
    WP isa (.block tabAddr) s fun s' => s'.mem = s.mem ∧ Keep [.r11] s s' ∧ TabOK s' :=
  WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ⟨rfl,
    ⟨fun r hr => RegUpd.gpr_setReg_of_ne _ _ (fun e => hr (by simp [e])), rfl, rfl⟩, RegUpd.gpr_setReg_self _ _ _⟩⟩

/-- The static's address, after squeezes, which it keeps. -/
theorem tabT_ok {σ : State} {t b : Nat} {s : State} (h : SqTW w16 σ t b s) :
    WP isa (.block tabAddr) s fun s' => SqTW w16 σ t b s' ∧ TabOK s' ∧ s'.mem = s.mem :=
  WP.mono (tabAddr_ok s) fun s' ⟨hm, k, ht⟩ => ⟨⟨h.env.keep hm k (by decide), by rw [k.gpr (by decide), h.r14],
    by rw [hm]; exact h.rc, by rw [hm]; exact h.lanes, by rw [hm]; exact h.buf⟩, ht, hm⟩

end VG.Proof.MlKem.X86_64.S4
