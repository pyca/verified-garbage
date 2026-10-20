module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Teardown
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stack

/-! # Compose the round's two saved frames -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Impl.MillerRabin.X86_64

theorem round_frames {s : State} {body : Prog isa} {Q : State → Prop}
    (hs : 120 ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (entered s) fun t =>
      t.gpr .rsp = (entered s).gpr .rsp ∧ t.wr = (entered s).wr ∧ Q (exited t)) :
    WP isa (.frame (.push saved) (.frame (.push [.rbp]) body (.pop .rbp 1))
      (.pop .r11 13)) s Q := by
  have hn : saved.length = 13 := by decide +kernel
  have h104 : 8 * saved.length ≤ (s.gpr .rsp).toNat := by rw [hn]; omega_arith
  have hi : 8 * ([Reg.rbp] : List Reg).length ≤ ((pushed saved s).gpr .rsp).toNat := by
    rw [pushed_rsp, hn, toNat_sub_ofNat (by omega_arith : 8 * 13 ≤ (s.gpr .rsp).toNat)]
    simp only [List.length_cons, List.length_nil]
    omega_arith
  apply WP.frame (by decide +kernel) (by decide +kernel) (by decide) h104
  apply WP.frame (by decide) (by decide) (by decide) hi
  refine WP.mono hb ?_
  rintro t ⟨hsp, hw, hq⟩
  refine ⟨hsp, hw, ?_, ?_, ?_⟩
  · rw [popped_rsp, hsp, entered_rsp, pushed_rsp, hn]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
    bv_omega
  · rw [popped_wr, hw]
    rfl
  · simpa only [hn, exited, List.length_cons, List.length_nil, Nat.reduceAdd] using hq

end VG.Proof.MillerRabin.X86_64
