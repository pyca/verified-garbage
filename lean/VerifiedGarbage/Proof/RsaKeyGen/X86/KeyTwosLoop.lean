module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyTwosBody

/-! # The complete fixed schedule matches the shared LCM arithmetic -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem twos_loop {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (counter : s.gpr .esi = BitVec.ofNat 32 (32 * n)) :
    WP isa (.loop (twoStep n) .ne) s fun t => HalveLoop s B Z n (32 * n) t := by
  have positive : 0 < 32 * n := by have := h.wpos; omega
  have initial : HalveLoop s B Z n 0 s :=
    ⟨h, VG.Proof.Rsa.X86.Keys.Keep.refl B n halveArrays [kFlag] s.mem, Keeps.refl .., by simpa only [Nat.sub_zero] using counter, rfl⟩
  refine WP.loop (M := isa)
    (fun remaining t => ∃ i, remaining = 32 * n - i ∧ i < 32 * n ∧ HalveLoop s B Z n i t)
    ?_ (32 * n) s ⟨0, by omega, positive, initial⟩
  rintro remaining t ⟨i, rfl, index, H⟩
  refine WP.mono (twoStep_ok H index) fun u ⟨next, Zf⟩ => ?_
  by_cases last : i + 1 = 32 * n
  · exact .inl ⟨by simp only [eval, Zf, last, decide_true, Option.map_some, Bool.not_true], last ▸ next⟩
  · exact .inr ⟨by simp only [eval, Zf, decide_eq_false last, Option.map_some, Bool.not_false],
      32 * n - (i + 1), by omega, i + 1, rfl, by omega, next⟩

end VG.Proof.RsaKeyGen.X86.Key
