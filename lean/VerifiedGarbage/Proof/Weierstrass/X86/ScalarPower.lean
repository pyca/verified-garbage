import VerifiedGarbage.Impl.Weierstrass.X86.ScalarPower
import VerifiedGarbage.Proof.Weierstrass.X86.P256Power

/-! # P-256 scalar inversion: a fixed prefix and the existing suffix loop -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem p256ScalarPrefix_exponent : chainExponents p256ScalarPrefixOps (1, 1) =
    ((p256Order - 2) >>> 128, 2 ^ 32 - 1) := by
  decide +kernel

theorem p256ScalarPrefix_bound : ∀ op ∈ p256ScalarPrefixOps, powerOpBound op := by
  simp only [p256ScalarPrefixOps, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, powerOpBound]
  decide +kernel

theorem p256ScalarPower_ok {P : PowCfg} {base : Addr} {size wk m : Nat} [NeZero m]
    (hL : PowLay P size) (hW : PowWk P size wk) (hm : UnitMod m (2 ^ (64 * P.M.n)))
    {s : State} (hs : Scr s base size) (hM : ModOkW P.M size m s.mem base)
    (hB : wordsVal s.mem base P.base P.M.n < m) (hnb : 128 ≤ P.nbits)
    (hbits : ∀ t < P.nbits, s.mem (off base (P.bits + t)) =
      if (p256Order - 2).testBit t then 1 else 0) :
    WP isa (p256ScalarPower P wk) s fun u => Keeps powClob s u ∧
      Unch base (powWx P wk) s.mem u.mem ∧ wordsVal u.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal u.mem base P.acc P.M.n) =
        toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ (p256Order - 2) := by
  refine WP.seq (WP.mono (powerInit_ok hL hW hs hM hB) fun s₁ ⟨I₁, K₁, U₁⟩ => ?_)
  refine WP.seq (WP.mono (powerChain_ok hL hW hm p256ScalarPrefixOps
    p256ScalarPrefix_bound (v := (1, 1)) I₁) fun s₂ ⟨I₂, K₂, U₂⟩ => ?_)
  rw [p256ScalarPrefix_exponent] at I₂
  refine WP.seq (wp_movS rfl fun s₃ u₃ _ => WP.block_nil ?_)
  refine countLoop_ok (Inv := fun j u => PowInv P wk base size m (p256Order - 2) s u j)
    (n := 128)
    (fun j u h1 h2 hi => powBody_ok hL hW hm hM hB hbits h1 (by omega) hi)
    (fun u hi => ⟨hi.keep, hi.unch, hi.lt, by rw [hi.val, Nat.shiftRight_zero]⟩)
    (by omega) ?_
  refine ⟨I₂.scr.of_keeps u₃.keeps (by decide), u₃.gpr,
    ((K₁.mono (by decide)).trans K₂).trans (u₃.keeps.mono (by decide)), ?_, ?_, ?_⟩
  · intro x hx
    rw [u₃.mem, U₂ x hx, U₁ x hx]
  · rw [u₃.mem]; exact I₂.acc_lt
  · rw [u₃.mem]; exact I₂.acc_val

theorem powScalar_ok {P : PowCfg} {base : Addr} {size wk m : Nat} [NeZero m]
    (hL : PowLay P size) (hW : PowWk P size wk) (hm : UnitMod m (2 ^ (64 * P.M.n)))
    {s : State} (hs : Scr s base size) (hM : ModOkW P.M size m s.mem base)
    (hB : wordsVal s.mem base P.base P.M.n < m)
    (hO : wordsVal s.mem base P.one P.M.n = 2 ^ (64 * P.M.n) % m)
    (hbits : ∀ t < P.nbits, s.mem (off base (P.bits + t)) = if (m - 2).testBit t then 1 else 0)
    (he : m - 2 < 2 ^ P.nbits) :
    WP isa (powScalar P wk m) s fun u => Keeps powClob s u ∧ Unch base (powWx P wk) s.mem u.mem ∧
      wordsVal u.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal u.mem base P.acc P.M.n) =
        toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ (m - 2) := by
  unfold powScalar
  split
  next hp =>
    have hb : ∀ t < P.nbits, s.mem (off base (P.bits + t)) =
        if (p256Order - 2).testBit t then 1 else 0 := by simpa only [hp.1] using hbits
    exact WP.mono (p256ScalarPower_ok hL hW hm hs hM hB hp.2 hb) fun u ⟨K, U, L, V⟩ =>
      ⟨K, U, L, by rw [← hp.1] at V; exact V⟩
  next _ => exact pow_ok hL hW hm hs hM hB hO hbits he

end VG.Proof.Weierstrass.X86
