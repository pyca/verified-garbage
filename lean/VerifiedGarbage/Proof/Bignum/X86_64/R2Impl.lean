import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
import VerifiedGarbage.Proof.Bignum.X86_64.R2aCT

/-!
# Computations of `R² mod m` on x86-64

What the functions that compute `R² mod m` use of the code that does
(`R2Impl`): its result (`r2_ok`'s, as `R2w.choice_ok` states it) and that it
leaks only `m` (`R2w.choice_ct`). `R2Words.choice` (`R2Impl.words`) and, with
ADX, `R2Adx.choice` (`R2Impl.adx`) do.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-- Code computing `R² mod m` into `aR2`, with Montgomery multiplication `M`. -/
structure R2Impl (M : Mont) where
  code : Prog isa
  ok : ∀ {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat},
    Good s B Z w minv → slot w 8 ≤ Z → 2 ≤ w → w < 2 ^ 30 → wv s.mem B (slot w aN) w = N →
    ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 →
    s.gpr .r12 = BitVec.ofNat 64 w → s.gpr .r10 = off B (slot w aN) → N % 2 = 1 → 2 ^ (64 * (w - 1)) ≤ N →
    WP isa code s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w aR2) w < N ∧ wv t.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t
  ct : RelCT isa (Two R2Pre) code fun _ _ => True

/-- By word steps and two squarings, or doublings and squarings. -/
def R2Impl.words (M : Mont) : R2Impl M :=
  ⟨R2Words.choice M.mm, R2w.choice_ok M, R2w.choice_ct M⟩

/-- By `w` word steps with ADX, or doublings and squarings. -/
def R2Impl.adx (M : Mont) : R2Impl M :=
  ⟨R2Adx.choice M.mm, R2ax.choice_ok M, R2ax.choice_ct M⟩

end VG.Proof.Bignum.X86_64
