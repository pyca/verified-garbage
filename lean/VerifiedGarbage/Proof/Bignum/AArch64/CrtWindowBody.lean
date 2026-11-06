module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawBody
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowReset

/-! Exponent-prefix semantics of a window, including its reset. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- A complete window leaves its table and packed source exponent intact. -/
def WindowPost (s : State) (P : Addr) (w : Nat) (mi : BitVec 64) (X Xc : Nat)
    (Q : Prop) (x E v : Nat) (t : State) : Prop :=
  TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
  wv t.mem P (slot w aY) w < X ∧
  (Q → wv t.mem P (slot w aY) w % X = x ^ (32 * E + v) * 2 ^ (64 * w) % X) ∧
  Frm P (rawWindowRanges w) s.mem t.mem ∧ Keep mmRegs s t ∧
  word t.mem P (8 * Crt.sNib) = 0 ∧ word t.mem P (8 * Crt.sBit) = 0 ∧
  (∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → k ≠ Crt.sNib → k ≠ Crt.sBit →
    word t.mem P (8 * k) = word s.mem P (8 * k))

/-- Internal proof interface for the inline or outlined arithmetic window. -/
structure Window where
  code : Prog isa
  ok : ∀ {s : State} {P : Addr} {w : Nat} {mi : BitVec 64} {X Xc x E v : Nat} {Q : Prop},
    TableCtx s P w mi X Xc → CrtWindowFive.CTab s.mem P w X Q x →
    2 ≤ w → w < 2 ^ 30 → Nat.Coprime (2 ^ (64 * w)) X →
    wv s.mem P (slot w aY) w < X →
    (Q → wv s.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X) →
    v < 32 → word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v →
    WP isa code s (WindowPost s P w mi X Xc Q x E v)
  ct : RelCT isa (Two RawWindowPre) code (fun _ _ => True)

end VG.Proof.Bignum.AArch64.WindowFive
