module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtTab

/-! Constant-time composition of a five-bit window. Only workspace layout
is shared between runs; the modulus, table and selected digit are secret. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

def WindowPre (p : XPub) (s : State) : Prop :=
  ∃ mi X Xc v, TableCtx s (off p.B p.o) p.wx mi X Xc ∧
    CrtWindowFive.CTab s.mem (off p.B p.o) p.wx X False 0 ∧
    wv s.mem (off p.B p.o) (slot p.wx aY) p.wx < X ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.wx)) X ∧ v < 32 ∧
    word s.mem (off p.B p.o) (8 * Crt.sNib) = BitVec.ofNat 64 v

theorem WindowPre.sel {p : XPub} {s : State} (h : WindowPre p s) : SelP p s := by
  obtain ⟨mi, X, Xc, v, hc, ht, _, hw, hw', _, hv, hn⟩ := h
  exact ⟨mi, X, Xc, v, hc, hw, hw', hv, ht.tab, hn⟩

end VG.Proof.Bignum.AArch64.WindowFive
