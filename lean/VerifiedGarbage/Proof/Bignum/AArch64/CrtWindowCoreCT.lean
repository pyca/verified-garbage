module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowSquares
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp

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

theorem squares_post (M : Mont) {p : XPub} {s : State} (h : WindowPre p s) :
    WP isa (seqs (List.replicate 5 (M.mm aY aY aY))) s (WindowPre p) := by
  obtain ⟨mi, X, Xc, v, hc, ht, hy, hw, hw', hR, hv, hn⟩ := h
  exact WP.mono (crtSquares_ok M 4 (Q := False) (x := 0) (E := 0)
    hc.base hw hw' hR hy False.elim) fun t ⟨_, hyt, _, hh, hf, hk⟩ =>
      ⟨mi, X, Xc, v, hc.of_win hf hk.wr (hk.gpr .x0 (by decide)),
        ht.of_win hf hc.scrT.nowrap, hyt, hw, hw', hR, hv,
        (hh _ (by decide)).trans hn⟩

theorem windowCore_ct (M : Mont) (S : Selector) :
    RelCT isa (Two WindowPre)
      (VG.Impl.Rsa.AArch64.WindowFive.windowCore M.mm S.code) (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.windowCore
  refine RelCT.seqs_append (by simp) (by simp) ?_
  refine RelCT.seq (two_post (Ψ := WindowPre)
    (two_map (fun p : XPub => (off p.B p.o, p.wx)) ?_ (crtSquares_ct M 4))
    (fun _ _ h => squares_post M h)) ?_
  · rintro p s ⟨mi, X, Xc, _, hc, _, hy, hw, hw', hR, _⟩
    exact ⟨mi, X, Xc, hc.base, hw, hw', hR, hy⟩
  simp only [seqs]
  refine RelCT.seq (two_post (Ψ := fun p : XPub => GoodW p.ws)
    (two_map id (fun _ _ h => h.sel) S.ct) ?_)
    (two_map (fun p : XPub => p.ws) (fun _ _ h => h)
      (M.ct (o := aY) (a := aY) (b := Crt.aT) (by unfold MmUse; decide)))
  rintro p s ⟨mi, X, Xc, v, hc, ht, _, hw, hw', _, hv, hn⟩
  exact WP.mono (S.ok hc hw hw' hv ht.tab hn) fun t ⟨ct, _⟩ =>
    ⟨mi, ct.good, Nat.le_refl _⟩

end VG.Proof.Bignum.AArch64.WindowFive
