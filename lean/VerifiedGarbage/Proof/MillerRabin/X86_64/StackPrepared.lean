module
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stack
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSq

import VerifiedGarbage.Proof.MillerRabin.X86_64.StackContext
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.CrtExp

/-! # The Montgomery and exponent contexts survive the saved frame -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.X86_64
open VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.RsaKeyGen.X86_64.Candidate

private theorem dim_read {B : Addr} {Z w j k : Nat} (h : MrDims B Z w)
    (hj : j ≤ 26) (hk : k ≤ w + 2) : slot w j + 8 * k ≤ Z := by
  have hm := VG.Proof.Bignum.slot_mono w hj
  have hx := h.x
  change slot w 26 + 8 * (w + 2) ≤ Z at hx
  omega_arith

theorem entered_ctx {s : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (h : MrDims B Z w)
    (hs : 120 ≤ (s.gpr .rsp).toNat)
    (hd : Region.Disjoint ⟨s.gpr .rsp - 112#64, 112⟩ ⟨B, Z⟩) :
    MrCtx (entered s) B Z w mi c bm := by
  have hn := hc.good.scr.nowrap
  refine ⟨entered_good hc.good h.z hs hd, ?_, ?_, ?_, ?_, ?_⟩
  · rw [entered_word hs hn hd (dim_read h (by decide : aN ≤ 26) (by omega_arith : 1 ≤ w + 2))]
    exact hc.inv
  · rw [entered_wv hs hn hd (dim_read h (by decide : aN ≤ 26) (by omega_arith))]
    exact hc.n
  · rw [entered_wv hs hn hd (dim_read h (by decide : aB ≤ 26) (by omega_arith))]
    exact hc.b
  · rw [entered_wv hs hn hd (dim_read h (by decide : aR1 ≤ 26) (by omega_arith))]
    exact hc.r1
  · rw [entered_wv hs hn hd (dim_read h (by decide : aRm1 ≤ 26) (by omega_arith))]
    exact hc.rm1

theorem entered_exp {s : State} {B : Addr} {Z w c : Nat}
    (he : ECtx s.mem B w c) (h : MrDims B Z w)
    (hs : 120 ≤ (s.gpr .rsp).toNat) (hn : B.toNat + Z ≤ 2 ^ 64)
    (hd : Region.Disjoint ⟨s.gpr .rsp - 112#64, 112⟩ ⟨B, Z⟩) :
    ECtx (entered s).mem B w c := by
  refine ⟨?_, ?_⟩
  · rw [entered_wv hs hn hd (dim_read h (by decide : aE ≤ 26) (by omega_arith))]
    exact he.e
  · rw [entered_word hs hn hd (by have := dim_read (j := aE) (k := w + 1) h (by decide) (by omega_arith); omega_arith)]
    exact he.l

end VG.Proof.MillerRabin.X86_64
