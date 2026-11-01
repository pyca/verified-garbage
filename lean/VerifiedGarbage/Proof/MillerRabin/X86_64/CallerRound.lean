module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerPre
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerEntry
import VerifiedGarbage.Proof.MillerRabin.X86_64.Prepared

/-! # Call the complete shared round with its verified stack frame -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

theorem round_call_ok (v : RoundImpl) {s : State} {B : Addr} {Z w c bm b : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (he : ECtx s.mem B w c) (hd : MrDims B Z w)
    (hZ : slot w 28 ≤ Z) (hr : Room s B Z)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 (callWords w))
    (ho : c % 2 = 1) (h3 : 3 ≤ c)
    (hx : wv s.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c) :
    WP isa (.call v.name v.code) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame ([⟨B, 8 * callWords w⟩] ++ [below (s.gpr .rsp) 128]) s.mem t.mem ∧
      ((t.gpr .rax).setWidth 32).toNat = (if Proof.MillerRabin.Round.round c b then 1 else 0) ∧
      Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.extended B (callWords w) w s.mem t.mem ∧
      t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hvDepth : v.code.x86_64Depth ≤ 120 := v.depth
  have hn := hc.good.scr.nowrap
  have hsize := call_size hZ
  have hN : callWords w < 2 ^ 64 := by have := hd.w128; unfold callWords; omega_arith
  have hxlt : wv s.mem B (slot w aXm) w < c := by
    rw [hx]
    exact Nat.mod_lt _ (by omega_arith)
  obtain ⟨hc₁, _⟩ := entry_context hc he hd hr.disjoint
  have hw := ctx_width hc₁ hd.w128
  have heX : Proof.Rsa.Mont.numAt s.callEntry.mem B w 5 = b % c * 2 ^ (64 * w) % c := by
    rw [VG.Proof.Bignum.X86_64.MontFn.numAt_eq, entry_wv s hn (by
      have hz := hd.x
      simp only [slot, hdrBytes, aRm1] at hz ⊢
      omega_arith) hr.disjoint]
    exact hx
  obtain ⟨hcov, hwr⟩ := narrow_covers hc.good.scr hZ
  refine WP.call_sp_mx (s := s) (c := v.code) (rd := []) (wr := [⟨B, 8 * callWords w⟩]) (k := roundContract) v.correct
    (SpSafe.of_all v.spSafe) (by omega_arith)
    (narrow_pre hc he hd hZ hr hsi ho h3 hxlt) hcov hwr ?_
  rintro t hrd hwt hcs hf _ ⟨u, hmu, hgu, hp⟩ hmx
  have hf' : Frame ([⟨B, 8 * callWords w⟩] ++ [below (s.gpr .rsp) 128]) s.mem t.mem :=
    Frame.below_mono hf (by omega_arith) (by decide)
  have hBase : (narrowed s B w).gpr .rdi = B := by
    change s.callEntry.gpr .rdi = B
    rw [State.callEntry_gpr _ (by decide)]
    exact hc.good.rdi
  have hLen : ((narrowed s B w).gpr .rsi).toNat = callWords w := by
    change (s.callEntry.gpr .rsi).toNat = callWords w
    rw [State.callEntry_gpr _ (by decide), hsi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN]
  have hWidth : Proof.Rsa.Mont.wOf (narrowed s B w).mem B = w := hw
  have hMod : Proof.Rsa.Mont.numAt (narrowed s B w).mem B w 0 = c :=
    (VG.Proof.Bignum.X86_64.MontFn.numAt_eq _ _ _ _).trans hc₁.n
  change roundPost (narrowed s B w) u at hp
  dsimp only [roundPost] at hp
  rw [hBase, hLen, hWidth, hMod, hmu] at hp
  have hrx := hp.1 b heX
  rw [hgu .rax (by decide)] at hrx
  refine ⟨hcs, hrd, hwt, hf', hrx, ?_, hmx⟩
  intro i hi hh ha ht
  exact (hp.2 i hi hh ha ht).trans (entry_byte s hn (by omega_arith) hr.disjoint)

end VG.Proof.MillerRabin.X86_64.Caller
