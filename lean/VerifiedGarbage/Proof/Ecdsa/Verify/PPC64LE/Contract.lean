module

public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.Ecdsa.Verify
public import VerifiedGarbage.Spec.P256
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.VerifiedAll
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.PPC64LE
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.TComb
import VerifiedGarbage.Proof.P256.PPC64LE.Comb
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.TCombJ
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256.Window
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep

/-! ### `Ecdsa.Verify.PPC64LE.P256Comb`, which the modules that import this one used -/

section

/-!
# ECDSA verification over P-256 on PPC64LE, by the comb and windows: `[u]G + [v]Q`

`combPts_ok`: `pointsP256` computes `[u]G + [v]Q` as `PtsOk` states,
from the comb's table in memory at the address its symbol names: `u`'s bits,
`b` in Montgomery's form at `EM`, `[u]G` by the comb (`combJ_ok`), `U = [u]G`
and `R = O` (`save_ok`), `v`'s bits, `[v]Q` by the windows (`Window.mul_ok`),
and `R = U + R` (`sum_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE.P256

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdsa.Verify.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdsa.Verify.PPC64LE VG.Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.Point (tmv)
open VG.Proof.Weierstrass.PPC64LE.TComb (TableMem)
open VG.Impl.Ecdh.PPC64LE (PX PY)
open VG.Impl.Ecdsa.Verify.PPC64LE (U V UX UY UZ RM')

theorem pointsP256_eq : pointsP256 =
    .seq (bits (p256.sl U) (bitsAt p256.n 0) (8 * p256.n)) (.seq
      (.block (VG.Impl.Mont.PPC64LE.setConst p256.n (p256.sl EM) (p256.mont p256.C.b)))
      (.seq mulGeneratorP256 (.seq (.block (Cfg.save p256)) (.seq (bits (p256.sl V) (bitsAt p256.n 0) (8 * p256.n))
        (.seq (Window.Cfg.mul p256 PX PY EM) (Cfg.sum p256)))))) := rfl

/-- `[u]G + [v]Q` by the comb and windows, with the comb's table at `T`. -/
theorem combPts_ok (hC : Law Spec.P256.curve) {s₀ : State} {T : Addr}
    (ht : TableMem s₀ T p256CombWords) (sym : s₀.syms p256Comb.tsym = T)
    (hd : Region.Disjoint ⟨T, 8 * p256CombWords.length⟩ ⟨s₀.gpr .r6, 8192⟩) :
    PtsOk p256 s₀ pointsP256 := by
  rw [pointsP256_eq]
  refine CombWin.kit_pts_ok Window.kit (by decide) (Or.inl ⟨rfl, rfl⟩) (by decide) hC
    fun {s k} K sy hk bits => ?_
  obtain ht₂ : TableMem s T p256CombWords :=
    ht.unch (by rw [K.rk.rd, K.rk.wr]) K.whole (by decide) hd
  obtain ht' : TableMem s T (TComb.tableWords p256Comb Spec.P256.curve VG.Impl.P256.p256Comb7) := by
    rw [Proof.P256.PPC64LE.comb_words_eq]; exact ht₂
  obtain hd' : Region.Disjoint ⟨T, 8 * (TComb.tableWords p256Comb Spec.P256.curve VG.Impl.P256.p256Comb7).length⟩
      ⟨s₀.gpr .r6, 8192⟩ := by
    rw [Proof.P256.PPC64LE.comb_words_eq]; exact hd
  exact WP.mono (TCombJ.combJ_ok p256Comb (Proof.P256.PPC64LE.comb_jconfig hC) hC
    p256_ok.onG K.ws ht' (by rw [sy, sym]) hd'
    hk K.fixed.zero (fun i hi => bits i (by
      have : i < 8 * Spec.P256.curve.len := hi
      exact Nat.lt_of_lt_of_le this (by decide))) K.fixed.ap K.fixed.b3p)
    fun s₃ ⟨k₃, U₃, L₃, R₃⟩ => ⟨k₃, U₃.cover Proof.P256.PPC64LE.comb_writes_cover, L₃, R₃⟩

end VG.Proof.Ecdsa.Verify.PPC64LE.P256

end

end

/-!
# ECDSA verification over P-256 on PPC64LE: the contract the proof is written against

The facts of `Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst` for PPC64LE, by name:
`vg_ecdsa_p256_verify(public, digest, sig, scratch)`, with the arguments in
`r3`–`r6` and the result in `r3` (ELFv2). Only the pointers are public here:
the proof shows that nothing else affects timing, although the contract
would let the contents of the three buffers.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE

open VG VG.PPC64LE Spec.Weierstrass Spec.Ecdsa

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.P256.curve (bytesAt m pk 65) (hashToInt Spec.P256.curve (bytesAt m digest 32)) (bytesAt m sig 64)

def verifyPPC : Contract PPC64LE.isa where
  pre s :=
    let pk : Region := ⟨s.gpr .r3, 65⟩
    let digest : Region := ⟨s.gpr .r4, 32⟩
    let sig : Region := ⟨s.gpr .r5, 64⟩
    let scratch : Region := ⟨s.gpr .r6, 8192⟩
    s.rd = [pk, digest, sig] ∧ s.wr = [scratch] ∧ pk.Disjoint scratch ∧ digest.Disjoint scratch ∧
      sig.Disjoint scratch ∧ (s.gpr .r3).toNat + 65 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 32 ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + 8192 ≤ 2 ^ 64
  post s s' := s'.gpr .r3 = if vf s.mem (s.gpr .r3) (s.gpr .r4) (s.gpr .r5) then 1 else 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6

end VG.Proof.Ecdsa.Verify.PPC64LE
