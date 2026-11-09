module
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Base
public import VerifiedGarbage.Spec.MlDsa.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.Contract

import VerifiedGarbage.Proof.MlDsa.X86.Sign.Params
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Sha3.X86.Lit

/-!
# ML-DSA signing on x86 (32-bit): the contracts

The contract's precondition implies the layout `Y p` of the arguments
(`pre_of`); its public data are the pointers and `signLeak`, which is
`signLeakT` (`pub_of`).

Not trusted: the contract of the internal function `vg_mldsa*_sign_core`
(`signCoreContract`), the signing code that `vg_mldsa*_sign` and
`vg_mldsa*_sign_prepared` share. It is `signContract`, but for the word
`KEYS` of `scratch` (at byte `oKEYS`): if it is not 0, `scratch` holds the
polynomials `preparedSecretPolys` of `sk` in the slots of `ŝ₁`, `ŝ₂` and
`t̂₀` (`KeysIn`), which the function uses in place of decoding them; and the
function may leak whether it is 0.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece E0 retR)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params}

/-! ## The contract of `vg_mldsa*_sign_core` -/

/-- The word `KEYS` of the working space at `scratch`. -/
def keysWord (m : Mem) (scratch : Addr) : BitVec 32 := m.readW (scratch + BitVec.ofNat 64 oKEYS) 32

/-- The working space at `scratch` holds the polynomials of the private key
`sk` (`preparedSecretPolys`: `ŝ₁`, `ŝ₂`, `t̂₀`), from the slot of `ŝ₁[0]`. -/
def KeysIn (p : Params) (m : Mem) (scratch : Addr) (sk : List Byte) : Prop :=
  ∀ i < p.ℓ + 2 * p.k, PolyIs m (scratch + BitVec.ofNat 64 (oP (5 + 2 * p.k + 2 * p.ℓ + i))) (preparedSecretPolys p sk)[i]!

/-- `signContract`, with the private key's polynomials decoded from `sk` if
`KEYS` is 0 and in `scratch` otherwise; it may leak whether `KEYS` is 0. -/
def signCoreContract (p : Params) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (signSig p).contract A
    (pre := fun sk _mu _rnd _sig scratch m =>
      keysWord m scratch = 0 ∨ KeysIn p m scratch (bytesAt m sk p.skLen))
    (post := fun sk mu rnd sig _scratch m m' r =>
      Outcome (fun b => signMu p b (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32)) r
        (bytesAt m' sig p.sigLen))
    (writeArgs := true) (stack := stack)
    (leak := some fun sk mu rnd _sig scratch m =>
      (if keysWord m scratch = 0 then 0 else 1) ::
        signLeak p (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32))

set_option linter.unusedSimpArgs false in
theorem pre_of {s₀ : State} (h : (signContract p X86.abi 96).pre s₀) : TPre (Y p) s₀ := by
  sig_pre [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, d03, d04, d0g, d13, d14, d1g, d23, d24, d2g, d34, d3g, d4g, r0, r1, r2, r3, r4, rg,
    s0, s1, s2, s3, s4, sg, f0, f1, f2, f3, f4⟩ := h
  rw [Nat.mul_comm (scratchWords p) 8] at h4 d04 d14 d24 d34 d4g r4 s4 f4
  have hs : (⟨(E0 s₀).setWidth 64 - 96#64, 96⟩ : Region) = below (E0 s₀) 96 := by
    simp only [below]; rw [VG.X86.Taint.sub_setWidth h1]
  rw [hs] at s0 s1 s2 s3 s4 sg
  have c5 : ∀ i, i < (Y p).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := fun i hi => by
    rw [Y_n] at hi; omega
  refine ⟨h1, by show 16 ≤ 96; decide, by rw [Y_n]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sg, ?_, by show 4 < 5; decide⟩
  · intro i hi hw
    rw [h3]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    all_goals exact absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4])
  · intro i hi hw
    rw [h4]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4])
    · exact absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4])
    · exact absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4])
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · rw [h4]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  · intro i hi j hj hne hw
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl <;> rcases c5 j hj with rfl | rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4]), absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4]), d03, d04, absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4]), absurd rfl hne, absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4]), d13, d14, absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4]), absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4]), absurd rfl hne, d23, d24, d03.symm, d13.symm, d23.symm, absurd rfl hne, d34, d04.symm, d14.symm, d24.symm, d34.symm, absurd rfl hne]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [d0g.symm, d1g.symm, d2g.symm, d3g.symm, d4g.symm]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [r0, r1, r2, r3, r4]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [s0, s1, s2, s3, s4]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [f0, f1, f2, f3, f4]

set_option linter.unusedSimpArgs false in
/-- The kernel's precondition: the layout, and `KEYS`. -/
theorem core_pre_of {s₀ : State} (h : (signCoreContract p X86.abi 96).pre s₀) : TPre (Y p) s₀ ∧
    (keysWord s₀.mem ((arg s₀ 4).setWidth 64) = 0 ∨
      KeysIn p s₀.mem ((arg s₀ 4).setWidth 64) (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen)) := by
  sig_pre [signCoreContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, d03, d04, d0g, d13, d14, d1g, d23, d24, d2g, d34, d3g, d4g, r0, r1, r2, r3, r4, rg,
    s0, s1, s2, s3, s4, sg, f0, f1, f2, f3, f4, kp⟩ := h
  rw [Nat.mul_comm (scratchWords p) 8] at h4 d04 d14 d24 d34 d4g r4 s4 f4
  have hs : (⟨(E0 s₀).setWidth 64 - 96#64, 96⟩ : Region) = below (E0 s₀) 96 := by
    simp only [below]; rw [VG.X86.Taint.sub_setWidth h1]
  rw [hs] at s0 s1 s2 s3 s4 sg
  have c5 : ∀ i, i < (Y p).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := fun i hi => by
    rw [Y_n] at hi; omega
  refine ⟨⟨h1, by show 16 ≤ 96; decide, by rw [Y_n]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sg, ?_, by show 4 < 5; decide⟩, kp⟩
  · intro i hi hw
    rw [h3]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    all_goals exact absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4])
  · intro i hi hw
    rw [h4]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4])
    · exact absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4])
    · exact absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4])
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · rw [h4]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  · intro i hi j hj hne hw
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl <;> rcases c5 j hj with rfl | rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4]), absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4]), d03, d04, absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4]), absurd rfl hne, absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4]), d13, d14, absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4]), absurd hw (by simp [Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4]), absurd rfl hne, d23, d24, d03.symm, d13.symm, d23.symm, absurd rfl hne, d34, d04.symm, d14.symm, d24.symm, d34.symm, absurd rfl hne]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [d0g.symm, d1g.symm, d2g.symm, d3g.symm, d4g.symm]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [r0, r1, r2, r3, r4]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [s0, s1, s2, s3, s4]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [f0, f1, f2, f3, f4]

theorem addr0 (s₀ : State) (i l : Nat) : Buf.addr s₀ ⟨i, 0, l⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

end VG.Proof.MlDsa.X86.Sign
