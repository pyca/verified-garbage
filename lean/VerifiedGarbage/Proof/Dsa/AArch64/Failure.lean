module

public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Dsa.AArch64.Operands
public import VerifiedGarbage.Proof.Bignum.AArch64.PubFail
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Zeroing the signature on public domain rejection -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.WriteBytes (writeW8_apply)

/-- After `j` zero bytes of the rejected signature from `s₀`. -/
structure FailInv (s₀ : State) (op : Addr) (j : Nat) (t : State) : Prop where
  keep : Keep [.x1, .x9] s₀ t
  x1 : t.gpr .x1 = op + BitVec.ofNat 64 j
  bytes : ∀ i < j, t.mem (op + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s₀.mem x

theorem failStep_ok {s₀ : State} {op : Addr} {N : Nat} (hN : N < 2 ^ 63) (h3 : s₀.gpr .x3 = 0)
    (hwr : ∀ j < N, InRegions s₀.wr (op + BitVec.ofNat 64 j) 1) {j : Nat} (hj : j < N) {t : State}
    (hI : FailInv s₀ op j t) :
    WP isa (.block [.strb .x3 .x1 0, .addImm .x .x1 .x1 1, .subImm .x .x9 .x9 1]) t
      fun t' => FailInv s₀ op (j + 1) t' ∧ t'.gpr .x9 = t.gpr .x9 - BitVec.ofNat 64 1 := by
  have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by rw [hI.keep.wr]; exact hwr j hj
  have h3' : t.gpr .x3 = 0 := (hI.keep.gpr .x3 (by decide)).trans h3
  have hw8 : ∀ (m : Mem) (a : Addr) (v : BitVec 8), m.write a 1 v = m.writeW a v := fun _ _ _ => rfl
  rw [show ([.strb .x3 .x1 0, .addImm .x .x1 .x1 1, .subImm .x .x9 .x9 1] : List Instr) =
    ([.strb .x3 .x1 0, .addImm .x .x1 .x1 1] : List Instr) ++ ([.subImm .x .x9 .x9 1] : List Instr) from rfl,
    WP.block_append_iff]
  refine WP.mono (WP.keep [.x1] (Q := fun t₁ => t₁.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
      t₁.gpr .x1 = op + BitVec.ofNat 64 (j + 1)) (by
    brun [hI.x1, hst, h3', hw8, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl) (by decide) (by decide)
      (by decide +kernel))
    fun t₁ ⟨⟨hm, h1⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x9) fun t' ⟨⟨h9, hm', _⟩, k'⟩ => ⟨?_, by rw [h9, k₁.gpr .x9 (by decide)]⟩
  refine ⟨((hI.keep.trans k₁).trans k').mono (by decide), by rw [k'.gpr .x1 (by decide), h1], fun i hi => ?_,
    fun x hx => ?_⟩
  · rw [hm', hm, writeW8_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
      exact hI.bytes i (by omega)
  · rw [hm', hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
    exact hI.frame x fun i hi => hx i (by omega)

/-- `signFailure`: `2 q` zero bytes to `out`, and 0 returned. -/
theorem signFailure_ok {s : State} {B : Addr} {Z k q : Nat} {op : Addr} (hs : Scr s B Z) (hdi : s.gpr .x0 = B)
    (hZ : pWorkspace ≤ Z) (hkq : k = 2 * q) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hO : word s.mem B Field.out.offset = op) (hK : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa SignVerify.signFailure s fun t =>
      (List.range k).map (fun i => t.mem (op + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp 0 k ∧
      t.gpr .x0 = 0 ∧
      (∀ x, (∀ j < k, x ≠ op + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧ Keep (.x0 :: mmRegs) s t := by
  unfold SignVerify.signFailure seqs
  refine WP.seq (WP.mono (WP.keep [.x1, .x9, .x3] (Q := fun t => t.gpr .x1 = op + BitVec.ofNat 64 0 ∧
      t.gpr .x9 = BitVec.ofNat 64 k ∧ t.gpr .x3 = 0 ∧ t.mem = s.mem) (by
    unfold Core.field
    brun [hdi, field_enc, hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 hZ), hO, hK]
    rw [BitVec.ofNat_add_ofNat, hkq, Nat.two_mul]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h1, h9, h3, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (wp_countdown (N := k) (by omega) (by omega) (FailInv s₁ op)
    (fun j hj t hI _ => failStep_ok (by omega) h3 (fun i hi => by rw [k₁.wr]; exact hout i hi) hj hI)
    ⟨Keep.refl _ _, h1, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩ h9) fun t₂ hI => ?_)
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = t₂.mem) (by brun) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨⟨hx, hm⟩, k₃⟩ => ⟨?_, hx, fun x hx' => ?_, ((k₁.trans hI.keep).trans k₃).mono
      (by decide)⟩
  · rw [i2osp_zero]
    exact List.map_congr_left fun i hi => by rw [hm]; exact hI.bytes i (List.mem_range.mp hi)
  · rw [hm, hI.frame x hx', hm₁]

end VG.Proof.Dsa.AArch64
