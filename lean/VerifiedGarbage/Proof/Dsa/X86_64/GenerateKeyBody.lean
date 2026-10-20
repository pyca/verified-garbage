module

public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyFinish
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyCheckStep
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeySampled
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Key generation's body: entry, the domain check, generation, the finish -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem keygen_result_unchecked {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    (hc : keygenChecked s = false) : keygenResult s = ⟨none, 0, 0, [4]⟩ := by
  have hpl : (keygenInput s).params.length = 2 * (keygenInput s).pLen + (keygenInput s).qLen := by
    simp only [keygenInput, bytesAt_length]; exact h.paramsLength
  unfold keygenResult
  rw [VG.Proof.Dsa.generateKeyBytes_eq (pLen := (keygenInput s).pLen) (qLen := (keygenInput s).qLen)
    h.lengths hpl]
  simp only [show Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
    = false from hc, Bool.false_eq_true, ↓reduceIte]

theorem keygen_test_check {t : State} :
    WP isa (.block [.mov32 .rax (.reg .rax), .alu .cmp .rax (.imm 0)]) t fun u =>
      (u.mem = t.mem ∧ u.zf = some (((t.gpr .rax).setWidth 32).toNat == 0)) ∧ Keep [.rax] t u := by
  refine WP.keep [.rax] ?_ rfl
  xrun []
  rw [sub_beq_zero]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  have hz : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide
  rw [hz]
  constructor
  · intro he
    have hn := congrArg BitVec.toNat he
    simp only [BitVec.toNat_setWidth] at hn ⊢
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide : 2 ^ 32 ≤ 2 ^ 64))] at hn
    exact hn
  · intro he
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, he, Nat.zero_mod]
    rfl

theorem keygen_body (v : Backend) {s : State} (h : GenerateKeyABI v.stack s) :
    WP isa (GenerateKey.body (keygenCheckName v) (keygenDeriveName v)
      (Generate.checkParameters v.sq v.mul) (Generate.deriveKey v.sq v.mul))
      (allocState Random.frameBytes s) (KeygenBodyPost s (keygenResult s)) := by
  have hb := keygen_result_bounds h
  unfold GenerateKey.body
  refine WP.seq (WP.mono (keygen_head h) fun t ⟨ht, hst, hQ, hdi, hsi, hdx, hcx, h8, h9⟩ => ?_)
  refine WP.seq (WP.mono (keygen_check_step v ht hdi hsi hdx hcx h8 h9) fun u ⟨hu, hw, hax⟩ => ?_)
  refine WP.seq (WP.mono_mx (by decide) (keygen_test_check (t := u)) fun w ⟨⟨hwm, hwz⟩, hkw⟩ hmxw => ?_)
  have hsw : KeygenState h 0 w :=
    hu.of_frame (by rw [hwm]; exact InScr.refl _ _ _) (fun d _ _ => by rw [hwm]) (hkw.mono (by decide))
      (by rw [hmxw])
  have hword (d : Nat) (hd : d + 8 ≤ Random.frameBytes) : word w.mem (randomBase s) d = word t.mem (randomBase s) d := by
    rw [hwm]; exact hw d hd
  refine WP.seq ?_
  cases hc : keygenChecked s with
  | false =>
    rw [hc] at hax
    refine WP.ite true (by simp only [eval, hwz, hax]; rfl) (fun _ => WP.block_nil ?_)
      (fun he => Bool.noConfusion he)
    have hr := keygen_result_unchecked h hc
    rw [hr] at hb ⊢
    exact keygen_finish_result hsw (by rw [hword _ (by decide), hst]; rfl) (fun he => absurd he (by decide))
      hb.1 hb.2
  | true =>
    rw [hc] at hax
    refine WP.ite false (by simp only [eval, hwz, hax]; rfl) (fun he => Bool.noConfusion he) fun _ => ?_
    refine WP.mono (keygen_generate v hsw (by rw [hword _ (by decide)]; exact hQ) hc)
      fun x ⟨hx, hxs, hxo⟩ => keygen_finish_result hx hxs hxo hb.1 hb.2

end VG.Proof.Dsa.X86_64
