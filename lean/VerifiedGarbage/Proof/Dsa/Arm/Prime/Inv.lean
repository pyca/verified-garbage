module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.St
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Inv
import VerifiedGarbage.Proof.Rsa.Arm.InverseCT

/-! # A candidate on ARMv7: differences and inverses as pieces

`sub3` (`St.psub3`), and `invOf a m` (`St.pinv`): from `(a, m, 1, 0)`,
`inverse` modulo the odd `m > 1` leaves `ivr W a m` in arrays 0–3
(`Proof/RsaKeyGen/Arm/Key/Inv.lean`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 sub32_of)
open VG.Proof.RsaKeyGen.Arm.Key (ivr ivr_spec copy1M_taint copy3Zero_taint subNM_taint)

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- `sub3 o a b`: `[o] := [a] − [b]` modulo `2^(32 W)`. -/
theorem St.psub3 {o a b : Nat} (cert : Cert (sub3 o a b)) (ho : o < nArr) (ha : a ∈ L) (hb : b ∈ L) (hoa : o ≠ a)
    (hob : o ≠ b) :
    VP (St P E A L V LS) (sub3 o a b) (St P E (fun σ => upd (A σ) o (sub32 P.W (A σ a) (A σ b))) (o :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ =>
    WP.mono (sub3_ok hw ho (h.live_lt a ha) (h.live_lt b hb) (by decide) hoa hob) fun t ⟨ht, k, v, bo, r⟩ => by
      obtain ⟨e1, -⟩ := sub32_of (val32_lt _ _ _ _) (val32_lt _ _ _ _) v bo
      have ea : val32 s.mem (State.addr P.B) (arr P.W a) P.W = A σ a := h.arrs a ha
      have eb : val32 s.mem (State.addr P.B) (arr P.W b) P.W = A σ b := h.arrs b hb
      simp only [num, ea, eb] at e1
      exact ⟨e, h.write1 k ho (by simp) r.sp r.rd r.wr e1 (by simp), ht⟩

end

end VG.Proof.Dsa.Arm.Prime
