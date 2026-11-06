module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.St
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Words
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Math
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Words
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Rsa.Arm.RdTwos
import VerifiedGarbage.Proof.Rsa.TwosMath
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Tools
import VerifiedGarbage.Proof.Rsa.Arm.Stage.MM
import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Taint2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP

/-! # A candidate on ARMv7: more operations as pieces

Halvings, words of constants, header words set, the candidate's bits and a
witness's fixed bits, as pieces (`VP`) on a stage.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)
open VG.Impl.RsaKeyGen.Arm.Key (setWd setHi)

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- `r11 := 0`. -/
theorem St.pmov11 (cert : Cert (.block [.mov .r11 (.imm 0)])) : VP (St P E A L V LS) (.block [.mov .r11 (.imm 0)])
    (fun σ s => St P E A L V LS σ s ∧ s.gpr .r11 = 0) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ =>
    wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ⟨⟨e, h.of_rest (u.rest (ws := [.r11]) (by simp)) u.mem,
      hw.of_upd u (by decide) (by decide) (by decide)⟩, u.gpr⟩

/-- `half j` with `r11 = 0`: `[j] := [j] / 2`. -/
theorem St.phalf {j : Nat} (cert : Cert (half j)) (hj : j ∈ L) :
    VP (fun σ s => St P E A L V LS σ s ∧ s.gpr .r11 = 0) (half j)
      (St P E (fun σ => upd (A σ) j (A σ j / 2)) (j :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, r11⟩ => by
    have hj' := h.live_lt j hj
    exact WP.mono (half_ok hw hj' (by decide) (by rw [r11]; decide)) fun t ⟨ht, k, v, r⟩ =>
      ⟨e, h.write1 k hj' (by simp) r.sp r.rd r.wr (by rw [v, r11, h.arrs j hj]; simp) (by simp), ht⟩

/-- `setWd j o x`: word `o / 4` of `[j]` := `x`, above the number. -/
theorem St.psetWd {j o x : Nat} (cert : Cert (.block (setWd j o x))) (hj : j ∈ L) (ho : o % 4 = 0)
    (how : o / 4 < 10) (hx : encodable (BitVec.ofNat 32 x) = true)
    (hl : ∀ σ, E σ → A σ j < 2 ^ (32 * (o / 4))) :
    VP (St P E A L V LS) (.block (setWd j o x))
      (St P E (fun σ => upd (A σ) j (A σ j + 2 ^ (32 * (o / 4)) * (x % 2 ^ 32))) (j :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    rw [← List.append_nil (setWd j o x)]
    have hj' := h.live_lt j hj
    refine setWd_ok hw hj' (by decide) ho (by have := h.pre.wge; omega) hx (by rw [h.arrs j hj]; exact hl σ e)
      fun t ht k v r => WP.block_nil ⟨e, h.write1 k hj' (by simp) r.sp r.rd r.wr (by rw [v, h.arrs j hj]) (by simp),
        ht⟩

/-- `setS d v`: the header word `d := v`. -/
theorem St.psetS {d v : Nat} (cert : Cert (.block (setS d v))) (hd : LsOk d) (hv : encodable (BitVec.ofNat 32 v) = true)
    (hv' : v < 2 ^ 32) :
    VP (St P E A L V LS) (.block (setS d v)) (St P E A L (fun σ => upd (V σ) d v) (d :: LS)) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    unfold setS
    refine wp_mov (op2_imm hv) fun s1 u1 => ?_
    have h1 := h.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
    have hw1 := hw.of_upd u1 (by decide) (by decide) (by decide)
    refine h1.str hw1 hd fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
    rwa [u1.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv'] at ht

end

end VG.Proof.Dsa.Arm.Prime
