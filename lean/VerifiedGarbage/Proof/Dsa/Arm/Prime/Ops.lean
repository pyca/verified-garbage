module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.St
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Words
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Math
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Words
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Rsa.Arm.RvCand2

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

/-- `setHi j sh c x`: word `i` of `[j]` := `x`, above the number, for `W 2^sh = 4 i + c`. -/
theorem St.psetHi {j sh c x : Nat} {i : CP → Nat} (cert : Cert (.block (setHi j sh c x))) (hj : j ∈ L)
    (hsh : 1 ≤ sh ∧ sh ≤ 2) (hc : encodable (BitVec.ofNat 32 c) = true) (hx : encodable (BitVec.ofNat 32 x) = true)
    (hi : ∀ σ, E σ → In P σ → P.W * 2 ^ sh = 4 * i P + c ∧ i P < P.W)
    (hl : ∀ σ, E σ → In P σ → A σ j < 2 ^ (32 * i P)) :
    VP (St P E A L V LS) (.block (setHi j sh c x))
      (St P E (fun σ => upd (A σ) j (A σ j + 2 ^ (32 * i P) * (x % 2 ^ 32))) (j :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    rw [← List.append_nil (setHi j sh c x)]
    have hj' := h.live_lt j hj
    obtain ⟨i1, i2⟩ := hi σ e h.pre
    refine setHi_ok hw hj' (by decide) hsh hc hx i1 i2 (by rw [h.arrs j hj]; exact hl σ e h.pre)
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

/-- `orOne j`: the low bit of `[j]` set. -/
theorem St.porOne {j : Nat} (cert : Cert (.block (orOne j))) (hj : j ∈ L) :
    VP (St P E A L V LS) (.block (orOne j))
      (St P E (fun σ => upd (A σ) j (2 * (A σ j / 2) + 1)) (j :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    rw [← List.append_nil (orOne j)]
    have hj' := h.live_lt j hj
    exact orOne_ok hw hj' (by decide) fun t ht k v r => WP.block_nil ⟨e, h.write1 k hj' (by simp) r.sp r.rd r.wr
      (by rw [v, h.arrs j hj]) (by simp), ht⟩

/-- `orTwo j`: bit 1 of `[j]` set. -/
theorem St.porTwo {j : Nat} (cert : Cert (.block (orTwo j))) (hj : j ∈ L) :
    VP (St P E A L V LS) (.block (orTwo j))
      (St P E (fun σ => upd (A σ) j (A σ j ||| 2)) (j :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    unfold orTwo
    rw [← List.append_nil (ptr .r0 j ++ _), List.append_assoc]
    have hj' := h.live_lt j hj
    refine lowOp_ok (ops := [.dp .orr .r1 .r1 (.imm 2)]) (f := fun x => x ||| 2) hw hj' (by decide)
      (fun u R k' => wp_dp (op2_imm (by decide)) fun u' up => WP.block_nil (k' u' up))
      fun t ht k v r _ => WP.block_nil ⟨e, h.write1 k hj' (by simp) r.sp r.rd r.wr ?_ (by simp), ht⟩
    rw [v, h.arrs j hj, or_low (b := 2) (by decide), BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_mod]
    rfl

/-- A word op on word `i` of `[j]`, at byte `4 W − c`: the number becomes `g`. -/
theorem St.phiOp {j c : Nat} {i : CP → Nat} {ops : List Instr} {f : BitVec 32 → BitVec 32} {g : State → Nat}
    (cert : Cert (.block (ptr .r0 j ++ .dp .add .r0 .r0 (.shifted .r9 .lsl 2) ::
      .dp .sub .r0 .r0 (.imm (BitVec.ofNat 32 c)) :: .ldr .r1 .r0 0 :: (ops ++ ([.str .r1 .r0 0] : List Instr)))))
    (hj : j ∈ L) (hc : encodable (BitVec.ofNat 32 c) = true)
    (hi : ∀ σ, E σ → In P σ → P.W * 4 = 4 * i P + c ∧ i P < P.W)
    (hops : ∀ u : State, ∀ R : State → Prop, (∀ u', Upd u u' .r1 (f (u.gpr .r1)) → R u') →
      WP isa (.block ops) u R)
    (hg : ∀ σ, E σ → In P σ → A σ j % 2 ^ (32 * i P) +
        2 ^ (32 * i P) * (f (BitVec.ofNat 32 (A σ j / 2 ^ (32 * i P) % 2 ^ 32))).toNat +
        2 ^ (32 * (i P + 1)) * (A σ j / 2 ^ (32 * (i P + 1))) = g σ) :
    VP (St P E A L V LS) (.block (ptr .r0 j ++ .dp .add .r0 .r0 (.shifted .r9 .lsl 2) ::
      .dp .sub .r0 .r0 (.imm (BitVec.ofNat 32 c)) :: .ldr .r1 .r0 0 :: (ops ++ ([.str .r1 .r0 0] : List Instr))))
      (St P E (fun σ => upd (A σ) j (g σ)) (j :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    have hj' := h.live_lt j hj
    obtain ⟨i1, i2⟩ := hi σ e h.pre
    exact hiOp_ok hw hj' (by decide) hc i1 i2 hops fun t ht k v r => WP.block_nil
      ⟨e, h.write1 k hj' (by simp) r.sp r.rd r.wr (by rw [v, h.arrs j hj]; exact hg σ e h.pre) (by simp), ht⟩

end

end VG.Proof.Dsa.Arm.Prime
