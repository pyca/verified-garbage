module
public import VerifiedGarbage.Proof.Rsa.Arm.RvSt
public import VerifiedGarbage.Proof.Rsa.RecoverExp

import VerifiedGarbage.Proof.Rsa.RecoverSubtract
import VerifiedGarbage.Proof.Rsa.Arm.RvStage
import VerifiedGarbage.Proof.Rsa.Arm.RvOps2
import VerifiedGarbage.Proof.Rsa.Arm.RvLoads

/-! # `vg_rsa_recover_primes` on ARMv7: the steps of the factors as pieces

`Sk`: a stage of the working space with `v` words, without Montgomery
multiplication (which the factors no longer use).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (b2n)

/-- A stage without Montgomery multiplication. -/
abbrev Sk (P : RP) (E : State → Prop) (A : State → Nat → Nat) (L : List Nat) (AW : State → Nat → Nat)
    (LW : List Nat) (V : State → Nat → Nat) (LS : List Nat) (v N : Nat) (σ s : State) : Prop :=
  E σ ∧ KS P σ (A σ) L (AW σ) LW (V σ) LS s ∧ Ws s P.B P.Z v N

/-- `a - b` modulo `2^(32 w)`. -/
def sub32 (w a b : Nat) : Nat := (a + 2 ^ (32 * w) - b) % 2 ^ (32 * w)

theorem sub32_of {X a b w c : Nat} (hX : X < 2 ^ (32 * w)) (hb : b < 2 ^ (32 * w))
    (h : X + b = a + 2 ^ (32 * w) * c) (hc : c ≤ 1) : X = sub32 w a b ∧ c = b2n (decide (a < b)) :=
  VG.Proof.Rsa.sub32_of hX hb h hc

section
variable {P : RP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {AW : State → Nat → Nat}
  {LW : List Nat} {V : State → Nat → Nat} {LS : List Nat}

theorem Sk.pcopy {o a : Nat} (cert : Cert (copy o a)) (ho : o < nArr) (ha : a ∈ L) (hoa : o ≠ a)
    (hlW : ∀ j ∈ LW, o / 2 ≠ j) :
    VP (Sk P E A L AW LW V LS P.w nArr) (copy o a)
      (Sk P E (fun σ => upd (A σ) o (A σ a)) (o :: L) AW LW V LS P.w nArr) :=
  VP.ctx cert (fun _ _ h => h.2.2) fun _ _ ⟨e, h, hw⟩ =>
    WP.mono (h.copy_w hw ho ha hoa hlW) fun _ ⟨ht, hwt, _⟩ => ⟨e, ht, hwt⟩

theorem Sk.psel {o a b sl : Nat} (cert : Cert (sel o a b sl)) (ho : o < nArr) (ha : a ∈ L) (hb : b ∈ L)
    (hoa : o ≠ a) (hob : o ≠ b) (hsl : sl ∈ LS) (bit : ∀ σ, E σ → V σ sl ≤ 1) (hlW : ∀ j ∈ LW, o / 2 ≠ j) :
    VP (Sk P E A L AW LW V LS P.w nArr) (sel o a b sl)
      (Sk P E (fun σ => upd (A σ) o (if V σ sl = 0 then A σ a else A σ b)) (o :: L) AW LW V LS P.w nArr) :=
  VP.ctx cert (fun _ _ h => h.2.2) fun σ _ ⟨e, h, hw⟩ =>
    WP.mono (h.sel_w hw ho ha hb hoa hob hsl (bit σ e) hlW) fun _ ⟨ht, hwt, _⟩ => ⟨e, ht, hwt⟩

theorem Sk.psub3 {o a b : Nat} (cert : Cert (sub3 o a b)) (ho : o < nArr) (ha : a ∈ L) (hb : b ∈ L)
    (hoa : o ≠ a) (hob : o ≠ b) (hlW : ∀ j ∈ LW, o / 2 ≠ j)
    (hv : ∀ σ, E σ → A σ a < 2 ^ (32 * P.w) ∧ A σ b < 2 ^ (32 * P.w)) :
    VP (Sk P E A L AW LW V LS P.w nArr) (sub3 o a b) (fun σ s =>
      Sk P E (fun σ => upd (A σ) o (sub32 P.w (A σ a) (A σ b))) (o :: L) AW LW V LS P.w nArr σ s ∧
        (s.gpr .r11).toNat = b2n (decide (A σ a < A σ b))) :=
  VP.ctx cert (fun _ _ h => h.2.2) fun σ _ ⟨e, h, hw⟩ =>
    WP.mono (h.sub3_w hw ho ha hb hoa hob hlW) fun t ⟨X, ht, hwt, _, hx, hc⟩ => by
      have hX : X < 2 ^ (32 * P.w) := by
        rw [← show num t.mem P.B P.w o = X by rw [ht.arrs o (List.mem_cons_self ..), upd_self]]
        exact val32_lt _ _ _ _
      obtain ⟨e1, e2⟩ := sub32_of hX (hv σ e).2 hx hc
      rw [e1] at ht
      exact ⟨⟨e, ht, hwt⟩, e2⟩

theorem Sk.psetOne {j : Nat} (cert : Cert (.block (setOne j))) (hj : j ∈ L) (hlW : ∀ i ∈ LW, j / 2 ≠ i) :
    VP (Sk P E A L AW LW V LS P.w nArr) (.block (setOne j))
      (Sk P E (fun σ => upd (A σ) j (1 + 2 ^ 32 * (A σ j / 2 ^ 32))) (j :: L) AW LW V LS P.w nArr) := by
  refine VP.ctx cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  rw [← List.append_nil (setOne j)]
  exact h.setOne_w hw hj hlW fun t ht hwt _ => WP.block_nil ⟨e, ht, hwt⟩

theorem St.toSk : VP (St P E A L AW LW V LS P.w nArr) (.block []) (Sk P E A L AW LW V LS P.w nArr) :=
  VP.block_nil fun _ _ h => ⟨h.1, h.2.1, h.2.2.2⟩

theorem Sk.mono {E' : State → Prop} {A' : State → Nat → Nat} {L' : List Nat} {AW' : State → Nat → Nat}
    {LW' : List Nat} {V' : State → Nat → Nat} {LS' : List Nat} {v N : Nat} {σ s : State}
    (h : Sk P E A L AW LW V LS v N σ s) (he : E' σ)
    (hl : ∀ j ∈ L', j ∈ L ∧ A σ j = A' σ j) (hlW : ∀ j ∈ LW', j ∈ LW ∧ AW σ j = AW' σ j)
    (hls : ∀ d ∈ LS', d ∈ LS ∧ V σ d = V' σ d) : Sk P E' A' L' AW' LW' V' LS' v N σ s :=
  ⟨he, h.2.1.mono hl hlW hls, h.2.2⟩

end

end VG.Proof.Rsa.Arm.Recover
