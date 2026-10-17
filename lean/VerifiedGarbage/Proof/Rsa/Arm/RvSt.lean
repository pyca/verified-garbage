module

public import VerifiedGarbage.Proof.Rsa.Arm.RvMont5
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_recover_primes` on ARMv7: the steps of the candidates as pieces

`St P E A L AW LW V LS v N`: the stage, with Montgomery multiplication
ready and the context of the working space with `v` words; each step of the
candidates as a piece from one such stage to the next.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

/-- A stage of the candidates. -/
abbrev St (P : RP) (E : State → Prop) (A : State → Nat → Nat) (L : List Nat) (AW : State → Nat → Nat)
    (LW : List Nat) (V : State → Nat → Nat) (LS : List Nat) (v N : Nat) (σ s : State) : Prop :=
  E σ ∧ KS P σ (A σ) L (AW σ) LW (V σ) LS s ∧ MM P s ∧ Ws s P.B P.Z v N

section
variable {P : RP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {AW : State → Nat → Nat}
  {LW : List Nat} {V : State → Nat → Nat} {LS : List Nat}

/-- Taint certificates of the working space's pieces. -/
abbrev Cert (c : Prog isa) : Prop := ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs ctxRegs) c hc).isSome = true

theorem St.pcopy {o a : Nat} (cert : Cert (copy o a)) (ho : o < nArr) (hoM : mBase < o) (ha : a ∈ L)
    (hoa : o ≠ a) (hlW : ∀ j ∈ LW, o / 2 ≠ j) :
    VP (St P E A L AW LW V LS P.w nArr) (copy o a)
      (St P E (fun σ => upd (A σ) o (A σ a)) (o :: L) AW LW V LS P.w nArr) :=
  VP.ctx cert (fun _ _ h => h.2.2.2) fun _ _ ⟨e, h, hm, hw⟩ =>
    WP.mono (h.copy_m hm hw ho hoM ha hoa hlW) fun _ ⟨ht, mt, hwt, _⟩ => ⟨e, ht, mt, hwt⟩

theorem St.pcopyW {o a : Nat} (cert : Cert (copy o a)) (ho : o < 22) (hoM : 10 < o) (ha : a ∈ LW)
    (hoa : o ≠ a) (hl : ∀ j ∈ L, j / 2 ≠ o) :
    VP (St P E A L AW LW V LS P.W 22) (copy o a)
      (St P E A L (fun σ => upd (AW σ) o (AW σ a)) (o :: LW) V LS P.W 22) :=
  VP.ctx cert (fun _ _ h => h.2.2.2) fun _ _ ⟨e, h, hm, hw⟩ =>
    WP.mono (h.copy_Wm hm hw ho hoM ha hoa hl) fun _ ⟨ht, mt, hwt, _⟩ => ⟨e, ht, mt, hwt⟩

theorem St.psel {o a b sl : Nat} (cert : Cert (sel o a b sl)) (ho : o < nArr) (hoM : mBase < o) (ha : a ∈ L)
    (hb : b ∈ L) (hoa : o ≠ a) (hob : o ≠ b) (hsl : sl ∈ LS) (bit : ∀ σ, E σ → V σ sl ≤ 1)
    (hlW : ∀ j ∈ LW, o / 2 ≠ j) :
    VP (St P E A L AW LW V LS P.w nArr) (sel o a b sl)
      (St P E (fun σ => upd (A σ) o (if V σ sl = 0 then A σ a else A σ b)) (o :: L) AW LW V LS P.w nArr) :=
  VP.ctx cert (fun _ _ h => h.2.2.2) fun σ _ ⟨e, h, hm, hw⟩ =>
    WP.mono (h.sel_m hm hw ho hoM ha hb hoa hob hsl (bit σ e) hlW) fun _ ⟨ht, mt, hwt, _⟩ => ⟨e, ht, mt, hwt⟩

theorem St.peqS {d a b : Nat} (cert : Cert (eqS d a b aW)) (ha : a ∈ L) (hb : b ∈ L) (hd : SlotOk d)
    (hW : aW ∉ L) (hlW : ∀ j ∈ LW, aW / 2 ≠ j) (hls : ∀ e ∈ LS, e + 4 ≤ sT ∨ sT + 4 ≤ e) (hdT : d ≠ sT) :
    VP (St P E A L AW LW V LS P.w nArr) (eqS d a b aW)
      (St P E A L AW LW (fun σ => upd (V σ) d (if A σ a = A σ b then 1 else 0)) (d :: LS) P.w nArr) :=
  VP.ctx cert (fun _ _ h => h.2.2.2) fun _ _ ⟨e, h, hm, hw⟩ =>
    WP.mono (h.eqS_m hm hw ha hb hd hW hlW hls hdT) fun _ ⟨ht, mt, hwt, _⟩ => ⟨e, ht, mt, hwt⟩

theorem St.pmmul {o a b : Nat} (hi : MIdx o a b) (hodd : P.n % 2 = 1) {T : State → Nat}
    (ha : mBase + a ∈ L) (hb : mBase + b ∈ L) (hl2 : mBase + 2 ∉ L) (hl3 : mBase + 3 ∉ L)
    (hlW : ∀ j ∈ LW, j ≠ (mBase + 2) / 2 ∧ j ≠ (mBase + o) / 2)
    (hv : ∀ σ, E σ → A σ (mBase + a) < P.n ∧ A σ (mBase + b) < P.n ∧ T σ < P.n ∧
      T σ * 2 ^ (64 * P.w6) % P.n = A σ (mBase + a) * A σ (mBase + b) % P.n) :
    VP (St P E A L AW LW V LS P.w nArr) (seqs (mmul o a b))
      (St P E (fun σ => upd (A σ) (mBase + o) (T σ)) ((mBase + o) :: L) AW LW V LS P.w nArr) :=
  (mmul_vp hi hodd ha hb hl2 hl3 hlW hv).mono (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩) fun _ _ h => h

theorem St.pctxW : VP (St P E A L AW LW V LS P.w nArr) (.block ctxW) (St P E A L AW LW V LS P.W 22) :=
  VP.taint [.r8] ctxW_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1.r8, h₂.2.1.r8])
    fun _ _ ⟨e, h, hm, _⟩ => WP.mono (ctxW_ok h.bs h.r8 h.cnt) fun _ ⟨ht, r, m⟩ =>
      ⟨e, h.of_rest r m (by decide), hm.of_rest r m, ht⟩

theorem St.pctxw : VP (St P E A L AW LW V LS P.W 22) (.block ctxw) (St P E A L AW LW V LS P.w nArr) :=
  VP.taint [.r8] ctxw_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1.r8, h₂.2.1.r8])
    fun _ _ ⟨e, h, hm, _⟩ => WP.mono (ctxw_ok h.bs h.r8 h.cnt) fun _ ⟨ht, r, m⟩ =>
      ⟨e, h.of_rest r m (by decide), hm.of_rest r m, ht⟩

theorem St.pcnt {v N : Nat} (cert : Cert (.block cntNext)) (hws : ∀ s, Ws s P.B P.Z v N → Ws s P.B P.Z P.w nArr)
    (hc : sCnt ∈ LS) (h1 : ∀ σ, E σ → 1 ≤ V σ sCnt) (h2 : ∀ σ, E σ → V σ sCnt < 2 ^ 32) :
    VP (St P E A L AW LW V LS v N) (.block cntNext) (fun σ s =>
      St P E A L AW LW (fun σ => upd (V σ) sCnt (V σ sCnt - 1)) (sCnt :: LS) v N σ s ∧
        s.z = decide (V σ sCnt - 1 = 0)) :=
  VP.ctx cert (fun _ _ h => hws _ h.2.2.2) fun σ _ ⟨e, h, hm, hw⟩ =>
    WP.mono (h.cntNext_m hm hw hc (h1 σ e) (h2 σ e)) fun _ ⟨ht, mt, hwt, z⟩ => ⟨⟨e, ht, mt, hwt⟩, z⟩

theorem St.mono {A' : State → Nat → Nat} {L' : List Nat} {AW' : State → Nat → Nat} {LW' : List Nat}
    {V' : State → Nat → Nat} {LS' : List Nat} {v N : Nat} {σ s : State} (h : St P E A L AW LW V LS v N σ s)
    (hl : ∀ j ∈ L', j ∈ L ∧ A σ j = A' σ j) (hlW : ∀ j ∈ LW', j ∈ LW ∧ AW σ j = AW' σ j)
    (hls : ∀ d ∈ LS', d ∈ LS ∧ V σ d = V' σ d) : St P E A' L' AW' LW' V' LS' v N σ s :=
  ⟨h.1, h.2.1.mono hl hlW hls, h.2.2⟩

end

end VG.Proof.Rsa.Arm.Recover
