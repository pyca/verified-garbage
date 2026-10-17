module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecD
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: the calls of the hash functions

A call of verified code that writes only within `scratch` and the 3440
bytes below the frame (`hashCall`): it leaves a state of the body, and the
call's result (`Base.after`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

theorem In.safe_of_sub {σ : State} (h : In P σ) {r : Region} (hr : Region.Sub r P.SCR) : Safe P r := by
  have hw := h.ok.wrw
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hw
  exact ⟨hw.1.2.sub_right hr, (h.ok.stk_fr (R := P.SCR) (.inr (by simp)) (by simp only [oR, frameBytes]; decide)).sub_right hr⟩

theorem Base.after {σ s t : State} (h : Base P σ s) (st : P.lay.St σ t) {wr : List Region}
    (fr : Frame (wr ++ [P.lay.LOW]) s.mem t.mem) (hw : ∀ r ∈ wr, Region.Sub r P.SCR) : Base P σ t :=
  h.frame st fr fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact h.1.1.safe_of_sub (hw r hr)
    · simp only [List.mem_singleton] at hr; subst hr; exact h.1.1.safe_low

/-- A call of verified code `c`, given the regions `rd` and `wr`, writing only
within `scratch` and below the frame. -/
theorem hashCall {n : String} {c : Prog isa} {k : Contract isa} (hv : Verified target c k)
    (hst : FrameStack.armStack c ≤ 3440) (rd wr : List Region) {F G : State → State → Prop}
    (hS : ∀ σ s, F σ s → S P σ s)
    (pre : ∀ σ s, F σ s → k.pre (s.callEntry.withRegions rd wr))
    (cov : ∀ σ s, F σ s → Covers (rd ++ wr) (s.rd ++ s.wr) ∧ Covers wr s.wr)
    (hw : ∀ σ s, F σ s → ∀ r ∈ wr, Region.Sub r P.SCR)
    (pub : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ →
      k.pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr))
    (post : ∀ σ s s', F σ s → P.lay.St σ s' → Frame (wr ++ [P.lay.LOW]) s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      k.post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → G σ s') :
    VP F (.call n c) G :=
  VP.callF hv hst rd wr pre cov (fun σ s h => by rw [(hS σ s h).2.sp]; exact (hS σ s h).1.ok.B56) pub
    fun σ s s' h rd' wr' sp' fr g po => by
      have hs := hS σ s h
      have low : FrameStack.belowA s.sp 3440 = P.lay.LOW := by rw [hs.2.sp]; exact hs.1.ok.low_eq
      rw [low] at fr
      have st : P.lay.St σ s' := hs.2.write fr (fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact ⟨P.SCR, by simp, hw σ s h r hr⟩
        · simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.lay.LOW, by simp, fun _ h => h⟩) rd' wr' sp'
      exact post σ s s' h st fr g po

theorem In.subW {σ : State} (h : In P σ) {o n : Nat} (hn : o + n ≤ 8448) (ho : o < 8448) :
    Region.Sub ⟨State.addr (P.scr + BitVec.ofNat 32 o), n⟩ P.SCR := by
  rw [h.scrA ho]; exact h.sc_sub hn

theorem In.subW0 {σ : State} (h : In P σ) {n : Nat} (hn : n ≤ 8448) :
    Region.Sub ⟨State.addr P.scr, n⟩ P.SCR :=
  Region.sub_prefix (by have := h.sl8; omega)

theorem In.scW0 {σ s : State} (hs : S P σ s) {n : Nat} (hn : n ≤ 8448) :
    Covers [⟨State.addr P.scr, n⟩] s.wr := by
  have := St.sc_w hs (o := 0) (n := n) (by omega)
  simp only [BitVec.add_zero] at this
  exact Covers.one this

/-- `scratch + o` as an address. -/
theorem In.scW {σ s : State} (hs : S P σ s) {o n : Nat} (hn : o + n ≤ 8448) (ho : o < 8448) :
    Covers [⟨State.addr (P.scr + BitVec.ofNat 32 o), n⟩] s.wr := by
  rw [hs.1.scrA ho]; exact Covers.one (St.sc_w hs hn)

theorem In.frW {σ s : State} (hs : S P σ s) {n : Nat} (hn : n ≤ frameBytes) :
    Covers [⟨State.addr P.B, n⟩] s.wr := by
  have q0 : State.addr P.B = P.lay.fr 0 := by simp
  rw [q0]; exact Covers.one (hs.2.inFr (by show 0 + n ≤ frameBytes; omega))

theorem In.roR {σ s : State} (hs : S P σ s) {R : Region} (hR : R ∈ P.lay.ro) :
    Covers [R] (s.rd ++ s.wr) :=
  Covers.left (Covers.of_mem fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.rd, hs.1.ok.rd]; exact List.mem_append_left _ hR)

end VG.Proof.RsaPkcs1Enc.Arm.Dec
