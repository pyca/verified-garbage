module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTCalls
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View

/-!
# RSA paddings on PPC64LE: two runs

Untrusted: everything here is checked by Lean. Two runs are compared through
an anchor `a`, a state with their public data: for a function whose entry
states satisfy `Pre`, `Pub a s` says the entry state `s` has `a`'s public
data, and `B S vf Pre Pub a t` that `t` has `Base` from such an entry state.
`Ok` is what the shared code needs of `Pre` and `Pub`: `Pre` gives what
`Base` needs (`Fits`), and `Pub a s` that `s` agrees with `a` on what `Base`
fixes (`Agree`), so that `r14`–`r23` hold `a`'s values (`Base.agree`).
`two_seq`: a piece checked for both runs, then what each run satisfies after
it by correctness.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo Two Pins two_post wp_addi wp_nil)

/-- The entry state `s` agrees with the anchor `a` on what `Base` fixes. -/
structure Agree (S : State → Addr) (vf : State → Reg → BitVec 64) (a s : State) : Prop where
  sp : s.sp = a.sp
  S : S s = S a
  v : ∀ r ∈ fx, vf s r = vf a r

/-- What the shared code needs of a function's entry states (`Pre`) and of
their public data (`Pub`). -/
structure Ok (S : State → Addr) (vf : State → Reg → BitVec 64) (Pre : State → Prop)
    (Pub : State → State → Prop) : Prop where
  fits : ∀ {s}, Pre s → Fits S s
  agree : ∀ {a s}, Pub a s → Agree S vf a s

/-- What MGF1 and the hash functions' calls need: `Pre` gives `Fits`, and
`Pub a s` that `s` agrees with `a` on the stack pointer and `S`, whatever
`r15`–`r23` hold (a function may keep secrets there, as decryption keeps the
private operation's result). -/
structure OkS (S : State → Addr) (Pre : State → Prop) (Pub : State → State → Prop) : Prop where
  fits : ∀ {s}, Pre s → Fits S s
  sp : ∀ {a s}, Pub a s → s.sp = a.sp
  S : ∀ {a s}, Pub a s → S s = S a

theorem Ok.s {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop}
    {Pub : State → State → Prop} (X : Ok S vf Pre Pub) : OkS S Pre Pub :=
  ⟨X.fits, fun p => (X.agree p).sp, fun p => (X.agree p).S⟩

/-- `t` has `Base` from an entry state with `a`'s public data. -/
def B (S : State → Addr) (vf : State → Reg → BitVec 64) (Pre : State → Prop) (Pub : State → State → Prop)
    (a t : State) : Prop :=
  ∃ s, Pre s ∧ Pub a s ∧ Base S vf s t

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}

/-- What `Base` fixes, from the anchor. -/
theorem Base.agree {a s t : State} (g : Agree S vf a s) (h : Base S vf s t) :
    t.sp = fb a ∧ t.gpr .r14 = S a ∧ ∀ r ∈ fx, t.gpr r = vf a r :=
  ⟨by rw [h.sp, fb, fb, g.sp], h.r14.trans g.S, fun r hr => (h.vs r hr).trans (g.v r hr)⟩

variable (X : Ok S vf Pre Pub)
include X

theorem B.agree {a t : State} (h : B S vf Pre Pub a t) :
    t.sp = fb a ∧ t.gpr .r14 = S a ∧ ∀ r ∈ fx, t.gpr r = vf a r :=
  let ⟨_, _, p, b⟩ := h; b.agree (X.agree p)

theorem B.sp {a t : State} (h : B S vf Pre Pub a t) : t.sp = fb a := (h.agree X).1

theorem B.only {a t t' : State} {rs : List Reg} (h : B S vf Pre Pub a t) (o : Only rs t t')
    (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : B S vf Pre Pub a t' :=
  let ⟨s, P, p, b⟩ := h; ⟨s, P, p, b.only (X.fits P) o hrs⟩

end

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
  (X : OkS S Pre Pub)
include X

omit X in
theorem Base.spA (X : OkS S Pre Pub) {a s t : State} (p : Pub a s) (b : Base S vf s t) : t.sp = fb a := by
  rw [b.sp, fb, fb, X.sp p]

theorem B.spS {a t : State} (h : B S vf Pre Pub a t) : t.sp = fb a :=
  let ⟨_, _, p, b⟩ := h; by rw [b.sp, fb, fb, X.sp p]

theorem B.r14S {a t : State} (h : B S vf Pre Pub a t) : t.gpr .r14 = S a :=
  let ⟨_, _, p, b⟩ := h; b.r14.trans (X.S p)

theorem B.onlyS {a t t' : State} {rs : List Reg} (h : B S vf Pre Pub a t) (o : Only rs t t')
    (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : B S vf Pre Pub a t' :=
  let ⟨s, P, p, b⟩ := h; ⟨s, P, p, b.only (X.fits P) o hrs⟩

end

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
variable (X : Ok S vf Pre Pub)
include X

/-- Pins of states with `B` and more. -/
theorem pins_of {α : Type} {Φ : α → State → Prop} {an : α → State} (h : ∀ a t, Φ a t → B S vf Pre Pub (an a) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ Reg.r14 :: fx := by decide) : Pins Φ rs := fun a t₁ t₂ h₁ h₂ => by
  obtain ⟨f₁, g₁, v₁⟩ := (h a t₁ h₁).agree X
  obtain ⟨f₂, g₂, v₂⟩ := (h a t₂ h₂).agree X
  refine ⟨f₁.trans f₂.symm, fun r hr => ?_⟩
  rcases List.mem_cons.mp (hrs r hr) with rfl | hr'
  · exact g₁.trans g₂.symm
  · exact (v₁ r hr').trans (v₂ r hr').symm

/-- `r3 := S + oSt`. -/
theorem st_wp {a t : State} (h : B S vf Pre Pub a t) :
    WP isa (.block [.addi .r3 .r14 oSt]) t fun t' => B S vf Pre Pub a t' ∧ t'.gpr .r3 = off (S a) oSt :=
  wp_addi fun t' o e => wp_nil ⟨h.only X o, by rw [e, (h.agree X).2.1]⟩

end

/-- A piece of code checked for both runs, then the rest from what each run
satisfies after it. -/
theorem two_seq {α : Type} {Φ Ψ : α → State → Prop} {R : State → State → Prop} {c₁ c₂ : Prog isa}
    (h₁ : RelCT isa (Two Φ) c₁ fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c₁ s (Ψ a))
    (h₂ : RelCT isa (Two Ψ) c₂ R) : RelCT isa (Two Φ) (.seq c₁ c₂) R :=
  RelCT.seq (two_post h₁ hw) h₂

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
  (X : Ok S vf Pre Pub) {H : Hash} (hH : HashOK H) (cH : HashCT hH)

include X cH in
/-- `init` on the state at `S + oSt`, in both runs. -/
theorem init_two {Φ : State → State → Prop} (h : ∀ a t, Φ a t → B S vf Pre Pub a t ∧ t.gpr .r3 = off (S a) oSt) :
    RelCT isa (Two Φ) H.callInit fun _ _ => True :=
  init_ct (S := S) (vf := vf) cH fun t₁ t₂ ⟨a, h₁, h₂⟩ => by
    obtain ⟨⟨s₁, P₁, p₁, b₁⟩, e₁⟩ := h a t₁ h₁
    obtain ⟨⟨s₂, P₂, p₂, b₂⟩, e₂⟩ := h a t₂ h₂
    exact ⟨s₁, s₂, X.fits P₁, b₁, by rw [e₁, (X.agree p₁).S], X.fits P₂, b₂, by rw [e₂, (X.agree p₂).S],
      e₁.trans e₂.symm, (b₁.agree (X.agree p₁)).1.trans (b₂.agree (X.agree p₂)).1.symm⟩

include X hH in
theorem init_wp {a t : State} (h : B S vf Pre Pub a t) (h3 : t.gpr .r3 = off (S a) oSt) :
    WP isa H.callInit t (B S vf Pre Pub a) := by
  obtain ⟨s, P, p, b⟩ := h
  exact WP.mono (init_ok (X.fits P) hH b (by rw [h3, (X.agree p).S])) fun t' ⟨b', _⟩ => ⟨s, P, p, b'⟩

end

end VG.Proof.RsaOaep.PPC64LE
