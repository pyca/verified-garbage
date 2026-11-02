module

-- separate module: it needs only `Base`, so it builds in parallel with the proofs of correctness, from
-- `Pre` to `Correct`.
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Base
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSA paddings on RISC-V: two runs, and the calls of the hash functions

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/CTCalls.lean`, `CTBase.lean`). `HashCT`: a hash
function's streaming functions are constant time for the contracts the
proofs call them by (`initK`, `updK`, `finK`, whose public data are their
pointers, lengths and the stack pointer); `init_ct`, `upd_ct` and `fin_ct`:
two runs of a call from states with `Base` and the same arguments leak alike
(`RelCT.callEx`). Two runs are compared through an anchor `a`, a state with
their public data: for a function whose entry states satisfy `Pre`,
`Pub a s` says the entry state `s` has `a`'s public data, and
`B S vf Pre Pub a t` that `t` has `Base` from such an entry state. `Ok` is
what the shared code needs of `Pre` and `Pub`: `Pre` gives `Fits`, and
`Pub a s` that `s` agrees with `a` on what `Base` fixes (`Agree`), so that
`s0`–`s4` hold `a`'s values (`Base.agree`). `two_seq`: a piece checked for
both runs, then what each run satisfies after it by correctness.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK initK updK finK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo Two Pins two_post wp_addi wp_nil)

/-- The constant time of a hash function's streaming functions. -/
structure HashCT {H : Hash} (hH : HashOK H) : Prop where
  init : ConstantTime isa (initK H.S hH.SH.Repr).pre (initK H.S hH.SH.Repr).pub H.initC
  upd : ConstantTime isa (updK H.S H.F hH.SH.Repr).pre (updK H.S H.F hH.SH.Repr).pub H.updC
  fin : ConstantTime isa (finK H.S H.F H.D hH.SH.Repr hH.SH.H.hash).pre
    (finK H.S H.F H.D hH.SH.Repr hH.SH.H.hash).pub H.finC

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {H : Hash} {hH : HashOK H} (cH : HashCT hH)
  (hF : H.F ≤ 208)
include cH hF

omit hF in
/-- `init` on the state at `S + oSt`, in both runs. -/
theorem init_ct {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → ∃ s₁ s₂, Fits S s₁ ∧ Base S vf s₁ t₁ ∧ t₁.gpr .a0 = off (S s₁) oSt ∧
      Fits S s₂ ∧ Base S vf s₂ t₂ ∧ t₂.gpr .a0 = off (S s₂) oSt ∧ t₁.gpr .a0 = t₂.gpr .a0 ∧ t₁.sp = t₂.sp) :
    RelCT isa P H.callInit fun _ _ => True := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _⟩ := offs
  refine RelCT.callEx hH.init cH.init fun t₁ t₂ hp => ?_
  obtain ⟨s₁, s₂, P₁, b₁, h₁, P₂, b₂, h₂, e0, esp⟩ := hP t₁ t₂ hp
  have pre : ∀ {s t : State}, Fits S s → Base S vf s t → t.gpr .a0 = off (S s) oSt →
      (initK H.S hH.SH.Repr).pre (t.callEntry.withRegions [] [⟨t.gpr .a0, H.S⟩]) := fun {s t} _ _ _ => by
    simp only [initK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide)]
    exact ⟨trivial, trivial⟩
  have cov : ∀ {s t : State}, Fits S s → Base S vf s t → t.gpr .a0 = off (S s) oSt →
      Covers [⟨t.gpr .a0, H.S⟩] t.wr := fun {s t} P b h => by rw [h, b.wr]; exact sc_cov P (by omega)
  refine ⟨[], _, [], _, pre P₁ b₁ h₁, pre P₂ b₂ h₂, ?_, by rw [List.nil_append]; exact Covers.right (cov P₁ b₁ h₁),
    cov P₁ b₁ h₁, by rw [List.nil_append]; exact Covers.right (cov P₂ b₂ h₂), cov P₂ b₂ h₂⟩
  simp only [initK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp]
  exact ⟨by rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), e0], esp⟩

/-- What a call of `update` needs, in a run from the entry state `s`. -/
structure UpdArgs (S : State → Addr) (vf : State → Reg → BitVec 64) (H : Hash) (s t : State) (dat : Addr)
    (len : Nat) : Prop where
  P : Fits S s
  b : Base S vf s t
  h0 : t.gpr .a0 = off (S s) oSt
  h2 : t.gpr .a2 = dat
  h3 : (t.gpr .a3).toNat = len
  hdc : Covers [⟨dat, len⟩] (t.rd ++ t.wr)
  hd₁ : Region.Disjoint ⟨dat, len⟩ ⟨off (S s) oSt, H.S⟩
  hd₃ : (cR s).Disjoint ⟨dat, len⟩

/-- `update` on the state at `S + oSt`, in both runs, with the same
arguments. -/
theorem upd_ct {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → ∃ s₁ s₂ d₁ d₂ l₁ l₂, UpdArgs S vf H s₁ t₁ d₁ l₁ ∧ UpdArgs S vf H s₂ t₂ d₂ l₂ ∧
      (∀ r ∈ [Reg.a0, .a1, .a2, .a3], t₁.gpr r = t₂.gpr r) ∧ t₁.sp = t₂.sp) :
    RelCT isa P H.callUpd fun _ _ => True := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _⟩ := offs
  refine RelCT.callEx hH.upd cH.upd fun t₁ t₂ hp => ?_
  obtain ⟨s₁, s₂, d₁, d₂, l₁, l₂, A₁, A₂, eg, esp⟩ := hP t₁ t₂ hp
  have pre : ∀ {s t : State} {d : Addr} {l : Nat}, UpdArgs S vf H s t d l →
      (updK H.S H.F hH.SH.Repr).pre (t.callEntry.withRegions [⟨d, l⟩] [⟨off (S s) oSt, H.S⟩]) :=
    fun {s t d l} A => by
    have c0 : t.callEntry.gpr .a0 = t.gpr .a0 := State.callEntry_gpr _ (by decide)
    have c2 : t.callEntry.gpr .a2 = t.gpr .a2 := State.callEntry_gpr _ (by decide)
    have c3 : t.callEntry.gpr .a3 = t.gpr .a3 := State.callEntry_gpr _ (by decide)
    simp only [updK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp, c0, c2, c3, A.h0, A.h2, A.h3]
    exact ⟨trivial, trivial, A.hd₁, A.b.al A.P, A.b.spF A.P hF, A.b.cRd A.P hF (by omega),
      by rw [A.b.sp]; exact A.hd₃.sub_left (below_sub hF (by omega))⟩
  have cov : ∀ {s t : State} {d : Addr} {l : Nat}, UpdArgs S vf H s t d l →
      Covers [⟨off (S s) oSt, H.S⟩] t.wr := fun {s t d l} A => by
    rw [A.b.wr]; exact sc_cov A.P (by omega)
  refine ⟨_, _, _, _, pre A₁, pre A₂, ?_, Covers.append_left A₁.hdc (Covers.right (cov A₁)), cov A₁,
    Covers.append_left A₂.hdc (Covers.right (cov A₂)), cov A₂⟩
  simp only [updK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp]
  simp only [State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a3 ∉ linkRegs by decide)]
  exact ⟨eg _ (by decide), eg _ (by decide), eg _ (by decide), eg _ (by decide), esp⟩

/-- What a call of `finalize` needs, in a run from the entry state `s`. -/
structure FinArgs (S : State → Addr) (vf : State → Reg → BitVec 64) (s t : State) : Prop where
  P : Fits S s
  b : Base S vf s t
  h0 : t.gpr .a0 = off (S s) oSt
  h2 : t.gpr .a2 = off (S s) oDig

/-- `finalize` on the state at `S + oSt`, in both runs, with the same
arguments. -/
theorem fin_ct {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → ∃ s₁ s₂, FinArgs S vf s₁ t₁ ∧ FinArgs S vf s₂ t₂ ∧
      (∀ r ∈ [Reg.a0, .a1, .a2], t₁.gpr r = t₂.gpr r) ∧ t₁.sp = t₂.sp) :
    RelCT isa P H.callFin fun _ _ => True := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _⟩ := offs
  refine RelCT.callEx hH.fin cH.fin fun t₁ t₂ hp => ?_
  obtain ⟨s₁, s₂, A₁, A₂, eg, esp⟩ := hP t₁ t₂ hp
  have pre : ∀ {s t : State}, FinArgs S vf s t →
      (finK H.S H.F H.D hH.SH.Repr hH.SH.H.hash).pre (t.callEntry.withRegions []
        [⟨off (S s) oSt, H.S⟩, ⟨off (S s) oDig, H.D⟩]) := fun {s t} A => by
    have c0 : t.callEntry.gpr .a0 = t.gpr .a0 := State.callEntry_gpr _ (by decide)
    have c2 : t.callEntry.gpr .a2 = t.gpr .a2 := State.callEntry_gpr _ (by decide)
    simp only [finK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp, c0, c2, A.h0, A.h2]
    exact ⟨trivial, trivial, sdis (.inl (by omega)) (by omega) (by omega), A.b.al A.P, A.b.spF A.P hF,
      A.b.cRd A.P hF (by omega), A.b.cRd A.P hF (by omega)⟩
  have cov : ∀ {s t : State}, FinArgs S vf s t →
      Covers [⟨off (S s) oSt, H.S⟩, ⟨off (S s) oDig, H.D⟩] t.wr := fun {s t} A => by
    rw [A.b.wr]; exact Covers.pair (sc_cov A.P (by omega)) (sc_cov A.P (by omega))
  refine ⟨[], _, [], _, pre A₁, pre A₂, ?_, by rw [List.nil_append]; exact Covers.right (cov A₁), cov A₁,
    by rw [List.nil_append]; exact Covers.right (cov A₂), cov A₂⟩
  simp only [finK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp]
  simp only [State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide)]
  exact ⟨eg _ (by decide), eg _ (by decide), eg _ (by decide), esp⟩

end

/-! ## Two runs -/

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
`s1`–`s4` hold. -/
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
    t.sp = fb a ∧ t.gpr .s0 = S a ∧ ∀ r ∈ fx, t.gpr r = vf a r :=
  ⟨by rw [h.sp, fb, fb, g.sp], h.s0.trans g.S, fun r hr => (h.vs r hr).trans (g.v r hr)⟩

variable (X : Ok S vf Pre Pub)
include X

theorem B.agree {a t : State} (h : B S vf Pre Pub a t) :
    t.sp = fb a ∧ t.gpr .s0 = S a ∧ ∀ r ∈ fx, t.gpr r = vf a r :=
  let ⟨_, _, p, b⟩ := h; b.agree (X.agree p)

theorem B.sp {a t : State} (h : B S vf Pre Pub a t) : t.sp = fb a := (h.agree X).1

theorem B.only {a t t' : State} {rs : List Reg} (h : B S vf Pre Pub a t) (o : Only rs t t')
    (hrs : ∀ r ∈ rs, r ∉ fixed := by decide) : B S vf Pre Pub a t' :=
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

theorem B.s0S {a t : State} (h : B S vf Pre Pub a t) : t.gpr .s0 = S a :=
  let ⟨_, _, p, b⟩ := h; b.s0.trans (X.S p)

theorem B.onlyS {a t t' : State} {rs : List Reg} (h : B S vf Pre Pub a t) (o : Only rs t t')
    (hrs : ∀ r ∈ rs, r ∉ fixed := by decide) : B S vf Pre Pub a t' :=
  let ⟨s, P, p, b⟩ := h; ⟨s, P, p, b.only (X.fits P) o hrs⟩

end

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
variable (X : Ok S vf Pre Pub)
include X

/-- Pins of states with `B` and more. -/
theorem pins_of {α : Type} {Φ : α → State → Prop} {an : α → State} (h : ∀ a t, Φ a t → B S vf Pre Pub (an a) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ Reg.s0 :: fx := by decide) : Pins Φ rs := fun a t₁ t₂ h₁ h₂ => by
  obtain ⟨f₁, g₁, v₁⟩ := (h a t₁ h₁).agree X
  obtain ⟨f₂, g₂, v₂⟩ := (h a t₂ h₂).agree X
  refine ⟨f₁.trans f₂.symm, fun r hr => ?_⟩
  rcases List.mem_cons.mp (hrs r hr) with rfl | hr'
  · exact g₁.trans g₂.symm
  · exact (v₁ r hr').trans (v₂ r hr').symm

/-- `a0 := S + oSt`. -/
theorem st_wp {a t : State} (h : B S vf Pre Pub a t) :
    WP isa (.block [.addi .a0 .s0 oSt]) t fun t' => B S vf Pre Pub a t' ∧ t'.gpr .a0 = off (S a) oSt :=
  wp_addi (imm := oSt) fun t' o e => wp_nil ⟨h.only X o, by rw [e, (h.agree X).2.1]⟩

end

/-- A piece of code checked for both runs, then the rest from what each run
satisfies after it. -/
theorem two_seq {α : Type} {Φ Ψ : α → State → Prop} {R : State → State → Prop} {c₁ c₂ : Prog isa}
    (h₁ : RelCT isa (Two Φ) c₁ fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c₁ s (Ψ a))
    (h₂ : RelCT isa (Two Ψ) c₂ R) : RelCT isa (Two Φ) (.seq c₁ c₂) R :=
  RelCT.seq (two_post h₁ hw) h₂

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
  (X : Ok S vf Pre Pub) {H : Hash} (hH : HashOK H) (cH : HashCT hH) (hF : H.F ≤ 208)

include X cH in
/-- `init` on the state at `S + oSt`, in both runs. -/
theorem init_two {Φ : State → State → Prop}
    (h : ∀ a t, Φ a t → B S vf Pre Pub a t ∧ t.gpr .a0 = off (S a) oSt) :
    RelCT isa (Two Φ) H.callInit fun _ _ => True :=
  init_ct (S := S) (vf := vf) cH fun t₁ t₂ ⟨a, h₁, h₂⟩ => by
    obtain ⟨⟨s₁, P₁, p₁, b₁⟩, e₁⟩ := h a t₁ h₁
    obtain ⟨⟨s₂, P₂, p₂, b₂⟩, e₂⟩ := h a t₂ h₂
    exact ⟨s₁, s₂, X.fits P₁, b₁, by rw [e₁, (X.agree p₁).S], X.fits P₂, b₂, by rw [e₂, (X.agree p₂).S],
      e₁.trans e₂.symm, (b₁.agree (X.agree p₁)).1.trans (b₂.agree (X.agree p₂)).1.symm⟩

include X hH hF in
theorem init_wp {a t : State} (h : B S vf Pre Pub a t) (h0 : t.gpr .a0 = off (S a) oSt) :
    WP isa H.callInit t (B S vf Pre Pub a) := by
  obtain ⟨s, P, p, b⟩ := h
  exact WP.mono (init_ok (X.fits P) hH hF b (by rw [h0, (X.agree p).S])) fun t' ⟨b', _⟩ => ⟨s, P, p, b'⟩

end

end VG.Proof.RsaOaep.RISCV64
