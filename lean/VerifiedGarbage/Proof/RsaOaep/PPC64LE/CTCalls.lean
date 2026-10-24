module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Calls
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT

/-!
# RSAES-OAEP encryption on PPC64LE: the calls of the streaming hash functions, twice

Untrusted: everything here is checked by Lean. `HashCT`: a hash function's
streaming functions are constant time for the contracts the proofs call
them by (`initK`, `updK`, `finK`, whose public data are their pointers and
lengths); `init_ct`, `upd_ct` and `fin_ct`: two runs of a call from states
with `Base` and the same arguments leak alike (`RelCT.callEx`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK initK updK finK)

/-- The constant time of a hash function's streaming functions. -/
structure HashCT {H : Hash} (hH : HashOK H) : Prop where
  init : ConstantTime isa (initK H.S hH.SH.Repr).pre (initK H.S hH.SH.Repr).pub H.initC
  upd : ConstantTime isa (updK H.S H.W hH.SH.Repr).pre (updK H.S H.W hH.SH.Repr).pub H.updC
  fin : ConstantTime isa (finK H.S H.W H.FD hH.SH.Repr hH.fh).pre (finK H.S H.W H.FD hH.SH.Repr hH.fh).pub
    H.finC

section
variable {D : Nat} {H : Hash} {hH : HashOK H} (cH : HashCT hH)
include cH

/-- `init` on the state at `S + oSt`, in both runs. -/
theorem init_ct {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → ∃ s₁ s₂, PreO D s₁ ∧ Base s₁ t₁ ∧ t₁.gpr .r3 = off (S s₁) oSt ∧
      PreO D s₂ ∧ Base s₂ t₂ ∧ t₂.gpr .r3 = off (S s₂) oSt ∧ t₁.gpr .r3 = t₂.gpr .r3 ∧ t₁.sp = t₂.sp) :
    RelCT isa P H.callInit fun _ _ => True := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _, _⟩ := offs
  refine RelCT.callEx hH.init cH.init fun t₁ t₂ hp => ?_
  obtain ⟨s₁, s₂, P₁, b₁, h₁, P₂, b₂, h₂, e3, esp⟩ := hP t₁ t₂ hp
  have pre : ∀ {s t : State}, PreO D s → Base s t → t.gpr .r3 = off (S s) oSt →
      (initK H.S hH.SH.Repr).pre (t.callEntry.withRegions [] [⟨t.gpr .r3, H.S⟩]) := fun {s t} P b h => by
    have c3 : t.callEntry.gpr .r3 = t.gpr .r3 := State.callEntry_gpr _ (by decide)
    simp only [initK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp, c3, h]
    exact ⟨trivial, trivial, sp48 P b, by rw [b.sp]; exact cR_dis P (by omega)⟩
  have cov : ∀ {s t : State}, PreO D s → Base s t → t.gpr .r3 = off (S s) oSt →
      Covers [⟨t.gpr .r3, H.S⟩] t.wr := fun {s t} P b h => by rw [h, b.wr]; exact sc_cov P (by omega)
  refine ⟨[], _, [], _, pre P₁ b₁ h₁, pre P₂ b₂ h₂, ?_, by rw [List.nil_append]; exact Covers.right (cov P₁ b₁ h₁),
    cov P₁ b₁ h₁, by rw [List.nil_append]; exact Covers.right (cov P₂ b₂ h₂), cov P₂ b₂ h₂⟩
  simp only [initK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp]
  exact ⟨by rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), e3], esp⟩

/-- What a call of `update` needs, in a run from the entry state `s`. -/
structure UpdArgs (D : Nat) (H : Hash) (s t : State) (dat : Addr) (len : Nat) : Prop where
  P : PreO D s
  b : Base s t
  h3 : t.gpr .r3 = off (S s) oSt
  h5 : t.gpr .r5 = dat
  h6 : (t.gpr .r6).toNat = len
  h7 : t.gpr .r7 = off (S s) oW
  hdc : Covers [⟨dat, len⟩] (t.rd ++ t.wr)
  hd₁ : Region.Disjoint ⟨dat, len⟩ ⟨off (S s) oSt, H.S⟩
  hd₂ : Region.Disjoint ⟨dat, len⟩ ⟨off (S s) oW, H.W⟩
  hd₃ : (cR s).Disjoint ⟨dat, len⟩

/-- `update` on the state at `S + oSt`, in both runs, with the same
arguments. -/
theorem upd_ct {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → ∃ s₁ s₂ d₁ d₂ l₁ l₂, UpdArgs D H s₁ t₁ d₁ l₁ ∧ UpdArgs D H s₂ t₂ d₂ l₂ ∧
      (∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7], t₁.gpr r = t₂.gpr r) ∧ t₁.sp = t₂.sp) :
    RelCT isa P H.callUpd fun _ _ => True := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _, _⟩ := offs
  refine RelCT.callEx hH.upd cH.upd fun t₁ t₂ hp => ?_
  obtain ⟨s₁, s₂, d₁, d₂, l₁, l₂, A₁, A₂, eg, esp⟩ := hP t₁ t₂ hp
  have pre : ∀ {s t : State} {d : Addr} {l : Nat}, UpdArgs D H s t d l →
      (updK H.S H.W hH.SH.Repr).pre (t.callEntry.withRegions [⟨d, l⟩]
        [⟨off (S s) oSt, H.S⟩, ⟨off (S s) oW, H.W⟩]) := fun {s t d l} A => by
    have c3 : t.callEntry.gpr .r3 = t.gpr .r3 := State.callEntry_gpr _ (by decide)
    have c5 : t.callEntry.gpr .r5 = t.gpr .r5 := State.callEntry_gpr _ (by decide)
    have c6 : t.callEntry.gpr .r6 = t.gpr .r6 := State.callEntry_gpr _ (by decide)
    have c7 : t.callEntry.gpr .r7 = t.gpr .r7 := State.callEntry_gpr _ (by decide)
    simp only [updK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp, c3, c5, c6, c7, A.h3, A.h5, A.h6, A.h7]
    exact ⟨trivial, trivial, sdis (.inl (by omega)) (by omega) (by omega), A.hd₁, A.hd₂, sp48 A.P A.b,
      by rw [A.b.sp]; exact cR_dis A.P (by omega), by rw [A.b.sp]; exact A.hd₃,
      by rw [A.b.sp]; exact cR_dis A.P (by omega)⟩
  have cov : ∀ {s t : State} {d : Addr} {l : Nat}, UpdArgs D H s t d l →
      Covers [⟨off (S s) oSt, H.S⟩, ⟨off (S s) oW, H.W⟩] t.wr := fun {s t d l} A => by
    rw [A.b.wr]; exact Covers.pair (sc_cov A.P (by omega)) (sc_cov A.P (by omega))
  refine ⟨_, _, _, _, pre A₁, pre A₂, ?_, Covers.append_left A₁.hdc (Covers.right (cov A₁)), cov A₁,
    Covers.append_left A₂.hdc (Covers.right (cov A₂)), cov A₂⟩
  simp only [updK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp]
  simp only [State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r6 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r7 ∉ linkRegs by decide)]
  exact ⟨eg _ (by decide), eg _ (by decide), eg _ (by decide), eg _ (by decide), eg _ (by decide), esp⟩

/-- What a call of `finalize` needs, in a run from the entry state `s`. -/
structure FinArgs (D : Nat) (s t : State) : Prop where
  P : PreO D s
  b : Base s t
  h3 : t.gpr .r3 = off (S s) oSt
  h5 : t.gpr .r5 = off (S s) oDig
  h6 : t.gpr .r6 = off (S s) oW

/-- `finalize` on the state at `S + oSt`, in both runs, with the same
arguments. -/
theorem fin_ct {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → ∃ s₁ s₂, FinArgs D s₁ t₁ ∧ FinArgs D s₂ t₂ ∧
      (∀ r ∈ [Reg.r3, .r4, .r5, .r6], t₁.gpr r = t₂.gpr r) ∧ t₁.sp = t₂.sp) :
    RelCT isa P H.callFin fun _ _ => True := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _, _⟩ := offs
  refine RelCT.callEx hH.fin cH.fin fun t₁ t₂ hp => ?_
  obtain ⟨s₁, s₂, A₁, A₂, eg, esp⟩ := hP t₁ t₂ hp
  have pre : ∀ {s t : State}, FinArgs D s t →
      (finK H.S H.W H.FD hH.SH.Repr hH.fh).pre (t.callEntry.withRegions []
        [⟨off (S s) oSt, H.S⟩, ⟨off (S s) oDig, H.FD⟩, ⟨off (S s) oW, H.W⟩]) := fun {s t} A => by
    have c3 : t.callEntry.gpr .r3 = t.gpr .r3 := State.callEntry_gpr _ (by decide)
    have c5 : t.callEntry.gpr .r5 = t.gpr .r5 := State.callEntry_gpr _ (by decide)
    have c6 : t.callEntry.gpr .r6 = t.gpr .r6 := State.callEntry_gpr _ (by decide)
    simp only [finK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp, c3, c5, c6, A.h3, A.h5, A.h6]
    exact ⟨trivial, trivial, sdis (.inl (by omega)) (by omega) (by omega),
      sdis (.inl (by omega)) (by omega) (by omega), sdis (.inl (by omega)) (by omega) (by omega), sp48 A.P A.b,
      by rw [A.b.sp]; exact cR_dis A.P (by omega), by rw [A.b.sp]; exact cR_dis A.P (by omega),
      by rw [A.b.sp]; exact cR_dis A.P (by omega)⟩
  have cov : ∀ {s t : State}, FinArgs D s t →
      Covers [⟨off (S s) oSt, H.S⟩, ⟨off (S s) oDig, H.FD⟩, ⟨off (S s) oW, H.W⟩] t.wr := fun {s t} A => by
    rw [A.b.wr]; exact (sc_cov A.P (by omega)).cons (Covers.pair (sc_cov A.P (by omega)) (sc_cov A.P (by omega)))
  refine ⟨[], _, [], _, pre A₁, pre A₂, ?_, by rw [List.nil_append]; exact Covers.right (cov A₁), cov A₁,
    by rw [List.nil_append]; exact Covers.right (cov A₂), cov A₂⟩
  simp only [finK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp]
  simp only [State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r6 ∉ linkRegs by decide)]
  exact ⟨eg _ (by decide), eg _ (by decide), eg _ (by decide), eg _ (by decide), esp⟩

end

end VG.Proof.RsaOaep.PPC64LE
