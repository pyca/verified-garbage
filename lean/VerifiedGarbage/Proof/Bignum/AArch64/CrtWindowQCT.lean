module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPowCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPow
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow

/-! Constant time for the q phase with the wider window. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum

def QPreWide (p : PhasePub) (s : State) : Prop := QPre p s ∧ Wide (CrtCTQ.sp p).x

def Q1Wide (p : PhasePub) (s : State) : Prop := CrtCTQ.Q1 p s ∧ Wide (CrtCTQ.sp p).x

def QPhaseCT (W : Window) (M : Mont) (S : Selector) : Prop :=
  RelCT isa (Two QPreWide)
    (seqs (VG.Impl.Rsa.AArch64.WindowFive.qPhase W.code M.mm S.code)) (fun _ _ => True)

theorem unit_q1_wide (M : Mont) {p : PhasePub} {s : State} (h : QPreWide p s) :
    WP isa (seqs (unitSteps M.mm sWsQ)) s (Q1Wide p) :=
  WP.mono (CrtCTQ.unit_q1 M h.1) fun _ ht => ⟨ht,h.2⟩

theorem mm_pwPre_wide (M : Mont) {p : PhasePub} {s : State} (h : Q1Wide p s) :
    WP isa (M.mm Public.aY Public.aXm Public.aY) s (PwPreWide sWsQ sDq sQlen (CrtCTQ.sp p)) :=
  WP.mono (CrtCTQ.mm_pwPre M h.1) fun _ ht => ⟨ht,h.2⟩

theorem pow_q3_wide (W : Window) (M : Mont) (S : Selector) {p : PhasePub} {s : State}
    (h : PwPreWide sWsQ sDq sQlen (CrtCTQ.sp p) s) :
    WP isa (seqs (powSteps W.code S.code M.mm sWsQ sDq sQlen)) s (CrtCTQ.Q3 p) := by
  obtain ⟨h,hwide⟩ := h
  obtain ⟨_,mx,_,X,_,eb,hg,hw28,hlo,_,hwx2,hwx,hsl,hslv,hws,hX,hX1,hXodd,hnY,hyl,hyc,hsd,
    hsln,hep,hel,_,hL1,hL2,he⟩ := h
  exact WP.mono (powPhase_ok W M S hg hw28 hlo hwide hwx2 hwx hsl hslv hws hX hX1 hXodd hnY hyl hyc
    hsd hsln hep hel hL1 hL2 he) fun _ ⟨hc,hX',_⟩ =>
      ⟨mx,X,hc,hX',hX1,hwx2,(by omega : (CrtCTQ.sp p).x.wx < 2 ^ 28)⟩

theorem qPhase_ct (W : Window) (M : Mont) (S : Selector) (hU : UnitCT M sWsQ)
    (hP : PowCT W M S sWsQ sDq sQlen) : QPhaseCT W M S := by
  unfold QPhaseCT
  rw [qPhase_eq]
  refine RelCT.seqs_append (by simp [unitSteps,gPow]) (by simp) (RelCT.seq
    (two_post (Ψ := Q1Wide) (two_map CrtCTQ.up (fun _ _ h => CrtCTQ.uPre h.1) hU)
      fun _ _ h => unit_q1_wide M h) ?_)
  refine RelCT.seqs_append (by simp) (by simp [powSteps]) (RelCT.seq
    (two_post (Ψ := fun p => PwPreWide sWsQ sDq sQlen (CrtCTQ.sp p))
      (two_map (fun p : PhasePub => (⟨p.B,p.Z,p.w⟩ : Ws))
        (fun _ _ ⟨⟨_,_,_,hg,_,_,hlo,hhi,_⟩,_⟩ => ⟨_,hg,by dsimp only; omega⟩)
        (M.ct (by unfold MmUse; decide))) fun _ _ h => mm_pwPre_wide M h) ?_)
  exact RelCT.seqs_append (by simp [powSteps]) (by simp) (RelCT.seq
    (two_post (Ψ := CrtCTQ.Q3) (two_map CrtCTQ.sp (fun _ _ h => h) hP)
      fun _ _ h => pow_q3_wide W M S h) (CrtCTQ.mmLeave_ct M))

end VG.Proof.Bignum.AArch64.WindowFive
