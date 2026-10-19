module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTQ
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowQ
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowHeadCT
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2

/-! Constant time for conversion followed by five-bit exponentiation. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum

def Wide (p : XPub) : Prop := p.o + slot p.wx 8 + CrtWindowFive.tabBytes32 p.wx ≤ p.Z

def PwPreWide (sl sd slen : Nat) (p : BPub) (s : State) : Prop :=
  PwPre sl sd slen p s ∧ Wide p.x

def P1Wide (sd slen : Nat) (p : BPub) (s : State) : Prop :=
  CrtCTQ.P1 sd slen p s ∧ Wide p.x

def PowCT (W : Window) (M : Mont) (S : Selector) (sl sd slen : Nat) : Prop :=
  RelCT isa (Two (PwPreWide sl sd slen))
    (seqs (powSteps W.code S.code M.mm sl sd slen)) (fun _ _ => True)

theorem blk_p1_wide {sl sd slen : Nat} {p : BPub} {s : State} (h : PwPreWide sl sd slen p s) :
    WP isa (.block [ldh .x0 sl]) s (P1Wide sd slen p) :=
  WP.mono (CrtCTQ.blk_p1 h.1) fun _ ht => ⟨ht,h.2⟩

theorem redc_ePre_wide (M : Mont) {sd slen : Nat} {p : BPub} {s : State}
    (h : P1Wide sd slen p s) :
    WP isa (seqs (redc M.mm Public.aY)) s (EPreWide sd slen p) :=
  WP.mono (CrtCTQ.redc_ePre M h.1) fun _ ht => ⟨ht,h.2⟩

theorem pow_ct (W : Window) (M : Mont) (S : Selector) {sl sd slen : Nat}
    (hR : RedcCT M Public.aY)
    (hE : RelCT isa (Two (EPreWide sd slen))
      (VG.Impl.Rsa.AArch64.WindowFive.expLoop W.code M.mm S.code sd slen) (fun _ _ => True))
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x0 sl]) hc).isSome = true) :
    PowCT W M S sl sd slen := by
  unfold PowCT powSteps
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp) (by simp [redc]) (RelCT.seq
    (two_piece (Ψ := P1Wide sd slen) [.x0]
      (pins_x0B (fun p : BPub => p.x.B) fun _ _ ⟨⟨_,_,_,_,_,_,hg,_⟩,_⟩ => hg.x0)
      hT fun _ _ h => blk_p1_wide h) ?_)
  exact RelCT.seqs_append (by simp [redc]) (by simp) (RelCT.seq
    (two_post (Ψ := EPreWide sd slen)
      (two_map BPub.x (fun _ _ ⟨⟨mx,X,_,hc,_,hX,hwx2,hwx,hw28,hX1,_⟩,_⟩ =>
        ⟨mx,X,hc,hX,hwx2,hwx,by omega,hX1,by decide⟩) hR)
      fun _ _ h => redc_ePre_wide M h) hE)

end VG.Proof.Bignum.AArch64.WindowFive
