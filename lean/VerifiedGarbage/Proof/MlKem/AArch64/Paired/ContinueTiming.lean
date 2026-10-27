module
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Continue

import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Trace

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure ResumeW (w16 : Bool) (L : List Zq) (B : Nat→Byte) (aP : Addr) (s : State) : Prop where
  env : Rej8.EnvW w16 56 B (s.gpr .x20) aP s
  constants : Rej8.Constants s
  len : L.length≤256
  coeffs : Rej8.Scalar.CoeffsW w16 s.mem aP L
  x3 : s.gpr .x3=cAddr w16 aP L.length
  x4 : (s.gpr .x4).toNat=256-L.length

abbrev Resume := ResumeW false

theorem continue_relCT {w16 : Bool} {s u : State}
    {B : Nat→Byte} {L : List Zq} {aP : Addr} (ps : ResumeW w16 L B aP s) (pu : ResumeW w16 L B aP u)
    (hsp : s.sp=u.sp) (h20 : s.gpr .x20=u.gpr .x20) (h1 : s.gpr .x1=u.gpr .x1)
    (h16 : s.gpr .x16=u.gpr .x16) :
    RelCT isa (fun a b=>a=s ∧ b=u)
      (.seq (.block (continueEntry)) (Impl.MlKem.AArch64.Rej8.rejLoop w16))
      (fun a b=>a.sp=b.sp ∧ a.gpr .x1=b.gpr .x1) := by
  have start : RelCT isa (fun a b=>a=s ∧ b=u) (.block (continueEntry))
      (fun a b=>Rej8.EntryW w16 L 56 B (s.gpr .x20) aP a ∧
        Rej8.EntryW w16 L 56 B (s.gpr .x20) aP b ∧ a.sp=b.sp ∧ a.gpr .x16=b.gpr .x16) := by
    intro a b tr ur a' b' h ea eb
    rcases h with ⟨ha,hb'⟩
    subst a; subst b
    obtain ⟨ka,ha⟩ := exec_post (continueEntry_ok s ps.env ps.constants ps.len ps.coeffs ps.x3 ps.x4) ea
    obtain ⟨kb,hb'⟩ := exec_post (continueEntry_ok u pu.env pu.constants pu.len pu.coeffs pu.x3 pu.x4) eb
    refine ⟨continueEntry_ct s u tr ur a' b' trivial trivial (agree_of hsp (by simp)) ea eb,
      ha,?_,ka.sp.trans (hsp.trans kb.sp.symm),?_⟩
    · simpa only [h20] using hb'
    · rw [ka.get .x16,kb.get .x16,h16]
  have trace := RelCT.seq start (segment_entry_relCT L 56 B _ aP (by decide) (by decide))
  intro a b tr ur a' b' h ea eb
  rcases h with ⟨ha,hb'⟩
  subst a; subst b
  obtain ⟨ht,hsp'⟩ := trace s u tr ur a' b' ⟨rfl,rfl⟩ ea eb
  have hs := exec_post (continue_ok s ps.env ps.constants ps.len ps.coeffs ps.x3 ps.x4) ea
  have hu := exec_post (continue_ok u pu.env pu.constants pu.len pu.coeffs pu.x3 pu.x4) eb
  exact ⟨ht,hsp',by rw [hs.1.get .x1,hu.1.get .x1,h1]⟩

end VG.Proof.MlKem.AArch64.Paired
