module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure Resume (L : List Zq) (B : Nat→Byte) (buf : Nat) (aP : Addr) (s : State) : Prop where
  env : Rej8.Env 56 B (s.gpr .x19+BitVec.ofNat 64 buf) aP s
  constants : Rej8.Constants s
  len : L.length≤256
  coeffs : Rej8.Scalar.Coeffs s.mem aP L
  x3 : s.gpr .x3=coeffAddr aP L.length
  x4 : (s.gpr .x4).toNat=256-L.length

theorem continue_relCT {s u : State} {buf : Nat} (hb : buf<4096)
    {B : Nat→Byte} {L : List Zq} {aP : Addr} (ps : Resume L B buf aP s) (pu : Resume L B buf aP u)
    (hsp : s.sp=u.sp) (h19 : s.gpr .x19=u.gpr .x19) (h16 : s.gpr .x16=u.gpr .x16) :
    RelCT isa (fun a b=>a=s ∧ b=u)
      (.seq (.block (continueEntry buf)) Impl.MlKem.AArch64.Rej8.rejLoop)
      (fun a b=>a.sp=b.sp ∧ a.gpr .x19=b.gpr .x19) := by
  have start : RelCT isa (fun a b=>a=s ∧ b=u) (.block (continueEntry buf))
      (fun a b=>Rej8.Entry L 56 B (s.gpr .x19+BitVec.ofNat 64 buf) aP a ∧
        Rej8.Entry L 56 B (s.gpr .x19+BitVec.ofNat 64 buf) aP b ∧ a.sp=b.sp ∧ a.gpr .x16=b.gpr .x16) := by
    intro a b tr ur a' b' h ea eb
    rcases h with ⟨ha,hb'⟩
    subst a; subst b
    obtain ⟨ka,ha⟩ := exec_post (continueEntry_ok s hb ps.env ps.constants ps.len ps.coeffs ps.x3 ps.x4) ea
    obtain ⟨kb,hb'⟩ := exec_post (continueEntry_ok u hb pu.env pu.constants pu.len pu.coeffs pu.x3 pu.x4) eb
    refine ⟨continueEntry_ct buf s u tr ur a' b' trivial trivial (agree_of hsp (by simp)) ea eb,
      ha,?_,ka.sp.trans (hsp.trans kb.sp.symm),?_⟩
    · simpa only [h19] using hb'
    · rw [ka.get .x16,kb.get .x16,h16]
  have trace := RelCT.seq start (segment_entry_relCT L 56 B _ aP (by decide) (by decide))
  intro a b tr ur a' b' h ea eb
  rcases h with ⟨ha,hb'⟩
  subst a; subst b
  obtain ⟨ht,hsp'⟩ := trace s u tr ur a' b' ⟨rfl,rfl⟩ ea eb
  have hs := exec_post (continue_ok s hb ps.env ps.constants ps.len ps.coeffs ps.x3 ps.x4) ea
  have hu := exec_post (continue_ok u hb pu.env pu.constants pu.len pu.coeffs pu.x3 pu.x4) eb
  exact ⟨ht,hsp',by rw [hs.1.get .x19,hu.1.get .x19,h19]⟩

end VG.Proof.MlKem.AArch64.Paired
