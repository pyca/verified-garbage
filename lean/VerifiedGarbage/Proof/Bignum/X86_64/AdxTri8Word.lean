import VerifiedGarbage.Impl.Bignum.X86_64.AdxTri8
import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddWord

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

theorem word_ok (s : State) {k : Nat} {hi prev col : Reg} {v : BitVec 64} {c o : Bool}
    (hm : readSrc s (.mem (at_ .rbp (8*k)))=some v) (hc : s.cf=some c) (ho : s.of=some o)
    (h1 : hi≠.rsi) (h2 : col≠hi) (h3 : col≠.rsi)
    (h4 : prev≠hi) (h5 : prev≠.rsi) (h6 : prev≠col) :
    WP isa (.block (AdxTri8.word k hi prev col)) s fun t => ∃ c' o' : Bool,
      t.cf=some c' ∧ t.of=some o' ∧
      (t.gpr col).toNat+2^64*((t.gpr hi).toNat+c'.toNat+o'.toNat)=
        (s.gpr col).toNat+(s.gpr .rdx).toNat*v.toNat+(s.gpr prev).toNat+c.toNat+o.toNat ∧
      Keeps [hi,.rsi,col] s t := by
  rw [show AdxTri8.word k hi prev col = [.mulx hi .rsi (.mem (at_ .rbp (8*k)))] ++
    AdxDualAdd.word col (.reg .rsi) (.reg prev) from rfl,WP.block_append_iff]
  refine WP.mono (mulx_ok s hm (fun _ h => nomatch h) h1) fun a ⟨ea,ca,oa,ka⟩ => ?_
  refine WP.mono (AdxDualAdd.word_ok a (a := .reg .rsi) (b := .reg prev) (vb := a.gpr prev) rfl
    (fun u ku => by simp only [readSrc]; rw [ku.gpr (by simp [h6])])
    (fun _ h => nomatch h) (fun _ h => nomatch h) (ca.trans hc) (oa.trans ho))
    fun t ⟨ct,ot,hct,hot,eq,kt⟩ => ?_
  have colA : a.gpr col=s.gpr col := ka.gpr (by simp [h2,h3])
  have prevA : a.gpr prev=s.gpr prev := ka.gpr (by simp [h4,h5])
  have hiT : t.gpr hi=a.gpr hi := kt.gpr (by simp [Ne.symm h2])
  rw [colA,prevA] at eq
  refine ⟨ct,ot,hct,hot,?_,(ka.trans kt).mono (by simp)⟩
  rw [hiT]
  omega

theorem close_ok (s : State) {hi col : Reg} {c o : Bool}
    (hc : s.cf=some c) (ho : s.of=some o) (hz : s.gpr col=0) (hne : hi≠col) :
    WP isa (.block (AdxTri8.close hi col)) s fun t => ∃ c' o' : Bool,
      t.cf=some c' ∧ t.of=some o' ∧
      (t.gpr col).toNat+2^64*(c'.toNat+o'.toNat)=
        (s.gpr col).toNat+(s.gpr hi).toNat+c.toNat+o.toNat ∧ Keeps [col] s t := by
  change WP isa (.block (AdxDualAdd.word col (.reg col) (.reg hi))) s _
  refine WP.mono (AdxDualAdd.word_ok s (a := .reg col) (b := .reg hi) (vb := s.gpr hi) rfl
    (fun t kt => by simp only [readSrc]; rw [kt.gpr (by simp [hne])])
    (fun _ h => nomatch h) (fun _ h => nomatch h) hc ho) fun t ⟨ct,ot,hct,hot,eq,kt⟩ => ?_
  rw [hz] at eq ⊢
  simp only [show (0 : BitVec 64).toNat=0 from rfl,Nat.add_zero,Nat.zero_add] at eq ⊢
  exact ⟨ct,ot,hct,hot,eq,kt⟩

end VG.Proof.Bignum.X86_64.AdxTri8
