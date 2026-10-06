import VerifiedGarbage.Impl.Bignum.X86_64.AdxHeader
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep

/-! Scalar copies preserve every byte outside their destination. -/
namespace VG.Proof.Bignum.X86_64.AdxHeader
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRotate8
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)
open VG.Proof.MlKem.X86_64 (Keep)

theorem copyWord_ok {s : State} {B : Addr} {Z e d o : Nat} {src : MemOp} {dst : Reg}
    (hs : Scr s B Z) (he : s.ea src = off B e) (hd : s.gpr dst = off B d)
    (hne : dst ≠ .rax) (hE : e+8 ≤ Z) (hD : d+o+8 ≤ Z) :
    WP isa (AdxHeader.copyWord src dst o) s fun t =>
      word t.mem B (d+o) = word s.mem B e ∧ Outside B (d+o) 8 s.mem t.mem ∧ Keep [.rax] s t := by
  unfold AdxHeader.copyWord
  refine WP.seq (WP.mono (movMem_ok s (dst := .rax) (readSrc_word hs he hE))
    fun a ⟨va,_,_,ka⟩ => ?_)
  refine WP.mono (storeAt_ok (hs.congr ka.2.2.2) ((ka.gpr (by simpa)).trans hd) hD)
    fun t ⟨vt,ot,kt⟩ => ?_
  rw [ka.2.1] at ot
  exact ⟨vt.trans va,ot,(ka.keep.trans kt).mono (by simp)⟩

theorem copyPair_ok {s : State} {B : Addr} {Z e d a o : Nat} {src dst : Reg}
    (hs : Scr s B Z) (he : s.gpr src = off B e) (hd : s.gpr dst = off B d)
    (hsne : src ≠ .rax) (hdne : dst ≠ .rax) (hE : e+a+16 ≤ Z) (hD : d+o+16 ≤ Z)
    (hsep : e+a+16 ≤ d+o ∨ d+o+16 ≤ e+a) :
    WP isa (AdxHeader.copyPair src dst a o) s fun t =>
      (∀ q < 2, word t.mem B (d+o+8*q) = word s.mem B (e+a+8*q)) ∧
      Outside B (d+o) 16 s.mem t.mem ∧ Keep [.rax] s t := by
  have nowrap := hs.nowrap
  unfold AdxHeader.copyPair
  refine WP.seq (WP.mono (copyWord_ok hs (ea_at he a) hd hdne (by omega) (by omega))
    fun u ⟨vu,ou,ku⟩ => ?_)
  refine WP.mono (copyWord_ok (hs.congr ku.2.2)
    (ea_at ((ku.gpr (by simpa)).trans he) (a+8)) ((ku.gpr (by simpa)).trans hd)
    hdne (by omega) (by omega)) fun t ⟨vt,ot,kt⟩ => ?_
  have hi : word u.mem B (e+(a+8)) = word s.mem B (e+(a+8)) := ou.word (by omega) (by omega)
  rw [hi] at vt
  refine ⟨?_,(ou.mono (o' := d+o) (n' := 16) (by omega) (by omega)).trans
    (ot.mono (o' := d+o) (n' := 16) (by omega) (by omega)),(ku.trans kt).mono (by simp)⟩
  intro q hq
  rcases (show q=0 ∨ q=1 by omega) with rfl | rfl
  · simp only [Nat.mul_zero,Nat.add_zero]
    rw [ot.word (by omega) (by omega)]; exact vu
  · simpa only [Nat.mul_one,Nat.add_assoc] using vt

end VG.Proof.Bignum.X86_64.AdxHeader
