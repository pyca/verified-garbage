import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8RowCore
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderSave

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

theorem headBases_ok {s : State} {B : Addr} {Z w I : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    (hI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 I) :
    WP isa (.block AdxTri8.headBases) s fun t =>
      t.gpr .rsi=off B (slot w aAcc+16*I) ∧ t.mem=s.mem ∧ Keep [.rsi,.rcx] s t := by
  have ld : ∀ k<32, InRegions (s.rd++s.wr) (off B (8*k)) 8 := fun k hk =>
    hs.ld (by have := hdr_lt_slot w 8 hk; omega)
  have sh : BitVec.ofNat 64 I <<< (4 : Nat)=BitVec.ofNat 64 (16*I) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 I*BitVec.ofNat 64 16=BitVec.ofNat 64 (16*I)
    rw [← BitVec.ofNat_mul,Nat.mul_comm]
  have add : off B (slot w aAcc)+BitVec.ofNat 64 (16*I)=off B (slot w aAcc+16*I) := off_off ..
  refine WP.mono (WP.keep [.rsi,.rcx] (Q := fun t => t.gpr .rsi=off B (slot w aAcc+16*I) ∧ t.mem=s.mem) ?_ rfl)
    fun t ⟨⟨p,m⟩,k⟩ => ⟨p,m,k⟩
  unfold AdxTri8.headBases
  xrun [State.ea,hdr,hd,hdrOff,ld (sArr aAcc) (by decide),ld (sFn 12) (by decide),
    hh.harr aAcc (by decide),hI,sh,add]

theorem storeHead_ok {s : State} {B : Addr} {Z w I i : Nat} {mi : BitVec 64} {lo hi : Reg}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    (hI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 I)
    (he : slot w aAcc+16*I+(16+8*(2*i+2))+8≤Z)
    (hl : lo≠.rsi ∧ lo≠.rcx) (hh' : hi≠.rsi ∧ hi≠.rcx) :
    let e := slot w aAcc+16*I+(16+8*(2*i+1))
    WP isa (AdxTri8.storeHead i lo hi) s fun t =>
      wv t.mem B e 2=(s.gpr lo).toNat+2^64*(s.gpr hi).toNat ∧
      Outside B e 16 s.mem t.mem ∧ Keep [.rsi,.rcx] s t := by
  dsimp only
  have nowrap := hs.nowrap
  unfold AdxTri8.storeHead
  refine WP.seq (WP.mono (headBases_ok hs hd hh hZ hI) fun a ⟨pa,ma,ka⟩ => ?_)
  refine WP.seq (WP.mono (AdxRotate8.storeAt_ok (p := .rsi) (r := lo) (hs.congr ka.2.2) pa
    (by omega : slot w aAcc+16*I+(16+8*(2*i+1))+8≤Z)) fun b ⟨vb,ob,kb⟩ => ?_)
  refine WP.mono (AdxRotate8.storeAt_ok (p := .rsi) (r := hi) (hs.congr (ka.trans kb).2.2)
    ((kb.gpr (by simp)).trans pa) he) fun t ⟨vt,ot,kt⟩ => ?_
  have low : word t.mem B (slot w aAcc+16*I+(16+8*(2*i+1)))=s.gpr lo := by
    rw [ot.word (by omega) (by omega),vb,ka.gpr (by simp [hl.1,hl.2])]
  have high : word t.mem B (slot w aAcc+16*I+(16+8*(2*i+2)))=s.gpr hi :=
    vt.trans ((kb.gpr (by simp)).trans (ka.gpr (by simp [hh'.1,hh'.2])))
  rw [ma] at ob
  refine ⟨?_,(ob.mono (n' := 16) (by omega) (by omega)).trans (ot.mono (by omega) (by omega)),((ka.trans kb).trans kt).mono (by simp)⟩
  rw [wv,wv,wv]
  simp only [Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.one_mul,Nat.zero_add,Nat.add_zero]
  rw [low,show slot w aAcc+16*I+(16+8*(2*i+1))+8=slot w aAcc+16*I+(16+8*(2*i+2)) by omega,high]

end VG.Proof.Bignum.X86_64.AdxTri8
