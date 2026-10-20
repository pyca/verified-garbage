module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeBytes
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Load
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ProbablePrime
import VerifiedGarbage.Proof.Framework.Omega

/-! # Connect saved candidate bytes to the shared primality operation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Proof.MillerRabin.X86_64

/-- The primality call's arguments before its candidate array is loaded. -/
structure PrimeArguments (P : PrimeParams) (mi : BitVec 64) (used : Nat) (s : State) : Prop where
  good : Good s P.B P.Z P.w mi
  ptr : word s.mem P.B (8 * kOut) = P.p
  len : word s.mem P.B (8 * kUsedP) = BitVec.ofNat 64 P.len
  draw : word s.mem P.B (8 * kLen) = BitVec.ofNat 64 P.drawBytes
  rand : word s.mem P.B (8 * kRand) = P.rp
  randLen : word s.mem P.B (8 * kRandLen) = BitVec.ofNat 64 P.rand.length
  used : word s.mem P.B (8 * kUsed) = BitVec.ofNat 64 used
  checks : word s.mem P.B (8 * kChecks) = BitVec.ofNat 64 P.checks
  source : Src s P.B P.Z P.rp P.rand
  writable : ∀ i < P.len, InRegions s.wr (off P.p i) 1
  stack : s.gpr .rsp = P.sp

theorem loadPrimeBytes_ok {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeArguments P mi used s) {cp : Addr} {bs : List Byte}
    (hptr : word s.mem P.B 160 = cp) (hlen : bs.length = P.len)
    (hvalue : Spec.Rsa.os2ip bs = P.N) (hsrc : Src s P.B P.Z cp bs) :
    WP isa (Impl.Dsa.X86_64.Generation.loadPadded 0 20 18) s fun t =>
      PrimeInput P mi used t ∧ Outside P.B (slot P.w 0) (8 * (P.w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hZ : slot P.w 8 ≤ P.Z := Nat.le_trans (by unfold slot; omega) P.room
  refine WP.mono (loadPadded_ok h.good hZ (by have := P.dims.w4; omega)
    (by have := P.dims.w128; omega) (by decide : 0 < 8)
    (by decide : 20 < 32) (by decide : 18 < 32) hptr
    (by rw [hlen]; exact h.len) hsrc (by rw [hlen]; have := P.len2; omega)
    (by rw [hlen]; have := P.lenDraw; have := P.drawMax; omega)
    (by rw [hlen]; exact P.lenWords)) fun t ⟨ht, hn, hf, hk⟩ => ?_
  have hh : ∀ i < 32, word t.mem P.B (8 * i) = word s.mem P.B (8 * i) := by
    intro i hi
    exact hf.word (Or.inl (by simp only [slot, hdrBytes]; omega)) (by omega)
  refine ⟨⟨ht, hn.trans hvalue, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hf, hk⟩
  · exact (hh kOut (by decide)).trans h.ptr
  · exact (hh kUsedP (by decide)).trans h.len
  · exact (hh kLen (by decide)).trans h.draw
  · exact (hh kRand (by decide)).trans h.rand
  · exact (hh kRandLen (by decide)).trans h.randLen
  · exact (hh kUsed (by decide)).trans h.used
  · exact (hh kChecks (by decide)).trans h.checks
  · apply h.source.congrK _ hk
    intro a ha
    apply hf a
    right
    have hr : slot P.w 0 + 8 * (P.w + 2) ≤ P.Z := Nat.le_trans (slot_le (by decide : 0 < 8)) hZ
    omega
  · intro i hi; rw [hk.2.2]; exact h.writable i hi
  · exact (hk.gpr (by decide)).trans h.stack

/-- Trial division and Miller–Rabin operate on the saved candidate bytes;
all candidate-loading writes are included in the returned memory frame. -/
theorem primeBytes_ok (M : Mont) (K : Kernel) {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeArguments P mi used s) {cp : Addr} {bs : List Byte}
    (hptr : word s.mem P.B 160 = cp) (hlen : bs.length = P.len)
    (hvalue : Spec.Rsa.os2ip bs = P.N) (hsrc : Src s P.B P.Z cp bs)
    (hu : used ≤ P.rand.length) (hw : P.w ≤ 48) (hz : slot P.w aTab + 2048 ≤ P.Z)
    (hn : 8161 < P.N) (hpolicy : 1024 < Spec.Dsa.bitLength P.N ↔ 16 < P.w)
    (hchecks : P.checks = Spec.Dsa.primeChecks (Spec.Dsa.bitLength P.N)) :
    WP isa (Impl.Dsa.X86_64.Generation.primeBytes M.mm K.run P.len P.drawBytes) s fun t =>
      let res := Spec.Dsa.probablePrime P.N (P.rand.drop used)
      ∃ mi' used', PrimeInput P mi' used' t ∧ used' ≤ P.rand.length ∧
        (res = none → word t.mem P.B (8 * kStat) = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) →
          word t.mem P.B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = P.rand.length - rest.length) ∧
        WorkFrame P.B ((slot P.w 0, 8 * (P.w + 2)) :: primeRanges P.w) (primeExtras P) s.mem t.mem ∧
        Keep mmRegs s t := by
  unfold Impl.Dsa.X86_64.Generation.primeBytes
  refine WP.seq (WP.mono (loadPrimeBytes_ok h hptr hlen hvalue hsrc) fun u ⟨hi, hf, hk⟩ => ?_)
  refine WP.mono (probablePrime_ok M K hi hu hw hz hn hpolicy hchecks)
    fun t ⟨mi', used', ht, hut, he, hr, ft, kt⟩ => ?_
  have fl : Frm P.B [(slot P.w 0, 8 * (P.w + 2))] s.mem u.mem :=
    Frm.of_outside hf (by simp)
  exact ⟨mi', used', ht, hut, he, hr,
    (fl.work.mono (by simp)).trans (ft.mono (fun _ hr => List.mem_cons_of_mem _ hr)), (hk.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
