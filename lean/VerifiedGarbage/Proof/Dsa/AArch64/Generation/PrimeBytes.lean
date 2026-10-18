module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PrimeBytes
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ProbablePrime
import VerifiedGarbage.Proof.Framework.Omega

/-! # Connect saved candidate bytes to the shared primality operation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Rsa VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64 VG.Proof.MillerRabin.AArch64

/-- The primality call's arguments before its candidate array is loaded. -/
structure PrimeArguments (P : PrimeParams) (used : Nat) (s : State) : Prop where
  ws : Ws s P.B P.Z P.w
  ptr : word s.mem P.B (8 * kOut) = P.p
  len : word s.mem P.B (8 * kUsedP) = BitVec.ofNat 64 P.len
  draw : word s.mem P.B (8 * kLen) = BitVec.ofNat 64 P.drawBytes
  rand : word s.mem P.B (8 * kRand) = P.rp
  randLen : word s.mem P.B (8 * kRandLen) = BitVec.ofNat 64 P.rand.length
  used : word s.mem P.B (8 * kUsed) = BitVec.ofNat 64 used
  checks : word s.mem P.B (8 * kChecks) = BitVec.ofNat 64 P.checks
  source : Src s P.B P.Z P.rp P.rand
  writable : ∀ i < P.len, InRegions s.wr (off P.p i) 1

theorem loadPrimeBytes_ok {P : PrimeParams} {used : Nat} {s : State}
    (h : PrimeArguments P used s) {cp : Addr} {bs : List Byte}
    (hptr : word s.mem P.B 160 = cp) (hlen : bs.length = P.len)
    (hvalue : Spec.Rsa.os2ip bs = P.N) (hsrc : Src s P.B P.Z cp bs) :
    WP isa (seqs (Impl.Rsa.AArch64.Keys.loadA 0 20 kUsedP)) s fun t =>
      PrimeInput P used t ∧ Frm P.B [ar P.w 0] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (loadCandidateArray_ok h.ws (by decide : 0 < 16)
    (by decide : 20 < 32) (by decide : kUsedP < 32) hptr
    (by rw [hlen]; exact h.len) hsrc (by rw [hlen]; have := P.len2; omega)
    (by rw [hlen]; exact P.lenWords)) fun t ⟨ht, hn, hf, hk⟩ => ?_
  have hh : ∀ i < 32, word t.mem P.B (8 * i) = word s.mem P.B (8 * i) := by
    intro i hi
    exact hf.word_eq (by
      simp only [List.mem_singleton]; rintro r rfl
      left; simp only [slot, hdrBytes]; omega) (by
      have := h.ws.scr.nowrap; have := h.ws.h256; omega)
  refine ⟨⟨ht, hn.trans hvalue, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hf, hk⟩
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
    simp only [List.mem_singleton]
    rintro r rfl
    right
    change slot P.w 0 + 8 * (P.w + 2) ≤ ofs P.B a
    have hr := h.ws.sl (by decide : 0 < 16)
    omega
  · intro i hi; rw [hk.wr]; exact h.writable i hi

/-- Trial division and Miller–Rabin operate on the saved candidate bytes;
all candidate-loading writes are included in the returned memory frame. -/
theorem primeBytes_ok (M : Mont) (K : Kernel) {P : PrimeParams} {used : Nat} {s : State}
    (h : PrimeArguments P used s) {cp : Addr} {bs : List Byte}
    (hptr : word s.mem P.B 160 = cp) (hlen : bs.length = P.len)
    (hvalue : Spec.Rsa.os2ip bs = P.N) (hsrc : Src s P.B P.Z cp bs)
    (hu : used ≤ P.rand.length) (hw : P.w ≤ 48) (hz : slot P.w aTab + 2048 ≤ P.Z)
    (hn : 8161 < P.N) (hpolicy : 1024 < Spec.Dsa.bitLength P.N ↔ 16 < P.w)
    (hchecks : P.checks = Spec.Dsa.primeChecks (Spec.Dsa.bitLength P.N)) :
    WP isa (Impl.Dsa.AArch64.Generation.primeBytes M.mm K.run P.len P.drawBytes) s fun t =>
      let res := Spec.Dsa.probablePrime P.N (P.rand.drop used)
      ∃ used', PrimeInput P used' t ∧ used' ≤ P.rand.length ∧
        (res = none → word t.mem P.B (8 * kStat) = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) →
          word t.mem P.B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = P.rand.length - rest.length) ∧
        WorkFrame P.B ((slot P.w 0, 8 * (P.w + 2)) :: primeRanges P.w) (primeExtras P) s.mem t.mem ∧
        Keep mmRegs s t := by
  unfold Impl.Dsa.AArch64.Generation.primeBytes
  refine WP.seq (WP.mono (loadPrimeBytes_ok h hptr hlen hvalue hsrc) fun u ⟨hi, hf, hk⟩ => ?_)
  refine WP.mono (probablePrime_ok M K hi hu hw hz hn hpolicy hchecks)
    fun t ⟨used', ht, hut, he, hr, ft, kt⟩ => ?_
  have fl : Frm P.B [(slot P.w 0, 8 * (P.w + 2))] s.mem u.mem := hf
  exact ⟨used', ht, hut, he, hr,
    (fl.work.mono (by simp)).trans (ft.mono (fun _ hr => List.mem_cons_of_mem _ hr)), (hk.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation
