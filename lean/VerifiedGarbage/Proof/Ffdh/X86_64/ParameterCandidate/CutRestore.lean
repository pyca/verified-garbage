module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessCut
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TapeHead
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.ExternalWords

/-! # FFDH parameter generation on x86-64: mask a draw and restore the modulus -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem cutRestore_ok {p : WitnessParams} {s₀ s : State} {rp : Addr} {bs : List Byte}
    (hready : ModulusReady s₀ p.I p.IZ p.w p.mi p.N) (hwr : s.wr = s₀.wr)
    (hwords : ∀ d, d + 8 ≤ p.IZ → word s.mem p.I d = word s₀.mem p.I d)
    (hs : Scr s p.O p.Z) (hl : word s.mem p.I (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = p.O)
    (hop : word s.mem p.O (8 * oOut) = p.op)
    (hlen : word s.mem p.O (8 * oWitnessLen) = BitVec.ofNat 64 p.len)
    (hdi : s.gpr .rdi = p.op) (hsi : s.gpr .rsi = rp) (hbp : s.gpr .rbp = p.I)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 p.len) (hdx : s.gpr .rdx = BitVec.ofNat 64 p.bits)
    (hsrc : Src s p.O p.Z rp bs) (ho : OutOk s p.O p.Z p.op p.len)
    (ha : Apart p.op p.len rp bs.length) (hbl : bs.length = p.len) :
    WP isa cutRestore s fun t => ModulusReady t p.I p.IZ p.w p.mi p.N ∧
      t.gpr .rsi = p.op ∧ t.gpr .rcx = BitVec.ofNat 64 p.len ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem p.op p.len) = Spec.Rsa.os2ip bs % 2 ^ p.bits ∧
      (∀ d, d + 8 ≤ p.Z → word t.mem p.O d = word s.mem p.O d) ∧
      (∀ d, d + 8 ≤ p.IZ → word t.mem p.I d = word s.mem p.I d) ∧
      DrawFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  have hz64 : p.Z ≤ 2 ^ 64 := Nat.le_trans (Nat.le_add_left _ _) hs.nowrap
  have hiz64 : p.IZ ≤ 2 ^ 64 := by unfold WitnessParams.IZ; omega
  have hi := output_inner ho hz64
  have hb1 : 16 ≤ p.bits := by have := p.bits1; omega
  have hlen' : bs.length = (p.bits + 7) / 8 := hbl
  have hcount : s.gpr .rcx = BitVec.ofNat 64 bs.length := by rw [hbl]; exact hcx
  unfold cutRestore
  refine WP.seq (WP.mono (witnessCut_ok hb1 p.bits2 hlen' hsi hdi hcount hdx hsrc.rd
    (fun i hi => ho.wr i (by omega))
    (fun i hi => by
      rw [hsrc.val i hi]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some])
    (fun i hi j hj he => ha j (by omega) i hi he.symm)) fun u ⟨_, hv, hf, k⟩ => ?_)
  have hf' : ∀ a, (∀ i < p.len, a ≠ off p.op i) → u.mem a = s.mem a := by
    simpa only [hbl] using hf
  have hwO := words_outside_bytes hz64 hf' ho.sep
  have hwI := words_outside_bytes hiz64 hf' hi.sep
  have hI136 : 136 ≤ p.IZ := by
    have hroom := p.room
    unfold WitnessParams.IZ
    simp only [slot, VG.Impl.Bignum.hdrBytes] at hroom
    omega_using [hroom]
  have hsO : Scr u p.O 256 := by
    have hsize : 256 ≤ p.Z := by have := p.room; omega
    simpa [off] using (hs.congr k.2.2).sub (o := 0) (n := 256) (by omega) (by decide)
  have hlink : word u.mem p.I (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = p.O := by
    rw [hwI _ (by change 136 ≤ p.IZ; exact hI136)]
    exact hl
  have hOut : word u.mem p.O (8 * oOut) = p.op := by
    rw [hwO _ (by have := p.room; unfold oOut; omega)]
    exact hop
  have hLen : word u.mem p.O (8 * oWitnessLen) = BitVec.ofNat 64 p.len := by
    rw [hwO _ (by have := p.room; unfold oWitnessLen; omega)]
    exact hlen
  refine WP.mono (drawLoad_ok (hready.good.scr.congr (k.2.2.trans hwr)) hI136 hsO
    ((k.gpr (by decide)).trans hbp) hlink hOut hLen) fun t ⟨hdt, hst, hct, hmt, kt⟩ => ?_
  have hwOt : ∀ d, d + 8 ≤ p.Z → word t.mem p.O d = word s.mem p.O d := by
    intro d hd; rw [hmt]; exact hwO d hd
  have hwIt : ∀ d, d + 8 ≤ p.IZ → word t.mem p.I d = word s.mem p.I d := by
    intro d hd; rw [hmt]; exact hwI d hd
  refine ⟨hready.of_words p.dims (fun d hd => (hwIt d hd).trans (hwords d hd))
    (kt.2.2.trans (k.2.2.trans hwr)) hdt, hst, hct, ?_, hwOt, hwIt, ?_,
    (k.trans kt).mono (by decide)⟩
  · rw [hmt]
    simpa only [hbl] using hv
  · rw [hmt]
    exact DrawFrame.of_bytes hf'

end VG.Proof.Ffdh.X86_64.ParameterCandidate
