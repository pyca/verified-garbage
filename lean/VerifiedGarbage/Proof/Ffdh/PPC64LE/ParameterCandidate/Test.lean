module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Mr
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.MontPrep
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An FFDH parameter candidate on PPC64LE: the test of a modulus

`montPrep_mst`: `montPrep` after `phase` gives `MSt`, the state the
witnesses need; `testCore_ok`: then `millerRabin` ends in `MrEnd`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)

/-- `montPrep`: the Montgomery constants of the modulus `N` in array 0. -/
theorem montPrep_mst {p : PP} {mb N : Nat} {s : State} (h : St p s) (hp : Ph p mb s)
    (hm1 : 511 ≤ mb) (hm2 : mb ≤ p.bits) (hn : wv s.mem p.B (slot (wOf mb) 0) (wOf mb) = N)
    (hodd : N % 2 = 1) (hN3 : 3 ≤ N) :
    WP isa montPrep s fun t => MSt p mb N t ∧ Frm p.B (mutR p.n) s.mem t.mem ∧
      word t.mem p.B 152 = word s.mem p.B 152 := by
  have hdn := h.dims.n
  have hb2 := h.dims.b2
  have hw8 : 8 ≤ wOf mb := by simp only [wOf]; omega_arith
  have hw128 : wOf mb ≤ 128 := by simp only [wOf]; omega_arith
  have es : ∀ j, slot (wOf mb) j = 256 + j * (8 * (wOf mb + 2)) := fun _ => rfl
  have e1 := es 1; have e4 := es 4; have e6 := es 6; have e8 := es 8; have e9 := es 9; have e11 := es 11
  have e27 := es 27; have e28 := es 28
  have hZn : p.Z = 8 * p.n := rfl
  have hZ : slot (wOf mb) 28 + saveBytes ≤ p.Z := by
    have hwd : wOf mb = (mb + 63) / 64 := rfl
    have hL : p.L = (p.bits + 7) / 8 := rfl
    simp only [saveBytes, PP.Z]; omega_arith
  have env : Env s p.B (8 * p.n) (wOf mb) := ⟨h.scr, hp.r10, hp.r29, hp.r11, h.r31, by omega_arith, hw128, by simp only [PP.Z] at hZ; omega_arith⟩
  have harr : arr s.mem p.B (wOf mb) 0 = N := by rw [arr, Pre.val32_eq_wv]; exact hn
  refine WP.mono (montPrep_ok env harr hodd hN3) fun t ⟨⟨envt, nt, inv, _, _, r1, r9, r10, e, l, outs⟩, k⟩ => ?_
  have fo : Frm p.B (mpRanges (wOf mb)) s.mem t.mem := outs
  have hf : Frm p.B (mutR p.n) s.mem t.mem := Frm.toMut fo fun r hr => by
    simp only [mpRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact InMut.hdr (i := 7) (by decide)
    all_goals (try simp only [Impl.MillerRabin.PPC64LE.aE]); exact InMut.arrays (by omega_arith) (by omega_arith)
  have st := h.step hf k (by decide)
  have ew : ∀ d, d + 8 ≤ 56 ∨ (64 ≤ d ∧ d + 8 ≤ 256) → word t.mem p.B d = word s.mem p.B d := fun d hd =>
    fo.word_eq (fun r hr => by
      simp only [mpRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [Impl.MillerRabin.PPC64LE.aE] <;> omega_arith) (by omega_arith)
  have ph : Ph p mb t := ⟨envt.h10, envt.h11, envt.h29, (ew _ (by simp only [hMb]; omega_arith)).trans hp.mbW,
    (ew _ (by simp only [Impl.MillerRabin.PPC64LE.Search.hK]; omega_arith)).trans hp.kW,
    (ew _ (by simp only [hW]; omega_arith)).trans hp.wW, (ew _ (by simp only [hStride]; omega_arith)).trans hp.strideW,
    fun j hj => (ew _ (by omega_arith)).trans (hp.arrW j hj),
    (ew _ (by simp only [hChecks]; omega_arith)).trans hp.checksW, (ew _ (by simp only [hTop]; omega_arith)).trans hp.topW⟩
  refine ⟨⟨st, ph, ⟨envt, (ew 0 (by omega_arith)).trans h.args.wsLen, (ew 48 (by omega_arith)).trans hp.wW,
    (ew 224 (by omega_arith)).trans hp.strideW, fun j hj => (ew _ (by omega_arith)).trans (hp.arrW j hj), nt, hN3, hodd,
    inv, r1, r9, r10, e, l⟩, hm1, hm2⟩, hf, ew 152 (by omega_arith)⟩

/-- The test of the modulus `N` of `mb` bits in array 0, from octet `u` of
the tape. -/
theorem testCore_ok (R : RoundImpl) {p : PP} {mb N u : Nat} {s : State} (h : St p s) (hp : Ph p mb s)
    (hm1 : 511 ≤ mb) (hm2 : mb ≤ p.bits) (hn : wv s.mem p.B (slot (wOf mb) 0) (wOf mb) = N)
    (hbl : Spec.RsaKeyGen.bitLength (N - 1) = mb) (hodd : N % 2 = 1) (hN3 : 3 ≤ N)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) :
    WP isa (.seq montPrep (millerRabin R.name R.code)) s
      (MrEnd p mb N (VG.Proof.Ffdh.ParameterCandidate.checkWitnesses N (Spec.Ffdh.primeChecks mb) (p.r.drop u))) :=
  WP.seq (WP.mono (montPrep_mst h hp hm1 hm2 hn hodd hN3) fun _ ⟨M, _, h152⟩ =>
    millerRabin_ok R hbl M (h152.trans hu) hul)

/-- Before a modulus's Montgomery constants: what `testCore_ok` asks. -/
structure TCPre (p : PP) (mb N u : Nat) (s : State) : Prop where
  st : St p s
  ph : Ph p mb s
  mb1 : 511 ≤ mb
  mb2 : mb ≤ p.bits
  n : wv s.mem p.B (slot (wOf mb) 0) (wOf mb) = N
  bl : Spec.RsaKeyGen.bitLength (N - 1) = mb
  odd : N % 2 = 1
  n3 : 3 ≤ N
  used : word s.mem p.B 152 = BitVec.ofNat 64 u
  ul : u ≤ p.r.length

theorem TCPre.core (R : RoundImpl) {p : PP} {mb N u : Nat} {s : State} (h : TCPre p mb N u s) :
    WP isa (.seq montPrep (millerRabin R.name R.code)) s
      (MrEnd p mb N (VG.Proof.Ffdh.ParameterCandidate.checkWitnesses N (Spec.Ffdh.primeChecks mb) (p.r.drop u))) :=
  testCore_ok R h.st h.ph h.mb1 h.mb2 h.n h.bl h.odd h.n3 h.used h.ul

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
