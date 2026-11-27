module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Phase
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Mem
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Mr
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.MontPrep
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WordCut
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Prep

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Tests`, which the modules that import this one used -/

section

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Shape`, which this module and modules that import it used -/

section

/-!
# An FFDH parameter candidate on PPC64LE: the candidate p

`shapeP_ok`: in p's working space (`Ph p bits C`), the first `out_len` octets
of the tape into array 0 (`loadN_ok`), its top word cut to `bits` bits with
its top bit set, and its low bit set: `candidateOf bits` of their number
(`wv_shape`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search

/-- The registers `shapeP` writes. -/
def shRegs : List Reg := [.r0, .r4, .r5, .r6, .r12, .r14, .r15, .r16, .r17]

/-- `shapeP`'s first block: the tape's address and `out_len`. -/
theorem shapeHead_ok {p : PP} {s : State} (h : St p s) :
    WP isa (.block [ldh .r12 hRand, ldh .r6 hLen]) s fun u => (u.gpr .r12 = off p.rp 0 ∧
      u.gpr .r6 = BitVec.ofNat 64 p.L ∧ u.mem = s.mem) ∧ Keep [.r6, .r12] s u := by
  refine WP.keep [.r6, .r12] ?_ (by decide)
  simp only [ldh, hRand, hLen]
  prun [h.r31, h.ld (d := 136) (by decide), h.ld (d := 24) (by decide), h.args.rand', h.args.len',
    BitVec.add_zero]

theorem shapeP_ok {C : Nat} {p : PP} {s : State} (h : St p s) (hp : Ph p p.bits C s) (hrl : p.L ≤ p.r.length) :
    WP isa shapeP s fun t =>
      (wv t.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) =
          Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)) ∧
        Frm p.B [(slot (wOf p.bits) 0, 8 * wOf p.bits)] s.mem t.mem) ∧ Keep shRegs s t := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hn := h.dims.n
  have hnw := h.scr.nowrap
  have h10 := hp.r10
  have h11 := hp.r11
  have htop := hp.topW
  generalize hwd : wOf p.bits = w at h10 h11 htop ⊢
  obtain hw8 : 8 ≤ w := by simp only [wOf] at hwd; omega_arith
  obtain hw128 : w ≤ 128 := by simp only [wOf] at hwd; omega_arith
  obtain hLw : p.L ≤ 8 * w := by simp only [wOf, PP.L] at hwd ⊢; omega_arith
  obtain hZ : slot w 0 + 8 * w ≤ p.Z := by simp only [slot, hdrBytes, PP.Z, PP.L] at hn ⊢; omega_arith
  obtain hL1 : 1 ≤ p.L := by simp only [PP.L]; omega_arith
  unfold shapeP
  refine WP.seq (WP.mono (shapeHead_ok h) fun u ⟨⟨u12, u6, um⟩, ku⟩ => ?_)
  obtain hrd : ∀ i < p.L, InRegions (u.rd ++ u.wr) (off p.rp i) 1 := fun i hi => by
    rw [ku.rd, ku.wr]; exact h.bufs.rdR i (by omega_arith)
  refine WP.seq (WP.mono (loadN_ok (h.scr.congr ku.wr) ((ku.gpr .r10 (by decide)).trans h10) u12 u6
    ((ku.gpr .r11 (by decide)).trans h11) hL1 hLw (by omega_arith) (by simp [slot, hdrBytes]) hZ hrd
    (fun i hi => h.bufs.sepR i (by omega_arith))) fun v ⟨vv, vo, kv⟩ => ?_)
  obtain kuv := ku.trans kv
  rw [um, Pre.val32_eq_wv, h.take_bytes hrl] at vv
  obtain h0 : slot w 0 = 256 := by simp [slot, hdrBytes]
  -- The top word's mask, from the header.
  obtain hk1 : 1 ≤ p.bits + 64 - 64 * w := by simp only [wOf] at hwd; omega_arith
  obtain hk2 : p.bits + 64 - 64 * w ≤ 64 := by simp only [wOf] at hwd; omega_arith
  generalize hkd : p.bits + 64 - 64 * w = k at htop hk1 hk2
  obtain tv : v.mem.readW (p.B + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (2 ^ k - 1) := by
    show word v.mem p.B 192 = _
    rw [Outside.word vo (by omega_arith) (by omega_arith), um]; exact htop
  obtain e5 : off p.B (slot w 0 + 8 * w) - BitVec.ofNat 64 8 = off p.B (slot w 0 + 8 * (w - 1)) := by
    simp only [off]; rw [Offset.add_ofNat_sub _ (by omega_arith)]; congr 2; omega_arith
  obtain sT : InRegions v.wr (off p.B (slot w 0 + 8 * (w - 1))) 8 := by
    rw [kuv.wr]; exact h.scr.st (by omega_arith)
  obtain lT : InRegions (v.rd ++ v.wr) (off p.B (slot w 0 + 8 * (w - 1))) 8 := by
    rw [kuv.rd, kuv.wr]; exact h.scr.ld (by omega_arith)
  obtain sA : InRegions v.wr (off p.B (slot w 0)) 8 := by rw [kuv.wr]; exact h.scr.st (by omega_arith)
  obtain lA : InRegions (v.rd ++ v.wr) (off p.B (slot w 0)) 8 := by
    rw [kuv.rd, kuv.wr]; exact h.scr.ld (by omega_arith)
  obtain eA : ∀ x : BitVec 64, (v.mem.writeW (off p.B (slot w 0 + 8 * (w - 1))) x).readW (off p.B (slot w 0)) 64 =
      v.mem.readW (off p.B (slot w 0)) 64 := fun x => rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)
  obtain ebit : (BitVec.ofNat 64 (2 ^ k - 1)) >>> 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 (2 ^ (k - 1)) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_arith⟩
    rw [Nat.add_sub_cancel, Nat.pow_succ]
    have : 2 ^ j ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega_arith)
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    generalize 2 ^ j = P at *
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    omega_arith
  obtain l192 : InRegions (v.rd ++ v.wr) (p.B + BitVec.ofNat 64 192) 8 := by
    rw [kuv.rd, kuv.wr]; exact h.ld (d := 192) (by decide)
  refine WP.mono (WP.keep [.r4, .r5, .r6] (Q := fun t => t.mem =
      (v.mem.writeW (off p.B (slot w 0 + 8 * (w - 1)))
        ((v.mem.readW (off p.B (slot w 0 + 8 * (w - 1))) 64 &&& BitVec.ofNat 64 (2 ^ k - 1)) |||
          BitVec.ofNat 64 (2 ^ (k - 1)))).writeW (off p.B (slot w 0))
        (v.mem.readW (off p.B (slot w 0)) 64 ||| BitVec.ofNat 64 1)) ?_ (by decide))
    fun t ⟨tm, kt⟩ => ⟨⟨?_, ?_⟩, (kuv.trans kt).mono (by decide)⟩
  · simp only [ldh, hTop]
    prun [(kuv.gpr .r10 (by decide)).trans h10, (kuv.gpr .r11 (by decide)).trans h11,
      (kuv.gpr .r31 (by decide)).trans h.r31, Proof.MillerRabin.PPC64LE.shl2_ofNat, e5, sT, lT, sA, lA, eA,
      l192, tv, ebit, BitVec.add_zero]
  · have hb : 64 * (w - 1) + k = p.bits := by simp only [wOf] at hwd; omega_arith
    rw [← hb, ← vv]
    refine Proof.Ffdh.ParameterCandidate.wv_shape (by omega_arith) hk1 hk2 ?_ ?_ fun j hj0 hj => ?_
    · simp only [word, off] at tm ⊢; rw [tm, rw_self]; rfl
    · simp only [word, off] at tm ⊢
      rw [tm, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rw_self]
    · simp only [word, off] at tm ⊢
      rw [tm, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
  · rw [um] at vo
    obtain hr : ∀ a, a + 8 ≤ 8 * w → ∃ r ∈ [(slot w 0, 8 * w)], r.1 ≤ slot w 0 + a ∧ slot w 0 + a + 8 ≤ r.1 + r.2 :=
      fun a ha => ⟨_, List.mem_singleton_self _, by dsimp only; omega_arith, by dsimp only; omega_arith⟩
    simp only [off] at tm
    rw [tm]
    obtain f1 := frm_writeW (Frm.of_outside vo (List.mem_singleton_self _)) (a := slot w 0 + 8 * (w - 1))
      ((v.mem.readW (p.B + BitVec.ofNat 64 (slot w 0 + 8 * (w - 1))) 64 &&& BitVec.ofNat 64 (2 ^ k - 1)) |||
        BitVec.ofNat 64 (2 ^ (k - 1))) (hr _ (by omega_arith)) (by omega_arith)
    obtain f2 := frm_writeW f1 (a := slot w 0 + 0)
      (v.mem.readW (p.B + BitVec.ofNat 64 (slot w 0)) 64 ||| BitVec.ofNat 64 1) (hr _ (by omega_arith)) (by omega_arith)
    simpa only [Nat.add_zero] using f2

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Test`, which only this module used -/

section

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
theorem montPrep_mst {C : Nat} {p : PP} {mb N : Nat} {s : State} (h : St p s) (hp : Ph p mb C s)
    (hm1 : 511 ≤ mb) (hm2 : mb ≤ p.bits) (hn : wv s.mem p.B (slot (wOf mb) 0) (wOf mb) = N)
    (hodd : N % 2 = 1) (hN3 : 3 ≤ N) :
    WP isa montPrep s fun t => MSt p mb N C t ∧ Frm p.B (mutR p.n) s.mem t.mem ∧
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
  have ph : Ph p mb C t := ⟨envt.h10, envt.h11, envt.h29, (ew _ (by simp only [hMb]; omega_arith)).trans hp.mbW,
    (ew _ (by simp only [Impl.MillerRabin.PPC64LE.Search.hK]; omega_arith)).trans hp.kW,
    (ew _ (by simp only [hW]; omega_arith)).trans hp.wW, (ew _ (by simp only [hStride]; omega_arith)).trans hp.strideW,
    fun j hj => (ew _ (by omega_arith)).trans (hp.arrW j hj),
    (ew _ (by simp only [hChecks]; omega_arith)).trans hp.checksW, hp.k1, hp.k2, (ew _ (by simp only [hTop]; omega_arith)).trans hp.topW⟩
  refine ⟨⟨st, ph, ⟨envt, (ew 0 (by omega_arith)).trans h.args.wsLen, (ew 48 (by omega_arith)).trans hp.wW,
    (ew 224 (by omega_arith)).trans hp.strideW, fun j hj => (ew _ (by omega_arith)).trans (hp.arrW j hj), nt, hN3, hodd,
    inv, r1, r9, r10, e, l⟩, hm1, hm2⟩, hf, ew 152 (by omega_arith)⟩

/-- The test of the modulus `N` of `mb` bits in array 0, from octet `u` of
the tape. -/
theorem testCore_ok {C : Nat} (R : RoundImpl) {p : PP} {mb N u : Nat} {s : State} (h : St p s) (hp : Ph p mb C s)
    (hm1 : 511 ≤ mb) (hm2 : mb ≤ p.bits) (hn : wv s.mem p.B (slot (wOf mb) 0) (wOf mb) = N)
    (hbl : Spec.RsaKeyGen.bitLength (N - 1) = mb) (hodd : N % 2 = 1) (hN3 : 3 ≤ N)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) :
    WP isa (.seq montPrep (millerRabin R.name R.code)) s
      (MrEnd p mb N C (VG.Proof.Ffdh.ParameterCandidate.checkWitnesses N C (p.r.drop u))) :=
  WP.seq (WP.mono (montPrep_mst h hp hm1 hm2 hn hodd hN3) fun _ ⟨M, _, h152⟩ =>
    millerRabin_ok R hbl M (h152.trans hu) hul)

/-- Before a modulus's Montgomery constants: what `testCore_ok` asks. -/
structure TCPre (p : PP) (mb N u C : Nat) (s : State) : Prop where
  st : St p s
  ph : Ph p mb C s
  mb1 : 511 ≤ mb
  mb2 : mb ≤ p.bits
  n : wv s.mem p.B (slot (wOf mb) 0) (wOf mb) = N
  bl : Spec.RsaKeyGen.bitLength (N - 1) = mb
  odd : N % 2 = 1
  n3 : 3 ≤ N
  used : word s.mem p.B 152 = BitVec.ofNat 64 u
  ul : u ≤ p.r.length

theorem TCPre.core {C : Nat} (R : RoundImpl) {p : PP} {mb N u : Nat} {s : State} (h : TCPre p mb N u C s) :
    WP isa (.seq montPrep (millerRabin R.name R.code)) s
      (MrEnd p mb N C (VG.Proof.Ffdh.ParameterCandidate.checkWitnesses N C (p.r.drop u))) :=
  testCore_ok R h.st h.ph h.mb1 h.mb2 h.n h.bl h.odd h.n3 h.used h.ul

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end


/-!
# An FFDH parameter candidate on PPC64LE: the tests of q and p

`testQ_ok`: the test of q, halved in place from p's width; `testP_ok`: the
test of p, loaded again from the tape.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

/-- The low `k` words of a number below `2^(64 k)` are the number. -/
theorem wv_low {m : Mem} {B : Addr} {o w k v : Nat} (h : wv m B o w = v) (hk : k ≤ w)
    (hv : v < 2 ^ (64 * k)) : wv m B o k = v := by
  have e := wv_add m B o k (w - k)
  rw [show k + (w - k) = w by omega_arith, h] at e
  generalize 2 ^ (64 * k) = P at e hv
  generalize wv m B (o + 8 * k) (w - k) = hi at e
  rcases Nat.eq_zero_or_pos hi with h0 | hpos
  · rw [h0, Nat.mul_zero, Nat.add_zero] at e; exact e.symm
  · have := Nat.le_mul_of_pos_right P hpos; omega_arith

/-- `Ph` survives a change of memory that keeps the header. -/
theorem Ph.keepHdr {C : Nat} {p : PP} {mb : Nat} {s t : State} (h : Ph p mb C s)
    (r10 : t.gpr .r10 = s.gpr .r10) (r11 : t.gpr .r11 = s.gpr .r11) (r29 : t.gpr .r29 = s.gpr .r29)
    (hw : ∀ d, d + 8 ≤ 256 → word t.mem p.B d = word s.mem p.B d) : Ph p mb C t :=
  ⟨r10.trans h.r10, r11.trans h.r11, r29.trans h.r29, (hw 248 (by decide)).trans h.mbW,
    (hw 216 (by decide)).trans h.kW, (hw 48 (by decide)).trans h.wW, (hw 224 (by decide)).trans h.strideW,
    fun j hj => (hw _ (by omega_arith)).trans (h.arrW j hj), (hw 168 (by decide)).trans h.checksW, h.k1, h.k2,
    (hw 192 (by decide)).trans h.topW⟩

theorem slot_zero (w : Nat) : slot w 0 = 256 := by simp [slot, hdrBytes]

theorem phR_low : ∀ r ∈ phRanges ++ [(8 * hTop, 8)], r.1 + r.2 ≤ 256 := by
  intro r hr
  simp only [phRanges, hTop, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

theorem phR_used : ∀ r ∈ phRanges ++ [(8 * hTop, 8)], 152 + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 152 := by
  intro r hr
  simp only [phRanges, hTop, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The set-up of q's test: its working space. -/
theorem qPrep_ok {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hq : wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = (c - 1) / 2) (hqo : ((c - 1) / 2) % 2 = 1)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) :
    WP isa (.seq (phase true) (.block [])) s (TCPre p (p.bits - 1) ((c - 1) / 2) u (Spec.Ffdh.primeChecks (p.bits - 1))) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hdn := h.dims.n
  have hn' := h.dims.n'
  obtain ⟨hpo, hl, hu'⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hpo hl hu'
  obtain ⟨hql, hqu⟩ := VG.Proof.Ffdh.ParameterCandidate.half_shape (by omega_arith) hpo hl hu'
  have hbl := VG.Proof.Ffdh.ParameterCandidate.half_pred_bitLength (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L)) (by rw [← hc]; exact hqo)
  rw [← hc] at hbl
  refine WP.seq (WP.mono (phase_ok h true) fun t ⟨⟨st, ph, hf⟩, _⟩ => ?_)
  simp only [mbOf, ↓reduceIte] at ph
  rw [WP.block_nil_iff]
  have hL : p.L = (p.bits + 7) / 8 := rfl
  have hwq : wOf (p.bits - 1) ≤ wOf p.bits := by simp only [wOf]; omega_arith
  refine ⟨st, ph, by omega_arith, by omega_arith, ?_, hbl, hqo, ?_, ?_, hul⟩
  · rw [slot_zero] at hq ⊢
    refine wv_low (w := wOf p.bits) ?_ hwq (Nat.lt_of_lt_of_le hqu (Nat.pow_le_pow_right (by decide) (by
      simp only [wOf]; omega_arith)))
    rw [hf.wv_eq (fun r hr => .inr (phR_low r hr)) (by simp only [wOf]; omega_arith)]
    exact hq
  · have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 2 ≤ p.bits - 2 by omega_arith)
    omega_arith
  · rw [hf.word_eq phR_used (by decide)]; exact hu

/-- The test of q, halved in array 0 in p's width. -/
theorem testQ_ok (R : RoundImpl) {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hq : wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = (c - 1) / 2) (hqo : ((c - 1) / 2) % 2 = 1)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) :
    WP isa (test true (.block []) R.name R.code) s
      (MrEnd p (p.bits - 1) ((c - 1) / 2) (Spec.Ffdh.primeChecks (p.bits - 1))
        (checkWitnesses ((c - 1) / 2) (Spec.Ffdh.primeChecks (p.bits - 1)) (p.r.drop u))) := by
  unfold test
  simp only [↓reduceIte]
  exact WP.assoc (WP.seq (WP.mono (qPrep_ok h hc hq hqo hu hul) fun _ ht =>
    WP.seq (WP.block_nil_iff.mpr (ht.core R))))

/-- The set-up of p's test: its working space, and p from the tape. -/
theorem pPrep_ok {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (.seq (phase false) shapeP) s (TCPre p p.bits c u (Spec.Ffdh.primeChecks p.bits)) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hdn := h.dims.n
  obtain ⟨hpo, hl, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  have hbl := (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))).2
  rw [← hc] at hpo hl hbl
  refine WP.seq (WP.mono (phase_ok h false) fun t ⟨⟨st, ph, hf⟩, _⟩ => ?_)
  simp only [mbOf, Bool.false_eq_true, ↓reduceIte] at ph
  refine WP.mono (shapeP_ok st ph hL) fun t₂ ⟨⟨hn₂, f₂⟩, k₂⟩ => ?_
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hw : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  have hlow : ∀ d, d + 8 ≤ 256 → word t₂.mem p.B d = word t.mem p.B d := fun d hd =>
    f₂.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by rw [hsl]; exact hd)) (by omega_arith)
  have st₂ : St p t₂ := st.step (Frm.toMut f₂ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact InMut.arrays (by rw [hsl]) (by rw [hsl]; simp only [saveBytes]; omega_arith)) k₂ (by decide)
  have ph₂ : Ph p p.bits (Spec.Ffdh.primeChecks p.bits) t₂ := ph.keepHdr (k₂.gpr _ (by decide)) (k₂.gpr _ (by decide)) (k₂.gpr _ (by decide)) hlow
  refine ⟨st₂, ph₂, by omega_arith, Nat.le_refl _, by rw [hn₂, hc], hbl, hpo, ?_, ?_, hul⟩
  · have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 2 ≤ p.bits - 1 by omega_arith)
    omega_arith
  · rw [hlow 152 (by decide), hf.word_eq phR_used (by decide)]; exact hu

/-- `hChecks := C'`: the test's other data stay. -/
theorem TCPre.setChecks {C C' : Nat} {p : PP} {mb N u : Nat} {s t : State} (h : TCPre p mb N u C s)
    (hm : t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 168) (BitVec.ofNat 64 C')) {regs : List Reg}
    (k : Keep regs s t) (h31 : Reg.r31 ∉ regs) (h2 : Reg.r2 ∉ regs) (h10 : Reg.r10 ∉ regs)
    (h11 : Reg.r11 ∉ regs) (h29 : Reg.r29 ∉ regs) (c1 : 1 ≤ C') (c2 : C' ≤ 128) : TCPre p mb N u C' t := by
  have hdn := h.st.dims.n
  have hf : Frm p.B [(168, 8)] s.mem t.mem := by
    rw [hm]; exact frm_writeW (a := 168) (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by decide, by decide⟩
      (by decide)
  have st := h.st.step (Frm.toMut hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact InMut.hdr (i := 21) (by decide)) k h31 h2
  have ew : ∀ d, d + 8 ≤ 168 ∨ 176 ≤ d → d + 8 ≤ 2 ^ 64 → word t.mem p.B d = word s.mem p.B d := fun d hd hd' =>
    hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; dsimp only; omega_arith) hd'
  have hp := h.ph
  have ph : Ph p mb C' t := ⟨(k.gpr _ h10).trans hp.r10, (k.gpr _ h11).trans hp.r11, (k.gpr _ h29).trans hp.r29,
    (ew _ (by simp only [hMb]; omega_arith) (by simp only [hMb]; omega_arith)).trans hp.mbW,
    (ew _ (by simp only [Impl.MillerRabin.PPC64LE.Search.hK]; omega_arith)
      (by simp only [Impl.MillerRabin.PPC64LE.Search.hK]; omega_arith)).trans hp.kW,
    (ew _ (by simp only [hW]; omega_arith) (by simp only [hW]; omega_arith)).trans hp.wW,
    (ew _ (by simp only [hStride]; omega_arith) (by simp only [hStride]; omega_arith)).trans hp.strideW,
    fun j hj => (ew _ (by omega_arith) (by omega_arith)).trans (hp.arrW j hj),
    by show t.mem.readW (p.B + BitVec.ofNat 64 168) 64 = _; rw [hm, rw_self], c1, c2,
    (ew _ (by simp only [hTop]; omega_arith) (by simp only [hTop]; omega_arith)).trans hp.topW⟩
  refine ⟨st, ph, h.mb1, h.mb2, ?_, h.bl, h.odd, h.n3, (ew 152 (by decide) (by decide)).trans h.used, h.ul⟩
  have hb2 := h.st.dims.b2
  have hm2 := h.mb2
  rw [hf.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr, slot_zero]; exact .inr (by decide))
    (by rw [slot_zero]; simp only [wOf]; omega_arith)]
  exact h.n

/-- `firstCheck`: one witness. -/
theorem firstCheck_ok {C : Nat} {p : PP} {mb N u : Nat} {s : State} (h : TCPre p mb N u C s) :
    WP isa firstCheck s (TCPre p mb N u 1) := by
  have l168 : InRegions s.wr (p.B + BitVec.ofNat 64 168) 8 := h.st.st (d := 168) (by decide)
  refine WP.mono (WP.keep [.r3] (Q := fun t => t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 168) (BitVec.ofNat 64 1))
    (by simp only [firstCheck, sth, hChecks]; prun [h.st.r31, l168]) (by decide)) fun t ⟨tm, kt⟩ => ?_
  exact h.setChecks tm kt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `restChecks`: the witnesses but one. -/
theorem restChecks_ok {C : Nat} {p : PP} {mb N u : Nat} {s : State} (h : TCPre p mb N u C s) (hC : 2 ≤ C) :
    WP isa restChecks s (TCPre p mb N u (C - 1)) := by
  have l168 : InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 168) 8 := h.st.ld (d := 168) (by decide)
  have s168 : InRegions s.wr (p.B + BitVec.ofNat 64 168) 8 := h.st.st (d := 168) (by decide)
  have hc : s.mem.readW (p.B + BitVec.ofNat 64 168) 64 = BitVec.ofNat 64 C := h.ph.checksW
  have c2 := h.ph.k2
  have hC' : BitVec.ofNat 64 C - BitVec.ofNat 64 1 = BitVec.ofNat 64 (C - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  refine WP.mono (WP.keep [.r3] (Q := fun t => t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 168)
      (BitVec.ofNat 64 (C - 1)))
    (by simp only [restChecks, ldh, sth, hChecks]; prun [h.st.r31, l168, s168, hc, hC']) (by decide))
    fun t ⟨tm, kt⟩ => ?_
  exact h.setChecks tm kt (by decide) (by decide) (by decide) (by decide) (by decide) (by omega_arith) (by omega_arith)

/-- A test of p, loaded again from the tape, its witness count changed by
`adjust` to `K`. -/
theorem testP_of {K : Nat} (R : RoundImpl) {adjust : Prog isa} {p : PP} {s : State} {c u : Nat}
    (hadj : ∀ {t : State}, TCPre p p.bits c u (Spec.Ffdh.primeChecks p.bits) t →
      WP isa adjust t (TCPre p p.bits c u K))
    (h : St p s) (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (test false adjust R.name R.code) s (MrEnd p p.bits c K (checkWitnesses c K (p.r.drop u))) := by
  unfold test
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact WP.assoc (WP.seq (WP.mono (pPrep_ok h hc hu hul hL) fun _ ht =>
    WP.seq (WP.mono (hadj ht) fun _ ht' => ht'.core R)))

/-- The test of p's first witness. -/
theorem testP1_ok (R : RoundImpl) {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (test false firstCheck R.name R.code) s (MrEnd p p.bits c 1 (checkWitnesses c 1 (p.r.drop u))) :=
  testP_of R (fun ht => firstCheck_ok ht) h hc hu hul hL

/-- The test of p's other witnesses. -/
theorem testPR_ok (R : RoundImpl) {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (test false restChecks R.name R.code) s
      (MrEnd p p.bits c (Spec.Ffdh.primeChecks p.bits - 1)
        (checkWitnesses c (Spec.Ffdh.primeChecks p.bits - 1) (p.r.drop u))) :=
  testP_of R (fun ht => restChecks_ok ht (by unfold Spec.Ffdh.primeChecks; split <;> decide)) h hc hu hul hL

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on PPC64LE: the generator's congruence

`residue_ok`: `hBad` is zero exactly when array 0 is 11 modulo 24 (for the
generator 2), or 3 or 7 modulo 10 (for 5). The candidate modulo 3 or 5 is
its digits' sum's (`val32_mod`: `2³² ≡ 1`), reduced by the reciprocal
(`modSmall_ok`); modulo 8 it is its low digit's.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.Mont (w32 val32 val32_succ)

/-- The congruence the generator asks of p. -/
def goodRes (g x : Nat) : Prop := if g = 2 then x % 24 = 11 else x % 10 = 3 ∨ x % 10 = 7

/-- The registers `residue` writes. -/
def resRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7]

/-- `hBad` stored over `m`. -/
theorem bad_post {m : Mem} {B : Addr} {t : State} {v : BitVec 64} {P : Prop}
    (tm : t.mem = m.writeW (B + BitVec.ofNat 64 200) v) (hv : v = 0#64 ↔ P) :
    (word t.mem B (8 * hBad) = 0#64 ↔ P) ∧ Frm B [(8 * hBad, 8)] m t.mem := by
  refine ⟨?_, ?_⟩
  · simp only [word, off, hBad, Nat.reduceMul, tm, rw_self]; exact hv
  · rw [tm]
    exact frm_writeW (a := 200) (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by decide, by decide⟩ (by decide)

/-- `Ph` survives a change of memory that keeps the header but `hBad`. -/
theorem Ph.keepBad {C : Nat} {p : PP} {mb : Nat} {s t : State} (h : Ph p mb C s)
    (r10 : t.gpr .r10 = s.gpr .r10) (r11 : t.gpr .r11 = s.gpr .r11) (r29 : t.gpr .r29 = s.gpr .r29)
    (hw : ∀ d, d + 8 ≤ 200 ∨ (208 ≤ d ∧ d + 8 ≤ 256) → word t.mem p.B d = word s.mem p.B d) : Ph p mb C t :=
  ⟨r10.trans h.r10, r11.trans h.r11, r29.trans h.r29, (hw 248 (by decide)).trans h.mbW,
    (hw 216 (by decide)).trans h.kW, (hw 48 (by decide)).trans h.wW, (hw 224 (by decide)).trans h.strideW,
    fun j hj => (hw _ (by omega_arith)).trans (h.arrW j hj), (hw 168 (by decide)).trans h.checksW, h.k1, h.k2,
    (hw 192 (by decide)).trans h.topW⟩

/-! ## The digits' sum -/

/-- The sum of the `k` digits of 32 bits at `o`. -/
def dsum (m : Mem) (B : Addr) (o : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => dsum m B o k + w32 m B (o + 4 * k)

theorem dsum_le (m : Mem) (B : Addr) (o : Nat) : ∀ k, dsum m B o k ≤ k * 2 ^ 32
  | 0 => Nat.le_refl _
  | k + 1 => by
    have h1 := dsum_le m B o k
    have h2 : w32 m B (o + 4 * k) < 2 ^ 32 := (m.readW (off B (o + 4 * k)) 32).isLt
    show dsum m B o k + w32 m B (o + 4 * k) ≤ (k + 1) * 2 ^ 32
    rw [Nat.add_mul, Nat.one_mul]; omega_using [h1, h2]

/-- Modulo a divisor of `2³² − 1`, a number is its digits' sum. -/
theorem val32_mod {d : Nat} (hd : 2 ^ 32 % d = 1) (m : Mem) (B : Addr) (o : Nat) :
    ∀ k, val32 m B o k % d = dsum m B o k % d
  | 0 => rfl
  | k + 1 => by
    have hd1 : 1 % d = 1 := by
      rcases Nat.lt_or_ge d 2 with h | h
      · have : d = 0 ∨ d = 1 := by omega_using [h]
        rcases this with rfl | rfl <;> simp at hd
      · exact Nat.mod_eq_of_lt h
    have hp : 2 ^ (32 * k) % d = 1 := by rw [Nat.pow_mul, Nat.pow_mod, hd, Nat.one_pow, hd1]
    rw [val32_succ, dsum, Nat.add_mod, Nat.mul_mod, hp, Nat.one_mul, Nat.mod_mod, val32_mod hd m B o k,
      ← Nat.add_mod]

/-- After `j` digits. -/
def DInv (u : State) (B : Addr) (o : Nat) (j : Nat) (t : State) : Prop :=
  (t.gpr .r3 = BitVec.ofNat 64 (dsum u.mem B o j) ∧ t.gpr .r5 = off B (o + 4 * j) ∧ t.mem = u.mem) ∧
    Keep [.r0, .r3, .r4, .r5] u t

theorem digitSum_ok {u : State} {B : Addr} {Z o w : Nat} (hs : Scr u B Z) (h10 : u.gpr .r10 = off B o)
    (h11 : u.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w) (hw' : w ≤ 128) (hZ : o + 8 * w ≤ Z) :
    WP isa digitSum u fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (dsum u.mem B o (2 * w)) ∧ t.mem = u.mem) ∧ Keep [.r0, .r3, .r4, .r5] u t := by
  unfold digitSum
  refine WP.seq (WP.mono (WP.keep [.r3, .r4, .r5] (Q := fun v => v.gpr .r3 = BitVec.ofNat 64 0 ∧
      v.gpr .r4 = BitVec.ofNat 64 (2 * w) ∧ v.gpr .r5 = off B o ∧ v.mem = u.mem)
    (by prun [h10, h11, BitVec.add_zero]) (by decide)) fun v ⟨⟨v3, v4, v5, vm⟩, kv⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .r4) (N := 2 * w) (by omega_using [hw']) (by omega_using [hw]) (DInv u B o)
    (fun j hj t ⟨⟨t3, t5, tm⟩, kt⟩ tc => ?_)
    ⟨⟨by rw [v3]; rfl, by rw [v5, Nat.mul_zero, Nat.add_zero], vm⟩, kv.mono (by decide)⟩ v4)
    fun t ⟨⟨t3, _, tm⟩, kt⟩ => ⟨⟨t3, tm⟩, kt⟩
  have hld : InRegions (t.rd ++ t.wr) (off B (o + 4 * j)) 4 := by
    exact (hs.congr kt.wr).ld (by omega_using [hZ, hj])
  have hle := dsum_le u.mem B o j
  have hx : w32 u.mem B (o + 4 * j) < 2 ^ 32 := (u.mem.readW (off B (o + 4 * j)) 32).isLt
  refine WP.mono (WP.keep [.r0, .r3, .r4, .r5] (Q := fun t' => t'.gpr .r3 = BitVec.ofNat 64 (dsum u.mem B o (j + 1)) ∧
      t'.gpr .r5 = off B (o + 4 * (j + 1)) ∧ t'.mem = u.mem ∧ t'.gpr .r4 = t.gpr .r4 - BitVec.ofNat 64 1) ?_
    (by decide)) fun t' ⟨⟨a3, a5, am, a4⟩, k'⟩ => ⟨⟨⟨a3, a5, am⟩, (kt.trans k').mono (by decide)⟩, a4⟩
  simp only [List.cons_append, List.nil_append]
  prun [t5, t3, hld, tm, BitVec.add_zero]
  refine ⟨?_, by rw [show o + 4 * j + 4 = o + 4 * (j + 1) by omega_using []]⟩
  have hj' : j * 2 ^ 32 ≤ 256 * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega_using [hw', hj])
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  show (dsum u.mem B o j % 2 ^ 64 + w32 u.mem B (o + 4 * j) % 2 ^ 64) % 2 ^ 64 =
    (dsum u.mem B o j + w32 u.mem B (o + 4 * j)) % 2 ^ 64
  omega_using []

/-! ## The remainder by the reciprocal -/

theorem quot3 {S : Nat} (hS : S < 18446744073709551616) :
    S * 12297829382473034411 / 18446744073709551616 / 2 = S / 3 := by omega_using [hS]

theorem quot3_lt {S : Nat} (hS : S < 18446744073709551616) :
    S * 12297829382473034411 / 18446744073709551616 < 18446744073709551616 := by omega_using [hS]

/-- `mod3`'s arithmetic: `S − ⌊S m / 2^(64 + 1)⌋ 3 = S mod 3`. (`BitVec.toNat_sub` sends
`simp` astray here, so the product is rewritten first.) -/
theorem mod3_bv {S : Nat} (hS : S < 2 ^ 64) :
    BitVec.ofNat 64 S - BitVec.ofNat 64 ((BitVec.ofNat 64 S).toNat * (12297829382473034411#64).toNat / 18446744073709551616) >>> 1 *
      3#64 = BitVec.ofNat 64 (S % 3) := by
  have hS' : S < 18446744073709551616 := hS
  have hp : BitVec.ofNat 64 ((BitVec.ofNat 64 S).toNat * (12297829382473034411#64).toNat / 18446744073709551616) >>> 1 *
      3#64 = BitVec.ofNat 64 (S / 3 * 3) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hS]
    rw [show (12297829382473034411 : Nat) % 2 ^ 64 = 12297829382473034411 from rfl, Nat.mod_eq_of_lt (quot3_lt hS'),
      show (2 : Nat) ^ 1 = 2 from rfl, quot3 hS', show (3 : Nat) % 2 ^ 64 = 3 from rfl]
  rw [hp, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hS]) (Nat.div_mul_le_self S 3),
    show S - S / 3 * 3 = S % 3 by omega_using []]

theorem mod3_ok {u : State} {S : Nat} (h3 : u.gpr .r3 = BitVec.ofNat 64 S) (hS : S < 2 ^ 64) :
    WP isa (.block mod3) u fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (S % 3) ∧ t.mem = u.mem) ∧ Keep [.r3, .r6, .r7] u t := by
  have hc : ((BitVec.signExtend 64 ((0xAAAA : BitVec 16) ++ (0 : BitVec 16)) ||| BitVec.setWidth 64 (0xAAAA : BitVec 16))
      <<< 32 ||| BitVec.setWidth 64 (0xAAAA : BitVec 16) <<< 16 ||| BitVec.setWidth 64 (0xAAAB : BitVec 16)) =
      BitVec.ofNat 64 12297829382473034411 := by decide
  refine WP.keep _ ?_ (by decide)
  simp only [mod3, modSmall]
  prun [h3, exec_lis, exec_ori, exec_oris, exec_mulhu, hc]
  exact mod3_bv hS

theorem quot5 {S : Nat} (hS : S < 18446744073709551616) :
    S * 14757395258967641293 / 18446744073709551616 / 4 = S / 5 := by omega_using [hS]

theorem quot5_lt {S : Nat} (hS : S < 18446744073709551616) :
    S * 14757395258967641293 / 18446744073709551616 < 18446744073709551616 := by omega_using [hS]

/-- `mod5`'s arithmetic: `S − ⌊S m / 2^(64 + 2)⌋ 5 = S mod 5`. (`BitVec.toNat_sub` sends
`simp` astray here, so the product is rewritten first.) -/
theorem mod5_bv {S : Nat} (hS : S < 2 ^ 64) :
    BitVec.ofNat 64 S - BitVec.ofNat 64 ((BitVec.ofNat 64 S).toNat * (14757395258967641293#64).toNat / 18446744073709551616) >>> 2 *
      5#64 = BitVec.ofNat 64 (S % 5) := by
  have hS' : S < 18446744073709551616 := hS
  have hp : BitVec.ofNat 64 ((BitVec.ofNat 64 S).toNat * (14757395258967641293#64).toNat / 18446744073709551616) >>> 2 *
      5#64 = BitVec.ofNat 64 (S / 5 * 5) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hS]
    rw [show (14757395258967641293 : Nat) % 2 ^ 64 = 14757395258967641293 from rfl, Nat.mod_eq_of_lt (quot5_lt hS'),
      show (2 : Nat) ^ 2 = 4 from rfl, quot5 hS', show (5 : Nat) % 2 ^ 64 = 5 from rfl]
  rw [hp, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hS]) (Nat.div_mul_le_self S 5),
    show S - S / 5 * 5 = S % 5 by omega_using []]

theorem mod5_ok {u : State} {S : Nat} (h3 : u.gpr .r3 = BitVec.ofNat 64 S) (hS : S < 2 ^ 64) :
    WP isa (.block mod5) u fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (S % 5) ∧ t.mem = u.mem) ∧ Keep [.r3, .r6, .r7] u t := by
  have hc : ((BitVec.signExtend 64 ((0xCCCC : BitVec 16) ++ (0 : BitVec 16)) ||| BitVec.setWidth 64 (0xCCCC : BitVec 16))
      <<< 32 ||| BitVec.setWidth 64 (0xCCCC : BitVec 16) <<< 16 ||| BitVec.setWidth 64 (0xCCCD : BitVec 16)) =
      BitVec.ofNat 64 14757395258967641293 := by decide
  refine WP.keep _ ?_ (by decide)
  simp only [mod5, modSmall]
  prun [h3, exec_lis, exec_ori, exec_oris, exec_mulhu, hc]
  exact mod5_bv hS

/-! ## The congruence -/

theorem and7 (a : Nat) : BitVec.ofNat 64 a &&& BitVec.ofNat 64 7 = BitVec.ofNat 64 (a % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]

theorem and1 (a : Nat) : BitVec.ofNat 64 a &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (a % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (1 : Nat) % 2 ^ 64 = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]

theorem flag2 : ∀ b < 3, ∀ c < 8, ((BitVec.ofNat 64 b ^^^ BitVec.ofNat 64 2) |||
    (BitVec.ofNat 64 c ^^^ BitVec.ofNat 64 3) = 0#64 ↔ b = 2 ∧ c = 3) := by decide

theorem flag5 : ∀ b < 5, ∀ c < 2, (((BitVec.ofNat 64 b ||| BitVec.ofNat 64 1) ^^^ BitVec.ofNat 64 3) |||
    (BitVec.ofNat 64 c ^^^ BitVec.ofNat 64 1) = 0#64 ↔ (b = 2 ∨ b = 3) ∧ c = 1) := by decide

/-- The candidate's low digit and digits' sum. -/
theorem low_sum {m : Mem} {B : Addr} {o w : Nat} (hw : 1 ≤ w) :
    wv m B o w % 8 = w32 m B o % 8 ∧ wv m B o w % 2 = w32 m B o % 2 ∧
      wv m B o w % 3 = dsum m B o (2 * w) % 3 ∧ wv m B o w % 5 = dsum m B o (2 * w) % 5 := by
  rw [← Pre.val32_eq_wv]
  refine ⟨?_, ?_, val32_mod (by decide) m B o _, val32_mod (by decide) m B o _⟩ <;>
  · obtain ⟨k, hk⟩ : ∃ k, 2 * w = k + 1 := ⟨2 * w - 1, by omega_using [hw]⟩
    rw [hk, VG.Proof.Mont.val32]
    omega_using []

/-- Generator 2's branch. -/
theorem residue2_ok {C : Nat} {p : PP} {s : State} (h : St p s) (hp : Ph p p.bits C s) :
    WP isa residue2 s fun t =>
      ((word t.mem p.B (8 * hBad) = 0#64 ↔ wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) % 24 = 11) ∧
        Frm p.B [(8 * hBad, 8)] s.mem t.mem) ∧ Keep resRegs s t := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hn := h.dims.n
  have h10 := hp.r10
  have h11 := hp.r11
  generalize hwd : wOf p.bits = w at h10 h11 ⊢
  have hw8 : 8 ≤ w := by simp only [wOf] at hwd; omega_arith
  have hw128 : w ≤ 128 := by simp only [wOf] at hwd; omega_arith
  have hZ : slot w 0 + 8 * w ≤ p.Z := by simp only [slot, hdrBytes, PP.Z, PP.L] at hn ⊢; omega_arith
  obtain ⟨l8, -, l3, -⟩ := low_sum (m := s.mem) (B := p.B) (o := slot w 0) (by omega_using [hw8] : 1 ≤ w)
  unfold residue2
  refine WP.seq (WP.mono (digitSum_ok h.scr h10 h11 (by omega_using [hw8]) hw128 hZ) fun v ⟨⟨v3, vm⟩, kv⟩ => ?_)
  rw [WP.block_append_iff, WP.block_append_iff]
  have hld : InRegions (v.rd ++ v.wr) (off p.B (slot w 0)) 4 := (h.scr.congr kv.wr).ld (by omega_using [hw8, hZ])
  refine WP.mono (WP.keep [.r4] (Q := fun a => a.gpr .r4 = BitVec.ofNat 64 (w32 s.mem p.B (slot w 0)) ∧
      a.mem = s.mem) ?_ (by decide)) fun a ⟨⟨a4, am⟩, ka⟩ => ?_
  · prun [(kv.gpr .r10 (by decide)).trans h10, hld, vm, BitVec.add_zero]
    rw [BitVec.ofNat_toNat]
  have hS : dsum s.mem p.B (slot w 0) (2 * w) < 2 ^ 64 := by
    have := dsum_le s.mem p.B (slot w 0) (2 * w)
    have : 2 * w * 2 ^ 32 ≤ 256 * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega_using [hw128])
    omega_arith
  refine WP.mono (mod3_ok ((ka.gpr .r3 (by decide)).trans v3) hS) fun b ⟨⟨b3, bm⟩, kb⟩ => ?_
  have hb : St p b := h.step (by rw [bm, am]; exact Frm.refl _ _ _) ((kv.trans ka).trans kb)
  refine WP.mono (WP.keep [.r3, .r4, .r6] (Q := fun t => t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 200)
      ((BitVec.ofNat 64 (dsum s.mem p.B (slot w 0) (2 * w) % 3) ^^^ BitVec.ofNat 64 2) |||
        ((BitVec.ofNat 64 (w32 s.mem p.B (slot w 0)) &&& BitVec.ofNat 64 7) ^^^ BitVec.ofNat 64 3))) ?_ (by decide))
    fun t ⟨tm, kt⟩ => ⟨bad_post tm ?_, (((kv.trans ka).trans kb).trans kt).mono (by decide)⟩
  · simp only [sth, hBad]
    prun [hb.r31, hb.st (d := 200) (by decide), bm, am, b3, (kb.gpr .r4 (by decide)).trans a4]
  · rw [and7, flag2 _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)), ← l8, ← l3]
    omega_using []

/-- Generator 5's branch. -/
theorem residue5_ok {C : Nat} {p : PP} {s : State} (h : St p s) (hp : Ph p p.bits C s) :
    WP isa residue5 s fun t =>
      ((word t.mem p.B (8 * hBad) = 0#64 ↔ wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) % 10 = 3 ∨ wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) % 10 = 7) ∧
        Frm p.B [(8 * hBad, 8)] s.mem t.mem) ∧ Keep resRegs s t := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hn := h.dims.n
  have h10 := hp.r10
  have h11 := hp.r11
  generalize hwd : wOf p.bits = w at h10 h11 ⊢
  have hw8 : 8 ≤ w := by simp only [wOf] at hwd; omega_arith
  have hw128 : w ≤ 128 := by simp only [wOf] at hwd; omega_arith
  have hZ : slot w 0 + 8 * w ≤ p.Z := by simp only [slot, hdrBytes, PP.Z, PP.L] at hn ⊢; omega_arith
  obtain ⟨-, l2, -, l5⟩ := low_sum (m := s.mem) (B := p.B) (o := slot w 0) (by omega_using [hw8] : 1 ≤ w)
  unfold residue5
  refine WP.seq (WP.mono (digitSum_ok h.scr h10 h11 (by omega_using [hw8]) hw128 hZ) fun v ⟨⟨v3, vm⟩, kv⟩ => ?_)
  rw [WP.block_append_iff, WP.block_append_iff]
  have hld : InRegions (v.rd ++ v.wr) (off p.B (slot w 0)) 4 := (h.scr.congr kv.wr).ld (by omega_using [hw8, hZ])
  refine WP.mono (WP.keep [.r4] (Q := fun a => a.gpr .r4 = BitVec.ofNat 64 (w32 s.mem p.B (slot w 0)) ∧
      a.mem = s.mem) ?_ (by decide)) fun a ⟨⟨a4, am⟩, ka⟩ => ?_
  · prun [(kv.gpr .r10 (by decide)).trans h10, hld, vm, BitVec.add_zero]
    rw [BitVec.ofNat_toNat]
  have hS : dsum s.mem p.B (slot w 0) (2 * w) < 2 ^ 64 := by
    have := dsum_le s.mem p.B (slot w 0) (2 * w)
    have : 2 * w * 2 ^ 32 ≤ 256 * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega_using [hw128])
    omega_arith
  refine WP.mono (mod5_ok ((ka.gpr .r3 (by decide)).trans v3) hS) fun b ⟨⟨b3, bm⟩, kb⟩ => ?_
  have hb : St p b := h.step (by rw [bm, am]; exact Frm.refl _ _ _) ((kv.trans ka).trans kb)
  refine WP.mono (WP.keep [.r3, .r4, .r6] (Q := fun t => t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 200)
      (((BitVec.ofNat 64 (dsum s.mem p.B (slot w 0) (2 * w) % 5) ||| BitVec.ofNat 64 1) ^^^ BitVec.ofNat 64 3) |||
        ((BitVec.ofNat 64 (w32 s.mem p.B (slot w 0)) &&& BitVec.ofNat 64 1) ^^^ BitVec.ofNat 64 1))) ?_ (by decide))
    fun t ⟨tm, kt⟩ => ⟨bad_post tm ?_, (((kv.trans ka).trans kb).trans kt).mono (by decide)⟩
  · simp only [sth, hBad]
    prun [hb.r31, hb.st (d := 200) (by decide), bm, am, b3, (kb.gpr .r4 (by decide)).trans a4]
  · rw [and1, flag5 _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)), ← l2, ← l5]
    omega_using []

/-- `residue`: `hBad` zero iff array 0 has the generator's congruence. -/
theorem residue_ok {C : Nat} {p : PP} {s : State} (h : St p s) (hp : Ph p p.bits C s) :
    WP isa residue s fun t =>
      ((word t.mem p.B (8 * hBad) = 0#64 ↔ goodRes p.g (wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits))) ∧
        Frm p.B [(8 * hBad, 8)] s.mem t.mem) ∧ Keep resRegs s t := by
  unfold residue
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 p.g - 2#64 ∧ u.mem = s.mem)
    (by simp only [ldh, hGen]; prun [h.r31, h.ld (d := 128) (by decide), h.args.gen']) (by decide))
    fun u ⟨⟨u3, um⟩, ku⟩ => ?_)
  have hu := h.step (by rw [um]; exact Frm.refl _ _ _) ku
  have hpu : Ph p p.bits C u := hp.keepBad (ku.gpr .r10 (by decide)) (ku.gpr .r11 (by decide))
    (ku.gpr .r29 (by decide)) fun d _ => by rw [um]
  have hwv : wv u.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) := by
    rw [um]
  refine WP.ite (u.gpr .r3 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have hg : p.g = 2 := by
      rcases h.dims.g with hg | hg <;> rw [u3, hg] at hb
      · exact hg
      · exact absurd hb (by decide)
    refine WP.mono (residue2_ok hu hpu) fun t ⟨⟨hb', f⟩, k⟩ => ⟨⟨?_, by rw [← um]; exact f⟩, (ku.trans k).mono (by decide)⟩
    rw [hb', hwv, goodRes, ite_eq_left hg]
  · have hg : p.g = 5 := by
      rcases h.dims.g with hg | hg <;> rw [u3, hg] at hb
      · exact absurd hb (by decide)
      · exact hg
    refine WP.mono (residue5_ok hu hpu) fun t ⟨⟨hb', f⟩, k⟩ => ⟨⟨?_, by rw [← um]; exact f⟩, (ku.trans k).mono (by decide)⟩
    rw [hb', hwv, goodRes, ite_eq_right (by omega_arith)]

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
