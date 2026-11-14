module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerCall
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerEntry
import VerifiedGarbage.Proof.MillerRabin.X86_64.Prepared
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! ### `MillerRabin.X86_64.CallerResult`, which only this module used -/

section

/-! # Reuse the Montgomery context after the actual shared round call -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.MillerRabin.X86_64.Caller
open VG.Proof.MlKem.X86_64

private theorem call_header (w j : Nat) (hj : j < 16) :
    ∀ r ∈ callRanges w, 8 * j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * j := by
  simp only [callRanges, mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, pad, slot, hdrBytes, aR1,
    Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  and_intros <;> left <;> omega_arith

private theorem call_array (w j : Nat) (hj : j ∈ [0, 24, 25, 26]) :
    ∀ r ∈ callRanges w, slot w j + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl
  all_goals
    simp only [callRanges, mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, pad, slot, hdrBytes, aR1,
      Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
    and_intros <;> omega_arith

private theorem call_exponent (w : Nat) :
    ∀ r ∈ callRanges w, slot w aE + 8 * (w + 1) ≤ r.1 ∨ r.1 + r.2 ≤ slot w aE := by
  simp only [callRanges, mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, pad, slot, hdrBytes, aR1, aE,
    Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  and_intros <;> omega_arith

theorem call_result_ok (v : RoundImpl) {s : State} {B : Addr} {Z w c bm b : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (he : ECtx s.mem B w c) (hd : MrDims B Z w)
    (hZ : slot w 28 ≤ Z) (hr : Room s B Z)
    (ho : c % 2 = 1) (h3 : 3 ≤ c)
    (hx : wv s.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c) :
    WP isa (call v.name v.code) s fun t =>
      (∃ bm', MrCtx t B Z w mi c bm') ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round c b) ∧
      WorkFrame B (callRanges w) [below (s.gpr .rsp) 128] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.good.scr.nowrap
  have hz := hZ
  refine WP.mono (call_ok v hc he hd hZ hr ho h3 hx) ?_
  rintro t ⟨hdi, hflag, hf, hk, _⟩
  have hext : ∀ r ∈ [below (s.gpr .rsp) 128], Region.Disjoint ⟨B, Z⟩ r := by
    intro r h
    simp only [List.mem_singleton] at h
    subst r
    exact hr.disjoint
  have hHdr : ∀ j < 16, word t.mem B (8 * j) = word s.mem B (8 * j) := by
    intro j hj
    exact hf.word_eq (d := 8 * j) (call_header w j hj) (by
      have hh := hdr_lt_slot w 28 (by omega_arith : j < 32)
      omega_arith) hn hext
  have hArr : ∀ j ∈ [0, 24, 25, 26], wv t.mem B (slot w j) w = wv s.mem B (slot w j) w := by
    intro j hj
    apply hf.wv_eq (d := slot w j) (call_array w j hj) ?_ hn hext
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;>
      simp only [slot, hdrBytes] at hz ⊢ <;> omega_arith
  have hg : Good t B Z w mi := ⟨hc.good.scr.congr hk.2.2, hdi,
    ⟨(hHdr sW (by decide)).trans hc.good.hdr.hw,
      (hHdr sMinv (by decide)).trans hc.good.hdr.hminv,
      fun j hj => (hHdr (sArr j) (by unfold sArr; omega_arith)).trans (hc.good.hdr.harr j hj)⟩⟩
  refine ⟨⟨wv t.mem B (slot w aB) w, ⟨hg, ?_, (hArr aN (by simp [aN])).trans hc.n, rfl,
    (hArr aR1 (by simp [aR1])).trans hc.r1, (hArr aRm1 (by simp [aRm1])).trans hc.rm1⟩⟩,
    ⟨(hArr aE (by simp [aE])).trans he.e, ?_⟩, hflag, hf, hk⟩
  · rw [hf.word_eq (d := slot w aN) (fun r hr => by
      have hh := call_array w 0 (by simp) r hr
      have := hd.w4
      simpa only [aN] using hh.imp (fun h => by omega_arith) id) (by
        simp only [slot, hdrBytes, aN] at hz ⊢; omega_arith) hn hext]
    exact hc.inv
  · rw [hf.word_eq (d := slot w aE + 8 * w) (fun r hr => by
      have hh := call_exponent w r hr
      omega_arith) (by simp only [slot, hdrBytes, aE] at hz ⊢; omega_arith) hn hext]
    exact he.l

end VG.Proof.MillerRabin.X86_64.Caller

end

end

/-! ### `MillerRabin.X86_64.CallerCT`, which only this module used -/

section

/-! # Constant time of the complete shared-round caller -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.MillerRabin.X86_64.Caller

private theorem ready_base {L : Public} {s : State} (h : Ready L s) :
    s.gpr .rdi = L.ws.B := by
  obtain ⟨⟨mi, c, bm, b, hc, _⟩, _⟩ := h
  exact hc.good.rdi

private theorem ready_sp {L : Public} {s : State} (h : Ready L s) :
    s.gpr .rsp = L.sp := by
  obtain ⟨⟨mi, c, bm, b, hc, he, hd, hz, hr, hsp, _⟩, _⟩ := h
  exact hsp

private theorem ready_width {L : Public} {s : State} (h : Ready L s) :
    Proof.Rsa.Mont.wOf (narrowed s L.ws.B L.ws.w).mem L.ws.B = L.ws.w := by
  obtain ⟨⟨mi, c, bm, b, hc, he, hd, hz, hr, _⟩, _⟩ := h
  obtain ⟨hce, _⟩ := entry_context hc he hd hr.disjoint
  change Proof.Rsa.Mont.wOf s.callEntry.mem L.ws.B = L.ws.w
  exact ctx_width hce hd.w128

private theorem ready_pub {L : Public} {s t : State} (hs : Ready L s) (ht : Ready L t) :
    roundPub (narrowed s L.ws.B L.ws.w) (narrowed t L.ws.B L.ws.w) := by
  have hbs : (narrowed s L.ws.B L.ws.w).gpr .rdi = L.ws.B :=
    (s.callEntry_gpr (by decide)).trans (ready_base hs)
  have hbt : (narrowed t L.ws.B L.ws.w).gpr .rdi = L.ws.B :=
    (t.callEntry_gpr (by decide)).trans (ready_base ht)
  have hns : (narrowed s L.ws.B L.ws.w).gpr .rsi = BitVec.ofNat 64 (callWords L.ws.w) :=
    (s.callEntry_gpr (by decide)).trans hs.2.2
  have hnt : (narrowed t L.ws.B L.ws.w).gpr .rsi = BitVec.ofNat 64 (callWords L.ws.w) :=
    (t.callEntry_gpr (by decide)).trans ht.2.2
  refine ⟨?_, hbs.trans hbt.symm, hns.trans hnt.symm, ?_⟩
  · change s.callEntry.gpr .rsp = t.callEntry.gpr .rsp
    rw [State.callEntry_rsp, State.callEntry_rsp, ready_sp hs, ready_sp ht]
  · rw [hbs, hbt]
    exact (ready_width hs).trans (ready_width ht).symm

private theorem prepared_call_ct (v : RoundImpl) :
    RelCT isa (Two Ready) (.call v.name v.code) fun _ _ => True := by
  apply RelCT.callEx (k := roundContract) v.correct v.ct
  rintro s t ⟨L, hs, ht⟩
  have hcs := ready_covers hs
  have hct := ready_covers ht
  exact ⟨[], [⟨L.ws.B, 8 * callWords L.ws.w⟩], [], [⟨L.ws.B, 8 * callWords L.ws.w⟩],
    ready_pre hs, ready_pre ht, ready_pub hs ht, hcs.1, hcs.2, hct.1, hct.2,
    (ready_sp hs).trans (ready_sp ht).symm⟩

theorem call_ct (v : RoundImpl) :
    RelCT isa (Two Before) (call v.name v.code) fun _ _ => True := by
  unfold VG.Impl.MillerRabin.X86_64.Caller.call
  refine RelCT.seq (two_post (Ψ := Ready) ?_ (fun _ _ h => save_ready h)) ?_
  · exact two_map Public.ws (fun _ _ h => before_save h) save_ct
  · exact RelCT.seq (two_post (prepared_call_ct v) (fun _ _ h => call_restore_pre v h))
      (two_map Public.ws (fun _ _ h => h) restore_ct)

end VG.Proof.MillerRabin.X86_64.Caller

end

end


/-! # A callable prepared round for generic RSA and FFDH policies -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.MlKem.X86_64 (Keep)

/-- A prepared round, including the memory below the caller's stack pointer
that its actual call may modify. The Montgomery context remains reusable. -/
structure Kernel where
  run : Prog isa
  ok : ∀ {s : State} {B : Addr} {Z w c bm b : Nat} {mi : BitVec 64},
    MrCtx s B Z w mi c bm → ECtx s.mem B w c → MrDims B Z w → slot w 28 ≤ Z →
    Caller.Room s B Z → c % 2 = 1 → 3 ≤ c →
    wv s.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c →
    WP isa run s fun t =>
      (∃ bm', MrCtx t B Z w mi c bm') ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round c b) ∧
      WorkFrame B (Caller.callRanges w) [below (s.gpr .rsp) 128] s.mem t.mem ∧
      Keep mmRegs s t
  ct : RelCT isa (Two Caller.Before) run fun _ _ => True

/-- Use the selected Montgomery backend's shared Miller–Rabin entry point. -/
def Kernel.called (v : RoundImpl) : Kernel where
  run := VG.Impl.MillerRabin.X86_64.Caller.call v.name v.code
  ok := by exact Caller.call_result_ok v
  ct := by exact Caller.call_ct v

end VG.Proof.MillerRabin.X86_64
