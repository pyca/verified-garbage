module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerPre
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.MillerRabin.Keeps
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerSave
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `MillerRabin.X86_64.CallerCall`, which only this module used -/

section

/-! ### `MillerRabin.X86_64.CallerRestore`, which only this module used -/

section

/-! # Restore the workspace and turn the shared result into RSA's mask -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.MillerRabin.X86_64.Caller
open VG.Proof.MlKem.X86_64

private theorem low_result {v : BitVec 64} {p : Bool}
    (h : (v.setWidth 32).toNat = if p then 1 else 0) :
    v.setWidth 32 = BitVec.ofNat 32 p.toNat := by
  apply BitVec.eq_of_toNat_eq
  cases p <;> simpa using h

private theorem negative_result (p : Bool) :
    BitVec.signExtend 64 (0 : BitVec 32) - (BitVec.ofNat 32 p.toNat).setWidth 64 = mask p := by
  cases p <;> decide

private theorem imul_low (a b : BitVec 64) :
    BitVec.ofInt 64 (a.toInt * b.toInt) = a * b := by
  simp only [BitVec.ofInt_mul, BitVec.ofInt_toInt]

theorem restore_ok {s : State} {B old : Addr} {Z w : Nat} {p : Bool}
    (h : Scr s B Z) (hZ : slot w 28 ≤ Z) (hB : s.gpr .rbx = B)
    (hw : word s.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hv : word s.mem B (pad w) = old)
    (hr : ((s.gpr .rax).setWidth 32).toNat = if p then 1 else 0) :
    WP isa (.block restore) s fun t =>
      t.mem = s.mem.writeW (off B (8 * kFlag)) (mask p) ∧ t.gpr .rdi = B ∧ t.gpr .rbx = old ∧
      Keep [.rax, .rbx, .rcx, .rdi] s t := by
  have hf : InRegions s.wr (off B (8 * kFlag)) 8 :=
    h.st (by have := hdr_lt_slot w 28 (show kFlag < 32 by decide); omega_arith)
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sW)) 8 :=
    h.ld (by have := hdr_lt_slot w 28 (show sW < 32 by decide); omega_arith)
  have hp : pad w + 8 ≤ Z := by
    simp only [pad, slot, hdrBytes, aR1] at hZ ⊢
    omega_arith
  have hpL : InRegions (s.rd ++ s.wr) (off B (pad w)) 8 := h.ld hp
  let m := s.mem.writeW (off B (8 * kFlag)) (mask p)
  have ho : Outside B (8 * kFlag) 8 s.mem m := writeW_outside _ _ _ (by decide)
  have hmw : word m B (8 * sW) = BitVec.ofNat 64 w :=
    (ho.word (Or.inl (by decide)) (by decide)).trans hw
  have hmp : word m B (pad w) = old :=
    (ho.word (Or.inr (by simp only [pad, slot, hdrBytes, aR1, kFlag, kPlen, sFn]; omega_arith))
      (by have := h.nowrap; omega_arith)).trans hv
  dsimp only [m, VG.Proof.Bignum.word] at hmw hmp
  have ha : BitVec.signExtend 64 (208 : BitVec 32) * BitVec.ofNat 64 w +
      BitVec.signExtend 64 (656 : BitVec 32) + B = off B (pad w) := by
    change 208#64 * BitVec.ofNat 64 w + 656#64 + B = off B (pad w)
    simp only [pad, slot, hdrBytes, aR1, off]
    bv_omega
  have hb := low_result hr
  have hm := negative_result p
  refine WP.mono (WP.keep [.rax, .rbx, .rcx, .rdi] (c := .block restore)
    (Q := fun t => t.mem = m ∧ t.gpr .rdi = B ∧ t.gpr .rbx = old) ?_ rfl)
    fun t ⟨⟨hmem, hdi, hbx⟩, hk⟩ => ⟨hmem, hdi, hbx, hk⟩
  unfold restore padAddress
  simp only [List.cons_append, List.nil_append]
  xrun [execImul, imul_low, BitVec.add_zero,
    show BitVec.signExtend 64 (208#32) = 208#64 from rfl,
    show BitVec.signExtend 64 (656#32) = 656#64 from rfl,
    show BitVec.signExtend 64 (28#32) = 28#64 from rfl,
    show BitVec.signExtend 64 (88#32) = 88#64 from rfl,
    show BitVec.ofInt 64 0 = 0#64 from rfl, State.ea, hdr, hdrOff, at0, hB, hb, hm, hf, hl, hpL, ha,
    hmw, hmp]
  rfl

end VG.Proof.MillerRabin.X86_64.Caller

end

end


/-! # The actual x86-64 shared call preserves its RSA caller -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.MillerRabin.X86_64.Caller
open VG.Proof.MlKem.X86_64

def callRanges (w : Nat) : List (Nat × Nat) := [(pad w, 8)] ++ mutRanges Proof.MillerRabin.Round.extended w

private theorem outside_mm (r : Reg) (hr : r ∉ mmRegs) : r = .rdi ∨ r = .rsp := by
  cases r <;> simp_all [mmRegs]

private theorem callee_outside {r : Reg} (hr : r ∈ calleeSaved) (hne : r ≠ .rbx) :
    r ∉ [.rax, .rbx, .rcx, .rdx, .rsi] ∧ r ∉ [.rax, .rbx, .rcx, .rdi] := by
  cases r <;> simp_all [calleeSaved]

theorem call_ok (v : RoundImpl) {s : State} {B : Addr} {Z w c bm b : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (he : ECtx s.mem B w c) (hd : MrDims B Z w)
    (hZ : slot w 28 ≤ Z) (hr : Room s B Z)
    (ho : c % 2 = 1) (h3 : 3 ≤ c)
    (hx : wv s.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c) :
    WP isa (call v.name v.code) s fun t =>
      t.gpr .rdi = B ∧ word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round c b) ∧
      WorkFrame B (callRanges w) [below (s.gpr .rsp) 128] s.mem t.mem ∧ Keep mmRegs s t ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) := by
  have hn := hc.good.scr.nowrap
  have hsize := call_size hZ
  have hN : 8 * callWords w ≤ 2 ^ 64 := by omega_arith
  have hpZ : pad w + 8 ≤ 8 * callWords w := by
    simp only [pad, slot, hdrBytes, aR1, callWords]
    omega_arith
  unfold VG.Impl.MillerRabin.X86_64.Caller.call
  refine WP.seq (WP.mono (save_ok hc.good hZ) ?_)
  rintro u ⟨hm, hb, hsi, hskeep⟩
  obtain ⟨hcu, heu⟩ := save_context hc he hd hm hskeep
  have hsp : u.gpr .rsp = s.gpr .rsp := hskeep.gpr (by decide)
  have hru : Room u B Z := by
    exact ⟨by rw [hsp]; exact hr.size, by rw [hsp]; exact hr.disjoint⟩
  have hxu : wv u.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c := by
    rw [hm, (saved_outside s B w (by omega_arith)).wv
      (Or.inl (by simp only [pad, slot, hdrBytes, aR1, aXm]; omega_arith))
      (by have := hd.w128; simp only [slot, hdrBytes, aXm]; omega_arith)]
    exact hx
  refine WP.seq (WP.mono (round_call_ok v hcu heu hd hZ hru hsi ho h3 hxu) ?_)
  rintro t ⟨hcs, hrd, hwr, hf, hv, hk, _⟩
  have htScr := hcu.good.scr.congr hwr
  have htw : word t.mem B (8 * sW) = BitVec.ofNat 64 w :=
    (kept_header hk (by unfold callWords; omega_arith) (by decide) (by decide)).trans hcu.good.hdr.hw
  have htbx : word t.mem B (pad w) = s.gpr .rbx := by
    rw [kept_padding hk hpZ, hm, saved_rbx]
  refine WP.mono (restore_ok htScr hZ ((hcs .rbx (by simp [calleeSaved])).trans hb) htw htbx hv) ?_
  rintro f ⟨hfm, hB, hOld, hfkeep⟩
  have hflag : word f.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round c b) := by
    rw [hfm, word_writeW_self]
  have hfFinal : Frame ([⟨B, 8 * callWords w⟩] ++ [below (s.gpr .rsp) 128]) u.mem f.mem := by
    rw [hsp] at hf
    rw [hfm]
    exact hf.writeW (r := ⟨B, 8 * callWords w⟩) (by simp) _
      (Offset.contains_base B (by simp only [kFlag, kPlen, sFn]; unfold callWords; omega_arith) (by decide))
  have hkFinal : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.extended B (callWords w) w u.mem f.mem := by
    rw [hfm]
    exact keeps_write_flag hk hN (by decide) _
  have hSave : Frm B [(pad w, 8)] s.mem u.mem := by
    rw [hm]
    exact Frm.of_outside (saved_outside s B w (by omega_arith)) (by simp)
  have hFrame : WorkFrame B (callRanges w) [below (s.gpr .rsp) 128] s.mem f.mem :=
    (hSave.work.mono (fun r hr => List.mem_append_left _ hr)).trans
      ((keeps_to_work hkFinal hfFinal).mono (fun r hr => List.mem_append_right _ hr))
  have hSP : f.gpr .rsp = s.gpr .rsp :=
    ((hfkeep.gpr (by decide)).trans (hcs .rsp (by simp [calleeSaved]))).trans hsp
  have hKeep : Keep mmRegs s f := by
    refine ⟨?_, hfkeep.2.1.trans (hrd.trans hskeep.2.1), hfkeep.2.2.trans (hwr.trans hskeep.2.2)⟩
    intro r hr
    rcases outside_mm r hr with rfl | rfl
    · exact hB.trans hc.good.rdi.symm
    · exact hSP
  refine ⟨hB, hflag, hFrame, hKeep, ?_⟩
  intro r hr
  by_cases h : r = .rbx
  · subst r
    exact hOld
  · have hh := callee_outside hr h
    exact ((hfkeep.gpr hh.2).trans (hcs r hr)).trans (hskeep.gpr hh.1)

end VG.Proof.MillerRabin.X86_64.Caller

end

end

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
