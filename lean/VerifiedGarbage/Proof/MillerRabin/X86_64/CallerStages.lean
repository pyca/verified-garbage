module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerBoundaryCT
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerPre
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.MillerRabin.Keeps
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Caller
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

/-! ### `MillerRabin.X86_64.CallerSave`, which this module and modules that import it used -/

section

/-! # Save the shared caller's workspace in a preserved register -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.MillerRabin.X86_64.Caller
open VG.Proof.MlKem.X86_64

def pad (w : Nat) : Nat := slot w aR1 + 8 * w

def savedMem (s : State) (B : Addr) (w : Nat) : Mem :=
  s.mem.writeW (off B (pad w)) (s.gpr .rbx)

theorem saved_outside (s : State) (B : Addr) (w : Nat) (hp : pad w + 8 ≤ 2 ^ 64) :
    Outside B (pad w) 8 s.mem (savedMem s B w) :=
  writeW_outside s.mem B (s.gpr .rbx) hp

theorem saved_rbx (s : State) (B : Addr) (w : Nat) :
    word (savedMem s B w) B (pad w) = s.gpr .rbx := by
  simp only [savedMem, word_writeW_self]

private theorem imul_low (a b : BitVec 64) :
    BitVec.ofInt 64 (a.toInt * b.toInt) = a * b := by
  simp only [BitVec.ofInt_mul, BitVec.ofInt_toInt]

theorem save_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (h : Good s B Z w mi) (hZ : slot w 28 ≤ Z) :
    WP isa (.block save) s fun t =>
      t.mem = savedMem s B w ∧ t.gpr .rbx = B ∧
      t.gpr .rsi = BitVec.ofNat 64 (32 + 28 * (w + 2)) ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi] s t := by
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sW)) 8 :=
    h.scr.ld (by have := hdr_lt_slot w 28 (show sW < 32 by decide); omega_arith)
  have hp : pad w + 8 ≤ Z := by
    simp only [pad, slot, hdrBytes, aR1] at hZ ⊢
    omega_arith
  have hs : InRegions s.wr (off B (pad w)) 8 := h.scr.st hp
  have ha : BitVec.signExtend 64 (208 : BitVec 32) * BitVec.ofNat 64 w +
      BitVec.signExtend 64 (656 : BitVec 32) + B = off B (pad w) := by
    change 208#64 * BitVec.ofNat 64 w + 656#64 + B = off B (pad w)
    simp only [pad, slot, hdrBytes, aR1, off]
    bv_omega
  have hk : BitVec.ofNat 64 w * BitVec.signExtend 64 (28 : BitVec 32) +
      BitVec.signExtend 64 (88 : BitVec 32) = BitVec.ofNat 64 (32 + 28 * (w + 2)) := by
    change BitVec.ofNat 64 w * 28#64 + 88#64 = BitVec.ofNat 64 (32 + 28 * (w + 2))
    bv_omega
  refine WP.mono (WP.keep [.rax, .rbx, .rcx, .rdx, .rsi] (c := .block save)
    (Q := fun t => t.mem = savedMem s B w ∧ t.gpr .rbx = B ∧
      t.gpr .rsi = BitVec.ofNat 64 (32 + 28 * (w + 2))) ?_ rfl)
    fun t ⟨⟨hm, hb, hn⟩, hk⟩ => ⟨hm, hb, hn, hk⟩
  unfold save padAddress
  simp only [List.cons_append, List.nil_append]
  xrun [execImul, imul_low, BitVec.add_zero,
    show BitVec.signExtend 64 (208#32) = 208#64 from rfl,
    show BitVec.signExtend 64 (656#32) = 656#64 from rfl,
    show BitVec.signExtend 64 (28#32) = 28#64 from rfl,
    show BitVec.signExtend 64 (88#32) = 88#64 from rfl,
    show BitVec.ofInt 64 0 = 0#64 from rfl, State.ea, hdr, hdrOff, at0, h.rdi, hl, h.hdr.hw, ha, hs, savedMem, hk]

end VG.Proof.MillerRabin.X86_64.Caller

end

end

/-! ### `MillerRabin.X86_64.CallerKept`, which this module and modules that import it used -/

section

/-! # Recover the caller's header and padding after the prepared round -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.Proof.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

theorem kept_header {B : Addr} {n w j : Nat} {m m' : Mem}
    (h : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.extended B n w m m')
    (hn : 32 ≤ n) (hj : j < 32) (he : j ∉ [22, 26, 27, 28, 31]) :
    word m' B (8 * j) = word m B (8 * j) := by
  apply keeps_word h (by omega_arith)
  · intro k hk
    have hne : j ≠ k := fun hEq => he (hEq ▸ hk)
    omega_arith
  · simp only [Proof.MillerRabin.Round.extended, List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl | rfl | rfl | rfl) <;>
      left <;> simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega_arith
  · left
    simp only [Proof.MillerRabin.Round.extended, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
    omega_arith

theorem kept_padding {B : Addr} {n w : Nat} {m m' : Mem}
    (h : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.extended B n w m m')
    (hn : pad w + 8 ≤ 8 * n) :
    word m' B (pad w) = word m B (pad w) := by
  apply keeps_word h hn
  · simp only [Proof.MillerRabin.Round.extended, List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl | rfl | rfl | rfl) <;>
      right <;> simp only [pad, slot, hdrBytes, aR1] <;> omega_arith
  · simp only [Proof.MillerRabin.Round.extended, List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl | rfl | rfl | rfl)
    all_goals right
    all_goals simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, pad, slot, hdrBytes, aR1]
    all_goals omega_arith
  · right
    simp only [Proof.MillerRabin.Round.extended, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
      pad, slot, hdrBytes, aR1]
    omega_arith

end VG.Proof.MillerRabin.X86_64.Caller

end

end

/-! ### `MillerRabin.X86_64.CallerContext`, which this module and modules that import it used -/

section

/-! # Saving the workspace preserves its mathematical preparation -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.MillerRabin.X86_64.Caller
open VG.Proof.MlKem.X86_64

theorem save_context {s t : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (he : ECtx s.mem B w c) (hd : MrDims B Z w)
    (hm : t.mem = savedMem s B w) (hk : Keep [.rax, .rbx, .rcx, .rdx, .rsi] s t) :
    MrCtx t B Z w mi c bm ∧ ECtx t.mem B w c := by
  have hn := hc.good.scr.nowrap
  have hpad : pad w + 8 ≤ Z := by
    have hz := hd.x
    simp only [pad, slot, hdrBytes, aR1, aRm1] at hz ⊢
    omega_arith
  have hf : Frm B [(pad w, 8)] s.mem t.mem := by
    rw [hm]
    intro x hx
    exact saved_outside s B w (by omega_arith) x (hx (pad w, 8) (by simp))
  refine ⟨hc.of_frm hd hf (hc.good.scr.congr hk.2.2)
    ((hk.gpr (by decide)).trans hc.good.rdi) ?_ ?_ ?_ ?_ ?_,
    he.of_frm hf ?_ (by have := aE_fits hd; omega_arith)⟩
  all_goals
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
  · simp only [pad, slot, hdrBytes, aR1]; omega_arith
  · left; simp only [pad, slot, hdrBytes, aR1, aN]; omega_arith
  · left; simp only [pad, slot, hdrBytes, aR1, aB]; omega_arith
  · left; simp only [pad]; omega_arith
  · right; simp only [pad, slot, hdrBytes, aR1, aRm1]; omega_arith
  · left; simp only [pad, slot, hdrBytes, aR1, aE]; omega_arith

end VG.Proof.MillerRabin.X86_64.Caller

end

end

/-! ### `MillerRabin.X86_64.CallerRound`, which this module and modules that import it used -/

section

/-! # Call the complete shared round with its verified stack frame -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

theorem round_call_ok (v : RoundImpl) {s : State} {B : Addr} {Z w c bm b : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (he : ECtx s.mem B w c) (hd : MrDims B Z w)
    (hZ : slot w 28 ≤ Z) (hr : Room s B Z)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 (callWords w))
    (ho : c % 2 = 1) (h3 : 3 ≤ c)
    (hx : wv s.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c) :
    WP isa (.call v.name v.code) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame ([⟨B, 8 * callWords w⟩] ++ [below (s.gpr .rsp) 128]) s.mem t.mem ∧
      ((t.gpr .rax).setWidth 32).toNat = (if Proof.MillerRabin.Round.round c b then 1 else 0) ∧
      Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.extended B (callWords w) w s.mem t.mem ∧
      t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hvDepth : v.code.x86_64Depth ≤ 120 := v.depth
  have hn := hc.good.scr.nowrap
  have hsize := call_size hZ
  have hN : callWords w < 2 ^ 64 := by have := hd.w128; unfold callWords; omega_arith
  have hxlt : wv s.mem B (slot w aXm) w < c := by
    rw [hx]
    exact Nat.mod_lt _ (by omega_arith)
  obtain ⟨hc₁, _⟩ := entry_context hc he hd hr.disjoint
  have hw := ctx_width hc₁ hd.w128
  have heX : Proof.Rsa.Mont.numAt s.callEntry.mem B w 5 = b % c * 2 ^ (64 * w) % c := by
    rw [VG.Proof.Bignum.X86_64.MontFn.numAt_eq, entry_wv s hn (by
      have hz := hd.x
      simp only [slot, hdrBytes, aRm1] at hz ⊢
      omega_arith) hr.disjoint]
    exact hx
  obtain ⟨hcov, hwr⟩ := narrow_covers hc.good.scr hZ
  refine WP.call_sp_mx (s := s) (c := v.code) (rd := []) (wr := [⟨B, 8 * callWords w⟩]) (k := roundContract) v.correct
    (SpSafe.of_all v.spSafe) (by omega_arith)
    (narrow_pre hc he hd hZ hr hsi ho h3 hxlt) hcov hwr ?_
  rintro t hrd hwt hcs hf _ ⟨u, hmu, hgu, hp⟩ hmx
  have hf' : Frame ([⟨B, 8 * callWords w⟩] ++ [below (s.gpr .rsp) 128]) s.mem t.mem :=
    Frame.below_mono hf (by omega_arith) (by decide)
  have hBase : (narrowed s B w).gpr .rdi = B := by
    change s.callEntry.gpr .rdi = B
    rw [State.callEntry_gpr _ (by decide)]
    exact hc.good.rdi
  have hLen : ((narrowed s B w).gpr .rsi).toNat = callWords w := by
    change (s.callEntry.gpr .rsi).toNat = callWords w
    rw [State.callEntry_gpr _ (by decide), hsi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN]
  have hWidth : Proof.Rsa.Mont.wOf (narrowed s B w).mem B = w := hw
  have hMod : Proof.Rsa.Mont.numAt (narrowed s B w).mem B w 0 = c :=
    (VG.Proof.Bignum.X86_64.MontFn.numAt_eq _ _ _ _).trans hc₁.n
  change roundPost (narrowed s B w) u at hp
  dsimp only [roundPost] at hp
  rw [hBase, hLen, hWidth, hMod, hmu] at hp
  have hrx := hp.1 b heX
  rw [hgu .rax (by decide)] at hrx
  refine ⟨hcs, hrd, hwt, hf', hrx, ?_, hmx⟩
  intro i hi hh ha ht
  exact (hp.2 i hi hh ha ht).trans (entry_byte s hn (by omega_arith) hr.disjoint)

end VG.Proof.MillerRabin.X86_64.Caller

end

end

/-! # Contexts before and after the actual shared round call -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.MillerRabin.X86_64.Caller

structure Public where
  ws : Ws
  sp : Addr

def Before (L : Public) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (c bm b : Nat),
    MrCtx s L.ws.B L.ws.Z L.ws.w mi c bm ∧ ECtx s.mem L.ws.B L.ws.w c ∧
    MrDims L.ws.B L.ws.Z L.ws.w ∧ slot L.ws.w 28 ≤ L.ws.Z ∧
    Room s L.ws.B L.ws.Z ∧ s.gpr .rsp = L.sp ∧ c % 2 = 1 ∧ 3 ≤ c ∧
    wv s.mem L.ws.B (slot L.ws.w aXm) L.ws.w = b % c * 2 ^ (64 * L.ws.w) % c

def Ready (L : Public) (s : State) : Prop :=
  Before L s ∧ s.gpr .rbx = L.ws.B ∧ s.gpr .rsi = BitVec.ofNat 64 (callWords L.ws.w)

theorem before_save {L : Public} {s : State} (h : Before L s) : SavePre L.ws s := by
  obtain ⟨mi, c, bm, b, hc, _, _, hz, _⟩ := h
  exact ⟨mi, hc.good, hz⟩

theorem save_ready {L : Public} {s : State} (h : Before L s) :
    WP isa (.block save) s (Ready L) := by
  obtain ⟨mi, c, bm, b, hc, he, hd, hz, hr, hsp, ho, h3, hx⟩ := h
  refine WP.mono (save_ok hc.good hz) ?_
  rintro t ⟨hm, hb, hn, hk⟩
  obtain ⟨hct, het⟩ := save_context hc he hd hm hk
  have hts : t.gpr .rsp = s.gpr .rsp := hk.gpr (by decide)
  have hrt : Room t L.ws.B L.ws.Z := ⟨by rw [hts]; exact hr.size,
    by rw [hts]; exact hr.disjoint⟩
  refine ⟨⟨mi, c, bm, b, hct, het, hd, hz, hrt, hts.trans hsp, ho, h3, ?_⟩, hb, hn⟩
  have hp : pad L.ws.w + 8 ≤ 2 ^ 64 := by
    have hs := hc.good.scr.nowrap
    simp only [pad, slot, hdrBytes, aR1] at hz ⊢
    omega_arith
  rw [hm, (saved_outside s L.ws.B L.ws.w hp).wv (Or.inl (by
    simp only [pad, slot, hdrBytes, aR1, aXm]; omega_arith)) (by
      have hs := hc.good.scr.nowrap
      simp only [slot, hdrBytes, aXm] at hz ⊢
      omega_arith)]
  exact hx

theorem ready_pre {L : Public} {s : State} (h : Ready L s) :
    roundPre (narrowed s L.ws.B L.ws.w) := by
  obtain ⟨⟨mi, c, bm, b, hc, he, hd, hz, hr, hsp, ho, h3, hx⟩, hb, hn⟩ := h
  apply narrow_pre hc he hd hz hr hn ho h3
  rw [hx]
  exact Nat.mod_lt _ (by omega_arith)

theorem ready_covers {L : Public} {s : State} (h : Ready L s) :
    Covers ([] ++ [⟨L.ws.B, 8 * callWords L.ws.w⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨L.ws.B, 8 * callWords L.ws.w⟩] s.wr := by
  obtain ⟨⟨mi, c, bm, b, hc, _, _, hz, _⟩, _⟩ := h
  exact narrow_covers hc.good.scr hz

theorem call_restore_pre (v : RoundImpl) {L : Public} {s : State} (h : Ready L s) :
    WP isa (.call v.name v.code) s (RestorePre L.ws) := by
  obtain ⟨⟨mi, c, bm, b, hc, he, hd, hz, hr, hsp, ho, h3, hx⟩, hb, hn⟩ := h
  refine WP.mono (round_call_ok v hc he hd hz hr hn ho h3 hx) ?_
  rintro t ⟨hcs, hrd, hwr, hf, hresult, hkeep, hmx⟩
  refine ⟨hc.good.scr.congr hwr, hz, (hcs .rbx (by decide)).trans hb, ?_⟩
  exact (kept_header hkeep (by unfold callWords; omega_arith) (by decide) (by decide)).trans hc.good.hdr.hw

end VG.Proof.MillerRabin.X86_64.Caller
