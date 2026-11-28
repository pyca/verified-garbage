module

-- separate module: the contract's precondition and verify's correctness, kept apart from its constant-time proof

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopMain
public import VerifiedGarbage.Spec.SlhDsa.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.SlhDsa.X86_64.KeyGen
import VerifiedGarbage.Proof.SlhDsa.X86_64.ForsLeaf
import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopPro

/-!
# SLH-DSA (SHAKE) on x86-64, `verify`: correctness

Untrusted: everything here is checked by Lean. The precondition of
`verifyContract p X86_64.abi (st + 80)`, spelled out (`VPre`); the run's
layout (`vlay`); `slh_verify` as the code computes it (`verify_eq`); and
`verify` returning it, keeping the calling convention (`verify_wp`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.VerifyTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_mov32i ea_at)

section
variable (p : Params) (st : Nat) (s : State)

abbrev vPk : Region := ⟨s.gpr .rdi, p.pkLen⟩
abbrev vMsg : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
abbrev vCtx : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
abbrev vSig : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
abbrev vArgs : Region := ⟨stackArgAddr s 0, 16⟩
abbrev vScr : Region := ⟨stackArg s 1, scratchWords * 8⟩
abbrev vRet : Region := ⟨s.gpr .rsp, 8⟩
abbrev vStk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 (st + 80), st + 80⟩

end

/-- The precondition of `verifyContract p X86_64.abi (st + 80)`. -/
structure VPre (p : Params) (st : Nat) (s : State) : Prop where
  sp : st + 80 ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64
  rd : s.rd = [vPk p s, vMsg s, vCtx s, vSig s, vArgs s]
  wr : s.wr = [vScr s]
  pkScr : (vPk p s).Disjoint (vScr s)
  msgScr : (vMsg s).Disjoint (vScr s)
  ctxScr : (vCtx s).Disjoint (vScr s)
  sigScr : (vSig s).Disjoint (vScr s)
  scrArgs : (vScr s).Disjoint (vArgs s)
  retPk : (vRet s).Disjoint (vPk p s)
  retMsg : (vRet s).Disjoint (vMsg s)
  retCtx : (vRet s).Disjoint (vCtx s)
  retSig : (vRet s).Disjoint (vSig s)
  retScr : (vRet s).Disjoint (vScr s)
  retArgs : (vRet s).Disjoint (vArgs s)
  stkPk : (vStk st s).Disjoint (vPk p s)
  stkMsg : (vStk st s).Disjoint (vMsg s)
  stkCtx : (vStk st s).Disjoint (vCtx s)
  stkSig : (vStk st s).Disjoint (vSig s)
  stkScr : (vStk st s).Disjoint (vScr s)
  stkArgs : (vStk st s).Disjoint (vArgs s)
  nPk : (s.gpr .rdi).toNat + p.pkLen ≤ 2 ^ 64
  nMsg : (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  nCtx : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  nSig : (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  nScr : (stackArg s 1).toNat + scratchWords * 8 ≤ 2 ^ 64

theorem vPre_of {p : Params} {st : Nat} {s : State} (h : (verifyContract p X86_64.abi (st + 80)).pre s) :
    VPre p st s := by
  rw [show st + 80 = (st + 79) + 1 from rfl] at h
  sig_pre [verifyContract, verifySig, X86_64.abi, X86_64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26⟩

/-- The layout of a run of `verify` from `s`, whose calls take `st` bytes of stack. -/
def vlay (p : Params) (st : Nat) (s : State) : VL where
  B := s.gpr .rsp - BitVec.ofNat 64 (st + 80)
  st := st
  S := stackArg s 1
  pk := s.gpr .rdi
  msg := s.gpr .rsi
  len := s.gpr .rdx
  ctx := s.gpr .rcx
  ctxLen := s.gpr .r8
  sig := s.gpr .r9
  sigL := (stackArg s 0).toNat
  n := p.n

theorem vlay_ret (p : Params) (st : Nat) (s : State) :
    (vlay p st s).B + BitVec.ofNat 64 (st + 80) = s.gpr .rsp := by
  simp only [vlay, BitVec.sub_add_cancel]

theorem vlay_args (p : Params) (st : Nat) (s : State) :
    (vlay p st s).B + BitVec.ofNat 64 (st + 88) = stackArgAddr s 0 := by
  rw [show st + 88 = (st + 80) + 8 by omega, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, vlay_ret]; rfl

theorem vlay_ok {p : Params} (hp : VPar p) {st : Nat} {s : State} (h : VPre p st s) (h8 : (s.gpr .r8).toNat < 256)
    (hst : 16 ≤ st) (hst62 : st < 2 ^ 62) : (vlay p st s).Ok := by
  have hpk := hp.pk
  have eRet : (vlay p st s).RET = vRet s := by
    show (⟨(vlay p st s).B + BitVec.ofNat 64 (st + 80), 8⟩ : Region) = _; rw [vlay_ret]
  have eArgs : (vlay p st s).ARGS = vArgs s := by
    show (⟨(vlay p st s).B + BitVec.ofNat 64 (st + 88), 16⟩ : Region) = _; rw [vlay_args]
  have ePk : (vlay p st s).PK = vPk p s := by show (⟨s.gpr .rdi, 2 * p.n⟩ : Region) = ⟨s.gpr .rdi, p.pkLen⟩; rw [hpk]
  have hB : (vlay p st s).B.toNat = (s.gpr .rsp).toNat - (st + 80) := toNat_sub_ofNat h.sp
  refine ⟨by rw [hB]; show _ + st + 104 ≤ _; have := h.sp2; have := h.sp; omega, hst62, hst, h.nScr,
    by show _ + 2 * p.n ≤ _; rw [← hpk]; exact h.nPk, h.nMsg, h.nCtx, h.nSig, h8, hp.n,
    by rw [ePk]; exact h.pkScr.symm, h.msgScr.symm, h.ctxScr.symm, h.sigScr.symm, by rw [eArgs]; exact h.scrArgs,
    by rw [ePk]; exact h.stkPk, h.stkMsg, h.stkCtx, h.stkSig, h.stkScr,
    by rw [eRet]; exact h.retScr, by rw [eRet, ePk]; exact h.retPk, by rw [eRet]; exact h.retMsg,
    by rw [eRet]; exact h.retCtx, by rw [eRet]; exact h.retSig⟩

theorem bytesAt_drop' (m : Mem) (a : Addr) {k L : Nat} (h : k ≤ L) :
    (bytesAt m a L).drop k = bytesAt m (a + BitVec.ofNat 64 k) (L - k) := by
  have e := KeyGen.bytesAt_add m a k (L - k)
  rw [Nat.add_sub_cancel' h] at e
  rw [e, List.drop_left' (bytesAt_len _ _ _)]

theorem toByte_one {c : Nat} (_h : c < 256) : toByte c 1 = [BitVec.ofNat 8 c] := by
  simp [toByte]

/-- `slh_verify` of a run's inputs, as the code computes it. -/
theorem verify_eq {p : Params} (hp : VPar p) {st : Nat} {s : State} (h8 : (s.gpr .r8).toNat < 256)
    (hsl : (stackArg s 0).toNat = p.sigLen) :
    verify p (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) (bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)
      (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) (bytesAt s.mem (s.gpr .rdi) p.pkLen) =
      vOk p (vlay p st s) s.mem := by
  have hn := hp.n
  have hsg := hp.sigLen
  have hpk := hp.pk
  unfold verify formatMessage
  have h255 : ¬ (s.gpr .r8).toNat > 255 := by omega
  simp only [bytesAt_len, h255, ↓reduceIte]
  rw [verifyInternal_eq hp _ _ _ (by rw [bytesAt_len, hsl])]
  rw [hsl, bytesAt_take' _ _ (by omega), bytesAt_drop_take _ _ (by omega), bytesAt_drop' _ _ (by omega), hpk,
    show 2 * p.n = 2 * p.n from rfl, KeyGen.chunk_bytesAt _ _ (show 0 < 2 by decide),
    KeyGen.chunk_bytesAt _ _ (show 1 < 2 by decide), toByte_one h8,
    show toByte 0 1 = [0] from rfl]
  simp only [vOk, vDigest, hIn, sigHt, vlay, List.append_assoc, Nat.mul_zero, Nat.mul_one, List.cons_append,
    List.nil_append]
  rw [show p.sigLen - (p.n + p.forsSigLen) = p.d * p.xmssSigLen by omega]
  simp

/-! ## The frame's push -/

theorem vlay_sp {p : Params} {st : Nat} (s : State) (hst : 16 ≤ st) :
    (vlay p st s).SP = s.gpr .rsp - BitVec.ofNat 64 72 := by
  rw [Offset.sub_ofNat_eq (s.gpr .rsp) (a := 72) (b := st + 80) (by omega)]
  show s.gpr .rsp - BitVec.ofNat 64 (st + 80) + BitVec.ofNat 64 (st + 8) = _
  congr 2

theorem vlay_slot {p : Params} {st : Nat} (s : State) {j : Nat} (hj : j < 9) :
    (vlay p st s).SP + BitVec.ofNat 64 (8 * j) = s.gpr .rsp - BitVec.ofNat 64 (8 * (8 - j + 1)) := by
  rw [Offset.sub_ofNat_eq (s.gpr .rsp) (a := 8 * (8 - j + 1)) (b := st + 80) (by omega)]
  show s.gpr .rsp - BitVec.ofNat 64 (st + 80) + BitVec.ofNat 64 (st + 8) + BitVec.ofNat 64 (8 * j) = _
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2; omega

/-- The registers just before the push. -/
abbrev VMov (s s₃ : State) : Prop :=
  s₃.gpr .r10 = stackArg s 0 ∧ s₃.gpr .r11 = stackArg s 1 ∧ s₃.gpr .rax = 0 ∧
    (∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .rax → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr

theorem pushed_ok {p : Params} (hp : VPar p) {st : Nat} {s s₃ : State} (h : VPre p st s) (hst : 16 ≤ st)
    (hm : VMov s s₃) :
    Pushed (vlay p st s) s₃.gpr s.mem (pushed Impl.SlhDsa.X86_64.Verify.verifyRegs s₃) := by
  obtain ⟨h10, h11, hax, hg, hm₃, hr₃, hw₃⟩ := hm
  have hsp : s₃.gpr .rsp = s.gpr .rsp := hg _ (by decide) (by decide) (by decide)
  have hn : 8 * Impl.SlhDsa.X86_64.Verify.verifyRegs.length ≤ (s₃.gpr .rsp).toNat := by
    rw [hsp]; have := h.sp; simp only [Impl.SlhDsa.X86_64.Verify.verifyRegs, List.length_cons, List.length_nil]; omega
  obtain ⟨hf, hw⟩ := pushRegs_mem s₃ Impl.SlhDsa.X86_64.Verify.verifyRegs (by decide) hn
  have hpk := hp.pk
  refine ⟨?_, ?_, ?_, fun r hr => pushed_gpr _ _ hr, by rw [hg _ (by decide) (by decide) (by decide)]; rfl, ?_, ?_⟩
  · rw [pushed_rd, hr₃, h.rd]
    show _ = [(⟨s.gpr .rdi, 2 * p.n⟩ : Region), _, _, _, (vlay p st s).ARGS]
    rw [← hpk]
    show _ = [_, _, _, _, (⟨(vlay p st s).B + BitVec.ofNat 64 (st + 88), 16⟩ : Region)]
    rw [vlay_args]; rfl
  · rw [pushed_wr, hw₃, h.wr, hsp]
    show _ = (⟨(vlay p st s).SP, 72⟩ : Region) :: _
    rw [vlay_sp s hst]; rfl
  · rw [pushed_rsp, hsp, vlay_sp s hst]; rfl
  · intro j hj
    rw [vlay_slot s hj, ← hsp]
    show (pushRegs s₃ _).mem.readW _ 64 = _
    rw [hw (8 - j) (by simp [Impl.SlhDsa.X86_64.Verify.verifyRegs]; omega)]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Impl.SlhDsa.X86_64.Verify.verifyRegs, VL.vals, vlay, h10, h11, hax, hg]
  · rw [hm₃] at hf
    show Frame _ s.mem (pushRegs s₃ _).mem
    refine hf.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨(vlay p st s).STK, by simp, ?_⟩
    rw [hsp]
    exact Offset.sub_below (a := 72) (n := 72) (b := st + 80) (m := st + 80) _ (by omega) (by omega)

/-! ## `verify` -/

/-- What `verify` leaves, but MXCSR. -/
def VPost (p : Params) (s s' : State) : Prop :=
  gprPreserved s s' ∧ (s'.gpr .rax).setWidth 32 =
    if verify p (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) (bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)
      (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) (bytesAt s.mem (s.gpr .rdi) p.pkLen) then 1 else 0

theorem stackArgAddr_eq (s : State) (i : Nat) : stackArgAddr s i = s.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1)) := rfl

theorem verify_wp {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T4 : Thash4Impl p.n) (ht : f.t4 = T4.code)
    (hp : VPar p) (hmx : (Impl.SlhDsa.X86_64.Verify.forsPk p f).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsp : NoSp (Impl.SlhDsa.X86_64.Verify.forsPk p f)) (gv : Impl.SlhDsa.X86_64.Verify.VFns) {st : Nat}
    (hst : T4.stack + 16 ≤ st) (hst62 : st < 2 ^ 62) {s : State} (h : VPre p st s) :
    WP isa (Impl.SlhDsa.X86_64.Verify.verify p f gv) s (VPost p s) := by
  have hst16 : 16 ≤ st := by omega
  have hsl := hp.sigLen
  have hin : ∀ {d : Nat}, 8 ≤ d → d + 8 ≤ 24 → InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 d) 8 :=
    fun {d} hd8 hd =>
    ⟨vArgs s, by rw [h.rd]; simp, by
      rw [show s.gpr .rsp + BitVec.ofNat 64 d = stackArgAddr s 0 + BitVec.ofNat 64 (d - 8) by
        rw [stackArgAddr_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
      exact Offset.contains_base _ (by omega) (by omega)⟩
  have hsl31 := hp.sigLt
  unfold Impl.SlhDsa.X86_64.Verify.verify
  refine WP.seq ?_
  refine wp_movm (a := s.gpr .rsp + BitVec.ofNat 64 8) (by rw [ea_stk]) (hin (by omega) (by omega)) fun s₁ u₁ => ?_
  refine wp_movm (a := s.gpr .rsp + BitVec.ofNat 64 16) (by rw [ea_stk, u₁.other _ (by decide)])
    (by rw [u₁.rd, u₁.wr]; exact hin (by omega) (by omega)) fun s₂ u₂ => ?_
  refine wp_mov32i fun s₃ u₃ => Fors.wp_cmpiC fun s₄ g₄ m₄ r₄ w₄ z₄ c₄ => WP.block_nil ?_
  have hm₄ : s₄.mem = s.mem := by rw [m₄, u₃.mem, u₂.mem, u₁.mem]
  have hr₄ : s₄.rd = s.rd := by rw [r₄, u₃.rd, u₂.rd, u₁.rd]
  have hw₄ : s₄.wr = s.wr := by rw [w₄, u₃.wr, u₂.wr, u₁.wr]
  have hg₄ : ∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .rax → s₄.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [g₄, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have h10 : s₄.gpr .r10 = stackArg s 0 := by
    rw [g₄, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl
  have h11 : s₄.gpr .r11 = stackArg s 1 := by
    rw [g₄, u₃.other _ (by decide), u₂.gpr, u₁.mem]; rfl
  have hax : s₄.gpr .rax = 0 := by rw [g₄, u₃.gpr]; rfl
  have hcs : ∀ r ∈ calleeSaved, r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .rax := fun r hr => by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  -- the result 0, before the frame
  have zero : ∀ t : State, t.gpr = s₄.gpr → t.mem = s.mem → verify p (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
      (bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat) (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
      (bytesAt s.mem (s.gpr .rdi) p.pkLen) = false → VPost p s t := fun t hg hm hv => by
    refine ⟨⟨fun r hr => by rw [hg, hg₄ r (hcs r hr).1 (hcs r hr).2.1 (hcs r hr).2.2], by rw [hm]⟩, ?_⟩
    rw [hv, hg, hax]; rfl
  have hr8 : (BitVec.signExtend 64 (256 : BitVec 32)).toNat = 256 := by decide
  rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hr8] at c₄
  refine WP.ite (decide ((s.gpr .r8).toNat < 256)) (by rw [ForsCT.eval_b', c₄]) (fun hb => ?_) (fun hb => ?_)
  rotate_left
  · refine WP.block_nil (zero s₄ rfl hm₄ ?_)
    have h8 : ¬ (s.gpr .r8).toNat < 256 := by simpa using hb
    have h255 : (s.gpr .r8).toNat > 255 := by omega
    simp only [verify, formatMessage, bytesAt_len, h255, ↓reduceIte]
  have h8 : (s.gpr .r8).toNat < 256 := by simpa using hb
  refine WP.seq (Fors.wp_cmpiC fun s₅ g₅ m₅ r₅ w₅ z₅ _ => WP.block_nil ?_)
  rw [h10, Levels.sx_ofNat hsl31] at z₅
  refine WP.ite (decide (stackArg s 0 = BitVec.ofNat 64 p.sigLen)) (by
    rw [ForsCT.eval_e', z₅]; congr 1
    by_cases e : stackArg s 0 = BitVec.ofNat 64 p.sigLen
    · simp [e]
    · have : stackArg s 0 - BitVec.ofNat 64 p.sigLen ≠ 0 := fun h0 => e (by
        have := BitVec.sub_add_cancel (stackArg s 0) (BitVec.ofNat 64 p.sigLen)
        rw [h0] at this; simpa using this.symm)
      simp [e]; exact this) (fun hb2 => ?_) (fun hb2 => ?_)
  rotate_left
  · refine WP.block_nil (zero s₅ g₅ (by rw [m₅, hm₄]) ?_)
    have e : stackArg s 0 ≠ BitVec.ofNat 64 p.sigLen := by simpa using hb2
    have e' : (stackArg s 0).toNat ≠ p.sigLen := fun h' => e (by
      apply BitVec.eq_of_toNat_eq; rw [h', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    have h255 : ¬ (s.gpr .r8).toNat > 255 := by omega
    simp only [verify, formatMessage, bytesAt_len, h255, ↓reduceIte, verifyInternal, e', ne_eq, not_false_eq_true]
  -- the frame
  have hsg : (stackArg s 0).toNat = p.sigLen := by
    have e : stackArg s 0 = BitVec.ofNat 64 p.sigLen := by simpa using hb2
    rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hL := vlay_ok hp h h8 hst16 hst62
  have hmov : VMov s s₅ := ⟨by rw [g₅, h10], by rw [g₅, h11], by rw [g₅, hax],
    fun r h1 h2 h3 => by rw [g₅, hg₄ r h1 h2 h3], by rw [m₅, hm₄], by rw [r₅, hr₄], by rw [w₅, hw₄]⟩
  have hsp₅ : s₅.gpr .rsp = s.gpr .rsp := hmov.2.2.2.1 _ (by decide) (by decide) (by decide)
  refine WP.frame (by decide) (by decide) (by decide) (by
    rw [hsp₅]; have := h.sp; simp only [Impl.SlhDsa.X86_64.Verify.verifyRegs, List.length_cons, List.length_nil]; omega) ?_
  refine WP.mono (body_ok T4 ht hp hmx hsp hst hL rfl hsg gv (pushed_ok hp h hst16 hmov)) fun s₆ tp => ?_
  refine ⟨by rw [tp.rsp, pushed_rsp, hsp₅, vlay_sp s hst16]; rfl, ?_, fun m u fm => ?_⟩
  · rw [tp.wr, pushed_wr, hsp₅, hmov.2.2.2.2.2.2, h.wr]
    show [(⟨(vlay p st s).SP, 72⟩ : Region), _] = _
    rw [vlay_sp s hst16]; rfl
  have hspB := h.sp2
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · show (popped .r11 9 s₆).gpr r = _
    by_cases e : r = .rsp
    · subst e
      rw [popped_rsp, tp.rsp, vlay_sp s hst16]
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ e (by intro h'; subst h'; revert hr; decide), tp.cs r hr e, g₅,
        hg₄ r (hcs r hr).1 (hcs r hr).2.1 (hcs r hr).2.2]
  · show m.readW (s.gpr .rsp) 64 = _
    rw [fm.readW (r := vRet s) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [hsp₅]; exact Offset.base_disjoint_below _ (by simp [Impl.SlhDsa.X86_64.Verify.verifyRegs])) (by decide),
      tp.frame.readW (r := vRet s) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.retScr
        · exact Offset.base_disjoint_below _ (by have := h.sp; omega)) (by decide)]
  · show ((popped .r11 9 s₆).gpr .rax).setWidth 32 = _
    rw [popped_gpr _ _ _ (by decide) (by decide), tp.ret, verify_eq hp h8 hsg]

end VG.Proof.SlhDsa.X86_64.VerifyTop
