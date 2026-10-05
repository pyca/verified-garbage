import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignFn
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Prims

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyPre`. -/
section

/-!
# ML-DSA on x86-64, `verify_message`: the precondition and the layout

Untrusted: everything here is checked by Lean. The precondition of
`verifyMessageContract p X86_64.abi 112`, spelled out (`VPre`), and the
layout of a run from a state satisfying it (`vlay`): the key is `pk`, there
is no `rnd` (its slot holds 0) and `scratch` is the only argument on the
stack.
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params) (s : State)

abbrev vPk : Region := ⟨s.gpr .rdi, p.pkLen⟩
abbrev vSigR : Region := ⟨s.gpr .r9, p.sigLen⟩
abbrev vArgs : Region := ⟨stackArgAddr s 0, 8⟩
abbrev vScr : Region := ⟨stackArg s 0, mScrLen p⟩

end

/-- The precondition of `verifyMessageContract p X86_64.abi 112`. -/
structure VPre (p : Params) (s : State) : Prop where
  sp : 112 ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64
  rd : s.rd = [VG.Proof.MlDsa.X86_64.Message.vPk p s, rMsg s, rCtx s, VG.Proof.MlDsa.X86_64.Message.vSigR p s, VG.Proof.MlDsa.X86_64.Message.vArgs s]
  wr : s.wr = [VG.Proof.MlDsa.X86_64.Message.vScr p s]
  pkScr : (VG.Proof.MlDsa.X86_64.Message.vPk p s).Disjoint (VG.Proof.MlDsa.X86_64.Message.vScr p s)
  msgScr : (rMsg s).Disjoint (VG.Proof.MlDsa.X86_64.Message.vScr p s)
  ctxScr : (rCtx s).Disjoint (VG.Proof.MlDsa.X86_64.Message.vScr p s)
  sigScr : (VG.Proof.MlDsa.X86_64.Message.vSigR p s).Disjoint (VG.Proof.MlDsa.X86_64.Message.vScr p s)
  scrArgs : (VG.Proof.MlDsa.X86_64.Message.vScr p s).Disjoint (VG.Proof.MlDsa.X86_64.Message.vArgs s)
  retPk : (rRet s).Disjoint (VG.Proof.MlDsa.X86_64.Message.vPk p s)
  retMsg : (rRet s).Disjoint (rMsg s)
  retCtx : (rRet s).Disjoint (rCtx s)
  retSig : (rRet s).Disjoint (VG.Proof.MlDsa.X86_64.Message.vSigR p s)
  retScr : (rRet s).Disjoint (VG.Proof.MlDsa.X86_64.Message.vScr p s)
  retArgs : (rRet s).Disjoint (VG.Proof.MlDsa.X86_64.Message.vArgs s)
  stkPk : (rStk s).Disjoint (VG.Proof.MlDsa.X86_64.Message.vPk p s)
  stkMsg : (rStk s).Disjoint (rMsg s)
  stkCtx : (rStk s).Disjoint (rCtx s)
  stkSig : (rStk s).Disjoint (VG.Proof.MlDsa.X86_64.Message.vSigR p s)
  stkScr : (rStk s).Disjoint (VG.Proof.MlDsa.X86_64.Message.vScr p s)
  stkArgs : (rStk s).Disjoint (VG.Proof.MlDsa.X86_64.Message.vArgs s)
  nPk : (s.gpr .rdi).toNat + p.pkLen ≤ 2 ^ 64
  nMsg : (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  nCtx : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  nSig : (s.gpr .r9).toNat + p.sigLen ≤ 2 ^ 64
  nScr : (stackArg s 0).toNat + mScrLen p ≤ 2 ^ 64

theorem vPre_of {p : Params} {s : State} (h : (verifyMessageContract p X86_64.abi 112).pre s) : VG.Proof.MlDsa.X86_64.Message.VPre p s := by
  sig_pre [verifyMessageContract, verifyMessageSig, X86_64.abi, X86_64.argRegs, List.range, List.range.loop] at h
  obtain ⟨sp, sp2, rd, wr, pkScr, msgScr, ctxScr, sigScr, scrArgs, retPk, retMsg, retCtx, retSig, retScr,
    retArgs, stkPk, stkMsg, stkCtx, stkSig, stkScr, stkArgs, nPk, nMsg, nCtx, nSig, nScr⟩ := h
  exact ⟨sp, sp2, rd, wr, pkScr, msgScr, ctxScr, sigScr, scrArgs, retPk, retMsg, retCtx, retSig, retScr,
    retArgs, stkPk, stkMsg, stkCtx, stkSig, stkScr, stkArgs, nPk, nMsg, nCtx, nSig, nScr⟩

theorem pkLen_ge {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) : 128 ≤ p.pkLen ∧ p.pkLen < 2 ^ 31 := by
  simp only [VG.Proof.MlDsa.X86_64.Message.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

/-- The layout of a run of `verify_message` from `s`. -/
def vlay (p : Params) (s : State) : VG.Proof.MlDsa.X86_64.Message.Lay where
  B := s.gpr .rsp - BitVec.ofNat 64 112
  key := s.gpr .rdi
  keyLen := p.pkLen
  msg := s.gpr .rsi
  len := s.gpr .rdx
  ctx := s.gpr .rcx
  ctxLen := s.gpr .r8
  rnd := 0
  sig := s.gpr .r9
  scr := stackArg s 0
  E := oE p
  rd := s.rd
  wr := s.wr

theorem vlay_B (p : Params) (s : State) :
    (VG.Proof.MlDsa.X86_64.Message.vlay p s).B + BitVec.ofNat 64 112 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem vlay_X (p : Params) (s : State) : Within (VG.Proof.MlDsa.X86_64.Message.vlay p s).XS (VG.Proof.MlDsa.X86_64.Message.vScr p s) :=
  ⟨oE p, rfl, by show oE p + 1024 ≤ mScrLen p; rw [mScr_eq]⟩

theorem vlay_ok {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) {s : State} (h : VG.Proof.MlDsa.X86_64.Message.VPre p s) (h8 : (s.gpr .r8).toNat < 256) :
    (VG.Proof.MlDsa.X86_64.Message.vlay p s).Ok := by
  have hX := VG.Proof.MlDsa.X86_64.Message.vlay_X p s
  have hXs := hX.sub
  refine ⟨h8, oE_lt hp, VG.Proof.MlDsa.X86_64.Message.pkLen_ge hp, ?_, ⟨VG.Proof.MlDsa.X86_64.Message.vScr p s, by simp [VG.Proof.MlDsa.X86_64.Message.vlay, h.wr], hX⟩, by simp [VG.Proof.MlDsa.X86_64.Message.vlay, h.rd],
    by simp [VG.Proof.MlDsa.X86_64.Message.vlay, h.rd], by simp [VG.Proof.MlDsa.X86_64.Message.vlay, h.rd], h.pkScr.symm.sub_left hXs, h.msgScr.symm.sub_left hXs,
    h.ctxScr.symm.sub_left hXs, h.stkScr.sub_right hXs, h.stkPk, h.stkMsg, h.stkCtx, h.nPk, h.nMsg, h.nCtx, ?_⟩
  · have := h.sp; have := (s.gpr .rsp).isLt
    simp only [VG.Proof.MlDsa.X86_64.Message.vlay, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · intro R hR
    simp only [VG.Proof.MlDsa.X86_64.Message.vlay, h.wr, List.mem_cons, List.not_mem_nil, or_false] at hR
    have := h.nScr
    subst hR; simp only; omega

theorem vmu_eq (p : Params) (s : State) :
    (VG.Proof.MlDsa.X86_64.Message.vlay p s).MU = stackArg s 0 + BitVec.ofNat 64 (oE p + 840) := by
  simp only [Lay.MU, Lay.X, VG.Proof.MlDsa.X86_64.Message.vlay, add_add]

theorem vmu_nowrap {p : Params} {s : State} (h : VG.Proof.MlDsa.X86_64.Message.VPre p s) : (VG.Proof.MlDsa.X86_64.Message.vlay p s).MU.toNat + 64 ≤ 2 ^ 64 := by
  have hn : (stackArg s 0).toNat + (oE p + 1024) ≤ 2 ^ 64 := by rw [← mScr_eq]; exact h.nScr
  rw [VG.Proof.MlDsa.X86_64.Message.vmu_eq]
  generalize oE p = e at hn ⊢
  generalize stackArg s 0 = x at hn ⊢
  clear h
  rw [toNat_add_ofNat (by omega), Nat.add_assoc]
  exact Nat.le_trans (Nat.add_le_add_left (by clear hn; omega) _) hn

end VG.Proof.MlDsa.X86_64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyCall`. -/
section

/-!
# ML-DSA on x86-64, `verify_message`: the call of the verification function on `μ`

Untrusted: everything here is checked by Lean. Any code that meets the
contract the proof of `vg_mldsa*_verify` is written against (`verifyK p`),
never writes `rsp` and whose calls nest at most three deep (`VerifyFn`): its
call from the frame, on `pk`, `μ` at `X + 840`, `sig` and the first
`scratchWords p` words of `scratch` (`verifyCall_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.X86_64.Verify (verifyK)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A verification function on `μ` that `verify_message` can call. -/
structure VerifyFn (p : Params) (c : Prog isa) : Prop where
  ok : ∀ s, (verifyK p).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (verifyK p).post s s'
  ct : ConstantTime isa (verifyK p).pre (verifyK p).pub c
  nosp : NoSp c
  depth : c.depth ≤ 4

/-- The arguments of the call of the verification function on `μ`. -/
abbrev verifyArgs (p : Params) : List Arg := [.slot fKey, aMu p, .slot fSig, .slot fScr]

theorem verifyArgs_ok {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) : (VG.Proof.MlDsa.X86_64.Message.verifyArgs p).all Arg.ok = true := by
  have := oE_lt hp
  simp only [VG.Proof.MlDsa.X86_64.Message.verifyArgs, Impl.MlDsa.X86_64.Message.aMu, List.all_cons, List.all_nil, Arg.ok, fKey, fSig,
    fScr, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- The working space of the verification function on `μ`. -/
abbrev rScrV (p : Params) (L : VG.Proof.MlDsa.X86_64.Message.Lay) : Region := ⟨L.scr, Verify.scrLen p⟩

/-- The regions the verification function on `μ` reads and writes. -/
abbrev verifyRd (p : Params) (L : VG.Proof.MlDsa.X86_64.Message.Lay) : List Region := [⟨L.key, p.pkLen⟩, ⟨L.MU, 64⟩, ⟨L.sig, p.sigLen⟩]
abbrev verifyWr (p : Params) (L : VG.Proof.MlDsa.X86_64.Message.Lay) : List Region := [VG.Proof.MlDsa.X86_64.Message.rScrV p L]

/-- What a layout of `verify_message` says of `sig` and `scratch`. -/
structure VFacts (p : Params) (L : VG.Proof.MlDsa.X86_64.Message.Lay) : Prop where
  key : L.keyLen = p.pkLen
  e : oE p = L.E
  inSig : (⟨L.sig, p.sigLen⟩ : Region) ∈ L.rd
  inScr : ∃ R ∈ L.wr, Within (VG.Proof.MlDsa.X86_64.Message.rScrV p L) R
  inMu : ∃ R ∈ L.wr, Within ⟨L.MU, 64⟩ R
  sigScr : Region.Disjoint ⟨L.sig, p.sigLen⟩ ⟨L.scr, mScrLen p⟩
  keyScr : Region.Disjoint ⟨L.key, p.pkLen⟩ ⟨L.scr, mScrLen p⟩
  kSig : L.STK.Disjoint ⟨L.sig, p.sigLen⟩
  kScr : L.STK.Disjoint ⟨L.scr, mScrLen p⟩
  nSig : L.sig.toNat + p.sigLen ≤ 2 ^ 64
  nScr : L.scr.toNat + mScrLen p ≤ 2 ^ 64

/-- The layout is that of a run of `verify_message` from a state with the
memory `m`, past the branch on `ctx_len`. -/
def VOk (p : Params) (L : VG.Proof.MlDsa.X86_64.Message.Lay) (m : Mem) : Prop :=
  ∃ σ, VG.Proof.MlDsa.X86_64.Message.VPre p σ ∧ (σ.gpr .r8).toNat < 256 ∧ VG.Proof.MlDsa.X86_64.Message.vlay p σ = L ∧ σ.mem = m

theorem scrV_sub (p : Params) (L : VG.Proof.MlDsa.X86_64.Message.Lay) : Region.Sub (VG.Proof.MlDsa.X86_64.Message.rScrV p L) ⟨L.scr, mScrLen p⟩ :=
  Region.sub_prefix (by rw [mScr_eq]; simp only [Verify.scrLen, oE]; omega)

theorem VOk.facts {p : Params} {L : VG.Proof.MlDsa.X86_64.Message.Lay} {m : Mem} (h : VG.Proof.MlDsa.X86_64.Message.VOk p L m) : VG.Proof.MlDsa.X86_64.Message.VFacts p L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact ⟨rfl, rfl, by simp [VG.Proof.MlDsa.X86_64.Message.vlay, hσ.rd],
    ⟨VG.Proof.MlDsa.X86_64.Message.vScr p σ, by simp [VG.Proof.MlDsa.X86_64.Message.vlay, hσ.wr], within_base _ (by rw [mScr_eq]; simp only [Verify.scrLen, oE]; omega)⟩,
    ⟨VG.Proof.MlDsa.X86_64.Message.vScr p σ, by simp [VG.Proof.MlDsa.X86_64.Message.vlay, hσ.wr],
      (within_off (VG.Proof.MlDsa.X86_64.Message.vlay p σ).X (d := 840) (n := 64) (k := 1024) (by omega)).trans (VG.Proof.MlDsa.X86_64.Message.vlay_X p σ)⟩,
    hσ.sigScr, hσ.pkScr, hσ.stkSig, hσ.stkScr, hσ.nSig, hσ.nScr⟩

/-- The registers after the moves of the arguments of the verification function on `μ`. -/
theorem verifyRegsL {p : Params} {L : VG.Proof.MlDsa.X86_64.Message.Lay} (hE : oE p = L.E) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}
    {t t1 : State} (hc : Ctx L g mx m₀ t) (hm : Moved (VG.Proof.MlDsa.X86_64.Message.verifyArgs p) t t1) :
    t1.gpr .rdi = L.key ∧ t1.gpr .rsi = L.MU ∧ t1.gpr .rdx = L.sig ∧ t1.gpr .rcx = L.scr := by
  obtain ⟨e1, e2, e3, e4⟩ := argsIn4 hm.1.1
  rw [hc.slot, fKey, hc.pKey] at e1
  rw [hc.aMu p hE] at e2
  rw [hc.slot, fSig, hc.pSig] at e3
  rw [hc.slot, fScr, hc.pScr] at e4
  exact ⟨e1, e2, e3, e4⟩

theorem mu_scrV {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) {L : VG.Proof.MlDsa.X86_64.Message.Lay} (hE : oE p = L.E) :
    Region.Disjoint ⟨L.MU, 64⟩ (VG.Proof.MlDsa.X86_64.Message.rScrV p L) := by
  show Region.Disjoint ⟨L.scr + BitVec.ofNat 64 L.E + BitVec.ofNat 64 840, 64⟩ ⟨L.scr, Verify.scrLen p⟩
  rw [add_add, ← hE]
  exact Offset.disjoint_base _ (by simp only [Verify.scrLen, oE]; omega) (by have := oE_lt hp; omega)

/-- The precondition of the verification function on `μ`, on entry to it. -/
theorem verifyK_pre {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params) {L : VG.Proof.MlDsa.X86_64.Message.Lay} (hL : L.Ok) (F : VG.Proof.MlDsa.X86_64.Message.VFacts p L)
    {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t1 : State} (hc : Ctx L g mx m₀ t)
    (hm : Moved (VG.Proof.MlDsa.X86_64.Message.verifyArgs p) t t1) :
    (verifyK p).pre (t1.callEntry.withRegions (VG.Proof.MlDsa.X86_64.Message.verifyRd p L) (VG.Proof.MlDsa.X86_64.Message.verifyWr p L)) := by
  have hc1 : Ctx L g mx m₀ t1 :=
    hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (VG.Proof.MlDsa.X86_64.Message.argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4⟩ := VG.Proof.MlDsa.X86_64.Message.verifyRegsL F.e hc hm
  have hsub := VG.Proof.MlDsa.X86_64.Message.scrV_sub p L
  have hX : Within L.XS ⟨L.scr, mScrLen p⟩ := ⟨L.E, rfl, by rw [mScr_eq, F.e]⟩
  have hmu : Region.Sub ⟨L.MU, 64⟩ ⟨L.scr, mScrLen p⟩ :=
    ((within_off L.X (d := 840) (n := 64) (k := 1024) (by omega)).trans hX).sub
  have hB := hL.nB
  have hE := oE_lt hp
  have hkey : (⟨L.key, p.pkLen⟩ : Region) = L.KEY := by rw [Lay.KEY, F.key]
  have hrsp : t1.callEntry.gpr .rsp = L.B + BitVec.ofNat 64 32 := by
    rw [State.callEntry_rsp, hc1.rsp, Lay.SP]; exact sp_sub8 _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    hrsp, e1, e2, e3, e4, below32]
  · rw [toNat_add_ofNat (by omega)]; omega
  · exact F.keyScr.sub_right hsub
  · exact VG.Proof.MlDsa.X86_64.Message.mu_scrV hp F.e
  · exact F.sigScr.sub_right hsub
  · exact hL.stk_r (hkey ▸ hL.kKey) (by omega)
  · exact hL.stk_x (d := 32) (n := 8) (e := 840) (k := 64) (by omega) (by omega)
  · exact hL.stk_r F.kSig (by omega)
  · exact hL.stk_r (F.kScr.sub_right hsub) (by omega)
  · exact (hkey ▸ hL.kKey).sub_left (Region.sub_prefix (by omega))
  · exact (hL.kX.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by omega))
  · exact F.kSig.sub_left (Region.sub_prefix (by omega))
  · exact (F.kScr.sub_right hsub).sub_left (Region.sub_prefix (by omega))
  · exact F.key ▸ hL.nKey
  · show L.MU.toNat + 64 ≤ 2 ^ 64
    have hn : L.scr.toNat + (L.E + 1024) ≤ 2 ^ 64 := by rw [← F.e, ← mScr_eq]; exact F.nScr
    show (L.scr + BitVec.ofNat 64 L.E + BitVec.ofNat 64 840).toNat + 64 ≤ 2 ^ 64
    rw [add_add]
    generalize L.E = e at hn ⊢
    generalize L.scr = x at hn ⊢
    clear hc hc1 hm e1 e2 e3 e4 hsub hX hmu hkey hrsp F hL
    have hlt : x.toNat + (e + 840) < x.toNat + (e + 1024) :=
      Nat.add_lt_add_left (Nat.add_lt_add_left (by decide : 840 < 1024) e) _
    rw [toNat_add_ofNat (Nat.lt_of_lt_of_le hlt hn), Nat.add_assoc]
    exact Nat.le_trans (Nat.add_le_add_left (Nat.add_le_add_left (by decide : 840 + 64 ≤ 1024) e) _) hn
  · exact F.nSig
  · have := F.nScr; simp only [mScrLen, Verify.scrLen, messageScratchWords] at this ⊢; omega

/-- The call of the verification function on `μ`. -/
theorem verifyCall_ok {p : Params} {n : String} {c : Prog isa} (hV : VG.Proof.MlDsa.X86_64.Message.VerifyFn p c) (hp : p ∈ VG.Proof.MlDsa.X86_64.Message.params)
    {L : VG.Proof.MlDsa.X86_64.Message.Lay} (hL : L.Ok) (F : VG.Proof.MlDsa.X86_64.Message.VFacts p L) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx L g mx m₀ t) :
    WP isa (callA n c (VG.Proof.MlDsa.X86_64.Message.verifyArgs p)) t fun s' =>
      s'.rd = t.rd ∧ s'.wr = t.wr ∧ s'.gpr .rsp = t.gpr .rsp ∧ (∀ r ∈ calleeSaved, s'.gpr r = t.gpr r) ∧
      s'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧
      Frame [VG.Proof.MlDsa.X86_64.Message.rScrV p L, ⟨L.B, 40⟩] t.mem s'.mem ∧
      (let v := fun b => verifyMu p b (bytesAt t.mem L.key p.pkLen) (bytesAt t.mem L.MU 64)
          (bytesAt t.mem L.sig p.sigLen);
        (Verify.res s' = 1 ∧ ∃ b, v b = some true) ∨ (Verify.res s' = 0 ∧ v minBounds ≠ some true)) := by
  refine WP.seq (WP.mono (setArgs_ok _ (VG.Proof.MlDsa.X86_64.Message.verifyArgs_ok hp) t hc.frOk) fun t1 hm => ?_)
  obtain ⟨⟨hA, hm', hx⟩, k⟩ := hm
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm' hx fun r hr => k.gpr (VG.Proof.MlDsa.X86_64.Message.argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4⟩ := VG.Proof.MlDsa.X86_64.Message.verifyRegsL F.e hc ⟨⟨hA, hm', hx⟩, k⟩
  have hpre := VG.Proof.MlDsa.X86_64.Message.verifyK_pre hp hL F hc ⟨⟨hA, hm', hx⟩, k⟩
  have hdep := hV.depth
  have hrsp1 : t1.gpr .rsp = L.SP := hc1.rsp
  have hkey : (⟨L.key, p.pkLen⟩ : Region) = L.KEY := by rw [Lay.KEY, F.key]
  refine WP.call_mx hV.ok hV.nosp (by omega) hpre ?_ ?_ fun s' hrd hwr hcs hf _ hpost hmx => ?_
  · rw [hc1.rd, hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨L.KEY, List.mem_append_left _ hL.inKey, by rw [hkey]; exact within_self _⟩
    · obtain ⟨R, hR, hw⟩ := F.inMu; exact ⟨R, by simp [hR], hw⟩
    · exact ⟨_, by simp [F.inSig], within_self _⟩
    · obtain ⟨R, hR, hw⟩ := F.inScr; exact ⟨R, by simp [hR], hw⟩
  · rw [hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    obtain ⟨R, hR, hw⟩ := F.inScr; exact ⟨R, List.mem_cons_of_mem _ hR, hw⟩
  obtain ⟨s₂, hm₂, hg₂, hq⟩ := hpost
  refine ⟨hrd.trans k.2.1, hwr.trans k.2.2, by rw [hcs .rsp (by decide), k.gpr (by decide)],
    fun r hr => by rw [hcs r hr, k.gpr (VG.Proof.MlDsa.X86_64.Message.argRegs_cs r hr)], by rw [hmx, hx], ?_, ?_⟩
  · rw [← hm']
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨VG.Proof.MlDsa.X86_64.Message.rScrV p L, List.mem_cons_self .., fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨⟨L.B, 40⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
      rw [hrsp1]
      exact below_call_sub _ (by omega)
  · simp only [verifyK, Verify.vPk, Verify.vMu, Verify.vSig, State.withRegions_mem,
      gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp),
      gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp), e1, e2, e3, Verify.res] at hq
    rw [hc1.ce_bytesAt (p := L.key) (hL.stk_r (hkey ▸ hL.kKey) (by omega)) (by have := hL.nKey; rw [F.key] at this; omega),
      hc1.ce_bytesAt (p := L.MU) (hL.stk_x (d := 32) (n := 8) (e := 840) (k := 64) (by omega) (by omega)) (by omega),
      hc1.ce_bytesAt (p := L.sig) (hL.stk_r F.kSig (by omega)) (by have := F.nSig; omega), hm',
      hg₂ _ (by decide)] at hq
    exact hq

end VG.Proof.MlDsa.X86_64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyCorrect`. -/
section

/-!
# ML-DSA on x86-64, `verify_message`: correctness

Untrusted: everything here is checked by Lean. From a state satisfying
`verifyMessageContract p X86_64.abi 112`, `verifyMessage n c p` returns 2 if
the context string is longer than 255 bytes; otherwise it computes
`tr = H(pk, 64)`, then `μ` of the formatted message, and calls the
verification function on `μ` `c`, which gives `ML-DSA.Verify_internal` of
the formatted message (`verifyMessage_wp`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `scratch` to `r11`, 0 to `rax`. -/
theorem verifyMov_ok {p : Params} {s s1 : State} (h : VG.Proof.MlDsa.X86_64.Message.VPre p s) (hg : s1.gpr = s.gpr) (hm : s1.mem = s.mem)
    (hrd : s1.rd = s.rd) :
    WP isa (.block [.mov .r11 (.mem (stk 8)), .mov32 .rax (.imm 0)]) s1 fun s2 =>
      (s2.gpr .r11 = stackArg s 0 ∧ s2.gpr .rax = 0 ∧ s2.mem = s.mem ∧ s2.mxcsr = s1.mxcsr) ∧
        Keep [.r11, .rax] s1 s2 := by
  have h8 : InRegions (s1.rd ++ s1.wr) (s1.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    refine ⟨VG.Proof.MlDsa.X86_64.Message.vArgs s, by simp [hrd, h.rd], ?_⟩
    rw [hg, ← stackArgAddr0]
    exact Region.contains_self _ _
  refine WP.keep _ ?_ (by decide)
  xrun [ea_stk, h8, RegUpd.mxcsr_setReg]
  rw [hm, hg]
  exact ⟨rfl, rfl⟩

theorem cs_tmpV : ∀ r ∈ calleeSaved, r ∉ [Reg.r11, .rax] := by decide

/-- The arguments of `verifyRegs`, pushed. -/
theorem verifyRegs_vals {p : Params} {s s2 : State} (hk : ∀ r, r ∉ [Reg.r11, .rax] → s2.gpr r = s.gpr r)
    (h11 : s2.gpr .r11 = stackArg s 0) (hax : s2.gpr .rax = 0) :
    ∀ j (hj : j < 9), s2.gpr (verifyRegs[j]'(by simp [verifyRegs]; omega)) =
      (VG.Proof.MlDsa.X86_64.Message.vlay p s).vals[j]'(by simp [Lay.vals]; omega) := by
  intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [verifyRegs, Lay.vals, VG.Proof.MlDsa.X86_64.Message.vlay, List.getElem_cons_zero, List.getElem_cons_succ, h11, hax] <;>
    exact hk _ (by decide)

theorem verifyMessage_wp {p : Params} {n : String} {c : Prog isa} (hV : VG.Proof.MlDsa.X86_64.Message.VerifyFn p c) (hp : p ∈ params)
    {s : State} (hpre : (verifyMessageContract p X86_64.abi 112).pre s) :
    WP isa (verifyMessage n c p) s fun s' =>
      abiPreserved s s' ∧ (verifyMessageContract p X86_64.abi 112).post s s' := by
  have h := VG.Proof.MlDsa.X86_64.Message.vPre_of hpre
  unfold verifyMessage top
  refine WP.seq (WP.mono (cmp_ok s) fun s1 ⟨hg1, hm1, hrd1, hwr1, hx1, hc1⟩ => ?_)
  by_cases h8 : (s.gpr .r8).toNat < 256
  · rw [decide_eq_true h8] at hc1
    refine wp_ite_t hc1 (WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Message.verifyMov_ok h hg1 hm1 hrd1) fun s2 ⟨⟨h11, hax, hm2, hx2⟩, k2⟩ => ?_))
    have hL := VG.Proof.MlDsa.X86_64.Message.vlay_ok hp h h8
    have hg2 : ∀ r, r ∉ [Reg.r11, .rax] → s2.gpr r = s.gpr r := fun r hr => (k2.gpr hr).trans (by rw [hg1])
    have hsp2 : s2.gpr .rsp = (VG.Proof.MlDsa.X86_64.Message.vlay p s).B + BitVec.ofNat 64 112 := by
      rw [hg2 _ (by decide), VG.Proof.MlDsa.X86_64.Message.vlay_B]
    have hn : 8 * verifyRegs.length ≤ (s2.gpr .rsp).toNat := by
      rw [hg2 _ (by decide)]; have := h.sp; simp only [verifyRegs, List.length_cons, List.length_nil]; omega
    refine WP.frame (by decide) (by decide) (by decide) hn ?_
    refine WP.seq (WP.mono (entry_ok hL rfl (by decide) hsp2 (k2.2.1.trans hrd1) (k2.2.2.trans hwr1)
      (VG.Proof.MlDsa.X86_64.Message.verifyRegs_vals hg2 h11 hax) (hg2 _ (by decide)))
      fun t ⟨hc, htw, htsp⟩ => ?_)
    have hE := oE_lt hp
    have hk : (VG.Proof.MlDsa.X86_64.Message.vlay p s).keyLen = p.pkLen := rfl
    refine WP.seq (WP.mono (trHash_ok hL rfl hk hc) fun t₁ ⟨hc₁, _, htr⟩ => ?_)
    obtain ⟨R, hR, hw⟩ := hL.covX (e := 840) (k := 64) (by omega)
    refine WP.seq (WP.mono (muHash_ok hL rfl hc₁ (tr := aMu p)
      (by simp [Arg.ok, Impl.MlDsa.X86_64.Message.aMu, fScr]; omega)
      (fun t' hc' => hc'.aMu p rfl) ⟨R, by simp [hR], hw⟩ st_mu.symm mu_ks (k_mu hL))
      fun t₂ ⟨hc₂, _, hμ⟩ => ?_)
    have F : VG.Proof.MlDsa.X86_64.Message.VFacts p (VG.Proof.MlDsa.X86_64.Message.vlay p s) := VOk.facts ⟨s, h, h8, rfl, rfl⟩
    refine WP.mono (VG.Proof.MlDsa.X86_64.Message.verifyCall_ok hV hp hL F hc₂) fun s' ⟨hrd', hwr', hsp', hcs', hx', hf', hq⟩ => ?_
    have hm₀ : s2.mem = s.mem := hm2
    refine ⟨by rw [hsp', hc₂.rsp, ← htsp, hc.rsp], by rw [hwr', hc₂.wr, ← htw, hc.wr], ?_, ?_⟩
    · -- The calling convention.
      refine ⟨fun r hr => ?_, ?_, ?_⟩
      · by_cases hr' : r = .rsp
        · subst hr'
          rw [popped_rsp, hsp', hc₂.rsp, Lay.SP, add_add, show 40 + 8 * verifyRegs.length = 112 from rfl, VG.Proof.MlDsa.X86_64.Message.vlay_B]
        · rw [popped_gpr _ _ _ hr' (cs_r11 r hr), hcs' r hr, hc₂.cs r hr hr', hg2 r (VG.Proof.MlDsa.X86_64.Message.cs_tmpV r hr)]
      · have eR : rRet s = ⟨(VG.Proof.MlDsa.X86_64.Message.vlay p s).B + BitVec.ofNat 64 112, 8⟩ := by rw [VG.Proof.MlDsa.X86_64.Message.vlay_B]
        have dB : ∀ k, k ≤ 112 → (rRet s).Disjoint ⟨(VG.Proof.MlDsa.X86_64.Message.vlay p s).B, k⟩ := fun k hk => by
          rw [eR]; exact Offset.disjoint_base _ hk (by have := hL.nB; omega)
        rw [popped_mem, hf'.readW (r := rRet s) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact h.retScr.sub_right (VG.Proof.MlDsa.X86_64.Message.scrV_sub p _)
            · exact dB 40 (by decide)) (by decide),
          hc₂.frame.readW (r := rRet s) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact h.retScr.sub_right (VG.Proof.MlDsa.X86_64.Message.vlay_X p s).sub
            · exact dB 112 (by decide)) (by decide), hm₀]
      · rw [popped_mxcsr, hx', hc₂.mx, hx2, hx1]
    · sig_post [verifyMessageContract, verifyMessageSig, X86_64.abi, X86_64.argRegs, List.range,
        List.range.loop]
      rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
      simp only [verifyInternal, messageRep, pkTr]
      have ek : bytesAt t₂.mem (VG.Proof.MlDsa.X86_64.Message.vlay p s).key p.pkLen = bytesAt s.mem (s.gpr .rdi) p.pkLen := by
        rw [hc₂.bytesAt_eq (p := (VG.Proof.MlDsa.X86_64.Message.vlay p s).key) (n := p.pkLen) hL.xKey hL.kKey (by have := h.nPk; omega), hm₀]; rfl
      have es : bytesAt t₂.mem (VG.Proof.MlDsa.X86_64.Message.vlay p s).sig p.sigLen = bytesAt s.mem (s.gpr .r9) p.sigLen := by
        rw [hc₂.bytesAt_eq (p := (VG.Proof.MlDsa.X86_64.Message.vlay p s).sig) (n := p.sigLen) (h.sigScr.symm.sub_left (VG.Proof.MlDsa.X86_64.Message.vlay_X p s).sub) h.stkSig
          (by have := h.nSig; omega), hm₀]; rfl
      have hμ' := hμ
      rw [htr, hm₀] at hμ'
      simp only [Verify.res] at hq
      rw [ek, es, hμ'] at hq
      simp only [hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc] at hq ⊢
      exact hq
  · rw [decide_eq_false h8] at hc1
    refine wp_ite_f hc1 ?_
    xrun [show (2 : BitVec 32) = BitVec.ofNat 32 2 from rfl]
    refine ⟨⟨fun r hr => ?_, by rw [RegUpd.mem_setReg, hm1], by rw [RegUpd.mxcsr_setReg, hx1]⟩, ?_⟩
    · rw [RegUpd.gpr_setReg_of_ne _ _ (fun e => by subst e; revert hr; decide), hg1]
    · sig_post [verifyMessageContract, verifyMessageSig, X86_64.abi, X86_64.argRegs, List.range,
        List.range.loop]
      rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega)]
      rfl

end VG.Proof.MlDsa.X86_64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyCT`. -/
section

/-!
# ML-DSA on x86-64, `verify_message`: constant time

Untrusted: everything here is checked by Lean. Two runs from states that
satisfy the contract and agree on its public data, which include `pk`, the
message, the context string and the signature (`verifyI`), leak the same:
the branch on `ctx_len`, the moves and the frame depend only on the pointers
and the lengths; the hashing leaks only the layout (`trHash_tr`,
`muHash_tr`); and the call of the verification function on `μ` leaks only
`pk`, `μ` and `sig`, which are the same in both runs (`verifyCall_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86_64 (Keep RelCT.postDep)
open VG.Proof.MlDsa.X86_64.Verify (verifyK)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params}

/-- The inputs of a run, with the memory `m`. -/
abbrev vIn (p : Params) (L : VG.Proof.MlDsa.X86_64.Message.Lay) (m : Mem) : List Byte :=
  bytesAt m L.key p.pkLen ++ bytesAt m L.msg L.len.toNat ++ bytesAt m L.ctx L.ctxLen.toNat ++
    bytesAt m L.sig p.sigLen

/-- What the contract says two runs agree on, beyond the pointers and lengths. -/
def verifyI (p : Params) (L : VG.Proof.MlDsa.X86_64.Message.Lay) (m₁ m₂ : Mem) : Prop := leakBytes (VG.Proof.MlDsa.X86_64.Message.vIn p L m₁) = leakBytes (VG.Proof.MlDsa.X86_64.Message.vIn p L m₂)

theorem verifyI_eq {L : VG.Proof.MlDsa.X86_64.Message.Lay} {m₁ m₂ : Mem} (h : VG.Proof.MlDsa.X86_64.Message.verifyI p L m₁ m₂) :
    bytesAt m₁ L.key p.pkLen = bytesAt m₂ L.key p.pkLen ∧
      bytesAt m₁ L.msg L.len.toNat = bytesAt m₂ L.msg L.len.toNat ∧
      bytesAt m₁ L.ctx L.ctxLen.toNat = bytesAt m₂ L.ctx L.ctxLen.toNat ∧
      bytesAt m₁ L.sig p.sigLen = bytesAt m₂ L.sig p.sigLen := by
  have e := VG.Proof.MlDsa.Message.leakBytes_inj h
  obtain ⟨e, e₄⟩ := List.append_inj' e (by simp only [Proof.MlKem.bytesAt_length])
  obtain ⟨e, e₃⟩ := List.append_inj' e (by simp only [Proof.MlKem.bytesAt_length])
  obtain ⟨e₁, e₂⟩ := List.append_inj' e (by simp only [Proof.MlKem.bytesAt_length])
  exact ⟨e₁, e₂, e₃, e₄⟩

/-- `tr` at `X + 840`. -/
def TrOk (p : Params) (L : VG.Proof.MlDsa.X86_64.Message.Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (bytesAt m L.key p.pkLen) 64

/-- `μ` at `X + 840`. -/
def VMuOk (p : Params) (L : VG.Proof.MlDsa.X86_64.Message.Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (H (bytesAt m L.key p.pkLen) 64 ++ hdrBytes L ++
    bytesAt m L.ctx L.ctxLen.toNat ++ bytesAt m L.msg L.len.toNat) 64

/-- Two runs of the call of the verification function on `μ`. -/
theorem verifyCall_tr {n : String} {c : Prog isa} (hV : VG.Proof.MlDsa.X86_64.Message.VerifyFn p c) (hp : p ∈ params) :
    RelCT isa (Two (VG.Proof.MlDsa.X86_64.Message.verifyI p) fun L m t => VG.Proof.MlDsa.X86_64.Message.VOk p L m ∧ VG.Proof.MlDsa.X86_64.Message.VMuOk p L m t) (callA n c (VG.Proof.MlDsa.X86_64.Message.verifyArgs p))
      fun _ _ => True := by
  refine call_tr (VG.Proof.MlDsa.X86_64.Message.verifyArgs_ok hp) hV.ok hV.ct (VG.Proof.MlDsa.X86_64.Message.verifyRd p) (VG.Proof.MlDsa.X86_64.Message.verifyWr p)
    (fun L g mx m₀ t t1 hL hc hφ hm => VG.Proof.MlDsa.X86_64.Message.verifyK_pre hp hL hφ.1.facts hc hm)
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_)
    (fun L g mx m₀ t hL hc hφ => ?_)
  · have F := φ₁.1.facts
    obtain ⟨x1, x2, x3, x4⟩ := VG.Proof.MlDsa.X86_64.Message.verifyRegsL F.e c₁ f₁
    obtain ⟨y1, y2, y3, y4⟩ := VG.Proof.MlDsa.X86_64.Message.verifyRegsL F.e c₂ f₂
    have hkey : (⟨L.key, p.pkLen⟩ : Region) = L.KEY := by rw [Lay.KEY, F.key]
    simp only [verifyK, Verify.vPk, Verify.vMu, Verify.vSig, State.withRegions_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
      State.callEntry_rsp, x1, x2, x3, x4, y1, y2, y3, y4, f₁.2.gpr (by decide : Reg.rsp ∉ argRegs),
      f₂.2.gpr (by decide : Reg.rsp ∉ argRegs), c₁.rsp, c₂.rsp, true_and]
    have hk := hL.nKey
    rw [F.key] at hk
    have ce : ∀ {g mx m₀} {a a1 : State} {q : Addr} {k : Nat}, Ctx L g mx m₀ a → Moved (VG.Proof.MlDsa.X86_64.Message.verifyArgs p) a a1 →
        Region.Disjoint ⟨L.B + BitVec.ofNat 64 32, 8⟩ ⟨q, k⟩ → k ≤ 2 ^ 64 →
        bytesAt a1.callEntry.mem q k = bytesAt a.mem q k := fun c f hd hn => by
      rw [(c.regs f.2.2.1 f.2.2.2 f.1.2.1 f.1.2.2 fun r hr => f.2.gpr (argRegs_cs r hr)).ce_bytesAt hd hn, f.1.2.1]
    have dk := hL.stk_r (hkey ▸ hL.kKey) (d := 32) (n := 8) (by decide)
    have dμ := hL.stk_x (d := 32) (n := 8) (e := 840) (k := 64) (by decide) (by decide)
    have ds := hL.stk_r F.kSig (d := 32) (n := 8) (by decide)
    have hsx : L.XS.Disjoint ⟨L.sig, p.sigLen⟩ := by
      have hX : Within L.XS ⟨L.scr, mScrLen p⟩ := ⟨L.E, rfl, by rw [mScr_eq, F.e]⟩
      exact F.sigScr.symm.sub_left hX.sub
    have ns := F.nSig
    obtain ⟨ek, -, ec, es⟩ := VG.Proof.MlDsa.X86_64.Message.verifyI_eq hi
    obtain ⟨-, em, -, -⟩ := VG.Proof.MlDsa.X86_64.Message.verifyI_eq hi
    refine ⟨?_, ?_, ?_⟩
    · rw [ce c₁ f₁ dk (by omega), ce c₂ f₂ dk (by omega), c₁.bytesAt_eq (hkey ▸ hL.xKey) (hkey ▸ hL.kKey) (by omega),
        c₂.bytesAt_eq (hkey ▸ hL.xKey) (hkey ▸ hL.kKey) (by omega), ek]
    · rw [ce c₁ f₁ dμ (by decide), ce c₂ f₂ dμ (by decide), φ₁.2, φ₂.2, ek, ec, em]
    · rw [ce c₁ f₁ ds (by omega), ce c₂ f₂ ds (by omega), c₁.bytesAt_eq hsx F.kSig (by omega),
        c₂.bytesAt_eq hsx F.kSig (by omega), es]
  · have F := hφ.1.facts
    have hkey : (⟨L.key, p.pkLen⟩ : Region) = L.KEY := by rw [Lay.KEY, F.key]
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_append_left _ hL.inKey, by rw [hkey]; exact within_self _⟩
      · obtain ⟨R, hR, hw⟩ := F.inMu; exact ⟨R, by simp [hR], hw⟩
      · exact ⟨_, List.mem_append_left _ F.inSig, within_self _⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact F.inScr

/-- The public data of the contract, spelled out. -/
structure VPub (p : Params) (s₁ s₂ : State) : Prop where
  rsp : s₁.gpr .rsp = s₂.gpr .rsp
  leak : leakBytes (bytesAt s₁.mem (s₁.gpr .rdi) p.pkLen ++ bytesAt s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx).toNat ++
      bytesAt s₁.mem (s₁.gpr .rcx) (s₁.gpr .r8).toNat ++ bytesAt s₁.mem (s₁.gpr .r9) p.sigLen) =
    leakBytes (bytesAt s₂.mem (s₂.gpr .rdi) p.pkLen ++ bytesAt s₂.mem (s₂.gpr .rsi) (s₂.gpr .rdx).toNat ++
      bytesAt s₂.mem (s₂.gpr .rcx) (s₂.gpr .r8).toNat ++ bytesAt s₂.mem (s₂.gpr .r9) p.sigLen)
  rdi : s₁.gpr .rdi = s₂.gpr .rdi
  rsi : s₁.gpr .rsi = s₂.gpr .rsi
  rdx : s₁.gpr .rdx = s₂.gpr .rdx
  rcx : s₁.gpr .rcx = s₂.gpr .rcx
  r8 : s₁.gpr .r8 = s₂.gpr .r8
  r9 : s₁.gpr .r9 = s₂.gpr .r9
  a0 : stackArg s₁ 0 = stackArg s₂ 0

theorem vPub_of {s₁ s₂ : State} (h : (verifyMessageContract p X86_64.abi 112).pub s₁ s₂) : VG.Proof.MlDsa.X86_64.Message.VPub p s₁ s₂ := by
  sig_pub [verifyMessageContract, verifyMessageSig, X86_64.abi, X86_64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i⟩

/-- Two runs from states agreeing on the public data have the same layout. -/
theorem vlay_eq {s₁ s₂ : State} (h₁ : VG.Proof.MlDsa.X86_64.Message.VPre p s₁) (h₂ : VG.Proof.MlDsa.X86_64.Message.VPre p s₂) (h : VG.Proof.MlDsa.X86_64.Message.VPub p s₁ s₂) : VG.Proof.MlDsa.X86_64.Message.vlay p s₁ = VG.Proof.MlDsa.X86_64.Message.vlay p s₂ := by
  have e1 : s₁.rd = s₂.rd := by
    rw [h₁.rd, h₂.rd]; simp only [VG.Proof.MlDsa.X86_64.Message.vPk, rMsg, rCtx, VG.Proof.MlDsa.X86_64.Message.vSigR, VG.Proof.MlDsa.X86_64.Message.vArgs, stackArgAddr, h.rdi, h.rsi, h.rdx, h.rcx, h.r8,
      h.r9, h.rsp]
  have e2 : s₁.wr = s₂.wr := by
    rw [h₁.wr, h₂.wr]; simp only [VG.Proof.MlDsa.X86_64.Message.vScr, h.a0]
  simp only [VG.Proof.MlDsa.X86_64.Message.vlay, h.rsp, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.a0, e1, e2]

/-- The body of the frame. -/
theorem verifyBody_tr {n : String} {c : Prog isa} (hV : VG.Proof.MlDsa.X86_64.Message.VerifyFn p c) (hp : p ∈ params) :
    RelCT isa (Two (VG.Proof.MlDsa.X86_64.Message.verifyI p) fun L m _ => VG.Proof.MlDsa.X86_64.Message.VOk p L m)
      (.seq (trHash p) (.seq (muHash p (aMu p)) (callA n c (VG.Proof.MlDsa.X86_64.Message.verifyArgs p)))) fun _ _ => True := by
  have hE := oE_lt hp
  have hk := (VG.Proof.MlDsa.X86_64.Message.pkLen_ge hp).2
  have th := trHash_tr (I := VG.Proof.MlDsa.X86_64.Message.verifyI p) (Φ := fun L m _ => VG.Proof.MlDsa.X86_64.Message.VOk p L m) hE hk
    (fun _ _ _ h => ⟨h.facts.e, h.facts.key⟩)
  have th' := two_wp (I := VG.Proof.MlDsa.X86_64.Message.verifyI p) (Φ := fun L m _ => VG.Proof.MlDsa.X86_64.Message.VOk p L m) (Ψ := fun L m t => VG.Proof.MlDsa.X86_64.Message.VOk p L m ∧ VG.Proof.MlDsa.X86_64.Message.TrOk p L m t) th
    fun L g mx m₀ t hL hc hφ => WP.mono (trHash_ok hL hφ.facts.e hφ.facts.key hc) fun t' ⟨hc', _, htr⟩ =>
      ⟨hc', hφ, by unfold VG.Proof.MlDsa.X86_64.Message.TrOk; rw [htr, hφ.facts.key]⟩
  have hok : (aMu p).ok = true := by simp [Arg.ok, Impl.MlDsa.X86_64.Message.aMu, fScr]; omega
  have mh := muHash_tr (I := VG.Proof.MlDsa.X86_64.Message.verifyI p) (Φ := fun L m t => VG.Proof.MlDsa.X86_64.Message.VOk p L m ∧ VG.Proof.MlDsa.X86_64.Message.TrOk p L m t) hE
    (fun _ _ _ h => h.1.facts.e) (tr := aMu p) hok (fun L => L.MU)
    (fun L g mx m t hc hE => hc.aMu p hE)
    fun L hL => by
      obtain ⟨R, hR, hw⟩ := hL.covX (e := 840) (k := 64) (by omega)
      exact ⟨⟨R, by simp [hR], hw⟩, st_mu.symm, mu_ks, k_mu hL⟩
  have mh' := two_wp (I := VG.Proof.MlDsa.X86_64.Message.verifyI p) (Φ := fun L m t => VG.Proof.MlDsa.X86_64.Message.VOk p L m ∧ VG.Proof.MlDsa.X86_64.Message.TrOk p L m t)
    (Ψ := fun L m t => VG.Proof.MlDsa.X86_64.Message.VOk p L m ∧ VG.Proof.MlDsa.X86_64.Message.VMuOk p L m t) mh fun L g mx m₀ t hL hc hφ => by
      obtain ⟨R, hR, hw⟩ := hL.covX (e := 840) (k := 64) (by omega)
      refine WP.mono (muHash_ok hL hφ.1.facts.e hc (tr := aMu p) hok (fun t' hc' => hc'.aMu p hφ.1.facts.e)
        ⟨R, by simp [hR], hw⟩ st_mu.symm mu_ks (k_mu hL)) fun t' ⟨hc', _, hμ⟩ => ⟨hc', hφ.1, ?_⟩
      unfold VG.Proof.MlDsa.X86_64.Message.VMuOk
      rw [hμ, hφ.2]
  exact th'.seq (mh'.seq (VG.Proof.MlDsa.X86_64.Message.verifyCall_tr hV hp))

/-- The entry states of two runs: the precondition and the public data. -/
abbrev VP2 (p : Params) (x y : State) : Prop :=
  (verifyMessageContract p X86_64.abi 112).pre x ∧ (verifyMessageContract p X86_64.abi 112).pre y ∧
    (verifyMessageContract p X86_64.abi 112).pub x y

/-- After the moves before the push. -/
abbrev VMov (x x2 : State) : Prop :=
  (x.gpr .r8).toNat < 256 ∧ ((x2.gpr .r11 = stackArg x 0 ∧ x2.gpr .rax = 0 ∧
    x2.mem = x.mem ∧ x2.mxcsr = x.mxcsr) ∧ (∀ r, r ∉ [Reg.r11, .rax] → x2.gpr r = x.gpr r) ∧
    x2.rd = x.rd ∧ x2.wr = x.wr)

theorem verifyMessage_ct {n : String} {c : Prog isa} (hV : VG.Proof.MlDsa.X86_64.Message.VerifyFn p c) (hp : p ∈ params) :
    ConstantTime isa (verifyMessageContract p X86_64.abi 112).pre (verifyMessageContract p X86_64.abi 112).pub
      (verifyMessage n c p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (verifyMessageContract p X86_64.abi 112).pre s₁ ∧
      (verifyMessageContract p X86_64.abi 112).pre s₂ ∧ (verifyMessageContract p X86_64.abi 112).pub s₁ s₂) =
      Ghost (VG.Proof.MlDsa.X86_64.Message.VP2 p) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold verifyMessage top
  -- `cmp r8, 256`.
  have hcmp := ghost_step (P := VG.Proof.MlDsa.X86_64.Message.VP2 p) (A := fun x a => a = x) (B := ACmp) (c := .block [.alu .cmp .r8 (.imm 256)])
    (block_rsp_tr (fun i hi => by
        simp only [List.mem_singleton] at hi; subst hi; exact spOnly_nomem (fun _ => rfl) rfl)
      fun a b ⟨x, y, hxy, e₁, e₂⟩ => by subst e₁ e₂; exact (VG.Proof.MlDsa.X86_64.Message.vPub_of hxy.2.2).rsp)
    fun x y a b _ e₁ e₂ => by subst e₁ e₂; exact ⟨cmp_ok _, cmp_ok _⟩
  refine RelCT.seq hcmp (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.2.2.2.2.2, f₂.2.2.2.2.2, (VG.Proof.MlDsa.X86_64.Message.vPub_of hxy.2.2).r8]) ?_ ?_)
  · -- `ctx_len < 256`.
    have hmov := ghost_step (P := VG.Proof.MlDsa.X86_64.Message.VP2 p) (A := fun x a => ACmp x a ∧ (x.gpr .r8).toNat < 256) (B := VG.Proof.MlDsa.X86_64.Message.VMov)
      (c := .block [.mov .r11 (.mem (stk 8)), .mov32 .rax (.imm 0)])
      (block_rsp_tr (fun i hi => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
          · exact spOnly_nomem (fun _ => rfl) rfl)
        fun a b ⟨x, y, hxy, f₁, f₂⟩ => by rw [f₁.1.1, f₂.1.1]; exact (VG.Proof.MlDsa.X86_64.Message.vPub_of hxy.2.2).rsp)
      fun x y a b hxy f₁ f₂ => by
        have mv : ∀ {x a : State}, (verifyMessageContract p X86_64.abi 112).pre x → ACmp x a →
            (x.gpr .r8).toNat < 256 → WP isa (.block [.mov .r11 (.mem (stk 8)), .mov32 .rax (.imm 0)]) a
              (VG.Proof.MlDsa.X86_64.Message.VMov x) := fun hx f h8 =>
          WP.mono (VG.Proof.MlDsa.X86_64.Message.verifyMov_ok (VG.Proof.MlDsa.X86_64.Message.vPre_of hx) f.1 f.2.1 f.2.2.1) fun x2 ⟨h, k⟩ =>
            ⟨h8, ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans f.2.2.2.2.1⟩,
              fun r hr => (k.gpr hr).trans (by rw [f.1]), k.2.1.trans f.2.2.1, k.2.2.trans f.2.2.2.1⟩
        exact ⟨mv hxy.1 f₁.1 f₁.2, mv hxy.2.1 f₂.1 f₂.2⟩
    refine RelCT.seq (RelCT.mono hmov (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, ?_⟩, ⟨f₂, ?_⟩⟩)
      fun _ _ h => h) ?_
    · rw [f₁.2.2.2.2.2] at hc; simpa using hc
    · rw [f₁.2.2.2.2.2, (VG.Proof.MlDsa.X86_64.Message.vPub_of hxy.2.2).r8, ← f₂.2.2.2.2.2] at hc
      rw [f₂.2.2.2.2.2] at hc; simpa using hc
    refine RelCT.frame (R := fun _ _ => True) (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
      rw [f₁.2.2.1 _ (by decide), f₂.2.2.1 _ (by decide)]; exact (VG.Proof.MlDsa.X86_64.Message.vPub_of hxy.2.2).rsp) ?_
    -- The frame's body, from the push.
    let A : State → State → Prop := fun x a => ∃ s₁, VG.Proof.MlDsa.X86_64.Message.VMov x s₁ ∧ a = pushed verifyRegs s₁
    let B : State → State → Prop := fun x t => (x.gpr .r8).toNat < 256 ∧ Ctx (VG.Proof.MlDsa.X86_64.Message.vlay p x) x.gpr x.mxcsr x.mem t
    have hdr := ghost_step (P := VG.Proof.MlDsa.X86_64.Message.VP2 p) (A := A) (B := B) (c := .block setHdr)
      (block_rsp_tr (fun i hi => by
          simp only [setHdr, List.mem_singleton] at hi; subst hi
          exact ⟨fun s₁ s₂ h => by simp [addrs, State.ea, stk, h], rfl⟩)
        fun a b ⟨x, y, hxy, ⟨s₁, f₁, e₁⟩, ⟨s₂, f₂, e₂⟩⟩ => by
          subst e₁ e₂
          rw [pushed_rsp, pushed_rsp, f₁.2.2.1 _ (by decide), f₂.2.2.1 _ (by decide), (VG.Proof.MlDsa.X86_64.Message.vPub_of hxy.2.2).rsp])
      fun x y a b hxy fa fb => by
        have en : ∀ {x a : State}, (verifyMessageContract p X86_64.abi 112).pre x → A x a →
            WP isa (.block setHdr) a (B x) := fun hx ⟨s₁, f, e⟩ => by
          subst e
          have h := VG.Proof.MlDsa.X86_64.Message.vPre_of hx
          have hL := VG.Proof.MlDsa.X86_64.Message.vlay_ok hp h f.1
          refine WP.mono (entry_ok hL rfl (by decide) (by rw [f.2.2.1 _ (by decide), VG.Proof.MlDsa.X86_64.Message.vlay_B])
            (f.2.2.2.1.trans rfl) (f.2.2.2.2.trans rfl) (VG.Proof.MlDsa.X86_64.Message.verifyRegs_vals f.2.2.1 f.2.1.1 f.2.1.2.1)
            (f.2.2.1 _ (by decide))) fun t ⟨hc, _, _⟩ =>
            ⟨f.1, hc.congr (fun r hr _ => f.2.2.1 r (VG.Proof.MlDsa.X86_64.Message.cs_tmpV r hr)) f.2.1.2.2.2 f.2.1.2.2.1⟩
        exact ⟨en hxy.1 fa, en hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hdr (fun a b ⟨s₁, s₂, ⟨x, y, hxy, f₁, f₂⟩, e₁, e₂⟩ =>
      ⟨x, y, hxy, ⟨s₁, f₁, e₁⟩, ⟨s₂, f₂, e₂⟩⟩) fun a b ⟨x, y, hxy, ⟨h8x, ca⟩, ⟨h8y, cb⟩⟩ => ?_)
      (VG.Proof.MlDsa.X86_64.Message.verifyBody_tr hV hp)
    have hx := VG.Proof.MlDsa.X86_64.Message.vPre_of hxy.1
    have hy := VG.Proof.MlDsa.X86_64.Message.vPre_of hxy.2.1
    have hpub := VG.Proof.MlDsa.X86_64.Message.vPub_of hxy.2.2
    have e := VG.Proof.MlDsa.X86_64.Message.vlay_eq hx hy hpub
    refine ⟨VG.Proof.MlDsa.X86_64.Message.vlay p x, x.gpr, y.gpr, x.mxcsr, y.mxcsr, x.mem, y.mem, VG.Proof.MlDsa.X86_64.Message.vlay_ok hp hx h8x, ?_, ca, e ▸ cb,
      ⟨x, hx, h8x, rfl, rfl⟩, ⟨y, hy, h8y, e.symm, rfl⟩⟩
    have lk := hpub.leak
    rw [← hpub.rdi, ← hpub.rsi, ← hpub.rdx, ← hpub.rcx, ← hpub.r8, ← hpub.r9] at lk
    exact lk
  · exact block_rsp_tr (fun i hi => by
        simp only [List.mem_singleton] at hi; subst hi; exact spOnly_nomem (fun _ => rfl) rfl)
      fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, _⟩ => by rw [f₁.1, f₂.1]; exact (VG.Proof.MlDsa.X86_64.Message.vPub_of hxy.2.2).rsp

end

end VG.Proof.MlDsa.X86_64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyVerified`. -/
section

/-!
# ML-DSA on x86-64, `verify_message`: verified

Untrusted: everything here is checked by Lean. `verifyMessage n c p`, for
any verification function on `μ` `c` that `verify_message` can call
(`VerifyFn`), is verified against `verifyMessageContract p X86_64.abi 112`.
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa

/-- A state satisfying the precondition. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rcx => 0x3100 | .r9 => 0x3200 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8000A then 0x01 else 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, p.sigLen⟩, ⟨0x80008, 8⟩]
  wr := [⟨0x10000, mScrLen p⟩]

theorem verifyMessage_sat {p : Params} (hp : p ∈ params) :
    ∃ s, (verifyMessageContract p X86_64.abi 112).pre s := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, X86_64.abi, X86_64.argRegs, List.range,
      List.range.loop] [verifySat, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.MlDsa.X86_64.Message.verifySat mlDsa44
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, X86_64.abi, X86_64.argRegs, List.range,
      List.range.loop] [verifySat, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.MlDsa.X86_64.Message.verifySat mlDsa65
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, X86_64.abi, X86_64.argRegs, List.range,
      List.range.loop] [verifySat, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.MlDsa.X86_64.Message.verifySat mlDsa87

theorem verifyMessage_verified {p : Params} {n : String} {c : Prog isa} (hV : VG.Proof.MlDsa.X86_64.Message.VerifyFn p c) (hp : p ∈ params) :
    Verified X86_64.target (verifyMessage n c p) (verifyMessageContract p X86_64.abi 112) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := VG.Proof.MlDsa.X86_64.Message.verifyMessage_wp hV hp h; ⟨t, s', he, ha, hq⟩,
    VG.Proof.MlDsa.X86_64.Message.verifyMessage_ct hV hp, VG.Proof.MlDsa.X86_64.Message.verifyMessage_sat hp⟩

end VG.Proof.MlDsa.X86_64.Message

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyFn`. -/
section

/-!
# ML-DSA on x86-64, `verify_message`: the verification functions on `μ` it calls

Untrusted: everything here is checked by Lean. `vg_mldsa*_verify`, with any
implementation `v` of the polynomial arithmetic, is a function
`verify_message` can call (`verifyFn`): its proofs give its contract, it
never writes `rsp`, and its calls nest at most four deep, which, as whether
it writes `rsp`, is checked on the code with its primitives empty
(`verify_same`), given that theirs nest at most three deep.
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.X86_64 (Comp Same Same.ok ArithImpl)
open VG.Impl.MlDsa.X86_64.Verify (Prims callAt seqR ifOk sampled hint zOne aOne aGrp samples dot row compute)
open VG.Proof.MlDsa.X86_64.Verify (P0 PrimsOk primsWith prims_okWith verify_correct verify_ct)
open VG.Spec.MlDsa

/-- `mc` holds of every primitive of `P`. -/
structure PrimsM (mc : Prog isa → Bool) (P : Prims) : Prop where
  ntt : mc P.ntt = true
  invNtt : mc P.invNtt = true
  mul : mc P.mul = true
  mulAdd : mc P.mulAdd = true
  sub : mc P.sub = true
  rejNtt : mc P.rejNtt = true
  ball : mc P.ball = true
  useHint : mc P.useHint = true
  simpleBitPack : mc P.simpleBitPack = true
  bitUnpack : mc P.bitUnpack = true
  unpackT1 : mc P.unpackT1 = true
  hintUnpack : mc P.hintUnpack = true
  normLt : mc P.normLt = true
  rej4 : mc P.rej4 = true

section
variable {m mc : Prog isa → Bool} (hm : Comp m mc)
include hm

theorem Same.callAt {c : Prog isa} (hc : mc c = true) (n n' : String) (as : List (Reg × Impl.MlDsa.X86_64.Verify.Arg)) :
    Same m (VG.Impl.MlDsa.X86_64.Verify.callAt n c as) (VG.Impl.MlDsa.X86_64.Verify.callAt n' (.block []) as) :=
  Same.seq hm rfl (Same.call hm hc n n')

theorem Same.ifOk {c c' : Prog isa} (h : Same m c c') : Same m (VG.Impl.MlDsa.X86_64.Verify.ifOk c) (VG.Impl.MlDsa.X86_64.Verify.ifOk c') :=
  Same.seq hm rfl (Same.ite hm h rfl)

theorem Same.sampled {c c' : Prog isa} (h : Same m c c') (a : Impl.MlDsa.X86_64.Verify.Ptr) :
    Same m (VG.Impl.MlDsa.X86_64.Verify.sampled c a) (VG.Impl.MlDsa.X86_64.Verify.sampled c' a) :=
  Same.seq hm h rfl

variable {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Message.PrimsM mc P) (p : Params)
include hP

theorem verify_same : Same m (Impl.MlDsa.X86_64.Verify.verify P p) (Impl.MlDsa.X86_64.Verify.verify VG.Proof.MlDsa.X86_64.Verify.P0 p) := by
  have aOne : ∀ e, Same m (aOne P p e) (aOne VG.Proof.MlDsa.X86_64.Verify.P0 p e) := fun _ =>
    Same.seq hm rfl (Same.sampled hm (Same.callAt hm hP.rejNtt _ _ _) _)
  have dot : ∀ r, Same m (dot P p r) (dot VG.Proof.MlDsa.X86_64.Verify.P0 p r) := fun r =>
    Same.seq hm (Same.callAt hm hP.mul _ _ _) (Same.seqRV hm (fun _ => Same.callAt hm hP.mulAdd _ _ _) _ _)
  have row : ∀ r, Same m (row P p r) (row VG.Proof.MlDsa.X86_64.Verify.P0 p r) := fun r =>
    Same.seq hm (dot r) (Same.seq hm (Same.callAt hm hP.unpackT1 _ _ _) (Same.seq hm (Same.callAt hm hP.ntt _ _ _)
      (Same.seq hm (Same.callAt hm hP.mul _ _ _) (Same.seq hm (Same.callAt hm hP.sub _ _ _)
        (Same.seq hm (Same.callAt hm hP.invNtt _ _ _) (Same.seq hm (Same.callAt hm hP.useHint _ _ _)
          (Same.callAt hm hP.simpleBitPack _ _ _)))))))
  have aGrp : ∀ g, Same m (aGrp P p g) (aGrp VG.Proof.MlDsa.X86_64.Verify.P0 p g) := fun _ =>
    Same.seq hm rfl (Same.seq hm rfl (Same.seq hm rfl (Same.seq hm rfl
      (Same.seq hm (Same.callAt hm hP.rej4 _ _ _) rfl))))
  have samples : Same m (VG.Impl.MlDsa.X86_64.Verify.samples P p) (VG.Impl.MlDsa.X86_64.Verify.samples VG.Proof.MlDsa.X86_64.Verify.P0 p) :=
    Same.seq hm rfl (Same.seq hm (Same.seqRV hm aGrp _ _) (Same.seq hm (Same.seqRV hm aOne _ _)
      (Same.sampled hm (Same.callAt hm hP.ball _ _ _) _)))
  have compute : Same m (compute P p) (compute VG.Proof.MlDsa.X86_64.Verify.P0 p) :=
    Same.seq hm (Same.seqRV hm (fun _ => Same.callAt hm hP.ntt _ _ _) _ _) (Same.seq hm (Same.callAt hm hP.ntt _ _ _)
      (Same.seq hm (Same.seqRV hm row _ _) rfl))
  have zOne : ∀ i, Same m (zOne P p i) (zOne VG.Proof.MlDsa.X86_64.Verify.P0 p i) := fun _ =>
    Same.seq hm (Same.callAt hm hP.bitUnpack _ _ _) (Same.seq hm (Same.callAt hm hP.normLt _ _ _) rfl)
  exact Same.seq hm rfl (Same.seq hm (Same.seq hm (Same.seq hm (Same.callAt hm hP.hintUnpack _ _ _) rfl)
    (Same.ifOk hm (Same.seq hm (Same.seqRV hm zOne _ _) (Same.ifOk hm (Same.seq hm samples compute))))) rfl)

end

theorem verify0_noSp {p : Params} (h3 : Sign.Ok3 p) : noSpB (Impl.MlDsa.X86_64.Verify.verify VG.Proof.MlDsa.X86_64.Verify.P0 p) = true := by
  rcases h3 with rfl | rfl | rfl <;> decide +kernel

theorem verify0_depth {p : Params} (h3 : Sign.Ok3 p) :
    decide ((Impl.MlDsa.X86_64.Verify.verify VG.Proof.MlDsa.X86_64.Verify.P0 p).depth ≤ 4) = true := by
  rcases h3 with rfl | rfl | rfl <;> decide +kernel

/-- `mc` of every primitive, from what `PrimsOk` says of it. -/
theorem primsM_of {P : Prims} (C : PrimsOk P) {mc : Prog isa → Bool}
    (h : ∀ {c : Prog isa}, NoSp c → c.depth ≤ 3 → mc c = true) : VG.Proof.MlDsa.X86_64.Message.PrimsM mc P :=
  ⟨h C.ntt.nosp C.ntt.depth, h C.invNtt.nosp C.invNtt.depth, h C.mul.nosp C.mul.depth,
    h C.mulAdd.nosp C.mulAdd.depth, h C.sub.nosp C.sub.depth, h C.rejNtt.nosp C.rejNtt.depth,
    h C.ball.nosp C.ball.depth, h C.useHint.nosp C.useHint.depth, h C.simpleBitPack.nosp C.simpleBitPack.depth,
    h C.bitUnpack.nosp C.bitUnpack.depth, h C.unpackT1.nosp C.unpackT1.depth,
    h C.hintUnpack.nosp C.hintUnpack.depth, h C.normLt.nosp C.normLt.depth, h C.rej4.nosp C.rej4.depth⟩

/-- `vg_mldsa*_verify`, with the polynomial arithmetic of `v`. -/
theorem verifyFn (v : ArithImpl) {p : Params} (hp : p ∈ params) :
    VG.Proof.MlDsa.X86_64.Message.VerifyFn p (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) p) := by
  have h3 := ok3_of hp
  have hp' : p ∈ Verify.params := hp
  have C := prims_okWith v
  exact ⟨verify_correct C hp', verify_ct C hp',
    noSp_of (Same.ok (VG.Proof.MlDsa.X86_64.Message.verify_same (Comp.all _) (VG.Proof.MlDsa.X86_64.Message.primsM_of C fun h _ => noSpB_of h) p) (VG.Proof.MlDsa.X86_64.Message.verify0_noSp h3)),
    of_decide_eq_true (Same.ok (VG.Proof.MlDsa.X86_64.Message.verify_same (depthCompN 3) (VG.Proof.MlDsa.X86_64.Message.primsM_of C fun _ h => decide_eq_true h) p)
      (VG.Proof.MlDsa.X86_64.Message.verify0_depth h3))⟩

theorem verifyMessage_spSafe {p : Params} {n : String} {c : Prog isa} (hc : c.all (fun i => !isa.writesSp i) = true) :
    (Impl.MlDsa.X86_64.Message.verifyMessage n c p).all (fun i => !isa.writesSp i) = true := by
  generalize hq : (fun i => !isa.writesSp i) = q at hc ⊢
  have ha : Impl.Sha3.X86_64.Stream.absorb.all q = true := hq ▸ kabs_spSafe
  have hp' : Impl.Sha3.X86_64.Stream.pad.all q = true := hq ▸ kpad_spSafe
  have hs : Impl.Sha3.X86_64.Stream.squeeze.all q = true := hq ▸ ksqz_spSafe
  have hsa : ∀ as, (setArgs as).all q = true := fun as => hq ▸ setArgs_wsp as
  have hmv : ∀ a, (Arg.mov .rdi a).all q = true := fun a => hq ▸ arg_wsp .rdi (by decide) a
  simp only [Impl.MlDsa.X86_64.Message.verifyMessage, Impl.MlDsa.X86_64.Message.top,
    Impl.MlDsa.X86_64.Message.muHash, Impl.MlDsa.X86_64.Message.trHash, Impl.MlDsa.X86_64.Message.zeroSt,
    Impl.MlDsa.X86_64.Message.kabs, Impl.MlDsa.X86_64.Message.kpad, Impl.MlDsa.X86_64.Message.ksqz,
    Impl.MlDsa.X86_64.Message.callA, Code.all, hc, ha, hp', hs, hsa, hmv, Bool.and_true, Bool.true_and]
  subst hq
  decide

end VG.Proof.MlDsa.X86_64.Message

end
