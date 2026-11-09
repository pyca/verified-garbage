module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignPre
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.Rel
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Top
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.X86_64.Round
import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-DSA on x86-64, `sign_message`: the call of the signing function on `μ`

Untrusted: everything here is checked by Lean. Any code that meets the
contract the proof of `vg_mldsa*_sign` is written against (`signK p 32`),
never writes `rsp` and whose calls nest at most three deep (`SignFn`): its
call from the frame, on the key, `μ` at `X + 840`, `rnd`, `sig` and the
first `scratchWords p` words of `scratch` (`signCall_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.X86_64.Sign (signK scrLen skL)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A signing function on `μ` that `sign_message` can call. -/
structure SignFn (p : Params) (c : Prog isa) : Prop where
  ok : ∀ s, (signK p 32).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (signK p 32).post s s'
  ct : ConstantTime isa (signK p 32).pre (signK p 32).pub c
  nosp : NoSp c
  depth : c.depth ≤ 4

/-- The arguments of the call of the signing function on `μ`. -/
abbrev signArgs (p : Params) (prep : Bool) : List Arg :=
  [.slot fKey, aMu p, .slot fRnd, .slot fSig, .slot fScr, .imm (flagOf prep)]

/-- A prepared key is in the bytes of its region. -/
theorem prepared_congr {p : Params} {m m' : Mem} {a : Addr}
    (hb : bytesAt m' a (preparedSecretKeyBytes p) = bytesAt m a (preparedSecretKeyBytes p))
    (h : PreparedSecretKey p m a) : PreparedSecretKey p m' a := by
  have hl : p.skLen + 1024 * (p.ℓ + 2 * p.k) = preparedSecretKeyBytes p := by
    simp only [preparedSecretKeyBytes, n]
  have hsk : bytesAt m' a p.skLen = bytesAt m a p.skLen := by
    rw [← Proof.MlKem.bytesAt_take m' a (show p.skLen ≤ preparedSecretKeyBytes p by omega), hb,
      Proof.MlKem.bytesAt_take m a (show p.skLen ≤ preparedSecretKeyBytes p by omega)]
  intro i hi
  rw [hsk]
  have e4 : 4 * n * i = 1024 * i := by simp only [n]
  have hk : p.skLen + 4 * n * i + 1024 ≤ preparedSecretKeyBytes p := by rw [e4]; omega
  refine polyStored_iff.mpr (PreparedKey.polyIs_of_copy ?_ (polyStored_iff.mp (h i hi)))
  rw [← Proof.MlKem.bytesAt_slice _ _ hk, hb, Proof.MlKem.bytesAt_slice _ _ hk]

section
variable {p : Params} {prep : Bool} {s : State}

/-- The working space of the signing function on `μ`. -/
abbrev rScrMu (p : Params) (s : State) : Region := ⟨stackArg s 1, scrLen p⟩

theorem scrMu_sub (p : Params) (s : State) : Region.Sub (rScrMu p s) (rScr p s) :=
  Region.sub_prefix (by rw [mScr_eq]; simp [scrLen, oE])

theorem mu_within (p : Params) (prep : Bool) (s : State) : Within ⟨(slay p prep s).MU, 64⟩ (rScr p s) :=
  (within_off (slay p prep s).X (d := 840) (n := 64) (k := 1024) (by omega)).trans (slay_X p prep s)

theorem mu_scrMu {p : Params} (hp : p ∈ params) (prep : Bool) (s : State) : Region.Disjoint ⟨(slay p prep s).MU, 64⟩ (rScrMu p s) := by
  show Region.Disjoint ⟨stackArg s 1 + BitVec.ofNat 64 (oE p) + BitVec.ofNat 64 840, 64⟩ ⟨stackArg s 1, scrLen p⟩
  rw [add_add]
  exact Offset.disjoint_base _ (by simp [scrLen, oE]) (by have := oE_lt hp; omega)

/-- The regions the signing function on `μ` reads and writes. -/
abbrev signRd (p : Params) (prep : Bool) (s : State) : List Region :=
  [⟨s.gpr .rdi, keyLen p prep⟩, ⟨(slay p prep s).MU, 64⟩, ⟨s.gpr .r9, 32⟩]
abbrev signWr (p : Params) (s : State) : List Region := [⟨stackArg s 0, p.sigLen⟩, rScrMu p s]

theorem signArgs_ok (hp : p ∈ params) : (signArgs p prep).all Arg.ok = true := by
  have := oE_lt hp
  have : flagOf prep < 2 ^ 31 := by cases prep <;> decide
  simp only [signArgs, Impl.MlDsa.X86_64.Message.aMu, List.all_cons, List.all_nil, Arg.ok, fKey, fRnd, fSig,
    fScr, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- The registers after the moves of the arguments. -/
theorem signRegs_of {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : Ctx (slay p prep s) g mx m₀ t) (hm : Moved (signArgs p prep) t t1) :
    t1.gpr .rdi = s.gpr .rdi ∧ t1.gpr .rsi = (slay p prep s).MU ∧ t1.gpr .rdx = s.gpr .r9 ∧
      t1.gpr .rcx = stackArg s 0 ∧ t1.gpr .r8 = stackArg s 1 ∧ t1.gpr .r9 = BitVec.ofNat 64 (flagOf prep) := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hm.1.1
  rw [hc.slot, fKey, hc.pKey] at e1
  rw [hc.aMu p rfl] at e2
  rw [hc.slot, fRnd, hc.pRnd] at e3
  rw [hc.slot, fSig, hc.pSig] at e4
  rw [hc.slot, fScr, hc.pScr] at e5
  exact ⟨e1, e2, e3, e4, e5, e6⟩

/-- The precondition of the signing function on `μ`, on entry to it. -/
theorem signK_pre (hp : p ∈ params) (h : SPre p prep s) (h8 : (s.gpr .r8).toNat < 256) {g : Reg → BitVec 64}
    {mx : BitVec 32} {m₀ : Mem} {t t1 : State} (hc : Ctx (slay p prep s) g mx m₀ t) (hm₀ : s.mem = m₀)
    (hm : Moved (signArgs p prep) t t1) :
    (signK p 32).pre (t1.callEntry.withRegions (signRd p prep s) (signWr p s)) := by
  have hL := slay_ok hp h h8
  have hc1 : Ctx (slay p prep s) g mx m₀ t1 :=
    hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := signRegs_of hc hm
  have hK := keyLen_ge hp prep
  -- The prepared key, unchanged until the call.
  have hkey : prep = true → PreparedSecretKey p (t1.callEntry.withRegions (signRd p prep s) (signWr p s)).mem
      (s.gpr .rdi) := fun hpr => by
    refine prepared_congr ?_ (h.prepK hpr)
    have hk : keyLen p prep = preparedSecretKeyBytes p := by simp [keyLen, hpr]
    rw [State.withRegions_mem, ← hk, hc1.ce_bytesAt (p := s.gpr .rdi) (hL.stk_r h.stkSk (by omega))
      (by have := h.nSk; omega), hm.1.2.1, hc.bytesAt_eq (p := s.gpr .rdi) (n := keyLen p prep) hL.xKey hL.kKey
      (by have := h.nSk; omega), hm₀]
  have hL9 : skL p (t1.callEntry.withRegions (signRd p prep s) (signWr p s)) = keyLen p prep := by
    rw [skL, gpr_ce t1 _ _ (by decide : Reg.r9 ≠ .rsp), e6]
    cases prep <;> simp [flagOf, keyLen]
  have h9 : (t1.callEntry.withRegions (signRd p prep s) (signWr p s)).gpr .r9 ≠ 0 → prep = true := by
    rw [gpr_ce t1 _ _ (by decide : Reg.r9 ≠ .rsp), e6]
    cases prep <;> simp [flagOf]
  simp only [signK, hL9, State.withRegions_rd, State.withRegions_wr, gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.r8 ≠ .rsp), rsp_ce,
    e1, e2, e3, e4, e5, Sign.retR, hc1.rsp, sp_sub8, below32]
  have hsub := scrMu_sub p s
  have hmu := (mu_within p prep s).sub
  have hB := hL.nB
  have hn := h.nScr
  have hE := oE_lt hp
  refine ⟨trivial, trivial, h.skSig, h.skScr.sub_right hsub, h.sigScr.symm.sub_left hmu, mu_scrMu hp prep s, h.rndSig,
    h.rndScr.sub_right hsub, h.sigScr.sub_right hsub, hL.stk_r h.stkSk (by omega),
    hL.stk_x (d := 32) (n := 8) (e := 840) (k := 64) (by omega) (by omega), hL.stk_r h.stkRnd (by omega),
    hL.stk_r h.stkSig (by omega), hL.stk_r (h.stkScr.sub_right hsub) (by omega), ?_, ?_, ?_, ?_, ?_, h.nSk, ?_,
    h.nRnd, h.nSig, by simp only [mScrLen, scrLen, messageScratchWords] at hn ⊢; omega, ?_,
    fun h9' => hkey (h9 h9')⟩
  · exact h.stkSk.sub_left (Region.sub_prefix (by omega))
  · exact (hL.kX.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by omega))
  · exact h.stkRnd.sub_left (Region.sub_prefix (by omega))
  · exact h.stkSig.sub_left (Region.sub_prefix (by omega))
  · exact (h.stkScr.sub_right hsub).sub_left (Region.sub_prefix (by omega))
  · exact mu_nowrap h
  · rw [toNat_add_ofNat (by omega)]; omega


/-- The call of the signing function on `μ`. -/
theorem signCall_ok {n : String} {c : Prog isa} (hS : SignFn p c) (hp : p ∈ params) (h : SPre p prep s)
    (h8 : (s.gpr .r8).toNat < 256) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx (slay p prep s) g mx m₀ t) (hm₀ : s.mem = m₀) :
    WP isa (callA n c (signArgs p prep)) t fun s' =>
      s'.rd = t.rd ∧ s'.wr = t.wr ∧ s'.gpr .rsp = t.gpr .rsp ∧ (∀ r ∈ calleeSaved, s'.gpr r = t.gpr r) ∧
      s'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧
      Frame [rSig p s, rScrMu p s, ⟨(slay p prep s).B, 40⟩] t.mem s'.mem ∧
      Outcome (fun b => signMu p b (bytesAt t.mem (s.gpr .rdi) p.skLen) (bytesAt t.mem (slay p prep s).MU 64)
          (bytesAt t.mem (s.gpr .r9) 32)) ((s'.gpr .rax).setWidth 32)
        (bytesAt s'.mem (stackArg s 0) p.sigLen) := by
  have hL := slay_ok hp h h8
  refine WP.seq (WP.mono (setArgs_ok _ (signArgs_ok hp) t hc.frOk) fun t1 hm => ?_)
  obtain ⟨⟨hA, hm', hx⟩, k⟩ := hm
  have hc1 : Ctx (slay p prep s) g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm' hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := signRegs_of hc ⟨⟨hA, hm', hx⟩, k⟩
  have hpre := signK_pre hp h h8 hc hm₀ ⟨⟨hA, hm', hx⟩, k⟩
  have hm := hm'
  have hdep := hS.depth
  have hsub := scrMu_sub p s
  have hrsp1 : t1.gpr .rsp = (slay p prep s).SP := hc1.rsp
  refine WP.call_mx hS.ok hS.nosp (by omega) hpre ?_ ?_ fun s' hrd hwr hcs hf _ hpost hmx => ?_
  · rw [hc1.rd, hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨rSk p prep s, by simp [slay, h.rd], within_self _⟩
    · exact ⟨rScr p s, by simp [slay, h.wr], mu_within p prep s⟩
    · exact ⟨rRnd s, by simp [slay, h.rd], within_self _⟩
    · exact ⟨rSig p s, by simp [slay, h.wr], within_self _⟩
    · exact ⟨rScr p s, by simp [slay, h.wr], within_base _ (by rw [mScr_eq]; simp [scrLen, oE])⟩
  · rw [hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨rSig p s, by simp [slay, h.wr], within_self _⟩
    · exact ⟨rScr p s, by simp [slay, h.wr], within_base _ (by rw [mScr_eq]; simp [scrLen, oE])⟩
  obtain ⟨s₂, hm₂, hg₂, hq⟩ := hpost
  refine ⟨hrd.trans k.2.1, hwr.trans k.2.2, by rw [hcs .rsp (by decide), k.gpr (by decide)],
    fun r hr => by rw [hcs r hr, k.gpr (argRegs_cs r hr)], by rw [hmx, hx], ?_, ?_⟩
  · rw [← hm]
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨rSig p s, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨rScrMu p s, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨⟨(slay p prep s).B, 40⟩, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), ?_⟩
      rw [hrsp1]
      exact below_call_sub _ (by omega)
  · simp only [signK, State.withRegions_mem, gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), e1, e2, e3, e4, hm₂] at hq
    have hL := slay_ok hp h h8
    have hK := keyLen_ge hp prep
    rw [hc1.ce_bytesAt (p := s.gpr .rdi) (n := p.skLen)
        ((hL.stk_r h.stkSk (by omega)).sub_right (Region.sub_prefix hK.2.2)) (by have := h.nSk; omega),
      hc1.ce_bytesAt (p := (slay p prep s).MU) (hL.stk_x (d := 32) (n := 8) (e := 840) (k := 64) (by omega)
        (by omega)) (by omega),
      hc1.ce_bytesAt (p := s.gpr .r9) (hL.stk_r h.stkRnd (by omega)) (by omega), hm,
      hg₂ _ (by decide)] at hq
    exact hq
