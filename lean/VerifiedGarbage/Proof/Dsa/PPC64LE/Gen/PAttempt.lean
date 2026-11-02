module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.PArith
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.PX
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: one candidate p

`pAttempt` (`pAttempt_vp`): X, p from it, and unless p is below
`2^(L − 1)` (`topBit_vp`) its probable-prime test: `fP` := 0 if the
witnesses ran out, 1 if p is a probable prime, else as it was.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

theorem top_bit (b : BitVec 8) : (b.setWidth 64 >>> 7 == 0) = decide (b.toNat < 128) := by
  revert b; decide

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- `r0 = 0` iff the `pLen` big-endian bytes of `pv` at `sPBE` are below `2^(8 pLen − 1)`. -/
theorem topBit_vp {pv : Nat} (hc : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c.cl) (hpv : pv < 256 ^ G.pLen) :
    VP (St G c X) (.block [.lbz .r0 .r28 sPBE, .lsr .d .r0 .r0 7])
      (fun σ t => St G c X σ t ∧ isa.eval (.zero .d .r0) t = some (decide (pv < 2 ^ (8 * G.pLen - 1)))) := by
  refine VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28]) (.block [.lbz .r0 .r28 sPBE, .lsr .d .r0 .r0 7]), rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have l := h.lens
  have hkw : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega
  have hp0 : 0 < G.pLen := by rcases l with e | e | e <;> rw [e] <;> decide
  have nP : sPBE = 1056 := rfl
  have hkB : sPBE + G.pLen ≤ kB G.pLen := by rcases l with e | e | e <;> rw [e] <;> decide
  refine WP.sp_eq ?_
  refine wp_lbz (by decide) (by decide) (by rw [gi.r28]) (gi.inRdWr (by omega)) fun s₁ u₁ => ?_
  refine WP.wr (exec_lsr_d (by decide)) fun t u sp _ => WP.block_nil fun sp' => ⟨⟨h.of_keep
    (ws := [.r0]) ⟨fun r hr => by rw [u.other _ (by simpa using hr), u₁.other _ (by simpa using hr)],
      by rw [u.rd, u₁.rd], by rw [u.wr, u₁.wr]⟩ (by rw [u.mem, u₁.mem]) sp', x⟩, ?_⟩
  -- The byte: p's first.
  have b := h.sb _ hc
  simp only at b
  rw [VG.Proof.Rsa.i2osp_length] at b
  have byte : s.mem (G.sa sPBE) = (Spec.Rsa.i2osp pv G.pLen).getD 0 0 := by
    rw [← b]; simp [Spec.Rsa.bytesAt, hp0]
  rw [eval_zero, u.gpr, u₁.gpr, byte, top_bit]
  congr 1
  rw [← VG.Proof.Dsa.encodeBE_i2osp]
  exact decide_eq_decide.mpr (VG.Proof.Dsa.Generation.candidate_firstByte hp0 hpv)

theorem varOk_fP : VarOk G fP := varOk_of (by decide)

/-- The stage after a test's result recorded in `fP`. -/
def pRes (c0 : Cfg) (wl : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → Cfg
  | none => (testCfg c0 c0.cl wl none).setV fP (BitVec.ofNat 64 0)
  | some (true, r) => (testCfg c0 c0.cl wl (some (true, r))).setV fP (BitVec.ofNat 64 1)
  | some (false, r) => testCfg c0 c0.cl wl (some (false, r))

theorem testCfg_fRes (c0 : Cfg) (cl : Claims) (wl : Nat) (res : Option (Bool × Spec.RsaKeyGen.Rand)) :
    fRes ∈ (testCfg c0 cl wl res).LS ∧
      (testCfg c0 cl wl res).V fRes = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status res) := by
  rcases res with _ | ⟨b, r⟩
  · exact ⟨List.mem_cons_self, by simp [testCfg, Proof.Dsa.ProbablePrime.status]⟩
  · refine ⟨List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    simp only [testCfg, Cfg.setV]
    rw [upd_ne _ _ (by decide), upd_self]
    cases b <;> rfl

/-- `fP` := 0 if the witnesses ran out, 1 for a probable prime. -/
theorem pDecide_vp {c0 : Cfg} {wl : Nat} (res : Option (Bool × Spec.RsaKeyGen.Rand)) :
    VP (St G (testCfg c0 c0.cl wl res) X)
      (VG.Impl.Rsa.PPC64LE.Keys.seqs [.block (cmpF fRes 0), .ite (.zero .d .r0) (.block (stImm fP 0))
        (VG.Impl.Rsa.PPC64LE.Keys.seqs [.block (cmpF fRes 1), .ite (.zero .d .r0) (.block (stImm fP 1))
          (.block [])])])
      (St G (pRes c0 wl res) X) := by
  obtain ⟨fl, fv⟩ := testCfg_fRes c0 c0.cl wl res
  have vres : ∀ σ s, St G (testCfg c0 c0.cl wl res) X σ s →
      fw s.mem G fRes = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status res) := fun σ s h => by
    rw [h.1.gi.slotV fl, fv]
  refine VP.seq (cmpF_vp (fun σ s h => h.1) (by decide) (by decide) (by decide) vres
    fun σ s t h h' _ e => (⟨⟨h', h.2⟩, e⟩ : St G (testCfg c0 c0.cl wl res) X σ t ∧ _)) ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · rcases res with _ | ⟨b, r⟩
    · exact stImm_vp (c := fun _ => testCfg c0 c0.cl wl none) (fun σ s h => h.1.1.1) (by decide) varOk_fP
        fun σ s t h h' _ => ⟨h', h.1.1.2⟩
    · refine VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => ?_
      rw [e] at z
      unfold Proof.Dsa.ProbablePrime.status at z
      cases b <;> simp at z <;> contradiction
  · rcases res with _ | ⟨b, r⟩
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by
        rw [e] at z; simp [Proof.Dsa.ProbablePrime.status] at z <;> contradiction
    refine VP.seq (cmpF_vp (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
      (fun σ s h => vres σ s h.1.1) fun σ s t h h' _ e => (⟨⟨h', h.1.1.2⟩, e⟩ :
        St G (testCfg c0 c0.cl wl (some (b, r))) X σ t ∧ _)) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
    · cases b
      · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by
          rw [e] at z; simp [Proof.Dsa.ProbablePrime.status] at z <;> contradiction
      · exact stImm_vp (c := fun _ => testCfg c0 c0.cl wl (some (true, r))) (fun σ s h => h.1.1.1) (by decide)
          varOk_fP fun σ s t h h' _ => ⟨h', h.1.1.2⟩
    · cases b
      · exact VP.block_nil fun σ s h => h.1.1
      · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by
          rw [e] at z; simp [Proof.Dsa.ProbablePrime.status] at z <;> contradiction

/-- The claims kept through a candidate p: the padding and q. -/
abbrev pRest {B N L : Nat} (md : MdStream.Md B N L) (G : GP) (k : Nat) : Claims :=
  [(sMsg + G.qLen, padTail md G.qLen), (sQ, qBytes G k)]

/-- The stage after a candidate p from X (`xv`) and q (`qv`), tested with the
witnesses from `u` unless it is too short. -/
def pAttCfg (c : Cfg) (G : GP) (xv qv : Nat) (rest : Claims) (u : Nat) : Cfg :=
  if pVal xv qv < 2 ^ (8 * G.pLen - 1) then pOut c G xv qv rest
  else pRes (pOut c G xv qv rest) G.witLen (Spec.Dsa.probablePrime (pVal xv qv) (G.witB.drop u))

theorem pAttempt_vp {g : Geo} (HO : HashOk g.G) {Lp : Impl.Dsa.ProbablePrime.Layout} (okp : PrimeOk Lp g.pCode)
    (hLb : Lp.bits = 8 * G.pLen) (hLc : Lp.candidate = g.pCand) (hsize : Lp.size ≤ 8 * wWords G.pLen)
    (hL : ∀ r ∈ Lp.scratch, r.1 + r.2 ≤ 8 * wWords G.pLen)
    (hcand : Lp.candidate + Lp.bits / 8 ≤ 8 * wWords G.pLen) (hcand15 : wB G.pLen + Lp.candidate < 2 ^ 15)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    {k off u : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen)
    (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 64 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hoff : off + (cnt G + 1) < 2 ^ 32)
    (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u)
    (hU' : ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut) (hU88 : fUsedOut ∉ c.LS) :
    VP (St G (pCfg c HO G k off 0 [(sQ, qBytes G k)]) X) g.pAttempt
      (St G (pAttCfg c G (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k))
        (pRest HO.md G k) u) X) := by
  have hq56 : G.qLen < 56 := by omega_arith
  have pl := padTail_length HO.md hq56 HO.hL
  have hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega_arith
  have hHl : ∀ j, (hX HO G k off j).length = G.qLen := fun j => by
    rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega_arith), HO.md.digest_length, HO.hN, hk4]
  have hc : (cnt G + 1) * G.qLen ≤ G.pLen + 32 ∧ G.pLen ≤ (cnt G + 1) * G.qLen := by
    rcases hlq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [cnt, e1, e2] <;> decide
  have xl : (xBytes HO G k off).length = G.pLen := by
    rw [xBytes, VG.Proof.Ffdh.ParameterCandidate.topCut_length (by
      rw [← List.length_pos_iff, List.length_drop, accB_length HO hHl]; omega_arith), List.length_drop,
      accB_length HO hHl]; omega_arith
  have hHq : (Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k)).length = G.qLen := by
    rw [← hH, HO.hash _ (by omega_arith), HO.md.digest_length, HO.hN, hk4]
  have hne : Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k) ≠ [] := fun e => by rw [e] at hHq; simp at hHq; omega_arith
  have ql : (qBytes G k).length = G.qLen := by
    rw [qBytes, VG.Proof.Ffdh.ParameterCandidate.shapedOctets, VG.Proof.Ffdh.ParameterCandidate.lastOne_length
      (by rw [← List.length_pos_iff, VG.Proof.Ffdh.ParameterCandidate.topCut_length hne]; omega_arith),
      VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, hHq]
  have hqv : Spec.Dsa.decodeBE (qBytes G k) = Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k) :=
    VG.Proof.Dsa.Generation.qCandidate_octets (by omega_arith) _ (by rw [hHq])
  have qlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G k) := by
    rw [hqv]; exact (VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * G.qLen) (by omega_arith) (seedAt G k)).2.1
  have nX : sX = 672 := rfl
  have nM : sMsg = 512 := rfl
  have nS : sState = 576 := rfl
  have nQ : sQ = 608 := rfl
  have nP : sPBE = 1056 := rfl
  have nE : sE = 1440 := rfl
  have hkB : sE + G.pLen ≤ kB G.pLen := by rcases hlq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  have hkw : kB G.pLen ≤ wB G.pLen := by simp only [wB]; omega
  have eB : eBytes G.pLen G.qLen ≤ G.pLen := by simp only [eBytes]; omega
  unfold Geo.pAttempt
  simp only [VG.Impl.Rsa.PPC64LE.Keys.seqs]
  rw [hp, hq]
  refine VP.seq (pX_vp HO hlq hp hq hk4 hsb hk hS hSv hO hOv hoff (rest := [(sQ, qBytes G k)]) fun y hy => by
    rw [List.mem_singleton] at hy; subst hy
    simp only [Apart, ql, pStart]; omega_arith) ?_
  refine VP.seq ((pArith_vp hlq (by simp) xl (by simp) ql qlo (rest := pRest HO.md G k) fun y hy => by
    simp only [pRest, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact ⟨by simp, by simp only [Apart, pl]; omega_arith, by simp only [Apart, pl]; omega_arith⟩
    · exact ⟨by simp, by simp only [Apart, ql]; omega_arith, by simp only [Apart, ql]; omega_arith⟩).mono
      (fun _ _ h => h) fun _ _ h => h.1) ?_
  have xlt : Spec.Dsa.decodeBE (xBytes HO G k off) < 2 ^ (8 * G.pLen) := by
    have := VG.Proof.Dsa.decodeBE_lt (xBytes HO G k off)
    rwa [xl, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  have plt := pVal_lt (q := Spec.Dsa.decodeBE (qBytes G k)) (show 1 ≤ 8 * G.pLen by omega_arith) xlt
  have plt' : pVal (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k)) < 256 ^ G.pLen := by
    rwa [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  refine VP.seq (topBit_vp (by simp) plt') ?_
  generalize hpv : pVal (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k)) = pv at plt plt'
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · by_cases hcnd : pv < 2 ^ (8 * G.pLen - 1)
    · refine VP.block_nil fun σ s ⟨⟨h, _⟩, _⟩ => ?_
      unfold pAttCfg
      rw [hpv]
      simp only [hcnd, ↓reduceIte]
      exact h
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hcnd] at z
  · by_cases hcnd : pv < 2 ^ (8 * G.pLen - 1)
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hcnd] at z
    have pb : Spec.Dsa.decodeBE (Spec.Rsa.i2osp pv G.pLen) = pv := by
      rw [VG.Proof.Dsa.decodeBE_os2ip, VG.Proof.Rsa.os2ip_i2osp, Nat.mod_eq_of_lt plt']
    have podd : pv % 2 = 1 := hpv ▸ VG.Proof.Dsa.Generation.pReduction_odd _ _
    have pbl : Spec.Dsa.bitLength pv = 8 * G.pLen :=
      (VG.Proof.Dsa.bitLength_iff_bounds (by omega_arith)).mpr ⟨by omega_arith, plt⟩
    unfold pAttCfg
    rw [hpv]
    simp only [hcnd, ↓reduceIte]
    generalize hc0 : pOut c G (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k))
      (pRest HO.md G k) = c0
    have cl0 : c0.cl = (sE, Spec.Rsa.i2osp ((pv - 1) / Spec.Dsa.decodeBE (qBytes G k)) (eBytes G.pLen G.qLen)) ::
        (sPBE, Spec.Rsa.i2osp pv G.pLen) :: pRest HO.md G k := by rw [← hc0, ← hpv]
    have eLS : c0.LS = c.LS := by rw [← hc0]
    have eV : c0.V = c.V := by rw [← hc0]
    have small : ∀ y ∈ c0.cl, y.1 + y.2.length ≤ kB G.pLen := fun y hy => by
      rw [cl0] at hy
      simp only [pRest, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · simp only [VG.Proof.Rsa.i2osp_length]; omega_arith
      · simp only [VG.Proof.Rsa.i2osp_length]; omega_arith
      · simp only [pl]; omega_arith
      · simp only [ql]; omega_arith
    have pin : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c0.cl := by rw [cl0]; simp
    have := test_vp (X := X) (c := c0) (cb := Spec.Rsa.i2osp pv G.pLen) (src := sPBE) (cl' := c0.cl)
      (name := g.pName) okp hu (by rw [eLS]; exact hU) (by rw [eV]; exact hUv) hwl hsize hL hcand hcand15 pin
      (by rw [VG.Proof.Rsa.i2osp_length]; omega_arith) (by rw [VG.Proof.Rsa.i2osp_length, hLb]; omega_arith)
      (by rw [VG.Proof.Rsa.i2osp_length]; omega_arith) (by rw [VG.Proof.Rsa.i2osp_length]; omega_arith)
      (by decide) (by rw [pb]; exact podd) (by rw [pb, hLb, pbl]) (by rw [eLS]; exact hU') (by rw [eLS]; exact hU88)
      fun y hy => ⟨List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hy, by
        have := small y hy; simp only [Apart, decide_eq_true_eq]; omega_arith⟩),
        fun r _ => .inl (by have := small y hy; omega_arith)⟩
    rw [VG.Proof.Rsa.i2osp_length, hLc] at this
    refine VP.seq (this.mono (fun σ s h => h.1.1) fun _ _ h => h) ?_
    rw [tRes, pb]
    exact pDecide_vp _

end

end VG.Proof.Dsa.PPC64LE.Gen
