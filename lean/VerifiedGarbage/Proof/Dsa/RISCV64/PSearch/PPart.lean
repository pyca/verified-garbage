module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.PArith
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.PX
public import VerifiedGarbage.Proof.Dsa.Generation.Search
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Test
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix

-- separate module: p's search (`pPart_vp`), which builds beside q's part and the generator's (`QPart`, `GCheck`), all of which the seed's attempt imports

/-! # DSA parameter search on RISC-V: the search for p

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/PAttempt.lean`, `PPart.lean`,
`PLoop.lean`). `pAttempt` (`pAttempt_vp`): X, p from it (`pArith_vp`), and
unless p is below `2^(L − 1)` (`topBit_vp`) its probable-prime test with the
tape from the cursor: `fP` := 0 if the tape ran out, 1 if p is a probable
prime, else as it was. `pAdvance_vp`: the next counter; `pCont_vp` and
`pExit_vp`: the code after a candidate (`pTail`), which goes on to the next
counter, or ends the search; the search's stages, as
`Spec.Dsa.primeFromSeed` searches the counters (`pSpec`, `pCount`, `pU`,
`pFin`). `pGo_vp`: after a candidate that is not p, the next counter (or
`fP` := 2 after the last); `pStop_vp`: after one that ends the search;
`pBody_vp`: the iteration, by the cases of the spec's search; `pPart_vp`:
the search.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.Dsa.RISCV64.ParameterSearch

theorem top_bit (b : BitVec 8) : (b.setWidth 64 >>> 7 == 0) = decide (b.toNat < 128) := by
  revert b; decide

/-- X's hashes reach at most 12 bytes past its `pLen`. -/
theorem cnt_q (G : GP) (h : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) :
    (cnt G + 1) * G.qLen ≤ G.pLen + 12 := by
  rcases h with e | e | e <;> simp only [cnt, GP.qLen, e] <;> decide

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The block that reads p's top bit. -/
abbrev topBitOps : List Instr := [.load .b .t2 .s6 sPBE, .shift .srl .d .t2 .t2 7]

/-- `t2 = 0` iff the `pLen` big-endian bytes of `pv` at `sPBE` are below `2^(8 pLen − 1)`. -/
theorem topBit_vp {pv : Nat} (hc : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c.cl) (hpv : pv < 256 ^ G.pLen) :
    VP (St G c X) (.block topBitOps)
      (fun σ t => St G c X σ t ∧ isa.eval (.zero .t2) t = some (decide (pv < 2 ^ (8 * G.pLen - 1)))) := by
  refine VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64
      (Taint.ofRegs [.s6]) (.block topBitOps), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_
  have gi := h.gi
  have qB := q_bounds G gi
  have l := h.lens
  have hp0 : 0 < G.pLen := by rcases l with e | e | e <;> omega
  have hp3 : G.pLen ≤ 384 := by rcases l with e | e | e <;> omega
  have nP : sPBE = 960 := rfl
  refine WP.sp_eq ?_
  refine wp_lbu (by decide) (by rw [gi.s6]) (gi.inRdWr (by omega)) fun s₁ u₁ => ?_
  refine WP.wr (exec_shift_d (by decide)) fun t u => WP.block_nil fun sp' => ⟨⟨h.of_keep
    (ws := [.t2]) ⟨fun r hr => by rw [u.other _ (by simpa using hr), u₁.other _ (by simpa using hr)],
      by rw [u.rd, u₁.rd], by rw [u.wr, u₁.wr]⟩ (by rw [u.mem, u₁.mem]) sp', x⟩, ?_⟩
  -- The byte: p's first.
  have b := h.sb _ hc
  simp only at b
  rw [VG.Proof.Rsa.i2osp_length] at b
  have byte : s.mem (G.sa sPBE) = (Spec.Rsa.i2osp pv G.pLen).getD 0 0 := by
    rw [← b]; simp [Spec.Rsa.bytesAt, hp0]
  rw [eval_zero, u.gpr, u₁.gpr, byte]
  show some ((((Spec.Rsa.i2osp pv G.pLen).getD 0 0).setWidth 64 : BitVec 64) >>> (7 : Nat) == 0) = _
  rw [top_bit]
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

/-- `fP` := 0 if the tape ran out, 1 for a probable prime. -/
theorem pDecide_vp {c0 : Cfg} {wl : Nat} (res : Option (Bool × Spec.RsaKeyGen.Rand)) :
    VP (St G (testCfg c0 c0.cl wl res) X)
      (Impl.Rsa.RISCV64.Keys.seqs [.block (cmpF fRes 0), .ite (.zero .t2) (.block (stImm fP 0))
        (Impl.Rsa.RISCV64.Keys.seqs [.block (cmpF fRes 1), .ite (.zero .t2) (.block (stImm fP 1))
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
tape from `u` unless it is too short. -/
def pAttCfg (c : Cfg) (G : GP) (xv qv : Nat) (rest : Claims) (u : Nat) : Cfg :=
  if pVal xv qv < 2 ^ (8 * G.pLen - 1) then pOut c G xv qv rest
  else pRes (pOut c G xv qv rest) G.randLen (Spec.Dsa.probablePrime (pVal xv qv) (G.randB.drop u))

theorem pAttempt_vp {g : Geo} (HO : HashOk g.G) {Lp : Impl.Dsa.ProbablePrime.Layout} (okp : PrimeOk Lp g.pCode)
    (hLb : Lp.bits = 8 * G.pLen) (hc0 : Lp.candidate = 0) (hsize : Lp.size ≤ 256 * G.pLen)
    (hL : ∀ r ∈ Lp.scratch, r.1 + r.2 ≤ 256 * G.pLen)
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hwl : G.randB.length = G.randLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m)
    {k off u : Nat} (hk : k + G.qLen ≤ G.randLen) (hu : u ≤ G.randLen)
    (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.rand + BitVec.ofNat 64 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hoff : off + (cnt G + 1) < 2 ^ 32)
    (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u)
    (hU' : ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut) (hU88 : fUsedOut ∉ c.LS) :
    VP (St G (pCfg c HO G k off 0 [(sQ, qBytes G k)]) X) g.pAttempt
      (St G (pAttCfg c G (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k))
        (pRest HO.md G k) u) X) := by
  refine VP.byLens fun hlens => ?_
  have hqc2 := G.qLen_cases
  have hq56 : G.qLen < 56 := by omega
  have pl := padTail_length HO.md hq56 rfl
  have hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hwl]; omega
  have hHl : ∀ j, (hX HO G k off j).length = G.qLen := fun j => by
    rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega), HO.md.digest_length, hk4]
  have hc := cnt_facts G hlens
  have hcq := cnt_q G hlens
  have xl : (xBytes HO G k off).length = G.pLen := by
    rw [xBytes, VG.Proof.Ffdh.ParameterCandidate.topCut_length (by
      rw [← List.length_pos_iff, List.length_drop, accB_length HO hHl]; omega), List.length_drop,
      accB_length HO hHl]; omega
  have hHq : (Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k)).length = G.qLen := by
    rw [← hH, HO.hash _ (by omega), HO.md.digest_length, hk4]
  have hne : Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k) ≠ [] := fun e => by rw [e] at hHq; simp at hHq; omega
  have ql : (qBytes G k).length = G.qLen := by
    rw [qBytes, VG.Proof.Ffdh.ParameterCandidate.shapedOctets, VG.Proof.Ffdh.ParameterCandidate.lastOne_length
      (by rw [← List.length_pos_iff, VG.Proof.Ffdh.ParameterCandidate.topCut_length hne]; omega),
      VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, hHq]
  have hqv : Spec.Dsa.decodeBE (qBytes G k) = Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k) :=
    VG.Proof.Dsa.Generation.qCandidate_octets (by omega) _ (by rw [hHq])
  have qlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G k) := by
    rw [hqv]; exact (VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * G.qLen) (by omega) (seedAt G k)).2.1
  have nX : sX = 576 := rfl
  have nM : sMsg = 320 := rfl
  have nS : sState = 384 := rfl
  have nC : sCS = 416 := rfl
  have nQ : sQ = 512 := rfl
  have nP : sPBE = 960 := rfl
  have nE : sE = 1344 := rfl
  have k8 := kB_ge G.pLen
  have hkw := kB_le_wB G.pLen
  have eB : eBytes G.pLen G.qLen ≤ G.pLen := by simp only [eBytes]; omega
  unfold Geo.pAttempt
  simp only [Impl.Rsa.RISCV64.Keys.seqs]
  rw [hp, hq]
  refine VP.seq (pX_vp HO hp hq hk4 hwl hk hS hSv hO hOv hoff (rest := [(sQ, qBytes G k)]) fun y hy => by
    rw [List.mem_singleton] at hy; subst hy
    simp only [Apart, ql, pStart]; omega) ?_
  refine VP.seq ((pArith_vp hlens (by simp) xl (by simp) ql qlo (rest := pRest HO.md G k) fun y hy => by
    simp only [pRest, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact ⟨by simp, by simp only [Apart, pl]; omega, by simp only [Apart, pl]; omega⟩
    · exact ⟨by simp, by simp only [Apart, ql]; omega, by simp only [Apart, ql]; omega⟩).mono
      (fun _ _ h => h) fun _ _ h => h.1) ?_
  have xlt : Spec.Dsa.decodeBE (xBytes HO G k off) < 2 ^ (8 * G.pLen) := by
    have := VG.Proof.Dsa.decodeBE_lt (xBytes HO G k off)
    rwa [xl, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  have plt := pVal_lt (q := Spec.Dsa.decodeBE (qBytes G k)) (show 1 ≤ 8 * G.pLen by omega) xlt
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
      (VG.Proof.Dsa.bitLength_iff_bounds (by omega)).mpr ⟨by omega, plt⟩
    unfold pAttCfg
    rw [hpv]
    simp only [hcnd, ↓reduceIte]
    generalize hcc : pOut c G (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k))
      (pRest HO.md G k) = c0
    have cl0 : c0.cl = (sE, Spec.Rsa.i2osp ((pv - 1) / Spec.Dsa.decodeBE (qBytes G k)) (eBytes G.pLen G.qLen)) ::
        (sPBE, Spec.Rsa.i2osp pv G.pLen) :: pRest HO.md G k := by rw [← hcc, ← hpv]
    have eLS : c0.LS = c.LS := by rw [← hcc]
    have eV : c0.V = c.V := by rw [← hcc]
    have small : ∀ y ∈ c0.cl, y.1 + y.2.length ≤ kB G.pLen := fun y hy => by
      rw [cl0] at hy
      simp only [pRest, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · simp only [VG.Proof.Rsa.i2osp_length]; omega
      · simp only [VG.Proof.Rsa.i2osp_length]; omega
      · simp only [pl]; omega
      · simp only [ql]; omega
    have pin : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c0.cl := by rw [cl0]; simp
    have := test_vp (X := X) (c := c0) (cb := Spec.Rsa.i2osp pv G.pLen) (src := sPBE) (cl' := c0.cl)
      (name := g.pName) okp hc0 hu (by rw [eLS]; exact hU) (by rw [eV]; exact hUv) hwl hsize hL pin
      (by rw [VG.Proof.Rsa.i2osp_length]; omega) (by rw [VG.Proof.Rsa.i2osp_length, hLb]; omega)
      (by rw [VG.Proof.Rsa.i2osp_length]; omega) (by rw [VG.Proof.Rsa.i2osp_length]; omega)
      (by decide) (by rw [pb]; exact podd) (by rw [pb, hLb, pbl]) (by rw [eLS]; exact hU') (by rw [eLS]; exact hU88)
      fun y hy => ⟨List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hy, by
        have := small y hy; simp only [Apart, decide_eq_true_eq]; omega⟩),
        fun r _ => .inl (by have := small y hy; omega)⟩
    rw [VG.Proof.Rsa.i2osp_length] at this
    refine VP.seq (this.mono (fun σ s h => h.1.1) fun _ _ h => h) ?_
    rw [tRes, pb]
    exact pDecide_vp _

end

theorem shl5 (x : Nat) : BitVec.ofNat 64 x <<< 5 = BitVec.ofNat 64 (32 * x) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

section
variable {G : GP} {X : State → Prop}

/-- `r := r + i`, for a register both runs know. -/
theorem addi_vp {P : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → St G (c σ) X σ s) {r : Reg}
    (h6 : r ≠ .s6) {v i : Nat} (hi : i < 2048)
    (cert : ∃ hc, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s6, r]) (.block [.addi r r i]) hc).isSome = true) :
    VP (fun σ s => P σ s ∧ s.gpr r = BitVec.ofNat 64 v) (.block [.addi r r i])
      (fun σ s => St G (c σ) X σ s ∧ s.gpr r = BitVec.ofNat 64 (v + i)) := by
  refine VP.pub (SS.pub (c := c) fun σ s h => (hF σ s h.1).1) [r] cert
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
    fun σ s ⟨h, e⟩ => ?_
  have h' := hF σ s h
  refine wp_addi hi fun t u => WP.block_nil ⟨⟨h'.1.of_upd u h6, h'.2⟩, ?_⟩
  rw [u.gpr, e, BitVec.ofNat_add]

/-- The block of the next counter, with the hashes' count `C` and the width `L`. -/
abbrev advOps (C L : Nat) : List Instr :=
  [ld .t3 fCounter, .addi .t3 .t3 1, st .t3 fCounter, ld .t4 fOffset, .addi .t4 .t4 C, st .t4 fOffset,
    .li .t2 L, .shift .sll .d .t2 .t2 5, .sub .t2 .t3 .t2]

/-- The next counter: `fCounter` + 1, `fOffset` + `C`, and `t2 = 0` when the
counter reaches `32 pLen` (`4 L`). -/
theorem pAdvance_vp {d : Cfg} {j off C : Nat} (hC : C < 2048) (hCt : fCounter ∈ d.LS)
    (hCv : d.V fCounter = BitVec.ofNat 64 j) (hOf : fOffset ∈ d.LS) (hOv : d.V fOffset = BitVec.ofNat 64 off)
    (hj : j + 1 < 2 ^ 32) :
    VP (St G d X) (.block (advOps C G.pLen))
      (fun σ s => St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset (BitVec.ofNat 64 (off + C))) X σ s ∧
        isa.eval (.zero .t2) s = some (decide (j + 1 = 32 * G.pLen))) := by
  show VP _ (.block ([ld .t3 fCounter] ++ ([.addi .t3 .t3 (1 : Nat)] ++ ([st .t3 fCounter] ++ ([ld .t4 fOffset] ++
    ([.addi .t4 .t4 C] ++ ([st .t4 fOffset] ++ [.li .t2 G.pLen, .shift .sll .d .t2 .t2 5, .sub .t2 .t3 .t2]))))))) _
  -- The counter.
  refine VP.block_append (G := fun σ s => St G d X σ s ∧ s.gpr .t3 = BitVec.ofNat 64 j)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV hCt).trans hCv) fun σ s t ⟨_, x⟩ h' u => ⟨⟨h', x⟩, u.gpr⟩) ?_
  refine VP.block_append (G := fun σ s => St G d X σ s ∧ s.gpr .t3 = BitVec.ofNat 64 (j + 1))
    (addi_vp (c := fun _ => d) (fun σ s h => h) (by decide) (by decide)
      ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .t3]) (.block [.addi .t3 .t3 (1 : Nat)]),
        by kernel_rfl⟩) ?_
  have d1O : fOffset ∈ (d.setV fCounter (BitVec.ofNat 64 (j + 1))).LS := List.mem_cons_of_mem _ hOf
  refine VP.block_append (G := fun σ s => St G (d.setV fCounter (BitVec.ofNat 64 (j + 1))) X σ s ∧
      s.gpr .t3 = BitVec.ofNat 64 (j + 1))
    (st_vp (c := fun _ => d) (fun σ s h => h.1.1) (varOk_of (by decide))
      fun σ s t ⟨⟨_, x⟩, r3⟩ h' K => ⟨⟨r3 ▸ h', x⟩, by rw [K.gpr (by decide), r3]⟩) ?_
  -- The offset.
  refine VP.block_append (G := fun σ s => (St G (d.setV fCounter (BitVec.ofNat 64 (j + 1))) X σ s ∧
      s.gpr .t3 = BitVec.ofNat 64 (j + 1)) ∧ s.gpr .t4 = BitVec.ofNat 64 off)
    (ld_vp (c := fun _ => d.setV fCounter (BitVec.ofNat 64 (j + 1))) (fun σ s h => h.1.1) (by decide) (by decide)
      (by decide) (fun σ s h => (h.1.1.gi.slotV d1O).trans (by
        show upd d.V fCounter (BitVec.ofNat 64 (j + 1)) fOffset = _; rw [upd_ne _ _ (by decide)]; exact hOv))
      fun σ s t ⟨⟨_, x⟩, r3⟩ h' u => ⟨⟨⟨h', x⟩, by rw [u.other _ (by decide), r3]⟩, u.gpr⟩) ?_
  refine VP.block_append (G := fun σ s => (St G (d.setV fCounter (BitVec.ofNat 64 (j + 1))) X σ s ∧
      s.gpr .t3 = BitVec.ofNat 64 (j + 1)) ∧ s.gpr .t4 = BitVec.ofNat 64 (off + C))
    (VP.pub (SS.pub (c := fun _ => d.setV fCounter (BitVec.ofNat 64 (j + 1))) fun σ s h => h.1.1.1) [.t4]
      ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .t4]) (.block [.addi .t4 .t4 C]), by kernel_rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
      fun σ s ⟨⟨⟨h, x⟩, r3⟩, r4⟩ =>
        wp_addi hC fun t u => WP.block_nil
          ⟨⟨⟨h.of_upd u (by decide), x⟩, by rw [u.other _ (by decide), r3]⟩, by
            rw [u.gpr, r4, BitVec.ofNat_add]⟩) ?_
  refine VP.block_append (G := fun σ s => St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
      (BitVec.ofNat 64 (off + C))) X σ s ∧ s.gpr .t3 = BitVec.ofNat 64 (j + 1))
    (st_vp (c := fun _ => d.setV fCounter (BitVec.ofNat 64 (j + 1))) (fun σ s h => h.1.1.1)
      (varOk_of (by decide))
      fun σ s t ⟨⟨⟨_, x⟩, r3⟩, r4⟩ h' K => ⟨⟨r4 ▸ h', x⟩, by rw [K.gpr (by decide), r3]⟩) ?_
  -- The end of the counters.
  refine VP.pub (SS.pub (c := fun _ => (d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
      (BitVec.ofNat 64 (off + C))) fun σ s h => h.1.1) [.t3] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64
      (Taint.ofRegs [.s6, .t3]) (.block [.li .t2 G.pLen, .shift .sll .d .t2 .t2 5, .sub .t2 .t3 .t2]), by kernel_rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
    fun σ s ⟨⟨h, x⟩, r3⟩ => ?_
  have l := h.lens
  have hL : G.pLen < 2048 := by rcases l with e | e | e <;> omega
  refine wp_li hL fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => wp_sub fun t u => WP.block_nil ⟨⟨?_, x⟩, ?_⟩
  · exact ((h.of_upd u₁ (by decide)).of_upd u₂ (by decide)).of_upd u (by decide)
  rw [eval_zero, u.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r3, u₂.gpr, u₁.gpr, shl5, sub_beq_zero,
    ofNat_beq (by omega) (by omega)]

/-- The code after a candidate. -/
abbrev pTail (C : Nat) (L : Nat) : Prog isa :=
  .seq (.block (cmpF fP 4)) (.seq (.ite (.zero .t2) (.seq (.block (advOps C L))
    (.ite (.zero .t2) (.block (stImm fP 2)) (.block []))) (.block [])) (.block (cmpF fP 4)))

/-- After a candidate that is not p: the next counter, or `fP` := 2 after the last. -/
theorem pCont_vp {d : Cfg} {j off C : Nat} (hC : C < 2048) (hP : fP ∈ d.LS)
    (hPv : d.V fP = BitVec.ofNat 64 4) (hCt : fCounter ∈ d.LS) (hCv : d.V fCounter = BitVec.ofNat 64 j)
    (hOf : fOffset ∈ d.LS) (hOv : d.V fOffset = BitVec.ofNat 64 off) (hj : j + 1 < 2 ^ 32) :
    VP (St G d X) (pTail C G.pLen)
      (fun σ s => if j + 1 = 32 * G.pLen then
          St G (((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset (BitVec.ofNat 64 (off + C))).setV fP
            (BitVec.ofNat 64 2)) X σ s ∧ isa.eval (.zero .t2) s = some false
        else St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset (BitVec.ofNat 64 (off + C))) X σ s ∧
          isa.eval (.zero .t2) s = some true) := by
  refine VP.seq (G := fun σ s => St G d X σ s ∧ isa.eval (.zero .t2) s = some true)
    (cmpF_vp (c := fun _ => d) (x := BitVec.ofNat 64 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV hP).trans hPv) fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
  by_cases e : j + 1 = 32 * G.pLen
  · refine VP.mono (G := fun σ s => St G (((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
        (BitVec.ofNat 64 (off + C))).setV fP (BitVec.ofNat 64 2)) X σ s ∧ isa.eval (.zero .t2) s = some false) ?_
      (fun _ _ h => h) fun σ s h => by rw [ite_eq_left_of_eq_true _ _ (eq_true e)]; exact h
    refine VP.seq (G := St G (((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
        (BitVec.ofNat 64 (off + C))).setV fP (BitVec.ofNat 64 2)) X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
        rw [h₁.2, h₂.2]) (VP.seq ((pAdvance_vp hC hCt hCv hOf hOv hj).mono (fun σ s h => h.1.1) fun _ _ h => h)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (stImm_vp (c := fun _ => (d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
              (BitVec.ofNat 64 (off + C))) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
              fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
            (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp [e] at z)))
        (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp at z)) ?_
    exact cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp))
      fun σ s t ⟨_, x⟩ h' _ e' => ⟨⟨h', x⟩, by rw [e']; rfl⟩
  · refine VP.mono (G := fun σ s => St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
        (BitVec.ofNat 64 (off + C))) X σ s ∧ isa.eval (.zero .t2) s = some true) ?_
      (fun _ _ h => h) fun σ s h => by rw [ite_eq_right_of_eq_false _ _ (eq_false e)]; exact h
    refine VP.seq (G := St G ((d.setV fCounter (BitVec.ofNat 64 (j + 1))).setV fOffset
        (BitVec.ofNat 64 (off + C))) X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
        rw [h₁.2, h₂.2]) (VP.seq ((pAdvance_vp hC hCt hCv hOf hOv hj).mono (fun σ s h => h.1.1) fun _ _ h => h)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp [e] at z)
            (VP.block_nil fun σ s h => h.1.1)))
        (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp at z)) ?_
    exact cmpF_vp (x := BitVec.ofNat 64 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV (by simp [hP])).trans (by
        show upd (upd d.V fCounter (BitVec.ofNat 64 (j + 1))) fOffset (BitVec.ofNat 64 (off + C)) fP = _
        rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact hPv))
      fun σ s t ⟨_, x⟩ h' _ e' => ⟨⟨h', x⟩, by rw [e']; rfl⟩

/-- After a candidate that ends the search (`fP` := 0 or 1). -/
theorem pExit_vp {d : Cfg} {v C : Nat} (hP : fP ∈ d.LS) (hPv : d.V fP = BitVec.ofNat 64 v) (hv : v < 4) :
    VP (St G d X) (pTail C G.pLen) (fun σ s => St G d X σ s ∧ isa.eval (.zero .t2) s = some false) := by
  have ne : (BitVec.ofNat 64 v == BitVec.ofNat 64 4) = false := by
    rw [ofNat_beq (by omega) (by decide)]; simp; omega
  refine VP.seq (G := fun σ s => St G d X σ s ∧ isa.eval (.zero .t2) s = some false)
    (cmpF_vp (c := fun _ => d) (x := BitVec.ofNat 64 v) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV hP).trans hPv) fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e, ne]⟩) ?_
  refine VP.seq (G := St G d X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
    (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp at z) (VP.block_nil fun σ s h => h.1.1)) ?_
  exact cmpF_vp (c := fun _ => d) (x := BitVec.ofNat 64 v) (fun σ s h => h.1) (by decide) (by decide) (by decide)
    (fun σ s h => (h.1.gi.slotV hP).trans hPv) fun σ s t h h' _ e => ⟨⟨h', h.2⟩, by rw [e, ne]⟩

end

section
variable {Gh : Hash}

/-- Counter `j`'s candidate. -/
abbrev pCand (HO : HashOk Gh) (G : GP) (k j : Nat) : Nat :=
  pVal (Spec.Dsa.decodeBE (xBytes HO G k (1 + j * (cnt G + 1)))) (Spec.Dsa.decodeBE (qBytes G k))

/-- Whether counter `j`'s candidate is too short to test. -/
abbrev pShort (HO : HashOk Gh) (G : GP) (k j : Nat) : Prop := pCand HO G k j < 2 ^ (8 * G.pLen - 1)

/-- The tape's octets read before counter `j`. -/
def pU (HO : HashOk Gh) (G : GP) (k u0 : Nat) : Nat → Nat
  | 0 => u0
  | j + 1 => if pShort HO G k j then pU HO G k u0 j else
      match Spec.Dsa.probablePrime (pCand HO G k j) (G.randB.drop (pU HO G k u0 j)) with
      | some (_, r) => G.randLen - r.length
      | none => pU HO G k u0 j

/-- The search's iterations from counter `j`, with `m` counters after it. -/
def pCount (HO : HashOk Gh) (G : GP) (k u0 : Nat) : Nat → Nat → Nat
  | 0, j => j + 1
  | m + 1, j => if pShort HO G k j then pCount HO G k u0 m (j + 1) else
      match Spec.Dsa.probablePrime (pCand HO G k j) (G.randB.drop (pU HO G k u0 j)) with
      | some (false, _) => pCount HO G k u0 m (j + 1)
      | _ => j + 1

theorem pCount_gt (HO : HashOk Gh) (G : GP) (k u0 : Nat) : ∀ m j, j < pCount HO G k u0 m j
  | 0, j => by simp [pCount]
  | m + 1, j => by
    have := pCount_gt HO G k u0 m (j + 1)
    simp only [pCount]; split
    · omega
    · split <;> omega

/-- The search's header words at counter `j`, with `u` octets read. -/
abbrev pBase (c : Cfg) (HO : HashOk Gh) (G : GP) (k : Nat) : Cfg :=
  { c with
    cl := [(sMsg + G.qLen, padTail HO.md G.qLen), (pStart G 0, []), (sQ, qBytes G k)]
    live := []
    kls := [] }

abbrev pCfgJ (c : Cfg) (HO : HashOk Gh) (G : GP) (k j u : Nat) : Cfg :=
  ((((pBase c HO G k).setV fUsed (BitVec.ofNat 64 u)).setV fCounter (BitVec.ofNat 64 j)).setV fOffset
    (BitVec.ofNat 64 (1 + j * (cnt G + 1)))).setV fP (BitVec.ofNat 64 4)

/-- The spec's search from counter `j`. -/
abbrev pSpec (HO : HashOk Gh) (G : GP) (k u0 j : Nat) : Option (Option Nat × Spec.RsaKeyGen.Rand) :=
  VG.Proof.Dsa.Generation.primeSearch (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) j
    (G.randB.drop (pU HO G k u0 j))

/-- The arrays of p. -/
abbrev pAp (p q : Nat) : Nat → Nat := KU (KU (KU (KU (fun _ => 0) aOne 1) aPm1 (p - 1)) aE ((p - 1) / q)) aP p

/-- The stage after the search. -/
abbrev pFound (c : Cfg) (HO : HashOk Gh) (G : GP) (k p : Nat) : Cfg :=
  { c with
    cl := (sE, Spec.Rsa.i2osp ((p - 1) / Spec.Dsa.decodeBE (qBytes G k)) (eBytes G.pLen G.qLen)) ::
      (sPBE, Spec.Rsa.i2osp p G.pLen) :: pRest HO.md G k
    A := pAp p (Spec.Dsa.decodeBE (qBytes G k))
    live := [aE, aP, aPm1, aOne, aZero]
    kls := [] }

abbrev pNone (c : Cfg) (HO : HashOk Gh) (G : GP) : Cfg :=
  { c with
    cl := [(sMsg + G.qLen, padTail HO.md G.qLen)]
    live := []
    kls := [] }

/-- The stage after the search for p, from the spec's result. -/
def pFin (c : Cfg) (HO : HashOk Gh) (G : GP) (k : Nat) : Option (Option Nat × Spec.RsaKeyGen.Rand) → Cfg
  | some (some p, rest) =>
    ((pFound c HO G k p).setV fUsed (BitVec.ofNat 64 (G.randLen - rest.length))).setV fP (BitVec.ofNat 64 1)
  | some (none, r) => ((pNone c HO G).setV fUsed (BitVec.ofNat 64 (G.randLen - r.length))).setV fP (BitVec.ofNat 64 2)
  | none => (pNone c HO G).setV fP (BitVec.ofNat 64 0)

/-- The search with `r` iterations left of `N`. -/
abbrev pInv (c : Cfg) (HO : HashOk Gh) (G : GP) (k u0 N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  (r ≤ N ∧ N - r < 32 * G.pLen ∧ pCount HO G k u0 (32 * G.pLen - 1 - (N - r)) (N - r) = N ∧
    pSpec HO G k u0 (N - r) = pSpec HO G k u0 0 ∧ pU HO G k u0 (N - r) ≤ G.randLen) ∧
    St G (pCfgJ c HO G k (N - r) (pU HO G k u0 (N - r))) X σ s

/-- The words the search keeps apart from `c`'s. -/
abbrev PNot (c : Cfg) : Prop :=
  fUsed ∉ c.LS ∧ fCounter ∉ c.LS ∧ fOffset ∉ c.LS ∧ fP ∉ c.LS ∧ fRes ∉ c.LS ∧ fUsedOut ∉ c.LS ∧
    ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut

theorem PNot.ne {c : Cfg} (h : PNot c) {o : Nat} (ho : o ∈ c.LS) :
    o ≠ fUsed ∧ o ≠ fCounter ∧ o ≠ fOffset ∧ o ≠ fP ∧ o ≠ fRes :=
  ⟨fun e => h.1 (e ▸ ho), fun e => h.2.1 (e ▸ ho), fun e => h.2.2.1 (e ▸ ho), fun e => h.2.2.2.1 (e ▸ ho),
    fun e => h.2.2.2.2.1 (e ▸ ho)⟩

/-- A stage's words agree with the search's at counter `j`. -/
theorem pCfgJ_V {c : Cfg} (hn : PNot c) {HO : HashOk Gh} {G : GP} {k j u : Nat} {LS : List Nat}
    {V : Nat → BitVec 64} (hLS : ∀ o ∈ c.LS, o ∈ LS) (h1 : fP ∈ LS) (h2 : fOffset ∈ LS) (h3 : fCounter ∈ LS)
    (h4 : fUsed ∈ LS) (vP : V fP = BitVec.ofNat 64 4) (vO : V fOffset = BitVec.ofNat 64 (1 + j * (cnt G + 1)))
    (vC : V fCounter = BitVec.ofNat 64 j) (vU : V fUsed = BitVec.ofNat 64 u) (vc : ∀ o ∈ c.LS, V o = c.V o) :
    ∀ o ∈ (pCfgJ c HO G k j u).LS, o ∈ LS ∧ V o = (pCfgJ c HO G k j u).V o := by
  intro o ho
  change o ∈ fP :: fOffset :: fCounter :: fUsed :: c.LS at ho
  simp only [List.mem_cons] at ho
  rcases ho with rfl | rfl | rfl | rfl | ho
  · exact ⟨h1, by rw [vP]; simp [upd]⟩
  · exact ⟨h2, by rw [vO]; simp [upd, fOffset, fP]⟩
  · exact ⟨h3, by rw [vC]; simp [upd, fCounter, fOffset, fP]⟩
  · exact ⟨h4, by rw [vU]; simp [upd, fUsed, fCounter, fOffset, fP]⟩
  · obtain ⟨n1, n2, n3, n4, -⟩ := hn.ne ho
    exact ⟨hLS o ho, by rw [vc o ho]; simp [upd, n1, n2, n3, n4]⟩

end

/-- X's hashes are at most 12. -/
theorem cnt_le (G : GP) (h : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) : cnt G + 1 ≤ 12 := by
  rcases h with e | e | e <;> simp only [cnt, GP.qLen, e] <;> decide

section
variable {G : GP} {X : State → Prop} {Gh : Hash}

/-- The loop's postcondition after an iteration with `r` left. -/
abbrev pPost (c : Cfg) (HO : HashOk Gh) (G : GP) (k u0 N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  isa.eval (.zero .t2) s = some (decide (0 < r)) ∧ (r = 0 → St G (pFin c HO G k (pSpec HO G k u0 0)) X σ s) ∧
    (0 < r → pInv c HO G k u0 N X r σ s)

/-- The search's claims, from a stage that has them. -/
theorem SS.pBase {STK : Nat} {σ s : State} {d : Cfg} (h : SS G STK σ d s) {HO : HashOk Gh} {k : Nat}
    (dpad : (sMsg + G.qLen, padTail HO.md G.qLen) ∈ d.cl) (dq : (sQ, qBytes G k) ∈ d.cl) :
    SS G STK σ { d with cl := [(sMsg + G.qLen, padTail HO.md G.qLen), (pStart G 0, []), (sQ, qBytes G k)] } s :=
  h.reclaim fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨h.sb _ dpad, h.clOk _ dpad⟩
    · have qB := q_bounds G h.gi
      have hp3 : G.pLen ≤ 384 := by rcases h.lens with e | e | e <;> omega
      have nX : sX = 576 := rfl
      have nE : hEnd = 280 := rfl
      exact ⟨by simp [Spec.Rsa.bytesAt], by simp only [ClOk, pStart, List.length_nil]; omega⟩
    · exact ⟨h.sb _ dq, h.clOk _ dq⟩

/-- After a candidate that is not p, the next counter (`u'` witnesses read). -/
theorem pGo_vp {c : Cfg} (hn : PNot c) {HO : HashOk Gh} {k u0 N r j u' : Nat} {d : Cfg}
    (hjj : N - (r + 1) = j) (hr : r + 1 ≤ N) (hj : j < 32 * G.pLen) (hl : G.pLen ≤ 384)
    (hcnt : cnt G + 1 < 2048) (hwl : G.randB.length = G.randLen)
    (hc : pCount HO G k u0 (32 * G.pLen - 1 - j) j = N) (hR : pSpec HO G k u0 j = pSpec HO G k u0 0)
    (hstep : ∀ m, pCount HO G k u0 (m + 1) j = pCount HO G k u0 m (j + 1))
    (hpu : pU HO G k u0 (j + 1) = u')
    (hspec : pSpec HO G k u0 j = VG.Proof.Dsa.Generation.primeSearch (8 * G.pLen) (8 * G.qLen)
      (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) (j + 1) (G.randB.drop u'))
    (hu' : u' ≤ G.randLen)
    (dP : fP ∈ d.LS) (dPv : d.V fP = BitVec.ofNat 64 4) (dC : fCounter ∈ d.LS) (dCv : d.V fCounter = BitVec.ofNat 64 j)
    (dO : fOffset ∈ d.LS) (dOv : d.V fOffset = BitVec.ofNat 64 (1 + j * (cnt G + 1)))
    (dU : fUsed ∈ d.LS) (dUv : d.V fUsed = BitVec.ofNat 64 u')
    (dLS : ∀ o ∈ c.LS, o ∈ d.LS ∧ d.V o = c.V o)
    (dpad : (sMsg + G.qLen, padTail HO.md G.qLen) ∈ d.cl) (dq : (sQ, qBytes G k) ∈ d.cl) :
    VP (St G d X) (pTail (cnt G + 1) G.pLen) (pPost c HO G k u0 N X r) := by
  refine (pCont_vp (X := X) hcnt dP dPv dC dCv dO dOv (by omega)).mono (fun _ _ h => h) fun σ s h => ?_
  split at h
  · -- The last counter: `fP` := 2.
    rename_i e
    have hN : N = j + 1 := by
      rw [show 32 * G.pLen - 1 - j = 0 by omega] at hc; simp only [pCount] at hc; omega
    have r0 : r = 0 := by omega
    subst r0
    refine ⟨by rw [h.2]; rfl, fun _ => ⟨?_, h.1.2⟩, fun h0 => absurd h0 (by decide)⟩
    have hd : pSpec HO G k u0 0 = some (none, G.randB.drop u') := by
      rw [← hR, hspec, VG.Proof.Dsa.Generation.primeSearch_done _ _ (by omega)]
    rw [hd]; simp only [pFin]
    have lu : G.randLen - (G.randB.drop u').length = u' := by rw [List.length_drop, hwl]; omega
    refine h.1.1.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp))
      (fun _ h' => absurd h' (by simp))
    · change o ∈ fP :: fUsed :: c.LS at ho
      simp only [List.mem_cons] at ho
      rcases ho with rfl | rfl | ho
      · exact ⟨by simp, by simp [upd]⟩
      · refine ⟨by simp [dU], ?_⟩
        dsimp only [Cfg.setV]
        rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide),
          upd_self, dUv, lu]
      · obtain ⟨n1, n2, n3, n4, -⟩ := hn.ne ho
        refine ⟨by simp [(dLS o ho).1], ?_⟩
        dsimp only [Cfg.setV]
        rw [upd_ne _ _ n4, upd_ne _ _ n3, upd_ne _ _ n2, upd_ne _ _ n4, upd_ne _ _ n1, (dLS o ho).2]
    · change y ∈ [(sMsg + G.qLen, padTail HO.md G.qLen)] at hy
      rw [List.mem_singleton] at hy; subst hy; exact dpad
  · -- The next counter.
    rename_i e
    obtain ⟨m, hm⟩ : ∃ m, 32 * G.pLen - 1 - j = m + 1 := ⟨32 * G.pLen - 1 - j - 1, by omega⟩
    rw [hm, hstep] at hc
    have hgt := pCount_gt HO G k u0 m (j + 1)
    have rpos : 0 < r := by omega
    have hNr : N - r = j + 1 := by omega
    refine ⟨by rw [h.2]; simp [rpos], fun h0 => absurd h0 (by omega), fun _ => ?_⟩
    show (_ ∧ _) ∧ _
    rw [hNr, hpu]
    refine ⟨⟨by omega, by omega, by rw [show 32 * G.pLen - 1 - (j + 1) = m by omega]; exact hc,
      by rw [← hR, hspec]; simp only [pSpec, hpu], hu'⟩, ?_, h.1.2⟩
    have r1 := h.1.1.pBase (HO := HO) (k := k) (by exact dpad) (by exact dq)
    have eo : 1 + j * (cnt G + 1) + (cnt G + 1) = 1 + (j + 1) * (cnt G + 1) := by rw [Nat.succ_mul]; omega
    refine r1.mono (pCfgJ_V hn (fun o ho => ?_) (by simp [dP]) (by simp) (by simp [dC]) (by simp [dU]) ?_ ?_ ?_ ?_ ?_)
      (fun y hy => hy) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    · simp [(dLS o ho).1]
    · dsimp only [Cfg.setV]
      rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), dPv]
    · dsimp only [Cfg.setV]
      rw [upd_self, eo]
    · dsimp only [Cfg.setV]
      rw [upd_ne _ _ (by decide), upd_self]
    · dsimp only [Cfg.setV]
      rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), dUv]
    · intro o ho
      obtain ⟨n1, n2, n3, n4, -⟩ := hn.ne ho
      dsimp only [Cfg.setV]
      rw [upd_ne _ _ n3, upd_ne _ _ n2, (dLS o ho).2]

/-- After a candidate that ends the search. -/
theorem pStop_vp {c : Cfg} {HO : HashOk Gh} {k u0 N r j v C : Nat} {d : Cfg} (hjj : N - (r + 1) = j)
    (hr : r + 1 ≤ N) (hN : N = j + 1) (dP : fP ∈ d.LS) (dPv : d.V fP = BitVec.ofNat 64 v) (hv : v < 4)
    (fin : ∀ σ s, SS G STK0 σ d s → SS G STK0 σ (pFin c HO G k (pSpec HO G k u0 0)) s) :
    VP (St G d X) (pTail C G.pLen) (pPost c HO G k u0 N X r) := by
  have r0 : r = 0 := by omega
  subst r0
  exact (pExit_vp dP dPv hv).mono (fun _ _ h => h) fun σ s ⟨⟨h, x⟩, e⟩ =>
    ⟨by rw [e]; rfl, fun _ => ⟨fin σ s h, x⟩, fun h0 => absurd h0 (by decide)⟩

/-- What the search for p needs of its test, beyond `PrimeOk`. -/
structure PLay (G : GP) (Lp : Impl.Dsa.ProbablePrime.Layout) : Prop where
  bits : Lp.bits = 8 * G.pLen
  cand : Lp.candidate = 0
  size : Lp.size ≤ 256 * G.pLen
  scratch : ∀ r ∈ Lp.scratch, r.1 + r.2 ≤ 256 * G.pLen

theorem pBody_vp {g : Geo} (HO : HashOk g.G) {Lp : Impl.Dsa.ProbablePrime.Layout} (okp : PrimeOk Lp g.pCode)
    (lay : PLay G Lp)
    (hlens : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384)
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.randB.length = G.randLen)
    {c : Cfg} (hn : PNot c) {k u0 N : Nat} (hk : k + G.qLen ≤ G.randLen) (hS : fSeed ∈ c.LS)
    (hSv : c.V fSeed = G.rand + BitVec.ofNat 64 k)
    (hcand : ∀ j, Spec.Dsa.pCandidate (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k)
      (1 + j * ((8 * G.pLen - 1) / (8 * G.qLen) + 1)) = pCand HO G k j) (r : Nat) :
    VP (pInv c HO G k u0 N X (r + 1)) (Impl.Rsa.RISCV64.Keys.seqs [g.pAttempt, .block (cmpF fP 4),
        .ite (.zero .t2) (.seq (.block g.pAdvance) (.ite (.zero .t2) (.block (stImm fP 2)) (.block [])))
          (.block []),
        .block (cmpF fP 4)])
      (pPost c HO G k u0 N X r) := by
  refine VP.intro fun ⟨hr, hj, hc, hR, hu⟩ => ?_
  generalize hjj : N - (r + 1) = j at hj hc hR hu
  have hl : G.pLen ≤ 384 := by omega
  have hcnt : cnt G + 1 ≤ 12 := cnt_le G hlens
  have hcount : g.count = cnt G := by simp only [Geo.count, hp, hq, cnt]
  have ecode : Impl.Rsa.RISCV64.Keys.seqs [g.pAttempt, .block (cmpF fP 4),
      .ite (.zero .t2) (.seq (.block g.pAdvance) (.ite (.zero .t2) (.block (stImm fP 2)) (.block [])))
        (.block []),
      .block (cmpF fP 4)] = .seq g.pAttempt (pTail (cnt G + 1) G.pLen) := by
    simp only [Geo.pAdvance, hcount, hp]; rfl
  rw [ecode]
  have hoffb : 1 + j * (cnt G + 1) + (cnt G + 1) < 2 ^ 32 := by
    have := Nat.mul_le_mul (Nat.le_of_lt hj) hcnt; omega
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hn
  -- The spec's step.
  have hstepS := VG.Proof.Dsa.Generation.primeSearch_step (l := 8 * G.pLen) (n := 8 * G.qLen)
    (q := Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) (G.randB.drop (pU HO G k u0 j)) (by omega : j < 4 * (8 * G.pLen))
  dsimp only at hstepS
  rw [hcand j] at hstepS
  change pSpec HO G k u0 j = _ at hstepS
  -- The candidate.
  refine VP.seq ((pAttempt_vp (X := X) (c := pCfgJ c HO G k j (pU HO G k u0 j)) (off := 1 + j * (cnt G + 1))
    HO okp lay.bits lay.cand lay.size lay.scratch hp hq hk4 hwl hH hk hu
    (by simp [hS]) (by simp [upd, ⟨n1, n2, n3, n4, n5, n6, n7⟩ |> fun hn : PNot c => hn.ne hS]; exact hSv)
    (by simp) (by simp [upd, fOffset, fP]) hoffb (by simp) (by simp [upd, fUsed, fCounter, fOffset, fP])
    (by
      intro o ho
      change o ∈ fP :: fOffset :: fCounter :: fUsed :: c.LS at ho
      simp only [List.mem_cons] at ho
      rcases ho with rfl | rfl | rfl | rfl | ho
      · decide
      · decide
      · decide
      · decide
      · exact n7 o ho)
    (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, by decide, by decide, n6⟩)).mono
    (fun _ _ h => h) fun _ _ h => h) ?_
  have hn : PNot c := ⟨n1, n2, n3, n4, n5, n6, n7⟩
  have hN1 : ∀ (hlast : ∀ m, pCount HO G k u0 (m + 1) j = j + 1), N = j + 1 := fun hlast => by
    rw [← hc]
    rcases Nat.eq_zero_or_pos (32 * G.pLen - 1 - j) with h0 | h0
    · rw [h0]; rfl
    · obtain ⟨m, hm⟩ : ∃ m, 32 * G.pLen - 1 - j = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h0).symm⟩
      rw [hm, hlast]
  have padIn : ∀ x y : Nat × List Byte, (sMsg + G.qLen, padTail HO.md G.qLen) ∈ x :: y :: pRest HO.md G k := by
    simp [pRest]
  have qIn : ∀ x y : Nat × List Byte, (sQ, qBytes G k) ∈ x :: y :: pRest HO.md G k := by simp [pRest]
  by_cases hs : pShort HO G k j
  · -- Too short: the next counter.
    rw [pAttCfg, ite_eq_left_of_eq_true _ _ (eq_true hs)]
    refine pGo_vp hn hjj (by omega) hj hl (by omega) hwl hc hR
      (fun m => by simp only [pCount]; exact ite_eq_left_of_eq_true _ _ (eq_true hs))
      (by simp only [pU]; exact ite_eq_left_of_eq_true _ _ (eq_true hs))
      (by rw [hstepS]; exact ite_eq_left_of_eq_true _ _ (eq_true hs)) hu
      (by simp) (by simp [upd]) (by simp) (by simp [upd, fCounter, fOffset, fP]) (by simp)
      (by simp [upd, fOffset, fP]) (by simp) (by simp [upd, fUsed, fCounter, fOffset, fP])
      (fun o ho => ⟨by simp [ho], by obtain ⟨m1, m2, m3, m4, -⟩ := hn.ne ho; simp [upd, m1, m2, m3, m4]⟩)
      (padIn _ _) (qIn _ _)
  rw [pAttCfg, ite_eq_right_of_eq_false _ _ (eq_false hs)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at hstepS
  rcases hpp : Spec.Dsa.probablePrime (pCand HO G k j) (G.randB.drop (pU HO G k u0 j)) with _ | ⟨b, rr⟩
  · -- The witnesses ran out: `fP` := 0.
    rw [hpp] at hstepS
    refine pStop_vp (v := 0) hjj (by omega) (hN1 fun m => by simp only [pCount, hs, hpp, ↓reduceIte])
      (by simp [pRes]) (by simp [pRes, upd]) (by decide) fun σ s h => ?_
    rw [← hR, hstepS]; simp only [pFin]
    refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    · change o ∈ fP :: c.LS at ho
      simp only [List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact ⟨by simp [pRes], by simp [pRes, upd]⟩
      · obtain ⟨m1, m2, m3, m4, m5⟩ := hn.ne ho
        exact ⟨by simp [pRes, testCfg, ho], by simp [pRes, testCfg, upd, m1, m2, m3, m4, m5]⟩
    · change y ∈ [(sMsg + G.qLen, padTail HO.md G.qLen)] at hy
      rw [List.mem_singleton] at hy; subst hy; exact padIn _ _
  rcases b
  · -- Not a prime: the next counter.
    rw [hpp] at hstepS
    simp only [Bool.false_eq_true, ↓reduceIte] at hstepS
    refine pGo_vp (u' := G.randLen - rr.length) hn hjj (by omega) hj hl (by omega) hwl hc hR
      (fun m => by simp only [pCount, hs, hpp, ↓reduceIte])
      (by simp only [pU, hs, hpp, ↓reduceIte])
      (by rw [hstepS, ← hwl, VG.Proof.Dsa.Generation.probablePrime_cursor hpp]) (by omega)
      (by simp [pRes, testCfg]) (by simp [pRes, testCfg, upd, fP, fRes, fUsed])
      (by simp [pRes, testCfg]) (by simp [pRes, testCfg, upd, fCounter, fOffset, fP, fRes, fUsed])
      (by simp [pRes, testCfg]) (by simp [pRes, testCfg, upd, fOffset, fP, fRes, fUsed])
      (by simp [pRes, testCfg]) (by simp [pRes, testCfg, upd])
      (fun o ho => ⟨by simp [pRes, testCfg, ho], by
        obtain ⟨m1, m2, m3, m4, m5⟩ := hn.ne ho; simp [pRes, testCfg, upd, m1, m2, m3, m4, m5]⟩)
      (by simp [pRes, testCfg, pRest]) (by simp [pRes, testCfg, pRest])
  · -- A probable prime: `fP` := 1.
    rw [hpp] at hstepS
    simp only [↓reduceIte] at hstepS
    refine pStop_vp (v := 1) hjj (by omega) (hN1 fun m => by simp only [pCount, hs, hpp, ↓reduceIte])
      (by simp [pRes]) (by simp [pRes, upd]) (by decide) fun σ s h => ?_
    rw [← hR, hstepS]; simp only [pFin]
    refine h.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => ⟨h', rfl⟩) (fun _ h' => absurd h' (by simp))
    change o ∈ fP :: fUsed :: c.LS at ho
    simp only [List.mem_cons] at ho
    rcases ho with rfl | rfl | ho
    · exact ⟨by simp [pRes], by simp [pRes, upd]⟩
    · exact ⟨by simp [pRes, testCfg], by simp [pRes, testCfg, upd, fUsed, fP]⟩
    · obtain ⟨m1, m2, m3, m4, m5⟩ := hn.ne ho
      exact ⟨by simp [pRes, testCfg, ho], by simp [pRes, testCfg, upd, m1, m2, m3, m4, m5]⟩

/-- The search for p from the seed at `k`, with `u0` witnesses read. -/
theorem pPart_vp {g : Geo} (HO : HashOk g.G) {Lp : Impl.Dsa.ProbablePrime.Layout} (okp : PrimeOk Lp g.pCode)
    (lay : PLay G Lp)
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.randB.length = G.randLen)
    {c : Cfg} (hn : PNot c) {k u0 : Nat} (hk : k + G.qLen ≤ G.randLen) (hS : fSeed ∈ c.LS)
    (hSv : c.V fSeed = G.rand + BitVec.ofNat 64 k) (hu0 : u0 ≤ G.randLen)
    (hcand : ∀ j, Spec.Dsa.pCandidate (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k)
      (1 + j * ((8 * G.pLen - 1) / (8 * G.qLen) + 1)) = pCand HO G k j)
    {d : Cfg} (dU : fUsed ∈ d.LS) (dUv : d.V fUsed = BitVec.ofNat 64 u0)
    (dLS : ∀ o ∈ c.LS, o ∈ d.LS ∧ d.V o = c.V o)
    (dpad : (sMsg + G.qLen, padTail HO.md G.qLen) ∈ d.cl) (dq : (sQ, qBytes G k) ∈ d.cl) :
    VP (St G d X) g.pPart (St G (pFin c HO G k (pSpec HO G k u0 0)) X) := by
  refine VP.byLens fun hlens => ?_
  unfold Geo.pPart
  simp only [Impl.Rsa.RISCV64.Keys.seqs]
  have hN := pCount_gt HO G k u0 (32 * G.pLen - 1) 0
  generalize hNN : pCount HO G k u0 (32 * G.pLen - 1) 0 = N at hN
  have hl : G.pLen ≤ 384 := by omega
  have hpL : 0 < G.pLen := by omega
  refine VP.seq ?_ ?_ (G := pInv c HO G k u0 N X N)
  · rw [List.append_assoc]
    refine VP.block_append (G := St G (d.setV fCounter (BitVec.ofNat 64 0)) X)
      (stImm_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (varOk_of (by decide))
        fun σ s t h h' _ => ⟨h', h.2⟩) ?_
    refine VP.block_append (G := St G ((d.setV fCounter (BitVec.ofNat 64 0)).setV fOffset (BitVec.ofNat 64 1)) X)
      (stImm_vp (c := fun _ => d.setV fCounter (BitVec.ofNat 64 0)) (fun σ s h => h.1) (by decide)
        (varOk_of (by decide)) fun σ s t h h' _ => ⟨h', h.2⟩) ?_
    refine stImm_vp (c := fun _ => (d.setV fCounter (BitVec.ofNat 64 0)).setV fOffset (BitVec.ofNat 64 1))
      (fun σ s h => h.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ => ⟨⟨Nat.le_refl _, by simp; omega,
        by simp only [Nat.sub_self, Nat.sub_zero]; exact hNN, by rw [Nat.sub_self], by simp only [Nat.sub_self]; exact hu0⟩,
        ?_, h.2⟩
    have r1 := h'.pBase (HO := HO) (k := k) (by exact dpad) (by exact dq)
    rw [Nat.sub_self]
    refine r1.mono (pCfgJ_V hn (fun o ho => by simp [(dLS o ho).1]) (by simp) (by simp) (by simp) (by simp [dU])
      (by simp [upd]) (by simp [upd, fOffset, fP]) (by simp [upd, fCounter, fOffset, fP])
      (by simp [upd, fUsed, fCounter, fOffset, fP, pU]; exact dUv) fun o ho => ?_)
      (fun y hy => hy) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    obtain ⟨m1, m2, m3, m4, -⟩ := hn.ne ho
    simp [upd, m2, m3, m4]; exact (dLS o ho).2
  rw [show N = N - 1 + 1 by omega]
  exact VP.loop (I := pInv c HO G k u0 (N - 1 + 1) X)
    (pBody_vp HO okp lay hlens hp hq hk4 hH hwl hn hk hS hSv hcand) _

end

end VG.Proof.Dsa.RISCV64.PSearch
