module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.PArith
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.PX
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: one candidate p

`pAttempt` (`pAttempt_vp`): X, p from it, and unless p is below
`2^(L − 1)` (`topBit_vp`) its probable-prime test: `fP` := 0 if the
witnesses ran out, 1 if p is a probable prime, else as it was.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Fupd wp_dp wp_ldrb wp_cmp op2_imm dpVal eval_eq)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords)

theorem top_bit (b : BitVec 8) : ((b.setWidth 32 &&& (128 : BitVec 32)) - 0 == 0) = true ↔ b.toNat < 128 := by
  revert b; decide

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- Z iff the `pLen` big-endian bytes of `pv` at `sPBE` are below `2^(8 pLen − 1)`. -/
theorem topBit_vp {L pv : Nat} (hL : L = G.pLen) (hc : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c.cl)
    (hpv : pv < 256 ^ G.pLen) :
    VP (St G c X) (.block (scr L .r0 sPBE ++ ([.ldrb .r1 .r0 0, .dp .and .r1 .r1 (.imm 0x80), .cmp .r1 (.imm 0)] : List Instr)))
      (fun σ t => St G c X σ t ∧ isa.eval .eq t = some (decide (pv < 2 ^ (8 * G.pLen - 1)))) := by
  refine VP.taint [.r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8])
      (.block (scr 128 .r0 sPBE ++ [.ldrb .r1 .r0 0, .dp .and .r1 .r1 (.imm 0x80), .cmp .r1 (.imm 0)])), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.r8, h₂.1.r8]) fun σ s ⟨h, x⟩ => ?_
  subst hL
  have gi := h.gi
  have big := gi.scrBig
  have l := h.lens
  have hsK : sPBE + G.pLen ≤ sK G.pLen := by simp only [sPBE, sK, sA, wa]; omega
  refine scr_ok (d := .r0) (o := sPBE) h.r8 rfl l (by omega) fun s₁ v₁ R₁ M₁ => ?_
  have a0 : State.addr (s₁.gpr .r0 + BitVec.ofNat 32 0) = G.sa sPBE := by
    rw [BitVec.add_zero, v₁]; exact h.addr (by omega) (by omega)
  have c0 : (G.rs sPBE G.pLen).Contains (G.sa sPBE) 1 := by
    show (_ - _ : Addr).toNat + 1 ≤ G.pLen
    rw [BitVec.sub_self, BitVec.toNat_zero]; omega
  have w0 : InRegions (s.rd ++ s.wr) (G.sa sPBE) 1 :=
    let ⟨r, hr, hcn⟩ := Covers.one (gi.inScr (o := sPBE) (n := G.pLen) (by omega)) _ _
      ⟨_, List.mem_singleton_self _, c0⟩
    ⟨r, List.mem_append_right _ hr, hcn⟩
  refine wp_ldrb (by decide) a0 (by rw [R₁.rd, R₁.wr]; exact w0) fun s₂ u₂ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil ⟨⟨h.of_rest
    (((R₁.mono (by simp)).trans ((u₂.rest (ws := [.r0, .r1, .r12]) (by simp)).trans (u₃.rest (by simp)))).trans
      (f.rest _)) (by rw [f.mem, u₃.mem, u₂.mem, M₁]), x⟩, ?_⟩
  -- The byte: p's first.
  have b := h.sb _ hc
  simp only at b
  rw [VG.Proof.Rsa.i2osp_length] at b
  have byte : s.mem (G.sa sPBE) = (Spec.Rsa.i2osp pv G.pLen).getD 0 0 := by
    rw [← b]; simp [Spec.Rsa.bytesAt, show 0 < G.pLen by omega]
  rw [eval_eq, z, u₃.gpr, dpVal, u₂.gpr, M₁, byte]
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_iff, top_bit,
    ← VG.Proof.Dsa.encodeBE_i2osp]
  exact VG.Proof.Dsa.Generation.candidate_firstByte (by omega) hpv

theorem varOk_fP : VarOk G fP := varOk_of (by decide)

/-- The stage after a test's result recorded in `fP`. -/
def pRes (c0 : Cfg) (wl : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → Cfg
  | none => (testCfg c0 c0.cl wl none).setV fP 0
  | some (true, r) => (testCfg c0 c0.cl wl (some (true, r))).setV fP 1
  | some (false, r) => testCfg c0 c0.cl wl (some (false, r))

/-- `fP` := 0 if the witnesses ran out, 1 for a probable prime. -/
theorem pDecide_vp {c0 : Cfg} {wl : Nat} (res : Option (Bool × Spec.RsaKeyGen.Rand)) :
    VP (St G (testCfg c0 c0.cl wl res) X)
      (VG.Impl.Rsa.Arm.Keys.seqs [.block (cmpF fRes 0), .ite .eq (.block (stImm fP 0))
        (VG.Impl.Rsa.Arm.Keys.seqs [.block (cmpF fRes 1), .ite .eq (.block (stImm fP 1)) (.block [])])])
      (St G (pRes c0 wl res) X) := by
  have vres : ∀ σ s, St G (testCfg c0 c0.cl wl res) X σ s →
      fw s.mem G fRes = BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status res) := fun σ s h => by
    rw [h.1.slotV (by unfold testCfg; split <;> simp)]
    unfold testCfg Proof.Dsa.ProbablePrime.status
    split
    · simp [upd]
    · rename_i b r
      simp only [upd, ite_true]
      cases b <;> rfl
  refine VP.seq (cmpF_vp (fun σ s h => h.1) (by decide) (by decide) (by decide) vres
    fun σ s t h R m e => (⟨⟨h.1.of_rest R m, h.2⟩, e⟩ :
      St G (testCfg c0 c0.cl wl res) X σ t ∧ _)) ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · rcases res with _ | ⟨b, r⟩
    · exact stImm_vp (c := fun _ => testCfg c0 c0.cl wl none) (fun σ s h => h.1.1.1) (by decide) varOk_fP
        fun σ s t h h' _ => ⟨h', h.1.1.2⟩
    · refine VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => ?_
      rw [e] at z
      unfold Proof.Dsa.ProbablePrime.status at z
      cases b <;> simp at z
  · rcases res with _ | ⟨b, r⟩
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [Proof.Dsa.ProbablePrime.status] at z
    refine VP.seq (cmpF_vp (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
      (fun σ s h => vres σ s h.1.1) fun σ s t h R m e => (⟨⟨h.1.1.1.of_rest R m, h.1.1.2⟩, e⟩ :
        St G (testCfg c0 c0.cl wl (some (b, r))) X σ t ∧ _)) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
    · cases b
      · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [Proof.Dsa.ProbablePrime.status] at z
      · exact stImm_vp (c := fun _ => testCfg c0 c0.cl wl (some (true, r))) (fun σ s h => h.1.1.1) (by decide)
          varOk_fP fun σ s t h h' _ => ⟨h', h.1.1.2⟩
    · cases b
      · exact VP.block_nil fun σ s h => h.1.1
      · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [Proof.Dsa.ProbablePrime.status] at z

/-- The claims kept through a candidate p: the padding and q. -/
abbrev pRest {B N L : Nat} (md : MdStream.Md B N L) (G : GP) (k : Nat) : Claims :=
  [(G.qLen, padTail md G.qLen), (sQ, qBytes G k)]

/-- The stage after a candidate p from X (`xv`) and q (`qv`), tested with the
witnesses from `u` unless it is too short. -/
def pAttCfg (c : Cfg) (G : GP) (xv qv : Nat) (rest : Claims) (u : Nat) : Cfg :=
  if pVal xv qv < 2 ^ (8 * G.pLen - 1) then pOut c G xv qv rest
  else pRes (pOut c G xv qv rest) G.witLen (Spec.Dsa.probablePrime (pVal xv qv) (G.witB.drop u))

theorem pAttempt_vp {g : Geo} (HO : HashOk g.G) (okp : PrimeOk (8 * G.pLen) g.pCode)
    (certs : PArithCerts G.pLen G.qLen)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    (hsize : keyOff + 8 * keyWords (8 * G.pLen) ≤ wa G.pLen)
    {k off u : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen)
    (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 32 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 32 off) (hoff : off + (cnt G + 1) < 2 ^ 24)
    (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 32 u) (h88 : fUsedOut ∉ c.LS) (h92 : fUsedOut + 4 ∉ c.LS) :
    VP (St G (pCfg c HO G k off 0 [(sQ, qBytes G k)]) X) g.pAttempt
      (St G (pAttCfg c G (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k))
        (pRest HO.md G k) u) X) := by
  have hq56 : G.qLen < 56 := by omega_arith
  have pl := padTail_length HO.md hq56 HO.hL
  have hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega_arith
  have hHl : ∀ j, (hX HO G k off j).length = G.qLen := fun j => by
    rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega_arith), HO.md.digest_length, HO.hN, hk4]
  have hc : (cnt G + 1) * G.qLen + G.qLen ≤ G.pLen + 64 ∧ G.pLen ≤ (cnt G + 1) * G.qLen := by
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
  have qpos : 0 < Spec.Dsa.decodeBE (qBytes G k) := by
    rw [hqv]; have := (VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * G.qLen) (by omega_arith) (seedAt G k)).2.1
    have : 0 < 2 ^ (8 * G.qLen - 1) := Nat.two_pow_pos _
    omega_arith
  have hXv : sX = 192 := rfl
  have hAv : sA = 4096 := rfl
  have hQv : sQ = 128 := rfl
  have hPBE : sPBE = 576 := rfl
  unfold Geo.pAttempt
  rw [hp, hq]
  refine VP.seq (pX_vp HO hlq hp hq hk4 hsb hk hS hSv hO hOv hoff (rest := [(sQ, qBytes G k)]) fun y hy => by
    rw [List.mem_singleton] at hy; subst hy
    simp only [Apart, ql, pStart]; omega_arith) ?_
  refine VP.seq (pArith_vp certs hlq (by simp) xl (by simp) ql qpos (rest := pRest HO.md G k) fun y hy => by
    simp only [pRest, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact ⟨by simp, by simp only [Apart, pl]; omega_arith⟩
    · exact ⟨by simp, by simp only [Apart, ql]; omega_arith⟩) ?_
  have xlt : Spec.Dsa.decodeBE (xBytes HO G k off) < 2 ^ (8 * G.pLen) := by
    have := VG.Proof.Dsa.decodeBE_lt (xBytes HO G k off)
    rwa [xl, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  have plt := pVal_lt (q := Spec.Dsa.decodeBE (qBytes G k)) (show 1 ≤ 8 * G.pLen by omega_arith) xlt
  have plt' : pVal (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k)) < 256 ^ G.pLen := by
    rwa [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  refine VP.seq (topBit_vp rfl (by simp) plt') ?_
  generalize hpv : pVal (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k)) = pv at plt plt'
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · by_cases hcnd : pv < 2 ^ (8 * G.pLen - 1)
    · refine VP.block_nil fun σ s ⟨⟨h, _⟩, _⟩ => ?_
      unfold pAttCfg
      rw [hpv, ite_eq_left (by exact hcnd)]
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
    have cl0 : c0.cl = (sPBE, Spec.Rsa.i2osp pv G.pLen) :: pRest HO.md G k := by rw [← hc0, ← hpv]
    have eLS : c0.LS = c.LS := by rw [← hc0]
    have eV : c0.V = c.V := by rw [← hc0]
    have big : ∀ y ∈ c0.cl, y.1 + y.2.length ≤ 4096 := fun y hy => by
      rw [cl0] at hy
      simp only [pRest, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · simp only [VG.Proof.Rsa.i2osp_length]; omega_arith
      · simp only [pl]; omega_arith
      · simp only [ql]; omega_arith
    have pin : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c0.cl := by rw [cl0]; simp
    let c1 : Cfg := { c0 with cl := (sA, Spec.Rsa.i2osp pv G.pLen) :: c0.cl }
    refine VP.seq (G := St G c1 X) (copyS_vp (c := fun _ => c0) (fun σ s h => h.1.1.1) rfl (dst := sA) (src := sPBE)
      (n := G.pLen) (by omega_arith) (by omega_arith) (by simp only [sK, sA, wa]; omega_arith) (by simp only [sK, sA, wa]; omega_arith)
      (.inr (by omega_arith)) fun σ s t h R f e => ⟨?_, h.1.1.2⟩) ?_
    · have b := h.1.1.1.sb _ pin
      simp only [VG.Proof.Rsa.i2osp_length] at b
      refine h.1.1.1.of_scr R (o := sA) (n := G.pLen) (by simp only [sK, sA, wa]; omega_arith) (f.mono (by simp))
        fun y hy => ?_
      rcases List.mem_cons.mp hy with rfl | hy
      · exact .inr ⟨by rw [VG.Proof.Rsa.i2osp_length, e, b], by simp only [VG.Proof.Rsa.i2osp_length, sK, sA, wa]; omega_arith⟩
      · exact .inl ⟨hy, .inl (by have := big y hy; omega_arith)⟩
    refine VP.seq (test_vp (c := c1) (cb := Spec.Rsa.i2osp pv G.pLen) okp rfl hu (by simp only [c1, eLS]; exact hU)
      (by simp only [c1, eV]; exact hUv) hwl hsize (by simp only [wa]; omega_arith) (by simp [c1])
      (by rw [VG.Proof.Rsa.i2osp_length]; omega_arith) (by rw [pb]; exact podd) (by rw [pb]; exact pbl) (by simp only [c1, eLS]; exact h88) (by simp only [c1, eLS]; exact h92)
      (cl' := c0.cl) fun y hy => ⟨by simp [c1, hy], .inl (by have := big y hy; omega_arith)⟩) ?_
    rw [pb, show testCfg c1 c0.cl G.witLen (Spec.Dsa.probablePrime pv (G.witB.drop u)) =
      testCfg c0 c0.cl G.witLen (Spec.Dsa.probablePrime pv (G.witB.drop u)) by unfold testCfg; split <;> rfl]
    exact pDecide_vp _

end

end VG.Proof.Dsa.Arm.Gen
