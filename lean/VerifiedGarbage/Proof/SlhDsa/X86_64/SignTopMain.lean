module

-- separate module: the frame's body composed, apart from the function's entry and contract

public import VerifiedGarbage.Proof.SlhDsa.X86_64.SignTopLoop
public import VerifiedGarbage.Proof.SlhDsa.X86_64.SignTopPro
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.SlhDsa.X86_64.KeyGen
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsMain
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks
import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4AvxCorrect

/-!
# SLH-DSA (SHAKE) on x86-64, `sign`: the frame's body

Untrusted: everything here is checked by Lean. From the frame's push
(`Pushed`): the prologue (`pro_ok`), `R` and the digest (`hashR_ok`,
`hashD_ok`), FORS (`fblock_ok`, `forsCall_ok`), the hypertree (`init_ok`,
`loop_ok`) and the callee-saved registers restored (`body_ok`): the
signature of `slh_sign_internal` for the formatted message `Mp`, in the
terms of `signInternal_eq`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.SignTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout savedRegs copyWords)
open VG.Impl.SlhDsa.X86_64.Shake (oKgSave kgRestore)
open VG.Proof.Sha3.X86_64 (Upd wp_mov32i)
open VG.Proof.SlhDsa.X86_64.VerifyTop (VPar)

variable {L : SL} {g : Reg → BitVec 64} {m₀ : Mem}

theorem pro_nm (p : Params) :
    (Code.block (([.store8 (Impl.SlhDsa.X86_64.Shake.stk (Impl.SlhDsa.X86_64.Shake.fHdr + 1)) .r8,
      .mov .rdi (.mem (Impl.SlhDsa.X86_64.Shake.stk Impl.SlhDsa.X86_64.Shake.fScr))] : List Instr) ++
      Impl.SlhDsa.X86_64.Shake.kgSave .rdi ++
      ([.mov .rbx (.reg .rdi), .mov .rsi (.mem (Impl.SlhDsa.X86_64.Shake.stk Impl.SlhDsa.X86_64.Shake.fKey))] :
        List Instr) ++
      Impl.SlhDsa.X86_64.Shake.rcTable ++
      (List.range 4).flatMap (fun c => copyWords .rbx (Layout.oKeys + 32 * c) .rsi (p.n * c) (p.n / 8)) ++
      Impl.SlhDsa.X86_64.Shake.seedLanes p) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp [Code.allInstrs_eq, instrs, Impl.SlhDsa.X86_64.Shake.kgSave, Impl.SlhDsa.X86_64.Shake.rcTable,
    Impl.SlhDsa.X86_64.Shake.seedLanes, copyWords, List.all_flatMap, List.all_map, loadsMxcsr]

theorem tail_nm : (Code.block (kgRestore ++ ([.mov32 .rax (.imm 1)] : List Instr)) : Prog isa).allInstrs
    (fun i => !loadsMxcsr i) = true := by
  simp [Code.allInstrs_eq, instrs, kgRestore, List.all_map, loadsMxcsr]

/-- The epilogue: the callee-saved registers restored, and 1. -/
theorem epi_ok (_hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {Q : State → Prop}
    (k : ∀ t', t'.mem = t.mem → t'.rd = t.rd → t'.wr = t.wr → t'.gpr .rsp = L.SP →
      (∀ r ∈ calleeSaved, r ≠ .rsp → t'.gpr r = g r) → t'.gpr .rax = BitVec.ofNat 64 1 → MxEq t t' → Q t') :
    WP isa (.block (kgRestore ++ ([.mov32 .rax (.imm 1)] : List Instr))) t Q := by
  let σ : State := { t with gpr := fun r => if r = .rsp then t.gpr .rsp else g r }
  have hsr : ∀ i < 6, savedRegs.getD i .rbx ≠ .rsp := fun i hi => by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  refine WP.mono_mx tail_nm (Q := fun t' => _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) (WP.block_append (KeyGen.restore_ok (σ := σ)
    hc.rbx hc.inScr (fun i hi => by
      rw [hc.saved i hi]; show _ = (if savedRegs.getD i .rbx = .rsp then t.gpr .rsp else g _); rw [ite_eq_right (hsr i hi)])
    (by simp [σ])
    fun t₁ hm hr hw hcs => wp_mov32i fun t₂ u₂ => WP.block_nil ⟨by rw [u₂.mem, hm], by rw [u₂.rd, hr],
      by rw [u₂.wr, hw], ?_, ?_, ?_⟩)) fun t' ⟨a, b, c, d, e, f⟩ hm => k t' a b c d e f (MxEq.of_eq hm)
  · rw [u₂.other _ (by decide), hcs _ (by decide)]; simp [σ, hc.rsp]
  · intro r hr h1
    rw [u₂.other _ (by intro e; subst e; revert hr; decide), hcs r hr]
    simp [σ, h1]
  · rw [u₂.gpr]; rfl

/-! ## The body -/

/-- What signing needs of its run. -/
structure BP (p : Params) (L : SL) (T : Thash4Impl p.n) (fs : Nat) : Prop where
  lp : LP p L
  st : T.stack + 24 ≤ L.st
  fst : fs ≤ L.st
  ok : L.Ok

theorem body_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (F : ForsFn p (Impl.SlhDsa.X86_64.Shake.forsCode p f)) (hB : BP p L T F.stack) {u : State}
    (hu : Pushed L g m₀ u) :
    WP isa (Impl.SlhDsa.X86_64.Shake.signBody p f) u fun s₂ => s₂.gpr .rsp = L.SP ∧
      s₂.wr = L.FR :: [L.SIG, L.SCR] ∧ s₂.rd = L.rd ∧ (∀ r ∈ calleeSaved, r ≠ .rsp → s₂.gpr r = g r) ∧
      s₂.gpr .rax = BitVec.ofNat 64 1 ∧
      bytesAt s₂.mem L.sig p.sigLen = signInternal p (Mp L m₀) (bytesAt m₀ L.sk p.skLen) (bytesAt m₀ L.rnd p.n) ∧
      Frame [L.SCR, L.STK, L.SIG] m₀ s₂.mem ∧ MxEq u s₂ := by
  have hP := hB.lp
  have hL := hB.ok
  have hp := hP.hp
  have hn := hP.n
  have hn32 := hL.n32
  have hst8 : 8 ≤ L.st := by have := hB.st; omega
  have hsigL := hP.sigL
  unfold Impl.SlhDsa.X86_64.Shake.signBody
  -- the prologue
  refine WP.seq (WP.mono_mx (pro_nm p) (pro_ok hL hn hu) fun t₁ hc₁ hm₁ => ?_)
  -- `R`
  refine WP.seq (hashR_ok hL hc₁ hn hst8 fun t₂ hc₂ hR₂ hf₂ mx₂ => ?_)
  -- the digest
  refine WP.seq (hashD_ok hL hc₂ hn hp.m64 hst8 fun t₃ hc₃ hD₃ hf₃ mx₃ => ?_)
  rw [hR₂] at hD₃
  have hR₃ : bytesAt t₃.mem L.sig p.n = bytesAt t₂.mem L.sig p.n :=
    bytesAt_frame hf₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hL.sSig.symm.sub_left (Region.sub_prefix (by rw [← hn]; exact hL.sigN))).sub_right
          (hL.scr_sub (by simp only [show Layout.oStream = 30560 from rfl]; omega))
      · exact (hL.sSig.symm.sub_left (Region.sub_prefix (by rw [← hn]; exact hL.sigN))).sub_right
          (hL.scr_sub (by simp only [show Layout.oDigest = 30304 from rfl]; have := hp.m64; omega))
      · exact (hL.cs_sig.sub_left (SL.Ok.below_cs L (by omega) hL)).symm.sub_left
          (Region.sub_prefix (by rw [← hn]; exact hL.sigN))) (by omega)
  -- FORS's indices and lanes
  refine WP.seq (fblock_ok hp hL hn hc₃ fun t₄ hc₄ h0 h1 ha h1' h2' h3' hmd hS₄ mx₄ => ?_)
  generalize hsd : L.sd p t₃.mem = sd at h0 h1 ha h3'
  have hIL : sd.2.2 < 2 ^ p.hp := by
    rw [← hsd]; simp only [SL.sd, splitDigest, hp.hd]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hIT : sd.2.1 < 2 ^ 64 := by
    rw [← hsd]; simp only [SL.sd, splitDigest]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) (by have := hp.tb; have := hp.tb'; omega))
  -- FORS
  refine WP.seq (forsCall_ok F hB.fst hL hst8 hn (by rw [hsigL, hp.sigLen]; omega) hp.fsl
    (by have := hp.m; have := hp.m64; omega) hc₄ ha (Nat.lt_of_lt_of_le hIL (Nat.pow_le_pow_right (by decide)
      (by have := hp.hp9; omega))) h1' h2' h3' _ fun t₅ hc₅ hv₅ hF₅ hM₅ hS₅ mx₅ => ?_)
  -- the first layer
  refine WP.seq (init_ok hL hp.fsl hc₅ fun t₆ hc₆ v2 v3 v01 hf₆ mx₆ => ?_)
  have hsig₆ : ∀ {a : Addr} {l : Nat}, l ≤ 2 ^ 64 → Region.Sub ⟨a, l⟩ L.SIG → bytesAt t₆.mem a l = bytesAt t₅.mem a l :=
    fun hl hs => bytesAt_frame hf₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.sSig.symm.sub_left hs).sub_right (hL.scr_sub (by rw [show oKgSave = 34080 from rfl]; omega))) hl
  have hsubn : Region.Sub ⟨L.sig, p.n⟩ L.SIG := Region.sub_prefix (by rw [← hn]; exact hL.sigN)
  have hsubf : Region.Sub ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩ L.SIG :=
    Offset.sub_base _ (by rw [hsigL, hp.sigLen]; omega)
  have hRt : bytesAt t₆.mem L.sig p.n = bytesAt t₂.mem L.sig p.n := by
    rw [hsig₆ (by omega) hsubn]
    have := hS₅ (a := L.sig + BitVec.ofNat 64 0) (l := p.n) (by simpa using hsubn)
      (Offset.disjoint L.sig (.inl (by omega)) (by have := hL.nSig; rw [hsigL, hp.sigLen] at this; omega)
        (by have := hL.nSig; rw [hsigL, hp.sigLen] at this; omega)) (by omega)
    simp only [BitVec.add_zero] at this
    rw [this, hS₄ hsubn (by omega), hR₃]
  have hmsg₆ : bytesAt t₆.mem (at' L.S Layout.oMsg) p.n = bytesAt t₅.mem (at' L.S Layout.oMsg) p.n :=
    bytesAt_frame hf₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Levels.disj_scr L.S (by simp only [show oKgSave = 34080 from rfl, show Layout.oMsg = 30496 from rfl]; omega)
        (by simp only [show Layout.oMsg = 30496 from rfl]; omega) (by rw [show oKgSave = 34080 from rfl]; omega)) (by omega)
  have hi₀ : LI p L g m₀ (bytesAt t₂.mem L.sig p.n)
      (forsSign p (mdAt p t₄.mem L.S) (L.skSeed m₀) (L.pkSeed m₀) (Proof.SlhDsa.forsAdrs (Proof.SlhDsa.layerTree 0 sd.2.1) sd.2.2))
      (forsPkFromSig p (forsSign p (mdAt p t₄.mem L.S) (L.skSeed m₀) (L.pkSeed m₀)
        (Proof.SlhDsa.forsAdrs (Proof.SlhDsa.layerTree 0 sd.2.1) sd.2.2)) (mdAt p t₄.mem L.S) (L.pkSeed m₀)
        (Proof.SlhDsa.forsAdrs (Proof.SlhDsa.layerTree 0 sd.2.1) sd.2.2)) sd.2.1 sd.2.2 u 0 t₆ :=
    ⟨hc₆, Nat.zero_le _, by rw [v01 0 (by decide), hv₅ 0 (by decide), h0]; rfl,
      by rw [v01 1 (by decide), hv₅ 1 (by decide), h1]; rfl, v2, by rw [v3]; simp,
      by rw [hmsg₆, hM₅]; rfl, hRt, by rw [hsig₆ (by have := hp.fsl; omega) hsubf, hF₅], by simp [bytesAt],
      (MxEq.of_eq hm₁).trans (mx₂.trans (mx₃.trans (mx₄.trans (mx₅.trans mx₆))))⟩
  -- the layers
  refine WP.seq (WP.mono (loop_ok T ht hP hB.st hL hIT hIL hi₀) fun t₇ hi₇ => ?_)
  refine epi_ok hL hi₇.ctx fun t₈ hm₈ hr₈ hw₈ hsp₈ hcs₈ hax₈ mx₈ => ?_
  refine ⟨hsp₈, by rw [hw₈, hi₇.ctx.wr], by rw [hr₈, hi₇.ctx.rd], hcs₈, hax₈, ?_, by rw [hm₈]; exact hi₇.ctx.frame,
    hi₇.mx.trans mx₈⟩
  -- the signature
  have hmd' : mdAt p t₄.mem L.S = sd.1 := by
    rw [hmd, ← hsd]
    simp only [mdAt, SL.sd, splitDigest]
    rw [bytesAt_take' _ _ (by have := hp.m; omega)]
  have e2 : L.pkSeed m₀ = chunk (bytesAt m₀ L.sk p.skLen) p.n 2 := by
    simp only [SL.pkSeed, Params.skLen, hn]; rw [KeyGen.chunk_bytesAt _ _ (c := 4) (by decide)]
  have e0 : L.skSeed m₀ = chunk (bytesAt m₀ L.sk p.skLen) p.n 0 := by
    simp only [SL.skSeed, Params.skLen, hn]; rw [KeyGen.chunk_bytesAt _ _ (c := 4) (by decide)]
  have e1 : bytesAt m₀ (L.sk + BitVec.ofNat 64 (p.n * 1)) p.n = chunk (bytesAt m₀ L.sk p.skLen) p.n 1 := by
    simp only [Params.skLen]; rw [KeyGen.chunk_bytesAt _ _ (c := 4) (by decide)]
  have e3 : bytesAt m₀ (L.sk + BitVec.ofNat 64 (p.n * 3)) p.n = chunk (bytesAt m₀ L.sk p.skLen) p.n 3 := by
    simp only [Params.skLen]; rw [KeyGen.chunk_bytesAt _ _ (c := 4) (by decide)]
  have e2' : bytesAt m₀ (L.sk + BitVec.ofNat 64 (p.n * 2)) p.n = chunk (bytesAt m₀ L.sk p.skLen) p.n 2 := by
    simp only [Params.skLen]; rw [KeyGen.chunk_bytesAt _ _ (c := 4) (by decide)]
  have hsdD : sd = splitDigest p (Spec.Sha3.shake256 (Spec.Sha3.shake256 (chunk (bytesAt m₀ L.sk p.skLen) p.n 1 ++
      bytesAt m₀ L.rnd p.n ++ Mp L m₀) p.n ++ chunk (bytesAt m₀ L.sk p.skLen) p.n 2 ++
      chunk (bytesAt m₀ L.sk p.skLen) p.n 3 ++ Mp L m₀) p.m) := by
    rw [← hsd]; simp only [SL.sd]; rw [hD₃, ← e1, ← e2', ← e3]
  rw [signInternal_eq hp]
  dsimp only
  rw [hp.sigLen, KeyGen.bytesAt_add _ _ (p.n + p.forsSigLen), KeyGen.bytesAt_add _ _ p.n, hm₈,
    hi₇.r, hi₇.f, hi₇.hs, hR₂, hmd', hsdD, e0, e2, e1]

end VG.Proof.SlhDsa.X86_64.SignTop
