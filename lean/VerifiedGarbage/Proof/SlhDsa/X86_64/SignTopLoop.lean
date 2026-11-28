module

-- separate module: the hypertree's loop, apart from the body's composition

public import VerifiedGarbage.Proof.SlhDsa.X86_64.SignTopBody
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.SlhDsa.X86_64.KeyGen
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCT
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsMain
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks
import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4AvxCorrect

/-!
# SLH-DSA (SHAKE) on x86-64, `sign`: the hypertree's layers

Untrusted: everything here is checked by Lean. The loop over the `d`
layers: before layer `j` (`LI`), `sign`'s variables hold the layer, the
tree address and leaf index of `hsFold` and the place of the next XMSS
signature, `oMsg` the message of `hsFold`, and the signature `R`, FORS's
signature and the first `j` XMSS signatures (`hsSig`). Each layer sets
the lanes' addresses, signs with `xmssTree` and steps the indices
(`layer_ok`); the loop ends after layer `d - 1` (`loop_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.SignTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Impl.SlhDsa.X86_64.Shake (oKgSave var)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm)
open VG.Proof.SlhDsa.X86_64.VerifyTop (VPar)

variable {L : SL} {g : Reg → BitVec 64} {m₀ : Mem}

/-- Before layer `j`. -/
structure LI (p : Params) (L : SL) (g : Reg → BitVec 64) (m₀ : Mem) (R sigF M₀ : List Byte) (T₀ I₀ : Nat)
    (σ : State) (j : Nat) (t : State) : Prop where
  ctx : Ctx L g m₀ t
  jd : j ≤ p.d
  v0 : t.mem.readW (L.var 0) 64 = BitVec.ofNat 64 (hsFold p M₀ (L.skSeed m₀) (L.pkSeed m₀) T₀ I₀ j).2.1
  v1 : t.mem.readW (L.var 1) 64 = BitVec.ofNat 64 (hsFold p M₀ (L.skSeed m₀) (L.pkSeed m₀) T₀ I₀ j).2.2
  v2 : t.mem.readW (L.var 2) 64 = BitVec.ofNat 64 j
  v3 : t.mem.readW (L.var 3) 64 = L.sig + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen)
  msg : bytesAt t.mem (at' L.S Layout.oMsg) p.n = (hsFold p M₀ (L.skSeed m₀) (L.pkSeed m₀) T₀ I₀ j).1
  r : bytesAt t.mem L.sig p.n = R
  f : bytesAt t.mem (L.sig + BitVec.ofNat 64 p.n) p.forsSigLen = sigF
  hs : bytesAt t.mem (L.sig + BitVec.ofNat 64 (p.n + p.forsSigLen)) (j * p.xmssSigLen) =
    (List.range j).flatMap (hsSig p M₀ (L.skSeed m₀) (L.pkSeed m₀) T₀ I₀)
  mx : MxEq σ t

theorem hsFold_tree {p : Params} {M skSeed pkSeed : List Byte} {T I : Nat} (hT : T < 2 ^ 64) :
    ∀ k, (hsFold p M skSeed pkSeed T I k).2.1 < 2 ^ 64
  | 0 => hT
  | k + 1 => by
    rw [hsFold_succ]
    exact Nat.lt_of_le_of_lt (by simp only [hsStep, Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _)
      (hsFold_tree hT k)

/-- The first block of a layer. -/
abbrev lblock (p : Params) : List Instr :=
  [.mov .r10 (.mem (var 2)), .mov .r9 (.mem (var 0))] ++ Impl.SlhDsa.X86_64.Shake.treeLanes p .r10 .r9 ++
    [.mov .rdi (.reg .rbx), .mov .rsi (.mem (var 1)), .mov .rdx (.mem (var 3))]

theorem lblock_nm (p : Params) : (Code.block (lblock p) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp [Code.allInstrs_eq, instrs, lblock, Impl.SlhDsa.X86_64.Shake.treeLanes, Impl.SlhDsa.X86_64.setField,
    Impl.SlhDsa.X86_64.setFieldR, List.all_flatMap, loadsMxcsr]

theorem lblock_ok {p : Params} (hL : L.Ok) (hn : L.n = p.n) {t : State} (hc : Ctx L g m₀ t) {j T : Nat}
    (hj : j < 2 ^ 32) (hT : T < 2 ^ 64)
    (h0 : t.mem.readW (L.var 0) 64 = BitVec.ofNat 64 T) (h2 : t.mem.readW (L.var 2) 64 = BitVec.ofNat 64 j)
    {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → Adr L t'.mem (Proof.SlhDsa.layerTree j T) → t'.gpr .rdi = L.S →
      t'.gpr .rsi = t.mem.readW (L.var 1) 64 → t'.gpr .rdx = t.mem.readW (L.var 3) 64 →
      Frame [KeyGen.lanesR L.S] t.mem t'.mem → MxEq t t' → Q t') :
    WP isa (.block (lblock p)) t Q := by
  refine WP.mono_mx (lblock_nm p) (Q := fun t' => Ctx L g m₀ t' ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ?_
    fun t' ⟨a, b, c, d, e, f⟩ hm => k t' a b c d e f (MxEq.of_eq hm)
  have nc : ∀ {r : Reg}, r = .r10 ∨ r = .r9 ∨ r = .rdi ∨ r = .rsi ∨ r = .rdx → ∀ x ∈ calleeSaved, x ≠ r :=
    fun {r} hr x hx => by rcases hr with rfl | rfl | rfl | rfl | rfl <;> (intro e; subst e; revert hx; decide)
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_loadVar hc (by decide) fun t₁ u₁ => wp_loadVar (hc.regs u₁.rd u₁.wr u₁.mem fun r hr => u₁.other r
    (nc (.inl rfl) r hr)) (by decide) fun t₂ u₂ => ?_
  have hc₂ : Ctx L g m₀ t₂ := (hc.regs u₁.rd u₁.wr u₁.mem fun r hr => u₁.other r (nc (.inl rfl) r hr)).regs
    u₂.rd u₂.wr u₂.mem fun r hr => u₂.other r (nc (.inr (.inl rfl)) r hr)
  have hm₂ : t₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  refine WP.block_append (lanes_ok hL hn hj hT hc₂ (by rw [u₂.other _ (by decide), u₁.gpr, h2, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]) (by rw [u₂.gpr, u₁.mem, h0]) fun t₃ hc₃ hg₃ ha₃ hf₃ => ?_)
  rw [hm₂] at hf₃
  have hv : ∀ i < 4, t₃.mem.readW (L.var i) 64 = t.mem.readW (L.var i) 64 := fun i hi => by
    rw [Thash4Avx.readW_frame hf₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Levels.disj_scr L.S (by simp only [Layout.oA, show oKgSave = 34080 from rfl]; omega)
        (by rw [show oKgSave = 34080 from rfl]; omega) (by simp only [Layout.oA]; omega)]
  refine wp_mov fun t₄ u₄ => ?_
  have hc₄ : Ctx L g m₀ t₄ := hc₃.regs u₄.rd u₄.wr u₄.mem fun r hr => u₄.other r (nc (.inr (.inr (.inl rfl))) r hr)
  refine wp_loadVar hc₄ (by decide) fun t₅ u₅ => ?_
  have hc₅ : Ctx L g m₀ t₅ := hc₄.regs u₅.rd u₅.wr u₅.mem fun r hr => u₅.other r (nc (.inr (.inr (.inr (.inl rfl)))) r hr)
  refine wp_loadVar hc₅ (by decide) fun t₆ u₆ => WP.block_nil ?_
  have hc₆ : Ctx L g m₀ t₆ := hc₅.regs u₆.rd u₆.wr u₆.mem fun r hr => u₆.other r (nc (.inr (.inr (.inr (.inr rfl)))) r hr)
  have hm₆ : t₆.mem = t₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  refine ⟨hc₆, by rw [hm₆]; exact ha₃, by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, hc₃.rbx],
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, hv 1 (by decide)],
    by rw [u₆.gpr, u₅.mem, u₄.mem, hv 3 (by decide)], by rw [hm₆]; exact hf₃⟩

/-! ## A layer -/

/-- What the loop needs of the parameter set and the run. -/
structure LP (p : Params) (L : SL) : Prop where
  hp : VPar p
  hz : Wots4.Sz p
  hh : XmssTree.Hps p.hp
  n : L.n = p.n
  sigL : L.sigL = p.sigLen

theorem layer_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hP : LP p L) (hst : T.stack + 24 ≤ L.st) (hL : L.Ok) {R sigF M₀ : List Byte} {T₀ I₀ : Nat}
    (hT₀ : T₀ < 2 ^ 64) (hI₀ : I₀ < 2 ^ p.hp) {σ : State} {j : Nat} (hj : j < p.d) {t : State}
    (hi : LI p L g m₀ R sigF M₀ T₀ I₀ σ j t) :
    WP isa (Impl.SlhDsa.X86_64.Shake.layerBody p f) t fun t' =>
      isa.eval .ne t' = some (decide (j + 1 ≠ p.d)) ∧ LI p L g m₀ R sigF M₀ T₀ I₀ σ (j + 1) t' := by
  have hp := hP.hp
  have hn := hP.n
  have hn32 := hL.n32
  have hhp : 1 ≤ p.hp ∧ p.hp ≤ 9 := ⟨hp.hp1, hp.hp9⟩
  have hsl : p.n + p.forsSigLen + (j + 1) * p.xmssSigLen ≤ L.sigL := by
    rw [hP.sigL, hp.sigLen]; have := Nat.mul_le_mul_right p.xmssSigLen (show j + 1 ≤ p.d by omega); omega
  have hlt : p.n + p.forsSigLen + (j + 1) * p.xmssSigLen < 2 ^ 31 := by
    have := hp.sigLt; rw [hP.sigL, hp.sigLen] at hsl; rw [hp.sigLen] at this; omega
  have hjm : (j + 1) * p.xmssSigLen = j * p.xmssSigLen + p.xmssSigLen := Nat.succ_mul _ _
  have hTj := hsFold_tree (p := p) (M := M₀) (skSeed := L.skSeed m₀) (pkSeed := L.pkSeed m₀) (I := I₀) hT₀ j
  have hIj := hsFold_leaf p (M := M₀) (skSeed := L.skSeed m₀) (pkSeed := L.pkSeed m₀) (idxTree := T₀) hI₀ j
  unfold Impl.SlhDsa.X86_64.Shake.layerBody
  refine WP.seq (lblock_ok hL hn hi.ctx (j := j) (by have := hp.d22; omega) hTj hi.v0 hi.v2
    fun t₁ hc₁ ha₁ h1 h2 h3 hf₁ mx₁ => ?_)
  rw [hi.v1] at h2
  rw [hi.v3] at h3
  -- the lanes keep the signature and `oMsg`
  have hsig₁ : ∀ {a : Addr} {l : Nat}, Region.Sub ⟨a, l⟩ L.SIG → l ≤ 2 ^ 64 → bytesAt t₁.mem a l = bytesAt t.mem a l :=
    fun hs hl => bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.sSig.symm.sub_left hs).sub_right (lanesR_scr hL)) hl
  have hmsg₁ : bytesAt t₁.mem (at' L.S Layout.oMsg) p.n = bytesAt t.mem (at' L.S Layout.oMsg) p.n :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Levels.disj_scr L.S (by simp only [Layout.oA, show Layout.oMsg = 30496 from rfl]; omega)
        (by simp only [show Layout.oMsg = 30496 from rfl]; omega) (by simp only [Layout.oA]; omega)) (by omega)
  have hv₁ : ∀ i < 4, t₁.mem.readW (L.var i) 64 = t.mem.readW (L.var i) 64 := fun i hi' => by
    rw [Thash4Avx.readW_frame hf₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Levels.disj_scr L.S (by simp only [Layout.oA, show oKgSave = 34080 from rfl]; omega)
        (by rw [show oKgSave = 34080 from rfl]; omega) (by simp only [Layout.oA]; omega)]
  refine WP.seq (xmssCall_ok T ht hP.hz hP.hh hst (by have := hL.st62; omega) hL hn
    (o := p.n + p.forsSigLen + j * p.xmssSigLen) (by rw [Nat.add_assoc, ← Nat.succ_mul]; exact hsl)
    (by rw [Nat.add_assoc, ← Nat.succ_mul]; exact hlt) hc₁ ha₁ hIj h1 h2 h3
    fun t₂ hc₂ hv₂ hroot₂ hsig₂ hS₂ mx₂ => ?_)
  rw [hmsg₁, hi.msg] at hsig₂
  refine WP.mono (next_ok hL hhp (by have := hp.d22; omega) hp.xsl hc₂ (j := j) (T := (hsFold p M₀ (L.skSeed m₀)
      (L.pkSeed m₀) T₀ I₀ j).2.1) (o := p.n + p.forsSigLen + j * p.xmssSigLen) (by have := hp.d22; omega) hTj
    (by rw [hv₂ 0 (by decide), hv₁ 0 (by decide)]; exact hi.v0) (by rw [hv₂ 2 (by decide), hv₁ 2 (by decide)]; exact hi.v2)
    (by rw [hv₂ 3 (by decide), hv₁ 3 (by decide)]; exact hi.v3)
    (Q := fun t' => isa.eval .ne t' = some (decide (j + 1 ≠ p.d)) ∧ LI p L g m₀ R sigF M₀ T₀ I₀ σ (j + 1) t')
    fun t₃ hc₃ h0 h1 h2 h3 he hf₃ mx₃ => ⟨he, ?_⟩) fun _ h => h
  -- the next layer's state
  have hS : ∀ {a : Addr} {l : Nat}, Region.Sub ⟨a, l⟩ L.SIG →
      Region.Disjoint ⟨a, l⟩ ⟨L.sig + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen), p.xmssSigLen⟩ →
      l ≤ 2 ^ 64 → bytesAt t₃.mem a l = bytesAt t.mem a l := fun hs hd hl => by
    rw [bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hL.sSig.symm.sub_left hs).sub_right (hL.scr_sub (by rw [show oKgSave = 34080 from rfl]; omega))) hl,
      hS₂ hs hd hl, hsig₁ hs hl]
  have hsl' := hsl
  rw [hP.sigL] at hsl'
  have hsub : ∀ {o l : Nat}, o + l ≤ L.sigL → Region.Sub ⟨L.sig + BitVec.ofNat 64 o, l⟩ L.SIG := fun h =>
    Offset.sub_base _ h
  have hdisj : ∀ {o l : Nat}, o + l ≤ p.n + p.forsSigLen + j * p.xmssSigLen →
      Region.Disjoint ⟨L.sig + BitVec.ofNat 64 o, l⟩ ⟨L.sig + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen),
        p.xmssSigLen⟩ := fun h => Offset.disjoint L.sig (.inl h) (by have := hL.nSig; omega)
      (by have := hL.nSig; have := Nat.mul_le_mul_right p.xmssSigLen (show j + 1 ≤ p.d by omega); omega)
  have e0 : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => by simp
  refine ⟨hc₃, by omega, ?_, ?_, h2, ?_, ?_, ?_, ?_, ?_, hi.mx.trans (mx₁.trans (mx₂.trans mx₃))⟩
  · rw [h0, hsFold_succ]; rfl
  · rw [h1, hsFold_succ]; rfl
  · rw [h3, Nat.add_assoc, Nat.add_assoc, Nat.succ_mul, Nat.add_assoc]
  · rw [bytesAt_frame hf₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Levels.disj_scr L.S (by simp only [show oKgSave = 34080 from rfl, show Layout.oMsg = 30496 from rfl]; omega)
        (by simp only [show Layout.oMsg = 30496 from rfl]; omega) (by rw [show oKgSave = 34080 from rfl]; omega)) (by omega),
      hroot₂, hsFold_succ]
    rfl
  · rw [← hi.r]
    have := hS (a := L.sig + BitVec.ofNat 64 0) (l := p.n) (hsub (by omega)) (hdisj (by omega)) (by omega)
    simpa only [e0] using this
  · rw [← hi.f]; exact hS (hsub (by omega)) (hdisj (by omega)) (by omega)
  · rw [Nat.succ_mul, KeyGen.bytesAt_add, hS (hsub (by omega)) (hdisj (by omega)) (by omega), hi.hs,
      List.range_succ, List.flatMap_append, List.flatMap_singleton, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 1
    rw [bytesAt_frame hf₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.sSig.symm.sub_left (hsub (by omega))).sub_right (hL.scr_sub
        (by rw [show oKgSave = 34080 from rfl]; omega))) (by omega), hsig₂]
    rfl

/-! ## The loop -/

theorem loop_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hP : LP p L) (hst : T.stack + 24 ≤ L.st) (hL : L.Ok) {R sigF M₀ : List Byte} {T₀ I₀ : Nat}
    (hT₀ : T₀ < 2 ^ 64) (hI₀ : I₀ < 2 ^ p.hp) {σ : State} {t : State}
    (hi : LI p L g m₀ R sigF M₀ T₀ I₀ σ 0 t) :
    WP isa (.loop (Impl.SlhDsa.X86_64.Shake.layerBody p f) .ne) t (LI p L g m₀ R sigF M₀ T₀ I₀ σ p.d) := by
  have hd1 := hP.hp.d1
  refine Levels.wpLoop (I := fun m s => 1 ≤ m ∧ m ≤ p.d ∧ LI p L g m₀ R sigF M₀ T₀ I₀ σ (p.d - m) s)
    (fun m => decide (m ≠ 1)) (fun m => m - 1) (fun m s ⟨h1, h2, hs⟩ => ?_) p.d ⟨hd1, Nat.le_refl _, by
      rw [Nat.sub_self]; exact hi⟩
  refine WP.mono (layer_ok T ht hP hst hL hT₀ hI₀ (j := p.d - m) (by omega) hs) fun s' ⟨he, hs'⟩ => ⟨?_, ?_, ?_⟩
  · rw [he]; congr 1; simp only [decide_eq_decide]; omega
  · intro hc
    simp only [decide_eq_false_iff_not, Decidable.not_not] at hc
    subst hc
    rw [show p.d - 1 + 1 = p.d by omega] at hs'; exact hs'
  · intro hc
    simp only [decide_eq_true_eq] at hc
    exact ⟨by omega, ⟨by omega, by omega, by rw [show p.d - (m - 1) = p.d - m + 1 by omega]; exact hs'⟩⟩

end VG.Proof.SlhDsa.X86_64.SignTop
