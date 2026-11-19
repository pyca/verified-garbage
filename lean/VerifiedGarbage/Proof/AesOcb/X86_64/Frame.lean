module

public import VerifiedGarbage.Proof.AesOcb.Scratch
import VerifiedGarbage.Proof.AesOcb.X86_64.InitCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesOcb.X86_64.Seal
public import VerifiedGarbage.Proof.AesOcb.X86_64.Nonce
import VerifiedGarbage.Proof.AesOcb.X86_64.Open
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.AesOcb.X86_64.Open
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Impl.AesOcb.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.AesCcm.X86_64.CTBase
public import VerifiedGarbage.Proof.AesOcb.X86_64.Body
import VerifiedGarbage.Proof.AesOcb.X86_64.Run
import VerifiedGarbage.Proof.AesCcm.X86_64.Run
import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.AesOcb.X86_64.Seal
meta import VerifiedGarbage.Proof.AesCcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesOcb.X86_64.Body
meta import VerifiedGarbage.Proof.AesOcb.X86_64.Run
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Run
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesOcb.X86_64.NonceBlock
meta import VerifiedGarbage.Proof.AesOcb.X86_64.Nonce
meta import VerifiedGarbage.Proof.AesOcb.X86_64.NonceBlock
public import VerifiedGarbage.Proof.AesOcb.X86_64.Hash
import VerifiedGarbage.Proof.AesOcb.X86_64.PadTo
meta import VerifiedGarbage.Proof.AesOcb.X86_64.Hash
meta import VerifiedGarbage.Proof.AesOcb.X86_64.PadTo
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.AesOcb.X86_64.Words
meta import VerifiedGarbage.Proof.AesOcb.X86_64.Words

/-! ### `AesOcb.X86_64.SealCT`, which this module and modules that import it used -/

section

/-! ### `AesOcb.X86_64.CTBase`, which this module and modules that import it used -/

section

/-!
# AES-OCB on x86-64: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs piece by piece (`RelCT`). Both runs have the same public
arguments, kept in the slots of `W` (`Slots`), so the taint analysis starts
from the registers that agree, those slots and the words `ex` of `W` that
also agree, public (`ocbT`, `both_agree`); what correctness says about each
run is added with `RelCT.wp`. The calls of `vg_aes_encrypt_blocks` and
`vg_aes_decrypt_blocks` have the same arguments in both runs
(`callBlocks_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm.X86_64 (word_byte add_ofNat_assoc runBlock_append)

/-- The taint: the registers `rs`, `r14`, `r15` and `rsp` public, `r15` the
base of the working space (the second writable region), the slots of the
public arguments `[208, 248)` and `[288, 304)` and the words at `ex` public. -/
def ocbTN (rs : List Reg) (ex : List Nat) (wn : Nat) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.r14, .r15, .rsp]), flags := false, lens := [0, wn], bases := [(.r15, 1, 0)],
    slots := [(1, 208, 40), (1, 288, 16)] ++ ex.map fun d => (1, d, 8) }

abbrev ocbT (rs : List Reg) (ex : List Nat) : X86_64.Taint.T := ocbTN rs ex 3584

/-- Two runs with the same public arguments: both in the environment, with
the same slots and writable regions, agreeing on the registers `rs` and the
words of `W` at `ex`. -/
structure BothN (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (rs : List Reg) (ex : List Nat)
    (wn : Nat) (s₁ s₂ : State) : Prop where
  e₁ : EnvN K W SP wn s₁
  e₂ : EnvN K W SP wn s₂
  sl₁ : Slots W R N A D nl n tl s₁.mem
  sl₂ : Slots W R N A D nl n tl s₂.mem
  wr₁ : s₁.wr = [⟨D, n⟩, ⟨W, wn⟩]
  wr₂ : s₂.wr = [⟨D, n⟩, ⟨W, wn⟩]
  agree : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r
  ex : ∀ d ∈ ex, d + 8 ≤ wn ∧ s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s₂.mem.readW (W + BitVec.ofNat 64 d) 64

abbrev Both (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (rs : List Reg) (ex : List Nat)
    (s₁ s₂ : State) : Prop := BothN K W SP R N A D nl n tl rs ex 3584 s₁ s₂

theorem both_agreeN {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {rs : List Reg} {ex : List Nat}
    {wn : Nat} {s₁ s₂ : State} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, wn⟩) (hn : n ≤ 2 ^ 64)
    (h : BothN K W SP R N A D nl n tl rs ex wn s₁ s₂) (hwn : 304 ≤ wn := by decide) (hwlt : wn ≤ 2 ^ 64 := by decide) :
    X86_64.Taint.Agree (ocbTN rs ex wn) s₁ s₂ := by
  have wf : ∀ {s : State}, EnvN K W SP wn s → s.wr = [⟨D, n⟩, ⟨W, wn⟩] → X86_64.Taint.Wf (ocbTN rs ex wn) s :=
    fun E hw => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
    · rw [hw]; exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
    · rw [hw]; exact List.pairwise_pair.mpr hDW
    · rw [hw]; intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hn
      · exact hwlt
    · simp only [ocbTN, List.mem_singleton] at hp; subst hp
      simp only [X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
      rw [E.r15, BitVec.add_zero]
  have hb : ∀ s : State, s.wr = [⟨D, n⟩, ⟨W, wn⟩] → ∀ k, X86_64.Taint.byteAddr s 1 k = W + BitVec.ofNat 64 k :=
    fun s hw k => by
      simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
  have hw : ∀ {k : Nat} (d : Nat), d ≤ k → W + BitVec.ofNat 64 k = W + BitVec.ofNat 64 d + BitVec.ofNat 64 (k - d) :=
    fun {k} d e => by rw [add_ofNat_assoc, show d + (k - d) = k by omega_using [e]]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [h.wr₁, h.wr₂], wf h.e₁ h.wr₁, wf h.e₂ h.wr₂,
    fun sl hsl => ?_, fun sl hsl k hk₁ hk₂ => ?_, X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with hr | hr
    · exact h.agree r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.e₁.r14, h.e₂.r14]
      · rw [h.e₁.r15, h.e₂.r15]
      · rw [h.e₁.rsp, h.e₂.rsp]
  · simp only [ocbTN, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hsl
    rcases hsl with (rfl | rfl) | ⟨d, hd, rfl⟩
    · simp only [ocbTN, List.getD_cons_succ, List.getD_cons_zero]; omega_arith
    · simp only [ocbTN, List.getD_cons_succ, List.getD_cons_zero]; omega_arith
    · simp only [ocbTN, List.getD_cons_succ, List.getD_cons_zero]; exact (h.ex d hd).1
  · simp only [ocbTN, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hsl
    have S₁ := h.sl₁
    have S₂ := h.sl₂
    rcases hsl with (rfl | rfl) | ⟨d, hd, rfl⟩ <;> rw [hb s₁ h.wr₁, hb s₂ h.wr₂]
    · simp only at hk₁ hk₂
      have key : ∀ d, d ∈ [208, 216, 224, 232, 240] → d ≤ k → k < d + 8 →
          s₁.mem (W + BitVec.ofNat 64 k) = s₂.mem (W + BitVec.ofNat 64 k) := fun d hd h₁ h₂ => by
        rw [hw d h₁]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl
        · exact word_byte S₁.data S₂.data (by omega_using [h₂])
        · exact word_byte S₁.len S₂.len (by omega_using [h₂])
        · exact word_byte S₁.tl S₂.tl (by omega_using [h₂])
        · exact word_byte S₁.rounds S₂.rounds (by omega_using [h₂])
        · exact word_byte S₁.aad S₂.aad (by omega_using [hk₂])
      have hq : (k - 208) / 8 = 0 ∨ (k - 208) / 8 = 1 ∨ (k - 208) / 8 = 2 ∨ (k - 208) / 8 = 3 ∨
          (k - 208) / 8 = 4 := by omega_using [hk₂]
      exact key (208 + 8 * ((k - 208) / 8)) (by
        rcases hq with h | h | h | h | h <;> rw [h] <;> decide) (by omega_using [hk₁]) (by omega_using [])
    · simp only at hk₁ hk₂
      by_cases hk : k < 296
      · rw [hw 288 (by omega_using [hk₁])]; exact word_byte S₁.nonce S₂.nonce (by omega_using [hk])
      · rw [hw 296 (by omega_using [hk])]; exact word_byte S₁.nlen S₂.nlen (by omega_using [hk₂])
    · simp only at hk₁ hk₂
      rw [hw d hk₁]; exact word_byte (h.ex d hd).2 rfl (by omega_using [hk₂])

theorem both_agree {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {rs : List Reg} {ex : List Nat}
    {s₁ s₂ : State} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hn : n ≤ 2 ^ 64)
    (h : Both K W SP R N A D nl n tl rs ex s₁ s₂) : X86_64.Taint.Agree (ocbT rs ex) s₁ s₂ :=
  both_agreeN hDW hn h

/-- Code the taint analysis checks from `ocbTN rs ex wn`. -/
theorem rel_taintCN {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl wn : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (ex : List Nat) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, wn⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → BothN K W SP R N A D nl n tl rs ex wn s₁ s₂)
    (hc : ∃ hc, (taint.check (ocbTN rs ex wn) c hc).isSome = true) (hwn : 304 ≤ wn := by decide)
    (hwlt : wn ≤ 2 ^ 64 := by decide) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (ocbTN rs ex wn) (fun s₁ s₂ h => both_agreeN hDW hn (hP _ _ h) hwn hwlt) hc

/-- Code the taint analysis checks from `ocbT rs ex`. -/
theorem rel_taintC {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (ex : List Nat) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → Both K W SP R N A D nl n tl rs ex s₁ s₂)
    (hc : ∃ hc, (taint.check (ocbT rs ex) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  rel_taintCN rs ex hDW hn hP hc

/-- Code the taint analysis checks from `ocbT rs ex`, leaving the flags public. -/
theorem rel_flagsC {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (ex : List Nat) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → Both K W SP R N A D nl n tl rs ex s₁ s₂)
    (hc : ∃ hc, ((taint.check (ocbT rs ex) c hc).map (·.flags)) = some true) :
    RelCT isa P c fun s₁ s₂ => s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf := by
  obtain ⟨_, h⟩ := hc
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (both_agree hDW hn (hP _ _ hp)) e₁ e₂
  obtain ⟨hcf, hzf, -, -⟩ := ha.rf.2 hs
  exact ⟨ht, hcf, hzf⟩

/-- Runs related from each pair of states. -/
theorem rel_of_pt {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, P σ₁ σ₂ → RelCT isa (fun t₁ t₂ => t₁ = σ₁ ∧ t₂ = σ₂) c Q) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

/-- One run with the public arguments. -/
structure OneN (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (wn : Nat) (s : State) : Prop where
  env : EnvN K W SP wn s
  sl : Slots W R N A D nl n tl s.mem
  wr : s.wr = [⟨D, n⟩, ⟨W, wn⟩]

abbrev One (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (s : State) : Prop :=
  OneN K W SP R N A D nl n tl 3584 s

theorem BothN.of {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl wn : Nat} {s₁ s₂ : State}
    (o₁ : OneN K W SP R N A D nl n tl wn s₁) (o₂ : OneN K W SP R N A D nl n tl wn s₂) :
    BothN K W SP R N A D nl n tl [] [] wn s₁ s₂ :=
  ⟨o₁.env, o₂.env, o₁.sl, o₂.sl, o₁.wr, o₂.wr, fun _ h => (nomatch h), fun _ h => (nomatch h)⟩

theorem Both.of {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {s₁ s₂ : State}
    (o₁ : One K W SP R N A D nl n tl s₁) (o₂ : One K W SP R N A D nl n tl s₂) :
    Both K W SP R N A D nl n tl [] [] s₁ s₂ := BothN.of o₁ o₂

/-- One run, after a frame within the parts the pieces write. -/
theorem One.step {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} (L : Lay K W SP)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) {s s' : State} (o : One K W SP R N A D nl n tl s)
    (E : Env K W SP s') (hw : s'.wr = s.wr) (f : Frame (mutR W SP D n) s.mem s'.mem) :
    One K W SP R N A D nl n tl s' :=
  ⟨E, Slots.of_mut L hDW f o.sl, hw.trans o.wr⟩

/-- The data, in a run with the public arguments. -/
theorem DBufN.of_one {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {s s' : State}
    (h : DBuf K W SP s D n) (o : One K W SP R N A D nl n tl s') : DBuf K W SP s' D n where
  toBufN := { h.toBufN with rd := Covers.right (by rw [o.wr]; exact Covers.of_mem fun r hr => by simp_all) }
  wr := by rw [o.wr]; exact Covers.of_mem fun r hr => by simp_all
  k := h.k

/-- A call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on the same
`n` blocks at `D'` in both runs. -/
theorem callBlocks_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86_64 f).pre (Proof.Aes.blocksX86_64 f).pub b.code)
    {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D : Addr} {nl n tl : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hn : n ≤ 2 ^ 64) {args : List Instr} (rs : List Reg)
    (ex : List Nat)
    (hc : ∃ hc, (taint.check (ocbT rs ex)
      (.block (args ++ [mvr .rdi .r14, ld .rsi .r15 rndO, mvr .r8 .r15, addi .r8 scrO])) hc).isSome = true)
    {D' : Addr} {k : Nat} {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → Both K W SP R N A D nl n tl rs ex s₁ s₂ ∧ ArgsOk args s₁ D' k ∧ ArgsOk args s₂ D' k ∧
      Dst K W SP s₁ D' k ∧ Dst K W SP s₂ D' k) :
    RelCT isa P (callBlocks b args) fun _ _ => True := by
  unfold callBlocks
  have a := (rel_taintC rs ex hDW hn (fun s₁ s₂ h => (hP s₁ s₂ h).1) hc).wp
    (F₁ := fun (s : State) => BCall s K D' (W + BitVec.ofNat 64 512) R k ∧ s.gpr .rsp = SP)
    (F₂ := fun (s : State) => BCall s K D' (W + BitVec.ofNat 64 512) R k ∧ s.gpr .rsp = SP) fun s₁ s₂ h => by
      obtain ⟨B, a₁, a₂, d₁, d₂⟩ := hP s₁ s₂ h
      exact ⟨WP.mono (callArgs_ok L B.e₁ hR B.sl₁.rounds a₁ d₁) fun _ q => ⟨q.1, q.2.1⟩,
        WP.mono (callArgs_ok L B.e₂ hR B.sl₂.rounds a₂ d₂) fun _ q => ⟨q.1, q.2.1⟩⟩
  exact RelCT.seq a (blk_rel ok ct fun s₁ s₂ h => ⟨K, D', _, R, k, h.2.1.1, h.2.2.1, h.2.1.2.trans h.2.2.2.symm⟩)

end VG.Proof.AesOcb.X86_64

end

end

/-! ### `AesOcb.X86_64.BodyCT`, which only this module used -/

section

/-! ### `AesOcb.X86_64.RestCT`, which this module and modules that import it used -/

section

/-! ### `AesOcb.X86_64.TagCT`, which this module and modules that import it used -/

section

/-!
# AES-OCB on x86-64: the tag is constant time

Untrusted: everything here is checked by Lean. The blocks before and after
the call pass the taint analysis from the public slots (`rel_taintC`); the
call of `vg_aes_encrypt_blocks` has the same arguments in both runs
(`callBlocks_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append)

/-- A call of `vg_aes_encrypt_blocks` on the block at `W + tmpO` keeps the
public arguments. -/
theorem callTmp_one (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) {s : State}
    (o : One K W SP R N A D nl n tl s) :
    WP isa (callBlocks (callees v).enc (oneBlock tmpO)) s (One K W SP R N A D nl n tl) :=
  WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encDepth L o.env hR o.sl.rounds
    (oneBlock_ok o.env.r15 tmpO (by decide)) (dstW L o.env.perm (d := tmpO) (n := 1) (by decide))) fun s' Q => by
    have E' := o.env.of_saved Q.saved Q.rd Q.wr
    refine o.step L hDW E' Q.wr (Q.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
    · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
    · rw [o.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩

/-- The call on the block at `W + tmpO`, in two runs. -/
theorem callTmp_rel (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hn : n ≤ 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → One K W SP R N A D nl n tl s₁ ∧ One K W SP R N A D nl n tl s₂) :
    RelCT isa P (callBlocks (callees v).enc (oneBlock tmpO)) fun s₁ s₂ =>
      One K W SP R N A D nl n tl s₁ ∧ One K W SP R N A D nl n tl s₂ :=
  ((callBlocks_rel (b := (callees v).enc) v.encOk v.encCt L hR hDW hn [] [] (args := oneBlock tmpO)
    ⟨_, by taint_decide⟩ (D' := W + BitVec.ofNat 64 tmpO) (k := 1) fun s₁ s₂ h =>
      ⟨Both.of (hP s₁ s₂ h).1 (hP s₁ s₂ h).2, oneBlock_ok (hP s₁ s₂ h).1.env.r15 tmpO (by decide),
        oneBlock_ok (hP s₁ s₂ h).2.env.r15 tmpO (by decide), dstW L (hP s₁ s₂ h).1.env.perm (by decide),
        dstW L (hP s₁ s₂ h).2.env.perm (by decide)⟩).wp
    (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun s₁ s₂ h => ⟨callTmp_one v L hR hDW (hP s₁ s₂ h).1, callTmp_one v L hR hDW (hP s₁ s₂ h).2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-- The checksum, the offset and `L_$` at `W + tmpO`. -/
theorem tagHead_one {K W SP : Addr} (L : Lay K W SP) {N A D : Addr} {R nl n tl : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) {s : State} (o : One K W SP R N A D nl n tl s) :
    WP isa (.block (copy16 ckO tmpO ++ xor16 .r15 ofsO tmpO ++ xor16 .r15 ldO tmpO)) s
      (One K W SP R N A D nl n tl) := by
  have E := o.env
  obtain ⟨t₁, run₁, B₁⟩ := copy16_ok (s := s) (a := ckO) (d := tmpO) E.r15
    (E.perm.wR (by decide)) (E.perm.wR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have nE : ∀ r ∈ [Reg.r14, .r15, .rsp], r ∉ [Reg.rax, .rdx] := by decide
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => B₁.gpr r (nE r hr)) B₁.rd B₁.wr
  obtain ⟨t₂, run₂, B₂⟩ := xor16_ok (s := t₁) (b := .r15) (a := ofsO) (d := tmpO) E₁.r15 E₁.r15 (by decide) (by decide)
    (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide)) (E₁.perm.wW (by decide)) (E₁.perm.wW (by decide))
  have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => B₂.gpr r (nE r hr)) B₂.rd B₂.wr
  obtain ⟨t₃, run₃, B₃⟩ := xor16_ok (s := t₂) (b := .r15) (a := ldO) (d := tmpO) E₂.r15 E₂.r15 (by decide) (by decide)
    (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide)) (E₂.perm.wW (by decide)) (E₂.perm.wW (by decide))
  have E₃ : Env K W SP t₃ := E₂.keep (fun r hr => B₃.gpr r (nE r hr)) B₃.rd B₃.wr
  refine WP.of_runBlock ⟨t₃, by rw [runBlock_append, runBlock_append, run₁, Option.bind_some, run₂,
    Option.bind_some, run₃], o.step L hDW E₃ (by rw [B₃.wr, B₂.wr, B₁.wr])
      (((B₁.frame.trans B₂.frame).trans B₃.frame).sub fun r hr => ?_)⟩
  simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩

/-- `tag d` in two runs. -/
theorem tag_rel (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hn : n ≤ 2 ^ 64)
    {d : Nat} (hd : d = tagO ∨ d = t2O) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → One K W SP R N A D nl n tl s₁ ∧ One K W SP R N A D nl n tl s₂) :
    RelCT isa P (tag (callees v) d) fun _ _ => True := by
  have a := (rel_taintC [] [] hDW hn (fun s₁ s₂ h => Both.of (hP s₁ s₂ h).1 (hP s₁ s₂ h).2)
    (c := .block (copy16 ckO tmpO ++ xor16 .r15 ofsO tmpO ++ xor16 .r15 ldO tmpO)) ⟨_, by taint_decide⟩).wp
    (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun s₁ s₂ h => ⟨tagHead_one L hDW (hP s₁ s₂ h).1, tagHead_one L hDW (hP s₁ s₂ h).2⟩
  have b := callTmp_rel v L hR hDW hn (P := fun s₁ s₂ => True ∧ One K W SP R N A D nl n tl s₁ ∧
    One K W SP R N A D nl n tl s₂) fun _ _ h => h.2
  have c := rel_taintC [] [] hDW hn (fun s₁ s₂ (h : One K W SP R N A D nl n tl s₁ ∧ One K W SP R N A D nl n tl s₂) =>
    Both.of h.1 h.2) (c := .block (copy16 tmpO d ++ xor16 .r15 sumO d))
    (by rcases hd with rfl | rfl <;> exact ⟨_, by taint_decide⟩)
  exact RelCT.seq a (RelCT.seq b c)

end VG.Proof.AesOcb.X86_64

end

end

/-!
# AES-OCB on x86-64: the rest of the data is constant time

Untrusted: everything here is checked by Lean. The code around the call
passes the taint analysis from the public slots and the address and length
of the rest in `rbx` and `r12` (`rel_taintC`); the call of
`vg_aes_encrypt_blocks` has the same arguments in both runs (`callTmp_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append)

/-- A run before the rest: the public arguments, its address and length. -/
def RRun (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (P : Addr) (r : Nat) (s : State) : Prop :=
  One K W SP R N A D nl n tl s ∧ s.gpr .rbx = P ∧ s.gpr .r12 = BitVec.ofNat 64 r

theorem both_rr {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {P : Addr} {r : Nat} {s₁ s₂ : State}
    (h₁ : RRun K W SP R N A D nl n tl P r s₁) (h₂ : RRun K W SP R N A D nl n tl P r s₂) :
    Both K W SP R N A D nl n tl [.rbx, .r12] [] s₁ s₂ :=
  ⟨h₁.1.env, h₂.1.env, h₁.1.sl, h₂.1.sl, h₁.1.wr, h₂.1.wr, fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2], fun _ h => (nomatch h)⟩

/-- `Offset_*` and a copy of it at `W + tmpO`. -/
theorem restHead1_one {K W SP : Addr} (L : Lay K W SP) {N A D : Addr} {R nl n tl : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) {P : Addr} {r : Nat} {s : State}
    (h : RRun K W SP R N A D nl n tl P r s) :
    WP isa (.block (xor16 .r14 240 ofsO ++ copy16 ofsO tmpO)) s (RRun K W SP R N A D nl n tl P r) := by
  have E := h.1.env
  obtain ⟨t₁, run₁, B₁⟩ := xor16_ok (s := s) (b := .r14) (a := 240) (d := ofsO) E.r15 E.r14 (by decide) (by decide)
    (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have nE : ∀ r ∈ [Reg.r14, .r15, .rsp], r ∉ [Reg.rax, .rdx] := by decide
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => B₁.gpr r (nE r hr)) B₁.rd B₁.wr
  obtain ⟨t₂, run₂, B₂⟩ := copy16_ok (s := t₁) (a := ofsO) (d := tmpO) E₁.r15
    (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide)) (E₁.perm.wW (by decide)) (E₁.perm.wW (by decide))
  have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => B₂.gpr r (nE r hr)) B₂.rd B₂.wr
  refine WP.of_runBlock ⟨t₂, by rw [runBlock_append, run₁, Option.bind_some, run₂],
    h.1.step L hDW E₂ (by rw [B₂.wr, B₁.wr]) (((B₁.frame.sub fun r hr => ?_).trans (B₂.frame.sub fun r hr => ?_))),
    by rw [B₂.gpr _ (by decide), B₁.gpr _ (by decide), h.2.1], by rw [B₂.gpr _ (by decide), B₁.gpr _ (by decide), h.2.2]⟩
  all_goals simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩

/-- The call on the block at `W + tmpO` keeps the callee-saved registers. -/
theorem callTmp_rr (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) {P : Addr} {r : Nat} {s : State}
    (h : RRun K W SP R N A D nl n tl P r s) :
    WP isa (callBlocks (callees v).enc (oneBlock tmpO)) s (RRun K W SP R N A D nl n tl P r) :=
  WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encDepth L h.1.env hR h.1.sl.rounds
    (oneBlock_ok h.1.env.r15 tmpO (by decide)) (dstW L h.1.env.perm (d := tmpO) (n := 1) (by decide))) fun s' Q => by
    have E' := h.1.env.of_saved Q.saved Q.rd Q.wr
    refine ⟨h.1.step L hDW E' Q.wr (Q.frame.sub fun r hr => ?_), by rw [Q.saved _ (by decide), h.2.1],
      by rw [Q.saved _ (by decide), h.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
    · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
    · rw [h.1.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩

/-- `rest enc` in two runs. -/
theorem rest_rel (v : BlocksImpl) (enc : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩)
    (hn : n ≤ 2 ^ 64) {P : Addr} {r : Nat} {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → RRun K W SP R N A D nl n tl P r s₁ ∧ RRun K W SP R N A D nl n tl P r s₂) :
    RelCT isa Q (rest (callees v) enc) fun _ _ => True := by
  unfold rest
  have a := (rel_taintC [.rbx, .r12] [] hDW hn (fun s₁ s₂ h => both_rr (hQ s₁ s₂ h).1 (hQ s₁ s₂ h).2)
    (c := .block (xor16 .r14 240 ofsO ++ copy16 ofsO tmpO)) ⟨_, by taint_decide⟩).wp
    (F₁ := RRun K W SP R N A D nl n tl P r) (F₂ := RRun K W SP R N A D nl n tl P r)
    fun s₁ s₂ h => ⟨restHead1_one L hDW (hQ s₁ s₂ h).1, restHead1_one L hDW (hQ s₁ s₂ h).2⟩
  have b := ((callTmp_rel v L hR hDW hn (P := fun s₁ s₂ => True ∧ RRun K W SP R N A D nl n tl P r s₁ ∧
    RRun K W SP R N A D nl n tl P r s₂) fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩).wp
    (F₁ := RRun K W SP R N A D nl n tl P r) (F₂ := RRun K W SP R N A D nl n tl P r)
    fun s₁ s₂ h => ⟨callTmp_rr v L hR hDW h.2.1, callTmp_rr v L hR hDW h.2.2⟩)
  have c := rel_taintC [.rbx, .r12] [] hDW hn (fun s₁ s₂ (h : (One K W SP R N A D nl n tl s₁ ∧
      One K W SP R N A D nl n tl s₂) ∧ RRun K W SP R N A D nl n tl P r s₁ ∧ RRun K W SP R N A D nl n tl P r s₂) =>
    both_rr h.2.1 h.2.2) (c := if enc then .seq padCk xorPad else .seq xorPad padCk)
    (by cases enc <;> exact ⟨_, by taint_decide⟩)
  exact RelCT.seq a (RelCT.seq b c)

end VG.Proof.AesOcb.X86_64

end

end

/-! ### `AesOcb.X86_64.WholeCT`, which only this module used -/

section

/-!
# AES-OCB on x86-64: the whole blocks are constant time

Untrusted: everything here is checked by Lean. Each pass passes the taint
analysis from the public slots and the number of blocks in `r13`
(`rel_taintC`); the call of `vg_aes_encrypt_blocks` or
`vg_aes_decrypt_blocks` between them has the same arguments in both runs
(`callBlocks_rel`). A pass keeps the public arguments, whatever the offsets
and the checksum (`pass_one`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Ocb (Block blockAtMem lAt)
open VG.Proof.Ocb (offAt)
open VG.Proof.AesCcm.X86_64 (runBlock_append)

/-- The checksums of a pass, from `c₀`. -/
def ckRec (c₀ : Block) (f : Nat → Block → Block) : Nat → Block
  | 0 => c₀
  | i + 1 => f i (ckRec c₀ f i)

/-- A pass keeps the public arguments, the table and the registers it does
not use. -/
theorem pass_one {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl n tl m : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hmn : 16 * m ≤ n) {body : List Instr}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} (hB : BodyOk body fB fC)
    {t : State} (o : One K W SP R N A D nl n tl t) (hD : DBuf K W SP t D (16 * m)) (hm0 : 0 < m)
    {l : Block} (hT : ∃ M, Tbl W l M t.mem ∧ m ≤ M)
    (hbx : t.gpr .rbx = D) (hbp : t.gpr .rbp = BitVec.ofNat 64 1) (h12 : t.gpr .r12 = BitVec.ofNat 64 m) :
    WP isa (pass body) t fun t' => One K W SP R N A D nl n tl t' ∧ (∃ M, Tbl W l M t'.mem ∧ m ≤ M) ∧
      ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → t'.gpr r = t.gpr r := by
  let O0 := blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)
  let X := fun k => blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k))
  let ckF := ckRec (blockAtMem t.mem (W + BitVec.ofNat 64 ckO)) fun i c => fC c (X i) (offAt O0 l (i + 1))
  refine WP.mono (pass_ok hB (ckF := ckF) (O0 := O0) (fun i _ => rfl) ⟨L, hD, hT⟩ o.env hm0 hbx hbp h12 rfl rfl)
    fun t' P => ⟨?_, ?_, P.gpr⟩
  · refine o.step L hDW P.env P.wr (P.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
    · exact ⟨_, by simp, Region.sub_prefix hmn⟩
  · obtain ⟨M, T, hM⟩ := hT
    exact ⟨M, T.frame P.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.wT_w (by decide)
      · exact L.wT_w (by decide)
      · exact hD.w.symm.sub_left (Lay.wSub (by decide)), hM⟩

/-- What the whole blocks need of a run, and what their first pass keeps:
the public arguments, the number of blocks in `r13`, the table and the
data. -/
def WRun (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl m : Nat) (s : State) : Prop :=
  One K W SP R N A D nl n tl s ∧ s.gpr .r13 = BitVec.ofNat 64 m ∧
    (∃ l M, Tbl W l M s.mem ∧ m ≤ M) ∧ DBuf K W SP s D n

/-- The first pass. -/
theorem wholeA_one {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl n tl m : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hmn : 16 * m ≤ n) (hm0 : 0 < m)
    {body : List Instr} {fB : Block → Block → Block} {fC : Block → Block → Block → Block}
    (hB : BodyOk body fB fC) {s : State} (h : WRun K W SP R N A D nl n tl m s) :
    WP isa (.seq (.block [ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)]) (pass body)) s
      (WRun K W SP R N A D nl n tl m) := by
  obtain ⟨o, h13, ⟨l, M, T, hM⟩, hD⟩ := h
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 208) 8 := o.env.perm.wR (by decide)
  have hdata := o.sl.data
  obtain ⟨s₁, run₁, rbx₁, r12₁, rbp₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)] s = some s₁ ∧
      s₁.gpr .rbx = D ∧ s₁.gpr .r12 = BitVec.ofNat 64 m ∧ s₁.gpr .rbp = BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .rbp → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by orun [o.env.r15, r₁, hdata], ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h13]
    · simp only [gpr_setReg, ite_true, sext1]
    · simp only [gpr_setReg, h1, h2, h3, ite_false]
    all_goals rfl
  have E₁ : Env K W SP s₁ := o.env.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₁ wr₁
  have o₁ : One K W SP R N A D nl n tl s₁ := ⟨E₁, by rw [m₁]; exact o.sl, by rw [wr₁]; exact o.wr⟩
  have hD₁ : DBuf K W SP s₁ D n := hD.of_eq rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (pass_one L hDW hmn hB o₁ (hD₁.take' hmn) hm0 (l := l) ⟨M, by rw [m₁]; exact T, hM⟩ rbx₁ rbp₁ r12₁)
    fun t ⟨o', hT', g'⟩ => ⟨o', ?_, ⟨l, hT'⟩, hD₁.of_one o'⟩
  rw [g' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    g₁ _ (by decide) (by decide) (by decide), h13]

/-- Both runs with the number of blocks in `r13`. -/
theorem both_r13 {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl m : Nat} {s₁ s₂ : State}
    (o₁ : One K W SP R N A D nl n tl s₁) (o₂ : One K W SP R N A D nl n tl s₂)
    (h₁ : s₁.gpr .r13 = BitVec.ofNat 64 m) (h₂ : s₂.gpr .r13 = BitVec.ofNat 64 m) :
    Both K W SP R N A D nl n tl [.r13] [] s₁ s₂ :=
  ⟨o₁.env, o₂.env, o₁.sl, o₂.sl, o₁.wr, o₂.wr, fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂], fun _ h => (nomatch h)⟩

/-- `whole f pre post` in two runs. -/
theorem whole_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86_64 f).pre (Proof.Aes.blocksX86_64 f).pub b.code)
    (nosp : NoSp b.code) (depth : b.code.depth = 0)
    {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D : Addr} {nl n tl m : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hn : n ≤ 2 ^ 64) (hmn : 16 * m ≤ n) (hm0 : 0 < m)
    {pre post : List Instr} {fB : Block → Block → Block} {fC : Block → Block → Block → Block}
    (hB : BodyOk pre fB fC)
    (hc₁ : ∃ hc, (taint.check (ocbT [.r13] [])
      (.seq (.block [ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)]) (pass pre)) hc).isSome = true)
    (hc₂ : ∃ hc, (taint.check (ocbT [.r13] [])
      (.seq (.block (copy16 o0O ofsO ++ [ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)])) (pass post)) hc).isSome
        = true)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → WRun K W SP R N A D nl n tl m s₁ ∧ WRun K W SP R N A D nl n tl m s₂) :
    RelCT isa P (whole b pre post) fun _ _ => True := by
  unfold whole
  have a := (rel_taintC [.r13] [] hDW hn (fun s₁ s₂ h => both_r13 (hP s₁ s₂ h).1.1 (hP s₁ s₂ h).2.1
    (hP s₁ s₂ h).1.2.1 (hP s₁ s₂ h).2.2.1) hc₁).wp
    (F₁ := WRun K W SP R N A D nl n tl m) (F₂ := WRun K W SP R N A D nl n tl m)
    fun s₁ s₂ h => ⟨wholeA_one L hDW hmn hm0 hB (hP s₁ s₂ h).1, wholeA_one L hDW hmn hm0 hB (hP s₁ s₂ h).2⟩
  have args : ∀ {s : State}, WRun K W SP R N A D nl n tl m s → ArgsOk [ld .rdx .r15 dataO, mvr .rcx .r13] s D m :=
    fun h => dataArgs_ok h.1.env.r15 h.1.sl.data h.2.1 (h.1.env.perm.wR (by decide))
  have call : ∀ s, WRun K W SP R N A D nl n tl m s →
      WP isa (callBlocks b [ld .rdx .r15 dataO, mvr .rcx .r13]) s fun s' =>
        One K W SP R N A D nl n tl s' ∧ s'.gpr .r13 = BitVec.ofNat 64 m := fun s h =>
    WP.mono (callBlocks_ok ok nosp depth L h.1.env hR h.1.sl.rounds (args h) (dstD (h.2.2.2.take' hmn)))
      fun s' Q => by
      refine ⟨h.1.step L hDW (h.1.env.of_saved Q.saved Q.rd Q.wr) Q.wr (Q.frame.sub fun r hr => ?_),
        by rw [Q.saved _ (by decide), h.2.1]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, Region.sub_prefix hmn⟩
      · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
      · rw [h.1.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩
  have bb := (callBlocks_rel ok ct L hR hDW hn [.r13] [] (args := [ld .rdx .r15 dataO, mvr .rcx .r13])
    ⟨_, by taint_decide⟩ (D' := D) (k := m)
    (P := fun s₁ s₂ => True ∧ WRun K W SP R N A D nl n tl m s₁ ∧ WRun K W SP R N A D nl n tl m s₂) fun s₁ s₂ h =>
      ⟨both_r13 h.2.1.1 h.2.2.1 h.2.1.2.1 h.2.2.2.1, args h.2.1, args h.2.2, dstD (h.2.1.2.2.2.take' hmn),
        dstD (h.2.2.2.2.2.take' hmn)⟩).wp
    (F₁ := fun (s : State) => One K W SP R N A D nl n tl s ∧ s.gpr .r13 = BitVec.ofNat 64 m)
    (F₂ := fun (s : State) => One K W SP R N A D nl n tl s ∧ s.gpr .r13 = BitVec.ofNat 64 m)
    fun s₁ s₂ h => ⟨call s₁ h.2.1, call s₂ h.2.2⟩
  have c := rel_taintC [.r13] [] hDW hn (fun s₁ s₂ (h : True ∧ (One K W SP R N A D nl n tl s₁ ∧
      s₁.gpr .r13 = BitVec.ofNat 64 m) ∧ (One K W SP R N A D nl n tl s₂ ∧ s₂.gpr .r13 = BitVec.ofNat 64 m)) =>
    both_r13 h.2.1.1 h.2.2.1 h.2.1.2 h.2.2.2) hc₂
  exact Proof.AesCcm.X86_64.rel_assoc (RelCT.seq a (RelCT.seq bb c))

end VG.Proof.AesOcb.X86_64

end

end

/-!
# AES-OCB on x86-64: the data is constant time

Untrusted: everything here is checked by Lean. The number of whole blocks
and the length of the rest come from the public slots, so the branches agree
in both runs (`rel_flagsC`); the whole blocks and the rest are related by
`whole_rel` and `rest_rel`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (eval_e)

/-- What `body` needs of a run: the public arguments, the data, the table of
`L_j`, and the offset equal to `Offset_0`. -/
def BRun (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (s : State) : Prop :=
  One K W SP R N A D nl n tl s ∧ DBuf K W SP s D n ∧ (∃ l, TblL W l n s.mem) ∧
    blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = blockAtMem s.mem (W + BitVec.ofNat 64 o0O)

/-- The whole blocks, if any, keep the public arguments. -/
theorem wholeIte_one {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp b.code) (depth : b.code.depth = 0) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block}
    (hB1 : BodyOk pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk post (fun b o => b ^^^ o) fC2)
    {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D : Addr} {nl n tl : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) {s : State} (h : BRun K W SP R N A D nl n tl s) :
    WP isa (.seq (.block [ld .r13 .r15 lenO, .shift .shr .r13 4, .alu .test .r13 (.reg .r13)])
        (.ite .e (.block []) (whole b pre post))) s (One K W SP R N A D nl n tl) := by
  obtain ⟨o, hD, ⟨l, hT⟩, ho⟩ := h
  let O0 := blockAtMem s.mem (W + BitVec.ofNat 64 ofsO)
  let ckF1 := ckRec (blockAtMem s.mem (W + BitVec.ofNat 64 ckO))
    fun i c => fC1 c (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1))
  let ckF2 := ckRec (ckF1 (n / 16)) fun i c => fC2 c
    (G (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
    (offAt O0 l (i + 1))
  refine WP.mono (wholeIte_ok (O0 := O0) (l := l) (ckF1 := ckF1) (ckF2 := ckF2) ok nosp depth hcall hB1 hB2 L o.env hR
    hD o.sl.data o.sl.len o.sl.rounds rfl ho.symm rfl hT (fun _ => rfl) rfl (fun _ => rfl)) fun t P =>
    o.step L hDW P.env P.wr (bodyR_mut (P.frame.sub (wholeR_sub (Nat.mul_div_le n 16))))

/-- `body`, for its whole blocks `whole b pre post` and its rest `rest enc`, in two runs. -/
theorem body_rel' (v : BlocksImpl) (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86_64 f).pre (Proof.Aes.blocksX86_64 f).pub b.code)
    (nosp : NoSp b.code) (depth : b.code.depth = 0) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block}
    (hB1 : BodyOk pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk post (fun b o => b ^^^ o) fC2)
    (hc₁ : ∃ hc, (taint.check (ocbT [.r13] [])
      (.seq (.block [ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)]) (pass pre)) hc).isSome = true)
    (hc₂ : ∃ hc, (taint.check (ocbT [.r13] [])
      (.seq (.block (copy16 o0O ofsO ++ [ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)])) (pass post)) hc).isSome
        = true)
    {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D : Addr} {nl n tl : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hn : n < 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → BRun K W SP R N A D nl n tl s₁ ∧ BRun K W SP R N A D nl n tl s₂) :
    RelCT isa P (.seq (.block [ld .r13 .r15 lenO, .shift .shr .r13 4, .alu .test .r13 (.reg .r13)])
      (.seq (.ite .e (.block []) (whole b pre post))
        (.seq (.block [ld .rbx .r15 dataO, ld .rax .r15 lenO, mvr .r12 .rax, .alu .and .r12 (.imm 15),
            .alu .sub .rax (.reg .r12), .alu .add .rbx (.reg .rax), .alu .test .r12 (.reg .r12)])
          (.ite .e (.block []) (rest (callees v) enc))))) fun _ _ => True := by
  have hn' : n ≤ 2 ^ 64 := Nat.le_of_lt hn
  let m := n / 16
  -- The number of whole blocks.
  have head : ∀ s, BRun K W SP R N A D nl n tl s →
      WP isa (.block [ld .r13 .r15 lenO, .shift .shr .r13 4, .alu .test .r13 (.reg .r13)]) s fun s₁ =>
        WRun K W SP R N A D nl n tl m s₁ ∧ s₁.zf = some (decide (m = 0)) := fun s ⟨o, hD, ⟨l, hT⟩, _⟩ => by
    obtain ⟨s₁, run₁, r13₁, zf₁, m₁, g₁, rd₁, wr₁⟩ := bodyHead_ok o.env hn o.sl.len
    have E₁ : Env K W SP s₁ := o.env.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
      rd₁ wr₁
    have o₁ : One K W SP R N A D nl n tl s₁ := ⟨E₁, by rw [m₁]; exact o.sl, by rw [wr₁]; exact o.wr⟩
    exact WP.of_runBlock ⟨s₁, run₁, ⟨o₁, r13₁, ⟨l, by rw [m₁]; exact hT⟩, hD.of_one o₁⟩, zf₁⟩
  have a := (rel_flagsC [] [] hDW hn' (fun s₁ s₂ h => Both.of (hP s₁ s₂ h).1.1 (hP s₁ s₂ h).2.1)
    (c := .block [ld .r13 .r15 lenO, .shift .shr .r13 4, .alu .test .r13 (.reg .r13)]) ⟨_, by taint_decide⟩).wp
    (F₁ := fun (s : State) => WRun K W SP R N A D nl n tl m s ∧ s.zf = some (decide (m = 0)))
    (F₂ := fun (s : State) => WRun K W SP R N A D nl n tl m s ∧ s.zf = some (decide (m = 0)))
    fun s₁ s₂ h => ⟨head s₁ (hP s₁ s₂ h).1, head s₂ (hP s₁ s₂ h).2⟩
  have i₁ := RelCT.ite (M := isa) (c := .e) (t := .block []) (e := whole b pre post) (Q := fun _ _ => True)
    (P := fun s₁ s₂ => (s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf) ∧
      (WRun K W SP R N A D nl n tl m s₁ ∧ s₁.zf = some (decide (m = 0))) ∧
      (WRun K W SP R N A D nl n tl m s₂ ∧ s₂.zf = some (decide (m = 0))))
    (fun s₁ s₂ h => Proof.AesCcm.X86_64.eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) (by
      by_cases hm : m = 0
      · refine RelCT.of_false fun s₁ s₂ h => ?_
        have := (eval_e h.1.2.1.2).symm.trans h.2
        simp [hm] at this
      · exact whole_rel ok ct nosp depth L hR hDW hn' (Nat.mul_div_le n 16) (Nat.pos_of_ne_zero hm) hB1
          hc₁ hc₂ fun s₁ s₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩)
  have x := (RelCT.seq a i₁).wp (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun s₁ s₂ h => ⟨wholeIte_one ok nosp depth hcall hB1 hB2 L hR hDW (hP s₁ s₂ h).1,
      wholeIte_one ok nosp depth hcall hB1 hB2 L hR hDW (hP s₁ s₂ h).2⟩
  -- The rest.
  let Pr := D + BitVec.ofNat 64 (16 * (n / 16))
  have tail : ∀ s, One K W SP R N A D nl n tl s →
      WP isa (.block [ld .rbx .r15 dataO, ld .rax .r15 lenO, mvr .r12 .rax, .alu .and .r12 (.imm 15),
          .alu .sub .rax (.reg .r12), .alu .add .rbx (.reg .rax), .alu .test .r12 (.reg .r12)]) s fun t =>
        RRun K W SP R N A D nl n tl Pr (n % 16) t ∧ t.zf = some (decide (n % 16 = 0)) := fun s o => by
    obtain ⟨t₁, run₁, rbx₁, r12₁, zf₁, m₁, g₁, rd₁, wr₁⟩ := bodyTail_ok o.env hn o.sl.data o.sl.len
    have E₁ : Env K W SP t₁ := o.env.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
      rd₁ wr₁
    exact WP.of_runBlock ⟨t₁, run₁, ⟨⟨E₁, by rw [m₁]; exact o.sl, by rw [wr₁]; exact o.wr⟩, rbx₁, r12₁⟩, zf₁⟩
  have y₁ := (rel_flagsC [] [] hDW hn' (fun s₁ s₂ (h : True ∧ One K W SP R N A D nl n tl s₁ ∧
      One K W SP R N A D nl n tl s₂) => Both.of h.2.1 h.2.2)
    (c := .block [ld .rbx .r15 dataO, ld .rax .r15 lenO, mvr .r12 .rax, .alu .and .r12 (.imm 15),
      .alu .sub .rax (.reg .r12), .alu .add .rbx (.reg .rax), .alu .test .r12 (.reg .r12)]) ⟨_, by taint_decide⟩).wp
    (F₁ := fun (t : State) => RRun K W SP R N A D nl n tl Pr (n % 16) t ∧ t.zf = some (decide (n % 16 = 0)))
    (F₂ := fun (t : State) => RRun K W SP R N A D nl n tl Pr (n % 16) t ∧ t.zf = some (decide (n % 16 = 0)))
    fun s₁ s₂ h => ⟨tail s₁ h.2.1, tail s₂ h.2.2⟩
  have i₂ := RelCT.ite (M := isa) (c := .e) (t := .block []) (e := rest (callees v) enc) (Q := fun _ _ => True)
    (P := fun s₁ s₂ => (s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf) ∧
      (RRun K W SP R N A D nl n tl Pr (n % 16) s₁ ∧ s₁.zf = some (decide (n % 16 = 0))) ∧
      (RRun K W SP R N A D nl n tl Pr (n % 16) s₂ ∧ s₂.zf = some (decide (n % 16 = 0))))
    (fun s₁ s₂ h => Proof.AesCcm.X86_64.eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) (by
      by_cases hr : n % 16 = 0
      · refine RelCT.of_false fun s₁ s₂ h => ?_
        have := (eval_e h.1.2.1.2).symm.trans h.2
        simp [hr] at this
      · exact rest_rel v enc L hR hDW hn' fun s₁ s₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩)
  exact Proof.AesCcm.X86_64.rel_assoc (RelCT.seq x (RelCT.seq y₁ i₂))

/-- `body` for `seal`, in two runs. -/
theorem bodySeal_rel (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hn : n < 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → BRun K W SP R N A D nl n tl s₁ ∧ BRun K W SP R N A D nl n tl s₂) :
    RelCT isa P (body (callees v) true) fun _ _ => True := by
  simp only [body, ↓reduceIte]
  exact body_rel' v true v.encOk v.encCt v.encNosp v.encDepth hcall_enc sealPre_ok xorOfs_ok ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩ L hR hDW hn hP

/-- `body` for `open`, in two runs. -/
theorem bodyOpen_rel (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hn : n < 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → BRun K W SP R N A D nl n tl s₁ ∧ BRun K W SP R N A D nl n tl s₂) :
    RelCT isa P (body (callees v) false) fun _ _ => True := by
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  exact body_rel' v false v.decOk v.decCt v.decNosp v.decDepth hcall_dec xorOfs_ok openPost_ok ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩ L hR hDW hn hP

end VG.Proof.AesOcb.X86_64

end

end

/-! ### `AesOcb.X86_64.HashCT`, which only this module used -/

section

/-!
# AES-OCB on x86-64: `HASH` is constant time

Untrusted: everything here is checked by Lean. Each chunk fills its buffer
and adds it to the sum by code that passes the taint analysis from the
public slots, the number of blocks left (at `W + alenO`) and the position
in the associated data (`rbx`, `rbp`); the call between has the same
arguments in both runs (`callBlocks_rel`), and so does the rest's. Both runs
are at the same chunk at each iteration (`chunk_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append eval_e eval_ne)

section
variable {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte} {s₀ : State}

/-- A run of `HASH` keeps the public arguments. -/
theorem HInv.one {N : Addr} {nl tl : Nat} (C : HCtx K W SP D n R ciph l A a s₀)
    (o : One K W SP R N A D nl n tl s₀) {t : State} {j : Nat} (H : HInv K W SP D n ciph l A a s₀ t j) :
    One K W SP R N A D nl n tl t :=
  ⟨H.env, Slots.of_mut C.lay C.dw (hashR_mut H.frame) o.sl, H.wr.trans o.wr⟩

theorem FillInv.one {N : Addr} {nl tl : Nat} (C : HCtx K W SP D n R ciph l A a s₀)
    (o : One K W SP R N A D nl n tl s₀) {t : State} {j c i : Nat} (F : FillInv K W SP D n ciph l A a s₀ j c t i) :
    One K W SP R N A D nl n tl t :=
  ⟨F.env, Slots.of_mut C.lay C.dw (hashR_mut F.frame) o.sl, F.wr.trans o.wr⟩

/-- The first block and the chunks, if any. -/
theorem hashHI_ok (v : BlocksImpl) (C : HCtx K W SP D n R ciph l A a s₀) (E : Env K W SP s₀)
    (haad : s₀.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length) :
    WP isa (.seq (.block (zero16 sumO ++ zero16 ohO ++
      [ld .rbx .r15 aadO, ld .rax .r15 alenO, mvr .rcx .rax, .alu .and .rcx (.imm 15),
       st .r15 tmpO .rcx, .shift .shr .rax 4, st .r15 alenO .rax, .mov .rbp (.imm 1),
       .alu .test .rax (.reg .rax)])) (.ite .e (.block []) (.loop (hashChunk (callees v)) .ne))) s₀
      fun t => HInv K W SP D n ciph l A a s₀ t (a.length / 16) := by
  refine WP.seq (WP.mono (hashHead_ok C E haad halen) fun s₃ ⟨H₀, zf₃⟩ => ?_)
  refine WP.ite (decide (a.length / 16 = 0)) (eval_e zf₃) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · exact (of_decide_eq_true hb) ▸ H₀
  · exact hashLoop_ok v C H₀ (Nat.pos_of_ne_zero (of_decide_eq_false hb))

/-- The length of the rest. -/
theorem tailHead_ok {t : State} (H : HInv K W SP D n ciph l A a s₀ t (a.length / 16)) :
    WP isa (.block [ld .r12 .r15 tmpO, .alu .test .r12 (.reg .r12)]) t fun t₁ =>
      HInv K W SP D n ciph l A a s₀ t₁ (a.length / 16) ∧ t₁.gpr .r12 = BitVec.ofNat 64 (a.length % 16) ∧
        t₁.zf = some (decide (a.length % 16 = 0)) := by
  have r₁ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 112) 8 := H.env.perm.wR (by decide)
  have rest := H.rest
  simp only [tmpO] at rest
  obtain ⟨t₁, run₁, r12₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [ld .r12 .r15 tmpO, .alu .test .r12 (.reg .r12)] t =
      some t₁ ∧ t₁.gpr .r12 = BitVec.ofNat 64 (a.length % 16) ∧ t₁.zf = some (decide (a.length % 16 = 0)) ∧
      (∀ r, r ≠ .r12 → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by orun [H.env.r15, r₁, rest], ?_, ?_, fun r h => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true]
    · simp only [zf_arithFlags, gpr_setReg, ite_true,
        Proof.AesCcm.X86_64.and_self_beq (show a.length % 16 < 2 ^ 64 by omega_arith)]
    · simp only [gpr_setReg, gpr_arithFlags, h, ite_false]
    all_goals rfl
  exact WP.of_runBlock ⟨t₁, run₁,
    { H with
      env := H.env.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₁ wr₁
      frame := by rw [m₁]; exact H.frame
      rd := by rw [rd₁, H.rd]
      wr := by rw [wr₁, H.wr]
      sum := by rw [m₁, H.sum]
      oh := by rw [m₁, H.oh]
      rbx := by rw [g₁ _ (by decide), H.rbx]
      rbp := by rw [g₁ _ (by decide), H.rbp]
      alen := by rw [m₁, H.alen]
      rest := by rw [m₁, H.rest] }, r12₁, zf₁⟩

/-- The rest of the associated data, before its call, keeps the public arguments. -/
theorem hashRestPre_one {N : Addr} {nl tl : Nat} (C : HCtx K W SP D n R ciph l A a s₀)
    (o : One K W SP R N A D nl n tl s₀) {t : State} (H : HInv K W SP D n ciph l A a s₀ t (a.length / 16))
    (hr : 0 < a.length % 16) (h12 : t.gpr .r12 = BitVec.ofNat 64 (a.length % 16)) :
    WP isa (.seq (.block (xor16 .r14 240 ohO)) (.seq (padTo bufO) (.block (xor16 .r15 ohO bufO)))) t
      (One K W SP R N A D nl n tl) := by
  have L := C.lay
  have E := H.env
  have hs := C.short
  have o₀ := H.one C o
  generalize hm : a.length / 16 = m at H
  obtain ⟨t₁, run₁, B₁⟩ := xor16_ok (s := t) (b := .r14) (a := 240) (d := ohO) E.r15 E.r14 (by decide) (by decide)
    (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => B₁.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    B₁.rd B₁.wr
  have hB := C.buf.slice (a := 16 * m) (k := a.length % 16) (by omega_arith)
  have hS : Covers [⟨A + BitVec.ofNat 64 (16 * m), a.length % 16⟩] (t₁.rd ++ t₁.wr) := by
    rw [B₁.rd, B₁.wr, H.rd, H.wr]; exact hB.rd
  have hSD : (⟨A + BitVec.ofNat 64 (16 * m), a.length % 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 bufO, 16⟩ :=
    hB.w.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (padTo_ok E₁ hr (by omega_arith) (by decide) (by rw [B₁.gpr _ (by decide), H.rbx])
    (by rw [B₁.gpr _ (by decide), h12]) hS hSD) fun t₂ ⟨fr₂, _, g₂, rd₂, wr₂⟩ => ?_)
  have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => g₂ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₂ wr₂
  obtain ⟨t₃, run₃, B₃⟩ := xor16_ok (s := t₂) (b := .r15) (a := ohO) (d := bufO) E₂.r15 E₂.r15 (by decide) (by decide)
    (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide)) (E₂.perm.wW (by decide)) (E₂.perm.wW (by decide))
  have E₃ : Env K W SP t₃ := E₂.keep (fun r hr => B₃.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    B₃.rd B₃.wr
  refine WP.of_runBlock ⟨t₃, run₃, o₀.step L C.dw E₃ (by rw [B₃.wr, wr₂, B₁.wr])
    (((B₁.frame.sub fun r hr => ?_).trans (fr₂.sub fun r hr => ?_)).trans (B₃.frame.sub fun r hr => ?_))⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
  all_goals simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩

end

/-- One chunk, at the same position in both runs. -/
theorem chunk_rel (v : BlocksImpl) {K W SP D : Addr} {n R : Nat} {ciph₁ ciph₂ : Cipher} {l₁ l₂ : Block} {A : Addr}
    {a₁ a₂ : List Byte} {s₀₁ s₀₂ : State} {N : Addr} {nl tl : Nat}
    (C₁ : HCtx K W SP D n R ciph₁ l₁ A a₁ s₀₁) (C₂ : HCtx K W SP D n R ciph₂ l₂ A a₂ s₀₂)
    (o₁ : One K W SP R N A D nl n tl s₀₁) (o₂ : One K W SP R N A D nl n tl s₀₂) (hal : a₂.length = a₁.length)
    (hn : n ≤ 2 ^ 64) (k j : Nat) :
    RelCT isa (fun s₁ s₂ => k = a₁.length / 16 - j ∧ j < a₁.length / 16 ∧
        HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ j ∧ HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ j)
      (hashChunk (callees v)) fun s₁ s₂ => isa.eval .ne s₁ = isa.eval .ne s₂ ∧
        (isa.eval .ne s₁ = some false → HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ (a₁.length / 16) ∧
          HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ (a₂.length / 16)) ∧
        (isa.eval .ne s₁ = some true → ∃ m < k, ∃ j', m = a₁.length / 16 - j' ∧ j' < a₁.length / 16 ∧
          HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ j' ∧ HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ j') := by
  have L := C₁.lay
  have hDW := C₁.dw
  have hM : a₂.length / 16 = a₁.length / 16 := by rw [hal]
  obtain ⟨M, hMd⟩ : ∃ M, M = a₁.length / 16 := ⟨_, rfl⟩
  obtain ⟨c, hcd⟩ : ∃ c, c = min 8 (M - j) := ⟨_, rfl⟩
  rw [← hMd]
  rw [← hMd] at hM
  by_cases hkj : k = M - j ∧ j < M
  swap
  · exact RelCT.of_false fun s₁ s₂ h => hkj ⟨h.1, h.2.1⟩
  obtain ⟨hk, hjM⟩ := hkj
  have pre : ∀ {ciph : Cipher} {l : Block} {a : List Byte} {s₀ s : State}, HCtx K W SP D n R ciph l A a s₀ →
      a.length / 16 = M → j < M → HInv K W SP D n ciph l A a s₀ s j →
      WP isa (.seq (.block [ld .r12 .r15 alenO, .alu .cmp .r12 (.imm 8)])
        (.seq (.ite .b (.block []) (.block [.mov .r12 (.imm 8)])) (.seq (.block bufStart) (.loop hashFill .ne)))) s
        (FillInv K W SP D n ciph l A a s₀ j c · c) := fun {ciph l a s₀ s} C hm hj H => by
    have hc : min 8 (a.length / 16 - j) = c := by rw [hm, hcd]
    refine wp_seq_assoc (WP.seq (WP.mono (chunkHead_ok C H (by omega_arith)) fun t ⟨H', h12⟩ => ?_))
    rw [hc] at h12
    exact chunkFill_ok C H' (by omega_arith) (by omega_arith) (by omega_arith) h12
  have bX : ∀ s₁ s₂, (k = M - j ∧ j < M ∧ HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ j ∧
      HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ j) → Both K W SP R N A D nl n tl [.rbx, .rbp] [248] s₁ s₂ :=
    fun s₁ s₂ ⟨_, _, H₁, H₂⟩ => by
      have O₁ := H₁.one C₁ o₁
      have O₂ := H₂.one C₂ o₂
      refine ⟨O₁.env, O₂.env, O₁.sl, O₂.sl, O₁.wr, O₂.wr, fun x hx => ?_, fun d hd => ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · rw [H₁.rbx, H₂.rbx]
        · rw [H₁.rbp, H₂.rbp]
      · simp only [List.mem_singleton] at hd; subst hd
        exact ⟨by decide, by rw [show (248 : Nat) = alenO from rfl, H₁.alen, H₂.alen, hM, hMd]⟩
  have X := (rel_taintC [.rbx, .rbp] [248] hDW hn bX
    (c := .seq (.block [ld .r12 .r15 alenO, .alu .cmp .r12 (.imm 8)])
      (.seq (.ite .b (.block []) (.block [.mov .r12 (.imm 8)])) (.seq (.block bufStart) (.loop hashFill .ne))))
    ⟨_, by taint_decide⟩).wp
    (F₁ := (FillInv K W SP D n ciph₁ l₁ A a₁ s₀₁ j c · c)) (F₂ := (FillInv K W SP D n ciph₂ l₂ A a₂ s₀₂ j c · c))
    fun s₁ s₂ ⟨_, hj, H₁, H₂⟩ => ⟨pre C₁ hMd.symm hj H₁, pre C₂ hM hj H₂⟩
  have hc8 : c ≤ 8 := by omega_arith
  have call : ∀ {ciph : Cipher} {l : Block} {a : List Byte} {s₀ s : State}, HCtx K W SP D n R ciph l A a s₀ →
      One K W SP R N A D nl n tl s₀ → FillInv K W SP D n ciph l A a s₀ j c s c →
      WP isa (callBlocks (callees v).enc [mvr .rdx .r15, addi .rdx bufO, mvr .rcx .r12]) s fun s' =>
        One K W SP R N A D nl n tl s' ∧ s'.gpr .r12 = BitVec.ofNat 64 c := fun {ciph l a s₀ s} C o F => by
    have O := F.one C o
    exact WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encDepth L O.env C.rounds O.sl.rounds
      (bufArgs_ok F.env.r15 F.r12) (dstW L F.env.perm (d := 384) (n := c) (by omega_arith))) fun s' Q => by
      refine ⟨O.step L hDW (O.env.of_saved Q.saved Q.rd Q.wr) Q.wr (Q.frame.sub fun r hr => ?_),
        by rw [Q.saved _ (by decide), F.r12]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, sub_wC (by decide) (by omega_arith)⟩
      · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
      · rw [O.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩
  have B := (callBlocks_rel (b := (callees v).enc) v.encOk v.encCt L C₁.rounds hDW hn [] []
    (args := [mvr .rdx .r15, addi .rdx bufO, mvr .rcx .r12]) ⟨_, by taint_decide⟩
    (D' := W + BitVec.ofNat 64 384) (k := c)
    (P := fun s₁ s₂ => True ∧ FillInv K W SP D n ciph₁ l₁ A a₁ s₀₁ j c s₁ c ∧
      FillInv K W SP D n ciph₂ l₂ A a₂ s₀₂ j c s₂ c) fun s₁ s₂ h =>
      ⟨Both.of (h.2.1.one C₁ o₁) (h.2.2.one C₂ o₂), bufArgs_ok h.2.1.env.r15 h.2.1.r12,
        bufArgs_ok h.2.2.env.r15 h.2.2.r12, dstW L h.2.1.env.perm (d := 384) (n := c) (by omega_arith),
        dstW L h.2.2.env.perm (d := 384) (n := c) (by omega_arith)⟩).wp
    (F₁ := fun (s : State) => One K W SP R N A D nl n tl s ∧ s.gpr .r12 = BitVec.ofNat 64 c)
    (F₂ := fun (s : State) => One K W SP R N A D nl n tl s ∧ s.gpr .r12 = BitVec.ofNat 64 c)
    fun s₁ s₂ h => ⟨call C₁ o₁ h.2.1, call C₂ o₂ h.2.2⟩
  have Y := rel_taintC [.r12] [] hDW hn (fun s₁ s₂ (h : True ∧ (One K W SP R N A D nl n tl s₁ ∧
      s₁.gpr .r12 = BitVec.ofNat 64 c) ∧ (One K W SP R N A D nl n tl s₂ ∧ s₂.gpr .r12 = BitVec.ofNat 64 c)) =>
    (⟨h.2.1.1.env, h.2.2.1.env, h.2.1.1.sl, h.2.2.1.sl, h.2.1.1.wr, h.2.2.1.wr, fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; rw [h.2.1.2, h.2.2.2], fun _ h => (nomatch h)⟩ :
      Both K W SP R N A D nl n tl [.r12] [] s₁ s₂))
    (c := .seq hashSum (.block [ld .rax .r15 alenO, .alu .sub .rax (.reg .r12), st .r15 alenO .rax]))
    ⟨_, by taint_decide⟩
  have T : RelCT isa (fun s₁ s₂ => k = M - j ∧ j < M ∧ HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ j ∧
      HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ j) (hashChunk (callees v)) fun _ _ => True := by
    unfold hashChunk; exact Proof.AesCcm.X86_64.rel_assoc4 (RelCT.seq X (RelCT.seq B Y))
  refine (T.wp (F₁ := fun (t : State) => HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ t (j + c) ∧
      t.zf = some (decide (M - (j + c) = 0)))
    (F₂ := fun (t : State) => HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ t (j + c) ∧ t.zf = some (decide (M - (j + c) = 0)))
    fun s₁ s₂ ⟨_, hj, H₁, H₂⟩ => ⟨?_, ?_⟩).mono (fun _ _ h => h) fun s₁ s₂ ⟨_, ⟨H₁, z₁⟩, ⟨H₂, z₂⟩⟩ => ?_
  · have := hashChunk_ok v C₁ H₁ (by omega_arith)
    rw [← hMd, ← hcd] at this
    exact this
  · have := hashChunk_ok v C₂ H₂ (by omega_arith)
    rw [hM, ← hcd] at this
    exact this
  · rw [eval_ne z₁, eval_ne z₂]
    refine ⟨rfl, fun h => ?_, fun h => ?_⟩
    · have he : j + c = M := by simp at h; omega_arith
      rw [hM, ← he]; exact ⟨H₁, H₂⟩
    · have he : ¬ M - (j + c) = 0 := by simpa using h
      exact ⟨M - (j + c), by omega_arith, j + c, rfl, by omega_arith, H₁, H₂⟩

/-- The call on the block at `W + bufO` keeps the public arguments. -/
theorem callBuf_one (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) {s : State}
    (o : One K W SP R N A D nl n tl s) :
    WP isa (callBlocks (callees v).enc (oneBlock bufO)) s (One K W SP R N A D nl n tl) :=
  WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encDepth L o.env hR o.sl.rounds
    (oneBlock_ok o.env.r15 bufO (by decide)) (dstW L o.env.perm (d := bufO) (n := 1) (by decide))) fun s' Q => by
    refine o.step L hDW (o.env.of_saved Q.saved Q.rd Q.wr) Q.wr (Q.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
    · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
    · rw [o.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩

/-- `HASH` in two runs, from the starts `s₀₁` and `s₀₂` of the same length of associated data. -/
theorem hash_rel (v : BlocksImpl) {K W SP D : Addr} {n R : Nat} {ciph₁ ciph₂ : Cipher} {l₁ l₂ : Block} {A : Addr}
    {a₁ a₂ : List Byte} {s₀₁ s₀₂ : State} {N : Addr} {nl tl : Nat}
    (C₁ : HCtx K W SP D n R ciph₁ l₁ A a₁ s₀₁) (C₂ : HCtx K W SP D n R ciph₂ l₂ A a₂ s₀₂)
    (o₁ : One K W SP R N A D nl n tl s₀₁) (o₂ : One K W SP R N A D nl n tl s₀₂) (hal : a₂.length = a₁.length)
    (hn : n ≤ 2 ^ 64)
    (halen₁ : s₀₁.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a₁.length)
    (halen₂ : s₀₂.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a₂.length) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀₁ ∧ s₂ = s₀₂) (Impl.AesOcb.X86_64.hash (callees v)) fun _ _ => True := by
  have L := C₁.lay
  have hDW := C₁.dw
  have hM : a₂.length / 16 = a₁.length / 16 := by rw [hal]
  have hr : a₂.length % 16 = a₁.length % 16 := by rw [hal]
  have haad₁ := o₁.sl.aad
  have haad₂ := o₂.sl.aad
  -- The first block.
  have a := (rel_flagsC [] [248] hDW hn (fun s₁ s₂ (h : s₁ = s₀₁ ∧ s₂ = s₀₂) => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨o₁.env, o₂.env, o₁.sl, o₂.sl, o₁.wr, o₂.wr, fun _ h => (nomatch h), fun d hd => by
        simp only [List.mem_singleton] at hd; subst hd
        exact ⟨by decide, by rw [show (248 : Nat) = alenO from rfl, halen₁, halen₂, hal]⟩⟩)
    (c := .block (zero16 sumO ++ zero16 ohO ++
      [ld .rbx .r15 aadO, ld .rax .r15 alenO, mvr .rcx .rax, .alu .and .rcx (.imm 15),
       st .r15 tmpO .rcx, .shift .shr .rax 4, st .r15 alenO .rax, .mov .rbp (.imm 1),
       .alu .test .rax (.reg .rax)])) ⟨_, by taint_decide⟩).wp
    (F₁ := fun (s : State) => HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s 0 ∧ s.zf = some (decide (a₁.length / 16 = 0)))
    (F₂ := fun (s : State) => HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s 0 ∧ s.zf = some (decide (a₂.length / 16 = 0)))
    fun s₁ s₂ h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hashHead_ok C₁ o₁.env haad₁ halen₁, hashHead_ok C₂ o₂.env haad₂ halen₂⟩
  -- The chunks.
  have lp : RelCT isa (fun s₁ s₂ => ∃ j, a₁.length / 16 - 0 = a₁.length / 16 - j ∧ j < a₁.length / 16 ∧
      HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ j ∧ HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ j)
      (.loop (hashChunk (callees v)) .ne) fun _ _ => True :=
    (RelCT.loop (Q := fun s₁ s₂ => HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ (a₁.length / 16) ∧
        HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ (a₂.length / 16))
      (fun k s₁ s₂ => ∃ j, k = a₁.length / 16 - j ∧ j < a₁.length / 16 ∧
        HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ j ∧ HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ j)
      (fun k => RelCT.exists_ fun j => chunk_rel v C₁ C₂ o₁ o₂ hal hn k j) _).mono (fun _ _ h => h)
      fun _ _ _ => trivial
  have i₁ := RelCT.ite (M := isa) (c := .e) (t := .block []) (e := .loop (hashChunk (callees v)) .ne)
    (Q := fun _ _ => True)
    (P := fun s₁ s₂ => (s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf) ∧
      (HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ 0 ∧ s₁.zf = some (decide (a₁.length / 16 = 0))) ∧
      (HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ 0 ∧ s₂.zf = some (decide (a₂.length / 16 = 0))))
    (fun s₁ s₂ h => Proof.AesCcm.X86_64.eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) (by
      by_cases h0 : a₁.length / 16 = 0
      · refine RelCT.of_false fun s₁ s₂ h => ?_
        have := (eval_e h.1.2.1.2).symm.trans h.2
        simp [h0] at this
      · exact lp.mono (fun s₁ s₂ h => ⟨0, rfl, Nat.pos_of_ne_zero h0, h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h)
  have X := (RelCT.seq a i₁).wp
    (F₁ := fun s => HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s (a₁.length / 16))
    (F₂ := fun s => HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s (a₂.length / 16)) fun s₁ s₂ h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hashHI_ok v C₁ o₁.env haad₁ halen₁, hashHI_ok v C₂ o₂.env haad₂ halen₂⟩
  -- The rest.
  have t₁ := (rel_flagsC [] [112] hDW hn (fun s₁ s₂ (h : True ∧ HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ (a₁.length / 16) ∧
      HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ (a₂.length / 16)) => by
      have O₁ := h.2.1.one C₁ o₁
      have O₂ := h.2.2.one C₂ o₂
      exact ⟨O₁.env, O₂.env, O₁.sl, O₂.sl, O₁.wr, O₂.wr, fun _ h => (nomatch h), fun d hd => by
        simp only [List.mem_singleton] at hd; subst hd
        exact ⟨by decide, by rw [show (112 : Nat) = tmpO from rfl, h.2.1.rest, h.2.2.rest, hr]⟩⟩)
    (c := .block [ld .r12 .r15 tmpO, .alu .test .r12 (.reg .r12)]) ⟨_, by taint_decide⟩).wp
    (F₁ := fun (t : State) => HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ t (a₁.length / 16) ∧
      t.gpr .r12 = BitVec.ofNat 64 (a₁.length % 16) ∧ t.zf = some (decide (a₁.length % 16 = 0)))
    (F₂ := fun (t : State) => HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ t (a₂.length / 16) ∧
      t.gpr .r12 = BitVec.ofNat 64 (a₂.length % 16) ∧ t.zf = some (decide (a₂.length % 16 = 0)))
    fun s₁ s₂ h => ⟨tailHead_ok h.2.1, tailHead_ok h.2.2⟩
  have rr : (0 < a₁.length % 16) → RelCT isa (fun s₁ s₂ =>
      (HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ (a₁.length / 16) ∧ s₁.gpr .r12 = BitVec.ofNat 64 (a₁.length % 16)) ∧
      (HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ (a₂.length / 16) ∧ s₂.gpr .r12 = BitVec.ofNat 64 (a₂.length % 16)))
      (hashRest (callees v)) fun _ _ => True := fun hr0 => by
    have p := (rel_taintC [.rbx, .r12] [] hDW hn (fun s₁ s₂ (h :
        (HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ (a₁.length / 16) ∧ s₁.gpr .r12 = BitVec.ofNat 64 (a₁.length % 16)) ∧
        (HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ (a₂.length / 16) ∧ s₂.gpr .r12 = BitVec.ofNat 64 (a₂.length % 16))) =>
      (⟨(h.1.1.one C₁ o₁).env, (h.2.1.one C₂ o₂).env,
        (h.1.1.one C₁ o₁).sl, (h.2.1.one C₂ o₂).sl, (h.1.1.one C₁ o₁).wr, (h.2.1.one C₂ o₂).wr, fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · rw [h.1.1.rbx, h.2.1.rbx, hM]
          · rw [h.1.2, h.2.2, hr], fun _ h => (nomatch h)⟩ : Both K W SP R N A D nl n tl [.rbx, .r12] [] s₁ s₂))
      (c := .seq (.block (xor16 .r14 240 ohO)) (.seq (padTo bufO) (.block (xor16 .r15 ohO bufO))))
      ⟨_, by taint_decide⟩).wp (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
      fun s₁ s₂ h => ⟨hashRestPre_one C₁ o₁ h.1.1 hr0 h.1.2, hashRestPre_one C₂ o₂ h.2.1 (by omega_arith) h.2.2⟩
    have c := (callBlocks_rel (b := (callees v).enc) v.encOk v.encCt L C₁.rounds hDW hn [] [] (args := oneBlock bufO)
      ⟨_, by taint_decide⟩ (D' := W + BitVec.ofNat 64 bufO) (k := 1)
      (P := fun s₁ s₂ => True ∧ One K W SP R N A D nl n tl s₁ ∧ One K W SP R N A D nl n tl s₂) fun s₁ s₂ h =>
        ⟨Both.of h.2.1 h.2.2, oneBlock_ok h.2.1.env.r15 bufO (by decide), oneBlock_ok h.2.2.env.r15 bufO (by decide),
          dstW L h.2.1.env.perm (by decide), dstW L h.2.2.env.perm (by decide)⟩).wp
      (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
      fun s₁ s₂ h => ⟨callBuf_one v L C₁.rounds hDW h.2.1, callBuf_one v L C₁.rounds hDW h.2.2⟩
    have e := rel_taintC [] [] hDW hn (fun s₁ s₂ (h : True ∧ One K W SP R N A D nl n tl s₁ ∧
      One K W SP R N A D nl n tl s₂) => Both.of h.2.1 h.2.2) (c := .block (xor16 .r15 bufO sumO)) ⟨_, by taint_decide⟩
    unfold hashRest
    exact Proof.AesCcm.X86_64.rel_assoc3 (RelCT.seq p (RelCT.seq c e))
  have i₂ := RelCT.ite (M := isa) (c := .e) (t := .block []) (e := hashRest (callees v)) (Q := fun _ _ => True)
    (P := fun s₁ s₂ => (s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf) ∧
      (HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ (a₁.length / 16) ∧ s₁.gpr .r12 = BitVec.ofNat 64 (a₁.length % 16) ∧
        s₁.zf = some (decide (a₁.length % 16 = 0))) ∧
      (HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ (a₂.length / 16) ∧ s₂.gpr .r12 = BitVec.ofNat 64 (a₂.length % 16) ∧
        s₂.zf = some (decide (a₂.length % 16 = 0))))
    (fun s₁ s₂ h => Proof.AesCcm.X86_64.eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) (by
      by_cases h0 : a₁.length % 16 = 0
      · refine RelCT.of_false fun s₁ s₂ h => ?_
        have := (eval_e h.1.2.1.2.2).symm.trans h.2
        simp [h0] at this
      · exact (rr (Nat.pos_of_ne_zero h0)).mono (fun s₁ s₂ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.1⟩, ⟨h.1.2.2.1, h.1.2.2.2.1⟩⟩)
          fun _ _ h => h)
  unfold Impl.AesOcb.X86_64.hash
  exact Proof.AesCcm.X86_64.rel_assoc (RelCT.seq X (RelCT.seq t₁ i₂))

end VG.Proof.AesOcb.X86_64

end

end

/-! ### `AesOcb.X86_64.NonceCT`, which only this module used -/

section

/-!
# AES-OCB on x86-64: `Offset_0` is constant time

Untrusted: everything here is checked by Lean. The nonce block and the
stretch pass the taint analysis from the public slots (`rel_taintC`); the
call of `vg_aes_encrypt_blocks` has the same arguments in both runs
(`callBlocks_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem nonce_rel (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hn : n ≤ 2 ^ 64)
    (h1 : 1 ≤ nl) (h15 : nl ≤ 15) (ht : tl < 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → One K W SP R N A D nl n tl s₁ ∧ One K W SP R N A D nl n tl s₂ ∧
      Buf W SP s₁ N nl ∧ Buf W SP s₂ N nl) :
    RelCT isa P (nonce (callees v)) fun _ _ => True := by
  have step : ∀ s, One K W SP R N A D nl n tl s → Buf W SP s N nl →
      WP isa nonceBlock s (One K W SP R N A D nl n tl) := fun s o hB =>
    WP.mono (nonceBlock_ok L o.env o.sl.nonce o.sl.nlen o.sl.tl h1 h15 ht hB) fun s' Q =>
      o.step L hDW (o.env.keep (fun r hr => Q.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
        (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
        (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
        Q.rd Q.wr) Q.wr (Q.frame.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
          · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_wB (by decide) (by decide)⟩)
  have a := (rel_taintC [] [] hDW hn (fun s₁ s₂ h => Both.of (hP s₁ s₂ h).1 (hP s₁ s₂ h).2.1)
    (c := nonceBlock) ⟨_, by taint_decide⟩).wp (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun s₁ s₂ h => ⟨step s₁ (hP s₁ s₂ h).1 (hP s₁ s₂ h).2.2.1, step s₂ (hP s₁ s₂ h).2.1 (hP s₁ s₂ h).2.2.2⟩
  have call : ∀ s, One K W SP R N A D nl n tl s →
      WP isa (callBlocks (callees v).enc (oneBlock tmpO)) s (One K W SP R N A D nl n tl) := fun s o =>
    WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encDepth L o.env hR o.sl.rounds
      (oneBlock_ok o.env.r15 tmpO (by decide)) (dstW L o.env.perm (d := tmpO) (n := 1) (by decide))) fun s' Q => by
      have E' := o.env.of_saved Q.saved Q.rd Q.wr
      refine o.step L hDW E' Q.wr (Q.frame.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
      · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
      · rw [o.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩
  have b := (callBlocks_rel (b := (callees v).enc) v.encOk v.encCt L hR hDW hn [] [] (args := oneBlock tmpO) ⟨_, by taint_decide⟩
    (D' := W + BitVec.ofNat 64 tmpO) (k := 1)
    (P := fun s₁ s₂ => True ∧ One K W SP R N A D nl n tl s₁ ∧ One K W SP R N A D nl n tl s₂) fun s₁ s₂ h =>
      ⟨Both.of h.2.1 h.2.2, oneBlock_ok h.2.1.env.r15 tmpO (by decide), oneBlock_ok h.2.2.env.r15 tmpO (by decide),
        dstW L h.2.1.env.perm (by decide), dstW L h.2.2.env.perm (by decide)⟩).wp
    (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun s₁ s₂ h => ⟨call s₁ h.2.1, call s₂ h.2.2⟩
  have c := rel_taintC [] [] hDW hn (fun s₁ s₂ (h : True ∧ One K W SP R N A D nl n tl s₁ ∧ One K W SP R N A D nl n tl s₂) =>
    Both.of h.2.1 h.2.2) (c := .block offset0) ⟨_, by taint_decide⟩
  exact RelCT.seq a (RelCT.seq b c)

end VG.Proof.AesOcb.X86_64

end

end

/-!
# AES-OCB on x86-64: `vg_aes_ocb_seal` is constant time

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments are related piece by piece: the entry by the taint analysis from
the public registers, once the first instruction has loaded `W` (`entry_rel`),
then the table of `L_j` by the taint analysis from the public slots and the
length of the associated data, then `Offset_0`, `HASH`, the data and the tag
(`nonce_rel`, `hash_rel`, `bodySeal_rel`, `tag_rel`; `front_rel`), each run
satisfying what correctness says between them (`RelCT.wp`).

The taint analysis knows `W` as the second writable region, as it is for
`open`; `seal` may write `tag` too, before `W`, but its `front` does not, and
runs the same from its states with `tag` only readable (`rel_narrow`). The
copy of the tag and `restore` are related by the taint analysis from the
registers that correctness says agree (`sealTail_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append length_bytesAt bytesAt_frame in_off add_ofNat_assoc)

/-- A run after `entry` and `table`: what `Offset_0` needs, and the table. -/
structure TRun (K W SP N A D : Addr) (R nl al n tl : Nat) (s₀ s : State) : Prop where
  env : Env K W SP s
  slots : Slots W R N A D nl n tl s.mem
  alen : s.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 al
  tbl : Tbl W (ctxLstar s₀.mem K) ((n ||| al) / 16) s.mem
  frame : Frame (entryR W :: mutR W SP D n) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The table, after `entry`. -/
theorem table_trun {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Ar : Args s K W SP N A D R nl al n tl T) {s₁ : State} (P₁ : EntryPost K W SP R N A D nl al n tl T s s₁) :
    WP isa table s₁ (TRun K W SP N A D R nl al n tl s) := by
  have L : Lay _ _ _ := Ar.lay
  refine WP.mono (table_ok P₁.env Ar.data.lt Ar.aad.lt P₁.slots.len P₁.alen P₁.l0) fun s₂ Q => ?_
  exact
    { env := Q.env
      slots := Slots.of_mut L Ar.data.w (wT_mut Q.frame) P₁.slots
      alen := by
        rw [Q.frame.readW (r := ⟨W + BitVec.ofNat 64 alenO, 8⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact (L.wT_w (by decide)).symm) (by decide), P₁.alen]
      tbl := Q.tbl
      frame := (P₁.frame.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩).trans
        ((wT_mut Q.frame).sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
      rd := Q.rd.trans P₁.rd
      wr := Q.wr.trans P₁.wr }

/-- A run after `Offset_0`: what `HASH` needs. -/
structure NRun (K W SP N A D : Addr) (R nl al n tl : Nat) (s₀ s : State) : Prop where
  C : HCtx K W SP D n R (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) A (bytesAt s₀.mem A al) s
  one : One K W SP R N A D nl n tl s
  alen : s.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 (bytesAt s₀.mem A al).length

/-- `Offset_0`, after `entry` and `table`. -/
theorem nonce_nrun (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Ar : Args s K W SP N A D R nl al n tl T) (hw : s.wr = [⟨D, n⟩, ⟨W, 3584⟩]) {s₁ : State}
    (P₁ : TRun K W SP N A D R nl al n tl s s₁) :
    WP isa (nonce (callees v)) s₁ (NRun K W SP N A D R nl al n tl s) := by
  have L : Lay _ _ _ := Ar.lay
  have hRb : 16 * (R + 1) ≤ 256 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  have dK : ∀ r ∈ entryR W :: mutR W SP D n, (⟨K, 256⟩ : Region).Disjoint r := fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact k_mut L Ar.data.k r hr
  have eK : ctxCiph s₁.mem K R = ctxCiph s.mem K R := by
    unfold ctxCiph
    rw [bytesAt_frame P₁.frame (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega_using [hRb])]
  have eL : ctxLstar s₁.mem K = ctxLstar s.mem K :=
    blockAtMem_frame P₁.frame fun r hr => (dK r hr).sub_left (Lay.kSub (by decide))
  have eB : ∀ {P : Addr} {k : Nat}, Buf W SP s P k → (⟨P, k⟩ : Region).Disjoint ⟨D, n⟩ →
      bytesAt s₁.mem P k = bytesAt s.mem P k := fun hP hPD =>
    bytesAt_frame P₁.frame (fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hP.w.sub_right (Lay.wSub (by decide))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hP.w.sub_right (Region.sub_prefix (by decide))
        · exact hP.w.sub_right (Lay.wSub (by decide))
        · exact hP.w.sub_right (Lay.wSub (by decide))
        · exact hP.stk.symm
        · exact hPD
        · exact hP.w.sub_right (Lay.wSub (by decide))) (by have := hP.lt; omega_using [this])
  refine WP.mono (nonce_ok v L P₁.env Ar.rounds P₁.slots.rounds P₁.slots.nonce P₁.slots.nlen P₁.slots.tl
    Ar.n1 Ar.n15 (by have := Ar.t16; omega_using [this]) (Ar.nonce.of_eq P₁.rd P₁.wr) Ar.data.k Ar.data.w) fun s₂ P₂ => ?_
  have F₂ : Frame (mutR W SP D n) s₁.mem s₂.mem := nonceR_mut P₂.frame
  have S₂ := Slots.of_mut L Ar.data.w F₂ P₁.slots
  have c₂ : ctxCiph s₂.mem K R = ctxCiph s.mem K R := (ctxCiph_mut L Ar.data.k F₂ Ar.rounds).trans eK
  have l₂ : ctxLstar s₂.mem K = ctxLstar s.mem K := (lstar_mut L Ar.data.k F₂).trans eL
  have a₂ : bytesAt s₂.mem A al = bytesAt s.mem A al := (buf_mut Ar.aad Ar.ad F₂).trans (eB Ar.aad Ar.ad)
  exact
    { C := { lay := L, rounds := Ar.rounds, ciph := c₂, lstar := l₂
             buf := by rw [length_bytesAt]; exact Ar.aad.of_eq (P₂.rd.trans P₁.rd) (P₂.wr.trans P₁.wr)
             aad := by rw [length_bytesAt, a₂]
             ad := by rw [length_bytesAt]; exact Ar.ad
             kd := Ar.data.k, dw := Ar.data.w, rnd := S₂.rounds
             short := by rw [length_bytesAt]; exact Ar.aad.lt
             tbl := by
               rw [length_bytesAt]
               exact ⟨_, P₁.tbl.frame P₂.frame (wT_nonceR L), Nat.div_le_div_right Nat.right_le_or⟩ }
      one := ⟨P₂.env, S₂, P₂.wr.trans (P₁.wr.trans hw)⟩
      alen := by rw [P₂.alen, P₁.alen, length_bytesAt] }

/-- Two runs of the same public arguments: `seal`'s and `open`'s inputs. -/
structure TwoN (s₀ s₀' : State) (K W SP N A D : Addr) (R nl al n tl : Nat) (T : Addr) (wn : Nat) : Prop where
  ar : ArgsN s₀ K W SP N A D R nl al n tl T wn
  ar' : ArgsN s₀' K W SP N A D R nl al n tl T wn
  sp : s₀.gpr .rsp = SP
  sp' : s₀'.gpr .rsp = SP
  dd : s₀.mem.readW (SP + BitVec.ofNat 64 8) 64 = D
  dd' : s₀'.mem.readW (SP + BitVec.ofNat 64 8) 64 = D
  nn : s₀.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n
  nn' : s₀'.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n
  tg : s₀.mem.readW (SP + BitVec.ofNat 64 24) 64 = T
  tg' : s₀'.mem.readW (SP + BitVec.ofNat 64 24) 64 = T
  tt : s₀.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl
  tt' : s₀'.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl
  ww : s₀.mem.readW (SP + BitVec.ofNat 64 40) 64 = W
  ww' : s₀'.mem.readW (SP + BitVec.ofNat 64 40) 64 = W
  di : s₀.gpr .rdi = K
  di' : s₀'.gpr .rdi = K
  si : s₀.gpr .rsi = BitVec.ofNat 64 R
  si' : s₀'.gpr .rsi = BitVec.ofNat 64 R
  dx : s₀.gpr .rdx = N
  dx' : s₀'.gpr .rdx = N
  cx : s₀.gpr .rcx = BitVec.ofNat 64 nl
  cx' : s₀'.gpr .rcx = BitVec.ofNat 64 nl
  r8 : s₀.gpr .r8 = A
  r8' : s₀'.gpr .r8 = A
  r9 : s₀.gpr .r9 = BitVec.ofNat 64 al
  r9' : s₀'.gpr .r9 = BitVec.ofNat 64 al

abbrev Two (s₀ s₀' : State) (K W SP N A D : Addr) (R nl al n tl : Nat) (T : Addr) : Prop :=
  TwoN s₀ s₀' K W SP N A D R nl al n tl T 3584

section
variable {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr} {wn : Nat}
  (Tw : TwoN s₀ s₀' K W SP N A D R nl al n tl T wn)
include Tw

/-- What `entry` leaves, in each run. -/
theorem TwoN.entry₁ (hwn : 640 ≤ wn := by decide) (hwlt : wn < 2 ^ 64 := by decide) :
    WP isa (.block entry) s₀ (EntryPostN K W SP wn R N A D nl al n tl T s₀) := by
  obtain ⟨s₁, run₁, P₁⟩ := entry_ok Tw.ar.lay Tw.ar.perm Tw.sp Tw.ar.args Tw.ar.argsW Tw.dd Tw.nn Tw.tg Tw.tt Tw.ww
    Tw.di Tw.si Tw.dx Tw.cx Tw.r8 Tw.r9 hwn hwlt
  exact WP.of_runBlock ⟨s₁, run₁, P₁⟩

theorem TwoN.entry₂ (hwn : 640 ≤ wn := by decide) (hwlt : wn < 2 ^ 64 := by decide) :
    WP isa (.block entry) s₀' (EntryPostN K W SP wn R N A D nl al n tl T s₀') := by
  obtain ⟨s₁, run₁, P₁⟩ := entry_ok Tw.ar'.lay Tw.ar'.perm Tw.sp' Tw.ar'.args Tw.ar'.argsW Tw.dd' Tw.nn' Tw.tg'
    Tw.tt' Tw.ww' Tw.di' Tw.si' Tw.dx' Tw.cx' Tw.r8' Tw.r9' hwn hwlt
  exact WP.of_runBlock ⟨s₁, run₁, P₁⟩

/-- `entry` in two runs: the first instruction loads `W` from the stack, the
rest passes the taint analysis from the public registers. -/
theorem entry_rel : RelCT isa (fun a b => a = s₀ ∧ b = s₀') (.block entry) fun _ _ => True := by
  have a₄₀ := in_off (d := 32) (n := 8) Tw.ar.args (by decide) (by decide)
  have a₄₀' := in_off (d := 32) (n := 8) Tw.ar'.args (by decide) (by decide)
  rw [add_ofNat_assoc] at a₄₀ a₄₀'
  have first : ∀ {s : State}, s.gpr .rsp = SP → s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W →
      InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 (8 + 32)) 8 →
      WP isa (.block [.mov .rax (.mem (at_ .rsp 40))]) s fun t =>
        t.gpr .rax = W ∧ ∀ r, r ≠ .rax → t.gpr r = s.gpr r := fun hsp hW ha =>
    WP.of_runBlock ⟨_, by orun [hsp, hW, ha], by simp only [gpr_setReg, ite_true],
      fun r h => by simp only [gpr_setReg, h, ite_false]⟩
  have e : entry = [.mov .rax (.mem (at_ .rsp 40))] ++ (save .rax ++
      [mvr .r15 .rax, mvr .r14 .rdi, st .r15 rndO .rsi, st .r15 nO .rdx, st .r15 nlO .rcx,
       st .r15 aadO .r8, st .r15 alenO .r9,
       ld .rax .rsp 8, st .r15 dataO .rax, ld .rax .rsp 16, st .r15 lenO .rax, ld .rax .rsp 32,
       st .r15 tlO .rax, ld .rax .rsp 24, st .r15 tgO .rax] ++ lsetup ++ zero16 ckO) := by
    simp only [entry, List.append_assoc]
  rw [e]
  refine RelCT.block_append ?_
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (at_ .rsp 40))]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; rw [Tw.sp, Tw.sp']) hA).wp
    (F₁ := fun (t : State) => t.gpr .rax = W ∧ ∀ r, r ≠ .rax → t.gpr r = s₀.gpr r)
    (F₂ := fun (t : State) => t.gpr .rax = W ∧ ∀ r, r ≠ .rax → t.gpr r = s₀'.gpr r) fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab; exact ⟨first Tw.sp Tw.ww a₄₀, first Tw.sp' Tw.ww' a₄₀'⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block (save .rax ++ [mvr .r15 .rax, mvr .r14 .rdi, st .r15 rndO .rsi, st .r15 nO .rdx, st .r15 nlO .rcx,
       st .r15 aadO .r8, st .r15 alenO .r9,
       ld .rax .rsp 8, st .r15 dataO .rax, ld .rax .rsp 16, st .r15 lenO .rax, ld .rax .rsp 32,
       st .r15 tlO .rax, ld .rax .rsp 24, st .r15 tgO .rax] ++ lsetup ++ zero16 ckO)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have b := RelCT.taint (A := taint) (P := fun (a b : State) => True ∧
      (a.gpr .rax = W ∧ ∀ r, r ≠ .rax → a.gpr r = s₀.gpr r) ∧ (b.gpr .rax = W ∧ ∀ r, r ≠ .rax → b.gpr r = s₀'.gpr r))
    _ (fun a b ⟨_, ha, hb⟩ => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [ha.1, hb.1]
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.di, Tw.di']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.si, Tw.si']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.dx, Tw.dx']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.cx, Tw.cx']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.r8, Tw.r8']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.r9, Tw.r9']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.sp, Tw.sp']) hB
  exact RelCT.seq a b

end

section
variable {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
  (Tw : Two s₀ s₀' K W SP N A D R nl al n tl T)
include Tw

variable (hw : s₀.wr = [⟨D, n⟩, ⟨W, 3584⟩]) (hw' : s₀'.wr = [⟨D, n⟩, ⟨W, 3584⟩])
include hw hw'

/-- `entry`, the table, `Offset_0` and `HASH` in two runs. -/
theorem pre_rel (v : BlocksImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀')
      (.seq (.block entry) (.seq table (.seq (nonce (callees v)) (hash (callees v))))) fun _ _ => True := by
  have L : Lay _ _ _ := Tw.ar.lay
  have hDW := Tw.ar.data.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt Tw.ar.data.lt
  have e := (entry_rel Tw).wp (F₁ := EntryPost K W SP R N A D nl al n tl T s₀)
    (F₂ := EntryPost K W SP R N A D nl al n tl T s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨TwoN.entry₁ Tw, TwoN.entry₂ Tw⟩
  have tb := (rel_taintC [] [alenO] hDW hn (P := fun a b => True ∧ EntryPost K W SP R N A D nl al n tl T s₀ a ∧
      EntryPost K W SP R N A D nl al n tl T s₀' b)
    (fun a b h => ⟨h.2.1.env, h.2.2.env, h.2.1.slots, h.2.2.slots, h.2.1.wr.trans hw, h.2.2.wr.trans hw',
      fun _ h => (nomatch h), fun d hd => by
        simp only [List.mem_singleton] at hd; subst hd
        exact ⟨by decide, by rw [h.2.1.alen, h.2.2.alen]⟩⟩)
    (c := table) ⟨_, by taint_decide⟩).wp
    (F₁ := TRun K W SP N A D R nl al n tl s₀) (F₂ := TRun K W SP N A D R nl al n tl s₀')
    fun a b h => ⟨table_trun Tw.ar h.2.1, table_trun Tw.ar' h.2.2⟩
  have nn := (nonce_rel v L Tw.ar.rounds hDW hn Tw.ar.n1 Tw.ar.n15 (by have := Tw.ar.t16; omega_using [this])
    (P := fun a b => True ∧ TRun K W SP N A D R nl al n tl s₀ a ∧ TRun K W SP N A D R nl al n tl s₀' b)
    fun a b h => ⟨⟨h.2.1.env, h.2.1.slots, h.2.1.wr.trans hw⟩, ⟨h.2.2.env, h.2.2.slots, h.2.2.wr.trans hw'⟩,
      Tw.ar.nonce.of_eq h.2.1.rd h.2.1.wr, Tw.ar'.nonce.of_eq h.2.2.rd h.2.2.wr⟩).wp
    (F₁ := NRun K W SP N A D R nl al n tl s₀) (F₂ := NRun K W SP N A D R nl al n tl s₀')
    fun a b h => ⟨nonce_nrun v Tw.ar hw h.2.1, nonce_nrun v Tw.ar' hw' h.2.2⟩
  have hh := rel_of_pt (P := fun a b => True ∧ NRun K W SP N A D R nl al n tl s₀ a ∧
      NRun K W SP N A D R nl al n tl s₀' b) (Q := fun _ _ => True) (c := hash (callees v)) fun a b h =>
    hash_rel v h.2.1.C h.2.2.C h.2.1.one h.2.2.one (by simp only [length_bytesAt]) hn h.2.1.alen h.2.2.alen
  exact RelCT.seq e (RelCT.seq tb (RelCT.seq nn hh))

end

/-- A run with the public arguments and the address of the tag at `W + tgO`,
which it may read. -/
def OneT (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (T : Addr) (s : State) : Prop :=
  One K W SP R N A D nl n tl s ∧ s.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T ∧
    Covers [⟨T, tl⟩] (s.rd ++ s.wr)

/-- What `pre_wp'` leaves is what `body` needs. -/
theorem brun_of {s : State} {s' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Ar : Args s K W SP N A D R nl al n tl T) (hw : s.wr = [⟨D, n⟩, ⟨W, 3584⟩])
    (P : Pre K W SP N A D R nl al n tl T s s') : BRun K W SP R N A D nl n tl s' :=
  ⟨⟨P.env, P.slots, P.wr.trans hw⟩, Ar.data.of_eq P.rd P.wr, ⟨_, P.tbl⟩, P.ofs.trans P.o0.symm⟩

/-- `body` keeps the public arguments and the address of the tag. -/
theorem body_oneT (v : BlocksImpl) (enc : Bool) {σ s : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Ar : Args σ K W SP N A D R nl al n tl T) (hw : σ.wr = [⟨D, n⟩, ⟨W, 3584⟩])
    (P : Pre K W SP N A D R nl al n tl T σ s) :
    WP isa (body (callees v) enc) s (OneT K W SP R N A D nl n tl T) := by
  have L : Lay _ _ _ := Ar.lay
  have k : ∀ {t : State}, Env K W SP t → t.rd = s.rd → t.wr = s.wr → Frame (bodyR W SP D n) s.mem t.mem →
      OneT K W SP R N A D nl n tl T t := fun E hr' hw' f =>
    ⟨(brun_of Ar hw P).1.step L Ar.data.w E hw' (bodyR_mut f),
      by rw [kept_read L Ar.data.w (bodyR_mut f) (d := tgO) (by decide), P.tg],
      by rw [hr', hw', P.rd, P.wr]; exact Ar.tag.rd⟩
  cases enc
  · exact WP.mono (bodyOpen_ok v L P.env Ar.rounds P.slots.rounds (Ar.data.of_eq P.rd P.wr) P.slots.data
      P.slots.len P.ofs P.o0 P.ck (by rw [P.lstar]; exact P.tbl)) fun t B => k B.env B.rd B.wr B.frame
  · exact WP.mono (bodySeal_ok v L P.env Ar.rounds P.slots.rounds (Ar.data.of_eq P.rd P.wr) P.slots.data
      P.slots.len P.ofs P.o0 P.ck (by rw [P.lstar]; exact P.tbl)) fun t B => k B.env B.rd B.wr B.frame

/-- The tag keeps the public arguments and the address of the tag. -/
theorem tag_oneT (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} {T : Addr} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩)
    {d : Nat} (hd : d = tagO ∨ d = t2O) {s : State}
    (o : OneT K W SP R N A D nl n tl T s) : WP isa (tag (callees v) d) s (OneT K W SP R N A D nl n tl T) :=
  WP.mono (tag_ok v L o.1.env hR o.1.sl.rounds hd) fun t P =>
    have f := tagR_mut (D := D) (n := n) (by rcases hd with rfl | rfl <;> decide) P.frame
    ⟨o.1.step L hDW P.env P.wr f, by rw [kept_read L hDW f (d := tgO) (by decide), o.2.1],
      by rw [P.rd, P.wr]; exact o.2.2⟩

/-- `front` in two runs from states whose writable regions are the data and
`W`. -/
theorem front_rel {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Tw : Two s₀ s₀' K W SP N A D R nl al n tl T) (hw : s₀.wr = [⟨D, n⟩, ⟨W, 3584⟩])
    (hw' : s₀'.wr = [⟨D, n⟩, ⟨W, 3584⟩]) (v : BlocksImpl) (enc : Bool) {d : Nat} (hd : d = tagO ∨ d = t2O) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (front (callees v) enc d) fun a b =>
      True ∧ OneT K W SP R N A D nl n tl T a ∧ OneT K W SP R N A D nl n tl T b := by
  have L : Lay _ _ _ := Tw.ar.lay
  have hDW := Tw.ar.data.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt Tw.ar.data.lt
  have pre := (pre_rel Tw hw hw' v).wp (F₁ := Pre K W SP N A D R nl al n tl T s₀)
    (F₂ := Pre K W SP N A D R nl al n tl T s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨pre_wp' v Tw.ar Tw.sp Tw.dd Tw.nn Tw.tg Tw.tt Tw.ww Tw.di Tw.si Tw.dx Tw.cx Tw.r8 Tw.r9,
        pre_wp' v Tw.ar' Tw.sp' Tw.dd' Tw.nn' Tw.tg' Tw.tt' Tw.ww' Tw.di' Tw.si' Tw.dx' Tw.cx' Tw.r8' Tw.r9'⟩
  have bb : RelCT isa (fun a b => True ∧ Pre K W SP N A D R nl al n tl T s₀ a ∧ Pre K W SP N A D R nl al n tl T s₀' b)
      (body (callees v) enc) fun _ _ => True := by
    cases enc
    · exact bodyOpen_rel v L Tw.ar.rounds hDW Tw.ar.data.lt fun a b h => ⟨brun_of Tw.ar hw h.2.1, brun_of Tw.ar' hw' h.2.2⟩
    · exact bodySeal_rel v L Tw.ar.rounds hDW Tw.ar.data.lt fun a b h => ⟨brun_of Tw.ar hw h.2.1, brun_of Tw.ar' hw' h.2.2⟩
  have bb' := bb.wp (F₁ := OneT K W SP R N A D nl n tl T) (F₂ := OneT K W SP R N A D nl n tl T)
    fun a b h => ⟨body_oneT v enc Tw.ar hw h.2.1, body_oneT v enc Tw.ar' hw' h.2.2⟩
  have tt := (tag_rel v L Tw.ar.rounds hDW hn (d := d) hd
    (P := fun a b => True ∧ OneT K W SP R N A D nl n tl T a ∧ OneT K W SP R N A D nl n tl T b)
    fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩).wp
    (F₁ := OneT K W SP R N A D nl n tl T) (F₂ := OneT K W SP R N A D nl n tl T)
    fun a b h => ⟨tag_oneT v L Tw.ar.rounds hDW hd h.2.1, tag_oneT v L Tw.ar.rounds hDW hd h.2.2⟩
  unfold front
  exact Proof.AesCcm.X86_64.rel_assoc4 (RelCT.seq pre (RelCT.seq bb' tt))

/-! ## Moving the tag to the regions read only -/

/-- Two runs, as the runs from their states with the writable regions `ex`
moved to those they read only, and only the writable regions `w` left: the
code runs the same from both (`Exec.widen`, `Exec.det`). -/
theorem rel_narrow {P Q : State → State → Prop} {c : Prog isa} (ex w : List Region)
    (h : RelCT isa (fun σ₁ σ₂ => ∃ s₁ s₂, P s₁ s₂ ∧ σ₁ = s₁.withRegions (s₁.rd ++ ex) w ∧
      σ₂ = s₂.withRegions (s₂.rd ++ ex) w) c Q)
    (hP : ∀ s₁ s₂, P s₁ s₂ → (Covers (ex ++ w) s₁.wr ∧ Covers w s₁.wr ∧
        ∃ t s', Exec isa c (s₁.withRegions (s₁.rd ++ ex) w) t s') ∧
      (Covers (ex ++ w) s₂.wr ∧ Covers w s₂.wr ∧ ∃ t s', Exec isa c (s₂.withRegions (s₂.rd ++ ex) w) t s')) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨⟨c₁, w₁, u₁, σ₁', n₁⟩, ⟨c₂, w₂, u₂, σ₂', n₂⟩⟩ := hP _ _ hp
  have widen : ∀ {s σ' : State} {u : List Leak}, Covers (ex ++ w) s.wr → Covers w s.wr →
      Exec isa c (s.withRegions (s.rd ++ ex) w) u σ' → Exec isa c s u (σ'.withRegions s.rd s.wr) :=
    fun {s σ' u} hc hw n => by
    have m := Exec.widen n (rd := s.rd) (wr := s.wr)
      (by simp only [State.withRegions_rd, State.withRegions_wr, List.append_assoc]
          exact Covers.append (Covers.refl _) hc)
      (by simpa only [State.withRegions_wr] using hw)
    rwa [State.withRegions_withRegions, State.withRegions_self] at m
  obtain ⟨rfl, -⟩ := Exec.det e₁ (widen c₁ w₁ n₁)
  obtain ⟨rfl, -⟩ := Exec.det e₂ (widen c₂ w₂ n₂)
  exact ⟨(h _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ n₁ n₂).1, trivial⟩

/-- `s` with the tag `⟨T, tl⟩` read only, and the data and `W` its writable
regions. -/
abbrev narrowTN (D : Addr) (n : Nat) (T : Addr) (tl : Nat) (W : Addr) (wn : Nat) (s : State) : State :=
  s.withRegions (s.rd ++ [⟨T, tl⟩]) [⟨D, n⟩, ⟨W, wn⟩]

abbrev narrowT (D : Addr) (n : Nat) (T : Addr) (tl : Nat) (W : Addr) (s : State) : State :=
  narrowTN D n T tl W 3584 s

theorem covers_narrowT (rd : List Region) (d t w : Region) :
    Covers (rd ++ [d, t, w]) ((rd ++ [t]) ++ [d, w]) :=
  Covers.of_mem fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp [h]

/-- The arguments, in the state with the tag read only. -/
theorem ArgsN.narrow {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr} {wn : Nat}
    (Ar : ArgsN s K W SP N A D R nl al n tl T wn) (hw : s.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, wn⟩]) :
    ArgsN (narrowTN D n T tl W wn s) K W SP N A D R nl al n tl T wn := by
  have c : Covers (s.rd ++ s.wr) ((narrowTN D n T tl W wn s).rd ++ (narrowTN D n T tl W wn s).wr) := by
    rw [hw]; exact covers_narrowT _ _ _ _
  have b : ∀ {P : Addr} {k : Nat}, BufN W SP wn s P k → BufN W SP wn (narrowTN D n T tl W wn s) P k := fun h =>
    ⟨h.rd.trans c, h.lt, h.wrap, h.w, h.stk⟩
  have w : Covers [⟨W, wn⟩] (narrowTN D n T tl W wn s).wr := Covers.of_mem fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp
  have d : Covers [⟨D, n⟩] (narrowTN D n T tl W wn s).wr := Covers.of_mem fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp
  exact {
    lay := Ar.lay, perm := ⟨Ar.perm.k.trans c, w⟩
    rounds := Ar.rounds, nonce := b Ar.nonce, aad := b Ar.aad
    data := ⟨b Ar.data.toBufN, d, Ar.data.k⟩, tag := b Ar.tag
    nd := Ar.nd, ad := Ar.ad, td := Ar.td, n1 := Ar.n1, n15 := Ar.n15, t1 := Ar.t1, t16 := Ar.t16
    retW := Ar.retW, retD := Ar.retD, retT := Ar.retT, args := Ar.args.trans c, argsW := Ar.argsW }

/-- Two runs, from the states with the tag read only. -/
theorem TwoN.narrow {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr} {wn : Nat}
    (Tw : TwoN s₀ s₀' K W SP N A D R nl al n tl T wn) (hw : s₀.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, wn⟩])
    (hw' : s₀'.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, wn⟩]) :
    TwoN (narrowTN D n T tl W wn s₀) (narrowTN D n T tl W wn s₀') K W SP N A D R nl al n tl T wn :=
  { Tw with ar := Tw.ar.narrow hw, ar' := Tw.ar'.narrow hw' }

/-! ## The copy of the tag and the exit -/

/-- What the copy of the tag needs of a run: the environment, the tag
length in its slot and the address of the tag at `W + tgO`. -/
def SealOutN (K W SP T : Addr) (tl wn : Nat) (s : State) : Prop :=
  EnvN K W SP wn s ∧ s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl ∧
    s.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T

abbrev SealOut (K W SP T : Addr) (tl : Nat) (s : State) : Prop := SealOutN K W SP T tl 3584 s

/-- The copy of the tag and the exit, in two runs with the same `W`, tag
length and tag. -/
theorem sealTail_relN {K W SP T : Addr} {tl wn : Nat} {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → SealOutN K W SP T tl wn s₁ ∧ SealOutN K W SP T tl wn s₂)
    (hwn : 640 ≤ wn := by decide) (hwlt : wn < 2 ^ 64 := by decide) :
    RelCT isa P (.seq tagOut (.block restore)) fun _ _ => True := by
  let F : State → Prop := fun s => s.gpr .rbx = W ∧ s.gpr .rsi = T ∧ s.gpr .r12 = BitVec.ofNat 64 tl ∧
    s.gpr .rcx = BitVec.ofNat 64 0 ∧ s.gpr .r15 = W
  have args : ∀ {s : State}, SealOutN K W SP T tl wn s →
      WP isa (.block [mvr .rbx .r15, ld .rsi .r15 tgO, ld .r12 .r15 tlO, .mov .rcx (.imm 0)]) s F :=
    fun ⟨E, htl, htg⟩ => by
      obtain ⟨s', run, h1, h2, h3, h4, g, -⟩ := tagOutArgs_ok E htg htl hwn hwlt
      exact WP.of_runBlock ⟨s', run, h1, h2, h3, h4, by rw [g _ (by decide) (by decide) (by decide) (by decide), E.r15]⟩
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r15])
      (.block [mvr .rbx .r15, ld .rsi .r15 tgO, ld .r12 .r15 tlO, .mov .rcx (.imm 0)]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := P) _ (fun a b h => by
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; rw [(hP a b h).1.1.r15, (hP a b h).2.1.r15]) hA).wp
    (F₁ := F) (F₂ := F) fun a b h => ⟨args (hP a b h).1, args (hP a b h).2⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rsi, .r12, .rcx, .r15])
      (.seq copyLoop (.block restore)) hc).isSome = true := ⟨_, by taint_decide⟩
  have b := RelCT.taint (A := taint) (P := fun a b => True ∧ F a ∧ F b) _ (fun a b ⟨_, ha, hb⟩ => by
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [ha.1, hb.1]
    · rw [ha.2.1, hb.2.1]
    · rw [ha.2.2.1, hb.2.2.1]
    · rw [ha.2.2.2.1, hb.2.2.2.1]
    · rw [ha.2.2.2.2, hb.2.2.2.2]) hB
  unfold tagOut
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq e₁ c₁ => cases e₁ with | seq a₁ b₁ =>
  cases e₂ with | seq e₂ c₂ => cases e₂ with | seq a₂ b₂ =>
  obtain ⟨ht, hq⟩ := RelCT.seq a b _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

theorem sealTail_rel {K W SP T : Addr} {tl : Nat} {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → SealOut K W SP T tl s₁ ∧ SealOut K W SP T tl s₂) :
    RelCT isa P (.seq tagOut (.block restore)) fun _ _ => True :=
  sealTail_relN hP

/-- `vg_aes_ocb_seal` in two runs. -/
theorem seal_rel {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Tw : Two s₀ s₀' K W SP N A D R nl al n tl T) (hw : s₀.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 3584⟩])
    (hw' : s₀'.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 3584⟩]) (v : BlocksImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') («seal» (callees v)) fun _ _ => True := by
  have Tn := Tw.narrow hw hw'
  have inner := (front_rel Tn rfl rfl v true (.inl rfl)).mono (P' := fun σ₁ σ₂ => ∃ s₁ s₂,
      (s₁ = s₀ ∧ s₂ = s₀') ∧ σ₁ = s₁.withRegions (s₁.rd ++ [⟨T, tl⟩]) [⟨D, n⟩, ⟨W, 3584⟩] ∧
        σ₂ = s₂.withRegions (s₂.rd ++ [⟨T, tl⟩]) [⟨D, n⟩, ⟨W, 3584⟩])
    (fun _ _ ⟨_, _, ⟨rfl, rfl⟩, e₁, e₂⟩ => ⟨e₁, e₂⟩) fun _ _ h => h
  have cw : ∀ {s : State}, s.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 3584⟩] →
      Covers ([⟨T, tl⟩] ++ [⟨D, n⟩, ⟨W, 3584⟩]) s.wr ∧ Covers [⟨D, n⟩, ⟨W, 3584⟩] s.wr := fun h => by
    rw [h]
    refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  have fr := (rel_narrow [⟨T, tl⟩] [⟨D, n⟩, ⟨W, 3584⟩] inner fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨_, _, e₁, -⟩ := sealFront_wp' v Tn.ar Tn.sp Tn.dd Tn.nn Tn.tg Tn.tt Tn.ww Tn.di Tn.si Tn.dx Tn.cx
        Tn.r8 Tn.r9
      obtain ⟨_, _, e₂, -⟩ := sealFront_wp' v Tn.ar' Tn.sp' Tn.dd' Tn.nn' Tn.tg' Tn.tt' Tn.ww' Tn.di' Tn.si' Tn.dx'
        Tn.cx' Tn.r8' Tn.r9'
      exact ⟨⟨(cw hw).1, (cw hw).2, _, _, e₁⟩, ⟨(cw hw').1, (cw hw').2, _, _, e₂⟩⟩).wp
    (F₁ := SFront K W SP N A D R nl al n tl T s₀) (F₂ := SFront K W SP N A D R nl al n tl T s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨sealFront_wp' v Tw.ar Tw.sp Tw.dd Tw.nn Tw.tg Tw.tt Tw.ww Tw.di Tw.si Tw.dx Tw.cx Tw.r8 Tw.r9,
        sealFront_wp' v Tw.ar' Tw.sp' Tw.dd' Tw.nn' Tw.tg' Tw.tt' Tw.ww' Tw.di' Tw.si' Tw.dx' Tw.cx' Tw.r8' Tw.r9'⟩
  exact RelCT.seq fr (sealTail_rel fun a b h => ⟨⟨h.2.1.env, h.2.1.slots.tl, h.2.1.tg⟩,
    ⟨h.2.2.env, h.2.2.slots.tl, h.2.2.tg⟩⟩)

/-- Two runs of `seal` or `open` with the same public arguments. -/
theorem TwoN.of {s₁ s₂ : State} {wn : Nat} (hq : onePub s₁ s₂)
    (ar₁ : ArgsN s₁ (s₁.gpr .rdi) (arg s₁ 4) (s₁.gpr .rsp) (s₁.gpr .rdx) (s₁.gpr .r8) (arg s₁ 0) (s₁.gpr .rsi).toNat
      (s₁.gpr .rcx).toNat (s₁.gpr .r9).toNat (arg s₁ 1).toNat (arg s₁ 3).toNat (arg s₁ 2) wn)
    (ar₂ : ArgsN s₂ (s₂.gpr .rdi) (arg s₂ 4) (s₂.gpr .rsp) (s₂.gpr .rdx) (s₂.gpr .r8) (arg s₂ 0) (s₂.gpr .rsi).toNat
      (s₂.gpr .rcx).toNat (s₂.gpr .r9).toNat (arg s₂ 1).toNat (arg s₂ 3).toNat (arg s₂ 2) wn) :
    TwoN s₁ s₂ (s₁.gpr .rdi) (arg s₁ 4) (s₁.gpr .rsp) (s₁.gpr .rdx) (s₁.gpr .r8) (arg s₁ 0) (s₁.gpr .rsi).toNat
      (s₁.gpr .rcx).toNat (s₁.gpr .r9).toNat (arg s₁ 1).toNat (arg s₁ 3).toNat (arg s₁ 2) wn := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hq
  have a0 := q8 0 (by decide)
  have a1 := q8 1 (by decide)
  have a2 := q8 2 (by decide)
  have a3 := q8 3 (by decide)
  have a4 := q8 4 (by decide)
  have ar' := ar₂
  rw [← a0, ← a1, ← a2, ← a3, ← a4, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7] at ar'
  exact
  { ar := ar₁, ar' := ar', sp := rfl, sp' := q7.symm
    dd := rfl, dd' := by rw [q7]; exact a0.symm
    nn := (ofNat_toNat64 _).symm, nn' := by rw [q7, a1]; exact (ofNat_toNat64 _).symm
    tg := rfl, tg' := by rw [q7]; exact a2.symm
    tt := (ofNat_toNat64 _).symm, tt' := by rw [q7, a3]; exact (ofNat_toNat64 _).symm
    ww := rfl, ww' := by rw [q7]; exact a4.symm
    di := rfl, di' := q1.symm
    si := (ofNat_toNat64 _).symm, si' := by rw [← q2]; exact (ofNat_toNat64 _).symm
    dx := rfl, dx' := q3.symm
    cx := (ofNat_toNat64 _).symm, cx' := by rw [← q4]; exact (ofNat_toNat64 _).symm
    r8 := rfl, r8' := q5.symm
    r9 := (ofNat_toNat64 _).symm, r9' := by rw [← q6]; exact (ofNat_toNat64 _).symm }

theorem Two.of {s₁ s₂ : State} (hq : onePub s₁ s₂)
    (ar₁ : Args s₁ (s₁.gpr .rdi) (arg s₁ 4) (s₁.gpr .rsp) (s₁.gpr .rdx) (s₁.gpr .r8) (arg s₁ 0) (s₁.gpr .rsi).toNat
      (s₁.gpr .rcx).toNat (s₁.gpr .r9).toNat (arg s₁ 1).toNat (arg s₁ 3).toNat (arg s₁ 2))
    (ar₂ : Args s₂ (s₂.gpr .rdi) (arg s₂ 4) (s₂.gpr .rsp) (s₂.gpr .rdx) (s₂.gpr .r8) (arg s₂ 0) (s₂.gpr .rsi).toNat
      (s₂.gpr .rcx).toNat (s₂.gpr .r9).toNat (arg s₂ 1).toNat (arg s₂ 3).toNat (arg s₂ 2)) :
    Two s₁ s₂ (s₁.gpr .rdi) (arg s₁ 4) (s₁.gpr .rsp) (s₁.gpr .rdx) (s₁.gpr .r8) (arg s₁ 0) (s₁.gpr .rsi).toNat
      (s₁.gpr .rcx).toNat (s₁.gpr .r9).toNat (arg s₁ 1).toNat (arg s₁ 3).toNat (arg s₁ 2) :=
  TwoN.of hq ar₁ ar₂

/-- `vg_aes_ocb_seal` is constant time. -/
theorem seal_ct (v : BlocksImpl) : ConstantTime isa sealX86_64.pre sealX86_64.pub («seal» (callees v)) :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hq e₁ e₂ => by
    have T := Two.of hq (sealArgs_of h₁) (sealArgs_of h₂)
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hq
    have hw₂ : s₂.wr = [⟨arg s₁ 0, (arg s₁ 1).toNat⟩, ⟨arg s₁ 2, (arg s₁ 3).toNat⟩, ⟨arg s₁ 4, 3584⟩] := by
      rw [h₂.2.1, q8 0 (by decide), q8 1 (by decide), q8 2 (by decide), q8 3 (by decide), q8 4 (by decide)]
    exact (seal_rel T h₁.2.1 hw₂ v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesOcb.X86_64

end

end

/-! ### `AesOcb.X86_64.OpenCT`, which only this module used -/

section

/-!
# AES-OCB on x86-64: `vg_aes_ocb_open` is constant time

Untrusted: everything here is checked by Lean. As `seal` (`front_rel`), then
the copy of the received tag to `W`, the comparison, the mask and `restore`,
which pass the taint analysis from the public slots and the address of the
tag at `W + tgO`: the comparison's result is a value, not a branch.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)

section
variable {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {Tg : Addr}
  (T : Two s₀ s₀' K W SP N A D R nl al n tl Tg)
include T

/-- `recv` keeps the public arguments. -/
theorem recv_one {s : State} (o : OneT K W SP R N A D nl n tl Tg s) :
    WP isa recv s (One K W SP R N A D nl n tl) := by
  refine WP.mono (recv_ok o.1.env T.ar.t1 T.ar.t16 o.2.1 o.1.sl.tl o.2.2 T.ar.tag.w) fun t ⟨m, g, rd, wr⟩ => ?_
  have fr : Frame (mutR W SP D n) s.mem t.mem := by
    rw [m]
    refine (writeBytes_frame _ _ _ (by rw [Proof.AesCcm.X86_64.length_bytesAt]; exact Region.contains_self _ _)).sub
      fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by have := T.ar.t16; omega_using [this])⟩
  exact o.1.step T.ar.lay T.ar.data.w (o.1.env.keep g rd wr) wr fr

/-- The comparison keeps the public arguments, and leaves 1 or 0 at `W`. -/
theorem cmpRes {s : State} (o : One K W SP R N A D nl n tl s) :
    WP isa cmp s fun t => One K W SP R N A D nl n tl t ∧
      ∃ c : Bool, t.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64 := by
  refine WP.mono (cmp_ok o.env T.ar.t1 T.ar.t16 o.sl.tl) fun t ⟨m, g, rd, wr⟩ => ?_
  have E : Env K W SP t := o.env.keep (fun r hr => g r
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd wr
  have fr : Frame (mutR W SP D n) s.mem t.mem := by
    rw [m]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)).sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
  refine ⟨o.step T.ar.lay T.ar.data.w E wr fr, decide (bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl),
    ?_⟩
  rw [m, Mem.readW_writeW_self64]; simp only [decide_eq_true_eq]

/-- The mask keeps the public arguments. -/
theorem mask_one {s : State} (o : One K W SP R N A D nl n tl s) {c : Bool}
    (hok : s.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64) :
    WP isa mask s (One K W SP R N A D nl n tl) := by
  refine WP.mono (mask_ok o.env o.sl.data o.sl.len (T.ar.data.of_one o) hok) fun t ⟨E, _, wr, m⟩ => ?_
  have fr : Frame (mutR W SP D n) s.mem t.mem := by
    rw [m]
    refine (writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)).sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  exact o.step T.ar.lay T.ar.data.w E wr fr

variable (hw : s₀.wr = [⟨D, n⟩, ⟨W, 3584⟩]) (hw' : s₀'.wr = [⟨D, n⟩, ⟨W, 3584⟩])
include hw hw'

/-- `vg_aes_ocb_open` in two runs. -/
theorem open_rel (v : BlocksImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') («open» (callees v)) fun _ _ => True := by
  have hDW := T.ar.data.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt T.ar.data.lt
  have fr := front_rel T hw hw' v false (.inr rfl)
  have rr := (rel_taintC [] [tgO] hDW hn (fun a b (h : True ∧ OneT K W SP R N A D nl n tl Tg a ∧
    OneT K W SP R N A D nl n tl Tg b) => ⟨h.2.1.1.env, h.2.2.1.env, h.2.1.1.sl, h.2.2.1.sl, h.2.1.1.wr, h.2.2.1.wr,
      fun _ h => (nomatch h), fun d hd => by
        simp only [List.mem_singleton] at hd; subst hd; exact ⟨by decide, by rw [h.2.1.2.1, h.2.2.2.1]⟩⟩)
    (c := recv) ⟨_, by taint_decide⟩).wp
    (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun a b h => ⟨recv_one T h.2.1, recv_one T h.2.2⟩
  have cc := (rel_taintC [] [] hDW hn (fun a b (h : True ∧ One K W SP R N A D nl n tl a ∧
    One K W SP R N A D nl n tl b) => Both.of h.2.1 h.2.2) (c := cmp) ⟨_, by taint_decide⟩).wp
    (F₁ := fun (s : State) => One K W SP R N A D nl n tl s ∧ ∃ c : Bool, s.mem.readW (W + BitVec.ofNat 64 tagO) 64 =
      if c then 1#64 else 0#64)
    (F₂ := fun (s : State) => One K W SP R N A D nl n tl s ∧ ∃ c : Bool, s.mem.readW (W + BitVec.ofNat 64 tagO) 64 =
      if c then 1#64 else 0#64)
    fun a b h => ⟨cmpRes T h.2.1, cmpRes T h.2.2⟩
  have mm := (rel_taintC [] [] hDW hn (fun a b (h : True ∧ (One K W SP R N A D nl n tl a ∧
      ∃ c : Bool, a.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64) ∧
    (One K W SP R N A D nl n tl b ∧
      ∃ c : Bool, b.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64)) => Both.of h.2.1.1 h.2.2.1)
    (c := mask) ⟨_, by taint_decide⟩).wp
    (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun a b h => ⟨mask_one T h.2.1.1 h.2.1.2.choose_spec, mask_one T h.2.2.1 h.2.2.2.choose_spec⟩
  have rs := rel_taintC [] [] hDW hn (fun a b (h : True ∧ One K W SP R N A D nl n tl a ∧
    One K W SP R N A D nl n tl b) => Both.of h.2.1 h.2.2) (c := .block ([ld .rax .r15 tagO] ++ restore))
    ⟨_, by taint_decide⟩
  unfold «open»
  exact RelCT.seq fr (RelCT.seq rr (RelCT.seq cc (RelCT.seq mm rs)))

end

/-- `vg_aes_ocb_open` is constant time. -/
theorem open_ct (v : BlocksImpl) : ConstantTime isa openX86_64.pre openX86_64.pub («open» (callees v)) :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hq e₁ e₂ => by
    have T := Two.of hq.1 (openArgs_of h₁) (openArgs_of h₂)
    obtain ⟨⟨q1, q2, q3, q4, q5, q6, q7, q8⟩, -⟩ := hq
    have hw₂ : s₂.wr = [⟨arg s₁ 0, (arg s₁ 1).toNat⟩, ⟨arg s₁ 4, 3584⟩] := by
      rw [h₂.2.1, q8 0 (by decide), q8 1 (by decide), q8 4 (by decide)]
    exact (open_rel T h₁.2.1 hw₂ v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesOcb.X86_64

end

end

/-! ### `AesOcb.X86_64.Verified`, which only this module used -/

section

/-!
# AES-OCB on x86-64: `Verified`

Correctness and constant time (for any implementations `v` of
`vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks` and `vg_aes_expand_key_scratch`),
a state satisfying each precondition, and the shared contracts of
`Spec/Ocb/Contract.lean` with the working space as a last argument
(`Proof/AesOcb/Scratch.lean`; 3584 bytes for `seal` and `open`, 2560 for
`init`), with 8 bytes of stack: the return address of
the calls, whose callees use no stack. `Frame.lean` allocates the working
space.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem seal_mx (v : BlocksImpl) : («seal» (callees v)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«seal», front, tagOut, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill, hashSum, hashRest, padTo, body,
    whole, pass, nextOffset, rest, padCk, xorPad, tag, callBlocks, callees, Code.allInstrs, v.encMxcsr, v.decMxcsr,
    Bool.true_and, Bool.and_true, ↓reduceIte]
  decide +kernel

theorem open_mx (v : BlocksImpl) : («open» (callees v)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«open», front, recv, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill, hashSum, hashRest, padTo, body,
    whole, pass, nextOffset, rest, padCk, xorPad, tag, cmp, mask, callBlocks, callees, Code.allInstrs, v.encMxcsr,
    v.decMxcsr, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_mx (v : BlocksImpl) : (init (callees v)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, callees, Code.allInstrs, v.encMxcsr, v.expandMxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem seal_spSafe (v : BlocksImpl) : («seal» (callees v)).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«seal», front, tagOut, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill, hashSum, hashRest, padTo, body,
    whole, pass, nextOffset, rest, padCk, xorPad, tag, callBlocks, callees, Code.all, v.encSpSafe, v.decSpSafe,
    Bool.true_and, Bool.and_true, ↓reduceIte]
  decide +kernel

theorem open_spSafe (v : BlocksImpl) : («open» (callees v)).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«open», front, recv, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill, hashSum, hashRest, padTo, body,
    whole, pass, nextOffset, rest, padCk, xorPad, tag, cmp, mask, callBlocks, callees, Code.all, v.encSpSafe,
    v.decSpSafe, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_spSafe (v : BlocksImpl) : (init (callees v)).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, callees, Code.all, v.encSpSafe, v.expandSpSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem seal_correct (v : BlocksImpl) (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa («seal» (callees v)) s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := seal_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (seal_mx v) he hg, hp⟩

theorem open_correct (v : BlocksImpl) (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa («open» (callees v)) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := open_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (open_mx v) he hg, hp⟩

theorem init_correct (v : BlocksImpl) (s : State) (hs : initX86_64.pre s) :
    ∃ t s', Exec isa (init (callees v)) s t s' ∧ abiPreserved s s' ∧ initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := init_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (init_mx v) he hg, hp⟩

/-- A state satisfying the precondition of `vg_aes_ocb_seal`: a 1-byte nonce,
no associated data, no data, a 4-byte tag at `0x3000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 1 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8020 then 4 else if a = 0x8019 then 0x30 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x2100, 0⟩, ⟨0x8008, 40⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0, 3584⟩]

/-- A state satisfying the precondition of `vg_aes_ocb_init`: a 16-byte key. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩]

theorem seal_verified (v : BlocksImpl) :
    Verified X86_64.target («seal» (callees v)) (Proof.AesOcb.sealWorkContract X86_64.abi 448 8) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Proof.AesOcb.sealWorkContract, Proof.AesOcb.sealWorkSig, Spec.Ocb.sealPre,
      Proof.AesOcb.sealRoundsPost, Proof.AesOcb.sealX86_64, Proof.AesOcb.sealPreX, Proof.AesOcb.oneFacts,
      Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad, Proof.AesOcb.aData, Proof.AesOcb.aTag,
      Proof.AesOcb.aWork, Proof.AesOcb.onePub, X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8,
      Proof.AesOcb.ret, Proof.AesOcb.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
      List.range.loop, VG.X86_64.below, X86_64.argRegs] [sealSat] using sealSat)

theorem initF_correct (v : BlocksImpl) (f : Proof.Aes.X86_64.BlocksFree v.enc v.expand) (s : State)
    (hs : initX86_64F.pre s) :
    ∃ t s', Exec isa (init (callees v)) s t s' ∧ abiPreserved s s' ∧ initX86_64F.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := initF_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (init_mx v) he hg, hp⟩

/-- A state satisfying the precondition of `vg_aes_ocb_init` with 24 bytes of
working space. -/
def initSatF : State := { initSat with wr := [⟨0x2000, 256⟩, ⟨0x4000, 24⟩] }

theorem initF_verified (v : BlocksImpl) (f : Proof.Aes.X86_64.BlocksFree v.enc v.expand) :
    Verified X86_64.target (init (callees v)) (Proof.AesOcb.initScratchContractF X86_64.abi 8) :=
  Verified.of_correct (initF_correct v f) (initF_ct v f) (by
    sig_implies [Proof.AesOcb.initScratchContractF, Proof.AesOcb.initScratchSigF, Spec.Ocb.initPre,
      Spec.Ocb.initPost, Proof.AesOcb.initX86_64F, Proof.AesOcb.initX86_64, Proof.AesOcb.stk8, Proof.AesOcb.ret,
      X86_64.abi, X86_64.argRegs, VG.X86_64.below] [initSatF, initSat] using initSatF)

theorem init_verified (v : BlocksImpl) :
    Verified X86_64.target (init (callees v)) (Proof.AesOcb.initScratchContract X86_64.abi 8) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [Proof.AesOcb.initScratchContract, Proof.AesOcb.initScratchSig, Spec.Ocb.initPre,
      Spec.Ocb.initPost, Proof.AesOcb.initX86_64, Proof.AesOcb.stk8, Proof.AesOcb.ret, X86_64.abi, X86_64.argRegs,
      VG.X86_64.below] [initSat] using initSat)

/-- A state satisfying the precondition of `vg_aes_ocb_open`: as `sealSat`,
with the tag read only. -/
def openSat : State := { sealSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x2100, 0⟩, ⟨0x3000, 4⟩, ⟨0x8008, 40⟩]
  wr := [⟨0, 0⟩, ⟨0, 3584⟩] }

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified (v : BlocksImpl) :
    Verified X86_64.target («open» (callees v)) (Proof.AesOcb.openWorkContract X86_64.abi 448 8) :=
  Verified.of_correct (open_correct v) (open_ct v)
    { pre := by sig_implies_pre [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs]
      post := by sig_implies_post [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs]
        sig_simp [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs] [openSat, sealSat] using openSat }

end VG.Proof.AesOcb.X86_64

end

end


/-!
# AES-OCB on x86-64, with its working space on the stack

Every function runs its code, proved with the working space as its last
argument (`Verified.lean`), in a frame that allocates it. `init`'s working
space is in a register (`rcx`): its frame of 2568 bytes holds the 2560
bytes and 8 more to keep `rsp` aligned (`Verified.stackScratch`). The
working space of `seal` and `open` is passed on the stack after the six
argument registers and four other stack arguments (`data`, `len`, `tag` and
`tag_len`), so their frame of 3632 bytes holds the 3584 bytes of working
space, a copy of those four arguments, the word that stands for the return
address and the address of the working space (`Verified.stackArgScratch`).
The code's own calls use 8 bytes below the frame, the return address, as
`vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks` and `vg_aes_expand_key_scratch` use
no stack. `open`'s leak, whether it succeeds, reads only its buffers
(`openLeak_local`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

variable (v : BlocksImpl)

theorem init_xdepth : (init (callees v)).x86_64Depth ≤ 8 := by
  simp only [init, callees, Code.x86_64Depth, v.encNoStack, v.expandNoStack]
  decide +kernel

theorem seal_xdepth : («seal» (callees v)).x86_64Depth ≤ 8 := by
  simp only [«seal», front, tagOut, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill,
    hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest, padCk, xorPad, tag, callBlocks, callees,
    Code.x86_64Depth, v.encNoStack, v.decNoStack, ↓reduceIte]
  decide +kernel

theorem open_xdepth : («open» (callees v)).x86_64Depth ≤ 8 := by
  simp only [«open», front, recv, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill,
    hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest, padCk, xorPad, tag, cmp, mask, callBlocks, callees,
    Code.x86_64Depth, v.encNoStack, v.decNoStack, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

/-- A state satisfying `vg_aes_ocb_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Ocb.initContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Ocb.initContract, Spec.Ocb.initSig, Spec.Ocb.initPre, Spec.Ocb.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (init (callees v)))
      (Spec.Ocb.initContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratchPre (hpostOut := Proof.AesOcb.initPostOut_local _) (sig := Spec.Ocb.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Ocb.initPre X86_64.abi.ptrBits) (post := Spec.Ocb.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 8) (bytes := 2568) (init_verified v) (by decide) (by decide)
    (by decide) (init_spSafe v) (init_xdepth v) initFrameSat_pre

theorem initFrameSatF_pre : ∃ s, (Spec.Ocb.initContract X86_64.abi 40).pre s := by
  implies_sat [Spec.Ocb.initContract, Spec.Ocb.initSig, Spec.Ocb.initPre, Spec.Ocb.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- `init_framed`, over functions that need no working space: a frame of the
24 bytes `init` writes itself, after the 8 that stand for the return
address. -/
theorem initF_framed (f : Proof.Aes.X86_64.BlocksFree v.enc v.expand) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 32 .rcx (init (callees v)))
      (Spec.Ocb.initContract X86_64.abi 40) :=
  X86_64.Verified.stackScratchPre (hpostOut := Proof.AesOcb.initPostOut_local _) (sig := Spec.Ocb.initSig) (nm := "scratch") (e := .u64) (n := 3)
    (pre := Spec.Ocb.initPre X86_64.abi.ptrBits) (post := Spec.Ocb.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 8) (bytes := 32) (initF_verified v f) (by decide) (by decide)
    (by decide) (init_spSafe v) (init_xdepth v) initFrameSatF_pre

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x2100, 0⟩, ⟨0x8008, 32⟩], wr := [⟨0, 0⟩, ⟨0x3000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesOcb.sealRoundsContract X86_64.abi 3640).pre s := by
  implies_sat [Proof.AesOcb.sealRoundsContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Proof.AesOcb.sealRoundsPost,
    X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using sealFrameSat

theorem seal_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 3632 4 («seal» (callees v)))
      (Proof.AesOcb.sealRoundsContract X86_64.abi 3640) :=
  X86_64.Verified.stackArgScratchPre (hpostOut := sealPostOut_local _) (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64)
    (n := 448) (pre := Spec.Ocb.sealPre X86_64.abi.ptrBits)
    (post := Proof.AesOcb.sealRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3632) (seal_verified v) (by decide) (by decide) (by decide)
    (seal_spSafe v) (seal_xdepth v) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x2100, 0⟩, ⟨0x3000, 4⟩, ⟨0x8008, 32⟩], wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesOcb.openRoundsContract X86_64.abi 3640).pre s := by
  implies_sat [Proof.AesOcb.openRoundsContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Proof.AesOcb.openRoundsPost,
    Spec.Ocb.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, sealSat] using openFrameSat

theorem open_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 3632 4 («open» (callees v)))
      (Proof.AesOcb.openRoundsContract X86_64.abi 3640) :=
  X86_64.Verified.stackArgScratchPre (hpostOut := openPostOut_local _) (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64)
    (n := 448) (pre := Spec.Ocb.openPre X86_64.abi.ptrBits)
    (post := Proof.AesOcb.openRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.Ocb.openLeak X86_64.abi.ptrBits)) (bytes := 3632) (open_verified v)
    (by decide) (by decide) (by decide) (open_spSafe v) (open_xdepth v) (openPre_local _)
    (openPost_local _) openFrameSat_pre (hleak := openLeak_local _)

end VG.Proof.AesOcb.X86_64
