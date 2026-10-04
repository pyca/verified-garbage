import VerifiedGarbage.Proof.AesOcb.X86_64.Nonce
import VerifiedGarbage.Proof.AesCcm.X86_64.CTBase

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

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm.X86_64 (word_byte add_ofNat_assoc runBlock_append)

/-- The taint: the registers `rs`, `r14`, `r15` and `rsp` public, `r15` the
base of the working space (the second writable region), the slots of the
public arguments `[208, 248)` and `[288, 304)` and the words at `ex` public. -/
def ocbT (rs : List Reg) (ex : List Nat) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.r14, .r15, .rsp]), flags := false, lens := [0, 2560], bases := [(.r15, 1, 0)],
    slots := [(1, 208, 40), (1, 288, 16)] ++ ex.map fun d => (1, d, 8) }

/-- Two runs with the same public arguments: both in the environment, with
the same slots and writable regions, agreeing on the registers `rs` and the
words of `W` at `ex`. -/
structure Both (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (rs : List Reg) (ex : List Nat)
    (s₁ s₂ : State) : Prop where
  e₁ : Env K W SP s₁
  e₂ : Env K W SP s₂
  sl₁ : Slots W R N A D nl n tl s₁.mem
  sl₂ : Slots W R N A D nl n tl s₂.mem
  wr₁ : s₁.wr = [⟨D, n⟩, ⟨W, 2560⟩]
  wr₂ : s₂.wr = [⟨D, n⟩, ⟨W, 2560⟩]
  agree : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r
  ex : ∀ d ∈ ex, d + 8 ≤ 2560 ∧ s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s₂.mem.readW (W + BitVec.ofNat 64 d) 64

theorem both_agree {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {rs : List Reg} {ex : List Nat}
    {s₁ s₂ : State} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (h : Both K W SP R N A D nl n tl rs ex s₁ s₂) : X86_64.Taint.Agree (ocbT rs ex) s₁ s₂ := by
  have wf : ∀ {s : State}, Env K W SP s → s.wr = [⟨D, n⟩, ⟨W, 2560⟩] → X86_64.Taint.Wf (ocbT rs ex) s :=
    fun E hw => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
    · rw [hw]; exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
    · rw [hw]; exact List.pairwise_pair.mpr hDW
    · rw [hw]; intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hn
      · show 2560 ≤ 2 ^ 64; decide
    · simp only [ocbT, List.mem_singleton] at hp; subst hp
      simp only [X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
      rw [E.r15, BitVec.add_zero]
  have hb : ∀ s : State, s.wr = [⟨D, n⟩, ⟨W, 2560⟩] → ∀ k, X86_64.Taint.byteAddr s 1 k = W + BitVec.ofNat 64 k :=
    fun s hw k => by
      simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
  have hw : ∀ {k : Nat} (d : Nat), d ≤ k → W + BitVec.ofNat 64 k = W + BitVec.ofNat 64 d + BitVec.ofNat 64 (k - d) :=
    fun {k} d e => by rw [add_ofNat_assoc, show d + (k - d) = k by omega]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [h.wr₁, h.wr₂], wf h.e₁ h.wr₁, wf h.e₂ h.wr₂,
    fun sl hsl => ?_, fun sl hsl k hk₁ hk₂ => ?_, X86_64.Taint.noLo⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with hr | hr
    · exact h.agree r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.e₁.r14, h.e₂.r14]
      · rw [h.e₁.r15, h.e₂.r15]
      · rw [h.e₁.rsp, h.e₂.rsp]
  · simp only [ocbT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hsl
    rcases hsl with (rfl | rfl) | ⟨d, hd, rfl⟩
    · simp [ocbT]
    · simp [ocbT]
    · simp only [ocbT, List.getD_cons_succ, List.getD_cons_zero]; exact (h.ex d hd).1
  · simp only [ocbT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hsl
    have S₁ := h.sl₁
    have S₂ := h.sl₂
    rcases hsl with (rfl | rfl) | ⟨d, hd, rfl⟩ <;> rw [hb s₁ h.wr₁, hb s₂ h.wr₂]
    · simp only at hk₁ hk₂
      have key : ∀ d, d ∈ [208, 216, 224, 232, 240] → d ≤ k → k < d + 8 →
          s₁.mem (W + BitVec.ofNat 64 k) = s₂.mem (W + BitVec.ofNat 64 k) := fun d hd h₁ h₂ => by
        rw [hw d h₁]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl
        · exact word_byte S₁.data S₂.data (by omega)
        · exact word_byte S₁.len S₂.len (by omega)
        · exact word_byte S₁.tl S₂.tl (by omega)
        · exact word_byte S₁.rounds S₂.rounds (by omega)
        · exact word_byte S₁.aad S₂.aad (by omega)
      have hq : (k - 208) / 8 = 0 ∨ (k - 208) / 8 = 1 ∨ (k - 208) / 8 = 2 ∨ (k - 208) / 8 = 3 ∨
          (k - 208) / 8 = 4 := by omega
      exact key (208 + 8 * ((k - 208) / 8)) (by
        rcases hq with h | h | h | h | h <;> rw [h] <;> decide) (by omega) (by omega)
    · simp only at hk₁ hk₂
      by_cases hk : k < 296
      · rw [hw 288 (by omega)]; exact word_byte S₁.nonce S₂.nonce (by omega)
      · rw [hw 296 (by omega)]; exact word_byte S₁.nlen S₂.nlen (by omega)
    · simp only at hk₁ hk₂
      rw [hw d hk₁]; exact word_byte (h.ex d hd).2 rfl (by omega)

/-- Code the taint analysis checks from `ocbT rs ex`. -/
theorem rel_taintC {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (ex : List Nat) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → Both K W SP R N A D nl n tl rs ex s₁ s₂)
    (hc : ∃ hc, (taint.check (ocbT rs ex) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (ocbT rs ex) (fun s₁ s₂ h => both_agree hDW hn (hP _ _ h)) hc

/-- Code the taint analysis checks from `ocbT rs ex`, leaving the flags public. -/
theorem rel_flagsC {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (ex : List Nat) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
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
structure One (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (s : State) : Prop where
  env : Env K W SP s
  sl : Slots W R N A D nl n tl s.mem
  wr : s.wr = [⟨D, n⟩, ⟨W, 2560⟩]

theorem Both.of {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {s₁ s₂ : State}
    (o₁ : One K W SP R N A D nl n tl s₁) (o₂ : One K W SP R N A D nl n tl s₂) :
    Both K W SP R N A D nl n tl [] [] s₁ s₂ :=
  ⟨o₁.env, o₂.env, o₁.sl, o₂.sl, o₁.wr, o₂.wr, fun _ h => (nomatch h), fun _ h => (nomatch h)⟩

/-- One run, after a frame within the parts the pieces write. -/
theorem One.step {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} (L : Lay K W SP)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {s s' : State} (o : One K W SP R N A D nl n tl s)
    (E : Env K W SP s') (hw : s'.wr = s.wr) (f : Frame (mutR W SP D n) s.mem s'.mem) :
    One K W SP R N A D nl n tl s' :=
  ⟨E, Slots.of_mut L hDW f o.sl, hw.trans o.wr⟩

/-- The data, in a run with the public arguments. -/
theorem DBuf.of_one {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {s s' : State}
    (h : DBuf K W SP s D n) (o : One K W SP R N A D nl n tl s') : DBuf K W SP s' D n where
  toBuf := { h.toBuf with rd := Covers.right (by rw [o.wr]; exact Covers.of_mem fun r hr => by simp_all) }
  wr := by rw [o.wr]; exact Covers.of_mem fun r hr => by simp_all
  k := h.k

/-- A call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on the same
`n` blocks at `D'` in both runs. -/
theorem callBlocks_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86_64 f).pre (Proof.Aes.blocksX86_64 f).pub b.code)
    {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D : Addr} {nl n tl : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64) {args : List Instr} (rs : List Reg)
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
