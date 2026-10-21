module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.OnePass
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.PhaseOne
import VerifiedGarbage.Proof.Framework.X86_64.HighKeep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.LoopTo
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop48To
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop48
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The 512-bit loop in one pass over a source and then in place

Untrusted: everything here is checked by Lean. `StitchZHTo.encN` runs the
out-of-place loops over the `nb` blocks at `src` (`phase1`, from a state `s₀`
meeting `SPreTo`), then the in-place loop (`StitchZH.body`) over the blocks
at `dst` after them, `N` in all, as `StitchR.encN` does on 256-bit registers:
the in-place loop goes on from `nState s₀ N` (`StitchR.nState`) after the
group the out-of-place loops encrypted last (`switchZ_ok`), and what it
leaves is the contract `StitchR.NPost` (`StitchR.NPost.of_ePost`).

What `phase1` leaves (`PhaseOne`) needs the field's algebra for the powers
the setup stores and for the 48-block loop's: it is proved where that
algebra is imported (`StitchZHTo.phase1_ok`, `StitchZ/OkP.lean`) and passed
to the proofs of `encN`, which so need not import it. `phase1G_ok` proves it
of any setup and 48-block loop meeting what `encTailGTo_ok` takes of them.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZHTo

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo EPost CtxMode sp op oR nb nr kp cp yp pp cb ciph sch hk y₀ dp
  dR pR bAddr blk ctb)
open VG.Proof.Gcm.X86_64.StitchZ (EInv AInv FinOk)
open VG.Proof.Gcm.X86_64.StitchZTo (EInvTo AInvTo ReadyTo dst ctbT oAddr)
open VG.Proof.Gcm.X86_64.StitchR (nState nMem nR NPre NPost nState_gpr nState_r8 nState_mem nState_rd
  nState_wr nb_nState nMem_frame sch_nState ciph_nState cb_nState hk_nState y₀_nState blk_nState ctb_nState)
open VG.Proof.Gcm.X86_64.Pclmul (toNat_ofNat_lt)
open VG.Spec.Gcm (Block blockAt)

/-- `phase1` after its setup, for any 48-block loop `bigC` as `encTailGTo_ok`
takes it. -/
theorem phase1G_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block}
    (hf : FinOk (hk s₀) P) {bigC : Prog isa} {i : BitVec 32} (t : Nat) (hi : BitVec.signExtend 64 i = BitVec.ofNat 64 t)
    (ht : t < 2 ^ 64) (hbig : ∀ s, t ≤ nb s₀ → EInvTo s₀ P 1 s → VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s →
      WP isa bigC s fun s' => ∃ e, EInvTo s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s')
    {s : State} (hR : ReadyTo s₀ P s) (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.seq Impl.Gcm.X86_64.StitchZHTo.firstTo (.seq (.block [.alu .cmp .r9 (.imm i)])
      (.seq (.ite .b (.block []) bigC) (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.ite .b (.block []) (.loop Impl.Gcm.X86_64.StitchZHTo.bodyTo .ae)))))) s fun s' =>
      ∃ e, nb s₀ = 16 * e ∧ EInvTo s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.seq (WP.mono (firstTo_ok hp hR hCache) fun s₂ ⟨hI₂, hCache₂⟩ => ?_)
  refine WP.seq (WP.mono (WP.hkeep rfl (StitchZ.cmp_ok s₂ i t hi)) fun s₃ ⟨⟨hcf, g, l, m, rd, wr⟩, hh⟩ => ?_)
  have hI₃ := hI₂.of_eq g l m rd wr
  have hCache₃ := hCache₂.keep hh (hI₃.a.keys hp)
  rw [hI₂.r9, toNat_ofNat_lt (by omega), toNat_ofNat_lt ht] at hcf
  refine WP.seq (WP.mono (WP.ite (Q := fun s' => ∃ e, EInvTo s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s')
    (decide (nb s₀ - 16 * (1 - 1) < t)) (by simp only [eval, hcf]) (fun _ => WP.block_nil ⟨1, hI₃, hCache₃⟩)
    (fun h => hbig _ (by simp at h; omega) hI₃ hCache₃)) fun s₄ ⟨e, hI₄, hCache₄⟩ => ?_)
  refine WP.seq (WP.mono (WP.hkeep (by decide) (StitchZTo.cmpE_ok hI₄)) fun s₅ ⟨⟨hI₅, hcf₅⟩, hh₅⟩ => ?_)
  exact WP.mono (loopERTo_ok hp hf hI₅ hcf₅ (hCache₄.keep hh₅ (hI₅.a.keys hp))) fun s₆ ⟨e', hlt, hI₆, hK₆⟩ =>
    ⟨e', by have := hI₆.a.le; have := hI₆.one; omega, hI₆, hK₆⟩

section
variable {M : CtxMode} {s₀ : State} {N : Nat} (hp : SPreTo M s₀)
include hp

/-- A state with `r8 ← rbx` and `r9 += rbp` from one the out-of-place loops
left after their last group `e` is one the in-place loop reaches from
`nState s₀ N` after group `e`. -/
theorem eInvZ (hn : NPre M s₀ N) {P : Nat → Nat → Block} {e : Nat} (he : nb s₀ = 16 * e) {s : State}
    (hI : EInvTo s₀ P e s) {t : State} (g8 : t.gpr .r8 = s.gpr .rbx) (g9 : t.gpr .r9 = s.gpr .r9 + s.gpr .rbp)
    (g : ∀ r, r ≠ .r8 → r ≠ .r9 → t.gpr r = s.gpr r) (hm : t.mem = s.mem) (hx : t.xmm = s.xmm)
    (hy : t.ymmHi = s.ymmHi) (hz : t.zmmHi = s.zmmHi) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    EInv (nState s₀ N) P e t := by
  have hN : N < 2 ^ 64 := by have := hn.wrap; have := hp.nb16; have := hn.le; omega
  have hw := hp.wrap_o
  have hwN := hn.wrap
  have hle := hn.le
  have hl : ∀ r l, t.zlane r l = s.zlane r l := fun r l => by
    simp only [State.zlane, State.lane, hx, hy, hz]
  have h1 := hI.one
  have hA := hI.a
  have hg : ∀ r, r ≠ .r8 → r ≠ .r9 → (nState s₀ N).gpr r = s₀.gpr r := fun r h8 h9 => nState_gpr h8 h9
  have fr : Frame [dR (nState s₀ N), pR (nState s₀ N)] (nState s₀ N).mem t.mem := fun x hx' => by
    have h₁ := hx' _ List.mem_cons_self
    have h₂ := hx' _ (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [dp, nState_r8, nb_nState hN, pp, hg .r11 (by decide) (by decide), Region.Contains] at h₁ h₂
    rw [hm, nState_mem, hA.frame x (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [Region.Contains]; omega
      · simp only [Region.Contains]; exact h₂), nMem_frame s₀ x (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only [Region.Contains]; omega)]
  have bl : ∀ k < nb (nState s₀ N), blockAt t.mem (bAddr (nState s₀ N) k) =
      if k < 16 * e then ctb (nState s₀ N) k else blk (nState s₀ N) k := fun k hk => by
    rw [nb_nState hN] at hk
    rw [show bAddr (nState s₀ N) k = oAddr s₀ k by simp only [bAddr, dp, nState_r8], hm]
    by_cases hlo : k < 16 * e
    · simp only [hlo, ↓reduceIte, ctb_nState hp hwN (by omega) hk]
      exact hA.blocks k (by omega)
    · simp only [hlo, ↓reduceIte, blk_nState hp hwN hk, show ¬ k < nb s₀ by omega]
      refine VG.Proof.Aes.X86_64.AesNi.blockAt_frame hA.frame fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ (by omega) (by omega)
      · exact hn.o_p.sub_left (Offset.sub_base _ (by omega))
  have rbp : s.gpr .rbp = BitVec.ofNat 64 (N - nb s₀) := by
    rw [hI.gpr .rbp (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hn.rbp
  exact {
    a := {
      le := by rw [nb_nState hN]; omega
      slot := by
        rw [show pp (nState s₀ N) = pp s₀ from hg .r11 (by decide) (by decide), cb_nState hp, hm]
        exact hA.slot
      msk := fun l hl' => by rw [hl]; exact hA.msk l hl'
      r11 := by rw [g .r11 (by decide) (by decide), hA.r11]; exact (hg .r11 (by decide) (by decide)).symm
      rdi := by rw [g .rdi (by decide) (by decide), hA.rdi]; exact (hg .rdi (by decide) (by decide)).symm
      rsi := by rw [g .rsi (by decide) (by decide), hA.rsi, hg .rsi (by decide) (by decide)]
      r10 := by
        rw [g .r10 (by decide) (by decide), hA.r10]
        simp only [kp, nr, hg .rdi (by decide) (by decide), hg .rsi (by decide) (by decide)]
      frame := fr
      blocks := bl
      rd := by rw [hrd, hA.rd]; rfl
      wr := by rw [hwr, hA.wr]; rfl }
    one := h1
    rdx := by rw [g .rdx (by decide) (by decide), hI.rdx, dp, nState_r8]
    r9 := by
      rw [g9, hI.r9, rbp, nb_nState hN, ← BitVec.ofNat_add]
      congr 1; omega
    rax := by rw [g .rax (by decide) (by decide), hI.rax]; exact (hg .rdx (by decide) (by decide)).symm
    gpr := fun r ha hd h9 h10 => by
      by_cases h8 : r = .r8
      · subst h8
        rw [g8, hI.gpr .rbx (by decide) (by decide) (by decide) (by decide) (by decide), hn.rbx, nState_r8]
      · rw [g r h8 h9, hI.gpr r ha hd h8 h9 h10, hg r h8 h9]
    pw := fun k hk l hl' => by
      rw [hm, pp, hg .r11 (by decide) (by decide)]; exact hI.pw k hk l hl'
    m1 := fun l hl' => by rw [hl]; exact hI.m1 l hl'
    y := by
      rw [hl, hI.y, hk_nState hp, y₀_nState hp]
      congr 1
      refine List.map_congr_left fun k hk => ?_
      have := List.mem_range.mp hk
      exact (ctb_nState hp hwN (by omega) (by omega)).symm
    y1 := fun l h1l hl4 => by rw [hl]; exact hI.y1 l h1l hl4 }

omit hp in
theorem nr_nState : nr (nState s₀ N) = nr s₀ := by
  simp only [nr, nState_gpr (r := .rsi) (by decide) (by decide)]

/-- `r8 ← rbx`, `r9 += rbp` and `cmp r9, 32` after the out-of-place loops,
with the round keys kept in registers. -/
theorem switchZ_ok (hn : NPre M s₀ N) {P : Nat → Nat → Block} {e : Nat} (he : nb s₀ = 16 * e) {s : State}
    (hI : EInvTo s₀ P e s) (hK : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.block [.mov .r8 (.reg .rbx), .alu .add .r9 (.reg .rbp), .alu .cmp .r9 (.imm 32)]) s fun t =>
      EInv (nState s₀ N) P e t ∧ t.cf = some (decide (nb (nState s₀ N) - 16 * (e - 1) < 32)) ∧
        VG.Proof.Aes.X86_64.VaesZH.Keys (nr (nState s₀ N)) (sch (nState s₀ N)) t := by
  have hp' := hn.sPre hp
  rw [show ([.mov .r8 (.reg .rbx), .alu .add .r9 (.reg .rbp), .alu .cmp .r9 (.imm 32)] : List Instr) =
    [.mov .r8 (.reg .rbx), .alu .add .r9 (.reg .rbp)] ++ [.alu .cmp .r9 (.imm 32)] from rfl, WP.block_append_iff]
  refine WP.mono (Q := fun t => EInv (nState s₀ N) P e t ∧ HKeep s t) ?_ fun t ⟨hI', hh⟩ =>
    WP.mono (WP.hkeep (by decide) (StitchZ.cmpE_ok hI')) fun u ⟨⟨hI'', hcf⟩, hh'⟩ => ⟨hI'', hcf, by
      rw [nr_nState, sch_nState hp]
      exact hK.keep (hh.trans hh') (by
        have := hI''.a.keys hp'
        rwa [nr_nState, sch_nState hp] at this)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨eInvZ hp hn he hI (by simp [RegUpd.gpr_setReg]) (by simp [RegUpd.gpr_setReg])
    (fun r h8 h9 => by simp [RegUpd.gpr_setReg, h8, h9]) rfl rfl rfl rfl rfl rfl, ⟨rfl, rfl⟩⟩

end

/-- `encN` meets its contract. -/
theorem encN_ok (h1 : PhaseOne) {s₀ : State} (hp : SPreTo CtxMode.prepared s₀) (hm : nb s₀ % 16 = 0) {N : Nat}
    (hn : NPre CtxMode.prepared s₀ N) : WP isa Impl.Gcm.X86_64.StitchZHTo.encN s₀ (NPost s₀ N) := by
  have hN : N < 2 ^ 64 := by have := hn.wrap; have := hp.nb16; have := hn.le; omega
  have hp' := hn.sPre hp
  refine WP.seq (WP.mono (h1 hp hm) fun s₄ ⟨P, e, he, hI₄, hK₄, hf⟩ => ?_)
  refine WP.seq (WP.mono (switchZ_ok hp hn he hI₄ hK₄) fun s₅ ⟨hI₅, hcf₅, hK₅⟩ => ?_)
  have hf' : FinOk (hk (nState s₀ N)) P := by rw [hk_nState hp]; exact hf
  have hm' : nb (nState s₀ N) % 16 = 0 := by rw [nb_nState hN]; exact hn.m16
  refine WP.seq (WP.mono (StitchZH.loopE_ok hp' hm' hf' hI₅ hcf₅ hK₅) fun s₆ ⟨e', he', hI₆⟩ => ?_)
  exact WP.mono (StitchZ.final_ok hp' hf' he' hI₆) fun _ h => StitchR.NPost.of_ePost hp hn h

end VG.Proof.Gcm.X86_64.StitchZHTo
