import VerifiedGarbage.Proof.AesOcb.X86.Offset0

/-!
# AES-OCB on x86: enciphering blocks (`callBlocks`)

Untrusted: everything here is checked by Lean. `callBlocks f args` sets up
the arguments of `vg_aes_*_blocks` (`args` puts the blocks' address in `edx`
and their number in `ebx`) and calls it with the key context and the working
space at `W + scrO` (`callBlocks_ok`): the blocks at `D` (`DReg`, in `W` or
the data) go through `f` with the key schedule.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq runBlock_app_of toNat_rounds)

/-- `n` blocks at `D` that a call may encipher in place: in `W` before
`scrO`, or in the data. -/
structure DReg (p : Prm) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  fD : D.toNat + 16 * n ≤ 2 ^ 32
  kd : (⟨w64 p.K, 240⟩ : Region).Disjoint ⟨w64 D, 16 * n⟩
  ds : (⟨w64 D, 16 * n⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩
  bd : (stk p).Disjoint ⟨w64 D, 16 * n⟩
  wr : Covers [⟨w64 D, 16 * n⟩] s.wr
  inm : InMut p [⟨w64 D, 16 * n⟩]

theorem DReg.of_eq {p : Prm} {s s' : State} {D : BitVec 32} {n : Nat} (h : DReg p s D n) (hwr : s'.wr = s.wr) :
    DReg p s' D n := ⟨h.fD, h.kd, h.ds, h.bd, by rw [hwr]; exact h.wr, h.inm⟩

/-- Blocks of `W` before `scrO`. -/
theorem DReg.w {p : Prm} (L : Lay p) {s : State} (E : Env p s) {d n : Nat} (h : d + 16 * n ≤ scrO)
    (hm : d + 16 * n ≤ 128 ∨ 144 ≤ d ∧ d + 16 * n ≤ 176 ∨ 216 ≤ d ∧ d + 16 * n ≤ 384 ∨ 384 ≤ d) :
    DReg p s (p.W + BitVec.ofNat 32 d) n := by
  simp only [scrO] at h
  have a := L.aW (o := d) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [L.nW (by omega)]; have := L.ww; omega
  · rw [a]; exact (L.k_w' (by omega)).sub_left (Region.sub_prefix (by decide))
  · rw [a]; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · rw [a]; exact L.bw' (by omega)
  · rw [a]; exact E.perm.wC (by omega)
  simp only [List.mem_singleton] at hr; subst hr; rw [a]
  rcases hm with hm | hm | hm | hm
  · exact inMut_w p (.inl hm)
  · exact inMut_w p (.inr (.inl hm))
  · exact inMut_w p (.inr (.inr (.inl hm)))
  · exact inMut_w p (.inr (.inr (.inr ⟨hm, by omega⟩)))

/-- What `callBlocks` leaves: the blocks through `f`. -/
structure CallPost (p : Prm) (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (D : BitVec 32) (n : Nat)
    (s s' : State) : Prop where
  env : Env p s'
  frame : Frame [⟨w64 D, 16 * n⟩, ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p] s.mem s'.mem
  out : Spec.Aes.statesAt s'.mem (w64 D) n =
    (Spec.Aes.statesAt s.mem (w64 D) n).map (f p.R (bytesAt s.mem (w64 p.K) (16 * (p.R + 1))))
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The call, from the state after `args`. -/
theorem blocksCall_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {p : Prm} (L : Lay p) {s : State} (E : Env p s)
    {D : BitVec 32} {n : Nat} (hdx : s.gpr .edx = D) (hbx : s.gpr .ebx = BitVec.ofNat 32 n) (hD : DReg p s D n) :
    WP isa (.seq (.block [.mov .eax (slot ctxO), .mov .ecx (slot rndO), .alu .add .ebp (imm scrO)])
      (.seq (blocksFrame fn) (.block [.alu .sub .ebp (imm scrO)]))) s (CallPost p f D n s) := by
  have hc := E.slots.ctx
  have hr := E.slots.rounds
  simp only [slotv_eq] at hc hr
  obtain ⟨s₁, run₁, ax₁, cx₁, bp₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov .eax (slot ctxO),
      .mov .ecx (slot rndO), .alu .add .ebp (imm scrO)] s = some s₁ ∧ s₁.gpr .eax = p.K ∧
      s₁.gpr .ecx = BitVec.ofNat 32 p.R ∧ s₁.gpr .ebp = p.W + BitVec.ofNat 32 scrO ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .ebp → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hc, hr], by gregs [hc], by gregs [hr], by gregs [E.ebp],
      fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [], by gmems []⟩
  have aS : w64 (p.W + BitVec.ofNat 32 scrO) = w64 p.W + BitVec.ofNat 64 scrO := L.aW (by decide)
  have hsp₁ : s₁.gpr .esp = p.SP := by rw [g₁ _ (by decide) (by decide) (by decide), E.esp]
  have bc : BCall s₁ p.K D (p.W + BitVec.ofNat 32 scrO) p.R n := {
    eax := ax₁, ecx := cx₁, edx := by rw [g₁ _ (by decide) (by decide) (by decide), hdx],
    ebx := by rw [g₁ _ (by decide) (by decide) (by decide), hbx], ebp := bp₁, rounds := L.rounds,
    esp := by rw [hsp₁]; exact L.sp, kd := hD.kd,
    ks := by rw [aS]; exact (L.k_w' (by decide)).sub_left (Region.sub_prefix (by decide)),
    ds := by rw [aS]; exact hD.ds, bk := by rw [hsp₁]; exact L.bk.sub_right (Region.sub_prefix (by decide)),
    bd := by rw [hsp₁]; exact hD.bd, bs := by rw [hsp₁, aS]; exact L.bw' (by decide),
    fK := by have := L.kw; omega, fD := hD.fD, fS := by rw [L.nW (by decide)]; have := L.ww; omega,
    reads := by rw [rd₁, wr₁]; exact covers_prefix E.perm.k (by decide),
    writes := by
      rw [wr₁, aS]
      intro a k ⟨r, hr, hc⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hD.wr a k ⟨_, List.mem_singleton_self _, hc⟩
      · exact E.perm.wC (show scrO + 2048 ≤ 2560 by decide) a k ⟨_, List.mem_singleton_self _, hc⟩ }
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (blk_call ok nosp stack bc) fun s₂ P₂ => ?_)
  have bp₂ : s₂.gpr .ebp = p.W + BitVec.ofNat 32 scrO := by rw [P₂.saved _ (by decide), bp₁]
  have sp₂ : s₂.gpr .esp = p.SP := by rw [P₂.saved _ (by decide), hsp₁]
  obtain ⟨s₃, run₃, bp₃, g₃, m₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa [.alu .sub .ebp (imm scrO)] s₂ = some s₃ ∧
      s₃.gpr .ebp = p.W ∧ (∀ r, r ≠ .ebp → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧
      s₃.wr = s₂.wr := by
    refine ⟨_, by grun [], by gregs [bp₂]; exact BitVec.add_sub_cancel _ _, fun r h => by gregs [h], by gmems [],
      by gmems [], by gmems []⟩
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have fr : Frame [⟨w64 D, 16 * n⟩, ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p] s.mem s₃.mem := by
    rw [m₃, ← m₁, ← aS]
    have := P₂.frame
    rw [hsp₁] at this
    exact this.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (by rfl))
  refine ⟨E.mut L bp₃ (by rw [g₃ _ (by decide), sp₂]) (by rw [rd₃, P₂.rd, rd₁]) (by rw [wr₃, P₂.wr, wr₁])
      (fr.sub fun r hr => ?_), fr, ?_, fun r h₁ h₂ h₃ => ?_, by rw [rd₃, P₂.rd, rd₁], by rw [wr₃, P₂.wr, wr₁]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hD.inm _ (List.mem_singleton_self _)
    · exact inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
    · exact inMut_stk p
  · rw [m₃, P₂.out, m₁]
  · by_cases h₄ : r = .ebp
    · subst h₄; rw [bp₃, E.ebp]
    · rw [g₃ r h₄, P₂.saved r (by cases r <;> simp_all [calleeSaved]), g₁ r h₁ h₂ h₄]

end VG.Proof.AesOcb.X86
