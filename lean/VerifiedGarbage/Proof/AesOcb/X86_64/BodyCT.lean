import VerifiedGarbage.Proof.AesOcb.X86_64.WholeCT
import VerifiedGarbage.Proof.AesOcb.X86_64.RestCT
import VerifiedGarbage.Proof.AesOcb.X86_64.Body

/-!
# AES-OCB on x86-64: the data is constant time

Untrusted: everything here is checked by Lean. The number of whole blocks
and the length of the rest come from the public slots, so the branches agree
in both runs (`rel_flagsC`); the whole blocks and the rest are related by
`whole_rel` and `rest_rel`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (eval_e)

/-- What `body` needs of a run: the public arguments, the data, `L_0`, and
the offset equal to `Offset_0`. -/
def BRun (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (s : State) : Prop :=
  One K W SP R N A D nl n tl s ∧ DBuf K W SP s D n ∧ (∃ l, blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) ∧
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
    (hB1 : ∀ {W}, BodyOk W pre (fun b o => b ^^^ o) fC1) (hB2 : ∀ {W}, BodyOk W post (fun b o => b ^^^ o) fC2)
    {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D : Addr} {nl n tl : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {s : State} (h : BRun K W SP R N A D nl n tl s) :
    WP isa (.seq (.block [ld .r13 .r15 lenO, .shift .shr .r13 4, .alu .test .r13 (.reg .r13)])
        (.ite .e (.block []) (whole b pre post))) s (One K W SP R N A D nl n tl) := by
  obtain ⟨o, hD, ⟨l, hl0⟩, ho⟩ := h
  let O0 := blockAtMem s.mem (W + BitVec.ofNat 64 ofsO)
  let ckF1 := ckRec (blockAtMem s.mem (W + BitVec.ofNat 64 ckO))
    fun i c => fC1 c (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1))
  let ckF2 := ckRec (ckF1 (n / 16)) fun i c => fC2 c
    (G (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
    (offAt O0 l (i + 1))
  refine WP.mono (wholeIte_ok (O0 := O0) (l := l) (ckF1 := ckF1) (ckF2 := ckF2) ok nosp depth hcall hB1 hB2 L o.env hR
    hD o.sl.data o.sl.len o.sl.rounds rfl ho.symm rfl hl0 (fun _ => rfl) rfl (fun _ => rfl)) fun t P =>
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
    (hB1 : ∀ {W}, BodyOk W pre (fun b o => b ^^^ o) fC1) (hB2 : ∀ {W}, BodyOk W post (fun b o => b ^^^ o) fC2)
    (hc₁ : ∃ hc, (taint.check (ocbT [.r13] [])
      (.seq (.block [ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)]) (pass pre)) hc).isSome = true)
    (hc₂ : ∃ hc, (taint.check (ocbT [.r13] [])
      (.seq (.block (copy16 o0O ofsO ++ [ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)])) (pass post)) hc).isSome
        = true)
    {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D : Addr} {nl n tl : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n < 2 ^ 64) {P : State → State → Prop}
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
        WRun K W SP R N A D nl n tl m s₁ ∧ s₁.zf = some (decide (m = 0)) := fun s ⟨o, hD, ⟨l, hl0⟩, _⟩ => by
    obtain ⟨s₁, run₁, r13₁, zf₁, m₁, g₁, rd₁, wr₁⟩ := bodyHead_ok o.env hn o.sl.len
    have E₁ : Env K W SP s₁ := o.env.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
      rd₁ wr₁
    have o₁ : One K W SP R N A D nl n tl s₁ := ⟨E₁, by rw [m₁]; exact o.sl, by rw [wr₁]; exact o.wr⟩
    exact WP.of_runBlock ⟨s₁, run₁, ⟨o₁, r13₁, ⟨l, by rw [m₁]; exact hl0⟩, hD.of_one o₁⟩, zf₁⟩
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
      · exact whole_rel ok ct nosp depth L hR hDW hn' (Nat.mul_div_le n 16) (Nat.pos_of_ne_zero hm) (by omega) hB1
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
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n < 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → BRun K W SP R N A D nl n tl s₁ ∧ BRun K W SP R N A D nl n tl s₂) :
    RelCT isa P (body (callees v) true) fun _ _ => True := by
  simp only [body, ↓reduceIte]
  exact body_rel' v true v.encOk v.encCt v.encNosp v.encDepth hcall_enc sealPre_ok xorOfs_ok ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩ L hR hDW hn hP

/-- `body` for `open`, in two runs. -/
theorem bodyOpen_rel (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n < 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → BRun K W SP R N A D nl n tl s₁ ∧ BRun K W SP R N A D nl n tl s₂) :
    RelCT isa P (body (callees v) false) fun _ _ => True := by
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  exact body_rel' v false v.decOk v.decCt v.decNosp v.decDepth hcall_dec xorOfs_ok openPost_ok ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩ L hR hDW hn hP

end VG.Proof.AesOcb.X86_64
