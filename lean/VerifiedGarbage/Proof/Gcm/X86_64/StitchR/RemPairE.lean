module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.RemPair
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemLoopOne
import VerifiedGarbage.Proof.Framework.X86_64.Lane0Zero
import VerifiedGarbage.Proof.Framework.X86_64.ZFrame
import VerifiedGarbage.Proof.Gcm.X86_64.StitchTo.Base
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemBody
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemBodyD
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The blocks after the last group, encrypted two at a time

`StitchR.remE` encrypts the `r` blocks after the last group of the 256-bit
loop as `StitchZH.remLoop_ok` does one at a time, but in pairs, as
`RemPair.lean` decrypts them: the first alone if `r` is odd
(`StitchZH.remStep_ok`, in the lower lanes, which clears the upper lanes of
what it writes: `oddStepE_ok`), then two at a time, one in each lane
(`remPairE`, `pairStepE_ok`), the products of the ciphertext of block `i + l`
in lane `l`. The blocks are read at `src`, which may be another buffer than
the one they are written to. `RInvPE` is `StitchZH.RInv` with the products of
both lanes added; `foldLanesE_ok` adds them into the lower lanes, where
`RInv` has them.

`remE` and `remD` read the powers from the key context instead (`OkC`,
`RInvC`, `RInvPC`, whatever blocks they hash), with the steps of encryption
(`oneStepC_ok`, `pairStepC_ok`) or of decryption (`oneStepDC_ok`,
`pairStepDC_ok`) composed alike (`remMidG_ok`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchR

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod eval_pxor)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.StitchZTo (atIx)
open VG.Impl.Gcm.X86_64.StitchR (remPairE remPairD remNextPair foldLanes)
open VG.Impl.Gcm.X86_64.StitchZH (remBody remNext)
open VG.Proof.Gcm.X86_64.StitchZTo (ea_atIx)
open VG.Proof.Gcm.X86_64.StitchTo (blockAt_writeW_lane2 load256_lane ymm_lane2)
open VG.Proof.Gcm.X86_64.StitchZH (REnv RInv accR remStep_ok addr0 addr768 lane0_remBody remBody_dst
  lane0_remBodyD remBodyD_dst)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Proof.Gcm.X86_64.Stitch (blockAt_writeW_sep')
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (Block blockAt)

/-- The loads and the store of `remPairE src`. -/
abbrev pairMemE (src : Reg) : List Instr :=
  [.vmovdquLoad .l256 .xmm13 (atIx src .r10 0), .vmovdquLoad .l256 .xmm12 (atIx .r11 .r10 768),
   .vop (.vbin .vpxor .l256 .xmm13 .xmm13 .xmm12), .vmovdquStore .l256 (atIx .rdx .r10 0) .xmm13,
   .vmovdquLoad .l256 .xmm12 (atIx .rax .r10 0)]

theorem remPairE_eq (src : Reg) : remPairE src = pairMemE src ++ pairLanes := rfl

/-- The two blocks at `src + r10` loaded into `ymm13`, their keystream at
`r11 + r10 + 768` added and the result stored to `rdx + r10`, and the powers
at `rax + r10` loaded into `ymm12`. -/
theorem pairMemE_ok (src : Reg) (t : State)
    (hinS : InRegions (t.rd ++ t.wr) (t.gpr src + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 32)
    (hinK : InRegions (t.rd ++ t.wr) (t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int)) 32)
    (hinD : InRegions t.wr (t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 32)
    (hinP : InRegions (t.rd ++ t.wr) (t.gpr .rax + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 32) :
    WP isa (.block (pairMemE src)) t fun t' =>
      (∃ v : BitVec 256, t'.mem = t.mem.writeW (t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) v) ∧
      (∀ l < 2, blockAt t'.mem (t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) + BitVec.ofNat 64 (16 * l)) =
        blockAt t.mem (t.gpr src + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) + BitVec.ofNat 64 (16 * l)) ^^^
        blockAt t.mem (t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int) + BitVec.ofNat 64 (16 * l))) ∧
      (∀ l < 2, t'.lane .xmm13 l =
        t.mem.readW (t.gpr src + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128 ^^^
        t.mem.readW (t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128) ∧
      (∀ l < 2, t'.lane .xmm12 l =
        t'.mem.readW (t.gpr .rax + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128) ∧
      t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm12 → ∀ l < 2, t'.lane r l = t.lane r l) := by
  let aS := t.gpr src + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)
  let aK := t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int)
  let aD := t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)
  let aW := t.gpr .rax + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)
  let v := t.mem.readW aS 256
  let k := t.mem.readW aK 256
  let s₁ := t.setV .l256 .xmm13 (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  let s₂ := s₁.setV .l256 .xmm12 (k.extractLsb' 0 128) (k.extractLsb' 128 128)
  let s₃ := (VOp.vbin .vpxor .l256 .xmm13 .xmm13 .xmm12).exec s₂
  let s₄ := s₃.setMem (t.mem.writeW aD (s₃.ymm .xmm13))
  let w := s₄.mem.readW aW 256
  let s₅ := s₄.setV .l256 .xmm12 (w.extractLsb' 0 128) (w.extractLsb' 128 128)
  obtain l₁ : ∀ l < 2, s₁.lane .xmm13 l = t.mem.readW (aS + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [← load256_lane _ _ hl]
    rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl <;> simp [s₁, State.lane_setV256, v]
  obtain l₂ : ∀ l < 2, s₂.lane .xmm12 l = t.mem.readW (aK + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [← load256_lane _ _ hl]
    rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl <;> simp [s₂, State.lane_setV256, k]
  obtain l₂' : ∀ l < 2, s₂.lane .xmm13 l = s₁.lane .xmm13 l := fun l hl => by
    simp [s₂, State.lane_setV256]
  obtain l₃ : ∀ l < 2, s₃.lane .xmm13 l =
      t.mem.readW (aS + BitVec.ofNat 64 (16 * l)) 128 ^^^ t.mem.readW (aK + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by
      simp only [s₃, lane_vbin256, ite_true, VBinOp.sse, ← l₁ l hl, ← l₂ l hl, ← l₂' l hl, eval_pxor]
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load256, ea_atIx, hinS, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₂, by simp only [isa, exec, State.load256, ea_atIx, s₁, State.setV_gpr, State.setV_rd, State.setV_wr,
    hinK, ite_true, Option.map_some, State.setV_mem]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₃, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₄, by simp only [isa, exec, State.store256_eq, ea_atIx, s₃, s₂, s₁, VOp.exec_gpr, State.setV_gpr,
    VOp.exec_wr, State.setV_wr, VOp.exec_mem, State.setV_mem, hinD, ite_true, s₄, aD], ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₅, by simp only [isa, exec, State.load256, ea_atIx, s₄, s₃, s₂, s₁, State.setMem_gpr, State.setMem_rd,
    State.setMem_wr, VOp.exec_gpr, VOp.exec_rd, VOp.exec_wr, State.setV_gpr, State.setV_rd, State.setV_wr, hinP,
    ite_true, Option.map_some]; rfl, WP.block_nil ?_⟩
  obtain m₅ : s₅.mem = t.mem.writeW aD (s₃.ymm .xmm13) := by simp [s₅, s₄]
  refine ⟨⟨_, m₅⟩, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, by simp [s₅, s₄, s₃, s₂, s₁],
    by simp [s₅, s₄, s₃, s₂, s₁], by simp [s₅, s₄, s₃, s₂, s₁], fun r h13 h12 l hl => ?_⟩
  · rw [m₅, blockAt_writeW_lane2 _ _ _ hl, ymm_lane2 _ _ hl, l₃ l hl, pshufb_rev_xor, ← blockAt_eq, ← blockAt_eq]
  · rw [← l₃ l hl]
    simp [s₅, s₄, State.lane_setV256]
  · rw [← load256_lane _ _ hl]
    rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl <;> simp [s₅, State.lane_setV256, w, aW]
  · simp [s₅, s₄, s₃, s₂, s₁, lane_vbin256, State.lane_setV256, h13, h12]

/-- After `i` of the `r` blocks encrypted, with the products of both lanes. -/
structure RInvPE (E : REnv) (i : Nat) (t : State) : Prop where
  le : i ≤ E.r
  r10 : t.gpr .r10 = BitVec.ofNat 64 (16 * i)
  r9 : t.gpr .r9 = BitVec.ofNat 64 (16 + (E.r - i))
  gpr : ∀ q, q ≠ .r9 → q ≠ .r10 → t.gpr q = E.g q
  rd : t.rd = E.rd
  wr : t.wr = E.wr
  frame : Frame [⟨E.A, 16 * i⟩] E.m t.mem
  ct : ∀ j < i, blockAt t.mem (E.aD j) = E.X j
  prod : (prod (t.proj 0)).xor (prod (t.proj 1)) = accR E.X E.T E.y i
  y : t.lane .xmm2 0 = if i = 0 then E.y else 0
  y1 : t.lane .xmm2 1 = 0
  m0 : ∀ l < 2, t.lane .xmm0 l = revMask
  m1 : t.lane .xmm1 0 = poly

/-- `RInv` with nothing in the upper lanes of the products and `Y`. -/
theorem RInvPE.of_R {E : REnv} {i : Nat} {t : State} (hI : RInv E i t) (h8 : t.lane .xmm8 1 = 0)
    (h9 : t.lane .xmm9 1 = 0) (h10 : t.lane .xmm10 1 = 0) (y1 : t.lane .xmm2 1 = 0)
    (m0 : t.lane .xmm0 1 = revMask) : RInvPE E i t :=
  { le := hI.le, r10 := hI.r10, r9 := hI.r9, gpr := hI.gpr, rd := hI.rd, wr := hI.wr, frame := hI.frame,
    ct := hI.ct
    prod := by
      rw [← hI.prod, show Pclmul.prod (t.proj 1) = Prod.zero by
        simp only [Pclmul.prod, State.proj_xmm, h8, h9, h10]; rfl,
        xor_zero]
    y := hI.y, y1 := y1
    m0 := fun l hl => by rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl; exacts [hI.m0, m0]
    m1 := hI.m1 }

/-- Two blocks, one in each lane. -/
theorem pairStepE_ok {E : REnv} (hE : E.Ok) (h2 : Ok2 E) {i : Nat} (hi : i + 2 ≤ E.r)
    {t : State} (hI : RInvPE E i t) :
    WP isa (.block (remPairE E.src ++ remNextPair)) t fun t' =>
      RInvPE E (i + 2) t' ∧ t'.zf = some (decide (E.r - i = 2)) := by
  have r15 := hE.r15
  obtain gS : t.gpr E.src = E.S := by rw [hI.gpr _ hE.src9 hE.src10, hE.gS]
  obtain gA : t.gpr .rdx = E.A := by rw [hI.gpr _ (by decide) (by decide), hE.gA]
  obtain gP : t.gpr .r11 = E.P := by rw [hI.gpr _ (by decide) (by decide), hE.gP]
  obtain gW : t.gpr .rax = E.W := by rw [hI.gpr _ (by decide) (by decide), hE.gW]
  obtain eS : t.gpr E.src + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aS i := by rw [gS, hI.r10, addr0]
  obtain eK : t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int) = E.aK i := by rw [gP, hI.r10, addr768]
  obtain eD : t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aD i := by rw [gA, hI.r10, addr0]
  obtain eW : t.gpr .rax + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aW i := by rw [gW, hI.r10, addr0]
  rw [remPairE_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (pairMemE_ok E.src t (by rw [eS, hI.rd, hI.wr]; exact h2.inS i hi)
    (by rw [eK, hI.rd, hI.wr]; exact h2.inK i hi) (by rw [eD, hI.wr]; exact h2.inD i hi)
    (by rw [eW, hI.rd, hI.wr]; exact h2.inW i hi))
    fun t₁ ⟨⟨v, m₁⟩, b₁, x13, x12, g₁, rd₁, wr₁, k₁⟩ => ?_
  rw [eD] at m₁ b₁
  rw [eS] at b₁ x13
  rw [eK] at b₁ x13
  rw [eW] at x12
  rw [WP.block_append_iff]
  refine WP.mono (pairLanes_ok t₁ fun l hl => by rw [k₁ _ (by decide) (by decide) l hl]; exact hI.m0 l hl)
    fun t₂ ⟨kk, q₂⟩ => ?_
  refine WP.mono (remNextPair_ok t₂ (m := E.r - i) (i := i) (by omega_using [hi]) (by omega_using [r15]) (by rw [kk.gpr, g₁, hI.r9])
    (by rw [kk.gpr, g₁, hI.r10])) fun t' ⟨a10, a9, z, gg, ln, mm, rd', wr'⟩ => ⟨?_, z⟩
  obtain fA : ∀ (R : Region), R.Disjoint ⟨E.A, 16 * E.r⟩ → ∀ k ≤ E.r, ∀ r' ∈ [(⟨E.A, 16 * k⟩ : Region)],
      R.Disjoint r' := fun R hR k hk r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hR.sub_right (Region.sub_prefix (by omega_using [hk]))
  obtain F₁ : Frame [⟨E.A, 16 * (i + 2)⟩] E.m t₁.mem := by
    rw [m₁]
    exact (hI.frame.sub fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [])⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using []) (by omega_using [hi, r15]))
  obtain mt : t'.mem = t₁.mem := by rw [mm, kk.mem]
  obtain bS : ∀ l < 2, blockAt t.mem (E.S + BitVec.ofNat 64 (16 * (i + l))) = blockAt E.m (E.aS (i + l)) :=
    fun l hl => blockAt_frame hI.frame fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact hE.dS (i + l) (by omega_using [hi, hl]) i (by omega_using [])
  obtain bK : ∀ l < 2, blockAt t.mem (E.P + BitVec.ofNat 64 (768 + 16 * (i + l))) = blockAt E.m (E.aK (i + l)) :=
    fun l hl => blockAt_frame hI.frame (fA _ (hE.dK _ (by omega_using [hi, hl])) i (by omega_using [hi]))
  obtain rW : ∀ l < 2, t₁.mem.readW (E.aW (i + l)) 128 = E.T (i + l) := fun l hl =>
    F₁.readW (Region.contains_self _ _) (fA _ (hE.dW _ (by omega_using [hi, hl])) (i + 2) hi) (by decide)
  obtain P : ∀ l < 2, Pclmul.prod (t'.proj l) =
      (Pclmul.prod (t.proj l)).acc (E.X (i + l) ^^^ t.lane .xmm2 l) (E.T (i + l)) := fun l hl => by
    obtain ⟨p₂, -, -⟩ := q₂ l hl
    obtain e : Pclmul.prod (t'.proj l) = Pclmul.prod (t₂.proj l) := by simp only [Pclmul.prod, State.proj_xmm, ln]
    obtain e₁ : Pclmul.prod (t₁.proj l) = Pclmul.prod (t.proj l) := by
      simp only [Pclmul.prod, State.proj_xmm, k₁ .xmm8 (by decide) (by decide) l hl,
        k₁ .xmm9 (by decide) (by decide) l hl, k₁ .xmm10 (by decide) (by decide) l hl]
    rw [e, p₂, e₁, x13 l hl, x12 l hl, k₁ _ (by decide) (by decide) l hl, aOff, aOff, aOffK, rW l hl,
      pshufb_rev_xor, ← blockAt_eq, ← blockAt_eq, bS l hl, bK l hl]
  refine ⟨by omega_using [hi], a10, by rw [a9, show E.r - i - 2 = E.r - (i + 2) by omega_using []],
    fun q h9 h10 => by rw [gg q h9 h10, kk.gpr, g₁]; exact hI.gpr q h9 h10, by rw [rd', kk.rd, rd₁, hI.rd],
    by rw [wr', kk.wr, wr₁, hI.wr], by rw [mt]; exact F₁, fun j hj => ?_, ?_, ?_, ?_, fun l hl => ?_, ?_⟩
  · rw [mt]
    by_cases hji : j < i
    · rw [m₁, show E.aD i = (⟨E.aD i, 32⟩ : Region).base from rfl,
        blockAt_writeW_sep' (Offset.disjoint _ (.inl (by omega_using [hji])) (by omega_using [hi, r15, hj]) (by omega_using [hi, r15])) rfl]
      exact hI.ct j hji
    · obtain ⟨l, hl, rfl⟩ : ∃ l < 2, j = i + l := ⟨j - i, by omega_using [hj], by omega_using [hji]⟩
      obtain b := b₁ l hl
      rw [aOff, aOff, aOffK, bS l hl, bK l hl] at b
      exact b
  · rw [P 0 (by decide), P 1 (by decide), xor_acc_acc, hI.prod, hI.y, hI.y1]
    simp only [accR, Nat.add_zero, Nat.add_one_ne_zero, ↓reduceIte]
    rw [BitVec.xor_comm (E.X i), BitVec.xor_comm (E.X (i + 1))]
  · rw [ln, (q₂ 0 (by decide)).2.1]; exact (ite_eq_right_iff.mpr fun h => absurd h (by omega_using [])).symm
  · rw [ln, (q₂ 1 (by decide)).2.1]
  · rw [ln, (q₂ l hl).2.2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₁ _ (by decide) (by decide) l hl]
    exact hI.m0 l hl
  · rw [ln, (q₂ 0 (by decide)).2.2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₁ _ (by decide) (by decide) 0 (by decide)]
    exact hI.m1

/-- The pairs, while two or more blocks are left. -/
theorem pairLoopE_ok {E : REnv} (hE : E.Ok) (h2 : Ok2 E) {i : Nat} (hi : i + 2 ≤ E.r)
    (hev : (E.r - i) % 2 = 0) {t : State} (hI : RInvPE E i t) :
    WP isa (.loop (.block (remPairE E.src ++ remNextPair)) .ne) t (RInvPE E E.r) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = E.r - j ∧ j + 2 ≤ E.r ∧ (E.r - j) % 2 = 0 ∧ RInvPE E j s) ?_
    (E.r - i) t ⟨i, rfl, hi, hev, hI⟩
  rintro n s ⟨j, rfl, hj, hjev, hIs⟩
  refine WP.mono (pairStepE_ok hE h2 hj hIs) fun s' ⟨hI', hz⟩ => ?_
  by_cases h1 : E.r - j = 2
  · refine .inl ⟨by simp only [eval, hz, h1, decide_true, Option.map_some, Bool.not_true], ?_⟩
    rwa [show E.r = j + 2 by omega_using [h1]]
  · exact .inr ⟨by simp only [eval, hz, h1, decide_false, Option.map_some, Bool.not_false], E.r - (j + 2),
      by omega_using [hj], j + 2, rfl, by omega_using [hj, hjev, h1], by omega_using [hjev], hI'⟩

/-- The first block alone (for odd `r`), in the lower lanes, leaving the
upper lanes of the products and `Y` clear. -/
theorem oddStepE_ok {E : REnv} (hE : E.Ok) {t : State} (hI : RInv E 0 t) (h8 : t.lane .xmm8 1 = 0)
    (h9 : t.lane .xmm9 1 = 0) (h10 : t.lane .xmm10 1 = 0) (y1 : t.lane .xmm2 1 = 0)
    (m0 : t.lane .xmm0 1 = revMask) :
    WP isa (.block (remBody E.src ++ remNext)) t fun t' =>
      RInvPE E 1 t' ∧ RInv E 1 t' ∧ t'.zf = some (decide (E.r = 1)) := by
  refine WP.mono (wp_and_run (remStep_ok hE hE.r1 hI) (R := fun t' => t'.lane .xmm8 1 = 0 ∧
      t'.lane .xmm9 1 = 0 ∧ t'.lane .xmm10 1 = 0 ∧ t'.lane .xmm2 1 = 0 ∧ t'.lane .xmm0 1 = revMask)
      fun t' e => ?_) fun t' ⟨⟨hI', hz⟩, a8, a9, a10, a2, a0⟩ =>
    ⟨RInvPE.of_R hI' a8 a9 a10 a2 a0, hI', by rw [hz, Nat.sub_zero]⟩
  rw [runBlock_append] at e
  cases e₁ : runBlock isa (remBody E.src) t with
  | none => rw [e₁] at e; cases e
  | some t₁ =>
    rw [e₁, Option.bind_some] at e
    obtain nl := remNext_lanes e
    obtain z : ∀ r, t.lane r 1 = 0 → t'.lane r 1 = 0 := fun r h => by
      rw [nl, ← State.zlane_lt2 _ _ (by decide)]
      exact lane0Block_zhi (lane0_remBody _) e₁ r (by decide) (by decide)
        (by rw [State.zlane_lt2 _ _ (by decide)]; exact h)
    refine ⟨z _ h8, z _ h9, z _ h10, z _ y1, ?_⟩
    rw [nl, ← State.zlane_lt2 _ _ (by decide),
      lane0Block_zkeep (lane0_remBody _) e₁ _ (remBody_dst _ _ (by decide)) (by decide),
      State.zlane_lt2 _ _ (by decide)]
    exact m0

/-- The products of both lanes added into the lower lanes: `RInv`. -/
theorem foldLanesE_ok {E : REnv} {i : Nat} {t : State} (hI : RInvPE E i t) :
    WP isa (.block foldLanes) t (RInv E i) :=
  WP.mono (foldLanes_run t) fun t' ⟨a8, a9, a10, k, g, m, rd, wr⟩ =>
    { le := hI.le, r10 := by rw [g]; exact hI.r10, r9 := by rw [g]; exact hI.r9
      gpr := fun q h9 h10 => by rw [g]; exact hI.gpr q h9 h10
      rd := by rw [rd]; exact hI.rd, wr := by rw [wr]; exact hI.wr
      frame := by rw [m]; exact hI.frame
      ct := fun j hj => by rw [m]; exact hI.ct j hj
      prod := by
        rw [← hI.prod]
        simp only [Pclmul.prod, State.proj_xmm, a8, a9, a10, Prod.xor]
      y := by rw [k _ (by decide) (by decide) (by decide) (by decide)]; exact hI.y
      m0 := by rw [k _ (by decide) (by decide) (by decide) (by decide)]; exact hI.m0 0 (by decide)
      m1 := by rw [k _ (by decide) (by decide) (by decide) (by decide)]; exact hI.m1 }

/-- `RInv` holds of a state with the same registers, memory and lanes. -/
theorem rinv_keep {E : REnv} {i : Nat} {t t' : State} (hI : RInv E i t) (g : t'.gpr = t.gpr)
    (m : t'.mem = t.mem) (rd : t'.rd = t.rd) (wr : t'.wr = t.wr) (l : ∀ x k, t'.lane x k = t.lane x k) :
    RInv E i t' :=
  { le := hI.le, r10 := by rw [g]; exact hI.r10, r9 := by rw [g]; exact hI.r9
    gpr := fun q h9 h10 => by rw [g]; exact hI.gpr q h9 h10
    rd := by rw [rd]; exact hI.rd, wr := by rw [wr]; exact hI.wr
    frame := by rw [m]; exact hI.frame
    ct := fun j hj => by rw [m]; exact hI.ct j hj
    prod := by simp only [Pclmul.prod, State.proj_xmm, l]; exact hI.prod
    y := by rw [l]; exact hI.y, m0 := by rw [l]; exact hI.m0, m1 := by rw [l]; exact hI.m1 }

/-- The first block alone if `r` is odd, then the pairs and their lanes
added: what `remE` does between clearing the products and reducing them. -/
theorem remMidE_ok {E : REnv} (hE : E.Ok) (h2 : Ok2 E) {t : State} (hI : RInv E 0 t)
    (h8 : t.lane .xmm8 1 = 0) (h9 : t.lane .xmm9 1 = 0) (h10 : t.lane .xmm10 1 = 0) (y1 : t.lane .xmm2 1 = 0)
    (m0 : t.lane .xmm0 1 = revMask) {X : Prog isa} {Q : State → Prop} (hX : ∀ s, RInv E E.r s → WP isa X s Q) :
    WP isa (.block [.alu .test .r9 (.imm 1)]) t fun s =>
      WP isa (.seq (.ite .e (.block [.alu .cmp .r9 (.imm 16)]) (.block (remBody E.src ++ remNext)))
        (.seq (.ite .e (.block []) (.seq (.loop (.block (remPairE E.src ++ remNextPair)) .ne) (.block foldLanes)))
          X)) s Q := by
  have r1 := hE.r1
  have r15 := hE.r15
  -- After the first ite: `i` blocks done, `i ≤ 1`, an even number left, and `zf` whether none are.
  obtain hlast : ∀ s, (∃ i, i ≤ 1 ∧ (E.r - i) % 2 = 0 ∧ RInvPE E i s ∧ (E.r = i → RInv E i s) ∧
      s.zf = some (decide (E.r = i))) →
      WP isa (.seq (.ite .e (.block []) (.seq (.loop (.block (remPairE E.src ++ remNextPair)) .ne)
        (.block foldLanes))) X) s Q := by
    rintro s ⟨i, hi1, hev, hIs, hD, hz⟩
    refine WP.seq (WP.ite (decide (E.r = i)) (by simp only [eval, hz]) (fun h => ?_) (fun h => ?_))
    · have h' : E.r = i := by simpa using h
      refine WP.block_nil (hX s ?_)
      rw [h']; exact hD h'
    · exact WP.seq (WP.mono (pairLoopE_ok hE h2 (by simp at h; omega_using [r1, hi1, hev, h]) hev hIs) fun s' hP =>
        WP.mono (foldLanesE_ok hP) hX)
  refine WP.mono (test91_ok t) fun t₁ ⟨z₁, g₁, l₁, m₁, rd₁, wr₁⟩ => ?_
  obtain hI₁ := rinv_keep hI g₁ m₁ rd₁ wr₁ l₁
  rw [hI.r9, Nat.sub_zero, parity16 _ (by omega_using [r15])] at z₁
  refine WP.seq (WP.ite (decide (E.r % 2 = 0)) (by simp only [eval, z₁]) (fun h => ?_) (fun h => ?_))
  · refine WP.mono (cmp916_ok t₁) fun t₂ ⟨z₂, g₂, l₂, m₂, rd₂, wr₂⟩ =>
      hlast t₂ ⟨0, by omega_using [], by simpa using h, ?_, fun h0 => absurd h0 (by omega_using [r1]), ?_⟩
    · exact RInvPE.of_R (rinv_keep hI₁ g₂ m₂ rd₂ wr₂ l₂) (by rw [l₂, l₁]; exact h8) (by rw [l₂, l₁]; exact h9)
        (by rw [l₂, l₁]; exact h10) (by rw [l₂, l₁]; exact y1) (by rw [l₂, l₁]; exact m0)
    · rw [z₂, g₁, hI.r9, Nat.sub_zero, zero16 _ (by omega_using [r15])]
  · exact WP.mono (oddStepE_ok (E := E) hE hI₁ (by rw [l₁]; exact h8) (by rw [l₁]; exact h9)
      (by rw [l₁]; exact h10) (by rw [l₁]; exact y1) (by rw [l₁]; exact m0))
      fun t₂ ⟨hP₂, hD₂, z₂⟩ => hlast t₂ ⟨1, Nat.le_refl _, by simp at h; omega_using [h], hP₂, fun _ => hD₂, z₂⟩

/-! ## The powers read from the key context

`StitchR.remE` reads the power of block `j` of the `r` at `REnv.aC j`:
`W + 16 (r - j)`, or `32` more if `r - j` is odd, `W` being `rdi + 224`, where
the prepared pairs of the key context put them. It reads it at `rax + r10`,
with `rax` moved around each step so that `rax + r10 = W + 16 (r - i)` once
`i` blocks are done (`RInvC.ax`): `32` more for a first block alone
(`remOneC`), and `64` less after each step. -/

/-- Where `remE` reads the power of block `j`. -/
abbrev _root_.VG.Proof.Gcm.X86_64.StitchZH.REnv.aC (E : REnv) (j : Nat) : Addr :=
  E.W + BitVec.ofNat 64 (16 * (E.r - j) + 32 * ((E.r - j) % 2))

/-- That power. -/
abbrev _root_.VG.Proof.Gcm.X86_64.StitchZH.REnv.TC (E : REnv) (j : Nat) : BitVec 128 := E.m.readW (E.aC j) 128

/-- `REnv.Ok` and `Ok2`, with the powers at `aC` and `rax` at `W + 16 r`. -/
structure OkC (E : REnv) : Prop where
  r1 : 1 ≤ E.r
  r15 : E.r ≤ 15
  gS : E.g E.src = E.S
  gA : E.g .rdx = E.A
  gP : E.g .r11 = E.P
  gW : E.g .rax = E.W + BitVec.ofNat 64 (16 * E.r)
  src9 : E.src ≠ .r9
  src10 : E.src ≠ .r10
  srcA : E.src ≠ .rax
  inS : ∀ j < E.r, InRegions (E.rd ++ E.wr) (E.aS j) 16
  inK : ∀ j < E.r, InRegions (E.rd ++ E.wr) (E.aK j) 16
  inD : ∀ j < E.r, InRegions E.wr (E.aD j) 16
  inW : ∀ j < E.r, InRegions (E.rd ++ E.wr) (E.aC j) 16
  dS : ∀ j < E.r, ∀ i ≤ j, Region.Disjoint ⟨E.aS j, 16⟩ ⟨E.A, 16 * i⟩
  dK : ∀ j < E.r, Region.Disjoint ⟨E.aK j, 16⟩ ⟨E.A, 16 * E.r⟩
  dW : ∀ j < E.r, Region.Disjoint ⟨E.aC j, 16⟩ ⟨E.A, 16 * E.r⟩
  inS2 : ∀ j, j + 2 ≤ E.r → InRegions (E.rd ++ E.wr) (E.aS j) 32
  inK2 : ∀ j, j + 2 ≤ E.r → InRegions (E.rd ++ E.wr) (E.aK j) 32
  inD2 : ∀ j, j + 2 ≤ E.r → InRegions E.wr (E.aD j) 32
  inW2 : ∀ j, j + 2 ≤ E.r → (E.r - j) % 2 = 0 → InRegions (E.rd ++ E.wr) (E.aC j) 32

/-- `RInv`, with `rax` moved and the powers at `aC`, the blocks hashed being
`V` (`E.X`, the ciphertext written, for encryption; `E.H`, the blocks as read,
for decryption). -/
structure RInvC (E : REnv) (V : Nat → Block) (i : Nat) (t : State) : Prop where
  le : i ≤ E.r
  r10 : t.gpr .r10 = BitVec.ofNat 64 (16 * i)
  r9 : t.gpr .r9 = BitVec.ofNat 64 (16 + (E.r - i))
  ax : t.gpr .rax + t.gpr .r10 = E.W + BitVec.ofNat 64 (16 * (E.r - i))
  gpr : ∀ q, q ≠ .r9 → q ≠ .r10 → q ≠ .rax → t.gpr q = E.g q
  rd : t.rd = E.rd
  wr : t.wr = E.wr
  frame : Frame [⟨E.A, 16 * i⟩] E.m t.mem
  ct : ∀ j < i, blockAt t.mem (E.aD j) = E.X j
  prod : prod (t.proj 0) = accR V E.TC E.y i
  y : t.lane .xmm2 0 = if i = 0 then E.y else 0
  m0 : t.lane .xmm0 0 = revMask
  m1 : t.lane .xmm1 0 = poly

/-- `RInvPE`, with `rax` moved and the powers at `aC`. -/
structure RInvPC (E : REnv) (V : Nat → Block) (i : Nat) (t : State) : Prop where
  le : i ≤ E.r
  r10 : t.gpr .r10 = BitVec.ofNat 64 (16 * i)
  r9 : t.gpr .r9 = BitVec.ofNat 64 (16 + (E.r - i))
  ax : t.gpr .rax + t.gpr .r10 = E.W + BitVec.ofNat 64 (16 * (E.r - i))
  gpr : ∀ q, q ≠ .r9 → q ≠ .r10 → q ≠ .rax → t.gpr q = E.g q
  rd : t.rd = E.rd
  wr : t.wr = E.wr
  frame : Frame [⟨E.A, 16 * i⟩] E.m t.mem
  ct : ∀ j < i, blockAt t.mem (E.aD j) = E.X j
  prod : (prod (t.proj 0)).xor (prod (t.proj 1)) = accR V E.TC E.y i
  y : t.lane .xmm2 0 = if i = 0 then E.y else 0
  y1 : t.lane .xmm2 1 = 0
  m0 : ∀ l < 2, t.lane .xmm0 l = revMask
  m1 : t.lane .xmm1 0 = poly

theorem RInvPC.of_C {E : REnv} {V : Nat → Block} {i : Nat} {t : State} (hI : RInvC E V i t)
    (h8 : t.lane .xmm8 1 = 0) (h9 : t.lane .xmm9 1 = 0) (h10 : t.lane .xmm10 1 = 0) (y1 : t.lane .xmm2 1 = 0)
    (m0 : t.lane .xmm0 1 = revMask) : RInvPC E V i t :=
  { le := hI.le, r10 := hI.r10, r9 := hI.r9, ax := hI.ax, gpr := hI.gpr, rd := hI.rd, wr := hI.wr,
    frame := hI.frame, ct := hI.ct
    prod := by
      rw [← hI.prod, show Pclmul.prod (t.proj 1) = Prod.zero by
        simp only [Pclmul.prod, State.proj_xmm, h8, h9, h10]; rfl,
        xor_zero]
    y := hI.y, y1 := y1
    m0 := fun l hl => by rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl; exacts [hI.m0, m0]
    m1 := hI.m1 }

theorem rax_one (W x : BitVec 64) : W + x + BitVec.ofNat 64 32 - BitVec.ofNat 64 64 + BitVec.ofNat 64 16 =
    W + (x - BitVec.ofNat 64 16) := by bv_omega

theorem rax_pair {a b c : BitVec 64} (h : a + b = c + BitVec.ofNat 64 32) :
    a - BitVec.ofNat 64 64 + b + BitVec.ofNat 64 32 = c := by bv_omega

/-- `add rax, 32`. -/
theorem addRax32_ok (s : State) :
    WP isa (.block [.alu .add .rax (.imm 32)]) s fun s' =>
      s'.gpr .rax = s.gpr .rax + BitVec.ofNat 64 32 ∧ (∀ q, q ≠ .rax → s'.gpr q = s.gpr q) ∧
      (∀ x l, s'.lane x l = s.lane x l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain e : BitVec.signExtend 64 (32 : BitVec 32) = BitVec.ofNat 64 32 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    State.setReg, e, ↓reduceIte, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩

/-- `sub rax, 64`. -/
theorem subRax64_ok (s : State) :
    WP isa (.block [.alu .sub .rax (.imm 64)]) s fun s' =>
      s'.gpr .rax = s.gpr .rax - BitVec.ofNat 64 64 ∧ (∀ q, q ≠ .rax → s'.gpr q = s.gpr q) ∧
      (∀ x l, s'.lane x l = s.lane x l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain e : BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    State.setReg, e, ↓reduceIte, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩

/-- The pair of blocks `i` and `i + 1` (`r - i` even) reads its powers at
`W + 16 (r - i)`: block `i`'s, and 16 bytes on, block `i + 1`'s. -/
theorem aC_pair (E : REnv) {i l : Nat} (hi : i + 2 ≤ E.r) (h : (E.r - i) % 2 = 0) (hl : l < 2) :
    E.W + BitVec.ofNat 64 (16 * (E.r - i)) + BitVec.ofNat 64 (16 * l) = E.aC (i + l) := by
  rw [Offset.add_add]
  rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
  · simp only [StitchZH.REnv.aC, Nat.add_zero, h, Nat.mul_zero]
  · have h1 : (E.r - (i + 1)) % 2 = 1 := by omega_using [hi, h]
    simp only [StitchZH.REnv.aC, h1]
    congr 2; omega_using [hi]

/-- A first block alone (`r` odd) reads its power at `W + 16 r + 32`. -/
theorem aC_first (E : REnv) (h : E.r % 2 = 1) :
    E.W + BitVec.ofNat 64 (16 * E.r) + BitVec.ofNat 64 32 = E.aC 0 := by
  rw [Offset.add_add]; simp only [StitchZH.REnv.aC, Nat.sub_zero, h]

/-- The first block alone, for odd `r`, in the lower lanes: `rax` moved up
for its power and down for the pairs after it. -/
theorem oneStepC_ok {E : REnv} (hE : OkC E) (hodd : E.r % 2 = 1) {t : State} (hI : RInvC E E.X 0 t) :
    WP isa (.block (Impl.Gcm.X86_64.StitchR.remOneC E.src)) t fun t' =>
      RInvC E E.X 1 t' ∧ t'.zf = some (decide (E.r = 1)) ∧
      (∀ x, t.lane x 1 = 0 → x ≠ .xmm0 → t'.lane x 1 = 0) ∧ t'.lane .xmm0 1 = t.lane .xmm0 1 := by
  have r15 := hE.r15
  have r1 := hE.r1
  have h0 : (0 : Nat) < E.r := r1
  obtain gS : t.gpr E.src = E.S := by rw [hI.gpr _ hE.src9 hE.src10 hE.srcA, hE.gS]
  obtain gA : t.gpr .rdx = E.A := by rw [hI.gpr _ (by decide) (by decide) (by decide), hE.gA]
  obtain gP : t.gpr .r11 = E.P := by rw [hI.gpr _ (by decide) (by decide) (by decide), hE.gP]
  have r10z : t.gpr .r10 = BitVec.ofNat 64 (16 * 0) := hI.r10
  obtain ax0 : t.gpr .rax = E.W + BitVec.ofNat 64 (16 * E.r) := by
    obtain h := hI.ax; rw [r10z, Nat.sub_zero] at h; rw [← h]; exact (BitVec.add_zero _).symm
  simp only [Impl.Gcm.X86_64.StitchR.remOneC, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (addRax32_ok t) fun t₀ ⟨a₀, g₀, l₀, m₀, rd₀, wr₀⟩ => ?_
  obtain eS : t₀.gpr E.src + t₀.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aS 0 := by
    rw [g₀ _ hE.srcA, g₀ _ (by decide), gS, r10z, addr0]
  obtain eK : t₀.gpr .r11 + t₀.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int) = E.aK 0 := by
    rw [g₀ _ (by decide), g₀ _ (by decide), gP, r10z, addr768]
  obtain eD : t₀.gpr .rdx + t₀.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aD 0 := by
    rw [g₀ _ (by decide), g₀ _ (by decide), gA, r10z, addr0]
  obtain eW : t₀.gpr .rax + t₀.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aC 0 := by
    rw [a₀, g₀ _ (by decide), r10z, ax0, ← aC_first E hodd, BitVec.ofInt_natCast, Nat.mul_zero]
    exact BitVec.add_zero _ ▸ BitVec.add_zero _
  obtain dD : Region.Sub ⟨E.aD 0, 16⟩ ⟨E.A, 16 * E.r⟩ := Offset.sub_base _ (by omega_using [r1])
  obtain sDW : Mem.Sep (E.aD 0) 16 (E.aC 0) 16 :=
    ((hE.dW 0 h0).symm.sub_left dD).sep (Region.contains_self _ _) (Region.contains_self _ _)
  obtain fA : ∀ (R : Region), R.Disjoint ⟨E.A, 16 * E.r⟩ → ∀ r' ∈ [(⟨E.A, 16 * 0⟩ : Region)], R.Disjoint r' :=
    fun R hR r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hR.sub_right (Region.sub_prefix (by omega_using []))
  obtain bS : blockAt t.mem (E.aS 0) = blockAt E.m (E.aS 0) := blockAt_frame hI.frame fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hE.dS 0 h0 0 (Nat.le_refl _)
  obtain bK : blockAt t.mem (E.aK 0) = blockAt E.m (E.aK 0) := blockAt_frame hI.frame (fA _ (hE.dK 0 h0))
  obtain rW : t.mem.readW (E.aC 0) 128 = E.TC 0 :=
    hI.frame.readW (Region.contains_self _ _) (fA _ (hE.dW 0 h0)) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (wp_and_run (StitchZH.remBody_ok E.src t₀ (by rw [l₀]; exact hI.m0)
    (by rw [eS, rd₀, wr₀, hI.rd, hI.wr]; exact hE.inS 0 h0)
    (by rw [eK, rd₀, wr₀, hI.rd, hI.wr]; exact hE.inK 0 h0) (by rw [eD, wr₀, hI.wr]; exact hE.inD 0 h0)
    (by rw [eW, rd₀, wr₀, hI.rd, hI.wr]; exact hE.inW 0 h0) (by rw [eD, eW]; exact sDW))
    (R := fun t₁ => (∀ x, t₀.lane x 1 = 0 → x ≠ .xmm0 → t₁.lane x 1 = 0) ∧ t₁.lane .xmm0 1 = t₀.lane .xmm0 1)
    fun t₁ e₁ => ⟨fun x hx _ => by
        rw [← State.zlane_lt2 _ _ (by decide)]
        exact lane0Block_zhi (lane0_remBody _) e₁ x (by decide) (by decide)
          (by rw [State.zlane_lt2 _ _ (by decide)]; exact hx),
      by rw [← State.zlane_lt2 _ _ (by decide),
          lane0Block_zkeep (lane0_remBody _) e₁ _ (remBody_dst _ _ (by decide)) (by decide),
          State.zlane_lt2 _ _ (by decide)]⟩)
    fun t₁ ⟨⟨m₁, p₁, y₁, g₁, rd₁, wr₁, k₁⟩, z₁, x₁⟩ => ?_
  rw [eD, eS, eK] at m₁
  rw [eS, eK, eW] at p₁
  have hm₀ : t₀.mem = t.mem := m₀
  rw [hm₀] at m₁ p₁
  obtain hX : XBinOp.eval .pshufb (t.mem.readW (E.aS 0) 128 ^^^ t.mem.readW (E.aK 0) 128) revMask = E.X 0 := by
    rw [pshufb_rev_xor, ← blockAt_eq, ← blockAt_eq, bS, bK]
  rw [WP.block_append_iff]
  refine WP.mono (subRax64_ok t₁) fun t₂ ⟨a₂, g₂, l₂, m₂, rd₂, wr₂⟩ => ?_
  refine WP.mono (StitchZH.remNext_ok t₂ (m := E.r - 0) (i := 0) (by omega_using [r1]) (by omega_using [r15])
    (by rw [g₂ _ (by decide), g₁, g₀ _ (by decide), hI.r9])
    (by rw [g₂ _ (by decide), g₁, g₀ _ (by decide), hI.r10])) fun t' ⟨a10, a9, z, gg, ln, mm, rd', wr'⟩ => ?_
  obtain m' : t'.mem = t.mem.writeW (E.aD 0) (t.mem.readW (E.aS 0) 128 ^^^ t.mem.readW (E.aK 0) 128) := by
    rw [mm, m₂, m₁]
  refine ⟨⟨by omega_using [r1], a10, by rw [a9, show E.r - 0 - 1 = E.r - (0 + 1) by omega_using []], ?_,
    fun q h9 h10 hax => by rw [gg q h9 h10, g₂ q hax, g₁, g₀ q hax]; exact hI.gpr q h9 h10 hax,
    by rw [rd', rd₂, rd₁, rd₀, hI.rd], by rw [wr', wr₂, wr₁, wr₀, hI.wr], ?_, fun j hj => ?_, ?_, ?_, ?_, ?_⟩,
    by rw [z, Nat.sub_zero], fun x hx h0x => by rw [ln, l₂]; exact z₁ x (by rw [l₀]; exact hx) h0x,
    by rw [ln, l₂, x₁, l₀]⟩
  · rw [gg _ (by decide) (by decide), a10, a₂, g₁, a₀, ax0]
    rw [show 16 * (E.r - (0 + 1)) = 16 * E.r - 16 by omega_using []]
    have : 16 ≤ 16 * E.r := by omega_using [r1]
    obtain hw : 16 * E.r < 2 ^ 64 := by omega_using [r15]
    rw [← Offset.ofNat_sub_ofNat this, Nat.zero_add, Nat.mul_one]
    exact rax_one _ _
  · rw [m']
    exact (hI.frame.sub fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [])⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using []) (by omega_using [r1, r15]))
  · rw [m']
    obtain rfl : j = 0 := by omega_using [hj]
    rw [blockAt_eq, Mem.readW_writeW_self _ _ 16 _ (by decide), hX]
  · have e : prod (t'.proj 0) = prod (t₁.proj 0) := by simp only [prod, State.proj_xmm, ln, l₂]
    rw [e, p₁, show prod (t₀.proj 0) = prod (t.proj 0) by simp only [prod, State.proj_xmm, l₀], hI.prod, hX,
      rW, show t₀.lane .xmm2 0 = t.lane .xmm2 0 from l₀ _ _, hI.y]
    simp only [accR]
    rw [BitVec.xor_comm]
  · rw [ln, l₂, y₁]; simp only [Nat.add_one_ne_zero, ↓reduceIte]
  · rw [ln, l₂, k₁ _ (by decide), l₀]; exact hI.m0
  · rw [ln, l₂, k₁ _ (by decide), l₀]; exact hI.m1

/-- Two blocks, one in each lane, then `rax` moved down for the next pair. -/
theorem pairStepC_ok {E : REnv} (hE : OkC E) {i : Nat} (hi : i + 2 ≤ E.r) (hev : (E.r - i) % 2 = 0)
    {t : State} (hI : RInvPC E E.X i t) :
    WP isa (.block (remPairE E.src ++ ([.alu .sub .rax (.imm 64)] : List Instr) ++ remNextPair)) t fun t' =>
      RInvPC E E.X (i + 2) t' ∧ t'.zf = some (decide (E.r - i = 2)) := by
  have r15 := hE.r15
  obtain gS : t.gpr E.src = E.S := by rw [hI.gpr _ hE.src9 hE.src10 hE.srcA, hE.gS]
  obtain gA : t.gpr .rdx = E.A := by rw [hI.gpr _ (by decide) (by decide) (by decide), hE.gA]
  obtain gP : t.gpr .r11 = E.P := by rw [hI.gpr _ (by decide) (by decide) (by decide), hE.gP]
  obtain eS : t.gpr E.src + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aS i := by rw [gS, hI.r10, addr0]
  obtain eK : t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int) = E.aK i := by rw [gP, hI.r10, addr768]
  obtain eD : t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aD i := by rw [gA, hI.r10, addr0]
  obtain eW : t.gpr .rax + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.W + BitVec.ofNat 64 (16 * (E.r - i)) := by
    rw [hI.ax, BitVec.ofInt_natCast]; exact BitVec.add_zero _
  obtain eW0 : E.W + BitVec.ofNat 64 (16 * (E.r - i)) = E.aC i := by
    have := aC_pair E hi hev (show 0 < 2 by decide); rwa [Nat.mul_zero, show BitVec.ofNat 64 0 = 0#64 from rfl,
      BitVec.add_zero, Nat.add_zero] at this
  rw [List.append_assoc, remPairE_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (pairMemE_ok E.src t (by rw [eS, hI.rd, hI.wr]; exact hE.inS2 i hi)
    (by rw [eK, hI.rd, hI.wr]; exact hE.inK2 i hi) (by rw [eD, hI.wr]; exact hE.inD2 i hi)
    (by rw [eW, eW0, hI.rd, hI.wr]; exact hE.inW2 i hi hev))
    fun t₁ ⟨⟨v, m₁⟩, b₁, x13, x12, g₁, rd₁, wr₁, k₁⟩ => ?_
  rw [eD] at m₁ b₁
  rw [eS] at b₁ x13
  rw [eK] at b₁ x13
  rw [eW] at x12
  rw [WP.block_append_iff]
  refine WP.mono (pairLanes_ok t₁ fun l hl => by rw [k₁ _ (by decide) (by decide) l hl]; exact hI.m0 l hl)
    fun t₂ ⟨kk, q₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subRax64_ok t₂) fun t₃ ⟨a₃, g₃, l₃, m₃, rd₃, wr₃⟩ => ?_
  refine WP.mono (remNextPair_ok t₃ (m := E.r - i) (i := i) (by omega_using [hi]) (by omega_using [r15])
    (by rw [g₃ _ (by decide), kk.gpr, g₁, hI.r9]) (by rw [g₃ _ (by decide), kk.gpr, g₁, hI.r10]))
    fun t' ⟨a10, a9, z, gg, ln, mm, rd', wr'⟩ => ⟨?_, z⟩
  obtain fA : ∀ (R : Region), R.Disjoint ⟨E.A, 16 * E.r⟩ → ∀ k ≤ E.r, ∀ r' ∈ [(⟨E.A, 16 * k⟩ : Region)],
      R.Disjoint r' := fun R hR k hk r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hR.sub_right (Region.sub_prefix (by omega_using [hk]))
  obtain F₁ : Frame [⟨E.A, 16 * (i + 2)⟩] E.m t₁.mem := by
    rw [m₁]
    exact (hI.frame.sub fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [])⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using []) (by omega_using [hi, r15]))
  obtain mt : t'.mem = t₁.mem := by rw [mm, m₃, kk.mem]
  obtain bS : ∀ l < 2, blockAt t.mem (E.S + BitVec.ofNat 64 (16 * (i + l))) = blockAt E.m (E.aS (i + l)) :=
    fun l hl => blockAt_frame hI.frame fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact hE.dS (i + l) (by omega_using [hi, hl]) i (by omega_using [])
  obtain bK : ∀ l < 2, blockAt t.mem (E.P + BitVec.ofNat 64 (768 + 16 * (i + l))) = blockAt E.m (E.aK (i + l)) :=
    fun l hl => blockAt_frame hI.frame (fA _ (hE.dK _ (by omega_using [hi, hl])) i (by omega_using [hi]))
  obtain rW : ∀ l < 2, t₁.mem.readW (E.aC (i + l)) 128 = E.TC (i + l) := fun l hl =>
    F₁.readW (Region.contains_self _ _) (fA _ (hE.dW _ (by omega_using [hi, hl])) (i + 2) hi) (by decide)
  obtain P : ∀ l < 2, Pclmul.prod (t'.proj l) =
      (Pclmul.prod (t.proj l)).acc (E.X (i + l) ^^^ t.lane .xmm2 l) (E.TC (i + l)) := fun l hl => by
    obtain ⟨p₂, -, -⟩ := q₂ l hl
    obtain e : Pclmul.prod (t'.proj l) = Pclmul.prod (t₂.proj l) := by simp only [Pclmul.prod, State.proj_xmm, ln, l₃]
    obtain e₁ : Pclmul.prod (t₁.proj l) = Pclmul.prod (t.proj l) := by
      simp only [Pclmul.prod, State.proj_xmm, k₁ .xmm8 (by decide) (by decide) l hl,
        k₁ .xmm9 (by decide) (by decide) l hl, k₁ .xmm10 (by decide) (by decide) l hl]
    rw [e, p₂, e₁, x13 l hl, x12 l hl, k₁ _ (by decide) (by decide) l hl, aOff, aOffK, aC_pair E hi hev hl, rW l hl,
      pshufb_rev_xor, ← blockAt_eq, ← blockAt_eq, bS l hl, bK l hl]
  refine ⟨by omega_using [hi], a10, by rw [a9, show E.r - i - 2 = E.r - (i + 2) by omega_using []], ?_,
    fun q h9 h10 hax => by rw [gg q h9 h10, g₃ q hax, kk.gpr, g₁]; exact hI.gpr q h9 h10 hax,
    by rw [rd', rd₃, kk.rd, rd₁, hI.rd],
    by rw [wr', wr₃, kk.wr, wr₁, hI.wr], by rw [mt]; exact F₁, fun j hj => ?_, ?_, ?_, ?_, fun l hl => ?_, ?_⟩
  · have hax : t.gpr .rax + t.gpr .r10 = E.W + BitVec.ofNat 64 (16 * (E.r - i)) := hI.ax
    rw [gg _ (by decide) (by decide), a10, a₃, kk.gpr, g₁]
    rw [hI.r10] at hax
    obtain h32 : 16 * (E.r - (i + 2)) + 32 = 16 * (E.r - i) := by omega_using [hi]
    rw [← h32, ← Offset.add_add] at hax
    rw [show 16 * (i + 2) = 16 * i + 32 by omega_using [], ← Offset.add_add]
    exact rax_pair hax
  · rw [mt]
    by_cases hji : j < i
    · rw [m₁, show E.aD i = (⟨E.aD i, 32⟩ : Region).base from rfl,
        blockAt_writeW_sep' (Offset.disjoint _ (.inl (by omega_using [hji])) (by omega_using [hi, r15, hj]) (by omega_using [hi, r15])) rfl]
      exact hI.ct j hji
    · obtain ⟨l, hl, rfl⟩ : ∃ l < 2, j = i + l := ⟨j - i, by omega_using [hj], by omega_using [hji]⟩
      obtain b := b₁ l hl
      rw [aOff, aOff, aOffK, bS l hl, bK l hl] at b
      exact b
  · rw [P 0 (by decide), P 1 (by decide), xor_acc_acc, hI.prod, hI.y, hI.y1]
    simp only [accR, Nat.add_zero, Nat.add_one_ne_zero, ↓reduceIte]
    rw [BitVec.xor_comm (E.X i), BitVec.xor_comm (E.X (i + 1))]
  · rw [ln, l₃, (q₂ 0 (by decide)).2.1]; exact (ite_eq_right_iff.mpr fun h => absurd h (by omega_using [])).symm
  · rw [ln, l₃, (q₂ 1 (by decide)).2.1]
  · rw [ln, l₃, (q₂ l hl).2.2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₁ _ (by decide) (by decide) l hl]
    exact hI.m0 l hl
  · rw [ln, l₃, (q₂ 0 (by decide)).2.2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₁ _ (by decide) (by decide) 0 (by decide)]
    exact hI.m1

/-- The pairs, while two or more blocks are left, for any step `pair` that
does two. -/
theorem pairLoopG_ok {E : REnv} {V : Nat → Block} {pair : List Instr}
    (hstep : ∀ i, i + 2 ≤ E.r → (E.r - i) % 2 = 0 → ∀ t, RInvPC E V i t →
      WP isa (.block pair) t fun t' => RInvPC E V (i + 2) t' ∧ t'.zf = some (decide (E.r - i = 2)))
    {i : Nat} (hi : i + 2 ≤ E.r) (hev : (E.r - i) % 2 = 0) {t : State} (hI : RInvPC E V i t) :
    WP isa (.loop (.block pair) .ne) t (RInvPC E V E.r) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = E.r - j ∧ j + 2 ≤ E.r ∧ (E.r - j) % 2 = 0 ∧ RInvPC E V j s) ?_
    (E.r - i) t ⟨i, rfl, hi, hev, hI⟩
  rintro n s ⟨j, rfl, hj, hjev, hIs⟩
  refine WP.mono (hstep j hj hjev s hIs) fun s' ⟨hI', hz⟩ => ?_
  by_cases h1 : E.r - j = 2
  · refine .inl ⟨by simp only [eval, hz, h1, decide_true, Option.map_some, Bool.not_true], ?_⟩
    rwa [show E.r = j + 2 by omega_using [h1]]
  · exact .inr ⟨by simp only [eval, hz, h1, decide_false, Option.map_some, Bool.not_false], E.r - (j + 2),
      by omega_using [hj], j + 2, rfl, by omega_using [hj, hjev, h1], by omega_using [hjev], hI'⟩

/-- The products of both lanes added into the lower lanes: `RInvC`. -/
theorem foldLanesC_ok {E : REnv} {V : Nat → Block} {i : Nat} {t : State} (hI : RInvPC E V i t) :
    WP isa (.block foldLanes) t (RInvC E V i) :=
  WP.mono (foldLanes_run t) fun t' ⟨a8, a9, a10, k, g, m, rd, wr⟩ =>
    { le := hI.le, r10 := by rw [g]; exact hI.r10, r9 := by rw [g]; exact hI.r9, ax := by rw [g]; exact hI.ax
      gpr := fun q h9 h10 hax => by rw [g]; exact hI.gpr q h9 h10 hax
      rd := by rw [rd]; exact hI.rd, wr := by rw [wr]; exact hI.wr
      frame := by rw [m]; exact hI.frame
      ct := fun j hj => by rw [m]; exact hI.ct j hj
      prod := by
        rw [← hI.prod]
        simp only [Pclmul.prod, State.proj_xmm, a8, a9, a10, Prod.xor]
      y := by rw [k _ (by decide) (by decide) (by decide) (by decide)]; exact hI.y
      m0 := by rw [k _ (by decide) (by decide) (by decide) (by decide)]; exact hI.m0 0 (by decide)
      m1 := by rw [k _ (by decide) (by decide) (by decide) (by decide)]; exact hI.m1 }

/-- `RInvC` holds of a state with the same registers, memory and lanes. -/
theorem rinvC_keep {E : REnv} {V : Nat → Block} {i : Nat} {t t' : State} (hI : RInvC E V i t)
    (g : t'.gpr = t.gpr) (m : t'.mem = t.mem) (rd : t'.rd = t.rd) (wr : t'.wr = t.wr)
    (l : ∀ x k, t'.lane x k = t.lane x k) : RInvC E V i t' :=
  { le := hI.le, r10 := by rw [g]; exact hI.r10, r9 := by rw [g]; exact hI.r9, ax := by rw [g]; exact hI.ax
    gpr := fun q h9 h10 hax => by rw [g]; exact hI.gpr q h9 h10 hax
    rd := by rw [rd]; exact hI.rd, wr := by rw [wr]; exact hI.wr
    frame := by rw [m]; exact hI.frame
    ct := fun j hj => by rw [m]; exact hI.ct j hj
    prod := by simp only [Pclmul.prod, State.proj_xmm, l]; exact hI.prod
    y := by rw [l]; exact hI.y, m0 := by rw [l]; exact hI.m0, m1 := by rw [l]; exact hI.m1 }

/-- The first block alone if `r` is odd (`one`), then the pairs (`pair`) and
their lanes added: what `remD` and `remE` do between clearing the products and
reducing them. -/
theorem remMidG_ok {E : REnv} {V : Nat → Block} (r1 : 1 ≤ E.r) (r15 : E.r ≤ 15) {one pair : List Instr}
    (hone : E.r % 2 = 1 → ∀ t, RInvC E V 0 t → WP isa (.block one) t fun t' =>
      RInvC E V 1 t' ∧ t'.zf = some (decide (E.r = 1)) ∧
      (∀ x, t.lane x 1 = 0 → x ≠ .xmm0 → t'.lane x 1 = 0) ∧ t'.lane .xmm0 1 = t.lane .xmm0 1)
    (hstep : ∀ i, i + 2 ≤ E.r → (E.r - i) % 2 = 0 → ∀ t, RInvPC E V i t →
      WP isa (.block pair) t fun t' => RInvPC E V (i + 2) t' ∧ t'.zf = some (decide (E.r - i = 2)))
    {t : State} (hI : RInvC E V 0 t)
    (h8 : t.lane .xmm8 1 = 0) (h9 : t.lane .xmm9 1 = 0) (h10 : t.lane .xmm10 1 = 0) (y1 : t.lane .xmm2 1 = 0)
    (m0 : t.lane .xmm0 1 = revMask) {X : Prog isa} {Q : State → Prop} (hX : ∀ s, RInvC E V E.r s → WP isa X s Q) :
    WP isa (.block [.alu .test .r9 (.imm 1)]) t fun s =>
      WP isa (.seq (.ite .e (.block [.alu .cmp .r9 (.imm 16)]) (.block one))
        (.seq (.ite .e (.block []) (.seq (.loop (.block pair) .ne) (.block foldLanes))) X)) s Q := by
  obtain hlast : ∀ s, (∃ i, i ≤ 1 ∧ (E.r - i) % 2 = 0 ∧ RInvPC E V i s ∧ (E.r = i → RInvC E V i s) ∧
      s.zf = some (decide (E.r = i))) →
      WP isa (.seq (.ite .e (.block []) (.seq (.loop (.block pair) .ne) (.block foldLanes))) X) s Q := by
    rintro s ⟨i, hi1, hev, hIs, hD, hz⟩
    refine WP.seq (WP.ite (decide (E.r = i)) (by simp only [eval, hz]) (fun h => ?_) (fun h => ?_))
    · have h' : E.r = i := by simpa using h
      refine WP.block_nil (hX s ?_)
      rw [h']; exact hD h'
    · exact WP.seq (WP.mono (pairLoopG_ok hstep (by simp at h; omega_using [r1, hi1, hev, h]) hev hIs) fun s' hP =>
        WP.mono (foldLanesC_ok hP) hX)
  refine WP.mono (test91_ok t) fun t₁ ⟨z₁, g₁, l₁, m₁, rd₁, wr₁⟩ => ?_
  obtain hI₁ := rinvC_keep hI g₁ m₁ rd₁ wr₁ l₁
  rw [hI.r9, Nat.sub_zero, parity16 _ (by omega_using [r15])] at z₁
  refine WP.seq (WP.ite (decide (E.r % 2 = 0)) (by simp only [eval, z₁]) (fun h => ?_) (fun h => ?_))
  · refine WP.mono (cmp916_ok t₁) fun t₂ ⟨z₂, g₂, l₂, m₂, rd₂, wr₂⟩ =>
      hlast t₂ ⟨0, by omega_using [], by simpa using h, ?_, fun h0 => absurd h0 (by omega_using [r1]), ?_⟩
    · exact RInvPC.of_C (rinvC_keep hI₁ g₂ m₂ rd₂ wr₂ l₂) (by rw [l₂, l₁]; exact h8) (by rw [l₂, l₁]; exact h9)
        (by rw [l₂, l₁]; exact h10) (by rw [l₂, l₁]; exact y1) (by rw [l₂, l₁]; exact m0)
    · rw [z₂, g₁, hI.r9, Nat.sub_zero, zero16 _ (by omega_using [r15])]
  · have hodd : E.r % 2 = 1 := by simp at h; omega_using [h]
    refine WP.mono (hone hodd t₁ hI₁) fun t₂ ⟨hI₂, z₂, zz, x0⟩ =>
      hlast t₂ ⟨1, Nat.le_refl _, by omega_using [hodd], ?_, fun _ => hI₂, z₂⟩
    exact RInvPC.of_C hI₂ (zz _ (by rw [l₁]; exact h8) (by decide)) (zz _ (by rw [l₁]; exact h9) (by decide))
      (zz _ (by rw [l₁]; exact h10) (by decide)) (zz _ (by rw [l₁]; exact y1) (by decide)) (by rw [x0, l₁]; exact m0)

/-- `remMidG_ok` for `remE`. -/
theorem remMidC_ok {E : REnv} (hE : OkC E) {t : State} (hI : RInvC E E.X 0 t)
    (h8 : t.lane .xmm8 1 = 0) (h9 : t.lane .xmm9 1 = 0) (h10 : t.lane .xmm10 1 = 0) (y1 : t.lane .xmm2 1 = 0)
    (m0 : t.lane .xmm0 1 = revMask) {X : Prog isa} {Q : State → Prop} (hX : ∀ s, RInvC E E.X E.r s → WP isa X s Q) :
    WP isa (.block [.alu .test .r9 (.imm 1)]) t fun s =>
      WP isa (.seq (.ite .e (.block [.alu .cmp .r9 (.imm 16)]) (.block (Impl.Gcm.X86_64.StitchR.remOneC E.src)))
        (.seq (.ite .e (.block []) (.seq (.loop (.block (remPairE E.src ++ ([.alu .sub .rax (.imm 64)] : List Instr) ++
            remNextPair)) .ne) (.block foldLanes)))
          X)) s Q :=
  remMidG_ok hE.r1 hE.r15 (fun hodd _ hI => oneStepC_ok hE hodd hI) (fun _ hi hev _ hI => pairStepC_ok hE hi hev hI)
    hI h8 h9 h10 y1 m0 hX

/-! ## Decryption, with the powers read from the key context

`StitchR.remD` hashes the blocks as it reads them (`REnv.H`) and decrypts them
in place, reading the powers at `aC` as `remE` does (`remOneD`, then
`remPairD` with `rax` moved after each pair). -/

/-- The first block alone, for odd `r`, decrypted in place, in the lower
lanes: `rax` moved up for its power and down for the pairs after it. -/
theorem oneStepDC_ok {E : REnv} (hE : OkC E) (hsrc : E.src = .rdx) (hodd : E.r % 2 = 1) {t : State}
    (hI : RInvC E E.H 0 t) :
    WP isa (.block Impl.Gcm.X86_64.StitchR.remOneD) t fun t' =>
      RInvC E E.H 1 t' ∧ t'.zf = some (decide (E.r = 1)) ∧
      (∀ x, t.lane x 1 = 0 → x ≠ .xmm0 → t'.lane x 1 = 0) ∧ t'.lane .xmm0 1 = t.lane .xmm0 1 := by
  have r15 := hE.r15
  have r1 := hE.r1
  have h0 : (0 : Nat) < E.r := r1
  obtain hSA : E.S = E.A := by rw [← hE.gS, hsrc, hE.gA]
  obtain eSD : ∀ j, E.aS j = E.aD j := fun j => by show E.S + _ = E.A + _; rw [hSA]
  obtain gA : t.gpr .rdx = E.A := by rw [hI.gpr _ (by decide) (by decide) (by decide), hE.gA]
  obtain gP : t.gpr .r11 = E.P := by rw [hI.gpr _ (by decide) (by decide) (by decide), hE.gP]
  have r10z : t.gpr .r10 = BitVec.ofNat 64 (16 * 0) := hI.r10
  obtain ax0 : t.gpr .rax = E.W + BitVec.ofNat 64 (16 * E.r) := by
    obtain h := hI.ax; rw [r10z, Nat.sub_zero] at h; rw [← h]; exact (BitVec.add_zero _).symm
  simp only [Impl.Gcm.X86_64.StitchR.remOneD, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (addRax32_ok t) fun t₀ ⟨a₀, g₀, l₀, m₀, rd₀, wr₀⟩ => ?_
  obtain eK : t₀.gpr .r11 + t₀.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int) = E.aK 0 := by
    rw [g₀ _ (by decide), g₀ _ (by decide), gP, r10z, addr768]
  obtain eD : t₀.gpr .rdx + t₀.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aD 0 := by
    rw [g₀ _ (by decide), g₀ _ (by decide), gA, r10z, addr0]
  obtain eW : t₀.gpr .rax + t₀.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aC 0 := by
    rw [a₀, g₀ _ (by decide), r10z, ax0, ← aC_first E hodd, BitVec.ofInt_natCast, Nat.mul_zero]
    exact BitVec.add_zero _ ▸ BitVec.add_zero _
  obtain dD : Region.Sub ⟨E.aD 0, 16⟩ ⟨E.A, 16 * E.r⟩ := Offset.sub_base _ (by omega_using [r1])
  obtain sDW : Mem.Sep (E.aD 0) 16 (E.aC 0) 16 :=
    ((hE.dW 0 h0).symm.sub_left dD).sep (Region.contains_self _ _) (Region.contains_self _ _)
  obtain fA : ∀ (R : Region), R.Disjoint ⟨E.A, 16 * E.r⟩ → ∀ r' ∈ [(⟨E.A, 16 * 0⟩ : Region)], R.Disjoint r' :=
    fun R hR r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hR.sub_right (Region.sub_prefix (by omega_using []))
  obtain bS : blockAt t.mem (E.aD 0) = blockAt E.m (E.aS 0) := by
    rw [← eSD]
    exact blockAt_frame hI.frame fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact hE.dS 0 h0 0 (Nat.le_refl _)
  obtain bK : blockAt t.mem (E.aK 0) = blockAt E.m (E.aK 0) := blockAt_frame hI.frame (fA _ (hE.dK 0 h0))
  obtain rW : t.mem.readW (E.aC 0) 128 = E.TC 0 :=
    hI.frame.readW (Region.contains_self _ _) (fA _ (hE.dW 0 h0)) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (wp_and_run (StitchZH.remBodyD_ok .rdx t₀ (by rw [l₀]; exact hI.m0)
    (by rw [eD, rd₀, wr₀, hI.rd, hI.wr, ← eSD]; exact hE.inS 0 h0)
    (by rw [eK, rd₀, wr₀, hI.rd, hI.wr]; exact hE.inK 0 h0) (by rw [eD, wr₀, hI.wr]; exact hE.inD 0 h0)
    (by rw [eW, rd₀, wr₀, hI.rd, hI.wr]; exact hE.inW 0 h0) (by rw [eD, eW]; exact sDW))
    (R := fun t₁ => (∀ x, t₀.lane x 1 = 0 → x ≠ .xmm0 → t₁.lane x 1 = 0) ∧ t₁.lane .xmm0 1 = t₀.lane .xmm0 1)
    fun t₁ e₁ => ⟨fun x hx _ => by
        rw [← State.zlane_lt2 _ _ (by decide)]
        exact lane0Block_zhi (lane0_remBodyD _) e₁ x (by decide) (by decide)
          (by rw [State.zlane_lt2 _ _ (by decide)]; exact hx),
      by rw [← State.zlane_lt2 _ _ (by decide),
          lane0Block_zkeep (lane0_remBodyD _) e₁ _ (remBodyD_dst _ _ (by decide)) (by decide),
          State.zlane_lt2 _ _ (by decide)]⟩)
    fun t₁ ⟨⟨m₁, p₁, y₁, g₁, rd₁, wr₁, k₁⟩, z₁, x₁⟩ => ?_
  rw [eK, eD] at m₁
  rw [eD, eW] at p₁
  have hm₀ : t₀.mem = t.mem := m₀
  rw [hm₀] at m₁ p₁
  obtain hX : XBinOp.eval .pshufb (t.mem.readW (E.aK 0) 128 ^^^ t.mem.readW (E.aD 0) 128) revMask = E.X 0 := by
    rw [pshufb_rev_xor, ← blockAt_eq, ← blockAt_eq, bS, bK, BitVec.xor_comm]
  obtain hH : XBinOp.eval .pshufb (t.mem.readW (E.aD 0) 128) revMask = E.H 0 := by rw [← blockAt_eq, bS]
  rw [WP.block_append_iff]
  refine WP.mono (subRax64_ok t₁) fun t₂ ⟨a₂, g₂, l₂, m₂, rd₂, wr₂⟩ => ?_
  refine WP.mono (StitchZH.remNext_ok t₂ (m := E.r - 0) (i := 0) (by omega_using [r1]) (by omega_using [r15])
    (by rw [g₂ _ (by decide), g₁, g₀ _ (by decide), hI.r9])
    (by rw [g₂ _ (by decide), g₁, g₀ _ (by decide), hI.r10])) fun t' ⟨a10, a9, z, gg, ln, mm, rd', wr'⟩ => ?_
  obtain m' : t'.mem = t.mem.writeW (E.aD 0) (t.mem.readW (E.aK 0) 128 ^^^ t.mem.readW (E.aD 0) 128) := by
    rw [mm, m₂, m₁]
  refine ⟨⟨by omega_using [r1], a10, by rw [a9, show E.r - 0 - 1 = E.r - (0 + 1) by omega_using []], ?_,
    fun q h9 h10 hax => by rw [gg q h9 h10, g₂ q hax, g₁, g₀ q hax]; exact hI.gpr q h9 h10 hax,
    by rw [rd', rd₂, rd₁, rd₀, hI.rd], by rw [wr', wr₂, wr₁, wr₀, hI.wr], ?_, fun j hj => ?_, ?_, ?_, ?_, ?_⟩,
    by rw [z, Nat.sub_zero], fun x hx h0x => by rw [ln, l₂]; exact z₁ x (by rw [l₀]; exact hx) h0x,
    by rw [ln, l₂, x₁, l₀]⟩
  · rw [gg _ (by decide) (by decide), a10, a₂, g₁, a₀, ax0]
    rw [show 16 * (E.r - (0 + 1)) = 16 * E.r - 16 by omega_using []]
    have : 16 ≤ 16 * E.r := by omega_using [r1]
    obtain hw : 16 * E.r < 2 ^ 64 := by omega_using [r15]
    rw [← Offset.ofNat_sub_ofNat this, Nat.zero_add, Nat.mul_one]
    exact rax_one _ _
  · rw [m']
    exact (hI.frame.sub fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [])⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using []) (by omega_using [r1, r15]))
  · rw [m']
    obtain rfl : j = 0 := by omega_using [hj]
    rw [blockAt_eq, Mem.readW_writeW_self _ _ 16 _ (by decide), hX]
  · have e : prod (t'.proj 0) = prod (t₁.proj 0) := by simp only [prod, State.proj_xmm, ln, l₂]
    rw [e, p₁, show prod (t₀.proj 0) = prod (t.proj 0) by simp only [prod, State.proj_xmm, l₀], hI.prod, hH,
      rW, show t₀.lane .xmm2 0 = t.lane .xmm2 0 from l₀ _ _, hI.y]
    simp only [accR]
    rw [BitVec.xor_comm]
  · rw [ln, l₂, y₁]; simp only [Nat.add_one_ne_zero, ↓reduceIte]
  · rw [ln, l₂, k₁ _ (by decide), l₀]; exact hI.m0
  · rw [ln, l₂, k₁ _ (by decide), l₀]; exact hI.m1

/-- Two blocks decrypted in place, one in each lane, then `rax` moved down for
the next pair. -/
theorem pairStepDC_ok {E : REnv} (hE : OkC E) (hsrc : E.src = .rdx) {i : Nat} (hi : i + 2 ≤ E.r)
    (hev : (E.r - i) % 2 = 0) {t : State} (hI : RInvPC E E.H i t) :
    WP isa (.block (remPairD ++ ([.alu .sub .rax (.imm 64)] : List Instr) ++ remNextPair)) t fun t' =>
      RInvPC E E.H (i + 2) t' ∧ t'.zf = some (decide (E.r - i = 2)) := by
  have r15 := hE.r15
  obtain hSA : E.S = E.A := by rw [← hE.gS, hsrc, hE.gA]
  obtain eSD : ∀ j, E.aS j = E.aD j := fun j => by show E.S + _ = E.A + _; rw [hSA]
  obtain gA : t.gpr .rdx = E.A := by rw [hI.gpr _ (by decide) (by decide) (by decide), hE.gA]
  obtain gP : t.gpr .r11 = E.P := by rw [hI.gpr _ (by decide) (by decide) (by decide), hE.gP]
  obtain eK : t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int) = E.aK i := by rw [gP, hI.r10, addr768]
  obtain eD : t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.aD i := by rw [gA, hI.r10, addr0]
  obtain eW : t.gpr .rax + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) = E.W + BitVec.ofNat 64 (16 * (E.r - i)) := by
    rw [hI.ax, BitVec.ofInt_natCast]; exact BitVec.add_zero _
  obtain eW0 : E.W + BitVec.ofNat 64 (16 * (E.r - i)) = E.aC i := by
    have := aC_pair E hi hev (show 0 < 2 by decide); rwa [Nat.mul_zero, show BitVec.ofNat 64 0 = 0#64 from rfl,
      BitVec.add_zero, Nat.add_zero] at this
  rw [List.append_assoc, remPairD_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (pairMem_ok t (by rw [eD, hI.rd, hI.wr, ← eSD]; exact hE.inS2 i hi)
    (by rw [eK, hI.rd, hI.wr]; exact hE.inK2 i hi) (by rw [eD, hI.wr]; exact hE.inD2 i hi)
    (by rw [eW, eW0, hI.rd, hI.wr]; exact hE.inW2 i hi hev))
    fun t₁ ⟨⟨v, m₁⟩, b₁, x13, x12, g₁, rd₁, wr₁, k₁⟩ => ?_
  rw [eD] at m₁ b₁ x13
  rw [eK] at b₁
  rw [eW] at x12
  rw [WP.block_append_iff]
  refine WP.mono (pairLanes_ok t₁ fun l hl => by rw [k₁ _ (by decide) (by decide) l hl]; exact hI.m0 l hl)
    fun t₂ ⟨kk, q₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subRax64_ok t₂) fun t₃ ⟨a₃, g₃, l₃, m₃, rd₃, wr₃⟩ => ?_
  refine WP.mono (remNextPair_ok t₃ (m := E.r - i) (i := i) (by omega_using [hi]) (by omega_using [r15])
    (by rw [g₃ _ (by decide), kk.gpr, g₁, hI.r9]) (by rw [g₃ _ (by decide), kk.gpr, g₁, hI.r10]))
    fun t' ⟨a10, a9, z, gg, ln, mm, rd', wr'⟩ => ⟨?_, z⟩
  obtain fA : ∀ (R : Region), R.Disjoint ⟨E.A, 16 * E.r⟩ → ∀ k ≤ E.r, ∀ r' ∈ [(⟨E.A, 16 * k⟩ : Region)],
      R.Disjoint r' := fun R hR k hk r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hR.sub_right (Region.sub_prefix (by omega_using [hk]))
  obtain F₁ : Frame [⟨E.A, 16 * (i + 2)⟩] E.m t₁.mem := by
    rw [m₁]
    exact (hI.frame.sub fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [])⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using []) (by omega_using [hi, r15]))
  obtain mt : t'.mem = t₁.mem := by rw [mm, m₃, kk.mem]
  obtain bS : ∀ l < 2, blockAt t.mem (E.A + BitVec.ofNat 64 (16 * (i + l))) = blockAt E.m (E.aS (i + l)) :=
    fun l hl => by
      rw [show E.A + BitVec.ofNat 64 (16 * (i + l)) = E.aS (i + l) by rw [eSD]]
      exact blockAt_frame hI.frame fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hE.dS (i + l) (by omega_using [hi, hl]) i (by omega_using [])
  obtain bK : ∀ l < 2, blockAt t.mem (E.P + BitVec.ofNat 64 (768 + 16 * (i + l))) = blockAt E.m (E.aK (i + l)) :=
    fun l hl => blockAt_frame hI.frame (fA _ (hE.dK _ (by omega_using [hi, hl])) i (by omega_using [hi]))
  obtain rW : ∀ l < 2, t₁.mem.readW (E.aC (i + l)) 128 = E.TC (i + l) := fun l hl =>
    F₁.readW (Region.contains_self _ _) (fA _ (hE.dW _ (by omega_using [hi, hl])) (i + 2) hi) (by decide)
  obtain P : ∀ l < 2, Pclmul.prod (t'.proj l) =
      (Pclmul.prod (t.proj l)).acc (E.H (i + l) ^^^ t.lane .xmm2 l) (E.TC (i + l)) := fun l hl => by
    obtain ⟨p₂, -, -⟩ := q₂ l hl
    obtain e : Pclmul.prod (t'.proj l) = Pclmul.prod (t₂.proj l) := by simp only [Pclmul.prod, State.proj_xmm, ln, l₃]
    obtain e₁ : Pclmul.prod (t₁.proj l) = Pclmul.prod (t.proj l) := by
      simp only [Pclmul.prod, State.proj_xmm, k₁ .xmm8 (by decide) (by decide) l hl,
        k₁ .xmm9 (by decide) (by decide) l hl, k₁ .xmm10 (by decide) (by decide) l hl]
    rw [e, p₂, e₁, x13 l hl, x12 l hl, k₁ _ (by decide) (by decide) l hl, aC_pair E hi hev hl, rW l hl, aOff,
      ← blockAt_eq, bS l hl]
  refine ⟨by omega_using [hi], a10, by rw [a9, show E.r - i - 2 = E.r - (i + 2) by omega_using []], ?_,
    fun q h9 h10 hax => by rw [gg q h9 h10, g₃ q hax, kk.gpr, g₁]; exact hI.gpr q h9 h10 hax,
    by rw [rd', rd₃, kk.rd, rd₁, hI.rd],
    by rw [wr', wr₃, kk.wr, wr₁, hI.wr], by rw [mt]; exact F₁, fun j hj => ?_, ?_, ?_, ?_, fun l hl => ?_, ?_⟩
  · have hax : t.gpr .rax + t.gpr .r10 = E.W + BitVec.ofNat 64 (16 * (E.r - i)) := hI.ax
    rw [gg _ (by decide) (by decide), a10, a₃, kk.gpr, g₁]
    rw [hI.r10] at hax
    obtain h32 : 16 * (E.r - (i + 2)) + 32 = 16 * (E.r - i) := by omega_using [hi]
    rw [← h32, ← Offset.add_add] at hax
    rw [show 16 * (i + 2) = 16 * i + 32 by omega_using [], ← Offset.add_add]
    exact rax_pair hax
  · rw [mt]
    by_cases hji : j < i
    · rw [m₁, show E.aD i = (⟨E.aD i, 32⟩ : Region).base from rfl,
        blockAt_writeW_sep' (Offset.disjoint _ (.inl (by omega_using [hji])) (by omega_using [hi, r15, hj])
          (by omega_using [hi, r15])) rfl]
      exact hI.ct j hji
    · obtain ⟨l, hl, rfl⟩ : ∃ l < 2, j = i + l := ⟨j - i, by omega_using [hj], by omega_using [hji]⟩
      obtain b := b₁ l hl
      rw [aOff, aOffK, bS l hl, bK l hl] at b
      exact b
  · rw [P 0 (by decide), P 1 (by decide), xor_acc_acc, hI.prod, hI.y, hI.y1]
    simp only [accR, Nat.add_zero, Nat.add_one_ne_zero, ↓reduceIte]
    rw [BitVec.xor_comm (E.H i), BitVec.xor_comm (E.H (i + 1))]
  · rw [ln, l₃, (q₂ 0 (by decide)).2.1]; exact (ite_eq_right_iff.mpr fun h => absurd h (by omega_using [])).symm
  · rw [ln, l₃, (q₂ 1 (by decide)).2.1]
  · rw [ln, l₃, (q₂ l hl).2.2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₁ _ (by decide) (by decide) l hl]
    exact hI.m0 l hl
  · rw [ln, l₃, (q₂ 0 (by decide)).2.2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₁ _ (by decide) (by decide) 0 (by decide)]
    exact hI.m1

/-- `remMidG_ok` for `remD`. -/
theorem remMidDC_ok {E : REnv} (hE : OkC E) (hsrc : E.src = .rdx) {t : State} (hI : RInvC E E.H 0 t)
    (h8 : t.lane .xmm8 1 = 0) (h9 : t.lane .xmm9 1 = 0) (h10 : t.lane .xmm10 1 = 0) (y1 : t.lane .xmm2 1 = 0)
    (m0 : t.lane .xmm0 1 = revMask) {X : Prog isa} {Q : State → Prop} (hX : ∀ s, RInvC E E.H E.r s → WP isa X s Q) :
    WP isa (.block [.alu .test .r9 (.imm 1)]) t fun s =>
      WP isa (.seq (.ite .e (.block [.alu .cmp .r9 (.imm 16)]) (.block Impl.Gcm.X86_64.StitchR.remOneD))
        (.seq (.ite .e (.block []) (.seq (.loop (.block (remPairD ++ ([.alu .sub .rax (.imm 64)] : List Instr) ++
            remNextPair)) .ne) (.block foldLanes)))
          X)) s Q :=
  remMidG_ok hE.r1 hE.r15 (fun hodd _ hI => oneStepDC_ok hE hsrc hodd hI)
    (fun _ hi hev _ hI => pairStepDC_ok hE hsrc hi hev hI) hI h8 h9 h10 y1 m0 hX

end VG.Proof.Gcm.X86_64.StitchR
