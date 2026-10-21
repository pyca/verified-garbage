module
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGLanes
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop

import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGD
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop48
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base

/-!
# The blocks after the last group, decrypted

`loopDR_ok`: the decryption loop, for any number of blocks, stops with
fewer than 16 left (`DInv`). `decTailRG_ok` is `dec` after its setup for any
number of blocks from 16 on: the blocks after the last group, if any, by
`remGD_ok`.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre DPost nb nr kp pp cp yp cb dp dR pR cR yR bAddr blk ctb ciph sch hk y₀
  addr_eq in_sub in_sub_int in_rdwr blocks_ctr32 blockAt_writeW_sep' ite_t ite_f)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB toNat_ofNat_lt)
open VG.Impl.Gcm.X86_64.Pclmul (poly at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeY)
open VG.Impl.Gcm.X86_64.Slot (storeCtr)
open VG.Impl.Gcm.X86_64.StitchZH (remGD dbody)
open VG.Proof.Gcm.X86_64.StitchZ (DInv AInv FinOk Ready cmp_ok dfinal_ok)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-- `test r9, r9`. -/
theorem test99_ok (s : State) :
    WP isa (.block [.alu .test .r9 (.reg .r9)]) s fun s' =>
      s'.zf = some (s.gpr .r9 &&& s.gpr .r9 == 0) ∧ s'.gpr = s.gpr ∧ (∀ x l, s'.zlane x l = s.zlane x l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun _ _ => rfl, trivial, trivial, trivial⟩

/-- The decryption loop, for any number of blocks: it stops with fewer than 16 left. -/
theorem loopDR_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e : Nat}
    {s : State} (hI : DInv s₀ P e s) (hcf : s.cf = some (decide (nb s₀ - 16 * e < 16)))
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.ite .b (.block []) (.loop dbody .ae)) s fun s' => ∃ e, nb s₀ - 16 * e < 16 ∧ DInv s₀ P e s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  have hle := hI.a.le
  refine WP.ite (decide (nb s₀ - 16 * e < 16)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil ⟨e, by simpa using h, hI, hCache⟩
  · let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ DInv s₀ P e s ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s
    have hstep : ∀ m s, I m s → WP isa dbody s (fun s' =>
        (eval .ae s' = some false ∧ ∃ e, nb s₀ - 16 * e < 16 ∧ DInv s₀ P e s' ∧
          VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s') ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨e, rfl, he, hI, hCI⟩
      refine WP.mono (dbody_ok hp hf he hI hCI) fun s' ⟨hI', hcf', hCI'⟩ => ?_
      by_cases hlt : nb s₀ - 16 * (e + 1) < 16
      · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
          e + 1, hlt, hI', hCI'⟩
      · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
          nb s₀ - 16 * (e + 1), by omega, e + 1, rfl, by omega, hI', hCI'⟩
    exact WP.loop (M := isa) I hstep (nb s₀ - 16 * e) s ⟨e, rfl, by simp at h; omega, hI, hCache⟩

/-- `decR` after the setup, for any number of blocks from 16 on. -/
theorem decTailRG_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hr : RemOkG (hk s₀) P)
    {bigC : Prog isa} {i : BitVec 32} (t : Nat) (hi : BitVec.signExtend 64 i = BitVec.ofNat 64 t)
    (ht : t < 2 ^ 64) (hbig : ∀ s, t ≤ nb s₀ → DInv s₀ P 0 s → VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s →
      WP isa bigC s fun s' => ∃ e, DInv s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s')
    {s : State} (hR : Ready s₀ P s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.seq (.block [.alu .cmp .r9 (.imm i)]) (.seq (.ite .b (.block []) bigC)
      (.seq (.block [.alu .cmp .r9 (.imm 16)])
        (.seq (.ite .b (.block []) (.loop dbody .ae))
          (.seq (.block [.alu .test .r9 (.reg .r9)])
            (.ite .e (.block (storeCtr ++ storeY)) (.seq (.block [.alu .add .r9 (.imm 16)]) remGD))))))) s
      (DPost s₀) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hI₁ : DInv s₀ P 0 s :=
    ⟨hR.a, by rw [hR.rdx]; simp, by rw [hR.gpr _ (by decide) (by decide) (by decide)]; simp, hR.rax,
      fun r h1 h2 _ h4 => hR.gpr r h1 h2 h4, hR.pw, hR.m1, by rw [hR.y]; simp [ghashFrom], hR.y1⟩
  refine WP.seq (WP.mono (WP.hkeep rfl (cmp_ok s i t hi))
    fun s₂ ⟨⟨hcf, g, l, m, rd, wr⟩, hh⟩ => ?_)
  have hI₂ := hI₁.of_eq g l m rd wr
  have hCache₂ := hCache.keep hh (hI₂.a.keys hp)
  rw [hI₁.r9, toNat_ofNat_lt (by omega), toNat_ofNat_lt ht] at hcf
  refine WP.seq (WP.mono (WP.ite (Q := fun s' => ∃ e, DInv s₀ P e s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s') (decide (nb s₀ - 16 * 0 < t))
    (by simp only [eval, hcf]) (fun _ => WP.block_nil ⟨0, hI₂, hCache₂⟩)
    (fun h => hbig _ (by simp at h; omega) hI₂ hCache₂)) fun s₃ ⟨e, hI₃, hCache₃⟩ => ?_)
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp_ok s₃ 16 16 (by decide)))
    fun s₄ ⟨⟨hcf₄, g₄, l₄, m₄, rd₄, wr₄⟩, hh₄⟩ => ?_)
  have hI₄ := hI₃.of_eq g₄ l₄ m₄ rd₄ wr₄
  have hle := hI₃.a.le
  rw [hI₃.r9, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by decide)] at hcf₄
  refine WP.seq (WP.mono (loopDR_ok hp hf hI₄ hcf₄ (hCache₃.keep hh₄ (hI₄.a.keys hp))) fun s₅ ⟨e, hlt, hI₅, hC₅⟩ => ?_)
  have hle₅ := hI₅.a.le
  refine WP.seq (WP.mono (WP.hkeep (by decide) (test99_ok s₅)) fun s₆ ⟨⟨z₆, g₆, l₆, m₆, rd₆, wr₆⟩, hh₆⟩ => ?_)
  have hI₆ := hI₅.of_eq g₆ (fun x l => l₆ x l) m₆ rd₆ wr₆
  have hz : (s₅.gpr .r9 &&& s₅.gpr .r9 == 0) = decide (nb s₀ = 16 * e) := by
    rw [BitVec.and_self, hI₅.r9]
    by_cases h : nb s₀ = 16 * e
    · rw [show nb s₀ - 16 * e = 0 by omega, decide_eq_true h]; rfl
    · have : BitVec.ofNat 64 (nb s₀ - 16 * e) ≠ 0 := fun e' => by
        have := congrArg BitVec.toNat e'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
        omega
      rw [beq_false_of_ne this, decide_eq_false h]
  refine WP.ite (decide (nb s₀ = 16 * e)) (by simp only [eval, z₆, hz]) (fun h => ?_) (fun h => ?_)
  · exact dfinal_ok hp (by simpa using h) hI₆
  · exact remGD_ok hp hr hI₆ hlt (by simpa using h) (hC₅.keep hh₆ (hI₆.a.keys hp))

end VG.Proof.Gcm.X86_64.StitchZH
