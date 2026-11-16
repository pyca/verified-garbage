module

public import VerifiedGarbage.Proof.AesCfb.Spec
public import VerifiedGarbage.Impl.AesCfb.AArch64
public import VerifiedGarbage.Proof.AesCbc.AArch64.Group
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesCfb.Spec
meta import VerifiedGarbage.Impl.AesCfb.AArch64
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Group
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Contract

-- separate module: the CFB128 group, which only `Verified.lean` uses, out of the one-block proofs.

/-!
# AES-CFB128 on AArch64: decryption four blocks at a time

`decGroup_ok`: one run of `decGroup` takes the loop invariant AES-CBC's
proofs share (`Proof/AesCbc/AArch64/Loop.lean`) from `k` blocks to `k + 4`
(`GroupOk`), for `cfbMode false`, for any implementation of the block
functions (`BlocksImpl`): the four ciphertext blocks `Cⱼ` are saved as CBC's
decryption saves them (`decSave_wp`), the inputs of the block cipher, `Cⱼ₋₁`
(the chaining value for the first, the saved block before for the others),
are copied over the data blocks (`cfbA4_wp`) and enciphered there in place by
one call, each is XORed with its saved `Cⱼ`, and the last saved `Cⱼ` becomes
the chaining value. `decGroup_ct`: it is constant time (`GroupCt`).
-/

@[expose] public section

namespace VG.Proof.AesCfb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCfb.AArch64
open VG.Impl.AesCbc.AArch64 (copy gOff cOff xorAt advance4 decSave callArgs4)
open VG.Proof.AesCbc
open VG.Proof.AesCbc.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)

theorem xor_comm (x y : List Byte) : Spec.Cbc.xor x y = Spec.Cbc.xor y x := by
  simp only [Spec.Cbc.xor]
  exact List.zipWith_comm_of_comm (fun a b => BitVec.xor_comm a b)

section
variable {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 4 ≤ N s₀)
include hp hk

/-! ## The pieces of the group -/

/-- Slot `j` copied over data block `i = j + 1`. -/
theorem inAt_ok {j i : Nat} (hi : i = j + 1) (hj : j < 3) {t : State} (x22 : t.gpr .x22 = blk s₀ k)
    (x24 : t.gpr .x24 = S s₀) (rd : t.rd = s₀.rd) (wr : t.wr = s₀.wr) :
    ∃ t', runBlock isa (inAt j) t = some t' ∧ (∀ r, r ≠ .x9 → t'.gpr r = t.gpr r) ∧ t'.sp = t.sp ∧
      t'.mem = copyMem t.mem (blk s₀ (k + i)) (sl s₀ j) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  subst hi
  have hR : t.rd ++ t.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd, wr, hp.rd, hp.wr]; rfl
  have hW : t.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr, hp.wr]
  exact copy_ok t (dst := .x22) (src := .x24) (d := 16 * (j + 1)) (e := gOff + 16 * j)
    (by rw [x22, UPre.blk_add]) (by rw [x22, UPre.blk_add8]) (by rw [x24]) (by rw [x24, sl8])
    (by rw [hR]; exact in_rw (by simp) (cSl s₀ hj)) (by rw [hR]; exact in_rw (by simp) (cSl8 s₀ hj))
    (by rw [hW]; exact in_rw (by simp) (hp.cBlk0 (k := k + (j + 1)) (by omega_using [hk, hj])))
    (by rw [hW]; exact in_rw (by simp) (hp.cBlk8 (k := k + (j + 1)) (by omega_using [hk, hj])))
    (by decide) (by decide) (by omega_using [hj]) (by omega_using [hj])
    (by simp only [gOff]; omega_using [hj]) (by simp only [gOff]; omega_using [hj])

/-- The chaining value copied over data block 0. -/
theorem chainIn_ok {t : State} (x21 : t.gpr .x21 = Iv s₀) (x22 : t.gpr .x22 = blk s₀ k)
    (rd : t.rd = s₀.rd) (wr : t.wr = s₀.wr) :
    ∃ t', runBlock isa (copy .x22 0 .x21 0) t = some t' ∧ (∀ r, r ≠ .x9 → t'.gpr r = t.gpr r) ∧
      t'.sp = t.sp ∧ t'.mem = copyMem t.mem (blk s₀ (k + 0)) (Iv s₀) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR : t.rd ++ t.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd, wr, hp.rd, hp.wr]; rfl
  have hW : t.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr, hp.wr]
  exact copy_ok t (dst := .x22) (src := .x21) (d := 0) (e := 0) (P := blk s₀ (k + 0)) (Q := Iv s₀)
    ((congrArg (· + BitVec.ofNat 64 0) x22).trans (UPre.blk_add (j := 0)))
    ((congrArg (· + BitVec.ofNat 64 (0 + 8)) x22).trans (UPre.blk_add8 (j := 0)))
    (by rw [x21]; simp) (by rw [x21])
    (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
    (by rw [hW]; exact in_rw (by simp) (hp.cBlk0 (k := k + 0) (by omega_using [hk])))
    (by rw [hW]; exact in_rw (by simp) (hp.cBlk8 (k := k + 0) (by omega_using [hk])))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Slot `j` XORed into data block `j`. -/
theorem cfbFix_ok {j : Nat} (hj : j < 3) {t : State} (x22 : t.gpr .x22 = blk s₀ k)
    (x24 : t.gpr .x24 = S s₀) (rd : t.rd = s₀.rd) (wr : t.wr = s₀.wr) :
    ∃ t', runBlock isa (fixAt j) t = some t' ∧ (∀ r, r ≠ .x9 → r ≠ .x10 → t'.gpr r = t.gpr r) ∧
      t'.sp = t.sp ∧ t'.mem = xorMem t.mem (blk s₀ (k + j)) (sl s₀ j) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR : t.rd ++ t.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd, wr, hp.rd, hp.wr]; rfl
  have hW : t.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr, hp.wr]
  exact xorAt_ok t (dst := .x22) (src := .x24) (d := 16 * j) (e := gOff + 16 * j)
    (by rw [x22, UPre.blk_add]) (by rw [x22, UPre.blk_add8]) (by rw [x24]) (by rw [x24, sl8])
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 (k := k + j) (by omega_using [hk, hj])))
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 (k := k + j) (by omega_using [hk, hj])))
    (by rw [hR]; exact in_rw (by simp) (cSl s₀ hj)) (by rw [hR]; exact in_rw (by simp) (cSl8 s₀ hj))
    (by rw [hW]; exact in_rw (by simp) (hp.cBlk0 (k := k + j) (by omega_using [hk, hj])))
    (by rw [hW]; exact in_rw (by simp) (hp.cBlk8 (k := k + j) (by omega_using [hk, hj])))
    (by decide) (by decide) (by decide) (by decide)
    (by omega_using [hj]) (by omega_using [hj]) (by simp only [gOff]; omega_using [hj])
    (by simp only [gOff]; omega_using [hj])

/-- The saved block 3 XORed into data block 3. -/
theorem fixLast_ok {t : State} (x22 : t.gpr .x22 = blk s₀ k)
    (x24 : t.gpr .x24 = S s₀) (rd : t.rd = s₀.rd) (wr : t.wr = s₀.wr) :
    ∃ t', runBlock isa (xorAt .x22 48 .x24 cOff) t = some t' ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → t'.gpr r = t.gpr r) ∧
      t'.sp = t.sp ∧ t'.mem = xorMem t.mem (blk s₀ (k + 3)) (Sv s₀) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR : t.rd ++ t.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd, wr, hp.rd, hp.wr]; rfl
  have hW : t.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr, hp.wr]
  exact xorAt_ok t (dst := .x22) (src := .x24) (d := 48) (e := cOff)
    (by rw [x22]; exact UPre.blk_add (j := 3)) (by rw [x22]; exact UPre.blk_add8 (j := 3))
    (by rw [x24]; rfl) (by rw [x24]; exact sv8 _)
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 (k := k + 3) (by omega_using [hk])))
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 (k := k + 3) (by omega_using [hk])))
    (by rw [hR]; exact in_rw (by simp) cSv0) (by rw [hR]; exact in_rw (by simp) cSv8)
    (by rw [hW]; exact in_rw (by simp) (hp.cBlk0 (k := k + 3) (by omega_using [hk])))
    (by rw [hW]; exact in_rw (by simp) (hp.cBlk8 (k := k + 3) (by omega_using [hk])))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end

/-! ## Before the call -/

/-- What the code before the call leaves: the inputs of the block cipher in
the data blocks, and the blocks themselves in the slots. -/
structure CfbA4 (s₀ : State) (k : Nat) (s t : State) : Prop where
  pre : CallPre4 t (W s₀) (blk s₀ k) (S s₀) (R s₀)
  saved : ∀ r ∈ preserved, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨blk s₀ k, 64⟩, ⟨S s₀, 2064⟩, gR s₀] s.mem t.mem
  in0 : bytesAt t.mem (blk s₀ (k + 0)) 16 = bytesAt s.mem (Iv s₀) 16
  in1 : bytesAt t.mem (blk s₀ (k + 1)) 16 = bytesAt s.mem (blk s₀ (k + 0)) 16
  in2 : bytesAt t.mem (blk s₀ (k + 2)) 16 = bytesAt s.mem (blk s₀ (k + 1)) 16
  in3 : bytesAt t.mem (blk s₀ (k + 3)) 16 = bytesAt s.mem (blk s₀ (k + 2)) 16
  slot : ∀ j < 3, bytesAt t.mem (sl s₀ j) 16 = bytesAt s.mem (blk s₀ (k + j)) 16
  last : bytesAt t.mem (Sv s₀) 16 = bytesAt s.mem (blk s₀ (k + 3)) 16

theorem cfbA4_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 4 ≤ N s₀)
    {s : State} (h : LInv M s₀ k s) :
    WP isa (.block (decSave ++ decIn ++ callArgs4)) s (CfbA4 s₀ k s) := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (decSave_wp hp hk h.x22 h.x24 h.rd h.wr) fun t₄ sv => ?_
  have x21₄ : t₄.gpr .x21 = Iv s₀ := by rw [sv.g _ (by decide), h.x21]
  have x22₄ : t₄.gpr .x22 = blk s₀ k := by rw [sv.g _ (by decide), h.x22]
  have x24₄ : t₄.gpr .x24 = S s₀ := by rw [sv.g _ (by decide), h.x24]
  have rd₄ : t₄.rd = s₀.rd := by rw [sv.rd, h.rd]
  have wr₄ : t₄.wr = s₀.wr := by rw [sv.wr, h.wr]
  obtain ⟨t₅, run₅, g₅, sp₅, m₅, rd₅, wr₅⟩ := inAt_ok hp hk (j := 0) (i := 1) rfl (by decide) x22₄ x24₄ rd₄ wr₄
  obtain ⟨t₆, run₆, g₆, sp₆, m₆, rd₆, wr₆⟩ := inAt_ok hp hk (j := 1) (i := 2) rfl (by decide)
    (by rw [g₅ _ (by decide), x22₄]) (by rw [g₅ _ (by decide), x24₄]) (by rw [rd₅, rd₄]) (by rw [wr₅, wr₄])
  obtain ⟨t₇, run₇, g₇, sp₇, m₇, rd₇, wr₇⟩ := inAt_ok hp hk (j := 2) (i := 3) rfl (by decide)
    (by rw [g₆ _ (by decide), g₅ _ (by decide), x22₄]) (by rw [g₆ _ (by decide), g₅ _ (by decide), x24₄])
    (by rw [rd₆, rd₅, rd₄]) (by rw [wr₆, wr₅, wr₄])
  obtain ⟨t₈, run₈, g₈, sp₈, m₈, rd₈, wr₈⟩ := chainIn_ok hp hk
    (by rw [g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), x21₄])
    (by rw [g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), x22₄])
    (by rw [rd₇, rd₆, rd₅, rd₄]) (by rw [wr₇, wr₆, wr₅, wr₄])
  obtain ⟨t₉, run₉, x0₉, x1₉, x2₉, x3₉, x4₉, cs₉, sp₉, mem₉, rd₉, wr₉⟩ := callArgs4_ok t₈
  have g (r : Reg) (hr : r ≠ .x9) : t₈.gpr r = s.gpr r := by
    rw [g₈ r hr, g₇ r hr, g₆ r hr, g₅ r hr, sv.g r hr]
  have rd₈' : t₈.rd = s.rd := by rw [rd₈, rd₇, rd₆, rd₅, sv.rd]
  have wr₈' : t₈.wr = s.wr := by rw [wr₈, wr₇, wr₆, wr₅, sv.wr]
  show WP isa (.block (inAt 0 ++ inAt 1 ++ inAt 2 ++ copy .x22 0 .x21 0 ++ callArgs4)) t₄ _
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.of_runBlock ⟨t₅, run₅, WP.of_runBlock ⟨t₆, run₆, WP.of_runBlock ⟨t₇, run₇,
    WP.of_runBlock ⟨t₈, run₈, WP.of_runBlock ⟨t₉, run₉, ?_⟩⟩⟩⟩⟩
  have keep (r : Reg) (hr : r ∈ preserved) : t₉.gpr r = s.gpr r := by
    rw [cs₉ r hr, g r (preserved_ne hr).1]
  have ivS : bytesAt t₄.mem (Iv s₀) 16 = bytesAt s.mem (Iv s₀) 16 :=
    Proof.Cmac.bytesAt_frame sv.frame (all_cons hp.dIS' (all_cons hp.dIG all_nil)) (by decide)
  refine ⟨hp.callPre4 hk (by rw [x0₉, g _ (by decide), h.x19]) (by rw [x1₉, g _ (by decide), h.x20])
    (by rw [x2₉, g _ (by decide), h.x22]) x3₉ (by rw [x4₉, g _ (by decide), h.x24])
    (by rw [rd₉, rd₈', h.rd]) (by rw [wr₉, wr₈', h.wr]),
    keep, by rw [sp₉, sp₈, sp₇, sp₆, sp₅, sv.sp], by rw [rd₉, rd₈'], by rw [wr₉, wr₈'], ?_, ?_, ?_, ?_, ?_,
    fun j hj => ?_, ?_⟩
  · rw [mem₉, m₈, m₇, m₆, m₅]
    refine (sv.frame.sub ?_).trans (((copyMem_frameB _ (by decide) _).sub ?_).trans
      (((copyMem_frameB _ (by decide) _).sub ?_).trans (((copyMem_frameB _ (by decide) _).sub ?_).trans
        ((copyMem_frameB _ (by decide) _).sub ?_))))
    all_goals intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · rcases hr with rfl | rfl
      · exact ⟨⟨S s₀, 2064⟩, by simp, fun _ h => h⟩
      · exact ⟨gR s₀, by simp, fun _ h => h⟩
    all_goals subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · rw [mem₉, m₈, copyMem_bytes, m₇, copyMem_other, m₆, copyMem_other, m₅, copyMem_other, ivS] <;> cbc_gd
  · rw [mem₉, m₈, copyMem_other, m₇, copyMem_other, m₆, copyMem_other, m₅, copyMem_bytes,
      sv.slot 0 (by decide)] <;> cbc_gd
  · rw [mem₉, m₈, copyMem_other, m₇, copyMem_other, m₆, copyMem_bytes, m₅, copyMem_other,
      sv.slot 1 (by decide)] <;> cbc_gd
  · rw [mem₉, m₈, copyMem_other, m₇, copyMem_bytes, m₆, copyMem_other, m₅, copyMem_other,
      sv.slot 2 (by decide)] <;> cbc_gd
  · rw [mem₉, m₈, copyMem_other, m₇, copyMem_other, m₆, copyMem_other, m₅, copyMem_other, sv.slot j hj]
      <;> cbc_gd
  · rw [mem₉, m₈, copyMem_other, m₇, copyMem_other, m₆, copyMem_other, m₅, copyMem_other, sv.last] <;> cbc_gd

/-! ## The group -/

theorem decGroup_ok (v : BlocksImpl) : GroupOk (cfbMode false) (decGroup v.enc) := by
  intro s₀ hp k hk s h
  have len : (blks s₀).length = N s₀ := by simp [Spec.Cbc.blocksAt]
  refine WP.seq (WP.mono (cfbA4_wp hp hk h) fun t₉ a => ?_)
  refine WP.seq (WP.mono (blk_call4 v.encOk v.encNoFrames a.pre) fun t₁₀ c => ?_)
  have g₁₀ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : t₁₀.gpr r = s.gpr r := by
    rw [c.saved r hr h30, a.saved r hr]
  have rd₁₀ : t₁₀.rd = s₀.rd := by rw [c.rd, a.rd, h.rd]
  have wr₁₀ : t₁₀.wr = s₀.wr := by rw [c.wr, a.wr, h.wr]
  have x21₁₀ : t₁₀.gpr .x21 = Iv s₀ := by rw [g₁₀ _ (by simp [preserved]) (by decide), h.x21]
  have x22₁₀ : t₁₀.gpr .x22 = blk s₀ k := by rw [g₁₀ _ (by simp [preserved]) (by decide), h.x22]
  have x24₁₀ : t₁₀.gpr .x24 = S s₀ := by rw [g₁₀ _ (by simp [preserved]) (by decide), h.x24]
  obtain ⟨t₁₁, run₁₁, g₁₁, sp₁₁, m₁₁, rd₁₁, wr₁₁⟩ := cfbFix_ok hp hk (j := 0) (by decide) x22₁₀ x24₁₀ rd₁₀ wr₁₀
  obtain ⟨t₁₂, run₁₂, g₁₂, sp₁₂, m₁₂, rd₁₂, wr₁₂⟩ := cfbFix_ok hp hk (j := 1) (by decide)
    (by rw [g₁₁ _ (by decide) (by decide), x22₁₀]) (by rw [g₁₁ _ (by decide) (by decide), x24₁₀])
    (by rw [rd₁₁, rd₁₀]) (by rw [wr₁₁, wr₁₀])
  obtain ⟨t₁₃, run₁₃, g₁₃, sp₁₃, m₁₃, rd₁₃, wr₁₃⟩ := cfbFix_ok hp hk (j := 2) (by decide)
    (by rw [g₁₂ _ (by decide) (by decide), g₁₁ _ (by decide) (by decide), x22₁₀])
    (by rw [g₁₂ _ (by decide) (by decide), g₁₁ _ (by decide) (by decide), x24₁₀])
    (by rw [rd₁₂, rd₁₁, rd₁₀]) (by rw [wr₁₂, wr₁₁, wr₁₀])
  obtain ⟨t₁₄, run₁₄, g₁₄, sp₁₄, m₁₄, rd₁₄, wr₁₄⟩ := fixLast_ok hp hk
    (by rw [g₁₃ _ (by decide) (by decide), g₁₂ _ (by decide) (by decide), g₁₁ _ (by decide) (by decide), x22₁₀])
    (by rw [g₁₃ _ (by decide) (by decide), g₁₂ _ (by decide) (by decide), g₁₁ _ (by decide) (by decide), x24₁₀])
    (by rw [rd₁₃, rd₁₂, rd₁₁, rd₁₀]) (by rw [wr₁₃, wr₁₂, wr₁₁, wr₁₀])
  have g₁₄' (r : Reg) (h9 : r ≠ .x9) (h10 : r ≠ .x10) : t₁₄.gpr r = t₁₀.gpr r := by
    rw [g₁₄ r h9 h10, g₁₃ r h9 h10, g₁₂ r h9 h10, g₁₁ r h9 h10]
  obtain ⟨t₁₅, run₁₅, g₁₅, sp₁₅, m₁₅, rd₁₅, wr₁₅⟩ := hp.last_ok
    (by rw [g₁₄' _ (by decide) (by decide), x21₁₀]) (by rw [g₁₄' _ (by decide) (by decide), x24₁₀])
    (by rw [rd₁₄, rd₁₃, rd₁₂, rd₁₁, rd₁₀]) (by rw [wr₁₄, wr₁₃, wr₁₂, wr₁₁, wr₁₀])
  obtain ⟨t₁₆, run₁₆, x22₁₆, x23₁₆, few₁₆, keep₁₆, sp₁₆, m₁₆, rd₁₆, wr₁₆⟩ := advance4_regs hp (s := t₁₅) hk
    (by rw [g₁₅ _ (by decide), g₁₄' _ (by decide) (by decide), x22₁₀])
    (by rw [g₁₅ _ (by decide), g₁₄' _ (by decide) (by decide), g₁₀ _ (by simp [preserved]) (by decide), h.x23])
  show WP isa (.block (fixAt 0 ++ fixAt 1 ++ fixAt 2 ++ xorAt .x22 48 .x24 cOff ++ copy .x21 0 .x24 cOff ++
    advance4)) t₁₀ _
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.of_runBlock ⟨t₁₁, run₁₁, WP.of_runBlock ⟨t₁₂, run₁₂, WP.of_runBlock ⟨t₁₃, run₁₃,
    WP.of_runBlock ⟨t₁₄, run₁₄, WP.of_runBlock ⟨t₁₅, run₁₅, WP.of_runBlock ⟨t₁₆, run₁₆, ?_⟩⟩⟩⟩⟩⟩
  have g (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) (h22 : r ≠ .x22) (h23 : r ≠ .x23) :
      t₁₆.gpr r = s.gpr r := by
    rw [keep₁₆ r h22 h23 (preserved_ne hr).1, g₁₅ r (preserved_ne hr).1,
      g₁₄' r (preserved_ne hr).1 (preserved_ne hr).2, g₁₀ r hr h30]
  -- Memory.
  have fA : Frame [⟨blk s₀ k, 64⟩, ivR s₀, ⟨S s₀, 2064⟩, gR s₀] s.mem t₉.mem :=
    a.frame.sub (all_cons ⟨_, by simp, fun _ h => h⟩ (all_cons ⟨⟨S s₀, 2064⟩, by simp, fun _ h => h⟩
      (all_cons ⟨gR s₀, by simp, fun _ h => h⟩ all_nil)))
  have fAll : Frame [⟨blk s₀ k, 64⟩, ivR s₀, ⟨S s₀, 2064⟩, gR s₀] s.mem t₁₆.mem := by
    rw [m₁₆, m₁₅, m₁₄, m₁₃, m₁₂, m₁₁]
    refine fA.trans ((c.frame.sub ?_).trans (((xorMem_frameB _ (by decide) _).sub ?_).trans
      (((xorMem_frameB _ (by decide) _).sub ?_).trans (((xorMem_frameB _ (by decide) _).sub ?_).trans
        (((xorMem_frameB _ (by decide) _).sub ?_).trans ((copyMem_frame _ _ _).sub ?_))))))
    all_goals intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
    all_goals subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have big₉ : Frame (Big s₀) s₀.mem t₉.mem :=
    (UPre.big_of h.frame).trans (UPre.bigStep (stepFrame4 hk fA))
  have hb (j : Nat) (hj : j < 4) :
      bytesAt s.mem (blk s₀ (k + j)) 16 = (blks s₀)[k + j]'(by rw [len]; omega_using [hk, hj]) :=
    h.blockAt (by omega_using []) (by omega_using [hk, hj])
  have chain : bytesAt s.mem (Iv s₀) 16 = Spec.Cbc.next (iv0 s₀) ((blks s₀).take k) := by
    rw [h.iv]; simp only [chainK, cfbMode_chain, cts, Bool.false_eq_true, ite_false]
  -- The enciphered blocks after the call, and the slots it left.
  have e (j : Nat) (hj : j < 4) : bytesAt t₁₀.mem (blk s₀ (k + j)) 16 =
      Spec.Cbc.aesWith (R s₀) (wK s₀) (bytesAt t₉.mem (blk s₀ (k + j)) 16) := by
    have := c.out j hj
    rw [UPre.blk_add] at this
    rw [this, ← aesWith_state, UPre.sched_bytes hp big₉]
  have sv (j : Nat) (hj : j < 3) :
      bytesAt t₁₀.mem (sl s₀ j) 16 = (blks s₀)[k + j]'(by rw [len]; omega_using [hk, hj]) := by
    rw [Proof.Cmac.bytesAt_frame c.frame (all_cons (hp.dT64 hk hj) (all_cons (hp.dTS hj) all_nil)) (by decide),
      a.slot j hj, hb j (by omega_using [hj])]
  have svL : bytesAt t₁₀.mem (Sv s₀) 16 = (blks s₀)[k + 3]'(by rw [len]; omega_using [hk]) := by
    rw [Proof.Cmac.bytesAt_frame c.frame (all_cons (hp.dV64 hk) (all_cons hp.sv_scr all_nil)) (by decide),
      a.last, hb 3 (by decide)]
  -- The blocks and the chaining value after the group.
  have o0 : bytesAt t₁₆.mem (blk s₀ (k + 0)) 16 = Spec.Cbc.xor ((blks s₀)[k + 0]'(by rw [len]; omega_using [hk]))
      (Spec.Cbc.aesWith (R s₀) (wK s₀) (Spec.Cbc.next (iv0 s₀) ((blks s₀).take k))) := by
    rw [xor_comm, m₁₆, m₁₅, copyMem_other, m₁₄, xorMem_other, m₁₃, xorMem_other, m₁₂, xorMem_other, m₁₁,
      xorMem_bytes, e 0 (by decide), a.in0, chain, sv 0 (by decide)] <;> cbc_gd
  have o1 : bytesAt t₁₆.mem (blk s₀ (k + 1)) 16 = Spec.Cbc.xor ((blks s₀)[k + 1]'(by rw [len]; omega_using [hk]))
      (Spec.Cbc.aesWith (R s₀) (wK s₀) ((blks s₀)[k + 0]'(by rw [len]; omega_using [hk]))) := by
    rw [xor_comm, m₁₆, m₁₅, copyMem_other, m₁₄, xorMem_other, m₁₃, xorMem_other, m₁₂, xorMem_bytes, m₁₁,
      xorMem_other, xorMem_other, e 1 (by decide), a.in1, hb 0 (by decide), sv 1 (by decide)] <;> cbc_gd
  have o2 : bytesAt t₁₆.mem (blk s₀ (k + 2)) 16 = Spec.Cbc.xor ((blks s₀)[k + 2]'(by rw [len]; omega_using [hk]))
      (Spec.Cbc.aesWith (R s₀) (wK s₀) ((blks s₀)[k + 1]'(by rw [len]; omega_using [hk]))) := by
    rw [xor_comm, m₁₆, m₁₅, copyMem_other, m₁₄, xorMem_other, m₁₃, xorMem_bytes, m₁₂, xorMem_other, xorMem_other,
      m₁₁, xorMem_other, xorMem_other, e 2 (by decide), a.in2, hb 1 (by decide), sv 2 (by decide)] <;> cbc_gd
  have o3 : bytesAt t₁₆.mem (blk s₀ (k + 3)) 16 = Spec.Cbc.xor ((blks s₀)[k + 3]'(by rw [len]; omega_using [hk]))
      (Spec.Cbc.aesWith (R s₀) (wK s₀) ((blks s₀)[k + 2]'(by rw [len]; omega_using [hk]))) := by
    rw [xor_comm, m₁₆, m₁₅, copyMem_other, m₁₄, xorMem_bytes, m₁₃, xorMem_other, xorMem_other, m₁₂, xorMem_other,
      xorMem_other, m₁₁, xorMem_other, xorMem_other, e 3 (by decide), a.in3, hb 2 (by decide), svL] <;> cbc_gd
  have ivF : bytesAt t₁₆.mem (Iv s₀) 16 = (blks s₀)[k + 3]'(by rw [len]; omega_using [hk]) := by
    rw [m₁₆, m₁₅, copyMem_bytes, m₁₄, xorMem_other, m₁₃, xorMem_other, m₁₂, xorMem_other, m₁₁, xorMem_other,
      svL] <;> cbc_gd
  -- The mode.
  have take4 : (blks s₀).take (k + 4) = (blks s₀).take k ++ [(blks s₀)[k + 0]'(by rw [len]; omega_using [hk])] ++
      [(blks s₀)[k + 1]'(by rw [len]; omega_using [hk])] ++ [(blks s₀)[k + 2]'(by rw [len]; omega_using [hk])] ++
      [(blks s₀)[k + 3]'(by rw [len]; omega_using [hk])] := by
    have t₀ : (blks s₀).take (k + 1) = (blks s₀).take k ++ [(blks s₀)[k + 0]'(by rw [len]; omega_using [hk])] :=
      take_succ_blks s₀ (by omega_using [hk])
    have t₁ : (blks s₀).take (k + 2) = (blks s₀).take (k + 1) ++ [(blks s₀)[k + 1]'(by rw [len]; omega_using [hk])] :=
      take_succ_blks s₀ (by omega_using [hk])
    have t₂ : (blks s₀).take (k + 3) = (blks s₀).take (k + 2) ++ [(blks s₀)[k + 2]'(by rw [len]; omega_using [hk])] :=
      take_succ_blks s₀ (by omega_using [hk])
    have t₃ : (blks s₀).take (k + 4) = (blks s₀).take (k + 3) ++ [(blks s₀)[k + 3]'(by rw [len]; omega_using [hk])] :=
      take_succ_blks s₀ (by omega_using [hk])
    rw [t₃, t₂, t₁, t₀]
  have hl : (outK (cfbMode false) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega_using [hk]
  obtain ⟨x19', x20', x21', x24', other'⟩ := h.next g
  refine ⟨⟨x19', x20', x21', x22₁₆, x23₁₆, x24', other', ?_, ?_, ?_, ?_, ?_, ?_⟩, few₁₆⟩
  · rw [sp₁₆, sp₁₅, sp₁₄, sp₁₃, sp₁₂, sp₁₁, c.sp, a.sp, h.sp]
  · rw [rd₁₆, rd₁₅, rd₁₄, rd₁₃, rd₁₂, rd₁₁, rd₁₀]
  · rw [wr₁₆, wr₁₅, wr₁₄, wr₁₃, wr₁₂, wr₁₁, wr₁₀]
  · exact h.frame.trans (stepFrame4 hk fAll)
  · rw [hp.blocksAt_step4 hk fAll h.data hl, o0, o1, o2, o3]
    simp only [outK, cfbMode_out, cfb, Bool.false_eq_true, ite_false]
    rw [take4, decrypt_snoc, decrypt_snoc, decrypt_snoc, decrypt_snoc, next_snoc, next_snoc, next_snoc]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · rw [ivF]
    simp only [chainK, cfbMode_chain, cts, Bool.false_eq_true, ite_false, take4, next_snoc]

/-! ## Constant time -/

theorem decGroupPre_taint : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24])
    (.block (decSave ++ decIn ++ callArgs4)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decGroupPost_taint : ∃ h, (taint.check (Taint.ofRegs [.x21, .x22, .x23, .x24])
    (.block (decFix ++ advance4)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decGroup_ct (v : BlocksImpl) : GroupCt (cfbMode false) (decGroup v.enc) :=
  fun hp hp' hq k => group_ct (fun hq k => pub_blk hq k) v.encOk v.encCt v.encNoFrames
    decGroupPre_taint decGroupPost_taint
    (@fun _ hp _ hk _ h => WP.mono (cfbA4_wp hp hk h) fun _ a => Mid4.of h a.pre a.saved a.sp) hp hp' hq k

end VG.Proof.AesCfb.AArch64
