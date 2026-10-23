module

public import VerifiedGarbage.Proof.AesCtr.PPC64LE.Call
import VerifiedGarbage.Proof.AesCtr.PPC64LE.Steps
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Loop
public import VerifiedGarbage.Proof.AesCtr.Ctr32
public import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesCtr.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Ctr

/-!
# AES-CTR on PPC64LE: the code before the call

As on x86-64 (`Proof/AesCtr/X86_64/Body.lean`): the blocks of the call after
`k` blocks (`mOf`), what is left but no further than where the last 32 bits
of the counter block wrap around, and `pre_wp`: the code before the call
sets up a call of `vg_aes_ctr32` on them (`CtrCall`), with their number in
the scratch buffer, from AES-CBC's loop invariant for `ctrMode`
(`Proof/AesCbc/PPC64LE/Loop.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCtr.PPC64LE
open VG.Impl.AesCbc.PPC64LE (mov)
open VG.Proof.AesCbc (Mode)
open VG.Proof.AesCbc.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat ofNat)

/-- The blocks of the call after `k` blocks: what is left, but no further
than where the last 32 bits of the counter block wrap around. -/
def mOf (s₀ : State) (k : Nat) : Nat := min (N s₀ - k) (2 ^ 32 - (toNat (iv0 s₀) + k) % 2 ^ 32)

theorem length_iv0 (s₀ : State) : (iv0 s₀).length = 16 := Proof.Cmac.bytesAt_length _ _ _

theorem mOf_pos {s₀ : State} {k : Nat} (hk : k < N s₀) : 0 < mOf s₀ k := by
  unfold mOf; have := Nat.mod_lt (toNat (iv0 s₀) + k) (show 0 < 2 ^ 32 by decide); omega

theorem mOf_le (s₀ : State) (k : Nat) : mOf s₀ k ≤ N s₀ - k := Nat.min_le_left _ _

theorem lo32_mOf (s₀ : State) (k : Nat) : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k ≤ 2 ^ 32 := by
  rw [AesCtr.lo32_next (length_iv0 s₀)]; unfold mOf; omega

theorem chainK_ctr (s₀ : State) {k : Nat} (hk : k ≤ N s₀) : chainK AesCtr.ctrMode s₀ k = next (iv0 s₀) k := by
  rw [chainK, AesCtr.ctrMode_chain, List.length_take, Proof.AesCbc.length_blocksAt, Nat.min_eq_left hk]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.N_le : N s₀ ≤ 2 ^ 60 := by
  have := hp.data_wrap; omega

theorem UPre.seg_wrap {k m : Nat} (hk : k < N s₀) (hkm : k + m ≤ N s₀) : (blk s₀ k).toNat + 16 * m ≤ 2 ^ 64 := by
  have := hp.data_wrap
  have : (blk s₀ k).toNat = (Dp s₀).toNat + 16 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  omega

omit hp in
theorem UPre.seg_sub {k m : Nat} (hkm : k + m ≤ N s₀) : Region.Sub ⟨blk s₀ k, 16 * m⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega)

/-- The arguments of the call after `k` blocks. -/
theorem UPre.ctrCall {k : Nat} (hk : k < N s₀) {s : State}
    (r3 : s.gpr .r3 = W s₀) (r4 : s.gpr .r4 = s₀.gpr .r4) (r5 : s.gpr .r5 = Iv s₀)
    (r6 : s.gpr .r6 = blk s₀ k) (r7 : s.gpr .r7 = BitVec.ofNat 64 (mOf s₀ k)) (r8 : s.gpr .r8 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CtrCall s (W s₀) (Iv s₀) (blk s₀ k) (S s₀) (R s₀) (mOf s₀ k) where
  r3 := r3
  r4 := by rw [r4, r4_ofNat]
  r5 := r5
  r6 := r6
  r7 := r7
  r8 := r8
  rounds := hp.rounds
  wrap := UPre.seg_wrap hp hk (by have := mOf_le s₀ k; omega)
  kc := hp.sch_iv
  kd := hp.sch_data.sub_right (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega))
  ks := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  cd := hp.iv_data.sub_right (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega))
  cs := hp.iv_scr.sub_right (Region.sub_prefix (by decide))
  ds := (hp.data_scr.sub_left (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega))).sub_right
    (Region.sub_prefix (by decide))
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; have := mOf_le s₀ k; omega⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; have := mOf_le s₀ k; omega⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-- What the code before the call leaves. -/
structure Pre (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  call : CtrCall s₁ (W s₀) (Iv s₀) (blk s₀ k) (S s₀) (R s₀) (mOf s₀ k)
  saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  mem : s₁.mem = s.mem.writeW (S s₀ + BitVec.ofNat 64 2048) (BitVec.ofNat 64 (mOf s₀ k))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

omit hp in
theorem preserved_ne' {r : Reg} (hr : r ∈ preserved) :
    r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧
      r ≠ .r12 := by
  revert hr; cases r <;> decide

theorem pre_wp {k : Nat} (hk : k < N s₀) {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa (.block (count ++ args)) s (Pre s₀ k s) := by
  have hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have hNl := UPre.N_le hp
  refine count_wp (Q := Iv s₀) (S := S s₀) (left := N s₀ - k) h.r16 h.r18 (by omega) h.r19
    (by rw [hR]; exact in_rw (r := ivR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide)))
    (by rw [hW]; exact in_rw (by simp) cSv0) fun s₁ r10₁ g₁ mem₁ rd₁ wr₁ => ?_
  -- The number of blocks.
  have hiv : bytesAt s.mem (Iv s₀) 16 = next (iv0 s₀) k := by rw [h.iv, chainK_ctr s₀ (by omega)]
  have hlo := AesCtr.lo32_bytesAt s.mem (Iv s₀)
  rw [hiv, AesCtr.lo32_next (length_iv0 s₀)] at hlo
  have hm : s₁.gpr .r10 = BitVec.ofNat 64 (mOf s₀ k) := by rw [r10₁, ← hlo]; rfl
  unfold args mov
  refine wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_mr fun s₄ u₄ => wp_mr fun s₅ u₅ => ?_
  refine wp_mr fun s₆ u₆ => wp_mr fun s₇ u₇ => wp_nil ?_
  have g (r : Reg) (hr : r ∈ preserved) : s₇.gpr r = s.gpr r := by
    obtain ⟨h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := preserved_ne' hr
    rw [u₇.other _ h8, u₆.other _ h7, u₅.other _ h6, u₄.other _ h5, u₃.other _ h4, u₂.other _ h3,
      g₁ r h9 h10 h11 h12]
  have g₁' (r : Reg) (hr : r ∈ preserved) : s₁.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, -, h9, h10, h11, h12⟩ := preserved_ne' hr
    exact g₁ r h9 h10 h11 h12
  refine ⟨UPre.ctrCall hp hk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, g, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₁' .r14 (by decide), h.r14]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), g₁' .r15 (by decide), h.r15]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), g₁' .r16 (by decide), h.r16]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁' .r17 (by decide), h.r17]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), hm]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁' .r19 (by decide), h.r19]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁, h.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁, h.wr]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, mem₁, hm]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]

end

end VG.Proof.AesCtr.PPC64LE
