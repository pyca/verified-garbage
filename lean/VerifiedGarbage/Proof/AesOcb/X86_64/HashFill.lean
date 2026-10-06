import VerifiedGarbage.Proof.AesOcb.X86_64.Nonce
import VerifiedGarbage.Proof.AesOcb.X86_64.LNtz

/-!
# AES-OCB on x86-64: filling the buffer of `HASH` (`hashFill`)

Untrusted: everything here is checked by Lean. `hashFill` computes the next
offset of `HASH`, `Offset_{i+1} = Offset_i ⊕ L_{ntz(i+1)}` (`lAddr_ok`, the
table, `xor16_ok`), and writes the next block of the associated data XORed with it
to the next slot of the buffer at `W + bufO` (`hashFill_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt)
open VG.Proof.Cmac (le8)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt imm_eq)

theorem add_ofNat_imm (p : Addr) (a k : Nat) (hk : k < 2 ^ 31) :
    p + BitVec.ofNat 64 a + BitVec.signExtend 64 (BitVec.ofNat 32 k) = p + BitVec.ofNat 64 (a + k) := by
  rw [imm_eq hk, Offset.add_add]

theorem ofNat_imm (a k : Nat) (hk : k < 2 ^ 31) :
    BitVec.ofNat 64 a + BitVec.signExtend 64 (BitVec.ofNat 32 k) = BitVec.ofNat 64 (a + k) := by
  rw [imm_eq hk, ← BitVec.ofNat_add]

/-- What one `hashFill` leaves. -/
structure FillPost (W A : Addr) (l : Block) (j i c : Nat) (t t' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 ohO, 16⟩, ⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩] t.mem t'.mem
  oh : blockAtMem t'.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1)
  buf : blockAtMem t'.mem (W + BitVec.ofNat 64 (384 + 16 * i)) =
    blockAtMem t.mem (A + BitVec.ofNat 64 (16 * (j + i))) ^^^ offAt 0 l (j + i + 1)
  rbx : t'.gpr .rbx = A + BitVec.ofNat 64 (16 * (j + i + 1))
  rbp : t'.gpr .rbp = BitVec.ofNat 64 (j + i + 2)
  rsi : t'.gpr .rsi = W + BitVec.ofNat 64 (384 + 16 * (i + 1))
  r13 : t'.gpr .r13 = BitVec.ofNat 64 (i + 1)
  zf : t'.zf = some (decide (i + 1 = c))
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r11 → r ≠ .rsi → r ≠ .rbx → r ≠ .rbp →
    r ≠ .r13 → t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem hashFill_ok {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {A : Addr} {l : Block}
    {j i c : Nat} (hi : i < c) (hc : c ≤ 8) (hj : j + i + 2 < 2 ^ 61)
    (hbp : t.gpr .rbp = BitVec.ofNat 64 (j + i + 1)) (hbx : t.gpr .rbx = A + BitVec.ofNat 64 (16 * (j + i)))
    (hsi : t.gpr .rsi = W + BitVec.ofNat 64 (384 + 16 * i)) (h13 : t.gpr .r13 = BitVec.ofNat 64 i)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 c)
    {M : Nat} (T : Tbl W l M t.mem) (hM : j + i + 1 ≤ M)
    (hoh : blockAtMem t.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i))
    (hA : Covers [⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩] (t.rd ++ t.wr))
    (hAW : (⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint ⟨W, 3584⟩) :
    WP isa hashFill t (FillPost W A l j i c t) := by
  have hM60 := T.lt
  obtain ⟨t₁, run₁, h1₁, g₁, m₁, -, rd₁, wr₁⟩ := lAddr_ok E.r15 (i := j + i + 1) (by omega) (by omega) hbp
  have hs := slot_lt (ntz (j + i + 1))
  have h15₁ : t₁.gpr .r15 = W := by rw [g₁ _ (by decide) (by decide) (by decide), E.r15]
  obtain ⟨t₂, run₂, B₂⟩ := xor16_ok (s := t₁) (b := .rcx) (a := tblO) (d := ohO) h15₁ h1₁ (by decide) (by decide)
    (by rw [slot_addr, rd₁, wr₁]; exact E.perm.wR (by simp only [tblO]; omega))
    (by rw [Offset.add_add, rd₁, wr₁, show 16 * slot (ntz (j + i + 1)) + (tblO + 8) =
          tblO + 16 * slot (ntz (j + i + 1)) + 8 by omega]; exact E.perm.wR (by simp only [tblO]; omega))
    (by rw [wr₁]; exact E.perm.wW (by decide)) (by rw [wr₁]; exact E.perm.wW (by decide))
  have oh₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1) := by
    rw [B₂.val, slot_addr, m₁, T.ntz (by omega) hM, hoh]
    rfl
  have g₂ : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r11 → t₂.gpr r = t.gpr r := fun r h1 h2 h3 h4 h5 => by
    rw [B₂.gpr r (by simp [h1, h2]), g₁ r h1 h3 h2]
  have hbx₂ : t₂.gpr .rbx = A + BitVec.ofNat 64 (16 * (j + i)) := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), hbx]
  have hsi₂ : t₂.gpr .rsi = W + BitVec.ofNat 64 (384 + 16 * i) := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), hsi]
  have h15₂ : t₂.gpr .r15 = W := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), E.r15]
  have hbp₂ : t₂.gpr .rbp = BitVec.ofNat 64 (j + i + 1) := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), hbp]
  have h13₂ : t₂.gpr .r13 = BitVec.ofNat 64 i := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h13]
  have h12₂ : t₂.gpr .r12 = BitVec.ofNat 64 c := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h12]
  have rd₂ : t₂.rd = t.rd := by rw [B₂.rd, rd₁]
  have wr₂ : t₂.wr = t.wr := by rw [B₂.wr, wr₁]
  have fr₂ : Frame [⟨W + BitVec.ofNat 64 ohO, 16⟩] t.mem t₂.mem := by rw [← m₁]; exact B₂.frame
  have eA : blockAtMem t₂.mem (A + BitVec.ofNat 64 (16 * (j + i))) = blockAtMem t.mem (A + BitVec.ofNat 64 (16 * (j + i))) :=
    blockAtMem_frame fr₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hAW.sub_right (Lay.wSub (by decide))
  have ea0 : A + BitVec.ofNat 64 (16 * (j + i)) + BitVec.ofNat 64 0 = A + BitVec.ofNat 64 (16 * (j + i)) :=
    BitVec.add_zero _
  have ew0 : W + BitVec.ofNat 64 (384 + 16 * i) + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 (384 + 16 * i) :=
    BitVec.add_zero _
  have rA₀ : InRegions (t₂.rd ++ t₂.wr) (A + BitVec.ofNat 64 (16 * (j + i))) 8 := by
    rw [rd₂, wr₂]; simpa using Proof.AesCcm.X86_64.in_off (d := 0) (n := 8) hA (by decide) (by decide)
  have rA₈ : InRegions (t₂.rd ++ t₂.wr) (A + BitVec.ofNat 64 (16 * (j + i)) + BitVec.ofNat 64 8) 8 := by
    rw [rd₂, wr₂]; exact Proof.AesCcm.X86_64.in_off (d := 8) (n := 8) hA (by decide) (by decide)
  have rO₀ : InRegions (t₂.rd ++ t₂.wr) (W + BitVec.ofNat 64 144) 8 := by rw [rd₂, wr₂]; exact E.perm.wR (by decide)
  have rO₈ : InRegions (t₂.rd ++ t₂.wr) (W + BitVec.ofNat 64 152) 8 := by rw [rd₂, wr₂]; exact E.perm.wR (by decide)
  have wS₀ : InRegions t₂.wr (W + BitVec.ofNat 64 (384 + 16 * i)) 8 := by rw [wr₂]; exact E.perm.wW (by omega)
  have wS₈ : InRegions t₂.wr (W + BitVec.ofNat 64 (384 + 16 * i) + BitVec.ofNat 64 8) 8 := by
    rw [wr₂, Offset.add_add]; exact E.perm.wW (by omega)
  unfold hashFill
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_append, runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some]
    orun [hbx₂, hsi₂, h15₂, hbp₂, h13₂, h12₂, ea0, ew0, rA₀, rA₈, rO₀, rO₈, wS₀, wS₈], ?_⟩
  have fs : ∀ (M : Mem) (v₀ v₁ : BitVec 64), Frame [⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩] M
      ((M.writeW (W + BitVec.ofNat 64 (384 + 16 * i)) v₀).writeW (W + BitVec.ofNat 64 (384 + 16 * i) + 8#64) v₁) :=
    fun M v₀ v₁ => frame_store2 _ _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags]
    exact (fr₂.mono (by simp)).trans ((fs _ _ _).mono (by simp))
  · simp only [mem_setReg, mem_arithFlags]
    rw [blockAtMem_frame (fs _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 144) (n := 16) (d := 384 + 16 * i) (k := 16) (.inl (by omega)) (by decide) (by omega)), oh₂]
  · simp only [mem_setReg, mem_arithFlags]
    rw [blockAtMem_store2, show W + 152#64 = W + BitVec.ofNat 64 144 + BitVec.ofNat 64 8 from (addr8 W 144).symm,
      blockAtMem_xor_words, eA, show W + BitVec.ofNat 64 144 = W + BitVec.ofNat 64 ohO from rfl, oh₂]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx₂, Offset.add_add]
    rw [show 16 * (j + i) + 16 = 16 * (j + i + 1) by omega]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbp₂, ← BitVec.ofNat_add]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hsi₂, Offset.add_add]
    rw [show 384 + 16 * i + 16 = 384 + 16 * (i + 1) by omega]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h13₂, ← BitVec.ofNat_add]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h13₂, h12₂,
      ← BitVec.ofNat_add]
    rw [Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  · simp only [gpr_setReg, gpr_arithFlags, h1, h2, h3, h4, h5, h6, h7, h8, h9, ite_false]
    exact g₂ r h1 h2 h3 h4 h5
  · simp only [rd_setReg, rd_arithFlags]; exact rd₂
  · simp only [wr_setReg, wr_arithFlags]; exact wr₂

end VG.Proof.AesOcb.X86_64
