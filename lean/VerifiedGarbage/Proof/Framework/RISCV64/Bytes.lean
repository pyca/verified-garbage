module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.TCB.RISCV64.Isa
import all Init.Data.Nat.Bitwise.Basic

/-!
# RISC-V: bytes of argument buffers

Untrusted: everything here is checked by Lean. The effect of the sequences
of `Impl/Words/RISCV64/Bytes.lean`, byte by byte:
* `copyBytes_ok`: each byte written is the byte read from the source (which
  the writes must not overlap), and memory changes only there;
* `storeBytes_ok`: each byte written is the constant;
* `loadLE64_ok`: the little-endian doubleword `readW`;
* `storeLE64_ok`: the doubleword written as its two words.
-/

@[expose] public section

namespace VG.RISCV64.Bytes

open VG.Impl.Words.RISCV64 VG.RISCV64.Steps VG.RISCV64.ByteLoad

variable {s : State}

/-- A byte `li` loads, stored. -/
theorem setWidth_ofNat_byte {b : Nat} : (BitVec.ofNat 64 b).setWidth 8 = BitVec.ofNat 8 b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_mod_of_dvd b (by decide : 2 ^ 8 ∣ 2 ^ 64)]

/-- A byte written, read back at a different offset from the same base. -/
theorem byte_writeW_ne (m : Mem) (p : Addr) (b : Byte) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : j ≠ i) : (m.writeW (p + BitVec.ofNat 64 i) b) (p + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 j) := by
  rw [WriteBytes.writeW8_apply]
  simp only [Offset.add_ofNat_ne p hj hi h, ite_false]

/-- What `copyBytes` and `storeBytes` keep: the registers but `tmp`. -/
structure Keep (tmp : Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ≠ tmp → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

/-- Bytes `0 … k - 1` copied. -/
structure CopyI (tmp src dst : Reg) (soff doff n : Nat) (s : State) (k : Nat) (s' : State) : Prop
    extends Keep tmp s s' where
  copied : ∀ j < k, s'.mem (s.gpr dst + BitVec.ofNat 64 (doff + j)) =
    s.mem (s.gpr src + BitVec.ofNat 64 (soff + j))
  frame : Frame [⟨s.gpr dst + BitVec.ofNat 64 doff, n⟩] s.mem s'.mem

theorem copyBytes_ok {tmp src dst : Reg} {soff doff n : Nat} (hts : tmp ≠ src) (htd : tmp ≠ dst)
    (hs : soff + n ≤ 2048) (hd : doff + n ≤ 2048)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 (soff + i)) 1)
    (hw : ∀ i < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 (doff + i)) 1)
    (hsep : ∀ i < n,
      ¬ (⟨s.gpr dst + BitVec.ofNat 64 doff, n⟩ : Region).Contains (s.gpr src + BitVec.ofNat 64 (soff + i)) 1) :
    WP isa (.block (copyBytes tmp src dst soff doff n)) s (CopyI tmp src dst soff doff n s n) := by
  refine wp_range_flatMap (M := isa) (CopyI tmp src dst soff doff n s) (fun k s₁ hk h => ?_) n
    (Nat.le_refl _) s ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, fun _ h => absurd h (by omega), Frame.refl _ _⟩
  have hsrc : s₁.gpr src = s.gpr src := h.gpr _ (Ne.symm hts)
  have hdst : s₁.gpr dst = s.gpr dst := h.gpr _ (Ne.symm htd)
  refine wp_lbu (a := s.gpr src + BitVec.ofNat 64 (soff + k)) (by omega) (by rw [hsrc])
    (by rw [h.rd, h.wr]; exact hr k hk) fun s₂ u₂ => ?_
  refine wp_sb (a := s.gpr dst + BitVec.ofNat 64 (doff + k)) (by omega)
    (by rw [u₂.other _ (Ne.symm htd), hdst]) (by rw [u₂.wr, h.wr]; exact hw k hk) fun s₃ g₃ =>
    WP.block_nil ?_
  have hv : (s₂.gpr tmp).setWidth 8 = s.mem (s.gpr src + BitVec.ofNat 64 (soff + k)) := by
    rw [u₂.gpr, h.frame _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hsep k hk]
    simp
  have hm : s₃.mem = s₁.mem.writeW (s.gpr dst + BitVec.ofNat 64 (doff + k))
      (s.mem (s.gpr src + BitVec.ofNat 64 (soff + k))) := by
    rw [g₃.mem, hv, u₂.mem]
  refine ⟨⟨fun r hr => by rw [g₃.gpr, u₂.other r hr, h.gpr r hr], by rw [g₃.rd, u₂.rd, h.rd],
    by rw [g₃.wr, u₂.wr, h.wr], by rw [g₃.sp, u₂.sp, h.sp]⟩, fun j hj => ?_, ?_⟩
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [byte_writeW_ne _ _ _ (by omega) (by omega) (by omega)]; exact h.copied j hj
    · simp only [WriteBytes.writeW8_apply, ite_true]
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

/-- Bytes `0 … k - 1` of `bs` stored. -/
structure StoreI (tmp dst : Reg) (doff : Nat) (bs : List Nat) (s : State) (k : Nat) (s' : State) : Prop
    extends Keep tmp s s' where
  stored : ∀ j < k, s'.mem (s.gpr dst + BitVec.ofNat 64 (doff + j)) = BitVec.ofNat 8 (bs.getD j 0)
  frame : Frame [⟨s.gpr dst + BitVec.ofNat 64 doff, bs.length⟩] s.mem s'.mem

theorem storeBytes_ok {tmp dst : Reg} {doff : Nat} {bs : List Nat} (htd : tmp ≠ dst)
    (hb : ∀ i < bs.length, bs.getD i 0 < 2048) (hd : doff + bs.length ≤ 2048)
    (hw : ∀ i < bs.length, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 (doff + i)) 1) :
    WP isa (.block (storeBytes tmp dst doff bs)) s (StoreI tmp dst doff bs s bs.length) := by
  refine wp_range_flatMap (M := isa) (StoreI tmp dst doff bs s) (fun k s₁ hk h => ?_) bs.length
    (Nat.le_refl _) s ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, fun _ h => absurd h (by omega), Frame.refl _ _⟩
  have hdst : s₁.gpr dst = s.gpr dst := h.gpr _ (Ne.symm htd)
  refine wp_li (imm := bs.getD k 0) (hb k hk) fun s₂ u₂ => ?_
  refine wp_sb (a := s.gpr dst + BitVec.ofNat 64 (doff + k)) (by omega)
    (by rw [u₂.other _ (Ne.symm htd), hdst]) (by rw [u₂.wr, h.wr]; exact hw k hk) fun s₃ g₃ =>
    WP.block_nil ?_
  have hm : s₃.mem = s₁.mem.writeW (s.gpr dst + BitVec.ofNat 64 (doff + k)) (BitVec.ofNat 8 (bs.getD k 0)) := by
    rw [g₃.mem, u₂.gpr, setWidth_ofNat_byte, u₂.mem]
  refine ⟨⟨fun r hr => by rw [g₃.gpr, u₂.other r hr, h.gpr r hr], by rw [g₃.rd, u₂.rd, h.rd],
    by rw [g₃.wr, u₂.wr, h.wr], by rw [g₃.sp, u₂.sp, h.sp]⟩, fun j hj => ?_, ?_⟩
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [byte_writeW_ne _ _ _ (by omega) (by omega) (by omega)]; exact h.stored j hj
    · simp only [WriteBytes.writeW8_apply, ite_true]
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

/-! ## Doublewords as two words -/

/-- Two doublewords with the same bytes are equal. -/
theorem dword_ext {x y : BitVec 64} (h : ∀ i < 8, x.extractLsb' (8 * i) 8 = y.extractLsb' (8 * i) 8) :
    x = y := by
  ext j hj
  have := congrArg (·.getLsbD (j % 8)) (h (j / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show j % 8 < 8 by omega, decide_true,
    Bool.true_and] at this
  rw [show 8 * (j / 8) + j % 8 = j by omega] at this
  simpa [BitVec.getLsbD_eq_getElem hj] using this

/-- Byte `j` of a little-endian doubleword. -/
theorem readW64_byte (m : Mem) (a : Addr) {j : Nat} (hj : j < 8) :
    (m.readW a 64).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 64 j) := by
  rw [← Mem.extractLsb'_read m a (n := 8) hj]
  simp only [Mem.readW]
  rfl

/-- A doubleword from its words, as `loadLE64` combines them. -/
theorem readW64_words (m : Mem) (a : Addr) :
    (m.readW (a + BitVec.ofNat 64 4) 32).setWidth 64 <<< 32 ||| (m.readW a 32).setWidth 64 =
      m.readW a 64 := by
  refine dword_ext fun j hj => ?_
  rw [readW64_byte _ _ hj]
  by_cases h : j < 4
  · rw [Mem.readW_byte m a h]
    ext k hk
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth]
    simp [show 8 * j + k < 32 by omega, show 8 * j + k < 64 by omega]
  · rw [show j = 4 + (j - 4) by omega, ← Offset.add_add, Mem.readW_byte m (a + BitVec.ofNat 64 4) (show j - 4 < 4 by omega)]
    ext k hk
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth]
    simp [show ¬ 8 * (4 + (j - 4)) + k < 32 by omega, show 8 * (4 + (j - 4)) + k < 64 by omega,
      show 8 * (4 + (j - 4)) + k - 32 = 8 * (j - 4) + k by omega, show 8 * (j - 4) + k < 32 by omega,
      show 8 * (j - 4) + k < 64 by omega, BitVec.getLsbD_of_ge (m.readW a 32) _ (show 32 ≤ 8 * (4 + (j - 4)) + k by omega)]

theorem loadLE64_ok {d tmp hi n : Reg} {off : Nat} (hdn : d ≠ n) (htn : tmp ≠ n) (hhn : hi ≠ n)
    (hdt : d ≠ tmp) (hdh : d ≠ hi) (hth : tmp ≠ hi) (ho : off + 7 < 2048)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 4)
    (h4 : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 (off + 4)) 4) :
    WP isa (.block (loadLE64 d tmp hi n off)) s fun s' =>
      s'.gpr d = s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64 ∧
      (∀ r, r ≠ d → r ≠ tmp → r ≠ hi → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold loadLE64
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadLE32_ok hdn htn hdt (by omega) h0) fun s₁ e₁ => ?_
  rw [WP.block_append_iff]
  have n₁ : s₁.gpr n = s.gpr n := by
    rw [e₁, RegUpd.gpr_write_of_ne _ _ (Ne.symm hdn), RegUpd.gpr_write_of_ne _ _ (Ne.symm htn)]
  refine WP.mono (loadLE32_ok hhn htn (Ne.symm hth) (by omega)
    (by rw [n₁, e₁]; exact h4)) fun s₂ e₂ => ?_
  have d₂ : s₂.gpr d = (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 32).setWidth 64 := by
    rw [e₂, RegUpd.gpr_write_of_ne _ _ hdh, RegUpd.gpr_write_of_ne _ _ hdt, e₁, RegUpd.gpr_write_self]
  have h₂ : s₂.gpr hi = (s.mem.readW (s.gpr n + BitVec.ofNat 64 (off + 4)) 32).setWidth 64 := by
    rw [e₂, RegUpd.gpr_write_self, n₁, e₁]; rfl
  have g₂ : ∀ r, r ≠ d → r ≠ tmp → r ≠ hi → s₂.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [e₂, RegUpd.gpr_write_of_ne _ _ h₃, RegUpd.gpr_write_of_ne _ _ h₂, e₁,
      RegUpd.gpr_write_of_ne _ _ h₁, RegUpd.gpr_write_of_ne _ _ h₂]
  have m₂ : s₂.mem = s.mem := by rw [e₂, e₁]; rfl
  refine wp_sll (by decide) fun s₃ u₃ => wp_or fun s₄ u₄ => WP.block_nil ?_
  refine ⟨?_, fun r h₁ h₂ h₃ => ?_, by rw [u₄.mem, u₃.mem, m₂], by rw [u₄.rd, u₃.rd, e₂, e₁]; rfl,
    by rw [u₄.wr, u₃.wr, e₂, e₁]; rfl, by rw [u₄.sp, u₃.sp, e₂, e₁]; rfl⟩
  · rw [u₄.gpr, u₃.other _ hdh, u₃.gpr, d₂, h₂, BitVec.or_comm, ← Offset.add_add, readW64_words]
  · rw [u₄.other r h₁, u₃.other r h₃, g₂ r h₁ h₂ h₃]

theorem storeLE64_ok {v tmp hi n : Reg} {off : Nat} (htv : tmp ≠ v) (htn : tmp ≠ n)
    (hhn : hi ≠ n) (hth : tmp ≠ hi) (ho : off + 7 < 2048)
    (h0 : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 4)
    (h4 : InRegions s.wr (s.gpr n + BitVec.ofNat 64 (off + 4)) 4) :
    WP isa (.block (storeLE64 v tmp hi n off)) s fun s' =>
      s'.mem = (s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) ((s.gpr v).setWidth 32)).writeW
        (s.gpr n + BitVec.ofNat 64 (off + 4)) ((s.gpr v >>> 32).setWidth 32) ∧
      (∀ r, r ≠ tmp → r ≠ hi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold storeLE64
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (storeLE32_ok htv htn (by omega) h0) fun s₁ e₁ => ?_
  have n₁ : s₁.gpr n = s.gpr n := by rw [e₁, RegUpd.gpr_write_of_ne _ _ (Ne.symm htn)]
  have v₁ : s₁.gpr v = s.gpr v := by rw [e₁, RegUpd.gpr_write_of_ne _ _ (Ne.symm htv)]
  refine wp_srl (by decide) fun s₂ u₂ => ?_
  refine WP.mono (storeLE32_ok hth htn (by omega)
    (by rw [u₂.other _ (Ne.symm hhn), n₁, u₂.wr, e₁]; exact h4)) fun s₃ e₃ => ?_
  subst e₃
  refine ⟨?_, fun r h₁ h₂ => ?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.mem_write, u₂.other _ (Ne.symm hhn), u₂.gpr, u₂.mem, e₁, RegUpd.gpr_write,
      Ne.symm htn, Ne.symm htv, ite_false]
  · rw [RegUpd.gpr_write_of_ne _ _ h₁]
    show s₂.gpr r = _
    rw [u₂.other r h₂, e₁, RegUpd.gpr_write_of_ne _ _ h₁]
  · rw [RegUpd.rd_write]; exact u₂.rd.trans (by rw [e₁]; rfl)
  · rw [RegUpd.wr_write]; exact u₂.wr.trans (by rw [e₁]; rfl)
  · rw [RegUpd.sp_write]; exact u₂.sp.trans (by rw [e₁]; rfl)

end VG.RISCV64.Bytes
