module

import VerifiedGarbage.Proof.CmacAes.PPC64LE.Subkeys
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.CmacAes.PPC64LE
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.AesCbc.Spec
public import VerifiedGarbage.Proof.Cmac.Block
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK

/-!
# AES-CMAC on PPC64LE: the pieces of `vg_cmac_aes_finalize`

Each straight-line piece before the call, in continuation-passing style: the
block XOR that `full`, `padK2` and `finArgs` do (`xor2_wp`, whose memory is
`Proof.Cmac.xor2Mem`), the branch on `last_len - 16` (`sub16_wp`), the zeroed
block (`zero_wp`), the byte copy (`copy_wp`, whose memory is `writeBytes`)
and the `0x80` after it (`pad_wp`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.PPC64LE
open VG.Spec.Aes (bytesAt)

theorem read1 (m : Mem) (a : Addr) : m.read a 1 = m a := by
  have := Mem.extractLsb'_read m a (n := 1) (j := 0) (by decide)
  rw [BitVec.add_zero] at this
  rw [← this]
  exact (BitVec.extractLsb'_eq_self (x := m.read a 1)).symm

theorem write1 (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : m.write a 1 v = m.writeW a v := by
  simp [Mem.writeW]

theorem byte_rt (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `lbz t, off(n)`. -/
theorem wp_lbz {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.lbz t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem a).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_lbz hn ho (by rw [ha]; exact hin), ha, read1]

/-- `stb t, off(n)`. -/
theorem wp_stb {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.stb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩)
  rw [exec_stb hn ho (by rw [ha]; exact hout), ha, write1]

end

/-- The block XOR `full`, `padK2` and `finArgs` do: the words at `pb + pd` and
`qb + qd` XORed into `cb + cd`. -/
def xor2 (pb qb cb : Reg) (pd qd cd : Nat) : List Instr :=
  [.load .d .r9 pb pd, .load .d .r10 qb qd, .logic .xor .r9 .r9 .r10, .store .d .r9 cb cd,
   .load .d .r9 pb (pd + 8), .load .d .r10 qb (qd + 8), .logic .xor .r9 .r9 .r10, .store .d .r9 cb (cd + 8)]

theorem full_eq : full = xor2 .r6 .r3 .r8 0 240 2048 := rfl

theorem padK2_eq : padK2 = ([.li .r9 0x80, .stb .r9 .r10 0] : List Instr) ++ xor2 .r8 .r3 .r8 2048 256 2048 := rfl

theorem finArgs_eq : finArgs = xor2 .r5 .r8 .r5 0 2048 0 ++
    ([Impl.AesCbc.PPC64LE.mov .r14 .r8, .li .r6 1, Impl.AesCbc.PPC64LE.mov .r7 .r14] : List Instr) := rfl

theorem finSave_eq : finSave = .mflr .r0 :: Spill.saveCode .r8 finSaved := rfl

theorem xor2_wp {s : State} (pb qb cb : Reg) (pd qd cd : Nat) {P Q C : Addr} {rest : List Instr}
    {Φ : State → Prop} (h0 : pb ≠ .r0 ∧ qb ≠ .r0 ∧ cb ≠ .r0)
    (hpd : pd + 8 < 2 ^ 15 ∧ pd % 4 = 0) (hqd : qd + 8 < 2 ^ 15 ∧ qd % 4 = 0)
    (hcd : cd + 8 < 2 ^ 15 ∧ cd % 4 = 0)
    (hp : s.gpr pb + BitVec.ofNat 64 pd = P) (hp8 : s.gpr pb + BitVec.ofNat 64 (pd + 8) = P + BitVec.ofNat 64 8)
    (hq : s.gpr qb + BitVec.ofNat 64 qd = Q) (hq8 : s.gpr qb + BitVec.ofNat 64 (qd + 8) = Q + BitVec.ofNat 64 8)
    (hc : s.gpr cb + BitVec.ofNat 64 cd = C) (hc8 : s.gpr cb + BitVec.ofNat 64 (cd + 8) = C + BitVec.ofNat 64 8)
    (hr : pb ≠ .r9 ∧ pb ≠ .r10 ∧ qb ≠ .r9 ∧ qb ≠ .r10 ∧ cb ≠ .r9 ∧ cb ≠ .r10)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wc : InRegions s.wr C 8) (wc8 : InRegions s.wr (C + BitVec.ofNat 64 8) 8)
    (k : ∀ s', (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) → s'.mem = Proof.Cmac.xor2Mem s.mem C P Q →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block rest) s' Φ) :
    WP isa (.block (xor2 pb qb cb pd qd cd ++ rest)) s Φ := by
  obtain ⟨p9, p10, q9, q10, c9, c10⟩ := hr
  simp only [xor2, List.cons_append, List.nil_append]
  refine wp_ld h0.1 ⟨by omega, hpd.2⟩ hp rp fun s₁ u₁ => ?_
  refine wp_ld h0.2.1 ⟨by omega, hqd.2⟩ (by rw [u₁.other _ q9, hq]) (by rw [u₁.rd, u₁.wr]; exact rq)
    fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_std h0.2.2 ⟨by omega, hcd.2⟩ (by rw [u₃.other _ c9, u₂.other _ c10, u₁.other _ c9, hc])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact wc) fun s₄ u₄ => ?_
  have g₄ (r : Reg) (h9 : r ≠ .r9) (h10 : r ≠ .r10) : s₄.gpr r = s.gpr r := by
    rw [u₄.gpr, u₃.other _ h9, u₂.other _ h10, u₁.other _ h9]
  refine wp_ld h0.1 ⟨by omega, by omega⟩ (by rw [g₄ _ p9 p10, hp8])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rp8) fun s₅ u₅ => ?_
  refine wp_ld h0.2.1 ⟨by omega, by omega⟩ (by rw [u₅.other _ q9, g₄ _ q9 q10, hq8])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rq8)
    fun s₆ u₆ => ?_
  refine wp_xor fun s₇ u₇ => ?_
  refine wp_std h0.2.2 ⟨by omega, by omega⟩ (by rw [u₇.other _ c9, u₆.other _ c10, u₅.other _ c9, g₄ _ c9 c10, hc8])
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact wc8) fun s₈ u₈ => ?_
  refine k s₈ (fun r h9 h10 => ?_) ?_ ?_ ?_
  · rw [u₈.gpr, u₇.other _ h9, u₆.other _ h10, u₅.other _ h9, g₄ _ h9 h10]
  · rw [u₈.mem, u₇.gpr, u₇.mem, u₆.gpr, u₆.other _ (by decide), u₆.mem, u₅.gpr, u₅.mem, u₄.mem,
      u₃.gpr, u₃.mem, u₂.gpr, u₂.other _ (by decide), u₂.mem, u₁.gpr, u₁.mem]
    rfl
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-- `r9 = last_len - 16`, zero exactly for a complete last block. -/
theorem sub16_wp {s : State} {L : Nat} (h7 : s.gpr .r7 = BitVec.ofNat 64 L) (hL : L ≤ 16) :
    WP isa (.block [.subi .r9 .r7 16]) s fun s' => isa.eval (.zero .d .r9) s' = some (decide (L = 16)) ∧
      (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine wp_subi (by decide) (by decide) fun s₁ u₁ => wp_nil ⟨?_, fun r h => u₁.other r h, u₁.mem, u₁.rd, u₁.wr⟩
  rw [eval_zero, u₁.gpr, h7]
  by_cases h : L = 16
  · subst h; rfl
  · have hne : BitVec.ofNat 64 L - BitVec.ofNat 64 16 ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
      have h0 : (0 : BitVec 64).toNat = 0 := rfl
      rw [h0] at this
      omega
    rw [beq_eq_false_iff_ne.mpr hne]; simp [h]

/-- The last block zeroed, with `r10` pointing at it, `r11` at the last bytes
and `r12` counting them. -/
theorem zero_wp {s : State} {C : Addr} (hc : s.gpr .r8 + BitVec.ofNat 64 cOff = C)
    (hc8 : s.gpr .r8 + BitVec.ofNat 64 (cOff + 8) = C + BitVec.ofNat 64 8)
    (w₀ : InRegions s.wr C 8) (w₁ : InRegions s.wr (C + BitVec.ofNat 64 8) 8) :
    WP isa (.block zero) s fun s' => s'.mem = Proof.Cmac.zero2 s.mem C ∧ s'.gpr .r10 = C ∧
      s'.gpr .r11 = s.gpr .r6 ∧ s'.gpr .r12 = s.gpr .r7 ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold zero Impl.AesCbc.PPC64LE.mov
  refine wp_li (by decide) fun s₁ u₁ => ?_
  refine wp_std (by decide) (by decide) (by rw [u₁.other _ (by decide), hc]) (by rw [u₁.wr]; exact w₀)
    fun s₂ u₂ => ?_
  refine wp_std (by decide) (by decide) (by rw [u₂.gpr, u₁.other _ (by decide), hc8])
    (by rw [u₂.wr, u₁.wr]; exact w₁) fun s₃ u₃ => ?_
  refine wp_addi (by decide) (by decide) fun s₄ u₄ => wp_mr fun s₅ u₅ => wp_mr fun s₆ u₆ =>
    wp_nil ⟨?_, ?_, ?_, ?_, fun r h9 h10 h11 h12 => ?_, ?_, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem]; rfl
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hc]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide)]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide)]
  · rw [u₆.other _ h12, u₅.other _ h11, u₄.other _ h10, u₃.gpr, u₂.gpr, u₁.other _ h9]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

theorem succ_ofNat (i : Nat) : BitVec.ofNat 64 i + BitVec.ofNat 64 1 = BitVec.ofNat 64 (i + 1) :=
  (BitVec.ofNat_add i 1).symm

open VG.WriteBytes in
theorem copy_wp (s : State) {P C : Addr} {L : Nat} (hL₀ : 0 < L) (hL : L < 2 ^ 64)
    (h11 : s.gpr .r11 = P) (h10 : s.gpr .r10 = C) (h12 : s.gpr .r12 = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < L, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hd : (⟨P, L⟩ : Region).Disjoint ⟨C, L⟩) :
    WP isa copy s fun s' => s'.mem = writeBytes s.mem C (bytesAt s.mem P L) ∧
      s'.gpr .r10 = C + BitVec.ofNat 64 L ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (c := .nonzero .d .r12)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .r11 = P + BitVec.ofNat 64 i ∧
      t.gpr .r10 = C + BitVec.ofNat 64 i ∧ t.gpr .r12 = BitVec.ofNat 64 (L - i) ∧
      t.mem = writeBytes s.mem C (bytesAt s.mem P i) ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_
    (L - 0) _
    ⟨0, rfl, hL₀, by rw [h11]; simp, by rw [h10]; simp, by rw [h12, Nat.sub_zero],
      by simp [bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, x11, x10, x12, mem, g, rd, wr⟩
  refine wp_lbz (a := P + BitVec.ofNat 64 i) (by decide) (by decide) (by rw [x11, BitVec.add_zero])
    (by rw [rd, wr]; exact hr i hi) fun t₁ u₁ => ?_
  refine wp_stb (a := C + BitVec.ofNat 64 i) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), x10, BitVec.add_zero]) (by rw [u₁.wr, wr]; exact hw i (by omega))
    fun t₂ u₂ => ?_
  refine wp_addi (by decide) (by decide) fun t₃ u₃ => wp_addi (by decide) (by decide) fun t₄ u₄ =>
    wp_subi (by decide) (by decide) fun t₅ u₅ => wp_nil ?_
  have hlen : (bytesAt s.mem P i).length = i := by simp [bytesAt]
  have hx : writeBytes s.mem C (bytesAt s.mem P i) (P + BitVec.ofNat 64 i) = s.mem (P + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem C _ (R := ⟨C, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base P (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t₅.mem = writeBytes s.mem C (bytesAt s.mem P (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, mem, byte_rt, hx, Proof.Cmac.bytesAt_succ,
      writeBytes_snoc s.mem C (bytesAt s.mem P i) (s.mem (P + BitVec.ofNat 64 i)) (by rw [hlen]; omega), hlen]
  have x12' : t₅.gpr .r12 = BitVec.ofNat 64 (L - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), x12,
      Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev := eval_nonzero_ofNat' t₅ .r12 (k := L - (i + 1)) (by omega) x12'
  have x10' : t₅.gpr .r10 = C + BitVec.ofNat 64 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), x10,
      BitVec.add_assoc, succ_ofNat]
  have gg : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t₅.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [u₅.other _ h₄, u₄.other _ h₂, u₃.other _ h₃, u₂.gpr, u₁.other _ h₁, g r h₁ h₂ h₃ h₄]
  have rd₅ : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, rd]
  have wr₅ : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [x10', he], gg, rd₅, wr₅⟩
  · right
    refine ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), x11,
        BitVec.add_assoc, succ_ofNat], x10', x12', hmem, gg, rd₅, wr₅⟩

end VG.Proof.CmacAes.PPC64LE
