module

public import VerifiedGarbage.Impl.CmacAes.PPC64LE
public import VerifiedGarbage.Spec.Cmac.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.CmacAes.PPC64LE.Subkeys
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.CmacAes.PPC64LE.Subkeys
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Loop
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesCbc.PPC64LE
meta import VerifiedGarbage.Impl.CmacAes.PPC64LE
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Loop
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Impl.AesCbc.PPC64LE
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Spec.Cmac
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.AesCbc.Spec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.Spec.Cmac
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Aes.SboxSpec
meta import VerifiedGarbage.Proof.AesCbc.Spec
meta import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
meta import VerifiedGarbage.Proof.Framework.Inline
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK

/-! ### `CmacAes.PPC64LE.CT`, which this module and modules that import it used -/

section

/-! ### `CmacAes.PPC64LE.Finalize`, which this module and modules that import it used -/

section

/-! ### `CmacAes.PPC64LE.FinSteps`, which this module and modules that import it used -/

section

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
  omega_using []

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
  refine wp_ld h0.1 ⟨by omega_using [hpd], hpd.2⟩ hp rp fun s₁ u₁ => ?_
  refine wp_ld h0.2.1 ⟨by omega_using [hqd], hqd.2⟩ (by rw [u₁.other _ q9, hq]) (by rw [u₁.rd, u₁.wr]; exact rq)
    fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_std h0.2.2 ⟨by omega_using [hcd], hcd.2⟩ (by rw [u₃.other _ c9, u₂.other _ c10, u₁.other _ c9, hc])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact wc) fun s₄ u₄ => ?_
  have g₄ (r : Reg) (h9 : r ≠ .r9) (h10 : r ≠ .r10) : s₄.gpr r = s.gpr r := by
    rw [u₄.gpr, u₃.other _ h9, u₂.other _ h10, u₁.other _ h9]
  refine wp_ld h0.1 ⟨by omega_using [hpd], by omega_using [hpd]⟩ (by rw [g₄ _ p9 p10, hp8])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rp8) fun s₅ u₅ => ?_
  refine wp_ld h0.2.1 ⟨by omega_using [hqd], by omega_using [hqd]⟩ (by rw [u₅.other _ q9, g₄ _ q9 q10, hq8])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rq8)
    fun s₆ u₆ => ?_
  refine wp_xor fun s₇ u₇ => ?_
  refine wp_std h0.2.2 ⟨by omega_using [hcd], by omega_using [hcd]⟩ (by rw [u₇.other _ c9, u₆.other _ c10, u₅.other _ c9, g₄ _ c9 c10, hc8])
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
      omega_using [hL, h, this]
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
    (by rw [u₁.other _ (by decide), x10, BitVec.add_zero]) (by rw [u₁.wr, wr]; exact hw i (by omega_using [hi]))
    fun t₂ u₂ => ?_
  refine wp_addi (by decide) (by decide) fun t₃ u₃ => wp_addi (by decide) (by decide) fun t₄ u₄ =>
    wp_subi (by decide) (by decide) fun t₅ u₅ => wp_nil ?_
  have hlen : (bytesAt s.mem P i).length = i := by simp [bytesAt]
  have hx : writeBytes s.mem C (bytesAt s.mem P i) (P + BitVec.ofNat 64 i) = s.mem (P + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem C _ (R := ⟨C, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base P (by omega_using [hi]) (by omega_using [hL, hi])) (Region.sub_prefix (by omega_using [hi]) _ hcon)
  have hmem : t₅.mem = writeBytes s.mem C (bytesAt s.mem P (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, mem, byte_rt, hx, Proof.Cmac.bytesAt_succ,
      writeBytes_snoc s.mem C (bytesAt s.mem P i) (s.mem (P + BitVec.ofNat 64 i)) (by rw [hlen]; omega_using [hL, hi]), hlen]
  have x12' : t₅.gpr .r12 = BitVec.ofNat 64 (L - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), x12,
      Offset.ofNat_sub_ofNat (by omega_using [hi])]; rfl
  have ev := eval_nonzero_ofNat' t₅ .r12 (k := L - (i + 1)) (by omega_using [hL]) x12'
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
    refine ⟨by rw [ev]; simp; omega_using [hi, he], L - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, he],
      by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), x11,
        BitVec.add_assoc, succ_ofNat], x10', x12', hmem, gg, rd₅, wr₅⟩

end VG.Proof.CmacAes.PPC64LE

end

end

/-!
# AES-CMAC on PPC64LE: `vg_cmac_aes_finalize`

The return address and `r14` saved (`Spill.save_ok`), the last block `Mₙ`
formed in the scratch buffer (`full_wp` for a complete block, `partial_wp`
for a partial one, `BPost`), XORed into the state (`finArgs_wp`), the state
enciphered in place, and the registers restored: `CIPH_K(Cₙ₋₁ ⊕ Mₙ)`, the
MAC (`Proof.Cmac.macFull_split`), as on AArch64
(`Proof/CmacAes/AArch64/Aese.lean`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.PPC64LE
open VG.Proof.AesCbc.PPC64LE (CallPre blk_call in_rw)
open VG.Spec.Aes (bytesAt)

/-- The precondition, by name: the key (schedule and subkeys) `W`, the state
`St`, the last bytes `P` (`L` of them), the scratch buffer `S` and the
rounds `R`. -/
structure FPre (s₀ : State) (W St P S : Addr) (L R : Nat) : Prop where
  r3 : s₀.gpr .r3 = W
  r5 : s₀.gpr .r5 = St
  r6 : s₀.gpr .r6 = P
  r7 : (s₀.gpr .r7).toNat = L
  r8 : s₀.gpr .r8 = S
  r4 : (s₀.gpr .r4).toNat = R
  rd : s₀.rd = [⟨W, 272⟩, ⟨P, L⟩]
  wr : s₀.wr = [⟨St, 16⟩, ⟨S, 2176⟩]
  key_st : (⟨W, 272⟩ : Region).Disjoint ⟨St, 16⟩
  key_scr : (⟨W, 272⟩ : Region).Disjoint ⟨S, 2176⟩
  last_st : (⟨P, L⟩ : Region).Disjoint ⟨St, 16⟩
  last_scr : (⟨P, L⟩ : Region).Disjoint ⟨S, 2176⟩
  st_scr : (⟨St, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  key_wrap : W.toNat + 272 ≤ 2 ^ 64
  st_wrap : St.toNat + 16 ≤ 2 ^ 64
  last_wrap : P.toNat + L ≤ 2 ^ 64
  scr_wrap : S.toNat + 2176 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16

theorem FPre.of {s₀ : State} (h : finalizePPC64LE.pre s₀) :
    FPre s₀ (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r8) (s₀.gpr .r7).toNat (s₀.gpr .r4).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes in `m`. -/
abbrev mn (m : Mem) (W P : Addr) (L : Nat) : List Byte :=
  Spec.Cmac.lastBlock 16 (bytesAt m (W + BitVec.ofNat 64 240) 16)
    (bytesAt m (W + BitVec.ofNat 64 256) 16) (bytesAt m P L)

/-- The memory after saving `r14` and the return address. -/
abbrev finMem (s₀ : State) (S : Addr) : Mem := Spill.saveMem s₀.mem S (s₀.write .r0 s₀.lr).gpr finSaved

theorem fin_bound : ∀ p ∈ finSaved, 2064 ≤ p.2 ∧ p.2 + 8 ≤ 2080 := by decide

/-- What the branch on the length leaves: `Mₙ` in the scratch buffer. -/
structure BPost (s₀ : State) (W St P S : Addr) (L : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = W
  r5 : s.gpr .r5 = St
  r8 : s.gpr .r8 = S
  r4 : s.gpr .r4 = s₀.gpr .r4
  keep : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨S + BitVec.ofNat 64 2048, 16⟩] (finMem s₀ S) s.mem
  blk : bytesAt s.mem (S + BitVec.ofNat 64 2048) 16 = mn s₀.mem W P L

/-- Saving the registers changes only their slots. -/
theorem finMem_frame (s₀ : State) (S : Addr) : Frame [⟨S + BitVec.ofNat 64 2064, 16⟩] s₀.mem (finMem s₀ S) :=
  Spill.saveMem_frame (lo := 2064) (n := 16) (fun p hp' => fin_bound p hp') (by decide) _ _ _

theorem slots_scr (S : Addr) : Region.Sub ⟨S + BitVec.ofNat 64 2064, 16⟩ ⟨S, 2176⟩ := Offset.sub_base _ (by decide)

section
variable {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R)
include hp

theorem FPre.inScr {d n : Nat} (h : d + n ≤ 2176) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by have := hp.scr_wrap; omega_arith))

theorem FPre.inKey {d n : Nat} (h : d + n ≤ 272) : InRegions (s₀.rd ++ s₀.wr) (W + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := ⟨W, 272⟩) (by simp) (Offset.contains_base _ h (by have := hp.key_wrap; omega_arith))

theorem FPre.inLast {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (P + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := ⟨P, L⟩) (by simp) (Offset.contains_base _ h (by have := hp.len; omega_arith))

/-- The last block, from the memory after saving the registers. -/
theorem FPre.mn_fin : mn (finMem s₀ S) W P L = mn s₀.mem W P L := by
  have kS (d : Nat) (h : d + 16 ≤ 272) :
      bytesAt (finMem s₀ S) (W + BitVec.ofNat 64 d) 16 = bytesAt s₀.mem (W + BitVec.ofNat 64 d) 16 :=
    Proof.Cmac.bytesAt_frame (finMem_frame s₀ S) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right (slots_scr S)) (by decide)
  rw [mn, mn, kS 240 (by decide), kS 256 (by decide), Proof.Cmac.bytesAt_frame (finMem_frame s₀ S) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.last_scr.sub_right (slots_scr S)) (by have := hp.len; omega_arith)]

end

theorem wr_in {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem full_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) (hL : L = 16)
    {s : State} (hg : ∀ r, r ≠ .r0 → r ≠ .r9 → s.gpr r = s₀.gpr r) (hm : s.mem = finMem s₀ S)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block full) s (BPost s₀ W St P S L) := by
  subst hL
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  rw [full_eq, ← List.append_nil (xor2 _ _ _ _ _ _)]
  refine xor2_wp .r6 .r3 .r8 0 240 2048 (P := P) (Q := W + BitVec.ofNat 64 240) (C := S + BitVec.ofNat 64 2048)
    ⟨by decide, by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by rw [hg _ (by decide) (by decide), hp.r6, BitVec.add_zero]) (by rw [hg _ (by decide) (by decide), hp.r6])
    (by rw [hg _ (by decide) (by decide), hp.r3]) (by rw [hg _ (by decide) (by decide), hp.r3, Offset.add_add])
    (by rw [hg _ (by decide) (by decide), hp.r8]) (by rw [hg _ (by decide) (by decide), hp.r8, Offset.add_add])
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by rw [hrd, hwr]; simpa using hp.inLast (d := 0) (n := 8) (by decide))
    (by rw [hrd, hwr]; exact hp.inLast (d := 8) (n := 8) (by decide))
    (by rw [hrd, hwr]; exact hp.inKey (d := 240) (n := 8) (by decide))
    (by rw [hrd, hwr, Offset.add_add]; exact hp.inKey (d := 248) (n := 8) (by decide))
    (by rw [hwr]; exact hp.inScr (d := 2048) (n := 8) (by decide))
    (by rw [hwr, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
    fun s' g mem rd wr => wp_nil ?_
  have gg (r : Reg) (h₀ : r ≠ .r0) (h₁ : r ≠ .r9) (h₂ : r ≠ .r10) : s'.gpr r = s₀.gpr r := by
    rw [g r h₁ h₂, hg r h₀ h₁]
  refine ⟨by rw [gg _ (by decide) (by decide) (by decide), hp.r3],
    by rw [gg _ (by decide) (by decide) (by decide), hp.r5], by rw [gg _ (by decide) (by decide) (by decide), hp.r8],
    gg _ (by decide) (by decide) (by decide),
    fun r hr => gg r (preserved_ne r hr).1 (preserved_ne r hr).2.2.2.2.2.2.2.1 (preserved_ne r hr).2.2.2.2.2.2.2.2.1,
    by rw [rd, hrd], by rw [wr, hwr], by rw [mem, hm]; exact Proof.Cmac.xor2Mem_frame _ _ _ _, ?_⟩
  rw [mem, hm, Proof.Cmac.xor2Mem_bytes, ← hp.mn_fin]
  · simp only [mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, ite_true]
    exact Proof.Cmac.xor_comm _ _
  · exact (hp.last_scr.symm.sub_left (Offset.sub_base S (d := 2048) (n := 8) (k := 2176) (by decide))).sub_right
      (Offset.sub_base P (d := 8) (n := 8) (k := 16) (by decide))
  · rw [Offset.add_add]
    exact (hp.key_scr.symm.sub_left (Offset.sub_base S (d := 2048) (n := 8) (k := 2176) (by decide))).sub_right
      (Offset.sub_base W (d := 248) (n := 8) (k := 272) (by decide))

open VG.WriteBytes in
theorem partial_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) (hL : L < 16)
    {s : State} (hg : ∀ r, r ≠ .r0 → r ≠ .r9 → s.gpr r = s₀.gpr r) (hm : s.mem = finMem s₀ S)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa partialBlock s (BPost s₀ W St P S L) := by
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  obtain hb : L < 2 ^ 64 := by omega_arith
  obtain h7 : s₀.gpr .r7 = BitVec.ofNat 64 L := by rw [← hp.r7]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨C, hC⟩ : ∃ C, S + BitVec.ofNat 64 2048 = C := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, finMem s₀ S = M := ⟨_, rfl⟩
  obtain dPC : (⟨P, L⟩ : Region).Disjoint ⟨C, 16⟩ := by
    rw [← hC]; exact hp.last_scr.sub_right (Offset.sub_base _ (by decide))
  have dKC (d n : Nat) (h : d + n ≤ 272) : (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨C, 16⟩ := by
    rw [← hC]; exact (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right (Offset.sub_base _ (by decide))
  -- Zero the block.
  refine WP.seq (WP.mono (zero_wp (s := s) (C := C) (by rw [hg _ (by decide) (by decide), hp.r8, ← hC, cOff])
    (by rw [hg _ (by decide) (by decide), hp.r8, ← hC, Offset.add_add, cOff])
    (by rw [hwr, ← hC]; exact hp.inScr (d := 2048) (n := 8) (by decide))
    (by rw [hwr, ← hC, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide)))
    fun s₁ ⟨mem₁, r10₁, r11₁, r12₁, g₁, rd₁, wr₁⟩ => ?_)
  obtain zf : s₁.mem = Proof.Cmac.zero2 M C := by rw [mem₁, hm, hM]
  obtain fz : Frame [⟨C, 16⟩] M (Proof.Cmac.zero2 M C) := Proof.Cmac.frame_store2 _ _ _
  obtain lastZ : bytesAt (Proof.Cmac.zero2 M C) P L = bytesAt M P L :=
    Proof.Cmac.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dPC) (by omega_arith)
  have g₁' (r : Reg) (h₀ : r ≠ .r0) (h₁ : r ≠ .r9) (h₂ : r ≠ .r10) (h₃ : r ≠ .r11) (h₄ : r ≠ .r12) :
      s₁.gpr r = s₀.gpr r := by rw [g₁ r h₁ h₂ h₃ h₄, hg r h₀ h₁]
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
      s₂.mem = writeBytes (Proof.Cmac.zero2 M C) C (bytesAt M P L) ∧ s₂.gpr .r10 = C + BitVec.ofNat 64 L ∧
      (∀ r, r ≠ .r0 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s₂.gpr r = s₀.gpr r) ∧
      s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr) ?_ fun s₂ h₂ => ?_)
  · have ev := eval_zero_ofNat s₁ .r7 hb (by rw [g₁' _ (by decide) (by decide) (by decide) (by decide) (by decide), h7])
    by_cases hL0 : L = 0
    · subst hL0
      refine WP.ite true (by rw [ev]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [zf]; simp [bytesAt, writeBytes_nil], by rw [r10₁]; simp,
        fun r h₀ h₁ h₂ h₃ h₄ => g₁' r h₀ h₁ h₂ h₃ h₄, by rw [rd₁, hrd], by rw [wr₁, hwr]⟩
    · refine WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (copy_wp s₁ (P := P) (C := C) (by omega_arith) (by omega_arith)
        (by rw [r11₁, hg _ (by decide) (by decide), hp.r6]) r10₁
        (by rw [r12₁, hg _ (by decide) (by decide), h7])
        (fun i hi => by rw [rd₁, wr₁, hrd, hwr]; exact hp.inLast (d := i) (n := 1) (by omega_arith))
        (fun i hi => by
          rw [wr₁, hwr, ← hC, Offset.add_add]; exact hp.inScr (d := 2048 + i) (n := 1) (by omega_arith))
        (dPC.sub_right (Region.sub_prefix (by omega_arith)))) ?_
      rintro s₂ ⟨m₂, r10₂, g₂, rd₂, wr₂⟩
      refine ⟨by rw [m₂, zf, lastZ], r10₂, fun r h₀ h₁ h₂ h₃ h₄ => by rw [g₂ r h₁ h₂ h₃ h₄, g₁' r h₀ h₁ h₂ h₃ h₄],
        by rw [rd₂, rd₁, hrd], by rw [wr₂, wr₁, hwr]⟩
  · obtain ⟨m₂, r10₂, g₂, rd₂, wr₂⟩ := h₂
    rw [padK2_eq, List.cons_append, List.cons_append, List.nil_append]
    refine wp_li (by decide) fun s₃ u₃ => ?_
    refine wp_stb (a := C + BitVec.ofNat 64 L) (by decide) (by decide)
      (by rw [u₃.other _ (by decide), r10₂, BitVec.add_zero])
      (by rw [u₃.wr, wr₂, ← hC, Offset.add_add]; exact hp.inScr (d := 2048 + L) (n := 1) (by omega_arith)) fun s₄ u₄ => ?_
    have g₄ (r : Reg) (h₀ : r ≠ .r0) (h₁ : r ≠ .r9) (h₂ : r ≠ .r10) (h₃ : r ≠ .r11) (h₄ : r ≠ .r12) :
        s₄.gpr r = s₀.gpr r := by rw [u₄.gpr, u₃.other _ h₁, g₂ r h₀ h₁ h₂ h₃ h₄]
    obtain r8₄ : s₄.gpr .r8 = S := by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.r8]
    obtain r3₄ : s₄.gpr .r3 = W := by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.r3]
    obtain rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, rd₂]
    obtain wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, wr₂]
    rw [← List.append_nil (xor2 _ _ _ _ _ _)]
    refine xor2_wp .r8 .r3 .r8 2048 256 2048 (P := C) (Q := W + BitVec.ofNat 64 256) (C := C)
      ⟨by decide, by decide, by decide⟩ (by decide) (by decide) (by decide)
      (by rw [r8₄, hC]) (by rw [r8₄, ← hC, Offset.add_add]) (by rw [r3₄]) (by rw [r3₄, Offset.add_add])
      (by rw [r8₄, hC]) (by rw [r8₄, ← hC, Offset.add_add])
      ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
      (by rw [rd₄, wr₄, ← hC]; exact wr_in (hp.inScr (d := 2048) (n := 8) (by decide)))
      (by rw [rd₄, wr₄, ← hC, Offset.add_add]; exact wr_in (hp.inScr (d := 2056) (n := 8) (by decide)))
      (by rw [rd₄, wr₄]; exact hp.inKey (d := 256) (n := 8) (by decide))
      (by rw [rd₄, wr₄, Offset.add_add]; exact hp.inKey (d := 264) (n := 8) (by decide))
      (by rw [wr₄, ← hC]; exact hp.inScr (d := 2048) (n := 8) (by decide))
      (by rw [wr₄, ← hC, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
      fun s₅ g₅ m₅ rd₅ wr₅ => wp_nil ?_
    have gg (r : Reg) (h₀ : r ≠ .r0) (h₁ : r ≠ .r9) (h₂ : r ≠ .r10) (h₃ : r ≠ .r11) (h₄ : r ≠ .r12) :
        s₅.gpr r = s₀.gpr r := by rw [g₅ r h₁ h₂, g₄ r h₀ h₁ h₂ h₃ h₄]
    obtain hlen : (bytesAt M P L).length = L := Proof.Cmac.bytesAt_length _ _ _
    obtain m₄ : s₄.mem = (writeBytes (Proof.Cmac.zero2 M C) C (bytesAt M P L)).writeW
        (C + BitVec.ofNat 64 L) (0x80 : Byte) := by
      rw [u₄.mem, u₃.gpr, u₃.mem, m₂]; rfl
    obtain fW : Frame [⟨C, 16⟩] (writeBytes (Proof.Cmac.zero2 M C) C (bytesAt M P L)) s₄.mem := by
      rw [m₄]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
    obtain fB : Frame [⟨C, 16⟩] (Proof.Cmac.zero2 M C) (writeBytes (Proof.Cmac.zero2 M C) C (bytesAt M P L)) :=
      writeBytes_frame _ _ _ (by
        rw [hlen]; simpa using Offset.contains_base C (d := 0) (n := L) (k := 16) (by omega_arith) (by decide))
    obtain f₄ : Frame [⟨C, 16⟩] M s₄.mem := (fz.trans fB).trans fW
    obtain k2 : bytesAt s₄.mem (W + BitVec.ofNat 64 256) 16 = bytesAt M (W + BitVec.ofNat 64 256) 16 :=
      Proof.Cmac.bytesAt_frame16 f₄ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dKC 256 16 (by decide)
    obtain pad : bytesAt s₄.mem C 16 = bytesAt M P L ++ [0x80] ++ Spec.Cmac.zeros (16 - L - 1) := by
      have := Proof.Cmac.padded_bytes (Proof.Cmac.zero2 M C) C (bytesAt M P L)
        (by rw [hlen]; exact hL) (Proof.Cmac.zero2_bytes _ _)
      rw [hlen] at this
      rw [m₄]; exact this
    refine ⟨by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.r3],
      by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.r5],
      by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.r8],
      gg _ (by decide) (by decide) (by decide) (by decide) (by decide),
      fun r hr => gg r (preserved_ne r hr).1 (preserved_ne r hr).2.2.2.2.2.2.2.1 (preserved_ne r hr).2.2.2.2.2.2.2.2.1
        (preserved_ne r hr).2.2.2.2.2.2.2.2.2.1 (preserved_ne r hr).2.2.2.2.2.2.2.2.2.2,
      by rw [rd₅, rd₄], by rw [wr₅, wr₄], ?_, ?_⟩
    · rw [m₅, hC, hM]; exact f₄.trans (Proof.Cmac.xor2Mem_frame _ _ _ _)
    · rw [m₅, hC, Proof.Cmac.xor2Mem_bytes, pad, k2, ← hp.mn_fin, hM]
      · simp only [mn, Spec.Cmac.lastBlock, hlen, show L ≠ 16 by omega_arith, ite_false]
        exact Proof.Cmac.xor_comm _ _
      · simpa using Offset.disjoint C (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)
      · rw [Offset.add_add]
        exact (dKC 264 8 (by decide)).symm.sub_left (Region.sub_prefix (by decide))

/-! ## Up to the call -/

/-- What the code before the call leaves. -/
structure FMid (s₀ : State) (W St P S : Addr) (L R : Nat) (s : State) : Prop where
  pre : CallPre s W St S R
  r14 : s.gpr .r14 = S
  keep : ∀ r ∈ preserved, r ≠ .r14 → s.gpr r = s₀.gpr r
  frame : Frame [⟨S + BitVec.ofNat 64 2048, 16⟩, ⟨St, 16⟩] (finMem s₀ S) s.mem
  st : bytesAt s.mem St 16 = Spec.Cmac.xor (bytesAt s₀.mem St 16) (mn s₀.mem W P L)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finArgs_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) {s : State}
    (h : BPost s₀ W St P S L s) : WP isa (.block finArgs) s (FMid s₀ W St P S L R) := by
  have sw := hp.scr_wrap
  have tw := hp.st_wrap
  obtain hRegs : s.rd ++ s.wr = [⟨W, 272⟩, ⟨P, L⟩, ⟨St, 16⟩, ⟨S, 2176⟩] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have inC (d : Nat) (hd : d + 8 ≤ 2176) : InRegions s.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [h.wr]; exact hp.inScr (by omega_arith)
  have inSt (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (St + BitVec.ofNat 64 d) 8 := by
    rw [h.wr, hp.wr]; exact in_rw (r := ⟨St, 16⟩) (by simp) (Offset.contains_base _ hd (by omega_arith))
  obtain dCSt : (⟨S + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨St, 16⟩ :=
    hp.st_scr.symm.sub_left (Offset.sub_base _ (by decide))
  rw [finArgs_eq]
  refine xor2_wp .r5 .r8 .r5 0 2048 0 (P := St) (Q := S + BitVec.ofNat 64 2048) (C := St)
    ⟨by decide, by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by rw [h.r5, BitVec.add_zero]) (by rw [h.r5]) (by rw [h.r8]) (by rw [h.r8, Offset.add_add])
    (by rw [h.r5, BitVec.add_zero]) (by rw [h.r5])
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by simpa using wr_in (inSt 0 (by decide))) (wr_in (inSt 8 (by decide)))
    (wr_in (inC 2048 (by decide))) (by rw [Offset.add_add]; exact wr_in (inC 2056 (by decide)))
    (by simpa using inSt 0 (by decide)) (inSt 8 (by decide)) fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  unfold Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ => wp_mr fun s₄ u₄ => wp_nil ?_
  have g (r : Reg) (h₁ : r ≠ .r9) (h₂ : r ≠ .r10) (h₃ : r ≠ .r14) (h₄ : r ≠ .r6) (h₅ : r ≠ .r7) :
      s₄.gpr r = s.gpr r := by
    rw [u₄.other _ h₅, u₃.other _ h₄, u₂.other _ h₃, g₁ r h₁ h₂]
  obtain r14₄ : s₄.gpr .r14 = S := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁ _ (by decide) (by decide), h.r8]
  obtain rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, u₂.rd, rd₁, h.rd]
  obtain wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, u₂.wr, wr₁, h.wr]
  obtain m₄ : s₄.mem = Proof.Cmac.xor2Mem s.mem St St (S + BitVec.ofNat 64 2048) := by
    rw [u₄.mem, u₃.mem, u₂.mem, m₁]
  obtain stS : bytesAt s.mem St 16 = bytesAt s₀.mem St 16 := by
    rw [Proof.Cmac.bytesAt_frame16 h.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dCSt.symm]
    exact Proof.Cmac.bytesAt_frame16 (finMem_frame s₀ S) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (slots_scr S)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hp.rounds, hp.key_st.sub_left (Region.sub_prefix (by decide)),
    (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)),
    hp.st_scr.sub_right (Region.sub_prefix (by decide)), hp.st_wrap, ?_, ?_⟩, r14₄, fun r hr h14 => ?_, ?_, ?_,
    rd₄, wr₄⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r3]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r4, ← hp.r4, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r5]
  · rw [u₄.other _ (by decide), u₃.gpr]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, g₁ _ (by decide) (by decide), h.r8]
  · rw [rd₄, wr₄, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨W, 272⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨St, 16⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
  · rw [wr₄, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨St, 16⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
  · obtain ⟨-, -, -, -, h6, h7, -, h9, h10, -⟩ := preserved_ne r hr
    rw [g r h9 h10 h14 h6 h7, h.keep r hr]
  · rw [m₄]
    exact (h.frame.mono (by simp)).trans ((Proof.Cmac.xor2Mem_frame _ _ _ _).mono (by simp))
  · rw [m₄, Proof.Cmac.xor2Mem_bytes, stS, h.blk]
    · simpa using Offset.disjoint St (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by omega_arith)
    · exact (hp.st_scr.sub_left (Region.sub_prefix (by decide))).sub_right
        (by rw [Offset.add_add]; exact Offset.sub_base _ (by decide))

theorem finPre_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) :
    WP isa finPre s₀ (FMid s₀ W St P S L R) := by
  obtain h7 : s₀.gpr .r7 = BitVec.ofNat 64 L := by rw [← hp.r7]; apply BitVec.eq_of_toNat_eq; simp
  obtain A : WP isa (.block (finSave ++ [.subi .r9 .r7 16])) s₀ fun s =>
      isa.eval (.zero .d .r9) s = some (decide (L = 16)) ∧ (∀ r, r ≠ .r0 → r ≠ .r9 → s.gpr r = s₀.gpr r) ∧
      s.mem = finMem s₀ S ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
    rw [finSave_eq, List.cons_append]
    refine WP.cons exec_mflr (Spill.save_ok (b := .r8) (l := finSaved) (by decide) (by decide) (fun p hp' => ?_) ?_)
    · have := fin_bound p hp'
      show InRegions s₀.wr (s₀.gpr .r8 + BitVec.ofNat 64 p.2) 8
      rw [hp.r8]; exact hp.inScr (by omega_arith)
    have g₀ (r : Reg) (hr : r ≠ .r0) : (s₀.write .r0 s₀.lr).gpr r = s₀.gpr r := by simp [State.write, hr]
    refine WP.mono (sub16_wp (L := L) (by rw [g₀ _ (by decide), h7]) hp.len) fun s₁ ⟨ev, g, m, rd, wr⟩ =>
      ⟨ev, fun r h0 h9 => by rw [g r h9]; exact g₀ r h0, ?_, rd, wr⟩
    rw [m]; show Spill.saveMem _ _ _ _ = _; rw [g₀ .r8 (by decide), hp.r8]; rfl
  refine WP.seq (WP.mono A fun s₁ ⟨ev₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := BPost s₀ W St P S L) ?_ fun _ h => finArgs_wp hp h)
  by_cases hL : L = 16
  · exact WP.ite true (by rw [ev₁]; simp [hL]) (fun _ => full_wp hp hL g₁ m₁ rd₁ wr₁) (fun h => by cases h)
  · exact WP.ite false (by rw [ev₁]; simp [hL]) (fun h => by cases h)
      (fun _ => partial_wp hp (by have := hp.len; omega_arith) g₁ m₁ rd₁ wr₁)

theorem finalize_wp {s₀ : State} (h0 : finalizePPC64LE.pre s₀) :
    WP isa finalize s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧
      finalizePPC64LE.post s₀ s' := by
  obtain hp := FPre.of h0
  generalize hW : s₀.gpr .r3 = W at hp
  generalize hSt : s₀.gpr .r5 = St at hp
  generalize hP : s₀.gpr .r6 = P at hp
  generalize hS : s₀.gpr .r8 = S at hp
  generalize hL : (s₀.gpr .r7).toNat = L at hp
  generalize hR : (s₀.gpr .r4).toNat = R at hp
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_arith
  have sw := hp.scr_wrap
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (blk_call (name := "vg_aes_encrypt_blocks") Proof.Aes.PPC64LE.encryptBlocks_correct
    AesCbc.PPC64LE.encryptBlocks_noFrames h₁.pre) fun s₂ c => ?_)
  obtain slotD : ∀ p ∈ finSaved, ∀ r ∈ [⟨S + BitVec.ofNat 64 2048, 16⟩, ⟨St, 16⟩, ⟨S, 2048⟩],
      Region.Disjoint ⟨S + BitVec.ofNat 64 p.2, 8⟩ r := by
    intro p hp' r hr
    obtain hb := fin_bound p hp'
    obtain hsub : Region.Sub ⟨S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 2176⟩ := Offset.sub_base _ (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint S (by omega_arith) (by omega_arith) (by omega_arith)
    · exact hp.st_scr.symm.sub_left hsub
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  obtain hsv : Spill.Saved S (s₀.write .r0 s₀.lr).gpr finSaved s₂.mem :=
    ((Spill.saveMem_saved (by decide) s₀.mem S _).frame h₁.frame fun p hp' r hr =>
      slotD p hp' r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl
        · exact .inl rfl
        · exact .inr (.inl rfl))).frame
      c.frame fun p hp' r hr => slotD p hp' r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl
        · exact .inr (.inl rfl)
        · exact .inr (.inr rfl))
  obtain r14₂ : s₂.gpr .r14 = S := by rw [c.saved _ (by decide), h₁.r14]
  obtain rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, h₁.rd, h₁.wr]
  rw [show finSaved.map (fun (r, d) => Instr.load .d r .r14 d) = Spill.restoreCode .r14 finSaved from rfl]
  refine Spill.restore_ok (b := .r14) (l := finSaved) (by decide) r14₂ (by decide) (by decide)
    (fun p hp' => ?_) hsv fun s₃ r₃ => WP.cons exec_mtlr (wp_nil ⟨fun r hr => ?_, ?_, ?_⟩)
  · have := fin_bound p hp'
    rw [rdwr₂]; exact wr_in (hp.inScr (by omega_arith))
  · show s₃.gpr r = _
    obtain h0 : (s₀.write .r0 s₀.lr).gpr r = s₀.gpr r := by simp [State.write, (preserved_ne r hr).1]
    rw [r₃.gpr_of (r := r) ?_, h0]
    by_cases h14 : r = .r14
    · left; subst h14; decide
    · right; rw [c.saved r hr, h₁.keep r hr h14, h0]
  · show s₃.gpr .r0 = _
    rw [r₃.gpr (.r0, 2064) (by decide)]; simp [State.write]
  · intro hk msg hm hne hst
    rw [hW, hR] at hk hst ⊢
    rw [hSt] at hst ⊢
    rw [hL] at hne
    rw [hP, hL]
    obtain sch : bytesAt s₁.mem W (16 * (R + 1)) = bytesAt s₀.mem W (16 * (R + 1)) := by
      rw [Proof.Cmac.bytesAt_frame h₁.frame (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Offset.sub_base _ (by decide))
          · exact hp.key_st.sub_left (Region.sub_prefix (by omega_arith))) (by omega_arith)]
      exact Proof.Cmac.bytesAt_frame (finMem_frame s₀ S) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.key_scr.sub_left (Region.sub_prefix (by omega_arith))).sub_right (slots_scr S)) (by omega_arith)
    obtain ⟨e1, e2⟩ := Proof.Cmac.k1k2 (Proof.Cmac.subkeys_aes_length _ _) hk
    rw [r₃.mem, c.out, cipher_bytes, sch, h₁.st, mn, e1, e2, hst,
      Proof.Cmac.macFull_split _ hm (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
        (by rw [Proof.Cmac.bytesAt_length]; exact hne)]

end VG.Proof.CmacAes.PPC64LE

end

end

/-! ### `CmacAes.PPC64LE.Update`, which only this module used -/

section

/-!
# AES-CMAC on PPC64LE: `vg_cmac_aes_update`

AES-CBC's registers, prologue and epilogue (`Proof/AesCbc/PPC64LE/Loop.lean`),
with the chaining value at `state` and the data only read: the invariant
after `k` blocks (`UInv`) has the state `C` chained over the first `k`
blocks (`Spec.Cmac.chain`), and each block (`body_ok`) XORs the next block
into the state and enciphers it in place.
-/

@[expose] public section

namespace VG.Proof.CmacAes.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.PPC64LE
open VG.Impl.AesCbc.PPC64LE (save setup restore xorInto advance whole lrOff saved)
open VG.Proof.AesCbc.PPC64LE (W R Iv Dp N S schR ivR dataR scrR blk saveL saveG savedMem vars wK
  saved_bound savedMem_frame in_rw r4_ofNat r7_ofNat advance_regs save_eq restore_eq preserved_ne_r0
  xorInto_wp CallPre blk_call bytesAt_frame)
open VG.Proof.AesCbc (xorMem xorMem_frame xorMem_bytes)
open VG.Spec.Aes (bytesAt)

/-- The blocks on entry. -/
abbrev cblks (s₀ : State) : List (List Byte) := Spec.Cmac.blocksAt s₀.mem (Dp s₀) 16 (N s₀)

/-- `CIPH_K`. -/
abbrev ciph (s₀ : State) : Spec.Cmac.Cipher := ciphAt s₀.mem (W s₀) (R s₀)

/-- The state on entry. -/
abbrev st0 (s₀ : State) : List Byte := bytesAt s₀.mem (Iv s₀) 16

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, dataR s₀]
  wr : s₀.wr = [ivR s₀, scrR s₀]
  sch_st : (schR s₀).Disjoint (ivR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  data_st : (dataR s₀).Disjoint (ivR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  st_scr : (ivR s₀).Disjoint (scrR s₀)
  st_wrap : (Iv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (Dp s₀).toNat + 16 * N s₀ ≤ 2 ^ 64
  scr_wrap : (S s₀).toNat + 2176 ≤ 2 ^ 64
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {s₀ : State} (h : updatePPC64LE.pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k⟩

/-- The loop invariant, after `k` blocks. -/
structure UInv (s₀ : State) (k : Nat) (s : State) : Prop where
  r14 : s.gpr .r14 = W s₀
  r15 : s.gpr .r15 = s₀.gpr .r4
  r16 : s.gpr .r16 = Iv s₀
  r17 : s.gpr .r17 = blk s₀ k
  r18 : s.gpr .r18 = BitVec.ofNat 64 (N s₀ - k)
  r19 : s.gpr .r19 = S s₀
  keep : ∀ r ∈ preserved, r ∉ vars → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, ⟨S s₀, 2064⟩] (savedMem s₀) s.mem
  st : bytesAt s.mem (Iv s₀) 16 = Spec.Cmac.chain (ciph s₀) (st0 s₀) ((cblks s₀).take k)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

omit hp in
/-- Memory after saving the registers and changing at most the state and
the first 2064 bytes of the scratch buffer. -/
theorem UPre.of_frame {m : Mem} (hf : Frame [ivR s₀, ⟨S s₀, 2064⟩] (savedMem s₀) m) :
    Frame [ivR s₀, scrR s₀] s₀.mem m :=
  ((savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, AesCbc.PPC64LE.UPre.scr_sub (by decide)⟩).trans
    (hf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩)

theorem UPre.sched {m : Mem} (hf : Frame [ivR s₀, scrR s₀] s₀.mem m) :
    bytesAt m (W s₀) (16 * (R s₀ + 1)) = wK s₀ := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine bytesAt_frame hf (fun r hr => ?_) (by omega_using [hR])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.sch_st.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)

omit hp in
theorem UPre.blk_sub {k : Nat} (hk : k < N s₀) : Region.Sub ⟨blk s₀ k, 16⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_using [hk])

theorem UPre.block {m : Mem} (hf : Frame [ivR s₀, scrR s₀] s₀.mem m) {k : Nat} (hk : k < N s₀) :
    bytesAt m (blk s₀ k) 16 = (cblks s₀)[k]'(by simp [Spec.Cmac.blocksAt]; exact hk) := by
  rw [bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.data_st.sub_left (UPre.blk_sub hk)
    · exact hp.data_scr.sub_left (UPre.blk_sub hk)) (by decide)]
  simp [Spec.Cmac.blocksAt, blk]

end

/-! ## The prologue -/

theorem prologue_wp {s₀ : State} (hp : UPre s₀) : WP isa (.block (save ++ setup)) s₀ (UInv s₀ 0) := by
  have hN := (s₀.gpr .r7).isLt
  rw [save_eq, List.cons_append]
  refine WP.cons exec_mflr (Spill.save_ok (b := .r8) (l := saveL) (by decide) (by decide) (fun p hp' => ?_) ?_)
  · have := saved_bound p hp'
    show InRegions s₀.wr (S s₀ + BitVec.ofNat 64 p.2) 8
    rw [hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega_using [this]) (by omega_using [this]))
  unfold setup Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_mr fun s₄ u₄ =>
    wp_mr fun s₅ u₅ => wp_mr fun s₆ u₆ => wp_nil ?_
  have m₆ : s₆.mem = savedMem s₀ := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; rfl
  have g₀ (r : Reg) (hr : r ≠ .r0) : (s₀.write .r0 s₀.lr).gpr r = s₀.gpr r := by
    simp [State.write, hr]
  have stS : bytesAt (savedMem s₀) (Iv s₀) 16 = st0 s₀ :=
    bytesAt_frame (savedMem_frame s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (AesCbc.PPC64LE.UPre.scr_sub (by decide))) (by decide)
  exact {
    r14 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr]; exact g₀ .r3 (by decide)
    r15 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.other _ (by decide)]; exact g₀ .r4 (by decide)
    r16 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact g₀ .r5 (by decide)
    r17 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), g₀ .r6 (by decide)]; simp [blk]
    r18 := by
      rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), g₀ .r7 (by decide), r7_ofNat]; rfl
    r19 := by
      rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact g₀ .r8 (by decide)
    keep := fun r hr hv => by
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
      obtain ⟨h14, h15, h16, h17, h18, h19⟩ := hv
      rw [u₆.other _ h19, u₅.other _ h18, u₄.other _ h17, u₃.other _ h16, u₂.other _ h15, u₁.other _ h14]
      exact g₀ _ (preserved_ne_r0 r hr)
    rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; rfl
    wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; rfl
    frame := by rw [m₆]; exact Frame.refl _ _
    st := by rw [m₆, stS, List.take_zero]; rfl }

/-! ## One block -/

/-- The arguments of the call on the state. -/
theorem updArgs_wp {s₀ : State} (hp : UPre s₀) {s : State} (r14 : s.gpr .r14 = W s₀)
    (r15 : s.gpr .r15 = s₀.gpr .r4) (r16 : s.gpr .r16 = Iv s₀) (r19 : s.gpr .r19 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block updArgs) s fun s' => CallPre s' (W s₀) (Iv s₀) (S s₀) (R s₀) ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold updArgs Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ =>
    wp_mr fun s₅ u₅ => wp_nil ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, hp.rounds, hp.sch_st,
      hp.sch_scr.sub_right (Region.sub_prefix (by decide)),
      hp.st_scr.sub_right (Region.sub_prefix (by decide)), hp.st_wrap, ?_, ?_⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.gpr, r14]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
        u₁.other _ (by decide), r15, r4_ofNat]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
        u₁.other _ (by decide), r16]
    · rw [u₅.other _ (by decide), u₄.gpr]
    · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), r19]
    · rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
    · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  · obtain ⟨-, h3, h4, h5, h6, h7, -⟩ := preserved_ne r hr
    rw [u₅.other _ h7, u₄.other _ h6, u₃.other _ h5, u₂.other _ h4, u₁.other _ h3]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-- The block XORed into the state, and the arguments of the call. -/
theorem bodyPre_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : UInv s₀ k s) :
    WP isa (.block (xorInto .r16 .r17 ++ updArgs)) s fun s' =>
      CallPre s' (W s₀) (Iv s₀) (S s₀) (R s₀) ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = xorMem s.mem (Iv s₀) (blk s₀ k) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hR : s.rd ++ s.wr = [schR s₀, dataR s₀, ivR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [ivR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have dw := hp.data_wrap
  have cB0 : (dataR s₀).Contains (blk s₀ k) 8 := Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk, dw])
  have cB8 : (dataR s₀).Contains (blk s₀ k + BitVec.ofNat 64 8) 8 := by
    rw [Offset.add_add]; exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk, dw])
  refine xorInto_wp (P := Iv s₀) (Q := blk s₀ k) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h.r16 h.r17
    (by rw [hR]; exact in_rw (by simp) AesCbc.PPC64LE.cIv0) (by rw [hR]; exact in_rw (by simp) AesCbc.PPC64LE.cIv8)
    (by rw [hR]; exact in_rw (by simp) cB0) (by rw [hR]; exact in_rw (by simp) cB8)
    (by rw [hW]; exact in_rw (by simp) AesCbc.PPC64LE.cIv0) (by rw [hW]; exact in_rw (by simp) AesCbc.PPC64LE.cIv8)
    fun s₁ g₁ mem₁ rd₁ wr₁ => ?_
  have g₁' (r : Reg) (hr : r ∈ preserved) : s₁.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, -, -, h9, h10, -⟩ := preserved_ne r hr
    exact g₁ r h9 h10
  exact WP.mono (updArgs_wp hp (by rw [g₁' _ (by decide), h.r14]) (by rw [g₁' _ (by decide), h.r15])
    (by rw [g₁' _ (by decide), h.r16]) (by rw [g₁' _ (by decide), h.r19]) (by rw [rd₁, h.rd])
    (by rw [wr₁, h.wr])) fun s₂ ⟨c, g₂, mem₂, rd₂, wr₂⟩ =>
      ⟨c, fun r hr => by rw [g₂ r hr, g₁' r hr], by rw [mem₂, mem₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

theorem body_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : UInv s₀ k s) :
    WP isa body s (UInv s₀ (k + 1)) := by
  have bS : (⟨Iv s₀, 16⟩ : Region).Disjoint ⟨blk s₀ k, 16⟩ := hp.data_st.symm.sub_right (UPre.blk_sub hk)
  have pre := bodyPre_wp hp hk h
  refine WP.seq (WP.mono pre fun s₂ ⟨c₂, g₂, mem₂, rd₂, wr₂⟩ => WP.seq (WP.mono (blk_call (name := "vg_aes_encrypt_blocks")
    Proof.Aes.PPC64LE.encryptBlocks_correct AesCbc.PPC64LE.encryptBlocks_noFrames c₂) fun s₃ c => ?_))
  have g₃ (r : Reg) (hr : r ∈ preserved) : s₃.gpr r = s.gpr r := by rw [c.saved r hr, g₂ r hr]
  refine advance_regs (s := s₃) hk (by rw [g₃ _ (by decide), h.r17]) (by rw [g₃ _ (by decide), h.r18])
    fun s₄ r17₄ r18₄ keep₄ mem₄ rd₄ wr₄ => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h17 : r ≠ .r17) (h18 : r ≠ .r18) : s₄.gpr r = s.gpr r := by
    rw [keep₄ r h17 h18, g₃ r hr]
  -- Memory.
  have f₂ : Frame [ivR s₀] s.mem s₂.mem := by rw [mem₂]; exact xorMem_frame _ _ _
  have fStep : Frame [ivR s₀, ⟨S s₀, 2064⟩] s.mem s₄.mem := by
    rw [mem₄]
    refine (f₂.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
  have big : Frame [ivR s₀, scrR s₀] s₀.mem s₂.mem :=
    (UPre.of_frame h.frame).trans (f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  have blkB : bytesAt s.mem (blk s₀ k) 16 = (cblks s₀)[k]'(by simp [Spec.Cmac.blocksAt]; exact hk) :=
    hp.block (UPre.of_frame h.frame) hk
  have newSt : bytesAt s₄.mem (Iv s₀) 16 =
      Spec.Cmac.chain (ciph s₀) (st0 s₀) ((cblks s₀).take (k + 1)) := by
    rw [mem₄, c.out, cipher_bytes, hp.sched big, mem₂, xorMem_bytes _ bS, h.st, blkB,
      List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; exact hk), Option.toList_some,
      Proof.Cmac.chain_append, Proof.Cmac.chain_single]
    rfl
  refine ⟨?_, ?_, ?_, r17₄, r18₄, ?_, fun r hr hv => ?_, ?_, ?_, h.frame.trans fStep, newSt⟩
  · rw [g .r14 (by decide) (by decide) (by decide), h.r14]
  · rw [g .r15 (by decide) (by decide) (by decide), h.r15]
  · rw [g .r16 (by decide) (by decide) (by decide), h.r16]
  · rw [g .r19 (by decide) (by decide) (by decide), h.r19]
  · rw [g r hr (fun e => hv (by simp [e])) (fun e => hv (by simp [e])), h.keep r hr hv]
  · rw [rd₄, c.rd, rd₂, h.rd]
  · rw [wr₄, c.wr, wr₂, h.wr]

/-! ## The loop, and the whole function -/

theorem loop_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : UInv s₀ k s) :
    WP isa (.loop body (.nonzero .d .r18)) s (UInv s₀ (N s₀)) := by
  have hN := (s₀.gpr .r7).isLt
  refine WP.loop (M := isa) (body := body) (c := .nonzero .d .r18) (Q := UInv s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ UInv s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok hp hk h) fun s' h' => ?_
  have ev := eval_nonzero_ofNat' s' .r18 (k := N s₀ - (k + 1)) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN) h'.r18
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega_using [hk, hz]]
  · right
    refine ⟨by rw [ev]; simp [hz], N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hz], h'⟩

theorem mid_wp {s₀ : State} (hp : UPre s₀) {s₁ : State} (h : UInv s₀ 0 s₁) :
    WP isa (.ite (.zero .d .r18) (.block []) (.loop body (.nonzero .d .r18))) s₁ (UInv s₀ (N s₀)) := by
  have hN := (s₀.gpr .r7).isLt
  have ev := eval_zero_ofNat s₁ .r18 (k := N s₀ - 0) (by omega) h.r18
  rw [Nat.sub_zero] at ev
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hp (by omega_using [hn]) h

/-- The postcondition, but for the stack pointer. -/
def UDone (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧ updatePPC64LE.post s₀ s'

theorem epilogue_wp {s₀ : State} (hp : UPre s₀) {s₂ : State} (h₂ : UInv s₀ (N s₀) s₂) :
    WP isa (.block restore) s₂ (UDone s₀) := by
  have rdwr : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr]
  have hsv : Spill.Saved (S s₀) (saveG s₀) saveL s₂.mem :=
    (Spill.saveMem_saved (by decide) _ _ _).frame h₂.frame fun p hp' r hr => by
      have hb := saved_bound p hp'
      have hsub : Region.Sub ⟨S s₀ + BitVec.ofNat 64 p.2, 8⟩ (scrR s₀) := AesCbc.PPC64LE.UPre.scr_sub (by omega_using [hb])
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.st_scr.symm.sub_left hsub
      · exact Offset.disjoint_base _ (by omega_using [hb]) (by have := hp.scr_wrap; omega_using [hb])
  have hall : (cblks s₀).take (N s₀) = cblks s₀ := List.take_of_length_le (by simp [Spec.Cmac.blocksAt])
  rw [restore_eq]
  refine Spill.restore_ok (b := .r19) (l := saveL) (by decide) h₂.r19 (by decide) (by decide)
    (fun p hp' => ?_) hsv fun s₃ r₃ => ?_
  · have := saved_bound p hp'
    rw [rdwr, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega_using [this]) (by have := hp.scr_wrap; omega_arith))
  refine WP.cons exec_mtlr (wp_nil ⟨fun r hr => ?_, ?_, ?_⟩)
  · show s₃.gpr r = _
    have h0 : saveG s₀ r = s₀.gpr r := ite_eq_right_iff.mpr fun h => absurd h (preserved_ne_r0 r hr)
    rw [r₃.gpr_of (r := r) ?_, h0]
    by_cases hv : r ∈ vars
    · left
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · right; rw [h₂.keep r hr hv, h0]
  · show s₃.gpr .r0 = _
    rw [r₃.gpr (.r0, lrOff) (by decide)]; rfl
  · show bytesAt s₃.mem (s₀.gpr .r5) 16 = _
    rw [r₃.mem, h₂.st, hall]

theorem update_wp {s₀ : State} (h0 : updatePPC64LE.pre s₀) : WP isa update s₀ (UDone s₀) := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ h₁ =>
    WP.seq (WP.mono (mid_wp hp h₁) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.CmacAes.PPC64LE

end

end

/-!
# AES-CMAC on PPC64LE: constant time

As for AES-CBC (`Proof/AesCbc/PPC64LE/CT.lean`): two runs from states that
agree on the public arguments are related piece by piece (`RelCT`): the
taint analysis covers the code between the calls, from the registers the
correctness proofs pin to public values and the stack pointer, which no code
changes (`wp_sp`), and each call of `vg_aes_encrypt_blocks` is constant time
by its own proof (`blk_rel`). The branches of `update` are on `n`, and of
`finalize` on `last_len`, which are public.
-/

@[expose] public section

namespace VG.Proof.CmacAes.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.PPC64LE
open VG.Impl.AesCbc.PPC64LE (save setup restore encCall)
open VG.Proof.AesCbc.PPC64LE (W R Iv Dp N S blk vars CallPre CallPost blk_call blk_rel taintRegs wp_sp)

/-! ## `vg_cmac_aes_subkeys` -/

theorem subkeys_rel {s₀ s₀' : State} (h0 : subkeysPPC64LE.pre s₀) (h0' : subkeysPPC64LE.pre s₀')
    (hq : subkeysPPC64LE.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') subkeys fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp := SPre.of h0
  have hp' : SPre s₀' (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r4).toNat := by
    rw [q1, q2, q3, q4]; exact SPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6]) (.block subkeysPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r14, .r15]) (.block subkeysPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.r3, .r4, .r5, .r6]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨q5, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := fun (s : State) => SkMid s₀ (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r4).toNat s ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => SkMid s₀' (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r4).toNat s ∧
      s.sp = s₀'.sp)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨wp_sp (subkeysPre_wp hp), wp_sp (subkeysPre_wp hp')⟩
  have c := (blk_rel (name := "vg_aes_encrypt_blocks") Proof.Aes.PPC64LE.encryptBlocks_correct
      Proof.Aes.PPC64LE.encryptBlocks_ct (P := fun s₁ s₂ =>
      (SkMid s₀ (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r4).toNat s₁ ∧ s₁.sp = s₀.sp) ∧
      (SkMid s₀' (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r4).toNat s₂ ∧ s₂.sp = s₀'.sp)) fun s₁ s₂ h =>
      ⟨h.1.1.pre, h.2.1.pre, by rw [h.1.2, h.2.2, q5]⟩).wp
    (F₁ := fun (s : State) => s.gpr .r14 = s₀.gpr .r5 ∧ s.gpr .r15 = s₀.gpr .r6 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .r14 = s₀.gpr .r5 ∧ s.gpr .r15 = s₀.gpr .r6 ∧ s.sp = s₀'.sp)
    fun s₁ s₂ h =>
      ⟨WP.mono (blk_call Proof.Aes.PPC64LE.encryptBlocks_correct AesCbc.PPC64LE.encryptBlocks_noFrames h.1.1.pre)
        fun _ hc => ⟨by rw [hc.saved .r14 (by decide), h.1.1.r14], by rw [hc.saved .r15 (by decide), h.1.1.r15],
          by rw [hc.sp, h.1.2]⟩,
       WP.mono (blk_call Proof.Aes.PPC64LE.encryptBlocks_correct AesCbc.PPC64LE.encryptBlocks_noFrames h.2.1.pre)
        fun _ hc => ⟨by rw [hc.saved .r14 (by decide), h.2.1.r14], by rw [hc.saved .r15 (by decide), h.2.1.r15],
          by rw [hc.sp, h.2.2]⟩⟩
  have b := taintRegs
    (P := fun s₁ s₂ => (s₁.gpr .r14 = s₀.gpr .r5 ∧ s₁.gpr .r15 = s₀.gpr .r6 ∧ s₁.sp = s₀.sp) ∧
      (s₂.gpr .r14 = s₀.gpr .r5 ∧ s₂.gpr .r15 = s₀.gpr .r6 ∧ s₂.sp = s₀'.sp)) [.r14, .r15]
    (fun s₁ s₂ h => ⟨by rw [h.1.2.2, h.2.2.2, q5], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2.1, h.2.2.1]⟩) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem subkeys_ct : ConstantTime isa subkeysPPC64LE.pre subkeysPPC64LE.pub subkeys :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (subkeys_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `vg_cmac_aes_finalize` -/

theorem finalize_rel {s₀ s₀' : State} (h0 : finalizePPC64LE.pre s₀) (h0' : finalizePPC64LE.pre s₀')
    (hq : finalizePPC64LE.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finalize fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp := FPre.of h0
  have hp' : FPre s₀' (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r8) (s₀.gpr .r7).toNat
      (s₀.gpr .r4).toNat := by
    rw [q1, q2, q3, q4, q5, q6]; exact FPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) finPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r14])
      (.block (finSaved.map (fun (r, d) => Instr.load .d r .r14 d) ++ [.mtlr .r0])) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.r3, .r4, .r5, .r6, .r7, .r8]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨q7, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := fun (s : State) =>
      FMid s₀ (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r8) (s₀.gpr .r7).toNat (s₀.gpr .r4).toNat s ∧
        s.sp = s₀.sp)
    (F₂ := fun (s : State) =>
      FMid s₀' (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r8) (s₀.gpr .r7).toNat (s₀.gpr .r4).toNat s ∧
        s.sp = s₀'.sp)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨wp_sp (finPre_wp hp), wp_sp (finPre_wp hp')⟩
  have c := (blk_rel (name := "vg_aes_encrypt_blocks") Proof.Aes.PPC64LE.encryptBlocks_correct
      Proof.Aes.PPC64LE.encryptBlocks_ct (P := fun s₁ s₂ =>
      (FMid s₀ (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r8) (s₀.gpr .r7).toNat (s₀.gpr .r4).toNat s₁ ∧
        s₁.sp = s₀.sp) ∧
      (FMid s₀' (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r8) (s₀.gpr .r7).toNat (s₀.gpr .r4).toNat s₂ ∧
        s₂.sp = s₀'.sp)) fun s₁ s₂ h => ⟨h.1.1.pre, h.2.1.pre, by rw [h.1.2, h.2.2, q7]⟩).wp
    (F₁ := fun (s : State) => s.gpr .r14 = s₀.gpr .r8 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .r14 = s₀.gpr .r8 ∧ s.sp = s₀'.sp) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call Proof.Aes.PPC64LE.encryptBlocks_correct AesCbc.PPC64LE.encryptBlocks_noFrames h.1.1.pre)
        fun _ hc => ⟨by rw [hc.saved .r14 (by decide), h.1.1.r14], by rw [hc.sp, h.1.2]⟩,
       WP.mono (blk_call Proof.Aes.PPC64LE.encryptBlocks_correct AesCbc.PPC64LE.encryptBlocks_noFrames h.2.1.pre)
        fun _ hc => ⟨by rw [hc.saved .r14 (by decide), h.2.1.r14], by rw [hc.sp, h.2.2]⟩⟩
  have b := taintRegs
    (P := fun s₁ s₂ => (s₁.gpr .r14 = s₀.gpr .r8 ∧ s₁.sp = s₀.sp) ∧ (s₂.gpr .r14 = s₀.gpr .r8 ∧ s₂.sp = s₀'.sp))
    [.r14] (fun s₁ s₂ h => ⟨by rw [h.1.2, h.2.2, q7], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.1, h.2.1]⟩) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem finalize_ct : ConstantTime isa finalizePPC64LE.pre finalizePPC64LE.pub finalize :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finalize_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `vg_cmac_aes_update` -/

section
variable {s₀ s₀' : State} (hq : updatePPC64LE.pub s₀ s₀')
include hq

theorem upub_W : W s₀ = W s₀' := hq.1
theorem upub_r4 : s₀.gpr .r4 = s₀'.gpr .r4 := hq.2.1
theorem upub_R : R s₀ = R s₀' := by rw [R, R, upub_r4 hq]
theorem upub_Iv : Iv s₀ = Iv s₀' := hq.2.2.1
theorem upub_Dp : Dp s₀ = Dp s₀' := hq.2.2.2.1
theorem upub_N : N s₀ = N s₀' := by rw [N, N, hq.2.2.2.2.1]
theorem upub_S : S s₀ = S s₀' := hq.2.2.2.2.2.1
theorem upub_sp : s₀.sp = s₀'.sp := hq.2.2.2.2.2.2
theorem upub_blk (k : Nat) : blk s₀ k = blk s₀' k := by rw [blk, blk, upub_Dp hq]

theorem UInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : UInv s₀ k s₁) (h₂ : UInv s₀' k s₂) :
    ∀ r ∈ vars, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.r14, h₂.r14, upub_W hq]
  · rw [h₁.r15, h₂.r15, upub_r4 hq]
  · rw [h₁.r16, h₂.r16, upub_Iv hq]
  · rw [h₁.r17, h₂.r17, upub_blk hq]
  · rw [h₁.r18, h₂.r18, upub_N hq]
  · rw [h₁.r19, h₂.r19, upub_S hq]

end

/-- The invariant, and the stack pointer on entry. -/
def US (s₀ : State) (k : Nat) (s : State) : Prop := UInv s₀ k s ∧ s.sp = s₀.sp

/-- What is known between the code before the call and the call. -/
structure UMid (s₀ : State) (k : Nat) (s : State) : Prop where
  pre : CallPre s (W s₀) (Iv s₀) (S s₀) (R s₀)
  r17 : s.gpr .r17 = blk s₀ k
  r18 : s.gpr .r18 = BitVec.ofNat 64 (N s₀ - k)
  sp : s.sp = s₀.sp

/-- What is known after the call. -/
structure UAfter (s₀ : State) (k : Nat) (s : State) : Prop where
  r17 : s.gpr .r17 = blk s₀ k
  r18 : s.gpr .r18 = BitVec.ofNat 64 (N s₀ - k)
  sp : s.sp = s₀.sp

theorem upd_body_ct {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : updatePPC64LE.pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ US s₀ k s₁ ∧ US s₀' k s₂) body fun s₁ s₂ =>
      US s₀ (k + 1) s₁ ∧ US s₀' (k + 1) s₂ := by
  have hN := upub_N hq
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs vars) (.block (Impl.AesCbc.PPC64LE.xorInto .r16 .r17 ++ updArgs))
    h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r17, .r18]) (.block Impl.AesCbc.PPC64LE.advance) h).isSome =
    true := ⟨_, by taint_decide⟩
  have mid (t : State) (ht : UPre t) (hk : k < N t) {s : State} (h : US t k s) :
      WP isa (.block (Impl.AesCbc.PPC64LE.xorInto .r16 .r17 ++ updArgs)) s (UMid t k) :=
    WP.mono (wp_sp (bodyPre_wp ht hk h.1)) fun s' ⟨⟨c, g, _, _, _⟩, e⟩ =>
      ⟨c, by rw [g _ (by decide), h.1.r17], by rw [g _ (by decide), h.1.r18], e.trans h.2⟩
  have a := (taintRegs (P := fun s₁ s₂ => k < N s₀ ∧ US s₀ k s₁ ∧ US s₀' k s₂) vars
    (fun _ _ h => ⟨by rw [h.2.1.2, h.2.2.2, upub_sp hq], UInv.agree hq h.2.1.1 h.2.2.1⟩) hA).wp
    (F₁ := UMid s₀ k) (F₂ := UMid s₀' k) fun _ _ h =>
      ⟨mid s₀ hp h.1 h.2.1, mid s₀' hp' (by rw [← hN]; exact h.1) h.2.2⟩
  have c := (blk_rel (name := "vg_aes_encrypt_blocks") Proof.Aes.PPC64LE.encryptBlocks_correct
    Proof.Aes.PPC64LE.encryptBlocks_ct (P := fun s₁ s₂ => UMid s₀ k s₁ ∧ UMid s₀' k s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [upub_W hq, upub_Iv hq, upub_S hq, upub_R hq]; exact h.2.pre,
        by rw [h.1.sp, h.2.sp, upub_sp hq]⟩).wp
    (F₁ := UAfter s₀ k) (F₂ := UAfter s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call Proof.Aes.PPC64LE.encryptBlocks_correct AesCbc.PPC64LE.encryptBlocks_noFrames h.1.pre)
        fun _ hc => ⟨by rw [hc.saved .r17 (by decide), h.1.r17], by rw [hc.saved .r18 (by decide), h.1.r18],
          hc.sp.trans h.1.sp⟩,
       WP.mono (blk_call Proof.Aes.PPC64LE.encryptBlocks_correct AesCbc.PPC64LE.encryptBlocks_noFrames h.2.pre)
        fun _ hc => ⟨by rw [hc.saved .r17 (by decide), h.2.r17], by rw [hc.saved .r18 (by decide), h.2.r18],
          hc.sp.trans h.2.sp⟩⟩
  have b := taintRegs (P := fun s₁ s₂ => UAfter s₀ k s₁ ∧ UAfter s₀' k s₂) [.r17, .r18]
    (fun s₁ s₂ h => ⟨by rw [h.1.sp, h.2.sp, upub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r17, h.2.r17, upub_blk hq]
      · rw [h.1.r18, h.2.r18, upub_N hq]⟩) hB
  have whole := (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)
  exact (whole.wp (F₁ := US s₀ (k + 1)) (F₂ := US s₀' (k + 1)) fun s₁ s₂ h =>
    ⟨WP.mono (wp_sp (body_ok hp h.1 h.2.1.1)) fun _ ⟨l, e⟩ => ⟨l, e.trans h.2.1.2⟩,
     WP.mono (wp_sp (body_ok hp' (by rw [← hN]; exact h.1) h.2.2.1)) fun _ ⟨l, e⟩ => ⟨l, e.trans h.2.2.2⟩⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-- The loop's relation, with the number of iterations left. -/
def URel (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ US s₀ k s₁ ∧ US s₀' k s₂

theorem upd_loop_ct {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : updatePPC64LE.pub s₀ s₀') (n : Nat) :
    RelCT isa (URel s₀ s₀' n) (.loop body (.nonzero .d .r18))
      fun s₁ s₂ => US s₀ (N s₀) s₁ ∧ US s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (URel s₀ s₀') (fun n => ?_) n
  have hN := upub_N hq
  have hb₀ := (s₀.gpr .r7).isLt
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : URel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  refine (upd_body_ct hp hp' hq k).mono (fun _ _ h => h.2) fun s₁ s₂ ⟨l₁, l₂⟩ => ?_
  have bd : N s₀ - (k + 1) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hb₀
  have e₁ := eval_nonzero_ofNat' s₁ .r18 bd l₁.1.r18
  have e₂ := eval_nonzero_ofNat' s₂ .r18 (k := N s₀ - (k + 1)) bd (by rw [l₂.1.r18, hN])
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : N s₀ = k + 1 := by
      have : N s₀ - (k + 1) = 0 := by simpa using hf
      omega_using [hk, this]
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [h0], l₁, l₂⟩

theorem update_rel {s₀ s₀' : State} (h0 : updatePPC64LE.pre s₀) (h0' : updatePPC64LE.pre s₀')
    (hq : updatePPC64LE.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') update fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := upub_N hq
  obtain ⟨_, hpro⟩ : ∃ h, (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8])
    (.block (save ++ setup)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hepi⟩ : ∃ h, (taint.check (Taint.ofRegs [.r19]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true := ⟨_, by taint_decide⟩
  have pro := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.r3, .r4, .r5, .r6, .r7, .r8]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨upub_sp hq, fun r hr => ?_⟩
      obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hpro).wp
    (F₁ := US s₀ 0) (F₂ := US s₀' 0)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨wp_sp (prologue_wp hp), wp_sp (prologue_wp hp')⟩
  have ev {t : State} {s : State} (h : US t 0 s) : isa.eval (.zero .d .r18) s = some (decide (N t = 0)) := by
    have := eval_zero_ofNat s .r18 (k := N t - 0) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (t.gpr .r7).isLt)
      h.1.r18
    rwa [Nat.sub_zero] at this
  have nil := taintRegs (P := fun a b => (US s₀ 0 a ∧ US s₀' 0 b) ∧ isa.eval (.zero .d .r18) a = some true) []
    (fun _ _ h => ⟨by rw [h.1.1.2, h.1.2.2, upub_sp hq], fun r hr => by simp at hr⟩) hnil
  have mid : RelCT isa (fun a b => US s₀ 0 a ∧ US s₀' 0 b)
      (.ite (.zero .d .r18) (.block []) (.loop body (.nonzero .d .r18)))
      (fun a b => US s₀ (N s₀) a ∧ US s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1, ev h.2, hN]) ?_ ?_
    · refine (nil.wp (F₁ := US s₀ (N s₀)) (F₂ := US s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; rw [ev h.1.1] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2)⟩
    · refine (RelCT.exists_ (P := fun (_ : 0 < N s₀) a b => US s₀ 0 a ∧ US s₀' 0 b) fun hn =>
          (upd_loop_ct hp hp' hq (N s₀ - 0)).mono (fun _ _ h => ⟨0, rfl, hn, h.1, h.2⟩) fun _ _ h => h).mono
        (fun a b h => ⟨?_, h.1.1, h.1.2⟩) fun _ _ h => h
      have := h.2; rw [ev h.1.1] at this
      have : N s₀ ≠ 0 := by simpa using this
      omega_using [this]
  have epi := taintRegs (P := fun a b => US s₀ (N s₀) a ∧ US s₀' (N s₀') b) [.r19]
    (fun a b h => ⟨by rw [h.1.2, h.2.2, upub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.1.r19, h.2.1.r19, upub_S hq]⟩) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

theorem update_ct : ConstantTime isa updatePPC64LE.pre updatePPC64LE.pub update :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (update_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.PPC64LE

end

end

/-!
# AES-CMAC on PPC64LE: `Verified`

Correctness and constant time, a state satisfying each precondition, and the
shared contracts of `Spec/Cmac/Contract.lean` (with no stack: a call stores
nothing in memory, and each function saves the return address in the
scratch buffer).
-/

@[expose] public section

namespace VG.Proof.CmacAes.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.PPC64LE

theorem subkeys_correct (s : State) (hs : subkeysPPC64LE.pre s) :
    ∃ t s', Exec isa subkeys s t s' ∧ abiPreserved s s' ∧ subkeysPPC64LE.post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := subkeys_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem update_correct (s : State) (hs : updatePPC64LE.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ updatePPC64LE.post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := update_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem finalize_correct (s : State) (hs : finalizePPC64LE.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ finalizePPC64LE.post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := finalize_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

end VG.Proof.CmacAes.PPC64LE
