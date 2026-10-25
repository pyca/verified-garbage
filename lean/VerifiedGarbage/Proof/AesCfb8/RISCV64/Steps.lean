module

public import VerifiedGarbage.Impl.AesCfb8.RISCV64
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
import VerifiedGarbage.Proof.AesCfb8.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# AES-CFB8 on RISC-V: the code after the call

The straight-line pieces of a byte, each run in continuation-passing style,
as on PPC64LE (`Proof/AesCfb8/PPC64LE/Steps.lean`): the data byte XORed
with the first byte of the enciphered block at `sv` (`encByte_wp`,
`decByte_wp`, the ciphertext byte left in `t1`), and the input block
shifted left by a byte with it shifted in, through the block at `sv`
(`shift_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.Impl.AesCfb8.RISCV64
open VG.Impl.AesCbc.RISCV64 (savePtr copy)
open VG.Spec.Aes (bytesAt)

/-- `scratch + 2048`, rounded up to a multiple of 8: the block at `sv`. -/
abbrev svOf (S : Addr) : Addr := S + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (pad (S + BitVec.ofNat 64 2048))

/-- A byte zero-extended and truncated again. -/
theorem byte_ext (a : Byte) : (a.setWidth 64).setWidth 8 = a := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := a.isLt
  omega

/-- Two bytes zero-extended and XORed, truncated again. -/
theorem xor_ext (a b : Byte) : ((a.setWidth 64) ^^^ (b.setWidth 64)).setWidth 8 = a ^^^ b := by
  rw [← BitVec.setWidth_xor, byte_ext]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem t0_svOf (s : State) {S : Addr} (h : s.gpr .s6 = S) :
    (s.write .t0 (s.gpr .s6 + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (pad (s.gpr .s6 + BitVec.ofNat 64 2048)))).gpr
      .t0 = svOf S := by
  rw [RegUpd.gpr_write_self, h]

end

/-- `t0 := sv`, then the data byte at `P` XORed with the byte at `sv`; the
data byte (the ciphertext when decrypting) is left in `t1`, the new data
byte in `t2`. -/
theorem decByte_wp {s : State} {P S : Addr} {rest : List Instr} {Φ : State → Prop}
    (h4 : s.gpr .s4 = P) (h6 : s.gpr .s6 = S)
    (rp : InRegions (s.rd ++ s.wr) P 1) (rt : InRegions (s.rd ++ s.wr) (svOf S) 1)
    (wp : InRegions s.wr P 1)
    (k : ∀ s', s'.gpr .t1 = (s.mem P).setWidth 64 → s'.gpr .t0 = svOf S →
      (∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW P (s.mem (svOf S) ^^^ s.mem P) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block rest) s' Φ) :
    WP isa (.block (savePtr .s6 ++
      (([.load .b .t1 .s4 0, .load .b .t2 .t0 0, .logic .xor .t2 .t2 .t1, .store .b .t2 .s4 0] : List Instr) ++
        rest))) s Φ := by
  rw [WP.block_append_iff]
  refine WP.mono (AesCbc.RISCV64.savePtr_ok .s6) fun s₁ e₁ => ?_
  subst e₁
  have t₀ := t0_svOf s h6
  have g₁ (r : Reg) (h0 : r ≠ .t0) : (s.write .t0 (s.gpr .s6 + BitVec.ofNat 64 2048 +
      BitVec.ofNat 64 (pad (s.gpr .s6 + BitVec.ofNat 64 2048)))).gpr r = s.gpr r :=
    RegUpd.gpr_write_of_ne _ _ h0
  simp only [List.cons_append, List.nil_append]
  refine wp_lbu (a := P) (by decide) (by rw [g₁ _ (by decide), h4]; simp)
    (by rw [RegUpd.rd_write, RegUpd.wr_write]; exact rp) fun s₂ u₂ => ?_
  refine wp_lbu (a := svOf S) (by decide) (by rw [u₂.other _ (by decide), t₀]; simp)
    (by rw [u₂.rd, u₂.wr, RegUpd.rd_write, RegUpd.wr_write]; exact rt) fun s₃ u₃ => ?_
  refine wp_xor fun s₄ u₄ => ?_
  refine wp_sb (a := P) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), h4]; simp)
    (by rw [u₄.wr, u₃.wr, u₂.wr, RegUpd.wr_write]; exact wp) fun s₅ u₅ => ?_
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, RegUpd.mem_write]
  have t1₄ : s₄.gpr .t1 = (s.mem P).setWidth 64 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, RegUpd.mem_write]
  have t2₄ : s₄.gpr .t2 = (s.mem (svOf S)).setWidth 64 ^^^ (s.mem P).setWidth 64 := by
    rw [u₄.gpr, u₃.gpr, u₃.other .t1 (by decide), u₂.gpr, u₂.mem, RegUpd.mem_write]
  refine k s₅ ?_ ?_ (fun r h0 h1 h2 => ?_) ?_ ?_ ?_ ?_
  · rw [u₅.gpr, t1₄]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), t₀]
  · rw [u₅.gpr, u₄.other _ h2, u₃.other _ h2, u₂.other _ h1, g₁ r h0]
  · rw [u₅.mem, t2₄, xor_ext, u₄.mem, m₃]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, RegUpd.rd_write]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, RegUpd.wr_write]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, RegUpd.sp_write]

/-- `t0 := sv`, then the data byte at `P` XORed with the byte at `sv`; the
new data byte (the ciphertext when encrypting) is left in `t1`. -/
theorem encByte_wp {s : State} {P S : Addr} {rest : List Instr} {Φ : State → Prop}
    (h4 : s.gpr .s4 = P) (h6 : s.gpr .s6 = S)
    (rp : InRegions (s.rd ++ s.wr) P 1) (rt : InRegions (s.rd ++ s.wr) (svOf S) 1)
    (wp : InRegions s.wr P 1)
    (k : ∀ s', s'.gpr .t1 = (s.mem P).setWidth 64 ^^^ (s.mem (svOf S)).setWidth 64 → s'.gpr .t0 = svOf S →
      (∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW P (s.mem P ^^^ s.mem (svOf S)) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block rest) s' Φ) :
    WP isa (.block (savePtr .s6 ++
      (([.load .b .t1 .s4 0, .load .b .t2 .t0 0, .logic .xor .t1 .t1 .t2, .store .b .t1 .s4 0] : List Instr) ++
        rest))) s Φ := by
  rw [WP.block_append_iff]
  refine WP.mono (AesCbc.RISCV64.savePtr_ok .s6) fun s₁ e₁ => ?_
  subst e₁
  have t₀ := t0_svOf s h6
  have g₁ (r : Reg) (h0 : r ≠ .t0) : (s.write .t0 (s.gpr .s6 + BitVec.ofNat 64 2048 +
      BitVec.ofNat 64 (pad (s.gpr .s6 + BitVec.ofNat 64 2048)))).gpr r = s.gpr r :=
    RegUpd.gpr_write_of_ne _ _ h0
  simp only [List.cons_append, List.nil_append]
  refine wp_lbu (a := P) (by decide) (by rw [g₁ _ (by decide), h4]; simp)
    (by rw [RegUpd.rd_write, RegUpd.wr_write]; exact rp) fun s₂ u₂ => ?_
  refine wp_lbu (a := svOf S) (by decide) (by rw [u₂.other _ (by decide), t₀]; simp)
    (by rw [u₂.rd, u₂.wr, RegUpd.rd_write, RegUpd.wr_write]; exact rt) fun s₃ u₃ => ?_
  refine wp_xor fun s₄ u₄ => ?_
  refine wp_sb (a := P) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), h4]; simp)
    (by rw [u₄.wr, u₃.wr, u₂.wr, RegUpd.wr_write]; exact wp) fun s₅ u₅ => ?_
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, RegUpd.mem_write]
  have t1₄ : s₄.gpr .t1 = (s.mem P).setWidth 64 ^^^ (s.mem (svOf S)).setWidth 64 := by
    rw [u₄.gpr, u₃.other .t1 (by decide), u₃.gpr, u₂.gpr, u₂.mem, RegUpd.mem_write]
  refine k s₅ ?_ ?_ (fun r h0 h1 h2 => ?_) ?_ ?_ ?_ ?_
  · rw [u₅.gpr, t1₄]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), t₀]
  · rw [u₅.gpr, u₄.other _ h1, u₃.other _ h2, u₂.other _ h1, g₁ r h0]
  · rw [u₅.mem, t1₄, xor_ext, u₄.mem, m₃]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, RegUpd.rd_write]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, RegUpd.wr_write]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, RegUpd.sp_write]

/-- Byte `x` after a byte store at `a`. -/
theorem byte_write_ne (m : Mem) {a x : Addr} (v : Byte) (h : ¬ (⟨a, 1⟩ : Region).Contains x 1) :
    m.writeW a v x = m x := by
  rw [AesCfb8.writeW8_apply]
  have : ¬ (x - a).toNat < 1 := fun e => h (by
    simp only [Region.Contains]; omega)
  simp only [this, ↓reduceIte]

/-- The block at `Q` shifted left by a byte, with the low byte of `t1`
shifted in, through the block at `T`. -/
theorem shift_wp {s : State} {Q T : Addr} {rest : List Instr} {Φ : State → Prop}
    (h3 : s.gpr .s3 = Q) (h0 : s.gpr .t0 = T)
    (rq : ∃ r ∈ s.rd ++ s.wr, Region.Sub ⟨Q, 16⟩ r) (wq : ∃ r ∈ s.wr, Region.Sub ⟨Q, 16⟩ r)
    (rt : ∃ r ∈ s.rd ++ s.wr, Region.Sub ⟨T, 16⟩ r) (wt : ∃ r ∈ s.wr, Region.Sub ⟨T, 16⟩ r)
    (hd : (⟨Q, 16⟩ : Region).Disjoint ⟨T, 16⟩)
    (k : ∀ s', (∀ r, r ≠ .t3 → s'.gpr r = s.gpr r) →
      bytesAt s'.mem Q 16 = (bytesAt s.mem Q 16).tail ++ [(s.gpr .t1).setWidth 8] →
      Frame [⟨Q, 16⟩, ⟨T, 16⟩] s.mem s'.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      WP isa (.block rest) s' Φ) :
    WP isa (.block (shift ++ rest)) s Φ := by
  unfold shift
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.copyBytes_ok (tmp := .t3) (src := .s3) (dst := .t0) (soff := 1) (doff := 0) (n := 15)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi => by
      rw [h3]; exact AesCbc.RISCV64.in_bytes rq (1 + i) (by omega))
    (fun i hi => by
      rw [h0, Nat.zero_add]; exact AesCbc.RISCV64.in_bytes wt i (by omega))
    (fun i hi hc => by
      rw [h0, h3, AesCbc.RISCV64.ofNat_zero_add] at hc
      exact hd _ (Offset.contains_base _ (by omega) (by omega)) ((Region.sub_prefix (by decide)) _ hc)))
    fun s₁ c₁ => ?_
  rw [List.singleton_append]
  have t1₁ : s₁.gpr .t1 = s.gpr .t1 := c₁.gpr _ (by decide)
  refine wp_sb (a := T + BitVec.ofNat 64 15) (by decide) (by rw [c₁.gpr _ (by decide), h0])
    (by rw [c₁.wr]; exact AesCbc.RISCV64.in_bytes wt 15 (by decide)) fun s₂ u₂ => ?_
  have m₂ : ∀ j (hj : j < 16), s₂.mem (T + BitVec.ofNat 64 j) =
      ((bytesAt s.mem Q 16).tail ++ [(s.gpr .t1).setWidth 8])[j]'(by simp [bytesAt]; exact hj) := by
    intro j hj
    rw [u₂.mem, t1₁]
    by_cases e : j = 15
    · subst e
      rw [AesCfb8.writeW8_apply, BitVec.sub_self]
      simp [bytesAt]
    · rw [byte_write_ne _ _ (fun hc => ?_)]
      · have := c₁.copied j (by omega)
        rw [h0, h3, Nat.zero_add] at this
        rw [this, List.getElem_append_left (by simp [bytesAt]; omega)]
        simp [bytesAt, Nat.add_comm]
      · simp only [Region.Contains] at hc
        rw [Offset.add_sub_add_left, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hc
        omega
  refine AesCbc.RISCV64.copy_wp (dst := .s3) (src := .t0) (P := Q) (Q := T) (by decide) (by decide)
    (by rw [u₂.gpr, c₁.gpr _ (by decide), h3]) (by rw [u₂.gpr, c₁.gpr _ (by decide), h0])
    (by rw [u₂.rd, u₂.wr, c₁.rd, c₁.wr]; exact rt) (by rw [u₂.wr, c₁.wr]; exact wq) hd
    fun s₃ g₃ b₃ f₃ rd₃ wr₃ sp₃ => k s₃ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr; rw [g₃ r hr, u₂.gpr, c₁.gpr r hr]
  · rw [b₃]
    apply List.ext_getElem (by simp [bytesAt])
    intro j h₁ _
    have hj : j < 16 := by simpa [bytesAt] using h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    exact m₂ j hj
  · have hf₂ : Frame [⟨T, 16⟩] s.mem s₂.mem := by
      rw [u₂.mem]
      refine (c₁.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _
        (Offset.contains_base (d := 15) (n := 1) (k := 16) _ (by decide) (by decide))
      simp only [List.mem_singleton] at hr; subst hr
      rw [h0, AesCbc.RISCV64.ofNat_zero_add]
      exact ⟨⟨T, 16⟩, by simp, Region.sub_prefix (show 15 ≤ 16 by decide)⟩
    exact (hf₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans
      (f₃.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  · rw [rd₃, u₂.rd, c₁.rd]
  · rw [wr₃, u₂.wr, c₁.wr]
  · rw [sp₃, u₂.sp, c₁.sp]

end VG.Proof.AesCfb8.RISCV64
