module

public import VerifiedGarbage.Impl.Cmac.RISCV64
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Cmac
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Omega

/-!
# CMAC on RISC-V: doubling a block a byte at a time

`dbl n c src dst` (`Impl/Cmac/RISCV64.lean`) doubles the block of `n` bytes
at `s1 + src` into `s1 + dst` (§6.1 steps 2 and 3): byte `j < n - 1` of the
result is byte `j` shifted left by one bit with the top bit of byte `j + 1`
entering on the right (`X << 1`), and byte `n - 1` is byte `n - 1` shifted,
XORed with `c` if the top bit of byte 0 is set (`dblByte`), which is
`Spec.Cmac.dbl n` for AES's 16 bytes and `0x87` and TDEA's 8 bytes and
`0x1b` (`dbl_spec16`, `dbl_spec8`). After byte 0 and the mask, each step `j`
(`dblStep`) reads byte `j + 1` and writes byte `j`: the invariant (`DblI`)
after `k` steps has byte `k` in `t1` and the first `k` bytes written, and
nothing else (so bytes `k + 1 …` of the source are still as on entry when
`dst` is `src`, and the source is never written when `dst` is past it).
-/

@[expose] public section

namespace VG.Proof.Cmac.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Cmac.RISCV64
open VG.Spec.Aes (bytesAt)

/-! ## Bytes -/

/-- Byte `j` of `x` doubled, for the `n` bytes `x 0, …, x (n - 1)` and `R_b`'s
last byte `c`. -/
def dblByte (n : Nat) (c : Byte) (x : Nat → Byte) (j : Nat) : Byte :=
  if j < n - 1 then (x j <<< 1) ||| (x (j + 1) >>> 7)
  else (x (n - 1) <<< 1) ^^^ (if (x 0).msb then c else 0)

theorem or_byte (b c : Byte) :
    ((b.setWidth 64 <<< 1) ||| (c.setWidth 64 >>> 7)).setWidth 8 = (b <<< 1) ||| (c >>> 7) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  by_cases h0 : i < 1
  · simp [h0]; omega
  · simp [h0, show i < 64 by omega, show i - 1 < 64 by omega, show i - 1 < 8 by omega,
      BitVec.getLsbD_of_ge c (7 + i) (by omega)]

theorem xor_byte (b m : Byte) :
    ((b.setWidth 64 <<< 1) ^^^ m.setWidth 64).setWidth 8 = (b <<< 1) ^^^ m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, hi, decide_true,
    Bool.true_and]
  by_cases h0 : i < 1 <;> simp [h0, show i < 64 by omega, show i - 1 < 8 by omega, show i - 1 < 64 by omega]

theorem mask_all : ∀ c ∈ ([0x87, 0x1b] : List Nat), ∀ n < 256, ((((BitVec.ofNat 8 n).setWidth 64 >>> 7) -
    BitVec.ofNat 64 1) &&& BitVec.ofInt 64 c) ^^^ BitVec.ofInt 64 c =
      (if (BitVec.ofNat 8 n).msb then BitVec.ofNat 8 c else 0 : Byte).setWidth 64 := by decide +kernel

/-- The mask: `c` if the top bit of `b` is set, else 0. -/
theorem mask_val {c : Nat} (hc : c ∈ ([0x87, 0x1b] : List Nat)) (b : Byte) :
    (((b.setWidth 64 >>> 7) - BitVec.ofNat 64 1) &&& BitVec.ofInt 64 c) ^^^ BitVec.ofInt 64 c =
      (if b.msb then BitVec.ofNat 8 c else 0 : Byte).setWidth 64 := by
  have := mask_all c hc b.toNat b.isLt
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

theorem getElem_bytesAt (m : Mem) (p : Addr) {n j : Nat} (h : j < (bytesAt m p n).length) :
    (bytesAt m p n)[j] = m (p + BitVec.ofNat 64 j) := by
  simp [bytesAt]

/-- `Spec.Cmac.dbl 16`, byte by byte. -/
theorem dbl_spec16 (m : Mem) (p : Addr) :
    Spec.Cmac.dbl 16 (bytesAt m p 16) =
      (List.range 16).map (dblByte 16 0x87 fun j => m (p + BitVec.ofNat 64 j)) := by
  simp only [bytesAt, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, Spec.Cmac.dbl, Spec.Cmac.msb1, Spec.Cmac.shiftLeft1, Spec.Cmac.rb, Spec.Cmac.zeros,
    Spec.Cmac.xor, List.drop_succ_cons, List.drop_zero, List.zipWith_cons_cons, List.zipWith_nil_right,
    List.headD_cons, List.replicate_succ, List.replicate_zero, dblByte]
  split <;> simp

/-- `Spec.Cmac.dbl 8`, byte by byte. -/
theorem dbl_spec8 (m : Mem) (p : Addr) :
    Spec.Cmac.dbl 8 (bytesAt m p 8) =
      (List.range 8).map (dblByte 8 0x1b fun j => m (p + BitVec.ofNat 64 j)) := by
  simp only [bytesAt, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, Spec.Cmac.dbl, Spec.Cmac.msb1, Spec.Cmac.shiftLeft1, Spec.Cmac.rb, Spec.Cmac.zeros,
    Spec.Cmac.xor, List.drop_succ_cons, List.drop_zero, List.zipWith_cons_cons, List.zipWith_nil_right,
    List.headD_cons, List.replicate_succ, List.replicate_zero, dblByte]
  split <;> simp

/-! ## Steps -/

theorem wp_xori {s : State} {is : List Instr} {Q : State → Prop} {d n : Reg} {imm : Int} (h : imm12 imm)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ BitVec.ofInt 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .xor d n imm :: is)) s Q :=
  WP.cons (exec_logicImm h) (k _ (Upd.write _ _ _))

section
variable (s : State) (K : Addr) (src : Nat)

/-- Byte `j` of the source on entry. -/
abbrev srcB (j : Nat) : Byte := s.mem (K + BitVec.ofNat 64 (src + j))

end

/-- After byte 0, the mask and `k` steps. -/
structure DblI (n c : Nat) (s : State) (K : Addr) (src dst : Nat) (k : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  t1 : s'.gpr .t1 = (srcB s K src k).setWidth 64
  t2 : s'.gpr .t2 = (if (srcB s K src 0).msb then BitVec.ofNat 8 c else 0 : Byte).setWidth 64
  out : ∀ j < k, s'.mem (K + BitVec.ofNat 64 (dst + j)) = dblByte n (BitVec.ofNat 8 c) (srcB s K src) j
  frame : Frame [⟨K + BitVec.ofNat 64 dst, k⟩] s.mem s'.mem

/-- A byte written, read back at a different offset from the same base. -/
theorem byte_writeW_ne (m : Mem) (p : Addr) (b : Byte) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : j ≠ i) : (m.writeW (p + BitVec.ofNat 64 i) b) (p + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 j) := by
  rw [WriteBytes.writeW8_apply]
  simp only [Offset.add_ofNat_ne p hj hi h, ite_false]

theorem dbl_wp {n c : Nat} {s : State} {K : Addr} {src dst : Nat} {rest : List Instr} {Φ : State → Prop}
    (hn : 2 ≤ n) (hc : c ∈ [0x87, 0x1b])
    (hspec : ∀ m p, Spec.Cmac.dbl n (bytesAt m p n) =
      (List.range n).map (dblByte n (BitVec.ofNat 8 c) fun j => m (p + BitVec.ofNat 64 j)))
    (hk : s.gpr .s1 = K) (hsd : dst = src ∨ src + n ≤ dst) (hs : src + n ≤ 2048) (hd : dst + n ≤ 2048)
    (hwd : K.toNat + dst + n ≤ 2 ^ 64)
    (hr : ∀ j < n, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 (src + j)) 1)
    (hw : ∀ j < n, InRegions s.wr (K + BitVec.ofNat 64 (dst + j)) 1)
    (k : ∀ s', (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → s'.gpr r = s.gpr r) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [⟨K + BitVec.ofNat 64 dst, n⟩] s.mem s'.mem →
      bytesAt s'.mem (K + BitVec.ofNat 64 dst) n = Spec.Cmac.dbl n (bytesAt s.mem (K + BitVec.ofNat 64 src) n) →
      WP isa (.block rest) s' Φ) :
    WP isa (.block (dbl n c src dst ++ rest)) s Φ := by
  have hK : K.toNat < 2 ^ 64 := K.isLt
  have hc' : c < 256 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; omega
  have hci : imm12 (c : Int) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; rcases hc with rfl | rfl <;> decide
  -- Bytes of the source, past the `k` bytes written, read as on entry.
  have hsep : ∀ k < n - 1, ¬ (⟨K + BitVec.ofNat 64 dst, k⟩ : Region).Contains (K + BitVec.ofNat 64 (src + (k + 1))) 1 :=
    fun k hk' hc => Offset.disjoint K (d := dst) (n := k) (e := src + (k + 1)) (k := 1) (by omega)
      (by omega) (by omega) _ hc (Region.contains_self _ _)
  rw [dbl, List.append_assoc, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  -- Byte 0 and the mask.
  refine wp_lbu (a := K + BitVec.ofNat 64 (src + 0)) (by omega) (by rw [hk, Nat.add_zero]) (hr 0 (by omega)) fun s₁ u₁ => ?_
  refine wp_srl (by decide) fun s₂ u₂ => wp_subi (imm := 1) (by decide) fun s₃ u₃ => ?_
  refine wp_andi hci fun s₄ u₄ => wp_xori hci fun s₅ u₅ => ?_
  have i₀ : DblI n c s K src dst 0 s₅ := by
    refine ⟨fun r h1 h2 _ _ => ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => absurd hj (by omega), ?_⟩
    · rw [u₅.other _ h2, u₄.other _ h2, u₃.other _ h2, u₂.other _ h2, u₁.other _ h1]
    · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
    · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.gpr]
    · rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, ← mask_val hc]
    · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact Frame.refl _ _
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (DblI n c s K src dst) (fun j t hj h => ?_) (n - 1) (Nat.le_refl _) s₅ i₀)
    fun t h => ?_
  · -- One step.
    have ht : t.gpr .s1 = K := by rw [h.gpr _ (by decide) (by decide) (by decide) (by decide), hk]
    unfold dblStep
    refine wp_lbu (a := K + BitVec.ofNat 64 (src + (j + 1))) (by omega)
      (by rw [ht, Nat.add_assoc]) (by rw [h.rd, h.wr]; exact hr (j + 1) (by omega)) fun t₁ v₁ => ?_
    refine wp_sll (by decide) fun t₂ v₂ => wp_srl (by decide) fun t₃ v₃ => wp_or fun t₄ v₄ => ?_
    refine wp_sb (a := K + BitVec.ofNat 64 (dst + j)) (by omega)
      (by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
        v₁.other _ (by decide), ht]) (by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, h.wr]; exact hw j (by omega))
      fun t₅ g₅ => ?_
    refine wp_mv fun t₆ v₆ => WP.block_nil ?_
    have rd₁ : t.mem (K + BitVec.ofNat 64 (src + (j + 1))) = srcB s K src (j + 1) :=
      h.frame _ fun r hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'; exact hsep j hj
    have hv : (t₄.gpr .t1).setWidth 8 = dblByte n (BitVec.ofNat 8 c) (srcB s K src) j := by
      rw [v₄.gpr, v₃.other _ (by decide), v₃.gpr, v₂.gpr, v₂.other _ (by decide), v₁.gpr,
        v₁.other _ (by decide), h.t1, rd₁, or_byte]
      simp [dblByte, hj]
    have hm : t₆.mem = t.mem.writeW (K + BitVec.ofNat 64 (dst + j)) (dblByte n (BitVec.ofNat 8 c) (srcB s K src) j) := by
      rw [v₆.mem, g₅.mem, hv, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
    refine ⟨fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, ?_⟩
    · rw [v₆.other _ h1, g₅.gpr, v₄.other _ h1, v₃.other _ h4, v₂.other _ h1, v₁.other _ h3,
        h.gpr r h1 h2 h3 h4]
    · rw [v₆.rd, g₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, h.rd]
    · rw [v₆.wr, g₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, h.wr]
    · rw [v₆.sp, g₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, h.sp]
    · rw [v₆.gpr, g₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, rd₁]
    · rw [v₆.other _ (by decide), g₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.other _ (by decide), h.t2]
    · rw [hm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [byte_writeW_ne _ _ _ (by omega) (by omega) (by omega)]; exact h.out i hi
      · simp only [WriteBytes.writeW8_apply, ite_true]
    · rw [hm]
      exact (h.frame.sub fun r hr' => ⟨_, List.mem_singleton_self _, by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact Region.sub_prefix (by omega)⟩).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by omega))
  · -- Byte `n - 1`.
    have ht : t.gpr .s1 = K := by rw [h.gpr _ (by decide) (by decide) (by decide) (by decide), hk]
    refine wp_sll (by decide) fun t₁ v₁ => wp_xor fun t₂ v₂ => ?_
    refine wp_sb (a := K + BitVec.ofNat 64 (dst + (n - 1))) (by omega)
      (by rw [v₂.other _ (by decide), v₁.other _ (by decide), ht]) (by rw [v₂.wr, v₁.wr, h.wr]; exact hw (n - 1) (by omega))
      fun t₃ g₃ => ?_
    have hv : (t₂.gpr .t1).setWidth 8 = dblByte n (BitVec.ofNat 8 c) (srcB s K src) (n - 1) := by
      rw [v₂.gpr, v₁.gpr, v₁.other _ (by decide), h.t1, h.t2, xor_byte]
      simp [dblByte]
    have hm : t₃.mem = t.mem.writeW (K + BitVec.ofNat 64 (dst + (n - 1)))
        (dblByte n (BitVec.ofNat 8 c) (srcB s K src) (n - 1)) := by
      rw [g₃.mem, hv, v₂.mem, v₁.mem]
    have out : ∀ j < n, t₃.mem (K + BitVec.ofNat 64 (dst + j)) = dblByte n (BitVec.ofNat 8 c) (srcB s K src) j := by
      intro j hj
      rw [hm]
      rcases Nat.lt_or_ge j (n - 1) with hj' | hj'
      · rw [byte_writeW_ne _ _ _ (by omega) (by omega) (by omega)]; exact h.out j hj'
      · obtain rfl : j = n - 1 := by omega
        simp only [WriteBytes.writeW8_apply, ite_true]
    refine k t₃ (fun r h1 h2 h3 h4 => ?_) (by rw [g₃.rd, v₂.rd, v₁.rd, h.rd])
      (by rw [g₃.wr, v₂.wr, v₁.wr, h.wr]) (by rw [g₃.sp, v₂.sp, v₁.sp, h.sp]) ?_ ?_
    · rw [g₃.gpr, v₂.other _ h1, v₁.other _ h1, h.gpr r h1 h2 h3 h4]
    · rw [hm, show n = (n - 1) + 1 by omega]
      exact (h.frame.sub fun r hr' => ⟨_, List.mem_singleton_self _, by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact Region.sub_prefix (by omega)⟩).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by omega))
    · rw [hspec]
      apply List.ext_getElem (by simp [bytesAt])
      intro j h₁ h₂
      simp only [bytesAt, List.length_map, List.length_range] at h₁
      simp only [bytesAt, List.getElem_map, List.getElem_range]
      rw [Offset.add_add, out j h₁]
      congr 1
      funext i
      rw [Offset.add_add]

end VG.Proof.Cmac.RISCV64
