import VerifiedGarbage.Proof.Modes.Words
import VerifiedGarbage.Proof.CmacAes.Arm.Words
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Impl.Modes.Arm.Seq

/-!
# Copying and XORing blocks a word at a time, on ARMv7

`copyN_wp`: `k` words (`copyWord`: `ldr r9, [rs, #os + 4w]; str r9, [rd, #od + 4w]`)
copy the block at `Q` (`rs + os`) to `P` (`rd + od`); `xorN_wp`: `k` words
(`xorWord`: `ldr r9`, `ldr r10`, `eor`, `str r9`) XOR it into `P`'s. They go through
`r9` (and `r10`), change no other register, and leave memory `over` the
`4 k` bytes at `P` (`Proof/Modes/Words.lean`, with 4-byte words here:
`over_step4`).
-/

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm
open VG.Proof.Modes (over over_zero over_out over_sep)
open VG.Proof.MdStream.Arm (Upd Mupd wp_ldr wp_str op2_reg)

/-- The byte at `x` is word `d / 4` of `P`'s exactly when its offset from
`P` is in `[d, d + 4)`. -/
theorem sub_add_lt4 (x P : Addr) {d : Nat} (hd : d + 4 ≤ 2 ^ 64) :
    (x - (P + BitVec.ofNat 64 d)).toNat < 4 ↔ d ≤ (x - P).toNat ∧ (x - P).toNat < d + 4 := by
  bv_omega

theorem sub_add_eq4 (x P : Addr) {d : Nat} (hd : d + 4 ≤ 2 ^ 64) (h : d ≤ (x - P).toNat) :
    (x - (P + BitVec.ofNat 64 d)).toNat = (x - P).toNat - d := by
  bv_omega

/-- The next word: a memory that is `over m P (4 w) f` but in word `w`,
which holds `f`'s next 4 bytes, is `over m P (4 w + 4) f`. -/
theorem over_step4 {m m' : Mem} {P : Addr} {w : Nat} {f : Nat → Byte} (hw : 4 * w + 4 ≤ 2 ^ 64)
    (h : ∀ x, m' x = if (x - (P + BitVec.ofNat 64 (4 * w))).toNat < 4 then
      f (4 * w + (x - (P + BitVec.ofNat 64 (4 * w))).toNat) else over m P (4 * w) f x) :
    m' = over m P (4 * w + 4) f := by
  funext x
  rw [h x]
  by_cases hx : (x - (P + BitVec.ofNat 64 (4 * w))).toNat < 4
  · have := (sub_add_lt4 x P hw).mp hx
    rw [ite_eq_left hx, sub_add_eq4 x P hw this.1, show 4 * w + ((x - P).toNat - 4 * w) = (x - P).toNat by omega]
    simp only [over]; rw [ite_eq_left (by omega)]
  · rw [ite_eq_right hx]
    have := mt (sub_add_lt4 x P hw).mpr hx
    simp only [over]
    by_cases h1 : (x - P).toNat < 4 * w
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
    · rw [ite_eq_right h1, ite_eq_right (by omega)]

/-- A byte of a little-endian word stored from the XOR of two loads. -/
theorem writeW_xor_apply32 (m m₁ m₂ : Mem) (a c e x : Addr) :
    m.writeW a (m₁.readW c 32 ^^^ m₂.readW e 32) x =
      if (x - a).toNat < 4 then m₁ (c + BitVec.ofNat 64 (x - a).toNat) ^^^ m₂ (e + BitVec.ofNat 64 (x - a).toNat)
      else m x := by
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq]
  split
  · rename_i h
    rw [BitVec.extractLsb'_xor, Mem.readW, Mem.readW, BitVec.setWidth_eq, BitVec.setWidth_eq,
      Mem.extractLsb'_read m₁ c (n := 4) h, Mem.extractLsb'_read m₂ e (n := 4) h]
  · rfl

/-- A byte of a little-endian word stored from a load. -/
theorem writeW_readW_apply32 (m m₁ : Mem) (a c x : Addr) :
    m.writeW a (m₁.readW c 32) x =
      if (x - a).toNat < 4 then m₁ (c + BitVec.ofNat 64 (x - a).toNat) else m x := by
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq]
  split
  · rename_i h
    rw [Mem.readW, BitVec.setWidth_eq, Mem.extractLsb'_read m₁ c (n := 4) h]
  · rfl

/-- What the `k` word steps from `s` keep, and their memory. -/
structure NInv (s : State) (m : Mem) (s' : State) : Prop where
  regs : ∀ x, x ≠ .r9 → x ≠ .r10 → s'.gpr x = s.gpr x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : s'.mem = m

/-- The hypotheses of both, with `P = rd + od` and `Q = rs + os`: the words
of `P` writable, `Q`'s readable, the blocks apart, neither base register a
temporary, and the offsets in reach. -/
structure NPre (k : Nat) (s : State) (rd rs : Reg) (od os : Nat) (P Q : Addr) : Prop where
  hP : State.addr (s.gpr rd) + BitVec.ofNat 64 od = P
  hQ : State.addr (s.gpr rs) + BitVec.ofNat 64 os = Q
  fP : (s.gpr rd).toNat + od + 4 * k ≤ 2 ^ 32
  fQ : (s.gpr rs).toNat + os + 4 * k ≤ 2 ^ 32
  oP : od + 4 * k ≤ 4096
  oQ : os + 4 * k ≤ 4096
  d9 : rd ≠ .r9
  d10 : rd ≠ .r10
  s9 : rs ≠ .r9
  s10 : rs ≠ .r10
  wP : Covers [⟨P, 4 * k⟩] s.wr
  rQ : Covers [⟨Q, 4 * k⟩] (s.rd ++ s.wr)
  sep : Region.Disjoint ⟨P, 4 * k⟩ ⟨Q, 4 * k⟩

theorem word_addr {b : BitVec 32} {o w k : Nat} (hw : w < k) (h : b.toNat + o + 4 * k ≤ 2 ^ 32) :
    State.addr (b + BitVec.ofNat 32 (o + 4 * w)) = State.addr b + BitVec.ofNat 64 o + BitVec.ofNat 64 (4 * w) := by
  rw [addr_add (by omega), VG.Offset.add_add]

theorem word_in {rs : List Region} {P : Addr} {k w : Nat} (h : Covers [⟨P, 4 * k⟩] rs) (hw : w < k)
    (hk : 4 * k ≤ 2 ^ 64) :
    InRegions rs (P + BitVec.ofNat 64 (4 * w)) 4 :=
  h _ _ ⟨_, List.mem_singleton_self _, VG.Offset.contains_base P (by omega) (by omega)⟩

theorem copyN_wp {k : Nat} {s : State} {rd rs : Reg} {od os : Nat} {P Q : Addr} (h : NPre k s rd rs od os P Q) :
    WP isa (.block ((List.range k).flatMap (copyWord rd rs od os))) s
      (NInv s (over s.mem P (4 * k) fun i => s.mem (Q + BitVec.ofNat 64 i))) := by
  refine wp_range_flatMap (M := isa) (N := k) (fun w s' => NInv s (over s.mem P (4 * w) fun i =>
      s.mem (Q + BitVec.ofNat 64 i)) s')
    (fun w s' hw hi => ?_) k (Nat.le_refl _) s ⟨fun _ _ _ => rfl, rfl, rfl, rfl, by rw [Nat.mul_zero, over_zero]⟩
  have hP' : State.addr (s'.gpr rd + BitVec.ofNat 32 (od + 4 * w)) = P + BitVec.ofNat 64 (4 * w) := by
    rw [hi.regs _ h.d9 h.d10, word_addr hw h.fP, h.hP]
  have hQ' : State.addr (s'.gpr rs + BitVec.ofNat 32 (os + 4 * w)) = Q + BitVec.ofNat 64 (4 * w) := by
    rw [hi.regs _ h.s9 h.s10, word_addr hw h.fQ, h.hQ]
  have hfit : 4 * k ≤ 2 ^ 64 := by have := h.fP; omega
  refine wp_ldr (a := Q + BitVec.ofNat 64 (4 * w)) (by have := h.oQ; omega) hQ' (by rw [hi.rd, hi.wr]; exact word_in h.rQ hw hfit) fun s₁ u₁ => ?_
  refine wp_str (a := P + BitVec.ofNat 64 (4 * w)) (by have := h.oP; omega) (by rw [u₁.other _ h.d9]; exact hP')
    (by rw [u₁.wr, hi.wr]; exact word_in h.wP hw hfit) fun s₂ u₂ => WP.block_nil ⟨fun x h9 h10 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₂.gpr, u₁.other _ h9, hi.regs _ h9 h10]
  · rw [u₂.rd, u₁.rd, hi.rd]
  · rw [u₂.wr, u₁.wr, hi.wr]
  · rw [u₂.sp, u₁.sp, hi.sp]
  rw [u₂.mem, u₁.gpr, u₁.mem, hi.mem]
  refine over_step4 (by omega) fun x => ?_
  rw [writeW_readW_apply32]
  split
  · rename_i hx
    rw [VG.Offset.add_add, over_sep (h.sep.sub_left (Region.sub_prefix (by omega))) (by omega) (by omega)]
  · rfl

theorem xorN_wp {k : Nat} {s : State} {rd rs : Reg} {od os : Nat} {P Q : Addr} (h : NPre k s rd rs od os P Q) :
    WP isa (.block ((List.range k).flatMap (xorWord rd rs od os))) s
      (NInv s (over s.mem P (4 * k) fun i => s.mem (P + BitVec.ofNat 64 i) ^^^ s.mem (Q + BitVec.ofNat 64 i))) := by
  refine wp_range_flatMap (M := isa) (N := k) (fun w s' => NInv s (over s.mem P (4 * w) fun i =>
      s.mem (P + BitVec.ofNat 64 i) ^^^ s.mem (Q + BitVec.ofNat 64 i)) s')
    (fun w s' hw hi => ?_) k (Nat.le_refl _) s ⟨fun _ _ _ => rfl, rfl, rfl, rfl, by rw [Nat.mul_zero, over_zero]⟩
  have hP' : State.addr (s'.gpr rd + BitVec.ofNat 32 (od + 4 * w)) = P + BitVec.ofNat 64 (4 * w) := by
    rw [hi.regs _ h.d9 h.d10, word_addr hw h.fP, h.hP]
  have hQ' : State.addr (s'.gpr rs + BitVec.ofNat 32 (os + 4 * w)) = Q + BitVec.ofNat 64 (4 * w) := by
    rw [hi.regs _ h.s9 h.s10, word_addr hw h.fQ, h.hQ]
  have hfit : 4 * k ≤ 2 ^ 64 := by have := h.fP; omega
  refine wp_ldr (a := P + BitVec.ofNat 64 (4 * w)) (by have := h.oP; omega) hP' (by rw [hi.rd, hi.wr]; exact word_in (Covers.right h.wP) hw hfit) fun s₁ u₁ => ?_
  refine wp_ldr (a := Q + BitVec.ofNat 64 (4 * w)) (by have := h.oQ; omega) (by rw [u₁.other _ h.s9]; exact hQ')
    (by rw [u₁.rd, u₁.wr, hi.rd, hi.wr]; exact word_in h.rQ hw hfit) fun s₂ u₂ => ?_
  refine VG.Proof.CmacAes.Arm.wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_str (a := P + BitVec.ofNat 64 (4 * w)) (by have := h.oP; omega) (by rw [u₃.other _ h.d9, u₂.other _ h.d10, u₁.other _ h.d9]; exact hP')
    (by rw [u₃.wr, u₂.wr, u₁.wr, hi.wr]; exact word_in h.wP hw hfit) fun s₄ u₄ =>
      WP.block_nil ⟨fun x h9 h10 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₄.gpr, u₃.other _ h9, u₂.other _ h10, u₁.other _ h9, hi.regs _ h9 h10]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, hi.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hi.wr]
  · rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, hi.sp]
  rw [u₄.mem, u₃.gpr, u₃.mem, u₂.other _ (by decide), u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, hi.mem]
  refine over_step4 (by omega) fun x => ?_
  rw [writeW_xor_apply32]
  split
  · rename_i hx
    rw [VG.Offset.add_add, VG.Offset.add_add, over_out (by rw [VG.Proof.Modes.off_self P (by omega)]; omega),
      over_sep (h.sep.sub_left (Region.sub_prefix (by omega))) (by omega) (by omega)]
  · rfl

end VG.Proof.Modes.Arm
