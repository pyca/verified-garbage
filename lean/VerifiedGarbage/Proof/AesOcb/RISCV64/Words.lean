module

public import VerifiedGarbage.Impl.AesOcb.RISCV64
public import VerifiedGarbage.Spec.Ocb
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.BE64
public import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Dbl
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Cmac.Dbl64
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-OCB on RISC-V: blocks, two doublewords at a time

Untrusted: everything here is checked by Lean. `zero16`, `copy16` and
`xorB` and `dbl` write a block (`BlkStep`): zeros, a copy, the XOR of two
blocks and `double` of a block (`zero16_ok`, `copy16_ok`, `xorB_ok`,
`dbl_ok`), as blocks of memory (`blockAtMem`). As on PPC64LE
(`Proof/AesOcb/PPC64LE/Words.lean`); the doublewords `zero16`, `copy16` and
`xorB` access are aligned, and `dbl` loads and stores its doublewords
big-endian a byte at a time, at any alignment.
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.BE64 VG.Impl.AesOcb.RISCV64
open VG.Spec.Ocb (Block blockAtMem double)
open VG.Proof.Cmac (le8 le8_readW xor_words bytesAt_store2)

/-- What a step writing the block at `C + d` does: it writes only there,
the block `v`, and keeps the registers but `clob`. -/
structure BlkStep (C : Addr) (d : Nat) (v : Block) (clob : List Reg) (s s' : State) : Prop where
  frame : Frame [⟨C + BitVec.ofNat 64 d, 16⟩] s.mem s'.mem
  val : blockAtMem s'.mem (C + BitVec.ofNat 64 d) = v
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem addr8 (p : Addr) (d : Nat) : p + BitVec.ofNat 64 d + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (d + 8) :=
  Offset.add_add p d 8

theorem blockAtMem_store2 (m : Mem) (p : Addr) (w₀ w₁ : BitVec 64) :
    blockAtMem ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) p = Spec.Ocb.ofBytes (le8 w₀ ++ le8 w₁) := by
  rw [blockAtMem, bytesAt_store2]

/-- The two doublewords of a block, XORed with those of another, are the XOR
of the blocks. -/
theorem blockAtMem_xor_words (m : Mem) (p q : Addr) :
    Spec.Ocb.ofBytes (le8 (m.readW p 64 ^^^ m.readW q 64) ++
      le8 (m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64)) =
      blockAtMem m p ^^^ blockAtMem m q := by
  rw [xor_words, ← Proof.Ocb.xor_eq, Proof.Ocb.ofBytes_xor (by simp [Spec.Aes.bytesAt])
    (by simp [Spec.Aes.bytesAt])]
  rfl

theorem blockAtMem_words (m : Mem) (p : Addr) :
    Spec.Ocb.ofBytes (le8 (m.readW p 64) ++ le8 (m.readW (p + BitVec.ofNat 64 8) 64)) = blockAtMem m p := by
  rw [le8_readW, le8_readW, ← Proof.Cmac.bytesAt_split]; rfl

theorem frame2 (m : Mem) (p : Addr) (w₀ w₁ : BitVec 64) :
    Frame [⟨p, 16⟩] m ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) :=
  Proof.Cmac.frame_store2 _ _ _


section
variable {s : State} {Q : State → Prop}

/-- `zero16 d`: `W + d ← 0`, `W` (in `s0`) and `d` aligned. -/
theorem zero16_ok {W : Addr} {d : Nat} (hW : W.toNat % 8 = 0) (hd : d % 8 = 0 ∧ d + 8 < 2048)
    (hs0 : s.gpr .s0 = W)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    WP isa (.block (zero16 d)) s (BlkStep W d 0 [.t0] s) := by
  unfold zero16
  refine wp_li (imm := 0) (by decide) fun s₁ u₁ => ?_
  refine wp_sd (a := W + BitVec.ofNat 64 d) (by omega) (by rw [u₁.other _ (by decide), hs0])
    (Spill.al8 hW hd.1) (by rw [u₁.wr]; exact w₀) fun s₂ u₂ => ?_
  refine wp_sd (a := W + BitVec.ofNat 64 (d + 8)) (by omega)
    (by rw [u₂.gpr, u₁.other _ (by decide), hs0]) (Spill.al8 hW (by omega)) (by rw [u₂.wr, u₁.wr]; exact w₁)
    fun s₃ u₃ => WP.block_nil ?_
  have m₃ : s₃.mem = (s.mem.writeW (W + BitVec.ofNat 64 d) (0 : BitVec 64)).writeW
      (W + BitVec.ofNat 64 d + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [u₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, addr8]; rfl
  refine ⟨by rw [m₃]; exact frame2 _ _ _ _, by rw [m₃, blockAtMem_store2]; decide, fun r hr => ?_,
    by rw [u₃.sp, u₂.sp, u₁.sp], by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr]⟩
  simp only [List.mem_singleton] at hr
  rw [u₃.gpr, u₂.gpr, u₁.other _ hr]

/-- `copy16 a d`: `W + d ← W + a`. -/
theorem copy16_ok {W : Addr} {a d : Nat} (hW : W.toNat % 8 = 0) (ha : a % 8 = 0 ∧ a + 8 < 2048)
    (hd : d % 8 = 0 ∧ d + 8 < 2048) (hs0 : s.gpr .s0 = W)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    WP isa (.block (copy16 a d)) s (BlkStep W d (blockAtMem s.mem (W + BitVec.ofNat 64 a)) [.t1, .t2] s) := by
  unfold copy16
  refine wp_ld (a := W + BitVec.ofNat 64 a) (by omega) (by rw [hs0]) (Spill.al8 hW ha.1) r₀ fun s₁ u₁ => ?_
  refine wp_ld (a := W + BitVec.ofNat 64 (a + 8)) (by omega)
    (by rw [u₁.other _ (by decide), hs0]) (Spill.al8 hW (by omega)) (by rw [u₁.rd, u₁.wr]; exact r₁)
    fun s₂ u₂ => ?_
  refine wp_sd (a := W + BitVec.ofNat 64 d) (by omega)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hs0]) (Spill.al8 hW hd.1)
    (by rw [u₂.wr, u₁.wr]; exact w₀) fun s₃ u₃ => ?_
  refine wp_sd (a := W + BitVec.ofNat 64 (d + 8)) (by omega)
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hs0]) (Spill.al8 hW (by omega))
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact w₁) fun s₄ u₄ => WP.block_nil ?_
  have m₄ : s₄.mem = (s.mem.writeW (W + BitVec.ofNat 64 d) (s.mem.readW (W + BitVec.ofNat 64 a) 64)).writeW
      (W + BitVec.ofNat 64 d + BitVec.ofNat 64 8) (s.mem.readW (W + BitVec.ofNat 64 a + BitVec.ofNat 64 8) 64) := by
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, u₂.other _ (by decide), u₁.gpr, u₁.mem, addr8, addr8]
  refine ⟨by rw [m₄]; exact frame2 _ _ _ _, by rw [m₄, blockAtMem_store2, blockAtMem_words], fun r hr => ?_,
    by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [u₄.gpr, u₃.gpr, u₂.other _ hr.2, u₁.other _ hr.1]

/-- `xorB pb qb cb pd qd cd`: `C + cd ← (P + pd) ⊕ (Q + qd)`, `P`, `Q` and
`C` in `pb`, `qb` and `cb`, all aligned, the second doublewords of the
sources apart from the first of the result (it may be either source, in
place). -/
theorem xorB_ok {P Q C : Addr} {pb qb cb : Reg} {pd qd cd : Nat} (hP : P.toNat % 8 = 0) (hQ : Q.toNat % 8 = 0)
    (hC : C.toNat % 8 = 0) (hpd : pd % 8 = 0 ∧ pd + 8 < 2048)
    (hqd : qd % 8 = 0 ∧ qd + 8 < 2048) (hcd : cd % 8 = 0 ∧ cd + 8 < 2048)
    (hp : s.gpr pb = P) (hq : s.gpr qb = Q) (hc : s.gpr cb = C)
    (np : pb ≠ .t1 ∧ pb ≠ .t2) (nq : qb ≠ .t1 ∧ qb ≠ .t2) (nc : cb ≠ .t1 ∧ cb ≠ .t2)
    (rp₀ : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 pd) 8)
    (rp₁ : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 (pd + 8)) 8)
    (rq₀ : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 qd) 8)
    (rq₁ : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 (qd + 8)) 8)
    (w₀ : InRegions s.wr (C + BitVec.ofNat 64 cd) 8) (w₁ : InRegions s.wr (C + BitVec.ofNat 64 (cd + 8)) 8)
    (sp₁ : Mem.Sep (P + BitVec.ofNat 64 (pd + 8)) 8 (C + BitVec.ofNat 64 cd) 8)
    (sq₁ : Mem.Sep (Q + BitVec.ofNat 64 (qd + 8)) 8 (C + BitVec.ofNat 64 cd) 8) :
    WP isa (.block (xorB pb qb cb pd qd cd)) s
      (BlkStep C cd (blockAtMem s.mem (P + BitVec.ofNat 64 pd) ^^^ blockAtMem s.mem (Q + BitVec.ofNat 64 qd))
        [.t1, .t2] s) := by
  unfold xorB
  refine wp_ld (a := P + BitVec.ofNat 64 pd) (by omega) (by rw [hp]) (Spill.al8 hP hpd.1) rp₀ fun s₁ u₁ => ?_
  refine wp_ld (a := Q + BitVec.ofNat 64 qd) (by omega) (by rw [u₁.other _ nq.1, hq]) (Spill.al8 hQ hqd.1)
    (by rw [u₁.rd, u₁.wr]; exact rq₀) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_sd (a := C + BitVec.ofNat 64 cd) (by omega)
    (by rw [u₃.other _ nc.1, u₂.other _ nc.2, u₁.other _ nc.1, hc]) (Spill.al8 hC hcd.1)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact w₀) fun s₄ u₄ => ?_
  have g₄ : ∀ r, r ≠ .t1 → r ≠ .t2 → s₄.gpr r = s.gpr r := fun r h3 h4 => by
    rw [u₄.gpr, u₃.other _ h3, u₂.other _ h4, u₁.other _ h3]
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have m₄ : s₄.mem = s.mem.writeW (C + BitVec.ofNat 64 cd)
      (s.mem.readW (P + BitVec.ofNat 64 pd) 64 ^^^ s.mem.readW (Q + BitVec.ofNat 64 qd) 64) := by
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, u₂.other _ (by decide), u₁.gpr, u₁.mem]
  refine wp_ld (a := P + BitVec.ofNat 64 (pd + 8)) (by omega)
    (by rw [g₄ _ np.1 np.2, hp]) (Spill.al8 hP (by omega)) (by rw [rd₄, wr₄]; exact rp₁) fun s₅ u₅ => ?_
  refine wp_ld (a := Q + BitVec.ofNat 64 (qd + 8)) (by omega)
    (by rw [u₅.other _ nq.1, g₄ _ nq.1 nq.2, hq]) (Spill.al8 hQ (by omega))
    (by rw [u₅.rd, u₅.wr, rd₄, wr₄]; exact rq₁) fun s₆ u₆ => ?_
  refine wp_xor fun s₇ u₇ => ?_
  refine wp_sd (a := C + BitVec.ofNat 64 (cd + 8)) (by omega)
    (by rw [u₇.other _ nc.1, u₆.other _ nc.2, u₅.other _ nc.1, g₄ _ nc.1 nc.2, hc]) (Spill.al8 hC (by omega))
    (by rw [u₇.wr, u₆.wr, u₅.wr, wr₄]; exact w₁) fun s₈ u₈ => WP.block_nil ?_
  have v₅ : s₆.gpr .t1 = s.mem.readW (P + BitVec.ofNat 64 (pd + 8)) 64 := by
    rw [u₆.other _ (by decide), u₅.gpr, m₄, Mem.readW_writeW_sep sp₁ (by decide)]
  have v₆ : s₆.gpr .t2 = s.mem.readW (Q + BitVec.ofNat 64 (qd + 8)) 64 := by
    rw [u₆.gpr, u₅.mem, m₄, Mem.readW_writeW_sep sq₁ (by decide)]
  have m₈ : s₈.mem = (s.mem.writeW (C + BitVec.ofNat 64 cd)
      (s.mem.readW (P + BitVec.ofNat 64 pd) 64 ^^^ s.mem.readW (Q + BitVec.ofNat 64 qd) 64)).writeW
      (C + BitVec.ofNat 64 cd + BitVec.ofNat 64 8)
      (s.mem.readW (P + BitVec.ofNat 64 pd + BitVec.ofNat 64 8) 64 ^^^
        s.mem.readW (Q + BitVec.ofNat 64 qd + BitVec.ofNat 64 8) 64) := by
    rw [u₈.mem, u₇.gpr, u₇.mem, u₆.mem, u₅.mem, m₄, v₅, v₆, addr8, addr8, addr8]
  refine ⟨by rw [m₈]; exact frame2 _ _ _ _, by rw [m₈, blockAtMem_store2, blockAtMem_xor_words], fun r hr => ?_,
    by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, rd₄],
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [u₈.gpr, u₇.other _ hr.1, u₆.other _ hr.2, u₅.other _ hr.1, g₄ _ hr.1 hr.2]

/-- `double` of a block, from its doublewords read big-endian. -/
theorem dbl_mem (m : Mem) (p : Addr) :
    Spec.Ocb.ofBytes (le8 (byteRev64 (Proof.Cmac.dblHi (byteRev64 (m.readW p 64))
        (byteRev64 (m.readW (p + BitVec.ofNat 64 8) 64)))) ++
      le8 (byteRev64 (Proof.Cmac.dblLo (byteRev64 (m.readW p 64))
        (byteRev64 (m.readW (p + BitVec.ofNat 64 8) 64))))) = double (blockAtMem m p) := by
  have e := Proof.Cmac.dbl_byteRev m p
  rw [BitVec.add_zero] at e
  rw [e, Proof.Cmac.dbl_eq (Proof.Cmac.bytesAt_length _ _ _), ← Proof.Ocb.toBytes_eq, Proof.Ocb.ofBytes_toBytes,
    Proof.Ocb.double_eq]
  rfl

theorem wp_and {is : List Instr} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

/-- `dbl b a d`: `W + d ← double(B + a)`, `B` in `b`. -/
theorem dbl_ok {W B : Addr} {b : Reg} {a d : Nat} (ha : a + 15 < 2048) (hd : d + 16 ≤ 2048)
    (hs0 : s.gpr .s0 = W) (hb : s.gpr b = B) (nb : b ≠ .t0 ∧ b ≠ .t1 ∧ b ≠ .t2 ∧ b ≠ .t3 ∧ b ≠ .t4)
    (r₀ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    WP isa (.block (dbl b a d)) s
      (BlkStep W d (double (blockAtMem s.mem (B + BitVec.ofNat 64 a))) [.t0, .t1, .t2, .t3, .t4] s) := by
  unfold dbl
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_loadBE64 (a := B + BitVec.ofNat 64 a) (Ne.symm nb.2.1) (Ne.symm nb.1) (by decide) (by omega)
    (by rw [hb]) r₀ fun s₁ s₂ u₁ u₂ => ?_
  refine wp_loadBE64 (a := B + BitVec.ofNat 64 (a + 8)) (Ne.symm nb.2.2.1) (Ne.symm nb.1) (by decide) (by omega)
    (by rw [u₂.other _ nb.2.1, u₁.other _ nb.1, hb]) (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact r₁)
    fun s₃ s₄ u₃ u₄ => ?_
  refine wp_srl (by decide) fun s₅ u₅ => wp_li (imm := 0) (by decide) fun s₆ u₆ => wp_sub fun s₇ u₇ => ?_
  refine wp_li (imm := 0x87) (by decide) fun s₈ u₈ => wp_and fun s₉ u₉ => ?_
  refine wp_sll (by decide) fun s₁₀ u₁₀ => wp_srl (by decide) fun s₁₁ u₁₁ => wp_or fun s₁₂ u₁₂ => ?_
  refine wp_sll (by decide) fun s₁₃ u₁₃ => wp_xor fun s₁₄ u₁₄ => ?_
  have g₁₄ : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → s₁₄.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h4 => by
      rw [u₁₄.other _ h2, u₁₃.other _ h2, u₁₂.other _ h1, u₁₁.other _ h4, u₁₀.other _ h1, u₉.other _ h3,
        u₈.other _ h4, u₇.other _ h3, u₆.other _ h4, u₅.other _ h3, u₄.other _ h2, u₃.other _ h0, u₂.other _ h1,
        u₁.other _ h0]
  have m₁₄ : s₁₄.mem = s.mem := by
    rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem,
      u₂.mem, u₁.mem]
  have h3 : s₄.gpr .t1 = byteRev64 (s.mem.readW (B + BitVec.ofNat 64 a) 64) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  have h4 : s₄.gpr .t2 = byteRev64 (s.mem.readW (B + BitVec.ofNat 64 (a + 8)) 64) := by
    rw [u₄.gpr, u₂.mem, u₁.mem]
  have hi : s₁₄.gpr .t1 = Proof.Cmac.dblHi (s₄.gpr .t1) (s₄.gpr .t2) := by
    rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.gpr, u₁₁.other .t1 (by decide),
      u₁₀.gpr, u₁₀.other .t2 (by decide), u₉.other .t1 (by decide), u₉.other .t2 (by decide),
      u₈.other .t1 (by decide), u₈.other .t2 (by decide), u₇.other .t1 (by decide), u₇.other .t2 (by decide),
      u₆.other .t1 (by decide), u₆.other .t2 (by decide), u₅.other .t1 (by decide), u₅.other .t2 (by decide)]
    rfl
  have lo : s₁₄.gpr .t2 = Proof.Cmac.dblLo (s₄.gpr .t1) (s₄.gpr .t2) := by
    rw [u₁₄.gpr, u₁₃.gpr, u₁₃.other .t3 (by decide), u₁₂.other .t2 (by decide), u₁₂.other .t3 (by decide),
      u₁₁.other .t2 (by decide), u₁₁.other .t3 (by decide), u₁₀.other .t2 (by decide), u₁₀.other .t3 (by decide),
      u₉.gpr, u₉.other .t2 (by decide), u₈.gpr, u₈.other .t3 (by decide), u₈.other .t2 (by decide), u₇.gpr,
      u₇.other .t2 (by decide), u₆.gpr, u₆.other .t3 (by decide), u₆.other .t2 (by decide), u₅.gpr,
      u₅.other .t2 (by decide)]
    rfl
  have rd₁₄ : s₁₄.rd = s.rd := by
    rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₁₄ : s₁₄.wr = s.wr := by
    rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₁₄ : s₁₄.sp = s.sp := by
    rw [u₁₄.sp, u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have w0 : s₁₄.gpr .s0 = W := by rw [g₁₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), hs0]
  refine wp_storeBE8 (a := W + BitVec.ofNat 64 d) (by decide) (by decide) (by omega) (by rw [w0])
    (by rw [wr₁₄]; exact w₀) fun s₁₅ s₁₆ u₁₅ u₁₆ => ?_
  refine wp_storeBE8 (a := W + BitVec.ofNat 64 (d + 8)) (by decide) (by decide) (by omega)
    (by rw [u₁₆.other _ (by decide), u₁₅.gpr, w0])
    (by rw [u₁₆.wr, u₁₅.wr, wr₁₄]; exact w₁) fun s₁₇ s₁₈ u₁₇ u₁₈ => WP.block_nil ?_
  have m₁₈ : s₁₈.mem = (s.mem.writeW (W + BitVec.ofNat 64 d)
      (byteRev64 (Proof.Cmac.dblHi (byteRev64 (s.mem.readW (B + BitVec.ofNat 64 a) 64))
        (byteRev64 (s.mem.readW (B + BitVec.ofNat 64 a + BitVec.ofNat 64 8) 64))))).writeW
      (W + BitVec.ofNat 64 d + BitVec.ofNat 64 8)
      (byteRev64 (Proof.Cmac.dblLo (byteRev64 (s.mem.readW (B + BitVec.ofNat 64 a) 64))
        (byteRev64 (s.mem.readW (B + BitVec.ofNat 64 a + BitVec.ofNat 64 8) 64)))) := by
    rw [u₁₈.mem, u₁₇.mem, u₁₆.other .t2 (by decide), u₁₅.gpr, u₁₆.mem, u₁₅.mem, hi, lo, m₁₄, h3, h4, addr8, addr8]
  refine ⟨by rw [m₁₈]; exact frame2 _ _ _ _, by rw [m₁₈, blockAtMem_store2]; exact dbl_mem _ _, fun r hr => ?_,
    by rw [u₁₈.sp, u₁₇.sp, u₁₆.sp, u₁₅.sp, sp₁₄], by rw [u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, rd₁₄],
    by rw [u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, wr₁₄]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [u₁₈.other _ hr.1, u₁₇.gpr, u₁₆.other _ hr.1, u₁₅.gpr, g₁₄ _ hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2]

end

end VG.Proof.AesOcb.RISCV64
