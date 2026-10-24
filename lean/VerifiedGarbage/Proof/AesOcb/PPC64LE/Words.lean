module

public import VerifiedGarbage.Impl.AesOcb.PPC64LE
public import VerifiedGarbage.Spec.Ocb
public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
public import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Dbl
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Cmac.Dbl64
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-OCB on PPC64LE: blocks, two doublewords at a time

Untrusted: everything here is checked by Lean. `zero16`, `copy16` and
`xorB` and `dbl` write a block (`BlkStep`): zeros, a copy, the XOR of two
blocks and `double` of a block (`zero16_ok`, `copy16_ok`, `xorB_ok`,
`dbl_ok`), as blocks of memory (`blockAtMem`).
As on AArch64 (`Proof/AesOcb/AArch64/Words.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE
open VG.Spec.Ocb (Block blockAtMem double)
open VG.Proof.Cmac (le8 le8_readW xor_words bytesAt_store2)
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_li wp_ld wp_std wp_xor wp_or wp_and wp_sub wp_lsr wp_lsl)

/-- What a step writing the block at `C + d` does: it writes only there,
the block `v`, and keeps the registers but `clob`. -/
structure BlkStep (C : Addr) (d : Nat) (v : Block) (clob : List Reg) (s s' : State) : Prop where
  frame : Frame [⟨C + BitVec.ofNat 64 d, 16⟩] s.mem s'.mem
  val : blockAtMem s'.mem (C + BitVec.ofNat 64 d) = v
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr
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

/-- `zero16 d`: `W + d ← 0`. -/
theorem zero16_ok {W : Addr} {d : Nat} (hd : d % 4 = 0 ∧ d + 8 < 2 ^ 15) (h31 : s.gpr .r31 = W)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    WP isa (.block (zero16 d)) s (BlkStep W d 0 [.r0] s) := by
  unfold zero16
  refine wp_li (by decide) fun s₁ u₁ => ?_
  refine wp_std (a := W + BitVec.ofNat 64 d) (by decide) ⟨by omega, hd.1⟩ (by rw [u₁.other _ (by decide), h31])
    (by rw [u₁.wr]; exact w₀) fun s₂ u₂ => ?_
  refine wp_std (a := W + BitVec.ofNat 64 (d + 8)) (by decide) ⟨by omega, by omega⟩
    (by rw [u₂.gpr, u₁.other _ (by decide), h31]) (by rw [u₂.wr, u₁.wr]; exact w₁) fun s₃ u₃ => WP.block_nil ?_
  have m₃ : s₃.mem = (s.mem.writeW (W + BitVec.ofNat 64 d) (0 : BitVec 64)).writeW
      (W + BitVec.ofNat 64 d + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [u₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, addr8]; rfl
  refine ⟨by rw [m₃]; exact frame2 _ _ _ _, by rw [m₃, blockAtMem_store2]; decide, fun r hr => ?_,
    by rw [u₃.sp, u₂.sp, u₁.sp], by rw [u₃.lr, u₂.lr, u₁.lr], by rw [u₃.rd, u₂.rd, u₁.rd],
    by rw [u₃.wr, u₂.wr, u₁.wr]⟩
  simp only [List.mem_singleton] at hr
  rw [u₃.gpr, u₂.gpr, u₁.other _ hr]

/-- `copy16 a d`: `W + d ← W + a`. -/
theorem copy16_ok {W : Addr} {a d : Nat} (ha : a % 4 = 0 ∧ a + 8 < 2 ^ 15) (hd : d % 4 = 0 ∧ d + 8 < 2 ^ 15)
    (h31 : s.gpr .r31 = W)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    WP isa (.block (copy16 a d)) s (BlkStep W d (blockAtMem s.mem (W + BitVec.ofNat 64 a)) [.r3, .r4] s) := by
  unfold copy16
  refine wp_ld (a := W + BitVec.ofNat 64 a) (by decide) ⟨by omega, ha.1⟩ (by rw [h31]) r₀ fun s₁ u₁ => ?_
  refine wp_ld (a := W + BitVec.ofNat 64 (a + 8)) (by decide) ⟨by omega, by omega⟩
    (by rw [u₁.other _ (by decide), h31]) (by rw [u₁.rd, u₁.wr]; exact r₁) fun s₂ u₂ => ?_
  refine wp_std (a := W + BitVec.ofNat 64 d) (by decide) ⟨by omega, hd.1⟩
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h31]) (by rw [u₂.wr, u₁.wr]; exact w₀) fun s₃ u₃ => ?_
  refine wp_std (a := W + BitVec.ofNat 64 (d + 8)) (by decide) ⟨by omega, by omega⟩
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h31])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact w₁) fun s₄ u₄ => WP.block_nil ?_
  have m₄ : s₄.mem = (s.mem.writeW (W + BitVec.ofNat 64 d) (s.mem.readW (W + BitVec.ofNat 64 a) 64)).writeW
      (W + BitVec.ofNat 64 d + BitVec.ofNat 64 8) (s.mem.readW (W + BitVec.ofNat 64 a + BitVec.ofNat 64 8) 64) := by
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, u₂.other _ (by decide), u₁.gpr, u₁.mem, addr8, addr8]
  refine ⟨by rw [m₄]; exact frame2 _ _ _ _, by rw [m₄, blockAtMem_store2, blockAtMem_words], fun r hr => ?_,
    by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp], by rw [u₄.lr, u₃.lr, u₂.lr, u₁.lr],
    by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [u₄.gpr, u₃.gpr, u₂.other _ hr.2, u₁.other _ hr.1]

/-- `xorB pb qb cb pd qd cd`: `C + cd ← (P + pd) ⊕ (Q + qd)`, `P`, `Q` and
`C` in `pb`, `qb` and `cb`, the second doublewords of the sources apart from
the first of the result (it may be either source, in place). -/
theorem xorB_ok {P Q C : Addr} {pb qb cb : Reg} {pd qd cd : Nat} (hpd : pd % 4 = 0 ∧ pd + 8 < 2 ^ 15)
    (hqd : qd % 4 = 0 ∧ qd + 8 < 2 ^ 15) (hcd : cd % 4 = 0 ∧ cd + 8 < 2 ^ 15)
    (hp : s.gpr pb = P) (hq : s.gpr qb = Q) (hc : s.gpr cb = C)
    (np : pb ≠ .r0 ∧ pb ≠ .r3 ∧ pb ≠ .r4) (nq : qb ≠ .r0 ∧ qb ≠ .r3 ∧ qb ≠ .r4) (nc : cb ≠ .r0 ∧ cb ≠ .r3 ∧ cb ≠ .r4)
    (rp₀ : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 pd) 8)
    (rp₁ : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 (pd + 8)) 8)
    (rq₀ : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 qd) 8)
    (rq₁ : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 (qd + 8)) 8)
    (w₀ : InRegions s.wr (C + BitVec.ofNat 64 cd) 8) (w₁ : InRegions s.wr (C + BitVec.ofNat 64 (cd + 8)) 8)
    (sp₁ : Mem.Sep (P + BitVec.ofNat 64 (pd + 8)) 8 (C + BitVec.ofNat 64 cd) 8)
    (sq₁ : Mem.Sep (Q + BitVec.ofNat 64 (qd + 8)) 8 (C + BitVec.ofNat 64 cd) 8) :
    WP isa (.block (xorB pb qb cb pd qd cd)) s
      (BlkStep C cd (blockAtMem s.mem (P + BitVec.ofNat 64 pd) ^^^ blockAtMem s.mem (Q + BitVec.ofNat 64 qd))
        [.r3, .r4] s) := by
  unfold xorB
  refine wp_ld (a := P + BitVec.ofNat 64 pd) np.1 ⟨by omega, hpd.1⟩ (by rw [hp]) rp₀ fun s₁ u₁ => ?_
  refine wp_ld (a := Q + BitVec.ofNat 64 qd) nq.1 ⟨by omega, hqd.1⟩ (by rw [u₁.other _ nq.2.1, hq])
    (by rw [u₁.rd, u₁.wr]; exact rq₀) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_std (a := C + BitVec.ofNat 64 cd) nc.1 ⟨by omega, hcd.1⟩
    (by rw [u₃.other _ nc.2.1, u₂.other _ nc.2.2, u₁.other _ nc.2.1, hc])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact w₀) fun s₄ u₄ => ?_
  have g₄ : ∀ r, r ≠ .r3 → r ≠ .r4 → s₄.gpr r = s.gpr r := fun r h3 h4 => by
    rw [u₄.gpr, u₃.other _ h3, u₂.other _ h4, u₁.other _ h3]
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have m₄ : s₄.mem = s.mem.writeW (C + BitVec.ofNat 64 cd)
      (s.mem.readW (P + BitVec.ofNat 64 pd) 64 ^^^ s.mem.readW (Q + BitVec.ofNat 64 qd) 64) := by
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, u₂.other _ (by decide), u₁.gpr, u₁.mem]
  refine wp_ld (a := P + BitVec.ofNat 64 (pd + 8)) np.1 ⟨by omega, by omega⟩
    (by rw [g₄ _ np.2.1 np.2.2, hp]) (by rw [rd₄, wr₄]; exact rp₁) fun s₅ u₅ => ?_
  refine wp_ld (a := Q + BitVec.ofNat 64 (qd + 8)) nq.1 ⟨by omega, by omega⟩
    (by rw [u₅.other _ nq.2.1, g₄ _ nq.2.1 nq.2.2, hq]) (by rw [u₅.rd, u₅.wr, rd₄, wr₄]; exact rq₁) fun s₆ u₆ => ?_
  refine wp_xor fun s₇ u₇ => ?_
  refine wp_std (a := C + BitVec.ofNat 64 (cd + 8)) nc.1 ⟨by omega, by omega⟩
    (by rw [u₇.other _ nc.2.1, u₆.other _ nc.2.2, u₅.other _ nc.2.1, g₄ _ nc.2.1 nc.2.2, hc])
    (by rw [u₇.wr, u₆.wr, u₅.wr, wr₄]; exact w₁) fun s₈ u₈ => WP.block_nil ?_
  have v₅ : s₆.gpr .r3 = s.mem.readW (P + BitVec.ofNat 64 (pd + 8)) 64 := by
    rw [u₆.other _ (by decide), u₅.gpr, m₄, Mem.readW_writeW_sep sp₁ (by decide)]
  have v₆ : s₆.gpr .r4 = s.mem.readW (Q + BitVec.ofNat 64 (qd + 8)) 64 := by
    rw [u₆.gpr, u₅.mem, m₄, Mem.readW_writeW_sep sq₁ (by decide)]
  have m₈ : s₈.mem = (s.mem.writeW (C + BitVec.ofNat 64 cd)
      (s.mem.readW (P + BitVec.ofNat 64 pd) 64 ^^^ s.mem.readW (Q + BitVec.ofNat 64 qd) 64)).writeW
      (C + BitVec.ofNat 64 cd + BitVec.ofNat 64 8)
      (s.mem.readW (P + BitVec.ofNat 64 pd + BitVec.ofNat 64 8) 64 ^^^
        s.mem.readW (Q + BitVec.ofNat 64 qd + BitVec.ofNat 64 8) 64) := by
    rw [u₈.mem, u₇.gpr, u₇.mem, u₆.mem, u₅.mem, m₄, v₅, v₆, addr8, addr8, addr8]
  refine ⟨by rw [m₈]; exact frame2 _ _ _ _, by rw [m₈, blockAtMem_store2, blockAtMem_xor_words], fun r hr => ?_,
    by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp],
    by rw [u₈.lr, u₇.lr, u₆.lr, u₅.lr, u₄.lr, u₃.lr, u₂.lr, u₁.lr], by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, rd₄],
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [u₈.gpr, u₇.other _ hr.1, u₆.other _ hr.2, u₅.other _ hr.1, g₄ _ hr.1 hr.2]

/-- `ldbrx t, a, b`. -/
theorem wp_ldbrx {is : List Instr} {t a b : Reg} {ea : Addr} (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea)
    (hin : InRegions (s.rd ++ s.wr) ea 8)
    (k : ∀ s', Upd s s' t (byteRev64 (s.mem.readW ea 64)) → WP isa (.block is) s' Q) :
    WP isa (.block (.loadRev .d t a b :: is)) s Q := by
  refine VG.Proof.ChaCha20Poly1305.PPC64LE.WP.cons (s' := s.write t (byteRev64 (s.mem.readW ea 64))) ?_
    (k _ (Upd.write _ _ _))
  rw [exec_loadRev_d hn (by rw [hea]; exact hin), hea]
  rfl

/-- `stdbrx t, a, b`. -/
theorem wp_stdbrx {is : List Instr} {t a b : Reg} {ea : Addr} (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea)
    (hout : InRegions s.wr ea 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW ea (byteRev64 (s.gpr t))) → WP isa (.block is) s' Q) :
    WP isa (.block (.storeRev .d t a b :: is)) s Q := by
  refine VG.Proof.ChaCha20Poly1305.PPC64LE.WP.cons (s' := { s with mem := s.mem.writeW ea (byteRev64 (s.gpr t)) })
    ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_storeRev_d hn (by rw [hea]; exact hout), hea]
  rfl

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

/-- `dbl b a d`: `W + d ← double(B + a)`, `B` in `b`. -/
theorem dbl_ok {W B : Addr} {b : Reg} {a d : Nat} (ha : a + 8 < 2 ^ 15) (hd : d + 8 < 2 ^ 15)
    (h31 : s.gpr .r31 = W) (hb : s.gpr b = B) (nb : b ≠ .r0 ∧ b ≠ .r3 ∧ b ≠ .r4 ∧ b ≠ .r5 ∧ b ≠ .r6)
    (r₀ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    WP isa (.block (dbl b a d)) s
      (BlkStep W d (double (blockAtMem s.mem (B + BitVec.ofNat 64 a))) [.r0, .r3, .r4, .r5, .r6] s) := by
  unfold dbl
  refine wp_li (by omega) fun s₁ u₁ => ?_
  refine wp_ldbrx (ea := B + BitVec.ofNat 64 a) nb.1 (by rw [u₁.other _ nb.1, u₁.gpr, hb])
    (by rw [u₁.rd, u₁.wr]; exact r₀) fun s₂ u₂ => ?_
  refine wp_li (by omega) fun s₃ u₃ => ?_
  refine wp_ldbrx (ea := B + BitVec.ofNat 64 (a + 8)) nb.1
    (by rw [u₃.other _ nb.1, u₃.gpr, u₂.other _ nb.2.1, u₁.other _ nb.1, hb])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact r₁) fun s₄ u₄ => ?_
  refine wp_lsr (by decide) fun s₅ u₅ => wp_li (by decide) fun s₆ u₆ => wp_sub fun s₇ u₇ => ?_
  refine wp_li (by decide) fun s₈ u₈ => wp_and fun s₉ u₉ => ?_
  refine wp_lsl (by decide) fun s₁₀ u₁₀ => wp_lsr (by decide) fun s₁₁ u₁₁ => wp_or fun s₁₂ u₁₂ => ?_
  refine wp_lsl (by decide) fun s₁₃ u₁₃ => wp_xor fun s₁₄ u₁₄ => ?_
  have g₁₄ : ∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s₁₄.gpr r = s.gpr r := fun r h0 h3 h4 h5 h6 => by
    rw [u₁₄.other _ h4, u₁₃.other _ h4, u₁₂.other _ h3, u₁₁.other _ h6, u₁₀.other _ h3, u₉.other _ h5,
      u₈.other _ h6, u₇.other _ h5, u₆.other _ h6, u₅.other _ h5, u₄.other _ h4, u₃.other _ h0, u₂.other _ h3,
      u₁.other _ h0]
  have m₁₄ : s₁₄.mem = s.mem := by
    rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem,
      u₂.mem, u₁.mem]
  have h3 : s₄.gpr .r3 = byteRev64 (s.mem.readW (B + BitVec.ofNat 64 a) 64) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem]
  have h4 : s₄.gpr .r4 = byteRev64 (s.mem.readW (B + BitVec.ofNat 64 (a + 8)) 64) := by
    rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
  have hi : s₁₄.gpr .r3 = Proof.Cmac.dblHi (s₄.gpr .r3) (s₄.gpr .r4) := by
    rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.gpr, u₁₁.other .r3 (by decide),
      u₁₀.gpr, u₁₀.other .r4 (by decide), u₉.other .r3 (by decide), u₉.other .r4 (by decide),
      u₈.other .r3 (by decide), u₈.other .r4 (by decide), u₇.other .r3 (by decide), u₇.other .r4 (by decide),
      u₆.other .r3 (by decide), u₆.other .r4 (by decide), u₅.other .r3 (by decide), u₅.other .r4 (by decide)]
    rfl
  have lo : s₁₄.gpr .r4 = Proof.Cmac.dblLo (s₄.gpr .r3) (s₄.gpr .r4) := by
    rw [u₁₄.gpr, u₁₃.gpr, u₁₃.other .r5 (by decide), u₁₂.other .r4 (by decide), u₁₂.other .r5 (by decide),
      u₁₁.other .r4 (by decide), u₁₁.other .r5 (by decide), u₁₀.other .r4 (by decide), u₁₀.other .r5 (by decide),
      u₉.gpr, u₉.other .r4 (by decide), u₈.gpr, u₈.other .r5 (by decide), u₈.other .r4 (by decide), u₇.gpr,
      u₇.other .r4 (by decide), u₆.gpr, u₆.other .r5 (by decide), u₆.other .r4 (by decide), u₅.gpr,
      u₅.other .r4 (by decide)]
    rfl
  have rd₁₄ : s₁₄.rd = s.rd := by
    rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₁₄ : s₁₄.wr = s.wr := by
    rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₁₄ : s₁₄.sp = s.sp := by
    rw [u₁₄.sp, u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have lr₁₄ : s₁₄.lr = s.lr := by
    rw [u₁₄.lr, u₁₃.lr, u₁₂.lr, u₁₁.lr, u₁₀.lr, u₉.lr, u₈.lr, u₇.lr, u₆.lr, u₅.lr, u₄.lr, u₃.lr, u₂.lr, u₁.lr]
  have w31 : s₁₄.gpr .r31 = W := by rw [g₁₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), h31]
  refine wp_li (by omega) fun s₁₅ u₁₅ => ?_
  refine wp_stdbrx (ea := W + BitVec.ofNat 64 d) (by decide) (by rw [u₁₅.other _ (by decide), u₁₅.gpr, w31])
    (by rw [u₁₅.wr, wr₁₄]; exact w₀) fun s₁₆ u₁₆ => ?_
  refine wp_li (by omega) fun s₁₇ u₁₇ => ?_
  refine wp_stdbrx (ea := W + BitVec.ofNat 64 (d + 8)) (by decide)
    (by rw [u₁₇.other _ (by decide), u₁₇.gpr, u₁₆.gpr, u₁₅.other _ (by decide), w31])
    (by rw [u₁₇.wr, u₁₆.wr, u₁₅.wr, wr₁₄]; exact w₁) fun s₁₈ u₁₈ => WP.block_nil ?_
  have m₁₈ : s₁₈.mem = (s.mem.writeW (W + BitVec.ofNat 64 d)
      (byteRev64 (Proof.Cmac.dblHi (byteRev64 (s.mem.readW (B + BitVec.ofNat 64 a) 64))
        (byteRev64 (s.mem.readW (B + BitVec.ofNat 64 a + BitVec.ofNat 64 8) 64))))).writeW
      (W + BitVec.ofNat 64 d + BitVec.ofNat 64 8)
      (byteRev64 (Proof.Cmac.dblLo (byteRev64 (s.mem.readW (B + BitVec.ofNat 64 a) 64))
        (byteRev64 (s.mem.readW (B + BitVec.ofNat 64 a + BitVec.ofNat 64 8) 64)))) := by
    rw [u₁₈.mem, u₁₇.mem, u₁₇.other .r4 (by decide), u₁₆.gpr, u₁₆.mem, u₁₅.mem, u₁₅.other .r4 (by decide),
      u₁₅.other .r3 (by decide), hi, lo, m₁₄, h3, h4, addr8, addr8]
  refine ⟨by rw [m₁₈]; exact frame2 _ _ _ _, by rw [m₁₈, blockAtMem_store2]; exact dbl_mem _ _, fun r hr => ?_,
    by rw [u₁₈.sp, u₁₇.sp, u₁₆.sp, u₁₅.sp, sp₁₄], by rw [u₁₈.lr, u₁₇.lr, u₁₆.lr, u₁₅.lr, lr₁₄],
    by rw [u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, rd₁₄], by rw [u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, wr₁₄]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [u₁₈.gpr, u₁₇.other _ hr.1, u₁₆.gpr, u₁₅.other _ hr.1, g₁₄ _ hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2]

end

end VG.Proof.AesOcb.PPC64LE
