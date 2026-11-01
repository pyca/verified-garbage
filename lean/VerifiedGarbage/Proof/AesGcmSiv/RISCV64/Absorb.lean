module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Wp
import VerifiedGarbage.Proof.GcmSiv.Spec
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesGcmSiv.RISCV64
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Callee
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.Spec.GcmSiv

/-!
# AES-GCM-SIV on RISC-V: POLYVAL's whole blocks (`chunk`)

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcmSiv/PPC64LE/Absorb.lean`): `revLoop` copies blocks to
`W + 496`, each with its bytes reversed (each half loaded big-endian a byte
at a time, `loadBE64`, and stored), so that GHASH reads POLYVAL's field
elements of them (`revMem_block`); `chunk` absorbs up to 64 of them by a call
of `vg_ghash` (`chunk_wp`), whose frame takes the 2048 bytes below the stack
pointer, and a loop of chunks the whole blocks of a string (`chunks_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.Impl.AesGcmSiv.RISCV64 VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_addi wp_li wp_ld wp_sd wp_sll wp_srl wp_sub wp_subi wp_mv)
open VG.Proof.AesGcm.RISCV64 (GhCall GhPost gh_call covers_off covers_prefix in_off)
open VG.Spec.Aes (bytesAt)

/-! ## Reversing blocks -/

theorem be64_byte (m : Mem) (S : Addr) (off : Nat) {i : Nat} (hi : i < 8) :
    (ByteLoad.be64 m S off).extractLsb' (8 * i) 8 = m (S + BitVec.ofNat 64 (off + (7 - i))) := by
  apply BitVec.eq_of_toNat_eq
  simp only [ByteLoad.be64, BitVec.extractLsb'_toNat, Proof.Gcm.toNat_append, Nat.shiftRight_eq_div_pow]
  have h0 := (m (S + BitVec.ofNat 64 off)).isLt
  have h1 := (m (S + BitVec.ofNat 64 (off + 1))).isLt
  have h2 := (m (S + BitVec.ofNat 64 (off + 2))).isLt
  have h3 := (m (S + BitVec.ofNat 64 (off + 3))).isLt
  have h4 := (m (S + BitVec.ofNat 64 (off + 4))).isLt
  have h5 := (m (S + BitVec.ofNat 64 (off + 5))).isLt
  have h6 := (m (S + BitVec.ofNat 64 (off + 6))).isLt
  have h7 := (m (S + BitVec.ofNat 64 (off + 7))).isLt
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul, Nat.reducePow, Nat.reduceSub] <;> omega

theorem writeW64_at (m : Mem) (P : Addr) (v : BitVec 64) {i : Nat} (hi : i < 8) :
    (m.writeW P v) (P + BitVec.ofNat 64 i) = v.extractLsb' (8 * i) 8 := by
  simp only [Mem.writeW, Mem.write, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  simp [show i < 64 / 8 by omega, BitVec.setWidth_eq]

theorem writeW64_off (m : Mem) (P : Addr) (v : BitVec 64) {i : Nat} (hi : 8 ≤ i) (hi' : i < 2 ^ 64 - 8) :
    (m.writeW P v) (P + BitVec.ofNat 64 i) = m (P + BitVec.ofNat 64 i) := by
  simp only [Mem.writeW, Mem.write, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  simp [show ¬ i < 64 / 8 by omega]

theorem writeW64_below (m : Mem) (P : Addr) (v : BitVec 64) {i : Nat} (hi : i < 8) :
    (m.writeW (P + BitVec.ofNat 64 8) v) (P + BitVec.ofNat 64 i) = m (P + BitVec.ofNat 64 i) := by
  simp only [Mem.writeW, Mem.write, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := P.isLt
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]

/-- The big-endian doubleword of bytes in the other order of a little-endian one. -/
theorem be64_rev {m' m : Mem} {P Q : Addr} {off : Nat}
    (h : ∀ j < 8, m' (P + BitVec.ofNat 64 (off + (7 - j))) = m (Q + BitVec.ofNat 64 j)) :
    ByteLoad.be64 m' P off = m.readW Q 64 := by
  refine Bytes.dword_ext fun j hj => ?_
  rw [be64_byte _ _ _ hj, Bytes.readW64_byte _ _ hj, h j hj]

/-- The two doublewords of `revLoop`'s step, loaded big-endian and stored. -/
def revMem (m : Mem) (S P : Addr) : Mem :=
  (m.writeW P (ByteLoad.be64 m S 8)).writeW (P + BitVec.ofNat 64 8) (ByteLoad.be64 m S 0)

theorem revMem_block (m : Mem) (S P : Addr) :
    Spec.Gcm.blockAt (revMem m S P) P = Spec.GcmSiv.ofBytes (Spec.Aes.bytesAt m S 16) := by
  have e₁ : ByteLoad.be64 (revMem m S P) P 0 = m.readW (S + BitVec.ofNat 64 8) 64 := be64_rev fun j hj => by
    rw [Nat.zero_add, revMem, writeW64_below _ _ _ (by omega), writeW64_at _ _ _ (by omega), be64_byte _ _ _ (by omega),
      Offset.add_add, show 8 + (7 - (7 - j)) = 8 + j by omega]
  have e₂ : ByteLoad.be64 (revMem m S P) P 8 = m.readW S 64 := be64_rev fun j hj => by
    rw [revMem, ← Offset.add_add, writeW64_at _ _ _ (by omega), be64_byte _ _ _ (by omega),
      show 0 + (7 - (7 - j)) = j by omega]
  rw [Proof.Gcm.RISCV64.blockAt_hOf, Proof.GcmSiv.ofBytes_bytesAt, Proof.Gcm.RISCV64.hOf, e₁, e₂]

theorem revMem_frame (m : Mem) (S P : Addr) : Frame [⟨P, 16⟩] m (revMem m S P) :=
  Proof.Cmac.frame_store2 _ _ _

theorem blocksAt_succ (m : Mem) (p : Addr) (j : Nat) :
    Spec.Gcm.blocksAt m p (j + 1) = Spec.Gcm.blocksAt m p j ++ [Spec.Gcm.blockAt m (p + BitVec.ofNat 64 (16 * j))] := by
  simp [Spec.Gcm.blocksAt, List.range_succ]

/-- POLYVAL's field elements of the `k` blocks at `Q`. -/
abbrev elemsAt (m : Mem) (Q : Addr) (k : Nat) : List Spec.GcmSiv.Elem :=
  (List.range k).map fun i => Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * i)) 16)

/-- What a chunk may read: `k` bytes at `Q` apart from what it writes. -/
structure Src (c : Cx) (s : State) (Q : Addr) (k : Nat) : Prop where
  rd : Covers [⟨Q, k⟩] (s.rd ++ s.wr)
  lt : k < 2 ^ 64
  wrap : Q.toNat + k ≤ 2 ^ 64
  y : (⟨Q, k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 80, 16⟩
  rev : (⟨Q, k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 496, 1024⟩
  gh : (⟨Q, k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 1536, 256⟩
  b : (below c.SP 2048).Disjoint ⟨Q, k⟩

namespace Src

variable {c : Cx} {s : State} {Q : Addr} {n : Nat} (h : Src c s Q n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Src c s' Q n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

theorem toNat_add {j : Nat} (hj : j < n) : (Q + BitVec.ofNat 64 j).toNat = Q.toNat + j := by
  have := h.wrap
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Src c s Q k where
  rd := covers_prefix h.rd hk
  lt := by have := h.lt; omega_arith
  wrap := by have := h.wrap; omega_arith
  y := h.y.sub_left (Region.sub_prefix hk)
  rev := h.rev.sub_left (Region.sub_prefix hk)
  gh := h.gh.sub_left (Region.sub_prefix hk)
  b := h.b.sub_right (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`, for `a < n`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) (ha : a < n) : Src c s (Q + BitVec.ofNat 64 a) k := by
  have hs : Region.Sub ⟨Q + BitVec.ofNat 64 a, k⟩ ⟨Q, n⟩ := Offset.sub_base _ hk
  exact ⟨covers_off h.rd hk h.lt, by have := h.lt; omega_arith,
    by rw [h.toNat_add ha]; have := h.wrap; omega_arith, h.y.sub_left hs, h.rev.sub_left hs, h.gh.sub_left hs,
    h.b.sub_right hs⟩

end Src

/-- `loadBE64`, as an update of `d` (and of `tmp`). -/
theorem loadBE64_upd {s : State} {d tmp n : Reg} {off : Nat} (hdn : d ≠ n) (htn : tmp ≠ n) (hdt : d ≠ tmp)
    (ho : off + 7 < 2048) (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8) :
    WP isa (.block (Impl.Words.RISCV64.loadBE64 d tmp n off)) s fun s' =>
      s'.gpr d = ByteLoad.be64 s.mem (s.gpr n) off ∧ (∀ r, r ≠ d → r ≠ tmp → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  WP.mono (ByteLoad.loadBE64_ok hdn htn hdt ho h) fun s' e => by
    subst e
    exact ⟨RegUpd.gpr_write_self _ _ _, fun r h1 h2 => by
      rw [RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2], rfl, rfl, rfl, rfl⟩

/-- What `revLoop` leaves after `j` blocks, from `t₀`. -/
structure RInv (c : Cx) (Q : Addr) (k j : Nat) (t₀ t : State) : Prop where
  s9 : t.gpr .s9 = Q + BitVec.ofNat 64 (16 * j)
  a1 : t.gpr .a1 = c.W + BitVec.ofNat 64 (496 + 16 * j)
  a0 : t.gpr .a0 = BitVec.ofNat 64 (k - j)
  frame : Frame [⟨c.W + BitVec.ofNat 64 496, 16 * k⟩] t₀.mem t.mem
  out : Spec.Gcm.blocksAt t.mem (c.W + BitVec.ofNat 64 496) j = elemsAt t₀.mem Q j
  keep : Keep [.t0, .a0, .a1, .a2, .a3, .s9] t₀ t
  sp : t.sp = t₀.sp

/-- `revLoop`: `k` blocks at `Q` copied to `W + 496`, each reversed, so that
GHASH reads POLYVAL's field elements of them. -/
theorem revLoop_wp {c : Cx} (L : Lay c) {t₀ : State} (E : Env c t₀) {Q : Addr} {k : Nat}
    (hk1 : 1 ≤ k) (hk : k ≤ 64) (hQ : Src c t₀ Q (16 * k)) (h23 : t₀.gpr .s9 = Q)
    (h4 : t₀.gpr .a1 = c.W + BitVec.ofNat 64 496) (h3 : t₀.gpr .a0 = BitVec.ofNat 64 k) :
    WP isa revLoop t₀ fun t => Frame [⟨c.W + BitVec.ofNat 64 496, 16 * k⟩] t₀.mem t.mem ∧
      Spec.Gcm.blocksAt t.mem (c.W + BitVec.ofNat 64 496) k = elemsAt t₀.mem Q k ∧
      t.gpr .s9 = Q + BitVec.ofNat 64 (16 * k) ∧ Keep [.t0, .a0, .a1, .a2, .a3, .s9] t₀ t ∧ t.sp = t₀.sp := by
  have hw := L.ww
  have I₀ : RInv c Q k 0 t₀ t₀ := ⟨by rw [h23, Nat.mul_zero, BitVec.add_zero], by rw [h4],
    by rw [h3, Nat.sub_zero], Frame.refl _ _, by simp only [Spec.Gcm.blocksAt, elemsAt, List.range_zero, List.map_nil],
    Keep.refl _ _, rfl⟩
  refine WP.loop (M := isa)
    (fun (w : Nat) (t : State) => ∃ j, w = k - j ∧ j < k ∧ RInv c Q k j t₀ t) ?_ (k - 0) t₀ ⟨0, rfl, hk1, I₀⟩
  rintro w t ⟨j, rfl, hj, I⟩
  have hr : Covers [⟨Q + BitVec.ofNat 64 (16 * j), 16⟩] (t.rd ++ t.wr) := by
    rw [I.keep.2.1, I.keep.2.2]; exact covers_off hQ.rd (by omega_arith) hQ.lt
  have hwr : Covers [⟨c.W + BitVec.ofNat 64 (496 + 16 * j), 16⟩] t.wr := by
    rw [I.keep.2.2]; exact E.perm.wC (by omega_arith)
  have in8 (P : Addr) {rs : List Region} (h : Covers [⟨P, 16⟩] rs) (d : Nat) (hd : d + 8 ≤ 16) :
      InRegions rs (P + BitVec.ofNat 64 d) 8 := in_off h hd (by decide)
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (loadBE64_upd (s := t) (d := .a2) (tmp := .t0) (n := .s9) (off := 8)
    (by decide) (by decide) (by decide) (by decide) (by rw [I.s9]; exact in8 _ hr 8 (by decide)))
    fun t₁ ⟨v₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  refine WP.block_append (WP.mono (loadBE64_upd (s := t₁) (d := .a3) (tmp := .t0) (n := .s9) (off := 0)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [rd₁, wr₁, g₁ _ (by decide) (by decide), I.s9]; simpa using in8 _ hr 0 (by decide)))
    fun t₂ ⟨v₂, g₂, m₂, rd₂, wr₂, sp₂⟩ => ?_)
  have a1₂ : t₂.gpr .a1 = c.W + BitVec.ofNat 64 (496 + 16 * j) := by
    rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), I.a1]
  have al : (c.W + BitVec.ofNat 64 (496 + 16 * j)).toNat % 8 = 0 := L.wal8 (by omega_arith) (by omega_arith)
  refine wp_sd (a := c.W + BitVec.ofNat 64 (496 + 16 * j)) (by decide) (by rw [a1₂]; exact BitVec.add_zero _) al
    (by rw [wr₂, wr₁]; simpa using in8 _ hwr 0 (by decide)) fun t₃ u₃ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 (496 + 16 * j) + BitVec.ofNat 64 8) (by decide)
    (by rw [u₃.gpr, a1₂]) (by rw [Offset.add_add]; exact L.wal8 (by omega_arith) (by omega_arith))
    (by rw [u₃.wr, wr₂, wr₁]; exact in8 _ hwr 8 (by decide)) fun t₄ u₄ => ?_
  refine wp_addi (by decide) fun t₅ u₅ => wp_addi (by decide) fun t₆ u₆ =>
    wp_subi (imm := 1) (by decide) fun t₇ u₇ => WP.block_nil ?_
  have s9t : t.gpr .s9 = Q + BitVec.ofNat 64 (16 * j) := I.s9
  have hm : t₇.mem = revMem t.mem (Q + BitVec.ofNat 64 (16 * j)) (c.W + BitVec.ofNat 64 (496 + 16 * j)) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, m₂, v₂, g₂ .a2 (by decide) (by decide), v₁,
      g₁ .s9 (by decide) (by decide), m₁, s9t]
    rfl
  -- The source is outside the copies.
  have src : bytesAt t.mem (Q + BitVec.ofNat 64 (16 * j)) 16 = bytesAt t₀.mem (Q + BitVec.ofNat 64 (16 * j)) 16 :=
    Proof.Cmac.bytesAt_frame16 I.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hQ.rev.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub _ (by omega_arith) (by omega_arith)))
  have fr : Frame [⟨c.W + BitVec.ofNat 64 (496 + 16 * j), 16⟩] t.mem t₇.mem := by
    rw [hm]; exact revMem_frame _ _ _
  have kp : Keep [.t0, .a0, .a1, .a2, .a3, .s9] t t₇ :=
    ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₇.other _ hr.2.1, u₆.other _ hr.2.2.1, u₅.other _ hr.2.2.2.2.2, u₄.gpr, u₃.gpr, g₂ _ hr.2.2.2.2.1 hr.1,
        g₁ _ hr.2.2.2.1 hr.1],
      by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, rd₁], by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁]⟩
  have r3' : t₇.gpr .a0 = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, g₂ _ (by decide) (by decide),
      g₁ _ (by decide) (by decide), I.a0, ofNat_sub (by omega_arith) (by omega_arith), Nat.sub_sub]
  have I' : RInv c Q k (j + 1) t₀ t₇ := by
    refine ⟨?_, ?_, r3', ?_, ?_, (I.keep.trans kp).mono (by decide), ?_⟩
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.gpr, g₂ _ (by decide) (by decide),
        g₁ _ (by decide) (by decide), I.s9, Offset.add_add, Nat.mul_succ]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, a1₂, Offset.add_add,
        Nat.mul_succ, Nat.add_assoc]
    · exact I.frame.trans (fr.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega_arith) (by omega_arith)⟩)
    · rw [blocksAt_succ, blocksAt_frame fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith), I.out]
      simp only [elemsAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [Offset.add_add, hm, revMem_block, src]
    · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, sp₁, I.sp]
  have ev := Steps.eval_nonzero_ofNat _ _ (by omega_arith) r3'
  by_cases he : j + 1 = k
  · left
    refine ⟨ev.trans (by simp [he]), ?_⟩
    exact ⟨I'.frame, he ▸ I'.out, he ▸ I'.s9, I'.keep, I'.sp⟩
  · right
    exact ⟨ev.trans (by simp; omega_arith), k - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, I'⟩

/-! ## A chunk -/

/-- `chunkLen`: the number of blocks of the chunk, `min (m / 16) 64`. -/
theorem chunkLen_wp {t : State} {m : Nat} (hm : m < 2 ^ 64) (h10 : t.gpr .s10 = BitVec.ofNat 64 m) :
    WP isa chunkLen t fun t' => Upd t t' .s11 (BitVec.ofNat 64 (min (m / 16) 64)) := by
  unfold chunkLen
  refine WP.seq (wp_srl (by decide) fun t₁ u₁ => WP.block_nil ?_)
  have e1 : t₁.gpr .s11 = BitVec.ofNat 64 (m / 1024) := by rw [u₁.gpr, h10, ofNat_lsr 10 hm]
  refine WP.ite (decide (m / 1024 = 0)) (Steps.eval_zero_ofNat _ _ (by omega_arith) e1) (fun ht => ?_)
    (fun hf => ?_)
  · have h0 : m / 1024 = 0 := by simpa using ht
    refine wp_srl (by decide) fun t₂ u₂ => WP.block_nil (upd2 u₁ u₂ ?_)
    rw [u₁.other _ (by decide), h10, ofNat_lsr 4 hm]
    exact congrArg (BitVec.ofNat 64) (by omega_arith)
  · have h0 : m / 1024 ≠ 0 := by simpa using hf
    refine wp_li (by decide) fun t₂ u₂ => WP.block_nil (upd2 u₁ u₂ ?_)
    have h64 : 64 ≤ m / 16 := by omega_arith
    exact congrArg (BitVec.ofNat 64) (Nat.min_eq_right h64).symm

/-- A chunk up to its call: up to 64 blocks reversed at `W + 496`, the
pointer and the count past them, and the arguments of `vg_ghash`. -/
structure ChunkPre (c : Cx) (Q : Addr) (m k : Nat) (t t₅ : State) : Prop where
  call : GhCall t₅ (c.W + BitVec.ofNat 64 64) (c.W + BitVec.ofNat 64 80) (c.W + BitVec.ofNat 64 496)
    (c.W + BitVec.ofNat 64 1536) k
  pk : PK t t₅
  s9 : t₅.gpr .s9 = Q + BitVec.ofNat 64 (16 * k)
  s10 : t₅.gpr .s10 = BitVec.ofNat 64 (m - 16 * k)
  frame : Frame [⟨c.W + BitVec.ofNat 64 496, 16 * k⟩] t.mem t₅.mem
  out : Spec.Gcm.blocksAt t₅.mem (c.W + BitVec.ofNat 64 496) k = elemsAt t.mem Q k

/-- The pieces of a chunk before its call. -/
theorem chunkPre_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {Q : Addr} {m : Nat} (hm : m < 2 ^ 64)
    (h16 : 16 ≤ m) (hQ : Src c t Q (16 * (m / 16))) (h9 : t.gpr .s9 = Q) (h10 : t.gpr .s10 = BitVec.ofNat 64 m) :
    WP isa chunkPre t (ChunkPre c Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  have hk1 : 1 ≤ min (m / 16) 64 := by omega_arith
  unfold chunkPre
  refine WP.seq (WP.mono (chunkLen_wp hm h10) fun t₁ u₁ => ?_)
  refine WP.seq (wp_addi (by decide) fun t₂ u₂ => wp_mv fun t₃ u₃ => WP.block_nil ?_)
  have pk₃ : PK t t₃ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans (PK.ofUpd u₃))
  have E₃ := E.of_pk pk₃
  have hQ₃ : Src c t₃ Q (16 * min (m / 16) 64) := (hQ.take (by omega_arith)).of_eq pk₃.rd pk₃.wr
  have m₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.seq (WP.mono (revLoop_wp L E₃ hk1 (by omega_arith) hQ₃
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h9])
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s0]; rfl)
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr]))
    fun t₆ ⟨fr₆, out₆, s9₆, kp₆, sp₆⟩ => ?_)
  have pk₆ : PK t₃ t₆ := ⟨kp₆.2.1, kp₆.2.2, sp₆, fun r hr => kp₆.1 r (by revert r; decide)⟩
  have E₆ := E₃.of_pk pk₆
  have s11₆ : t₆.gpr .s11 = BitVec.ofNat 64 (min (m / 16) 64) := by
    rw [kp₆.1 _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have s10₆ : t₆.gpr .s10 = BitVec.ofNat 64 m := by
    rw [kp₆.1 _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h10]
  rw [m₃] at fr₆ out₆
  unfold chunkArgs
  refine wp_sll (by decide) fun t₇ u₇ => wp_sub fun t₈ u₈ => wp_addi (by decide) fun t₉ u₉ =>
    wp_addi (by decide) fun t₁₀ u₁₀ => wp_addi (by decide) fun t₁₁ u₁₁ =>
    wp_mv fun t₁₂ u₁₂ => wp_addi (by decide) fun t₁₃ u₁₃ => WP.block_nil ?_
  have pk₁₃ : PK t₆ t₁₃ := (PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans ((PK.ofUpd u₉).trans ((PK.ofUpd u₁₀).trans
    ((PK.ofUpd u₁₁).trans ((PK.ofUpd u₁₂).trans (PK.ofUpd u₁₃))))))
  have E₁₃ := E₆.of_pk pk₁₃
  have hk : 16 * min (m / 16) 64 ≤ 1024 := by omega_arith
  have sp₁₃ : t₁₃.sp = c.SP := E₁₃.sp
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    pk₃.trans (pk₆.trans pk₁₃), ?_, ?_,
    by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]; exact fr₆,
    by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]; exact out₆⟩
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), E₆.s0]; rfl
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr,
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), E₆.s0]; rfl
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), E₆.s0]; rfl
  · rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), s11₆]
  · rw [u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), E₆.s0]; rfl
  · exact L.w_w (.inl (by decide)) (by decide) (by omega_arith)
  · rw [sp₁₃]; exact L.b_w' (by decide)
  · rw [sp₁₃]; exact L.b_w' (by decide)
  · rw [sp₁₃]; exact L.b_w' (by omega_arith)
  · rw [L.wrapW (by decide)]; omega_arith
  · rw [L.wrapW (by decide)]; omega_arith
  · rw [sp₁₃]; exact L.spal
  · rw [sp₁₃]; exact L.spge
  · exact Covers.append_left (Covers.cons (E₁₃.perm.wCR (by decide)) (Covers.cons (E₁₃.perm.wCR (by omega_arith))
      Covers.nil)) (Covers.cons (E₁₃.perm.wCR (by decide)) (Covers.cons (E₁₃.perm.wCR (by decide)) Covers.nil))
  · exact Covers.cons (E₁₃.perm.wC (by decide)) (Covers.cons (E₁₃.perm.wC (by decide)) Covers.nil)
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), s9₆]
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₇.other _ (by decide), s10₆, s11₆, ofNat_shl,
      ofNat_sub (by omega_arith) hm]

/-- What a chunk writes: GHASH's accumulator, the reversed blocks,
`vg_ghash`'s working space and the 2048 bytes below the stack pointer. -/
abbrev absR (c : Cx) : List Region :=
  [⟨c.W + BitVec.ofNat 64 80, 16⟩, ⟨c.W + BitVec.ofNat 64 496, 1024⟩, ⟨c.W + BitVec.ofNat 64 1536, 256⟩,
    below c.SP 2048]

/-- What a chunk leaves, from `t`, after absorbing `k` blocks of the `m`
bytes at `Q`. -/
structure ChunkPost (c : Cx) (Q : Addr) (m k : Nat) (t t' : State) : Prop where
  pk : PK t t'
  s9 : t'.gpr .s9 = Q + BitVec.ofNat 64 (16 * k)
  s10 : t'.gpr .s10 = BitVec.ofNat 64 (m - 16 * k)
  a7 : t'.gpr .a7 = BitVec.ofNat 64 ((m - 16 * k) / 16)
  frame : Frame (absR c) t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (c.W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (c.W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (c.W + BitVec.ofNat 64 80)) (elemsAt t.mem Q k)

theorem chunk_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {Q : Addr} {m : Nat}
    (hm : m < 2 ^ 64) (h16 : 16 ≤ m) (hQ : Src c t Q (16 * (m / 16))) (h9 : t.gpr .s9 = Q)
    (h10 : t.gpr .s10 = BitVec.ofNat 64 m) :
    WP isa chunk t (ChunkPost c Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  have hk : 16 * min (m / 16) 64 ≤ 1024 := by omega_arith
  unfold chunk
  refine WP.seq (WP.mono (chunkPre_wp L E hm h16 hQ h9 h10) fun t₅ Pr => ?_)
  refine WP.seq (WP.mono (gh_call Pr.call) fun t₆ P => ?_)
  have pk₆ : PK t₅ t₆ := PK.ofSaved P.rd P.wr P.sp P.saved
  have s10₆ : t₆.gpr .s10 = BitVec.ofNat 64 (m - 16 * min (m / 16) 64) := by
    rw [P.saved _ (by decide), Pr.s10]
  have dH : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 496, 16 * min (m / 16) 64⟩ : Region)],
      (⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega_arith)) (by decide) (by omega_arith)
  have dY : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 496, 16 * min (m / 16) 64⟩ : Region)],
      (⟨c.W + BitVec.ofNat 64 80, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega_arith)) (by decide) (by omega_arith)
  have out₆ := P.out
  rw [blockAt_frame Pr.frame dH, blockAt_frame Pr.frame dY, Pr.out] at out₆
  have sp₅ : t₅.sp = c.SP := (E.of_pk Pr.pk).sp
  unfold wholeLeft
  refine wp_srl (by decide) fun t₇ u₇ => WP.block_nil ⟨Pr.pk.trans (pk₆.trans (PK.ofUpd u₇)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), P.saved _ (by decide), Pr.s9]
  · rw [u₇.other _ (by decide), s10₆]
  · rw [u₇.gpr, s10₆, ofNat_lsr 4 (by omega_arith)]
  · rw [u₇.mem]
    have fr := P.frame
    rw [sp₅] at fr
    refine (Pr.frame.sub fun r hr => ?_).trans (fr.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega_arith)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  · rw [u₇.mem]; exact out₆

/-! ## Absorbing -/

theorem elemsAt_add (m : Mem) (Q : Addr) (d k : Nat) :
    elemsAt m Q (d + k) = elemsAt m Q d ++ elemsAt m (Q + BitVec.ofNat 64 (16 * d)) k := by
  simp only [elemsAt, List.range_add, List.map_append, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp, Offset.add_add, Nat.mul_add]

theorem elemsAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Q : Addr} {k : Nat}
    (hd : ∀ r ∈ rs, (⟨Q, 16 * k⟩ : Region).Disjoint r) (hk : 16 * k ≤ 2 ^ 64) : elemsAt m' Q k = elemsAt m Q k := by
  unfold elemsAt
  rw [← GcmSiv.elems_bytesAt, ← GcmSiv.elems_bytesAt, Proof.Cmac.bytesAt_frame hf hd hk]

/-- What absorbing writes: what a chunk writes, and the block at `W + 240`. -/
abbrev absorbR (c : Cx) : List Region := ⟨c.W + BitVec.ofNat 64 240, 16⟩ :: absR c

/-- What absorbing leaves, from `t`, having absorbed the elements `xs` and
written only `rs`. -/
structure Absorbed (c : Cx) (rs : List Region) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop where
  pk : PK t t'
  frame : Frame rs t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (c.W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (c.W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (c.W + BitVec.ofNat 64 80)) xs

theorem absorbR_H {c : Cx} (L : Lay c) :
    ∀ r ∈ absorbR c, (⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.b_w' (by decide)).symm

theorem absR_H {c : Cx} (L : Lay c) : ∀ r ∈ absR c, (⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r :=
  fun r hr => absorbR_H L r (List.mem_cons_of_mem _ hr)

/-- A buffer apart from `W` misses what absorbing writes. -/
theorem absorbR_buf {c : Cx} {P : Addr} {k : Nat} (hd : (⟨P, k⟩ : Region).Disjoint ⟨c.W, 3840⟩)
    (hb : (below c.SP 2048).Disjoint ⟨P, k⟩) : ∀ r ∈ absorbR c, (⟨P, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hb.symm

theorem absR_sub (c : Cx) : ∀ r ∈ absR c, ∃ r' ∈ absorbR c, Region.Sub r r' :=
  fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩

theorem Absorbed.trans {c : Cx} {rs : List Region} {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (hH : ∀ r ∈ rs, (⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r)
    (h₁ : Absorbed c rs xs t t₁) (h₂ : Absorbed c rs ys t₁ t₂) : Absorbed c rs (xs ++ ys) t t₂ := by
  refine ⟨h₁.pk.trans h₂.pk, h₁.frame.trans h₂.frame, ?_⟩
  rw [h₂.out, h₁.out, blockAt_frame h₁.frame hH, Proof.Gcm.ghashFrom_append]

theorem Absorbed.sub {c : Cx} {rs rs' : List Region} {xs : List Spec.GcmSiv.Elem} {t t' : State}
    (h : Absorbed c rs xs t t') (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : Absorbed c rs' xs t t' :=
  ⟨h.pk, h.frame.sub hs, h.out⟩

theorem Absorbed.of_chunk {c : Cx} {Q : Addr} {m k : Nat} {t t' : State}
    (h : ChunkPost c Q m k t t') : Absorbed c (absR c) (elemsAt t.mem Q k) t t' :=
  ⟨h.pk, h.frame, h.out⟩

theorem Absorbed.of_eq {c : Cx} {rs : List Region} {xs : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h : Absorbed c rs xs t₁ t₂) (pk : PK t t₁) (hm : t₁.mem = t.mem) : Absorbed c rs xs t t₂ :=
  ⟨pk.trans h.pk, hm ▸ h.frame, by rw [h.out, hm]⟩

/-- The chunks of the `m` bytes at `Q`, from `σ`, after `d` blocks. -/
structure CInv (c : Cx) (σ : State) (Q : Addr) (m d : Nat) (t : State) : Prop where
  abs : Absorbed c (absR c) (elemsAt σ.mem Q d) σ t
  s9 : t.gpr .s9 = Q + BitVec.ofNat 64 (16 * d)
  s10 : t.gpr .s10 = BitVec.ofNat 64 (m - 16 * d)

/-- A chunk, in the chunks. -/
theorem CInv.step {c : Cx} (L : Lay c) {σ t t' : State} {Q : Addr} {m d : Nat}
    (hQ : Src c σ Q (16 * (m / 16))) (hd : d < m / 16) (I : CInv c σ Q m d t)
    (C : ChunkPost c (Q + BitVec.ofNat 64 (16 * d)) (m - 16 * d) (min ((m - 16 * d) / 16) 64) t t') :
    CInv c σ Q m (d + min (m / 16 - d) 64) t' ∧
      t'.gpr .a7 = BitVec.ofNat 64 (m / 16 - (d + min (m / 16 - d) 64)) := by
  have hk : min ((m - 16 * d) / 16) 64 = min (m / 16 - d) 64 := by congr 1; omega_arith
  rw [hk] at C
  have hs := hQ.slice (a := 16 * d) (k := 16 * min (m / 16 - d) 64) (by omega_arith) (by omega_arith)
  have C' := Absorbed.of_chunk C
  rw [elemsAt_frame I.abs.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hs.y
      · exact hs.rev
      · exact hs.gh
      · exact hs.b.symm) (by omega_arith)] at C'
  refine ⟨⟨by rw [elemsAt_add]; exact Absorbed.trans (absR_H L) I.abs C', by rw [C.s9, Offset.add_add, Nat.mul_add],
    by rw [C.s10]; congr 1; omega_arith⟩, by rw [C.a7]; congr 1; omega_arith⟩

/-- The whole blocks: chunks until fewer than 16 bytes are left. -/
theorem chunks_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {Q : Addr} {m : Nat}
    (hm : m < 2 ^ 64) (h16 : 16 ≤ m) (hQ : Src c t Q (16 * (m / 16))) (h9 : t.gpr .s9 = Q)
    (h10 : t.gpr .s10 = BitVec.ofNat 64 m) :
    WP isa (.loop chunk (.nonzero .a7)) t fun t' =>
      Absorbed c (absR c) (elemsAt t.mem Q (m / 16)) t t' ∧
      t'.gpr .s9 = Q + BitVec.ofNat 64 (16 * (m / 16)) ∧ t'.gpr .s10 = BitVec.ofNat 64 (m % 16) := by
  refine WP.loop (M := isa)
    (fun (k : Nat) (t' : State) => ∃ d, k = m / 16 - d ∧ d < m / 16 ∧ CInv c t Q m d t') ?_
    (m / 16 - 0) t ⟨0, rfl, by omega_arith, ⟨⟨PK.refl _, Frame.refl _ _, by simp [elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
      by rw [h9, Nat.mul_zero, BitVec.add_zero], by rw [h10, Nat.mul_zero, Nat.sub_zero]⟩⟩
  rintro k t' ⟨d, rfl, hd, I⟩
  refine WP.mono (chunk_wp L (E.of_pk I.abs.pk) (by omega_arith) (by omega_arith)
    ((hQ.slice (by omega_arith) (by omega_arith)).of_eq I.abs.pk.rd I.abs.pk.wr) I.s9 I.s10) fun t'' C => ?_
  obtain ⟨I', a7⟩ := I.step L hQ hd C
  have ev := Steps.eval_nonzero_ofNat _ _ (by omega_arith) a7
  by_cases he : d + min (m / 16 - d) 64 = m / 16
  · left
    refine ⟨ev.trans (by simp; omega_arith), he ▸ I'.abs, by rw [I'.s9, he], by rw [I'.s10, he]; congr 1; omega_arith⟩
  · right
    exact ⟨ev.trans (by simp; omega_arith), m / 16 - (d + min (m / 16 - d) 64), by omega_arith, d + min (m / 16 - d) 64, rfl,
      by omega_arith, I'⟩

end VG.Proof.AesGcmSiv.RISCV64
