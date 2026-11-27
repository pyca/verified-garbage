module

import VerifiedGarbage.Proof.AesSiv.RISCV64.Mac
import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.Siv.Spec
import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesSiv.RISCV64.Env
public import VerifiedGarbage.Proof.AesCtr.RISCV64.Call
public import VerifiedGarbage.Proof.AesSiv.CtrPart
public import VerifiedGarbage.Impl.AesSiv.RISCV64
public import VerifiedGarbage.Proof.AesSiv.Words
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.RISCV64.BE64

/-! ### `AesSiv.RISCV64.Ctr`, which this module and modules that import it used -/

section

/-!
# AES-SIV on RISC-V: the counter and the calls of CTR

Untrusted: everything here is checked by Lean. The counter `Q + i` is kept
at `W + 64` as two byte-reversed doublewords whose second is
`(Q mod 2⁶⁴) + i`, below `2⁶⁴` (`CntAt`): its bytes are `be128 (Q + i)`
(`CntAt.bytes`), and adding `k` to the second doubleword alone adds `k`
(`cnt_add`), which the code does by loading it big-endian a byte at a time
(`loadBE64`, a byte-reversed doubleword), adding, and storing it back the
same way (`storeBE`; `bump_wp`). `counter` writes `Q` from the IV
(`counter_wp`), `copy16` copies a block of `W` (`copy16_wp`), and
`ctrWhole` encrypts the first `⌊L / 16⌋ mod 2³¹` blocks of the data by one
call of `vg_aes_ctr32` (`ctrWhole_wp`). As on PPC64LE
(`Proof/AesSiv/PPC64LE/CtrLoop.lean`), with `byteRev64` for its byte-reversed
loads and stores.

Untrusted: everything here is checked by Lean. The counter `Q + i` is kept
at `W + 64` as two doublewords whose bytes are the halves of the 128-bit
integer, big-endian (`le8_rev`): the second is read and written a byte at a
time, big-endian (`loadBE64`, `storeBE`), which loads and stores the
byte-reversed doubleword (`BE64.wp_loadBE64`, `BE64.wp_storeBE8`). `counter` clears bit 7 of the
IV's bytes 8 and 12 by setting and flipping it (`orr_eor`), which leaves the
counter's second doubleword below `2⁶³` (`counter_low64`), so adding to that
doubleword alone, fewer than `2⁶³` in all, adds to the integer (`add_lo`).
The counter's words are as on PPC64LE (`Proof/AesSiv/PPC64LE/Counter.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

section Counter

open VG
open VG.Proof.Cmac (le8 length_le8)
open VG.Proof.AesCcm (beVal beVal_append beVal_cons beVal_lt)

/-- Storing the byte-reversed halves of `h ++ l` stores its bytes, big-endian. -/
theorem le8_rev (h l : BitVec 64) :
    le8 (byteRev64 h) ++ le8 (byteRev64 l) = Spec.Gcm.toBytes (h ++ l) := by
  refine Proof.Cmac.ext16 (by simp [length_le8]) (Proof.Cmac.toBytes_length _) fun k hk => ?_
  rw [Proof.Aes.toBytes_getD _ hk]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp only [hj, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge k 8 with h8 | h8
  · rw [getD_le8_append _ _ hk]
    simp only [h8, ↓reduceIte]
    rw [BitVec.getLsbD_extractLsb', byteRev64_getLsbD _ (by omega_using [hj, h8])]
    simp only [hj, decide_true, Bool.true_and, show ¬ 8 * (15 - k) + j < 64 by omega_using [h8], ite_false]
    congr 1; omega_using [hj, h8]
  · rw [getD_le8_append _ _ hk]
    simp only [show ¬ k < 8 by omega_using [h8], ↓reduceIte]
    rw [BitVec.getLsbD_extractLsb', byteRev64_getLsbD _ (by omega_using [hk, hj])]
    simp only [hj, decide_true, Bool.true_and, show 8 * (15 - k) + j < 64 by omega_using [hj, h8], ite_true]
    congr 1; omega_using [hj, h8]

theorem rev64_rev64 (a : BitVec 64) : byteRev64 (byteRev64 a) = a := Proof.Gcm.byteRev64_byteRev64 a

/-- Adding to the low doubleword, without a carry, adds to the integer. -/
theorem add_lo (hi lo : BitVec 64) {k : Nat} (h : lo.toNat + k < 2 ^ 64) :
    (hi ++ (lo + BitVec.ofNat 64 k) : BitVec 128) = (hi ++ lo : BitVec 128) + BitVec.ofNat 128 k := by
  apply BitVec.eq_of_toNat_eq
  have hl := lo.isLt
  have hh := hi.isLt
  simp only [BitVec.toNat_append, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_using [h]), Nat.mod_eq_of_lt (show k < 2 ^ 128 by omega_using [h]),
    Nat.mod_eq_of_lt h, ← Nat.shiftLeft_add_eq_or_of_lt h, ← Nat.shiftLeft_add_eq_or_of_lt hl,
    Nat.shiftLeft_eq]
  have : hi.toNat * 2 ^ 64 + lo.toNat + k < 2 ^ 128 := by
    have : hi.toNat * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := Nat.mul_le_mul_right _ (by omega_using [])
    omega_using [h]
  rw [Nat.mod_eq_of_lt this]
  omega_using []

/-- The bits `counter` sets and flips: bit 7 of the doubleword's bytes 0 and 4. -/
def qbits : BitVec 64 := 0x8000000080

/-- Setting the bits and flipping them clears them. -/
theorem orr_eor (x : BitVec 64) : (x ||| qbits) ^^^ qbits = x &&& qmask := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  obtain hb : ∀ j < 64, qbits.getLsbD j = decide (j = 7 ∨ j = 39) := by decide
  obtain hq : ∀ j < 64, qmask.getLsbD j = !decide (j = 7 ∨ j = 39) := by decide
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_and, hb j hj, hq j hj]
  cases x.getLsbD j <;> by_cases h : j = 7 ∨ j = 39 <;> simp [h]

/-- The counter `Q`'s last 64 bits, as a big-endian integer, are below `2⁶³`. -/
theorem counter_low64 (v : List Byte) : Spec.Siv.beNat (Spec.Siv.counter v) % 2 ^ 64 < 2 ^ 63 := by
  obtain e : Spec.Siv.counter v = ((List.range 8).map fun i => v.getD i 0) ++
      [v.getD 8 0 &&& 0x7f, v.getD 9 0, v.getD 10 0, v.getD 11 0, v.getD 12 0 &&& 0x7f, v.getD 13 0,
        v.getD 14 0, v.getD 15 0] := by
    simp [Spec.Siv.counter, List.range_succ]
  rw [e, show Spec.Siv.beNat = beVal from rfl, beVal_append]
  simp only [List.length_cons, List.length_nil]
  obtain hr := beVal_lt [v.getD 9 0, v.getD 10 0, v.getD 11 0, v.getD 12 0 &&& 0x7f, v.getD 13 0, v.getD 14 0,
    v.getD 15 0]
  simp only [List.length_cons, List.length_nil] at hr
  rw [beVal_cons]
  simp only [List.length_cons, List.length_nil]
  obtain h0 : (v.getD 8 0 &&& 0x7f).toNat < 128 := by
    rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  generalize beVal [v.getD 9 0, v.getD 10 0, v.getD 11 0, v.getD 12 0 &&& 0x7f, v.getD 13 0, v.getD 14 0,
    v.getD 15 0] = r at hr ⊢
  generalize (v.getD 8 0 &&& 0x7f).toNat = b at h0 ⊢
  simp only [Nat.reducePow, Nat.reduceAdd] at hr ⊢
  omega_using [hr, h0]

end Counter


open VG VG.Impl.AesSiv.RISCV64
open VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.AesCtr.RISCV64 (CtrCall)
open VG.Proof.AesCcm.RISCV64 (covers_prefix)
open VG.Proof.Cmac (le8)
open VG.Spec.Aes (bytesAt)

/-- What CTR writes: the data, the counter, keystream and counter blocks at
`W + 64`, and the working space of `vg_aes_ctr32`. -/
abbrev ctrR (c : Cx) : List Region :=
  [⟨c.D, c.n⟩, ⟨c.W + BitVec.ofNat 64 64, 48⟩, ⟨c.W + BitVec.ofNat 64 384, 2048⟩]

/-! ## The counter -/

/-- The counter `Q + i` at `W + 64`, `Q` the bytes `q`: two byte-reversed
doublewords, the second `(Q mod 2⁶⁴) + i`. -/
def CntAt (m : Mem) (W : Addr) (q : List Byte) (i : Nat) : Prop :=
  ∃ hi lo : BitVec 64, m.readW (W + BitVec.ofNat 64 cntO) 64 = byteRev64 hi ∧
    m.readW (W + BitVec.ofNat 64 (cntO + 8)) 64 = byteRev64 lo ∧
    (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes q + BitVec.ofNat 128 i ∧
    lo.toNat = Spec.Siv.beNat q % 2 ^ 64 + i

theorem CntAt.bytes {m : Mem} {W : Addr} {q : List Byte} {i : Nat} (h : CntAt m W q i) :
    bytesAt m (W + BitVec.ofNat 64 cntO) 16 = Spec.Siv.be128 (Spec.Siv.beNat q + i) := by
  obtain ⟨hi, lo, h0, h8, happ, _⟩ := h
  rw [Proof.Cmac.bytesAt_split, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, Offset.add_add, h0, h8, le8_rev,
    happ, be128_add]

theorem CntAt.frame {m m' : Mem} {W : Addr} {q : List Byte} {i : Nat} (h : CntAt m W q i) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 cntO, 16⟩ : Region).Disjoint r) : CntAt m' W q i := by
  obtain ⟨hi, lo, h0, h8, happ, hlo⟩ := h
  refine ⟨hi, lo, ?_, ?_, happ, hlo⟩
  · have := Proof.Cmac.readW_frame16 hf (d := 0) (by decide) hd
    rw [BitVec.add_zero] at this
    rw [this, h0]
  · have := Proof.Cmac.readW_frame16 hf (d := 8) (by decide) hd
    rw [Offset.add_add] at this
    rw [this, h8]

theorem toNat_append_lo (hi lo : BitVec 64) : (hi ++ lo : BitVec 128).toNat % 2 ^ 64 = lo.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]
  have := lo.isLt
  omega_arith

/-- The bytes `q` at `W + 64`: the counter `q + 0`. -/
theorem cnt_init {m : Mem} {W : Addr} {q : List Byte} (h : bytesAt m (W + BitVec.ofNat 64 cntO) 16 = q) :
    CntAt m W q 0 := by
  refine ⟨byteRev64 (m.readW (W + BitVec.ofNat 64 cntO) 64), byteRev64 (m.readW (W + BitVec.ofNat 64 (cntO + 8)) 64),
    (rev64_rev64 _).symm, (rev64_rev64 _).symm, ?_, ?_⟩
  · have e : Spec.Gcm.toBytes (byteRev64 (m.readW (W + BitVec.ofNat 64 cntO) 64) ++
        byteRev64 (m.readW (W + BitVec.ofNat 64 (cntO + 8)) 64)) = q := by
      rw [← le8_rev, rev64_rev64, rev64_rev64, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Offset.add_add,
        ← Proof.Cmac.bytesAt_split, h]
    rw [← e, Proof.Cmac.ofBytes_toBytes]
    exact (BitVec.add_zero _).symm
  · have e : Spec.Gcm.toBytes (byteRev64 (m.readW (W + BitVec.ofNat 64 cntO) 64) ++
        byteRev64 (m.readW (W + BitVec.ofNat 64 (cntO + 8)) 64)) = q := by
      rw [← le8_rev, rev64_rev64, rev64_rev64, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Offset.add_add,
        ← Proof.Cmac.bytesAt_split, h]
    obtain ha := congrArg Spec.Gcm.ofBytes e
    rw [Proof.Cmac.ofBytes_toBytes, beNat_eq] at ha
    rw [← toNat_append_lo (byteRev64 (m.readW (W + BitVec.ofNat 64 cntO) 64)), ha, BitVec.toNat_ofNat,
      Nat.mod_mod_of_dvd _ (by decide), Nat.add_zero]

/-- Adding `k` to the counter's second doubleword, without a carry. -/
theorem cnt_add {m : Mem} {W : Addr} {q : List Byte} {i k : Nat} {hi lo : BitVec 64}
    (h0 : m.readW (W + BitVec.ofNat 64 cntO) 64 = byteRev64 hi)
    (happ : (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes q + BitVec.ofNat 128 i)
    (hlo : lo.toNat = Spec.Siv.beNat q % 2 ^ 64 + i) (hk : Spec.Siv.beNat q % 2 ^ 64 + i + k < 2 ^ 64) :
    CntAt (m.writeW (W + BitVec.ofNat 64 (cntO + 8)) (byteRev64 (lo + BitVec.ofNat 64 k))) W q (i + k) := by
  refine ⟨hi, lo + BitVec.ofNat 64 k, ?_, Mem.readW_writeW_self64 _ _ _, ?_, ?_⟩
  · rw [Mem.readW_writeW_sep (Offset.sep W (d := cntO) (n := 8) (e := cntO + 8) (k := 8) (by decide) (by decide)
      (by decide)) (by decide), h0]
  · rw [add_lo hi lo (by omega_arith), happ, BitVec.add_assoc, BitVec.ofNat_add]
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_arith), hlo,
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith

/-! ## Copies within `W` -/

/-- The block at `W + a` copied to `W + b`, a doubleword at a time. -/
abbrev copyMem (m : Mem) (W : Addr) (a b : Nat) : Mem :=
  (m.writeW (W + BitVec.ofNat 64 b) (m.readW (W + BitVec.ofNat 64 a) 64)).writeW
    (W + BitVec.ofNat 64 b + BitVec.ofNat 64 8) (m.readW (W + BitVec.ofNat 64 a + BitVec.ofNat 64 8) 64)

theorem copyMem_frame (m : Mem) (W : Addr) (a b : Nat) : Frame [⟨W + BitVec.ofNat 64 b, 16⟩] m (copyMem m W a b) :=
  Proof.Cmac.frame_store2 _ _ _

theorem copyMem_bytes (m : Mem) (W : Addr) (a b : Nat) :
    bytesAt (copyMem m W a b) (W + BitVec.ofNat 64 b) 16 = bytesAt m (W + BitVec.ofNat 64 a) 16 := by
  rw [Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]

theorem copy16_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {a b : Nat} (ha : a + 16 ≤ 384)
    (hb : b + 16 ≤ 384) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hab : a + 16 ≤ b ∨ b + 16 ≤ a) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ s', PK s s' → (∀ r, r ≠ .t0 → s'.gpr r = s.gpr r) → s'.mem = copyMem s.mem c.W a b →
      WP isa (.block is) s' Q) :
    WP isa (.block (copy16 a b ++ is)) s Q := by
  simp only [copy16, List.cons_append, List.nil_append]
  refine wp_ld (a := c.W + BitVec.ofNat 64 a) (by omega_arith) (by rw [E.s1]) (L.alW ha8 (by omega_arith))
    (E.perm.wR (by omega_arith)) fun s₁ u₁ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 b) (by omega_arith) (by rw [u₁.other _ (by decide), E.s1])
    (L.alW hb8 (by omega_arith)) (by rw [u₁.wr]; exact E.perm.wW (by omega_arith)) fun s₂ u₂ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 a + BitVec.ofNat 64 8) (by omega_arith)
    (by rw [u₂.gpr, u₁.other _ (by decide), E.s1, Offset.add_add])
    (by rw [Offset.add_add]; exact L.alW (by omega_arith) (by omega_arith))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, Offset.add_add]; exact E.perm.wR (by omega_arith)) fun s₃ u₃ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 b + BitVec.ofNat 64 8) (by omega_arith)
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s1, Offset.add_add])
    (by rw [Offset.add_add]; exact L.alW (by omega_arith) (by omega_arith))
    (by rw [u₃.wr, u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by omega_arith)) fun s₄ u₄ => ?_
  refine k s₄ ((PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofUpd u₃).trans (PK.ofMupd u₄))))
    (fun r hr => by rw [u₄.gpr, u₃.other _ hr, u₂.gpr, u₁.other _ hr]) ?_
  obtain sep : Mem.Sep (c.W + BitVec.ofNat 64 a + BitVec.ofNat 64 8) (64 / 8) (c.W + BitVec.ofNat 64 b) (64 / 8) := by
    rw [Offset.add_add]
    exact Offset.sep c.W (d := a + 8) (n := 8) (e := b) (k := 8) (by omega_arith) (by omega_arith) (by omega_arith)
  rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, Mem.readW_writeW_sep sep (by decide)]

/-! ## The counter `Q` -/

theorem qbits_eq : BitVec.ofNat 64 128 ||| BitVec.ofNat 64 128 <<< 32 = qbits := by decide

/-- `counter`: the counter `Q` of the IV at `W + src` at `W + 64`. -/
theorem counter_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {src : Nat} (hsrc : src + 16 ≤ cntO)
    (hsrc8 : src % 8 = 0) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', PK s s' → Frame [⟨c.W + BitVec.ofNat 64 cntO, 16⟩] s.mem s'.mem →
      bytesAt s'.mem (c.W + BitVec.ofNat 64 cntO) 16 =
        Spec.Siv.counter (bytesAt s.mem (c.W + BitVec.ofNat 64 src) 16) → WP isa (.block is) s' Q) :
    WP isa (.block (counter src ++ is)) s Q := by
  simp only [cntO] at hsrc
  simp only [counter, List.cons_append, List.nil_append]
  refine wp_ld (a := c.W + BitVec.ofNat 64 src) (by omega_arith) (by rw [E.s1]) (L.alW hsrc8 (by omega_arith))
    (E.perm.wR (by omega_arith)) fun s₁ u₁ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 cntO) (by decide) (by rw [u₁.other _ (by decide), E.s1])
    (L.alW (by decide) (by decide)) (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun s₂ u₂ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 (src + 8)) (by omega_arith)
    (by rw [u₂.gpr, u₁.other _ (by decide), E.s1]) (L.alW (by omega_arith) (by omega_arith))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by omega_arith)) fun s₃ u₃ => ?_
  refine wp_li (imm := 128) (by decide) fun s₄ u₄ => wp_sll (by decide) fun s₅ u₅ => wp_or fun s₆ u₆ =>
    wp_or fun s₇ u₇ => wp_xor fun s₈ u₈ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 (cntO + 8)) (by decide)
    (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr,
      u₁.other, E.s1]) (L.alW (by decide) (by decide))
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by decide))
    fun s₉ u₉ => ?_
  obtain pk : PK s s₉ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans (PK.ofMupd u₉))))))))
  obtain t1₆ : s₆.gpr .t1 = qbits := by
    rw [u₆.gpr, u₅.other _ (by decide), u₅.gpr, u₄.gpr]
    exact qbits_eq
  obtain t1₇ : s₇.gpr .t1 = qbits := by rw [u₇.other _ (by decide), t1₆]
  obtain t0 : s₈.gpr .t0 = s.mem.readW (c.W + BitVec.ofNat 64 (src + 8)) 64 &&& qmask := by
    rw [u₈.gpr, t1₇, u₇.gpr, t1₆, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      orr_eor, u₂.mem, u₁.mem, Mem.readW_writeW_sep (Offset.sep c.W (d := src + 8) (n := 8) (e := cntO) (k := 8)
        (by (try simp only [cntO]); omega_arith) (by (try simp only [cntO]); omega_arith) (by decide)) (by decide)]
  obtain m₉ : s₉.mem = (s.mem.writeW (c.W + BitVec.ofNat 64 cntO) (s.mem.readW (c.W + BitVec.ofNat 64 src) 64)).writeW
      (c.W + BitVec.ofNat 64 (cntO + 8)) (s.mem.readW (c.W + BitVec.ofNat 64 (src + 8)) 64 &&& qmask) := by
    rw [u₉.mem, t0, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]
  refine k s₉ pk (by rw [m₉, ← Offset.add_add c.W cntO 8]; exact Proof.Cmac.frame_store2 _ _ _) ?_
  rw [m₉, ← Offset.add_add c.W cntO 8, Proof.Cmac.bytesAt_store2, counter_words, Proof.Cmac.le8_readW,
    Proof.Cmac.le8_readW, ← Offset.add_add c.W src 8, ← Proof.Cmac.bytesAt_split]

/-! ## The whole blocks, by one call -/

/-- The whole blocks `ctrWhole` does, of `left` bytes. -/
abbrev wholeOf (left : Nat) : Nat := left / 16 % 2 ^ 31

theorem count_eq {left : Nat} (hl : left < 2 ^ 64) :
    BitVec.ofNat 64 left >>> 4 <<< 33 >>> 33 = BitVec.ofNat 64 (wholeOf left) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, show (2 : Nat) ^ 64 = 2 ^ 31 * 2 ^ 33 from rfl, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (by decide), Nat.mod_eq_of_lt (a := left / 2 ^ 4 % 2 ^ 31) (by omega_arith)]

theorem wholeOf_le (left : Nat) : 16 * wholeOf left ≤ left := by
  show 16 * (left / 16 % 2 ^ 31) ≤ left; omega_arith

theorem wholeOf_lt (left : Nat) : wholeOf left < 2 ^ 31 := Nat.mod_lt _ (by decide)

theorem wholeCount_wp {s : State} {left : Nat} (d : Reg) (h7 : s.gpr .s7 = BitVec.ofNat 64 left)
    (hl : left < 2 ^ 64) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 (wholeOf left)) → WP isa (.block is) s' Q) :
    WP isa (.block (wholeCount d ++ is)) s Q := by
  simp only [wholeCount, List.cons_append, List.nil_append]
  refine wp_srl (by decide) fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => wp_srl (by decide) fun s₃ u₃ => k s₃ ?_
  obtain v : s₃.gpr d = BitVec.ofNat 64 (wholeOf left) := by rw [u₃.gpr, u₂.gpr, u₁.gpr, h7, count_eq hl]
  exact ⟨v, fun r hr => by rw [u₃.other _ hr, u₂.other _ hr, u₁.other _ hr], by rw [u₃.mem, u₂.mem, u₁.mem],
    by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.sp, u₂.sp, u₁.sp]⟩

/-- The state at the start of block `i` of CTR from the state `s₀`: the
data is CTR's output on its first `16 i` bytes, from `s6` on are the rest
(`s7` bytes), and the counter is `Q + i`. -/
structure CInv (c : Cx) (s₀ : State) (q : List Byte) (i : Nat) (s : State) : Prop where
  pk : PK s₀ s
  s6 : s.gpr .s6 = c.D + BitVec.ofNat 64 (16 * i)
  s7 : s.gpr .s7 = BitVec.ofNat 64 (c.n - 16 * i)
  le : 16 * i ≤ c.n
  cnt : CntAt s.mem c.W q i
  data : bytesAt s.mem c.D c.n = ctrPart (Spec.Siv.ctxCiph s₀.mem c.C c.R) q (bytesAt s₀.mem c.D c.n) (16 * i)
  frame : Frame (ctrR c) s₀.mem s.mem

/-- `wholePre`: the counter block is `Q`, and the arguments of
`vg_aes_ctr32` over the first `wholeOf L` blocks of the data. -/
theorem wholePre_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) :
    WP isa (.block wholePre) s fun s' => PK s s' ∧ s'.gpr .s6 = c.D ∧ s'.gpr .s7 = BitVec.ofNat 64 c.n ∧
      s'.mem = copyMem s.mem c.W cntO cbO ∧
      CtrCall s' (c.C + BitVec.ofNat 64 272) (c.W + BitVec.ofNat 64 cbO) c.D (c.W + BitVec.ofNat 64 384) c.R
        (wholeOf c.n) := by
  have hn := L.n_lt
  obtain hk := wholeOf_le c.n
  unfold wholePre ctrArgs
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => ?_
  obtain pk₂ : PK s s₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  obtain E₂ := E.of_pk pk₂
  refine copy16_wp L E₂ (by decide) (by decide) (by decide) (by decide) (by decide) fun s₃ pk₃ g₃ m₃ => ?_
  obtain s7₃ : s₃.gpr .s7 = BitVec.ofNat 64 c.n := by rw [g₃ _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s10]
  refine wholeCount_wp .a4 s7₃ hn fun s₄ u₄ => ?_
  refine wp_addi (imm := 272) (by decide) fun s₅ u₅ => wp_mv fun s₆ u₆ => wp_addi (by decide) fun s₇ u₇ =>
    wp_addi (by decide) fun s₈ u₈ => wp_mv fun s₉ u₉ => WP.block_nil ?_
  obtain pk₉ : PK s₃ s₉ := (PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans
    ((PK.ofUpd u₈).trans (PK.ofUpd u₉)))))
  obtain E₉ := E.of_pk (pk₂.trans (pk₃.trans pk₉))
  obtain s6₉ : s₉.gpr .s6 = c.D := by
    simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, g₃, u₂.other, u₁.gpr,
      E.s9]
  refine ⟨pk₂.trans (pk₃.trans pk₉), s6₉, by
      simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, s7₃],
    by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem], ?_⟩
  exact cargs L E₉ (o := cbO) (by decide) ((L.bufD E₉.perm).take hk).src
    ((L.d_w' (d := cbO) (k := 16) (by decide)).sub_left (Region.sub_prefix hk))
    ((L.c_d.sub_left (Lay.cSub (d := 272) (n := 240) (by decide))).sub_right (Region.sub_prefix hk))
    (covers_prefix E₉.perm.d hk)
    (by simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, g₃, u₂.other,
      u₁.other, E.s2])
    (by simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, g₃, u₂.other,
      u₁.other, E.s3])
    (by simp (disch := decide) only [u₉.other, u₈.other, u₇.gpr, u₆.other, u₅.other, u₄.other, g₃, u₂.other,
      u₁.other, E.s1])
    (by rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), g₃ _ (by decide), u₂.other _ (by decide), u₁.gpr, E.s9])
    (by simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr])
    (by simp (disch := decide) only [u₉.other, u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, g₃, u₂.other,
      u₁.other, E.s1]; rfl)

/-! ## Adding to the counter -/

theorem cnt_frame (W : Addr) (m : Mem) (v : BitVec 64) :
    Frame [⟨W + BitVec.ofNat 64 cntO, 16⟩] m (m.writeW (W + BitVec.ofNat 64 (cntO + 8)) v) := by
  refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
  rw [← Offset.add_add]
  exact Offset.contains_base _ (d := 8) (n := 64 / 8) (k := 16) (by decide) (by decide)

/-- The counter's second doubleword loaded big-endian, a byte at a time, `t0`
added, and stored back the same way. -/
theorem bump_wp {c : Cx} {s : State} (E : Env c s) {q : List Byte} {i k : Nat} (hc : CntAt s.mem c.W q i)
    (hb : Spec.Siv.beNat q % 2 ^ 64 + i + k < 2 ^ 64) (h0 : s.gpr .t0 = BitVec.ofNat 64 k) {is : List Instr}
    {Q : State → Prop}
    (cont : ∀ s', PK s s' → (∀ r, r ≠ .t1 → r ≠ .t2 → s'.gpr r = s.gpr r) →
      Frame [⟨c.W + BitVec.ofNat 64 cntO, 16⟩] s.mem s'.mem → CntAt s'.mem c.W q (i + k) → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.Words.RISCV64.loadBE64 .t1 .t2 .s1 (cntO + 8) ++
      .add .t1 .t1 .t0 :: (Impl.Words.RISCV64.storeBE 8 .t1 .t2 .s1 (cntO + 8) ++ is))) s Q := by
  obtain ⟨hi, lo, h0', h8, happ, hlo⟩ := hc
  refine BE64.wp_loadBE64 (a := c.W + BitVec.ofNat 64 (cntO + 8)) (by decide) (by decide) (by decide) (by decide)
    (by rw [E.s1]) (E.perm.wR (by decide)) fun s₁ s₂ u₁ u₂ => ?_
  refine wp_add fun s₃ u₃ => ?_
  refine BE64.wp_storeBE8 (a := c.W + BitVec.ofNat 64 (cntO + 8)) (by decide) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), E.s1])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by decide)) fun s₄ s₅ u₄ u₅ => ?_
  obtain t1 : s₃.gpr .t1 = lo + BitVec.ofNat 64 k := by
    rw [u₃.gpr, u₂.gpr, h8, rev64_rev64, u₂.other _ (by decide), u₁.other _ (by decide), h0]
  obtain m₅ : s₅.mem = s.mem.writeW (c.W + BitVec.ofNat 64 (cntO + 8)) (byteRev64 (lo + BitVec.ofNat 64 k)) := by
    rw [u₅.mem, u₄.mem, t1, u₃.mem, u₂.mem, u₁.mem]
  refine cont s₅ ((PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofMupd u₄).trans
    (PK.ofUpd u₅))))) (fun r h1 h2 => by rw [u₅.other _ h2, u₄.gpr, u₃.other _ h1, u₂.other _ h1, u₁.other _ h2])
    (by rw [m₅]; exact cnt_frame _ _ _) (by rw [m₅]; exact cnt_add h0' happ hlo hb)

/-- The counter's second doubleword loaded big-endian, incremented, and stored
back. -/
theorem bump1_wp {c : Cx} {s : State} (E : Env c s) {q : List Byte} {i : Nat} (hc : CntAt s.mem c.W q i)
    (hb : Spec.Siv.beNat q % 2 ^ 64 + i + 1 < 2 ^ 64) {is : List Instr} {Q : State → Prop}
    (cont : ∀ s', PK s s' → (∀ r, r ≠ .t1 → r ≠ .t2 → s'.gpr r = s.gpr r) →
      Frame [⟨c.W + BitVec.ofNat 64 cntO, 16⟩] s.mem s'.mem → CntAt s'.mem c.W q (i + 1) → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.Words.RISCV64.loadBE64 .t1 .t2 .s1 (cntO + 8) ++
      .addi .t1 .t1 1 :: (Impl.Words.RISCV64.storeBE 8 .t1 .t2 .s1 (cntO + 8) ++ is))) s Q := by
  obtain ⟨hi, lo, h0', h8, happ, hlo⟩ := hc
  refine BE64.wp_loadBE64 (a := c.W + BitVec.ofNat 64 (cntO + 8)) (by decide) (by decide) (by decide) (by decide)
    (by rw [E.s1]) (E.perm.wR (by decide)) fun s₁ s₂ u₁ u₂ => ?_
  refine wp_addi (imm := 1) (by decide) fun s₃ u₃ => ?_
  refine BE64.wp_storeBE8 (a := c.W + BitVec.ofNat 64 (cntO + 8)) (by decide) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), E.s1])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by decide)) fun s₄ s₅ u₄ u₅ => ?_
  obtain t1 : s₃.gpr .t1 = lo + BitVec.ofNat 64 1 := by
    rw [u₃.gpr, u₂.gpr, h8, rev64_rev64]
  obtain m₅ : s₅.mem = s.mem.writeW (c.W + BitVec.ofNat 64 (cntO + 8)) (byteRev64 (lo + BitVec.ofNat 64 1)) := by
    rw [u₅.mem, u₄.mem, t1, u₃.mem, u₂.mem, u₁.mem]
  refine cont s₅ ((PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofMupd u₄).trans
    (PK.ofUpd u₅))))) (fun r h1 h2 => by rw [u₅.other _ h2, u₄.gpr, u₃.other _ h1, u₂.other _ h1, u₁.other _ h2])
    (by rw [m₅]; exact cnt_frame _ _ _) (by rw [m₅]; exact cnt_add h0' happ hlo hb)

/-! ## `ctrWhole` -/

theorem ctrPart_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.schedCiph m' (C + BitVec.ofNat 64 272) R = Spec.Siv.ctxCiph m C R := by
  unfold Spec.Siv.ctxCiph Spec.Siv.schedCiph
  rw [Proof.Cmac.bytesAt_frame hf (p := C + BitVec.ofNat 64 272)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 272) (n := 16 * (R + 1)) (by omega_arith))) (by omega_arith)]
  rfl

/-- `ctrWhole`: the first `wholeOf L` blocks of the data by one call of
`vg_aes_ctr32` from `Q`, whose last 32 bits are below `2³¹`, and the counter
`Q + wholeOf L`. -/
theorem ctrWhole_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {q : List Byte} (hq : q.length = 16)
    (hlow : Spec.Siv.beNat q % 2 ^ 32 < 2 ^ 31) (hlow64 : Spec.Siv.beNat q % 2 ^ 64 < 2 ^ 63)
    (hc : CntAt s.mem c.W q 0) :
    WP isa ctrWhole s (CInv c s q (wholeOf c.n)) := by
  have hn := L.n_lt
  obtain hk := wholeOf_le c.n
  obtain hk31 := wholeOf_lt c.n
  have hRb := L.rb
  have hdw := L.dw
  unfold ctrWhole
  refine WP.seq (WP.mono (wholePre_wp L E) fun s₁ ⟨pk₁, s6₁, s7₁, m₁, C₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.AesCtr.RISCV64.ctr_call C₁) fun s₂ h₂ => ?_)
  obtain pk₂ : PK s₁ s₂ := PK.ofSaved h₂.rd h₂.wr h₂.sp h₂.saved
  obtain E₂ := E.of_pk (pk₁.trans pk₂)
  obtain f₁ : Frame [⟨c.W + BitVec.ofNat 64 cbO, 16⟩] s.mem s₁.mem := by rw [m₁]; exact copyMem_frame _ _ _ _
  have f₂ := h₂.frame
  obtain hc₂ : CntAt s₂.mem c.W q 0 := by
    refine (hc.frame f₁ fun r hr => ?_).frame f₂ fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.d_w' (d := cntO) (k := 16) (by decide)).symm.sub_right (Region.sub_prefix hk)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  obtain s7₂ : s₂.gpr .s7 = BitVec.ofNat 64 c.n := by rw [h₂.saved _ (by decide), s7₁]
  unfold wholePost
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wholeCount_wp .t0 s7₂ hn fun s₃ u₃ => ?_
  obtain E₃ := E₂.of_pk (PK.ofUpd u₃)
  refine bump_wp E₃ (by rw [u₃.mem]; exact hc₂) (by omega_arith) u₃.gpr fun s₄ pk₄ g₄ f₄ hc₄ => ?_
  refine wp_sll (by decide) fun s₅ u₅ => wp_add fun s₆ u₆ => wp_sub fun s₇ u₇ => WP.block_nil ?_
  obtain pk₇ : PK s s₇ := pk₁.trans (pk₂.trans ((PK.ofUpd u₃).trans (pk₄.trans ((PK.ofUpd u₅).trans
    ((PK.ofUpd u₆).trans (PK.ofUpd u₇))))))
  obtain m₇ : s₇.mem = s₄.mem := by rw [u₇.mem, u₆.mem, u₅.mem]
  obtain t0₅ : s₅.gpr .t0 = BitVec.ofNat 64 (16 * wholeOf c.n) := by
    rw [u₅.gpr, g₄ _ (by decide) (by decide), u₃.gpr, ofNat_shl4 (by omega_arith)]
  -- The data: the first `16 k` bytes are CTR's output, the rest as it was.
  obtain dC : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 cbO, 16⟩ : Region)], (⟨c.C, 512⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.c0_w' (by decide) (by decide)
  have dP {a l : Nat} (ha : a + l ≤ c.n) : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 cbO, 16⟩ : Region)],
      (⟨c.D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (L.d_w' (d := cbO) (k := 16) (by decide)).sub_left (Offset.sub_base _ ha)
  obtain hcb : Spec.Gcm.blockAt s₁.mem (c.W + BitVec.ofNat 64 cbO) = Spec.Gcm.ofBytes q := by
    rw [Spec.Gcm.blockAt, m₁, copyMem_bytes, hc.bytes, Nat.add_zero, ofBytes_be128, ← beNat_eq]
  obtain hd₂ := ctr32_ctrPart (m := s₁.mem) (m' := s₂.mem) (K := c.C + BitVec.ofNat 64 272)
    (C := c.W + BitVec.ofNat 64 cbO) (D := c.D) (R := c.R) (q := q) (k := wholeOf c.n)
    (fun i hi => by rw [hcb]; exact repeat_inc32 hq (k := wholeOf c.n) (by omega_arith) i hi) h₂.out
  rw [ctrPart_frame f₁ dC hRb] at hd₂
  obtain pd₁ : bytesAt s₁.mem c.D (16 * wholeOf c.n) = bytesAt s.mem c.D (16 * wholeOf c.n) := by
    have := Proof.Cmac.bytesAt_frame f₁ (dP (a := 0) (l := 16 * wholeOf c.n) (by omega_arith)) (by omega_arith)
    rwa [BitVec.add_zero] at this
  rw [pd₁] at hd₂
  obtain rest : bytesAt s₂.mem (c.D + BitVec.ofNat 64 (16 * wholeOf c.n)) (c.n - 16 * wholeOf c.n) =
      bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * wholeOf c.n)) (c.n - 16 * wholeOf c.n) := by
    obtain hsub : Region.Sub ⟨c.D + BitVec.ofNat 64 (16 * wholeOf c.n), c.n - 16 * wholeOf c.n⟩ ⟨c.D, c.n⟩ :=
      Offset.sub_base _ (by omega_arith)
    rw [Proof.Cmac.bytesAt_frame f₂ (fun r hr => ?_) (by omega_arith),
      Proof.Cmac.bytesAt_frame f₁ (dP (by omega_arith)) (by omega_arith)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (L.d_w' (d := cbO) (k := 16) (by decide)).sub_left hsub
    · exact (Offset.base_disjoint c.D (e := 16 * wholeOf c.n) (n := c.n - 16 * wholeOf c.n)
        (k := 16 * wholeOf c.n) (by omega_arith) (by omega_arith)).symm
    · exact (L.d_w' (d := 384) (k := 2048) (by decide)).sub_left hsub
  obtain e := Proof.Cmac.Stream.bytesAt_append s₂.mem c.D (16 * wholeOf c.n) (c.n - 16 * wholeOf c.n)
  rw [show 16 * wholeOf c.n + (c.n - 16 * wholeOf c.n) = c.n by omega_arith] at e
  obtain e₀ := Proof.Cmac.Stream.bytesAt_append s.mem c.D (16 * wholeOf c.n) (c.n - 16 * wholeOf c.n)
  rw [show 16 * wholeOf c.n + (c.n - 16 * wholeOf c.n) = c.n by omega_arith] at e₀
  obtain hpa := ctrPart_append (Spec.Siv.ctxCiph s.mem c.C c.R) q (bytesAt s.mem c.D (16 * wholeOf c.n))
    (bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * wholeOf c.n)) (c.n - 16 * wholeOf c.n))
  rw [Proof.Cmac.bytesAt_length] at hpa
  obtain d₄ : bytesAt s₄.mem c.D c.n = bytesAt s₂.mem c.D c.n := by
    rw [Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by omega_arith), u₃.mem]
  -- The frame.
  obtain s96 : Region.Sub ⟨c.W + BitVec.ofNat 64 cbO, 16⟩ ⟨c.W + BitVec.ofNat 64 64, 48⟩ :=
    Offset.sub _ (by decide) (by decide)
  refine ⟨pk₇, ?_, ?_, hk, by rw [m₇]; simpa using hc₄, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.gpr, t0₅, u₅.other _ (by decide), g₄ _ (by decide) (by decide),
      u₃.other _ (by decide), h₂.saved _ (by decide), s6₁]
  · simp (disch := decide) only [u₇.gpr, u₆.other, t0₅, u₅.other, g₄, u₃.other, s7₂]
    exact ofNat_sub' hk hn
  · rw [m₇, d₄, e, hd₂, rest, e₀, hpa]
  · rw [m₇]
    refine ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)).trans
      ((u₃.mem ▸ f₄).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, s96⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, s96⟩
      · exact ⟨⟨c.D, c.n⟩, by simp, Region.sub_prefix hk⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W + BitVec.ofNat 64 64, 48⟩, by simp, Region.sub_prefix (by decide)⟩

end VG.Proof.AesSiv.RISCV64

end

end

/-!
# AES-SIV on RISC-V: CTR a block at a time, and the whole of CTR

Untrusted: everything here is checked by Lean. After `ctrWhole`, the rest of
the data (its last `L mod 16` bytes, and more only if `L ≥ 2³⁵`) is done a
block at a time: the counter `Q + i` is copied to the counter block at
`W + 96`, `vg_aes_ctr32` writes its cipher over the zeroed keystream block at
`W + 80` (`ctrHead_wp`), its first `min(16, left)` bytes are XORed into the
data, a byte at a time (AES-CCM's `xorBytes`), the counter is incremented
and the length left reduced (`ctrTail_wp`). After block `i` the data is
CTR's output on its first `16 i + min(16, left)` bytes (`ctrPart_step`);
`ctr_wp` is the whole: CTR's output from the counter `Q` of the IV. As on
PPC64LE (`Proof/AesSiv/PPC64LE/CtrLoop.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.Impl.AesSiv.RISCV64 VG.WriteBytes
open VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.AesCcm.RISCV64 (BytesPre xorBytes_wp xorL covers_off)
open VG.Proof.AesCtr.RISCV64 (CtrCall ctr_call)
open VG.Spec.Aes (bytesAt)

/-- Branching on whether a register holding `n` is zero. -/
theorem evalZ {s : State} {r : Reg} {n : Nat} (h : s.gpr r = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    isa.eval (.zero r) s = some (decide (n = 0)) :=
  Steps.eval_zero_ofNat s r hn h

/-- Looping while a register holding `n` is nonzero. -/
theorem evalNZ {s : State} {r : Reg} {n : Nat} (h : s.gpr r = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    isa.eval (.nonzero r) s = some (decide (n ≠ 0)) :=
  Steps.eval_nonzero_ofNat s r hn h

/-- The C context is clear of what CTR writes. -/
theorem ctrR_c {c : Cx} (L : Lay c) : ∀ r ∈ ctrR c, (⟨c.C, 512⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.c_d
  · exact L.c0_w' (by decide) (by decide)
  · exact L.c0_w' (by decide) (by decide)

/-- What the setup of a block, the call and the length leave. -/
structure CHead (c : Cx) (s₀ : State) (q : List Byte) (i : Nat) (s s' : State) : Prop where
  pk : PK s s'
  s6 : s'.gpr .s6 = s.gpr .s6
  s7 : s'.gpr .s7 = s.gpr .s7
  a0 : s'.gpr .a0 = c.W + BitVec.ofNat 64 ksO
  a1 : s'.gpr .a1 = s.gpr .s6
  a2 : s'.gpr .a2 = BitVec.ofNat 64 (min 16 (c.n - 16 * i))
  ks : bytesAt s'.mem (c.W + BitVec.ofNat 64 ksO) 16 = Siv.ksBlock (Spec.Siv.ctxCiph s₀.mem c.C c.R) q i
  frame : Frame [⟨c.W + BitVec.ofNat 64 ksO, 32⟩, ⟨c.W + BitVec.ofNat 64 384, 2048⟩] s.mem s'.mem

/-- `ctrPre`, the call and `ctrMin`: the keystream block of block `i`, and
the bytes of it to XOR. -/
theorem ctrHead_wp {c : Cx} (L : Lay c) {s₀ : State} {q : List Byte} {i : Nat} {s : State}
    (I : CInv c s₀ q i s) (hi : 16 * i < c.n) (E₀ : Env c s₀) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ s', CHead c s₀ q i s s' → WP isa rest s' Q) :
    WP isa (.seq (.block ctrPre) (.seq Impl.AesCtr.RISCV64.ctrCall (.seq ctrMin rest))) s Q := by
  have hn := L.n_lt
  have hRb := L.rb
  obtain E := E₀.of_pk I.pk
  unfold ctrPre
  simp only [List.append_assoc]
  refine WP.seq (zero16_wp L E (d := ksO) (by decide) (by decide) fun s₁ pk₁ g₁ m₁ => ?_)
  obtain E₁ := E.of_pk pk₁
  refine copy16_wp L E₁ (by decide) (by decide) (by decide) (by decide) (by decide) fun s₂ pk₂ g₂ m₂ => ?_
  unfold ctrArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (imm := 272) (by decide) fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ =>
    wp_addi (by decide) fun s₆ u₆ => wp_addi (by decide) fun s₇ u₇ => wp_li (imm := 1) (by decide) fun s₈ u₈ =>
    WP.block_nil ?_
  obtain pk₈ : PK s₂ s₈ := (PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans
    ((PK.ofUpd u₇).trans (PK.ofUpd u₈)))))
  obtain E₈ := E.of_pk (pk₁.trans (pk₂.trans pk₈))
  obtain m₈ : s₈.mem = s₂.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  obtain C : CtrCall s₈ (c.C + BitVec.ofNat 64 272) (c.W + BitVec.ofNat 64 cbO) (c.W + BitVec.ofNat 64 ksO)
      (c.W + BitVec.ofNat 64 384) c.R 1 :=
    cargsW L E₈ (o := cbO) (by decide) (d := ksO) (by decide) (.inr (by decide))
      (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂, g₁, E.s2])
      (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂, g₁, E.s3])
      (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g₂, g₁, E.s1])
      (by simp (disch := decide) only [u₈.other, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, g₂, g₁, E.s1])
      (by simp (disch := decide) only [u₈.gpr])
      (by simp (disch := decide) only [u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, g₂, g₁, E.s1]; rfl)
  refine WP.seq (WP.mono (ctr_call C) fun s₉ h₉ => ?_)
  obtain pk₉ : PK s₈ s₉ := PK.ofSaved h₉.rd h₉.wr h₉.sp h₉.saved
  obtain E₉ := E₈.of_pk pk₉
  have keep9 (r : Reg) (hr : r ∈ preserved) : s₉.gpr r = s.gpr r := by
    obtain h0 : r ≠ .t0 := fun e => by subst e; exact absurd hr (by decide)
    obtain ha0 : r ≠ .a0 := fun e => by subst e; exact absurd hr (by decide)
    obtain ha1 : r ≠ .a1 := fun e => by subst e; exact absurd hr (by decide)
    obtain ha2 : r ≠ .a2 := fun e => by subst e; exact absurd hr (by decide)
    obtain ha3 : r ≠ .a3 := fun e => by subst e; exact absurd hr (by decide)
    obtain ha4 : r ≠ .a4 := fun e => by subst e; exact absurd hr (by decide)
    obtain ha5 : r ≠ .a5 := fun e => by subst e; exact absurd hr (by decide)
    rw [h₉.saved r hr, u₈.other _ ha4, u₇.other _ ha3, u₆.other _ ha5, u₅.other _ ha2, u₄.other _ ha1,
      u₃.other _ ha0, g₂ _ h0, g₁ _ h0]
  -- `ctrMin`.
  obtain hl : c.n - 16 * i < 2 ^ 64 := by omega_arith
  obtain s7₉ : s₉.gpr .s7 = BitVec.ofNat 64 (c.n - 16 * i) := by rw [keep9 _ (by decide), I.s7]
  -- The keystream block.
  obtain f₁ : Frame [⟨c.W + BitVec.ofNat 64 ksO, 16⟩] s.mem s₁.mem := by
    rw [m₁]; exact Proof.Cmac.frame_store2 _ _ _
  obtain f₂ : Frame [⟨c.W + BitVec.ofNat 64 cbO, 16⟩] s₁.mem s₂.mem := by rw [m₂]; exact copyMem_frame _ _ _ _
  obtain s80 : Region.Sub ⟨c.W + BitVec.ofNat 64 ksO, 16⟩ ⟨c.W + BitVec.ofNat 64 ksO, 32⟩ := Region.sub_prefix (by decide)
  obtain s96 : Region.Sub ⟨c.W + BitVec.ofNat 64 cbO, 16⟩ ⟨c.W + BitVec.ofNat 64 ksO, 32⟩ :=
    Offset.sub _ (by decide) (by decide)
  obtain f₀₈ : Frame (ctrR c) s₀.mem s₈.mem := by
    rw [m₈]
    refine I.frame.trans ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W + BitVec.ofNat 64 64, 48⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W + BitVec.ofNat 64 64, 48⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  obtain hz : bytesAt s₂.mem (c.W + BitVec.ofNat 64 ksO) 16 = Spec.Cmac.zeros 16 := by
    rw [m₂, Proof.Cmac.bytesAt_frame (copyMem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), m₁, Proof.Cmac.zero2_bytes]
  obtain hcb : bytesAt s₂.mem (c.W + BitVec.ofNat 64 cbO) 16 = Spec.Siv.be128 (Spec.Siv.beNat q + i) := by
    rw [m₂, copyMem_bytes, m₁, Proof.Cmac.zero2, Proof.Cmac.bytesAt_frame (Proof.Cmac.frame_store2 _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), I.cnt.bytes]
  obtain hks : bytesAt s₉.mem (c.W + BitVec.ofNat 64 ksO) 16 = Siv.ksBlock (Spec.Siv.ctxCiph s₀.mem c.C c.R) q i := by
    obtain hx := Proof.AesCcm.ctr32_bytes h₉.out
    rw [Nat.mul_one, m₈, hz, Proof.AesSiv.xorKs_zeros, Spec.Gcm.blockAt, hcb,
      Proof.Cmac.aesWith_bytes _ _ (length_be128 _)] at hx
    rw [hx, ← m₈]
    have := ctrPart_frame f₀₈ (ctrR_c L) hRb
    rw [← this]
    rfl
  unfold ctrMin
  refine WP.seq (WP.seq (wp_srl (by decide) fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by decide)
    fun t₃ v₃ => wp_mv fun t₄ v₄ => WP.block_nil ?_))
  obtain pk₄ : PK s₉ t₄ := (PK.ofUpd v₁).trans ((PK.ofUpd v₂).trans ((PK.ofUpd v₃).trans (PK.ofUpd v₄)))
  obtain m₄ : t₄.mem = s₉.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  obtain t1 : t₄.gpr .t1 = BitVec.ofNat 64 ((c.n - 16 * i) / 16) := by
    rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, s7₉, ofNat_lsr4' hl]
  obtain fr : Frame [⟨c.W + BitVec.ofNat 64 ksO, 32⟩, ⟨c.W + BitVec.ofNat 64 384, 2048⟩] s.mem t₄.mem := by
    obtain f₁₈ : Frame [⟨c.W + BitVec.ofNat 64 ksO, 32⟩, ⟨c.W + BitVec.ofNat 64 384, 2048⟩] s₁.mem s₈.mem := by
      rw [m₈]
      refine f₂.sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, s96⟩
    rw [m₄]
    refine (f₁.sub fun r hr => ?_).trans (f₁₈.trans (h₉.frame.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, s80⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, s96⟩
      · exact ⟨_, by simp, s80⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  obtain base : PK s t₄ ∧ t₄.gpr .s6 = s.gpr .s6 ∧ t₄.gpr .s7 = s.gpr .s7 ∧
      t₄.gpr .a0 = c.W + BitVec.ofNat 64 ksO ∧ t₄.gpr .a1 = s.gpr .s6 := by
    refine ⟨pk₁.trans (pk₂.trans (pk₈.trans (pk₉.trans pk₄))),
      by simp (disch := decide) only [v₄.other, v₃.other, v₂.other, v₁.other, keep9],
      by simp (disch := decide) only [v₄.other, v₃.other, v₂.other, v₁.other, keep9],
      by simp (disch := decide) only [v₄.other, v₃.gpr, v₂.other, v₁.other, E₉.s1],
      by simp (disch := decide) only [v₄.gpr, v₃.other, v₂.other, v₁.other, keep9]⟩
  refine WP.ite (decide ((c.n - 16 * i) / 16 = 0)) (evalZ t1 (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : (c.n - 16 * i) / 16 = 0 := by simpa using ht
    refine WP.block_nil (k _ ⟨base.1, base.2.1, base.2.2.1, base.2.2.2.1, base.2.2.2.2, ?_, by rw [m₄, hks], fr⟩)
    rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), s7₉,
      Nat.min_eq_right (by omega_arith)]
  · have h0 : (c.n - 16 * i) / 16 ≠ 0 := by simpa using hf
    refine wp_li (imm := 16) (by decide) fun t₅ v₅ => WP.block_nil (k _ ⟨base.1.trans (PK.ofUpd v₅),
      by rw [v₅.other _ (by decide), base.2.1], by rw [v₅.other _ (by decide), base.2.2.1],
      by rw [v₅.other _ (by decide), base.2.2.2.1], by rw [v₅.other _ (by decide), base.2.2.2.2],
      by rw [v₅.gpr, Nat.min_eq_left (by omega_arith)], by rw [v₅.mem, m₄, hks], by rw [v₅.mem]; exact fr⟩)

/-- What a block of CTR leaves: block `i + 1`'s registers and counter, and
the data CTR's output on its first `16 i + min(16, left)` bytes. -/
structure Stepped (c : Cx) (s₀ : State) (q : List Byte) (i : Nat) (s s' : State) : Prop where
  pk : PK s s'
  s6 : s'.gpr .s6 = c.D + BitVec.ofNat 64 (16 * (i + 1))
  s7 : s'.gpr .s7 = BitVec.ofNat 64 (c.n - 16 * i - min 16 (c.n - 16 * i))
  cnt : CntAt s'.mem c.W q (i + 1)
  data : bytesAt s'.mem c.D c.n =
    ctrPart (Spec.Siv.ctxCiph s₀.mem c.C c.R) q (bytesAt s₀.mem c.D c.n) (16 * i + min 16 (c.n - 16 * i))
  frame : Frame (ctrR c) s₀.mem s'.mem

/-- The XOR, the counter's increment and the length left. -/
theorem ctrTail_wp {c : Cx} (L : Lay c) {s₀ : State} {q : List Byte} {i : Nat} {s s₃ : State}
    (I : CInv c s₀ q i s) (hi : 16 * i < c.n) (E₀ : Env c s₀) (hlow64 : Spec.Siv.beNat q % 2 ^ 64 < 2 ^ 63)
    (H : CHead c s₀ q i s s₃) :
    WP isa (.seq Impl.AesCcm.RISCV64.xorBytes (.seq (.block ctrPost) ctrLeft)) s₃ (Stepped c s₀ q i s) := by
  have hn := L.n_lt
  obtain E := E₀.of_pk I.pk
  obtain E₃ := E.of_pk H.pk
  obtain hm1 : 0 < min 16 (c.n - 16 * i) := by omega_arith
  obtain hm16 : min 16 (c.n - 16 * i) ≤ 16 := Nat.min_le_left _ _
  obtain hmn : 16 * i + min 16 (c.n - 16 * i) ≤ c.n := by omega_arith
  generalize hmd : min 16 (c.n - 16 * i) = mn at hm1 hm16 hmn
  obtain hsub : Region.Sub ⟨c.D + BitVec.ofNat 64 (16 * i), mn⟩ ⟨c.D, c.n⟩ := Offset.sub_base _ hmn
  obtain xp : BytesPre s₃ (c.W + BitVec.ofNat 64 ksO) (c.D + BitVec.ofNat 64 (16 * i)) mn :=
    { a0 := H.a0
      a1 := by rw [H.a1, I.s6]
      a2 := by rw [H.a2, hmd]
      pos := hm1
      lt := by omega_arith
      rd := E₃.perm.wCR (by simp only [ksO]; omega_arith)
      wr := covers_off E₃.perm.d hmn hn
      disj := ((L.d_w' (d := ksO) (k := mn) (by simp only [ksO]; omega_arith)).sub_left hsub).symm }
  refine WP.seq (WP.mono (xorBytes_wp s₃ xp) fun s₄ ⟨m₄, _, k₄⟩ => ?_)
  obtain ck : ∀ r ∈ keepRegs, r ∉ Proof.AesCcm.RISCV64.copyRegs := by decide
  obtain pk₄ : PK s₃ s₄ := ⟨k₄.rd, k₄.wr, k₄.sp, fun r hr => k₄.gpr r (ck r hr)⟩
  obtain E₄ := E₃.of_pk pk₄
  obtain hxl : (xorL (bytesAt s₃.mem (c.D + BitVec.ofNat 64 (16 * i)) mn)
      (bytesAt s₃.mem (c.W + BitVec.ofNat 64 ksO) mn)).length = mn := by
    simp [xorL, Proof.Cmac.bytesAt_length]
  obtain fx : Frame [⟨c.D + BitVec.ofNat 64 (16 * i), mn⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  -- The counter, as it was.
  obtain dH : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 ksO, 32⟩ : Region), ⟨c.W + BitVec.ofNat 64 384, 2048⟩],
      (⟨c.W + BitVec.ofNat 64 cntO, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact L.w_w (.inl (by decide)) (by decide) (by decide)
  obtain cnt₄ : CntAt s₄.mem c.W q i := (I.cnt.frame H.frame dH).frame fx fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((L.d_w' (d := cntO) (k := 16) (by decide)).sub_left hsub).symm
  obtain hb : Spec.Siv.beNat q % 2 ^ 64 + i + 1 < 2 ^ 64 := by omega_arith
  unfold ctrPost
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq (bump1_wp E₄ cnt₄ hb fun s₅ pk₅ g₅ f₅ cnt₅ => ?_)
  refine wp_addi (imm := 16) (by decide) fun s₆ u₆ => wp_srl (by decide) fun s₇ u₇ => WP.block_nil ?_
  obtain s7₇ : s₇.gpr .s7 = BitVec.ofNat 64 (c.n - 16 * i) := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), g₅ _ (by decide) (by decide), k₄.gpr _ (by decide), H.s7,
      I.s7]
  obtain t0₇ : s₇.gpr .t0 = BitVec.ofNat 64 ((c.n - 16 * i) / 16) := by
    rw [u₇.gpr, u₆.other _ (by decide), g₅ _ (by decide) (by decide), k₄.gpr _ (by decide), H.s7, I.s7,
      ofNat_lsr4' (by omega_arith)]
  obtain s6₇ : s₇.gpr .s6 = c.D + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [u₇.other _ (by decide), u₆.gpr, g₅ _ (by decide) (by decide), k₄.gpr _ (by decide), H.s6, I.s6,
      Offset.add_add]
    congr 2
  obtain pk₇ : PK s s₇ := H.pk.trans (pk₄.trans (pk₅.trans ((PK.ofUpd u₆).trans (PK.ofUpd u₇))))
  obtain m₇ : s₇.mem = s₅.mem := by rw [u₇.mem, u₆.mem]
  -- The data.
  obtain hx : (bytesAt s₀.mem c.D c.n).length = c.n := Proof.Cmac.bytesAt_length _ _ _
  obtain dP : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 ksO, 32⟩ : Region), ⟨c.W + BitVec.ofNat 64 384, 2048⟩],
      (⟨c.D, c.n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact L.d_w' (by decide)
  obtain d₃ : bytesAt s₃.mem c.D (bytesAt s₀.mem c.D c.n).length =
      ctrPart (Spec.Siv.ctxCiph s₀.mem c.C c.R) q (bytesAt s₀.mem c.D c.n) (16 * i) := by
    rw [hx, Proof.Cmac.bytesAt_frame H.frame dP (by omega_arith), I.data]
  obtain st := ctrPart_step (Spec.Siv.ctxCiph s₀.mem c.C c.R) (fun y => Proof.Cmac.aesWith_length _ _ y) q
    (bytesAt s₀.mem c.D c.n) s₃.mem c.D (i := i) (n := mn) (by omega_arith) hm16 (by omega_arith) d₃
  obtain kt : bytesAt s₃.mem (c.W + BitVec.ofNat 64 ksO) mn =
      (Siv.ksBlock (Spec.Siv.ctxCiph s₀.mem c.C c.R) q i).take mn := by
    rw [← H.ks]
    have := take_bytesAt s₃.mem (c.W + BitVec.ofNat 64 ksO) (a := mn) (b := 16 - mn)
    rw [show mn + (16 - mn) = 16 by omega_arith] at this
    exact this.symm
  rw [hx, ← kt, show Spec.Cmac.xor (bytesAt s₃.mem (c.D + BitVec.ofNat 64 (16 * i)) mn)
      (bytesAt s₃.mem (c.W + BitVec.ofNat 64 ksO) mn) = xorL (bytesAt s₃.mem (c.D + BitVec.ofNat 64 (16 * i)) mn)
      (bytesAt s₃.mem (c.W + BitVec.ofNat 64 ksO) mn) from rfl, ← m₄] at st
  obtain data₇ : bytesAt s₇.mem c.D c.n =
      ctrPart (Spec.Siv.ctxCiph s₀.mem c.C c.R) q (bytesAt s₀.mem c.D c.n) (16 * i + mn) := by
    rw [m₇, Proof.Cmac.bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by omega_arith), st]
  -- The frame.
  obtain frame₇ : Frame (ctrR c) s₀.mem s₇.mem := by
    rw [m₇]
    refine ((I.frame.trans (H.frame.sub fun r hr => ?_)).trans (fx.sub fun r hr => ?_)).trans
      (f₅.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨c.W + BitVec.ofNat 64 64, 48⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, hsub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W + BitVec.ofNat 64 64, 48⟩, by simp, Region.sub_prefix (by decide)⟩
  unfold ctrLeft
  refine WP.ite (decide ((c.n - 16 * i) / 16 = 0)) (evalZ t0₇ (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : (c.n - 16 * i) / 16 = 0 := by simpa using ht
    refine wp_li (imm := 0) (by decide) fun s₈ u₈ => WP.block_nil ⟨pk₇.trans (PK.ofUpd u₈),
      by rw [u₈.other _ (by decide), s6₇], by rw [u₈.gpr]; congr 1; omega_arith, by rw [u₈.mem, m₇]; exact cnt₅,
      by rw [u₈.mem, hmd]; exact data₇, by rw [u₈.mem]; exact frame₇⟩
  · have h0 : (c.n - 16 * i) / 16 ≠ 0 := by simpa using hf
    refine wp_subi (imm := 16) (by decide) fun s₈ u₈ => WP.block_nil ⟨pk₇.trans (PK.ofUpd u₈),
      by rw [u₈.other _ (by decide), s6₇], ?_, by rw [u₈.mem, m₇]; exact cnt₅, by rw [u₈.mem, hmd]; exact data₇,
      by rw [u₈.mem]; exact frame₇⟩
    rw [u₈.gpr, s7₇, ofNat_sub' (by omega_arith) (by omega_arith)]
    congr 1; omega_arith

/-- `ctr`: the data XORed with CTR's keystream under `K2` from the counter
`Q` of the IV at `W + src`. -/
theorem ctr_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {src : Nat} (hsrc : src + 16 ≤ cntO)
    (hsrc8 : src % 8 = 0) :
    WP isa (ctr src) s fun s' => PK s s' ∧ Frame (ctrR c) s.mem s'.mem ∧
      bytesAt s'.mem c.D c.n = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem c.C c.R)
        (Spec.Siv.counter (bytesAt s.mem (c.W + BitVec.ofNat 64 src) 16)) (bytesAt s.mem c.D c.n) := by
  have hn := L.n_lt
  have hRb := L.rb
  obtain hk := wholeOf_le c.n
  unfold ctr
  rw [← List.append_nil (counter src)]
  refine WP.seq (counter_wp L E hsrc hsrc8 fun s₁ pk₁ f₁ hq₁ => WP.block_nil ?_)
  generalize hqd : Spec.Siv.counter (bytesAt s.mem (c.W + BitVec.ofNat 64 src) 16) = q at hq₁ ⊢
  obtain hql : q.length = 16 := by rw [← hqd]; exact length_counter _
  obtain hlow : Spec.Siv.beNat q % 2 ^ 32 < 2 ^ 31 := by rw [← hqd]; exact counter_low _
  obtain hlow64 : Spec.Siv.beNat q % 2 ^ 64 < 2 ^ 63 := by rw [← hqd]; exact counter_low64 _
  obtain E₁ := E.of_pk pk₁
  obtain dC : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 cntO, 16⟩ : Region)], (⟨c.C, 512⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.c0_w' (by decide) (by decide)
  obtain hc : Spec.Siv.ctxCiph s₁.mem c.C c.R = Spec.Siv.ctxCiph s.mem c.C c.R := by
    rw [← ctrPart_frame f₁ dC hRb]; rfl
  obtain hd : bytesAt s₁.mem c.D c.n = bytesAt s.mem c.D c.n :=
    Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by omega_arith)
  obtain fr : ∀ {m' : Mem}, Frame (ctrR c) s₁.mem m' → Frame (ctrR c) s.mem m' := fun h =>
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W + BitVec.ofNat 64 64, 48⟩, by simp, Region.sub_prefix (by decide)⟩).trans h
  have done {t : State} (pk : PK s₁ t) (f : Frame (ctrR c) s₁.mem t.mem)
      (hdat : bytesAt t.mem c.D c.n = Spec.Siv.ctr (Spec.Siv.ctxCiph s₁.mem c.C c.R) q (bytesAt s₁.mem c.D c.n)) :
      PK s t ∧ Frame (ctrR c) s.mem t.mem ∧
        bytesAt t.mem c.D c.n = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem c.C c.R) q (bytesAt s.mem c.D c.n) :=
    ⟨pk₁.trans pk, fr f, by rw [hdat, hc, hd]⟩
  obtain hcl : ∀ y, (Spec.Siv.ctxCiph s₁.mem c.C c.R y).length = 16 := fun y => Proof.Cmac.aesWith_length _ _ y
  refine WP.seq (WP.mono (ctrWhole_wp L E₁ hql hlow hlow64 (cnt_init hq₁)) fun s₂ I => ?_)
  refine WP.ite (decide (c.n - 16 * wholeOf c.n = 0)) (evalZ I.s7 (by omega_arith)) (fun ht => WP.block_nil ?_)
    (fun hf => ?_)
  · have h0 : c.n - 16 * wholeOf c.n = 0 := by simpa using ht
    refine done I.pk I.frame ?_
    rw [I.data]
    exact ctrPart_all _ hcl q _ (by rw [Proof.Cmac.bytesAt_length]; omega_arith)
  · have h0 : 16 * wholeOf c.n < c.n := by have : c.n - 16 * wholeOf c.n ≠ 0 := by simpa using hf
                                           omega_arith
    refine WP.loop (M := isa) (fun (m : Nat) (t : State) => ∃ i, m = c.n - 16 * i ∧ 16 * i < c.n ∧ CInv c s₁ q i t)
      ?_ (c.n - 16 * wholeOf c.n) s₂ ⟨wholeOf c.n, rfl, h0, I⟩
    rintro m t ⟨i, rfl, hi, It⟩
    unfold ctrBody
    refine ctrHead_wp L It hi E₁ fun t₃ H => WP.mono (ctrTail_wp L It hi E₁ hlow64 H) fun t' S => ?_
    obtain ev := evalNZ S.s7 (by omega_arith)
    by_cases hfin : c.n - 16 * i ≤ 16
    · left
      refine ⟨by rw [ev]; simp; omega_arith, done (It.pk.trans S.pk) S.frame ?_⟩
      rw [S.data]
      exact ctrPart_all _ hcl q _ (by rw [Proof.Cmac.bytesAt_length]; omega_arith)
    · right
      refine ⟨by rw [ev]; simp; omega_arith, c.n - 16 * (i + 1), by omega_arith, i + 1, rfl, by omega_arith,
        ⟨It.pk.trans S.pk, S.s6, ?_, by omega_arith, S.cnt, ?_, S.frame⟩⟩
      · rw [S.s7]; congr 1; omega_arith
      · rw [S.data]; congr 1; omega_arith

end VG.Proof.AesSiv.RISCV64
