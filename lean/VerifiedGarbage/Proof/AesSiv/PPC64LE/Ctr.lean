module

public import VerifiedGarbage.Proof.AesSiv.PPC64LE.Env
import VerifiedGarbage.Proof.AesSiv.PPC64LE.Mac
public import VerifiedGarbage.Proof.AesSiv.Words
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesCtr.PPC64LE.Call
public import VerifiedGarbage.Proof.AesSiv.CtrPart
public import VerifiedGarbage.Impl.AesSiv.PPC64LE
import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-! ### `AesSiv.PPC64LE.Counter`, which only this module used -/

section

/-!
# AES-SIV on PPC64LE: the counter's words

Untrusted: everything here is checked by Lean. The counter `Q + i` is kept
at `W + 64` as two doublewords stored byte-reversed (`ldbrx`, `stdbrx`), the
halves of the 128-bit integer (`le8_rev`). `counter` clears bit 7 of the
IV's bytes 8 and 12 by setting and flipping it (`orr_eor`), which leaves the
counter's second doubleword below `2⁶³` (`counter_low64`), so adding to that
doubleword alone, fewer than `2⁶³` in all, adds to the integer (`add_lo`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.PPC64LE

open VG VG.PPC64LE
open VG.Proof.Cmac (le8 length_le8)
open VG.Proof.AesCcm (beVal beVal_append beVal_cons beVal_lt)

theorem getLsbD_rev64 (x : BitVec 64) {p : Nat} (hp : p < 64) :
    (rev64 x).getLsbD p = x.getLsbD (8 * (7 - p / 8) + p % 8) :=
  byteRev64_getLsbD x hp

/-- Storing the byte-reversed halves of `h ++ l` stores its bytes, big-endian. -/
theorem le8_rev (h l : BitVec 64) :
    le8 (rev64 h) ++ le8 (rev64 l) = Spec.Gcm.toBytes (h ++ l) := by
  refine Proof.Cmac.ext16 (by simp [length_le8]) (Proof.Cmac.toBytes_length _) fun k hk => ?_
  rw [Proof.Aes.toBytes_getD _ hk]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp only [hj, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge k 8 with h8 | h8
  · rw [getD_le8_append _ _ hk]
    simp only [h8, ↓reduceIte]
    rw [BitVec.getLsbD_extractLsb', getLsbD_rev64 _ (by omega_using [hj, h8])]
    simp only [hj, decide_true, Bool.true_and, show ¬ 8 * (15 - k) + j < 64 by omega_using [h8], ite_false]
    congr 1; omega_using [hj, h8]
  · rw [getD_le8_append _ _ hk]
    simp only [show ¬ k < 8 by omega_using [h8], ↓reduceIte]
    rw [BitVec.getLsbD_extractLsb', getLsbD_rev64 _ (by omega_using [hk, hj])]
    simp only [hj, decide_true, Bool.true_and, show 8 * (15 - k) + j < 64 by omega_using [hj, h8], ite_true]
    congr 1; omega_using [hj, h8]

theorem rev64_rev64 (a : BitVec 64) : rev64 (rev64 a) = a := Proof.Gcm.byteRev64_byteRev64 a

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

end VG.Proof.AesSiv.PPC64LE

end

end


/-!
# AES-SIV on PPC64LE: the counter and the calls of CTR

Untrusted: everything here is checked by Lean. The counter `Q + i` is kept
at `W + 64` as two byte-reversed doublewords whose second is
`(Q mod 2⁶⁴) + i`, below `2⁶⁴` (`CntAt`): its bytes are `be128 (Q + i)`
(`CntAt.bytes`), and adding `k` to the second doubleword alone adds `k`
(`cnt_add`). `counter` writes `Q` from the IV (`counter_wp`), `copy16` copies
a block of `W` (`copy16_wp`), and `cargs` gives `vg_aes_ctr32` its
arguments: `K2`'s schedule in the context, the counter block at `W + 96` and
the working space at `W + 384`.
-/

@[expose] public section

namespace VG.Proof.AesSiv.PPC64LE

open VG VG.Impl.AesSiv.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor Upd Mupd
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_addi wp_li wp_lsl wp_lsr wp_ld wp_std wp_or wp_xor wp_add wp_sub)
open VG.Proof.AesCcm.PPC64LE (wp_mv wp_ldbrx wp_stdbrx)
open VG.Proof.AesCtr.PPC64LE (CtrCall)
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
  ∃ hi lo : BitVec 64, m.readW (W + BitVec.ofNat 64 cntO) 64 = rev64 hi ∧
    m.readW (W + BitVec.ofNat 64 (cntO + 8)) 64 = rev64 lo ∧
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
  refine ⟨rev64 (m.readW (W + BitVec.ofNat 64 cntO) 64), rev64 (m.readW (W + BitVec.ofNat 64 (cntO + 8)) 64),
    (rev64_rev64 _).symm, (rev64_rev64 _).symm, ?_, ?_⟩
  · have e : Spec.Gcm.toBytes (rev64 (m.readW (W + BitVec.ofNat 64 cntO) 64) ++
        rev64 (m.readW (W + BitVec.ofNat 64 (cntO + 8)) 64)) = q := by
      rw [← le8_rev, rev64_rev64, rev64_rev64, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Offset.add_add,
        ← Proof.Cmac.bytesAt_split, h]
    rw [← e, Proof.Cmac.ofBytes_toBytes]
    exact (BitVec.add_zero _).symm
  · have e : Spec.Gcm.toBytes (rev64 (m.readW (W + BitVec.ofNat 64 cntO) 64) ++
        rev64 (m.readW (W + BitVec.ofNat 64 (cntO + 8)) 64)) = q := by
      rw [← le8_rev, rev64_rev64, rev64_rev64, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Offset.add_add,
        ← Proof.Cmac.bytesAt_split, h]
    obtain ha := congrArg Spec.Gcm.ofBytes e
    rw [Proof.Cmac.ofBytes_toBytes, beNat_eq] at ha
    rw [← toNat_append_lo (rev64 (m.readW (W + BitVec.ofNat 64 cntO) 64)), ha, BitVec.toNat_ofNat,
      Nat.mod_mod_of_dvd _ (by decide), Nat.add_zero]

/-- Adding `k` to the counter's second doubleword, without a carry. -/
theorem cnt_add {m : Mem} {W : Addr} {q : List Byte} {i k : Nat} {hi lo : BitVec 64}
    (h0 : m.readW (W + BitVec.ofNat 64 cntO) 64 = rev64 hi)
    (happ : (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes q + BitVec.ofNat 128 i)
    (hlo : lo.toNat = Spec.Siv.beNat q % 2 ^ 64 + i) (hk : Spec.Siv.beNat q % 2 ^ 64 + i + k < 2 ^ 64) :
    CntAt (m.writeW (W + BitVec.ofNat 64 (cntO + 8)) (rev64 (lo + BitVec.ofNat 64 k))) W q (i + k) := by
  refine ⟨hi, lo + BitVec.ofNat 64 k, ?_, Mem.readW_writeW_self64 _ _ _, ?_, ?_⟩
  · rw [Mem.readW_writeW_sep (Offset.sep W (d := cntO) (n := 8) (e := cntO + 8) (k := 8) (by decide) (by decide)
      (by decide)) (by decide), h0]
  · rw [add_lo hi lo (by omega_arith), happ, BitVec.add_assoc, BitVec.ofNat_add]
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_arith), hlo, Nat.mod_eq_of_lt (by omega_arith)]
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

theorem copy16_wp {c : Cx} {s : State} (E : Env c s) {a b : Nat} (ha : a + 16 ≤ 384) (hb : b + 16 ≤ 384)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hab : a + 16 ≤ b ∨ b + 16 ≤ a) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', PK s s' → (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) → s'.mem = copyMem s.mem c.W a b →
      WP isa (.block is) s' Q) :
    WP isa (.block (copy16 a b ++ is)) s Q := by
  simp only [copy16, List.cons_append, List.nil_append]
  refine wp_ld (a := c.W + BitVec.ofNat 64 a) (by decide) ⟨by omega_arith, by omega_arith⟩ (by rw [E.r14])
    (E.perm.wR (by omega_arith)) fun s₁ u₁ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 b) (by decide) ⟨by omega_arith, by omega_arith⟩
    (by rw [u₁.other _ (by decide), E.r14]) (by rw [u₁.wr]; exact E.perm.wW (by omega_arith)) fun s₂ u₂ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 a + BitVec.ofNat 64 8) (by decide) ⟨by omega_arith, by omega_arith⟩
    (by rw [u₂.gpr, u₁.other _ (by decide), E.r14, Offset.add_add])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, Offset.add_add]; exact E.perm.wR (by omega_arith)) fun s₃ u₃ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 b + BitVec.ofNat 64 8) (by decide) ⟨by omega_arith, by omega_arith⟩
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.r14, Offset.add_add])
    (by rw [u₃.wr, u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by omega_arith)) fun s₄ u₄ => ?_
  refine k s₄ ((PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofUpd u₃).trans (PK.ofMupd u₄))))
    (fun r hr => by rw [u₄.gpr, u₃.other _ hr, u₂.gpr, u₁.other _ hr]) ?_
  obtain sep : Mem.Sep (c.W + BitVec.ofNat 64 a + BitVec.ofNat 64 8) (64 / 8) (c.W + BitVec.ofNat 64 b) (64 / 8) := by
    rw [Offset.add_add]
    exact Offset.sep c.W (d := a + 8) (n := 8) (e := b) (k := 8) (by omega_arith) (by omega_arith) (by omega_arith)
  rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, Mem.readW_writeW_sep sep (by decide)]

/-! ## The counter `Q` -/

theorem qbits_eq : BitVec.ofNat 64 0x80 ||| BitVec.ofNat 64 0x80 <<< 32 = qbits := by decide

/-- `counter`: the counter `Q` of the IV at `W + src` at `W + 64`. -/
theorem counter_wp {c : Cx} {s : State} (E : Env c s) {src : Nat} (hsrc : src + 16 ≤ cntO) (hsrc8 : src % 8 = 0)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', PK s s' → Frame [⟨c.W + BitVec.ofNat 64 cntO, 16⟩] s.mem s'.mem →
      bytesAt s'.mem (c.W + BitVec.ofNat 64 cntO) 16 =
        Spec.Siv.counter (bytesAt s.mem (c.W + BitVec.ofNat 64 src) 16) → WP isa (.block is) s' Q) :
    WP isa (.block (counter src ++ is)) s Q := by
  simp only [counter, List.cons_append, List.nil_append]
  refine wp_ld (a := c.W + BitVec.ofNat 64 src) (by decide) ⟨by simp only [cntO] at hsrc; omega_arith, by omega_arith⟩
    (by rw [E.r14]) (E.perm.wR (by simp only [cntO] at hsrc; omega_arith)) fun s₁ u₁ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 cntO) (by decide) ⟨by decide, by decide⟩
    (by rw [u₁.other _ (by decide), E.r14]) (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun s₂ u₂ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 (src + 8)) (by decide) ⟨by simp only [cntO] at hsrc; omega_arith, by omega_arith⟩
    (by rw [u₂.gpr, u₁.other _ (by decide), E.r14])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by simp only [cntO] at hsrc; omega_arith)) fun s₃ u₃ => ?_
  refine wp_li (by decide) fun s₄ u₄ => wp_lsl (by decide) fun s₅ u₅ => wp_or fun s₆ u₆ => wp_or fun s₇ u₇ =>
    wp_xor fun s₈ u₈ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 (cntO + 8)) (by decide) ⟨by decide, by decide⟩
    (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other,
      E.r14]) (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by decide))
    fun s₉ u₉ => ?_
  obtain pk : PK s s₉ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans (PK.ofMupd u₉))))))))
  obtain r10₆ : s₆.gpr .r10 = qbits := by
    rw [u₆.gpr, u₅.other _ (by decide), u₅.gpr, u₄.gpr]
    exact qbits_eq
  obtain r10₇ : s₇.gpr .r10 = qbits := by rw [u₇.other _ (by decide), r10₆]
  obtain r9 : s₈.gpr .r9 = s.mem.readW (c.W + BitVec.ofNat 64 (src + 8)) 64 &&& qmask := by
    rw [u₈.gpr, r10₇, u₇.gpr, r10₆, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      orr_eor, u₂.mem, u₁.mem, Mem.readW_writeW_sep (Offset.sep c.W (d := src + 8) (n := 8) (e := cntO) (k := 8)
        (by simp only [cntO] at hsrc ⊢; omega_arith) (by simp only [cntO] at hsrc ⊢; omega_arith) (by decide)) (by decide)]
  obtain m₉ : s₉.mem = (s.mem.writeW (c.W + BitVec.ofNat 64 cntO) (s.mem.readW (c.W + BitVec.ofNat 64 src) 64)).writeW
      (c.W + BitVec.ofNat 64 (cntO + 8)) (s.mem.readW (c.W + BitVec.ofNat 64 (src + 8)) 64 &&& qmask) := by
    rw [u₉.mem, r9, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]
  refine k s₉ pk (by rw [m₉, ← Offset.add_add c.W cntO 8]; exact Proof.Cmac.frame_store2 _ _ _) ?_
  rw [m₉, ← Offset.add_add c.W cntO 8, Proof.Cmac.bytesAt_store2, counter_words, Proof.Cmac.le8_readW,
    Proof.Cmac.le8_readW, ← Offset.add_add c.W src 8, ← Proof.Cmac.bytesAt_split]

/-! ## The calls' arguments -/

/-- The arguments of `vg_aes_ctr32`: `K2`'s schedule, the counter block at
`W + 96`, `k` blocks at `P`, and the working space at `W + 384`. -/
theorem cargs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {k : Nat}
    (hp : Covers [⟨P, 16 * k⟩] s.wr) (hpw : P.toNat + 16 * k ≤ 2 ^ 64)
    (hpc : (⟨c.C + BitVec.ofNat 64 272, 240⟩ : Region).Disjoint ⟨P, 16 * k⟩)
    (hpb : (⟨c.W + BitVec.ofNat 64 cbO, 16⟩ : Region).Disjoint ⟨P, 16 * k⟩)
    (hps : (⟨P, 16 * k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 scrO, 2048⟩)
    (r3 : s.gpr .r3 = c.C + BitVec.ofNat 64 272) (r4 : s.gpr .r4 = BitVec.ofNat 64 c.R)
    (r5 : s.gpr .r5 = c.W + BitVec.ofNat 64 cbO) (r6 : s.gpr .r6 = P) (r7 : s.gpr .r7 = BitVec.ofNat 64 k)
    (r8 : s.gpr .r8 = c.W + BitVec.ofNat 64 scrO) :
    CtrCall s (c.C + BitVec.ofNat 64 272) (c.W + BitVec.ofNat 64 cbO) P (c.W + BitVec.ofNat 64 scrO) c.R k where
  r3 := r3
  r4 := r4
  r5 := r5
  r6 := r6
  r7 := r7
  r8 := r8
  rounds := L.rounds
  wrap := hpw
  kc := L.c_w' (by decide) (by decide)
  kd := hpc
  ks := L.c_w' (by decide) (by decide)
  cd := hpb
  cs := L.w_w (.inl (by decide)) (by decide) (by decide)
  ds := hps
  reads := Covers.append_left (Covers.cons (E.perm.cC (by decide)) Covers.nil)
    (Covers.cons (E.perm.wCR (by decide)) (Covers.cons (Covers.right hp)
      (Covers.cons (E.perm.wCR (by decide)) Covers.nil)))
  writes := Covers.cons (E.perm.wC (by decide)) (Covers.cons hp (Covers.cons (E.perm.wC (by decide)) Covers.nil))

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

theorem wholeCount_wp {s : State} {left : Nat} (d : Reg) (h20 : s.gpr .r20 = BitVec.ofNat 64 left)
    (hl : left < 2 ^ 64) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 (wholeOf left)) → WP isa (.block is) s' Q) :
    WP isa (.block (wholeCount d ++ is)) s Q := by
  simp only [wholeCount, List.cons_append, List.nil_append]
  refine wp_lsr (by decide) fun s₁ u₁ => wp_lsl (by decide) fun s₂ u₂ => wp_lsr (by decide) fun s₃ u₃ => k s₃ ?_
  obtain v : s₃.gpr d = BitVec.ofNat 64 (wholeOf left) := by rw [u₃.gpr, u₂.gpr, u₁.gpr, h20, count_eq hl]
  exact ⟨v, fun r hr => by rw [u₃.other _ hr, u₂.other _ hr, u₁.other _ hr], by rw [u₃.mem, u₂.mem, u₁.mem],
    by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.sp, u₂.sp, u₁.sp],
    by rw [u₃.lr, u₂.lr, u₁.lr]⟩

/-- The state at the start of block `i` of CTR from the state `s₀`: the
data is CTR's output on its first `16 i` bytes, from `r19` on are the rest
(`r20` bytes), and the counter is `Q + i`. -/
structure CInv (c : Cx) (s₀ : State) (q : List Byte) (i : Nat) (s : State) : Prop where
  pk : PK s₀ s
  r19 : s.gpr .r19 = c.D + BitVec.ofNat 64 (16 * i)
  r20 : s.gpr .r20 = BitVec.ofNat 64 (c.n - 16 * i)
  le : 16 * i ≤ c.n
  cnt : CntAt s.mem c.W q i
  data : bytesAt s.mem c.D c.n = ctrPart (Spec.Siv.ctxCiph s₀.mem c.C c.R) q (bytesAt s₀.mem c.D c.n) (16 * i)
  frame : Frame (ctrR c) s₀.mem s.mem

/-- `wholePre`: the counter block is `Q`, and the arguments of
`vg_aes_ctr32` over the first `wholeOf L` blocks of the data. -/
theorem wholePre_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) :
    WP isa (.block wholePre) s fun s' => PK s s' ∧ s'.gpr .r19 = c.D ∧ s'.gpr .r20 = BitVec.ofNat 64 c.n ∧
      s'.mem = copyMem s.mem c.W cntO cbO ∧
      CtrCall s' (c.C + BitVec.ofNat 64 272) (c.W + BitVec.ofNat 64 cbO) c.D (c.W + BitVec.ofNat 64 scrO) c.R
        (wholeOf c.n) := by
  have hn := L.n_lt
  obtain hk := wholeOf_le c.n
  unfold wholePre ctrArgs
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => ?_
  obtain pk₂ : PK s s₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  obtain E₂ := E.of_pk pk₂
  refine copy16_wp E₂ (by decide) (by decide) (by decide) (by decide) (by decide) fun s₃ pk₃ g₃ m₃ => ?_
  obtain r20₃ : s₃.gpr .r20 = BitVec.ofNat 64 c.n := by rw [g₃ _ (by decide), u₂.gpr, u₁.other _ (by decide), E.r23]
  refine wholeCount_wp .r7 r20₃ hn fun s₄ u₄ => ?_
  refine wp_addi (by decide) (by decide) fun s₅ u₅ => wp_mv fun s₆ u₆ => wp_addi (by decide) (by decide) fun s₇ u₇ =>
    wp_addi (by decide) (by decide) fun s₈ u₈ => wp_mv fun s₉ u₉ => WP.block_nil ?_
  obtain pk₉ : PK s₃ s₉ := (PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans
    ((PK.ofUpd u₈).trans (PK.ofUpd u₉)))))
  obtain E₉ := E.of_pk (pk₂.trans (pk₃.trans pk₉))
  obtain r19₉ : s₉.gpr .r19 = c.D := by
    simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, g₃, u₂.other, u₁.gpr,
      E.r22]
  refine ⟨pk₂.trans (pk₃.trans pk₉), r19₉, by
      simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, r20₃],
    by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem], ?_⟩
  obtain hd := L.d_w' (d := cbO) (k := 16) (by decide)
  obtain hs := L.d_w' (d := scrO) (k := 2048) (by decide)
  exact cargs L E₉ (Proof.Gather.PPC64LE.covers_prefix E₉.perm.d hk) (by have := L.dw; omega_arith)
    ((L.c_d.sub_left (Lay.cSub (d := 272) (n := 240) (by decide))).sub_right (Region.sub_prefix hk))
    (hd.symm.sub_right (Region.sub_prefix hk)) (hs.sub_left (Region.sub_prefix hk))
    (by simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, g₃, u₂.other,
      u₁.other, E.r15])
    (by simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, g₃, u₂.other,
      u₁.other, E.r16])
    (by simp (disch := decide) only [u₉.other, u₈.other, u₇.gpr, u₆.other, u₅.other, u₄.other, g₃, u₂.other,
      u₁.other, E.r14])
    (by rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), g₃ _ (by decide), u₂.other _ (by decide), u₁.gpr, E.r22])
    (by simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr])
    (by simp (disch := decide) only [u₉.other, u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, g₃, u₂.other,
      u₁.other, E.r14])

/-! ## Adding to the counter -/

theorem cnt_frame (W : Addr) (m : Mem) (v : BitVec 64) :
    Frame [⟨W + BitVec.ofNat 64 cntO, 16⟩] m (m.writeW (W + BitVec.ofNat 64 (cntO + 8)) v) := by
  refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
  rw [← Offset.add_add]
  exact Offset.contains_base _ (d := 8) (n := 64 / 8) (k := 16) (by decide) (by decide)

/-- The counter's second doubleword loaded byte-reversed, `k` added, and
stored back. -/
theorem bump_wp {c : Cx} {s : State} (E : Env c s) {q : List Byte} {i k : Nat} (hc : CntAt s.mem c.W q i)
    (hb : Spec.Siv.beNat q % 2 ^ 64 + i + k < 2 ^ 64) (h9 : s.gpr .r9 = BitVec.ofNat 64 k) {is : List Instr}
    {Q : State → Prop}
    (cont : ∀ s', PK s s' → (∀ r, r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) →
      Frame [⟨c.W + BitVec.ofNat 64 cntO, 16⟩] s.mem s'.mem → CntAt s'.mem c.W q (i + k) → WP isa (.block is) s' Q) :
    WP isa (.block (.li .r11 (cntO + 8) :: .loadRev .d .r10 .r14 .r11 :: .add .r10 .r10 .r9 ::
      .storeRev .d .r10 .r14 .r11 :: is)) s Q := by
  obtain ⟨hi, lo, h0, h8, happ, hlo⟩ := hc
  refine wp_li (by decide) fun s₁ u₁ => ?_
  refine wp_ldbrx (ea := c.W + BitVec.ofNat 64 (cntO + 8)) (by decide)
    (by rw [u₁.gpr, u₁.other _ (by decide), E.r14]) (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide))
    fun s₂ u₂ => ?_
  refine wp_add fun s₃ u₃ => ?_
  refine wp_stdbrx (ea := c.W + BitVec.ofNat 64 (cntO + 8)) (by decide)
    (by simp (disch := decide) only [u₃.other, u₂.other, u₁.gpr, u₁.other, E.r14])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by decide)) fun s₄ u₄ => ?_
  obtain r10 : s₃.gpr .r10 = lo + BitVec.ofNat 64 k := by
    rw [u₃.gpr, u₂.gpr, u₁.mem, h8, rev64_rev64, u₂.other _ (by decide), u₁.other _ (by decide), h9]
  obtain m₄ : s₄.mem = s.mem.writeW (c.W + BitVec.ofNat 64 (cntO + 8)) (rev64 (lo + BitVec.ofNat 64 k)) := by
    rw [u₄.mem, r10, u₃.mem, u₂.mem, u₁.mem]
  refine cont s₄ ((PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans (PK.ofMupd u₄))))
    (fun r h10 h11 => by rw [u₄.gpr, u₃.other _ h10, u₂.other _ h10, u₁.other _ h11]) (by rw [m₄]; exact cnt_frame _ _ _)
    (by rw [m₄]; exact cnt_add h0 happ hlo hb)

/-- The counter's second doubleword loaded byte-reversed, incremented, and
stored back. -/
theorem bump1_wp {c : Cx} {s : State} (E : Env c s) {q : List Byte} {i : Nat} (hc : CntAt s.mem c.W q i)
    (hb : Spec.Siv.beNat q % 2 ^ 64 + i + 1 < 2 ^ 64) {is : List Instr} {Q : State → Prop}
    (cont : ∀ s', PK s s' → (∀ r, r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) →
      Frame [⟨c.W + BitVec.ofNat 64 cntO, 16⟩] s.mem s'.mem → CntAt s'.mem c.W q (i + 1) → WP isa (.block is) s' Q) :
    WP isa (.block (.li .r11 (cntO + 8) :: .loadRev .d .r10 .r14 .r11 :: .addi .r10 .r10 1 ::
      .storeRev .d .r10 .r14 .r11 :: is)) s Q := by
  obtain ⟨hi, lo, h0, h8, happ, hlo⟩ := hc
  refine wp_li (by decide) fun s₁ u₁ => ?_
  refine wp_ldbrx (ea := c.W + BitVec.ofNat 64 (cntO + 8)) (by decide)
    (by rw [u₁.gpr, u₁.other _ (by decide), E.r14]) (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide))
    fun s₂ u₂ => ?_
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => ?_
  refine wp_stdbrx (ea := c.W + BitVec.ofNat 64 (cntO + 8)) (by decide)
    (by simp (disch := decide) only [u₃.other, u₂.other, u₁.gpr, u₁.other, E.r14])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by decide)) fun s₄ u₄ => ?_
  obtain r10 : s₃.gpr .r10 = lo + BitVec.ofNat 64 1 := by
    rw [u₃.gpr, u₂.gpr, u₁.mem, h8, rev64_rev64]
  obtain m₄ : s₄.mem = s.mem.writeW (c.W + BitVec.ofNat 64 (cntO + 8)) (rev64 (lo + BitVec.ofNat 64 1)) := by
    rw [u₄.mem, r10, u₃.mem, u₂.mem, u₁.mem]
  refine cont s₄ ((PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans (PK.ofMupd u₄))))
    (fun r h10 h11 => by rw [u₄.gpr, u₃.other _ h10, u₂.other _ h10, u₁.other _ h11]) (by rw [m₄]; exact cnt_frame _ _ _)
    (by rw [m₄]; exact cnt_add h0 happ hlo hb)

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
  refine WP.seq (WP.mono (wholePre_wp L E) fun s₁ ⟨pk₁, r19₁, r20₁, m₁, C₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.AesCtr.PPC64LE.ctr_call C₁) fun s₂ h₂ => ?_)
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
  obtain r20₂ : s₂.gpr .r20 = BitVec.ofNat 64 c.n := by rw [h₂.saved _ (by decide), r20₁]
  unfold wholePost
  refine wholeCount_wp .r9 r20₂ hn fun s₃ u₃ => ?_
  obtain E₃ := E₂.of_pk (PK.ofUpd u₃)
  refine bump_wp E₃ (by rw [u₃.mem]; exact hc₂) (by omega_arith) u₃.gpr fun s₄ pk₄ g₄ f₄ hc₄ => ?_
  refine wp_lsl (by decide) fun s₅ u₅ => wp_add fun s₆ u₆ => wp_sub fun s₇ u₇ => WP.block_nil ?_
  obtain pk₇ : PK s s₇ := pk₁.trans (pk₂.trans ((PK.ofUpd u₃).trans (pk₄.trans ((PK.ofUpd u₅).trans
    ((PK.ofUpd u₆).trans (PK.ofUpd u₇))))))
  obtain m₇ : s₇.mem = s₄.mem := by rw [u₇.mem, u₆.mem, u₅.mem]
  obtain r9₅ : s₅.gpr .r9 = BitVec.ofNat 64 (16 * wholeOf c.n) := by
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
    · exact (L.d_w' (d := scrO) (k := 2048) (by decide)).sub_left hsub
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
  · rw [u₇.other _ (by decide), u₆.gpr, r9₅, u₅.other _ (by decide), g₄ _ (by decide) (by decide),
      u₃.other _ (by decide), h₂.saved _ (by decide), r19₁]
  · simp (disch := decide) only [u₇.gpr, u₆.other, r9₅, u₅.other, g₄, u₃.other, r20₂]
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
      · exact ⟨_, by simp [scrO], fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W + BitVec.ofNat 64 64, 48⟩, by simp, Region.sub_prefix (by decide)⟩

end VG.Proof.AesSiv.PPC64LE
