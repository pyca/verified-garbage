module

public import VerifiedGarbage.Proof.AesSiv.PPC64LE.Env
public import VerifiedGarbage.Proof.AesSiv.PPC64LE.Counter
public import VerifiedGarbage.Proof.AesCtr.PPC64LE.Call
public import VerifiedGarbage.Proof.AesSiv.CtrPart
public import VerifiedGarbage.Impl.AesSiv.PPC64LE
import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.AesSiv.Words
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp

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
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_addi wp_li wp_lsl wp_ld wp_std wp_or wp_xor)
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
  omega

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
    have ha := congrArg Spec.Gcm.ofBytes e
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
  · rw [add_lo hi lo (by omega), happ, BitVec.add_assoc, BitVec.ofNat_add]
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), hlo, Nat.mod_eq_of_lt (by omega)]
    omega

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
  refine wp_ld (a := c.W + BitVec.ofNat 64 a) (by decide) ⟨by omega, by omega⟩ (by rw [E.r14])
    (E.perm.wR (by omega)) fun s₁ u₁ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 b) (by decide) ⟨by omega, by omega⟩
    (by rw [u₁.other _ (by decide), E.r14]) (by rw [u₁.wr]; exact E.perm.wW (by omega)) fun s₂ u₂ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 a + BitVec.ofNat 64 8) (by decide) ⟨by omega, by omega⟩
    (by rw [u₂.gpr, u₁.other _ (by decide), E.r14, Offset.add_add])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, Offset.add_add]; exact E.perm.wR (by omega)) fun s₃ u₃ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 b + BitVec.ofNat 64 8) (by decide) ⟨by omega, by omega⟩
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.r14, Offset.add_add])
    (by rw [u₃.wr, u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by omega)) fun s₄ u₄ => ?_
  refine k s₄ ((PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofUpd u₃).trans (PK.ofMupd u₄))))
    (fun r hr => by rw [u₄.gpr, u₃.other _ hr, u₂.gpr, u₁.other _ hr]) ?_
  have sep : Mem.Sep (c.W + BitVec.ofNat 64 a + BitVec.ofNat 64 8) (64 / 8) (c.W + BitVec.ofNat 64 b) (64 / 8) := by
    rw [Offset.add_add]
    exact Offset.sep c.W (d := a + 8) (n := 8) (e := b) (k := 8) (by omega) (by omega) (by omega)
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
  refine wp_ld (a := c.W + BitVec.ofNat 64 src) (by decide) ⟨by simp only [cntO] at hsrc; omega, by omega⟩
    (by rw [E.r14]) (E.perm.wR (by simp only [cntO] at hsrc; omega)) fun s₁ u₁ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 cntO) (by decide) ⟨by decide, by decide⟩
    (by rw [u₁.other _ (by decide), E.r14]) (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun s₂ u₂ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 (src + 8)) (by decide) ⟨by simp only [cntO] at hsrc; omega, by omega⟩
    (by rw [u₂.gpr, u₁.other _ (by decide), E.r14])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by simp only [cntO] at hsrc; omega)) fun s₃ u₃ => ?_
  refine wp_li (by decide) fun s₄ u₄ => wp_lsl (by decide) fun s₅ u₅ => wp_or fun s₆ u₆ => wp_or fun s₇ u₇ =>
    wp_xor fun s₈ u₈ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 (cntO + 8)) (by decide) ⟨by decide, by decide⟩
    (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other,
      E.r14]) (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by decide))
    fun s₉ u₉ => ?_
  have pk : PK s s₉ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans (PK.ofMupd u₉))))))))
  have r10₆ : s₆.gpr .r10 = qbits := by
    rw [u₆.gpr, u₅.other _ (by decide), u₅.gpr, u₄.gpr]
    exact qbits_eq
  have r10₇ : s₇.gpr .r10 = qbits := by rw [u₇.other _ (by decide), r10₆]
  have r9 : s₈.gpr .r9 = s.mem.readW (c.W + BitVec.ofNat 64 (src + 8)) 64 &&& qmask := by
    rw [u₈.gpr, r10₇, u₇.gpr, r10₆, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      orr_eor, u₂.mem, u₁.mem, Mem.readW_writeW_sep (Offset.sep c.W (d := src + 8) (n := 8) (e := cntO) (k := 8)
        (by simp only [cntO] at hsrc ⊢; omega) (by simp only [cntO] at hsrc ⊢; omega) (by decide)) (by decide)]
  have m₉ : s₉.mem = (s.mem.writeW (c.W + BitVec.ofNat 64 cntO) (s.mem.readW (c.W + BitVec.ofNat 64 src) 64)).writeW
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

end VG.Proof.AesSiv.PPC64LE
