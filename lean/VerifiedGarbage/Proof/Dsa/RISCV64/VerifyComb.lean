module

public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyProd
public import VerifiedGarbage.Proof.Dsa.RISCV64.CheckKey
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA verification on RISC-V: `g^u1 y^u2 mod p`

As on PPC64LE (`Proof/Dsa/PPC64LE/VerifyComb.lean`). `combine_ok`: into the P
space (p in array 0, `R² mod p` in array 24), `-p⁻¹ mod 2⁶⁴` into `t1`, `g^u1
mod p` (kept in array 25) and `y^u2 mod p` (`powP_ok`), for the exponents
`u1` and `u2` of the buffer's first and second `q_len` octets, and their
product modulo p to the buffer's first `p_len` octets. The Q space is kept.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Verify
open VG.Proof.Bignum (slot Arrays)

/-- `-p⁻¹ mod 2⁶⁴` is in `t1`. -/
abbrev PInv (s : State) (L : Lay) : Prop :=
  ((word s.mem L.S (slot L.wp 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0

/-- A byte of the buffer is at its offset from `S`. -/
theorem bufAt {L : Lay} (hL : L.Ok) {d : Nat} (hd : d < 2 * L.pl) :
    off L.Buf d = off L.S (L.bOff + d) ∧ ofs L.S (off L.Buf d) = L.bOff + d := by
  have hb := hL.buf_end
  have hw := hL.nowrap
  have e : off L.Buf d = off L.S (L.bOff + d) := by
    simp only [Lay.Buf, off, BitVec.add_assoc, BitVec.ofNat_add]
  exact ⟨e, by rw [e]; exact ofs_off0 L.S (by omega_arith)⟩

/-- The buffer's bytes are past the P space. -/
theorem bufSepP {L : Lay} (hL : L.Ok) {o k : Nat} (hk : o + k ≤ 2 * L.pl) :
    ∀ i < k, ∀ x, ofs L.S x < L.qOff → off (off L.Buf o) i ≠ x := by
  intro i hi x hx e
  subst e
  rw [off_off, (bufAt hL (by omega_arith)).2] at hx
  simp only [Lay.bOff] at hx
  omega_arith

/-- The buffer's bytes are readable. -/
theorem bufRd {s : State} {L : Lay} (hL : L.Ok) (hs : ScrL s L) {o k : Nat} (hk : o + k ≤ 2 * L.pl) :
    ∀ i < k, InRegions (s.rd ++ s.wr) (off (off L.Buf o) i) 1 := by
  intro i hi
  have hb := hL.buf_end
  rw [off_off, (bufAt hL (by omega_arith)).1]
  exact hs.ld (by omega_arith)

/-- The buffer's bytes, kept by a change before the Q space. -/
theorem bufBytes {L : Lay} (hL : L.Ok) {a n : Nat} {m m' : Mem} (h : Outside L.S a n m m')
    (han : a + n ≤ L.qOff) {o k : Nat} (hk : o + k ≤ 2 * L.pl) :
    Spec.Rsa.bytesAt m' (off L.Buf o) k = Spec.Rsa.bytesAt m (off L.Buf o) k := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  have hi := List.mem_range.mp hi
  rw [show off L.Buf o + BitVec.ofNat 64 i = off (off L.Buf o) i from rfl, off_off,
    (bufAt hL (by omega_arith)).2]
  simp only [Lay.bOff]
  omega_arith

/-- The buffer's bytes are past the P space, as `storeBE` needs. -/
theorem bufPastP {L : Lay} (hL : L.Ok) : ∀ x, ofs L.Buf x < L.pl → L.qOff ≤ ofs L.S x := by
  have hb := hL.buf_end
  have hw := hL.nowrap
  intro x hx
  have := (Offset.lt_iff x L.S (d := L.bOff) (n := L.pl) (by omega_arith)).mp hx
  simp only [Lay.bOff] at this
  simp only [ofs]
  omega_arith

/-- A change in the buffer keeps the Q space. -/
theorem bufKeepQ {L : Lay} {m m' : Mem} {n : Nat} (h : Outside L.Buf 0 n m m') (hn : n ≤ 2 ^ 64 - 1600) :
    Outside L.Q 1600 (2 ^ 64 - 1600) m m' := by
  intro x hx
  have hlt := (x - L.Q).isLt
  have hq : ofs L.Q x < 1600 := by simp only [ofs] at hx ⊢; omega_arith
  refine h x (Or.inr ?_)
  rw [buf_eq]
  simp only [ofs, off] at hq ⊢
  rw [Offset.toNat_sub_add x L.Q (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

/-- Memory changed only in the P space's arrays from array 1 on. -/
abbrev PArr (L : Lay) (m m' : Mem) : Prop := Outside L.S (slot L.wp 1) (27 * (8 * (L.wp + 2))) m m'

theorem PArr.of {L : Lay} {o n : Nat} {m m' : Mem} (h : Outside L.S o n m m') (ho : slot L.wp 1 ≤ o)
    (hn : o + n ≤ slot L.wp 28) : PArr L m m' :=
  h.mono ho (by simp only [Lay.slot_eq] at hn ⊢; omega_arith)

theorem PArr.pbody {L : Lay} {m m' : Mem} (h : PArr L m m') : PBody L m m' :=
  PBody.of h (by simp only [Lay.slot_eq]; omega_arith) (by simp only [Lay.qOff, Lay.slot_eq]; omega_arith)

/-- The registers `powP` writes. -/
def powPRegs : List Reg := [.s8] ++ loadRegs ++ copyRegs ++ [.s10] ++ Win.powWRegs

/-- `powP`: the `p_len` octets at `N` (`s7`) to the power of the `q_len`
octets at `off L.Buf o` (`s9`), modulo p, into array 4. Arrays 1–23 change. -/
theorem powP_ok {s : State} {L : Lay} {key sig N : Addr} {o p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hin : InP s L) (hi : PInv s L) (hN : Src s L N L.pl) (h7 : s.gpr .s7 = N)
    (h9 : s.gpr .s9 = off L.Buf o) (ho : o + L.ql ≤ 2 * L.pl)
    (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1) (hrr : arrP s.mem L 24 = 2 ^ (128 * L.wp) % p) :
    WP isa powP s fun t =>
      (arrP t.mem L 4 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N L.pl) ^
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off L.Buf o) L.ql) % p ∧
        InP t L ∧ PInv t L ∧ Outside L.S (slot L.wp 1) (23 * (8 * (L.wp + 2))) s.mem t.mem) ∧
        Keep powPRegs s t := by
  have hZ := hL.z256
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have hbe := hL.buf_end
  have hqZ : L.qOff + 1600 ≤ L.Z := by simp only [Lay.bOff] at hbe; omega_arith
  have hq28 : L.qOff = slot L.wp 28 := rfl
  have e : ∀ j, slot L.wp j = 256 + j * (8 * (L.wp + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e5 := e 5; have e24 := e 24; have e25 := e 25
  have e28 := e 28
  have en := hin.env
  unfold powP
  refine WP.seq (WP.mono (getP_ok hs hL hr .s8) fun s₁ ⟨⟨a8, m1⟩, k1⟩ => ?_)
  have en1 := en.keep k1
  refine WP.seq (WP.mono (loadArr_ok en1 (j := 4) (N := N) (by decide)
      (by rw [k1.gpr (by decide), h7]; exact (BitVec.add_zero _).symm) a8 (by omega) (by omega)
      (by rw [k1.2.1, k1.2.2]; exact hN.rd) (fun i hi x hx => hN.sep i hi x (by omega_arith)))
    fun s₂ ⟨⟨v4, _, o2, a7⟩, k2⟩ => ?_)
  rw [m1] at v4 o2
  have en2 : Env s₂ L.S L.qOff L.wp := ⟨en.hs.congr (k1.trans k2).2.2, a7, ((k1.trans k2).gpr (by decide)).trans en.s5,
    ((k1.trans k2).gpr (by decide)).trans en.t0, en.w2, en.w48, en.hZ⟩
  refine WP.seq (WP.mono (copy_ok en2 (o := 1) (a := 24) (by decide) (by decide) (by decide))
    fun s₃ ⟨⟨c1, o3⟩, k3⟩ => ?_)
  have en3 := en2.keep k3
  have k13 := (k1.trans k2).trans k3
  have o23 : Outside L.S (slot L.wp 1) (4 * (8 * (L.wp + 2))) s.mem s₃.mem :=
    (o2.mono (by omega) (by omega)).trans (o3.mono (by omega) (by omega))
  have hb3 : Body L s.mem s₃.mem := Body.ofP hL o23 (by omega) (by omega)
  refine WP.seq (WP.mono (getQ_ok (hs.congr k13.2.2) hL (hr.keep k13 hb3) .s10) fun s₄ ⟨⟨a10, m4⟩, k4⟩ => ?_)
  have en4 := en3.keep k4
  have k14 := k13.trans k4
  have A0 : arrP s₄.mem L 0 = p := by
    rw [arrP, m4, o3.wordsVal (by omega) (by omega_arith), o2.wordsVal (by omega) (by omega_arith)]; exact hp0
  have W0 : word s₄.mem L.S (slot L.wp 0) = word s.mem L.S (slot L.wp 0) := by
    rw [m4, o3.word (by omega) (by omega_arith), o2.word (by omega) (by omega_arith)]
  have A1 : arrP s₄.mem L 1 = 2 ^ (128 * L.wp) % p := by
    rw [arrP, m4, wordsVal_congr (m := s₂.mem) (d := slot L.wp 24) fun i hi => c1 i (by omega)]
    rw [← hrr, arrP, o2.wordsVal (by omega) (by omega_arith)]
  have A4 : arrP s₄.mem L 4 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N L.pl) := by
    rw [arrP, m4, o3.wordsVal (by omega) (by omega_arith)]; exact v4
  have hbuf : Spec.Rsa.bytesAt s₄.mem (off L.Buf o) L.ql = Spec.Rsa.bytesAt s.mem (off L.Buf o) L.ql := by
    rw [m4]; exact bufBytes hL o23 (by omega) ho
  refine WP.mono (Win.powWin_ok (D := off L.Buf o) (L := L.ql) en4.hs (by omega) (by omega)
    (by omega) en4.a7 en4.s5 en4.t0 (by rw [W0, k14.gpr (by decide)]; exact hi)
    (by show 2 ≤ arrP s₄.mem L 0; rw [A0]; exact hp) (by show arrP s₄.mem L 0 % 2 = 1; rw [A0]; exact hpo)
    (by show arrP s₄.mem L 1 < arrP s₄.mem L 0; rw [A1, A0]; exact Nat.mod_lt _ (by omega))
    (by rw [k4.gpr (by decide), k13.gpr (by decide), h9]; exact (BitVec.add_zero _).symm) a10 (by omega)
    (by omega_arith) (by rw [k14.2.1, k14.2.2]; exact bufRd hL hs (k := L.ql) ho)
    (fun i hi x hx => bufSepP hL ho i hi x hx)) fun t ⟨⟨r4, o5'⟩, k5⟩ => ?_
  have o5 : Outside L.S (slot L.wp 1) (23 * (8 * (L.wp + 2))) s₄.mem t.mem := o5'
  have r4 := r4 (by
    show arrP s₄.mem L 1 = 2 ^ (64 * L.wp) * 2 ^ (64 * L.wp) % arrP s₄.mem L 0
    rw [A1, A0, pow_two_mul])
  refine ⟨⟨?_, ⟨en4.keep k5, ((k14.trans k5).gpr (by decide)).trans hin.s6⟩, ?_, ?_⟩, (k14.trans k5).mono (by decide)⟩
  · show wordsVal t.mem L.S (slot L.wp 4) L.wp = _
    rw [r4, hbuf]
    show arrP s₄.mem L 4 ^ _ % arrP s₄.mem L 0 = _
    rw [A4, A0]
  · show ((word t.mem L.S (slot L.wp 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [o5.word (by omega) (by omega_arith), W0, (k14.trans k5).gpr (by decide)]; exact hi
  · rw [← m4] at o23
    exact (o23.mono (by omega) (by omega)).trans o5

/-- Two Montgomery multiplications: `[5] R ≡ y (R² mod p)` and `[7] R ≡ g [5]`
give `[7] = g y mod p`. -/
theorem combMont {p R V5 V7 G Y : Nat} (hR : Nat.Coprime R p) (h5 : V5 * R % p = Y * (R * R % p) % p)
    (h7 : V7 * R % p = G * V5 % p) (hlt : V7 < p) : V7 = G * Y % p := by
  have e5 : V5 % p = Y * R % p := VG.Proof.Bignum.mont_cancel hR (by
    rw [h5, Nat.mul_mod_mod, Nat.mul_assoc])
  have e7 : V7 % p = G * Y % p := VG.Proof.Bignum.mont_cancel hR (by
    rw [h7, Nat.mul_mod, e5, ← Nat.mul_mod, Nat.mul_assoc])
  rw [← e7, Nat.mod_eq_of_lt hlt]

/-- `montOp o a b` in the P space, for `o` among 5 and 7, `[b] < p`. -/
theorem pmont_ok {s : State} {L : Lay} (hL : L.Ok) (hin : InP s L) (hi : PInv s L)
    {o a b : Nat} (ho : o = 5 ∨ o = 7) (ha : a < 8) (ha2 : a ≠ 2) (hb : b < 8) (hb2 : b ≠ 2)
    (hB : arrP s.mem L b < arrP s.mem L 0) :
    WP isa (PublicChecked.montOp o a b) s fun t =>
      (InP t L ∧ PInv t L ∧ arrP t.mem L o < arrP s.mem L 0 ∧
        arrP t.mem L o * 2 ^ (64 * L.wp) % arrP s.mem L 0 = arrP s.mem L a * arrP s.mem L b % arrP s.mem L 0 ∧
        (∀ j < 28, j ≠ 2 → j ≠ 3 → j ≠ o → arrP t.mem L j = arrP s.mem L j) ∧ PArr L s.mem t.mem) ∧
        Keep Pub.montRegs s t := by
  have e := hin.env
  have hw := hL.wp_ge
  have h8 := slot_lt (w := L.wp) (show 8 < 28 by decide)
  have hn : L.S.toNat + slot L.wp 28 ≤ 2 ^ 64 := by have := e.hs.nowrap; have := e.hZ; omega
  refine WP.mono (Pub.montOp_ok e.hs (by omega) ha hb (by omega) (by omega) ha2 hb2 e.w2 (by omega)
    (by have := e.hZ; omega) e.a7 e.s5 e.t0 hi hB) fun t ⟨⟨lt, eq, ar⟩, k⟩ => ?_
  have pa : PArr L s.mem t.mem := fun x hx => ar x fun k hk => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    have h1 := slot_mono (w := L.wp) (show 1 ≤ k by omega)
    have h2 := slot_lt (w := L.wp) (show k < 28 by omega)
    have e1 := Lay.slot_eq L.wp 1; have e28 := Lay.slot_eq L.wp 28
    simp only [VG.Proof.Bignum.ofs, ofs] at hx ⊢
    omega
  refine ⟨⟨hin.keep k, ?_, lt, eq, fun j hj h2 h3 ho' => arrays_val ar hj (by
    intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega) hn, pa⟩, k⟩
  show ((word t.mem L.S (slot L.wp 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  rw [arrays_word0 ar (by intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega) hn,
    k.gpr (by decide)]
  exact hi

theorem parr_win {L : Lay} {m m' : Mem} (h : Outside L.S (slot L.wp 1) (23 * (8 * (L.wp + 2))) m m') :
    PArr L m m' :=
  PArr.of h (Nat.le_refl _) (by simp only [Lay.slot_eq]; omega)

theorem parr_arr {L : Lay} {j : Nat} (hj1 : 1 ≤ j) (hj : j < 28) {m m' : Mem}
    (h : Outside L.S (slot L.wp j) (8 * (L.wp + 2)) m m') : PArr L m m' :=
  PArr.of h (slot_mono hj1) (slot_lt hj)

/-- The registers `combine`'s first block writes. -/
def headRegs : List Reg := enterRegs ++ [.s0, .s1, .s2, .s3, .t1] ++ [.s7, .t2, .s8] ++ [.s9] ++ ptrRegs

/-- `combine`'s first block: into the P space, `-p⁻¹ mod 2⁶⁴` into `t1`, the
buffer into `s9` and g's octets into `s7`. -/
theorem combHead_ok {s : State} {L : Lay} {key sig : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hp0 : arrP s.mem L 0 = p) (hpo : p % 2 = 1) :
    WP isa (.block (enterP ++ Precompute.minv ++ ptrBuf ++ [.addi .s9 .s7 0] ++ ptrG)) s fun t =>
      (InP t L ∧ PInv t L ∧ t.gpr .s7 = off key (L.pl + L.ql) ∧ t.gpr .s8 = BitVec.ofNat 64 L.pl ∧
        t.gpr .s9 = off L.Buf 0 ∧ t.mem = s.mem) ∧ Keep headRegs s t := by
  have hw := hL.wp_ge
  have hq28 : L.qOff = slot L.wp 28 := rfl
  have h0 := slot_lt (w := L.wp) (show 0 < 28 by decide)
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (enterP_ok hL hs hr) fun s₁ ⟨⟨in1, m1⟩, k1⟩ => ?_
  have hodd : (word s₁.mem L.S (slot L.wp 0)).toNat % 2 = 1 := by
    rw [wordsVal_mod_two _ _ _ (w := L.wp) (by omega), m1]
    exact (show arrP s.mem L 0 % 2 = 1 by rw [hp0]; exact hpo)
  refine WP.mono (minv_ok in1.env.hs in1.env.a7 (slot_al _ _) (by omega) hodd) fun s₂ ⟨⟨i2, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hm2 : s₂.mem = s.mem := m2.trans m1
  refine WP.mono (ptrBuf_ok (hs.congr k12.2.2) hL (hr.keepM k12 hm2)) fun s₃ ⟨⟨a7, _, m3⟩, k3⟩ => ?_
  refine WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = off L.Buf 0 ∧ u.mem = s₃.mem)
    (by brun [a7, BitVec.add_zero]) (by rfl) (by rfl)) fun s₄ ⟨⟨a9, m4⟩, k4⟩ => ?_
  have k14 := (k12.trans k3).trans k4
  have hm4 : s₄.mem = s.mem := by rw [m4, m3, hm2]
  refine WP.mono (ptrG_ok (hs.congr k14.2.2) hL (hr.keepM k14 hm4)) fun t ⟨⟨b7, b8, m5⟩, k5⟩ => ?_
  have hm5 : t.mem = s.mem := by rw [m5, hm4]
  refine ⟨⟨in1.keep ((k2.trans k3).trans (k4.trans k5)), ?_, b7, b8, (k5.gpr (by decide)).trans a9, hm5⟩,
    (k14.trans k5).mono (by decide)⟩
  show ((word t.mem L.S (slot L.wp 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  rw [hm5, (k3.trans (k4.trans k5)).gpr (by decide), ← m1]; exact i2

/-- The registers `combine`'s second block writes. -/
def midRegs : List Reg := [.s7, .t2, .s8, .s9] ++ ptrRegs

/-- `combine`'s second block: the buffer from `q_len` on into `s9` and y's
octets into `s7`. -/
theorem combMid_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key sig) :
    WP isa (.block (ptrBuf2 ++ [.addi .s9 .s7 0] ++ ptrY)) s fun t =>
      (t.gpr .s7 = off key (2 * L.pl + L.ql) ∧ t.gpr .s9 = off L.Buf L.ql ∧ t.mem = s.mem) ∧
        Keep midRegs s t := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ptrBuf2_ok hs hL hr) fun s₁ ⟨⟨c7, _, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = off L.Buf L.ql ∧ u.mem = s₁.mem)
    (by brun [c7, BitVec.add_zero]) (by rfl) (by rfl)) fun s₂ ⟨⟨c9, m2⟩, k2⟩ => ?_
  refine WP.mono (ptrY_ok (hs.congr (k1.trans k2).2.2) hL (hr.keepM (k1.trans k2) (by rw [m2, m1])))
    fun t ⟨⟨d7, _, m3⟩, k3⟩ => ⟨⟨d7, (k3.gpr (by decide)).trans c9, by rw [m3, m2, m1]⟩,
      ((k1.trans k2).trans k3).mono (by decide)⟩

/-- The registers `combine`'s products write. -/
def tailRegs : List Reg := copyRegs ++ Pub.montRegs ++ [.s7, .t2, .s8] ++ storeRegs

/-- `combine`'s products: `[25] [4] mod p` to the buffer's first `p_len`
octets. -/
theorem combTail_ok {s : State} {L : Lay} {key sig : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hin : InP s L) (hi : PInv s L) (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p)
    (hpo : p % 2 = 1) (hrr : arrP s.mem L 24 = 2 ^ (128 * L.wp) % p) :
    WP isa (.seq (copy 1 24) (.seq (PublicChecked.montOp 5 4 1) (.seq (copy 6 25)
      (.seq (PublicChecked.montOp 7 6 5) (.seq (.block (bufBase .s7 .t2 ++ getP .s8)) (storeBE 7)))))) s
      fun t =>
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.pl) = arrP s.mem L 25 * arrP s.mem L 4 % p ∧
        InP t L ∧ Body L s.mem t.mem ∧ Outside L.Q 1600 (2 ^ 64 - 1600) s.mem t.mem) ∧ Keep tailRegs s t := by
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hpl : 128 ≤ L.pl := by rcases hL.pl with e | e | e <;> omega
  have hn : L.S.toNat + slot L.wp 28 ≤ 2 ^ 64 := by have := hin.env.hs.nowrap; have := hin.env.hZ; omega
  have e0 := Lay.slot_eq L.wp 0; have e1 := Lay.slot_eq L.wp 1; have e4 := Lay.slot_eq L.wp 4
  have e5 := Lay.slot_eq L.wp 5; have e6 := Lay.slot_eq L.wp 6; have e24 := Lay.slot_eq L.wp 24
  have e25 := Lay.slot_eq L.wp 25
  -- `R² mod p` into array 1.
  refine WP.seq (WP.mono (copy_ok hin.env (o := 1) (a := 24) (by decide) (by decide) (by decide))
    fun s₁ ⟨⟨v1, o1⟩, k1⟩ => ?_)
  have in1 := hin.keep k1
  have I1 : PInv s₁ L := by
    show ((word s₁.mem L.S (slot L.wp 0)).toNat * (s₁.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [o1.word (by omega) (by omega_arith), k1.gpr (by decide)]; exact hi
  have B0 : arrP s₁.mem L 0 = p := by rw [arrP, o1.wordsVal (by omega) (by omega_arith)]; exact hp0
  have B1 : arrP s₁.mem L 1 = 2 ^ (128 * L.wp) % p := by
    rw [arrP, wordsVal_congr (m := s.mem) (d := slot L.wp 24) fun i hi => v1 i (by omega)]; exact hrr
  have B4 : arrP s₁.mem L 4 = arrP s.mem L 4 := by rw [arrP, o1.wordsVal (by omega) (by omega_arith)]
  have B25 : arrP s₁.mem L 25 = arrP s.mem L 25 := by rw [arrP, o1.wordsVal (by omega) (by omega_arith)]
  -- `[5] R ≡ y R² (mod p)`.
  refine WP.seq (WP.mono (pmont_ok (o := 5) (a := 4) (b := 1) hL in1 I1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [B1, B0]; exact Nat.mod_lt _ (by omega)))
    fun s₂ ⟨⟨in2, I2, lt5, eq5, k2a, pa2⟩, k2⟩ => ?_)
  rw [B0, B1, B4] at eq5
  rw [B0] at lt5
  -- `g` into array 6.
  refine WP.seq (WP.mono (copy_ok in2.env (o := 6) (a := 25) (by decide) (by decide) (by decide))
    fun s₃ ⟨⟨v6, o3⟩, k3⟩ => ?_)
  have in3 := in2.keep k3
  have I3 : PInv s₃ L := by
    show ((word s₃.mem L.S (slot L.wp 0)).toNat * (s₃.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [o3.word (by omega) (by omega_arith), k3.gpr (by decide)]; exact I2
  have C0 : arrP s₃.mem L 0 = p := by
    rw [arrP, o3.wordsVal (by omega) (by omega_arith)]
    exact (k2a 0 (by decide) (by decide) (by decide) (by decide)).trans B0
  have C5 : arrP s₃.mem L 5 = arrP s₂.mem L 5 := by rw [arrP, o3.wordsVal (by omega) (by omega_arith)]
  have C6 : arrP s₃.mem L 6 = arrP s.mem L 25 := by
    rw [arrP, wordsVal_congr (m := s₂.mem) (d := slot L.wp 25) fun i hi => v6 i (by omega)]
    exact ((k2a 25 (by decide) (by decide) (by decide) (by decide)).trans B25)
  -- `[7] R ≡ g [5] (mod p)`.
  refine WP.seq (WP.mono (pmont_ok (o := 7) (a := 6) (b := 5) hL in3 I3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [C5, C0]; exact lt5))
    fun s₄ ⟨⟨in4, _, lt7, eq7, _, pa4⟩, k4⟩ => ?_)
  rw [C0, C6, C5] at eq7
  rw [C0] at lt7
  have v7 : arrP s₄.mem L 7 = arrP s.mem L 25 * arrP s.mem L 4 % p := by
    have hR := VG.Proof.Bignum.coprime_pow2 hpo (64 * L.wp)
    rw [← pow_two_mul] at eq5
    exact combMont hR eq5 eq7 lt7
  have pa : PArr L s.mem s₄.mem :=
    (((parr_arr (j := 1) (by decide) (by decide) o1).trans pa2).trans
      (parr_arr (j := 6) (by decide) (by decide) o3)).trans pa4
  have k14 := ((k1.trans k2).trans k3).trans k4
  have hr4 : Regs s₄ L key sig := hr.keep k14 (pa.pbody.body hL)
  -- To the buffer.
  refine WP.seq (WP.block_append (WP.mono (bufBase_ok (hs.congr k14.2.2) hL hr4 (rd := .s7) (t := .t2)
      (by decide) (by decide) (by decide)) fun u ⟨⟨f7, mu⟩, ku⟩ =>
    WP.mono (getP_ok (hs.congr (k14.trans ku).2.2) hL (hr4.keepM ku mu) .s8) fun s₅ ⟨⟨f8, m5⟩, k5⟩ => ?_))
  have m54 : s₅.mem = s₄.mem := by rw [m5, mu]
  have en5 := in4.env.keep (ku.trans k5)
  have ks5 := (k14.trans ku).trans k5
  refine WP.mono (storeBE_ok (j := 7) (O := L.Buf) (k := L.pl) en5 (by decide)
    (by have := ScrL.bufSt (hs.congr ks5.2.2) hL (o := 0) (k := L.pl) (by omega)
        simpa only [off, BitVec.add_zero] using this)
    (by have := buf_nowrap hL (o := 0) (k := L.pl) (by omega) (by omega); simpa only [off, BitVec.add_zero] using this)
    ((k5.gpr (by decide)).trans f7) f8 (by omega) (by omega) (bufPastP hL)) fun t ⟨⟨vt, ot⟩, kt⟩ => ?_
  rw [m54] at vt ot
  have hplt : p < 2 ^ (8 * L.pl) := by
    rw [← C0, ← hw8, show 8 * (8 * L.wp) = 64 * L.wp by omega]; exact wordsVal_lt _ _ _ _
  refine ⟨⟨?_, ⟨en5.keep kt, ((ks5.trans kt).gpr (by decide)).trans hin.s6⟩,
    (pa.pbody.body hL).trans (Body.ofBuf hL ot (by omega)),
    (pa.pbody.keepQ hL).trans (bufKeepQ ot (by omega))⟩, (ks5.trans kt).mono (by decide)⟩
  rw [vt, read_low _ _ (w := L.wp) (by omega) (by
    show arrP s₄.mem L 7 < 2 ^ (8 * L.pl); rw [v7]; exact Nat.lt_trans (Nat.mod_lt _ (by omega)) hplt)]
  exact v7

/-- The registers `combine` writes. -/
def combRegs : List Reg := headRegs ++ powPRegs ++ copyRegs ++ midRegs ++ powPRegs ++ tailRegs

theorem parr_q (L : Lay) : slot L.wp 1 + 27 * (8 * (L.wp + 2)) ≤ L.qOff := by
  simp only [Lay.qOff, Lay.slot_eq]; omega

theorem body_le {L : Lay} (hL : L.Ok) : 256 + (L.Z - 256) ≤ L.Z := by have := hL.z256; omega

theorem ql2_le {L : Lay} (hL : L.Ok) : L.ql + L.ql ≤ 2 * L.pl := by
  rcases hL.pl with e | e | e <;> rcases hL.ql with f | f | f <;> omega

theorem comb_sub1 {L : Lay} : L.pl + L.ql + L.pl ≤ 3 * L.pl + L.ql := by omega
theorem comb_sub2 {L : Lay} : 2 * L.pl + L.ql + L.pl ≤ 3 * L.pl + L.ql := by omega

/-- `combine`: `g^u1 y^u2 mod p` to the buffer's first `p_len` octets. -/
theorem combine_ok {s : State} {L : Lay} {key sig : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hk : Src s L key (3 * L.pl + L.ql))
    (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1) (hrr : arrP s.mem L 24 = 2 ^ (128 * L.wp) % p) :
    WP isa combine s fun t =>
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.pl) =
          gOf s.mem L key ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.ql) % p *
            (yOf s.mem L key ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off L.Buf L.ql) L.ql) % p) % p ∧
        InP t L ∧ Body L s.mem t.mem ∧ Outside L.Q 1600 (2 ^ 64 - 1600) s.mem t.mem) ∧ Keep combRegs s t := by
  have hZ := hL.z256
  have hw := hL.wp_ge
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have hpl : 128 ≤ L.pl := by rcases hL.pl with e | e | e <;> omega
  have e1 := Lay.slot_eq L.wp 1; have e24 := Lay.slot_eq L.wp 24; have e25 := Lay.slot_eq L.wp 25
  have e0 := Lay.slot_eq L.wp 0; have e4 := Lay.slot_eq L.wp 4
  have hn : L.S.toNat + L.qOff ≤ 2 ^ 64 := by
    have := hL.nowrap; have := hL.buf_end; simp only [Lay.bOff] at *; omega
  have hqs : slot L.wp 28 = L.qOff := rfl
  have h28 := slot_lt (w := L.wp) (show 25 < 28 by decide)
  unfold combine
  refine WP.seq (WP.mono (combHead_ok hL hs hr hp0 hpo) fun s₁ ⟨⟨in1, I1, a7, _, a9, m1⟩, k1⟩ => ?_)
  -- `g^u1 mod p` into array 4.
  refine WP.seq (WP.mono (powP_ok (o := 0) (p := p) hL (hs.congr k1.2.2) (hr.keepM k1 m1) in1 I1
    ((hk.keep k1.2.1 k1.2.2).sub (o := L.pl + L.ql) (k := L.pl) comb_sub1) a7 a9 (by omega)
    (by rw [m1]; exact hp0) hp hpo (by rw [m1]; exact hrr)) fun s₂ ⟨⟨v4, in2, I2, o2⟩, k2⟩ => ?_)
  rw [m1] at v4 o2
  -- Into array 25.
  refine WP.seq (WP.mono (copy_ok in2.env (o := 25) (a := 4) (by decide) (by decide) (by decide))
    fun s₃ ⟨⟨v25, o3⟩, k3⟩ => ?_)
  have pa3 : PArr L s.mem s₃.mem := (parr_win o2).trans (parr_arr (j := 25) (by decide) (by decide) o3)
  have k13 := (k1.trans k2).trans k3
  have hr3 : Regs s₃ L key sig := hr.keep k13 (pa3.pbody.body hL)
  refine WP.seq (WP.mono (combMid_ok hL (hs.congr k13.2.2) hr3) fun s₄ ⟨⟨b7, b9, m4⟩, k4⟩ => ?_)
  have k14 := k13.trans k4
  have in4 : InP s₄ L := (in2.keep k3).keep k4
  have I4 : PInv s₄ L := by
    show ((word s₄.mem L.S (slot L.wp 0)).toNat * (s₄.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [m4, o3.word (by omega) (by omega_arith), (k3.trans k4).gpr (by decide)]; exact I2
  have A0 : arrP s₄.mem L 0 = p := by rw [m4, arrP, pa3.wordsVal (by omega) (by omega_arith)]; exact hp0
  have A24 : arrP s₄.mem L 24 = 2 ^ (128 * L.wp) % p := by
    rw [m4, arrP, o3.wordsVal (by omega) (by omega_arith), o2.wordsVal (by omega) (by omega_arith)]; exact hrr
  -- `y^u2 mod p` into array 4.
  refine WP.seq (WP.mono (powP_ok (o := L.ql) (p := p) hL (hs.congr k14.2.2) (hr3.keepM k4 m4) in4 I4
    ((hk.keep k14.2.1 k14.2.2).sub (o := 2 * L.pl + L.ql) (k := L.pl) comb_sub2) b7 b9 (by omega)
    A0 hp hpo A24) fun s₅ ⟨⟨w4, in5, I5, o5⟩, k5⟩ => ?_)
  rw [m4, (hk.sub (o := 2 * L.pl + L.ql) (k := L.pl) comb_sub2).bytes (pa3.pbody.body hL) (body_le hL),
    bufBytes hL pa3 (parr_q L) (o := L.ql) (k := L.ql) (ql2_le hL)] at w4
  rw [m4] at o5
  have k15 := k14.trans k5
  have pa5 : PArr L s.mem s₅.mem := pa3.trans (parr_win o5)
  have hr5 : Regs s₅ L key sig := hr.keep k15 (pa5.pbody.body hL)
  have B0 : arrP s₅.mem L 0 = p := by rw [arrP, pa5.wordsVal (by omega) (by omega_arith)]; exact hp0
  have B24 : arrP s₅.mem L 24 = 2 ^ (128 * L.wp) % p := by
    rw [arrP, o5.wordsVal (by omega) (by omega_arith)]; rw [← m4]; exact A24
  have B25 : arrP s₅.mem L 25 = arrP s₂.mem L 4 := by
    rw [arrP, o5.wordsVal (by omega) (by omega_arith)]
    exact wordsVal_congr fun i hi => v25 i (by omega)
  refine WP.mono (combTail_ok hL (hs.congr k15.2.2) hr5 in5 I5 B0 hp hpo B24) fun t ⟨⟨vt, int, bt, qt⟩, kt⟩ =>
    ⟨⟨?_, int, (pa5.pbody.body hL).trans bt, (pa5.pbody.keepQ hL).trans qt⟩, k15.trans kt⟩
  rw [vt, B25, v4, w4, show off L.Buf 0 = L.Buf from BitVec.add_zero _]
  rfl

end VG.Proof.Dsa.RISCV64
