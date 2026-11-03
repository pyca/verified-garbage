module

public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyProd
public import VerifiedGarbage.Proof.Dsa.RISCV64.CheckKey
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA verification on RISC-V: `g^u1 y^u2 mod p`

`combine_ok`: into the P space (p in array 0, `R² mod p` in array 24),
`-p⁻¹ mod 2⁶⁴` into `t1`, g and y into arrays 4 and 5 (`combG_ok`,
`combT_ok`), the joint table `g^i y^j R mod p` for `i, j < 4`
(`jointTable_ok`), the joint windows of the exponents `u1` and `u2`, the
buffer's first `q_len` octets and those 32 octets on (`combL_ok`), and
`g^u1 y^u2 mod p` to the buffer's first `p_len` octets. The Q space is kept.
`powP_ok`, one power by the windows of `ModExpWin`, is the signature's.
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

/-! ## The joint power `g^u1 y^u2 mod p`

`jointTable` builds `T_(i + 4 j) = g^i y^j R mod p` for `i, j < 4` in arrays
8–23 (`jointTable_ok`), each entry the Montgomery product of two before it
(`montStep`); a joint window is two squares and `a := a T_(d1 + 4 d2)` for
two bits of each exponent (`jointWindow_ok`); a byte of each is four windows
(`jointByte_ok`); and the power is the bytes in turn (`jointLoop_ok`). -/

section Joint
open Win
open VG.Impl.Bignum.RISCV64.PublicChecked (montOp)

/-- A Montgomery product of products of powers of `G` and `Y` in Montgomery form. -/
theorem mont_pow2 {o a b G Y i j k l R N : Nat} (hR : Nat.Coprime R N) (ha : a % N = G ^ i * Y ^ j * R % N)
    (hb : b % N = G ^ k * Y ^ l * R % N) (h : o * R % N = a * b % N) :
    o % N = G ^ (i + k) * Y ^ (j + l) * R % N := by
  refine VG.Proof.Bignum.mont_cancel hR ?_
  rw [h, Nat.mul_mod, ha, hb, ← Nat.mul_mod, Nat.pow_add, Nat.pow_add]
  congr 1
  ac_rfl

/-- Entry `k` of the joint table is `G^e1 Y^e2 R mod N`, if `R² mod N` is right. -/
def JGood (m : Mem) (B : Addr) (w N G Y RR k e1 e2 : Nat) : Prop :=
  A m B w (8 + k) < N ∧ (RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N →
    A m B w (8 + k) % N = G ^ e1 * Y ^ e2 * 2 ^ (64 * w) % N)

/-- While the joint table is built: `R² mod N` in array 1, `G` and `Y` in
arrays 4 and 5, 1 in array 7, and the entries `done`. -/
structure JInv (m : Mem) (B : Addr) (w N G Y RR : Nat) (done : List (Nat × Nat × Nat)) : Prop where
  rr : A m B w 1 = RR
  g : A m B w 4 = G
  y : A m B w 5 = Y
  one : A m B w 7 = 1
  good : ∀ q ∈ done, JGood m B w N G Y RR q.1 q.2.1 q.2.2

/-- Every key of `done` is below 16 and none is `k`. -/
def Fresh (done : List (Nat × Nat × Nat)) (k : Nat) : Bool :=
  decide (k < 16) && done.all fun q => decide (q.1 < 16 ∧ q.1 ≠ k)

theorem JInv.after {m m' : Mem} {B : Addr} {w N G Y RR : Nat} {done : List (Nat × Nat × Nat)} {o : Nat}
    (h : JInv m B w N G Y RR done) (ho : o ≠ 1 ∧ o ≠ 4 ∧ o ≠ 5 ∧ o ≠ 7) (hf : ∀ q ∈ done, 8 + q.1 ≠ o ∧ q.1 < 16)
    (hv : ∀ j < 24, j ≠ 2 → j ≠ 3 → j ≠ o → A m' B w j = A m B w j) :
    JInv m' B w N G Y RR done := by
  refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [hv 1 (by decide) (by decide) (by decide) (by omega)]; exact h.rr
  · rw [hv 4 (by decide) (by decide) (by decide) (by omega)]; exact h.g
  · rw [hv 5 (by decide) (by decide) (by decide) (by omega)]; exact h.y
  · rw [hv 7 (by decide) (by decide) (by decide) (by omega)]; exact h.one
  · have := hf q hq
    unfold JGood
    rw [hv (8 + q.1) (by omega) (by omega) (by omega) this.1]
    exact h.good q hq

/-- `T_k := T_k1 T_k2`, for entries `(k1, i1, j1)` and `(k2, i2, j2)` of `done`. -/
theorem montStep {s : State} {B : Addr} {Z w N G Y RR : Nat} {done : List (Nat × Nat × Nat)}
    (h : WCtx s B Z w N) (hodd : N % 2 = 1) (hj : JInv s.mem B w N G Y RR done) {k k1 k2 i1 j1 i2 j2 : Nat}
    (hk : Fresh done k = true) (h1 : (k1, i1, j1) ∈ done) (h2 : (k2, i2, j2) ∈ done) :
    WP isa (montOp (8 + k) (8 + k1) (8 + k2)) s fun t =>
      (WCtx t B Z w N ∧ WinO B w s.mem t.mem ∧
        JInv t.mem B w N G Y RR ((k, i1 + i2, j1 + j2) :: done)) ∧ Keep Pub.montRegs s t := by
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  simp only [Fresh, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hk
  obtain ⟨hk16, hall⟩ := hk
  have f1 := hall _ h1; have f2 := hall _ h2
  refine WP.mono (h.mont (o := 8 + k) (a := 8 + k1) (b := 8 + k2) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (hj.good _ h2).1) fun t ⟨⟨ct, lt, e, v, o⟩, kt⟩ =>
    ⟨⟨ct, o, ?_⟩, kt⟩
  have hj' := hj.after (m' := t.mem) (o := 8 + k) (by omega)
    (fun q hq => ⟨by have := (hall q hq).2; omega, (hall q hq).1⟩) v
  refine ⟨hj'.rr, hj'.g, hj'.y, hj'.one, fun q hq => ?_⟩
  rcases List.mem_cons.1 hq with rfl | hq
  · refine ⟨lt, fun hE => mont_pow2 hR ((hj.good _ h1).2 hE) ((hj.good _ h2).2 hE) e⟩
  · exact hj'.good q hq

/-- The table's entries, from `jointTable`'s order. -/
def jDone : List (Nat × Nat × Nat) :=
  [(15, 3, 3), (14, 2, 3), (13, 1, 3), (12, 0, 3), (11, 3, 2), (10, 2, 2), (9, 1, 2), (8, 0, 2),
   (7, 3, 1), (6, 2, 1), (5, 1, 1), (3, 3, 0), (2, 2, 0), (4, 0, 1), (1, 1, 0), (0, 0, 0)]

/-- The registers the joint table writes. -/
def jtRegs : List Reg := Pub.montRegs ++ copyRegs ++ [.s0, .t3, .t5]

/-- `montStep`, with what the steps before it changed. -/
theorem montStepAcc {s₀ s : State} {B : Addr} {Z w N G Y RR : Nat} {done : List (Nat × Nat × Nat)}
    (h : WCtx s B Z w N) (hodd : N % 2 = 1) (O : WinO B w s₀.mem s.mem) (K : Keep jtRegs s₀ s)
    (hj : JInv s.mem B w N G Y RR done) {k k1 k2 i1 j1 i2 j2 : Nat}
    (hk : Fresh done k = true) (h1 : (k1, i1, j1) ∈ done) (h2 : (k2, i2, j2) ∈ done) :
    WP isa (montOp (8 + k) (8 + k1) (8 + k2)) s fun t =>
      WCtx t B Z w N ∧ WinO B w s₀.mem t.mem ∧ JInv t.mem B w N G Y RR ((k, i1 + i2, j1 + j2) :: done) ∧
        Keep jtRegs s₀ t :=
  WP.mono (montStep h hodd hj hk h1 h2) fun _ ⟨⟨c, o, J⟩, k⟩ => ⟨c, O.trans o, J, (K.trans k).mono (by decide)⟩

/-- `jointTable`. -/
theorem jointTable_ok {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) (hN : 2 ≤ N) (hodd : N % 2 = 1)
    (hRR : A s.mem B w 1 < N) :
    WP isa jointTable s fun t =>
      (WCtx t B Z w N ∧ WinO B w s.mem t.mem ∧ A t.mem B w 7 = 1 ∧ A t.mem B w 6 = A t.mem B w 8 ∧
        JInv t.mem B w N (A s.mem B w 4) (A s.mem B w 5) (A s.mem B w 1) jDone) ∧ Keep jtRegs s t := by
  have hn := h.nw
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  generalize hG : A s.mem B w 4 = G
  generalize hY : A s.mem B w 5 = Y
  generalize hRRd : A s.mem B w 1 = RR at hRR
  unfold jointTable
  -- 1 in array 7.
  refine WP.seq (WP.mono (Pub.oneP_ok h.scr (by have := h.w2; omega_arith) h.w31
    (Nat.le_trans (by unfold slot; omega_arith) h.hZ) h.a7 h.s5 h.t0) fun s₁ ⟨⟨h7, o1⟩, k1⟩ => ?_)
  replace h7 : A s₁.mem B w 7 = 1 := h7
  have c1 := h.of k1 (by decide) (arrO o1 (by decide) (by decide))
  have R1 : A s₁.mem B w 1 = RR := by rw [arr_out o1 (by decide) (by decide) hn, hRRd]
  have G1 : A s₁.mem B w 4 = G := by rw [arr_out o1 (by decide) (by decide) hn, hG]
  have Y1 : A s₁.mem B w 5 = Y := by rw [arr_out o1 (by decide) (by decide) hn, hY]
  -- `T_0 = R mod N`.
  refine WP.seq (WP.mono (c1.mont (o := 8) (a := 1) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [h7]; omega_arith)) fun s₂ ⟨⟨c2, lt2, e2, v2, o2⟩, k2⟩ => ?_)
  rw [h7, Nat.mul_one, R1] at e2
  have J2 : JInv s₂.mem B w N G Y RR [(0, 0, 0)] :=
    ⟨by rw [v2 1 (by decide) (by decide) (by decide) (by decide), R1],
      by rw [v2 4 (by decide) (by decide) (by decide) (by decide), G1],
      by rw [v2 5 (by decide) (by decide) (by decide) (by decide), Y1],
      by rw [v2 7 (by decide) (by decide) (by decide) (by decide), h7],
      fun q hq => by
        rw [List.mem_singleton.1 hq]
        show JGood s₂.mem B w N G Y RR 0 0 0
        exact ⟨lt2, fun hE => by
          simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul]
          exact VG.Proof.Bignum.mont_cancel hR (by rw [e2, hE, Nat.mod_mod])⟩⟩
  -- `T_1 = G R mod N` and `T_4 = Y R mod N`.
  refine WP.seq (WP.mono (c2.mont (o := 9) (a := 4) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [J2.rr]; exact hRR))
    fun s₃ ⟨⟨c3, lt3, e3, v3, o3⟩, k3⟩ => ?_)
  rw [J2.g, J2.rr] at e3
  have J3' := J2.after (m' := s₃.mem) (o := 9) (by decide) (by decide) v3
  have J3 : JInv s₃.mem B w N G Y RR [(1, 1, 0), (0, 0, 0)] :=
    ⟨J3'.rr, J3'.g, J3'.y, J3'.one, fun q hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · show JGood s₃.mem B w N G Y RR 1 1 0
        exact ⟨lt3, fun hE => VG.Proof.Bignum.mont_cancel hR (by
          rw [e3, hE, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_one, Nat.pow_zero, Nat.mul_one,
            Nat.mul_assoc])⟩
      · exact J3'.good q hq⟩
  refine WP.seq (WP.mono (c3.mont (o := 12) (a := 5) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [J3.rr]; exact hRR))
    fun s₄ ⟨⟨c4, lt4, e4, v4, o4⟩, k4⟩ => ?_)
  rw [J3.y, J3.rr] at e4
  have J4' := J3.after (m' := s₄.mem) (o := 12) (by decide) (by decide) v4
  have J4 : JInv s₄.mem B w N G Y RR [(4, 0, 1), (1, 1, 0), (0, 0, 0)] :=
    ⟨J4'.rr, J4'.g, J4'.y, J4'.one, fun q hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · show JGood s₄.mem B w N G Y RR 4 0 1
        exact ⟨lt4, fun hE => VG.Proof.Bignum.mont_cancel hR (by
          rw [e4, hE, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_one, Nat.pow_zero, Nat.one_mul,
            Nat.mul_assoc])⟩
      · exact J4'.good q hq⟩
  have O4 : WinO B w s.mem s₄.mem := (((arrO o1 (by decide) (by decide)).trans o2).trans o3).trans o4
  have K4 := (((k1.trans k2).trans k3).trans k4)
  -- The other entries.
  have K4' : Keep jtRegs s s₄ := K4.mono (by decide)
  refine WP.seq (WP.mono (montStepAcc (k := 2) (k1 := 1) (i1 := 1) (j1 := 0) (k2 := 1) (i2 := 1)
    (j2 := 0) c4 hodd O4 K4' J4 (by decide) (by decide) (by decide)) fun s5 ⟨c5, O5, J5, K5⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 3) (k1 := 2) (i1 := 2) (j1 := 0) (k2 := 1) (i2 := 1)
    (j2 := 0) c5 hodd O5 K5 J5 (by decide) (by decide) (by decide)) fun s6 ⟨c6, O6, J6, K6⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 5) (k1 := 4) (i1 := 0) (j1 := 1) (k2 := 1) (i2 := 1)
    (j2 := 0) c6 hodd O6 K6 J6 (by decide) (by decide) (by decide)) fun s7 ⟨c7, O7, J7, K7⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 6) (k1 := 4) (i1 := 0) (j1 := 1) (k2 := 2) (i2 := 2)
    (j2 := 0) c7 hodd O7 K7 J7 (by decide) (by decide) (by decide)) fun s8 ⟨c8, O8, J8, K8⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 7) (k1 := 4) (i1 := 0) (j1 := 1) (k2 := 3) (i2 := 3)
    (j2 := 0) c8 hodd O8 K8 J8 (by decide) (by decide) (by decide)) fun s9 ⟨c9, O9, J9, K9⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 8) (k1 := 4) (i1 := 0) (j1 := 1) (k2 := 4) (i2 := 0)
    (j2 := 1) c9 hodd O9 K9 J9 (by decide) (by decide) (by decide)) fun s10 ⟨c10, O10, J10, K10⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 9) (k1 := 8) (i1 := 0) (j1 := 2) (k2 := 1) (i2 := 1)
    (j2 := 0) c10 hodd O10 K10 J10 (by decide) (by decide) (by decide)) fun s11 ⟨c11, O11, J11, K11⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 10) (k1 := 8) (i1 := 0) (j1 := 2) (k2 := 2) (i2 := 2)
    (j2 := 0) c11 hodd O11 K11 J11 (by decide) (by decide) (by decide)) fun s12 ⟨c12, O12, J12, K12⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 11) (k1 := 8) (i1 := 0) (j1 := 2) (k2 := 3) (i2 := 3)
    (j2 := 0) c12 hodd O12 K12 J12 (by decide) (by decide) (by decide)) fun s13 ⟨c13, O13, J13, K13⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 12) (k1 := 8) (i1 := 0) (j1 := 2) (k2 := 4) (i2 := 0)
    (j2 := 1) c13 hodd O13 K13 J13 (by decide) (by decide) (by decide)) fun s14 ⟨c14, O14, J14, K14⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 13) (k1 := 12) (i1 := 0) (j1 := 3) (k2 := 1) (i2 := 1)
    (j2 := 0) c14 hodd O14 K14 J14 (by decide) (by decide) (by decide)) fun s15 ⟨c15, O15, J15, K15⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 14) (k1 := 12) (i1 := 0) (j1 := 3) (k2 := 2) (i2 := 2)
    (j2 := 0) c15 hodd O15 K15 J15 (by decide) (by decide) (by decide)) fun s16 ⟨c16, O16, J16, K16⟩ => ?_)
  refine WP.seq (WP.mono (montStepAcc (k := 15) (k1 := 12) (i1 := 0) (j1 := 3) (k2 := 3) (i2 := 3)
    (j2 := 0) c16 hodd O16 K16 J16 (by decide) (by decide) (by decide)) fun s17 ⟨c17, O17, J17, K17⟩ => ?_)
  -- `a := T_0`.
  refine WP.mono (Win.copy_ok c17 (o := 6) (a := 8) (by decide) (by decide) (by decide)) fun t ⟨⟨ta, to⟩, kt⟩ => ?_
  have hv : ∀ j < 24, j ≠ 2 → j ≠ 3 → j ≠ 6 → A t.mem B w j = A s17.mem B w j :=
    fun j hj _ _ h6 => arr_out to hj h6 hn
  have Jt := J17.after (m' := t.mem) (o := 6) (by decide) (by decide) hv
  refine ⟨⟨c17.of kt (by decide) (arrO to (by decide) (by decide)), ?_, Jt.one, by rw [ta, hv 8 (by decide)
    (by decide) (by decide) (by decide)], Jt⟩, ?_⟩
  · exact O17.trans (arrO to (by decide) (by decide))
  · exact (K17.trans kt).mono (by decide)

theorem jDone_mem {i j : Nat} (hi : i < 4) (hj : j < 4) : (i + 4 * j, i, j) ∈ jDone := by
  have key : ∀ i < 4, ∀ j < 4, (i + 4 * j, i, j) ∈ jDone := by decide
  exact key i hi j hj

theorem jDone_lt {m : Mem} {B : Addr} {w N G Y RR : Nat} (h : JInv m B w N G Y RR jDone) :
    ∀ k < 16, A m B w (8 + k) < N := fun k hk => by
  have := (h.good _ (jDone_mem (i := k % 4) (j := k / 4) (Nat.mod_lt _ (by decide)) (by omega))).1
  rwa [show k % 4 + 4 * (k / 4) = k by omega] at this

/-- The digit of a joint window: `s7`'s top two bits, and its bits 54–55 times 4. -/
theorem digit_eq (x : BitVec 64) :
    (x >>> 62) + (((x >>> 54) &&& 3#64) <<< 2) =
      BitVec.ofNat 64 (x.toNat / 2 ^ 62 + 4 * (x.toNat / 2 ^ 54 % 4)) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have e3 : (3#64).toNat = 2 ^ 2 - 1 := rfl
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_ushiftRight, e3, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega_arith

/-- A square of `a` in the context, for powers of `G` and `Y`. -/
theorem sq2_ok {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) (hodd : N % 2 = 1)
    (ha : A s.mem B w 6 < N) {G Y c1 c2 : Nat} :
    WP isa (ModExp.sqrOp 6 6 5) s fun t =>
      (WCtx t B Z w N ∧ WinO B w s.mem t.mem ∧ Fix B w s.mem t.mem ∧ A t.mem B w 6 < N ∧
        (A s.mem B w 6 % N = G ^ c1 * Y ^ c2 * 2 ^ (64 * w) % N →
          A t.mem B w 6 % N = G ^ (c1 + c1) * Y ^ (c2 + c2) * 2 ^ (64 * w) % N)) ∧ Keep sqRegs s t := by
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  exact WP.mono (h.sqr (o := 6) (a := 6) (p := 5) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha)
    fun t ⟨⟨ct, lt, e, v, o⟩, k⟩ =>
    ⟨⟨ct, o, fun j hj h2 h3 h5 h6 => v j hj h2 h3 h5 h6, lt, fun hA => mont_pow2 hR hA hA e⟩, k⟩

/-- The registers a joint window writes. -/
def jwRegs : List Reg := Pub.montRegs ++ sqRegs ++ selectRegs ++ [.a1, .t3, .s7]

/-- `jointWindow`: two squares, then `a := a T_(d1 + 4 d2)`, for `d1` the top
two bits of `s7` and `d2` its bits 54–55. -/
theorem jointWindow_ok {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) (hodd : N % 2 = 1)
    (ha : A s.mem B w 6 < N) (htab : ∀ k < 16, A s.mem B w (8 + k) < N) {G Y c1 c2 : Nat} :
    WP isa jointWindow s fun t =>
      (WCtx t B Z w N ∧ WinO B w s.mem t.mem ∧ Fix B w s.mem t.mem ∧ A t.mem B w 6 < N ∧
        t.gpr .s7 = s.gpr .s7 <<< 2 ∧
        (A s.mem B w 6 % N = G ^ c1 * Y ^ c2 * 2 ^ (64 * w) % N →
          (∀ i < 4, ∀ j < 4, A s.mem B w (8 + (i + 4 * j)) % N = G ^ i * Y ^ j * 2 ^ (64 * w) % N) →
          A t.mem B w 6 % N = G ^ (4 * c1 + (s.gpr .s7).toNat / 2 ^ 62) *
            Y ^ (4 * c2 + (s.gpr .s7).toNat / 2 ^ 54 % 4) * 2 ^ (64 * w) % N)) ∧ Keep jwRegs s t := by
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  unfold jointWindow
  refine WP.seq (WP.mono (sq2_ok h hodd ha (G := G) (Y := Y) (c1 := c1) (c2 := c2))
    fun s₁ ⟨⟨cs1, o1, f1, l1, e1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (sq2_ok cs1 hodd l1 (G := G) (Y := Y) (c1 := c1 + c1) (c2 := c2 + c2))
    fun s₂ ⟨⟨cs2, o2, f2, l2, e2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have f12 := f1.trans f2
  have hx := (s.gpr .s7).isLt
  have hd1 : (s.gpr .s7).toNat / 2 ^ 62 < 4 := by omega_arith
  have hd2 : (s.gpr .s7).toNat / 2 ^ 54 % 4 < 4 := Nat.mod_lt _ (by decide)
  have hd : (s.gpr .s7).toNat / 2 ^ 62 + 4 * ((s.gpr .s7).toNat / 2 ^ 54 % 4) < 16 := by omega
  refine WP.seq (WP.mono (WP.keep [.a1, .t3] (Q := fun t =>
      t.gpr .a1 = BitVec.ofNat 64 ((s.gpr .s7).toNat / 2 ^ 62 + 4 * ((s.gpr .s7).toNat / 2 ^ 54 % 4)) ∧
        t.mem = s₂.mem)
    (by brun [digit_eq, k12.gpr (r := .s7) (by decide)]) (by rfl) (by rfl)) fun s₃ ⟨⟨a1, m3⟩, k3⟩ => ?_)
  have cs3 := cs2.regs k3 (by decide) m3
  refine WP.seq (WP.mono (select_ok cs3 a1 hd) fun s₄ ⟨⟨a5, v4, cs4, o4⟩, k4⟩ => ?_)
  have A6 : A s₄.mem B w 6 = A s₂.mem B w 6 := by rw [v4 6 (by decide) (by decide) (by decide), m3]
  rw [m3, f12 _ (by omega) (by omega) (by omega) (by omega) (by omega)] at a5
  refine WP.seq (WP.mono (cs4.mont (o := 6) (a := 6) (b := 5) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [a5]; exact htab _ hd))
    fun s₅ ⟨⟨cs5, l5, e5, v5, o5⟩, k5⟩ => ?_)
  refine WP.mono (WP.keep [.s7] (Q := fun t => t.gpr .s7 = s₅.gpr .s7 <<< 2 ∧ t.mem = s₅.mem)
    (by brun) (by rfl) (by rfl)) fun t ⟨⟨a7, mt⟩, kt⟩ =>
      ⟨⟨cs5.regs kt (by decide) mt, ?_, ?_, by rw [mt]; exact l5, ?_, ?_⟩, ?_⟩
  · rw [mt]
    exact ((o1.trans o2).trans (by rw [← m3]; exact o4)).trans o5
  · intro j hj h2 h3 h5 h6
    rw [mt, v5 j hj h2 h3 h6, v4 j hj h3 h5, m3]
    exact f12 j hj h2 h3 h5 h6
  · rw [a7, k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide), k12.gpr (by decide)]
  · intro hA hT
    rw [mt]
    rw [A6] at e5
    have := mont_pow2 hR (e2 (e1 hA)) (by rw [a5]; exact hT _ hd1 _ hd2) e5
    rw [this, show c1 + c1 + (c1 + c1) + (s.gpr .s7).toNat / 2 ^ 62 = 4 * c1 + (s.gpr .s7).toNat / 2 ^ 62 by omega,
      show c2 + c2 + (c2 + c2) + (s.gpr .s7).toNat / 2 ^ 54 % 4 = 4 * c2 + (s.gpr .s7).toNat / 2 ^ 54 % 4 by omega]
  · exact ((((k12.trans k3).trans k4).trans k5).trans kt).mono (by decide)

/-- A byte's four 2-bit digits, most significant first, after `c`. -/
theorem byte_digits (c b : Nat) :
    4 * (4 * (4 * (4 * c + b / 64) + b / 16 % 4) + b / 4 % 4) + b % 4 = 256 * c + b := by
  omega

/-- The first word of a byte pair: `b1` at the top, `b2` below it. -/
theorem pair_eq {b1 b2 : Nat} (h1 : b1 < 256) (h2 : b2 < 256) :
    (BitVec.ofNat 64 b1 <<< 56 + (BitVec.ofNat 64 b2 <<< 56) >>> 8).toNat = b1 * 2 ^ 56 + b2 * 2 ^ 48 := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_arith

theorem digits0 {x b1 b2 : Nat} (hx : x = b1 * 2 ^ 56 + b2 * 2 ^ 48) (h2 : b2 < 256) :
    x / 2 ^ 62 = b1 / 64 ∧ x / 2 ^ 54 % 4 = b2 / 64 := by subst hx; omega_arith

theorem digits1 {v : BitVec 64} {b1 b2 : Nat} (hx : v.toNat = b1 * 2 ^ 56 + b2 * 2 ^ 48)
    (h2 : b2 < 256) : (v <<< 2).toNat / 2 ^ 62 = b1 / 16 % 4 ∧ (v <<< 2).toNat / 2 ^ 54 % 4 = b2 / 16 % 4 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hx]; omega_arith

theorem digits2 {v : BitVec 64} {b1 b2 : Nat} (hx : v.toNat = b1 * 2 ^ 56 + b2 * 2 ^ 48)
    (h2 : b2 < 256) : (v <<< 2 <<< 2).toNat / 2 ^ 62 = b1 / 4 % 4 ∧ (v <<< 2 <<< 2).toNat / 2 ^ 54 % 4 = b2 / 4 % 4 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hx]; omega_arith

theorem digits3 {v : BitVec 64} {b1 b2 : Nat} (hx : v.toNat = b1 * 2 ^ 56 + b2 * 2 ^ 48)
    (h2 : b2 < 256) :
    (v <<< 2 <<< 2 <<< 2).toNat / 2 ^ 62 = b1 % 4 ∧ (v <<< 2 <<< 2 <<< 2).toNat / 2 ^ 54 % 4 = b2 % 4 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, hx]; omega_arith

/-- After the joint table (`t₀`), with `c1` and `c2` of the exponents scanned. -/
structure JRun (s₀ t₀ u : State) (B : Addr) (Z w N G Y RR c1 c2 : Nat) : Prop where
  ctx : WCtx u B Z w N
  out : WinO B w s₀.mem u.mem
  fix : Fix B w t₀.mem u.mem
  lt : A u.mem B w 6 < N
  pw : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A u.mem B w 6 % N = G ^ c1 * Y ^ c2 * 2 ^ (64 * w) % N
  keep : Keep (jtRegs ++ jwRegs ++ [.s9, .s10]) s₀ u

/-- The two bytes of a joint step into `s7`. -/
theorem lbu2_ok {u : State} {D : Addr} {i : Nat} (h9 : u.gpr .s9 = off D i)
    (hrd1 : InRegions (u.rd ++ u.wr) (off D i) 1) (hrd2 : InRegions (u.rd ++ u.wr) (off D (i + 32)) 1) :
    WP isa (.block [.load .b .s7 .s9 0, .shift .sll .d .s7 .s7 56, .load .b .t3 .s9 32,
        .shift .sll .d .t3 .t3 56, .shift .srl .d .t3 .t3 8, .add .s7 .s7 .t3, .addi .s9 .s9 1]) u fun t =>
      (t.gpr .s7 = BitVec.ofNat 64 (u.mem (off D i)).toNat <<< 56 +
          (BitVec.ofNat 64 (u.mem (off D (i + 32))).toNat <<< 56) >>> 8 ∧
        t.gpr .s9 = off D (i + 1) ∧ t.mem = u.mem) ∧ Keep [.s7, .t3, .s9] u t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [h9, hrd1, hrd2, read_byte64, add_ofNat_zero]

/-- The table's entries, from what the windows keep of it. -/
theorem jtab_of {t₀ : State} {m : Mem} {B : Addr} {w N G Y RR : Nat} (htab : JInv t₀.mem B w N G Y RR jDone)
    (hf : Fix B w t₀.mem m) :
    (∀ k < 16, A m B w (8 + k) < N) ∧ (RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N →
      ∀ i < 4, ∀ j < 4, A m B w (8 + (i + 4 * j)) % N = G ^ i * Y ^ j * 2 ^ (64 * w) % N) := by
  refine ⟨fun k hk => ?_, fun hE i hi j hj => ?_⟩
  · rw [hf (8 + k) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact jDone_lt htab k hk
  · rw [hf (8 + (i + 4 * j)) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact (htab.good _ (jDone_mem hi hj)).2 hE

theorem jw_jrun {r : Reg} (h : r ∈ jwRegs) : r ∈ jtRegs ++ jwRegs ++ ([.s9, .s10] : List Reg) :=
  List.mem_append_left _ (List.mem_append_right _ h)

/-- `jointByte`: the four joint windows of the bytes `b1` at `s9` and `b2` 32
bytes on, `c1 := 256 c1 + b1` and `c2 := 256 c2 + b2`. -/
theorem jointByte_ok {s₀ t₀ u : State} {B D : Addr} {Z w N G Y RR c1 c2 i : Nat} (hodd : N % 2 = 1)
    (htab : JInv t₀.mem B w N G Y RR jDone) (h : JRun s₀ t₀ u B Z w N G Y RR c1 c2) (h9 : u.gpr .s9 = off D i)
    (hrd1 : InRegions (u.rd ++ u.wr) (off D i) 1) (hrd2 : InRegions (u.rd ++ u.wr) (off D (i + 32)) 1) :
    WP isa jointByte u fun t =>
      JRun s₀ t₀ t B Z w N G Y RR (256 * c1 + (u.mem (off D i)).toNat) (256 * c2 + (u.mem (off D (i + 32))).toNat) ∧
        WinO B w u.mem t.mem ∧ t.gpr .s9 = off D (i + 1) ∧ t.gpr .s10 = u.gpr .s10 := by
  generalize hb1 : (u.mem (off D i)).toNat = b1
  generalize hb2 : (u.mem (off D (i + 32))).toNat = b2
  have h1 : b1 < 256 := by rw [← hb1]; exact (u.mem (off D i)).isLt
  have h2 : b2 < 256 := by rw [← hb2]; exact (u.mem (off D (i + 32))).isLt
  unfold jointByte
  refine WP.seq (WP.mono (lbu2_ok h9 hrd1 hrd2) fun u₁ ⟨⟨a7, a9, m1⟩, k1⟩ => ?_)
  rw [hb1, hb2] at a7
  have hv : (u₁.gpr .s7).toNat = b1 * 2 ^ 56 + b2 * 2 ^ 48 := by rw [a7]; exact pair_eq h1 h2
  have c1' := h.ctx.regs k1 (by decide) m1
  have f1 : Fix B w t₀.mem u₁.mem := by rw [m1]; exact h.fix
  have d0 := digits0 hv h2
  refine WP.seq (WP.mono (jointWindow_ok c1' hodd (by rw [m1]; exact h.lt) (jtab_of htab f1).1
    (G := G) (Y := Y) (c1 := c1) (c2 := c2)) fun u₂ ⟨⟨c2', o2, f2, l2, s2, e2⟩, k2⟩ => ?_)
  rw [d0.1, d0.2] at e2
  have d1 := digits1 hv h2
  rw [← s2] at d1
  refine WP.seq (WP.mono (jointWindow_ok c2' hodd l2 (jtab_of htab (f1.trans f2)).1
    (G := G) (Y := Y) (c1 := 4 * c1 + b1 / 64) (c2 := 4 * c2 + b2 / 64)) fun u₃ ⟨⟨c3', o3, f3, l3, s3, e3⟩, k3⟩ => ?_)
  rw [d1.1, d1.2] at e3
  have d2 := digits2 hv h2
  rw [← s2, ← s3] at d2
  refine WP.seq (WP.mono (jointWindow_ok c3' hodd l3 (jtab_of htab ((f1.trans f2).trans f3)).1
    (G := G) (Y := Y) (c1 := 4 * (4 * c1 + b1 / 64) + b1 / 16 % 4) (c2 := 4 * (4 * c2 + b2 / 64) + b2 / 16 % 4))
    fun u₄ ⟨⟨c4', o4, f4, l4, s4, e4⟩, k4⟩ => ?_)
  rw [d2.1, d2.2] at e4
  have d3 := digits3 hv h2
  rw [← s2, ← s3, ← s4] at d3
  refine WP.mono (jointWindow_ok c4' hodd l4 (jtab_of htab (((f1.trans f2).trans f3).trans f4)).1
    (G := G) (Y := Y) (c1 := 4 * (4 * (4 * c1 + b1 / 64) + b1 / 16 % 4) + b1 / 4 % 4)
    (c2 := 4 * (4 * (4 * c2 + b2 / 64) + b2 / 16 % 4) + b2 / 4 % 4))
    fun t ⟨⟨c5', o5, f5, l5, _, e5⟩, k5⟩ => ⟨⟨c5', ?_, ?_, l5, fun hE => ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [m1] at o2; exact (((h.out.trans o2).trans o3).trans o4).trans o5
  · exact f1.trans (f2.trans (f3.trans (f4.trans f5)))
  · rw [d3.1, d3.2] at e5
    have T : ∀ {m : Mem}, Fix B w t₀.mem m →
        ∀ i < 4, ∀ j < 4, A m B w (8 + (i + 4 * j)) % N = G ^ i * Y ^ j * 2 ^ (64 * w) % N :=
      fun hf => (jtab_of htab hf).2 hE
    have p1 := e2 (by rw [m1]; exact h.pw hE) (T f1)
    have p2 := e3 p1 (T (f1.trans f2))
    have p3 := e4 p2 (T ((f1.trans f2).trans f3))
    have p4 := e5 p3 (T (((f1.trans f2).trans f3).trans f4))
    exact p4.trans (by rw [byte_digits, byte_digits])
  · exact Keep.within (Keep.within (Keep.within (Keep.within (Keep.within h.keep k1 (by decide)) k2
      fun _ => jw_jrun) k3 fun _ => jw_jrun) k4 fun _ => jw_jrun) k5 fun _ => jw_jrun
  · rw [m1] at o2; exact ((o2.trans o3).trans o4).trans o5
  · rw [k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), a9]
  · rw [k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide)]

/-- The joint loop and the conversion out of Montgomery form: `G^U1 Y^U2 mod N`
into array 4, for `U1` the `L ≥ 1` bytes at `D` (`s9`, `s10`) and `U2` those
32 bytes on, apart from the working space. -/
theorem jointLoop_ok {s t₀ : State} {B D : Addr} {Z w N G Y RR L : Nat} (hN : 2 ≤ N) (hodd : N % 2 = 1)
    (htab : JInv t₀.mem B w N G Y RR jDone) (h : JRun s t₀ t₀ B Z w N G Y RR 0 0)
    (h9 : t₀.gpr .s9 = off D 0) (h10 : t₀.gpr .s10 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L < 2 ^ 63)
    (hrd : ∀ i < L + 32, InRegions (t₀.rd ++ t₀.wr) (off D i) 1)
    (hsep : ∀ i < L + 32, ∀ x, VG.Proof.Bignum.ofs B x < slot w 24 → off D i ≠ x) :
    WP isa (.seq (.loop (.seq jointByte (.block [.addi .s10 .s10 (-1)])) (.nonzero .s10)) (montOp 4 6 7)) t₀
      fun t =>
      ((RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N →
          A t.mem B w 4 = G ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt t₀.mem D L) *
            Y ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt t₀.mem (off D 32) L) % N) ∧
        WinO B w s.mem t.mem) ∧ Keep (jtRegs ++ jwRegs ++ ([.s9, .s10] : List Reg)) s t := by
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have hn := h.ctx.nw
  have hmem : ∀ {u : State}, WinO B w t₀.mem u.mem → ∀ i < L + 32, u.mem (off D i) = t₀.mem (off D i) :=
    fun hu i hi => by
      refine hu _ ?_
      have := slot_lt (w := w) (show 1 < 24 by decide)
      have e24 := slot24 w
      right
      by_contra hc
      exact hsep i hi (off D i) (by simp only [VG.Proof.Bignum.ofs] at hc ⊢; omega_arith) rfl
  let Inv : Nat → State → Prop := fun i u =>
    JRun s t₀ u B Z w N G Y RR (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t₀.mem D i))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t₀.mem (off D 32) i)) ∧ WinO B w t₀.mem u.mem ∧ u.gpr .s9 = off D i
  refine WP.seq (WP.mono (wp_countdown (cnt := .s10) (N := L) (by omega_arith) (by omega_arith) Inv
    (fun i hi u ⟨hu, ou, u9⟩ _ => ?_) ⟨by simpa [Spec.Rsa.bytesAt, Spec.Rsa.os2ip] using h,
      Outside.refl _ _ _ _, h9⟩ h10) fun u ⟨hu, _, _⟩ => ?_)
  · have hrd' : ∀ j < L + 32, InRegions (u.rd ++ u.wr) (off D j) 1 := fun j hj => by
      rw [hu.keep.2.1, hu.keep.2.2, ← h.keep.2.1, ← h.keep.2.2]; exact hrd j hj
    refine WP.seq (WP.mono (jointByte_ok hodd htab hu u9 (hrd' i (by omega)) (hrd' (i + 32) (by omega)))
      fun u₁ ⟨hu₁, o₁, a9, a10⟩ => ?_)
    refine WP.mono (dec_ok u₁ .s10) fun u₂ e => ?_
    subst e
    have ou₁ : WinO B w t₀.mem u₁.mem := ou.trans o₁
    refine ⟨⟨⟨hu₁.ctx.regs (Keep.write _ _ _) (by decide) (by rw [mem_write]), by rw [mem_write]; exact hu₁.out,
        by rw [mem_write]; exact hu₁.fix, by rw [mem_write]; exact hu₁.lt, fun hE => ?_,
        Keep.within hu₁.keep (Keep.write _ _ _) (by decide)⟩, by rw [mem_write]; exact ou₁, by gsimp; exact a9⟩,
      by gsimp; rw [a10]⟩
    rw [mem_write, hu₁.pw hE, hmem ou i (by omega), hmem ou (i + 32) (by omega), Pub.bytesAt_succ, Pub.bytesAt_succ,
      VG.Proof.Rsa.os2ip_snoc, VG.Proof.Rsa.os2ip_snoc, off_off, Nat.add_comm 32 i]
  -- Out of Montgomery form.
  have t7 : A u.mem B w 7 = 1 := by
    rw [hu.fix 7 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact htab.one
  refine WP.mono (hu.ctx.mont (o := 4) (a := 6) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [t7]; omega_arith)) fun t ⟨⟨_, lt, e, _, o⟩, k⟩ =>
    ⟨⟨fun hE => ?_, hu.out.trans o⟩, Keep.within hu.keep k fun _ h => jw_jrun (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ h)))⟩
  rw [t7, Nat.mul_one] at e
  refine (Nat.mod_eq_of_lt lt).symm.trans ?_
  exact VG.Proof.Bignum.mont_cancel hR (by rw [e, hu.pw hE])

end Joint

theorem parr_win {L : Lay} {m m' : Mem} (h : Outside L.S (slot L.wp 1) (23 * (8 * (L.wp + 2))) m m') :
    PArr L m m' :=
  PArr.of h (Nat.le_refl _) (by simp only [Lay.slot_eq]; omega)

/-- The registers `combine`'s first block writes. -/
def headRegs : List Reg := enterRegs ++ [.s0, .s1, .s2, .s3, .t1] ++ [.s7, .t2, .s8] ++ [.s9] ++ ptrRegs

/-- `combine`'s first block: into the P space, `-p⁻¹ mod 2⁶⁴` into `t1`, the
buffer into `s9` and g's octets into `s7`. -/
theorem combHead_ok {s : State} {L : Lay} {key sig : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hp0 : arrP s.mem L 0 = p) (hpo : p % 2 = 1) :
    WP isa (.block (enterP ++ Precompute.minv ++ ptrBuf ++ ([.addi .s9 .s7 0] : List Instr) ++ ptrG)) s fun t =>
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

theorem parr_q (L : Lay) : slot L.wp 1 + 27 * (8 * (L.wp + 2)) ≤ L.qOff := by
  simp only [Lay.qOff, Lay.slot_eq]; omega

theorem body_le {L : Lay} (hL : L.Ok) : 256 + (L.Z - 256) ≤ L.Z := by have := hL.z256; omega

theorem ql2_le {L : Lay} (hL : L.Ok) : L.ql + L.ql ≤ 2 * L.pl := by
  rcases hL.pl with e | e | e <;> rcases hL.ql with f | f | f <;> omega

theorem comb_sub1 {L : Lay} : L.pl + L.ql + L.pl ≤ 3 * L.pl + L.ql := by omega
theorem comb_sub2 {L : Lay} : 2 * L.pl + L.ql + L.pl ≤ 3 * L.pl + L.ql := by omega

/-- `loadArr`'s working space, `a7` back to array 0. -/
theorem Env.load {s t : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) (k : Keep loadRegs s t)
    (a7 : t.gpr .a7 = off B (slot w 0)) : Env t B Z w :=
  ⟨h.hs.congr k.2.2, a7, (k.gpr (by decide)).trans h.s5, (k.gpr (by decide)).trans h.t0, h.w2, h.w48, h.hZ⟩

/-- Three programs, then `R`. -/
theorem wp_seq3 {a b c R : Prog isa} {s : State} {P Q : State → Prop} (h : WP isa (.seq a (.seq b c)) s P)
    (hc : ∀ t, P t → WP isa R t Q) : WP isa (.seq a (.seq b (.seq c R))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h1 => WP.assoc (WP.seq (WP.mono h1 hc)))

/-- Four programs, then `R`. -/
theorem wp_seq4 {a b c d R : Prog isa} {s : State} {P Q : State → Prop}
    (h : WP isa (.seq a (.seq b (.seq c d))) s P) (hc : ∀ t, P t → WP isa R t Q) :
    WP isa (.seq a (.seq b (.seq c (.seq d R)))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h1 => wp_seq3 h1 hc)

/-- The registers `combG_ok`'s code writes. -/
def gRegs : List Reg := [.s8] ++ loadRegs ++ ptrRegs

/-- `combine`'s g: `p_len` into `s8`, g into array 4, then y's octets into
`s7` and `p_len` into `s8`. -/
theorem combG_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key sig)
    (hk : Src s L key (3 * L.pl + L.ql)) (hin : InP s L) (h7 : s.gpr .s7 = off key (L.pl + L.ql)) :
    WP isa (.seq (.block (getP .s8)) (.seq (loadArr 4) (.block ptrY))) s fun t =>
      (arrP t.mem L 4 = gOf s.mem L key ∧ InP t L ∧ Outside L.S (slot L.wp 4) (8 * (L.wp + 1)) s.mem t.mem ∧
        t.gpr .s7 = off key (2 * L.pl + L.ql) ∧ t.gpr .s8 = BitVec.ofNat 64 L.pl) ∧ Keep gRegs s t := by
  have hw := hL.wp_ge
  have hpl : 128 ≤ L.pl := by rcases hL.pl with e | e | e <;> omega
  have hw8 := hL.wp_eq
  have e : ∀ j, slot L.wp j = 256 + j * (8 * (L.wp + 2)) := fun _ => rfl
  have e1 := e 1; have e4 := e 4; have e28 := e 28
  have hqZ : L.qOff + 1600 ≤ L.Z := by have hbe := hL.buf_end; simp only [Lay.bOff] at hbe; omega_arith
  have hg := hk.sub (o := L.pl + L.ql) (k := L.pl) comb_sub1
  refine WP.seq (WP.mono (getP_ok hs hL hr .s8) fun s₂ ⟨⟨a8, m2⟩, k2⟩ => ?_)
  refine WP.seq (WP.mono (loadArr_ok (hin.env.keep k2) (j := 4) (N := off key (L.pl + L.ql)) (by decide)
      (by rw [k2.gpr (by decide), h7]; exact (BitVec.add_zero _).symm) a8 (by omega) (by omega)
      (by rw [k2.2.1, k2.2.2]; exact hg.rd) (fun i hi x hx => hg.sep i hi x (by omega_arith)))
    fun s₃ ⟨⟨v4, _, o3, a73⟩, k3⟩ => ?_)
  rw [m2] at v4 o3
  have en3 := (hin.env.keep k2).load k3 a73
  have k13 := k2.trans k3
  have pa3 : PArr L s.mem s₃.mem := PArr.of o3 (slot_mono (show 1 ≤ 4 by decide)) (by omega)
  exact WP.mono (ptrY_ok (hs.congr k13.2.2) hL (hr.keep k13 (pa3.pbody.body hL))) fun t ⟨⟨b7, b8, m4⟩, k4⟩ =>
    ⟨⟨by rw [arrP, m4]; exact v4, ⟨en3.keep k4, ((k13.trans k4).gpr (by decide)).trans hin.s6⟩,
      by rw [m4]; exact o3, b7, b8⟩, k13.trans k4⟩

/-- The registers `combT_ok`'s code writes. -/
def tRegs : List Reg := loadRegs ++ copyRegs ++ jtRegs ++ [.s10]

/-- `combine`'s table: y into array 5, `R² mod p` into array 1, the joint
table, then `q_len` into `s10`: the state the joint windows start from. -/
theorem combT_ok {s : State} {L : Lay} {key sig : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hk : Src s L key (3 * L.pl + L.ql)) (hin : InP s L) (hi : PInv s L)
    (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1) (hrr : arrP s.mem L 24 = 2 ^ (128 * L.wp) % p)
    (h7 : s.gpr .s7 = off key (2 * L.pl + L.ql)) (h8 : s.gpr .s8 = BitVec.ofNat 64 L.pl) :
    WP isa (.seq (loadArr 5) (.seq (copy 1 24) (.seq jointTable (.block (getQ .s10))))) s fun t =>
      (JInv t.mem L.S L.wp p (arrP s.mem L 4) (yOf s.mem L key) (2 ^ (128 * L.wp) % p) jDone ∧
        JRun t t t L.S L.qOff L.wp p (arrP s.mem L 4) (yOf s.mem L key) (2 ^ (128 * L.wp) % p) 0 0 ∧
        InP t L ∧ Outside L.S (slot L.wp 1) (23 * (8 * (L.wp + 2))) s.mem t.mem ∧
        t.gpr .s10 = BitVec.ofNat 64 L.ql) ∧ Keep tRegs s t := by
  have hw := hL.wp_ge
  have hpl : 128 ≤ L.pl := by rcases hL.pl with e | e | e <;> omega
  have hw8 := hL.wp_eq
  have e : ∀ j, slot L.wp j = 256 + j * (8 * (L.wp + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e5 := e 5; have e24 := e 24; have e28 := e 28
  have hq28 : L.qOff = slot L.wp 28 := rfl
  have hqZ : L.qOff + 1600 ≤ L.Z := by have hbe := hL.buf_end; simp only [Lay.bOff] at hbe; omega_arith
  have hy := hk.sub (o := 2 * L.pl + L.ql) (k := L.pl) comb_sub2
  -- y into array 5.
  refine WP.seq (WP.mono (loadArr_ok hin.env (j := 5) (N := off key (2 * L.pl + L.ql)) (by decide)
      (by rw [h7]; exact (BitVec.add_zero _).symm) h8 (by omega) (by omega)
      hy.rd (fun i hi x hx => hy.sep i hi x (by omega_arith)))
    fun s₅ ⟨⟨v5, _, o5, a75⟩, k5⟩ => ?_)
  have en5 := hin.env.load k5 a75
  -- `R² mod p` into array 1.
  refine WP.seq (WP.mono (copy_ok en5 (o := 1) (a := 24) (by decide) (by decide) (by decide))
    fun s₆ ⟨⟨v1, o6⟩, k6⟩ => ?_)
  have en6 := en5.keep k6
  have w6 : Outside L.S (slot L.wp 1) (23 * (8 * (L.wp + 2))) s.mem s₆.mem :=
    (o5.mono (by omega) (by omega)).trans (o6.mono (by omega) (by omega))
  have A0 : arrP s₆.mem L 0 = p := by rw [arrP, w6.wordsVal (by omega) (by omega_arith)]; exact hp0
  have W0 : word s₆.mem L.S (slot L.wp 0) = word s.mem L.S (slot L.wp 0) := w6.word (by omega) (by omega_arith)
  have A1 : arrP s₆.mem L 1 = 2 ^ (128 * L.wp) % p := by
    rw [arrP, wordsVal_congr (m := s₅.mem) (d := slot L.wp 24) fun i hi => v1 i (by omega),
      o5.wordsVal (by omega) (by omega_arith)]
    exact hrr
  have A4 : arrP s₆.mem L 4 = arrP s.mem L 4 := by
    rw [arrP, o6.wordsVal (by omega) (by omega_arith), o5.wordsVal (by omega) (by omega_arith)]
  have A5 : arrP s₆.mem L 5 = yOf s.mem L key := by
    rw [arrP, o6.wordsVal (by omega) (by omega_arith)]; exact v5
  have I6 : ((word s₆.mem L.S (slot L.wp 0)).toNat * (s₆.gpr .t1).toNat + 1) % 2 ^ 64 = 0 := by
    rw [W0, (k5.trans k6).gpr (by decide)]; exact hi
  have c6 : Win.WCtx s₆ L.S L.qOff L.wp p :=
    ⟨en6.hs, en6.w2, by have := en6.w48; omega, by omega, en6.a7, en6.s5, en6.t0, I6, A0⟩
  -- The joint table.
  refine WP.seq (WP.mono (jointTable_ok c6 hp hpo
    (by show arrP s₆.mem L 1 < p; rw [A1]; exact Nat.mod_lt _ (by omega)))
    fun u₁ ⟨⟨c7, o7, _, a6, J⟩, k7⟩ => ?_)
  rw [show Win.A s₆.mem L.S L.wp 4 = arrP s.mem L 4 from A4, show Win.A s₆.mem L.S L.wp 5 = yOf s.mem L key from A5,
    show Win.A s₆.mem L.S L.wp 1 = 2 ^ (128 * L.wp) % p from A1] at J
  have k57 := (k5.trans k6).trans k7
  refine WP.mono (getQ_ok (hs.congr k57.2.2) hL
    (hr.keep k57 ((parr_win (w6.trans o7)).pbody.body hL)) .s10) fun u₂ ⟨⟨a10, mq⟩, kq⟩ => ?_
  have g0 := J.good _ (show (0, 0, 0) ∈ jDone by decide)
  refine ⟨⟨by rw [mq]; exact J, ⟨c7.regs kq (by decide) mq, Outside.refl _ _ _ _, fun _ _ _ _ _ _ => rfl,
      by rw [mq, a6]; exact g0.1, fun hE => by rw [mq, a6]; exact g0.2 hE, Keep.refl _ _⟩,
    ⟨en6.keep (k7.trans kq), ((k57.trans kq).gpr (by decide)).trans hin.s6⟩, by rw [mq]; exact w6.trans o7, a10⟩,
    k57.trans kq⟩

/-- The registers `combL_ok`'s code writes. -/
def lRegs : List Reg := jtRegs ++ jwRegs ++ [.s9, .s10] ++ [.s7, .t2] ++ [.s8]

/-- `combine`'s joint windows over u1's `q_len` octets at the buffer and
u2's 32 octets on, out of Montgomery form, then the buffer into `s7` and
`p_len` into `s8`. -/
theorem combL_ok {s : State} {L : Lay} {key sig : Addr} {p G Y : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hin : InP s L) (hp : 2 ≤ p) (hpo : p % 2 = 1)
    (htab : JInv s.mem L.S L.wp p G Y (2 ^ (128 * L.wp) % p) jDone)
    (hj : JRun s s s L.S L.qOff L.wp p G Y (2 ^ (128 * L.wp) % p) 0 0)
    (h9 : s.gpr .s9 = off L.Buf 0) (h10 : s.gpr .s10 = BitVec.ofNat 64 L.ql) :
    WP isa (.seq (.loop (.seq jointByte (.block [.addi .s10 .s10 (-1)])) (.nonzero .s10))
      (.seq (PublicChecked.montOp 4 6 7) (.block (bufBase .s7 .t2 ++ getP .s8)))) s fun t =>
      (arrP t.mem L 4 = G ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.ql) *
          Y ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off L.Buf 32) L.ql) % p ∧
        InP t L ∧ Outside L.S (slot L.wp 1) (23 * (8 * (L.wp + 2))) s.mem t.mem ∧
        t.gpr .s7 = L.Buf ∧ t.gpr .s8 = BitVec.ofNat 64 L.pl) ∧ Keep lRegs s t := by
  have hw := hL.wp_ge
  have hpl : 128 ≤ L.pl := by rcases hL.pl with e | e | e <;> omega
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have hb0 : off L.Buf 0 = L.Buf := BitVec.add_zero _
  have hq28 : L.qOff = slot L.wp 28 := rfl
  refine WP.assoc (WP.seq (WP.mono (jointLoop_ok (L := L.ql) (D := L.Buf) hp hpo htab hj
      (by rw [h9, hb0]) h10 (by omega) (by omega)
      (fun i hi => by have := bufRd hL hs (o := 0) (k := L.ql + 32) (by omega) i hi; rwa [hb0] at this)
      (fun i hi x hx => by
        have := bufSepP hL (o := 0) (k := L.ql + 32) (by omega) i hi x
          (by have := slot_lt (w := L.wp) (show 24 < 28 by decide); simp only [VG.Proof.Bignum.ofs] at hx
              show (x - L.S).toNat < L.qOff; omega)
        rwa [hb0] at this))
    fun t₁ ⟨⟨v, o8⟩, k8⟩ => ?_))
  have hr8 : Regs t₁ L key sig := hr.keep k8 ((parr_win o8).pbody.body hL)
  refine WP.block_append (WP.mono (bufBase_ok (hs.congr k8.2.2) hL hr8 (rd := .s7) (t := .t2)
      (by decide) (by decide) (by decide)) fun u ⟨⟨f7, mu⟩, ku⟩ =>
    WP.mono (getP_ok (hs.congr (k8.trans ku).2.2) hL (hr8.keepM ku mu) .s8) fun t ⟨⟨f8, m9⟩, k9⟩ =>
      ⟨⟨?_, hin.keep ((k8.trans ku).trans k9), by rw [m9, mu]; exact o8, (k9.gpr (by decide)).trans f7, f8⟩,
        (k8.trans ku).trans k9⟩)
  rw [arrP, m9, mu]
  exact v (by rw [pow_two_mul])

/-- The registers `combine` writes. -/
def combRegs : List Reg := headRegs ++ gRegs ++ tRegs ++ lRegs ++ storeRegs

/-- `combine`: `g^u1 y^u2 mod p` to the buffer's first `p_len` octets, for
`u1` the buffer's first `q_len` octets and `u2` those 32 octets on. -/
theorem combine_ok {s : State} {L : Lay} {key sig : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hk : Src s L key (3 * L.pl + L.ql))
    (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1) (hrr : arrP s.mem L 24 = 2 ^ (128 * L.wp) % p) :
    WP isa combine s fun t =>
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.pl) =
          gOf s.mem L key ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.ql) % p *
            (yOf s.mem L key ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off L.Buf 32) L.ql) % p) % p ∧
        InP t L ∧ Body L s.mem t.mem ∧ Outside L.Q 1600 (2 ^ 64 - 1600) s.mem t.mem) ∧ Keep combRegs s t := by
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hpl : 128 ≤ L.pl := by rcases hL.pl with e | e | e <;> omega
  have e : ∀ j, slot L.wp j = 256 + j * (8 * (L.wp + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e24 := e 24; have e28 := e 28
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have hb0 : off L.Buf 0 = L.Buf := BitVec.add_zero _
  unfold combine
  refine WP.seq (WP.mono (combHead_ok hL hs hr hp0 hpo) fun s₁ ⟨⟨in1, I1, a7, _, a9, m1⟩, k1⟩ => ?_)
  have hk1 := hk.keep k1.2.1 k1.2.2
  -- g, then y's octets.
  refine wp_seq3 (combG_ok hL (hs.congr k1.2.2) (hr.keepM k1 m1) hk1 in1 a7) fun s₄ ⟨⟨v4, in4, o4, b7, b8⟩, k4⟩ => ?_
  rw [m1] at v4 o4
  have pa4 : PArr L s.mem s₄.mem := PArr.of o4 (slot_mono (show 1 ≤ 4 by decide)) (by omega)
  have k14 := k1.trans k4
  have I4 : PInv s₄ L := by
    show ((word s₄.mem L.S (slot L.wp 0)).toNat * (s₄.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [o4.word (by omega) (by omega_arith), ← m1, k4.gpr (by decide)]; exact I1
  have hr4 : Regs s₄ L key sig := hr.keep k14 (pa4.pbody.body hL)
  -- y, `R² mod p` and the joint table.
  refine wp_seq4 (combT_ok (p := p) hL (hs.congr k14.2.2) hr4 (hk.keep k14.2.1 k14.2.2) in4 I4
    (by rw [arrP, o4.wordsVal (by omega) (by omega_arith)]; exact hp0) hp hpo
    (by rw [arrP, o4.wordsVal (by omega) (by omega_arith)]; exact hrr) b7 b8)
    fun u₂ ⟨⟨J, r0, in5, o5, a10⟩, k5⟩ => ?_
  rw [v4] at J r0
  have ey : yOf s₄.mem L key = yOf s.mem L key := by
    unfold yOf; rw [(hk.sub (o := 2 * L.pl + L.ql) (k := L.pl) comb_sub2).bytes (pa4.pbody.body hL) (body_le hL)]
  rw [ey] at J r0
  have pa5 : PArr L s.mem u₂.mem := pa4.trans (parr_win o5)
  have k15 := k14.trans k5
  -- The joint windows.
  refine wp_seq3 (combL_ok hL (hs.congr k15.2.2) (hr.keep k15 (pa5.pbody.body hL)) in5 hp hpo J r0
    (by rw [k5.gpr (by decide), k4.gpr (by decide), a9]) a10) fun t₁ ⟨⟨V, in6, o6, f7, f8⟩, k6⟩ => ?_
  have bb1 : Spec.Rsa.bytesAt u₂.mem L.Buf L.ql = Spec.Rsa.bytesAt s.mem L.Buf L.ql := by
    have := bufBytes hL pa5 (parr_q L) (o := 0) (k := L.ql) (by omega); rwa [hb0] at this
  have bb2 : Spec.Rsa.bytesAt u₂.mem (off L.Buf 32) L.ql = Spec.Rsa.bytesAt s.mem (off L.Buf 32) L.ql :=
    bufBytes hL pa5 (parr_q L) (o := 32) (k := L.ql) (by omega)
  rw [bb1, bb2] at V
  have pa6 : PArr L s.mem t₁.mem := pa5.trans (parr_win o6)
  have k16 := k15.trans k6
  -- To the buffer.
  refine WP.mono (storeBE_ok (j := 4) (O := L.Buf) (k := L.pl) in6.env (by decide)
    (by have := ScrL.bufSt (hs.congr k16.2.2) hL (o := 0) (k := L.pl) (by omega)
        simpa only [off, BitVec.add_zero] using this)
    (by have := buf_nowrap hL (o := 0) (k := L.pl) (by omega) (by omega); simpa only [off, BitVec.add_zero] using this)
    f7 f8 (by omega) (by omega) (bufPastP hL)) fun t ⟨⟨vt, ot⟩, kt⟩ => ?_
  have A0 : arrP t₁.mem L 0 = p := by rw [arrP, pa6.wordsVal (by omega) (by omega_arith)]; exact hp0
  have hplt : p < 2 ^ (8 * L.pl) := by
    rw [← A0, ← hw8, show 8 * (8 * L.wp) = 64 * L.wp by omega]; exact wordsVal_lt _ _ _ _
  refine ⟨⟨?_, in6.keep kt, (pa6.pbody.body hL).trans (Body.ofBuf hL ot (by omega)),
    (pa6.pbody.keepQ hL).trans (bufKeepQ ot (by omega))⟩, k16.trans kt⟩
  rw [vt, read_low _ _ (w := L.wp) (by omega) (by
    show arrP t₁.mem L 4 < 2 ^ (8 * L.pl); rw [V]; exact Nat.lt_trans (Nat.mod_lt _ (by omega)) hplt)]
  show arrP t₁.mem L 4 = _
  rw [V]
  exact Nat.mul_mod _ _ _

end VG.Proof.Dsa.RISCV64
