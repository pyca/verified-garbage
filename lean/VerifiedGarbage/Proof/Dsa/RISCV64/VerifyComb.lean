module

public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyProd
public import VerifiedGarbage.Proof.Dsa.RISCV64.CheckKey
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
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

/-! ## The joint power `g^u1 y^u2 mod p`

`jointTable` builds `T_(i + 4 j) = g^i y^j R mod p` for `i, j < 4` in arrays
8–23 (`jointTable_ok`), each entry the Montgomery product of two before it
(`montStep`); a joint window is two squares and `a := a T_(d1 + 4 d2)` for
two bits of each exponent (`jointWindow_ok`); a byte of each is four windows
(`jointByte_ok`); and the power is the bytes in turn (`jointPow_ok`). -/

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

end Joint

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

/-- The registers `combine`'s second block writes. -/
def midRegs : List Reg := [.s7, .t2, .s8, .s9] ++ ptrRegs

/-- `combine`'s second block: the buffer from `q_len` on into `s9` and y's
octets into `s7`. -/
theorem combMid_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key sig) :
    WP isa (.block (ptrBuf2 ++ ([.addi .s9 .s7 0] : List Instr) ++ ptrY)) s fun t =>
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
