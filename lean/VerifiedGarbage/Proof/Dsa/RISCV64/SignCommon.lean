module

public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyComb
public import VerifiedGarbage.Proof.Dsa.RISCV64.Save
public import VerifiedGarbage.Impl.Dsa.RISCV64.Derive
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubOut
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA signing and key derivation on RISC-V: shared steps

* `powSrc_ok`: `Verify.powP` with the exponent's `q_len` octets in a buffer
  apart from `scratch` (x or the nonce);
* `nonZero_ok`: `Sign.nonZero`, `a4 &=` the mask of an array not being the
  value in array 7;
* `maskCopy_ok`, `zeroLoop_ok`: octets and'ed with a mask, or 0, to `out`;
* `sfinish_ok`: `restore`, keeping memory.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Verify
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-- The number of the `q_len` octets at `x` (the private key, or the nonce). -/
def kOf (m : Mem) (L : Lay) (x : Addr) : Nat := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m x L.ql)

theorem signStatus_ite (c : Prop) [Decidable c] (v : List Byte) :
    Spec.Dsa.signStatus (if c then some v else none) = if c then 1 else 0 := by
  split <;> rfl

theorem mask_low (c : Bool) : mask c &&& 1#64 = BitVec.ofNat 64 (if c then 1 else 0) := by
  cases c <;> rfl

theorem off_ofs (O x : Addr) : off O (ofs O x) = x := by
  simp only [off, ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [BitVec.add_comm, BitVec.sub_add_cancel]

/-- `powP`: the `p_len` octets at `N` (`s7`) to the power of the `q_len`
octets at `E` (`s9`), a buffer apart from `scratch`, modulo p, into array 4.
Arrays 1–23 change. -/
theorem powSrc_ok {s : State} {L : Lay} {key sig N E : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hin : InP s L) (hi : PInv s L) (hN : Src s L N L.pl) (h7 : s.gpr .s7 = N)
    (hE : Src s L E L.ql) (h9 : s.gpr .s9 = E)
    (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1) (hrr : arrP s.mem L 24 = 2 ^ (128 * L.wp) % p) :
    WP isa powP s fun t =>
      (arrP t.mem L 4 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N L.pl) ^
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E L.ql) % p ∧
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
  have hbuf : Spec.Rsa.bytesAt s₄.mem E L.ql = Spec.Rsa.bytesAt s.mem E L.ql := by
    rw [m4]; exact hE.bytes hb3 (by omega)
  refine WP.mono (Win.powWin_ok (D := E) (L := L.ql) en4.hs (by omega) (by omega)
    (by omega) en4.a7 en4.s5 en4.t0 (by rw [W0, k14.gpr (by decide)]; exact hi)
    (by show 2 ≤ arrP s₄.mem L 0; rw [A0]; exact hp) (by show arrP s₄.mem L 0 % 2 = 1; rw [A0]; exact hpo)
    (by show arrP s₄.mem L 1 < arrP s₄.mem L 0; rw [A1, A0]; exact Nat.mod_lt _ (by omega))
    (by rw [k4.gpr (by decide), k13.gpr (by decide), h9]; exact (BitVec.add_zero _).symm) a10 (by omega)
    (by omega_arith) (by rw [k14.2.1, k14.2.2]; exact hE.rd)
    (fun i hi x hx => hE.sep i hi x (Nat.lt_of_lt_of_le hx (by omega)))) fun t ⟨⟨r4, o5'⟩, k5⟩ => ?_
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

/-- The registers `nonZero` writes. -/
def nonZeroRegs : List Reg := [.a1] ++ eqRegs .a2 ++ [.a1, .a4]

/-- `nonZero a`: `a4 &=` the mask of `[a] ≠ [7]`. -/
theorem nonZero_ok {s : State} {B : Addr} {Z w a c : Nat} {b : Bool} (h : Env s B Z w) (ha : a < 28)
    (h7 : wordsVal s.mem B (slot w 7) w = c) (h4 : s.gpr .a4 = mask b) :
    WP isa (Sign.nonZero a) s fun t =>
      (t.gpr .a4 = mask (b && decide (wordsVal s.mem B (slot w a) w ≠ c)) ∧ t.mem = s.mem) ∧
        Keep nonZeroRegs s t := by
  unfold Sign.nonZero
  refine WP.seq (WP.mono (WP.keep [.a1] (Q := fun u => u.gpr .a1 = mask true ∧ u.mem = s.mem)
    (by brun [exec_li (show imm12 (-1) by decide)]; rfl) (by decide) (by rfl)) fun s₁ ⟨⟨a1, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (eqMask_ok (h.keep k1) (j := a) (k := 7) (rd := .a2) ha (by decide) (by decide))
    fun s₂ ⟨⟨c2, m2⟩, k2⟩ => ?_)
  rw [m1, h7] at c2
  rw [WP.block_append_iff]
  refine WP.mono (clear_ok s₂ ((k2.gpr (by decide)).trans a1) c2) fun s₃ ⟨⟨d1, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  refine WP.mono (WP.keep [.a4] (Q := fun t => t.gpr .a4 = mask (b && decide (wordsVal s.mem B (slot w a) w ≠ c)) ∧
      t.mem = s₃.mem) ?_ (by decide) (by rfl))
    fun t ⟨⟨t4, mt⟩, kt⟩ => ⟨⟨t4, by rw [mt, m3, m2, m1]⟩, (k13.trans kt).mono (by decide)⟩
  brun [d1, (k13.gpr (r := .a4) (by decide)).trans h4, mask_and]
  simp only [Bool.true_and, decide_not]

theorem mask_byte8 (x : BitVec 8) (c : Bool) : ((x.setWidth 64 &&& mask c).setWidth 8) = if c then x else 0 := by
  cases c
  · show ((x.setWidth 64 &&& 0#64).setWidth 8) = 0
    rw [BitVec.and_zero]; rfl
  · simp only [ite_true, Win.mask, BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    have := x.isLt
    omega_arith

/-- The registers `maskCopy` writes. -/
def maskCopyRegs : List Reg := [.s0, .t3, .t4, .t5]

/-- `maskCopy`: the `N` octets at `src` (`t3`), and'ed with the mask of `c`
(`a4`), to `dst` (`t4`); the pointers past them. -/
theorem maskCopy_ok {s : State} {src dst : Addr} {N : Nat} {c : Bool} (hN : 0 < N) (hN' : N < 2 ^ 64)
    (ho : ∀ i < N, InRegions s.wr (off dst i) 1) (hno : dst.toNat + N ≤ 2 ^ 64)
    (hrd : ∀ i < N, InRegions (s.rd ++ s.wr) (off src i) 1)
    (hsep : ∀ i < N, ∀ x, ofs dst x < N → off src i ≠ x)
    (h3 : s.gpr .t3 = src) (h4 : s.gpr .t4 = dst) (h5 : s.gpr .t5 = BitVec.ofNat 64 N)
    (ha4 : s.gpr .a4 = mask c) :
    WP isa Derive.maskCopy s fun t =>
      (Spec.Rsa.bytesAt t.mem dst N = (if c then Spec.Rsa.bytesAt s.mem src N else List.replicate N 0) ∧
        Outside dst 0 N s.mem t.mem ∧ t.gpr .t3 = off src N ∧ t.gpr .t4 = off dst N) ∧
        Keep maskCopyRegs s t := by
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off src i ∧ t.gpr .t4 = off dst i ∧ Outside dst 0 i s.mem t.mem ∧
      (∀ i' < i, t.mem (off dst i') = if c then s.mem (off src i') else 0) ∧ Keep maskCopyRegs s t
  unfold Derive.maskCopy
  refine WP.mono (wp_countdown (body := .block ([.load .b .s0 .t3 0, .logic .and .s0 .s0 .a4, .store .b .s0 .t4 0,
      .addi .t3 .t3 1, .addi .t4 .t4 1] ++ ([.addi .t5 .t5 (-1)] : List Instr)))
    (cnt := .t5) (N := N) hN' hN Inv (fun i hi t ⟨t3, t4, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [h3, off, BitVec.add_zero], by rw [h4, off, BitVec.add_zero], Outside.refl _ _ _ _,
      fun _ h => absurd h (by omega), Keep.refl _ _⟩ h5)
    fun t ⟨t3, t4, tout, tb, tk⟩ => ⟨⟨?_, tout, t3, t4⟩, tk⟩
  · have t24 : t.gpr .a4 = mask c := (tk.gpr (by decide)).trans ha4
    have hr : InRegions (t.rd ++ t.wr) (off src i) 1 := by rw [tk.2.1, tk.2.2]; exact hrd i hi
    have hw : InRegions t.wr (off dst i) 1 := by rw [tk.2.2]; exact ho i hi
    have hst : WP isa (.block [.load .b .s0 .t3 0, .logic .and .s0 .s0 .a4, .store .b .s0 .t4 0, .addi .t3 .t3 1,
        .addi .t4 .t4 1, .addi .t5 .t5 (-1)]) t fun t' => t' = ((({ ((t.write .s0
          ((t.mem.read (off src i) 1).setWidth 64)).write .s0
          ((t.mem.read (off src i) 1).setWidth 64 &&& mask c)) with
          mem := t.mem.write (off dst i) 1 (((t.mem.read (off src i) 1).setWidth 64 &&& mask c).setWidth 8) } :
            State).write .t3 (off src (i + 1))).write .t4 (off dst (i + 1))).write .t5
              (t.gpr .t5 - BitVec.ofNat 64 1) := by
      brun [t3, t4, t24, hr, hw, add_ofNat_zero]
    refine WP.mono hst fun t' e => ?_
    subst e
    have hw1 := write1_outside t.mem dst (d := i)
      (((t.mem.read (off src i) 1).setWidth 64 &&& mask c).setWidth 8) (by omega)
    refine ⟨⟨by gsimp, by gsimp, ?_, ?_, ?_⟩, by gsimp⟩
    · gsimp; exact (tout.mono (Nat.le_refl _) (by omega)).trans (hw1.mono (by omega) (by omega))
    · intro i' hi'
      gsimp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
      · rw [hw1 _ (by rw [ofs_off0 dst (by omega)]; omega)]; exact tb i' hi'
      · have hs : t.mem (off src i') = s.mem (off src i') := by
          refine tout _ (Or.inr ?_)
          by_contra hcon
          exact hsep i' hi (off src i') (by omega) rfl
        rw [write1_self, Pub.read1_setWidth, mask_byte8, hs]
    · exact Keep.trans' tk ((((((Keep.write _ _ _).trans (Keep.write _ _ _)).trans (Keep.mem _ _)).trans
        (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _) |>.mono (by decide))
  · rw [Spec.Rsa.bytesAt]
    rw [show (List.range N).map (fun i => t.mem (dst + BitVec.ofNat 64 i)) =
        (List.range N).map (fun i => if c then s.mem (off src i) else 0) from
      List.map_congr_left fun i hi => tb i (List.mem_range.mp hi)]
    cases c
    · refine List.eq_replicate_iff.mpr ⟨by simp, fun b hb => ?_⟩
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
      rfl
    · rfl

/-- The registers `zeroLoop` writes. -/
def zeroLoopRegs : List Reg := [.t4, .t5]

/-- The count loop of `zeroOut`: the `N` octets at `dst` (`t4`) := 0
(`s0`). -/
theorem zeroLoop_ok {s : State} {dst : Addr} {N : Nat} (hN : 0 < N) (hN' : N < 2 ^ 64)
    (ho : ∀ i < N, InRegions s.wr (off dst i) 1) (hno : dst.toNat + N ≤ 2 ^ 64)
    (h0 : s.gpr .s0 = 0) (h4 : s.gpr .t4 = dst) (h5 : s.gpr .t5 = BitVec.ofNat 64 N) :
    WP isa (countLoop .t5 [.store .b .s0 .t4 0, .addi .t4 .t4 1]) s fun t =>
      (Spec.Rsa.bytesAt t.mem dst N = List.replicate N 0 ∧ Outside dst 0 N s.mem t.mem) ∧
        Keep zeroLoopRegs s t := by
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t4 = off dst i ∧ Outside dst 0 i s.mem t.mem ∧ (∀ i' < i, t.mem (off dst i') = 0) ∧
      Keep zeroLoopRegs s t
  refine WP.mono (wp_countdown (body := .block ([.store .b .s0 .t4 0, .addi .t4 .t4 1] ++
      ([.addi .t5 .t5 (-1)] : List Instr)))
    (cnt := .t5) (N := N) hN' hN Inv (fun i hi t ⟨t4, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [h4, off, BitVec.add_zero], Outside.refl _ _ _ _, fun _ h => absurd h (by omega), Keep.refl _ _⟩ h5)
    fun t ⟨_, tout, tb, tk⟩ => ⟨⟨?_, tout⟩, tk⟩
  · have t0 : t.gpr .s0 = 0 := (tk.gpr (by decide)).trans h0
    have hw : InRegions t.wr (off dst i) 1 := by rw [tk.2.2]; exact ho i hi
    have hst : WP isa (.block [.store .b .s0 .t4 0, .addi .t4 .t4 1, .addi .t5 .t5 (-1)]) t fun t' =>
        t' = (({ t with mem := t.mem.write (off dst i) 1 ((0 : BitVec 64).setWidth 8) } : State).write .t4
          (off dst (i + 1))).write .t5 (t.gpr .t5 - BitVec.ofNat 64 1) := by
      brun [t4, t0, hw, add_ofNat_zero]
    refine WP.mono hst fun t' e => ?_
    subst e
    have hw1 := write1_outside t.mem dst (d := i) ((0 : BitVec 64).setWidth 8) (by omega)
    refine ⟨⟨by gsimp, ?_, ?_, ?_⟩, by gsimp⟩
    · gsimp; exact (tout.mono (Nat.le_refl _) (by omega)).trans (hw1.mono (by omega) (by omega))
    · intro i' hi'
      gsimp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
      · rw [hw1 _ (by rw [ofs_off0 dst (by omega)]; omega)]; exact tb i' hi'
      · rw [write1_self]; rfl
    · exact Keep.trans' tk ((((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))
  · rw [Spec.Rsa.bytesAt]
    refine List.eq_replicate_iff.mpr ⟨by simp, fun b hb => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact tb i (List.mem_range.mp hi)

/-- `restore`, from a state with `S` in `s6` and `s`'s callee-saved registers
and `ra` in the saved words; memory is kept. -/
theorem sfinish_ok {s u : State} {S : Addr} (h6 : u.gpr .s6 = S)
    (hwr : ∀ i < 13, InRegions u.wr (off (savW S) (8 * i)) 8)
    (hal : ∀ i < 13, (off (savW S) (8 * i)).toNat % 8 = 0)
    (hsav : ∀ i < 13, word u.mem S (saveOff i) = s.gpr (saved i)) :
    WP isa (.block restore) u fun w =>
      ((∀ r ∈ preserved, w.gpr r = s.gpr r) ∧ w.gpr .ra = s.gpr .ra) ∧ w.gpr .a0 = u.gpr .a0 ∧
        w.mem = u.mem := by
  have saved_all' : ∀ r ∈ preserved, ∃ i < 13, r = saved i := by decide
  refine WP.mono (restore_ok u (v := fun i => s.gpr (saved i)) h6 hwr hal fun i hi => ?_)
    fun w ⟨wrs, wot, wm, _⟩ => ⟨⟨fun r hr => ?_, wrs 11 (by decide)⟩, wot .a0 (by decide), wm⟩
  · rw [← hsav i hi]
    show u.mem.readW (off (savW S) (8 * i)) 64 = u.mem.readW (S + BitVec.ofNat 64 (saveOff i)) 64
    rw [saveOff_eq]
  · obtain ⟨i, hi, rfl⟩ := saved_all' r hr
    exact wrs i hi

end VG.Proof.Dsa.RISCV64
