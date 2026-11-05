module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Base
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.RISCV64.PubOut
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.Sieve
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the entry, the end and the exit, whose symbolic executions the tests' changes need not re-check

/-!
# An FFDH parameter candidate on RISC-V: the entry, the end and the exit

As on PPC64LE (`Proof/Ffdh/PPC64LE/ParameterCandidate/{Entry,ZeroOut,Finish,WriteP,End,Exit,Front}.lean`):
`front_ok`, the entry (`scratch_len` from the stack, the registers saved at
the end of `scratch`, the arguments in the header) and `out` zeroed give
`St` for the arguments (`ppOf`); `CEnd p res`, before the exit, the status
of `res` in `a0`, `out` and `used` as the contract states them
(`finEnd`, `pEnd`); `exit_ok`, the registers back from the save area.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.ParameterCandidate

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Ffdh.RISCV64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Impl.MillerRabin.RISCV64.Search
open VG.Proof.MillerRabin.RISCV64.Search (rw_self frm_writeW shl3_ofNat)

/-! ## The entry -/

theorem entryA_ok {s : State} {B : Addr} {n : Nat} (h7 : s.gpr .a7 = B) (hn : stackArg s 0 = BitVec.ofNat 64 n)
    (hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) (hal : s.sp.toNat % 8 = 0) (h80 : 104 ≤ 8 * n) :
    WP isa (.block [.addSp .t3 0, .load .d .t3 .t3 0, .shift .sll .d .t4 .t3 3, .add .t4 .a7 .t4,
      .addi .t4 .t4 (-104)]) s fun t =>
      (t.gpr .t4 = off B (8 * n - 104) ∧ t.gpr .t3 = BitVec.ofNat 64 n ∧ t.mem = s.mem) ∧ Keep [.t3, .t4] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  simp only [stackArgAddr, stackArg, Nat.mul_zero, BitVec.add_zero] at hargs hn
  have e1 : B + BitVec.ofNat 64 (8 * n) - BitVec.ofNat 64 104 = off B (8 * n - 104) :=
    VG.Offset.add_ofNat_sub B h80
  brun [exec_addSp (show 0 < 2048 by decide), BitVec.add_zero, add_ofNat_zero, hargs, hn, hal, h7, shl3_ofNat, e1]

/-- The first `k` registers saved, from the state `s₀` after `entryA`. -/
structure SV (B : Addr) (n : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  out : Outside B (8 * n - 104) 104 s₀.mem s.mem
  saved : ∀ i < k, word s.mem B (8 * n - 104 + 8 * i) = s₀.gpr (saved i)

theorem save_step {B : Addr} {n : Nat} {s₀ : State} (h4 : s₀.gpr .t4 = off B (8 * n - 104))
    (h80 : 104 ≤ 8 * n) (hn : 8 * n ≤ 2 ^ 64)
    (hin : ∀ i < 13, InRegions s₀.wr (off B (8 * n - 104 + 8 * i)) 8)
    (hal : ∀ i < 13, (off B (8 * n - 104 + 8 * i)).toNat % 8 = 0) {k : Nat} (hk : k < 13) {s : State}
    (h : SV B n s₀ k s) : WP isa (.block [.store .d (saved k) .t4 (8 * k)]) s (SV B n s₀ (k + 1)) := by
  have hw : s.gpr .t4 = off B (8 * n - 104) := by rw [h.gpr, h4]
  have hout : InRegions s.wr (s.gpr .t4 + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [h.wr, hw, off_add]; exact hin k hk
  have ha : (s.gpr .t4 + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 := by rw [hw, off_add]; exact hal k hk
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show 8 * k < 2048 by omega) ha hout, Option.some.injEq, exists_eq_left', hw, off_add]
  have hW := writeW_outside s.mem B (d := 8 * n - 104 + 8 * k) (s.gpr (saved k)) (by omega)
  refine ⟨h.gpr, h.rd, h.wr, h.sp, h.out.trans (hW.mono (by omega) (by omega)), fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · simp only [word, off]
    rw [rw_off _ _ _ (by omega) (by omega) (by omega)]
    exact h.saved i hi
  · simp only [word, off]; rw [rw_self, h.gpr]

theorem map_flatMap {α β : Type} (g : α → β) (l : List α) : l.map g = l.flatMap fun i => [g i] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem saves_ok {B : Addr} {n : Nat} {s₀ : State} (h4 : s₀.gpr .t4 = off B (8 * n - 104))
    (h80 : 104 ≤ 8 * n) (hn : 8 * n ≤ 2 ^ 64)
    (hin : ∀ i < 13, InRegions s₀.wr (off B (8 * n - 104 + 8 * i)) 8)
    (hal : ∀ i < 13, (off B (8 * n - 104 + 8 * i)).toNat % 8 = 0) :
    WP isa (.block ((List.range 13).map fun i => .store .d (saved i) .t4 (8 * i))) s₀ (SV B n s₀ 13) := by
  rw [map_flatMap]
  exact wp_range_flatMap (M := isa) (SV B n s₀) (fun k s hk h => save_step h4 h80 hn hin hal hk h) 13
    (Nat.le_refl _) s₀ ⟨rfl, rfl, rfl, rfl, Outside.refl _ _ _ _, fun _ h => absurd h (by omega)⟩

/-- The header's stores. -/
def hdrW (m : Mem) (B : Addr) (t3 a0 a1 a2 a3 a4 a5 a6 : BitVec 64) : Mem :=
  ((((((((m.writeW (B + BitVec.ofNat 64 0) t3).writeW (B + BitVec.ofNat 64 16) a0).writeW
    (B + BitVec.ofNat 64 24) a1).writeW (B + BitVec.ofNat 64 152) a1).writeW (B + BitVec.ofNat 64 32) a2).writeW
    (B + BitVec.ofNat 64 40) a3).writeW (B + BitVec.ofNat 64 128) a4).writeW (B + BitVec.ofNat 64 136) a5).writeW
    (B + BitVec.ofNat 64 144) a6

theorem header_ok {s : State} {B : Addr} (h7 : s.gpr .a7 = B)
    (hst : ∀ d, d + 8 ≤ 256 → InRegions s.wr (B + BitVec.ofNat 64 d) 8)
    (hal : ∀ d, d + 8 ≤ 256 → d % 8 = 0 → (B + BitVec.ofNat 64 d).toNat % 8 = 0) :
    WP isa (.block [.addi .s6 .a7 0, sth .t3 hWsLen, sth .a0 hOut, sth .a1 hLen, sth .a1 hUsed, sth .a2 hUsedP,
      sth .a3 hBits, .shift .sll .d .a4 .a4 32, .shift .srl .d .a4 .a4 32, sth .a4 hGen, sth .a5 hRand,
      sth .a6 hRandLen]) s fun t =>
      (t.gpr .s6 = B ∧ t.gpr .a4 = (s.gpr .a4 <<< 32) >>> 32 ∧
        t.mem = hdrW s.mem B (s.gpr .t3) (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) (s.gpr .a3)
          ((s.gpr .a4 <<< 32) >>> 32) (s.gpr .a5) (s.gpr .a6)) ∧ Keep [.a4, .s6] s t := by
  have h0 : InRegions s.wr B 8 := by simpa using hst 0 (by decide)
  have a0 : B.toNat % 8 = 0 := by simpa using hal 0 (by decide) (by decide)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  simp only [sth, hWsLen, hOut, hLen, hUsed, hUsedP, hBits, hGen, hRand, hRandLen]
  brun [h7, BitVec.add_zero, add_ofNat_zero, h0, a0, hst 16 (by decide), hst 24 (by decide),
    hst 152 (by decide), hst 32 (by decide), hst 40 (by decide), hst 128 (by decide), hst 136 (by decide),
    hst 144 (by decide), hal 16 (by decide) (by decide), hal 24 (by decide) (by decide), hal 152 (by decide) (by decide),
    hal 32 (by decide) (by decide), hal 40 (by decide) (by decide), hal 128 (by decide) (by decide), hal 136 (by decide) (by decide), hal 144 (by decide) (by decide)]
  simp only [hdrW, BitVec.add_zero]
  done

theorem hdrW_words (m : Mem) (B : Addr) (t3 a0 a1 a2 a3 a4 a5 a6 : BitVec 64) :
    let h := hdrW m B t3 a0 a1 a2 a3 a4 a5 a6
    word h B 0 = t3 ∧ word h B 16 = a0 ∧ word h B 24 = a1 ∧ word h B 152 = a1 ∧ word h B 32 = a2 ∧
      word h B 40 = a3 ∧ word h B 128 = a4 ∧ word h B 136 = a5 ∧ word h B 144 = a6 := by
  simp (disch := decide) only [hdrW, word, off, rw_off, rw_self, and_self]

theorem hdrW_frm (m : Mem) (B : Addr) (t3 a0 a1 a2 a3 a4 a5 a6 : BitVec 64) :
    Frm B [(0, 256)] m (hdrW m B t3 a0 a1 a2 a3 a4 a5 a6) := by
  unfold hdrW
  iterate 9 (refine frm_writeW ?_ _ ⟨(0, 256), List.mem_singleton_self _, by decide, by decide⟩ (by decide))
  exact Frm.refl _ _ _

/-! ## `out` zeroed -/

theorem zeroOut_ok {s : State} {B O : Addr} {Z k : Nat} (hs : Scr s B Z) (hO : ∀ i < k, InRegions s.wr (off O i) 1)
    (h6 : s.gpr .s6 = B)
    (hOv : s.mem.readW (B + BitVec.ofNat 64 16) 64 = O)
    (hL : s.mem.readW (B + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hk' : k < 2 ^ 63) (hZ : 32 ≤ Z) :
    WP isa zeroOut s fun t =>
      ((∀ i < k, t.mem (off O i) = 0) ∧ Outside O 0 k s.mem t.mem) ∧ Keep [.t3, .t4, .t5] s t := by
  unfold zeroOut
  refine WP.seq ?_
  refine WP.mono (WP.keep [.t3, .t4, .t5] (Q := fun s₂ => s₂.gpr .t3 = O ∧ s₂.gpr .t4 = BitVec.ofNat 64 k ∧
    s₂.gpr .t5 = BitVec.ofNat 64 0 ∧ s₂.mem = s.mem)
    (by simp only [ldh, hOut, hLen]
        brun [h6, hOv, hL, hs.ld (d := 16) (n := 8) (by omega_arith), hs.ld (d := 24) (n := 8) (by omega_arith),
          hs.al8 (d := 16) (by omega_arith) (by decide), hs.al8 (d := 24) (by omega_arith) (by decide),
          exec_li (show imm12 0 by decide)])
    (by rfl) (by rfl)) fun s₂ ⟨⟨b3, b4, b5, m2⟩, k2⟩ => ?_
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .t3 = off O j ∧ t.gpr .t5 = BitVec.ofNat 64 0 ∧ Outside O 0 j s.mem t.mem ∧
      (∀ i < j, t.mem (off O i) = 0) ∧ Keep [.t3, .t4, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.store .b .t5 .t3 0, .addi .t3 .t3 1] ++
      ([.addi .t4 .t4 (-1)] : List Instr)))
    (cnt := .t4) (N := k) (by omega_arith) (by omega_arith) Inv (fun j hj t ⟨t3, t5, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [b3]; simp [off], b5, by rw [m2]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k2⟩ b4) fun t ⟨_, _, tout, tb, tk⟩ => ⟨⟨tb, tout⟩, tk⟩
  have hst : WP isa (.block [.store .b .t5 .t3 0, .addi .t3 .t3 1, .addi .t4 .t4 (-1)]) t fun t' =>
      t' = (({ t with mem := t.mem.write (off O j) 1 ((BitVec.ofNat 64 0).setWidth 8) } :
          State).write .t3 (off O (j + 1))).write .t4 (t.gpr .t4 - BitVec.ofNat 64 1) := by
    have hw : InRegions t.wr (off O j) 1 := by rw [tk.2.2]; exact hO j hj
    brun [t3, t5, hw]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw1 := write1_outside t.mem O (d := j) ((BitVec.ofNat 64 0).setWidth 8) (by omega_arith)
  refine ⟨⟨by gsimp, by gsimp; exact t5, ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; exact (tout.mono (Nat.le_refl _) (by omega_arith)).trans (hw1.mono (by omega_arith) (by omega_arith))
  · intro i hi
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hw1 _ (by rw [VG.Proof.Mont.ofs_off0 O (by omega_arith)]; omega_arith)]; exact tb i hi
    · rw [write1_self]; rfl
  · exact Keep.trans' tk ((((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))

/-! ## The result -/

theorem finish_ok (r : Nat) (hr : r ≤ 2) {s : State} {B U : Addr} {Z v : Nat} (hs : Scr s B Z) (hu : Scr s U 8)
    (h6 : s.gpr .s6 = B) (hU : s.mem.readW (B + BitVec.ofNat 64 32) 64 = U)
    (hV : s.mem.readW (B + BitVec.ofNat 64 152) 64 = BitVec.ofNat 64 v) (hZ : 160 ≤ Z) :
    WP isa (.block (finish r)) s fun t => (t.gpr .a0 = BitVec.ofNat 64 r ∧
      t.mem = s.mem.writeW (off U 0) (BitVec.ofNat 64 (if r = 0 then 0 else v))) ∧ Keep [.t3, .t4, .a0] s t := by
  have su : InRegions s.wr U 8 := by simpa using hu.st (d := 0) (n := 8) (by omega)
  have au : U.toNat % 8 = 0 := hu.al
  obtain rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  · refine WP.keep [.t3, .t4, .a0] ?_ (by rfl) (by rfl)
    simp only [finish, ldh, hUsedP, ↓reduceIte, List.cons_append, List.nil_append]
    brun [h6, hU, hs.ld (d := 32) (n := 8) (by omega), hs.al8 (d := 32) (by omega) (by decide), su, au,
      BitVec.add_zero, add_ofNat_zero, exec_li (show imm12 0 by decide)]
  all_goals
    refine WP.keep [.t3, .t4, .a0] ?_ (by rfl) (by rfl)
    simp only [finish, ldh, hUsedP, hUsed, Nat.reduceEqDiff, ↓reduceIte, List.cons_append,
      List.nil_append]
    brun [h6, hU, hV, hs.ld (d := 32) (n := 8) (by omega), hs.ld (d := 152) (n := 8) (by omega),
      hs.al8 (d := 32) (by omega) (by decide), hs.al8 (d := 152) (by omega) (by decide), su, au,
      BitVec.add_zero, add_ofNat_zero, exec_li (show imm12 1 by decide), exec_li (show imm12 2 by decide)]

/-! ## p to `out` -/

/-- `writeP`'s first block: `out`, `out_len`, and the address of p's last
octet. -/
theorem writeHead_ok {s : State} {B O : Addr} {Z k : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .s6 = B) (h7 : s.gpr .a7 = off B 256)
    (hO : s.mem.readW (B + BitVec.ofNat 64 16) 64 = O) (hL : s.mem.readW (B + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hZ : 256 + k ≤ Z) :
    WP isa (.block [ldh .t3 hOut, ldh .t4 hLen, .add .t5 .a7 .t4, .addi .t5 .t5 (-1)]) s fun s₂ =>
      (s₂.gpr .t5 = off B (256 + (k - 1)) ∧ s₂.gpr .t3 = O ∧ s₂.gpr .t4 = BitVec.ofNat 64 k ∧ s₂.mem = s.mem) ∧
        Keep [.t3, .t4, .t5] s s₂ := by
  have hnw := hs.nowrap
  refine WP.keep [.t3, .t4, .t5] ?_ (by rfl) (by rfl)
  simp only [ldh, hOut, hLen]
  brun [h6, h7, hO, hL, hs.ld (d := 16) (n := 8) (by omega_arith), hs.ld (d := 24) (n := 8) (by omega_arith),
    hs.al8 (d := 16) (by omega_arith) (by decide), hs.al8 (d := 24) (by omega_arith) (by decide), off_add,
    BitVec.add_zero]
  rw [off_sub _ (by omega_arith)]; congr 2; omega_arith

theorem writeP_ok {s : State} {B O : Addr} {Z k : Nat} (hs : Scr s B Z) (ho : ∀ i < k, InRegions s.wr (off O i) 1)
    (hno : O.toNat + k ≤ 2 ^ 64)
    (h6 : s.gpr .s6 = B) (h7 : s.gpr .a7 = off B 256)
    (hO : s.mem.readW (B + BitVec.ofNat 64 16) 64 = O) (hL : s.mem.readW (B + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hZ : 256 + k ≤ Z) (hsep : ∀ x, ofs O x < k → Z ≤ ofs B x) :
    WP isa writeP s fun t =>
      ((∀ i < k, t.mem (off O i) = s.mem (off B (256 + (k - 1 - i)))) ∧ Outside O 0 k s.mem t.mem) ∧
      Keep [.t3, .t4, .t5, .t6] s t := by
  have hnw := hs.nowrap
  unfold writeP
  refine WP.seq ?_
  refine WP.mono (writeHead_ok hs h6 h7 hO hL hk hZ) fun s₂ ⟨⟨b5, b3, b4, m2⟩, k2⟩ => ?_
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .t5 = off B (256 + (k - 1) - j) ∧ t.gpr .t3 = off O j ∧ Outside O 0 j s.mem t.mem ∧
      (∀ i < j, t.mem (off O i) = s.mem (off B (256 + (k - 1 - i)))) ∧ Keep [.t3, .t4, .t5, .t6] s t
  refine WP.mono (wp_countdown (body := .block ([.load .b .t6 .t5 0, .store .b .t6 .t3 0, .addi .t3 .t3 1,
      .addi .t5 .t5 (-1)] ++ ([.addi .t4 .t4 (-1)] : List Instr)))
    (cnt := .t4) (N := k) (by omega_arith) (by omega_arith) Inv (fun j hj t ⟨t5, t3, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [b5]; rfl, by rw [b3]; simp [off], by rw [m2]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k2.mono (by decide)⟩ b4) fun t ⟨_, _, tout, tb, tk⟩ => ⟨⟨tb, tout⟩, tk⟩
  have hrd : InRegions (t.rd ++ t.wr) (off B (256 + (k - 1) - j)) 1 := by
    rw [tk.2.1, tk.2.2]; exact hs.ld (show 256 + (k - 1) - j + 1 ≤ Z by omega_arith)
  have hst : WP isa (.block [.load .b .t6 .t5 0, .store .b .t6 .t3 0, .addi .t3 .t3 1, .addi .t5 .t5 (-1),
      .addi .t4 .t4 (-1)]) t fun t' => t' = ((({ (t.write .t6
        ((t.mem.read (off B (256 + (k - 1) - j)) 1).setWidth 64)) with
        mem := t.mem.write (off O j) 1 (((t.mem.read (off B (256 + (k - 1) - j)) 1).setWidth 64).setWidth 8) } :
          State).write .t3 (off O (j + 1))).write .t5
            (off B (256 + (k - 1) - j) - BitVec.ofNat 64 1)).write .t4 (t.gpr .t4 - BitVec.ofNat 64 1) := by
    have hw : InRegions t.wr (off O j) 1 := by rw [tk.2.2]; exact ho j hj
    brun [t5, t3, hrd, hw]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw1 := write1_outside t.mem O (d := j) (((t.mem.read (off B (256 + (k - 1) - j)) 1).setWidth 64).setWidth 8)
    (by omega_arith)
  have harr : t.mem (off B (256 + (k - 1) - j)) = s.mem (off B (256 + (k - 1) - j)) := by
    refine tout _ (Or.inr ?_)
    by_contra hc
    have := hsep (off B (256 + (k - 1) - j)) (by omega_arith)
    rw [show ofs B (off B (256 + (k - 1) - j)) = 256 + (k - 1) - j from
      Mem.sub_ofNat_toNat B (by omega_arith)] at this
    omega_arith
  refine ⟨⟨?_, by gsimp, ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; rw [off_sub _ (by omega_arith), show 256 + (k - 1) - j - 1 = 256 + (k - 1) - (j + 1) by omega_arith]
  · gsimp; exact (tout.mono (Nat.le_refl _) (by omega_arith)).trans (hw1.mono (by omega_arith) (by omega_arith))
  · intro i hi
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hw1 _ (by rw [VG.Proof.Mont.ofs_off0 O (by omega_arith)]; omega_arith)]; exact tb i hi
    · rw [write1_self, Pub.read1_setWidth, show 256 + (k - 1 - i) = 256 + (k - 1) - i by omega_arith, ← harr]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth]
      have := (t.mem (off B (256 + (k - 1) - i))).isLt
      omega_arith
  · exact Keep.trans' tk ((((((Keep.write _ _ _).trans (Keep.mem _ _)).trans
      (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))

/-! ## The end of a candidate -/

/-- What the exit reads: the working space, its length and the save area. -/
structure ESt (p : PP) (s : State) : Prop where
  scr : Scr s p.B p.Z
  s6 : s.gpr .s6 = p.B
  len : word s.mem p.B 0 = BitVec.ofNat 64 p.n
  save : ∀ i < 13, word s.mem p.B (8 * p.n - saveBytes + 8 * i) = p.sv i
  sp : s.sp = p.sp
  dims : Dims p

theorem St.toE {p : PP} {s : State} (h : St p s) : ESt p s :=
  ⟨h.scr, h.s6, h.args.wsLen, h.save, h.sp, h.dims⟩

/-- `ESt` survives a change outside the working space. -/
theorem ESt.frame {p : PP} {s t : State} (h : ESt p s) (hm : ∀ x, ofs p.B x < p.Z → t.mem x = s.mem x)
    {regs : List Reg} (k : Keep regs s t) (hsp : t.sp = s.sp) (h6 : Reg.s6 ∉ regs) : ESt p t := by
  have hnw := h.scr.nowrap
  have hdn := h.dims.n
  have hb := h.dims.b1
  have hf : Frm p.B [(p.Z, 2 ^ 64)] s.mem t.mem := fun x hx => hm x (by
    have h1 := hx _ (List.mem_singleton_self _)
    have h2 := (x - p.B).isLt
    simp only [ofs] at h1 h2 ⊢; omega_arith)
  have wd : ∀ d, d + 8 ≤ p.Z → word t.mem p.B d = word s.mem p.B d := fun d hd =>
    hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl hd) (by omega_arith)
  exact ⟨h.scr.congr k.2.2, (k.gpr h6).trans h.s6, (wd 0 (by simp only [PP.Z, PP.L] at *; omega_arith)).trans h.len,
    fun i hi => (wd _ (by simp only [PP.Z, PP.L, saveBytes] at *; omega_arith)).trans (h.save i hi), hsp.trans h.sp,
    h.dims⟩

/-- `out` as the contract states it. -/
def outOf (p : PP) : Option (Option Nat × List Byte) → List Byte
  | some (some c, _) => Spec.Rsa.i2osp c p.L
  | _ => List.replicate p.L 0

/-- `used` as the contract states it. -/
def usedOf (p : PP) : Option (Option Nat × List Byte) → Nat
  | some (_, rest) => p.r.length - rest.length
  | none => 0

/-- The end of a candidate, before the exit. -/
def CEnd (p : PP) (res : Option (Option Nat × List Byte)) (t : State) : Prop :=
  ESt p t ∧ t.gpr .a0 = BitVec.ofNat 64 (Proof.Ffdh.candidateStatus res) ∧
    Spec.Rsa.bytesAt t.mem p.op p.L = outOf p res ∧ t.mem.readW p.up 64 = BitVec.ofNat 64 (usedOf p res)

/-- A store to `used` keeps the working space and `out`. -/
theorem used_store {p : PP} {s : State} (h : Bufs p s) {m m' : Mem} (hm : Outside p.up 0 8 m m') :
    (∀ x, ofs p.B x < p.Z → m' x = m x) ∧ Spec.Rsa.bytesAt m' p.op p.L = Spec.Rsa.bytesAt m p.op p.L := by
  have hnu := h.scrU.nowrap
  have hno := h.oNW
  refine ⟨fun x hx => hm x (Or.inr ?_), ?_⟩
  · by_contra hc
    have := h.sepU x (by omega_arith)
    omega_arith
  · simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hm _ (Or.inr ?_)
    have hi' := List.mem_range.mp hi
    by_contra hc
    exact h.dOU _ (VG.Proof.Bignum.contains_byte p.op hi' (by omega_arith)) (by
      simp only [Region.Contains]; simp only [ofs] at hc; omega)

/-- `finish` for a candidate without p, from `St`. -/
theorem finEnd {p : PP} {s : State} (h : St p s) {r v : Nat} (hr : r = 0 ∨ r = 2)
    {res : Option (Option Nat × List Byte)} (hst : Proof.Ffdh.candidateStatus res = r)
    (hout : outOf p res = List.replicate p.L 0) (huse : usedOf p res = if r = 0 then 0 else v)
    (hv : word s.mem p.B 152 = BitVec.ofNat 64 v) :
    WP isa (.block (finish r)) s (CEnd p res) := by
  have hdn := h.dims.n
  refine WP.mono (WP.rdwr (finish_ok r (by omega_arith) h.scr h.bufs.scrU h.s6 h.args.usedP' hv
    (by simp only [PP.Z, PP.L] at *; omega_arith))) fun t ⟨⟨⟨t3, tm⟩, k⟩, _, _, tsp⟩ => ?_
  have hO : Outside p.up 0 8 s.mem t.mem := by rw [tm]; exact writeW_outside _ _ _ (by omega_arith)
  obtain ⟨hws, hob⟩ := used_store h.bufs hO
  refine ⟨h.toE.frame hws k tsp (by decide), by rw [t3, hst], by rw [hob, h.bufs.bO, hout], ?_⟩
  have e0 : off p.up 0 = p.up := by simp [off]
  rw [tm, e0, Mem.readW_writeW_self64, huse]

/-- A header word, kept by a change outside the working space. -/
theorem word_of_ws {p : PP} {m m' : Mem} (hm : ∀ x, ofs p.B x < p.Z → m' x = m x) {d : Nat} (hd : d + 8 ≤ p.Z)
    (hnw : p.B.toNat + p.Z ≤ 2 ^ 64) : m'.readW (p.B + BitVec.ofNat 64 d) 64 = m.readW (p.B + BitVec.ofNat 64 d) 64 :=
  (show Frm p.B [(p.Z, 2 ^ 64)] m m' from fun x hx => hm x (by
    have h1 := hx _ (List.mem_singleton_self _)
    have h2 := (x - p.B).isLt
    simp only [ofs] at h1 h2 ⊢; omega_arith)).word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl hd)
    (by omega_arith)

/-- `out`'s bytes are writable. -/
theorem Bufs.outW {p : PP} {s : State} (h : Bufs p s) : ∀ i < p.L, InRegions s.wr (off p.op i) 1 :=
  fun _ hi => ⟨_, h.oW, VG.Proof.Bignum.contains_byte _ hi (by have := h.oNW; omega_arith)⟩

/-- p to `out`, then `finish` with the status 1. -/
theorem pEnd {C : Nat} {p : PP} {s : State} {c u : Nat} (h : St p s) (hp : Ph p p.bits C s)
    (hn : wv s.mem p.B 256 (wOf p.bits) = c) (hc : c < 2 ^ p.bits)
    (hv : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) :
    WP isa (.seq writeP (.block (finish 1))) s (CEnd p (some (some c, p.r.drop u))) := by
  have hdn := h.dims.n
  have hb1 := h.dims.b1
  have hnw := h.scr.nowrap
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  have h7 : s.gpr .a7 = off p.B 256 := hp.a7.trans (by rw [show slot (wOf p.bits) 0 = 256 by simp [slot, hdrBytes]])
  refine WP.seq (WP.mono (WP.rdwr (writeP_ok h.scr h.bufs.outW h.bufs.oNW h.s6 h7 h.args.out' h.args.len'
    (by omega_arith) (by omega_arith) h.bufs.sepO)) fun t₁ ⟨⟨⟨tb, tout⟩, k₁⟩, _, _, sp₁⟩ => ?_)
  have hws₁ : ∀ x, ofs p.B x < p.Z → t₁.mem x = s.mem x := fun x hx => tout x (Or.inr (by
    by_contra hc'
    have := h.bufs.sepO x (by omega_arith)
    omega_arith))
  have E₁ := h.toE.frame hws₁ k₁ sp₁ (by decide)
  refine WP.mono (WP.rdwr (finish_ok 1 (by decide) E₁.scr (h.bufs.scrU.congr k₁.2.2) E₁.s6
    ((word_of_ws hws₁ (d := 32) (by omega_arith) hnw).trans h.args.usedP')
    ((word_of_ws hws₁ (d := 152) (by omega_arith) hnw).trans hv) (by omega_arith)))
    fun t ⟨⟨⟨t3, tm⟩, k⟩, _, _, tsp⟩ => ?_
  have hO : Outside p.up 0 8 t₁.mem t.mem := by rw [tm]; exact writeW_outside _ _ _ (by omega_arith)
  obtain ⟨hws, hob⟩ := used_store h.bufs hO
  refine ⟨E₁.frame hws k tsp (by decide), by rw [t3]; rfl, ?_, ?_⟩
  · rw [hob]
    simp only [outOf]
    refine Pub.out_bytes (w := wOf p.bits) (by simp only [wOf]; omega_arith) hn ?_ tb
    rw [VG.Proof.Bignum.pow256_eq]
    exact Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) (by omega_arith))
  · have e0 : off p.up 0 = p.up := by simp [off]
    rw [tm, e0, Mem.readW_writeW_self64]
    simp only [usedOf, List.length_drop, Nat.one_ne_zero, ↓reduceIte]
    congr 1; omega_arith

/-! ## The exit -/

theorem exitA_ok {p : PP} {t : State} (h : ESt p t) :
    WP isa (.block [ldh .t3 hWsLen, .shift .sll .d .t3 .t3 3, .add .t3 .s6 .t3, .addi .t3 .t3 (-104)]) t fun u =>
      (u.gpr .t3 = off p.B (8 * p.n - 104) ∧ u.mem = t.mem) ∧ Keep [.t3] t u := by
  have hdn := h.dims.n
  have hb := h.dims.b1
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have h80 : 104 ≤ 8 * p.n := by omega_arith
  have hZe : p.Z = 8 * p.n := rfl
  have e1 : p.B + BitVec.ofNat 64 (8 * p.n) - BitVec.ofNat 64 104 = off p.B (8 * p.n - 104) :=
    VG.Offset.add_ofNat_sub p.B h80
  have l0 : InRegions (t.rd ++ t.wr) p.B 8 := by simpa using h.scr.ld (d := 0) (n := 8) (by omega_arith)
  have a0 : p.B.toNat % 8 = 0 := h.scr.al
  have w0 : t.mem.readW p.B 64 = BitVec.ofNat 64 p.n := by simpa [word, off] using h.len
  refine WP.keep _ ?_ (by rfl) (by rfl)
  simp only [ldh, hWsLen]
  brun [h.s6, BitVec.add_zero, add_ofNat_zero, l0, a0, w0, shl3_ofNat, e1]

theorem saved_inj : ∀ i < 13, ∀ j < 13, saved i = saved j → i = j := by decide

theorem saved_ne3 : ∀ i < 13, saved i ≠ .t3 := by decide

/-- The first `k` registers restored to `v`, from the state `sB`. -/
structure XI (sB : State) (S : Addr) (v : Nat → BitVec 64) (k : Nat) (s : State) : Prop where
  t3 : s.gpr .t3 = S
  restored : ∀ i < k, s.gpr (saved i) = v i
  others : ∀ r, (∀ i < 13, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp

theorem restore_step (sB : State) {S : Addr} {v : Nat → BitVec 64}
    (hin : ∀ i < 13, InRegions (sB.rd ++ sB.wr) (off S (8 * i)) 8)
    (hal : ∀ i < 13, (off S (8 * i)).toNat % 8 = 0)
    (hv : ∀ i < 13, sB.mem.readW (off S (8 * i)) 64 = v i)
    {k : Nat} (hk : k < 13) {s : State} (h : XI sB S v k s) :
    WP isa (.block [.load .d (saved k) .t3 (8 * k)]) s (XI sB S v (k + 1)) := by
  have hin' : InRegions (s.rd ++ s.wr) (s.gpr .t3 + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [h.rd, h.wr, h.t3]; exact hin k hk
  have ha : (s.gpr .t3 + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 := by rw [h.t3]; exact hal k hk
  have hv' : s.mem.readW (S + BitVec.ofNat 64 (8 * k)) 64 = v k := by rw [h.mem]; exact hv k hk
  have hn3 := saved_ne3 k hk
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show 8 * k < 2048 by omega_arith) ha hin', Option.some.injEq, exists_eq_left', h.t3, hv']
  refine ⟨?_, fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (Ne.symm hn3)]; exact h.t3
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved k := fun e => absurd (saved_inj i (by omega_arith) k hk e) (by omega_arith)
      rw [ite_eq_right_iff.mpr fun e' => absurd e' e]; exact h.restored i hi
    · rw [ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (hr k hk)]
    exact h.others r hr

/-- The exit: the registers back from the save area. -/
theorem exit_ok {p : PP} {t : State} (h : ESt p t) :
    WP isa (.block exit) t fun u =>
      (∀ i < 13, u.gpr (saved i) = p.sv i) ∧ u.mem = t.mem ∧ u.sp = t.sp ∧
        ∀ r, r ≠ .t3 → (∀ i < 13, r ≠ saved i) → u.gpr r = t.gpr r := by
  have hdn := h.dims.n
  have hb := h.dims.b1
  have hn' := h.dims.n'
  have hZe : p.Z = 8 * p.n := rfl
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  unfold exit
  rw [map_flatMap, WP.block_append_iff]
  refine WP.mono (WP.rdwr (exitA_ok h)) fun sB ⟨⟨⟨b3, bm⟩, kb⟩, _, _, bsp⟩ => ?_
  have e : ∀ i, off (off p.B (8 * p.n - 104)) (8 * i) = off p.B (8 * p.n - 104 + 8 * i) := fun i => by
    simp only [off, BitVec.add_assoc, BitVec.ofNat_add]
  have hs : Scr sB p.B p.Z := h.scr.congr kb.2.2
  have hin : ∀ i < 13, InRegions (sB.rd ++ sB.wr) (off (off p.B (8 * p.n - 104)) (8 * i)) 8 := fun i hi => by
    rw [e]; exact hs.ld (by omega_arith)
  have hal : ∀ i < 13, (off (off p.B (8 * p.n - 104)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [e]; exact hs.al8 (by omega_arith) (by omega_arith)
  have hv : ∀ i < 13, sB.mem.readW (off (off p.B (8 * p.n - 104)) (8 * i)) 64 = p.sv i := fun i hi => by
    rw [bm, e]
    exact h.save i (by omega_arith)
  refine WP.mono (WP.rdwr (wp_range_flatMap (M := isa) (XI sB (off p.B (8 * p.n - 104)) p.sv)
    (fun k s hk hs => restore_step sB hin hal hv hk hs) 13 (Nat.le_refl _) sB
    ⟨b3, fun _ h => absurd h (by omega_arith), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩)) fun u ⟨hu, _, _, usp⟩ => ?_
  refine ⟨hu.restored, by rw [hu.mem, bm], ?_, fun r h3 hs => by rw [hu.others r hs, kb.gpr (by simpa using h3)]⟩
  rw [usp, bsp]

/-! ## The front -/

/-- The candidate's arguments, on entry. -/
def ppOf (s : State) : PP where
  B := s.gpr .a7
  n := (stackArg s 0).toNat
  op := s.gpr .a0
  up := s.gpr .a2
  bits := (s.gpr .a3).toNat
  g := ((s.gpr .a4).setWidth 32).toNat
  rp := s.gpr .a5
  r := pcRand s
  sp := s.sp
  sv i := s.gpr (saved i)

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

theorem zext_eq (x : BitVec 64) : (x <<< 32) >>> 32 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-- Memory kept outside a region. -/
theorem out_word {O B : Addr} {L Z : Nat} {m m' : Mem} (hd : (⟨O, L⟩ : Region).Disjoint ⟨B, Z⟩)
    (hm : Outside O 0 L m m') (hnw : B.toNat + Z ≤ 2 ^ 64) {d : Nat} (hdz : d + 8 ≤ Z) :
    m'.readW (B + BitVec.ofNat 64 d) 64 = m.readW (B + BitVec.ofNat 64 d) 64 := by
  refine Mem.readW_congr fun i hi => hm _ (Or.inr ?_)
  by_contra hc
  exact hd (B + BitVec.ofNat 64 d + BitVec.ofNat 64 i) (by simp only [Region.Contains]; simp only [ofs] at hc; omega_arith)
    (by simp only [Region.Contains]; rw [VG.Offset.add_add, Mem.sub_ofNat_toNat B (by omega_arith)]; omega_arith)

theorem saved_notin : ∀ i < 13, saved i ∉ ([.t3, .t4] : List Reg) := by decide

theorem front_ok (s : State) (h : pcPre s) :
    WP isa (.seq (.block entry) zeroOut) s fun t =>
      St (ppOf s) t ∧ word t.mem (ppOf s).B 152 = BitVec.ofNat 64 (ppOf s).L ∧
        Frame [⟨s.gpr .a7, 8 * (stackArg s 0).toNat⟩, ⟨s.gpr .a0, (s.gpr .a1).toNat⟩] s.mem t.mem ∧
        t.rd = s.rd := by
  obtain ⟨hsp, hsp16, hspT, hrd, hwr, dOU, dOR, dOS, dOA, dUR, dUS, dUA, dRS, dSA, qO, qU, qR, qS, qA, nwO, nwU,
    nwR, nwS, alU, alS, hb1, hb2, hL, hg, hsw, -⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsw
  have hn : stackArg s 0 = BitVec.ofNat 64 (stackArg s 0).toNat := (ofNat_toNat _).symm
  have h80 : 104 ≤ 8 * (stackArg s 0).toNat := by omega_arith
  have hscr : Scr s (s.gpr .a7) (8 * (stackArg s 0).toNat) :=
    Scr.of_mem (by rw [hwr, Nat.mul_comm]; simp) (by omega_arith) alS
  have hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8 :=
    ⟨⟨stackArgAddr s 0, 8⟩, by rw [hrd]; simp, by simp [Region.Contains]⟩
  refine WP.seq ?_
  simp only [entry]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.rdwr (entryA_ok rfl hn hargs (by omega_arith) h80)) fun tA ⟨⟨⟨a4, a3, am⟩, ka⟩, _, _, asp⟩ => ?_
  refine WP.mono (saves_ok (s₀ := tA) a4 h80 (by omega_arith) (fun i hi => by
    rw [ka.2.2]; exact hscr.st (by omega_arith)) fun i hi => hscr.al8 (by omega_arith) (by omega_arith)) fun tS hS => ?_
  have hS7 : tS.gpr .a7 = s.gpr .a7 := by rw [hS.gpr, ka.gpr (by decide)]
  refine WP.mono (WP.rdwr <| header_ok (s := tS) hS7 (fun d hd => by
    rw [hS.wr, ka.2.2]; exact hscr.st (d := d) (by omega_arith)) fun d hd h8 => hscr.al8 (by omega_arith) h8)
    fun t₁ ⟨⟨⟨c6, c4, cm⟩, kc⟩, _, _, csp⟩ => ?_
  have gS : ∀ r, r ∉ ([.t3, .t4] : List Reg) → tS.gpr r = s.gpr r := fun r hr => by
    rw [hS.gpr]; exact ka.gpr hr
  have hS3 : tS.gpr .t3 = BitVec.ofNat 64 (stackArg s 0).toNat := by rw [hS.gpr]; exact a3
  obtain ⟨w0, w16, w24, w152, w32, w40, w128, w136, w144⟩ := hdrW_words tS.mem (s.gpr .a7) (tS.gpr .t3)
    (tS.gpr .a0) (tS.gpr .a1) (tS.gpr .a2) (tS.gpr .a3) ((tS.gpr .a4 <<< 32) >>> 32) (tS.gpr .a5) (tS.gpr .a6)
  rw [← cm] at w0 w16 w24 w152 w32 w40 w128 w136 w144
  have hwr₁ : t₁.wr = s.wr := by rw [kc.2.2, hS.wr, ka.2.2]
  have hscr₁ : Scr t₁ (s.gpr .a7) (8 * (stackArg s 0).toNat) := hscr.congr hwr₁
  have hO₁ : ∀ i < (s.gpr .a1).toNat, InRegions t₁.wr (off (s.gpr .a0) i) 1 := fun i hi =>
    ⟨_, by rw [hwr₁, hwr]; simp, VG.Proof.Bignum.contains_byte _ hi (by omega_arith)⟩
  refine WP.mono (WP.rdwr (zeroOut_ok (s := t₁) hscr₁ hO₁ c6 (by rw [gS _ (by decide)] at w16; exact w16)
    (by rw [gS _ (by decide), ← ofNat_toNat (s.gpr .a1)] at w24; exact w24) (by omega_arith) (by omega_arith)
    (by omega_arith))) fun t ⟨⟨⟨zb, zo⟩, kz⟩, _, _, zsp⟩ => ?_
  have hnw := hscr.nowrap
  have dOS' : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint ⟨s.gpr .a7, 8 * (stackArg s 0).toNat⟩ := by
    rw [Nat.mul_comm]; exact dOS
  have wsW : ∀ d, d + 8 ≤ 8 * (stackArg s 0).toNat →
      t.mem.readW (s.gpr .a7 + BitVec.ofNat 64 d) 64 = t₁.mem.readW (s.gpr .a7 + BitVec.ofNat 64 d) 64 :=
    fun d hd => out_word dOS' zo hnw hd
  -- The memory, changed only in the working space and `out`.
  have fr : Frame [⟨s.gpr .a7, 8 * (stackArg s 0).toNat⟩, ⟨s.gpr .a0, (s.gpr .a1).toNat⟩] s.mem t.mem := by
    have ws_of : ∀ x, (∀ r ∈ ([⟨s.gpr .a7, 8 * (stackArg s 0).toNat⟩, ⟨s.gpr .a0, (s.gpr .a1).toNat⟩] : List Region),
        ¬ r.Contains x 1) → 8 * (stackArg s 0).toNat ≤ ofs (s.gpr .a7) x ∧ (s.gpr .a1).toNat ≤ ofs (s.gpr .a0) x :=
      fun x hx => by
        have h1 := hx _ (List.mem_cons_self ..)
        have h2 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        simp only [Region.Contains, ofs] at h1 h2 ⊢; omega_arith
    intro x hx
    obtain ⟨hx1, hx2⟩ := ws_of x hx
    rw [zo x (Or.inr (by omega_arith)), cm, hdrW_frm _ _ _ _ _ _ _ _ _ _ x (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (by omega_arith)), hS.out x (Or.inr (by omega_arith)), am]
  have hlen : (pcRand s).length = (s.gpr .a6).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  have hLe : (s.gpr .a1).toNat = (ppOf s).L := hL
  have hd : ∀ {d}, d + 8 ≤ 256 → word t.mem (s.gpr .a7) d = word t₁.mem (s.gpr .a7) d := fun hd' =>
    wsW _ (by omega_arith)
  have sav : ∀ i < 13, word t.mem (s.gpr .a7) (8 * (stackArg s 0).toNat - saveBytes + 8 * i) = (ppOf s).sv i := by
    intro i hi
    simp only [saveBytes]
    rw [show word t.mem (s.gpr .a7) (8 * (stackArg s 0).toNat - 104 + 8 * i) =
        word t₁.mem (s.gpr .a7) (8 * (stackArg s 0).toNat - 104 + 8 * i) from wsW _ (by omega_arith), cm,
      (hdrW_frm _ _ _ _ _ _ _ _ _ _).word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by omega_arith))
        (by omega_arith), hS.saved i hi, ka.gpr (saved_notin i hi)]
    rfl
  have dRS' : (⟨s.gpr .a5, (s.gpr .a6).toNat⟩ : Region).Disjoint ⟨s.gpr .a7, 8 * (stackArg s 0).toNat⟩ := by
    rw [Nat.mul_comm]; exact dRS
  have dUS' : (⟨s.gpr .a2, 8⟩ : Region).Disjoint ⟨s.gpr .a7, 8 * (stackArg s 0).toNat⟩ := by
    rw [Nat.mul_comm]; exact dUS
  have hwrt : t.wr = s.wr := by rw [kz.2.2, hwr₁]
  have hspt : t.sp = s.sp := by rw [zsp, csp, hS.sp, asp]
  refine ⟨⟨hscr₁.congr kz.2.2, (kz.gpr (by decide)).trans c6,
    ⟨(hd (d := 0) (by decide)).trans (w0.trans hS3),
     (hd (d := 16) (by decide)).trans (w16.trans (gS .a0 (by decide))),
     (hd (d := 24) (by decide)).trans (w24.trans ((gS .a1 (by decide)).trans (by rw [← hLe, ofNat_toNat]))),
     (hd (d := 32) (by decide)).trans (w32.trans (gS .a2 (by decide))),
     (hd (d := 40) (by decide)).trans (w40.trans ((gS .a3 (by decide)).trans (ofNat_toNat _).symm)),
     (hd (d := 128) (by decide)).trans (w128.trans (by rw [gS .a4 (by decide), zext_eq]; rfl)),
     (hd (d := 136) (by decide)).trans (w136.trans (gS .a5 (by decide))),
     (hd (d := 144) (by decide)).trans (w144.trans ((gS .a6 (by decide)).trans (by
       rw [show (ppOf s).r.length = (s.gpr .a6).toNat from hlen, ofNat_toNat])))⟩,
    ⟨fun i hi => ?_, fun i hi x hx he => ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, ?_, fun x hx => ?_,
      by show (below s.sp 96).Disjoint ⟨s.gpr .a5, (pcRand s).length⟩; rw [hlen]; exact qR,
      by show (below s.sp 96).Disjoint ⟨s.gpr .a0, (ppOf s).L⟩; rw [← hLe]; exact qO, qU, by
      show (⟨s.gpr .a0, (ppOf s).L⟩ : Region).Disjoint _; rw [← hLe]; exact dOU⟩,
    ⟨hb1, hb2, hg, by simp only [ppOf, PP.L] at hLe ⊢; omega_arith, by simp only [ppOf]; omega_arith,
      by show (pcRand s).length < 2 ^ 64; rw [hlen]; exact (s.gpr .a6).isLt⟩,
    by rw [hwrt, hwr]; simp [ppOf, PP.Z, Nat.mul_comm], hspt, hsp, hsp16,
    by show (below s.sp 96).Disjoint ⟨s.gpr .a7, 8 * (stackArg s 0).toNat⟩; rw [Nat.mul_comm]; exact qS,
    sav⟩,
    (hd (d := 152) (by decide)).trans (w152.trans ((gS .a1 (by decide)).trans (by rw [← hLe, ofNat_toNat]))),
    fr, by rw [kz.2.1, kc.2.1, hS.rd, ka.2.1]⟩
  · rw [kz.2.1, kc.2.1, hS.rd, ka.2.1, hrd]
    rw [show (ppOf s).r.length = (s.gpr .a6).toNat from hlen] at hi
    exact ⟨⟨s.gpr .a5, (s.gpr .a6).toNat⟩, by simp, VG.Proof.Bignum.contains_byte _ hi (by omega_arith)⟩
  · rw [show (ppOf s).r.length = (s.gpr .a6).toNat from hlen] at hi
    subst he
    exact dRS' _ (VG.Proof.Bignum.contains_byte _ hi (by omega_arith)) (VG.Proof.Bignum.contains_scr hx)
  · show Spec.Rsa.bytesAt t.mem (s.gpr .a5) (pcRand s).length = pcRand s
    rw [hlen]
    refine VG.Proof.Rsa.rsa_bytes_frame fr (s.gpr .a6).isLt fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRS'
    · exact dOR.symm
  · show Spec.Rsa.bytesAt t.mem (s.gpr .a0) (ppOf s).L = List.replicate (ppOf s).L 0
    rw [← hLe]; exact Pub.zero_bytes zb
  · show (⟨s.gpr .a0, (ppOf s).L⟩ : Region) ∈ t.wr
    rw [← hLe, hwrt, hwr]; simp
  · show (s.gpr .a0).toNat + (ppOf s).L ≤ 2 ^ 64
    rw [← hLe]; exact nwO
  · have hx' : ofs (s.gpr .a0) x < (s.gpr .a1).toNat := by rw [hLe]; exact hx
    exact VG.Proof.Bignum.out_scr dOS' (by simp only [Region.Contains]; simp only [ofs] at hx'; omega_arith)
  · exact (Scr.of_mem (by rw [hwr]; simp) nwU alU).congr hwrt
  · have hx' : ofs (s.gpr .a2) x < 8 := hx
    exact VG.Proof.Bignum.out_scr dUS' (by simp only [Region.Contains]; simp only [ofs] at hx'; omega_arith)

end VG.Proof.Ffdh.RISCV64.ParameterCandidate
