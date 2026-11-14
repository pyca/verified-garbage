module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.PArith
public import VerifiedGarbage.Proof.Dsa.RISCV64.Elem
public import VerifiedGarbage.Proof.Bignum.RISCV64.ModExpWin
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.PackedRead
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Rsa.Octets
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

-- separate module: the power in the P space imports the modular exponentiation's proofs, which the key
-- working space's arithmetic (`PArith`) does not need

/-! # DSA parameter search on RISC-V: the power in the P space

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/Power.lean` and `GPow.lean`). `power
pLen qLen` (`Impl/Dsa/RISCV64/ParameterSearch.lean`) works in the P space,
`pZ pLen` bytes at `pB` of `scratch`, a working space of the DSA functions'
layout (`Env`, with `w = p_len / 8`): `powA_ok`, p from `sPBE` into array
0, `−p⁻¹ mod 2⁶⁴` into `t1` and `R² mod p` into arrays 1 and 24; `powC_ok`,
h from `s7` into array 4, its power by the exponent at `sE` into array 4, its
word `w` zeroed, and `a0 = 0` exactly when it is above 1 and below p. As
pieces (`power_vp`), `powA` and h's pointer are analysed with `s6` public,
`powC` with the P space's registers and h's pointer public. `gStore_vp`:
`g`, array 4, big-endian at `sG`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Proof.Dsa.RISCV64 (Env loadArr_ok rr_ok storeBE_ok elemRange_ok wordsVal_mod_two loadRegs rrRegs
  storeRegs elemRangeRegs)
open VG.Proof.Bignum (slot)
open VG.Impl.Dsa.RISCV64.ParameterSearch

/-- The P space's bytes. -/
abbrev pZ (pLen : Nat) : Nat := kB pLen - pB

/-- The P space's words. -/
abbrev pw (pLen : Nat) : Nat := pLen / 8

/-- The P space's base. -/
abbrev GP.pS (G : GP) : Addr := off G.scr pB

theorem pZ_ok {L : Nat} (hl : L = 128 ∨ L = 256 ∨ L = 384) :
    slot (pw L) 28 ≤ pZ L ∧ pB + pZ L = kB L ∧ 16 ≤ pw L ∧ pw L ≤ 48 ∧ 8 * pw L = L ∧
      8 * (pw L + 2) = L + 16 := by
  rcases hl with rfl | rfl | rfl <;> decide

theorem slot_eq (w j : Nat) : slot w j = 256 + j * (8 * (w + 2)) := rfl

theorem lui_pB : sext32 (BitVec.ofNat 20 (pB / 4096) ++ (0 : BitVec 12)) = BitVec.ofNat 64 pB := by decide

/-- The registers `powA` writes. -/
def powARegs : List Reg :=
  [.a7, .t0, .s5, .s7, .s8] ++ loadRegs ++ [.s0, .s1, .s2, .s3, .t1] ++ rrRegs

/-- `powA`: into the P space at `B = S + pB`, p from the `pLen` bytes at
`S + sPBE` into array 0 (word `w` zero), `−p⁻¹ mod 2⁶⁴` into `t1` and `R² mod p`
into arrays 1 and 24. -/
theorem powA_ok {s : State} {G : GP} (hl : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384)
    (h6 : s.gpr .s6 = G.scr) (hs : Scr s G.pS (pZ G.pLen))
    (hrd : ∀ i < G.pLen, InRegions (s.rd ++ s.wr) (off (G.sa sPBE) i) 1)
    (hsep : ∀ i < G.pLen, ∀ x, ofs G.pS x < pZ G.pLen → off (G.sa sPBE) i ≠ x) {P : Nat}
    (hP : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (G.sa sPBE) G.pLen) = P) (hp : 2 ≤ P) (hpo : P % 2 = 1) :
    WP isa (powA G.pLen) s fun t =>
      (Env t G.pS (pZ G.pLen) (pw G.pLen) ∧ wordsVal t.mem G.pS (slot (pw G.pLen) 0) (pw G.pLen) = P ∧
        word t.mem G.pS (slot (pw G.pLen) 0 + 8 * pw G.pLen) = 0 ∧
        ((word t.mem G.pS (slot (pw G.pLen) 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0 ∧
        wordsVal t.mem G.pS (slot (pw G.pLen) 1) (pw G.pLen) = 2 ^ (128 * pw G.pLen) % P ∧
        wordsVal t.mem G.pS (slot (pw G.pLen) 24) (pw G.pLen) = 2 ^ (128 * pw G.pLen) % P ∧
        Outside G.pS (slot (pw G.pLen) 0) (25 * (8 * (pw G.pLen + 2))) s.mem t.mem) ∧ Keep powARegs s t := by
  have ⟨z28, zk, w16, w48, w8, wS⟩ := pZ_ok hl
  have hnw := hs.nowrap
  have e := slot_eq (pw G.pLen)
  have e0 := e 0; have e1 := e 1; have e24 := e 24; have e25 := e 25; have e28 := e 28
  have p11 : G.pLen < 2048 := by omega
  -- Into the P space.
  have hb : WP isa (.block (enterP G.pLen ++ [scr .s7 sPBE, .li .s8 G.pLen])) s fun u =>
      (u.gpr .a7 = off G.pS (slot (pw G.pLen) 0) ∧ u.gpr .t0 = BitVec.ofNat 64 (pw G.pLen) ∧
        u.gpr .s5 = BitVec.ofNat 64 (8 * (pw G.pLen + 2)) ∧ u.gpr .s7 = off (G.sa sPBE) 0 ∧
        u.gpr .s8 = BitVec.ofNat 64 G.pLen ∧ u.mem = s.mem) ∧ Keep [.a7, .t0, .s5, .s7, .s8] s u := by
    have p8 : G.pLen / 8 < 2048 := by omega
    have p16 : G.pLen + 16 < 2048 := by omega
    rw [show enterP G.pLen ++ [scr .s7 sPBE, .li .s8 G.pLen] = scrB .a7 pB ++
      [.addi .a7 .a7 VG.Impl.Bignum.hdrBytes, .li .t0 (G.pLen / 8), .li .s5 (G.pLen + 16), scr .s7 sPBE,
        .li .s8 G.pLen] from rfl]
    refine scrB_ok (by decide) h6 (by decide) (by decide) fun s₁ k₁ m₁ sp₁ a₁ => ?_
    refine wp_addi (imm := VG.Impl.Bignum.hdrBytes) (by decide) fun s₂ u₂ => ?_
    refine wp_li p8 fun s₃ u₃ => wp_li p16 fun s₄ u₄ => ?_
    refine wp_addi (imm := sPBE) (by decide) fun s₅ u₅ => wp_li p11 fun t u => WP.block_nil ?_
    have K : Keep [.a7, .t0, .s5, .s7, .s8] s t := ⟨fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [u.other _ hr.2.2.2.2, u₅.other _ hr.2.2.2.1, u₄.other _ hr.2.2.1, u₃.other _ hr.2.1,
          u₂.other _ hr.1, k₁.gpr (by simpa using hr.1)],
      by rw [u.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, k₁.2.1], by rw [u.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, k₁.2.2]⟩
    have h6' : s₄.gpr .s6 = G.scr := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), k₁.gpr (by decide), h6]
    refine ⟨⟨?_, ?_, ?_, ?_, u.gpr, by rw [u.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]⟩, K⟩
    · rw [u.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
        a₁, e0, Nat.zero_mul, Nat.add_zero]; rfl
    · rw [u.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
    · rw [u.other _ (by decide), u₅.other _ (by decide), u₄.gpr, wS]
    · rw [u.other _ (by decide), u₅.gpr, h6', VG.Proof.Mont.off, BitVec.add_zero]
  unfold powA
  rw [show VG.Impl.Rsa.RISCV64.Keys.seqs [Code.block (enterP G.pLen ++ [scr .s7 sPBE, .li .s8 G.pLen]),
      VG.Impl.Dsa.RISCV64.loadArr 0, .block VG.Impl.Bignum.RISCV64.Precompute.minv, VG.Impl.Dsa.RISCV64.rr] =
    .seq (.block (enterP G.pLen ++ [scr .s7 sPBE, .li .s8 G.pLen])) (.seq (VG.Impl.Dsa.RISCV64.loadArr 0)
      (.seq (.block VG.Impl.Bignum.RISCV64.Precompute.minv) VG.Impl.Dsa.RISCV64.rr)) from rfl]
  refine WP.seq (WP.mono hb fun s₁ ⟨⟨a7, t0, s5, s7, s8, m1⟩, k1⟩ => ?_)
  have en1 : Env s₁ G.pS (pZ G.pLen) (pw G.pLen) := ⟨hs.congr k1.2.2, a7, s5, t0, by omega, w48, z28⟩
  refine WP.seq (WP.mono (loadArr_ok en1 (j := 0) (N := G.sa sPBE) (by decide) s7 s8 (by omega) (by omega)
    (fun i hi => by rw [k1.2.1, k1.2.2]; exact hrd i hi) hsep) fun s₂ ⟨⟨v0, top0, o2, a7'⟩, k2⟩ => ?_)
  rw [m1, hP] at v0
  have en2 : Env s₂ G.pS (pZ G.pLen) (pw G.pLen) :=
    ⟨en1.hs.congr k2.2.2, a7', (k2.gpr (by decide)).trans s5, (k2.gpr (by decide)).trans t0, en1.w2, w48, z28⟩
  have hodd : (word s₂.mem G.pS (slot (pw G.pLen) 0)).toNat % 2 = 1 := by
    rw [wordsVal_mod_two _ _ _ (w := pw G.pLen) (by omega), v0]; exact hpo
  refine WP.seq (WP.mono (minv_ok en2.hs en2.a7 (by rw [e0]; omega) (by omega) hodd)
    fun s₃ ⟨⟨i3, m3⟩, k3⟩ => ?_)
  have en3 := en2.keep k3
  refine WP.mono (rr_ok en3 (by rw [m3, v0]; exact hp)) fun t ⟨⟨r1, r24, o4⟩, k4⟩ => ?_
  rw [m3, v0] at r1 r24
  rw [m3] at o4
  refine ⟨⟨en3.keep k4, ?_, ?_, ?_, r1, r24, ?_⟩, ((k1.trans k2).trans (k3.trans k4)).mono (by decide)⟩
  · show wordsVal t.mem _ _ _ = _
    rw [o4.wordsVal (d := slot (pw G.pLen) 0) (k := pw G.pLen) (by omega) (by omega)]; exact v0
  · rw [o4.word (d := slot (pw G.pLen) 0 + 8 * pw G.pLen) (by omega) (by omega)]; exact top0
  · rw [o4.word (d := slot (pw G.pLen) 0) (by omega) (by omega), k4.gpr (by decide)]; exact i3
  · rw [← m1]
    exact (o2.mono (o' := slot (pw G.pLen) 0) (n' := 25 * (8 * (pw G.pLen + 2))) (Nat.le_refl _)
      (by omega)).trans (o4.mono (by omega) (by omega))

theorem zeroTop4_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) :
    WP isa (.block zeroTop4) s fun t =>
      (t.mem = s.mem.writeW (off B (slot w 4 + 8 * w)) (0 : BitVec 64)) ∧ Keep [.t3, .s0] s t := by
  have hnw := h.hs.nowrap
  have hZ := h.arr (j := 4) (by decide)
  have e := slot_eq w
  have e4 := e 4; have e5 := e 5
  unfold zeroTop4
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .t3) (by decide) 5) fun t₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  have ea : off B (slot w 5) - BitVec.ofNat 64 16 = off B (slot w 4 + 8 * w) := by
    rw [off_sub B (by omega)]; congr 1; omega
  have st : InRegions t₁.wr (off B (slot w 4 + 8 * w)) 8 := (h.hs.congr k1.2.2).st (by omega)
  have al : (off B (slot w 4 + 8 * w)).toNat % 8 = 0 := h.hs.al8 (by omega) (by rw [e4]; omega)
  refine wp_subi (imm := 16) (by decide) fun u₁ v₁ => wp_li (imm := 0) (by decide) fun u₂ v₂ => ?_
  refine wp_sd (off := 0) (a := off B (slot w 4 + 8 * w)) (by decide)
    (by rw [v₂.other _ (by decide), v₁.gpr, a3, BitVec.add_zero, ea]) al
    (by rw [v₂.wr, v₁.wr]; exact st) fun u₃ m₃ => WP.block_nil ?_
  refine ⟨by rw [m₃.mem, v₂.gpr, v₂.mem, v₁.mem, m1]; rfl, ⟨fun r hr => ?_, by rw [m₃.rd, v₂.rd, v₁.rd, k1.2.1],
    by rw [m₃.wr, v₂.wr, v₁.wr, k1.2.2]⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [m₃.gpr, v₂.other _ hr.2, v₁.other _ hr.1, k1.gpr (by simpa using hr.1)]

/-- The registers `powC` writes. -/
def powCRegs : List Reg :=
  loadRegs ++ VG.Proof.Dsa.RISCV64.copyRegs ++ [.s9, .s10] ++ VG.Proof.Bignum.RISCV64.Win.powWRegs ++
    [.t3, .s0] ++ elemRangeRegs

/-- `powC`: h (the `pLen` bytes at `H`, `s7`) into array 4, `h^e mod p` for
the `eB` bytes of `e` at `S + sE` into array 4, and `a0 = 0` exactly when it
is above 1 and below p. -/
theorem powC_ok {s : State} {G : GP} {H : Addr} {p : Nat} (hl : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384)
    (en : Env s G.pS (pZ G.pLen) (pw G.pLen)) (h6 : s.gpr .s6 = G.scr)
    (h7 : s.gpr .s7 = off H 0) (h8 : s.gpr .s8 = BitVec.ofNat 64 G.pLen)
    (hHrd : ∀ i < G.pLen, InRegions (s.rd ++ s.wr) (off H i) 1)
    (hHsep : ∀ i < G.pLen, ∀ x, ofs G.pS x < pZ G.pLen → off H i ≠ x)
    (heB : 1 ≤ eBytes G.pLen G.qLen) (heB' : eBytes G.pLen G.qLen < 2048)
    (hErd : ∀ i < eBytes G.pLen G.qLen, InRegions (s.rd ++ s.wr) (off (G.sa sE) i) 1)
    (hEsep : ∀ i < eBytes G.pLen G.qLen, ∀ x, ofs G.pS x < pZ G.pLen → off (G.sa sE) i ≠ x)
    (hp0 : wordsVal s.mem G.pS (slot (pw G.pLen) 0) (pw G.pLen) = p)
    (hinv : ((word s.mem G.pS (slot (pw G.pLen) 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hp : 2 ≤ p) (hpo : p % 2 = 1) (hrr : wordsVal s.mem G.pS (slot (pw G.pLen) 24) (pw G.pLen) = 2 ^ (128 * pw G.pLen) % p) :
    WP isa (powC G.pLen G.qLen) s fun t =>
      (wordsVal t.mem G.pS (slot (pw G.pLen) 4) (pw G.pLen) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem H G.pLen) ^
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (G.sa sE) (eBytes G.pLen G.qLen)) % p ∧
        (t.gpr .a0 = 0 ↔ 1 < wordsVal t.mem G.pS (slot (pw G.pLen) 4) (pw G.pLen) ∧ wordsVal t.mem G.pS (slot (pw G.pLen) 4) (pw G.pLen) < p) ∧
        Env t G.pS (pZ G.pLen) (pw G.pLen) ∧
        Outside G.pS (slot (pw G.pLen) 1) (23 * (8 * (pw G.pLen + 2))) s.mem t.mem) ∧
      Keep powCRegs s t := by
  have ⟨z28, zk, w16, w48, w8, wS⟩ := pZ_ok hl
  have hnw := en.hs.nowrap
  have e := slot_eq (pw G.pLen)
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e8 := e 8; have e24 := e 24
  have e28 := e 28
  unfold powC
  rw [show VG.Impl.Rsa.RISCV64.Keys.seqs [VG.Impl.Dsa.RISCV64.loadArr 4, VG.Impl.Dsa.RISCV64.copy 1 24,
      Code.block [scr .s9 sE, .li .s10 (eBytes G.pLen G.qLen)], VG.Impl.Bignum.RISCV64.ModExp.powWin,
      .block zeroTop4, VG.Impl.Dsa.RISCV64.elemRange] =
    .seq (VG.Impl.Dsa.RISCV64.loadArr 4) (.seq (VG.Impl.Dsa.RISCV64.copy 1 24)
      (.seq (.block [scr .s9 sE, .li .s10 (eBytes G.pLen G.qLen)]) (.seq VG.Impl.Bignum.RISCV64.ModExp.powWin
        (.seq (.block zeroTop4) VG.Impl.Dsa.RISCV64.elemRange)))) from rfl]
  -- h into array 4.
  refine WP.seq (WP.mono (loadArr_ok en (j := 4) (N := H) (by decide) h7 h8 (by omega) (by omega) hHrd hHsep)
    fun s₁ ⟨⟨v4, top4, o1, a7⟩, k1⟩ => ?_)
  have en1 : Env s₁ G.pS (pZ G.pLen) (pw G.pLen) :=
    ⟨en.hs.congr k1.2.2, a7, (k1.gpr (by decide)).trans en.s5, (k1.gpr (by decide)).trans en.t0, en.w2, w48, z28⟩
  -- `R² mod p` into array 1.
  refine WP.seq (WP.mono (VG.Proof.Dsa.RISCV64.copy_ok en1 (o := 1) (a := 24) (by decide) (by decide) (by decide))
    fun s₂ ⟨⟨c2, o2⟩, k2⟩ => ?_)
  have en2 := en1.keep k2
  have A1 : wordsVal s₂.mem G.pS (slot (pw G.pLen) 1) (pw G.pLen) = 2 ^ (128 * pw G.pLen) % p := by
    show wordsVal _ _ _ _ = _
    rw [VG.Proof.Dsa.RISCV64.wordsVal_congr (m := s₁.mem) (d := slot (pw G.pLen) 24) fun i hi => c2 i (by omega),
      o1.wordsVal (by omega) (by omega)]
    exact hrr
  have A0 : wordsVal s₂.mem G.pS (slot (pw G.pLen) 0) (pw G.pLen) = p := by
    show wordsVal _ _ _ _ = _
    rw [o2.wordsVal (by omega) (by omega), o1.wordsVal (by omega) (by omega)]; exact hp0
  have A4 : wordsVal s₂.mem G.pS (slot (pw G.pLen) 4) (pw G.pLen) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem H G.pLen) := by
    show wordsVal _ _ _ _ = _
    rw [o2.wordsVal (by omega) (by omega)]; exact v4
  have W0 : word s₂.mem G.pS (slot (pw G.pLen) 0) = word s.mem G.pS (slot (pw G.pLen) 0) := by
    rw [o2.word (by omega) (by omega), o1.word (by omega) (by omega)]
  -- The exponent's pointer and length.
  have h6₂ : s₂.gpr .s6 = G.scr := (k2.gpr (by decide)).trans ((k1.gpr (by decide)).trans h6)
  have hEb : WP isa (.block [scr .s9 sE, .li .s10 (eBytes G.pLen G.qLen)]) s₂ fun u =>
      (u.gpr .s9 = off (G.sa sE) 0 ∧ u.gpr .s10 = BitVec.ofNat 64 (eBytes G.pLen G.qLen) ∧ u.mem = s₂.mem) ∧
        Keep [.s9, .s10] s₂ u := by
    refine wp_addi (imm := sE) (by decide) fun u₁ v₁ => wp_li heB' fun u₂ v₂ => WP.block_nil ?_
    refine ⟨⟨by rw [v₂.other _ (by decide), v₁.gpr, h6₂, VG.Proof.Mont.off, BitVec.add_zero], v₂.gpr,
      by rw [v₂.mem, v₁.mem]⟩, ⟨fun r hr => ?_, by rw [v₂.rd, v₁.rd], by rw [v₂.wr, v₁.wr]⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [v₂.other _ hr.2, v₁.other _ hr.1]
  refine WP.seq (WP.mono hEb fun s₃ ⟨⟨b9, b10, m3⟩, k3⟩ => ?_)
  have en3 := en2.keep k3
  have hE : ∀ i < eBytes G.pLen G.qLen, InRegions (s₃.rd ++ s₃.wr) (off (G.sa sE) i) 1 := fun i hi => by
    rw [k3.2.1, k3.2.2, k2.2.1, k2.2.2, k1.2.1, k1.2.2]; exact hErd i hi
  refine WP.seq (WP.mono (VG.Proof.Bignum.RISCV64.Win.powWin_ok (D := G.sa sE) (L := eBytes G.pLen G.qLen)
    en3.hs (by omega) (by omega) (by omega) en3.a7 en3.s5 en3.t0
    (by rw [m3, W0, k3.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide)]; exact hinv)
    (by rw [m3, A0]; exact hp) (by rw [m3, A0]; exact hpo) (by rw [m3, A0, A1]; exact Nat.mod_lt _ (by omega))
    b9 b10 heB (by omega) hE hEsep) fun s₄ ⟨⟨r4, o4⟩, k4⟩ => ?_)
  have pw2 : 2 ^ (64 * pw G.pLen) * 2 ^ (64 * pw G.pLen) = 2 ^ (128 * pw G.pLen) := by
    rw [← Nat.pow_add, show 64 * pw G.pLen + 64 * pw G.pLen = 128 * pw G.pLen by omega]
  have eE : Spec.Rsa.bytesAt s₂.mem (G.sa sE) (eBytes G.pLen G.qLen) =
      Spec.Rsa.bytesAt s.mem (G.sa sE) (eBytes G.pLen G.qLen) := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    have hn := fun h' => hEsep i hi _ h' rfl
    rcases Nat.lt_or_ge (ofs G.pS (off (G.sa sE) i)) (pZ G.pLen) with h | h
    · exact absurd h hn
    · have h' : pZ G.pLen ≤ (off (G.sa sE) i - G.pS).toNat := h
      rw [o2 _ (.inr (by show _ ≤ (off (G.sa sE) i - G.pS).toNat; omega)),
        o1 _ (.inr (by show _ ≤ (off (G.sa sE) i - G.pS).toNat; omega))]
  rw [m3] at r4
  have v5 := r4 (by rw [A1, A0, pw2])
  rw [A4, A0, eE] at v5
  have o4' : Outside G.pS (slot (pw G.pLen) 1) (23 * (8 * (pw G.pLen + 2))) s₃.mem s₄.mem := o4
  have o3 : Outside G.pS (slot (pw G.pLen) 1) (23 * (8 * (pw G.pLen + 2))) s₂.mem s₃.mem :=
    fun _ _ => by rw [m3]
  have en4 := en3.keep k4
  -- Array 4's word `w` zeroed.
  refine WP.seq (WP.mono (zeroTop4_ok en4) fun s₅ ⟨m5, k5⟩ => ?_)
  have en5 := en4.keep k5
  have wo : Outside G.pS (slot (pw G.pLen) 4 + 8 * pw G.pLen) 8 s₄.mem s₅.mem := by
    rw [m5]; exact VG.Proof.Mont.writeW_outside s₄.mem G.pS 0 (by omega)
  have top5 : word s₅.mem G.pS (slot (pw G.pLen) 4 + 8 * pw G.pLen) = 0 := by
    rw [m5]; exact VG.Proof.Mont.word_writeW_self _ _ _ _
  have v6 : wordsVal s₅.mem G.pS (slot (pw G.pLen) 4) (pw G.pLen) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem H G.pLen) ^
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (G.sa sE) (eBytes G.pLen G.qLen)) % p := by
    show wordsVal _ _ _ _ = _
    rw [wo.wordsVal (d := slot (pw G.pLen) 4) (k := pw G.pLen) (by omega) (by omega)]; exact v5
  have p6 : wordsVal s₅.mem G.pS (slot (pw G.pLen) 0) (pw G.pLen) = p := by
    show wordsVal _ _ _ _ = _
    rw [wo.wordsVal (d := slot (pw G.pLen) 0) (k := pw G.pLen) (by omega) (by omega),
      o4'.wordsVal (d := slot (pw G.pLen) 0) (k := pw G.pLen) (by omega) (by omega), m3]; exact A0
  refine WP.mono (elemRange_ok en5 top5) fun t ⟨⟨r0, v7, o7, en7⟩, k7⟩ => ?_
  rw [show wordsVal s₅.mem G.pS (slot (pw G.pLen) 0) (pw G.pLen) = p from p6] at r0
  refine ⟨⟨by show wordsVal _ _ _ _ = _; rw [v7]; exact v6, by rw [show wordsVal t.mem G.pS (slot (pw G.pLen) 4) (pw G.pLen) =
      wordsVal s₅.mem G.pS (slot (pw G.pLen) 4) (pw G.pLen) from v7]; exact r0, en7, ?_⟩,
    ((k1.trans k2).trans ((k3.trans k4).trans (k5.trans k7))).mono (by decide)⟩
  exact (((((o1.mono (o' := slot (pw G.pLen) 1) (n' := 23 * (8 * (pw G.pLen + 2))) (by omega) (by omega)).trans
    (o2.mono (by omega) (by omega))).trans o3).trans o4').trans (wo.mono (by omega) (by omega))).trans
    (o7.mono (by omega) (by omega))

/-! ## As pieces -/

section
variable {G : GP} {STK : Nat} {σ : State} {V : Nat → BitVec 64} {LS : List Nat} {s : State}

theorem GI.pBig (h : GI G STK σ V LS s) : pB + pZ G.pLen ≤ G.scrLen * 8 ∧ hEnd ≤ pB := by
  have := h.wBig; have := h.kBig; have := (pZ_ok h.lens).2.1
  exact ⟨by omega, by decide⟩

/-- A range of `scratch` as a working space. -/
theorem GI.scrAt (h : GI G STK σ V LS s) {o n : Nat} (ho : o + n ≤ G.scrLen * 8) (hn : 0 < n) (h8 : o % 8 = 0) :
    Scr s (off G.scr o) n := by
  have f := h.scrFit; have a := h.scrAl
  have e : (off G.scr o).toNat = G.scr.toNat + o := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨⟨G.scr, o, G.scrLen * 8, by rw [h.wr, h.pre.wr, h.hG]; simp, rfl, ho, by omega⟩, ?_, ?_⟩
  · rw [e]; omega
  · rw [e]; omega

/-- An address outside `[S + a, S + a + Z)`, by its distance from `S`, is
at least `Z` past `S + a`. -/
theorem le_ofs_off {S x : Addr} {a Z : Nat} (ha' : a < 2 ^ 64) (ha : a + Z ≤ 2 ^ 64)
    (h : (x - S).toNat < a ∨ a + Z ≤ (x - S).toNat) : Z ≤ ofs (off S a) x := by
  have hlt := (x - S).isLt
  simp only [ofs, off]
  rw [Offset.toNat_sub_add x S (by omega)]
  rcases h with h | h
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - a + (x - S).toNat = (x - S).toNat - a + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- The bytes of `scratch` at `a`, below the P space, as a source of a load into it. -/
theorem GI.srcBelow (h : GI G STK σ V LS s) {a n : Nat} (ha : a + n ≤ pB) :
    (∀ i < n, InRegions (s.rd ++ s.wr) (off (G.sa a) i) 1) ∧
      ∀ i < n, ∀ x, ofs G.pS x < pZ G.pLen → off (G.sa a) i ≠ x := by
  have ⟨pb, _⟩ := h.pBig
  have fit := h.scrFit
  refine ⟨fun i hi => ?_, fun i hi x hx e => ?_⟩
  · rw [show off (G.sa a) i = G.sa (a + i) from G.sa_add a i]
    exact h.inRdWr (by omega)
  · subst e
    have d : (off (G.sa a) i - G.scr).toNat = a + i := by
      rw [show off (G.sa a) i = G.scr + BitVec.ofNat 64 (a + i) from G.sa_add a i, Offset.add_sub_cancel_left,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have : pZ G.pLen ≤ ofs G.pS (off (G.sa a) i) :=
      le_ofs_off (S := G.scr) (a := pB) (by decide) (by omega) (.inl (by omega))
    omega

end

/-- Bytes apart from `scratch` are apart from the P space. -/
theorem src_apart {G : GP} {H : Addr} {n : Nat} (hd : Region.Disjoint ⟨H, n⟩ G.rScr) (hfit : H.toNat + n ≤ 2 ^ 64)
    (hp : pB + pZ G.pLen ≤ G.scrLen * 8) :
    ∀ i < n, ∀ x, ofs G.pS x < pZ G.pLen → off H i ≠ x := by
  intro i hi x hx e
  subst e
  have := past_of_disjoint' hd (a := off H i) (Offset.contains_base _ (show i + 1 ≤ n by omega) (by omega))
  have : pZ G.pLen ≤ ofs G.pS (off H i) :=
    le_ofs_off (S := G.scr) (a := pB) (by decide) (by omega) (.inr (by omega))
  omega

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- A step that writes the P space alone keeps a stage whose claims are apart from it. -/
theorem SS.of_pspace {σ s t : State} {ws : List Reg} (h : SS G STK0 σ c s) (k : Keep ws s t) (sp : t.sp = s.sp)
    {lo n : Nat} (o : Outside G.pS lo n s.mem t.mem) (hn : lo + n ≤ pZ G.pLen)
    (hcl : ∀ x ∈ c.cl, Apart pB (pZ G.pLen) x) (h6 : .s6 ∉ ws := by decide) : SS G STK0 σ c t := by
  have ⟨pb, pk⟩ := h.gi.pBig
  have zk := (pZ_ok h.lens).2.1
  have f0 : Frame [G.rs pB (pZ G.pLen)] s.mem t.mem :=
    frame_of_outside (L := pZ G.pLen) (o.mono (Nat.zero_le _) (by omega))
  have f : Frame (G.rss [(pB, pZ G.pLen)] ++ [rBelow σ STK0]) s.mem t.mem :=
    f0.mono fun r hr => List.mem_append_left _ hr
  have e : { c with cl := c.cl } = c := rfl
  rw [← e]
  exact h.of_scrs (ws := ws) k sp (os := [(pB, pZ G.pLen)])
    (fun p hp => by
      rw [List.mem_singleton] at hp; subst hp
      refine ⟨pk, .inl (by simp only [List.length_replicate]; omega), by simp only [List.length_replicate]; omega⟩)
    f (cl' := c.cl) (fun x hx => .inl ⟨hx, fun p hp => by rw [List.mem_singleton] at hp; subst hp; exact hcl x hx⟩) h6

/-- After `powA`: p in array 0, its word `w` zero, `−p⁻¹` in `t1`, and `R² mod p` in arrays 1 and 24. -/
abbrev PA (G : GP) (c : Cfg) (X : State → Prop) (pv : Nat) (σ s : State) : Prop :=
  St G c X σ s ∧ Env s G.pS (pZ G.pLen) (pw G.pLen) ∧ wordsVal s.mem G.pS (slot (pw G.pLen) 0) (pw G.pLen) = pv ∧
    ((word s.mem G.pS (slot (pw G.pLen) 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0 ∧
    wordsVal s.mem G.pS (slot (pw G.pLen) 24) (pw G.pLen) = 2 ^ (128 * pw G.pLen) % pv

/-- p from `sPBE` into the P space. -/
theorem powA_vp {pv : Nat} (hPc : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c.cl) (hpv : pv < 256 ^ G.pLen)
    (hp2 : 2 ≤ pv) (hpo : pv % 2 = 1) (hcl : ∀ x ∈ c.cl, Apart pB (pZ G.pLen) x) :
    VP (St G c X) (powA G.pLen) (PA G c X pv) := by
  refine VP.pub (SS.pub fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
    (powA G.pLen), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_
  have gi := h.gi
  have ⟨pb, pE⟩ := gi.pBig
  have l := gi.lens
  have hb' : Spec.Rsa.bytesAt s.mem (G.sa sPBE) G.pLen = Spec.Rsa.i2osp pv G.pLen := by
    have := h.sb _ hPc
    simp only [VG.Proof.Rsa.i2osp_length] at this
    exact this
  have ev : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (G.sa sPBE) G.pLen) = pv := by
    rw [hb', VG.Proof.Rsa.os2ip_i2osp, Nat.mod_eq_of_lt hpv]
  have hsrc := gi.srcBelow (a := sPBE) (n := G.pLen) (by rcases l with e | e | e <;> rw [e] <;> decide)
  refine WP.sp_eq (WP.mono (powA_ok l gi.s6 (gi.scrAt pb (by have := (pZ_ok l).1; have := slot_eq (pw G.pLen) 28; omega) (by decide)) hsrc.1 hsrc.2 ev hp2 hpo)
    fun t ⟨⟨en, v0, _, inv, _, v24, o⟩, k⟩ sp => ?_)
  refine ⟨⟨h.of_pspace k sp o ?_ hcl, x⟩, en, v0, inv, v24⟩
  have ⟨z28, _⟩ := pZ_ok l
  have e := slot_eq (pw G.pLen)
  have := e 0; have := e 28; omega

/-- After `h`'s pointer and its length. -/
abbrev PE (G : GP) (c : Cfg) (X : State → Prop) (pv : Nat) (H : Addr) (σ s : State) : Prop :=
  PA G c X pv σ s ∧ s.gpr .s7 = off H 0 ∧ s.gpr .s8 = BitVec.ofNat 64 G.pLen

/-- `h`'s pointer, from the header word `fH`, and its length. -/
theorem hPtr_vp {pv : Nat} {H : Addr} (hH : fH ∈ c.LS) (hHv : c.V fH = H) :
    VP (PA G c X pv) (.block [ld .s7 fH, .li .s8 G.pLen]) (PE G c X pv H) := by
  refine VP.pub (SS.pub fun σ s h => h.1.1) [] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
    (.block [ld .s7 fH, .li .s8 G.pLen]), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s ⟨⟨h, x⟩, en, v0, inv, v24⟩ => ?_
  have l := h.lens
  have p11 : G.pLen < 2048 := by rcases l with e | e | e <;> rw [e] <;> decide
  refine h.ldK (o := fH) (by decide) (by decide) ((h.gi.slotV hH).trans hHv) (t := .s7) (by decide)
    fun s₁ h₁ u₁ => wp_li p11 fun t u => WP.block_nil ?_
  have K : Keep [.s7, .s8] s t := ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u.other _ hr.2, u₁.other _ hr.1], by rw [u.rd, u₁.rd], by rw [u.wr, u₁.wr]⟩
  have mt : t.mem = s.mem := by rw [u.mem, u₁.mem]
  refine ⟨⟨⟨h₁.of_upd u (by decide), x⟩, en.keep K, by rw [mt]; exact v0,
    by rw [mt, K.gpr (by decide)]; exact inv, by rw [mt]; exact v24⟩, ?_, u.gpr⟩
  rw [u.other _ (by decide), u₁.gpr, VG.Proof.Mont.off, BitVec.add_zero]

/-- The certificate of `powC`. -/
abbrev CertC (pLen qLen : Nat) : Prop := ∃ hc, (VG.Taint.check VG.RISCV64.taint
  (Taint.ofRegs [.s6, .s7, .s8, .a7, .s5, .t0]) (powC pLen qLen) hc).isSome = true

/-- `powC`'s certificate, for any widths. -/
theorem certC (pLen qLen : Nat) : CertC pLen qLen :=
  ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .s7, .s8, .a7, .s5, .t0]) (powC pLen qLen),
    by kernel_rfl⟩

/-- h into array 4, its power, and the range check. -/
theorem powC_vp {pv ev : Nat} {H : Addr} {hb : List Byte} (cert : CertC G.pLen G.qLen)
    (hEc : (sE, Spec.Rsa.i2osp ev (eBytes G.pLen G.qLen)) ∈ c.cl) (hev : ev < 256 ^ eBytes G.pLen G.qLen)
    (hp2 : 2 ≤ pv) (hpo : pv % 2 = 1) (hcl : ∀ x ∈ c.cl, Apart pB (pZ G.pLen) x)
    (hsrc : ∀ σ s, St G c X σ s → (∀ i < G.pLen, InRegions (s.rd ++ s.wr) (off H i) 1) ∧
      Region.Disjoint ⟨H, G.pLen⟩ G.rScr ∧ H.toNat + G.pLen ≤ 2 ^ 64 ∧ Spec.Rsa.bytesAt s.mem H G.pLen = hb) :
    VP (PE G c X pv H) (powC G.pLen G.qLen) (fun σ t => St G c X σ t ∧ Env t G.pS (pZ G.pLen) (pw G.pLen) ∧
      wordsVal t.mem G.pS (slot (pw G.pLen) 4) (pw G.pLen) = Spec.Rsa.os2ip hb ^ ev % pv ∧
      (t.gpr .a0 = 0 ↔ 1 < wordsVal t.mem G.pS (slot (pw G.pLen) 4) (pw G.pLen) ∧ wordsVal t.mem G.pS (slot (pw G.pLen) 4) (pw G.pLen) < pv)) := by
  refine VP.taint _ cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
      rw [(SS.pub (G := G) (fun σ s (h : PE G c X pv H σ s) => h.1.1.1) σ₁ s₁ h₁).2,
        (SS.pub (G := G) (fun σ s (h : PE G c X pv H σ s) => h.1.1.1) σ₂ s₂ h₂).2])
    (fun σ₁ σ₂ s₁ s₂ ⟨⟨⟨h₁, _⟩, e₁, _⟩, c7, c8⟩ ⟨⟨⟨h₂, _⟩, e₂, _⟩, f7, f8⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₁.gi.s6, h₂.gi.s6]
      · rw [c7, f7]
      · rw [c8, f8]
      · rw [e₁.a7, e₂.a7]
      · rw [e₁.s5, e₂.s5]
      · rw [e₁.t0, e₂.t0]) fun σ s ⟨⟨⟨h, x⟩, en, v0, inv, v24⟩, a7, a8⟩ => ?_
  have gi := h.gi
  have ⟨pb, _⟩ := gi.pBig
  have l := gi.lens
  have lq := qLen_of l
  have heB : 1 ≤ eBytes G.pLen G.qLen ∧ eBytes G.pLen G.qLen < 2048 ∧ sE + eBytes G.pLen G.qLen ≤ pB := by
    simp only [eBytes]; rcases lq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> decide
  have hEb : Spec.Rsa.bytesAt s.mem (G.sa sE) (eBytes G.pLen G.qLen) = Spec.Rsa.i2osp ev (eBytes G.pLen G.qLen) := by
    have := h.sb _ hEc
    simp only [VG.Proof.Rsa.i2osp_length] at this
    exact this
  have ev' : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (G.sa sE) (eBytes G.pLen G.qLen)) = ev := by
    rw [hEb, VG.Proof.Rsa.os2ip_i2osp, Nat.mod_eq_of_lt hev]
  obtain ⟨hrd, hdj, hfit, hbs⟩ := hsrc σ s ⟨h, x⟩
  have hE := gi.srcBelow (a := sE) (n := eBytes G.pLen G.qLen) heB.2.2
  refine WP.sp_eq (WP.mono (powC_ok l en gi.s6 a7 a8 hrd (src_apart hdj hfit pb) heB.1 heB.2.1 hE.1 hE.2 v0
    inv hp2 hpo v24) fun t ⟨⟨v4, r0, en', o⟩, k⟩ sp => ?_)
  rw [ev', hbs] at v4
  refine ⟨⟨h.of_pspace k sp o ?_ hcl, x⟩, en', v4, r0⟩
  have ⟨z28, _⟩ := pZ_ok l
  have e := slot_eq (pw G.pLen)
  have := e 1; have := e 28; omega

/-- `power`: `h^e mod p` into array 4 of the P space, for p at `sPBE`, `e`
at `sE` and `h` at the header word `fH`, and `a0 = 0` exactly when it is
above 1 and below p. -/
theorem power_vp {pv ev : Nat} {H : Addr} {hb : List Byte} (cert : CertC G.pLen G.qLen)
    (hPc : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c.cl) (hpv : pv < 256 ^ G.pLen) (hp2 : 2 ≤ pv) (hpo : pv % 2 = 1)
    (hEc : (sE, Spec.Rsa.i2osp ev (eBytes G.pLen G.qLen)) ∈ c.cl) (hev : ev < 256 ^ eBytes G.pLen G.qLen)
    (hH : fH ∈ c.LS) (hHv : c.V fH = H) (hcl : ∀ x ∈ c.cl, Apart pB (pZ G.pLen) x)
    (hsrc : ∀ σ s, St G c X σ s → (∀ i < G.pLen, InRegions (s.rd ++ s.wr) (off H i) 1) ∧
      Region.Disjoint ⟨H, G.pLen⟩ G.rScr ∧ H.toNat + G.pLen ≤ 2 ^ 64 ∧ Spec.Rsa.bytesAt s.mem H G.pLen = hb) :
    VP (St G c X) (power G.pLen G.qLen) (fun σ t => St G c X σ t ∧ Env t G.pS (pZ G.pLen) (pw G.pLen) ∧
      wordsVal t.mem G.pS (slot (pw G.pLen) 4) (pw G.pLen) = Spec.Rsa.os2ip hb ^ ev % pv ∧
      (t.gpr .a0 = 0 ↔ 1 < wordsVal t.mem G.pS (slot (pw G.pLen) 4) (pw G.pLen) ∧ wordsVal t.mem G.pS (slot (pw G.pLen) 4) (pw G.pLen) < pv)) :=
  VP.seq (powA_vp hPc hpv hp2 hpo hcl) (VP.seq (hPtr_vp hH hHv) (powC_vp cert hEc hev hp2 hpo hcl hsrc))

/-- `g`, array 4 of the P space, big-endian at `sG`. -/
theorem gStore_vp {g : Nat} (hcl : ∀ x ∈ c.cl, Apart sG G.pLen x) :
    VP (fun σ s => St G c X σ s ∧ Env s G.pS (pZ G.pLen) (pw G.pLen) ∧ wordsVal s.mem G.pS (slot (pw G.pLen) 4) (pw G.pLen) = g)
      (.seq (.block [scr .s7 sG, .li .s8 G.pLen]) (VG.Impl.Dsa.RISCV64.storeBE 4))
      (St G { c with cl := (sG, Spec.Rsa.i2osp g G.pLen) :: c.cl } X) := by
  refine VP.pub (SS.pub fun σ s h => h.1.1) [.a7, .s5] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64
    (Taint.ofRegs [.s6, .a7, .s5]) (.seq (.block [scr .s7 sG, .li .s8 G.pLen]) (VG.Impl.Dsa.RISCV64.storeBE 4)),
    by kernel_rfl⟩ (fun σ₁ σ₂ s₁ s₂ ⟨_, e₁, _⟩ ⟨_, e₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [e₁.a7, e₂.a7]
      · rw [e₁.s5, e₂.s5]) fun σ s ⟨⟨h, x⟩, en, v4⟩ => ?_
  have gi := h.gi
  have l := gi.lens
  have ⟨z28, zk, w16, w48, w8, wS⟩ := pZ_ok l
  have ⟨pb, pE⟩ := gi.pBig
  have fit := gi.scrFit
  have big := gi.wBig
  have kb := gi.kBig
  have p11 : G.pLen < 2048 := by omega
  have gL : sG + G.pLen ≤ pB := by rcases l with e | e | e <;> rw [e] <;> decide
  refine WP.seq (wp_addi (by decide) fun s₁ u₁ => wp_li p11 fun s₂ u₂ => WP.block_nil ?_)
  have K2 : Keep [.s7, .s8] s s₂ := ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₂.other _ hr.2, u₁.other _ hr.1], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  have en2 := en.keep K2
  have sNat : (G.sa sG).toNat = G.scr.toNat + sG := by
    rw [GP.sa, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := sG) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have m2 : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine WP.sp_eq (WP.mono (storeBE_ok en2 (j := 4) (O := G.sa sG) (k := G.pLen) (by decide)
    (fun i hi => by rw [show off (G.sa sG) i = G.sa (sG + i) from G.sa_add sG i, K2.2.2]; exact gi.inScr (by omega))
    (by omega) (by rw [u₂.other _ (by decide), u₁.gpr, gi.s6]) u₂.gpr (by omega) (by omega)
    (fun x hx => le_ofs_off (S := G.scr) (a := pB) (by decide) (by omega) (.inl (by
      have := (x - G.sa sG).isLt
      have e : (x - G.scr).toNat = (x - G.sa sG).toNat + sG := by
        rw [show x - G.scr = (x - G.sa sG) + BitVec.ofNat 64 sG by
          rw [GP.sa, ← BitVec.sub_sub, BitVec.sub_add_cancel]]
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := sG) (by omega)]
        simp only [ofs] at hx
        omega
      simp only [ofs] at hx
      omega)))) fun t ⟨⟨bt, ot⟩, kt⟩ sp => ?_)
  have v : Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (G.sa sG) G.pLen) = g := by
    have r : (s₂.mem.read (off G.pS (slot (pw G.pLen) 4)) G.pLen).toNat =
        (s₂.mem.read (off G.pS (slot (pw G.pLen) 4)) (8 * pw G.pLen)).toNat := by rw [w8]
    rw [bt, r, ← VG.Proof.Bignum.wordsVal_read, m2]; exact v4
  have bs : Spec.Rsa.bytesAt t.mem (G.sa sG) G.pLen = Spec.Rsa.i2osp g G.pLen := by
    have := VG.Proof.Rsa.i2osp_os2ip (Spec.Rsa.bytesAt t.mem (G.sa sG) G.pLen)
    rw [show (Spec.Rsa.bytesAt t.mem (G.sa sG) G.pLen).length = G.pLen by simp [Spec.Rsa.bytesAt], v] at this
    exact this.symm
  have h2 : SS G STK0 σ c s₂ := h.of_keep K2 m2 (by rw [u₂.sp, u₁.sp])
  refine ⟨h2.of_scrs (os := [(sG, G.pLen)]) kt sp (fun p hp => ?_) ((frame_of_outside ot).mono (by simp))
    (cl' := (sG, Spec.Rsa.i2osp g G.pLen) :: c.cl) fun y hy => ?_, x⟩
  · simp only [List.mem_singleton] at hp; subst hp
    simp only [ClOk, List.length_replicate]; exact ⟨by decide, .inl (by omega), by omega⟩
  · rcases List.mem_cons.mp hy with rfl | hy
    · exact .inr ⟨by rw [VG.Proof.Rsa.i2osp_length]; exact bs, by
        simp only [ClOk, VG.Proof.Rsa.i2osp_length]; exact ⟨by decide, .inl (by omega), by omega⟩⟩
    · exact .inl ⟨hy, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact hcl y hy⟩

end

end VG.Proof.Dsa.RISCV64.PSearch
