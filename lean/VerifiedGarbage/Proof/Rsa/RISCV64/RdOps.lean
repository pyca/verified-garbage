module

public import VerifiedGarbage.Impl.Rsa.RISCV64.RecoverDet
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyOps
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyDiv
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyBytes
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFios
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The working space and operations of `vg_rsa_recover_primes_det` on RISC-V

The 64-bit counterpart of `Proof/Rsa/KeyViews.lean`, and the operations the
function adds to those of `KeyOps`.

**Views.** The same working space read with `w` words (narrow) and with
`W = W2 w = 2 w + 2` (wide): the wide stride is twice the narrow one
(`S_W2`), so the wide array `j` is the narrow arrays `2 j` and `2 j + 1`
(`arr_W2`), and frames move between the views (`Frame.toNarrow`,
`Frame.toWide`). A wide number is its low narrow half plus `2^(64 w)` times
its upper `w + 2` words (`numW_split`, `hiW_eq`). `ctxInit_ok`, `ctxW_ok`,
`ctxw_ok`: the code that sets the narrow count and moves between the views
keeps the working space (`Ws`); `rd_fits`: the 63 narrow arrays fit the
contract's scratch for every valid `n_len`.

**Operations**, each in either view, keeping the working space, the memory
but what it writes (`Frame`, and for `shlC`, `shl` and `mulLow` only the
first `w` words of the array), and the registers but `opRegs` (`mulRegs` for
`mulLow`):

* `shlC_ok`, `shl_ok`: `[j] := 2 [j] + t4` (`t4 = 0` for `shl`) modulo
  `2^(64 w)`, the bit shifted out in `t4` (`Div.shlBody`, `shlLoop_ok`);
* `add_ok`: `[o] := ([a] + [b]) mod 2^(64 w)`, as `[a] - ([z] - [b])`;
* `mulLow_ok`: `[o] := [y] [x] mod 2^(64 w)` from `[o] = 0`, a row
  (`mulRow_ok`) for each word of `[y]`, each a `mul`/`mulhu` multiply-add of
  the words of `[x]` (`mulLoop_ok`) into the words of `[o]` from it on.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Loops
  VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr sub3 mov)
open VG.Impl.Rsa.RISCV64.Div (shlBody)
open VG.Impl.Rsa.RISCV64.RecoverDet (ctxInit ctxW ctxw shlC shl add mulBody mulRow mulLow)

/-- The wide count of words, `W = 2 w + 2`. -/
abbrev W2 (w : Nat) : Nat := 2 * w + 2

theorem S_W2 (w : Nat) : S (W2 w) = 2 * S w := by simp only [S, W2]; omega_arith

theorem arr_W2 (w j : Nat) : arr (W2 w) j = arr w (2 * j) := by
  simp only [arr, S, W2]
  rw [show 8 * (2 * w + 2 + 2) = 2 * (8 * (w + 2)) by omega_arith, Nat.mul_left_comm, Nat.mul_assoc]

/-- The narrow arrays of the wide arrays `js`. -/
def halves (js : List Nat) : List Nat := js.flatMap fun j => [2 * j, 2 * j + 1]

/-! ## Frames -/

theorem Frame.toNarrow {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Frame B (W2 w) js ds m m') : Frame B w (halves js) ds m m' := by
  intro x hx
  refine h x fun r hr => ?_
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
  · have h0 := hx (arr w (2 * j), S w) (by
      simp only [ranges, halves, List.mem_append, List.mem_map, List.mem_flatMap]
      exact .inl ⟨2 * j, ⟨j, hj, by simp⟩, rfl⟩)
    have h1 := hx (arr w (2 * j + 1), S w) (by
      simp only [ranges, halves, List.mem_append, List.mem_map, List.mem_flatMap]
      exact .inl ⟨2 * j + 1, ⟨j, hj, by simp⟩, rfl⟩)
    have e := arr_succ w (2 * j)
    dsimp only at h0 h1 ⊢
    rw [arr_W2, S_W2]
    omega_arith
  · exact hx (d, 8) (by simp only [ranges, List.mem_append, List.mem_map]; exact .inr ⟨d, hd, rfl⟩)

theorem Frame.toWide {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Frame B w js ds m m') : Frame B (W2 w) (js.map (· / 2)) ds m m' := by
  intro x hx
  refine h x fun r hr => ?_
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
  · have h0 := hx (arr (W2 w) (j / 2), S (W2 w)) (by
      simp only [ranges, List.mem_append, List.mem_map]
      exact .inl ⟨j / 2, ⟨j, hj, rfl⟩, rfl⟩)
    rw [arr_W2, S_W2] at h0
    have e := arr_succ w (2 * (j / 2))
    have lo : arr w (2 * (j / 2)) ≤ arr w j := arr_mono (by omega_arith)
    have hi : arr w j + S w ≤ arr w (2 * (j / 2) + 1) + S w := by
      have := arr_mono (w := w) (show j ≤ 2 * (j / 2) + 1 by omega_arith); omega_arith
    dsimp only at h0 ⊢
    omega_arith
  · exact hx (d, 8) (by simp only [ranges, List.mem_append, List.mem_map]; exact .inr ⟨d, hd, rfl⟩)

/-! ## Numbers -/

/-- The upper `w + 2` words of the wide array `j`: words `w`, `w + 1` of the
narrow array `2 j`, then the narrow array `2 j + 1`. -/
abbrev hiW (m : Mem) (B : Addr) (w j : Nat) : Nat := wordsVal m B (arr w (2 * j) + 8 * w) (w + 2)

theorem hiW_eq (m : Mem) (B : Addr) (w j : Nat) :
    hiW m B w j = wordsVal m B (arr w (2 * j) + 8 * w) 2 + 2 ^ 128 * num m B w (2 * j + 1) := by
  rw [hiW, Nat.add_comm w 2, wordsVal_append,
    show arr w (2 * j) + 8 * w + 8 * 2 = arr w (2 * j + 1) by rw [arr_succ]; simp only [S]; omega_arith]

theorem numW_split (m : Mem) (B : Addr) (w j : Nat) :
    num m B (W2 w) j = num m B w (2 * j) + 2 ^ (64 * w) * hiW m B w j := by
  rw [num, arr_W2, show W2 w = w + (w + 2) by simp only [W2]; omega_arith, wordsVal_append]

theorem numW_low {m : Mem} {B : Addr} {w j : Nat} (hz : hiW m B w j = 0) :
    num m B (W2 w) j = num m B w (2 * j) := by
  rw [numW_split, hz, Nat.mul_zero, Nat.add_zero]

theorem num_low (m : Mem) (B : Addr) (w j : Nat) :
    num m B w (2 * j) = num m B (W2 w) j % 2 ^ (64 * w) := by
  rw [numW_split, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wordsVal_lt _ _ _ _)]

/-- Word `W` of the wide array `j` (Div's `hdz`) is word `w` of the narrow array `2 j + 1`. -/
theorem wideTop (m : Mem) (B : Addr) (w j : Nat) :
    word m B (arr (W2 w) j + 8 * W2 w) = word m B (arr w (2 * j + 1) + 8 * w) := by
  rw [arr_W2, arr_succ]; simp only [S, W2]
  rw [show arr w (2 * j) + 8 * (2 * w + 2) = arr w (2 * j) + 8 * (w + 2) + 8 * w by omega_arith]

/-- The 63 narrow arrays fit the contract's scratch (`scratchWords L` words) for
every `L` that `lenValid` admits. -/
theorem rd_fits {L : Nat} (h1 : 64 ≤ L) (h2 : L ≤ 1024) :
    arr ((L + 7) / 8 + 1) 63 ≤ 8 * (16 * L + 32) ∧ W2 ((L + 7) / 8 + 1) ≤ 1024 := by
  simp only [arr, S, W2, hdr_eq]; omega_arith

/-! ## The counts -/

theorem shl1_ofNat (a : Nat) (h : 2 * a < 2 ^ 64) : BitVec.ofNat 64 a <<< 1 = BitVec.ofNat 64 (2 * a) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := a) (by omega_arith)]
  omega_arith

theorem shr1_ofNat (a : Nat) (h : 2 * a < 2 ^ 64) : BitVec.ofNat 64 (2 * a) >>> 1 = BitVec.ofNat 64 a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (a := a) (by omega_arith)]
  omega_arith

theorem add_ofNat (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add _ _).symm

theorem sub_ofNat2 (a : Nat) : BitVec.ofNat 64 (a + 2) - BitVec.ofNat 64 2 = BitVec.ofNat 64 a := by
  rw [← add_ofNat, BitVec.add_sub_cancel]

/-- `ctxInit`: `s9 := w = ⌈L / 8⌉ + 1` and `s10 := 8 (w + 2)` from `s2 = L`. -/
theorem ctxInit_ok {s : State} {L : Nat} (hl : s.gpr .s2 = BitVec.ofNat 64 L) (hL : L < 2 ^ 32) :
    WP isa (.block ctxInit) s fun t =>
      (t.gpr .s9 = BitVec.ofNat 64 ((L + 7) / 8 + 1) ∧
        t.gpr .s10 = BitVec.ofNat 64 (S ((L + 7) / 8 + 1)) ∧ t.mem = s.mem) ∧ Keep [.s9, .s10] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [ctxInit, hl]
  rw [add7_shr3 L hL]
  refine ⟨add_ofNat _ _, ?_⟩
  simp only [off, add_ofNat, shl3_ofNat, S]

/-- `ctxW`: the narrow view to the wide one. -/
theorem ctxW_ok {s : State} {B : Addr} {Z w N M : Nat} (h : Ws s B Z w N) (hW : W2 w ≤ 1024)
    (hM : 2 * M ≤ N) :
    WP isa (.block ctxW) s fun t => (Ws t B Z (W2 w) M ∧ t.mem = s.mem) ∧ Keep [.s9, .s10] s t := by
  have := h.wle
  have hb : WP isa (.block ctxW) s fun t =>
      (t.gpr .s9 = BitVec.ofNat 64 (W2 w) ∧ t.gpr .s10 = BitVec.ofNat 64 (S (W2 w)) ∧ t.mem = s.mem) ∧
        Keep [.s9, .s10] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [ctxW, h.s9, h.s10, shl1_ofNat w (by omega_arith), shl1_ofNat (S w) (by simp only [S]; omega_arith),
      add_ofNat, S_W2]
  refine WP.mono hb fun t ⟨⟨t9, t10, tm⟩, k⟩ => ⟨⟨⟨h.scr.congr k.2.2, ?_, by simp only [W2]; omega_arith, hW,
    t9, t10, (k.gpr (by decide)).trans h.s11⟩, tm⟩, k⟩
  rw [arr_W2]; exact Nat.le_trans (arr_mono hM) h.fits

/-- `ctxw`: the wide view back to the narrow one. -/
theorem ctxw_ok {s : State} {B : Addr} {Z w N M : Nat} (h : Ws s B Z (W2 w) M) (hw : 0 < w)
    (hN : arr w N ≤ Z) :
    WP isa (.block ctxw) s fun t => (Ws t B Z w N ∧ t.mem = s.mem) ∧ Keep [.s9, .s10] s t := by
  have hle := h.wle
  have hb : WP isa (.block ctxw) s fun t =>
      (t.gpr .s9 = BitVec.ofNat 64 w ∧ t.gpr .s10 = BitVec.ofNat 64 (S w) ∧ t.mem = s.mem) ∧
        Keep [.s9, .s10] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    rw [show W2 w = 2 * w + 2 from rfl] at hle
    brun [ctxw, h.s9, h.s10, S_W2, sub_ofNat2, shr1_ofNat w (by omega_arith),
      shr1_ofNat (S w) (by simp only [S]; omega_arith)]
  refine WP.mono hb fun t ⟨⟨t9, t10, tm⟩, k⟩ =>
    ⟨⟨⟨h.scr.congr k.2.2, hN, hw, by simp only [W2] at hle; omega_arith, t9, t10,
      (k.gpr (by decide)).trans h.s11⟩, tm⟩, k⟩

/-! ## The left shift -/

/-- `shlC j`: `[j] := 2 [j] + t4` modulo `2^(64 w)`, the bit shifted out in `t4`;
only the first `w` words of `j` change. -/
theorem shlC_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 2048) (h4 : (s.gpr .t4).toNat ≤ 1) :
    WP isa (shlC j) s fun t => Ws t B Z w N ∧ Frame B w [j] [] s.mem t.mem ∧
      Outside B (arr w j) (8 * w) s.mem t.mem ∧
      num t.mem B w j + 2 ^ (64 * w) * (t.gpr .t4).toNat = 2 * num s.mem B w j + (s.gpr .t4).toNat ∧
      (t.gpr .t4).toNat ≤ 1 ∧ Keep opRegs s t := by
  have fj := h.arr_fit hj
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  rw [shlC, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (show j < 2048 by omega_arith) ?_
  have hb : WP isa (.block [mov .t3 .s9]) (s.write .t0 (off B (arr w j))) fun u =>
      (u.gpr .t0 = off B (arr w j) ∧ u.gpr .t3 = BitVec.ofNat 64 w ∧ u.gpr .t4 = s.gpr .t4 ∧ u.mem = s.mem) ∧
        Keep [.t3] (s.write .t0 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mov, h.s9, add_ofNat_zero']
  refine WP.mono hb fun u ⟨⟨u0, u3, u4, um⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := ((Keep.write _ _ _).trans ku).mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k₁
  refine WP.mono (shlLoop_ok hu.scr u0 u3 (by rw [u4]; exact h4) (by omega_arith) (by omega_arith) (arr_al _ _)
    (by omega_arith)) fun v ⟨c4, veq, vout, kv⟩ => ?_
  rw [um, u4] at veq
  rw [um] at vout
  exact ⟨hu.of_keep kv, Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using vout) (by omega_arith)
    (by simp), vout, veq, c4, Keep.trans' k₁ kv⟩

/-- `shl j`: `[j] := 2 [j]` modulo `2^(64 w)`, the bit shifted out in `t4`. -/
theorem shl_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 2048) :
    WP isa (shl j) s fun t => Ws t B Z w N ∧ Frame B w [j] [] s.mem t.mem ∧
      Outside B (arr w j) (8 * w) s.mem t.mem ∧
      num t.mem B w j + 2 ^ (64 * w) * (t.gpr .t4).toNat = 2 * num s.mem B w j ∧
      (t.gpr .t4).toNat ≤ 1 ∧ Keep opRegs s t := by
  rw [shl, WP.seq_iff]
  have hb : WP isa (.block [.li .t4 0]) s fun u => (u.gpr .t4 = 0 ∧ u.mem = s.mem) ∧ Keep [.t4] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero]
  refine WP.mono hb fun u ⟨⟨u4, um⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := ku.mono (by decide)
  refine WP.mono (shlC_ok (h.of_keep k₁) hj hN (by rw [u4]; decide)) fun v ⟨hv, fv, ov, ev, cv, kv⟩ => ?_
  rw [um] at fv ov ev
  rw [u4] at ev
  exact ⟨hv, fv, ov, by simpa using ev, cv, Keep.trans' k₁ kv⟩

/-! ## The sum -/

/-- The arithmetic of `add`: `t = (0 - b) mod X`, then `o = (a - t) mod X`. -/
theorem add_mod_arith {X o t a b c₁ c₂ : Nat} (ho : o < X) (h₁ : t + b = X * c₁) (h₂ : o + t = a + X * c₂)
    (hc₁ : c₁ ≤ 1) (hc₂ : c₂ ≤ 1) : o = (a + b) % X := by
  rcases (show c₁ = 0 ∨ c₁ = 1 by omega_arith) with e₁ | e₁ <;>
    rcases (show c₂ = 0 ∨ c₂ = 1 by omega_arith) with e₂ | e₂ <;>
    subst e₁ e₂ <;> simp only [Nat.mul_zero, Nat.mul_one] at h₁ h₂
  · rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · omega_arith
  · rw [show a + b = o + X by omega_arith, Nat.add_mod_right, Nat.mod_eq_of_lt ho]
  · rw [show a + b = o by omega_arith, Nat.mod_eq_of_lt ho]

/-- `add o a b z t`: `[o] := ([a] + [b]) mod 2^(64 w)`, through `[t] := [z] - [b]`, `[z] = 0`. -/
theorem add_ok {s : State} {B : Addr} {Z w N o a b z t : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hz : z < N) (ht : t < N) (hN : N ≤ 2048)
    (htz : t ≠ z) (htb : t ≠ b) (hta : t ≠ a) (hoa : o ≠ a) (hot : o ≠ t)
    (hz0 : num s.mem B w z = 0) :
    WP isa (add o a b z t) s fun u => Ws u B Z w N ∧ Frame B w [t, o] [] s.mem u.mem ∧
      num u.mem B w o = (num s.mem B w a + num s.mem B w b) % 2 ^ (64 * w) ∧ Keep opRegs s u := by
  rw [add, WP.seq_iff]
  refine WP.mono (sub3_ok h ht hz hb hN htz htb) fun u ⟨hu, fu, eu, cu, ku⟩ => ?_
  refine WP.mono (sub3_ok hu ho ha ht hN hoa hot) fun v ⟨hv, fv, ev, cv, kv⟩ => ?_
  have ua : num u.mem B w a = num s.mem B w a :=
    fu.num (by simpa using hta) (by simp) (h.fit64 ha)
  rw [hz0, Nat.zero_add] at eu
  rw [ua] at ev
  exact ⟨hv, fu.join fv, add_mod_arith (wordsVal_lt _ _ _ _) eu ev cu cv, Keep.trans' ku kv⟩

/-! ## The product -/

/-- The arithmetic of a word of a row: the low word of `p q + o + c` and its
high word, the high word of `p q` plus both carries. -/
theorem mul_word_arith (p q o c : BitVec 64) :
    (p * q + o + c).toNat +
      2 ^ 64 * (BitVec.ofNat 64 (p.toNat * q.toNat / 2 ^ 64) + (if p * q + o < o then 1 else 0) +
        (if p * q + o + c < c then 1 else 0)).toNat =
      p.toNat * q.toNat + o.toNat + c.toNat := by
  have hp := p.isLt
  have hq := q.isLt
  have ho := o.isLt
  have hc := c.isLt
  have hP : p.toNat * q.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  simp only [BitVec.toNat_add (_ + _), BitVec.toNat_add (BitVec.ofNat 64 _), carry_toNat]
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  by_cases h1 : 2 ^ 64 ≤ p.toNat * q.toNat % 2 ^ 64 + o.toNat <;>
    by_cases h2 : 2 ^ 64 ≤ (p.toNat * q.toNat % 2 ^ 64 + o.toNat) % 2 ^ 64 + c.toNat <;>
    simp only [h1, h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- A row's multiply-add (`countLoop .t3 mulBody`): the `n` words at `t0`
plus `a6` times the `n` words at `t1` plus the carry in `t4`, the carry out
in `t4`. -/
theorem mulLoop_ok {s : State} {B : Addr} {Z dO dX n : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dO) (h1 : s.gpr .t1 = off B dX) (h3 : s.gpr .t3 = BitVec.ofNat 64 n)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hO8 : dO % 8 = 0) (hX8 : dX % 8 = 0) (hO : dO + 8 * n ≤ Z)
    (hX : dX + 8 * n ≤ Z) (hd : dX + 8 * n ≤ dO ∨ dO + 8 * n ≤ dX) :
    WP isa (countLoop .t3 mulBody) s fun t =>
      wordsVal t.mem B dO n + 2 ^ (64 * n) * (t.gpr .t4).toNat =
        wordsVal s.mem B dO n + (s.gpr .a6).toNat * wordsVal s.mem B dX n + (s.gpr .t4).toNat ∧
      Outside B dO (8 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 8 * i) ∧ t.gpr .t1 = off B (dX + 8 * i) ∧ Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i + 2 ^ (64 * i) * (t.gpr .t4).toNat =
        wordsVal s.mem B dO i + (s.gpr .a6).toNat * wordsVal s.mem B dX i + (s.gpr .t4).toNat ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (mulBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j1, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, Outside.refl _ _ _ _, by simp [wordsVal], Keep.refl _ _⟩ h3)
    fun t ⟨_, _, jout, jeq, jk⟩ => ⟨jeq, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have ha6 : t.gpr .a6 = s.gpr .a6 := jk.gpr (by decide)
  have hst : WP isa (.block (mulBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t1 = off B (dX + 8 * i + 8) ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (t.gpr .a6 * word t.mem B (dX + 8 * i) + word t.mem B (dO + 8 * i) + t.gpr .t4) ∧
        t'.gpr .t4 = BitVec.ofNat 64 ((t.gpr .a6).toNat * (word t.mem B (dX + 8 * i)).toNat / 2 ^ 64) +
          (if t.gpr .a6 * word t.mem B (dX + 8 * i) + word t.mem B (dO + 8 * i) < word t.mem B (dO + 8 * i)
            then 1 else 0) +
          (if t.gpr .a6 * word t.mem B (dX + 8 * i) + word t.mem B (dO + 8 * i) + t.gpr .t4 < t.gpr .t4
            then 1 else 0)) ∧
      Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mulBody, mov, add_ofNat_zero', j0, j1, hs'.ld (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.ld (show dX + 8 * i + 8 ≤ Z by omega_arith), hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dX + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l0, l1, l3, lm, l4⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l1, show dX + 8 * i + 8 = dX + 8 * (i + 1) by omega_arith]
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · have wo : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have wx : word t.mem B (dX + 8 * i) = word s.mem B (dX + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have k := mul_word_arith (t.gpr .a6) (word t.mem B (dX + 8 * i)) (word t.mem B (dO + 8 * i)) (t.gpr .t4)
    rw [lm, l4, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B dO i,
      wordsVal_succ_top s.mem B dX i, Nat.mul_succ, Nat.pow_add]
    rw [wo, wx, ha6] at k
    have e : 2 ^ (64 * i) * (s.gpr .a6 * word s.mem B (dX + 8 * i) + word s.mem B (dO + 8 * i) + t.gpr .t4).toNat +
        2 ^ (64 * i) * 2 ^ 64 * (BitVec.ofNat 64 ((s.gpr .a6).toNat * (word s.mem B (dX + 8 * i)).toNat / 2 ^ 64) +
          (if s.gpr .a6 * word s.mem B (dX + 8 * i) + word s.mem B (dO + 8 * i) < word s.mem B (dO + 8 * i)
            then 1 else 0) +
          (if s.gpr .a6 * word s.mem B (dX + 8 * i) + word s.mem B (dO + 8 * i) + t.gpr .t4 < t.gpr .t4
            then 1 else 0)).toNat =
        2 ^ (64 * i) * ((s.gpr .a6).toNat * (word s.mem B (dX + 8 * i)).toNat +
          (word s.mem B (dO + 8 * i)).toNat + (t.gpr .t4).toNat) := by
      rw [Nat.mul_assoc, ← Nat.mul_add, k]
    rw [wo, wx, ha6]
    grind

/-- The arithmetic of a row: adding `y_i [x]`'s low `n` words to the `n`
words of `[o]` from word `i` adds `2^(64 i) y_i [x]` modulo `2^(64 (i + n))`. -/
theorem row_arith {i n : Nat} {Olow Ohi Ohi' c yi X Yi : Nat}
    (hlow : Olow < 2 ^ (64 * i)) (hhi' : Ohi' < 2 ^ (64 * n))
    (hO : Olow + 2 ^ (64 * i) * Ohi = Yi * X % 2 ^ (64 * (i + n)))
    (hrow : Ohi' + 2 ^ (64 * n) * c = Ohi + yi * (X % 2 ^ (64 * n))) :
    Olow + 2 ^ (64 * i) * Ohi' = (Yi + 2 ^ (64 * i) * yi) * X % 2 ^ (64 * (i + n)) := by
  rw [Nat.mul_add, Nat.pow_add] at hO ⊢
  generalize 2 ^ (64 * i) = A at *
  generalize 2 ^ (64 * n) = Bn at *
  have hX := Nat.div_add_mod X Bn
  have hY := Nat.div_add_mod (Yi * X) (A * Bn)
  generalize X / Bn = q at hX
  generalize X % Bn = Xn at hX hrow
  generalize Yi * X / (A * Bn) = r at hY
  rw [← hO] at hY
  have e : (Yi + A * yi) * X = (Olow + A * Ohi') + (A * Bn) * (r + c + yi * q) := by
    rw [← hX] at hY ⊢
    grind
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  have : A * Ohi' + A ≤ A * Bn := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hhi'
  omega_arith

/-- The low `a` words of `a + b` words. -/
theorem wordsVal_mod_low (m : Mem) (B : Addr) (d a b : Nat) :
    wordsVal m B d (a + b) % 2 ^ (64 * a) = wordsVal m B d a := by
  rw [wordsVal_append, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wordsVal_lt _ _ _ _)]

theorem off_add8 (B : Addr) (d : Nat) : off B d + BitVec.ofNat 64 8 = off B (d + 8) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- The registers `mulLow` may change. -/
abbrev mulRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4, .a2, .a3, .a6, .s8]

/-- A row of `mulLow`: `y_i` (the word at `a2`) times the low `w - i` words of
`[x]` added to the `w - i` words of `[o]` from word `i` (at `a3`). -/
theorem mulRow_ok {s : State} {B : Addr} {Z w N o y x i : Nat} (h : Ws s B Z w N)
    (ho : o < N) (hy : y < N) (hx : x < N) (hN : N ≤ 2048) (hox : o ≠ x) (hi : i < w)
    (h2 : s.gpr .a2 = off B (arr w y + 8 * i)) (h3 : s.gpr .a3 = off B (arr w o + 8 * i))
    (h8 : s.gpr .s8 = BitVec.ofNat 64 (w - i)) :
    WP isa (mulRow x) s fun t => Ws t B Z w N ∧ t.gpr .a2 = off B (arr w y + 8 * (i + 1)) ∧
      t.gpr .a3 = off B (arr w o + 8 * (i + 1)) ∧ t.gpr .s8 = s.gpr .s8 - BitVec.ofNat 64 1 ∧
      Outside B (arr w o + 8 * i) (8 * (w - i)) s.mem t.mem ∧
      (∃ c, wordsVal t.mem B (arr w o + 8 * i) (w - i) + 2 ^ (64 * (w - i)) * c =
        wordsVal s.mem B (arr w o + 8 * i) (w - i) +
          (word s.mem B (arr w y + 8 * i)).toNat * wordsVal s.mem B (arr w x) (w - i)) ∧
      Keep mulRegs s t := by
  have fo := h.arr_fit ho
  have fy := h.arr_fit hy
  have fx := h.arr_fit hx
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wle
  have dox := arr_disj (w := w) hox
  have alo := arr_al w o
  have aly := arr_al w y
  have alx := arr_al w x
  rw [mulRow, WP.seq_iff,
    show ([.load .d .a6 .a2 0, mov .t0 .a3] ++ ptr .t1 x ++ [mov .t3 .s8, .li .t4 0] : List Instr) =
      [.load .d .a6 .a2 0, mov .t0 .a3] ++ (ptr .t1 x ++ [mov .t3 .s8, .li .t4 0]) from List.append_assoc _ _ _,
    WP.block_append_iff]
  have hs := h.scr
  have hb : WP isa (.block [.load .d .a6 .a2 0, mov .t0 .a3]) s fun u =>
      (u.gpr .a6 = word s.mem B (arr w y + 8 * i) ∧ u.gpr .t0 = off B (arr w o + 8 * i) ∧ u.mem = s.mem) ∧
        Keep [.a6, .t0] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mov, add_ofNat_zero', h2, h3, hs.ld (show arr w y + 8 * i + 8 ≤ Z by omega_arith),
      hs.al8 (show arr w y + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hb fun u ⟨⟨u6, u0, um⟩, ku⟩ => ?_
  have k₁ : Keep mulRegs s u := ku.mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k₁
  refine ptr_ok hu (by decide) (by decide) (show x < 2048 by omega_arith) ?_
  have hb2 : WP isa (.block [mov .t3 .s8, .li .t4 0]) (u.write .t1 (off B (arr w x))) fun v =>
      (v.gpr .t0 = off B (arr w o + 8 * i) ∧ v.gpr .t1 = off B (arr w x) ∧
        v.gpr .t3 = BitVec.ofNat 64 (w - i) ∧ v.gpr .t4 = 0 ∧ v.gpr .a6 = word s.mem B (arr w y + 8 * i) ∧
        v.mem = s.mem) ∧ Keep [.t3, .t4] (u.write .t1 (off B (arr w x))) v := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    have u8 : u.gpr .s8 = BitVec.ofNat 64 (w - i) := (ku.gpr (by decide)).trans h8
    brun [mov, add_ofNat_zero', fin64_exec_li_zero, u0, u6, u8, um]
  refine WP.mono hb2 fun v ⟨⟨v0, v1, v3, v4, v6, vm⟩, kv⟩ => ?_
  have k₂ : Keep mulRegs s v := Keep.trans' k₁ (((Keep.write _ _ _).trans kv).mono (by decide))
  have hv : Ws v B Z w N := h.of_keep k₂
  rw [WP.seq_iff]
  refine WP.mono (mulLoop_ok hv.scr v0 v1 v3 (by omega_arith) (by omega_arith) (by omega_arith) alx
    (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨teq, tout, kt⟩ => ?_
  have k₃ : Keep mulRegs s t := Keep.trans' k₂ (kt.mono (by decide))
  have ht : Ws t B Z w N := h.of_keep k₃
  have kk : Keep (opRegs ++ [.a6]) s t :=
    (((ku.trans (Keep.write _ _ _)).trans kv).trans kt).mono (by decide)
  have t2 : t.gpr .a2 = off B (arr w y + 8 * i) := (kk.gpr (by decide)).trans h2
  have t3 : t.gpr .a3 = off B (arr w o + 8 * i) := (kk.gpr (by decide)).trans h3
  have t8 : t.gpr .s8 = s.gpr .s8 := kk.gpr (by decide)
  have hb3 : WP isa (.block [.addi .a2 .a2 8, .addi .a3 .a3 8, .addi .s8 .s8 (-1)]) t fun t' =>
      (t'.gpr .a2 = off B (arr w y + 8 * i) + BitVec.ofNat 64 8 ∧
        t'.gpr .a3 = off B (arr w o + 8 * i) + BitVec.ofNat 64 8 ∧
        t'.gpr .s8 = s.gpr .s8 - BitVec.ofNat 64 1 ∧ t'.mem = t.mem) ∧ Keep [.a2, .a3, .s8] t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_addi_nat (show 8 < 2048 by decide), t2, t3, t8]
  refine WP.mono hb3 fun t' ⟨⟨a2', a3', s8', tm'⟩, kt'⟩ => ?_
  rw [vm] at teq tout
  rw [v4, v6] at teq
  refine ⟨ht.of_keep kt', ?_, ?_, s8', by rw [tm']; exact tout, ⟨(t.gpr .t4).toNat, by rw [tm']; simpa using teq⟩,
    Keep.trans' k₃ (kt'.mono (by decide))⟩
  · rw [a2', off_add8, show arr w y + 8 * i + 8 = arr w y + 8 * (i + 1) by omega_arith]
  · rw [a3', off_add8, show arr w o + 8 * i + 8 = arr w o + 8 * (i + 1) by omega_arith]

/-- `mulLow o y x`: `[o] := [y] [x] mod 2^(64 w)` from `[o] = 0` (`y = x` allowed);
only the first `w` words of `o` change. -/
theorem mulLow_ok {s : State} {B : Addr} {Z w N o y x : Nat} (h : Ws s B Z w N)
    (ho : o < N) (hy : y < N) (hx : x < N) (hN : N ≤ 2048) (hoy : o ≠ y) (hox : o ≠ x)
    (hz : num s.mem B w o = 0) :
    WP isa (mulLow o y x) s fun t => Ws t B Z w N ∧ Frame B w [o] [] s.mem t.mem ∧
      Outside B (arr w o) (8 * w) s.mem t.mem ∧
      num t.mem B w o = num s.mem B w y * num s.mem B w x % 2 ^ (64 * w) ∧ Keep mulRegs s t := by
  have fo := h.arr_fit ho
  have fy := h.arr_fit hy
  have fx := h.arr_fit hx
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  have doy := arr_disj (w := w) hoy
  have dox := arr_disj (w := w) hox
  rw [mulLow, WP.seq_iff, List.append_assoc]
  refine ptr2_ok h (r := .a2) (r' := .a3) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (show y < 2048 by omega_arith) (show o < 2048 by omega_arith) fun u u2 u3 ku um => ?_
  have hb : WP isa (.block [mov .s8 .s9]) u fun v => (v.gpr .s8 = BitVec.ofNat 64 w ∧ v.mem = u.mem) ∧
      Keep [.s8] u v := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    have u9 : u.gpr .s9 = BitVec.ofNat 64 w := (ku.gpr (by decide)).trans h.s9
    brun [mov, add_ofNat_zero', u9]
  refine WP.mono hb fun v ⟨⟨v8, vm⟩, kv⟩ => ?_
  have k₁ : Keep mulRegs s v := (ku.trans kv).mono (by decide)
  have v2 : v.gpr .a2 = off B (arr w y + 8 * 0) := by rw [kv.gpr (by decide), u2]; rfl
  have v3 : v.gpr .a3 = off B (arr w o + 8 * 0) := by rw [kv.gpr (by decide), u3]; rfl
  let Inv : Nat → State → Prop := fun i t => Ws t B Z w N ∧ t.gpr .a2 = off B (arr w y + 8 * i) ∧
    t.gpr .a3 = off B (arr w o + 8 * i) ∧ Outside B (arr w o) (8 * w) s.mem t.mem ∧
    num t.mem B w o = wordsVal s.mem B (arr w y) i * num s.mem B w x % 2 ^ (64 * w) ∧ Keep mulRegs s t
  refine WP.mono (wp_countdown (body := mulRow x) (cnt := .s8) (N := w) (by omega_arith) h.wpos Inv
    (fun i hi t ⟨jw, j2, j3, jout, jeq, jk⟩ hc => ?_)
    ⟨h.of_keep k₁, v2, v3, by rw [vm, um]; exact Outside.refl _ _ _ _,
      by rw [vm, um, hz]; simp [wordsVal], k₁⟩ v8)
    fun t ⟨tw, _, _, tout, teq, tk⟩ =>
      ⟨tw, Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using tout) (by omega_arith) (by simp), tout,
        teq, tk⟩
  refine WP.mono (mulRow_ok jw ho hy hx hN hox hi j2 j3 hc)
    fun t' ⟨hw', a2', a3', s8', rout, ⟨c, req⟩, rk⟩ => ⟨⟨hw', a2', a3', ?_, ?_, Keep.trans' jk rk⟩, s8'⟩
  · exact jout.trans (rout.mono (by omega_arith) (by omega_arith))
  · have hwi : i + (w - i) = w := by omega_arith
    have sp : ∀ m : Mem, num m B w o =
        wordsVal m B (arr w o) i + 2 ^ (64 * i) * wordsVal m B (arr w o + 8 * i) (w - i) := fun m => by
      have e := wordsVal_append m B (arr w o) i (w - i)
      rw [hwi] at e; exact e
    have lo : wordsVal t'.mem B (arr w o) i = wordsVal t.mem B (arr w o) i :=
      rout.wordsVal (by omega_arith) (by omega_arith)
    have yi : word t.mem B (arr w y + 8 * i) = word s.mem B (arr w y + 8 * i) :=
      jout.word (by omega_arith) (by omega_arith)
    have xs : wordsVal t.mem B (arr w x) (w - i) = wordsVal s.mem B (arr w x) (w - i) :=
      jout.wordsVal (by omega_arith) (by omega_arith)
    have xm : num s.mem B w x % 2 ^ (64 * (w - i)) = wordsVal s.mem B (arr w x) (w - i) := by
      have e := wordsVal_mod_low s.mem B (arr w x) (w - i) i
      rw [show w - i + i = w by omega_arith] at e; exact e
    rw [yi, xs, ← xm] at req
    have hO : wordsVal t.mem B (arr w o) i + 2 ^ (64 * i) * wordsVal t.mem B (arr w o + 8 * i) (w - i) =
        wordsVal s.mem B (arr w y) i * num s.mem B w x % 2 ^ (64 * (i + (w - i))) := by
      rw [← sp, jeq, hwi]
    have r := row_arith (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _) hO req
    rw [hwi] at r
    rw [sp, lo, r, wordsVal_succ_top]

end VG.Proof.Rsa.RISCV64.Keys
