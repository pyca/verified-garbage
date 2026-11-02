module

public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Ops
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyOps
public import VerifiedGarbage.Proof.Rsa.RISCV64.InvLaw
public import VerifiedGarbage.Proof.Rsa.RISCV64.RdOps
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The operations of `vg_rsa_keygen_key` on RISC-V beyond the key routines'

On the RSA key operations' working space (`Proof/Rsa/RISCV64/KeyLayout.lean`):

* `notS_ok`, `andNotS_ok`, `selS_ok`: slots holding bits;
* `setLow_ok`: the low word of an array := a small constant;
* `mulTo_ok`: `[o] := [a] [b] mod 2^(64 w)`;
* `invOf_ok`: `[a]` and `[m]` into the batched inverse's arrays 0 and 8, and
  `InvBatch.inverse` (through `InvLaw`): `gcd([a], [m])` in array 1 and the
  inverse in array 3;
* `nP_ok`, `nTwo_ok`, `nW_ok`: the digit counts `invOf` takes.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Loops
open VG.Impl.Rsa.RISCV64.Keys (copy sub3 setOne seqs)
open VG.Impl.RsaKeyGen.RISCV64.Key (aZero)

/-! ## Bits -/

theorem bit01 {x : BitVec 64} (h : x.toNat ≤ 1) : x = 0#64 ∨ x = 1#64 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with e | e
  · exact .inl (BitVec.eq_of_toNat_eq (by simpa using e))
  · exact .inr (BitVec.eq_of_toNat_eq (by simpa using e))

theorem not01 {x : BitVec 64} (hx : x.toNat ≤ 1) : (x ^^^ BitVec.ofInt 64 1).toNat = 1 - x.toNat := by
  rcases bit01 hx with rfl | rfl <;> decide

theorem andNot01 {x y : BitVec 64} (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    ((x ^^^ BitVec.ofInt 64 1) &&& y).toNat = (1 - x.toNat) * y.toNat := by
  rcases bit01 hx with rfl | rfl <;> rcases bit01 hy with rfl | rfl <;> decide

theorem sel01 {x y z : BitVec 64} (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) (hz : z.toNat ≤ 1) :
    (x ^^^ ((y ^^^ x) &&& z)).toNat = if z.toNat = 0 then x.toNat else y.toNat := by
  rcases bit01 hx with rfl | rfl <;> rcases bit01 hy with rfl | rfl <;> rcases bit01 hz with rfl | rfl <;> decide

/-! ## The slot operations -/

theorem notS_ok {s : State} {B : Addr} {Z w N d a : Nat} (h : Ws s B Z w N)
    (hd : d + 8 ≤ hdr) (hd8 : d % 8 = 0) (ha : a + 8 ≤ hdr) (ha8 : a % 8 = 0)
    (ba : slot s.mem B a ≤ 1) :
    WP isa (.block (Impl.RsaKeyGen.RISCV64.Key.notS d a)) s fun t => Ws t B Z w N ∧
      Frame B w [] [d] s.mem t.mem ∧ slot t.mem B d = 1 - slot s.mem B a ∧ Keep opRegs s t := by
  have nw := h.nowrap
  have hz := h.hdr_le
  have hk : WP isa (.block (Impl.RsaKeyGen.RISCV64.Key.notS d a)) s fun u =>
      (u.mem = s.mem.writeW (off B d) (word s.mem B a ^^^ BitVec.ofInt 64 1)) ∧ Keep [.t5] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [Impl.RsaKeyGen.RISCV64.Key.notS, h.s11, h.scr.st (d := d) (n := 8) (by omega_arith),
      h.scr.al8 (d := d) (by omega_arith) hd8,
      h.scr.ld (d := a) (n := 8) (by omega_arith), h.scr.al8 (d := a) (by omega_arith) ha8,
      show d < 2048 by simp only [hdr_eq] at hd; omega_arith, show a < 2048 by simp only [hdr_eq] at ha; omega_arith]
  refine WP.mono hk fun u ⟨mu, ku⟩ => ?_
  have sw := slot_write (m := s.mem) (B := B) (w := w) (d := d) (word s.mem B a ^^^ BitVec.ofInt 64 1)
    (by omega_arith)
  rw [← mu] at sw
  exact ⟨h.of_keep ku, sw.1, by rw [sw.2]; exact not01 ba, ku.mono (by decide)⟩

theorem andNotS_ok {s : State} {B : Addr} {Z w N d a b : Nat} (h : Ws s B Z w N)
    (hd : d + 8 ≤ hdr) (hd8 : d % 8 = 0) (ha : a + 8 ≤ hdr) (ha8 : a % 8 = 0)
    (hb : b + 8 ≤ hdr) (hb8 : b % 8 = 0) (ba : slot s.mem B a ≤ 1) (bb : slot s.mem B b ≤ 1) :
    WP isa (.block (Impl.RsaKeyGen.RISCV64.Key.andNotS d a b)) s fun t => Ws t B Z w N ∧
      Frame B w [] [d] s.mem t.mem ∧ slot t.mem B d = (1 - slot s.mem B a) * slot s.mem B b ∧
      Keep opRegs s t := by
  have nw := h.nowrap
  have hz := h.hdr_le
  have hk : WP isa (.block (Impl.RsaKeyGen.RISCV64.Key.andNotS d a b)) s fun u =>
      (u.mem = s.mem.writeW (off B d) ((word s.mem B a ^^^ BitVec.ofInt 64 1) &&& word s.mem B b)) ∧
        Keep [.t5, .t6] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [Impl.RsaKeyGen.RISCV64.Key.andNotS, h.s11, h.scr.st (d := d) (n := 8) (by omega_arith),
      h.scr.al8 (d := d) (by omega_arith) hd8,
      h.scr.ld (d := a) (n := 8) (by omega_arith), h.scr.al8 (d := a) (by omega_arith) ha8,
      h.scr.ld (d := b) (n := 8) (by omega_arith), h.scr.al8 (d := b) (by omega_arith) hb8,
      show d < 2048 by simp only [hdr_eq] at hd; omega_arith, show a < 2048 by simp only [hdr_eq] at ha; omega_arith,
      show b < 2048 by simp only [hdr_eq] at hb; omega_arith]
  refine WP.mono hk fun u ⟨mu, ku⟩ => ?_
  have sw := slot_write (m := s.mem) (B := B) (w := w) (d := d)
    ((word s.mem B a ^^^ BitVec.ofInt 64 1) &&& word s.mem B b) (by omega_arith)
  rw [← mu] at sw
  exact ⟨h.of_keep ku, sw.1, by rw [sw.2]; exact andNot01 ba bb, ku.mono (by decide)⟩

/-- `d := c ? b : a`, all three slots bits. -/
theorem selS_ok {s : State} {B : Addr} {Z w N d a b c : Nat} (h : Ws s B Z w N)
    (hd : d + 8 ≤ hdr) (hd8 : d % 8 = 0) (ha : a + 8 ≤ hdr) (ha8 : a % 8 = 0)
    (hb : b + 8 ≤ hdr) (hb8 : b % 8 = 0) (hc : c + 8 ≤ hdr) (hc8 : c % 8 = 0)
    (ba : slot s.mem B a ≤ 1) (bb : slot s.mem B b ≤ 1) (bc : slot s.mem B c ≤ 1) :
    WP isa (.block (Impl.RsaKeyGen.RISCV64.Key.selS d a b c)) s fun t => Ws t B Z w N ∧
      Frame B w [] [d] s.mem t.mem ∧
      slot t.mem B d = (if slot s.mem B c = 0 then slot s.mem B a else slot s.mem B b) ∧
      Keep opRegs s t := by
  have nw := h.nowrap
  have hz := h.hdr_le
  have hk : WP isa (.block (Impl.RsaKeyGen.RISCV64.Key.selS d a b c)) s fun u =>
      (u.mem = s.mem.writeW (off B d)
        (word s.mem B a ^^^ ((word s.mem B b ^^^ word s.mem B a) &&& word s.mem B c))) ∧
        Keep [.t4, .t5, .t6] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [Impl.RsaKeyGen.RISCV64.Key.selS, h.s11, h.scr.st (d := d) (n := 8) (by omega_arith),
      h.scr.al8 (d := d) (by omega_arith) hd8,
      h.scr.ld (d := a) (n := 8) (by omega_arith), h.scr.al8 (d := a) (by omega_arith) ha8,
      h.scr.ld (d := b) (n := 8) (by omega_arith), h.scr.al8 (d := b) (by omega_arith) hb8,
      h.scr.ld (d := c) (n := 8) (by omega_arith), h.scr.al8 (d := c) (by omega_arith) hc8,
      show d < 2048 by simp only [hdr_eq] at hd; omega_arith, show a < 2048 by simp only [hdr_eq] at ha; omega_arith,
      show b < 2048 by simp only [hdr_eq] at hb; omega_arith, show c < 2048 by simp only [hdr_eq] at hc; omega_arith]
  refine WP.mono hk fun u ⟨mu, ku⟩ => ?_
  have sw := slot_write (m := s.mem) (B := B) (w := w) (d := d)
    (word s.mem B a ^^^ ((word s.mem B b ^^^ word s.mem B a) &&& word s.mem B c)) (by omega_arith)
  rw [← mu] at sw
  exact ⟨h.of_keep ku, sw.1, by rw [sw.2]; exact sel01 ba bb bc, ku.mono (by decide)⟩

/-! ## The low word -/

theorem exec_li_small {s : State} {d : Reg} {x : Nat} (hx : x < 2048) :
    exec (.li d (x : Int)) s = some (s.write d (BitVec.ofNat 64 x)) := by
  rw [exec_li (by simp only [imm12]; omega)]
  congr 2

/-- The low word of `[j]` := `x` (a small constant). -/
theorem setLow_ok {s : State} {B : Addr} {Z w N j x : Nat} (h : Ws s B Z w N) (hj : j < N) (hN : N ≤ 2048)
    (hx : x < 2048) :
    WP isa (.block (Impl.RsaKeyGen.RISCV64.Key.setLow j (x : Int))) s fun t => Ws t B Z w N ∧
      Frame B w [j] [] s.mem t.mem ∧ num t.mem B w j = x + 2 ^ 64 * (num s.mem B w j / 2 ^ 64) ∧
      Keep opRegs s t := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  refine WP.mono (low_ok h hj hN (f := fun _ => BitVec.ofNat 64 x) fun s₀ e0 em ew er => ?_)
    fun t ⟨a, b, c, d⟩ => ⟨a, b, by rw [c, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)], d⟩
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [e0, em, exec_li_small (d := .t5) hx, (h.scr.congr ew).st (d := arr w j) (n := 8) (by omega_arith),
    (h.scr.congr ew).al8 (d := arr w j) (by omega_arith) (arr_al _ _)]

/-! ## The product -/

/-- `[o] := [a] [b] mod 2^(64 w)`; the words past `w` of `[o]` are kept (`Outside`). -/
theorem mulTo_ok {s : State} {B : Addr} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 2048) (hz : aZero < N)
    (hoa : o ≠ a) (hob : o ≠ b) (hoz : o ≠ aZero) (hz0 : num s.mem B w aZero = 0) :
    WP isa (Impl.RsaKeyGen.RISCV64.Key.mulTo o a b) s fun t => Ws t B Z w N ∧
      Frame B w [o] [] s.mem t.mem ∧ Outside B (arr w o) (8 * w) s.mem t.mem ∧
      num t.mem B w o = num s.mem B w a * num s.mem B w b % 2 ^ (64 * w) ∧ Keep mulRegs s t := by
  have fa := h.fit64 ha
  have fb := h.fit64 hb
  rw [Impl.RsaKeyGen.RISCV64.Key.mulTo, WP.seq_iff]
  refine WP.mono (copy_ok h ho hz hN hoz) fun u ⟨wu, fu, vu, ku, ou⟩ => ?_
  have ea : num u.mem B w a = num s.mem B w a :=
    fu.num (fun _ hk => by rw [List.mem_singleton.mp hk]; exact hoa) (by simp) fa
  have eb : num u.mem B w b = num s.mem B w b :=
    fu.num (fun _ hk => by rw [List.mem_singleton.mp hk]; exact hob) (by simp) fb
  refine WP.mono (mulLow_ok wu ho ha hb hN hoa hob (by rw [vu, hz0])) fun t ⟨wt, ft, ot, vt, kt⟩ => ?_
  exact ⟨wt, fu.trans ft |>.mono (by simp) (by simp), ou.trans ot, by rw [vt, ea, eb],
    Keep.trans' (ku.mono (by decide)) kt⟩

/-! ## The inverse -/

/-- The arrays `invOf` writes: the batched inverse's input arrays and the ones it writes. -/
abbrev invOfArrs : List Nat := 0 :: 8 :: VG.Proof.Rsa.RISCV64.InvBatch.invArrs

/-- The registers `invOf` changes. -/
abbrev invOfRegs : List Reg := .s8 :: VG.Proof.Rsa.RISCV64.InvBatch.invRegs

/-- `invOf a m k`: with `k` setting `s8 := n` (the digit count) from registers the copies
keep (`hk`), for `[a]` and an odd `[m]` below `2^(32 n)`, `gcd([a], [m])` in array 1 and,
for `[m] > 1`, the inverse in array 3. `a` and `m` are past the inverse's arrays. -/
theorem invOf_ok [InvLaw] {s : State} {B : Addr} {Z w N a m n : Nat} {k : List Instr}
    (h : Ws s B Z w N) (hN15 : 15 ≤ N) (hN : N ≤ 256) (hw : 4 ≤ w) (ha : a < N) (hm : m < N)
    (ha15 : 15 ≤ a) (hm15 : 15 ≤ m) (hn1 : 1 ≤ n) (hnw : n ≤ 2 * w)
    (hk : ∀ u : State, (∀ r ∉ opRegs, u.gpr r = s.gpr r) →
      WP isa (.block k) u fun v => (v.gpr .s8 = BitVec.ofNat 64 n ∧ v.mem = u.mem) ∧ Keep [.s8] u v)
    (hxn : num s.mem B w a < 2 ^ (32 * n)) (hmn : num s.mem B w m < 2 ^ (32 * n))
    (hodd : num s.mem B w m % 2 = 1) :
    WP isa (Impl.RsaKeyGen.RISCV64.Key.invOf a m k) s fun t => Ws t B Z w N ∧
      Frame B w invOfArrs [] s.mem t.mem ∧ Keep invOfRegs s t ∧
      (1 < num s.mem B w m →
        num t.mem B w 1 = Nat.gcd (num s.mem B w a) (num s.mem B w m) ∧
        (num s.mem B w m : Int) ∣ (num t.mem B w 3 : Int) * num s.mem B w a - num t.mem B w 1 ∧
        num t.mem B w 3 < num s.mem B w m) := by
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have h0 : 0 < N := by omega
  have h8 : 8 < N := by omega
  have hN' : N ≤ 2048 := by omega
  have ha0 : a ≠ 0 := by omega
  have hm8 : m ≠ 8 := by omega
  have hm0 : m ≠ 0 := by omega
  have e : Impl.RsaKeyGen.RISCV64.Key.invOf a m k =
      seqs [copy VG.Impl.Rsa.RISCV64.InvBatch.aX a, copy VG.Impl.Rsa.RISCV64.InvBatch.aMin m, .block k,
        VG.Impl.Rsa.RISCV64.InvBatch.inverse] := rfl
  rw [e, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h h0 ha hN' (Ne.symm ha0)) fun t1 ⟨w1, f1, v1, k1, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok w1 h8 hm hN' (Ne.symm hm8)) fun t2 ⟨w2, f2, v2, k2, _⟩ => ?_
  have m1 : num t1.mem B w m = num s.mem B w m :=
    f1.num (j := m) (fun _ hk => by rw [List.mem_singleton.mp hk]; exact Ne.symm hm0) (by simp) (fit m hm)
  have a2 : num t2.mem B w VG.Impl.Rsa.RISCV64.InvBatch.aX = num s.mem B w a := by
    rw [f2.num (j := VG.Impl.Rsa.RISCV64.InvBatch.aX) (fun _ hk => by rw [List.mem_singleton.mp hk]; decide)
      (by simp) (fit 0 h0), v1]
  have K2 : Keep opRegs s t2 := Keep.trans' k1 k2 |>.mono (by decide)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (hk t2 fun r hr => K2.gpr hr) fun t3 ⟨⟨c3, m3⟩, k3⟩ => ?_
  have w3 := w2.of_keep k3
  have ctx : VG.Proof.Rsa.RISCV64.InvBatch.Ctx t3 B Z w N n := ⟨w3, c3, hn1, hnw, hN15, hw⟩
  have x3 : num t3.mem B w VG.Impl.Rsa.RISCV64.InvBatch.aX = num s.mem B w a := by rw [m3, a2]
  have mm3 : num t3.mem B w VG.Impl.Rsa.RISCV64.InvBatch.aMin = num s.mem B w m := by
    rw [m3, v2, m1]
  simp only [seqs]
  refine WP.mono (InvLaw.inverse_ok ctx hN x3 hxn mm3 hmn hodd) fun t ⟨wt, ft, kt, vt⟩ => ?_
  rw [m3] at ft
  refine ⟨wt, ((f1.mono (by decide) (by simp)).trans (f2.mono (by decide) (by simp))).trans
      (ft.mono (by decide) (by simp)),
    Keep.trans' (Keep.trans' (K2.mono (by decide)) (k3.mono (by decide))) (kt.mono (by decide)), vt⟩

end VG.Proof.Rsa.RISCV64.Keys
