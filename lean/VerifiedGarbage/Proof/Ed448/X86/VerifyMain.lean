module

public import VerifiedGarbage.Proof.Ed448.X86.VerifyLocal
import VerifiedGarbage.Proof.Ed448.X86.VerifyDecode
public import VerifiedGarbage.Proof.Ed448.X86.ScalarIO
public import VerifiedGarbage.Proof.Ed448.X86.VerifyChecks
import VerifiedGarbage.Proof.X448.X86.FnLit
import VerifiedGarbage.Proof.X448.X86.Frame
import VerifiedGarbage.Proof.X448.X86.Copy
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed448.ScalarWords
import VerifiedGarbage.Proof.Ed448.VerifyFormulas
import VerifiedGarbage.Proof.Ed448.X86.VerifyDecodeY
import VerifiedGarbage.Proof.Ed448.X86.VerifyS
import VerifiedGarbage.Proof.Ed448.X86.VerifySign
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.X25519.X86.Basic
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X448.X86.Carry
import VerifiedGarbage.Proof.X448.X86.Columns
import VerifiedGarbage.Proof.X448.X86.Counters
import VerifiedGarbage.Proof.X448.X86.Decode
import VerifiedGarbage.Proof.X448.X86.FnVerified
import VerifiedGarbage.Proof.X448.X86.Freeze
import VerifiedGarbage.Proof.X448.X86.Restore
import VerifiedGarbage.Proof.X448.X86.Select
import VerifiedGarbage.Proof.X448.X86.Small
import VerifiedGarbage.Proof.X448.X86.Step
import VerifiedGarbage.Proof.Ed448.X86.VerifyFinish
public import VerifiedGarbage.Proof.Ed448.X86.BaseMain
import VerifiedGarbage.Proof.X448.X86.Iter
import VerifiedGarbage.Proof.Ed448.X86.ScalarMain
import VerifiedGarbage.Proof.X448.X86.Bits
import VerifiedGarbage.Proof.Ed448.X86.VerifyField
public import VerifiedGarbage.Proof.Ed448.Formulas
public import VerifiedGarbage.Proof.X448.X86.Env
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Ed448.X86.VerifyEquation
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.X86.Mem
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.Scalar
public import VerifiedGarbage.Proof.Ed448.CombRef
import VerifiedGarbage.Proof.X448.X86.ByteMem
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.X86.Reduce

/-! ### `Ed448.X86.VerifyLoop`, which this module and modules that import it used -/

section

/-! ### `Ed448.X86.VerifyBits`, which this module and modules that import it used -/

section

/-!
# Ed448 verification's equation on x86 (32-bit): the bits of `S` and `k`

`vbits_ok`: byte `t` at `BITS` is bit `t` of `S` (the signature's last 57
bytes), and byte `t` at `KBITS` bit `t` of `k` (the challenge), for `t < 456`
(`VBits`), by X448's `bitsLoop`.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448.X86 VG.Proof.X448.X86
open VG.Impl.X448.X86 (BITS at_)
open VG.Impl.Ed448.X86 (KBITS)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- The bits of `S` at `BITS` and those of `K` at `KBITS`, one per byte. -/
def VBits (base : Addr) (S K : Nat) (m : Mem) : Prop :=
  ∀ t < 456, m (off base (BITS + t)) = BitVec.ofNat 8 ((S >>> t) &&& 1) ∧
    m (off base (KBITS + t)) = BitVec.ofNat 8 ((K >>> t) &&& 1)

/-- `vbits`: the bits of `k` (the challenge, the argument at `[esp + 12]`) at `KBITS`, then those of
`S` (the signature's last 57 bytes, from the argument at `[esp + 8]`) at `BITS`, with `esi` back at
the signature. -/
theorem vbits_ok {s : State} {base : Addr} (hs : Scr s base) {a8 a12 : Addr}
    (ha8 : s.ea (at_ .esp 8) = a8) (hr8 : InRegions (s.rd ++ s.wr) a8 4)
    (ha12 : s.ea (at_ .esp 12) = a12) (hr12 : InRegions (s.rd ++ s.wr) a12 4)
    {sg ch : BitVec 32} (hsg : s.mem.readW a8 32 = sg) (hch : s.mem.readW a12 32 = ch)
    (hfs : sg.toNat + 114 ≤ 2 ^ 32) (hfk : ch.toNat + 57 ≤ 2 ^ 32)
    (hsr : ∀ i < 57, InRegions (s.rd ++ s.wr) (sg.setWidth 64 + BitVec.ofNat 64 57 + BitVec.ofNat 64 i) 1)
    (hkr : ∀ i < 57, InRegions (s.rd ++ s.wr) (ch.setWidth 64 + BitVec.ofNat 64 i) 1)
    (hsd : ∀ i < 57, 8192 ≤ ofs base (sg.setWidth 64 + BitVec.ofNat 64 57 + BitVec.ofNat 64 i))
    (hkd : ∀ i < 57, 8192 ≤ ofs base (ch.setWidth 64 + BitVec.ofNat 64 i)) :
    WP isa vbits s fun t =>
      t.gpr .esi = sg ∧ Keeps [.esi, .ebp, .eax, .ecx, .edx, .ebx] s t ∧
      (∃ m, Outside base KBITS 456 s.mem m ∧ Outside base BITS 456 m t.mem) ∧
      VBits base (decodeLE (bytesAt s.mem (sg.setWidth 64 + BitVec.ofNat 64 57) 57))
        (decodeLE (bytesAt s.mem (ch.setWidth 64) 57)) t.mem := by
  have hB : BITS = 3072 := rfl
  have hK : KBITS = 4608 := rfl
  unfold vbits
  refine WP.seq (wp_load ha12 hr12 fun u hu => ?_)
  refine wp_load (a := a8) (by change addr (u.gpr .esp) 8 = _; rw [hu.other _ (by decide)]; exact ha8)
    (by rw [hu.rd, hu.wr]; exact hr8) fun v hv => WP.block_nil ?_
  rw [hu.mem, hsg] at hv
  rw [hch] at hu
  have vs := (hs.of_upd hu (by decide)).of_upd hv (by decide)
  have rv : v.rd ++ v.wr = s.rd ++ s.wr := by rw [hv.rd, hv.wr, hu.rd, hu.wr]
  have ve : v.gpr .esi = ch := by rw [hv.other _ (by decide), hu.gpr]
  -- The bits of `k`.
  refine WP.seq (WP.mono (bitsLoop_ok vs (o := KBITS) (n := 57) (by decide) (by decide) (by decide)
    (k := ch.setWidth 64) (by rw [ve]) (by rw [ve]; omega_using [hfk]) (by rw [rv]; exact hkr) hkd)
    fun w ⟨wk, wo, wb, _⟩ => ?_)
  have ws := vs.of_keeps wk (by decide)
  have wx : w.gpr .ebx = sg := by rw [wk.1 _ (by decide), hv.gpr]
  -- The bits of `S`.
  refine WP.seq (wp_mov rfl fun x hx => wp_alu (Or.inl rfl) rfl fun y hy _ => WP.block_nil ?_)
  have ys := (ws.of_upd hx (by decide)).of_upd hy (by decide)
  have ye : y.gpr .esi = sg + BitVec.ofNat 32 57 := by
    rw [hy.gpr]; change x.gpr .esi + BitVec.ofNat 32 57 = _; rw [hx.gpr]; change w.gpr .ebx + _ = _; rw [wx]
  have ry : y.rd ++ y.wr = s.rd ++ s.wr := by rw [hy.rd, hy.wr, hx.rd, hx.wr, wk.2.1, wk.2.2, rv]
  have ym : y.mem = w.mem := by rw [hy.mem, hx.mem]
  refine WP.seq (WP.mono (bitsLoop_ok ys (o := BITS) (n := 57) (by decide) (by decide) (by decide)
    (k := sg.setWidth 64 + BitVec.ofNat 64 57)
    (by rw [ye]; exact (addr_eq (x := sg) (k := 57) (by omega_using [hfs]) : _))
    (by rw [ye, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hfs]) (by rw [ry]; exact hsr) hsd)
    fun z ⟨zk, zo, zb, ze⟩ => ?_)
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun t ht _ =>
    WP.block_nil ⟨?_, ?_, ⟨w.mem, ?_, ?_⟩, fun j hj => ⟨?_, ?_⟩⟩
  · rw [ht.gpr]; change z.gpr .esi - BitVec.ofNat 32 114 = _
    rw [ze, ye, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  · refine (hu.rest (by decide)).trans ((hv.rest (by decide)).trans ((wk.mono (by simp [bitRegs])).trans
      ((hx.rest (by decide)).trans ((hy.rest (by decide)).trans ((zk.mono (by simp [bitRegs])).trans
        (ht.rest (by decide)))))))
  · rw [hv.mem, hu.mem] at wo; exact wo
  · rw [ht.mem, ← ym]; exact zo
  · have src : y.mem (off (sg.setWidth 64 + BitVec.ofNat 64 57) (j / 8)) =
        s.mem (off (sg.setWidth 64 + BitVec.ofNat 64 57) (j / 8)) := by
      rw [ym, wo _ (Or.inr (Nat.le_trans (by decide) (hsd (j / 8) (by omega_using [hj])))), hv.mem, hu.mem]
    rw [ht.mem, zb j (by omega_using [hj]), src, Proof.Ed448.scalar_bit _ _ hj]
  · have src : v.mem (off (ch.setWidth 64) (j / 8)) = s.mem (off (ch.setWidth 64) (j / 8)) := by
      rw [hv.mem, hu.mem]
    rw [ht.mem, zo _ (Or.inr (by rw [ofs_off' base (by omega_using [hK, hj])]; omega_using [hB, hK])), ym, wb j (by omega_using [hj]), src,
      Proof.Ed448.scalar_bit _ _ hj]

end VG.Proof.Ed448.X86

end

end

/-! ### `Ed448.X86.VerifyRecode`, which this module and modules that import it used -/

section

/-!
# Ed448 verification's equation on x86 (32-bit): `k`'s digits

`vrecode_ok`: `vrecode` leaves byte `t` at `KBITS` as digit `t` of `k`
(`Proof.Ed448.vdigits`, the digits of `Proof/Ed25519/SlidingDigits.lean`, each
zero or odd and below 16, which sum to `k` at the powers of two). One bit keeps
`RecSt`: the registers hold that recoding's state after the bits read
(`Slide.run`), the bytes below them are those of its digits, and the bytes from
there on are still the bits. The pieces of a bit (`recHead_ok`, `recOpen_ok`,
`recGrow_ok`, `recNext_ok`) are stated apart, for the proof that two runs on the
same `k` leave the same trace.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (vdigits)
open VG.Proof.Ed25519 (Slide.run Slide.step Slide.bit Slide.upd)
open VG.Impl.X448.X86 (at_)

/-- Bit `q` of `k`. -/
def kbit (K q : Nat) : Nat := (K >>> q) &&& 1

theorem kbit_eq (K q : Nat) : kbit K q = Slide.bit K q := by
  simp only [kbit, Slide.bit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

theorem kbit_lt (K q : Nat) : kbit K q < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- A bit of `k`, loaded: the digit and the weight of the window it opens. -/
theorem rec_open_fact : ∀ b < 2,
    (BitVec.ofNat 8 b).setWidth 32 = BitVec.ofNat 32 b ∧
    (BitVec.ofNat 8 b).setWidth 32 + (BitVec.ofNat 8 b).setWidth 32 = BitVec.ofNat 32 (2 * b) := by decide

/-- A bit of `k` at the weight `m`; the next weight; and the test of no window. -/
theorem rec_grow_fact : ∀ b < 2, ∀ m < 16,
    ((((BitVec.ofNat 8 b).setWidth 32 ^^^ (0xFFFFFFFF : BitVec 32)) + 1) &&& BitVec.ofNat 32 m) =
      BitVec.ofNat 32 (m * b) ∧
    (BitVec.ofNat 32 m + BitVec.ofNat 32 m) &&& (15 : BitVec 32) = BitVec.ofNat 32 (2 * m % 16) ∧
    (BitVec.ofNat 32 m - (0 : BitVec 32) == 0) = decide (m = 0) := by decide

theorem evalNe {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .ne s = some (!b) := by
  change s.zf.map (!·) = _
  rw [h]; rfl

/-- The count of bits read, moved up, against 456. -/
theorem rec_next_fact : ∀ n < 456,
    ((BitVec.ofNat 32 n + (1 : BitVec 32) - (456 : BitVec 32)) == 0) = decide (n + 1 = 456) := by
  decide +kernel

theorem ofNat32_setWidth8 (x : Nat) : (BitVec.ofNat 32 x).setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- The registers the recoding changes. -/
abbrev recRegs : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

/-- The address of a byte at `r + c`, for `r` the working space's address plus `q`. -/
theorem ptr_ea {s : State} {base : Addr} (hs : Scr s base) {r : Reg} {q c : Nat}
    (hr : s.gpr r = s.gpr .edi + BitVec.ofNat 32 q) (hq : q + c < 8192) :
    s.ea (at_ r c) = off base (q + c) := by
  change (s.gpr r + BitVec.ofNat 32 c).setWidth 64 = _
  rw [hr, Offset.add_add]
  exact hs.ea hq

/-- After `i` bits of `K`, with the counter `e` (`i`, or `i - 1` before it is moved up): the
recoding's state (`Slide.run`) in `ebx`, `eax` and `ecx`; the bytes below `i` those of the digits
of the bits read, and the bytes from `i` on still the bits. -/
structure RecSt (base : Addr) (K i e : Nat) (s : State) : Prop where
  scr : Scr s base
  esi : s.gpr .esi = BitVec.ofNat 32 e
  ebx : s.gpr .ebx = BitVec.ofNat 32 (Slide.run K i).m
  eax : s.gpr .eax = s.gpr .edi + BitVec.ofNat 32 (Slide.run K i).p
  ecx : s.gpr .ecx = BitVec.ofNat 32 (Slide.run K i).w
  dig : ∀ q < i, s.mem (off base (KBITS + q)) = BitVec.ofNat 8 ((Slide.run K i).u q)
  rest : ∀ q, i ≤ q → q < 456 → s.mem (off base (KBITS + q)) = BitVec.ofNat 8 (kbit K q)

/-- After a bit's first block: the bit loaded, its address, and the test of a window in hand. -/
structure RecH (base : Addr) (K i : Nat) (s : State) : Prop where
  st : RecSt base K i i s
  ebp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 i
  edx : s.gpr .edx = (BitVec.ofNat 8 (kbit K i)).setWidth 32
  zf : s.zf = some (decide ((Slide.run K i).m = 0))

theorem run_m_lt (K i : Nat) : (Slide.run K i).m < 16 := by
  rcases (Proof.Ed25519.Slide.run_good K i).m_cases with e | e | e | e <;> rw [e] <;> decide

theorem recHead_ok {base : Addr} {K i : Nat} {s : State} (h : RecSt base K i i s) (hi : i < 456) :
    WP isa (.block recHead) s fun t => RecH base K i t ∧ Keeps recRegs s t ∧ t.mem = s.mem := by
  have hK : KBITS = 4608 := rfl
  obtain ⟨hs, hesi, hebx, heax, hecx, hdig, hrest⟩ := h
  unfold recHead
  refine wp_mov rfl fun u1 v1 => wp_alu (Or.inl rfl) rfl fun u2 v2 _ => ?_
  obtain hs2 : Scr u2 base := (hs.of_upd v1 (by decide)).of_upd v2 (by decide)
  obtain p2 : u2.gpr .ebp = u2.gpr .edi + BitVec.ofNat 32 i := by
    rw [v2.gpr, v2.other .edi (by decide)]; change u1.gpr .ebp + u1.gpr .esi = _
    rw [v1.gpr, v1.other .esi (by decide), v1.other .edi (by decide), hesi]
  refine wp_load8 (a := off base (i + KBITS)) (ptr_ea hs2 p2 (by omega_using [hi, hK]))
    (hs2.read (by omega_using [hi, hK])) fun u3 v3 => wp_cmp rfl fun t ft hz => WP.block_nil ?_
  obtain k : Keeps recRegs s t :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans (ft.rest _)))
  obtain m : t.mem = s.mem := by rw [ft.mem, v3.mem, v2.mem, v1.mem]
  obtain g : ∀ r, r ≠ .ebp → r ≠ .edx → t.gpr r = s.gpr r := fun r h1 h2 => by
    rw [ft.gpr, v3.other r h2, v2.other r h1, v1.other r h1]
  refine ⟨⟨⟨hs.of_keeps k (by decide), ?_, ?_, ?_, ?_, fun q hq => ?_, fun q h1 h2 => ?_⟩, ?_, ?_, ?_⟩, k, m⟩
  · rw [g _ (by decide) (by decide), hesi]
  · rw [g _ (by decide) (by decide), hebx]
  · rw [g _ (by decide) (by decide), g .edi (by decide) (by decide), heax]
  · rw [g _ (by decide) (by decide), hecx]
  · rw [m]; exact hdig q hq
  · rw [m]; exact hrest q h1 h2
  · rw [ft.gpr, v3.other .ebp (by decide), v3.other .edi (by decide), p2]
  · rw [ft.gpr, v3.gpr, v2.mem, v1.mem, Nat.add_comm i KBITS, hrest i (Nat.le_refl _) hi]
  · rw [hz, v3.other .ebx (by decide), v2.other .ebx (by decide), v1.other .ebx (by decide), hebx]
    exact congrArg some (rec_grow_fact 0 (by decide) _ (run_m_lt K i)).2.2

/-- No window in hand: the bit is the digit, and opens a window if it is set. -/
theorem recOpen_ok {base : Addr} {K i : Nat} {s : State} (h : RecH base K i s) (hi : i < 456)
    (h0 : (Slide.run K i).m = 0) :
    WP isa (.block recOpen) s fun t => RecSt base K (i + 1) i t ∧ Keeps recRegs s t ∧ t.mem = s.mem := by
  obtain ⟨⟨hs, hesi, hebx, heax, hecx, hdig, hrest⟩, hebp, hedx, -⟩ := h
  obtain Si := Proof.Ed25519.Slide.run_i K i
  obtain ⟨em, ew, ep, eu⟩ := Proof.Ed25519.Slide.step_idle (K := K) h0
  rw [Si, ← kbit_eq] at em ew eu
  rw [Si] at ep
  obtain of := rec_open_fact _ (kbit_lt K i)
  unfold recOpen
  refine wp_mov rfl fun u1 v1 => wp_mov rfl fun u2 v2 => wp_alu (Or.inl rfl) rfl fun u3 v3 _ =>
    wp_mov rfl fun t vt => WP.block_nil ?_
  obtain k : Keeps recRegs s t :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans (vt.rest (by decide))))
  obtain m : t.mem = s.mem := by rw [vt.mem, v3.mem, v2.mem, v1.mem]
  refine ⟨⟨hs.of_keeps k (by decide), ?_, ?_, ?_, ?_, fun q hq => ?_, fun q h1 h2 => ?_⟩, k, m⟩
  · rw [vt.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), hesi]
  · rw [vt.other _ (by decide), v3.gpr]; change u2.gpr .ebx + u2.gpr .ebx = _
    rw [v2.gpr, v1.other _ (by decide), hedx, Proof.Ed25519.Slide.run_succ, em]
    exact of.2
  · rw [vt.gpr, v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), hebp,
      k.1 _ (by decide), Proof.Ed25519.Slide.run_succ, ep]
  · rw [vt.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide), v1.gpr, hedx,
      Proof.Ed25519.Slide.run_succ, ew]
    exact of.1
  · rw [m, Proof.Ed25519.Slide.run_succ, eu]
    by_cases hqi : q = i
    · rw [hqi, Proof.Ed25519.Slide.upd_self]; exact hrest i (Nat.le_refl _) hi
    · rw [Proof.Ed25519.Slide.upd_ne _ _ hqi]; exact hdig q (by omega_using [hq, hqi])
  · rw [m]; exact hrest q (by omega_using [h1]) h2

/-- A window in hand: the bit is added to its digit, and the digit of the bit is zero. -/
theorem recGrow_ok {base : Addr} {K i : Nat} {s : State} (h : RecH base K i s) (hi : i < 456)
    (h0 : (Slide.run K i).m ≠ 0) :
    WP isa (.block recGrow) s fun t => RecSt base K (i + 1) i t ∧ Keeps recRegs s t ∧
      Outside base KBITS 456 s.mem t.mem := by
  have hK : KBITS = 4608 := rfl
  obtain ⟨⟨hs, hesi, hebx, heax, hecx, hdig, hrest⟩, hebp, hedx, -⟩ := h
  obtain G := Proof.Ed25519.Slide.run_good K i
  obtain Si := Proof.Ed25519.Slide.run_i K i
  obtain ⟨em, ew, ep, eu⟩ := Proof.Ed25519.Slide.step_grow (K := K) h0
  rw [Si, ← kbit_eq] at ew eu
  obtain ⟨hp1, -, -, -, -, -⟩ := G.m.resolve_left h0
  rw [Si] at hp1
  obtain hS := Proof.Ed25519.Slide.run_succ K i
  obtain hm16 := run_m_lt K i
  generalize Slide.run K i = T at hebx heax hecx hdig em ew ep eu hp1 hS hm16
  obtain gf := rec_grow_fact _ (kbit_lt K i) _ hm16
  unfold recGrow
  refine wp_alu (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) rfl fun u1 v1 _ =>
    wp_alu (Or.inl rfl) rfl fun u2 v2 _ => wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun u3 v3 _ =>
    wp_alu (Or.inl rfl) rfl fun u4 v4 _ => wp_mov rfl fun u5 v5 => ?_
  obtain k5 : Keeps recRegs s u5 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide)))))
  obtain m5 : u5.mem = s.mem := by rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  obtain hs5 := hs.of_keeps k5 (by decide)
  obtain c5 : u5.gpr .ecx = BitVec.ofNat 32 (T.w + T.m * kbit K i) := by
    rw [v5.other _ (by decide), v4.gpr]; change u3.gpr .ecx + u3.gpr .edx = _
    rw [v3.gpr, v3.other .ecx (by decide), v2.other .ecx (by decide), v1.other .ecx (by decide), hecx]
    change _ + (u2.gpr .edx &&& u2.gpr .ebx) = _
    rw [v2.gpr, v2.other .ebx (by decide), v1.other .ebx (by decide), hebx]
    change _ + ((u1.gpr .edx + 1) &&& _) = _
    rw [v1.gpr]; change _ + (((s.gpr .edx ^^^ (0xFFFFFFFF : BitVec 32)) + 1) &&& _) = _
    rw [hedx, gf.1, ← BitVec.ofNat_add]
  obtain b5 : u5.gpr .ebx = BitVec.ofNat 32 T.m := by
    rw [v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide),
      v1.other _ (by decide), hebx]
  obtain p5 : u5.gpr .ebp = u5.gpr .edi + BitVec.ofNat 32 i := by
    rw [k5.1 .edi (by decide), v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide),
      v2.other _ (by decide), v1.other _ (by decide), hebp]
  obtain a5 : u5.gpr .eax = u5.gpr .edi + BitVec.ofNat 32 T.p := by
    rw [k5.1 .edi (by decide), v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide),
      v2.other _ (by decide), v1.other _ (by decide), heax]
  refine wp_store8 (a := off base (i + KBITS)) (ptr_ea hs5 p5 (by omega_using [hi, hK]))
    (hs5.write (by omega_using [hi, hK])) fun u6 v6 => ?_
  obtain hs6 := hs5.of_keeps (v6.rest []) (by decide)
  refine wp_store8 (a := off base (T.p + KBITS))
    (ptr_ea hs6 (by rw [v6.gpr]; exact a5) (by omega_using [hi, hp1, hK]))
    (hs6.write (by omega_using [hi, hp1, hK])) fun u7 v7 =>
    wp_alu (Or.inl rfl) rfl fun u8 v8 _ => wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun t vt _ =>
      WP.block_nil ?_
  obtain k : Keeps recRegs s t :=
    k5.trans ((v6.rest _).trans ((v7.rest _).trans ((v8.rest (by decide)).trans (vt.rest (by decide)))))
  obtain m : t.mem = (s.mem.writeW (off base (KBITS + i)) (BitVec.ofNat 8 0)).writeW (off base (KBITS + T.p))
      (BitVec.ofNat 8 (T.w + T.m * kbit K i)) := by
    rw [vt.mem, v8.mem, v7.mem, v6.mem, m5]
    change (s.mem.writeW _ ((u5.gpr .edx).setWidth 8)).writeW _ ((u6.gpr .ecx).setWidth 8) = _
    rw [v6.gpr, c5, v5.gpr, ofNat32_setWidth8, Nat.add_comm i KBITS, Nat.add_comm T.p KBITS]
    rfl
  refine ⟨⟨hs.of_keeps k (by decide), ?_, ?_, ?_, ?_, fun q hq => ?_, fun q h1 h2 => ?_⟩, k, ?_⟩
  · rw [vt.other _ (by decide), v8.other _ (by decide), v7.gpr, v6.gpr, v5.other _ (by decide),
      v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), hesi]
  · rw [vt.gpr]; change u8.gpr .ebx &&& (15 : BitVec 32) = _
    rw [v8.gpr]; change (u7.gpr .ebx + u7.gpr .ebx) &&& (15 : BitVec 32) = _
    rw [v7.gpr, v6.gpr, b5, hS, em]
    exact gf.2.1
  · rw [k.1 .edi (by decide), vt.other _ (by decide), v8.other _ (by decide), v7.gpr, v6.gpr, a5,
      k5.1 .edi (by decide), hS, ep]
  · rw [vt.other _ (by decide), v8.other _ (by decide), v7.gpr, v6.gpr, c5, hS, ew]
  · rw [m, hS, eu, writeW8_apply]
    by_cases hqp : q = T.p
    · rw [hqp, ite_eq_left rfl, Proof.Ed25519.Slide.upd_self]
    · rw [ite_eq_right (fun e => hqp ((off_eq_iff base (by omega_using [hq, hi, hK]) (by omega_using [hp1, hi, hK])).mp e
          |> fun e' => by omega_using [e'])), writeW8_apply, Proof.Ed25519.Slide.upd_ne _ _ hqp]
      by_cases hqi : q = i
      · rw [hqi, ite_eq_left rfl, Proof.Ed25519.Slide.upd_self]
      · rw [ite_eq_right (fun e => hqi ((off_eq_iff base (by omega_using [hq, hi, hK]) (by omega_using [hi, hK])).mp e
            |> fun e' => by omega_using [e'])), Proof.Ed25519.Slide.upd_ne _ _ hqi]
        exact hdig q (by omega_using [hq, hqi])
  · rw [m, writeW8_outside _ _ _ (by omega_using [hp1, hi, hK])
        (by rw [ofs_off' base (by omega_using [h2, hK])]; omega_using [h1, hp1]),
      writeW8_outside _ _ _ (by omega_using [hi, hK]) (by rw [ofs_off' base (by omega_using [h2, hK])]; omega_using [h1])]
    exact hrest q (by omega_using [h1]) h2
  · intro y hy
    rw [m, writeW8_outside _ _ _ (by omega_using [hp1, hi, hK]) (by omega_using [hy, hp1, hi]),
      writeW8_outside _ _ _ (by omega_using [hi, hK]) (by omega_using [hy, hi])]

/-- The next bit. -/
theorem recNext_ok {base : Addr} {K i : Nat} {s : State} (h : RecSt base K (i + 1) i s) (hi : i < 456) :
    WP isa (.block recNext) s fun t => RecSt base K (i + 1) (i + 1) t ∧
      t.zf = some (decide (i + 1 = 456)) ∧ Keeps recRegs s t ∧ t.mem = s.mem := by
  obtain ⟨hs, hesi, hebx, heax, hecx, hdig, hrest⟩ := h
  unfold recNext
  refine wp_alu (Or.inl rfl) rfl fun u1 v1 _ => wp_cmp rfl fun t ft hz => WP.block_nil ?_
  obtain k : Keeps recRegs s t := (v1.rest (by decide)).trans (ft.rest _)
  obtain m : t.mem = s.mem := by rw [ft.mem, v1.mem]
  obtain g1 : u1.gpr .esi = BitVec.ofNat 32 i + 1 := by rw [v1.gpr]; change s.gpr .esi + 1 = _; rw [hesi]
  refine ⟨⟨hs.of_keeps k (by decide), ?_, ?_, ?_, ?_, fun q hq => ?_, fun q h1 h2 => ?_⟩, ?_, k, m⟩
  · rw [ft.gpr, g1]; exact (BitVec.ofNat_add i 1).symm
  · rw [ft.gpr, v1.other _ (by decide), hebx]
  · rw [ft.gpr, v1.other _ (by decide), v1.other .edi (by decide), heax]
  · rw [ft.gpr, v1.other _ (by decide), hecx]
  · rw [m]; exact hdig q hq
  · rw [m]; exact hrest q h1 h2
  · rw [hz, g1]; exact congrArg some (rec_next_fact i hi)

/-- One bit. -/
theorem recBit_ok {base : Addr} {K i : Nat} {s : State} (h : RecSt base K i i s) (hi : i < 456) :
    WP isa recBit s fun u => Keeps recRegs s u ∧ Outside base KBITS 456 s.mem u.mem ∧
      RecSt base K (i + 1) (i + 1) u ∧ u.zf = some (decide (i + 1 = 456)) := by
  rw [recBit]
  refine WP.seq (WP.mono (recHead_ok h hi) fun s₁ ⟨h₁, k₁, m₁⟩ => ?_)
  have mid : WP isa (.ite .e (.block recOpen) (.block recGrow)) s₁ fun x =>
      RecSt base K (i + 1) i x ∧ Keeps recRegs s₁ x ∧ Outside base KBITS 456 s₁.mem x.mem := by
    refine WP.ite (decide ((Slide.run K i).m = 0)) h₁.zf (fun h0 => ?_) (fun h0 => ?_)
    · exact WP.mono (recOpen_ok h₁ hi (of_decide_eq_true h0)) fun x ⟨a, k, m⟩ =>
        ⟨a, k, by rw [m]; exact Outside.refl _ _ _ _⟩
    · exact recGrow_ok h₁ hi (of_decide_eq_false h0)
  refine WP.seq (WP.mono mid fun s₂ ⟨h₂, k₂, o₂⟩ => ?_)
  refine WP.mono (recNext_ok h₂ hi) fun u ⟨hu, zu, ku, mu⟩ => ⟨k₁.trans (k₂.trans ku), ?_, hu, zu⟩
  rw [mu, ← m₁]; exact o₂

/-- No bit read. -/
theorem recInit_ok {base : Addr} {K : Nat} {s : State} (hs : Scr s base)
    (hbits : ∀ q < 456, s.mem (off base (KBITS + q)) = BitVec.ofNat 8 (kbit K q)) :
    WP isa (.block recInit) s fun t => Keeps recRegs s t ∧ t.mem = s.mem ∧ RecSt base K 0 0 t := by
  unfold recInit
  refine wp_mov rfl fun u1 v1 => wp_mov rfl fun u2 v2 => wp_mov rfl fun u3 v3 => wp_mov rfl fun t vt =>
    WP.block_nil ?_
  obtain k : Keeps recRegs s t :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans (vt.rest (by decide))))
  obtain m : t.mem = s.mem := by rw [vt.mem, v3.mem, v2.mem, v1.mem]
  refine ⟨k, m, hs.of_keeps k (by decide), ?_, ?_, ?_, ?_, fun q hq => absurd hq (Nat.not_lt_zero _),
    fun q _ hq => by rw [m]; exact hbits q hq⟩
  · rw [vt.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide), v1.gpr]; rfl
  · rw [vt.other _ (by decide), v3.other _ (by decide), v2.gpr]; rfl
  · rw [vt.gpr, vt.other .edi (by decide)]
    exact (BitVec.add_zero _).symm
  · rw [vt.other _ (by decide), v3.gpr]; rfl

/-- `k`'s digits in place of its bits. -/
theorem vrecode_ok {base : Addr} {K : Nat} {s : State} (hs : Scr s base)
    (hbits : ∀ q < 456, s.mem (off base (KBITS + q)) = BitVec.ofNat 8 (kbit K q)) :
    WP isa vrecode s fun t => Keeps recRegs s t ∧ Outside base KBITS 456 s.mem t.mem ∧
      ∀ q < 456, t.mem (off base (KBITS + q)) = BitVec.ofNat 8 (vdigits K q) := by
  rw [vrecode]
  refine WP.seq (WP.mono (recInit_ok hs hbits) fun s₁ ⟨k₁, m₁, a₁⟩ => ?_)
  refine WP.loop (M := isa) (fun n t => 0 < n ∧ n ≤ 456 ∧ Keeps recRegs s t ∧
    Outside base KBITS 456 s.mem t.mem ∧ RecSt base K (456 - n) (456 - n) t) ?_ 456 s₁
    ⟨by decide, Nat.le_refl _, k₁, by rw [m₁]; exact Outside.refl _ _ _ _, by rw [Nat.sub_self]; exact a₁⟩
  intro n x ⟨n0, n456, kx, fx, ax⟩
  refine WP.mono (recBit_ok ax (by omega_using [n0])) fun t ⟨kt, ft, at', zt⟩ => ?_
  by_cases h1 : n = 1
  · subst h1
    rw [show 456 - 1 + 1 = 456 from rfl] at at' zt
    refine .inl ⟨by rw [evalNe zt]; rfl, kx.trans kt, fx.trans ft, fun q hq => ?_⟩
    show t.mem _ = BitVec.ofNat 8 (Proof.Ed25519.Slide.digits 456 K q)
    rw [Proof.Ed25519.Slide.digits_eq]
    exact at'.dig q hq
  · refine .inr ⟨by rw [evalNe zt, decide_eq_false (by omega_using [h1, n0])]; rfl, n - 1,
      by omega_using [n0], by omega_using [h1, n0], by omega_using [n456], kx.trans kt, fx.trans ft, ?_⟩
    rw [show 456 - (n - 1) = 456 - n + 1 by omega_using [n0, n456]]
    exact at'

end VG.Proof.Ed448.X86

end

end

/-! ### `Ed448.X86.VerifyTable`, which this module and modules that import it used -/

section

/-!
# Ed448 verification's equation on x86 (32-bit): the table of `-A`'s odd multiples

`vtable_ok`: `vtable` leaves entry `j < 8` of the table at `VTAB` as `oddMul A j`
(`Proof/Ed448/CombRef.lean`), the multiple `[2j + 1]` of the point `A` in slots 6, 7 and 10, its
coordinates' limbs bounded (`TabOk`), and `Q` the neutral point. An entry is stored from `Q`
(`ventryStore_ok`), three slots copied to the words at `ebp` (`toEntry_ok`), and read back into
slots the same way (`fromEntry_ok`, `ventryLoad_ok`); the field operations write below the table
(`EntryOk.keep`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448 VG.Impl.Ed448.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.Ed448 (double oddMul pt addWith)
open VG.Impl.X448.X86 (slot ACC ld st at_ ops)

/-! ## Operations and where they write -/

def fdest : FieldOp → Index
  | .mul o _ _ | .add o _ _ | .sub o _ _ | .mulSmall o _ | .copy o _ => o

theorem fop_apply_keep (op : FieldOp) (e : Env) {i : Index} (h : fdest op ≠ i) :
    op.apply e i = e i := by
  cases op <;> exact Function.update_of_ne (Ne.symm h) _ _

theorem applyOps_keep (xs : List FieldOp) (e : Env) {i : Index} (h : i ∉ xs.map fdest) :
    applyOps xs e i = e i := by
  induction xs generalizing e with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [applyOps, ih _ h.2, fop_apply_keep _ _ (Ne.symm h.1)]

/-- The point in slots `x`, `y`, `z` doubled in place (RFC 8032 §5.2.4), with the temporaries
12–19. -/
def doubleF (x y z : Index) : List FieldOp := [
  .add 12 x y, .mul 12 12 12, .mul 13 x x, .mul 14 y y, .add 15 13 14, .mul 16 z z,
  .add 17 16 16, .sub 17 15 17, .sub 18 12 15, .mul x 18 17, .sub 19 13 14, .mul y 15 19,
  .mul z 15 17]

/-- `T = Q + (x : y : z)` into slots 3–5, for `Q` in slots 0–2 and `d` in slot 11, with the
temporaries 12–20. -/
def addF (x y z : Index) : List FieldOp := [
  .mul 12 2 z, .mul 13 12 12, .mul 14 0 x, .mul 15 1 y, .mul 16 11 14, .mul 16 16 15,
  .sub 17 13 16, .add 18 13 16, .add 19 0 1, .add 20 x y, .mul 19 19 20, .mul 20 12 17,
  .sub 19 19 14, .sub 19 19 15, .mul 3 20 19, .mul 20 12 18, .sub 19 15 14, .mul 4 20 19,
  .mul 5 17 18]

/-- `T` (slots 3–5) taken into `Q` (slots 0–2). -/
def takeF : List FieldOp := [.copy 0 3, .copy 1 4, .copy 2 5]

/-- `Q` and the copy of `-A`'s `Z` in slot 21. -/
def tableQF : List FieldOp := [.copy 0 6, .copy 1 7, .copy 2 10, .copy 21 10]

/-- `Q` the neutral point. -/
def neutralF : List FieldOp := [.sub 0 0 0, .copy 1 10, .copy 2 10]

theorem doubleF0_impl : doubleOps.map toOp = (doubleF 0 1 2).map FieldOp.impl := by decide +kernel
theorem doubleF6_impl : (doubleAt 6 7 21).map toOp = (doubleF 6 7 21).map FieldOp.impl := by decide +kernel
theorem addTake8_impl : addTake addOps = ops ((addF 8 9 10 ++ takeF).map FieldOp.impl) :=
  congrArg ops (by decide +kernel)
theorem addTake6_impl : addTake (addAtZ 6 7 21) = ops ((addF 6 7 21 ++ takeF).map FieldOp.impl) :=
  congrArg ops (by decide +kernel)
theorem tableQF_impl : vtableQ = tableQF.map FieldOp.impl := by decide +kernel
theorem neutralF_impl : vneutral = neutralF.map FieldOp.impl := by decide +kernel

theorem doubleF_eval0 (e : Env) :
    pt (applyOps (doubleF 0 1 2) e) 0 1 2 = double (pt e 0 1 2) := rfl

theorem doubleF_eval6 (e : Env) :
    pt (applyOps (doubleF 6 7 21) e) 6 7 21 = double (pt e 6 7 21) := rfl

theorem doubleF_keep0 (e : Env) (i : Index)
    (hi : 3 ≤ i.val ∧ i.val < 12 ∨ i.val = 20 ∨ i.val = 21) :
    applyOps (doubleF 0 1 2) e i = e i := by
  refine applyOps_keep _ _ ?_
  revert i; decide

theorem doubleF_keep6 (e : Env) (i : Index)
    (hi : i.val < 6 ∨ (8 ≤ i.val ∧ i.val < 12) ∨ i.val = 20) :
    applyOps (doubleF 6 7 21) e i = e i := by
  refine applyOps_keep _ _ ?_
  revert i; decide

/-- The slots an addition writes, whatever its second point's. -/
theorem addF_dest (x y z : Index) :
    (addF x y z).map fdest = [12, 13, 14, 15, 16, 16, 17, 18, 19, 20, 19, 20, 19, 19, 3, 20, 19, 4, 5] := rfl

theorem addTake_keep (e : Env) (x y z : Index) (i : Index) (hi : (6 ≤ i.val ∧ i.val < 12) ∨ i.val = 21) :
    applyOps (addF x y z ++ takeF) e i = e i := by
  refine applyOps_keep _ _ ?_
  rw [List.map_append, addF_dest]
  revert i; decide

theorem addTake_pt6 (e : Env) :
    pt (applyOps (addF 6 7 21 ++ takeF) e) 0 1 2 = addWith (e 11) (pt e 0 1 2) (pt e 6 7 21) := rfl

/-! ## An entry's words -/

/-- The limbs of the slot at `a` to the twenty-eight words at `ebp + o`, which are at byte `e + o`
of the working space, above the slots. -/
theorem toEntry_ok {s : State} {base : Addr} (hs : Scr s base) {o a e : Nat} (ha : a + 112 ≤ 4096)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 e) (hq1 : 4096 ≤ e + o) (hq2 : e + o + 112 ≤ 8192) :
    WP isa (.block (toEntry o a)) s fun t =>
      (∀ i < 28, limbs t.mem base (e + o) i = limbs s.mem base a i) ∧
      Outside base (e + o) 112 s.mem t.mem ∧ Keeps [.eax] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base (e + o) i = limbs s.mem base a i) ∧
    Outside base (e + o) 112 s.mem t.mem ∧ Keeps [.eax] s t
  obtain step : ∀ n t, n < 28 → inv n t →
      WP isa (.block [ld .eax (a + 4 * n), .store (at_ .ebp (o + 4 * n)) .eax]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    obtain ht := hs.of_keeps tk (by decide)
    refine load_ok ht (by omega_using [ha, hn]) fun u hu => ?_
    obtain hu' := ht.of_upd hu (by decide)
    refine wp_store (a := off base (e + o + 4 * n))
      (by rw [ptr_ea hu' (by rw [hu.other _ (by decide), hu.other .edi (by decide), tk.1 _ (by decide),
            tk.1 .edi (by decide)]; exact hp) (by omega_using [hq2, hn]), Nat.add_assoc])
      (hu'.write (by omega_using [hq2, hn])) fun v hv => WP.block_nil ?_
    obtain out : Outside base (e + o + 4 * n) 4 t.mem v.mem := by
      rw [hv.mem, hu.mem]; exact writeW_outside _ _ _ (by omega_using [hq2, hn])
    refine ⟨fun i hi => ?_, tm.trans (out.mono (by omega_using []) (by omega_using [hn])),
      tk.trans ((hu.rest (by decide)).trans (hv.rest _))⟩
    change (word v.mem base (e + o + 4 * i)).toNat = _
    rw [hv.mem, hu.mem, word_write t.mem base (by omega_using [hq2, hn]) (by omega_using [hq2, hn, hi])]
    by_cases h : i = n
    · rw [ite_eq_left h, h, hu.gpr]
      exact congrArg BitVec.toNat (tm.word (Or.inl (by omega_using [ha, hq1, hn])) (by omega_using [ha, hn]))
    · rw [ite_eq_right h]; exact tf i (by omega_using [hi, h])
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hi => absurd hi (Nat.not_lt_zero _), Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- The twenty-eight words at `ebp + a`, which are at byte `e + a` of the working space, above the
slots, to the limbs of the slot at `o`. -/
theorem fromEntry_ok {s : State} {base : Addr} (hs : Scr s base) {o a e : Nat} (ho : o + 112 ≤ 4096)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 e) (hq1 : 4096 ≤ e + a) (hq2 : e + a + 112 ≤ 8192) :
    WP isa (.block (fromEntry o a)) s fun t =>
      (∀ i < 28, limbs t.mem base o i = limbs s.mem base (e + a) i) ∧
      Outside base o 112 s.mem t.mem ∧ Keeps [.eax] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base o i = limbs s.mem base (e + a) i) ∧
    Outside base o 112 s.mem t.mem ∧ Keeps [.eax] s t
  obtain step : ∀ n t, n < 28 → inv n t →
      WP isa (.block [.mov .eax (.mem (at_ .ebp (a + 4 * n))), st .eax (o + 4 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    obtain ht := hs.of_keeps tk (by decide)
    refine wp_load (a := off base (e + a + 4 * n))
      (by rw [ptr_ea ht (by rw [tk.1 _ (by decide), tk.1 .edi (by decide)]; exact hp) (by omega_using [hq2, hn]),
            Nat.add_assoc])
      (ht.read (by omega_using [hq2, hn])) fun u hu => ?_
    refine store_ok (ht.of_upd hu (by decide)) (by omega_using [ho, hn]) fun v hv => WP.block_nil ?_
    obtain out : Outside base (o + 4 * n) 4 t.mem v.mem := by
      rw [hv.mem, hu.mem]; exact writeW_outside _ _ _ (by omega_using [ho, hn])
    refine ⟨fun i hi => ?_, tm.trans (out.mono (by omega_using []) (by omega_using [hn])),
      tk.trans ((hu.rest (by decide)).trans (hv.rest _))⟩
    change (word v.mem base (o + 4 * i)).toNat = _
    rw [hv.mem, hu.mem, word_write t.mem base (by omega_using [ho, hn]) (by omega_using [ho, hn, hi])]
    by_cases h : i = n
    · rw [ite_eq_left h, h, hu.gpr]
      exact congrArg BitVec.toNat (tm.word (Or.inr (by omega_using [ho, hq1])) (by omega_using [hq2, hn]))
    · rw [ite_eq_right h]; exact tf i (by omega_using [hi, h])
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hi => absurd hi (Nat.not_lt_zero _), Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- A slot from the entry's words at `ebp + a`. -/
theorem slotFrom_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o : Index)
    {a e : Nat} (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 e) (hq1 : 4096 ≤ e + a)
    (hq2 : e + a + 112 ≤ 8192) (hbq : Bounded s.mem base (e + a)) :
    WP isa (.block (fromEntry (slot o.val) a)) s fun t =>
      Keep base s t ∧ Keeps [.eax] s t ∧ BoundedEnv t.mem base ∧
      E t.mem base = Function.update (E s.mem base) o (F s.mem base (e + a)) := by
  refine WP.mono (fromEntry_ok hs (Nat.le_trans (slot_bound o) (by decide)) hp hq1 hq2)
    fun t ⟨tf, tm, tk⟩ => ?_
  have op : Op base (slot o.val) s t := ⟨tk.mono (by decide), FieldMem.output tm⟩
  refine ⟨op.keep, tk, bounded_update (op.mem.ws (by decide)) hb (fun i hi => ?_), ?_⟩
  · rw [tf i hi]; exact hbq i hi
  · rw [E_update (op.mem.ws (by decide)), show F t.mem base (slot o.val) = F s.mem base (e + a) from
      congrArg Proof.X448.toFe (valN_congr tf)]

/-! ## The table -/

/-- Entry `j` of the table holds the point `p`, its limbs bounded. -/
structure EntryOk (base : Addr) (m : Mem) (j : Nat) (p : Spec.Ed448.Point) : Prop where
  bx : Bounded m base (VTAB + 384 * j)
  by' : Bounded m base (VTAB + 384 * j + 128)
  bz : Bounded m base (VTAB + 384 * j + 256)
  x : F m base (VTAB + 384 * j) = p.X
  y : F m base (VTAB + 384 * j + 128) = p.Y
  z : F m base (VTAB + 384 * j + 256) = p.Z

/-- An entry whose words are kept. -/
theorem EntryOk.of_words {base : Addr} {m m' : Mem} {j : Nat} {p : Spec.Ed448.Point} (h : EntryOk base m j p)
    (hw : ∀ d, VTAB + 384 * j ≤ d → d + 4 ≤ VTAB + 384 * (j + 1) → word m' base d = word m base d) :
    EntryOk base m' j p := by
  obtain lim : ∀ c, c + 112 ≤ 384 → ∀ i < 28,
      limbs m' base (VTAB + 384 * j + c) i = limbs m base (VTAB + 384 * j + c) i := fun c hc i hi =>
    congrArg BitVec.toNat (hw _ (by omega_arith) (by omega_using [hc, hi]))
  obtain l0 : ∀ i < 28, limbs m' base (VTAB + 384 * j) i = limbs m base (VTAB + 384 * j) i := fun i hi =>
    lim 0 (by decide) i hi
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_⟩
  · rw [l0 i hi]; exact h.bx i hi
  · rw [lim 128 (by decide) i hi]; exact h.by' i hi
  · rw [lim 256 (by decide) i hi]; exact h.bz i hi
  · exact (congrArg Proof.X448.toFe (valN_congr l0)).trans h.x
  · exact (congrArg Proof.X448.toFe (valN_congr (lim 128 (by decide)))).trans h.y
  · exact (congrArg Proof.X448.toFe (valN_congr (lim 256 (by decide)))).trans h.z

/-- The field operations write below the table. -/
theorem EntryOk.keep {base : Addr} {m m' : Mem} {j : Nat} {p : Spec.Ed448.Point} (h : EntryOk base m j p)
    (hj : j < 8) (hm : WsOut2 base 64 2816 ACC 512 m m') : EntryOk base m' j p :=
  h.of_words fun d h1 h2 => hm.word (Or.inr (by simp only [VTAB] at h1; omega_using [h1]))
    (Or.inr (by simp only [VTAB, ACC] at h1 ⊢; omega_using [h1])) (by simp only [VTAB] at h2; omega_using [h2, hj])

/-- Another entry's store keeps it. -/
theorem EntryOk.other {base : Addr} {m m' : Mem} {j k : Nat} {p : Spec.Ed448.Point} (h : EntryOk base m j p)
    (hj : j < 8) (hjk : j ≠ k) (hm : Outside base (VTAB + 384 * k) 384 m m') : EntryOk base m' j p :=
  h.of_words fun d h1 h2 => hm.word (by omega_using [h1, h2, hjk])
    (by simp only [VTAB] at h2; omega_using [h2, hj])

/-- The table of the odd multiples of `A`. -/
def TabOk (base : Addr) (A : Spec.Ed448.Point) (m : Mem) : Prop := ∀ j < 8, EntryOk base m j (oddMul A j)

/-- A store of an entry writes within the table, above the field arithmetic. -/
theorem outT {base : Addr} {j : Nat} {m m' : Mem} (h : Outside base (VTAB + 384 * j) 384 m m') (hj : j < 8) :
    Outside base VTAB 3072 m m' := h.mono (by omega_arith) (by omega_using [hj])

/-- The next entry's place, and the test of the last. -/
theorem store_next_fact : ∀ j < 8,
    BitVec.ofNat 32 (VTAB + 384 * j) + (384 : BitVec 32) = BitVec.ofNat 32 (VTAB + 384 * (j + 1)) ∧
    (BitVec.ofNat 32 (VTAB + 384 * (j + 1)) - BitVec.ofNat 32 (VTAB + 8 * 384) == 0) =
      decide (j + 1 = 8) := by decide

/-- `Q` stored as entry `j`. -/
theorem ventryStore_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) {j : Nat}
    (hj : j < 8) (h11 : s.gpr .esi = BitVec.ofNat 32 (VTAB + 384 * j)) :
    WP isa (.block ventryStore) s fun t =>
      Keeps [.eax, .ebp, .esi] s t ∧ Outside base (VTAB + 384 * j) 384 s.mem t.mem ∧
      EntryOk base t.mem j (pt (E s.mem base) 0 1 2) ∧
      t.gpr .esi = BitVec.ofNat 32 (VTAB + 384 * (j + 1)) ∧ t.zf = some (decide (j + 1 = 8)) := by
  have hT : VTAB = 5120 := rfl
  obtain nf := store_next_fact j hj
  rw [ventryStore, List.append_assoc, List.append_assoc, List.append_assoc, List.cons_append, List.cons_append,
    List.nil_append]
  refine wp_mov rfl fun s₀ u₀ => wp_alu (Or.inl rfl) rfl fun s₁ u₁ _ => ?_
  obtain k01 : Keeps [.eax, .ebp, .esi] s s₁ := (u₀.rest (by decide)).trans (u₁.rest (by decide))
  obtain m₁ : s₁.mem = s.mem := by rw [u₁.mem, u₀.mem]
  obtain hs₁ := hs.of_keeps k01 (by decide)
  obtain hp₁ : s₁.gpr .ebp = s₁.gpr .edi + BitVec.ofNat 32 (VTAB + 384 * j) := by
    rw [u₁.gpr, u₁.other .edi (by decide)]; change s₀.gpr .ebp + s₀.gpr .esi = _
    rw [u₀.gpr, u₀.other .esi (by decide), u₀.other .edi (by decide), h11]
  obtain sl : ∀ i : Index, slot i.val + 112 ≤ 2880 := fun i => (slot_range i).2
  -- `X`.
  refine WP.block_append_iff.mpr (WP.mono (toEntry_ok hs₁ (o := 0) (a := slot (0 : Index).val)
    (by have := sl 0; omega_arith) hp₁ (by omega_arith) (by omega_arith)) fun s₂ ⟨f₂, o₂, k₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  obtain hp₂ : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (VTAB + 384 * j) := by
    rw [k₂.1 _ (by decide), k₂.1 .edi (by decide), hp₁]
  -- `Y`.
  refine WP.block_append_iff.mpr (WP.mono (toEntry_ok hs₂ (o := 128) (a := slot (1 : Index).val)
    (by have := sl 1; omega_arith) hp₂ (by omega_arith) (by omega_arith)) fun s₃ ⟨f₃, o₃, k₃⟩ => ?_)
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  obtain hp₃ : s₃.gpr .ebp = s₃.gpr .edi + BitVec.ofNat 32 (VTAB + 384 * j) := by
    rw [k₃.1 _ (by decide), k₃.1 .edi (by decide), hp₂]
  -- `Z`.
  refine WP.block_append_iff.mpr (WP.mono (toEntry_ok hs₃ (o := 256) (a := slot (2 : Index).val)
    (by have := sl 2; omega_arith) hp₃ (by omega_arith) (by omega_arith)) fun s₄ ⟨f₄, o₄, k₄⟩ => ?_)
  -- The next entry.
  refine wp_alu (Or.inl rfl) rfl fun s₅ u₅ _ => wp_cmp rfl fun t ft zt => WP.block_nil ?_
  obtain g11 : s₅.gpr .esi = BitVec.ofNat 32 (VTAB + 384 * (j + 1)) := by
    rw [u₅.gpr]; change s₄.gpr .esi + (384 : BitVec 32) = _
    rw [k₄.1 _ (by decide), k₃.1 _ (by decide), k₂.1 _ (by decide), u₁.other _ (by decide),
      u₀.other _ (by decide), h11]
    exact nf.1
  -- The limbs stored, from the slots, which the stores keep.
  obtain src : ∀ (i : Index) {m m' : Mem} {q : Nat}, Outside base q 112 m m' → 4096 ≤ q → ∀ k < 28,
      limbs m' base (slot i.val) k = limbs m base (slot i.val) k := fun i _ _ _ ho hq k hk =>
    ho.limbs (Or.inl (by have := sl i; omega_using [hq, this])) (by have := sl i; omega_using [this]) hk
  obtain lx : ∀ k < 28, limbs s₄.mem base (VTAB + 384 * j) k = limbs s.mem base (slot (0 : Index).val) k :=
    fun k hk => by
      rw [o₄.limbs (Or.inl (by omega_arith)) (by omega_arith) hk, o₃.limbs (Or.inl (by omega_arith)) (by omega_arith) hk,
        ← Nat.add_zero (VTAB + 384 * j), f₂ k hk, m₁]
  obtain ly : ∀ k < 28, limbs s₄.mem base (VTAB + 384 * j + 128) k = limbs s.mem base (slot (1 : Index).val) k :=
    fun k hk => by
      rw [o₄.limbs (Or.inl (by omega_arith)) (by omega_arith) hk, f₃ k hk, src 1 o₂ (by omega_arith) k hk, m₁]
  obtain lz : ∀ k < 28, limbs s₄.mem base (VTAB + 384 * j + 256) k = limbs s.mem base (slot (2 : Index).val) k :=
    fun k hk => by
      rw [f₄ k hk, src 2 o₃ (by omega_arith) k hk, src 2 o₂ (by omega_arith) k hk, m₁]
  obtain mt : t.mem = s₄.mem := by rw [ft.mem, u₅.mem]
  refine ⟨?_, ?_, ?_, by rw [ft.gpr, g11], ?_⟩
  · exact k01.trans ((k₂.mono (by decide)).trans ((k₃.mono (by decide)).trans ((k₄.mono (by decide)).trans
      ((u₅.rest (by decide)).trans (ft.rest _)))))
  · rw [mt, ← m₁]
    exact (o₂.mono (by omega_arith) (by omega_arith)).trans ((o₃.mono (by omega_arith) (by omega_arith)).trans
      (o₄.mono (by omega_arith) (by omega_arith)))
  · rw [mt]
    exact ⟨fun k hk => by rw [lx k hk]; exact hb 0 k hk, fun k hk => by rw [ly k hk]; exact hb 1 k hk,
      fun k hk => by rw [lz k hk]; exact hb 2 k hk, congrArg Proof.X448.toFe (valN_congr lx),
      congrArg Proof.X448.toFe (valN_congr ly), congrArg Proof.X448.toFe (valN_congr lz)⟩
  · rw [zt, g11]
    exact congrArg some nf.2

/-- The address of the entry of an odd digit, less `VTAB - 192`: 192 times the digit. -/
theorem entry_addr_fact : ∀ d < 16,
    (BitVec.ofNat 32 d).rotateRight 26 + ((BitVec.ofNat 32 d).rotateRight 26).rotateRight 31 =
      BitVec.ofNat 32 (192 * d) := by decide

/-- The entry of the odd digit in `ecx` into slots 6, 7 and 21. -/
theorem ventryLoad_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) {d : Nat}
    (hd : d < 16) (hodd : d % 2 = 1) (h3 : s.gpr .ecx = BitVec.ofNat 32 d) {p : Spec.Ed448.Point}
    (he : EntryOk base s.mem ((d - 1) / 2) p) :
    WP isa (.block ventryLoad) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧
      E t.mem base = Function.update (Function.update (Function.update (E s.mem base) 6 p.X) 7 p.Y) 21 p.Z := by
  have hT : VTAB = 5120 := rfl
  obtain ⟨j, hj⟩ : ∃ j, (d - 1) / 2 = j := ⟨_, rfl⟩
  obtain hj8 : j < 8 := by omega_using [hd, hj]
  obtain hdj : 192 * d = 192 + 384 * j := by omega_using [hodd, hj]
  obtain af := entry_addr_fact d hd
  rw [hj] at he
  rw [ventryLoad, ventryAddr, List.append_assoc, List.append_assoc, List.cons_append, List.cons_append,
    List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_shift (by decide) fun s₁ u₁ => wp_mov rfl fun s₂ u₂ => wp_shift (by decide) fun s₃ u₃ =>
    wp_alu (Or.inl rfl) rfl fun s₄ u₄ _ => wp_alu (Or.inl rfl) rfl fun s₅ u₅ _ => ?_
  obtain r5 : Keeps workRegs s s₅ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans
    ((u₃.rest (by decide)).trans ((u₄.rest (by decide)).trans (u₅.rest (by decide)))))
  obtain m5 : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain k5 : Keep base s s₅ := ⟨r5, by rw [m5]; exact WsOut2.refl _ _ _ _ _ _⟩
  obtain hs₅ := k5.scr hs
  obtain g1 : s₁.gpr .ecx = (BitVec.ofNat 32 d).rotateRight 26 := by rw [u₁.gpr, h3]
  obtain hp₅ : s₅.gpr .ebp = s₅.gpr .edi + BitVec.ofNat 32 (192 * d) := by
    rw [u₅.gpr, u₅.other .edi (by decide)]; change s₄.gpr .ebp + s₄.gpr .edi = _
    rw [u₄.gpr, u₄.other .edi (by decide)]; change s₃.gpr .ebp + s₃.gpr .ecx + s₃.gpr .edi = _
    rw [u₃.gpr, u₃.other .ebp (by decide), u₃.other .edi (by decide), u₂.gpr, u₂.other .ecx (by decide),
      u₂.other .edi (by decide), g1, af, BitVec.add_comm]
  obtain e0 : 192 * d + (VTAB - 192) = VTAB + 384 * j := by omega_using [hdj, hT]
  obtain e1 : 192 * d + (VTAB - 192 + 128) = VTAB + 384 * j + 128 := by omega_using [hdj, hT]
  obtain e2 : 192 * d + (VTAB - 192 + 256) = VTAB + 384 * j + 256 := by omega_using [hdj, hT]
  -- `X`.
  refine WP.block_append_iff.mpr (WP.mono (slotFrom_ok hs₅ (m5 ▸ hb) 6 (a := VTAB - 192) hp₅
    (by omega_using [e0, hT]) (by omega_using [e0, hT, hj8]) (by rw [e0, m5]; exact he.bx))
    fun s₆ ⟨k₆, k3₆, b₆, e₆⟩ => ?_)
  obtain hs₆ := k₆.scr hs₅
  obtain hp₆ : s₆.gpr .ebp = s₆.gpr .edi + BitVec.ofNat 32 (192 * d) := by
    rw [k3₆.1 _ (by decide), k3₆.1 .edi (by decide), hp₅]
  obtain t₆ : EntryOk base s₆.mem j p := (m5 ▸ he : EntryOk base s₅.mem j p).keep hj8 k₆.mem
  -- `Y`.
  refine WP.block_append_iff.mpr (WP.mono (slotFrom_ok hs₆ b₆ 7 (a := VTAB - 192 + 128) hp₆
    (by omega_using [e1, hT]) (by omega_using [e1, hT, hj8]) (by rw [e1]; exact t₆.by'))
    fun s₇ ⟨k₇, k3₇, b₇, e₇⟩ => ?_)
  obtain hs₇ := k₇.scr hs₆
  obtain hp₇ : s₇.gpr .ebp = s₇.gpr .edi + BitVec.ofNat 32 (192 * d) := by
    rw [k3₇.1 _ (by decide), k3₇.1 .edi (by decide), hp₆]
  obtain t₇ : EntryOk base s₇.mem j p := t₆.keep hj8 k₇.mem
  -- `Z`.
  refine WP.mono (slotFrom_ok hs₇ b₇ 21 (a := VTAB - 192 + 256) hp₇
    (by omega_using [e2, hT]) (by omega_using [e2, hT, hj8]) (by rw [e2]; exact t₇.bz))
    fun t ⟨kt, _, bt, et⟩ => ⟨k5.trans (k₆.trans (k₇.trans kt)), bt, ?_⟩
  rw [et, e₇, e₆, e2, e1, e0, t₇.z, t₆.y, m5, show F s.mem base (VTAB + 384 * j) = p.X from he.x]

/-! ## The frame -/

/-- The working space below `top`, outside the slots and the field functions' area, is kept:
what the field operations (`top = 8192`), the table's stores (`top = VTAB`) and the recoding of
the digits (`top = KBITS`) leave alone. -/
def WsBelow (base : Addr) (top : Nat) (m m' : Mem) : Prop :=
  ∀ p, ofs base p < top → (ofs base p < 64 ∨ 64 + 2816 ≤ ofs base p) →
    (ofs base p < ACC ∨ ACC + 512 ≤ ofs base p) → m' p = m p

theorem WsBelow.refl (base : Addr) (top : Nat) (m : Mem) : WsBelow base top m m := fun _ _ _ _ => rfl

theorem WsBelow.trans {base : Addr} {top : Nat} {m₁ m₂ m₃ : Mem} (h₁ : WsBelow base top m₁ m₂)
    (h₂ : WsBelow base top m₂ m₃) : WsBelow base top m₁ m₃ :=
  fun p h1 h2 h3 => (h₂ p h1 h2 h3).trans (h₁ p h1 h2 h3)

theorem WsBelow.mono {base : Addr} {top top' : Nat} {m m' : Mem} (h : WsBelow base top m m')
    (ht : top' ≤ top) : WsBelow base top' m m' := fun p h1 h2 h3 => h p (Nat.lt_of_lt_of_le h1 ht) h2 h3

/-- The field operations. -/
theorem WsBelow.of_keep {base : Addr} {top : Nat} {m m' : Mem} (h : WsOut2 base 64 2816 ACC 512 m m')
    (ht : top ≤ 8192) : WsBelow base top m m' := fun p h1 h2 h3 => h p (Nat.lt_of_lt_of_le h1 ht) h2 h3

/-- A store at or above `top`. -/
theorem WsBelow.of_out {base : Addr} {top o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    (ho : top ≤ o) : WsBelow base top m m' := fun p h1 _ _ => h p (Or.inl (Nat.lt_of_lt_of_le h1 ho))

theorem WsBelow.word {base : Addr} {top : Nat} {m m' : Mem} (h : WsBelow base top m m') (ht : top ≤ 8192)
    {d : Nat} (hd : d + 4 ≤ top) (hx : d + 4 ≤ 64 ∨ 2880 ≤ d) (hy : d + 4 ≤ ACC ∨ ACC + 512 ≤ d) :
    word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega_using [hd, ht, hi])]; omega_using [hd, hi])
    (by rw [ofs_off base (by omega_using [hd, ht, hi])]; omega_using [hx, hi])
    (by rw [ofs_off base (by omega_using [hd, ht, hi])]; omega_using [hy, hi])).symm).symm

/-- A byte of the digits, below the table. -/
theorem WsBelow.digit {base : Addr} {top : Nat} {m m' : Mem} (h : WsBelow base top m m') (ht : KBITS + 456 ≤ top)
    {q : Nat} (hq : q < 456) : m' (off base (KBITS + q)) = m (off base (KBITS + q)) := by
  have hK : KBITS = 4608 := rfl
  have hA : ACC = 3584 := rfl
  exact h _ (by rw [ofs_off' base (by omega_using [hq, hK])]; omega_using [hq, ht])
    (by rw [ofs_off' base (by omega_using [hq, hK])]; omega_using [hK])
    (by rw [ofs_off' base (by omega_using [hq, hK])]; omega_using [hK, hA])

/-- A field element at `RX` or `RY`, between the field arithmetic's working space and the
digits. -/
theorem F_below {base : Addr} {top : Nat} {m m' : Mem} (h : WsBelow base top m m') (h1 : KBITS ≤ top)
    (h2 : top ≤ 8192) {o : Nat} (ho : o = RX ∨ o = RY) :
    F m' base o = F m base o ∧ (Bounded m base o → Bounded m' base o) := by
  have hK : KBITS = 4608 := rfl
  have hA : ACC = 3584 := rfl
  obtain l : ∀ j < 28, limbs m' base o j = limbs m base o j := fun j hj =>
    congrArg BitVec.toNat (h.word h2 (by rcases ho with rfl | rfl <;> simp only [RX, RY] <;> omega_using [h1, hK, hj])
      (Or.inr (by rcases ho with rfl | rfl <;> simp only [RX, RY] <;> omega_arith))
      (Or.inr (by rcases ho with rfl | rfl <;> simp only [RX, RY] <;> omega_using [hA])))
  exact ⟨congrArg Proof.X448.toFe (valN_congr l), fun hb j hj => by rw [l j hj]; exact hb j hj⟩

/-! ## Its entries -/

/-- The table before entry `j`: the entries below it, `Q` the one before, and `[2]A` in slots 6, 7
and 21. -/
structure TabAt (base : Addr) (A : Spec.Ed448.Point) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base
  ctx : CallCtx s base
  bounded : BoundedEnv s.mem base
  regs : Keeps (.esi :: workRegs) s₀ s
  mem : WsBelow base VTAB s₀.mem s.mem
  esi : s.gpr .esi = BitVec.ofNat 32 (VTAB + 384 * j)
  q : pt (E s.mem base) 0 1 2 = oddMul A (j - 1)
  two : pt (E s.mem base) 6 7 21 = double A
  one : E s.mem base 10 = 1
  d : E s.mem base 11 = Spec.Ed448.d
  tab : ∀ i < j, EntryOk base s.mem i (oddMul A i)

/-- The slots after a store above them. -/
theorem slots_out {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (ho : 2880 ≤ o) :
    E m' base = E m base ∧ (BoundedEnv m base → BoundedEnv m' base) := by
  obtain w : ∀ i : Index, ∀ k < 28, limbs m' base (slot i.val) k = limbs m base (slot i.val) k :=
    fun i k hk => by
      have := slot_range i
      exact h.limbs (Or.inl (by omega_using [this, ho])) (by omega_using [this]) hk
  exact ⟨funext fun i => congrArg Proof.X448.toFe (valN_congr (w i)),
    fun hb i k hk => by rw [w i k hk]; exact hb i k hk⟩

theorem vtableInit_ok {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base)
    (hb : BoundedEnv s.mem base) (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) :
    WP isa vtableInit s fun t => TabAt base (pt (E s.mem base) 6 7 10) s t 1 := by
  have hT : VTAB = 5120 := rfl
  rw [vtableInit, tableQF_impl]
  refine WP.seq (WP.mono (ops_ok hs hc hb tableQF) fun s₁ ⟨k₁, b₁, e₁⟩ => ?_)
  obtain hs₁ := k₁.scr hs
  obtain hc₁ := k₁.ctx hc
  obtain q₁ : pt (E s₁.mem base) 0 1 2 = pt (E s.mem base) 6 7 10 := by rw [e₁]; rfl
  obtain a₁ : pt (E s₁.mem base) 6 7 21 = pt (E s.mem base) 6 7 10 := by rw [e₁]; rfl
  obtain o₁ : ∀ i : Index, i.val = 10 ∨ i.val = 11 → E s₁.mem base i = E s.mem base i := fun i hi => by
    rw [e₁]
    refine applyOps_keep _ _ ?_
    revert i; decide
  -- The first entry.
  refine WP.seq (wp_mov rfl fun s₂ u₂ => ?_)
  obtain k₂ : Keeps (.esi :: workRegs) s₁ s₂ := u₂.rest (by decide)
  refine WP.mono (ventryStore_ok (hs₁.of_keeps k₂ (by decide)) (u₂.mem ▸ b₁) (j := 0) (by decide)
    (by rw [u₂.gpr]; rfl)) fun s₃ ⟨k₃, o₃, t₃, g₃, _⟩ => ?_
  obtain k13 : Keeps (.esi :: workRegs) s₁ s₃ := k₂.trans (k₃.mono (by decide))
  obtain hs₃ := hs₁.of_keeps k13 (by decide)
  obtain hc₃ : CallCtx s₃ base := hc₁.keep (k13.1 _ (by decide))
  obtain ⟨e₃, b₃⟩ := slots_out o₃ (by omega_using [hT])
  rw [u₂.mem] at e₃ b₃
  rw [u₂.mem, q₁] at t₃
  -- `[2]A`.
  rw [field, doubleF6_impl]
  refine WP.mono (ops_ok hs₃ hc₃ (b₃ b₁) (doubleF 6 7 21)) fun t ⟨kt, bt, et⟩ => ?_
  obtain kp : ∀ i : Index, i.val < 6 ∨ (8 ≤ i.val ∧ i.val < 12) ∨ i.val = 20 →
      E t.mem base i = E s₁.mem base i := fun i hi => by
    rw [et, doubleF_keep6 _ _ hi, e₃]
  refine ⟨kt.scr hs₃, kt.ctx hc₃, bt,
    (k₁.regs.mono (fun _ h => List.mem_cons_of_mem _ h)).trans (k13.trans (kt.regs.mono (fun _ h => List.mem_cons_of_mem _ h))),
    ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · refine (WsBelow.of_keep k₁.mem (by decide)).trans (WsBelow.trans ?_ (WsBelow.of_keep kt.mem (by decide)))
    rw [← u₂.mem]
    exact WsBelow.of_out o₃ (by omega_arith)
  · rw [kt.regs.1 _ (by decide), g₃]
  · rw [pt_congr' (kp 0 (by decide)) (kp 1 (by decide)) (kp 2 (by decide)), q₁]; rfl
  · rw [et, doubleF_eval6, e₃, a₁]
  · rw [kp 10 (by decide), o₁ 10 (by decide), h10]
  · rw [kp 11 (by decide), o₁ 11 (by decide), h11]
  · obtain rfl : i = 0 := by omega_using [hi]
    exact t₃.keep (by decide) kt.mem

theorem vtableStep_ok {s₀ s : State} {base : Addr} {A : Spec.Ed448.Point} {j : Nat} (h : TabAt base A s₀ s j)
    (h1 : 1 ≤ j) (h8 : j < 8) :
    WP isa vtableStep s fun t => TabAt base A s₀ t (j + 1) ∧ t.zf = some (decide (j + 1 = 8)) := by
  have hT : VTAB = 5120 := rfl
  rw [vtableStep, addTake6_impl]
  refine WP.seq (WP.mono (ops_ok h.scr h.ctx h.bounded (addF 6 7 21 ++ takeF)) fun s₁ ⟨k₁, b₁, e₁⟩ => ?_)
  obtain hs₁ := k₁.scr h.scr
  obtain kp : ∀ i : Index, (6 ≤ i.val ∧ i.val < 12) ∨ i.val = 21 → E s₁.mem base i = E s.mem base i :=
    fun i hi => by rw [e₁, addTake_keep _ _ _ _ _ hi]
  obtain q₁ : pt (E s₁.mem base) 0 1 2 = oddMul A j := by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega_using [h1]⟩
    rw [e₁, addTake_pt6, h.d, h.q, h.two]
    rfl
  refine WP.mono (ventryStore_ok hs₁ b₁ h8 (by rw [k₁.regs.1 _ (by decide), h.esi]))
    fun t ⟨kt, ot, tt, gt, zt⟩ => ?_
  obtain ⟨et, bt⟩ := slots_out ot (by omega_using [hT])
  rw [q₁] at tt
  refine ⟨⟨hs₁.of_keeps kt (by decide), (k₁.ctx h.ctx).keep (kt.1 _ (by decide)), bt b₁,
    h.regs.trans ((k₁.regs.mono (fun _ h => List.mem_cons_of_mem _ h)).trans (kt.mono (by decide))),
    h.mem.trans ((WsBelow.of_keep k₁.mem (by decide)).trans (WsBelow.of_out ot (by omega_arith))), gt,
    by rw [et, Nat.add_sub_cancel]; exact q₁,
    by rw [et, pt_congr' (kp 6 (by decide)) (kp 7 (by decide)) (kp 21 (by decide))]; exact h.two,
    by rw [et, kp 10 (by decide)]; exact h.one, by rw [et, kp 11 (by decide)]; exact h.d, fun i hi => ?_⟩, zt⟩
  rcases Nat.lt_or_ge i j with hij | hij
  · exact ((h.tab i hij).keep (by omega_using [hij, h8]) k₁.mem).other (by omega_using [hij, h8])
      (by omega_using [hij]) ot
  · obtain rfl : i = j := by omega_using [hi, hij]
    exact tt

/-- What `vtable` leaves, from the state `s` before it: the table of the odd multiples of the
point that was in slots 6, 7 and 10, and `Q` the neutral point. -/
structure Tabled (base : Addr) (s t : State) : Prop where
  scr : Scr t base
  ctx : CallCtx t base
  bounded : BoundedEnv t.mem base
  regs : Keeps (.esi :: workRegs) s t
  mem : WsBelow base VTAB s.mem t.mem
  tab : TabOk base (pt (E s.mem base) 6 7 10) t.mem
  q : pt (E t.mem base) 0 1 2 = Spec.Ed448.identity
  one : E t.mem base 10 = 1
  d : E t.mem base 11 = Spec.Ed448.d

theorem vtable_ok {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base)
    (hb : BoundedEnv s.mem base) (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) :
    WP isa vtable s (Tabled base s) := by
  rw [vtable]
  refine WP.seq (WP.mono (vtableInit_ok hs hc hb h10 h11) fun s₁ a₁ => ?_)
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := fun t => TabAt base (pt (E s.mem base) 6 7 10) s t 8)
    (fun n t => 0 < n ∧ n ≤ 7 ∧ TabAt base (pt (E s.mem base) 6 7 10) s t (8 - n)) ?_ 7 s₁
    ⟨by decide, Nat.le_refl _, (show (8 : Nat) - 7 = 1 from rfl) ▸ a₁⟩) fun s₂ a₂ => ?_)
  · intro n x ⟨n0, n7, ax⟩
    refine WP.mono (vtableStep_ok ax (by omega_using [n7]) (by omega_using [n0])) fun t ⟨at', zt⟩ => ?_
    by_cases hn : n = 1
    · subst hn
      exact .inl ⟨by rw [evalNe zt]; rfl, at'⟩
    · refine .inr ⟨by rw [evalNe zt, decide_eq_false (by omega_using [hn, n0])]; rfl, n - 1,
        by omega_using [n0], by omega_using [hn, n0], by omega_using [n7], ?_⟩
      rw [show 8 - (n - 1) = 8 - n + 1 by omega_using [n0, n7]]
      exact at'
  · rw [neutralF_impl]
    refine WP.mono (ops_ok a₂.scr a₂.ctx a₂.bounded neutralF) fun t ⟨kt, bt, et⟩ => ?_
    obtain kp : ∀ i : Index, i.val = 10 ∨ i.val = 11 → E t.mem base i = E s₂.mem base i := fun i hi => by
      rw [et]
      refine applyOps_keep _ _ ?_
      revert i; decide
    refine ⟨kt.scr a₂.scr, kt.ctx a₂.ctx, bt, a₂.regs.trans (kt.regs.mono (fun _ h => List.mem_cons_of_mem _ h)),
      a₂.mem.trans (WsBelow.of_keep kt.mem (by decide)),
      fun j hj => (a₂.tab j hj).keep hj kt.mem, ?_, by rw [kp 10 (by decide)]; exact a₂.one,
      by rw [kp 11 (by decide)]; exact a₂.d⟩
    show (⟨E t.mem base 0, E t.mem base 1, E t.mem base 2⟩ : Spec.Ed448.Point) = ⟨0, 1, 1⟩
    rw [et]
    show (⟨E s₂.mem base 0 - E s₂.mem base 0, E s₂.mem base 10, E s₂.mem base 10⟩ : Spec.Ed448.Point) = _
    rw [Fin.sub_self, a₂.one]

end VG.Proof.Ed448.X86

end

end


/-!
# Ed448 verification's equation on x86 (32-bit): `[S]B + [k](-A)`

One iteration of `vloop` (`vstep_ok`), for bit `t` (byte `t` at `BITS` is the bit of `S`, and
byte `t` at `KBITS` digit `t` of `k`): `Q` (slots 0–2) doubled; in the comb's rows, `t < 114`,
the table's entry of the row's four bits of `S` (base-point multiplication's `combDigit_ok` and
`combSelect_ok`) added (`vcombIf_ok`); and, if the digit is not zero (`vdigit_ok`), its entry of
`-A`'s table loaded into slots 6, 7 and 21 (`ventryLoad_ok`) and added (`vaddIf_ok`). The loop's
invariant (`VInv`): `Q` is the reference computation's point after the digits above `n`
(`Proof.Ed448.vcomb`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448 VG.Impl.Ed448.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (double vcomb vcombStep vcomb_bit combDigit_lt oddMul vdigits pt addWith)
open VG.Impl.X448.X86 (BITS slot ACC at_)

/-! ## The values -/

/-- The slots after the point `p` is put in slots 6, 7 and 21 and added, made if `nz`. -/
def entEnv (p : Spec.Ed448.Point) : Bool → Env → Env
  | true, e => applyOps (addF 6 7 21 ++ takeF)
      (Function.update (Function.update (Function.update e 6 p.X) 7 p.Y) 21 p.Z)
  | false, e => e

/-- The slots after the comb's entry `i` is selected and added, in a row of the comb. -/
def combEnv (i : Nat) : Bool → Env → Env
  | true, e => applyOps (addF 8 9 10 ++ takeF) (selEnv i e)
  | false, e => e

/-- The slots after an iteration: in a row of the comb (`row`), of index `i`, and for the entry
`p` of a digit of `k` that is not zero (`nz`). -/
def vstepEnv (row : Bool) (i : Nat) (nz : Bool) (p : Spec.Ed448.Point) (e : Env) : Env :=
  entEnv p nz (combEnv i row (applyOps (doubleF 0 1 2) e))

/-- The addition of the digit's entry keeps 1 and `d`. -/
theorem entEnv_keep (p : Spec.Ed448.Point) (nz : Bool) (e : Env) (i : Index) (hi : 8 ≤ i.val ∧ i.val < 12) :
    entEnv p nz e i = e i := by
  cases nz
  · rfl
  · rw [entEnv, addTake_keep _ _ _ _ _ (Or.inl (by omega_using [hi])),
      Function.update_of_ne (fun h => by subst h; omega_arith),
      Function.update_of_ne (fun h => by subst h; omega_arith),
      Function.update_of_ne (fun h => by subst h; omega_arith)]

/-- The comb's addition keeps 1 and `d`. -/
theorem combEnv_keep (i : Nat) (row : Bool) (e : Env) (j : Index) (hj : j.val = 10 ∨ j.val = 11) :
    combEnv i row e j = e j := by
  cases row
  · rfl
  · have h8 : j ≠ 8 := fun h => by subst h; omega_arith
    have h9 : j ≠ 9 := fun h => by subst h; omega_arith
    rw [combEnv, addTake_keep _ _ _ _ _ (Or.inl (by omega_using [hj])), selEnv,
      Function.update_of_ne h9, Function.update_of_ne h8]

theorem combEnv_pt (i : Nat) (row : Bool) (e : Env) :
    pt (combEnv i row e) 0 1 2 =
      if row then addWith (e 11) (pt e 0 1 2) ⟨(Impl.Ed448.Comb.entry i).1, (Impl.Ed448.Comb.entry i).2, e 10⟩
      else pt e 0 1 2 := by
  cases row <;> rfl

theorem entEnv_pt (p : Spec.Ed448.Point) (nz : Bool) (e : Env) :
    pt (entEnv p nz e) 0 1 2 = if nz then addWith (e 11) (pt e 0 1 2) p else pt e 0 1 2 := by
  cases nz <;> rfl

theorem vstepEnv_pt (row : Bool) (i : Nat) (nz : Bool) (p : Spec.Ed448.Point) (e : Env) :
    pt (vstepEnv row i nz p e) 0 1 2 =
      let r₁ := double (pt e 0 1 2)
      let r₂ := if row then
        addWith (e 11) r₁ ⟨(Impl.Ed448.Comb.entry i).1, (Impl.Ed448.Comb.entry i).2, e 10⟩ else r₁
      if nz then addWith (e 11) r₂ p else r₂ := by
  unfold vstepEnv
  generalize he0 : applyOps (doubleF 0 1 2) e = e0
  obtain p0 : pt e0 0 1 2 = double (pt e 0 1 2) := by rw [← he0, doubleF_eval0]
  obtain k0 : ∀ i : Index, 3 ≤ i.val ∧ i.val < 12 → e0 i = e i := fun i hi => by
    rw [← he0, doubleF_keep0 _ _ (Or.inl hi)]
  generalize he1 : combEnv i row e0 = e1
  obtain p1 : pt e1 0 1 2 = if row then
      addWith (e0 11) (pt e0 0 1 2) ⟨(Impl.Ed448.Comb.entry i).1, (Impl.Ed448.Comb.entry i).2, e0 10⟩
      else pt e0 0 1 2 := by
    rw [← he1, combEnv_pt]
  obtain e11 : e1 11 = e 11 := by rw [← he1, combEnv_keep _ _ _ _ (Or.inr rfl), k0 11 (by decide)]
  rw [entEnv_pt, p1, e11, k0 11 (by decide), k0 10 (by decide), p0]

theorem vstepEnv_keep (row : Bool) (i : Nat) (nz : Bool) (p : Spec.Ed448.Point) (e : Env) (j : Index)
    (hj : j.val = 10 ∨ j.val = 11) : vstepEnv row i nz p e j = e j := by
  rw [vstepEnv, entEnv_keep _ _ _ _ (by omega_using [hj]), combEnv_keep _ _ _ _ hj,
    doubleF_keep0 _ _ (Or.inl (by omega_using [hj]))]

/-- One bit: the reference computation's point after the digits above `t`, then after digit
`t`. -/
theorem vcomb_step {e : Env} {S K t : Nat} {A : Spec.Ed448.Point} (ht : t < 456)
    (hr : pt e 0 1 2 = vcomb S K A (456 - (t + 1))) (h1 : e 10 = 1) (hd : e 11 = Spec.Ed448.d) :
    pt (vstepEnv (decide (t < 114)) (Proof.Ed448.combDigit S t) (!decide (vdigits K t = 0))
      (oddMul A ((vdigits K t - 1) / 2)) e) 0 1 2 = vcomb S K A (456 - t) := by
  rw [vstepEnv_pt, hd, h1, hr, vcomb_bit S K A ht]
  by_cases hz : vdigits K t = 0 <;> by_cases hrow : t < 114 <;>
    simp only [vcombStep, hz, hrow, decide_true, decide_false, Bool.not_true, Bool.not_false, ↓reduceIte,
      Bool.false_eq_true] <;> rfl

/-! ## One iteration -/

/-- The bits of `S` at `BITS` and the digits of `K` at `KBITS`, one per byte. -/
def VDig (base : Addr) (S K : Nat) (m : Mem) : Prop :=
  ∀ t < 456, m (off base (BITS + t)) = BitVec.ofNat 8 ((S >>> t) &&& 1) ∧
    m (off base (KBITS + t)) = BitVec.ofNat 8 (vdigits K t)

/-- The field operations keep the bits and the digits. -/
theorem VDig.keep {base : Addr} {S K : Nat} {m m' : Mem} (hv : VDig base S K m)
    (h : WsOut2 base 64 2816 ACC 512 m m') : VDig base S K m' := fun t ht => by
  have hB : BITS = 3072 := rfl
  have hK : KBITS = 4608 := rfl
  have hA : ACC = 3584 := rfl
  refine ⟨?_, ?_⟩
  · rw [h _ (by rw [ofs_off' base (by omega_arith)]; omega_arith) (by rw [ofs_off' base (by omega_arith)]; omega_arith)
      (by rw [ofs_off' base (by omega_arith)]; omega_arith)]
    exact (hv t ht).1
  · rw [h _ (by rw [ofs_off' base (by omega_arith)]; omega_arith) (by rw [ofs_off' base (by omega_arith)]; omega_arith)
      (by rw [ofs_off' base (by omega_arith)]; omega_arith)]
    exact (hv t ht).2

/-- The table's stores keep the bits and the digits. -/
theorem VDig.below {base : Addr} {S K : Nat} {m m' : Mem} {top : Nat} (hv : VDig base S K m)
    (h : WsBelow base top m m') (ht : KBITS + 456 ≤ top) (ht' : top ≤ 8192) : VDig base S K m' := fun t ht'' => by
  have hB : BITS = 3072 := rfl
  have hK : KBITS = 4608 := rfl
  have hA : ACC = 3584 := rfl
  refine ⟨?_, ?_⟩
  · rw [h _ (by rw [ofs_off' base (by omega_arith)]; omega_arith) (by rw [ofs_off' base (by omega_arith)]; omega_arith)
      (by rw [ofs_off' base (by omega_arith)]; omega_arith)]
    exact (hv t ht'').1
  · rw [h.digit ht ht'']
    exact (hv t ht'').2

/-- `k`'s digits are below 16. -/
theorem vdigits_lt (K q : Nat) : vdigits K q < 16 := by
  show Proof.Ed25519.Slide.digits 456 K q < 16
  rcases Proof.Ed25519.Slide.digits_odd 456 K q with h | h <;> omega_using [h]

/-- A comparison's carry: the unsigned order of its operands. -/
theorem wp_cmpb {is : List Instr} {s : State} {Q : State → Prop} {r : Reg} {src : Src} {v : BitVec 32}
    (h : readSrc s src = some v)
    (k : ∀ t, Fupd s t → t.cf = some (decide ((s.gpr r).toNat < v.toNat)) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .cmp r src :: is)) s Q :=
  WP.cons (t := arithFlags s (s.gpr r - v) ((s.gpr r).toNat < v.toNat)
    (subOverflow (s.gpr r) v (s.gpr r - v)))
    (by simp only [reduceExec, execAlu, h, Option.bind_some]) (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl)

theorem vrowTest_ok (s : State) {n : Nat} (hn : n < 456) (hb : s.gpr .esi = BitVec.ofNat 32 n) :
    WP isa (.block vrowTest) s fun u => isa.eval .b u = some (decide (n < 114)) ∧ Fupd s u := by
  unfold vrowTest
  refine wp_cmpb rfl fun u fu hc => WP.block_nil ⟨?_, fu⟩
  change u.cf = _
  rw [hc, hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])]
  rfl

theorem keepF {base : Addr} {s t : State} (h : Fupd s t) : Keep base s t :=
  ⟨h.rest _, by rw [h.mem]; exact WsOut2.refl _ _ _ _ _ _⟩

/-- In the comb's rows, the entry of the row's bits of `S` added. -/
theorem vcombIf_ok {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base)
    (hbd : BoundedEnv s.mem base) {S n : Nat} (hn : n < 456) (hb : s.gpr .esi = BitVec.ofNat 32 n)
    (hbits : ∀ i < 456, s.mem (off base (BITS + i)) = BitVec.ofNat 8 ((S >>> i) &&& 1)) :
    WP isa vcombIf s fun u => Keep base s u ∧ BoundedEnv u.mem base ∧
      E u.mem base = combEnv (Proof.Ed448.combDigit S n) (decide (n < 114)) (E s.mem base) := by
  have hB : BITS = 3072 := rfl
  unfold vcombIf
  refine WP.seq (WP.mono (vrowTest_ok s hn hb) fun u ⟨uc, fu⟩ => ?_)
  obtain ku : Keep base s u := keepF fu
  obtain hsu := ku.scr hs
  refine WP.ite (decide (n < 114)) uc (fun hrow => ?_) (fun hno => ?_)
  · obtain hlt : n < 114 := of_decide_eq_true hrow
    refine WP.seq (WP.block_append_iff.mpr (WP.mono (combDigit_ok (k := S) hsu (by omega_using [hB]) hlt
      (by rw [congrFun fu.gpr]; exact hb) (by rw [fu.mem]; exact hbits)) fun v ⟨vd, vk, vm⟩ => ?_))
    obtain kv : Keep base u v := ⟨vk.mono (by decide), by rw [vm]; exact WsOut2.refl _ _ _ _ _ _⟩
    refine WP.mono (combSelect_ok (kv.scr hsu) (by rw [vm, fu.mem]; exact hbd) (combDigit_lt S n) vd)
      fun w ⟨kw, bw, ew⟩ => ?_
    obtain kw' := ku.trans (kv.trans kw)
    rw [addTake8_impl]
    refine WP.mono (ops_ok (kw'.scr hs) (kw'.ctx hc) bw (addF 8 9 10 ++ takeF)) fun x ⟨kx, bx, ex⟩ =>
      ⟨kw'.trans kx, bx, ?_⟩
    rw [ex, ew, vm, fu.mem, hrow]; rfl
  · refine WP.block_nil ⟨ku, fu.mem ▸ hbd, ?_⟩
    rw [fu.mem, hno]; rfl

/-- A digit of `k`, loaded: the digit, and the test of zero. -/
theorem digit_test : ∀ d < 16,
    (BitVec.ofNat 8 d).setWidth 32 = BitVec.ofNat 32 d ∧
    ((BitVec.ofNat 8 d).setWidth 32 - (0 : BitVec 32) == 0) = decide (d = 0) := by decide

theorem vdigit_ok {s : State} {base : Addr} (hs : Scr s base) {n d : Nat} (hn : n < 456) (hd : d < 16)
    (hb : s.gpr .esi = BitVec.ofNat 32 n) (hdig : s.mem (off base (KBITS + n)) = BitVec.ofNat 8 d) :
    WP isa (.block vdigit) s fun u => u.zf = some (decide (d = 0)) ∧ u.gpr .ecx = BitVec.ofNat 32 d ∧
      Keeps workRegs s u ∧ u.mem = s.mem := by
  have hK : KBITS = 4608 := rfl
  obtain dt := digit_test d hd
  unfold vdigit
  refine wp_mov rfl fun u1 v1 => wp_alu (Or.inl rfl) rfl fun u2 v2 _ => ?_
  obtain hs2 : Scr u2 base := (hs.of_upd v1 (by decide)).of_upd v2 (by decide)
  obtain p2 : u2.gpr .ebp = u2.gpr .edi + BitVec.ofNat 32 n := by
    rw [v2.gpr, v2.other .edi (by decide)]; change u1.gpr .ebp + u1.gpr .esi = _
    rw [v1.gpr, v1.other .esi (by decide), v1.other .edi (by decide), hb]
  refine wp_load8 (a := off base (n + KBITS)) (ptr_ea hs2 p2 (by omega_using [hn, hK]))
    (hs2.read (by omega_using [hn, hK])) fun u3 v3 => wp_cmp rfl fun u fu hz => WP.block_nil ?_
  obtain c3 : u3.gpr .ecx = (BitVec.ofNat 8 d).setWidth 32 := by
    rw [v3.gpr, v2.mem, v1.mem, Nat.add_comm n KBITS, hdig]
  refine ⟨by rw [hz, c3]; exact congrArg some dt.2, by rw [congrFun fu.gpr, c3]; exact dt.1, ?_,
    by rw [fu.mem, v3.mem, v2.mem, v1.mem]⟩
  exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans (fu.rest _)))

/-- The entry of digit `n` of `k`, `d`, added, if the digit is not zero. -/
theorem vaddIf_ok {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base)
    (hbd : BoundedEnv s.mem base) {n d : Nat} (hn : n < 456) (hd : d = 0 ∨ (d % 2 = 1 ∧ d < 16))
    (hb : s.gpr .esi = BitVec.ofNat 32 n) (hdig : s.mem (off base (KBITS + n)) = BitVec.ofNat 8 d)
    {p : Spec.Ed448.Point} (he : EntryOk base s.mem ((d - 1) / 2) p) :
    WP isa vaddIf s fun u => Keep base s u ∧ BoundedEnv u.mem base ∧
      E u.mem base = entEnv p (!decide (d = 0)) (E s.mem base) := by
  obtain hd16 : d < 16 := by rcases hd with h | h <;> omega_using [h]
  unfold vaddIf
  refine WP.seq (WP.mono (vdigit_ok hs hn hd16 hb hdig) fun u ⟨uz, u3, uk, um⟩ => ?_)
  obtain ku : Keep base s u := ⟨uk, by rw [um]; exact WsOut2.refl _ _ _ _ _ _⟩
  refine WP.ite (!decide (d = 0)) (evalNe uz) (fun hset => ?_) (fun hclr => ?_)
  · obtain hodd : d % 2 = 1 := by
      rcases hd with h | h
      · rw [decide_eq_true h] at hset; exact absurd hset (by decide)
      · exact h.1
    refine WP.seq (WP.mono (ventryLoad_ok (ku.scr hs) (um ▸ hbd) hd16 hodd u3 (um ▸ he))
      fun v ⟨kv, bv, ev⟩ => ?_)
    obtain kv' := ku.trans kv
    rw [addTake6_impl]
    refine WP.mono (ops_ok (kv'.scr hs) (kv'.ctx hc) bv (addF 6 7 21 ++ takeF)) fun w ⟨kw, bw, ew⟩ =>
      ⟨kv'.trans kw, bw, ?_⟩
    rw [ew, ev, um, hset]; rfl
  · refine WP.block_nil ⟨ku, um ▸ hbd, ?_⟩
    rw [um, hclr]; rfl

/-- The loop's invariant, after the bits of `S` and the digits of `k` above `n`, for the table
of the odd multiples of `A`. -/
structure VInv (base : Addr) (S K : Nat) (A : Spec.Ed448.Point) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  ctx : CallCtx s base
  bounded : BoundedEnv s.mem base
  regs : Keeps (.esi :: workRegs) s₀ s
  esi : s.gpr .esi = BitVec.ofNat 32 n
  mem : WsOut2 base 64 2816 ACC 512 s₀.mem s.mem
  rep : pt (E s.mem base) 0 1 2 = vcomb S K A (456 - n)
  one : E s.mem base 10 = 1
  d : E s.mem base 11 = Spec.Ed448.d

theorem vstep_ok {s₀ s : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point} {n : Nat} (hn : n < 456)
    (hbits : VDig base S K s₀.mem) (htab : TabOk base A s₀.mem)
    (hi : VInv base S K A s₀ s (n + 1)) :
    WP isa vstep s fun t => VInv base S K A s₀ t n ∧ t.zf = some (decide (n = 0)) := by
  have hs := hi.scr
  obtain hdn := Proof.Ed25519.Slide.digits_odd 456 K n
  obtain hj8 : (vdigits K n - 1) / 2 < 8 := by have := vdigits_lt K n; omega_using [this]
  unfold vstep
  refine WP.seq (WP.mono (decCounter_ok (by omega_using [hn]) hi.esi) fun s₁ ⟨b₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_)
  obtain K₁ : Keeps [.esi] s s₁ := ⟨fun r hr => g₁ r (fun h => hr (by simp [h])), rd₁, wr₁⟩
  obtain hs₁ := hs.of_keeps K₁ (by decide)
  obtain hc₁ : CallCtx s₁ base := hi.ctx.keep (g₁ _ (by decide))
  rw [field, doubleF0_impl]
  refine WP.seq (WP.mono (ops_ok hs₁ hc₁ (m₁ ▸ hi.bounded) (doubleF 0 1 2)) fun s₂ ⟨k₂, bb₂, e₂⟩ => ?_)
  obtain hs₂ := k₂.scr hs₁
  obtain dig₂ : VDig base S K s₂.mem := (m₁ ▸ hbits.keep hi.mem : VDig base S K s₁.mem).keep k₂.mem
  refine WP.seq (WP.mono (vcombIf_ok hs₂ (k₂.ctx hc₁) bb₂ hn (by rw [k₂.regs.1 _ (by decide), b₁])
    (fun i hi' => (dig₂ i hi').1)) fun s₃ ⟨k₃, bb₃, e₃⟩ => ?_)
  obtain hs₃ := k₃.scr hs₂
  obtain k13 := k₂.trans k₃
  obtain tab₃ : EntryOk base s₃.mem ((vdigits K n - 1) / 2) (oddMul A ((vdigits K n - 1) / 2)) := by
    have t₁ : EntryOk base s₁.mem ((vdigits K n - 1) / 2) (oddMul A ((vdigits K n - 1) / 2)) :=
      m₁ ▸ (htab _ hj8).keep hj8 hi.mem
    exact t₁.keep hj8 k13.mem
  refine WP.seq (WP.mono (vaddIf_ok hs₃ (k13.ctx hc₁) bb₃ hn hdn
    (by rw [k13.regs.1 _ (by decide), b₁]) ((dig₂.keep k₃.mem n hn).2) tab₃) fun s₄ ⟨k₄, bb₄, e₄⟩ => ?_)
  refine wp_cmp rfl fun t vt hz => WP.block_nil ?_
  obtain core := k13.trans (k₄.trans (keepF vt))
  obtain b₄ : s₄.gpr .esi = BitVec.ofNat 32 n := by
    rw [k₄.regs.1 _ (by decide), k13.regs.1 _ (by decide), b₁]
  obtain ee : E t.mem base = vstepEnv (decide (n < 114)) (Proof.Ed448.combDigit S n) (!decide (vdigits K n = 0))
      (oddMul A ((vdigits K n - 1) / 2)) (E s.mem base) := by
    rw [vt.mem, e₄, e₃, e₂, m₁]; rfl
  obtain kk : ∀ j : Index, j.val = 10 ∨ j.val = 11 → E t.mem base j = E s.mem base j := fun j h => by
    rw [ee, vstepEnv_keep _ _ _ _ _ _ h]
  refine ⟨⟨core.scr hs₁, core.ctx hc₁, vt.mem ▸ bb₄, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · refine hi.regs.trans ⟨fun r hr => ?_, core.regs.2.1.trans rd₁, core.regs.2.2.trans wr₁⟩
    rw [core.regs.1 r (fun h => hr (List.mem_cons_of_mem _ h)), g₁ r (fun h => hr (by simp [h]))]
  · rw [core.regs.1 _ (by decide), b₁]
  · refine hi.mem.trans ?_
    intro p h8 hp hq
    rw [core.mem p h8 hp hq, m₁]
  · rw [ee]; exact vcomb_step hn hi.rep hi.one hi.d
  · rw [kk 10 (by decide)]; exact hi.one
  · rw [kk 11 (by decide)]; exact hi.d
  · rw [hz, b₄, show BitVec.ofNat 32 n - (0 : BitVec 32) = BitVec.ofNat 32 n from BitVec.sub_zero _,
      ofNat_beq_zero (by omega_using [hn])]

theorem vloop_ok {s₀ s : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point}
    (hbits : VDig base S K s₀.mem) (htab : TabOk base A s₀.mem)
    (hi : ∀ s', s'.gpr .esi = BitVec.ofNat 32 456 → (∀ r, r ≠ .esi → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → VInv base S K A s₀ s' 456) :
    WP isa vloop s fun s' => VInv base S K A s₀ s' 0 := by
  unfold vloop
  refine WP.seq (WP.mono (setCounter_ok s 456 (by decide)) fun s' ⟨h1, h2, h3, h4, h5⟩ => ?_)
  refine WP.loop (M := isa) (body := vstep) (c := .ne) (Q := fun s' => VInv base S K A s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 456 ∧ VInv base S K A s₀ s m) ?_ 456 s'
    ⟨by decide, by decide, hi s' h1 h2 h3 h4 h5⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega_arith⟩
  refine WP.mono (vstep_ok (by omega_arith) hbits htab hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega_arith : ¬m = 0), Bool.not_false], m, by omega_arith,
      by omega_arith, by omega_arith, hi'⟩

end VG.Proof.Ed448.X86

end

end

/-! ### `Ed448.X86.VerifyDecodeLoop`, which only this module used -/

section

/-!
# Ed448 verification's equation on x86 (32-bit): `R` and `A` decoded by one loop

`vdecode` decodes `R` (the signature's first half) and then `A` (the public key) with one copy
of the decoding: the pointer to the point it decodes next and the decodings left are words of
the working space (`PCUR`, `CNT`), and each iteration first copies slots 6–7 to `RX` and `RY`,
so that `R`, decoded into slots 6–7 by the first iteration, is kept there while `A` is decoded
into them by the second. `DecInv` is the state after `2 - m` decodings, `m` the count.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448 VG.Impl.Ed448.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.Ed448 (RecoverOk)
open VG.Impl.X448.X86 (slot ACC at_ ld st sc copy)
open VG.Spec.Ed448 (bytesAt)

/-- What the loop writes: the slots, `BAD` and `SIGN` (from byte 16), and from `ACC` to `CNT`
(`R`'s place and the loop's pointer and count). -/
abbrev DFrame (base : Addr) (m m' : Mem) : Prop := WsOut2 base 16 2864 ACC 776 m m'

theorem DFrame.of_v {base : Addr} {m m' : Mem} (h : WsOut2 base 16 2864 ACC 512 m m') :
    DFrame base m m' :=
  fun p h8 h1 h2 => h p h8 h1 (by simp only [ACC] at h2 ⊢; omega_arith)

theorem DFrame.of_out {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (h1 : ACC ≤ o)
    (h2 : o + n ≤ ACC + 776) : DFrame base m m' :=
  fun p _ _ hq => h p (by simp only [ACC] at h1 h2 hq; omega_arith)

theorem DFrame.trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : DFrame base m₁ m₂) (h₂ : DFrame base m₂ m₃) :
    DFrame base m₁ m₃ := WsOut2.trans h₁ h₂

/-- What the code writes: the working space and the stack its calls use. -/
abbrev XF (base : Addr) (s : State) (m m' : Mem) : Prop := Frame [⟨base, 8192⟩, callStk s] m m'

theorem XF.of_out {base : Addr} {s : State} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    (ho : o + n ≤ 8192) : XF base s m m' :=
  (Outside.frame (n := 8192) (fun p hp => h p (Or.inr (Nat.le_trans ho (by
    rcases hp with hp | hp
    · exact absurd hp (Nat.not_lt_zero _)
    · simpa using hp))))).mono fun r hr => by
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_self

/-- The frame code calling the field functions leaves, with the working space the only writable region. -/
theorem XF.of_frame {base : Addr} {s : State} {n : Nat} {m m' : Mem} (hw : s.wr = [⟨base, 8192⟩])
    (hn : n ≤ 20) (hc : CallCtx s base) (h : Frame (s.wr ++ [below (s.gpr .esp) n]) m m') : XF base s m m' :=
  h.sub fun r hr => by
    rw [hw] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨callStk s, List.mem_cons_of_mem _ List.mem_cons_self, below_sub hn hc.sp⟩

/-- An input's bytes across writes to the working space and the call stack, apart from it. -/
theorem Input.bytesX {s : State} {base : Addr} {p : BitVec 32} {N : Nat} (h : Input s base p N)
    (hd : (⟨p.setWidth 64, N⟩ : Region).Disjoint (callStk s)) {m m' : Mem} (hm : XF base s m m') :
    bytesAt m' (p.setWidth 64) N = bytesAt m (p.setWidth 64) N := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => hm _ ?_
  simp only [List.mem_range] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl) hr
  · have := h.far i hi
    simp only [Region.Contains, ofs] at hr this; omega_arith
  · exact hd _ (Offset.contains_base _ (by omega_arith) (by have := h.fit; omega_arith)) hr

/-- A slot's value outside a range written. -/
theorem E_out {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (i : Index)
    (hi : slot i.val + 112 ≤ o ∨ o + n ≤ slot i.val) : E m' base i = E m base i := by
  simp only [E, F]
  rw [h.fe hi (by have := slot_range i; omega_arith)]

/-- Bounded slots outside a range written above them. -/
theorem BoundedEnv.out {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (ho : 2880 ≤ o)
    (hb : BoundedEnv m base) : BoundedEnv m' base := fun i j hj => by
  have := slot_range i
  rw [h.limbs (Or.inl (by omega_arith)) (by omega_arith) hj]
  exact hb i j hj

/-- One store, keeping the flags. -/
theorem storeZ_ok {s : State} {base : Addr} (hs : Scr s base) (r : Reg) {d : Nat} (hd : d + 4 ≤ 8192) :
    WP isa (.block [st r d]) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.gpr r) ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.zf = s.zf :=
  WP.cons (t := {s with mem := s.mem.writeW (off base d) (s.gpr r)})
    (by simp only [st, exec, hs.ea (by omega_arith : d < 8192), State.store32, hs.write hd, ite_true])
    (WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-- The argument at `[esp + d]`, `p`, in any later state with the same stack pointer and
regions and the memory outside the working space unchanged. -/
def ArgAt (s : State) (base : Addr) (d : Nat) (p : BitVec 32) : Prop :=
  ∀ t : State, t.gpr .esp = s.gpr .esp → t.rd = s.rd → t.wr = s.wr → XF base s s.mem t.mem →
    ∃ a, t.ea (at_ .esp d) = a ∧ InRegions (t.rd ++ t.wr) a 4 ∧ t.mem.readW a 32 = p

theorem ArgAt.of {s u : State} {base : Addr} {d : Nat} {p : BitVec 32} (h : ArgAt s base d p) {rs : List Reg}
    (hk : Keeps rs s u) (hesp : .esp ∉ rs) (ho : XF base s s.mem u.mem) : ArgAt u base d p := by
  intro t h1 h2 h3 h4
  obtain e : callStk u = callStk s := by simp only [callStk, hk.1 _ hesp]
  change Frame [⟨base, 8192⟩, callStk u] _ _ at h4
  rw [e] at h4
  exact h t (h1.trans (hk.1 _ hesp)) (h2.trans hk.2.1) (h3.trans hk.2.2) (ho.trans h4)

/-- `decodePoint` of the 57 bytes at `p`. -/
abbrev decAt (m : Mem) (p : BitVec 32) : Option Spec.Ed448.Point :=
  Spec.Ed448.decodePoint (bytesAt m (p.setWidth 64) 57)

/-- After `2 - m` of the decodings, from the state `s` before the loop: `R`'s decoding (at `sig`)
in slots 6–7 after the first, then at `RX` and `RY` with `A`'s (at `pk`) in slots 6–7. -/
structure DecInv (base : Addr) (s : State) (sig pk : BitVec 32) (m : Nat) (t : State) : Prop where
  le : m ≤ 2
  keeps : Keeps (.esi :: workRegs) s t
  frame : DFrame base s.mem t.mem
  ext : XF base s s.mem t.mem
  bounded : BoundedEnv t.mem base
  cnt : word t.mem base CNT = BitVec.ofNat 32 m
  ptr : 1 ≤ m → word t.mem base PCUR = if m = 2 then sig else pk
  other : ∀ i : Index, i ≠ 6 → i ≠ 7 → (i.val = 0 ∨ i.val = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 11)) →
    E t.mem base i = E s.mem base i
  bad : BadUpd ((m ≤ 1 → (decAt s.mem sig).isSome) ∧ (m = 0 → (decAt s.mem pk).isSome))
    (word s.mem base BAD) (word t.mem base BAD)
  rIn : m = 1 → ∀ r, decAt s.mem sig = some r → E t.mem base 6 = r.X ∧ E t.mem base 7 = r.Y ∧ r.Z = 1
  rOut : m = 0 → ∀ r, decAt s.mem sig = some r → F t.mem base RX = r.X ∧ F t.mem base RY = r.Y ∧ r.Z = 1
  rBnd : m = 0 → Bounded t.mem base RX ∧ Bounded t.mem base RY
  aIn : m = 0 → ∀ a, decAt s.mem pk = some a → E t.mem base 6 = a.X ∧ E t.mem base 7 = a.Y ∧ a.Z = 1

theorem DecInv.scr {base : Addr} {s t : State} {sig pk : BitVec 32} {m : Nat} (h : DecInv base s sig pk m t)
    (hs : Scr s base) : Scr t base := hs.of_keeps h.keeps (by decide)

/-- The loop's pointer at `R`, and its count 2. -/
theorem vdecodeInit_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {sig pk : BitVec 32} (hsig : ArgAt s base 8 sig) :
    WP isa (.block vdecodeInit) s (DecInv base s sig pk 2) := by
  unfold vdecodeInit
  obtain ⟨a, ae, ar, av⟩ := hsig s rfl rfl rfl (Frame.refl _ _)
  refine wp_load ae ar fun u1 h1 => ?_
  rw [av] at h1
  obtain hs1 := hs.of_upd h1 (by decide)
  refine store_ok hs1 (o := PCUR) (by decide) fun u2 h2 => ?_
  obtain hs2 := hs1.of_keeps (h2.rest []) (by decide)
  refine wp_mov (v := 2) rfl fun u3 h3 => ?_
  obtain hs3 := hs2.of_upd h3 (by decide)
  refine store_ok hs3 (o := CNT) (by decide) fun t ht => WP.block_nil ?_
  obtain mt : t.mem = (s.mem.writeW (off base PCUR) sig).writeW (off base CNT) (2 : BitVec 32) := by
    rw [ht.mem, h3.gpr, h3.mem, h2.mem, h1.gpr, h1.mem]
  obtain out : Outside base PCUR 8 s.mem t.mem := by
    rw [mt]
    exact ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide))
  obtain bt : word t.mem base BAD = word s.mem base BAD := out.word (Or.inl (by decide)) (by decide)
  refine ⟨by decide, ((h1.rest (by decide)).trans (h2.rest _)).trans ((h3.rest (by decide)).trans (ht.rest _)),
    DFrame.of_out out (by decide) (by decide), XF.of_out out (by decide), BoundedEnv.out out (by decide) hb,
    ?_, fun _ => ?_,
    fun i _ _ _ => E_out out i (Or.inl (by have := slot_range i; simp only [PCUR]; omega_arith)),
    (BadUpd.rfl'.congr ⟨fun _ => ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩,
      fun _ => trivial⟩).of_eq bt, fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  · rw [mt, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_left rfl]
    rfl
  · rw [mt, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide),
      word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_left rfl, ite_eq_left rfl]

/-- What the first block of an iteration does: slots 6–7 copied to `RX` and `RY`, and `esi`
loaded from `PCUR`. -/
def AFacts (base : Addr) (t u : State) : Prop :=
  u.gpr .esi = word t.mem base PCUR ∧ Keeps (.esi :: workRegs) t u ∧ Outside base RX 256 t.mem u.mem ∧
    (∀ i < 28, limbs u.mem base RX i = limbs t.mem base (slot 6) i) ∧
    (∀ i < 28, limbs u.mem base RY i = limbs t.mem base (slot 7) i)

theorem vbodyA_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block vbodyA) s (AFacts base s) := by
  rw [vbodyA, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy_ok hs (o := RX) (a := slot 6) (by decide) (by decide) (Or.inr (Or.inr (by decide))))
    fun s1 ⟨f1, o1, k1⟩ => ?_
  obtain hs1 := hs.of_keeps k1 (by decide)
  refine WP.mono (copy_ok hs1 (o := RY) (a := slot 7) (by decide) (by decide) (Or.inr (Or.inr (by decide))))
    fun s2 ⟨f2, o2, k2⟩ => ?_
  obtain hs2 := hs1.of_keeps k2 (by decide)
  refine load_ok hs2 (o := PCUR) (by decide) fun t ht => WP.block_nil ⟨?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [ht.gpr, o2.word (Or.inr (by decide)) (by decide), o1.word (Or.inr (by decide)) (by decide)]
  · refine ((k1.mono ?_).trans (k2.mono ?_)).trans (ht.rest (by decide)) <;> intro r hr <;> revert r <;> decide
  · rw [ht.mem]
    exact (o1.mono (by decide) (by decide)).trans (o2.mono (by decide) (by decide))
  · rw [ht.mem, o2.limbs (Or.inl (by decide)) (by decide) hi, f1 i hi]
  · rw [ht.mem, f2 i hi, o1.limbs (Or.inl (by decide)) (by decide) hi]

/-- A decoding of the point at `esi` into slots 6–7, then `vnext`. -/
theorem vdecodeRest_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hcc : CallCtx s base)
    (hw : s.wr = [⟨base, 8192⟩]) (hb : BoundedEnv s.mem base) {p pk : BitVec 32} (hp : s.gpr .esi = p) (hin : Input s base p 57)
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) (hpk : ArgAt s base 4 pk)
    {c : Nat} (hc2 : c < 2) (hc : word s.mem base CNT = BitVec.ofNat 32 (c + 1)) :
    WP isa (.seq (decode 6 7) (.block vnext)) s fun t =>
      Keeps (.esi :: workRegs) s t ∧ DFrame base s.mem t.mem ∧ XF base s s.mem t.mem ∧
      BoundedEnv t.mem base ∧ BadUpd (decAt s.mem p).isSome (word s.mem base BAD) (word t.mem base BAD) ∧
      (∀ a, decAt s.mem p = some a → E t.mem base 6 = a.X ∧ E t.mem base 7 = a.Y ∧ a.Z = 1) ∧
      (∀ i : Index, i ≠ 6 → i ≠ 7 → (i.val = 0 ∨ i.val = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 11)) →
        E t.mem base i = E s.mem base i) ∧
      (∀ i < 28, limbs t.mem base RX i = limbs s.mem base RX i) ∧
      (∀ i < 28, limbs t.mem base RY i = limbs s.mem base RY i) ∧
      word t.mem base PCUR = pk ∧ word t.mem base CNT = BitVec.ofNat 32 c ∧ t.zf = some (decide (c = 0)) := by
  refine WP.seq (WP.mono (WP.withFrame (NoSp.of_all (by lit_decide))
    (Nat.le_trans (by lit_decide : stackUse (decode 6 7) ≤ 20) hcc.sp)
    (decode_ok hR hs hcc hb hp hin.fit hin.read hin.far 6 7 (Or.inl ⟨rfl, rfl⟩) h10 h11))
    fun w ⟨⟨kw, bw, cw, vw, ew⟩, fw⟩ => ?_)
  obtain xw : XF base s s.mem w.mem := XF.of_frame hw (by lit_decide) hcc fw
  obtain hsw := kw.scr hs
  obtain ⟨a, ae, ar, av⟩ := hpk w (kw.regs.1 _ (by decide)) kw.regs.2.1 kw.regs.2.2 xw
  unfold vnext
  refine wp_load ae ar fun w1 g1 => ?_
  rw [av] at g1
  obtain hs1 := hsw.of_upd g1 (by decide)
  refine store_ok hs1 (o := PCUR) (by decide) fun w2 g2 => ?_
  obtain hs2 := hs1.of_keeps (g2.rest []) (by decide)
  refine load_ok hs2 (o := CNT) (by decide) fun w3 g3 => ?_
  obtain hs3 := hs2.of_upd g3 (by decide)
  refine wp_alu (op := .sub) (v := 1) (Or.inr (Or.inl rfl)) rfl fun w4 g4 z4 => ?_
  obtain hs4 := hs3.of_upd g4 (by decide)
  refine WP.mono (storeZ_ok hs4 .ebx (d := CNT) (by decide)) fun t ⟨mt, gt, rdt, wrt, zt⟩ => ?_
  obtain c3 : w3.gpr .ebx = BitVec.ofNat 32 (c + 1) := by
    rw [g3.gpr, g2.mem, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_right (by decide), g1.mem, kw.mem.word (Or.inr (by decide)) (Or.inr (by decide)) (by decide), hc]
  obtain c4 : w4.gpr .ebx = BitVec.ofNat 32 c := by
    rw [g4.gpr]
    show w3.gpr .ebx - 1 = _
    rw [c3]
    rcases (by omega_arith : c = 0 ∨ c = 1) with rfl | rfl <;> rfl
  obtain mt' : t.mem = (w.mem.writeW (off base PCUR) pk).writeW (off base CNT) (BitVec.ofNat 32 c) := by
    rw [mt, c4, g4.mem, g3.mem, g2.mem, g1.gpr, g1.mem]
  obtain out : Outside base PCUR 8 w.mem t.mem := by
    rw [mt']
    exact ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide))
  obtain wl : ∀ o, ACC + 512 ≤ o → o + 112 ≤ PCUR → ∀ i < 28, limbs t.mem base o i = limbs s.mem base o i :=
    fun o h1 h2 i hi => by
      rw [out.limbs (Or.inl h2) (by simp only [PCUR] at h2; omega_arith) hi]
      exact congrArg BitVec.toNat (kw.mem.word (Or.inr (by simp only [ACC] at h1; omega_arith))
        (Or.inr (by omega_arith)) (by simp only [PCUR] at h2; omega_arith))
  refine ⟨?_, (DFrame.of_v kw.mem).trans (DFrame.of_out out (by decide) (by decide)),
    xw.trans (XF.of_out out (by decide)), BoundedEnv.out out (by decide) bw, cw.of_eq (out.word (Or.inl (by decide)) (by decide)), fun a ha => ?_,
    fun i h6 h7 hi => ?_, wl RX (by decide) (by decide), wl RY (by decide) (by decide), ?_, ?_, ?_⟩
  · refine kw.regs.trans (((g1.rest (by decide)).trans (g2.rest _)).trans (((g3.rest (by decide)).trans
      (g4.rest (by decide))).trans ⟨fun r _ => by rw [gt], rdt, wrt⟩))
  · obtain ⟨x, y, z⟩ := vw a ha
    exact ⟨by rw [E_out out 6 (Or.inl (by decide))]; exact x, by rw [E_out out 7 (Or.inl (by decide))]; exact y, z⟩
  · rw [E_out out i (Or.inl (by have := slot_range i; simp only [PCUR]; omega_arith)), ew i h6 h7 (by omega_arith)]
  · rw [mt', word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide),
      word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_left rfl]
  · rw [mt', word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_left rfl]
  · rw [zt, z4]
    show some (w3.gpr .ebx - 1 == 0) = _
    rw [c3]
    rcases (by omega_arith : c = 0 ∨ c = 1) with rfl | rfl <;> rfl

/-- `Input` of the first 57 bytes. -/
theorem Input.take57 {s : State} {base : Addr} {p : BitVec 32} {N : Nat} (h : Input s base p N) (hN : 57 ≤ N) :
    Input s base p 57 :=
  ⟨by have := h.fit; omega_arith, fun i hi => h.read i (by omega_arith), fun i hi => h.far i (by omega_arith)⟩

/-- An iteration's second part, after `vbodyA_ok`: from `m` decodings left to `m - 1`. -/
theorem vbodyB_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hcc : CallCtx s base)
    (hw : s.wr = [⟨base, 8192⟩]) {sig pk : BitVec 32}
    (hpk : ArgAt s base 4 pk) (isig : Input s base sig 57) (ipk : Input s base pk 57)
    (dsig : (⟨sig.setWidth 64, 57⟩ : Region).Disjoint (callStk s))
    (dpk : (⟨pk.setWidth 64, 57⟩ : Region).Disjoint (callStk s))
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) {m : Nat} (hm : 1 ≤ m)
    {t u : State} (ht : DecInv base s sig pk m t) (hA : AFacts base t u) :
    WP isa (.seq (decode 6 7) (.block vnext)) u fun v =>
      DecInv base s sig pk (m - 1) v ∧ v.zf = some (decide (m - 1 = 0)) := by
  obtain ⟨ae, ak, ao, arx, ary⟩ := hA
  obtain hst := ht.scr hs
  obtain kt := ht.keeps.trans ak
  obtain hsu := hs.of_keeps kt (by decide)
  obtain Ou : XF base s s.mem u.mem := ht.ext.trans (XF.of_out ao (by decide))
  obtain stku : callStk u = callStk s := by simp only [callStk, kt.1 _ (by decide : Reg.esp ∉ _)]
  obtain DAu : DFrame base t.mem u.mem := DFrame.of_out ao (by decide) (by decide)
  obtain Eu : ∀ i : Index, E u.mem base i = E t.mem base i := fun i =>
    E_out ao i (Or.inl (by have := slot_range i; simp only [RX]; omega_arith))
  obtain bu : BoundedEnv u.mem base := BoundedEnv.out ao (by decide) ht.bounded
  obtain badu : word u.mem base BAD = word t.mem base BAD := ao.word (Or.inl (by decide)) (by decide)
  obtain h10u : E u.mem base 10 = 1 := by rw [Eu, ht.other 10 (by decide) (by decide) (by decide), h10]
  obtain h11u : E u.mem base 11 = Spec.Ed448.d := by rw [Eu, ht.other 11 (by decide) (by decide) (by decide), h11]
  obtain hc : word u.mem base CNT = BitVec.ofNat 32 (m - 1 + 1) := by
    rw [ao.word (Or.inr (by decide)) (by decide), ht.cnt, Nat.sub_add_cancel hm]
  obtain hp : u.gpr .esi = (if m = 2 then sig else pk) := ae.trans (ht.ptr hm)
  obtain hin : Input u base (if m = 2 then sig else pk) 57 := by
    split
    · exact isig.of_keeps kt
    · exact ipk.of_keeps kt
  obtain dec : decAt u.mem (if m = 2 then sig else pk) = decAt s.mem (if m = 2 then sig else pk) := by
    split
    · exact congrArg Spec.Ed448.decodePoint (isig.bytesX dsig Ou)
    · exact congrArg Spec.Ed448.decodePoint (ipk.bytesX dpk Ou)
  refine WP.mono (vdecodeRest_ok hR hsu (hcc.keep (kt.1 _ (by decide))) (kt.2.2.trans hw) bu hp hin h10u h11u
    (hpk.of kt (by decide) Ou) (c := m - 1)
    (by have := ht.le; omega_arith) hc) fun v ⟨kv, Dv, Xv, bv, cv, vv, ev, xv, yv, pv, nv, zv⟩ => ?_
  rw [dec] at cv vv
  change Frame [⟨base, 8192⟩, callStk u] _ _ at Xv
  rw [stku] at Xv
  refine ⟨⟨by have := ht.le; omega_arith, kt.trans kv, (ht.frame.trans DAu).trans Dv, Ou.trans Xv, bv, nv, fun h => ?_,
    fun i h6 h7 hi => by rw [ev i h6 h7 hi, Eu, ht.other i h6 h7 hi], ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun h => ?_⟩, zv⟩
  · have : m = 2 := by have := ht.le; omega_arith
    subst this
    rw [pv]; rfl
  · rw [badu] at cv
    refine (ht.bad.trans cv).congr ?_
    rcases (by have := ht.le; omega_arith : m = 1 ∨ m = 2) with rfl | rfl
    · exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨fun _ => h1 (by decide), fun _ => h2⟩,
        fun ⟨h1, h2⟩ => ⟨⟨fun _ => h1 (by decide), fun h => absurd h (by decide)⟩, h2 rfl⟩⟩
    · exact ⟨fun ⟨_, h2⟩ => ⟨fun _ => h2, fun h => absurd h (by decide)⟩,
        fun ⟨h1, _⟩ => ⟨⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩, h1 (by decide)⟩⟩
  · have : m = 2 := by omega_arith
    subst this
    exact vv
  · have : m = 1 := by omega_arith
    subst this
    intro r hr
    obtain ⟨x, y, z⟩ := ht.rIn rfl r hr
    refine ⟨?_, ?_, z⟩
    · show Proof.X448.toFe (fe v.mem base RX) = r.X
      rw [← x]
      exact congrArg Proof.X448.toFe (valN_congr fun i hi => (xv i hi).trans (arx i hi))
    · show Proof.X448.toFe (fe v.mem base RY) = r.Y
      rw [← y]
      exact congrArg Proof.X448.toFe (valN_congr fun i hi => (yv i hi).trans (ary i hi))
  · have : m = 1 := by omega_arith
    subst this
    exact ⟨fun i hi => by rw [xv i hi, arx i hi]; exact ht.bounded 6 i hi,
      fun i hi => by rw [yv i hi, ary i hi]; exact ht.bounded 7 i hi⟩
  · have : m = 1 := by omega_arith
    subst this
    exact vv

/-- One iteration, from `m` decodings left to `m - 1`. -/
theorem vdecodeStep_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hcc : CallCtx s base)
    (hw : s.wr = [⟨base, 8192⟩]) {sig pk : BitVec 32}
    (hpk : ArgAt s base 4 pk) (isig : Input s base sig 57) (ipk : Input s base pk 57)
    (dsig : (⟨sig.setWidth 64, 57⟩ : Region).Disjoint (callStk s))
    (dpk : (⟨pk.setWidth 64, 57⟩ : Region).Disjoint (callStk s))
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) {m : Nat} (hm : 1 ≤ m)
    {t : State} (ht : DecInv base s sig pk m t) :
    WP isa vdecodeBody t fun v => DecInv base s sig pk (m - 1) v ∧ v.zf = some (decide (m - 1 = 0)) := by
  rw [vdecodeBody]
  exact WP.seq (WP.mono (vbodyA_ok (ht.scr hs)) fun u hA =>
    vbodyB_ok hR hs hcc hw hpk isig ipk dsig dpk h10 h11 hm ht hA)

/-- `R` (at `sig`) decoded and kept at `RX` and `RY`, then `A` (at `pk`) into slots 6–7. -/
theorem vdecode_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hcc : CallCtx s base)
    (hw : s.wr = [⟨base, 8192⟩]) (hb : BoundedEnv s.mem base)
    {sig pk : BitVec 32} (hsig : ArgAt s base 8 sig) (hpk : ArgAt s base 4 pk) (isig : Input s base sig 57)
    (ipk : Input s base pk 57) (dsig : (⟨sig.setWidth 64, 57⟩ : Region).Disjoint (callStk s))
    (dpk : (⟨pk.setWidth 64, 57⟩ : Region).Disjoint (callStk s)) (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) :
    WP isa vdecode s (DecInv base s sig pk 0) := by
  rw [vdecode]
  refine WP.seq (WP.mono (vdecodeInit_ok hs hb (pk := pk) hsig) fun t ht => ?_)
  refine WP.loop (M := isa) (fun n (t : State) => 1 ≤ n ∧ DecInv base s sig pk n t) ?_ 2 t ⟨by decide, ht⟩
  intro n u ⟨hn, hu⟩
  refine WP.mono (vdecodeStep_ok hR hs hcc hw hpk isig ipk dsig dpk h10 h11 hn hu) fun v ⟨hv, zv⟩ => ?_
  rcases (by have := hu.le; omega_arith : n = 1 ∨ n = 2) with rfl | rfl
  · exact .inl ⟨by show v.zf.map (!·) = _; rw [zv]; rfl, hv⟩
  · exact .inr ⟨by show v.zf.map (!·) = _; rw [zv]; rfl, 1, by decide, by decide, hv⟩

/-- `R` copied into slots 8 and 9. -/
theorem vR_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (hx : Bounded s.mem base RX) (hy : Bounded s.mem base RY) :
    WP isa (.block vR) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base 8 = F s.mem base RX ∧
      E t.mem base 9 = F s.mem base RY ∧ (∀ i : Index, i ≠ 8 → i ≠ 9 → E t.mem base i = E s.mem base i) := by
  rw [vR, WP.block_append_iff]
  refine WP.mono (copy_ok hs (o := slot 8) (a := RX) (by decide) (by decide) (Or.inr (Or.inl (by decide))))
    fun s1 ⟨f1, o1, k1⟩ => ?_
  obtain hs1 := hs.of_keeps k1 (by decide)
  refine WP.mono (copy_ok hs1 (o := slot 9) (a := RY) (by decide) (by decide) (Or.inr (Or.inl (by decide))))
    fun t ⟨f2, o2, k2⟩ => ?_
  obtain O : Outside base 64 2816 s.mem t.mem := (o1.mono (by decide) (by decide)).trans (o2.mono (by decide) (by decide))
  obtain l8 : ∀ j < 28, limbs t.mem base (slot 8) j = limbs s.mem base RX j := fun j hj => by
    rw [o2.limbs (Or.inl (by decide)) (by decide) hj, f1 j hj]
  obtain l9 : ∀ j < 28, limbs t.mem base (slot 9) j = limbs s.mem base RY j := fun j hj => by
    rw [f2 j hj, o1.limbs (Or.inr (by decide)) (by decide) hj]
  obtain lo : ∀ i : Index, i ≠ 8 → i ≠ 9 → ∀ j < 28, limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j :=
    fun i h8 h9 j hj => by
      have := slot_range i
      rw [o2.limbs (slot_sep (j := 9) h9) (by omega_arith) hj, o1.limbs (slot_sep (j := 8) h8) (by omega_arith) hj]
  refine ⟨⟨(k1.mono ?_).trans (k2.mono ?_), fun p _ hp _ => O p hp⟩, fun i j hj => ?_, ?_, ?_,
    fun i h8 h9 => ?_⟩
  · intro r hr; revert r; decide
  · intro r hr; revert r; decide
  · by_cases h8 : i = 8
    · subst h8; exact (l8 j hj) ▸ hx j hj
    · by_cases h9 : i = 9
      · subst h9; exact (l9 j hj) ▸ hy j hj
      · rw [lo i h8 h9 j hj]; exact hb i j hj
  · simp only [E, F]
    exact congrArg Proof.X448.toFe (valN_congr l8)
  · simp only [E, F]
    exact congrArg Proof.X448.toFe (valN_congr l9)
  · simp only [E, F]
    exact congrArg Proof.X448.toFe (valN_congr (lo i h8 h9))

/-- A field element at `RX` or `RY`, through the field arithmetic (which writes below them). -/
theorem F_high {base : Addr} {x nx : Nat} {m m' : Mem} (h : WsOut2 base x nx ACC 512 m m') (hx : x + nx ≤ 4096)
    {o : Nat} (ho : o = RX ∨ o = RY) : F m' base o = F m base o ∧ (Bounded m base o → Bounded m' base o) := by
  obtain l : ∀ j < 28, limbs m' base o j = limbs m base o j := fun j hj =>
    congrArg BitVec.toNat (h.word (Or.inr (by rcases ho with rfl | rfl <;> simp only [RX, RY] <;> omega_arith))
      (Or.inr (by rcases ho with rfl | rfl <;> simp only [RX, RY, ACC] <;> omega_arith))
      (by rcases ho with rfl | rfl <;> simp only [RX, RY] <;> omega_arith))
  exact ⟨congrArg Proof.X448.toFe (valN_congr l), fun hb j hj => by rw [l j hj]; exact hb j hj⟩

end VG.Proof.Ed448.X86

end

end


/-!
# Ed448 verification's equation on x86 (32-bit): the whole function

`vg_ed448_verify_equation(pk = [esp + 4], signature = [esp + 8],
challenge = [esp + 12], scratch = [esp + 16])` returns `verifyEquation` of
its inputs (`verifyEquation_main`), given the reference computations'
agreement with the specification (`RecoverOk`, `VerifyEqCombOk`): the entry (the
registers saved, the bits of `S` and `k`, the check of `S`, the slots), `R`
and `A` decoded by one loop, `A` negated, `k`'s digits and the table of `-A`'s
odd multiples, `Q = [S]B + [k](-A)` by the loop,
`R` copied back, and the comparison of `[4]Q` and `[4]R`. Every write is in the working space, so the
arguments and the inputs are read unchanged; the callee-saved registers are
restored from the working space, and the return address is kept.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448 VG.Impl.Ed448.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.Ed448 (RecoverOk VerifyEqCombOk vcomb negPoint double verifyEquation_none pt evalOps)
open VG.Impl.X448.X86 (slot X2 BITS ACC TMP at_ ops)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-! ## The precondition and the arguments -/

/-- The precondition of `vg_ed448_verify_equation`, by name. -/
structure VerifyPre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 0).setWidth 64, 57⟩, ⟨(arg s 1).setWidth 64, 114⟩, ⟨(arg s 2).setWidth 64, 57⟩,
    ⟨argAddr s 0, 16⟩]
  wr : s.wr = [scR (arg s 3)]
  pk_sc : (⟨(arg s 0).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 3))
  sig_sc : (⟨(arg s 1).setWidth 64, 114⟩ : Region).Disjoint (scR (arg s 3))
  ch_sc : (⟨(arg s 2).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 3))
  args_sc : (⟨argAddr s 0, 16⟩ : Region).Disjoint (scR (arg s 3))
  ret_sc : (retR s).Disjoint (scR (arg s 3))
  f0 : (arg s 0).toNat + 57 ≤ 2 ^ 32
  f1 : (arg s 1).toNat + 114 ≤ 2 ^ 32
  f2 : (arg s 2).toNat + 57 ≤ 2 ^ 32
  f3 : (arg s 3).toNat + 8192 ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  sp_room : 20 ≤ (s.gpr .esp).toNat
  stk_pk : (stkR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  stk_sig : (stkR s).Disjoint ⟨(arg s 1).setWidth 64, 114⟩
  stk_ch : (stkR s).Disjoint ⟨(arg s 2).setWidth 64, 57⟩
  stk_sc : (stkR s).Disjoint (scR (arg s 3))

theorem VerifyPre.of {s : State} (h : verifyEquationLocal.pre s) : VerifyPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem VerifyPre.stk_args {s : State} (h : VerifyPre s) : (stkR s).Disjoint ⟨argAddr s 0, 16⟩ := by
  have h1 := h.sp_room
  have h2 := h.sp_fit
  refine Region.disjoint_of_le (Or.inl ?_) ?_ ?_ <;> simp only [argAddr] <;> bv_omega

theorem VerifyPre.stk_ret {s : State} (h : VerifyPre s) : (stkR s).Disjoint (retR s) := by
  have h1 := h.sp_room
  have h2 := h.sp_fit
  refine Region.disjoint_of_le (Or.inl ?_) ?_ ?_ <;> bv_omega

theorem VerifyPre.args {s : State} (h : VerifyPre s) : Args s 4 3 :=
  ⟨by rw [h.rd]; simp, by have := h.sp_fit; omega_arith, by decide, by rw [h.wr]; simp, h.f3,
    h.args_sc, h.ret_sc⟩

/-- An argument's address, readable, and its value, in a later state. -/
theorem Args.argRead {s₀ s : State} {n sc : Nat} (hp : Args s₀ n sc) (hsp : s.gpr .esp = s₀.gpr .esp)
    (hr : s.rd = s₀.rd) (hw : s.wr = s₀.wr) (hm : Outside ((arg s₀ sc).setWidth 64) 0 8192 s₀.mem s.mem)
    {i : Nat} (hi : i < n) :
    s.ea (at_ .esp (4 + 4 * i)) = addr (s₀.gpr .esp) (4 + 4 * i) ∧
      InRegions (s.rd ++ s.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 ∧
      s.mem.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  ⟨by change addr (s.gpr .esp) (4 + 4 * i) = _; rw [hsp],
    by rw [hr, hw]; exact ⟨_, List.mem_append_left _ hp.in_rd, hp.arg_contains hi⟩,
    hp.arg_same hm.frame hi⟩

/-- `argRead`, with the memory changed only in regions apart from the arguments. -/
theorem Args.argReadF {s₀ s : State} {n sc : Nat} (hp : Args s₀ n sc) (hsp : s.gpr .esp = s₀.gpr .esp)
    (hr : s.rd = s₀.rd) (hw : s.wr = s₀.wr) {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, (⟨argAddr s₀ 0, 4 * n⟩ : Region).Disjoint r) {i : Nat} (hi : i < n) :
    s.ea (at_ .esp (4 + 4 * i)) = addr (s₀.gpr .esp) (4 + 4 * i) ∧
      InRegions (s.rd ++ s.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 ∧
      s.mem.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  ⟨by change addr (s.gpr .esp) (4 + 4 * i) = _; rw [hsp],
    by rw [hr, hw]; exact ⟨_, List.mem_append_left _ hp.in_rd, hp.arg_contains hi⟩,
    hp.arg_frame hf hd hi⟩

/-! ## The bytes of the inputs -/

theorem bytesAt_take57 (m : Mem) (p : Addr) : (bytesAt m p 114).take 57 = bytesAt m p 57 := by
  simp [bytesAt, ← List.map_take, List.take_range]

theorem bytesAt_drop57 (m : Mem) (p : Addr) :
    (bytesAt m p 114).drop 57 = bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  refine List.ext_getElem (by simp [bytesAt]) fun i _ _ => ?_
  simp only [bytesAt, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [Offset.add_add]

theorem bytesAt114_len (m : Mem) (p : Addr) : (bytesAt m p 114).length = 57 + 57 := by
  simp [bytesAt]

theorem VBits.kept {base : Addr} {S K : Nat} {m m' : Mem} (h : WsOut2 base 16 2864 ACC 512 m m')
    (hv : VBits base S K m) : VBits base S K m' := fun t ht => by
  have hB : BITS = 3072 := rfl
  have hK : KBITS = 4608 := rfl
  have hA : ACC = 3584 := rfl
  refine ⟨?_, ?_⟩
  · rw [h _ (by rw [ofs_off' base (by omega_arith)]; omega_arith) (by rw [ofs_off' base (by omega_arith)]; omega_arith)
      (by rw [ofs_off' base (by omega_arith)]; omega_arith)]
    exact (hv t ht).1
  · rw [h _ (by rw [ofs_off' base (by omega_arith)]; omega_arith) (by rw [ofs_off' base (by omega_arith)]; omega_arith)
      (by rw [ofs_off' base (by omega_arith)]; omega_arith)]
    exact (hv t ht).2

theorem VBits.keptD {base : Addr} {S K : Nat} {m m' : Mem} (h : DFrame base m m')
    (hv : VBits base S K m) : VBits base S K m' := fun t ht => by
  have hB : BITS = 3072 := rfl
  have hK : KBITS = 4608 := rfl
  have hA : ACC = 3584 := rfl
  refine ⟨?_, ?_⟩
  · rw [h _ (by rw [ofs_off' base (by omega_arith)]; omega_arith) (by rw [ofs_off' base (by omega_arith)]; omega_arith)
      (by rw [ofs_off' base (by omega_arith)]; omega_arith)]
    exact (hv t ht).1
  · rw [h _ (by rw [ofs_off' base (by omega_arith)]; omega_arith) (by rw [ofs_off' base (by omega_arith)]; omega_arith)
      (by rw [ofs_off' base (by omega_arith)]; omega_arith)]
    exact (hv t ht).2

/-- The checks of the decodings, in the order the result uses. -/
theorem decShape {S R A : Prop} : (S ∧ ((0 ≤ 1 → R) ∧ (0 = 0 → A))) ↔ ((S ∧ A) ∧ R) :=
  ⟨fun ⟨hs, hr, ha⟩ => ⟨⟨hs, ha rfl⟩, hr (by decide)⟩, fun ⟨⟨hs, ha⟩, hr⟩ => ⟨hs, fun _ => hr, fun _ => ha⟩⟩

/-! ## The entry -/

theorem ventry_ok {s₀ : State} (h : VerifyPre s₀) {base : Addr} (hbase : (arg s₀ 3).setWidth 64 = base) :
    WP isa ventry s₀ fun t =>
      Scr t base ∧ Saved base s₀.gpr t.mem ∧ Outside base 0 8192 s₀.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s₀ t ∧
      BadUpd (decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57) < Spec.Ed448.L)
        0 (word t.mem base BAD) ∧
      VBits base (decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57))
        (decodeLE (bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 57)) t.mem ∧
      BoundedEnv t.mem base ∧ (∀ i : Index, E t.mem base i = Proof.X448.toFe (initVal i.val)) := by
  have hA := h.args
  obtain isig : Input s₀ base (arg s₀ 1) 114 := Input.of_region h.f1 (by rw [h.rd]; simp) (hbase ▸ h.sig_sc)
  obtain ich : Input s₀ base (arg s₀ 2) 57 := Input.of_region h.f2 (by rw [h.rd]; simp) (hbase ▸ h.ch_sc)
  unfold ventry
  -- The registers saved.
  refine WP.seq (WP.mono (save_ok hA) fun s₁ ⟨hs₁, sv₁, o₁, k₁⟩ => ?_)
  rw [hbase] at hs₁ sv₁ o₁
  obtain o1w : Outside base 0 8192 s₀.mem s₁.mem := o₁.mono (by omega_arith) (by omega_arith)
  -- The bits.
  obtain ⟨e8, r8, v8⟩ := hA.argRead (k₁.1 _ (by decide)) k₁.2.1 k₁.2.2 (hbase ▸ o1w) (i := 1) (by decide)
  obtain ⟨e12, r12, v12⟩ := hA.argRead (k₁.1 _ (by decide)) k₁.2.1 k₁.2.2 (hbase ▸ o1w) (i := 2) (by decide)
  obtain rr1 : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [k₁.2.1, k₁.2.2]
  refine WP.seq (WP.mono (vbits_ok hs₁ e8 r8 e12 r12 v8 v12 h.f1 h.f2
    (fun i hi => by rw [rr1, Offset.add_add]; exact isig.read _ (by omega_arith))
    (fun i hi => by rw [rr1]; exact ich.read i hi)
    (fun i hi => by rw [Offset.add_add]; exact isig.far _ (by omega_arith)) ich.far)
    fun s₂ ⟨esi₂, k₂, ⟨mK, oK, oS⟩, b₂⟩ => ?_)
  have hB : BITS = 3072 := rfl
  have hK : KBITS = 4608 := rfl
  obtain o12 : Outside base 0 8192 s₁.mem s₂.mem :=
    (oK.mono (by omega_arith) (by omega_arith)).trans (oS.mono (by omega_arith) (by omega_arith))
  unfold vinit
  refine WP.seq ?_
  simp only [List.cons_append, List.nil_append]
  obtain bs : bytesAt s₁.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57 =
      bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57 := by
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => o1w _ (Or.inr ?_)
    simp only [List.mem_range] at hi
    rw [Offset.add_add]; exact isig.far _ (by omega_arith)
  rw [bs, ich.bytes o1w] at b₂
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  -- `BAD = 0`.
  refine wp_mov rfl fun s₃ v₃ => store_ok (hs₂.of_upd v₃ (by decide)) (by decide) fun s₄ v₄ => ?_
  obtain hs₄ := (hs₂.of_upd v₃ (by decide)).of_keeps (v₄.rest []) (by decide)
  obtain bad₄ : word s₄.mem base BAD = 0 := by
    rw [v₄.mem, v₃.gpr]; exact Mem.readW_writeW_self32 _ _ _
  obtain o₄ : Outside base BAD 4 s₂.mem s₄.mem := by
    rw [v₄.mem, v₃.mem]; exact writeW_outside _ _ _ (by decide)
  -- The check of `S`.
  obtain esi₄ : s₄.gpr .esi = arg s₀ 1 := by rw [v₄.gpr, v₃.other _ (by decide), esi₂]
  obtain rr4 : s₄.rd ++ s₄.wr = s₀.rd ++ s₀.wr := by rw [v₄.rd, v₄.wr, v₃.rd, v₃.wr, k₂.2.1, k₂.2.2, rr1]
  obtain o04 : Outside base 0 8192 s₀.mem s₄.mem :=
    (o1w.trans o12).trans (o₄.mono (by omega_arith) (by decide))
  refine WP.mono (sCheck_ok hs₄ (q := (arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) (by rw [esi₄])
    (by rw [esi₄]; exact h.f1) (fun j hj => by rw [rr4, Offset.add_add]; exact isig.read _ (by omega_arith))
    (fun j hj => by rw [Offset.add_add]; exact isig.far _ (by omega_arith))) fun s₅ ⟨c₅, o₅, k₅⟩ => ?_
  obtain bS : bytesAt s₄.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57 =
      bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57 := by
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => o04 _ (Or.inr ?_)
    simp only [List.mem_range] at hi
    rw [Offset.add_add]; exact isig.far _ (by omega_arith)
  rw [bS, bad₄] at c₅
  obtain hs₅ := hs₄.of_keeps k₅ (by decide)
  -- The slots.
  refine WP.mono (initSlots_ok hs₅) fun t ⟨lt, ot, kt⟩ => ?_
  obtain e : ∀ i : Index, E t.mem base i = Proof.X448.toFe (initVal i.val) := initSlots_E lt
  refine ⟨hs₅.of_keeps kt (by decide), ?_, ?_, ?_, ?_, fun j hj => ⟨?_, ?_⟩, initSlots_bounded lt, e⟩
  · exact ((((sv₁.outside oK (by decide)).outside oS (by decide)).outside o₄ (by decide)).outside2 o₅ (by decide)
      (by decide)).outside ot (by decide)
  · exact (o04.trans (o₅.whole (by decide) (by decide))).trans (ot.mono (by omega_arith) (by omega_arith))
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans ((v₃.rest (by decide)).trans
      ((v₄.rest _).trans ((k₅.mono (by decide)).trans (kt.mono (by decide))))))
  · refine c₅.of_eq ?_
    exact ot.word (Or.inl (by decide)) (by decide)
  · rw [ot _ (Or.inr (by rw [ofs_off' base (by simp only [BITS]; omega_arith)]; simp only [BITS]; omega_arith)),
      o₅ _ (by rw [ofs_off' base (by simp only [BITS]; omega_arith)]; simp only [BITS, TMP]; omega_arith)
        (by rw [ofs_off' base (by simp only [BITS]; omega_arith)]; simp only [BITS, BAD]; omega_arith),
      o₄ _ (by rw [ofs_off' base (by simp only [BITS]; omega_arith)]; simp only [BITS, BAD]; omega_arith)]
    exact (b₂ j hj).1
  · rw [ot _ (Or.inr (by rw [ofs_off' base (by omega_arith)]; simp only [KBITS]; omega_arith)),
      o₅ _ (by rw [ofs_off' base (by omega_arith)]; simp only [KBITS, TMP]; omega_arith)
        (by rw [ofs_off' base (by omega_arith)]; simp only [KBITS, BAD]; omega_arith),
      o₄ _ (by rw [ofs_off' base (by omega_arith)]; simp only [KBITS, BAD]; omega_arith)]
    exact (b₂ j hj).2

/-- The arguments, in any state after the entry block whose writes since are in the working
space and the stack below the return address. -/
theorem ventry_args {s₀ s₁ : State} (h : VerifyPre s₀) {base : Addr} (hbase : (arg s₀ 3).setWidth 64 = base)
    (o₁ : Outside base 0 8192 s₀.mem s₁.mem) {rs : List Reg} (k₁ : Keeps rs s₀ s₁) (hesp : .esp ∉ rs) :
    ∀ i < 2, ArgAt s₁ base (4 + 4 * i) (arg s₀ i) := fun i hi t h1 h2 h3 h4 => by
  obtain sp₁ := k₁.1 .esp hesp
  obtain st : callStk s₁ = stkR s₀ := by
    simp only [callStk, sp₁]; rw [stkR_below h.sp_room]
  change Frame [⟨base, 8192⟩, callStk s₁] _ _ at h4
  rw [st] at h4
  obtain ⟨ae, ar, av⟩ := h.args.argReadF (h1.trans sp₁) (h2.trans k₁.2.1) (h3.trans k₁.2.2)
    (((Outside.frame o₁).mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self).trans h4)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · rw [← hbase]; exact h.args_sc
      · exact h.stk_args.symm) (i := i) (by omega_arith)
  exact ⟨_, ae, ar, av⟩

/-- The calls' context after the entry block. -/
theorem ventry_ctx {s₀ s₁ : State} (h : VerifyPre s₀) {base : Addr} (hbase : (arg s₀ 3).setWidth 64 = base)
    (hsp : s₁.gpr .esp = s₀.gpr .esp) : CallCtx s₁ base :=
  ⟨by rw [hsp]; exact h.sp_room, by
    simp only [callStk, hsp]; rw [← stkR_below h.sp_room, ← hbase]; exact h.stk_sc.symm⟩

/-- What the decoding loop needs of the state `s` after the entry, with the arguments of
`s₀`. -/
structure LoopPre (s₀ s : State) : Prop where
  scr : Scr s ((arg s₀ 3).setWidth 64)
  ctx : CallCtx s ((arg s₀ 3).setWidth 64)
  wr : s.wr = [⟨(arg s₀ 3).setWidth 64, 8192⟩]
  bounded : BoundedEnv s.mem ((arg s₀ 3).setWidth 64)
  sig : ArgAt s ((arg s₀ 3).setWidth 64) 8 (arg s₀ 1)
  pk : ArgAt s ((arg s₀ 3).setWidth 64) 4 (arg s₀ 0)
  isig : Input s ((arg s₀ 3).setWidth 64) (arg s₀ 1) 57
  ipk : Input s ((arg s₀ 3).setWidth 64) (arg s₀ 0) 57
  dsig : (⟨(arg s₀ 1).setWidth 64, 57⟩ : Region).Disjoint (callStk s)
  dpk : (⟨(arg s₀ 0).setWidth 64, 57⟩ : Region).Disjoint (callStk s)
  e10 : E s.mem ((arg s₀ 3).setWidth 64) 10 = 1
  e11 : E s.mem ((arg s₀ 3).setWidth 64) 11 = Spec.Ed448.d

theorem ventry_loopPre {s₀ : State} (h : VerifyPre s₀) : WP isa ventry s₀ (LoopPre s₀) := by
  have hA := h.args
  obtain ipk : Input s₀ ((arg s₀ 3).setWidth 64) (arg s₀ 0) 57 :=
    Input.of_region h.f0 (by rw [h.rd]; simp) h.pk_sc
  obtain isig : Input s₀ ((arg s₀ 3).setWidth 64) (arg s₀ 1) 114 :=
    Input.of_region h.f1 (by rw [h.rd]; simp) h.sig_sc
  refine WP.mono (ventry_ok h rfl) fun s₁ ⟨hs₁, _, o₁, k₁, _, _, b₁, e₁⟩ => ?_
  obtain ⟨_, eq, ed⟩ := initE _ e₁
  obtain hArg := ventry_args h rfl o₁ k₁ (by decide)
  obtain st : callStk s₁ = stkR s₀ := by
    simp only [callStk, k₁.1 .esp (by decide)]; rw [stkR_below h.sp_room]
  exact ⟨hs₁, ventry_ctx h rfl (k₁.1 .esp (by decide)), k₁.2.2.trans h.wr, b₁, hArg 1 (by decide),
    hArg 0 (by decide), (isig.take57 (by decide)).of_keeps k₁, ipk.of_keeps k₁,
    by rw [st]; exact (h.stk_sig.sub_right (Region.sub_prefix (by decide))).symm,
    by rw [st]; exact h.stk_pk.symm, congrArg Spec.Ed448.Point.Z eq, ed⟩

/-! ## The whole function -/

theorem sub6_E (e : Env) : evalOps [.sub 6 0 6] e 6 = e 0 - e 6 ∧ ∀ i : Index, i ≠ 6 → evalOps [.sub 6 0 6] e i = e i :=
  ⟨rfl, fun _ hi => Function.update_of_ne hi _ _⟩

theorem verifyEquation_main (hR : RecoverOk) (hE : VerifyEqCombOk) {s₀ : State} (h : VerifyPre s₀) :
    WP isa verifyEquation s₀ fun t => abiPreserved s₀ t ∧
      t.gpr .eax = if Spec.Ed448.verifyEquation (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) 57)
        (bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 114) (bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 57)
        then 1 else 0 := by
  have hA := h.args
  obtain ⟨base, hbase⟩ : ∃ b, (arg s₀ 3).setWidth 64 = b := ⟨_, rfl⟩
  obtain ipk : Input s₀ base (arg s₀ 0) 57 := Input.of_region h.f0 (by rw [h.rd]; simp) (hbase ▸ h.pk_sc)
  obtain isig : Input s₀ base (arg s₀ 1) 114 := Input.of_region h.f1 (by rw [h.rd]; simp) (hbase ▸ h.sig_sc)
  obtain ⟨S, hS⟩ : ∃ S, decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57) = S :=
    ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, decodeLE (bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 57) = K := ⟨_, rfl⟩
  unfold verifyEquation
  -- The entry.
  refine WP.seq (WP.mono (ventry_ok h hbase) fun s₁ ⟨hs₁, sv₁, o₁, k₁, c₁, bits₁, b₁, e₁⟩ => ?_)
  rw [hS] at c₁ bits₁
  rw [hK] at bits₁
  obtain ⟨er, eq, ed⟩ := initE _ e₁
  obtain h10 : E s₁.mem base 10 = 1 := congrArg Spec.Ed448.Point.Z eq
  obtain sp₁ : s₁.gpr .esp = s₀.gpr .esp := k₁.1 .esp (by decide)
  obtain hc₁ : CallCtx s₁ base := ventry_ctx h hbase sp₁
  obtain hw₁ : s₁.wr = [⟨base, 8192⟩] := by rw [k₁.2.2, h.wr, ← hbase]
  obtain st₁ : callStk s₁ = stkR s₀ := by simp only [callStk, sp₁]; rw [stkR_below h.sp_room]
  -- The rest writes the working space and the stack below the return address.
  obtain retk : ∀ t : State, Frame (s₁.wr ++ [below (s₁.gpr .esp) (stackUse (.seq vdecode vafter))]) s₁.mem t.mem →
      t.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 := by
    intro t ft
    obtain frame : Frame (s₁.wr ++ [below (s₁.gpr .esp) 20]) s₀.mem t.mem :=
      ((Outside.frame o₁).mono fun r hr => by
        rw [List.mem_singleton.mp hr, hw₁]; exact List.mem_cons_self).trans
        (Frame.below_mono ft (by lit_decide) hc₁.sp)
    obtain ret : (retR s₀).Contains ((s₀.gpr .esp).setWidth 64) 4 := by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((s₀.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide)
          (by decide)
    refine frame.readW ret ?_ (by decide)
    rw [hw₁, show below (s₁.gpr .esp) 20 = stkR s₀ from st₁]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hbase ▸ h.ret_sc
    · exact h.stk_ret.symm
  refine WP.mono (WP.withFrame (NoSp.of_all (by lit_decide))
    (Nat.le_trans (by lit_decide : stackUse (.seq vdecode vafter) ≤ 20) hc₁.sp)
    (Q := fun t => (∀ r ∈ calleeSaved, t.gpr r = s₀.gpr r) ∧
      t.gpr .eax = if Spec.Ed448.verifyEquation (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) 57)
        (bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 114) (bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 57)
        then 1 else 0) ?_) fun t ⟨⟨regs, res⟩, ft⟩ => ⟨⟨regs, retk t ft⟩, res⟩
  -- `R` and `A`.
  obtain hArg := ventry_args h hbase o₁ k₁ (by decide)
  obtain isig57 : Input s₀ base (arg s₀ 1) 57 := isig.take57 (by decide)
  refine WP.seq (WP.mono (vdecode_ok hR hs₁ hc₁ hw₁ b₁ (hArg 1 (by decide)) (hArg 0 (by decide))
    (isig57.of_keeps k₁) (ipk.of_keeps k₁)
    (by rw [st₁]; exact (h.stk_sig.sub_right (Region.sub_prefix (by decide))).symm)
    (by rw [st₁]; exact h.stk_pk.symm) h10 ed) fun s₂ D₂ => ?_)
  obtain dR : decAt s₁.mem (arg s₀ 1) = Spec.Ed448.decodePoint ((bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 114).take 57) := by
    rw [bytesAt_take57]; exact congrArg Spec.Ed448.decodePoint (isig57.bytes o₁)
  obtain dA : decAt s₁.mem (arg s₀ 0) = Spec.Ed448.decodePoint (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) 57) :=
    congrArg Spec.Ed448.decodePoint (ipk.bytes o₁)
  have c₂ := D₂.bad
  obtain v₂ := D₂.aIn rfl
  obtain vR₂ := D₂.rOut rfl
  have e₂ := D₂.other
  rw [dR, dA] at c₂
  rw [dA] at v₂
  rw [dR] at vR₂
  obtain hs₂ := D₂.scr hs₁
  obtain hc₂ : CallCtx s₂ base := hc₁.keep (D₂.keeps.1 _ (by decide))
  have b₂ := D₂.bounded
  unfold vafter
  -- `-A`.
  refine field_seq [.sub 6 0 6] (by decide) hs₂ hc₂ b₂ fun s₃ k₃ b₃ e₃ => ?_
  obtain hs₃ := k₃.scr hs₂
  obtain hc₃ := k₃.ctx hc₂
  obtain ⟨n₃, k₃e⟩ := sub6_E (E s₂.mem base)
  rw [← e₃] at n₃ k₃e
  -- `k`'s digits.
  obtain bits₃ : VBits base S K s₃.mem :=
    VBits.kept (WsOut2.widen k₃.mem) (VBits.keptD D₂.frame bits₁)
  refine WP.seq (WP.mono (vrecode_ok (K := K) hs₃ fun q hq => (bits₃ q hq).2) fun s₄ ⟨k₄, o₄, dig₄⟩ => ?_)
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  obtain hc₄ : CallCtx s₄ base := hc₃.keep (k₄.1 _ (by decide))
  obtain ⟨e₄, b₄⟩ := slots_out o₄ (by decide)
  obtain dg₄ : VDig base S K s₄.mem := fun t ht =>
    ⟨by rw [o₄ _ (Or.inl (by rw [ofs_off' base (by simp only [BITS]; omega_arith)]; simp only [BITS, KBITS]; omega_arith))]
        exact (bits₃ t ht).1, dig₄ t ht⟩
  -- What is kept from the entry to the table.
  obtain k41 : ∀ i : Index, i.val = 0 ∨ i.val = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 11) →
      E s₄.mem base i = E s₁.mem base i := fun i hi => by
    rw [e₄, k₃e i (fun h => by subst h; omega_arith),
      e₂ i (fun h => by subst h; omega_arith) (fun h => by subst h; omega_arith) (by omega_arith)]
  -- The table of `-A`'s odd multiples.
  refine WP.seq (WP.mono (vtable_ok hs₄ hc₄ (b₄ b₃) (by rw [k41 10 (by decide)]; exact h10)
    (by rw [k41 11 (by decide)]; exact ed)) fun s₅ T₅ => ?_)
  obtain dg₅ : VDig base S K s₅.mem := dg₄.below T₅.mem (by decide) (by decide)
  -- The loop.
  refine WP.seq (WP.mono (vloop_ok (s₀ := s₅) (A := pt (E s₄.mem base) 6 7 10) dg₅ T₅.tab
    (fun s' h1 h2 h3 h4 h5 => ?_)) fun s₆ I₆ => ?_)
  · have k' : Keeps (.esi :: workRegs) s₅ s' :=
      ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
    refine ⟨T₅.scr.of_keeps k' (by decide), T₅.ctx.keep (h2 _ (by decide)), h3 ▸ T₅.bounded, k', h1,
      h3 ▸ WsOut2.refl _ _ _ _ _ _, ?_, ?_, ?_⟩
    · rw [h3, Nat.sub_self]; exact T₅.q
    · rw [h3]; exact T₅.one
    · rw [h3]; exact T₅.d
  -- `Q`'s `Y` moved to slot 6.
  have hs₆ := I₆.scr
  rw [show ops [Impl.X448.X86.Op.copy (slot 6) X2] = ops (([.copy 6 1] : List FieldOp).map FieldOp.impl)
    from rfl]
  refine WP.seq (WP.mono (ops_ok hs₆ I₆.ctx I₆.bounded [.copy 6 1]) fun s₇ ⟨k₇, b₇, e₇⟩ => ?_)
  obtain hs₇ := k₇.scr hs₆
  obtain e₇6 : E s₇.mem base 6 = E s₆.mem base 1 := by
    rw [e₇]; simp only [applyOps, FieldOp.apply, opCopy, Function.update_self]
  obtain e₇k : ∀ i : Index, i ≠ 6 → E s₇.mem base i = E s₆.mem base i := fun i hi => by
    rw [e₇]; exact Function.update_of_ne hi _ _
  obtain k07 : Keeps (.esi :: workRegs) s₁ s₇ :=
    ((D₂.keeps.trans (k₃.regs.mono (fun _ h => List.mem_cons_of_mem _ h))).trans
      ((k₄.mono (by decide)).trans T₅.regs)).trans
      (I₆.regs.trans (k₇.regs.mono (fun _ h => List.mem_cons_of_mem _ h)))
  -- `R` copied back.
  obtain h107 : E s₇.mem base 10 = 1 := by rw [e₇k 10 (by decide)]; exact I₆.one
  obtain FR : ∀ o, o = RX ∨ o = RY →
      F s₇.mem base o = F s₂.mem base o ∧ (Bounded s₂.mem base o → Bounded s₇.mem base o) := fun o ho => by
    obtain ⟨f3, g3⟩ := F_high k₃.mem (by decide) ho
    obtain ⟨f4, g4⟩ := F_below (WsBelow.of_out o₄ (Nat.le_refl _)) (Nat.le_refl _) (by decide) ho
    obtain ⟨f5, g5⟩ := F_below T₅.mem (by decide) (by decide) ho
    obtain ⟨f6, g6⟩ := F_high I₆.mem (by decide) ho
    obtain ⟨f7, g7⟩ := F_high k₇.mem (by decide) ho
    exact ⟨f7.trans (f6.trans (f5.trans (f4.trans f3))), fun h => g7 (g6 (g5 (g4 (g3 h))))⟩
  obtain ⟨bRX, bRY⟩ := D₂.rBnd rfl
  refine WP.seq (WP.mono (vR_ok hs₇ b₇ ((FR RX (Or.inl rfl)).2 bRX) ((FR RY (Or.inr rfl)).2 bRY))
    fun s₈ ⟨k₈, b₈, x₈, y₈, e₈⟩ => ?_)
  obtain hs₈ := k₈.scr hs₇
  -- `BAD`.
  obtain bad₅ : word s₅.mem base BAD = word s₂.mem base BAD := by
    rw [T₅.mem.word (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide)),
      o₄.word (Or.inl (by decide)) (by decide), Keep.bad k₃]
  obtain bad₇ : word s₇.mem base BAD = word s₅.mem base BAD := by
    rw [Keep.bad k₇]; exact I₆.mem.word (Or.inl (by decide)) (Or.inl (by decide)) (by decide)
  obtain bad₈ : word s₈.mem base BAD = word s₂.mem base BAD := by rw [Keep.bad k₈, bad₇, bad₅]
  obtain z₈ := ((c₁.trans (c₂.of_eq bad₈)).congr decShape).zero
  -- The comparison.
  obtain sv₅ : Saved base s₀.gpr s₅.mem :=
    (((sv₁.wsout2 D₂.frame (by decide) (by decide)).wsout2 k₃.mem (by decide) (by decide)).outside o₄
      (by decide)).of_readW fun p hp => have := savedSlots_bound p hp
        T₅.mem.word (by decide) (by simp only [VTAB]; omega_using [this]) (Or.inl (by omega_using [this]))
          (Or.inl (by simp only [ACC]; omega_using [this]))
  obtain sv₈ : Saved base s₀.gpr s₈.mem :=
    ((sv₅.wsout2 I₆.mem (by decide) (by decide)).wsout2 k₇.mem (by decide)
      (by decide)).wsout2 k₈.mem (by decide) (by decide)
  obtain hc₈ : CallCtx s₈ base := k₈.ctx (k₇.ctx I₆.ctx)
  refine WP.mono (vfinish_ok hs₈ hc₈ b₈ sv₈ z₈.2) fun t ⟨rt, st, spt⟩ => ⟨fun r hr => ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact st (.ebx, 0) (by decide)
    · exact st (.esi, 4) (by decide)
    · exact st (.edi, 8) (by decide)
    · exact st (.ebp, 12) (by decide)
    · rw [spt, k₈.regs.1 _ (by decide), k07.1 _ (by decide), k₁.1 _ (by decide)]
  · rw [rt]
    refine if_congr ?_ rfl rfl
    rw [z₈.1]
    cases ha : Spec.Ed448.decodePoint (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) 57) with
    | none =>
      rw [verifyEquation_none (Or.inl ha)]
      exact ⟨fun h => absurd h.1.1.2 (by simp), fun h => absurd h (by decide)⟩
    | some a =>
      cases hr : Spec.Ed448.decodePoint ((bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 114).take 57) with
      | none =>
        rw [verifyEquation_none (Or.inr hr)]
        exact ⟨fun h => absurd h.1.2 (by simp), fun h => absurd h (by decide)⟩
      | some r =>
        obtain ⟨ax, ay, az⟩ := v₂ a ha
        obtain ⟨rx, ry, rz⟩ := vR₂ r hr
        obtain e20 : E s₂.mem base 0 = 0 := by
          rw [e₂ 0 (by decide) (by decide) (Or.inl rfl)]; exact congrArg Spec.Ed448.Point.X er
        obtain e210 : E s₂.mem base 10 = 1 := by
          rw [e₂ 10 (by decide) (by decide) (by decide)]; exact h10
        obtain hA' : pt (E s₄.mem base) 6 7 10 = negPoint a := by
          show (⟨E s₄.mem base 6, E s₄.mem base 7, E s₄.mem base 10⟩ : Spec.Ed448.Point) = ⟨0 - a.X, a.Y, a.Z⟩
          rw [e₄, n₃, k₃e 7 (by decide), k₃e 10 (by decide), e20, ax, ay, e210, az]
        obtain hQ : pt (E s₈.mem base) 0 6 2 = vcomb S K (negPoint a) 456 := by
          rw [pt_congr' (e₈ 0 (by decide) (by decide)) (e₈ 6 (by decide) (by decide)) (e₈ 2 (by decide) (by decide))]
          show (⟨E s₇.mem base 0, E s₇.mem base 6, E s₇.mem base 2⟩ : Spec.Ed448.Point) = _
          rw [e₇k 0 (by decide), e₇6, e₇k 2 (by decide), ← hA']
          exact I₆.rep
        obtain hRR : pt (E s₈.mem base) 8 9 10 = r := by
          show (⟨E s₈.mem base 8, E s₈.mem base 9, E s₈.mem base 10⟩ : Spec.Ed448.Point) = r
          rw [x₈, y₈, (FR RX (Or.inl rfl)).1, (FR RY (Or.inr rfl)).1, rx, ry, e₈ 10 (by decide) (by decide), h107,
            ← rz]
        rw [hE _ _ _ _ _ (bytesAt57_len _ _) (bytesAt114_len _ _) (bytesAt57_len _ _) ha hr, hQ, hRR,
          bytesAt_drop57, hS, hK]
        simp only [Option.isSome_some, and_true, Bool.and_eq_true, decide_eq_true_eq]

end VG.Proof.Ed448.X86
