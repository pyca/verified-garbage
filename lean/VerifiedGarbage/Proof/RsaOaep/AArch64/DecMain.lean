module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecOut
public import VerifiedGarbage.Proof.RsaOaep.Decode
public import VerifiedGarbage.Spec.RsaOaep.Contract
import VerifiedGarbage.Proof.RsaOaep.AArch64.Args
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Loops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelT
public import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfT

/-! ### `RsaOaep.AArch64.DecLoops`, which only this module used -/

section

/-! ### `RsaOaep.AArch64.WordMemory`, which only this module used -/

section

/-!
# Word copies in the OAEP decoding workspace

The source word is read before the destination is written. Neither alignment
nor disjointness between the two words is required; the frame is preserved.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Mgf1 (ifp ifn)

/-- Copy eight bytes from the pre-store workspace. -/
def copy8V (V : Nat → Byte) (dst src : Nat) : Nat → Byte :=
  fun x => if dst ≤ x ∧ x < dst + 8 then V (src + (x - dst)) else V x

/-- A word load/store implements the byte copy even when the words overlap. -/
theorem Rep.copy8 {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep m F S V W) {dst src : Nat}
    (hd : dst + 8 ≤ oRsa) (hs : src + 8 ≤ oRsa) :
    Rep (m.writeW (off S dst) (m.readW (off S src) 64)) F S (copy8V V dst src) W where
  scr x hx := by
    obtain hw : dst + 8 ≤ 2 ^ 64 := by unfold oRsa at hd; omega_using [hd]
    obtain hrange : (off S x - off S dst).toNat < 8 ↔ dst ≤ x ∧ x < dst + 8 := by
     rw [Offset.lt_iff _ S hw, Mem.sub_ofNat_toNat S (by unfold oRsa at hx; omega_using [hx])]
    change (if (off S x - off S dst).toNat < 8 then
     (m.read (off S src) 8).extractLsb' (8 * (off S x - off S dst).toNat) 8 else m (off S x)) = _
    unfold copy8V
    by_cases h : dst ≤ x ∧ x < dst + 8
    · rw [ifp (hrange.mpr h), ifp h, Offset.sub_toNat S h.1 (by unfold oRsa at hx; omega_using [hx]),
       Mem.extractLsb'_read m (off S src) (n := 8) (by omega_using [h])]
      change m (off (off S src) (x - dst)) = _
      rw [off_off]
      exact R.scr _ (by omega_using [hs, h])
    · rw [ifn (fun e => h (hrange.mp e)), ifn h, R.scr x hx]
  fr k hk := by
    rw [word, Mem.readW_writeW_sep (Region.Disjoint.sep G.dFS (G.cFw hk) (cS S hd)) (by decide)]
    exact R.fr k hk

theorem frame_copy8 {F S : Addr} {ws : List Region} {m : Mem} {dst src : Nat}
    (hd : dst + 8 ≤ oRsa) :
    Frame (⟨F, frameBytes⟩ :: ⟨S, oRsa⟩ :: retR F :: ws) m
      (m.writeW (off S dst) (m.readW (off S src) 64)) := by
  exact (Frame.refl _ _).write (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    _ (cS S hd)

end VG.Proof.RsaOaep.AArch64

end

end


/-!
# RSAES-OAEP decryption on AArch64: the loops of the decoding

As on x86-64 (`Proof/RsaOaep/X86_64/DecLoops.lean`), each loop of `decMain`
after MGF1, as a function of the working space's bytes (`V`) and the
frame's words: the comparison of `lHash'` with `lHash` (`accLh_ok`, the
`accG` of `Proof/RsaOaep/Scan.lean`), the scan of `T` (`scan_ok`,
`scanS`), the buffer cleared (`clearBuf_ok`), `T` copied to it
(`copyT_ok`), the shift (`shift_ok`), and `out` (`outLoop_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

/-! ## `lHash'` against `lHash` -/

/-- The accumulator of `EM[0]` and `lHash ⊕ lHash'` after `j` bytes. -/
abbrev accL (V : Nat → Byte) (D j : Nat) : BitVec 64 := accG (V oEm) (fun i => V (oLh + i)) (fun i => V (1 + D + i)) j

theorem accHead_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {H : Hash} (hD : H.D < 1024) (ws : List Region) :
    WP isa (.block (scr .x11 oLh ++ scr .x12 (oEm + 1 + H.D) ++ scr .x13 oEm ++
      ([.ldrb .x14 .x13 0, .movz .x .x13 (BitVec.ofNat 16 H.D) 0] : List Instr))) u fun u' =>
      Step F S ws u u' ∧ u'.mem = u.mem ∧ u'.gpr .x11 = off S oLh ∧ u'.gpr .x12 = off S (1 + H.D) ∧
      u'.gpr .x13 = BitVec.ofNat 64 H.D ∧ u'.gpr .x14 = accL V H.D 0 := by
  obtain h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  obtain r0 : InRegions (u.rd ++ u.wr) S 1 := by simpa [off] using L.sld (o := 0) (n := 1) (by decide)
  obtain v0 : u.mem S = V oEm := by simpa [off, oEm] using R.scr 0 (by decide)
  oaep_run [scr, Mgf1.scr, lay, sScr, oLh, oEm, h96, L.sp, hs, show 1 + H.D < 4096 by omega_arith,
    show 0 + 1 + H.D = 1 + H.D by omega_arith, BitVec.add_zero, r0, read_one, v0, byte64, imm16 (show H.D < 65536 by omega_arith)]
  oaep_fin

/-- One byte of the comparison. -/
theorem accBody_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {D j : Nat} (hD : D < 1024) (hj : j < D)
    (h11 : u.gpr .x11 = off S (oLh + j)) (h12 : u.gpr .x12 = off S (1 + D + j)) (ws : List Region) :
    WP isa (.block [.ldrb .x10 .x11 0, .ldrb .x15 .x12 0, .logic .eor .x .x10 .x10 .x15,
      .logic .orr .x .x14 .x14 .x10, .addImm .x .x11 .x11 1, .addImm .x .x12 .x12 1, .subImm .x .x13 .x13 1]) u
      fun u' => Step F S ws u u' ∧ u'.mem = u.mem ∧ u'.gpr .x11 = off S (oLh + j) + BitVec.ofNat 64 1 ∧
        u'.gpr .x12 = off S (1 + D + j) + BitVec.ofNat 64 1 ∧ u'.gpr .x13 = u.gpr .x13 - BitVec.ofNat 64 1 ∧
        u'.gpr .x14 = u.gpr .x14 ||| ((V (oLh + j)).setWidth 64 ^^^ (V (1 + D + j)).setWidth 64) := by
  obtain r1 : InRegions (u.rd ++ u.wr) (off S (oLh + j)) 1 := L.sld (by unfold oLh oRsa; omega_arith)
  obtain r2 : InRegions (u.rd ++ u.wr) (off S (1 + D + j)) 1 := L.sld (by unfold oRsa; omega_arith)
  obtain v1 : u.mem (off S (oLh + j)) = V (oLh + j) := R.scr _ (by unfold oLh oRsa; omega_arith)
  obtain v2 : u.mem (off S (1 + D + j)) = V (1 + D + j) := R.scr _ (by unfold oRsa; omega_arith)
  oaep_run [h11, h12, BitVec.add_zero, r1, r2, read_one, v1, v2, byte64]
  oaep_fin

/-- The comparison of `lHash'` with `lHash`, after the first `j` bytes. -/
structure AccI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (D j : Nat) (v : State) :
    Prop where
  L : Lay v F S
  st : Step F S [] u₀ v
  mem : v.mem = u₀.mem
  x11 : v.gpr .x11 = off S (oLh + j)
  x12 : v.gpr .x12 = off S (1 + D + j)
  x13 : v.gpr .x13 = BitVec.ofNat 64 (D - j)
  x14 : v.gpr .x14 = accL V D j

theorem accLoop_ok {u₀ : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u₀.mem F S V W)
    {D : Nat} (hD : D < 1024) (hD0 : 0 < D) (h : AccI u₀ F S V W D 0 u₀) :
    WP isa (.loop (.block [.ldrb .x10 .x11 0, .ldrb .x15 .x12 0, .logic .eor .x .x10 .x10 .x15,
      .logic .orr .x .x14 .x14 .x10, .addImm .x .x11 .x11 1, .addImm .x .x12 .x12 1, .subImm .x .x13 .x13 1])
      (.nonzero .x .x13)) u₀ (AccI u₀ F S V W D D) :=
  count_loop hD0 (AccI u₀ F S V W D) (fun j hj u I => WP.mono (accBody_ok I.L (I.mem ▸ R) hD hj I.x11 I.x12 [])
    fun u' ⟨S', hm, x11, x12, x13, x14⟩ => ⟨⟨I.L.congr S'.sp S'.wr (by rw [hm]), I.st.trans S', hm.trans I.mem,
      x11.trans (off_off S _ 1), x12.trans (off_off S _ 1), by rw [x13, I.x13, counter_step hj (by omega_arith)],
      by rw [x14, I.x14]; rfl⟩, by rw [x13, I.x13, counter_step hj (by omega_arith)]; exact counter_ne hj (by omega_arith)⟩) h

/-- A register `r` to the frame's word `k` (`d = 8 k`), through `x9 = sp`. -/
theorem stSlot_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (r : Reg) (hr : r ≠ .x9) {d k : Nat} (hd : d = 8 * k) (hk : 13 ≤ k ∧ k < nW)
    (ws : List Region) :
    WP isa (.block [.addSp .x9 0, .str .x r .x9 d]) u fun u' => Lay u' F S ∧ Step F S ws u u' ∧
      Rep u'.mem F S V (upd W k (u.gpr r)) ∧ ∀ q, q ≠ .x9 → u'.gpr q = u.gpr q := by
  subst hd
  obtain hk' : 8 * k + 8 ≤ frameBytes := by unfold nW frameBytes at *; omega_arith
  obtain w : InRegions u.wr (F + BitVec.ofNat 64 (8 * k)) 8 := L.st hk'
  obtain R' : Rep (u.mem.write (off F (8 * k)) 8 (u.gpr r)) F S V (upd W k (u.gpr r)) := R.wq L.geo hk.2 _
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem.write (off F (8 * k)) 8 (u.gpr r) ∧ u'.rd = u.rd ∧
      u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧ ∀ q, q ≠ .x9 → u'.gpr q = u.gpr q) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hg⟩ => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.store, addr, Size.bits,
      Size.bytes, BitVec.setWidth_eq, Nat.reduceMul, Nat.mul_mod_right, and_self, ite_true,
      Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
      RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write, L.sp, BitVec.add_zero, w, hr, ite_false,
      show 8 * k < 32768 by unfold nW frameBytes at hk; omega_arith, show (0 : Nat) < 4096 by decide]
    and_intros <;> first | trivial | (intro q hq; simp [hq])
  obtain R'' : Rep u'.mem F S V (upd W k (u.gpr r)) := by rw [hm]; exact R'
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, fun q _ hq => hg q (by rintro rfl; simp [preserved] at *), fun q _ => by
    rw [hv], by rw [hm]; exact Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF F hk')⟩, R'', hg⟩
  rw [show sScr = 8 * 12 from rfl, R''.fr 12 (by decide), R.fr 12 (by decide), upd, ifn (by omega_arith)]

theorem accLh_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {H : Hash} (hD : H.D < 1024) (hD0 : 0 < H.D) :
    WP isa (accLh H) u fun u' => Lay u' F S ∧ Step F S [] u u' ∧ Rep u'.mem F S V (upd W 29 (accL V H.D H.D)) := by
  refine WP.seq (WP.mono (accHead_ok L R hD []) fun u1 ⟨S1, hm1, x11, x12, x13, x14⟩ => ?_)
  obtain L1 : Lay u1 F S := L.congr S1.sp S1.wr (by rw [hm1])
  obtain R1 : Rep u1.mem F S V W := hm1 ▸ R
  refine WP.seq (WP.mono (accLoop_ok R1 hD hD0 ⟨L1, Step.refl _ _ _ _, rfl, by rw [x11, Nat.add_zero],
    by rw [x12, Nat.add_zero], by rw [x13, Nat.sub_zero], x14⟩) fun u2 I => ?_)
  refine WP.mono (stSlot_ok I.L (I.mem ▸ R1) .x14 (by decide) (d := sAcc) (k := 29) rfl (by decide) [])
    fun u3 ⟨L3, S3, R3, _⟩ => ⟨L3, S1.trans (I.st.trans S3), by rw [I.x14] at R3; exact R3⟩

/-! ## The scan of `T` -/

/-- `T`, the bytes of `DB` after `lHash'`. -/
def tF (V : Nat → Byte) (D : Nat) (i : Nat) : Byte := V (1 + 2 * D + i)

theorem scanBody_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {D j : Nat} (hj : 1 + 2 * D + j < oRsa)
    (h11 : u.gpr .x11 = off S (1 + 2 * D + j)) (h17 : u.gpr .x17 = 1) (ws : List Region) :
    WP isa (.block scanBody) u fun u' => Step F S ws u u' ∧ u'.mem = u.mem ∧
      u'.gpr .x11 = off S (1 + 2 * D + j) + BitVec.ofNat 64 1 ∧ u'.gpr .x12 = u.gpr .x12 - BitVec.ofNat 64 1 ∧
      u'.gpr .x9 = u.gpr .x9 + BitVec.ofNat 64 1 ∧ u'.gpr .x17 = 1 ∧
      u'.gpr .x13 = u.gpr .x13 &&& ~~~(zM ((tF V D j).setWidth 64 ^^^ 1)) ∧
      u'.gpr .x8 = u.gpr .x8 ||| (u.gpr .x9 &&& u.gpr .x13 &&& zM ((tF V D j).setWidth 64 ^^^ 1)) ∧
      u'.gpr .x14 = u.gpr .x14 ||| (u.gpr .x13 &&&
        ~~~(zM ((tF V D j).setWidth 64) ||| zM ((tF V D j).setWidth 64 ^^^ 1))) := by
  obtain r1 : InRegions (u.rd ++ u.wr) (off S (1 + 2 * D + j)) 1 := L.sld (by omega_arith)
  obtain v1 : u.mem (off S (1 + 2 * D + j)) = tF V D j := R.scr _ hj
  oaep_run [scanBody, isZero, h11, h17, BitVec.add_zero, r1, read_one, v1, byte64, sbc_one,
    rotateRight_zero]
  oaep_fin

/-- The scan after the first `j` bytes of `T` (`t` bytes), from the accumulator `c₀`. -/
structure ScanI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (D t : Nat) (c₀ : BitVec 64)
    (j : Nat) (v : State) : Prop where
  L : Lay v F S
  st : Step F S [] u₀ v
  mem : v.mem = u₀.mem
  x11 : v.gpr .x11 = off S (1 + 2 * D + j)
  x12 : v.gpr .x12 = BitVec.ofNat 64 (t - j)
  x9 : v.gpr .x9 = BitVec.ofNat 64 j
  x17 : v.gpr .x17 = 1
  x13 : v.gpr .x13 = (scanS (tF V D) c₀ j).1
  x8 : v.gpr .x8 = (scanS (tF V D) c₀ j).2.1
  x14 : v.gpr .x14 = (scanS (tF V D) c₀ j).2.2

theorem scanLoop_ok {u₀ : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u₀.mem F S V W)
    {D t : Nat} {c₀ : BitVec 64} (ht : 1 + 2 * D + t ≤ oRsa) (ht0 : 0 < t) {v₀ : State}
    (h : ScanI u₀ F S V W D t c₀ 0 v₀) :
    WP isa (.loop (.block scanBody) (.nonzero .x .x12)) v₀ (ScanI u₀ F S V W D t c₀ t) := by
  have : oRsa = 8192 := rfl
  refine count_loop ht0 (ScanI u₀ F S V W D t c₀) (fun j hj u I => ?_) h
  refine WP.mono (scanBody_ok I.L (I.mem ▸ R) (j := j) (by omega_arith) I.x11 I.x17 [])
    fun u' ⟨S', hm, x11, x12, x9, x17, x13, x8, x14⟩ => ⟨⟨I.L.congr S'.sp S'.wr (by rw [hm]), I.st.trans S',
      hm.trans I.mem, x11.trans (off_off S _ 1), by rw [x12, I.x12, counter_step hj (by omega_arith)],
      by rw [x9, I.x9, BitVec.ofNat_add_ofNat], x17, ?_, ?_, ?_⟩, ?_⟩
  · rw [x13, I.x13, scanS, ← BitVec.xor_allOnes]
  · rw [x8, I.x8, I.x9, I.x13, scanS]
  · rw [x14, I.x14, I.x13, scanS, ← BitVec.xor_allOnes, BitVec.and_comm (scanS (tF V D) c₀ j).1]
  · rw [x12, I.x12, counter_step hj (by omega_arith)]; exact counter_ne hj (by omega_arith)

theorem scanHead_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {H : Hash} {k : Nat} (hk : W 21 = BitVec.ofNat 64 k) (hD : 2 * H.D + 2 ≤ k)
    (hk' : k ≤ 1024) :
    WP isa (.block (tArgs H ++ ([.movz .x .x13 0 0, .subImm .x .x13 .x13 1, .movz .x .x8 0 0, .ldrSp .x14 sAcc,
      .movz .x .x9 0 0, .movz .x .x17 1 0] : List Instr))) u
      (ScanI u F S V W H.D (k - 2 * H.D - 1) (W 29) 0) := by
  obtain h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  obtain h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  obtain h232 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 232) 8 := L.ld (d := 232) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  obtain rk := R.rdK hk
  obtain ra := R.rd8 (d := 232) (k := 29) rfl (by decide) rfl
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = off S (1 + 2 * H.D) ∧
      u'.gpr .x12 = BitVec.ofNat 64 (k - (2 * H.D + 1)) ∧ u'.gpr .x9 = BitVec.ofNat 64 0 ∧ u'.gpr .x17 = 1 ∧
      u'.gpr .x13 = BitVec.allOnes 64 ∧ u'.gpr .x8 = 0 ∧ u'.gpr .x14 = W 29) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x9, x17, x13, x8, x14⟩ =>
      ⟨L.congr hsp hwr (by rw [hm]), Step.blk _ hrd hwr hsp hv hcs hm, hm, x11, by rw [x12]; congr 1, x9, x17, x13,
        x8, x14⟩
  oaep_run [tArgs, scr, Mgf1.scr, lay, sScr, sK, sAcc, oEm, h96, h168, h232, L.sp, hs, rk, ra,
    Nat.zero_add, show 1 + 2 * H.D < 4096 by omega_arith, show 2 * H.D + 1 < 4096 by omega_arith,
    Offset.ofNat_sub_ofNat (show 2 * H.D + 1 ≤ k by omega_arith)]
  oaep_fin

theorem scanTail_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (ws : List Region) :
    WP isa (.block [.logic .orr .x .x14 .x14 .x13, .addSp .x9 0, .str .x .x14 .x9 sAcc, .str .x .x8 .x9 sIdx]) u
      fun u' => Lay u' F S ∧ Step F S ws u u' ∧
        Rep u'.mem F S V (upd (upd W 29 (u.gpr .x14 ||| u.gpr .x13)) 30 (u.gpr .x8)) := by
  have G' := L.geo
  obtain R2 : Rep ((u.mem.write (off F 232) 8 (u.gpr .x14 ||| u.gpr .x13)).write (off F 240) 8 (u.gpr .x8)) F S V
      (upd (upd W 29 (u.gpr .x14 ||| u.gpr .x13)) 30 (u.gpr .x8)) :=
    (R.wq G' (k := 29) (by decide) _).wq G' (k := 30) (by decide) _
  obtain w232 : InRegions u.wr (F + BitVec.ofNat 64 232) 8 := L.st (d := 232) (by decide)
  obtain w240 : InRegions u.wr (F + BitVec.ofNat 64 240) 8 := L.st (d := 240) (by decide)
  refine WP.mono (Q := fun (u' : State) => u'.mem = (u.mem.write (off F 232) 8 (u.gpr .x14 ||| u.gpr .x13)).write
      (off F 240) 8 (u.gpr .x8) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧
      (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r)) ?_ fun u' ⟨hm, hrd, hwr, hsp, hv, hcs⟩ => ?_
  · oaep_run [sAcc, sIdx, w232, w240, L.sp, BitVec.add_zero]
    oaep_fin
  obtain R' : Rep u'.mem F S V (upd (upd W 29 (u.gpr .x14 ||| u.gpr .x13)) 30 (u.gpr .x8)) := by rw [hm]; exact R2
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], ?_⟩, R'⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]; rfl
  · rw [hm]
    exact Frame.write (Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF F (by decide)))
      (List.mem_cons_self ..) _ (cF F (by decide))

/-- The scan of `T` (`t = k - 2 hLen - 1` bytes): `acc` ORed with the scan's
mask and whether no `0x01` was found, and `idx`, in their slots. -/
theorem scan_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {H : Hash} {k : Nat} (hk : W 21 = BitVec.ofNat 64 k) (hD : 2 * H.D + 2 ≤ k)
    (hk' : k ≤ 1024) :
    WP isa (scan H) u fun u' => Lay u' F S ∧ Step F S [] u u' ∧
      Rep u'.mem F S V (upd (upd W 29 ((scanS (tF V H.D) (W 29) (k - 2 * H.D - 1)).2.2 |||
        (scanS (tF V H.D) (W 29) (k - 2 * H.D - 1)).1)) 30 (scanS (tF V H.D) (W 29) (k - 2 * H.D - 1)).2.1) := by
  refine WP.seq (WP.mono (scanHead_ok L R hk hD hk') fun u1 I => ?_)
  refine WP.seq (WP.mono (scanLoop_ok R (by unfold oRsa; omega_arith) (by omega_arith) I) fun u2 I2 => ?_)
  refine WP.mono (scanTail_ok I2.L (I2.mem ▸ R) []) fun u3 ⟨L3, S3, R3⟩ => ⟨L3, I2.st.trans S3, ?_⟩
  rw [I2.x14, I2.x13, I2.x8] at R3; exact R3

/-! ## The buffer -/

theorem clearBuf_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) :
    WP isa clearBuf u fun u' => Lay u' F S ∧ Step F S [] u u' ∧ Rep u'.mem F S (zV V oBuf 2048) W := by
  obtain h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  refine WP.seq (WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = off S oBuf ∧
      u'.gpr .x12 = BitVec.ofNat 64 256 ∧ u'.gpr .x13 = 0) ?_ fun u1 ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x13⟩ => ?_)
  · oaep_run [clearBuf, scr, Mgf1.scr, lay, sScr, oBuf, h96, L.sp, hs]
    oaep_fin
  obtain S1 : Step F S [] u u1 := Step.blk _ hrd hwr hsp hv hcs hm
  refine WP.mono (clearLoop_ok (L.congr hsp hwr (by rw [hm])) (hm ▸ R) (o := oBuf) (n := 256) (by decide)
    (by decide) x11 x12 x13 []) fun u2 ⟨L2, S2, R2⟩ => ⟨L2, S1.trans S2, R2⟩

/-- `T` (`t = k - 2 hLen - 1` bytes at `1 + 2 hLen`) to the buffer. -/
theorem copyT_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {H : Hash} {k : Nat} (hk : W 21 = BitVec.ofNat 64 k) (hD : 2 * H.D + 2 ≤ k)
    (hk' : k ≤ 1024) :
    WP isa (copyT H) u fun u' => Lay u' F S ∧ Step F S [] u u' ∧
      Rep u'.mem F S (cpV V oBuf (k - 2 * H.D - 1) (tF V H.D)) W := by
  obtain h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  obtain h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  obtain rk := R.rdK hk
  refine WP.seq (WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = off S (1 + 2 * H.D) ∧
      u'.gpr .x12 = off S oBuf ∧ u'.gpr .x13 = BitVec.ofNat 64 (k - (2 * H.D + 1))) ?_
    fun u1 ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x13⟩ => ?_)
  · oaep_run [copyT, tArgs, mov, scr, Mgf1.scr, lay, sScr, sK, oBuf, oEm, h96, h168, L.sp, hs, rk, Nat.zero_add,
      show 1 + 2 * H.D < 4096 by omega_arith, show 2 * H.D + 1 < 4096 by omega_arith,
      Offset.ofNat_sub_ofNat (show 2 * H.D + 1 ≤ k by omega_arith), BitVec.or_self]
    oaep_fin
  obtain S1 : Step F S [] u u1 := Step.blk _ hrd hwr hsp hv hcs hm
  obtain L1 : Lay u1 F S := L.congr hsp hwr (by rw [hm])
  obtain R1 : Rep u1.mem F S V W := hm ▸ R
  have c : oRsa = 8192 := rfl
  have cb : oBuf = 1024 := rfl
  refine WP.mono (copyLoop_ok L1 R1 (A := off S (1 + 2 * H.D)) (b := oBuf) (n := k - 2 * H.D - 1) (by omega_arith)
    (by omega_arith) (fun i hi => by rw [off_off]; exact L1.sld (by omega_arith))
    (fun i hi j hj => by rw [off_off]; exact Offset.add_ofNat_ne S (by omega_arith) (by omega_arith) (by omega_arith))
    x11 x12 (by rw [x13]; congr 1) []) fun u2 ⟨L2, S2, R2⟩ => ⟨L2, S1.trans S2, ?_⟩
  refine (congrArg (fun V' => Rep u2.mem F S V' W) (funext fun x => ?_)).mp R2
  simp only [cpV]
  split
  · rw [off_off, R1.scr _ (by omega_arith)]; rfl
  · rfl

/-! ## One pass of the shift -/

theorem shr1_ofNat {a : Nat} (ha : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 1 = BitVec.ofNat 64 (a / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega_arith)]

/-- The buffer's first `j` bytes replaced by those `d` after them if `b`. -/
def selV (V : Nat → Byte) (d : Nat) (b : Bool) (j : Nat) (x : Nat) : Byte :=
  if oBuf ≤ x ∧ x < oBuf + j then (if b then V (x + d) else V x) else V x

/-- The mask of bit 0 of `a`. -/
def bM (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

theorem neg_and1 (a : BitVec 64) : 0#64 - (a &&& 1) = bM (decide (a.toNat % 2 = 1)) := by
  obtain h : a &&& 1 = BitVec.ofNat 64 (a.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat]
    omega_arith
  rw [h]
  rcases Nat.mod_two_eq_zero_or_one a.toNat with h0 | h1
  · rw [h0]; decide
  · rw [h1]; decide

theorem selWord (x y : BitVec 64) (b : Bool) :
    x ^^^ ((y ^^^ x) &&& bM b) = if b then y else x := by
  cases b
  · simp only [bM, Bool.false_eq_true, ite_false]
    rw [show (y ^^^ x) &&& (0 : BitVec 64) = 0 from BitVec.and_zero,
      show x ^^^ (0 : BitVec 64) = x from BitVec.xor_zero]
  · simp only [bM, ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm y, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem regs4 {P : Reg → Prop} (h17 : P .x17) (h14 : P .x14) (h9 : P .x9) (h8 : P .x8) :
    ∀ r ∈ [Reg.x17, .x14, .x9, .x8], P r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem passBody_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {d j : Nat} {b : Bool} (hj : oBuf + d + j + 8 ≤ oRsa)
    (h11 : u.gpr .x11 = off S (oBuf + j)) (h12 : u.gpr .x12 = off S (oBuf + d + j)) (h15 : u.gpr .x15 = bM b)
    (ws : List Region) :
    WP isa (.block passBody) u fun u' => Lay u' F S ∧ Step F S ws u u' ∧
      Rep u'.mem F S (copy8V V (oBuf + j) (if b then oBuf + d + j else oBuf + j)) W ∧
      u'.gpr .x11 = off S (oBuf + j + 8) ∧ u'.gpr .x12 = off S (oBuf + d + j + 8) ∧ u'.gpr .x15 = bM b ∧
      u'.gpr .x13 = u.gpr .x13 - BitVec.ofNat 64 1 ∧ (∀ r ∈ [Reg.x17, .x14, .x9, .x8], u'.gpr r = u.gpr r) := by
  obtain r1 : InRegions (u.rd ++ u.wr) (off S (oBuf + j)) 8 := L.sld (by omega_arith)
  obtain r2 : InRegions (u.rd ++ u.wr) (off S (oBuf + d + j)) 8 := L.sld (by omega_arith)
  obtain w1 : InRegions u.wr (off S (oBuf + j)) 8 := L.sst (by omega_arith)
  let src := if b then oBuf + d + j else oBuf + j
  obtain hs : src + 8 ≤ oRsa := by dsimp [src]; split <;> omega_arith
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem.writeW (off S (oBuf + j))
      (u.mem.readW (off S src) 64) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧
      (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = off S (oBuf + j) + BitVec.ofNat 64 8 ∧
      u'.gpr .x12 = off S (oBuf + d + j) + BitVec.ofNat 64 8 ∧ u'.gpr .x15 = bM b ∧
      u'.gpr .x13 = u.gpr .x13 - BitVec.ofNat 64 1 ∧ (∀ r ∈ [Reg.x17, .x14, .x9, .x8], u'.gpr r = u.gpr r)) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x15, x13, xk⟩ => ?_
  · cases b <;>
      oaep_run [passBody, h11, h12, h15, BitVec.add_zero, r1, r2, w1, selWord, src, Mem.readW, Mem.writeW,
        Bool.false_eq_true, ite_false, ite_true]
    all_goals and_intros <;> first | trivial | exact cs_rfl | exact regs4 rfl rfl rfl rfl
  obtain R' : Rep u'.mem F S (copy8V V (oBuf + j) src) W := by
    rw [hm]; exact R.copy8 L.geo (by omega_arith) hs
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], ?_⟩, R', x11.trans (off_off S _ 8),
    x12.trans (off_off S _ 8), x15, x13, xk⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]
  · rw [hm]; exact frame_copy8 (by omega_arith)

/-- The pass's loop, eight bytes per iteration. -/
theorem passLoop_ok {u₀ : State} {F S : Addr} (L : Lay u₀ F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u₀.mem F S V W) {d : Nat} {b : Bool} (hd1 : 1 ≤ d) (hd2 : d ≤ 1024)
    (h11 : u₀.gpr .x11 = off S oBuf) (h12 : u₀.gpr .x12 = off S (oBuf + d)) (h15 : u₀.gpr .x15 = bM b)
    (h13 : u₀.gpr .x13 = BitVec.ofNat 64 128) (ws : List Region) :
    WP isa (.loop (.block passBody) (.nonzero .x .x13)) u₀ fun u =>
      Lay u F S ∧ Step F S ws u₀ u ∧ Rep u.mem F S (selV V d b 1024) W ∧
        ∀ r ∈ [Reg.x17, .x14, .x9, .x8], u.gpr r = u₀.gpr r := by
  have c : oRsa = 8192 := rfl
  have cb : oBuf = 1024 := rfl
  refine WP.mono (count_loop (n := 128) (by decide) (fun j u => Lay u F S ∧ Step F S ws u₀ u ∧
      Rep u.mem F S (selV V d b (8 * j)) W ∧ u.gpr .x11 = off S (oBuf + 8 * j) ∧
      u.gpr .x12 = off S (oBuf + d + 8 * j) ∧
      u.gpr .x15 = bM b ∧ u.gpr .x13 = BitVec.ofNat 64 (128 - j) ∧
      ∀ r ∈ [Reg.x17, .x14, .x9, .x8], u.gpr r = u₀.gpr r)
    (fun j hj u ⟨Lu, Su, Ru, u11, u12, u15, u13, uk⟩ => ?_)
    ⟨L, Step.refl _ _ _ _, by
      refine (congrArg (fun V' => Rep _ F S V' _) (funext fun x => ?_)).mp R
      simp only [selV]; rw [ifn (by omega_arith)], by rw [h11]; rfl, by rw [h12]; rfl, h15, h13, fun _ _ => rfl⟩)
    fun u ⟨Lu, Su, Ru, _, _, _, _, uk⟩ => ⟨Lu, Su, Ru, uk⟩
  refine WP.mono (passBody_ok Lu Ru (d := d) (j := 8 * j) (by omega_arith) u11 u12 u15 ws)
    fun u' ⟨L', S', R', x11, x12, x15, x13, xk⟩ => ⟨⟨L', Su.trans S', ?_, ?_, ?_, x15, ?_,
      fun r hr => (xk r hr).trans (uk r hr)⟩, ?_⟩
  · refine (congrArg (fun V' => Rep u'.mem F S V' W) (funext fun x => ?_)).mp R'
    dsimp only [copy8V]
    by_cases hx : oBuf + 8 * j ≤ x ∧ x < oBuf + 8 * j + 8
    · rw [ifp hx]
      cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, selV]
      · rw [ifn (by omega_arith), ifp (by omega_arith)]
        congr 1; omega_arith
      · rw [ifn (by omega_arith), ifp (by omega_arith)]
        congr 1; omega_arith
    · rw [ifn hx]
      simp only [selV]
      obtain he : (oBuf ≤ x ∧ x < oBuf + 8 * j) ↔ (oBuf ≤ x ∧ x < oBuf + 8 * (j + 1)) := by omega_arith
      simp only [he]
  · rw [x11]; congr 1
  · rw [x12]; congr 1
  · rw [x13, u13, counter_step hj (by omega_arith)]
  · rw [x13, u13, counter_step hj (by omega_arith)]; exact counter_ne hj (by omega_arith)

/-- A pass of the shift, by `d` under bit 0 of `a`, and the next pass's `a / 2`, `2 d`, `j - 1`. -/
theorem pass_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {a d j : Nat} (ha : a < 2 ^ 64) (hd1 : 1 ≤ d) (hd2 : d ≤ 1024) (hj : 1 ≤ j)
    (h17 : u.gpr .x17 = off S oBuf) (h14 : u.gpr .x14 = BitVec.ofNat 64 d) (h9 : u.gpr .x9 = BitVec.ofNat 64 a)
    (h8 : u.gpr .x8 = BitVec.ofNat 64 j) :
    WP isa pass u fun u' => Lay u' F S ∧ Step F S [] u u' ∧
      Rep u'.mem F S (selV V d (decide (a % 2 = 1)) 1024) W ∧ u'.gpr .x17 = off S oBuf ∧
      u'.gpr .x14 = BitVec.ofNat 64 (2 * d) ∧ u'.gpr .x9 = BitVec.ofNat 64 (a / 2) ∧
      u'.gpr .x8 = BitVec.ofNat 64 (j - 1) := by
  obtain ha2 : (BitVec.ofNat 64 a).toNat % 2 = a % 2 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  unfold pass
  refine WP.seq (WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = off S oBuf ∧
      u'.gpr .x12 = off S oBuf + BitVec.ofNat 64 d ∧ u'.gpr .x15 = bM (decide (a % 2 = 1)) ∧
      u'.gpr .x13 = BitVec.ofNat 64 128 ∧ u'.gpr .x17 = off S oBuf ∧ u'.gpr .x14 = BitVec.ofNat 64 d ∧
      u'.gpr .x9 = BitVec.ofNat 64 a ∧ u'.gpr .x8 = BitVec.ofNat 64 j) ?_
    fun u1 ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x15, x13, x17, x14, x9, x8⟩ => ?_)
  · oaep_run [mov, h17, h14, h9, h8, BitVec.or_self, show BitVec.setWidth 64 (1 : BitVec 16) <<< 0 = 1 by decide,
      show BitVec.setWidth 64 (0 : BitVec 16) <<< 0 = 0#64 by decide,
      show BitVec.setWidth 64 (128 : BitVec 16) <<< 0 = BitVec.ofNat 64 128 by decide, neg_and1, ha2]
    oaep_fin
  obtain S1 : Step F S [] u u1 := Step.blk _ hrd hwr hsp hv hcs hm
  refine WP.seq (WP.mono (passLoop_ok (L.congr hsp hwr (by rw [hm])) (hm ▸ R) hd1 hd2 x11
    (x12.trans (off_off S oBuf d)) x15 x13 []) fun u2 ⟨L2, S2, R2, k2⟩ => ?_)
  refine WP.mono (Q := fun (u' : State) => u'.mem = u2.mem ∧ u'.rd = u2.rd ∧ u'.wr = u2.wr ∧ u'.sp = u2.sp ∧
      u'.v = u2.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u2.gpr r) ∧ u'.gpr .x17 = u2.gpr .x17 ∧
      u'.gpr .x14 = u2.gpr .x14 + u2.gpr .x14 ∧ u'.gpr .x9 = u2.gpr .x9 >>> 1 ∧
      u'.gpr .x8 = u2.gpr .x8 - BitVec.ofNat 64 1) ?_
    fun u3 ⟨hm3, hrd3, hwr3, hsp3, hv3, hcs3, x17', x14', x9', x8'⟩ => ?_
  · oaep_run []
    oaep_fin
  obtain e17 := k2 .x17 (by simp)
  obtain e14 := k2 .x14 (by simp)
  obtain e9 := k2 .x9 (by simp)
  obtain e8 := k2 .x8 (by simp)
  refine ⟨L2.congr hsp3 hwr3 (by rw [hm3]), S1.trans (S2.trans (Step.blk _ hrd3 hwr3 hsp3 hv3 hcs3 hm3)),
    hm3 ▸ R2, by rw [x17', e17, x17], by rw [x14', e14, x14, BitVec.ofNat_add_ofNat, Nat.two_mul],
    by rw [x9', e9, x9, shr1_ofNat ha], by rw [x8', e8, x8, Offset.ofNat_sub_ofNat hj]⟩

/-! ## The shift -/

/-- The buffer before the shift, as a function of the index: its first 1024
bytes, and zeros after them. -/
def bufB (V : Nat → Byte) (x : Nat) : Byte := if x < 1024 then V (oBuf + x) else 0

/-- Before pass `p` of the shift by `A`. -/
structure ShiftI (u₀ : State) (F S : Addr) (V₀ : Nat → Byte) (W : Nat → BitVec 64) (A p : Nat) (w : State) :
    Prop where
  L : Lay w F S
  st : Step F S [] u₀ w
  x17 : w.gpr .x17 = off S oBuf
  x14 : w.gpr .x14 = BitVec.ofNat 64 (2 ^ p)
  x9 : w.gpr .x9 = BitVec.ofNat 64 (A / 2 ^ p)
  x8 : w.gpr .x8 = BitVec.ofNat 64 (10 - p)
  rep : ∃ V, Rep w.mem F S V W ∧ (∀ i < 2048, V (oBuf + i) = bufB V₀ (i + A % 2 ^ p)) ∧
    (∀ o, ¬ (oBuf ≤ o ∧ o < oBuf + 2048) → V o = V₀ o)

/-- The buffer shifted left by `idx + 1` bytes, in 10 passes. -/
theorem shift_ok {u : State} {F S : Addr} (L : Lay u F S) {V₀ : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V₀ W) {idx : Nat} (hi : W 30 = BitVec.ofNat 64 idx) (hA : idx + 1 < 1024)
    (hz : ∀ x, 1024 ≤ x → x < 2048 → V₀ (oBuf + x) = 0) :
    WP isa shift u fun u' => Lay u' F S ∧ Step F S [] u u' ∧
      ∃ V, Rep u'.mem F S V W ∧ (∀ i < 2048, V (oBuf + i) = bufB V₀ (i + (idx + 1))) ∧
        (∀ o, ¬ (oBuf ≤ o ∧ o < oBuf + 2048) → V o = V₀ o) := by
  have c3 : oBuf = 1024 := rfl
  obtain h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  obtain h240 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 240) 8 := L.ld (d := 240) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  obtain ri := R.rd8 (d := 240) (k := 30) rfl (by decide) hi
  unfold shift
  refine WP.seq (WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x17 = off S oBuf ∧
      u'.gpr .x9 = BitVec.ofNat 64 (idx + 1) ∧ u'.gpr .x14 = BitVec.ofNat 64 1 ∧
      u'.gpr .x8 = BitVec.ofNat 64 10) ?_ fun v ⟨hm, hrd, hwr, hsp, hv, hcs, x17, x9, x14, x8⟩ => ?_)
  · oaep_run [scr, Mgf1.scr, lay, sScr, sIdx, oBuf, h96, h240, L.sp, hs, ri, BitVec.ofNat_add_ofNat,
      show BitVec.setWidth 64 (1 : BitVec 16) <<< 0 = BitVec.ofNat 64 1 by decide,
      show BitVec.setWidth 64 (10 : BitVec 16) <<< 0 = BitVec.ofNat 64 10 by decide]
    oaep_fin
  obtain Lv : Lay v F S := L.congr hsp hwr (by rw [hm])
  obtain I0 : ShiftI u F S V₀ W (idx + 1) 0 v := ⟨Lv, Step.blk _ hrd hwr hsp hv hcs hm, x17, x14,
    by rw [x9, Nat.pow_zero, Nat.div_one], x8, V₀, hm ▸ R,
    fun i hi => by
      simp only [Nat.pow_zero, Nat.mod_one, Nat.add_zero, bufB]
      by_cases h : i < 1024
      · rw [ifp h]
      · rw [ifn h, hz i (by omega_arith) hi], fun _ _ => rfl⟩
  refine WP.mono (count_loop (n := 10) (by decide) (ShiftI u F S V₀ W (idx + 1)) (fun p hp w I => ?_) I0)
    fun w I => ⟨I.L, I.st, ?_⟩
  · obtain ⟨V, Rw, hB, hO⟩ := I.rep
    obtain hp9 : 2 ^ p ≤ 512 := Nat.le_trans (Nat.pow_le_pow_right (by decide) (show p ≤ 9 by omega_arith))
      (by decide : 2 ^ 9 ≤ 512)
    have hp0 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
    refine WP.mono (pass_ok I.L Rw (a := (idx + 1) / 2 ^ p) (d := 2 ^ p) (j := 10 - p)
      (by have := Nat.div_le_self (idx + 1) (2 ^ p); omega_arith) hp0 (by omega_arith) (by omega_arith) I.x17 I.x14 I.x9 I.x8)
      fun w2 ⟨L2, S2, R2, x17, x14, x9, x8⟩ => ⟨⟨L2, I.st.trans S2, x17,
        by rw [x14, Nat.pow_succ, Nat.mul_comm], by rw [x9, Nat.pow_succ, Nat.div_div_eq_div_mul],
        by rw [x8]; congr 1, _, R2, fun i hi => ?_, fun o ho => ?_⟩, ?_⟩
    · simp only [selV]
      rw [Nat.mod_pow_succ]
      by_cases hi' : i < 1024
      · rw [ifp (show oBuf ≤ oBuf + i ∧ oBuf + i < oBuf + 1024 by omega_arith)]
        rcases Nat.mod_two_eq_zero_or_one ((idx + 1) / 2 ^ p) with h0 | h1
        · rw [h0, show decide (0 = 1) = false from rfl]
          simp only [Bool.false_eq_true, ite_false, Nat.mul_zero, Nat.add_zero]
          exact hB i hi
        · rw [h1, show decide (1 = 1) = true from rfl]
          simp only [ite_true, Nat.mul_one]
          rw [show oBuf + i + 2 ^ p = oBuf + (i + 2 ^ p) by omega_arith, hB (i + 2 ^ p) (by omega_arith)]
          congr 1; omega_arith
      · rw [ifn (show ¬ (oBuf ≤ oBuf + i ∧ oBuf + i < oBuf + 1024) by omega_arith), hB i hi, bufB, bufB,
          ifn (show ¬ (i + (idx + 1) % 2 ^ p < 1024) by omega_arith),
          ifn (show ¬ (i + ((idx + 1) % 2 ^ p + 2 ^ p * ((idx + 1) / 2 ^ p % 2)) < 1024) by omega_arith)]
    · have ho' : ¬ (oBuf ≤ o ∧ o < oBuf + 1024) := fun h => ho ⟨h.1, by omega_arith⟩
      unfold selV; rw [ifn ho']; exact hO o ho
    · rw [x8, show 10 - p - 1 = 10 - (p + 1) by omega_arith]; exact counter_ne hp (by omega_arith)
  · obtain ⟨V, Rw, hB, hO⟩ := I.rep
    refine ⟨V, Rw, fun i hi => ?_, hO⟩
    rw [hB i hi, Nat.mod_eq_of_lt (show idx + 1 < 2 ^ 10 by omega_arith)]

end VG.Proof.RsaOaep.AArch64

end

end


/-!
# RSAES-OAEP decryption on AArch64: the decoding

As on x86-64 (`Proof/RsaOaep/X86_64/DecMain.lean`): `decMain`
(`decMain_ok`), from `EM` in our working space and the private-key
operation's result in its slot, hashes the label, unmasks the seed and `DB`,
compares `lHash'`, scans, copies and shifts `T`, and writes the message
under the mask `ok` to `out` and its length to `*msg_len`: what
`Spec.RsaOaep.decrypt` writes for the operation's outcome.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)
open VG.Impl.Pbkdf2.Md.AArch64 (Stream)

theorem andB_ones (b : Byte) : andB b (BitVec.allOnes 64) = b := by
  simp only [andB, BitVec.and_allOnes]; exact byte_rt64 b

theorem andB_zero (b : Byte) : andB b 0 = 0 := by
  simp only [andB]; rw [show BitVec.setWidth 64 b &&& 0 = 0 from BitVec.and_zero]; rfl

/-- The private-key operation's result in its slot (word 28), and `EM` in
our working space. -/
def ResD (V : Nat → Byte) (W : Nat → BitVec 64) (k : Nat) : Spec.Rsa.Outcome → Prop
  | .ok em => W 28 = 1 ∧ (List.range k).map (fun i => V (oEm + i)) = em
  | .invalid => W 28 = 0
  | .fault => W 28 = 2

/-- Where `out` and `*msg_len` are: in their slots, writable, and apart
from the frame, our working space and each other. -/
structure OutAt (u : State) (F S : Addr) (W : Nat → BitVec 64) (o ml : Addr) (k : Nat) : Prop where
  ho : W 19 = o
  hml : W 27 = ml
  hw : Covers [⟨o, k⟩] u.wr
  hwm : Covers [⟨ml, 8⟩] u.wr
  hnw : o.toNat + k ≤ 2 ^ 64
  ha : Apart F S ⟨o, k⟩
  ham : Apart F S ⟨ml, 8⟩
  hom : Region.Disjoint ⟨o, k⟩ ⟨ml, 8⟩

theorem OutAt.congr {u u' : State} {F S : Addr} {W W' : Nat → BitVec 64} {o ml : Addr} {k : Nat}
    (h : OutAt u F S W o ml k) (hwr : u'.wr = u.wr) (h19 : W' 19 = W 19) (h27 : W' 27 = W 27) :
    OutAt u' F S W' o ml k :=
  ⟨h19.trans h.ho, h27.trans h.hml, hwr ▸ h.hw, hwr ▸ h.hwm, h.hnw, h.ha, h.ham, h.hom⟩

theorem Step.nil {F S : Addr} {ws : List Region} {t t' : State} (h : Step F S [] t t') : Step F S ws t t' :=
  h.weaken fun _ h => absurd h List.not_mem_nil

variable {Hl : Hash} {Gm : Stream} (hH : StreamOK Hl.stream) (hG : StreamOK Gm) {f : Fns}

include hH hG in
theorem decMain_ok {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D)
    (hGv : Proof.Mgf1.Valid Gs) {u : State} {F S pL p : Addr} (TL : Table.Tab Hl.stream f F S pL (arg 15) u)
    (T : Table.Tab Gm f F S p (arg 16) u) (L : Lay u F S)
    {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem F S V W) (hpL : W 32 = pL) {k : Nat} (hk : W 21 = BitVec.ofNat 64 k)
    (hD : 2 * Hl.D + 2 ≤ k) (hk' : k ≤ 1024) {lab : Addr} {labLen : Nat} (A : LabAt u F S W lab labLen)
    {o ml : Addr} (O : OutAt u F S W o ml k) {res : Spec.Rsa.Outcome} (hres : ResD V W k res) :
    WP isa (decMain Hl f) u fun u' => Lay u' F S ∧ Step F S [⟨o, k⟩, ⟨ml, 8⟩] u u' ∧
      Spec.RsaOaep.writtenDecrypt u'.mem o ml k ((u'.gpr .x0).setWidth 32)
        (decOut Hs Gs (Spec.Rsa.bytesAt u.mem lab labLen) res) := by
  obtain ⟨-, hzF, -, hzDF, hD0⟩ := sizes hH
  obtain hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  replace hD0 : 0 < Hl.D := hD0
  have cSt : oSt = 3072 := rfl
  have cR : oRsa = 8192 := rfl
  unfold decMain seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- The label's hash.
  refine WP.seq (WP.mono (Table.wp_sy (hashLabelT_ok hH hHh TL L R hpL A (Or.inr rfl)))
    fun u1 ⟨⟨L1, S1, V1, R1, hV1, hV1'⟩, sy1⟩ => ?_)
  -- The seed unmasked.
  refine WP.seq (WP.mono (Table.wp_sy (seedArgs_ok L1 R1 hk hD (by omega_using [hD64]) hk' [])) fun u2 ⟨⟨L2, S2, R2⟩, sy2⟩ => ?_)
  obtain f2 : MFit (1 + Hl.D) (k - Hl.D - 1) 1 Hl.D :=
    ⟨by rw [cSt]; omega_using [hk', hD64], by rw [cSt]; omega_using [hD64], by omega_using [], by omega_using [hD0], by omega_using [hD64]⟩
  obtain T2 := (T.step S1 sy1).step S2 sy2
  refine WP.seq (WP.mono (Table.wp_sy (Table.mgfXorT_ok hG hGh hGl hGv (by decide) T2 L2 R2 f2 (mW_args _ _ _ _ _ _)))
    fun u3 ⟨⟨L3, S3, V3, W3, R3, hW3, hV3⟩, sy3⟩ => ?_)
  obtain W3e : ∀ j < 32, (j < 13 ∨ 18 < j) → W3 j = W j := fun j hj h =>
    (hW3 j (by unfold nW frameBytes; omega_using [hj]) (by omega_using [h]) (by omega_using [h]) (by omega_using [hj])
      (by omega_using [hj])).trans (mW_eq _ _ _ _ _ _ (by omega_using [h]))
  -- `DB` unmasked.
  refine WP.seq (WP.mono (Table.wp_sy (dbArgs_ok L3 R3 ((W3e 21 (by decide) (by omega_using [])).trans hk) hD
      (by omega_using [hD64]) hk' []))
    fun u4 ⟨⟨L4, S4, R4⟩, sy4⟩ => ?_)
  obtain f4 : MFit 1 Hl.D (1 + Hl.D) (k - Hl.D - 1) :=
    ⟨by rw [cSt]; omega_using [hD64], by rw [cSt]; omega_using [hk', hD64], by omega_using [], by omega_using [hD], by omega_using [hk']⟩
  obtain T4 := (T2.step S3 sy3).step S4 sy4
  refine WP.seq (WP.mono (Table.mgfXorT_ok hG hGh hGl hGv (by decide) T4 L4 R4 f4 (mW_args _ _ _ _ _ _))
    fun u5 ⟨L5, S5, V5, W5, R5, hW5, hV5⟩ => ?_)
  obtain W5e : ∀ j < 32, (j < 13 ∨ 18 < j) → W5 j = W j := fun j hj h =>
    (hW5 j (by unfold nW frameBytes; omega_using [hj]) (by omega_using [h]) (by omega_using [h]) (by omega_using [hj])
      (by omega_using [hj])).trans ((mW_eq _ _ _ _ _ _ (by omega_using [h])).trans (W3e j hj h))
  -- `lHash'` against `lHash`, and the scan.
  refine WP.seq (WP.mono (accLh_ok L5 R5 (by omega_using [hD64]) hD0) fun u6 ⟨L6, S6, R6⟩ => ?_)
  obtain w6k : upd W5 29 (accL V5 Hl.D Hl.D) 21 = BitVec.ofNat 64 k := by
    simp only [upd]; rw [ifn (by decide)]; exact (W5e 21 (by decide) (by omega_using [])).trans hk
  refine WP.seq (WP.mono (scan_ok L6 R6 w6k hD hk') fun u7 ⟨L7, S7, R7⟩ => ?_)
  generalize hsc : scanS (tF V5 Hl.D) (upd W5 29 (accL V5 Hl.D Hl.D) 29) (k - 2 * Hl.D - 1) = sc at R7
  obtain ⟨W7, R7, w7e, w729, w730⟩ : ∃ W7, Rep u7.mem F S V5 W7 ∧ (∀ j, j ≠ 29 → j ≠ 30 → W7 j = W5 j) ∧
      W7 29 = sc.2.2 ||| sc.1 ∧ W7 30 = sc.2.1 :=
    ⟨_, R7, fun j h1 h2 => by simp only [upd, ifn h1, ifn h2], by simp [upd], by simp [upd]⟩
  obtain W7e : ∀ j < 32, (j < 13 ∨ 18 < j) → j ≠ 29 → j ≠ 30 → W7 j = W j := fun j hj h h1 h2 =>
    (w7e j h1 h2).trans (W5e j hj h)
  obtain w7k : W7 21 = BitVec.ofNat 64 k := (W7e 21 (by decide) (by omega_using []) (by omega_using []) (by omega_using [])).trans hk
  -- The buffer.
  refine WP.seq (WP.mono (clearBuf_ok L7 R7) fun u8 ⟨L8, S8, R8⟩ => ?_)
  refine WP.seq (WP.mono (copyT_ok L8 R8 w7k hD hk') fun u9 ⟨L9, S9, R9⟩ => ?_)
  -- The shift.
  obtain ⟨idx, hidx, hidx'⟩ := scan_idx (tF V5 Hl.D) (upd W5 29 (accL V5 Hl.D Hl.D) 29) (k - 2 * Hl.D - 1)
  rw [hsc] at hidx
  refine WP.seq (WP.mono (shift_ok L9 R9 (idx := idx) (w730.trans hidx) (by omega_using [hk', hidx']) fun x h1 h2 => by
      simp only [cpV, zV]
      rw [ifn (by omega_using [hk', h1]), ifp (by omega_using [h2])])
    fun u10 ⟨L10, S10, V10, R10, hB10, _⟩ => ?_)
  -- `ok`.
  refine WP.seq (WP.mono (okMask_ok L10 R10) fun u11 ⟨L11, S11, R11⟩ => ?_)
  obtain W11e : ∀ j < 32, (j < 13 ∨ 18 < j) → j ≠ 29 → j ≠ 30 → j ≠ 31 → upd W7 31 (okW W7) j = W j :=
    fun j hj h h1 h2 h3 => by simp only [upd, ifn h3]; exact W7e j hj h h1 h2
  obtain S11 : Step F S [] u u11 := S1.trans (S2.trans (S3.trans (S4.trans (S5.trans (S6.trans (S7.trans
    (S8.trans (S9.trans (S10.trans S11)))))))))
  obtain O11 : OutAt u11 F S (upd W7 31 (okW W7)) o ml k :=
    O.congr S11.wr (W11e 19 (by decide) (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using []))
      (W11e 27 (by decide) (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using []))
  obtain w11k : upd W7 31 (okW W7) 21 = BitVec.ofNat 64 k :=
    (W11e 21 (by decide) (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using [])).trans hk
  -- `out`.
  refine WP.seq (WP.mono (outLoop_ok L11 R11 O11.ho w11k (by omega_using [hD]) hk' O11.hw O11.hnw O11.ha)
    fun u12 ⟨L12, S12, R12, ho12⟩ => ?_)
  -- The length and the result.
  refine WP.mono (decRet_ok L12 R12 O11.hml w11k (by omega_using [hD64]) (S12.wr ▸ O11.hwm) O11.ham)
    fun u13 ⟨L13, S13, _, hml13, hx13⟩ => ?_
  refine ⟨L13, (S11.nil.trans (S12.weaken fun r h => by
    rw [List.mem_singleton.mp h]; exact List.mem_cons_self ..)).trans (S13.weaken fun r h => by
    rw [List.mem_singleton.mp h]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)), ?_⟩
  -- The bytes: `EM` unmasked, `lHash`, `T` and the buffer.
  obtain hlhl : (Hs.hash (Spec.Rsa.bytesAt u.mem lab labLen)).length = Hl.D := by rw [hHv.2, hHl]
  obtain e28 : upd W7 31 (okW W7) 28 = W 28 := W11e 28 (by decide) (by omega_using []) (by omega_using [])
      (by omega_using []) (by omega_using [])
  obtain e31 : upd W7 31 (okW W7) 31 = zM (sc.2.2 ||| sc.1) &&& zM (W 28 ^^^ 1) := by
    simp only [upd, ite_true, okW]
    rw [w729, W7e 28 (by decide) (by omega_using []) (by omega_using []) (by omega_using [])]
  obtain e30 : upd W7 31 (okW W7) 30 = BitVec.ofNat 64 idx := by
    simp only [upd]; rw [ifn (by decide), w730, hidx]
  rw [e31, e30] at hml13
  rw [e31] at ho12 hx13
  simp only [fltW, e28] at hx13
  generalize hDD : Hl.D = D at *
  obtain nl : ∀ x, x < oSt → ¬ inR (labR oLh) x := fun x hx => by
    simp only [labR, inR_cons, inR_nil, or_false]; unfold oSt oLh oW at *; omega_using [hx]
  obtain v1 : ∀ x < k, V1 x = V x := fun x hx => hV1 x (nl x (by omega_using [hk', cSt, hx]))
  obtain v3 : ∀ x < k, V3 x = mixV V1 (Spec.Mgf1.mgf1 Gs (srcB V1 (1 + D) (k - (D + 1))) D) 1 D x :=
    fun x hx => by
      rw [hV3 x (by omega_using [hk', cR, hx]) ((mOut_iff x).mpr (.inl (by omega_using [hk', cSt, hx]))),
          show k - D - 1 = k - (D + 1) by omega_using []]
  obtain v5 : ∀ x < k, V5 x = mixV V3 (Spec.Mgf1.mgf1 Gs (srcB V3 1 D) (k - (D + 1))) (1 + D) (k - (D + 1)) x :=
    fun x hx => by
      rw [hV5 x (by omega_using [hk', cR, hx]) ((mOut_iff x).mpr (.inl (by omega_using [hk', cSt, hx]))),
          show k - D - 1 = k - (D + 1) by omega_using []]
  obtain hc5 := chain_eq (by omega_using [hD]) v1 v3 v5
  obtain lh5 : ∀ i < D, V5 (oLh + i) = (Hs.hash (Spec.Rsa.bytesAt u.mem lab labLen)).getD i 0 := fun i hi => by
    obtain mo : mOut (oLh + i) := (mOut_iff _).mpr (.inr (.inl (by unfold oLh oDig oCtr; omega_using [hD64, hi])))
    rw [hV5 _ (by unfold oLh; omega_using [cR, hD64, hi]) mo, mixV, ifn (by unfold oLh; omega_using [hk']),
      hV3 _ (by unfold oLh; omega_using [cR, hD64, hi]) mo, mixV, ifn (by unfold oLh; omega_using [hD64]), hV1' i hi]
  -- `T` and the scan.
  obtain hTl : (srcB V5 (1 + 2 * D) (k - 2 * D - 1)).length = k - 2 * D - 1 := by simp [srcB]
  obtain hTg : ∀ i < k - 2 * D - 1, (srcB V5 (1 + 2 * D) (k - 2 * D - 1)).getD i 0 = tF V5 D i := fun i hi => by
    rw [srcB, map_range_getD' _ hi]; rfl
  obtain hsc2 : sc = scanS (fun i => (srcB V5 (1 + 2 * D) (k - 2 * D - 1)).getD i 0) (accL V5 D D)
      (srcB V5 (1 + 2 * D) (k - 2 * D - 1)).length := by
    rw [← hsc, hTl, show upd W5 29 (accL V5 D D) 29 = accL V5 D D by simp [upd]]
    exact scanS_congr _ _ fun i hi => (hTg i hi).symm
  generalize hT : srcB V5 (1 + 2 * D) (k - 2 * D - 1) = T at *
  -- The outputs.
  obtain hbuf : ∀ x, bufB (cpV (zV V5 oBuf 2048) oBuf (k - 2 * D - 1) (tF (zV V5 oBuf 2048) D)) x =
      T.getD x 0 := fun x => by
    obtain hge : ∀ y, k - 2 * D - 1 ≤ y → T.getD y 0 = 0 := fun y hy => by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show T.length ≤ y by omega_using [hTl, hy])]
    unfold bufB
    by_cases hx : x < 1024
    · rw [ifp hx, cpV]
      by_cases hxt : x < k - 2 * D - 1
      · rw [ifp (by unfold oBuf; omega_using [hxt]), hTg x hxt, show oBuf + x - oBuf = x by omega_using [], tF, tF, zV,
          ifn (by unfold oBuf; omega_using [hk', hxt])]
      · rw [ifn (by unfold oBuf; omega_using [hxt]), zV, ifp (by unfold oBuf; omega_using [hx]), hge x (by omega_using [hxt])]
    · rw [ifn hx, hge x (by omega_using [hk', hx])]
  obtain dO : ∀ r ∈ (⟨F, frameBytes⟩ :: ⟨S, oRsa⟩ :: retR F :: [⟨ml, 8⟩] : List Region),
      Region.Disjoint ⟨o, k⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [O.ha.dF, O.ha.dS, O.ha.dK, O.hom]
  obtain hout : ∀ i < k, u13.mem (o + BitVec.ofNat 64 i) =
      andB (T.getD (i + (idx + 1)) 0) (zM (sc.2.2 ||| sc.1) &&& zM (W 28 ^^^ 1)) := fun i hi =>
    (S13.frame.bytes (R := ⟨o, k⟩) dO (by show k ≤ 2 ^ 64; omega_using [hk']) hi).trans
      ((ho12 i hi).trans (by rw [hB10 i (by omega_using [hk', hi]), hbuf]))
  -- The accumulator.
  obtain ⟨i1, -, -, i4⟩ := scanS_inv (fun i => T.getD i 0) (accL V5 D D) T.length
  rw [← hsc2] at i1 i4
  obtain hacc : sc.2.2 ||| sc.1 = 0 ↔
      accL V5 D D = 0 ∧ ¬ bad (fun i => T.getD i 0) T.length ∧ ¬ lk (fun i => T.getD i 0) T.length := by
    rw [i4, i1, or_eq_zero, or_eq_zero, mk_eq_zero, mk_eq_zero, and_assoc]
  obtain zero_out : zM (sc.2.2 ||| sc.1) &&& zM (W 28 ^^^ 1) = 0 →
      Spec.Rsa.bytesAt u13.mem o k = Spec.RsaOaep.zeros k ∧ u13.mem.readW ml 64 = 0 ∧
      (u13.gpr .x0).setWidth 32 = (zM (W 28 ^^^ 2) &&& 2).setWidth 32 := fun h0 =>
    ⟨out_zero fun i hi => by rw [hout i hi, h0, andB_zero], by rw [hml13, h0]; exact BitVec.and_zero,
      by rw [hx13, h0, show (0 : BitVec 64) &&& 1 = 0 by decide,
        show ∀ x : BitVec 64, x ||| 0 = x from fun x => by simp]⟩
  cases res with
  | fault =>
    have h2 : W 28 = 2 := hres
    obtain ⟨a, b, c⟩ := zero_out (by rw [h2, show zM ((2 : BitVec 64) ^^^ 1) = 0 by decide]; exact BitVec.and_zero)
    exact ⟨by rw [c, h2]; decide, a, b⟩
  | invalid =>
    have h0 : W 28 = 0 := hres
    obtain ⟨a, b, c⟩ := zero_out (by rw [h0, show zM ((0 : BitVec 64) ^^^ 1) = 0 by decide]; exact BitVec.and_zero)
    exact ⟨by rw [c, h0]; decide, a, b⟩
  | ok em =>
    obtain ⟨h1, hem⟩ := hres
    subst hem
    have c0 : oEm = 0 := rfl
    obtain hV : (fun i => V (oEm + i)) = V := funext fun i => by rw [c0, Nat.zero_add]
    rw [hV]
    obtain hok : zM (sc.2.2 ||| sc.1) &&& zM (W 28 ^^^ 1) = zM (sc.2.2 ||| sc.1) := by
      rw [h1, show zM ((1 : BitVec 64) ^^^ 1) = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    obtain hf2 : zM (W 28 ^^^ 2) &&& 2 = 0 := by rw [h1]; decide
    rw [hok] at zero_out hout hml13 hx13
    rw [hf2, show ∀ x : BitVec 64, 0 ||| x = x from fun x => by simp] at hx13
    simp only [decOut]
    rw [decode_eq hGv _ (by omega_using [hD]) hHl hc5, show k - (2 * D + 1) = k - 2 * D - 1 by omega_using [], hT]
    obtain hz : ∀ (hne : sc.2.2 ||| sc.1 ≠ 0), _ := fun hne => zero_out (by simp only [zM]; rw [ifn hne])
    by_cases hfd : ¬ lk (fun i => T.getD i 0) T.length ∧ ¬ bad (fun i => T.getD i 0) T.length
    · obtain ⟨j₀, hj₀, hsj, hdw⟩ := scan_found T (accL V5 D D) hfd.1 hfd.2
      rw [← hsc2] at hsj
      obtain hij : idx = j₀ := by
        have := hidx.symm.trans hsj
        have := congrArg BitVec.toNat this
        rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk', hidx']),
          Nat.mod_eq_of_lt (by omega_using [hk', hTl, hj₀])] at this
      subst hij
      rw [hdw, show (1 : Byte) = 1#8 from rfl]
      simp only []
      obtain hV0 : V5 0 = V 0 := by
        rw [hc5 0 (by omega_using [hTl, hj₀]), mixV, ifn (by omega_using []), mixV, ifn (by omega_using [])]
      obtain htake : ((List.range k).map V).take 1 = [V 0] := by
        rw [show k = (k - 1) + 1 by omega_using [hTl, hj₀], List.range_succ_eq_map]; simp
      by_cases hc : ((List.range k).map V).take 1 = [0x00] ∧ srcB V5 (1 + D) D =
          Hs.hash (Spec.Rsa.bytesAt u.mem lab labLen)
      · rw [ifp hc]
        obtain hacc0 : sc.2.2 ||| sc.1 = 0 := hacc.mpr ⟨(accG_eq_zero _ _ _ D).mpr ⟨by
            rw [c0, hV0]; rw [htake] at hc; exact List.head_eq_of_cons_eq hc.1, fun i hi => by
            show V5 (oLh + i) = V5 (1 + D + i)
            rw [lh5 i hi, ← hc.2, srcB, map_range_getD' _ hi]⟩, hfd.2, hfd.1⟩
        obtain hzm : zM (sc.2.2 ||| sc.1) = BitVec.allOnes 64 := by simp only [zM]; rw [ifp hacc0]
        rw [hzm] at hout hml13 hx13
        refine ⟨by rw [hx13]; decide, out_list (by omega_using [hTl]) hj₀ fun i hi => by rw [hout i hi, andB_ones], ?_⟩
        rw [hml13, BitVec.and_allOnes, VG.Offset.ofNat_sub_ofNat (by omega_arith), VG.Offset.ofNat_sub_ofNat (by omega_using [hTl, hj₀]),
          List.length_drop]
        congr 1; omega_using [hTl]
      · rw [ifn hc]
        obtain hne : sc.2.2 ||| sc.1 ≠ 0 := fun h0 => by
          obtain ⟨e0, e1⟩ := (accG_eq_zero _ _ _ D).mp (hacc.mp h0).1
          refine hc ⟨by rw [htake, ← hV0, show (0 : Nat) = oEm from rfl, e0], ?_⟩
          refine srcB_eq hlhl fun i hi => ?_
          rw [← lh5 i hi]; exact (e1 i hi).symm
        obtain ⟨a, b, c⟩ := hz hne
        exact ⟨by rw [c, hf2]; rfl, a, b⟩
    · have hfail := scan_fail T (by
        by_contra hc; exact hfd ⟨fun h => hc (.inl h), fun h => hc (.inr h)⟩)
      obtain hne : sc.2.2 ||| sc.1 ≠ 0 := fun h0 => hfd ⟨(hacc.mp h0).2.2, (hacc.mp h0).2.1⟩
      obtain ⟨a, b, c⟩ := hz hne
      split
      · rename_i m heq
        split at heq
        · rename_i m' hm; exact absurd hm (hfail m')
        · cases heq
      · exact ⟨by rw [c, hf2]; rfl, a, b⟩

end VG.Proof.RsaOaep.AArch64
