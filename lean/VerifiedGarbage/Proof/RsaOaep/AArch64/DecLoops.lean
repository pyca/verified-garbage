import VerifiedGarbage.Proof.RsaOaep.AArch64.Args

/-!
# RSAES-OAEP decryption on AArch64: the loops of the decoding

As on x86-64 (`Proof/RsaOaep/X86_64/DecLoops.lean`), each loop of `decMain`
after MGF1, as a function of the working space's bytes (`V`) and the
frame's words: the comparison of `lHash'` with `lHash` (`accLh_ok`, the
`accG` of `Proof/RsaOaep/Scan.lean`), the scan of `T` (`scan_ok`,
`scanS`), the buffer cleared (`clearBuf_ok`), `T` copied to it
(`copyT_ok`), the shift (`shift_ok`), and `out` (`outLoop_ok`).
-/

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
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have r0 : InRegions (u.rd ++ u.wr) S 1 := by simpa [off] using L.sld (o := 0) (n := 1) (by decide)
  have v0 : u.mem S = V oEm := by simpa [off, oEm] using R.scr 0 (by decide)
  oaep_run [scr, Mgf1.scr, lay, sScr, oLh, oEm, h96, L.sp, hs, show 1 + H.D < 4096 by omega,
    show 0 + 1 + H.D = 1 + H.D by omega, BitVec.add_zero, r0, read_one, v0, byte64, imm16 (show H.D < 65536 by omega)]
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
  have r1 : InRegions (u.rd ++ u.wr) (off S (oLh + j)) 1 := L.sld (by unfold oLh oRsa; omega)
  have r2 : InRegions (u.rd ++ u.wr) (off S (1 + D + j)) 1 := L.sld (by unfold oRsa; omega)
  have v1 : u.mem (off S (oLh + j)) = V (oLh + j) := R.scr _ (by unfold oLh oRsa; omega)
  have v2 : u.mem (off S (1 + D + j)) = V (1 + D + j) := R.scr _ (by unfold oRsa; omega)
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
      x11.trans (off_off S _ 1), x12.trans (off_off S _ 1), by rw [x13, I.x13, counter_step hj (by omega)],
      by rw [x14, I.x14]; rfl⟩, by rw [x13, I.x13, counter_step hj (by omega)]; exact counter_ne hj (by omega)⟩) h

/-- A register `r` to the frame's word `k` (`d = 8 k`), through `x9 = sp`. -/
theorem stSlot_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (r : Reg) (hr : r ≠ .x9) {d k : Nat} (hd : d = 8 * k) (hk : 13 ≤ k ∧ k < nW)
    (ws : List Region) :
    WP isa (.block [.addSp .x9 0, .str .x r .x9 d]) u fun u' => Lay u' F S ∧ Step F S ws u u' ∧
      Rep u'.mem F S V (upd W k (u.gpr r)) ∧ ∀ q, q ≠ .x9 → u'.gpr q = u.gpr q := by
  subst hd
  have hk' : 8 * k + 8 ≤ frameBytes := by unfold nW frameBytes at *; omega
  have w : InRegions u.wr (F + BitVec.ofNat 64 (8 * k)) 8 := L.st hk'
  have R' : Rep (u.mem.write (off F (8 * k)) 8 (u.gpr r)) F S V (upd W k (u.gpr r)) := R.wq L.geo hk.2 _
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem.write (off F (8 * k)) 8 (u.gpr r) ∧ u'.rd = u.rd ∧
      u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧ ∀ q, q ≠ .x9 → u'.gpr q = u.gpr q) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hg⟩ => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.store, addr, Size.bits,
      Size.bytes, BitVec.setWidth_eq, Nat.reduceMul, Nat.mul_mod_right, and_self, ite_true,
      Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
      RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write, L.sp, BitVec.add_zero, w, hr, ite_false,
      show 8 * k < 32768 by unfold nW frameBytes at hk; omega, show (0 : Nat) < 4096 by decide]
    and_intros <;> first | trivial | (intro q hq; simp [hq])
  have R'' : Rep u'.mem F S V (upd W k (u.gpr r)) := by rw [hm]; exact R'
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, fun q _ hq => hg q (by rintro rfl; simp [preserved] at *), fun q _ => by
    rw [hv], by rw [hm]; exact Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF F hk')⟩, R'', hg⟩
  rw [show sScr = 8 * 12 from rfl, R''.fr 12 (by decide), R.fr 12 (by decide), upd, ifn (by omega)]

theorem accLh_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {H : Hash} (hD : H.D < 1024) (hD0 : 0 < H.D) :
    WP isa (accLh H) u fun u' => Lay u' F S ∧ Step F S [] u u' ∧ Rep u'.mem F S V (upd W 29 (accL V H.D H.D)) := by
  refine WP.seq (WP.mono (accHead_ok L R hD []) fun u1 ⟨S1, hm1, x11, x12, x13, x14⟩ => ?_)
  have L1 : Lay u1 F S := L.congr S1.sp S1.wr (by rw [hm1])
  have R1 : Rep u1.mem F S V W := hm1 ▸ R
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
  have r1 : InRegions (u.rd ++ u.wr) (off S (1 + 2 * D + j)) 1 := L.sld (by omega)
  have v1 : u.mem (off S (1 + 2 * D + j)) = tF V D j := R.scr _ hj
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
  refine WP.mono (scanBody_ok I.L (I.mem ▸ R) (j := j) (by omega) I.x11 I.x17 [])
    fun u' ⟨S', hm, x11, x12, x9, x17, x13, x8, x14⟩ => ⟨⟨I.L.congr S'.sp S'.wr (by rw [hm]), I.st.trans S',
      hm.trans I.mem, x11.trans (off_off S _ 1), by rw [x12, I.x12, counter_step hj (by omega)],
      by rw [x9, I.x9, BitVec.ofNat_add_ofNat], x17, ?_, ?_, ?_⟩, ?_⟩
  · rw [x13, I.x13, scanS, ← BitVec.xor_allOnes]
  · rw [x8, I.x8, I.x9, I.x13, scanS]
  · rw [x14, I.x14, I.x13, scanS, ← BitVec.xor_allOnes, BitVec.and_comm (scanS (tF V D) c₀ j).1]
  · rw [x12, I.x12, counter_step hj (by omega)]; exact counter_ne hj (by omega)

theorem scanHead_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {H : Hash} {k : Nat} (hk : W 21 = BitVec.ofNat 64 k) (hD : 2 * H.D + 2 ≤ k)
    (hk' : k ≤ 1024) :
    WP isa (.block (tArgs H ++ ([.movz .x .x13 0 0, .subImm .x .x13 .x13 1, .movz .x .x8 0 0, .ldrSp .x14 sAcc,
      .movz .x .x9 0 0, .movz .x .x17 1 0] : List Instr))) u
      (ScanI u F S V W H.D (k - 2 * H.D - 1) (W 29) 0) := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have h232 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 232) 8 := L.ld (d := 232) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have rk := R.rdK hk
  have ra := R.rd8 (d := 232) (k := 29) rfl (by decide) rfl
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = off S (1 + 2 * H.D) ∧
      u'.gpr .x12 = BitVec.ofNat 64 (k - (2 * H.D + 1)) ∧ u'.gpr .x9 = BitVec.ofNat 64 0 ∧ u'.gpr .x17 = 1 ∧
      u'.gpr .x13 = BitVec.allOnes 64 ∧ u'.gpr .x8 = 0 ∧ u'.gpr .x14 = W 29) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x9, x17, x13, x8, x14⟩ =>
      ⟨L.congr hsp hwr (by rw [hm]), Step.blk _ hrd hwr hsp hv hcs hm, hm, x11, by rw [x12]; congr 1, x9, x17, x13,
        x8, x14⟩
  oaep_run [tArgs, scr, Mgf1.scr, lay, sScr, sK, sAcc, oEm, h96, h168, h232, L.sp, hs, rk, ra,
    Nat.zero_add, show 1 + 2 * H.D < 4096 by omega, show 2 * H.D + 1 < 4096 by omega,
    Offset.ofNat_sub_ofNat (show 2 * H.D + 1 ≤ k by omega)]
  oaep_fin

theorem scanTail_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (ws : List Region) :
    WP isa (.block [.logic .orr .x .x14 .x14 .x13, .addSp .x9 0, .str .x .x14 .x9 sAcc, .str .x .x8 .x9 sIdx]) u
      fun u' => Lay u' F S ∧ Step F S ws u u' ∧
        Rep u'.mem F S V (upd (upd W 29 (u.gpr .x14 ||| u.gpr .x13)) 30 (u.gpr .x8)) := by
  have G' := L.geo
  have R2 : Rep ((u.mem.write (off F 232) 8 (u.gpr .x14 ||| u.gpr .x13)).write (off F 240) 8 (u.gpr .x8)) F S V
      (upd (upd W 29 (u.gpr .x14 ||| u.gpr .x13)) 30 (u.gpr .x8)) :=
    (R.wq G' (k := 29) (by decide) _).wq G' (k := 30) (by decide) _
  have w232 : InRegions u.wr (F + BitVec.ofNat 64 232) 8 := L.st (d := 232) (by decide)
  have w240 : InRegions u.wr (F + BitVec.ofNat 64 240) 8 := L.st (d := 240) (by decide)
  refine WP.mono (Q := fun (u' : State) => u'.mem = (u.mem.write (off F 232) 8 (u.gpr .x14 ||| u.gpr .x13)).write
      (off F 240) 8 (u.gpr .x8) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧
      (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r)) ?_ fun u' ⟨hm, hrd, hwr, hsp, hv, hcs⟩ => ?_
  · oaep_run [sAcc, sIdx, w232, w240, L.sp, BitVec.add_zero]
    oaep_fin
  have R' : Rep u'.mem F S V (upd (upd W 29 (u.gpr .x14 ||| u.gpr .x13)) 30 (u.gpr .x8)) := by rw [hm]; exact R2
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
  refine WP.seq (WP.mono (scanLoop_ok R (by unfold oRsa; omega) (by omega) I) fun u2 I2 => ?_)
  refine WP.mono (scanTail_ok I2.L (I2.mem ▸ R) []) fun u3 ⟨L3, S3, R3⟩ => ⟨L3, I2.st.trans S3, ?_⟩
  rw [I2.x14, I2.x13, I2.x8] at R3; exact R3

/-! ## The buffer -/

theorem clearBuf_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) :
    WP isa clearBuf u fun u' => Lay u' F S ∧ Step F S [] u u' ∧ Rep u'.mem F S (zV V oBuf 2048) W := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  refine WP.seq (WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = off S oBuf ∧
      u'.gpr .x12 = BitVec.ofNat 64 256 ∧ u'.gpr .x13 = 0) ?_ fun u1 ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x13⟩ => ?_)
  · oaep_run [clearBuf, scr, Mgf1.scr, lay, sScr, oBuf, h96, L.sp, hs]
    oaep_fin
  have S1 : Step F S [] u u1 := Step.blk _ hrd hwr hsp hv hcs hm
  refine WP.mono (clearLoop_ok (L.congr hsp hwr (by rw [hm])) (hm ▸ R) (o := oBuf) (n := 256) (by decide)
    (by decide) x11 x12 x13 []) fun u2 ⟨L2, S2, R2⟩ => ⟨L2, S1.trans S2, R2⟩

/-- `T` (`t = k - 2 hLen - 1` bytes at `1 + 2 hLen`) to the buffer. -/
theorem copyT_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {H : Hash} {k : Nat} (hk : W 21 = BitVec.ofNat 64 k) (hD : 2 * H.D + 2 ≤ k)
    (hk' : k ≤ 1024) :
    WP isa (copyT H) u fun u' => Lay u' F S ∧ Step F S [] u u' ∧
      Rep u'.mem F S (cpV V oBuf (k - 2 * H.D - 1) (tF V H.D)) W := by
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have rk := R.rdK hk
  refine WP.seq (WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = off S (1 + 2 * H.D) ∧
      u'.gpr .x12 = off S oBuf ∧ u'.gpr .x13 = BitVec.ofNat 64 (k - (2 * H.D + 1))) ?_
    fun u1 ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x13⟩ => ?_)
  · oaep_run [copyT, tArgs, mov, scr, Mgf1.scr, lay, sScr, sK, oBuf, oEm, h96, h168, L.sp, hs, rk, Nat.zero_add,
      show 1 + 2 * H.D < 4096 by omega, show 2 * H.D + 1 < 4096 by omega,
      Offset.ofNat_sub_ofNat (show 2 * H.D + 1 ≤ k by omega), BitVec.or_self]
    oaep_fin
  have S1 : Step F S [] u u1 := Step.blk _ hrd hwr hsp hv hcs hm
  have L1 : Lay u1 F S := L.congr hsp hwr (by rw [hm])
  have R1 : Rep u1.mem F S V W := hm ▸ R
  have c : oRsa = 8192 := rfl
  have cb : oBuf = 1024 := rfl
  refine WP.mono (copyLoop_ok L1 R1 (A := off S (1 + 2 * H.D)) (b := oBuf) (n := k - 2 * H.D - 1) (by omega)
    (by omega) (fun i hi => by rw [off_off]; exact L1.sld (by omega))
    (fun i hi j hj => by rw [off_off]; exact Offset.add_ofNat_ne S (by omega) (by omega) (by omega))
    x11 x12 (by rw [x13]; congr 1) []) fun u2 ⟨L2, S2, R2⟩ => ⟨L2, S1.trans S2, ?_⟩
  refine (congrArg (fun V' => Rep u2.mem F S V' W) (funext fun x => ?_)).mp R2
  simp only [cpV]
  split
  · rw [off_off, R1.scr _ (by omega)]; rfl
  · rfl

/-! ## One pass of the shift -/

theorem shr1_ofNat {a : Nat} (ha : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 1 = BitVec.ofNat 64 (a / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega)]

/-- The buffer's first `j` bytes replaced by those `d` after them if `b`. -/
def selV (V : Nat → Byte) (d : Nat) (b : Bool) (j : Nat) (x : Nat) : Byte :=
  if oBuf ≤ x ∧ x < oBuf + j then (if b then V (x + d) else V x) else V x

/-- The mask of bit 0 of `a`. -/
def bM (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

theorem neg_and1 (a : BitVec 64) : 0#64 - (a &&& 1) = bM (decide (a.toNat % 2 = 1)) := by
  have h : a &&& 1 = BitVec.ofNat 64 (a.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat]
    omega
  rw [h]
  rcases Nat.mod_two_eq_zero_or_one a.toNat with h0 | h1
  · rw [h0]; decide
  · rw [h1]; decide

theorem selB (x y : Byte) (b : Bool) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (x.setWidth 64 ^^^ ((y.setWidth 64 ^^^ x.setWidth 64) &&& bM b))) =
      if b then y else x := by
  cases b
  · simp only [bM, Bool.false_eq_true, ite_false]
    rw [show (BitVec.setWidth 64 y ^^^ BitVec.setWidth 64 x) &&& (0 : BitVec 64) = 0 from BitVec.and_zero,
      show BitVec.setWidth 64 x ^^^ (0 : BitVec 64) = BitVec.setWidth 64 x from BitVec.xor_zero]
    exact byte_rt64 x
  · simp only [bM, ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm (BitVec.setWidth 64 y), ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    exact byte_rt64 y

theorem regs4 {P : Reg → Prop} (h17 : P .x17) (h14 : P .x14) (h9 : P .x9) (h8 : P .x8) :
    ∀ r ∈ [Reg.x17, .x14, .x9, .x8], P r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem passBody_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {d j : Nat} {b : Bool} (hj : oBuf + d + j < oRsa)
    (h11 : u.gpr .x11 = off S (oBuf + j)) (h12 : u.gpr .x12 = off S (oBuf + d + j)) (h15 : u.gpr .x15 = bM b)
    (ws : List Region) :
    WP isa (.block passBody) u fun u' => Lay u' F S ∧ Step F S ws u u' ∧
      Rep u'.mem F S (upd V (oBuf + j) (if b then V (oBuf + d + j) else V (oBuf + j))) W ∧
      u'.gpr .x11 = off S (oBuf + j + 1) ∧ u'.gpr .x12 = off S (oBuf + d + j + 1) ∧ u'.gpr .x15 = bM b ∧
      u'.gpr .x13 = u.gpr .x13 - BitVec.ofNat 64 1 ∧ (∀ r ∈ [Reg.x17, .x14, .x9, .x8], u'.gpr r = u.gpr r) := by
  have r1 : InRegions (u.rd ++ u.wr) (off S (oBuf + j)) 1 := L.sld (by omega)
  have r2 : InRegions (u.rd ++ u.wr) (off S (oBuf + d + j)) 1 := L.sld (by omega)
  have w1 : InRegions u.wr (off S (oBuf + j)) 1 := L.sst (by omega)
  have v1 : u.mem (off S (oBuf + j)) = V (oBuf + j) := R.scr _ (by omega)
  have v2 : u.mem (off S (oBuf + d + j)) = V (oBuf + d + j) := R.scr _ (by omega)
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem.write (off S (oBuf + j)) 1
      (if b then V (oBuf + d + j) else V (oBuf + j)) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧
      (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = off S (oBuf + j) + BitVec.ofNat 64 1 ∧
      u'.gpr .x12 = off S (oBuf + d + j) + BitVec.ofNat 64 1 ∧ u'.gpr .x15 = bM b ∧
      u'.gpr .x13 = u.gpr .x13 - BitVec.ofNat 64 1 ∧ (∀ r ∈ [Reg.x17, .x14, .x9, .x8], u'.gpr r = u.gpr r)) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x15, x13, xk⟩ => ?_
  · oaep_run [passBody, h11, h12, h15, BitVec.add_zero, r1, r2, w1, read_one, byte64, v1, v2, selB]
    and_intros <;> first | trivial | exact cs_rfl | exact regs4 rfl rfl rfl rfl
  have R' : Rep u'.mem F S (upd V (oBuf + j) (if b then V (oBuf + d + j) else V (oBuf + j))) W := by
    rw [hm]; exact R.wb L.geo (by omega) _
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], ?_⟩, R', x11.trans (off_off S _ 1),
    x12.trans (off_off S _ 1), x15, x13, xk⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]
  · rw [hm]; exact frame_wb (Frame.refl _ _) (by omega) _

/-- The pass's loop, from the buffer's first byte. -/
theorem passLoop_ok {u₀ : State} {F S : Addr} (L : Lay u₀ F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u₀.mem F S V W) {d : Nat} {b : Bool} (hd1 : 1 ≤ d) (hd2 : d ≤ 1024)
    (h11 : u₀.gpr .x11 = off S oBuf) (h12 : u₀.gpr .x12 = off S (oBuf + d)) (h15 : u₀.gpr .x15 = bM b)
    (h13 : u₀.gpr .x13 = BitVec.ofNat 64 1024) (ws : List Region) :
    WP isa (.loop (.block passBody) (.nonzero .x .x13)) u₀ fun u =>
      Lay u F S ∧ Step F S ws u₀ u ∧ Rep u.mem F S (selV V d b 1024) W ∧
        ∀ r ∈ [Reg.x17, .x14, .x9, .x8], u.gpr r = u₀.gpr r := by
  have c : oRsa = 8192 := rfl
  have cb : oBuf = 1024 := rfl
  refine WP.mono (count_loop (n := 1024) (by decide) (fun j u => Lay u F S ∧ Step F S ws u₀ u ∧
      Rep u.mem F S (selV V d b j) W ∧ u.gpr .x11 = off S (oBuf + j) ∧ u.gpr .x12 = off S (oBuf + d + j) ∧
      u.gpr .x15 = bM b ∧ u.gpr .x13 = BitVec.ofNat 64 (1024 - j) ∧
      ∀ r ∈ [Reg.x17, .x14, .x9, .x8], u.gpr r = u₀.gpr r)
    (fun j hj u ⟨Lu, Su, Ru, u11, u12, u15, u13, uk⟩ => ?_)
    ⟨L, Step.refl _ _ _ _, by
      refine (congrArg (fun V' => Rep _ F S V' _) (funext fun x => ?_)).mp R
      simp only [selV]; rw [ifn (by omega)], by rw [h11]; rfl, by rw [h12]; rfl, h15, h13, fun _ _ => rfl⟩)
    fun u ⟨Lu, Su, Ru, _, _, _, _, uk⟩ => ⟨Lu, Su, Ru, uk⟩
  refine WP.mono (passBody_ok Lu Ru (d := d) (j := j) (by omega) u11 u12 u15 ws)
    fun u' ⟨L', S', R', x11, x12, x15, x13, xk⟩ => ⟨⟨L', Su.trans S', ?_, x11, x12, x15, ?_,
      fun r hr => (xk r hr).trans (uk r hr)⟩, ?_⟩
  · refine (congrArg (fun V' => Rep u'.mem F S V' W) (funext fun x => ?_)).mp R'
    simp only [upd, selV]
    by_cases hx : x = oBuf + j
    · subst hx
      rw [ifp rfl, ifp (show oBuf ≤ oBuf + j ∧ oBuf + j < oBuf + (j + 1) by omega),
        ifn (show ¬ (oBuf ≤ oBuf + d + j ∧ oBuf + d + j < oBuf + j) by omega),
        ifn (show ¬ (oBuf ≤ oBuf + j ∧ oBuf + j < oBuf + j) by omega), show oBuf + j + d = oBuf + d + j by omega]
    · rw [ifn hx]
      by_cases h' : oBuf ≤ x ∧ x < oBuf + j
      · rw [ifp h', ifp (show oBuf ≤ x ∧ x < oBuf + (j + 1) by omega)]
      · rw [ifn h', ifn (show ¬ (oBuf ≤ x ∧ x < oBuf + (j + 1)) by omega)]
  · rw [x13, u13, counter_step hj (by omega)]
  · rw [x13, u13, counter_step hj (by omega)]; exact counter_ne hj (by omega)

/-- A pass of the shift, by `d` under bit 0 of `a`, and the next pass's `a / 2`, `2 d`, `j - 1`. -/
theorem pass_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {a d j : Nat} (ha : a < 2 ^ 64) (hd1 : 1 ≤ d) (hd2 : d ≤ 1024) (hj : 1 ≤ j)
    (h17 : u.gpr .x17 = off S oBuf) (h14 : u.gpr .x14 = BitVec.ofNat 64 d) (h9 : u.gpr .x9 = BitVec.ofNat 64 a)
    (h8 : u.gpr .x8 = BitVec.ofNat 64 j) :
    WP isa pass u fun u' => Lay u' F S ∧ Step F S [] u u' ∧
      Rep u'.mem F S (selV V d (decide (a % 2 = 1)) 1024) W ∧ u'.gpr .x17 = off S oBuf ∧
      u'.gpr .x14 = BitVec.ofNat 64 (2 * d) ∧ u'.gpr .x9 = BitVec.ofNat 64 (a / 2) ∧
      u'.gpr .x8 = BitVec.ofNat 64 (j - 1) := by
  have ha2 : (BitVec.ofNat 64 a).toNat % 2 = a % 2 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  unfold pass
  refine WP.seq (WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = off S oBuf ∧
      u'.gpr .x12 = off S oBuf + BitVec.ofNat 64 d ∧ u'.gpr .x15 = bM (decide (a % 2 = 1)) ∧
      u'.gpr .x13 = BitVec.ofNat 64 1024 ∧ u'.gpr .x17 = off S oBuf ∧ u'.gpr .x14 = BitVec.ofNat 64 d ∧
      u'.gpr .x9 = BitVec.ofNat 64 a ∧ u'.gpr .x8 = BitVec.ofNat 64 j) ?_
    fun u1 ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x15, x13, x17, x14, x9, x8⟩ => ?_)
  · oaep_run [mov, h17, h14, h9, h8, BitVec.or_self, show BitVec.setWidth 64 (1 : BitVec 16) <<< 0 = 1 by decide,
      show BitVec.setWidth 64 (0 : BitVec 16) <<< 0 = 0#64 by decide,
      show BitVec.setWidth 64 (1024 : BitVec 16) <<< 0 = BitVec.ofNat 64 1024 by decide, neg_and1, ha2]
    oaep_fin
  have S1 : Step F S [] u u1 := Step.blk _ hrd hwr hsp hv hcs hm
  refine WP.seq (WP.mono (passLoop_ok (L.congr hsp hwr (by rw [hm])) (hm ▸ R) hd1 hd2 x11
    (x12.trans (off_off S oBuf d)) x15 x13 []) fun u2 ⟨L2, S2, R2, k2⟩ => ?_)
  refine WP.mono (Q := fun (u' : State) => u'.mem = u2.mem ∧ u'.rd = u2.rd ∧ u'.wr = u2.wr ∧ u'.sp = u2.sp ∧
      u'.v = u2.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u2.gpr r) ∧ u'.gpr .x17 = u2.gpr .x17 ∧
      u'.gpr .x14 = u2.gpr .x14 + u2.gpr .x14 ∧ u'.gpr .x9 = u2.gpr .x9 >>> 1 ∧
      u'.gpr .x8 = u2.gpr .x8 - BitVec.ofNat 64 1) ?_
    fun u3 ⟨hm3, hrd3, hwr3, hsp3, hv3, hcs3, x17', x14', x9', x8'⟩ => ?_
  · oaep_run []
    oaep_fin
  have e17 := k2 .x17 (by simp)
  have e14 := k2 .x14 (by simp)
  have e9 := k2 .x9 (by simp)
  have e8 := k2 .x8 (by simp)
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
  have h96 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  have h240 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 240) 8 := L.ld (d := 240) (by decide)
  have hs : u.mem.read (F + BitVec.ofNat 64 96) 8 = S := L.slot
  have ri := R.rd8 (d := 240) (k := 30) rfl (by decide) hi
  unfold shift
  refine WP.seq (WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x17 = off S oBuf ∧
      u'.gpr .x9 = BitVec.ofNat 64 (idx + 1) ∧ u'.gpr .x14 = BitVec.ofNat 64 1 ∧
      u'.gpr .x8 = BitVec.ofNat 64 10) ?_ fun v ⟨hm, hrd, hwr, hsp, hv, hcs, x17, x9, x14, x8⟩ => ?_)
  · oaep_run [scr, Mgf1.scr, lay, sScr, sIdx, oBuf, h96, h240, L.sp, hs, ri, BitVec.ofNat_add_ofNat,
      show BitVec.setWidth 64 (1 : BitVec 16) <<< 0 = BitVec.ofNat 64 1 by decide,
      show BitVec.setWidth 64 (10 : BitVec 16) <<< 0 = BitVec.ofNat 64 10 by decide]
    oaep_fin
  have Lv : Lay v F S := L.congr hsp hwr (by rw [hm])
  have I0 : ShiftI u F S V₀ W (idx + 1) 0 v := ⟨Lv, Step.blk _ hrd hwr hsp hv hcs hm, x17, x14,
    by rw [x9, Nat.pow_zero, Nat.div_one], x8, V₀, hm ▸ R,
    fun i hi => by
      simp only [Nat.pow_zero, Nat.mod_one, Nat.add_zero, bufB]
      by_cases h : i < 1024
      · rw [ifp h]
      · rw [ifn h, hz i (by omega) hi], fun _ _ => rfl⟩
  refine WP.mono (count_loop (n := 10) (by decide) (ShiftI u F S V₀ W (idx + 1)) (fun p hp w I => ?_) I0)
    fun w I => ⟨I.L, I.st, ?_⟩
  · obtain ⟨V, Rw, hB, hO⟩ := I.rep
    have hp9 : 2 ^ p ≤ 512 := Nat.le_trans (Nat.pow_le_pow_right (by decide) (show p ≤ 9 by omega))
      (by decide : 2 ^ 9 ≤ 512)
    have hp0 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
    refine WP.mono (pass_ok I.L Rw (a := (idx + 1) / 2 ^ p) (d := 2 ^ p) (j := 10 - p)
      (by have := Nat.div_le_self (idx + 1) (2 ^ p); omega) hp0 (by omega) (by omega) I.x17 I.x14 I.x9 I.x8)
      fun w2 ⟨L2, S2, R2, x17, x14, x9, x8⟩ => ⟨⟨L2, I.st.trans S2, x17,
        by rw [x14, Nat.pow_succ, Nat.mul_comm], by rw [x9, Nat.pow_succ, Nat.div_div_eq_div_mul],
        by rw [x8]; congr 1, _, R2, fun i hi => ?_, fun o ho => ?_⟩, ?_⟩
    · simp only [selV]
      rw [Nat.mod_pow_succ]
      by_cases hi' : i < 1024
      · rw [ifp (show oBuf ≤ oBuf + i ∧ oBuf + i < oBuf + 1024 by omega)]
        rcases Nat.mod_two_eq_zero_or_one ((idx + 1) / 2 ^ p) with h0 | h1
        · rw [h0, show decide (0 = 1) = false from rfl]
          simp only [Bool.false_eq_true, ite_false, Nat.mul_zero, Nat.add_zero]
          exact hB i hi
        · rw [h1, show decide (1 = 1) = true from rfl]
          simp only [ite_true, Nat.mul_one]
          rw [show oBuf + i + 2 ^ p = oBuf + (i + 2 ^ p) by omega, hB (i + 2 ^ p) (by omega)]
          congr 1; omega
      · rw [ifn (show ¬ (oBuf ≤ oBuf + i ∧ oBuf + i < oBuf + 1024) by omega), hB i hi, bufB, bufB,
          ifn (show ¬ (i + (idx + 1) % 2 ^ p < 1024) by omega),
          ifn (show ¬ (i + ((idx + 1) % 2 ^ p + 2 ^ p * ((idx + 1) / 2 ^ p % 2)) < 1024) by omega)]
    · have ho' : ¬ (oBuf ≤ o ∧ o < oBuf + 1024) := fun h => ho ⟨h.1, by omega⟩
      unfold selV; rw [ifn ho']; exact hO o ho
    · rw [x8, show 10 - p - 1 = 10 - (p + 1) by omega]; exact counter_ne hp (by omega)
  · obtain ⟨V, Rw, hB, hO⟩ := I.rep
    refine ⟨V, Rw, fun i hi => ?_, hO⟩
    rw [hB i hi, Nat.mod_eq_of_lt (show idx + 1 < 2 ^ 10 by omega)]

end VG.Proof.RsaOaep.AArch64
