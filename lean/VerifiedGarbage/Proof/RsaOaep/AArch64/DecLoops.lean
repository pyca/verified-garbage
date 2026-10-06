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

end VG.Proof.RsaOaep.AArch64
