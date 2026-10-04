import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Ctx
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Spec.Sha3

/-!
# Ed448's complete operations on AArch64: words kept in the locals

`keep r d` stores `r` in the locals (`keep_ok`); `hdr d ctxlen` stores the
first ten bytes of `dom4(0, context)` there (`hdr_ok`, `hdr_bytes`).
-/

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Whole
open VG.Impl.Ed25519.AArch64.Whole (Value setArg)

/-- `"SigEd448"`, as a little-endian word. -/
def sigWord : BitVec 64 := 0x3834346445676953

/-- Registers but `x9`, `x15`; the rest of the state but memory. -/
structure Keeps915 (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : t.v = s.v
  regs : ∀ r, r ≠ .x9 → r ≠ .x15 → t.gpr r = s.gpr r

theorem Keeps915.trans {s t u : State} (h : Keeps915 s t) (h' : Keeps915 t u) : Keeps915 s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.v.trans h.v,
    fun r h9 h15 => (h'.regs r h9 h15).trans (h.regs r h9 h15)⟩

/-- `x15 := sp + d`, then `[x15] := r`. -/
theorem keep_ok {s : State} {r : Reg} {d : Nat} (hd : d < 4096)
    (hw : InRegions s.wr (s.sp + BitVec.ofNat 64 d) 8) :
    WP isa (.block (keep r d)) s fun t => Keeps915 s t ∧ t.gpr .x15 = s.sp + BitVec.ofNat 64 d ∧
      t.mem = s.mem.writeW (s.sp + BitVec.ofNat 64 d) ((s.write .x .x15 (s.sp + BitVec.ofNat 64 d)).gpr r) := by
  have ha : exec (.addSp .x15 d) s = some (s.write .x .x15 (s.sp + BitVec.ofNat 64 d)) := by
    simp only [exec, hd, ite_true]
  apply WP.of_runBlock
  simp only [keep, runBlock_cons, runStep_some, ha]
  rw [exec_str_x ⟨by decide, by decide⟩ (by
    simpa only [RegUpd.wr_write, RegUpd.gpr_write, ite_true, BitVec.setWidth_eq, BitVec.add_zero] using hw)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', RegUpd.gpr_write,
    ite_true, BitVec.setWidth_eq, BitVec.add_zero, RegUpd.mem_write]
  exact ⟨⟨rfl, rfl, rfl, rfl, fun q _ h15 => RegUpd.gpr_write_of_ne _ _ _ h15⟩, trivial, trivial⟩

/-- `x9 := "SigEd448"`. -/
theorem sig_ok (s : State) :
    WP isa (.block [.movz .x .x9 0x6953 0, .movk .x .x9 0x4567 1, .movk .x .x9 0x3464 2,
      .movk .x .x9 0x3834 3]) s fun t => Keeps915 s t ∧ t.gpr .x9 = sigWord ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, RegUpd.gpr_write, RegUpd.mem_write, BitVec.setWidth_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, rfl, fun r h9 _ => ?_⟩, by decide, trivial⟩
  simp only [RegUpd.gpr_write, h9, ite_false]

/-- `x9 := x9 << 8`, then `[x15 + 8] := x9`. -/
theorem shiftStore_ok {s : State} (hw : InRegions s.wr (s.gpr .x15 + BitVec.ofNat 64 8) 8) :
    WP isa (.block [.lsl .x .x9 .x9 8, .str .x .x9 .x15 8]) s fun t => Keeps915 s t ∧
      t.mem = s.mem.writeW (s.gpr .x15 + BitVec.ofNat 64 8) (s.gpr .x9 <<< 8) := by
  have hl : exec (.lsl .x .x9 .x9 8) s = some (s.write .x .x9 (s.gpr .x9 <<< 8)) := by
    simp only [exec, Size.bits, Nat.reduceLT, ite_true, State.read, BitVec.setWidth_eq]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, hl]
  rw [exec_str_x ⟨by decide, by decide⟩ (by
    simpa only [RegUpd.wr_write, RegUpd.gpr_write, reduceCtorEq, ite_false] using hw)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', RegUpd.gpr_write,
    reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, RegUpd.mem_write]
  exact ⟨⟨rfl, rfl, rfl, rfl, fun q h9 _ => RegUpd.gpr_write_of_ne _ _ _ h9⟩, trivial⟩

/-- The header: `"SigEd448"` at `sp + d`, and the saved argument `j` (`ctxlen`)
shifted by 8 at `sp + d + 8`. -/
theorem hdr_ok {s : State} {d j : Nat} (hd : d + 16 ≤ 256) (hj : j < 6)
    (hw : (⟨s.sp, 256⟩ : Region) ∈ s.wr)
    (hr : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (256 + 8 * j)) 8) :
    WP isa (.block (hdr d (.caller j 0))) s fun t => Keeps915 s t ∧
      t.mem = (s.mem.writeW (s.sp + BitVec.ofNat 64 d) sigWord).writeW (s.sp + BitVec.ofNat 64 (d + 8))
        (s.mem.read (s.sp + BitVec.ofNat 64 (256 + 8 * j)) 8 <<< 8) := by
  rw [hdr, show ([.movz .x .x9 0x6953 0, .movk .x .x9 0x4567 1, .movk .x .x9 0x3464 2, .movk .x .x9 0x3834 3,
      .addSp .x15 d, .str .x .x9 .x15 0] : List Instr) = [.movz .x .x9 0x6953 0, .movk .x .x9 0x4567 1,
      .movk .x .x9 0x3464 2, .movk .x .x9 0x3834 3] ++ keep .x9 d from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (sig_ok s) fun a ⟨ka, a9, am⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (keep_ok (r := .x9) (d := d) (by omega)
    (by rw [ka.wr, ka.sp]; exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩))
    fun b ⟨kb, b15, bm⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.Whole.setArg_ok (r := .x9) (v := .caller j 0) rfl
    (show j < 6 ∧ 0 < 4096 from ⟨hj, by decide⟩) (fun j' d' h => by
      cases h; rw [kb.rd, kb.wr, kb.sp, ka.rd, ka.wr, ka.sp]; exact hr)) fun c ⟨kc, c9⟩ => ?_
  have c15 : c.gpr .x15 = s.sp + BitVec.ofNat 64 d := by
    rw [kc.regs _ (by decide), b15, ka.sp]
  refine WP.mono (shiftStore_ok (by
    rw [c15, kc.wr, kb.wr, ka.wr, Offset.add_add]
    exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩)) fun t ⟨kt, tm⟩ => ⟨?_, ?_⟩
  · exact ((ka.trans kb).trans ⟨kc.rd, kc.wr, kc.sp, kc.vec, fun r h9 _ => kc.regs r (by simpa using h9)⟩).trans kt
  · have ebm : b.mem = s.mem.writeW (s.sp + BitVec.ofNat 64 d) sigWord := by
      rw [bm, RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x9 ≠ .x15), a9, am, ka.sp]
    have ebsp : b.sp = s.sp := kb.sp.trans ka.sp
    have hread : b.mem.read (s.sp + BitVec.ofNat 64 (256 + 8 * j)) 8 =
        s.mem.read (s.sp + BitVec.ofNat 64 (256 + 8 * j)) 8 := by
      rw [ebm]
      simp only [Mem.writeW]
      exact Mem.read_write_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)
    rw [tm, c15, c9, kc.mem]
    simp only [VG.Proof.Ed25519.AArch64.Whole.value, BitVec.add_zero]
    rw [ebsp, hread, ebm, Offset.add_add]

theorem readW_eq_read (m : Mem) (p : Addr) : m.readW p 64 = m.read p 8 := by
  simp only [Mem.readW]; rfl

/-- `"SigEd448" ‖ 0 ‖ c`, the bytes of the header's two words. -/
theorem hdr_bytes (m : Mem) (p : Addr) (c : BitVec 64) (hc : c.toNat < 256) (h0 : m.read p 8 = sigWord)
    (h1 : m.read (p + BitVec.ofNat 64 8) 8 = c <<< 8) :
    Spec.Sha3.bytesAt m p 10 =
      "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 c.toNat] := by
  have hw : (c <<< 8).toNat = c.toNat * 256 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have e10 : Spec.Sha3.bytesAt m p 10 =
      Spec.Sha3.bytesAt m p 8 ++ (Spec.Sha3.bytesAt m (p + BitVec.ofNat 64 8) 8).take 2 := by
    have a := Proof.X25519.bytesAt_add m p 8 2
    have b := Proof.X25519.bytesAt_add m (p + BitVec.ofNat 64 8) 2 6
    have l := Proof.X25519.length_bytesAt m (p + BitVec.ofNat 64 8) 2
    change Spec.X25519.bytesAt m p 10 = Spec.X25519.bytesAt m p 8 ++
      (Spec.X25519.bytesAt m (p + BitVec.ofNat 64 8) 8).take 2
    rw [a, show (8 : Nat) = 2 + 6 from rfl, b, List.take_left' l]
  have b8 : ∀ q, Spec.Sha3.bytesAt m q 8 = Proof.X25519.leBytes 8 (m.readW q 64).toNat :=
    fun q => Proof.X25519.bytesAt_leBytes_64 m q
  rw [e10, b8, b8, readW_eq_read, readW_eq_read, h0, h1, hw, show Proof.X25519.leBytes 8 sigWord.toNat =
    "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) by decide]
  refine congrArg (List.append _) ?_
  simp only [Proof.X25519.leBytes_succ, List.take_succ_cons, List.take_zero]
  have e1 : BitVec.ofNat 8 (c.toNat * 256) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, show (0 : BitVec 8).toNat = 0 from rfl]; omega
  have e2 : c.toNat * 256 / 256 = c.toNat := by omega
  rw [e1, e2]
  rfl

theorem read_writeW_self (m : Mem) (a : Addr) (v : BitVec 64) : (m.writeW a v).read a 8 = v := by
  rw [← readW_eq_read]; exact Mem.readW_writeW_self64 _ _ _

theorem read_writeW_sep {m : Mem} {a b : Addr} {v : BitVec 64} (h : Mem.Sep a 8 b 8) :
    (m.writeW b v).read a 8 = m.read a 8 := by
  rw [← readW_eq_read, ← readW_eq_read]; exact Mem.readW_writeW_sep h (by decide)

end VG.Proof.Ed448.AArch64.Whole
