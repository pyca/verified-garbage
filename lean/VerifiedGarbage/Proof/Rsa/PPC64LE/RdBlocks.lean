module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdOps
public import VerifiedGarbage.Proof.Rsa.RecoverExp
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvSlots
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: the blocks on registers and slots

The counts in `r27` (`countN`, `countS`, `next`), the inverse's length in
`r11`, `r9` set or the negation of a slot, the flags of a halving step
(`twosFlags`) and the mask (`maskOf`), each keeping `DS`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.RecDet

theorem b2n_le1 (c : Bool) : VG.Proof.Rsa.b2n c ≤ 1 := by cases c <;> decide

theorem ite_le1 (p : Prop) [Decidable p] : (if p then 1 else 0) ≤ 1 := by split <;> decide

/-- The values of `upd` and `updV` chains on the arrays and slots named. -/
macro "rd_simp" : tactic => `(tactic| (set_option linter.unusedSimpArgs false in
  simp [VG.Proof.Rsa.PPC64LE.RecDet.upd, VG.Proof.Rsa.PPC64LE.RecDet.updV, VG.Proof.Rsa.b2n,
    VG.Proof.Rsa.PPC64LE.RecDet.b2n_le1, VG.Proof.Rsa.PPC64LE.RecDet.ite_le1,
    VG.Proof.Rsa.PPC64LE.RecDet.vw_false, VG.Proof.Rsa.PPC64LE.RecDet.vw_true,
    VG.Impl.Rsa.PPC64LE.RecoverDet.sB0, VG.Impl.Rsa.PPC64LE.RecoverDet.sB1, VG.Impl.Rsa.PPC64LE.RecoverDet.sU,
    VG.Impl.Rsa.PPC64LE.RecoverDet.sX, VG.Impl.Rsa.PPC64LE.RecoverDet.sEven, VG.Impl.Rsa.PPC64LE.RecoverDet.sBoth,
    VG.Impl.Rsa.PPC64LE.RecoverDet.sY, VG.Impl.Rsa.PPC64LE.RecoverDet.sLt, VG.Impl.Rsa.PPC64LE.RecoverDet.sExact,
    VG.Impl.Rsa.PPC64LE.RecoverDet.sC1, VG.Impl.Rsa.PPC64LE.RecoverDet.sC2, VG.Impl.Rsa.PPC64LE.RecoverDet.sBb,
    VG.Impl.Rsa.PPC64LE.RecoverDet.sOk5, VG.Impl.Rsa.PPC64LE.RecoverDet.sU1, VG.Impl.Rsa.PPC64LE.Recover.sMask,
    VG.Impl.Rsa.PPC64LE.CrtValues.sMask]))

/-- `rd_simp` with further lemmas. -/
macro "rd_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (set_option linter.unusedSimpArgs false in
  simp [VG.Proof.Rsa.PPC64LE.RecDet.upd, VG.Proof.Rsa.PPC64LE.RecDet.updV, VG.Proof.Rsa.b2n,
    VG.Proof.Rsa.PPC64LE.RecDet.b2n_le1, VG.Proof.Rsa.PPC64LE.RecDet.ite_le1,
    VG.Proof.Rsa.PPC64LE.RecDet.vw_false, VG.Proof.Rsa.PPC64LE.RecDet.vw_true,
    VG.Impl.Rsa.PPC64LE.RecoverDet.sB0, VG.Impl.Rsa.PPC64LE.RecoverDet.sB1, VG.Impl.Rsa.PPC64LE.RecoverDet.sU,
    VG.Impl.Rsa.PPC64LE.RecoverDet.sX, VG.Impl.Rsa.PPC64LE.RecoverDet.sEven, VG.Impl.Rsa.PPC64LE.RecoverDet.sBoth,
    VG.Impl.Rsa.PPC64LE.RecoverDet.sY, VG.Impl.Rsa.PPC64LE.RecoverDet.sLt, VG.Impl.Rsa.PPC64LE.RecoverDet.sExact,
    VG.Impl.Rsa.PPC64LE.RecoverDet.sC1, VG.Impl.Rsa.PPC64LE.RecoverDet.sC2, VG.Impl.Rsa.PPC64LE.RecoverDet.sBb,
    VG.Impl.Rsa.PPC64LE.RecoverDet.sOk5, VG.Impl.Rsa.PPC64LE.RecoverDet.sU1, VG.Impl.Rsa.PPC64LE.Recover.sMask,
    VG.Impl.Rsa.PPC64LE.CrtValues.sMask, $ls,*]))

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa.PPC64LE.Recover
open VG.Proof.Rsa (b2n)
open VG.Impl.Rsa.PPC64LE.RecoverDet (countN countS next twosFlags maskOf sU sX sEven sBoth sB0 sB1 sLt sExact sC1
  sC2 sOk5)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- `rd_simp` with further lemmas, at a hypothesis. -/
macro "rd_simp_at" h:ident " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (set_option linter.unusedSimpArgs false in
  simp [VG.Proof.Rsa.PPC64LE.RecDet.upd, VG.Proof.Rsa.PPC64LE.RecDet.updV, VG.Proof.Rsa.b2n,
    VG.Proof.Rsa.PPC64LE.RecDet.b2n_le1, VG.Proof.Rsa.PPC64LE.RecDet.ite_le1,
    VG.Proof.Rsa.PPC64LE.RecDet.vw_false, VG.Proof.Rsa.PPC64LE.RecDet.vw_true,
    VG.Impl.Rsa.PPC64LE.RecoverDet.sB0, VG.Impl.Rsa.PPC64LE.RecoverDet.sB1, VG.Impl.Rsa.PPC64LE.RecoverDet.sU,
    VG.Impl.Rsa.PPC64LE.RecoverDet.sX, VG.Impl.Rsa.PPC64LE.RecoverDet.sEven, VG.Impl.Rsa.PPC64LE.RecoverDet.sBoth,
    VG.Impl.Rsa.PPC64LE.RecoverDet.sY, VG.Impl.Rsa.PPC64LE.RecoverDet.sLt, VG.Impl.Rsa.PPC64LE.RecoverDet.sExact,
    VG.Impl.Rsa.PPC64LE.RecoverDet.sC1, VG.Impl.Rsa.PPC64LE.RecoverDet.sC2, VG.Impl.Rsa.PPC64LE.RecoverDet.sBb,
    VG.Impl.Rsa.PPC64LE.RecoverDet.sOk5, VG.Impl.Rsa.PPC64LE.RecoverDet.sU1, VG.Impl.Rsa.PPC64LE.Recover.sMask,
    VG.Impl.Rsa.PPC64LE.CrtValues.sMask, $ls,*] at $h:ident))

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.Rsa.PPC64LE.Recover
open VG.Proof.Rsa (b2n)
open VG.Impl.Rsa.PPC64LE.RecoverDet (countN countS next twosFlags maskOf sU sX sEven sBoth sB0 sB1 sLt sExact sC1
  sC2 sOk5)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

section
variable {s0 s : State} {b : Bool} {A : Bool → Nat → Nat} {live : List (Bool × Nat)} {V : Nat → Nat}
  {ls : List Nat}

/-- A block on registers alone. -/
theorem DS.reg (h : DS s0 b A live V ls s) {c : List Instr} (rs : List Reg) {P : State → Prop}
    (hc : WP isa (.block c) s fun u => P u ∧ u.mem = s.mem) (hw : writesOnly rs (.block c) = true)
    (h21 : .r21 ∉ rs := by decide) (h23 : .r23 ∉ rs := by decide) (h25 : .r25 ∉ rs := by decide)
    (h29 : .r29 ∉ rs := by decide) (h30 : .r30 ∉ rs := by decide) (h31 : .r31 ∉ rs := by decide) :
    WP isa (.block c) s fun u => DS s0 b A live V ls u ∧ P u ∧ Keep rs s u :=
  WP.mono (WP.keep rs hc hw) fun u ⟨⟨p, m⟩, k⟩ => ⟨h.regs k m h21 h23 h25 h29 h30 h31, p, k⟩

theorem DS.li9 (h : DS s0 b A live V ls s) {v : Nat} (hv : v < 2 ^ 15) :
    WP isa (.block [.li .r9 v]) s fun u => DS s0 b A live V ls u ∧ u.gpr .r9 = BitVec.ofNat 64 v ∧
      Keep [.r9] s u :=
  h.reg [.r9] (by prun [exec_li hv]) rfl

theorem DS.next (h : DS s0 b A live V ls s) :
    WP isa (.block next) s fun u => DS s0 b A live V ls u ∧ u.gpr .r27 = s.gpr .r27 - BitVec.ofNat 64 1 ∧
      Keep [.r27] s u :=
  h.reg [.r27] (by prun [VG.Impl.Rsa.PPC64LE.RecoverDet.next, exec_subi (show Reg.r27 ≠ .r0 by decide) (show 1 ≤ 2 ^ 15 by decide)]) (by decide)

theorem shl5_val (w : Nat) : BitVec.ofNat 64 w <<< 5 = BitVec.ofNat 64 (32 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem DS.countN (h : DS s0 false A live V ls s) :
    WP isa (.block countN) s fun u => DS s0 false A live V ls u ∧
      u.gpr .r27 = BitVec.ofNat 64 (32 * ww (kK s0)) ∧ Keep [.r27] s u := by
  have := h.ws.wle
  have r29 : s.gpr .r29 = BitVec.ofNat 64 (ww (kK s0)) := h.ws.r29
  exact h.reg [.r27] (by prun [VG.Impl.Rsa.PPC64LE.RecoverDet.countN, exec_lsl (show 5 < 64 by decide), r29, shl5_val _]) (by decide)

theorem DS.countS (h : DS s0 false A live V ls s) :
    WP isa (.block countS) s fun u => DS s0 false A live V ls u ∧
      u.gpr .r27 = BitVec.ofNat 64 (32 * ww (kK s0) + 32) ∧ Keep [.r27] s u := by
  have := h.ws.wle
  have r29 : s.gpr .r29 = BitVec.ofNat 64 (ww (kK s0)) := h.ws.r29
  refine h.reg [.r27] ?_ (by decide)
  prun [VG.Impl.Rsa.PPC64LE.RecoverDet.countS, exec_lsl (show 5 < 64 by decide), r29, shl5_val _,
    exec_addi (show Reg.r27 ≠ .r0 by decide) (show 32 < 2 ^ 15 by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem DS.set11 (h : DS s0 false A live V ls s) :
    WP isa (.block [.addi .r11 .r29 0]) s fun u => DS s0 false A live V ls u ∧
      u.gpr .r11 = BitVec.ofNat 64 (ww (kK s0)) ∧ Keep [.r11] s u := by
  have r29 : s.gpr .r29 = BitVec.ofNat 64 (ww (kK s0)) := h.ws.r29
  exact h.reg [.r11] (by prun [exec_addi (show Reg.r29 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), r29,
    BitVec.add_zero]) (by decide)

theorem bv01 (x : BitVec 32) (h : x.toNat ≤ 1) : x = 0#32 ∨ x = 1#32 := by
  rcases (show x.toNat = 0 ∨ x.toNat = 1 by omega) with e | e
  · exact .inl (BitVec.eq_of_toNat_eq e)
  · exact .inr (BitVec.eq_of_toNat_eq e)

/-- A slot of the header as a 32-bit word. -/
theorem slot_bv (m : Mem) (B : Addr) {d : Nat} {c : Bool} (h : slot m B d = b2n c) :
    m.readW (off B d) 32 = BitVec.ofNat 32 (b2n c) := by
  apply BitVec.eq_of_toNat_eq
  have := VG.Proof.Rsa.b2n_le c
  simp only [slot, w32] at h
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem b64_eq (c : Bool) : (BitVec.ofNat 32 (b2n c)).setWidth 64 = b64 c := by cases c <;> decide
theorem b64_xor (c : Bool) : b64 c ^^^ BitVec.ofNat 64 1 = b64 (!c) := by cases c <;> decide
theorem b64_and (c d : Bool) : b64 c &&& b64 d = b64 (c && d) := by cases c <;> cases d <;> decide
theorem b64_toNat (c : Bool) : ((b64 c).setWidth 32).toNat = b2n c := by cases c <;> decide

theorem DS.slotRd (h : DS s0 b A live V ls s) {d : Nat} (hd : d ∈ ls) {c : Bool} (hc : V d = b2n c) :
    s.mem.readW (off (rvB s0) d) 32 = BitVec.ofNat 32 (b2n c) :=
  slot_bv _ _ (by rw [h.sl d hd, hc])

/-- `r9 := 1 - slot`. -/
theorem DS.not9 (h : DS s0 b A live V ls s) {d : Nat} (hd : d ∈ ls) {c : Bool} (hc : V d = b2n c) :
    WP isa (.block [.load .w .r9 .r31 d, .li .r0 1, .logic .xor .r9 .r9 .r0]) s fun u =>
      DS s0 b A live V ls u ∧ (u.gpr .r9).toNat = b2n (!c) ∧ Keep [.r0, .r9] s u := by
  have ws := h.ws
  have z := h.base.sz
  have hl := h.ls_ok d hd
  refine WP.mono (h.reg [.r0, .r9] (P := fun u => u.gpr .r9 = b64 (!c)) ?_ rfl) fun u ⟨hu, p, k⟩ =>
    ⟨hu, by rw [p]; cases c <;> rfl, k⟩
  prun [ws.r31, exec_load_w (show Reg.r31 ≠ .r0 by decide) (show d < 2 ^ 15 by omega),
    ws.scr.ld (show d + 4 ≤ rvZ s0 by have := ws.hdr_le; simp only [KeyWorkspace.hdr] at this; omega),
    exec_li (show 1 < 2 ^ 15 by decide), exec_logic, h.slotRd hd hc, b64_eq, b64_xor]

/-- `twosFlags`' slots, after the low bits: `even := ¬u₀` and `both := ¬u₀ ∧ ¬x₀`. -/
theorem DS.twosTail (h : DS s0 b A live V ls s) (hu : sU ∈ ls) (hx : sX ∈ ls) {cu cx : Bool}
    (vu : V sU = b2n cu) (vx : V sX = b2n cx) {ls' : List Nat}
    (hl : ∀ e ∈ ls', e ∈ ls ∧ (e + 4 ≤ sEven ∨ sEven + 4 ≤ e) ∧ (e + 4 ≤ sBoth ∨ sBoth + 4 ≤ e)) :
    WP isa (.block [.load .w .r0 .r31 sU, .load .w .r3 .r31 sX, .li .r5 1, .logic .xor .r0 .r0 .r5,
      .logic .xor .r3 .r3 .r5, .store .w .r0 .r31 sEven, .logic .and .r3 .r3 .r0, .store .w .r3 .r31 sBoth]) s
      fun t => DS s0 b A live (updV (updV V sEven (b2n (!cu))) sBoth (b2n (!cx && !cu))) (sBoth :: sEven :: ls') t ∧
        Keep opRegs s t := by
  have ws := h.ws
  have hz := ws.hdr_le
  have nw := ws.nowrap
  simp only [KeyWorkspace.hdr] at hz
  have hb : WP isa (.block [.load .w .r0 .r31 sU, .load .w .r3 .r31 sX, .li .r5 1, .logic .xor .r0 .r0 .r5,
      .logic .xor .r3 .r3 .r5, .store .w .r0 .r31 sEven, .logic .and .r3 .r3 .r0, .store .w .r3 .r31 sBoth]) s
      fun u => u.mem = (s.mem.writeW (off (rvB s0) sEven) ((b64 (!cu)).setWidth 32)).writeW (off (rvB s0) sBoth)
        ((b64 (!cx && !cu)).setWidth 32) := by
    prun [ws.r31, exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sU < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sX < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sEven < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sBoth < 2 ^ 15 by decide),
      ws.scr.ld (show sU + 4 ≤ rvZ s0 by simp only [sU]; omega),
      ws.scr.ld (show sX + 4 ≤ rvZ s0 by simp only [sX]; omega),
      ws.scr.st (show sEven + 4 ≤ rvZ s0 by simp only [sEven]; omega),
      ws.scr.st (show sBoth + 4 ≤ rvZ s0 by simp only [sBoth]; omega),
      exec_li (show 1 < 2 ^ 15 by decide), exec_logic, h.slotRd hu vu, h.slotRd hx vx, b64_eq, b64_xor, b64_and]
  refine WP.mono (WP.keep opRegs hb (by decide)) fun t ⟨m, k⟩ => ⟨?_, k⟩
  have sep : sEven + 4 ≤ sBoth := by decide
  have kk : KeyWorkspace.Keep (rvB s0) (vw s0 b) [] [sEven, sBoth] s.mem t.mem := by
    rw [m]
    exact KeyWorkspace.Keep.trans (VG.Proof.Rsa.PPC64LE.Keys.keep_slot _ _ (by simp) (by simp only [sEven]; omega))
      (VG.Proof.Rsa.PPC64LE.Keys.keep_slot _ _ (by simp) (by simp only [sBoth]; omega))
  refine h.wrS2 (ws.of_keep k) (by decide) (by decide) sep kk ?_ ?_ hl k
  · rw [m, slot_wne _ _ _ (by decide) (by simp only [sBoth]; omega) (by simp only [sEven]; omega), VG.Proof.Rsa.PPC64LE.Keys.slot_write_self, b64_toNat]
  · rw [m, VG.Proof.Rsa.PPC64LE.Keys.slot_write_self, b64_toNat]

/-- `maskOf`: the mask := every check's flag. -/
theorem DS.mask (h : DS s0 b A live V ls s) {c0 c1 c2 c3 c4 c5 c6 : Bool}
    (h0 : sB0 ∈ ls) (h1 : sB1 ∈ ls) (h2 : sLt ∈ ls) (h3 : sExact ∈ ls) (h4 : sC1 ∈ ls) (h5 : sC2 ∈ ls)
    (h6 : sOk5 ∈ ls) (v0 : V sB0 = b2n c0) (v1 : V sB1 = b2n c1) (v2 : V sLt = b2n c2) (v3 : V sExact = b2n c3)
    (v4 : V sC1 = b2n c4) (v5 : V sC2 = b2n c5) (v6 : V sOk5 = b2n c6) :
    WP isa (.block maskOf) s fun t => DS s0 b A live (updV V VG.Impl.Rsa.PPC64LE.Recover.sMask
      (b2n ((((((!c0 && !c1) && c2) && c3) && !c4) && !c5) && c6))) [VG.Impl.Rsa.PPC64LE.Recover.sMask] t ∧
      Keep opRegs s t := by
  have ws := h.ws
  have hz := ws.hdr_le
  have nw := ws.nowrap
  simp only [KeyWorkspace.hdr] at hz
  have hb : WP isa (.block maskOf) s fun u => u.mem = s.mem.writeW (off (rvB s0) VG.Impl.Rsa.PPC64LE.Recover.sMask)
      ((b64 ((((((!c0 && !c1) && c2) && c3) && !c4) && !c5) && c6)).setWidth 32) := by
    prun [maskOf, ws.r31, exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sB0 < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sB1 < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sLt < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sExact < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sC1 < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sC2 < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sOk5 < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide)
        (show VG.Impl.Rsa.PPC64LE.Recover.sMask < 2 ^ 15 by decide),
      ws.scr.ld (show sB0 + 4 ≤ rvZ s0 by simp only [sB0]; omega),
      ws.scr.ld (show sB1 + 4 ≤ rvZ s0 by simp only [sB1]; omega),
      ws.scr.ld (show sLt + 4 ≤ rvZ s0 by simp only [sLt]; omega),
      ws.scr.ld (show sExact + 4 ≤ rvZ s0 by simp only [sExact]; omega),
      ws.scr.ld (show sC1 + 4 ≤ rvZ s0 by simp only [sC1]; omega),
      ws.scr.ld (show sC2 + 4 ≤ rvZ s0 by simp only [sC2]; omega),
      ws.scr.ld (show sOk5 + 4 ≤ rvZ s0 by simp only [sOk5]; omega),
      ws.scr.st (show VG.Impl.Rsa.PPC64LE.Recover.sMask + 4 ≤ rvZ s0 by
        simp only [VG.Impl.Rsa.PPC64LE.Recover.sMask, VG.Impl.Rsa.PPC64LE.CrtValues.sMask]; omega),
      exec_li (show 1 < 2 ^ 15 by decide), exec_logic, h.slotRd h0 v0, h.slotRd h1 v1, h.slotRd h2 v2,
      h.slotRd h3 v3, h.slotRd h4 v4, h.slotRd h5 v5, h.slotRd h6 v6, b64_eq, b64_xor, b64_and]
  refine WP.mono (WP.keep opRegs hb (by decide)) fun t ⟨m, k⟩ => ⟨?_, k⟩
  have hm : VG.Impl.Rsa.PPC64LE.Recover.sMask + 4 ≤ 2 ^ 64 := by decide
  have kk : KeyWorkspace.Keep (rvB s0) (vw s0 b) [] [VG.Impl.Rsa.PPC64LE.Recover.sMask] s.mem t.mem := by
    rw [m]; exact VG.Proof.Rsa.PPC64LE.Keys.keep_slot _ _ (by simp) hm
  have vv : slot t.mem (rvB s0) VG.Impl.Rsa.PPC64LE.Recover.sMask =
      b2n ((((((!c0 && !c1) && c2) && c3) && !c4) && !c5) && c6) := by
    rw [m, VG.Proof.Rsa.PPC64LE.Keys.slot_write_self, b64_toNat]
  exact h.wrS (ws.of_keep k) (by decide) kk vv (ls' := []) (by simp) k

/-! ## The blocks alone -/

theorem DS.setOneB (h : DS s0 b A live V ls s) {j : Nat} (hj : (b, j) ∈ live)
    {live' : List (Bool × Nat)} (hl : ∀ e ∈ live', e ∈ live ∧ Sep (b, j) e) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.Keys.setOne j)) s fun t =>
      DS s0 b (upd A b j (1 + 2 ^ 32 * (A b j / 2 ^ 32))) ((b, j) :: live') V ls t ∧ Keep opRegs s t := by
  rw [← List.append_nil (VG.Impl.Rsa.PPC64LE.Keys.setOne j)]
  exact h.setOne hj hl fun t ht k => WP.block_nil ⟨ht, k⟩

theorem DS.stBorrowB (h : DS s0 b A live V ls s) {sl c : Nat} (hsl : sl + 4 ≤ 160) (c9 : (s.gpr .r9).toNat = c)
    (hc : c ≤ 1) {ls' : List Nat} (hl : ∀ e ∈ ls', e ∈ ls ∧ (e + 4 ≤ sl ∨ sl + 4 ≤ e)) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.Keys.stBorrow sl)) s fun t =>
      DS s0 b A live (updV V sl c) (sl :: ls') t ∧ Keep opRegs s t := by
  rw [← List.append_nil (VG.Impl.Rsa.PPC64LE.Keys.stBorrow sl)]
  exact h.stBorrow hsl c9 hc hl fun t ht k => WP.block_nil ⟨ht, k⟩

theorem DS.bitOfB (h : DS s0 b A live V ls s) {j sl : Nat} (hj : (b, j) ∈ live) (hsl : sl + 4 ≤ 160)
    {ls' : List Nat} (hl : ∀ e ∈ ls', e ∈ ls ∧ (e + 4 ≤ sl ∨ sl + 4 ≤ e)) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.Keys.bitOf sl j)) s fun t =>
      DS s0 b A live (updV V sl (A b j % 2)) (sl :: ls') t ∧ Keep opRegs s t := by
  rw [← List.append_nil (VG.Impl.Rsa.PPC64LE.Keys.bitOf sl j)]
  exact h.bitOf hj hsl hl fun t ht k => WP.block_nil ⟨ht, k⟩

theorem DS.clrWB (h : DS s0 b A live V ls s) {j : Nat} (hj : (b, j) ∈ live)
    {live' : List (Bool × Nat)} (hl : ∀ e ∈ live', e ∈ live ∧ Sep (b, j) e) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.Recover.clrW j)) s fun t =>
      DS s0 b (upd A b j (A b j)) ((b, j) :: live') V ls t ∧
      w32 t.mem (rvB s0) (arr (vw s0 b) j + 4 * vw s0 b) = 0 ∧ Keep [.r0, .r5] s t := by
  rw [← List.append_nil (VG.Impl.Rsa.PPC64LE.Recover.clrW j)]
  exact h.clrW hj hl fun t ht z k => WP.block_nil ⟨ht, z, k⟩

theorem DS.toNB (h : DS s0 true A live V ls s) :
    WP isa (.block VG.Impl.Rsa.PPC64LE.Recover.ctxw) s fun t => DS s0 false A live V ls t ∧ Keep [.r29, .r30] s t := by
  rw [← List.append_nil VG.Impl.Rsa.PPC64LE.Recover.ctxw]
  exact h.toN fun t ht k => WP.block_nil ⟨ht, k⟩

theorem DS.toWB (h : DS s0 false A live V ls s) :
    WP isa (.block VG.Impl.Rsa.PPC64LE.Recover.ctxW) s fun t => DS s0 true A live V ls t ∧ Keep [.r29, .r30] s t := by
  rw [← List.append_nil VG.Impl.Rsa.PPC64LE.Recover.ctxW]
  exact h.toW fun t ht k => WP.block_nil ⟨ht, k⟩

end

end VG.Proof.Rsa.PPC64LE.RecDet
