module

public import VerifiedGarbage.Impl.X25519.AArch64.AltLadder
public import VerifiedGarbage.Proof.X25519.AArch64.Word.Head
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! # The bit of an iteration of the `_alt` ladder, and the flag `mux_4` reads -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.AltLadder
open VG VG.AArch64 VG.Proof.X25519 VG.Proof.Ed25519.AArch64 VG.Proof.X25519.AArch64.Word

theorem zf_addWithCarry (s : State) (sz : Size) (d : Reg) (a b : BitVec sz.bits) (c : Bool) :
    (s.addWithCarry sz d a b c).zf = decide (a + b + BitVec.ofNat sz.bits c.toNat = 0) := rfl

theorem subs_ok {s : State} {sw kt : Nat} (hsw : sw ≤ 1) (hkt : kt ≤ 1)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 sw) (h2 : s.gpr .x2 = BitVec.ofNat 64 kt) :
    WP isa (.block [.subs .x .x3 .x3 .x2]) s fun t =>
      t.zf = (sw == kt) ∧ Keeps [.x3] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, VG.Proof.X25519.AArch64.Alt.exec_subs_x, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [zf_addWithCarry, h3, h2]
    rcases (by omega : sw = 0 ∨ sw = 1) with rfl | rfl <;>
      rcases (by omega : kt = 0 ∨ kt = 1) with rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_addWithCarry, hr, ite_false]

/-- `bitFlags`: bit `i` of the scalar stored as the new swap, `Z` set if it is
the old swap, and the counter decremented. -/
theorem bitFlags_ok {base : Addr} {s : State} (hs : Scratch s base) {i sw kt : Nat}
    (hi : i < 255) (hsw : sw ≤ 1) (hkt : kt ≤ 1)
    (hc : s.gpr .x19 = BitVec.ofNat 64 (i+1))
    (hswap : word s.mem base 768 = BitVec.ofNat 64 sw)
    (hb : s.mem (off base (bitOffset+i)) = BitVec.ofNat 8 kt) :
    WP isa (.block VG.Impl.X25519.AArch64.AltLadder.bitFlags) s fun t =>
      LoopKeep base s t ∧
      (∀ r, r ≠ .x19 → r ≠ .x8 → r ≠ .x2 → r ≠ .x3 → t.gpr r = s.gpr r) ∧
      env t.mem base = env s.mem base ∧ t.gpr .x19 = BitVec.ofNat 64 i ∧ t.zf = (sw == kt) ∧
      word t.mem base 768 = BitVec.ofNat 64 kt ∧ Outside base 768 8 s.mem t.mem := by
  change WP isa (.block (([.subImm .x .x19 .x19 1, .add .x .x8 .x0 .x19,
    .ldrb .x2 .x8 bitOffset] : List Instr) ++
    ([VG.Impl.Ed25519.AArch64.ld .x3 768] ++
    ([VG.Impl.Ed25519.AArch64.st .x2 768] ++ ([.subs .x .x3 .x3 .x2] : List Instr))))) s _
  rw [WP.block_append_iff]
  refine WP.mono (loadBit_ok hs hi hkt hc hb) fun a ⟨ac, ak, ka⟩ => ?_
  have kla : LoopKeep base s a := LoopKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (kla.scratch hs) (d := 768) (by decide) (by decide) .x3)
    fun b ⟨bs, kb⟩ => ?_
  have klb : LoopKeep base s b := kla.trans (LoopKeep.of_keeps kb (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (storeSwap_ok (klb.scratch hs)) fun c ⟨klc, ec, sc, gc, oc⟩ => ?_
  have ck : c.gpr .x2 = BitVec.ofNat 64 kt := by rw [gc, kb.gpr _ (by decide), ak]
  have cs : c.gpr .x3 = BitVec.ofNat 64 sw := by rw [gc, bs, ka.mem, hswap]
  refine WP.mono (subs_ok hsw hkt cs ck) fun t ⟨tz, kt'⟩ => ?_
  refine ⟨(klb.trans klc).trans (LoopKeep.of_keeps kt' (by decide)), fun r h19 h8 h2 h3 => ?_,
    ?_, ?_, tz, ?_, ?_⟩
  · rw [kt'.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact h3), gc,
      kb.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact h3),
      ka.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h19, h8, h2⟩)]
  · rw [kt'.mem, ec, kb.mem, ka.mem]
  · rw [kt'.gpr _ (by decide), gc, kb.gpr _ (by decide), ac]
  · rw [kt'.mem, sc, kb.gpr _ (by decide), ak]
  · rw [kt'.mem, ← ka.mem, ← kb.mem]
    exact oc

end VG.Proof.X25519.AArch64.AltLadder
