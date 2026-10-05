import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy

/-!
# Short Weierstrass curves on AArch64: words to and from big-endian bytes

The steps of the loads and stores of numbers as bytes (`BytesLen.lean`): a
word loaded and byte-reversed (`rev`, which is `byteRev64`), masked and
byte-reversed, and stored.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

theorem rev64_eq (w : BitVec 64) : rev64 w = byteRev64 w := rfl

/-- The words of a region are accessible. -/
theorem inRegions_words {rs : List Region} {p : Addr} {len : Nat} (h : (⟨p, len⟩ : Region) ∈ rs)
    (hl : len ≤ 2 ^ 64) : ∀ d, d + 8 ≤ len → InRegions rs (p + BitVec.ofNat 64 d) 8 :=
  fun _ hd => ⟨_, h, Offset.contains_base p hd (by omega)⟩

/-- `t = byteRev64 [r + e]`, through `t`. -/
theorem ldRev_ok (s : State) {r t : Reg} {e : Nat} (he : e % 8 = 0 ∧ e < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 e) 8) :
    WP isa (.block [.ldr .x t r e, .rev t t]) s fun s' =>
      s'.gpr t = byteRev64 (s.mem.readW (s.gpr r + BitVec.ofNat 64 e) 64) ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_ldr_x he hr, runStep_some, runBlock_nil, exec_rev, read_x,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  rw [RegUpd.gpr_write_of_ne _ _ _ hq, RegUpd.gpr_write_of_ne _ _ _ hq]

/-- `x1 = byteRev64 (x1 & x3)`. -/
theorem andRev_ok (s : State) :
    WP isa (.block [.logic .and .x .x1 .x1 .x3, .rev .x1 .x1]) s fun s' =>
      s'.gpr .x1 = byteRev64 (s.gpr .x1 &&& s.gpr .x3) ∧ Keeps [.x1] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  rw [RegUpd.gpr_write_of_ne _ _ _ hq, RegUpd.gpr_write_of_ne _ _ _ hq]

/-- `[r + e] = t`. -/
theorem strReg_ok (s : State) {r t : Reg} {e : Nat} (he : e % 8 = 0 ∧ e < 32768)
    (hw : InRegions s.wr (s.gpr r + BitVec.ofNat 64 e) 8) :
    WP isa (.block [.str .x t r e]) s fun s' =>
      s' = { s with mem := s.mem.writeW (s.gpr r + BitVec.ofNat 64 e) (s.gpr t) } := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_str_x he hw, runStep_some, runBlock_nil, Option.some.injEq,
    exists_eq_left']

end VG.Proof.Weierstrass.AArch64
