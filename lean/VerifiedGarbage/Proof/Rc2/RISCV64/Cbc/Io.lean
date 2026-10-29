module

public import VerifiedGarbage.Impl.Rc2.RISCV64.Cbc
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Rc2.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd

/-!
# RC2-CBC on RISC-V: the blocks' bytes

The CBC code reads and writes the IV and the data a byte at a time, as
little-endian doublewords (`Bytes.loadLE64_ok`, `Bytes.storeLE64_ok`):
`before_run` and `after_run` state each of its blocks as the PPC64LE proofs'
single loads and stores (`Proof/Rc2/PPC64LE/Cbc/Body.lean`).
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Cbc

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Cbc
open VG.Impl.Words.RISCV64 (loadLE64 storeLE64)

/-- The doubleword's second word, from the region holding the doubleword. -/
theorem in8_hi {rs : List Region} {p : Addr} (h : InRegions rs p 8) : InRegions rs (p + BitVec.ofNat 64 4) 4 := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : p + BitVec.ofNat 64 4 - r.base = p - r.base + BitVec.ofNat 64 4 := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 4),
      ← BitVec.add_assoc]
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((p - r.base).toNat + 4 % 2 ^ 64) (2 ^ 64)
  omega

theorem in8_lo {rs : List Region} {p : Addr} (h : InRegions rs p 8) : InRegions rs (p + BitVec.ofNat 64 0) 4 := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains, BitVec.add_zero] at hc ⊢
  omega

theorem load64_run {d n : Reg} (hdn : d ≠ n) (h7n : Reg.a7 ≠ n) (h1n : Reg.t1 ≠ n) (hd7 : d ≠ .a7)
    (hd1 : d ≠ .t1) (u : State) {p : Addr} (hp : u.gpr n = p) (hr : InRegions (u.rd ++ u.wr) p 8) :
    WP isa (.block (loadLE64 d .a7 .t1 n 0)) u fun t =>
      t.gpr d = u.mem.readW p 64 ∧ t.mem = u.mem ∧ Keep [d, .a7, .t1] u t := by
  rw [← hp] at hr
  refine WP.mono (Bytes.loadLE64_ok hdn h7n h1n hd7 hd1 (by decide) (by decide) (in8_lo hr) (in8_hi hr))
    fun t ⟨a, g, m, rd, wr, _⟩ => ⟨by rw [a, BitVec.add_zero, hp], m, fun r hr => ?_, rd, wr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact g r hr.1 hr.2.1 hr.2.2

theorem store64_run {v n : Reg} (hv7 : Reg.a7 ≠ v) (h7n : Reg.a7 ≠ n) (h1n : Reg.t1 ≠ n) (u : State) {p : Addr}
    (hp : u.gpr n = p) (hw : InRegions u.wr p 8) :
    WP isa (.block (storeLE64 v .a7 .t1 n 0)) u fun t =>
      t.mem = u.mem.writeW p (u.gpr v) ∧ Keep [.a7, .t1] u t := by
  rw [← hp] at hw
  refine WP.mono (Bytes.storeLE64_ok hv7 h7n h1n (by decide) (by decide) (in8_lo hw) (in8_hi hw))
    fun t ⟨m, g, rd, wr, _⟩ => ⟨?_, fun r hr => ?_, rd, wr⟩
  · rw [m, BitVec.add_zero, show (0 + 4 : Nat) = 4 from rfl, Words64.writeW64_split, hp]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact g r hr.1 hr.2

/-- The block at `s3` XORed with the chaining value at `s2`, in place. -/
theorem xorIv_run (u : State) {p I : Addr} (h3 : u.gpr .s3 = p) (h2 : u.gpr .s2 = I)
    (hpr : InRegions (u.rd ++ u.wr) p 8) (hpw : InRegions u.wr p 8) (hir : InRegions (u.rd ++ u.wr) I 8) :
    WP isa (.block xorIv) u fun t =>
      t.mem = u.mem.writeW p (u.mem.readW p 64 ^^^ u.mem.readW I 64) ∧ Keep [.t0, .a7, .t1, .t2] u t := by
  unfold xorIv
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (load64_run (d := .t0) (n := .s3) (p := p) (by decide) (by decide) (by decide) (by decide) (by decide)
    u h3 hpr) fun t₁ ⟨a₁, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (load64_run (d := .t2) (n := .s2) (p := I) (by decide) (by decide) (by decide) (by decide)
    (by decide) t₁ (by rw [k₁.gpr (by decide), h2]) (by rw [k₁.2.1, k₁.2.2]; exact hir)) fun t₂ ⟨a₂, m₂, k₂⟩ => ?_
  rw [List.singleton_append, WP.block_cons_iff]
  let t₃ := t₂.write .t0 (t₂.gpr .t0 ^^^ t₂.gpr .t2)
  have k₃ : Keep [.t0] t₂ t₃ := ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ (by simpa using hr), rfl, rfl⟩
  refine ⟨t₃, rfl, ?_⟩
  refine WP.mono (store64_run (v := .t0) (n := .s3) (p := p) (by decide) (by decide) (by decide) t₃
    (by rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide), h3])
    (by rw [k₃.2.2, k₂.2.2, k₁.2.2]; exact hpw)) fun t ⟨m, k⟩ =>
      ⟨?_, (((k₁.trans k₂).trans k₃).trans k).mono (by simp)⟩
  rw [m, RegUpd.mem_write, RegUpd.gpr_write_self, m₂, m₁, k₂.gpr (by decide), a₁, a₂, m₁]

theorem args_run (u : State) {T p W : Addr} (h1 : u.gpr .s1 = T) (h3 : u.gpr .s3 = p) (h5 : u.gpr .s5 = W) :
    WP isa (.block args) u fun t => t.gpr .a0 = T ∧ t.gpr .a1 = p ∧ t.gpr .a2 = W ∧ t.mem = u.mem ∧
      Keep [.a0, .a1, .a2] u t :=
  WP.mono (WP.keep [.a0, .a1, .a2] (c := .block args) (Q := fun t => t.gpr .a0 = T ∧ t.gpr .a1 = p ∧
      t.gpr .a2 = W ∧ t.mem = u.mem) (by unfold args; rrun [mov, h1, h3, h5]) (by rfl) rfl)
    fun _ ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, c, d, k⟩

theorem advance_run (u : State) {p : Addr} {X : BitVec 64} (h3 : u.gpr .s3 = p) (h4 : u.gpr .s4 = X) :
    WP isa (.block advance) u fun t => t.gpr .s3 = p + 8#64 ∧ t.gpr .s4 = X - 1#64 ∧ t.mem = u.mem ∧
      Keep [.s3, .s4] u t :=
  WP.mono (WP.keep [.s3, .s4] (c := .block advance) (Q := fun t => t.gpr .s3 = p + 8#64 ∧ t.gpr .s4 = X - 1#64 ∧
      t.mem = u.mem) (by unfold advance; rrun [h3, h4]) (by rfl) rfl)
    fun _ ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, c, k⟩

theorem beforeEnc_run (t : State) {T p I W : Addr} (h1 : t.gpr .s1 = T) (h2 : t.gpr .s2 = I)
    (h3 : t.gpr .s3 = p) (h5 : t.gpr .s5 = W) (hpr : InRegions (t.rd ++ t.wr) p 8) (hpw : InRegions t.wr p 8)
    (hir : InRegions (t.rd ++ t.wr) I 8) :
    WP isa (.block (before .encrypt)) t fun t₁ => t₁.gpr .a0 = T ∧ t₁.gpr .a1 = p ∧ t₁.gpr .a2 = W ∧
      t₁.mem = t.mem.writeW p (t.mem.readW p 64 ^^^ t.mem.readW I 64) ∧
      Keep [.t0, .a7, .t1, .t2, .a0, .a1, .a2] t t₁ := by
  unfold before
  rw [WP.block_append_iff]
  refine WP.mono (xorIv_run t h3 h2 hpr hpw hir) fun u ⟨m, k⟩ => ?_
  refine WP.mono (args_run u (by rw [k.gpr (by decide), h1]) (by rw [k.gpr (by decide), h3])
    (by rw [k.gpr (by decide), h5])) fun t₁ ⟨a, b, c, m₁, k₁⟩ => ⟨a, b, c, by rw [m₁, m], k.trans k₁⟩

theorem beforeDec_run (t : State) {T p W : Addr} (h1 : t.gpr .s1 = T) (h3 : t.gpr .s3 = p) (h5 : t.gpr .s5 = W)
    (hpr : InRegions (t.rd ++ t.wr) p 8) :
    WP isa (.block (before .decrypt)) t fun t₁ => t₁.gpr .a0 = T ∧ t₁.gpr .a1 = p ∧ t₁.gpr .a2 = W ∧
      t₁.gpr .s6 = t.mem.readW p 64 ∧ t₁.mem = t.mem ∧ Keep [.s6, .a7, .t1, .a0, .a1, .a2] t t₁ := by
  unfold before
  rw [WP.block_append_iff]
  refine WP.mono (load64_run (d := .s6) (n := .s3) (p := p) (by decide) (by decide) (by decide) (by decide)
    (by decide) t h3 hpr) fun u ⟨a₀, m, k⟩ => ?_
  refine WP.mono (args_run u (by rw [k.gpr (by decide), h1]) (by rw [k.gpr (by decide), h3])
    (by rw [k.gpr (by decide), h5])) fun t₁ ⟨a, b, c, m₁, k₁⟩ =>
      ⟨a, b, c, by rw [k₁.gpr (by decide), a₀], by rw [m₁, m], k.trans k₁⟩

theorem afterEnc_run (t : State) {p I : Addr} {X : BitVec 64} (h2 : t.gpr .s2 = I) (h3 : t.gpr .s3 = p)
    (h4 : t.gpr .s4 = X) (hpr : InRegions (t.rd ++ t.wr) p 8) (hiw : InRegions t.wr I 8) :
    WP isa (.block (after .encrypt ++ advance)) t fun t₃ => t₃.gpr .s3 = p + 8#64 ∧ t₃.gpr .s4 = X - 1#64 ∧
      t₃.mem = t.mem.writeW I (t.mem.readW p 64) ∧ Keep [.t0, .a7, .t1, .s3, .s4] t t₃ := by
  unfold after
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (load64_run (d := .t0) (n := .s3) (p := p) (by decide) (by decide) (by decide) (by decide)
    (by decide) t h3 hpr) fun u ⟨a₀, m₀, k₀⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (store64_run (v := .t0) (n := .s2) (p := I) (by decide) (by decide) (by decide) u
    (by rw [k₀.gpr (by decide), h2]) (by rw [k₀.2.2]; exact hiw)) fun u₁ ⟨m₁, k₁⟩ => ?_
  refine WP.mono (advance_run u₁ (by rw [k₁.gpr (by decide), k₀.gpr (by decide), h3])
    (by rw [k₁.gpr (by decide), k₀.gpr (by decide), h4])) fun t₃ ⟨a, b, m, k⟩ =>
      ⟨a, b, by rw [m, m₁, a₀, m₀], ((k₀.trans k₁).trans k).mono (by simp)⟩

theorem afterDec_run (t : State) {p I : Addr} {X c : BitVec 64} (h2 : t.gpr .s2 = I) (h3 : t.gpr .s3 = p)
    (h4 : t.gpr .s4 = X) (h6 : t.gpr .s6 = c) (hpr : InRegions (t.rd ++ t.wr) p 8) (hpw : InRegions t.wr p 8)
    (hir : InRegions (t.rd ++ t.wr) I 8) (hiw : InRegions t.wr I 8) :
    WP isa (.block (after .decrypt ++ advance)) t fun t₃ => t₃.gpr .s3 = p + 8#64 ∧ t₃.gpr .s4 = X - 1#64 ∧
      t₃.mem = (t.mem.writeW p (t.mem.readW p 64 ^^^ t.mem.readW I 64)).writeW I c ∧
      Keep [.t0, .a7, .t1, .t2, .s3, .s4] t t₃ := by
  unfold after
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (xorIv_run t h3 h2 hpr hpw hir) fun u ⟨m₀, k₀⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (store64_run (v := .s6) (n := .s2) (p := I) (by decide) (by decide) (by decide) u
    (by rw [k₀.gpr (by decide), h2]) (by rw [k₀.2.2]; exact hiw)) fun u₁ ⟨m₁, k₁⟩ => ?_
  refine WP.mono (advance_run u₁ (by rw [k₁.gpr (by decide), k₀.gpr (by decide), h3])
    (by rw [k₁.gpr (by decide), k₀.gpr (by decide), h4])) fun t₃ ⟨a, b, m, k⟩ =>
      ⟨a, b, by rw [m, m₁, m₀, k₀.gpr (by decide), h6], ((k₀.trans k₁).trans k).mono (by simp)⟩

end VG.Proof.Rc2.RISCV64.Cbc
