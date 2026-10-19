module
public import VerifiedGarbage.Impl.Ed448.X86_64.Wnaf.Recode
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Mask
public import VerifiedGarbage.Proof.Framework.Sig

import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Digit

/-! Reading a bounded lookahead from the scalar's expanded bits. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG VG.X86_64 VG.Impl.Ed448.X86_64.Wnaf
open VG.Proof.X448.X86_64
open VG.Proof.Ed448.X86_64.Window

private theorem ea_set (s : State) (r : Reg) (v : BitVec 64) (o : Nat)
    (hr : r ≠ .rdi) (hb : r ≠ .rbx) :
    (s.setReg r v).ea { base := .rdi, index := some .rbx, disp := (o : Int) } =
      s.ea { base := .rdi, index := some .rbx, disp := (o : Int) } := by
  simp only [State.ea, RegUpd.gpr_setReg, Ne.symm hr, Ne.symm hb, ite_false]

private theorem ea_flags (s : State) (v : BitVec 64) (c f : Bool) (o : Nat) :
    (arithFlags s v c f).ea { base := .rdi, index := some .rbx, disp := (o : Int) } =
      s.ea { base := .rdi, index := some .rbx, disp := (o : Int) } := rfl

private theorem pack_ok : ∀ a < 2, ∀ b < 2, ∀ c < 2, ∀ d < 2, ∀ e < 2,
    let aa := (BitVec.ofNat 8 a).setWidth 64
    let bb := (BitVec.ofNat 8 b).setWidth 64
    let cc := (BitVec.ofNat 8 c).setWidth 64
    let dd := (BitVec.ofNat 8 d).setWidth 64
    let ee := (BitVec.ofNat 8 e).setWidth 64
    (((ee + ee + dd) + (ee + ee + dd) + cc) + ((ee + ee + dd) + (ee + ee + dd) + cc) + bb) +
      (((ee + ee + dd) + (ee + ee + dd) + cc) + ((ee + ee + dd) + (ee + ee + dd) + cc) + bb) + aa =
      BitVec.ofNat 64 (a + 2 * b + 4 * c + 8 * d + 16 * e) := by decide +kernel

theorem loadBits_ok {s : State} {base : Addr} (hs : Scr s base) {o t : Nat}
    (ho : o + 460 ≤ 8192) (ht : t < 456) (hb : s.gpr .rbx = BitVec.ofNat 64 t)
    {a b c d e : Nat} (ha : a < 2) (hb' : b < 2) (hc : c < 2) (hd : d < 2) (he : e < 2)
    (ba : s.mem (off base (o + t)) = BitVec.ofNat 8 a)
    (bb : s.mem (off base (o + 1 + t)) = BitVec.ofNat 8 b)
    (bc : s.mem (off base (o + 2 + t)) = BitVec.ofNat 8 c)
    (bd : s.mem (off base (o + 3 + t)) = BitVec.ofNat 8 d)
    (be : s.mem (off base (o + 4 + t)) = BitVec.ofNat 8 e) :
    WP isa (.block (loadBits o)) s fun u =>
      u.gpr .rax = BitVec.ofNat 64 (a + 2 * b + 4 * c + 8 * d + 16 * e) ∧
      u.gpr .rdx = BitVec.ofNat 64 a ∧ Keeps [.rax, .rdx] s u := by
  have hr : ∀ i ≤ 4, InRegions (s.rd ++ s.wr) (off base (o + i + t)) 1 :=
    fun i hi => hs.read (by omega)
  have hr0 : InRegions (s.rd ++ s.wr) (off base (o + t)) 1 := by
    simpa only [Nat.add_zero] using hr 0 (by decide)
  apply WP.of_runBlock
  simp only [loadBits, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load8,
    execAlu, ea_set _ .rax _ _ (by decide) (by decide), ea_set _ .rdx _ _ (by decide) (by decide),
    ea_flags, ea_bitsAt hs.rdi hb, Nat.add_zero, hr0, hr 1 (by decide), hr 2 (by decide),
    hr 3 (by decide), hr 4 (by decide), ba, bb, bc, bd, be,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨pack_ok a ha b hb' c hc d hd e he, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h : ∀ a < 2, (BitVec.ofNat 8 a).setWidth 64 = BitVec.ofNat 64 a := by decide +kernel
    exact h a ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

theorem loadBits_bits_ok {s : State} {base : Addr} (hs : Scr s base) {o k t : Nat}
    (ho : o + 460 ≤ 8192) (hlo : 1 ≤ o) (ht : t < 456)
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base o k s) :
    WP isa (.block (loadBits o)) s fun u =>
      u.gpr .rax = BitVec.ofNat 64 (k / 2 ^ t % 32) ∧
      u.gpr .rdx = BitVec.ofNat 64 (k / 2 ^ t % 2) ∧ Keeps [.rax, .rdx] s u := by
  have bit (i : Nat) (hi : i ≤ 4) :
      s.mem (off base (o + i + t)) = BitVec.ofNat 8 (k / 2 ^ (t + i) % 2) := by
    rw [show o + i + t = o + (t + i) by omega]
    exact bs.bit hlo (by omega)
  have he : k / 2 ^ t % 32 = k / 2 ^ t % 2 + 2 * (k / 2 ^ (t + 1) % 2) +
      4 * (k / 2 ^ (t + 2) % 2) + 8 * (k / 2 ^ (t + 3) % 2) + 16 * (k / 2 ^ (t + 4) % 2) := by
    simp only [Nat.pow_add, ← Nat.div_div_eq_div_mul]
    omega
  have b0 := bit 0 (by decide)
  simp only [Nat.add_zero] at b0
  refine WP.mono (loadBits_ok hs ho ht hb
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    b0 (bit 1 (by decide)) (bit 2 (by decide)) (bit 3 (by decide)) (bit 4 (by decide)))
    fun u ⟨hu, hd, hk⟩ => ⟨?_, hd, hk⟩
  rw [hu, he]

end VG.Proof.Ed448.X86_64.Wnaf
