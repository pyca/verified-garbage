module
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime
public import VerifiedGarbage.Impl.Ed448.X86_64.Window
public import VerifiedGarbage.Proof.X448.X86_64.Env
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Sig

import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.X448.X86_64.Setup
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! Direct lookup of a public verification digit in the projective table. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window
open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window
open VG.Proof.X448.X86_64
open VG.Impl.X448.X86_64 (W slot stores)

theorem keyAddress_ok (s : State) {d : Nat} (hd : d < 17)
    (hr : s.gpr .r15 = BitVec.ofNat 64 d) :
    WP isa (.block keyAddress) s fun u =>
      u.gpr .r15 = BitVec.ofNat 64 (192 * d) ∧ Keeps [.rax, .rdx, .r15] s u := by
  have hm : ∀ d < 17, BitVec.ofNat 64 d * BitVec.ofNat 64 192 = BitVec.ofNat 64 (192 * d) := by
    decide +kernel
  xrun [keyAddress, hr]
  refine ⟨?_, fun r h => ?_, rfl, rfl, rfl⟩
  · exact hm d hd
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, h.1, h.2.1, h.2.2, ite_false]

private theorem ea_key {s : State} {base : Addr} {d c i : Nat}
    (hb : s.gpr .rdi = base) (hd : s.gpr .r15 = BitVec.ofNat 64 (192 * d)) :
    s.ea { base := .rdi, index := some .r15, disp := ((TAB + 64 * c + 8 * i : Nat) : Int) } =
      off base (tabOffset d c + 8 * i) := by
  simp only [State.ea, hb, hd, off, tabOffset, BitVec.ofInt_natCast]
  simp only [BitVec.mul_one, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  omega

private theorem ea_key_set (s : State) (r : Reg) (v : BitVec 64) (c i : Nat)
    (h1 : r ≠ .rdi) (h2 : r ≠ .r15) :
    (s.setReg r v).ea { base := .rdi, index := some .r15, disp := ((TAB + 64 * c + 8 * i : Nat) : Int) } =
      s.ea { base := .rdi, index := some .r15, disp := ((TAB + 64 * c + 8 * i : Nat) : Int) } := by
  simp only [State.ea, RegUpd.gpr_setReg, Ne.symm h1, Ne.symm h2, ite_false]

theorem directKeyLoads_ok {s : State} {base : Addr} (hs : Scr s base) {d c : Nat}
    (hd : d < 17) (hc : c < 3) (hr : s.gpr .r15 = BitVec.ofNat 64 (192 * d)) :
    WP isa (.block ((W.zip (List.range 7)).map fun (r, i) =>
      .mov r (.mem { base := .rdi, index := some .r15, disp := ((TAB + 64 * c + 8 * i : Nat) : Int) }))) s
      fun u => rv u W = fe s.mem base (tabOffset d c) ∧ Keeps W s u := by
  have hread : ∀ i < 7, InRegions (s.rd ++ s.wr) (off base (tabOffset d c + 8 * i)) 8 :=
    fun i hi => hs.read (by simp only [tabOffset, TAB]; omega)
  apply WP.of_runBlock
  simp (disch := decide) only [W, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
    runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_key_set, ea_key hs.rdi hr, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    ite_true, hread 0 (by decide), hread 1 (by decide),
    hread 2 (by decide), hread 3 (by decide), hread 4 (by decide), hread 5 (by decide), hread 6 (by decide),
    Option.map_some, Option.some.injEq, exists_eq_left']
  constructor
  · simp only [rv, fe, mv, VG.Proof.X448.X86_64.word, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false,
      Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd]
  · refine ⟨fun r h => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp only [RegUpd.gpr_setReg, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2, ite_false]


theorem directKeyCoord_ok {s : State} {base : Addr} (hs : Scr s base)
    {d c : Nat} (hd : d < 17) (hc : c < 3)
    (hr : s.gpr .r15 = BitVec.ofNat 64 (192 * d)) :
    WP isa (.block (directKeyCoord c)) s fun u =>
      Keep base s u ∧ u.gpr .r15 = s.gpr .r15 ∧
      E u.mem base = Function.update (E s.mem base) ⟨8 + c, by omega⟩ (F s.mem base (tabOffset d c)) := by
  rw [directKeyCoord, WP.block_append_iff]
  refine WP.mono (directKeyLoads_ok hs hd hc hr) fun v ⟨ev, kv⟩ => ?_
  refine WP.mono (stores_E (hs.of_keeps kv (by decide)) ⟨8 + c, by omega⟩ W rfl)
    fun u ⟨eu, ou, gu, ru, wu⟩ => ?_
  refine ⟨⟨?_, ru.trans kv.2.2.1, wu.trans kv.2.2.2, ?_⟩,
    (gu _).trans (kv.1 _ (by decide)), ?_⟩
  · intro r h
    exact (gu r).trans (kv.1 r (fun hh => h ((show ∀ r ∈ W, r ∈ clob from by decide) r hh)))
  · rw [kv.2.1] at ou
    exact ou.mono (by simp only [slot]; omega) (by simp only [slot]; omega)
  · rw [eu, ev, kv.2.1]

end VG.Proof.Ed448.X86_64.Window
