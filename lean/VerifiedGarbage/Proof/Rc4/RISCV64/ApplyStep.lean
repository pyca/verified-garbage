module

import VerifiedGarbage.Proof.Rc4.RISCV64.Replace
import VerifiedGarbage.Proof.Rc4.Memory
public import VerifiedGarbage.Proof.Rc4.RISCV64.Lookup
public import VerifiedGarbage.Spec.Rc4
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep

/-! # RC4 on RISC-V: one PRGA step, on the table in the frame -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Spec.Rc4 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

/-- `i += 1`, then `j += S[i]`, copied to the index of the replacement. -/
def applyBefore : List Instr :=
  ([.addi .a3 .a3 1, .shift .sll .d .a3 .a3 56, .shift .srl .d .a3 .a3 56] : List Instr) ++ loadI ++
    ([.add .t4 .t4 .t0, .shift .sll .d .t4 .t4 56, .shift .srl .d .t4 .t4 56, .logic .or .a4 .t4 .t4] :
      List Instr)

/-- `S[i] := S[j]` (in `a5`), and the index `S[i] + S[j]` of the keystream byte. -/
def applyMiddle : List Instr :=
  loadI ++ ([.store .b .a5 .t2 0, .add .a4 .a5 .t0, .shift .sll .d .a4 .a4 56,
    .shift .srl .d .a4 .a4 56] : List Instr)

/-- The keystream byte XORed into the data. -/
def applyAfter : List Instr :=
  [.load .b .t0 .a1 0, .logic .xor .t0 .t0 .a5, .store .b .t0 .a1 0, .addi .a1 .a1 1,
    .addi .a2 .a2 (-1)]

theorem applyStep_eq :
    applyStep = applyBefore ++ (replace ++ (applyMiddle ++ (lookup ++ applyAfter))) := by
  simp only [applyStep, applyBefore, applyMiddle, applyAfter, List.append_assoc]

theorem apply_before (s : State) (i j : Byte)
    (hcx : s.gpr .a3 = i.setWidth 64) (h7 : s.gpr .t4 = j.setWidth 64)
    (hp : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256) :
    WP isa (.block applyBefore) s fun t =>
      t.gpr .a3 = (i + 1#8).setWidth 64 ∧
      t.gpr .t4 = (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.gpr .a4 = (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      Keep [.t0, .a3, .t4, .a4, .t2] s t ∧ t.mem = s.mem := by
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .a7 + (i + 1#8).setWidth 64) 1 := by
    rw [byte_addr (i + 1#8)]
    exact region_offset _ _ _ _ _ (by have := (i + 1#8).isLt; omega)
      (by have := (i + 1#8).isLt; omega) hp
  refine WP.mono (WP.keep (Q := fun t => t.gpr .a3 = (i + 1#8).setWidth 64 ∧
      t.gpr .t4 = (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.gpr .a4 = (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.mem = s.mem) [.t0, .a3, .t4, .a4, .t2] ?_ (by decide +kernel))
    fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, hk, h.2.2.2⟩
  unfold applyBefore loadI
  rrun [hcx, h7, byte_inc, hi, BitVec.or_self]
  rw [byte_addr (i + 1#8), byte_add]

theorem apply_middle (s : State) (ii b : Byte)
    (hcx : s.gpr .a3 = ii.setWidth 64) (hax : s.gpr .a5 = b.setWidth 64)
    (hw : InRegions s.wr (s.gpr .a7 + BitVec.ofNat 64 ii.toNat) 1) :
    WP isa (.block applyMiddle) s fun t =>
      t.mem = s.mem.write (s.gpr .a7 + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .a4 = (b + s.mem (s.gpr .a7 + BitVec.ofNat 64 ii.toNat)).setWidth 64 ∧
      Keep [.t0, .a4, .t2] s t := by
  have hw' : InRegions s.wr (s.gpr .a7 + ii.setWidth 64) 1 := by rw [byte_addr ii]; exact hw
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .a7 + ii.setWidth 64) 1 := by
    obtain ⟨r, hr, hc⟩ := hw'
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .a7 + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .a4 = (b + s.mem (s.gpr .a7 + BitVec.ofNat 64 ii.toNat)).setWidth 64)
      [.t0, .a4, .t2] ?_ (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  unfold applyMiddle loadI
  rrun [hcx, hax, hw', hr, low_byte, byte_add]
  rw [byte_addr ii]
  exact ⟨rfl, rfl⟩

theorem apply_after (s : State) (k : Byte) (hax : s.gpr .a5 = k.setWidth 64)
    (hd : InRegions s.wr (s.gpr .a1) 1) :
    WP isa (.block applyAfter) s fun t =>
      t.mem = s.mem.write (s.gpr .a1) 1 (s.mem (s.gpr .a1) ^^^ k) ∧
      t.gpr .a1 = s.gpr .a1 + 1#64 ∧ t.gpr .a2 = s.gpr .a2 - 1#64 ∧
      Keep [.t0, .a1, .a2] s t := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .a1) 1 := by
    obtain ⟨r, hr, hc⟩ := hd
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .a1) 1 (s.mem (s.gpr .a1) ^^^ k) ∧
      t.gpr .a1 = s.gpr .a1 + 1#64 ∧ t.gpr .a2 = s.gpr .a2 - 1#64) [.t0, .a1, .a2] ?_
      (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2, hk⟩
  unfold applyAfter
  rrun [hax, hd, hr, low_xor]

/-- One iteration, with the writes expressed against the original memory.
Both swap operands are read before either write, including for a self-swap. -/
theorem apply_step (s : State) (i j : Byte)
    (hcx : s.gpr .a3 = i.setWidth 64) (h7 : s.gpr .t4 = j.setWidth 64) (h6 : s.gpr .t6 = 0#64)
    (hal : (s.gpr .a7).toNat % 8 = 0)
    (hp : InRegions s.wr (s.gpr .a7) 256) (hd : InRegions s.wr (s.gpr .a1) 1) :
    let ii := i + 1#8
    let a := s.mem (s.gpr .a7 + BitVec.ofNat 64 ii.toNat)
    let jj := j + a
    let b := s.mem (s.gpr .a7 + BitVec.ofNat 64 jj.toNat)
    let swapped := (s.mem.write (s.gpr .a7 + BitVec.ofNat 64 jj.toNat) 1 a).write
      (s.gpr .a7 + BitVec.ofNat 64 ii.toNat) 1 b
    let k := swapped (s.gpr .a7 + BitVec.ofNat 64 (a + b).toNat)
    WP isa (.block applyStep) s fun t =>
      t.mem = swapped.write (s.gpr .a1) 1 (swapped (s.gpr .a1) ^^^ k) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .a7 = s.gpr .a7 ∧ t.gpr .t6 = s.gpr .t6 ∧
      t.gpr .a0 = s.gpr .a0 ∧
      t.gpr .a1 = s.gpr .a1 + 1#64 ∧ t.gpr .a2 = s.gpr .a2 - 1#64 ∧
      t.gpr .a3 = ii.setWidth 64 ∧ t.gpr .t4 = jj.setWidth 64 := by
  intro ii a jj b swapped k
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256 := by
    obtain ⟨r, hr, hc⟩ := hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [applyStep_eq, WP.block_append_iff]
  refine WP.mono (apply_before s i j hcx h7 hr) fun t ⟨tcx, t7, t9, tk, tm⟩ => ?_
  have tp : t.gpr .a7 = s.gpr .a7 := tk.gpr (by decide)
  have t0' : t.gpr .a0 = s.gpr .a0 := tk.gpr (by decide)
  have t1 : t.gpr .a1 = s.gpr .a1 := tk.gpr (by decide)
  have t2 : t.gpr .a2 = s.gpr .a2 := tk.gpr (by decide)
  have t6 : t.gpr .t6 = s.gpr .t6 := tk.gpr (by decide)
  have htp : InRegions t.wr (t.gpr .a7) 256 := by rw [tk.2.2, tp]; exact hp
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t0, .a5, .t1, .t2]
    (replace_core t jj ii t9 (t6.trans h6) tcx (by rw [tp]; exact hal) htp)
    (by decide +kernel)) fun u ⟨⟨uax, um⟩, uk⟩ => ?_
  rw [tm, tp] at uax um
  have ucx : u.gpr .a3 = ii.setWidth 64 := (uk.gpr (by decide)).trans tcx
  have u7 : u.gpr .t4 = jj.setWidth 64 := (uk.gpr (by decide)).trans t7
  have up : u.gpr .a7 = s.gpr .a7 := (uk.gpr (by decide)).trans tp
  have u0 : u.gpr .a0 = s.gpr .a0 := (uk.gpr (by decide)).trans t0'
  have u1 : u.gpr .a1 = s.gpr .a1 := (uk.gpr (by decide)).trans t1
  have u2 : u.gpr .a2 = s.gpr .a2 := (uk.gpr (by decide)).trans t2
  have u6 : u.gpr .t6 = s.gpr .t6 := (uk.gpr (by decide)).trans t6
  have urd : u.rd = s.rd := uk.2.1.trans tk.2.1
  have uwr : u.wr = s.wr := uk.2.2.trans tk.2.2
  have hw : InRegions u.wr (u.gpr .a7 + BitVec.ofNat 64 ii.toNat) 1 := by
    rw [uwr, up]
    exact region_offset _ _ _ _ _ (by have := ii.isLt; omega) (by have := ii.isLt; omega) hp
  rw [WP.block_append_iff]
  refine WP.mono (apply_middle u ii b ucx uax hw) fun v ⟨vm, v9, vk⟩ => ?_
  have ha : u.mem (u.gpr .a7 + BitVec.ofNat 64 ii.toNat) = a := by
    rw [um, up, write_byte]
    split <;> rfl
  rw [ha] at v9
  rw [up, um] at vm
  have hvm : v.mem = swapped := vm
  have v9' : v.gpr .a4 = (a + b).setWidth 64 := by rw [v9, BitVec.add_comm]
  have vp : v.gpr .a7 = s.gpr .a7 := (vk.gpr (by decide)).trans up
  have v6 : v.gpr .t6 = s.gpr .t6 := (vk.gpr (by decide)).trans u6
  have vrd : v.rd = s.rd := vk.2.1.trans urd
  have vwr : v.wr = s.wr := vk.2.2.trans uwr
  have hvp : InRegions (v.rd ++ v.wr) (v.gpr .a7) 256 := by rw [vrd, vwr, vp]; exact hr
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t0, .a5, .t1, .t2]
    (lookup_core v (a + b) v9' (v6.trans h6) (by rw [vp]; exact hal) hvp)
    (by decide +kernel)) fun w ⟨⟨wax, wm⟩, wk⟩ => ?_
  rw [hvm, vp] at wax
  have w0 : w.gpr .a0 = s.gpr .a0 := (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans u0)
  have w1 : w.gpr .a1 = s.gpr .a1 := (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans u1)
  have w2 : w.gpr .a2 = s.gpr .a2 := (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans u2)
  have wp : w.gpr .a7 = s.gpr .a7 := (wk.gpr (by decide)).trans vp
  have w6 : w.gpr .t6 = s.gpr .t6 := (wk.gpr (by decide)).trans v6
  have wrd : w.rd = s.rd := wk.2.1.trans vrd
  have wwr : w.wr = s.wr := wk.2.2.trans vwr
  have hwd : InRegions w.wr (w.gpr .a1) 1 := by rw [wwr, w1]; exact hd
  refine WP.mono (apply_after w k wax hwd) fun z ⟨zm, z1, z2, zk⟩ => ?_
  refine ⟨?_, zk.2.1.trans wrd, zk.2.2.trans wwr, (zk.gpr (by decide)).trans wp,
    (zk.gpr (by decide)).trans w6, (zk.gpr (by decide)).trans w0, ?_, ?_, ?_, ?_⟩
  · rw [zm, wm, hvm, w1]
  · rw [z1, w1]
  · rw [z2, w2]
  · rw [zk.gpr (by decide), wk.gpr (by decide), vk.gpr (by decide), ucx]
  · rw [zk.gpr (by decide), wk.gpr (by decide), vk.gpr (by decide), u7]

end VG.Proof.Rc4.RISCV64
