module

public import VerifiedGarbage.Proof.Rc4.PPC64LE.Schedule
import VerifiedGarbage.Proof.Rc4.Memory
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep

/-! # RC4 on PPC64LE: one PRGA step -/

@[expose] public section

namespace VG.Proof.Rc4.PPC64LE
open VG VG.PPC64LE VG.Impl.Rc4.PPC64LE VG.Spec.Rc4 VG.Proof.Rc4

/-- `i += 1`, then `j += S[i]`, copied to the index of the replacement. -/
def applyBefore : List Instr :=
  ([.addi .r6 .r6 1, .lsl .r6 .r6 56, .lsr .d .r6 .r6 56] : List Instr) ++ loadI ++
    ([.add .r7 .r7 .r0, .lsl .r7 .r7 56, .lsr .d .r7 .r7 56, .logic .or .r9 .r7 .r7] : List Instr)

/-- `S[i] := S[j]` (in `r10`), and the index `S[i] + S[j]` of the keystream byte. -/
def applyMiddle : List Instr :=
  loadI ++ ([.stb .r10 .r12 0, .add .r9 .r10 .r0, .lsl .r9 .r9 56, .lsr .d .r9 .r9 56] :
    List Instr)

/-- The keystream byte XORed into the data. -/
def applyAfter : List Instr :=
  [.lbz .r0 .r4 0, .logic .xor .r0 .r0 .r10, .stb .r0 .r4 0, .addi .r4 .r4 1, .subi .r5 .r5 1]

theorem applyStep_eq :
    applyStep = applyBefore ++ (replace ++ (applyMiddle ++ (lookup ++ applyAfter))) := by
  simp only [applyStep, applyBefore, applyMiddle, applyAfter, List.append_assoc]

theorem byte_inc (i : Byte) :
    ((i.setWidth 64 + 1#64) <<< 56) >>> 56 = (i + 1#8).setWidth 64 := by
  have h := byte_add i 1#8
  rwa [show (1#8).setWidth 64 = 1#64 from rfl] at h

theorem apply_before (s : State) (i j : Byte)
    (hcx : s.gpr .r6 = i.setWidth 64) (h7 : s.gpr .r7 = j.setWidth 64)
    (hp : InRegions (s.rd ++ s.wr) (s.gpr .r3) 256) :
    WP isa (.block applyBefore) s fun t =>
      t.gpr .r6 = (i + 1#8).setWidth 64 ∧
      t.gpr .r7 = (j + s.mem (s.gpr .r3 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.gpr .r9 = (j + s.mem (s.gpr .r3 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      Keep [.r0, .r6, .r7, .r9, .r12] s t ∧ t.mem = s.mem := by
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .r3 + (i + 1#8).setWidth 64) 1 := by
    rw [byte_addr (i + 1#8)]
    exact region_offset _ _ _ _ _ (by have := (i + 1#8).isLt; omega)
      (by have := (i + 1#8).isLt; omega) hp
  refine WP.mono (WP.keep (Q := fun t => t.gpr .r6 = (i + 1#8).setWidth 64 ∧
      t.gpr .r7 = (j + s.mem (s.gpr .r3 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.gpr .r9 = (j + s.mem (s.gpr .r3 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.mem = s.mem) [.r0, .r6, .r7, .r9, .r12] ?_ (by decide +kernel))
    fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, hk, h.2.2.2⟩
  unfold applyBefore loadI
  rrun [hcx, h7, byte_inc, hi, BitVec.or_self]
  rw [byte_addr (i + 1#8), byte_add]

theorem apply_middle (s : State) (ii b : Byte)
    (hcx : s.gpr .r6 = ii.setWidth 64) (hax : s.gpr .r10 = b.setWidth 64)
    (hw : InRegions s.wr (s.gpr .r3 + BitVec.ofNat 64 ii.toNat) 1) :
    WP isa (.block applyMiddle) s fun t =>
      t.mem = s.mem.write (s.gpr .r3 + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .r9 = (b + s.mem (s.gpr .r3 + BitVec.ofNat 64 ii.toNat)).setWidth 64 ∧
      Keep [.r0, .r9, .r12] s t := by
  have hw' : InRegions s.wr (s.gpr .r3 + ii.setWidth 64) 1 := by rw [byte_addr ii]; exact hw
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + ii.setWidth 64) 1 := by
    obtain ⟨r, hr, hc⟩ := hw'
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .r3 + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .r9 = (b + s.mem (s.gpr .r3 + BitVec.ofNat 64 ii.toNat)).setWidth 64)
      [.r0, .r9, .r12] ?_ (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  unfold applyMiddle loadI
  rrun [hcx, hax, hw', hr, low_byte, byte_add]
  rw [byte_addr ii]
  exact ⟨rfl, rfl⟩

theorem low_xor (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 = a ^^^ b := by
  rw [xor_byte, low_byte]

theorem apply_after (s : State) (k : Byte) (hax : s.gpr .r10 = k.setWidth 64)
    (hd : InRegions s.wr (s.gpr .r4) 1) :
    WP isa (.block applyAfter) s fun t =>
      t.mem = s.mem.write (s.gpr .r4) 1 (s.mem (s.gpr .r4) ^^^ k) ∧
      t.gpr .r4 = s.gpr .r4 + 1#64 ∧ t.gpr .r5 = s.gpr .r5 - 1#64 ∧
      Keep [.r0, .r4, .r5] s t := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .r4) 1 := by
    obtain ⟨r, hr, hc⟩ := hd
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .r4) 1 (s.mem (s.gpr .r4) ^^^ k) ∧
      t.gpr .r4 = s.gpr .r4 + 1#64 ∧ t.gpr .r5 = s.gpr .r5 - 1#64) [.r0, .r4, .r5] ?_
      (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2, hk⟩
  unfold applyAfter
  rrun [hax, hd, hr, low_xor]

/-- One iteration, with the writes expressed against the original memory.
Both swap operands are read before either write, including for a self-swap. -/
theorem apply_step (s : State) (i j : Byte)
    (hcx : s.gpr .r6 = i.setWidth 64) (h7 : s.gpr .r7 = j.setWidth 64) (h8 : s.gpr .r8 = 0)
    (hp : InRegions s.wr (s.gpr .r3) 256) (hd : InRegions s.wr (s.gpr .r4) 1) :
    let ii := i + 1#8
    let a := s.mem (s.gpr .r3 + BitVec.ofNat 64 ii.toNat)
    let jj := j + a
    let b := s.mem (s.gpr .r3 + BitVec.ofNat 64 jj.toNat)
    let swapped := (s.mem.write (s.gpr .r3 + BitVec.ofNat 64 jj.toNat) 1 a).write
      (s.gpr .r3 + BitVec.ofNat 64 ii.toNat) 1 b
    let k := swapped (s.gpr .r3 + BitVec.ofNat 64 (a + b).toNat)
    WP isa (.block applyStep) s fun t =>
      t.mem = swapped.write (s.gpr .r4) 1 (swapped (s.gpr .r4) ^^^ k) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .r3 = s.gpr .r3 ∧ t.gpr .r8 = s.gpr .r8 ∧
      t.gpr .r4 = s.gpr .r4 + 1#64 ∧ t.gpr .r5 = s.gpr .r5 - 1#64 ∧
      t.gpr .r6 = ii.setWidth 64 ∧ t.gpr .r7 = jj.setWidth 64 := by
  intro ii a jj b swapped k
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .r3) 256 := by
    obtain ⟨r, hr, hc⟩ := hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [applyStep_eq, WP.block_append_iff]
  refine WP.mono (apply_before s i j hcx h7 hr) fun t ⟨tcx, t7, t9, tk, tm⟩ => ?_
  have tp : t.gpr .r3 = s.gpr .r3 := tk.gpr (by decide)
  have t4 : t.gpr .r4 = s.gpr .r4 := tk.gpr (by decide)
  have t5 : t.gpr .r5 = s.gpr .r5 := tk.gpr (by decide)
  have t8 : t.gpr .r8 = s.gpr .r8 := tk.gpr (by decide)
  have htp : InRegions t.wr (t.gpr .r3) 256 := by rw [tk.2.2, tp]; exact hp
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r10, .r11, .r12] (replace_core t jj ii t9 (t8.trans h8) tcx htp)
    (by decide +kernel)) fun u ⟨⟨uax, um⟩, uk⟩ => ?_
  rw [tm, tp] at uax um
  have ucx : u.gpr .r6 = ii.setWidth 64 := (uk.gpr (by decide)).trans tcx
  have u7 : u.gpr .r7 = jj.setWidth 64 := (uk.gpr (by decide)).trans t7
  have up : u.gpr .r3 = s.gpr .r3 := (uk.gpr (by decide)).trans tp
  have u4 : u.gpr .r4 = s.gpr .r4 := (uk.gpr (by decide)).trans t4
  have u5 : u.gpr .r5 = s.gpr .r5 := (uk.gpr (by decide)).trans t5
  have u8 : u.gpr .r8 = s.gpr .r8 := (uk.gpr (by decide)).trans t8
  have urd : u.rd = s.rd := uk.2.1.trans tk.2.1
  have uwr : u.wr = s.wr := uk.2.2.trans tk.2.2
  have hw : InRegions u.wr (u.gpr .r3 + BitVec.ofNat 64 ii.toNat) 1 := by
    rw [uwr, up]
    exact region_offset _ _ _ _ _ (by have := ii.isLt; omega) (by have := ii.isLt; omega) hp
  rw [WP.block_append_iff]
  refine WP.mono (apply_middle u ii b ucx uax hw) fun v ⟨vm, v9, vk⟩ => ?_
  have ha : u.mem (u.gpr .r3 + BitVec.ofNat 64 ii.toNat) = a := by
    rw [um, up, write_byte]
    split <;> rfl
  rw [ha] at v9
  rw [up, um] at vm
  have hvm : v.mem = swapped := vm
  have v9' : v.gpr .r9 = (a + b).setWidth 64 := by rw [v9, BitVec.add_comm]
  have vp : v.gpr .r3 = s.gpr .r3 := (vk.gpr (by decide)).trans up
  have v8 : v.gpr .r8 = s.gpr .r8 := (vk.gpr (by decide)).trans u8
  have vrd : v.rd = s.rd := vk.2.1.trans urd
  have vwr : v.wr = s.wr := vk.2.2.trans uwr
  have hvp : InRegions (v.rd ++ v.wr) (v.gpr .r3) 256 := by rw [vrd, vwr, vp]; exact hr
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r10, .r11, .r12] (lookup_core v (a + b) v9' (v8.trans h8) hvp)
    (by decide +kernel)) fun w ⟨⟨wax, wm⟩, wk⟩ => ?_
  rw [hvm, vp] at wax
  have w4 : w.gpr .r4 = s.gpr .r4 := (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans u4)
  have w5 : w.gpr .r5 = s.gpr .r5 := (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans u5)
  have wp : w.gpr .r3 = s.gpr .r3 := (wk.gpr (by decide)).trans vp
  have w8 : w.gpr .r8 = s.gpr .r8 := (wk.gpr (by decide)).trans v8
  have wrd : w.rd = s.rd := wk.2.1.trans vrd
  have wwr : w.wr = s.wr := wk.2.2.trans vwr
  have hwd : InRegions w.wr (w.gpr .r4) 1 := by rw [wwr, w4]; exact hd
  refine WP.mono (apply_after w k wax hwd) fun z ⟨zm, z4, z5, zk⟩ => ?_
  refine ⟨?_, zk.2.1.trans wrd, zk.2.2.trans wwr, (zk.gpr (by decide)).trans wp,
    (zk.gpr (by decide)).trans w8, ?_, ?_, ?_, ?_⟩
  · rw [zm, wm, hvm, w4]
  · rw [z4, w4]
  · rw [z5, w5]
  · rw [zk.gpr (by decide), wk.gpr (by decide), vk.gpr (by decide), ucx]
  · rw [zk.gpr (by decide), wk.gpr (by decide), vk.gpr (by decide), u7]

end VG.Proof.Rc4.PPC64LE
