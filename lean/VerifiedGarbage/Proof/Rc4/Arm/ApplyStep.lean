import VerifiedGarbage.Proof.Rc4.Arm.Replace

/-! # RC4 on ARMv7: one PRGA step -/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

/-- What a step of the stream function keeps: the table at `P`, the `L`
bytes of data at `D`, all ones. -/
structure StepEnv (s : State) (P D L : BitVec 32) : Prop where
  p : s.gpr .r12 = P
  d : s.gpr .r1 = D
  l : s.gpr .r2 = L
  ones : s.gpr .r10 = BitVec.allOnes 32
  pfit : P.toNat + 258 ≤ 2 ^ 32
  dfit : D.toNat + L.toNat ≤ 2 ^ 32
  table : InRegions s.wr (State.addr P) 256
  data : InRegions s.wr (State.addr D) L.toNat
  sTD : Mem.Sep (State.addr P) 256 (State.addr D) L.toNat

/-- The registers a step writes. -/
abbrev stepRegs : List Reg := [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r11]

theorem StepEnv.keep {s t : State} {P D L : BitVec 32} (h : StepEnv s P D L) {rs : List Reg}
    (hk : Keep rs s t) (hrs : ∀ r ∈ rs, r ≠ .r12 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r10) :
    StepEnv t P D L :=
  { h with
    p := (hk.gpr fun hm => (hrs _ hm).1 rfl).trans h.p
    d := (hk.gpr fun hm => (hrs _ hm).2.1 rfl).trans h.d
    l := (hk.gpr fun hm => (hrs _ hm).2.2.1 rfl).trans h.l
    ones := (hk.gpr fun hm => (hrs _ hm).2.2.2 rfl).trans h.ones
    table := by rw [hk.2.2.1]; exact h.table
    data := by rw [hk.2.2.1]; exact h.data }

theorem StepEnv.tableEnv {s : State} {P D L : BitVec 32} (h : StepEnv s P D L)
    {idx : Byte} (h6 : s.gpr .r6 = idx.setWidth 32) : TableEnv s idx :=
  ⟨h6, h.ones, by rw [h.p]; have := h.pfit; omega, by rw [h.p]; exact h.table⟩

theorem apply_before (s : State) (i j : Byte) {P D L : BitVec 32} (he : StepEnv s P D L)
    (h4 : s.gpr .r4 = i.setWidth 32) (h5 : s.gpr .r5 = j.setWidth 32) :
    WP isa (.block (([.dp .add .r4 .r4 (imm 1), .dp .and .r4 .r4 (imm 255)] : List Instr) ++ loadI ++
      ([.dp .add .r5 .r5 (.reg .r11), .dp .and .r5 .r5 (imm 255), .mov .r6 (.reg .r5)] :
        List Instr))) s fun t =>
      t.gpr .r4 = (i + 1#8).setWidth 32 ∧
      t.gpr .r5 = (j + s.mem (State.addr P + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 32 ∧
      t.gpr .r6 = t.gpr .r5 ∧ Keep [.r4, .r5, .r6, .r9, .r11] s t ∧ t.mem = s.mem := by
  rw [WP.block_append_iff, WP.block_append_iff]
  have h1 : WP isa (.block [.dp .add .r4 .r4 (imm 1), .dp .and .r4 .r4 (imm 255)]) s fun t =>
      t.gpr .r4 = (i + 1#8).setWidth 32 ∧ t.mem = s.mem := by
    arun [h4, byte_inc32]
  refine WP.mono (WP.keep [.r4] h1 (by decide)) fun t ⟨⟨t4, tm⟩, tk⟩ => ?_
  have het := he.keep tk (by decide)
  refine WP.mono (loadI_ok t (i + 1#8) t4 (by rw [het.p]; have := he.pfit; omega)
    (by rw [het.p]; exact region_in het.table)) fun u ⟨u11, uk, um⟩ => ?_
  rw [het.p, tm] at u11
  have u5 : u.gpr .r5 = j.setWidth 32 :=
    (uk.gpr (by decide)).trans ((tk.gpr (by decide)).trans h5)
  have h2 : WP isa (.block [.dp .add .r5 .r5 (.reg .r11), .dp .and .r5 .r5 (imm 255),
      .mov .r6 (.reg .r5)]) u fun v =>
      v.gpr .r5 = (j + s.mem (State.addr P + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 32 ∧
      v.gpr .r6 = v.gpr .r5 ∧ v.mem = u.mem := by
    arun [u5, u11, byte_add32]
  refine WP.mono (WP.keep [.r5, .r6] h2 (by decide)) fun v ⟨⟨v5, v6, vm⟩, vk⟩ => ?_
  exact ⟨(vk.gpr (by decide)).trans ((uk.gpr (by decide)).trans t4), v5, v6,
    ((tk.trans uk).trans vk).mono (by decide), vm.trans (um.trans tm)⟩

theorem apply_middle (s : State) (ii a b : Byte) {P : BitVec 32} (h12 : s.gpr .r12 = P)
    (hfit : P.toNat + 256 ≤ 2 ^ 32) (h4 : s.gpr .r4 = ii.setWidth 32)
    (h7 : s.gpr .r7 = b.setWidth 32) (h11 : s.gpr .r11 = a.setWidth 32)
    (hw : InRegions s.wr (State.addr P + BitVec.ofNat 64 ii.toNat) 1) :
    WP isa (.block [.dp .add .r9 .r12 (.reg .r4), .strb .r7 .r9 0, .dp .add .r6 .r7 (.reg .r11),
      .dp .and .r6 .r6 (imm 255)]) s fun t =>
      t.mem = s.mem.write (State.addr P + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .r6 = (a + b).setWidth 32 ∧ Keep [.r6, .r9] s t := by
  have hw' : InRegions s.wr (State.addr (P + ii.setWidth 32 + BitVec.ofNat 32 0)) 1 := by
    rw [idx_addr hfit ii]; exact hw
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (State.addr P + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .r6 = (a + b).setWidth 32) [.r6, .r9] ?_ (by decide)) fun t ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  arun [h12, h4, h7, h11, hw', byte_add32]
  rw [idx_addr hfit ii, writeW_byte8, low_byte32, BitVec.add_comm b a]
  exact ⟨rfl, rfl⟩

theorem apply_after (s : State) (k : Byte) {D L : BitVec 32} {n : Nat}
    (h1 : s.gpr .r1 = D) (h2 : s.gpr .r2 = L) (h0 : s.gpr .r0 = BitVec.ofNat 32 n)
    (h7 : s.gpr .r7 = k.setWidth 32) (hfit : D.toNat + n < 2 ^ 32)
    (hd : InRegions s.wr (State.addr D + BitVec.ofNat 64 n) 1) :
    WP isa (.block [.dp .add .r9 .r1 (.reg .r0), .ldrb .r11 .r9 0, .dp .eor .r11 .r11 (.reg .r7),
      .strb .r11 .r9 0, .dp .add .r0 .r0 (imm 1), .cmp .r0 (.reg .r2)]) s fun t =>
      t.mem = s.mem.write (State.addr D + BitVec.ofNat 64 n) 1
          (s.mem (State.addr D + BitVec.ofNat 64 n) ^^^ k) ∧
        t.gpr .r0 = BitVec.ofNat 32 (n + 1) ∧
        t.z = (BitVec.ofNat 32 (n + 1) - L == 0#32) ∧ Keep [.r0, .r9, .r11] s t := by
  have hdn : State.addr (D + BitVec.ofNat 32 n + BitVec.ofNat 32 0) =
      State.addr D + BitVec.ofNat 64 n := by
    rw [BitVec.add_zero]
    exact addr_add hfit
  have hw : InRegions s.wr (State.addr (D + BitVec.ofNat 32 n + BitVec.ofNat 32 0)) 1 := by
    rw [hdn]; exact hd
  have hr := region_in (rs := s.rd) hw
  have hadd : BitVec.ofNat 32 n + BitVec.ofNat 32 1 = BitVec.ofNat 32 (n + 1) := by
    rw [← BitVec.ofNat_add]
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (State.addr D + BitVec.ofNat 64 n) 1
          (s.mem (State.addr D + BitVec.ofNat 64 n) ^^^ k) ∧
        t.gpr .r0 = BitVec.ofNat 32 (n + 1) ∧
        t.z = (BitVec.ofNat 32 (n + 1) - L == 0#32)) [.r0, .r9, .r11] ?_ (by decide))
    fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2, hk⟩
  arun [h1, h2, h0, h7, hw, hr, hadd]
  rw [hdn, writeW_byte8, low_xor32]

/-- One iteration, with the writes expressed against the original memory.
Both swap operands are read before either write, including for a self-swap. -/
theorem apply_step (s : State) (i j : Byte) {P D L : BitVec 32} {n : Nat}
    (he : StepEnv s P D L) (h4 : s.gpr .r4 = i.setWidth 32) (h5 : s.gpr .r5 = j.setWidth 32)
    (h0 : s.gpr .r0 = BitVec.ofNat 32 n) (hn : n < L.toNat) :
    let p := State.addr P
    let ii := i + 1#8
    let a := s.mem (p + BitVec.ofNat 64 ii.toNat)
    let jj := j + a
    let b := s.mem (p + BitVec.ofNat 64 jj.toNat)
    let swapped := (s.mem.write (p + BitVec.ofNat 64 jj.toNat) 1 a).write
      (p + BitVec.ofNat 64 ii.toNat) 1 b
    let k := swapped (p + BitVec.ofNat 64 (a + b).toNat)
    WP isa (.block applyStep) s fun t =>
      t.mem = swapped.write (State.addr D + BitVec.ofNat 64 n) 1
        (swapped (State.addr D + BitVec.ofNat 64 n) ^^^ k) ∧
      t.gpr .r4 = ii.setWidth 32 ∧ t.gpr .r5 = jj.setWidth 32 ∧
      t.gpr .r0 = BitVec.ofNat 32 (n + 1) ∧
      t.z = (BitVec.ofNat 32 (n + 1) - L == 0#32) ∧ Keep stepRegs s t := by
  intro p ii a jj b swapped k
  have hfit : P.toNat + 256 ≤ 2 ^ 32 := by have := he.pfit; omega
  simp only [applyStep, List.append_assoc]
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono (apply_before s i j he h4 h5) fun t ⟨t4, t5, t6, tk, tm⟩ => ?_
  have het := he.keep tk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (replace_core t jj ii (het.tableEnv (t6.trans t5)) t4) fun u ⟨u7, um, uk⟩ => ?_
  rw [tm, het.p] at u7 um
  have heu := het.keep uk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadI_ok u ii ((uk.gpr (by decide)).trans t4) (by rw [heu.p]; exact hfit)
    (by rw [heu.p]; exact region_in heu.table)) fun v ⟨v11, vk, vm⟩ => ?_
  have ha : u.mem (p + BitVec.ofNat 64 ii.toNat) = a := by
    rw [um, write_byte]
    split <;> rfl
  rw [heu.p, ha] at v11
  have hev := heu.keep vk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (apply_middle v ii a b hev.p hfit
    ((vk.gpr (by decide)).trans ((uk.gpr (by decide)).trans t4))
    ((vk.gpr (by decide)).trans u7) v11
    (by rw [vk.2.2.1, uk.2.2.1, tk.2.2.1]
        exact region_offset _ _ _ _ _ (by have := ii.isLt; omega) (by have := ii.isLt; omega)
          he.table)) fun w ⟨wm, w6, wk⟩ => ?_
  rw [vm, um] at wm
  have hw : w.mem = swapped := wm
  have hew := hev.keep wk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r7, .r8, .r9, .r11] (lookup_core w (a + b) (hew.tableEnv w6))
    (by decide +kernel)) fun x ⟨⟨x7, xm⟩, xk⟩ => ?_
  rw [hew.p, hw] at x7
  have hex := hew.keep xk (by decide)
  have ktx := ((uk.trans vk).trans wk).trans xk
  have x4 : x.gpr .r4 = ii.setWidth 32 := (ktx.gpr (by decide)).trans t4
  have x5 : x.gpr .r5 = jj.setWidth 32 := (ktx.gpr (by decide)).trans t5
  have x0 : x.gpr .r0 = BitVec.ofNat 32 n := (ktx.gpr (by decide)).trans ((tk.gpr (by decide)).trans h0)
  refine WP.mono (apply_after x k hex.d hex.l x0 x7 (by have := he.dfit; omega)
    (by rw [xk.2.2.1, wk.2.2.1, vk.2.2.1, uk.2.2.1, tk.2.2.1]
        exact region_offset _ _ _ _ _ (by have := he.dfit; omega) (by omega) he.data))
    fun y ⟨ym, y0, yz, yk⟩ => ?_
  exact ⟨by rw [ym, xm, hw], (yk.gpr (by decide)).trans x4, (yk.gpr (by decide)).trans x5, y0, yz,
    (((tk.trans ktx).trans yk)).mono (by decide)⟩

end VG.Proof.Rc4.Arm
