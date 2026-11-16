module

public import VerifiedGarbage.Proof.Rc4.Arm.Lookup
import VerifiedGarbage.Proof.Rc4.Arm.Replace
public import VerifiedGarbage.Proof.Rc4.Arm.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Rc4.Update
import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Rc4.Table
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Rc4.Arm.Contract
import VerifiedGarbage.Proof.Rc4.Arm.Init
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Rc4.Arm.ApplyLoop`, which only this module used -/

section

/-! ### `Rc4.Arm.ApplyStep`, which only this module used -/

section

/-! # RC4 on ARMv7: one PRGA step -/

@[expose] public section

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
  ⟨h6, h.ones, by rw [h.p]; have := h.pfit; omega_using [this], by rw [h.p]; exact h.table⟩

theorem apply_before (s : State) (i j : Byte) {P D L : BitVec 32} (he : StepEnv s P D L)
    (h4 : s.gpr .r4 = i.setWidth 32) (h5 : s.gpr .r5 = j.setWidth 32) :
    WP isa (.block (([.dp .add .r4 .r4 (imm 1), .dp .and .r4 .r4 (imm 255)] : List Instr) ++ loadI ++
      ([.dp .add .r5 .r5 (.reg .r11), .dp .and .r5 .r5 (imm 255), .mov .r6 (.reg .r5)] :
        List Instr))) s fun t =>
      t.gpr .r4 = (i + 1#8).setWidth 32 ∧
      t.gpr .r5 = (j + s.mem (State.addr P + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 32 ∧
      t.gpr .r6 = t.gpr .r5 ∧ Keep [.r4, .r5, .r6, .r9, .r11] s t ∧ t.mem = s.mem := by
  rw [WP.block_append_iff, WP.block_append_iff]
  obtain h1 : WP isa (.block [.dp .add .r4 .r4 (imm 1), .dp .and .r4 .r4 (imm 255)]) s fun t =>
      t.gpr .r4 = (i + 1#8).setWidth 32 ∧ t.mem = s.mem := by
    arun [h4, byte_inc32]
  refine WP.mono (WP.keep [.r4] h1 (by decide)) fun t ⟨⟨t4, tm⟩, tk⟩ => ?_
  obtain het := he.keep tk (by decide)
  refine WP.mono (loadI_ok t (i + 1#8) t4 (by rw [het.p]; have := he.pfit; omega_using [this])
    (by rw [het.p]; exact region_in het.table)) fun u ⟨u11, uk, um⟩ => ?_
  rw [het.p, tm] at u11
  obtain u5 : u.gpr .r5 = j.setWidth 32 :=
    (uk.gpr (by decide)).trans ((tk.gpr (by decide)).trans h5)
  obtain h2 : WP isa (.block [.dp .add .r5 .r5 (.reg .r11), .dp .and .r5 .r5 (imm 255),
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
  obtain hw' : InRegions s.wr (State.addr (P + ii.setWidth 32 + BitVec.ofNat 32 0)) 1 := by
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
  obtain hdn : State.addr (D + BitVec.ofNat 32 n + BitVec.ofNat 32 0) =
      State.addr D + BitVec.ofNat 64 n := by
    rw [BitVec.add_zero]
    exact addr_add hfit
  obtain hw : InRegions s.wr (State.addr (D + BitVec.ofNat 32 n + BitVec.ofNat 32 0)) 1 := by
    rw [hdn]; exact hd
  obtain hr := region_in (rs := s.rd) hw
  obtain hadd : BitVec.ofNat 32 n + BitVec.ofNat 32 1 = BitVec.ofNat 32 (n + 1) := by
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
  obtain hfit : P.toNat + 256 ≤ 2 ^ 32 := by have := he.pfit; omega_using [this]
  simp only [applyStep, List.append_assoc]
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono (apply_before s i j he h4 h5) fun t ⟨t4, t5, t6, tk, tm⟩ => ?_
  obtain het := he.keep tk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (replace_core t jj ii (het.tableEnv (t6.trans t5)) t4) fun u ⟨u7, um, uk⟩ => ?_
  rw [tm, het.p] at u7 um
  obtain heu := het.keep uk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadI_ok u ii ((uk.gpr (by decide)).trans t4) (by rw [heu.p]; exact hfit)
    (by rw [heu.p]; exact region_in heu.table)) fun v ⟨v11, vk, vm⟩ => ?_
  obtain ha : u.mem (p + BitVec.ofNat 64 ii.toNat) = a := by
    rw [um, write_byte]
    split <;> rfl
  rw [heu.p, ha] at v11
  obtain hev := heu.keep vk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (apply_middle v ii a b hev.p hfit
    ((vk.gpr (by decide)).trans ((uk.gpr (by decide)).trans t4))
    ((vk.gpr (by decide)).trans u7) v11
    (by rw [vk.2.2.1, uk.2.2.1, tk.2.2.1]
        exact region_offset _ _ _ _ _ (by have := ii.isLt; omega_using []) (by have := ii.isLt; omega_using [])
          he.table)) fun w ⟨wm, w6, wk⟩ => ?_
  rw [vm, um] at wm
  have hw : w.mem = swapped := wm
  obtain hew := hev.keep wk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r7, .r8, .r9, .r11] (lookup_core w (a + b) (hew.tableEnv w6))
    (by decide +kernel)) fun x ⟨⟨x7, xm⟩, xk⟩ => ?_
  rw [hew.p, hw] at x7
  obtain hex := hew.keep xk (by decide)
  obtain ktx := ((uk.trans vk).trans wk).trans xk
  obtain x4 : x.gpr .r4 = ii.setWidth 32 := (ktx.gpr (by decide)).trans t4
  obtain x5 : x.gpr .r5 = jj.setWidth 32 := (ktx.gpr (by decide)).trans t5
  obtain x0 : x.gpr .r0 = BitVec.ofNat 32 n := (ktx.gpr (by decide)).trans ((tk.gpr (by decide)).trans h0)
  refine WP.mono (apply_after x k hex.d hex.l x0 x7 (by have := he.dfit; omega_using [hn, this])
    (by rw [xk.2.2.1, wk.2.2.1, vk.2.2.1, uk.2.2.1, tk.2.2.1]
        exact region_offset _ _ _ _ _ (by have := he.dfit; omega_using [hn]) (by omega_using [hn]) he.data))
    fun y ⟨ym, y0, yz, yk⟩ => ?_
  exact ⟨by rw [ym, xm, hw], (yk.gpr (by decide)).trans x4, (yk.gpr (by decide)).trans x5, y0, yz,
    (((tk.trans ktx).trans yk)).mono (by decide)⟩

end VG.Proof.Rc4.Arm

end

end


/-! # RC4 on ARMv7: the stream loop -/

@[expose] public section

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

/-- The context and output after the first `k` data bytes, from memory `m`. -/
def upd (m : Mem) (P D : BitVec 32) (k : Nat) : Context × List Byte :=
  update (contextAt m (State.addr P)) (bytesAt m (State.addr D) k)

theorem upd_succ (m : Mem) (P D : BitVec 32) (k : Nat) :
    upd m P D (k + 1) = ((step (upd m P D k).1).1, (upd m P D k).2 ++
      [m (State.addr D + BitVec.ofNat 64 k) ^^^ (step (upd m P D k).1).2]) := by
  unfold upd
  rw [bytes_snoc, update_snoc]

/-- What the stream loop writes: the table and the data. -/
def loopRegions (P D L : BitVec 32) : List Region :=
  [⟨State.addr P, 256⟩, ⟨State.addr D, L.toNat⟩]

/-- The stream loop after `k` bytes, from the state `b` it started in; `m₀`
is the memory on entry, which differs from `b`'s only outside the context
and the data. -/
structure LoopInv (m₀ : Mem) (P D L : BitVec 32) (b : State) (k : Nat) (t : State) : Prop where
  le : k ≤ L.toNat
  table : (contextAt t.mem (State.addr P)).table = (upd m₀ P D k).1.table
  i : t.gpr .r4 = (upd m₀ P D k).1.i.setWidth 32
  j : t.gpr .r5 = (upd m₀ P D k).1.j.setWidth 32
  data : bytesAt t.mem (State.addr D) k = (upd m₀ P D k).2
  tail : ∀ x, k ≤ x → x < L.toNat →
    t.mem (State.addr D + BitVec.ofNat 64 x) = m₀ (State.addr D + BitVec.ofNat 64 x)
  frame : Frame (loopRegions P D L) b.mem t.mem
  count : t.gpr .r0 = BitVec.ofNat 32 k
  keep : Keep stepRegs b t

/-- A byte outside the table and the data byte an iteration writes. -/
theorem step_other {m : Mem} {p d x : Addr} {ii jj : Byte} {w : Byte}
    (hT : ¬ (x - p).toNat < 256) (hD : x ≠ d) :
    (((m.write (p + BitVec.ofNat 64 jj.toNat) 1 (m (p + BitVec.ofNat 64 ii.toNat))).write
      (p + BitVec.ofNat 64 ii.toNat) 1 (m (p + BitVec.ofNat 64 jj.toNat))).write d 1 w) x =
      m x := by
  rw [write_byte, ite_eq_right hD]
  exact swap_frame m p ii jj x hT

/-- The concrete stream iteration realizes the abstract PRGA transition. -/
theorem apply_step_table (t : State) (i j : Byte) {P D L : BitVec 32} {k : Nat}
    (he : StepEnv t P D L) (h4 : t.gpr .r4 = i.setWidth 32) (h5 : t.gpr .r5 = j.setWidth 32)
    (h0 : t.gpr .r0 = BitVec.ofNat 32 k) (hk : k < L.toNat) :
    let next := step { table := (contextAt t.mem (State.addr P)).table, i, j }
    WP isa (.block applyStep) t fun u =>
      (contextAt u.mem (State.addr P)).table = next.1.table ∧
      u.gpr .r4 = next.1.i.setWidth 32 ∧ u.gpr .r5 = next.1.j.setWidth 32 ∧
      u.mem (State.addr D + BitVec.ofNat 64 k) =
        t.mem (State.addr D + BitVec.ofNat 64 k) ^^^ next.2 ∧
      (∀ x, ¬ (x - State.addr P).toNat < 256 → x ≠ State.addr D + BitVec.ofNat 64 k →
        u.mem x = t.mem x) ∧
      Frame (loopRegions P D L) t.mem u.mem ∧
      u.gpr .r0 = BitVec.ofNat 32 (k + 1) ∧
      u.z = (BitVec.ofNat 32 (k + 1) - L == 0#32) ∧ Keep stepRegs t u := by
  dsimp only
  rw [step_eq]
  dsimp only
  simp only [table_get]
  have hone : (1 : Byte) = 1#8 := rfl
  simp only [hone]
  refine WP.mono (apply_step t i j he h4 h5 h0 hk)
    fun u ⟨hum, hu4, hu5, hu0, huz, huk⟩ => ?_
  obtain hdk : ¬ (State.addr D + BitVec.ofNat 64 k - State.addr P).toNat < 256 := by
    obtain hin : (State.addr D + BitVec.ofNat 64 k - State.addr D).toNat < L.toNat := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk])]
      exact hk
    exact fun h => he.sTD _ h hin
  obtain hTD : Mem.Sep (State.addr P) 256 (State.addr D + BitVec.ofNat 64 k) 1 :=
    sep_offset_right he.sTD (by omega_using [hk]) (by omega_using [hk])
  refine ⟨?_, hu4, hu5, ?_, ?_, ?_, hu0, huz, huk⟩
  · rw [hum, table_write_sep _ _ _ _ hTD, table_swap]
  · rw [hum, write_byte, ite_eq_left rfl, swap_frame _ _ _ _ _ hdk]
    obtain ht := table_swap t.mem (State.addr P) (i + 1#8)
      (j + t.mem (State.addr P + BitVec.ofNat 64 (i + 1#8).toNat))
    rw [← ht, table_get]
  · intro x hT hD
    rw [hum]
    exact step_other hT hD
  · rw [hum]
    have hP : (⟨State.addr P, 256⟩ : Region) ∈ loopRegions P D L := List.mem_cons_self
    obtain hD : (⟨State.addr D, L.toNat⟩ : Region) ∈ loopRegions P D L :=
      List.mem_cons_of_mem _ List.mem_cons_self
    refine Frame.write ?_ hD _ (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk]))
    refine Frame.write ?_ hP _ (Offset.contains_base _ (by omega_using []) (by omega_using []))
    exact Frame.write (Frame.refl _ _) hP _ (Offset.contains_base _ (by omega_using []) (by omega_using []))

theorem loop_step (m₀ : Mem) {P D L : BitVec 32} (b : State) (hb : StepEnv b P D L) {k : Nat}
    (hk : k < L.toNat) (t : State) (ht : LoopInv m₀ P D L b k t) :
    WP isa (.block applyStep) t fun u => LoopInv m₀ P D L b (k + 1) u ∧
      u.z = (BitVec.ofNat 32 (k + 1) - L == 0#32) := by
  obtain he := hb.keep ht.keep (by decide)
  obtain hsD : ∀ x, x < L.toNat →
      ¬ (State.addr D + BitVec.ofNat 64 x - State.addr P).toNat < 256 := by
    intro x hx
    obtain hin : (State.addr D + BitVec.ofNat 64 x - State.addr D).toNat < L.toNat := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hx])]
      exact hx
    exact fun h => hb.sTD _ h hin
  obtain hctx : (⟨(contextAt t.mem (State.addr P)).table, (upd m₀ P D k).1.i,
      (upd m₀ P D k).1.j⟩ : Context) = (upd m₀ P D k).1 := context_ext ht.table rfl rfl
  obtain hst := apply_step_table t (upd m₀ P D k).1.i (upd m₀ P D k).1.j he ht.i ht.j ht.count hk
  rw [hctx] at hst
  refine WP.mono hst fun u ⟨htab, hui, huj, hbyte, hother, hfr, hu0, huz, huk⟩ => ⟨?_, huz⟩
  obtain hkeep : ∀ x, x < L.toNat → x ≠ k →
      u.mem (State.addr D + BitVec.ofNat 64 x) = t.mem (State.addr D + BitVec.ofNat 64 x) :=
    fun x hx hne => hother _ (hsD x hx) (data_ne hx hk hne)
  refine
    { le := hk
      table := by rw [upd_succ]; exact htab
      i := by rw [upd_succ]; exact hui
      j := by rw [upd_succ]; exact huj
      data := ?_
      tail := fun x hx hxL => by
        rw [hkeep x hxL (by omega_using [hx])]
        exact ht.tail x (by omega_using [hx]) hxL
      frame := ht.frame.trans hfr
      count := hu0
      keep := (ht.keep.trans huk).mono (by decide) }
  rw [bytes_snoc, upd_succ, hbyte, ht.tail k (Nat.le_refl _) hk, ← ht.data]
  refine congrArg (· ++ _) ?_
  exact bytes_frame _ _ _ _ fun x hx => hkeep x (by omega_using [hk, hx]) (by omega_using [hx])

theorem apply_loop (m₀ : Mem) {P D L : BitVec 32} (b : State) (hb : StepEnv b P D L) {k : Nat}
    (hk : k < L.toNat) (t : State) (ht : LoopInv m₀ P D L b k t) :
    WP isa (.loop (.block applyStep) .ne) t (LoopInv m₀ P D L b L.toNat) := by
  refine WP.loop (M := isa)
    (fun rem u => ∃ j, j < L.toNat ∧ rem = L.toNat - j ∧ LoopInv m₀ P D L b j u)
    ?_ (L.toNat - k) t ⟨k, hk, rfl, ht⟩
  intro rem u ⟨j, hj, hrem, hu⟩
  refine WP.mono (loop_step m₀ b hb hj u hu) fun v ⟨hv, hz⟩ => ?_
  by_cases hend : j + 1 = L.toNat
  · left
    refine ⟨?_, hend ▸ hv⟩
    rw [hend, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.sub_self] at hz
    rw [eval_ne, hz]
    rfl
  · right
    have hL := L.isLt
    obtain hnz : BitVec.ofNat 32 (j + 1) - L ≠ 0#32 := by
      intro h
      obtain h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h'
      omega_using [hj, hend, h']
    refine ⟨?_, L.toNat - (j + 1), by omega_using [hj, hrem], j + 1, by omega_using [hj, hend], rfl, hv⟩
    rw [eval_ne, hz, beq_eq_false_iff_ne.mpr hnz]
    rfl

end VG.Proof.Rc4.Arm

end

end


/-! # RC4 on ARMv7: the stream function -/

@[expose] public section

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

theorem apply_entry (s : State) (hs : applyC.pre s) :
    WP isa (.block entry) s fun a => a.mem = s.mem ∧ Keep [.r12] s a ∧
      a.gpr .r12 = (contextAt s.mem (State.addr (s.gpr .r0))).i.setWidth 32 ∧
      a.z = (s.gpr .r2 - BitVec.ofNat 32 0 == 0#32) := by
  obtain ⟨_, hwr, _, _, _, cfit, _, _⟩ := hs
  obtain a256 : State.addr (s.gpr .r0 + BitVec.ofNat 32 256) = State.addr (s.gpr .r0) + 256#64 :=
    addr_add (a := s.gpr .r0) (k := 256) (by omega_using [cfit])
  obtain r256 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 256)) 1 := by
    rw [a256]
    refine region_in (region_offset _ _ 258 256 1 (by decide) (by decide) ?_)
    exact ⟨_, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  refine WP.mono (WP.keep (Q := fun a => a.mem = s.mem ∧
      a.gpr .r12 = (contextAt s.mem (State.addr (s.gpr .r0))).i.setWidth 32 ∧
      a.z = (s.gpr .r2 - BitVec.ofNat 32 0 == 0#32)) [.r12] ?_ (by decide))
    fun a ⟨h, hk⟩ => ⟨h.1, hk, h.2.1, h.2.2⟩
  unfold entry
  arun [r256]
  rw [a256]
  conj_rfl

theorem apply_start (b : State) {P : BitVec 32} (h0 : b.gpr .r0 = P)
    (hfit : P.toNat + 258 ≤ 2 ^ 32) (h257 : InRegions (b.rd ++ b.wr) (State.addr P + 257#64) 1) :
    WP isa (.block start) b fun c => c.mem = b.mem ∧ Keep [.r4, .r12, .r5, .r0, .r10] b c ∧
      c.gpr .r4 = b.gpr .r12 ∧ c.gpr .r12 = P ∧
      c.gpr .r5 = (b.mem (State.addr P + 257#64)).setWidth 32 ∧ c.gpr .r0 = 0#32 ∧
      c.gpr .r10 = BitVec.allOnes 32 := by
  obtain a257 : State.addr (P + BitVec.ofNat 32 257) = State.addr P + 257#64 := addr_add (by omega_using [hfit])
  obtain r257 : InRegions (b.rd ++ b.wr) (State.addr (P + BitVec.ofNat 32 257)) 1 := by
    rw [a257]; exact h257
  refine WP.mono (WP.keep (Q := fun c => c.mem = b.mem ∧ c.gpr .r4 = b.gpr .r12 ∧
      c.gpr .r12 = P ∧ c.gpr .r5 = (b.mem (State.addr P + 257#64)).setWidth 32 ∧
      c.gpr .r0 = 0#32 ∧ c.gpr .r10 = BitVec.allOnes 32) [.r4, .r12, .r5, .r0, .r10] ?_
    (by decide)) fun c ⟨h, hk⟩ => ⟨h.1, hk, h.2⟩
  unfold start ones
  arun [h0, r257, ones_eq]
  rw [a257]
  conj_rfl

theorem apply_finish (d : State) (i j : Byte) {P : BitVec 32} (hfit : P.toNat + 258 ≤ 2 ^ 32)
    (h4 : d.gpr .r4 = i.setWidth 32) (h5 : d.gpr .r5 = j.setWidth 32) (h12 : d.gpr .r12 = P)
    (hw : InRegions d.wr (State.addr P) 258) :
    WP isa (.block finish) d fun e =>
      e.mem = (d.mem.write (State.addr P + 256#64) 1 i).write (State.addr P + 257#64) 1 j ∧
      Keep [] d e := by
  obtain a256 : State.addr (P + BitVec.ofNat 32 256) = State.addr P + 256#64 := addr_add (by omega_using [hfit])
  obtain a257 : State.addr (P + BitVec.ofNat 32 257) = State.addr P + 257#64 := addr_add (by omega_using [hfit])
  obtain h256 : InRegions d.wr (State.addr (P + BitVec.ofNat 32 256)) 1 := by
    rw [a256]; exact region_offset _ _ _ 256 1 (by decide) (by decide) hw
  obtain h257 : InRegions d.wr (State.addr (P + BitVec.ofNat 32 257)) 1 := by
    rw [a257]; exact region_offset _ _ _ 257 1 (by decide) (by decide) hw
  refine WP.mono (WP.keep (Q := fun e =>
      e.mem = (d.mem.write (State.addr P + 256#64) 1 i).write (State.addr P + 257#64) 1 j)
    [] ?_ (by decide)) fun e ⟨h, hk⟩ => ⟨h, hk⟩
  unfold finish
  arun [h4, h5, h12, h256, h257]
  rw [a256, a257, writeW_byte8, writeW_byte8, low_byte32, low_byte32]

/-- The full stream function, including empty input. -/
theorem apply_ok (s : State) (hs : applyC.pre s) :
    WP isa VG.Impl.Rc4.Arm.apply s fun t => applyC.post s t ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp := by
  have hs' := hs
  obtain ⟨hrd, hwr, cd, cs, ds, cfit, dfit, sfit⟩ := hs'
  unfold applyC
  dsimp only
  generalize hP : s.gpr .r0 = P at hwr cd cs cfit ⊢
  generalize hD : s.gpr .r1 = D at hwr cd ds dfit ⊢
  generalize hL : s.gpr .r2 = L at hwr cd ds dfit ⊢
  generalize hS : s.gpr .r3 = Sc at hwr cs ds sfit
  obtain hctx : InRegions s.wr (State.addr P) 258 := ⟨_, by rw [hwr]; exact List.mem_cons_self,
    Region.contains_self _ _⟩
  obtain hdat : InRegions s.wr (State.addr D) L.toNat := ⟨_, by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩
  obtain hscr : InRegions s.wr (State.addr Sc) 64 := ⟨_, by
    rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
    Region.contains_self _ _⟩
  have hpres (t : State) (rs : List Reg) (hk : Keep rs s t) (hr : ∀ r ∈ preserved, r ∉ rs) :
      ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r h => hk.gpr (hr r h)
  unfold VG.Impl.Rc4.Arm.apply
  refine WP.seq (WP.mono (apply_entry s hs) fun a ⟨ham, hak, ha12, haz⟩ => ?_)
  rw [hP] at ha12
  rw [hL, BitVec.sub_zero] at haz
  refine WP.ite a.z (eval_eq a) (fun hz => ?_) (fun hnz => ?_)
  · have hL0 : L = 0#32 := by rw [haz, beq_iff_eq] at hz; exact hz
    refine WP.block_nil ⟨?_, hpres a _ hak (by decide), hak.2.2.2⟩
    rw [ham, hL0]
    exact ⟨rfl, rfl⟩
  obtain hL0 : L.toNat ≠ 0 := fun h => by
    have : L = 0#32 := BitVec.eq_of_toNat_eq h
    rw [haz, this] at hnz
    exact absurd hnz (by decide)
  refine WP.seq ?_
  obtain ha3 : a.gpr .r3 = Sc := (hak.gpr (by decide)).trans hS
  rw [WP.block_append_iff]
  refine WP.mono (save_ok a (by rw [ha3]; exact sfit) (by rw [hak.2.2.1, ha3]; exact hscr))
    fun b ⟨hbm, hbk⟩ => ?_
  rw [ha3] at hbm
  obtain ka : Keep [.r12] s b := (hak.trans hbk).mono (by decide)
  obtain hsave : Frame [⟨State.addr Sc, 64⟩] s.mem b.mem := by
    rw [hbm, ham]; exact save_frame _ _ _
  obtain hctxb : contextAt b.mem (State.addr P) = contextAt s.mem (State.addr P) :=
    contextAt_frame hsave fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cs
  obtain r257 : InRegions (b.rd ++ b.wr) (State.addr P + 257#64) 1 := by
    rw [ka.2.1, ka.2.2.1]
    exact region_in (region_offset _ _ _ 257 1 (by decide) (by decide) hctx)
  refine WP.mono (apply_start b ((ka.gpr (by decide)).trans hP) cfit r257)
    fun c ⟨hcm, hck, hc4, hc12, hc5, hc0, hc10⟩ => ?_
  obtain kc : Keep [.r12, .r4, .r5, .r0, .r10] s c := (ka.trans hck).mono (by decide)
  obtain hec : StepEnv c P D L :=
    { p := hc12
      d := (kc.gpr (by decide)).trans hD
      l := (kc.gpr (by decide)).trans hL
      ones := hc10
      pfit := cfit
      dfit := dfit
      table := by
        rw [kc.2.2.1]
        obtain h' := region_offset _ _ _ 0 256 (by decide) (by decide) hctx
        simpa only [BitVec.add_zero] using h'
      data := by rw [kc.2.2.1]; exact hdat
      sTD := sep_of_sub cd (contains_prefix _ (by decide)) (contains_prefix _ (Nat.le_refl _)) }
  obtain hinv : LoopInv s.mem P D L c 0 c := by
    have hu0 : upd s.mem P D 0 = (contextAt s.mem (State.addr P), []) := rfl
    refine
      { le := Nat.zero_le _
        table := by rw [hu0, hcm, hctxb]
        i := by
          rw [hu0, hc4, (hbk.gpr (by decide) : b.gpr .r12 = a.gpr .r12), ha12]
        j := by
          rw [hu0, hc5, ← hctxb]
          rfl
        data := by rw [hu0]; rfl
        tail := fun x _ hx => by
          rw [hcm]
          exact hsave.bytes (R := ⟨State.addr D, L.toNat⟩) (fun r hr => by
            simp only [List.mem_singleton] at hr
            subst hr
            exact ds) (show L.toNat ≤ 2 ^ 64 by have := L.isLt; omega_using []) hx
        frame := Frame.refl _ _
        count := hc0
        keep := Keep.refl _ _ }
  refine WP.seq (WP.mono (apply_loop s.mem c hec (Nat.pos_of_ne_zero hL0) c hinv)
    fun d hd => ?_)
  obtain kd : Keep (([.r12, .r4, .r5, .r0, .r10] : List Reg) ++ stepRegs) s d := kc.trans hd.keep
  rw [WP.block_append_iff]
  refine WP.mono (apply_finish d (upd s.mem P D L.toNat).1.i (upd s.mem P D L.toNat).1.j cfit
    hd.i hd.j ((hd.keep.gpr (by decide)).trans hc12) (by rw [kd.2.2.1]; exact hctx))
    fun e ⟨hem, hek⟩ => ?_
  obtain hce : Frame [⟨State.addr P, 258⟩, ⟨State.addr D, L.toNat⟩] b.mem e.mem := by
    have hc258 : (⟨State.addr P, 258⟩ : Region) ∈
        [⟨State.addr P, 258⟩, ⟨State.addr D, L.toNat⟩] := List.mem_cons_self
    rw [hem]
    refine Frame.write ?_ hc258 _ (Offset.contains_base _ (by decide) (by decide))
    refine Frame.write ?_ hc258 _ (Offset.contains_base _ (by decide) (by decide))
    obtain hbd : Frame (loopRegions P D L) b.mem d.mem := by rw [← hcm]; exact hd.frame
    refine hbd.sub fun r hr => ?_
    simp only [loopRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩
  obtain ke : Keep (([.r12, .r4, .r5, .r0, .r10] : List Reg) ++ stepRegs) s e :=
    (kd.trans hek).mono (by decide)
  obtain he3 : e.gpr .r3 = Sc := (ke.gpr (by decide)).trans hS
  obtain hsaved : Spill.Saved e.mem (State.addr (e.gpr .r3)) a.gpr saved := by
    rw [he3]
    obtain h0 : Spill.Saved b.mem (State.addr Sc) a.gpr saved := by
      rw [hbm]
      exact Spill.saveMem_saved _ _ _ _ saved_slots
    refine h0.frame saved_slots hce fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [BitVec.add_zero]
    rcases hr with rfl | rfl
    · exact (cs.symm.sub_left (Region.sub_prefix (by decide)))
    · exact (ds.symm.sub_left (Region.sub_prefix (by decide)))
  refine WP.mono (restore_ok e (by rw [he3]; exact sfit)
    (by rw [ke.2.1, ke.2.2.1, he3]; exact region_in hscr) hsaved)
    fun g ⟨hgr, hgk, hgm⟩ => ?_
  have hDP (o : Nat) (ho : o < 258) :
      Mem.Sep (State.addr D) L.toNat (State.addr P + BitVec.ofNat 64 o) 1 :=
    sep_of_sub cd.symm (contains_prefix _ (Nat.le_refl _))
      (Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho]))
  obtain hLn : L.toNat < 2 ^ 64 := by have := L.isLt; omega_using []
  refine ⟨⟨?_, ?_⟩, fun r hr => ?_, hgk.2.2.2.trans ke.2.2.2⟩
  · rw [hgm, hem, context_finish]
    exact context_ext hd.table rfl rfl
  · rw [hgm, hem, bytes_write_sep _ _ _ _ _ hLn (hDP 257 (by decide)),
      bytes_write_sep _ _ _ _ _ hLn (hDP 256 (by decide))]
    exact hd.data
  · by_cases hs : r ∈ saved.map Prod.fst
    · rw [hgr r hs]
      exact hak.gpr (by rw [saved_regs] at hs; revert hs; revert r; decide)
    · rw [hgk.gpr (by rw [← saved_regs]; exact hs)]
      have : r = .lr := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rw [saved_regs] at hs
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hs ⊢
      subst this
      exact ke.gpr (by decide)

end VG.Proof.Rc4.Arm
