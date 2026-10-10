import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Loop
import VerifiedGarbage.Proof.Rc2.AArch64.Vec.Loop

/-!
# Decryption's groups of eight blocks

`phase_ok`: the vector phase decrypts the first `8 ⌊n / 8⌋` of the `n`
blocks, leaves the chaining value updated and `x24` the blocks left.
`phaseLoop_ok`: it and the loop over the blocks left, as the loop alone.
-/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64 VG.Proof.Rc2 VG.Proof.Rc2.AArch64.Vec

theorem contains_prefix {a : Addr} {n k : Nat} (h : n ≤ k) : (⟨a, k⟩ : Region).Contains a n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith

/-- A region disjoint from a 128-byte one is shorter than the address space. -/
theorem Region.len_lt_of_disjoint {r r' : Region} (h : r.Disjoint r') (hr : 0 < r.len) :
    r'.len < 2 ^ 64 := by
  apply Nat.lt_of_not_le
  intro hl
  apply h r.base (contains_prefix hr)
  simp only [Region.Contains]
  have := (r.base - r'.base).isLt
  omega_arith

structure PhasePost (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (8 * (8 * (n / 8)))
  count : s'.gpr .x24 = BitVec.ofNat 64 (n % 8)
  reg : ∀ r ∈ kept, r ≠ .x1 → r ≠ .x24 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, r ≠ .x24 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [ivR s, dataR s (8 * (n / 8))] s.mem s'.mem
  data : Spec.Rc2.blocksAt s'.mem (s.gpr .x1) (8 * (n / 8)) =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) .decrypt
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) (8 * (n / 8)))).1
  iv : Spec.Rc2.blockAt s'.mem (s.gpr .x23) =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) .decrypt
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) (8 * (n / 8)))).2

theorem exec_lsr (s : State) (d n : Reg) {sh : Nat} (h : sh < 64) :
    exec (.lsr .x d n sh) s = some (s.write .x d (s.gpr n >>> sh)) := by
  simp [exec, Size.bits, h, State.read]

theorem ofNat_shift3 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hn]
  rw [Nat.mod_eq_of_lt (by omega_arith)]

theorem ofNat_mask3 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n <<< (64 - 3) >>> (64 - 3) = BitVec.ofNat 64 (n % 8) := by
  rw [maskBits _ 3 (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- The groups, when there are any. -/
theorem groups_ok (s s₁ : State) {n : Nat} (hp : StepPre s n) (bound : 8 * n < 2 ^ 64)
    (hg : 0 < n / 8) (e₁ : s₁ = s.write .x .x10 (BitVec.ofNat 64 (n / 8))) :
    WP isa (.seq (.block Vec.setup) (.seq (.loop (.block Vec.group) (.nonzero .x .x10))
      (.block [.str .x .x11 .x23 0]))) s₁ fun s' =>
        s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (8 * (8 * (n / 8))) ∧
        (∀ g, g ≠ .x1 → g ≠ .x6 → g ≠ .x7 → g ≠ .x9 → g ≠ .x10 → g ≠ .x11 → g ≠ .x12 →
          s'.gpr g = s.gpr g) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        Frame [ivR s, dataR s (8 * (n / 8))] s.mem s'.mem ∧
        Spec.Rc2.blocksAt s'.mem (s.gpr .x1) (8 * (n / 8)) =
          (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) .decrypt
            (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) (8 * (n / 8)))).1 ∧
        Spec.Rc2.blockAt s'.mem (s.gpr .x23) =
          (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) .decrypt
            (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) (8 * (n / 8)))).2 := by
  subst e₁
  let g := n / 8
  have z : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => BitVec.add_zero a
  apply WP.seq
  rw [Vec.setup, WP.block_append_iff]
  have rk : InRegions ((s.write .x .x10 (BitVec.ofNat 64 g)).rd ++ (s.write .x .x10 (BitVec.ofNat 64 g)).wr)
      ((s.write .x .x10 (BitVec.ofNat 64 g)).gpr .x0) 128 :=
    hp.reads _ _ ⟨keyR s, by simp, Region.contains_self _ _⟩
  refine WP.mono (loads_ok _ rk 8 (by decide)) fun a ⟨arow, av, ae⟩ => ?_
  let s₁ := s.write .x .x10 (BitVec.ofNat 64 g)
  have ag : a.gpr = s₁.gpr := by rw [ae]
  have am : a.mem = s.mem := by rw [ae]; rfl
  have ard : a.rd = s.rd := by rw [ae]; rfl
  have awr : a.wr = s.wr := by rw [ae]; rfl
  have asp : a.sp = s.sp := by rw [ae]; rfl
  have s₁g : ∀ r, r ≠ .x10 → s₁.gpr r = s.gpr r := fun r h => gpr_write_of_ne _ _ _ h
  let b₁ := a.write .x .x9 (BitVec.ofNat 64 65535)
  let b₂ := b₁.setV Vec.m16 (ofVWords ((b₁.gpr .x9).setWidth 32) ((b₁.gpr .x9).setWidth 32)
    ((b₁.gpr .x9).setWidth 32) ((b₁.gpr .x9).setWidth 32))
  let b₃ := b₂.write .x .x11 (b₂.mem.readW (b₂.gpr .x23 + BitVec.ofNat 64 0) 64)
  have x23 : b₂.gpr .x23 = s.gpr .x23 := by
    simp only [b₂, b₁, gpr_setV, gpr_write_of_ne _ _ _ (by decide : ¬Reg.x23 = .x9), ag]
    exact s₁g _ (by decide)
  have e₃ : exec (.ldr .x .x11 .x23 0) b₂ = some b₃ := exec_ldr_x b₂ .x11 .x23 0 ⟨by decide, by decide⟩ (by
    rw [x23, z]
    rw [show b₂.rd = s.rd from ard, show b₂.wr = s.wr from awr]
    exact hp.reads _ _ ⟨ivR s, by simp, Region.contains_self _ _⟩)
  refine WP.of_runBlock ⟨b₃, by
    rw [runBlock_cons, exec_imm _ _ _ (by decide), runStep_some, runBlock_cons, exec_dups,
      runStep_some, runBlock_cons, e₃, runStep_some, runBlock_nil], ?_⟩
  have b3g : ∀ r, r ≠ .x9 → r ≠ .x11 → b₃.gpr r = s₁.gpr r := fun r h9 h11 => by
    simp only [b₃, b₂, b₁, gpr_write_of_ne _ _ _ h11, gpr_setV, gpr_write_of_ne _ _ _ h9, ag]
  have x1 : b₃.gpr .x1 = s.gpr .x1 := (b3g _ (by decide) (by decide)).trans (s₁g _ (by decide))
  have hdata : (dataR s n).Contains (s.gpr .x1) (64 * g) := contains_prefix (by omega_arith)
  have big : 64 * g < 2 ^ 64 := by omega_arith
  apply WP.seq
  refine WP.mono (loopV_ok s.mem (s.gpr .x0) g b₃ (by omega_arith) big ?_ ?_ ?_ ?_ ?_) fun c hc => ?_
  · intro r hr
    have hne := (treg_ne_kb r hr).2
    simp only [b₃, b₂, b₁, v_write, v_setV_of_ne _ _ hne]
    rw [arow r hr]
    rw [show s₁.mem = s.mem from rfl, show s₁.gpr .x0 = s.gpr .x0 from s₁g _ (by decide)]
  · simp only [b₃, b₂, v_write, v_setV_self, b₁, gpr_write_self, BitVec.setWidth_eq]; rfl
  · rw [b3g _ (by decide) (by decide)]; exact gpr_write_self _ _ _ _
  · rw [x1, show b₃.rd = s.rd from ard, show b₃.wr = s.wr from awr]
    exact hp.reads _ _ ⟨dataR s n, by simp, hdata⟩
  · rw [x1, show b₃.wr = s.wr from awr]
    exact hp.writes _ _ ⟨dataR s n, by simp, hdata⟩
  -- The chaining value: the IV, then the last ciphertext block, stored.
  have cx23 : c.gpr .x23 = s.gpr .x23 := by
    rw [hc.reg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      b3g _ (by decide) (by decide), s₁g _ (by decide)]
  have b11 : wordBlock (b₃.gpr .x11) = Spec.Rc2.blockAt s.mem (s.gpr .x23) := by
    simp only [b₃, gpr_write_self, BitVec.setWidth_eq]
    rw [x23, z, ← blockAt_read64, show b₂.mem = s.mem from am]
  have data := hc.data
  have chain := hc.chain
  rw [b11, x1, show b₃.mem = s.mem from am] at data chain
  have ivw : InRegions c.wr (c.gpr .x23 + BitVec.ofNat 64 0) 8 := by
    rw [cx23, z, hc.wr, show b₃.wr = s.wr from awr]
    exact hp.writes _ _ ⟨ivR s, by simp, Region.contains_self _ _⟩
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_cons, exec_str_x c .x11 .x23 0 ⟨by decide, by decide⟩ ivw, runStep_some, runBlock_nil], ?_⟩
  simp only [cx23, z]
  have ivFrame := frame_store64 c.mem (s.gpr .x23) (c.gpr .x11)
  have sub : Region.Sub (dataR s (8 * g)) (dataR s n) := Region.sub_prefix (by omega_arith)
  refine ⟨?_, fun r h1 h6 h7 h9 h10 h11 h12 => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc.ptr, x1, show 64 * g = 8 * (8 * g) by omega_arith]
  · rw [hc.reg r h1 h6 h7 h9 h10 h11 h12, b3g r h9 h11, s₁g r h10]
  · rw [hc.rd]; exact ard
  · rw [hc.wr]; exact awr
  · rw [hc.sp]; exact asp
  · have f₁ : Frame [ivR s, dataR s (8 * g)] s.mem c.mem := by
      have := hc.frame
      rw [x1, show b₃.mem = s.mem from am] at this
      exact this.sub fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        exact ⟨dataR s (8 * g), by simp, Region.sub_prefix (by omega_arith)⟩
    exact f₁.writeW (r := ivR s) (by simp) _ (Region.contains_self _ _)
  · rw [blocksAt_frame ivFrame _ _ (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      exact (hp.ivData.sub_right sub).symm)]
    rw [show 8 * g = 8 * g from rfl] at data
    exact data
  · rw [blockAt_store64, chain]

theorem mask24_ok (s : State) :
    ∃ s', runBlock isa (mask .x24 3) s = some s' ∧
      s'.gpr .x24 = s.gpr .x24 <<< (64 - 3) >>> (64 - 3) ∧
      (∀ r, r ≠ .x24 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .x .x24 (s.gpr .x24 <<< (64 - 3))
  let s₂ := s₁.write .x .x24 (s₁.gpr .x24 >>> (64 - 3))
  refine ⟨s₂, by rw [mask, runBlock_cons, exec_lslx _ _ _ (by decide), runStep_some, runBlock_cons,
      exec_lsrx _ _ _ (by decide), runStep_some, runBlock_nil], ?_, fun r h => ?_, rfl, rfl, rfl⟩
  · simp only [s₂, s₁, gpr_write_self, BitVec.setWidth_eq]
  · simp only [s₂, s₁, gpr_write_of_ne _ _ _ h]

theorem phase_ok (s : State) {n : Nat} (hp : StepPre s n) (bound : 8 * n < 2 ^ 64)
    (count : s.gpr .x24 = BitVec.ofNat 64 n) :
    WP isa Vec.phase s (PhasePost s n) := by
  rw [Vec.phase]
  apply WP.seq
  let s₁ := s.write .x .x10 (s.gpr .x24 >>> 3)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, exec_lsr _ _ _ (by decide), runStep_some,
    runBlock_nil], ?_⟩
  have x10 : s.gpr .x24 >>> 3 = BitVec.ofNat 64 (n / 8) := by rw [count, ofNat_shift3 (by omega_arith)]
  have s₁g : ∀ r, r ≠ .x10 → s₁.gpr r = s.gpr r := fun r h => gpr_write_of_ne _ _ _ h
  apply WP.seq
  -- What the masking leaves, from a state with the blocks done.
  have finish : ∀ s₂ : State, s₂.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (8 * (8 * (n / 8))) →
      (∀ g, g ≠ .x1 → g ≠ .x6 → g ≠ .x7 → g ≠ .x9 → g ≠ .x10 → g ≠ .x11 → g ≠ .x12 →
        s₂.gpr g = s.gpr g) → s₂.rd = s.rd → s₂.wr = s.wr →
      Frame [ivR s, dataR s (8 * (n / 8))] s.mem s₂.mem →
      Spec.Rc2.blocksAt s₂.mem (s.gpr .x1) (8 * (n / 8)) =
        (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) .decrypt
          (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) (8 * (n / 8)))).1 →
      Spec.Rc2.blockAt s₂.mem (s.gpr .x23) =
        (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) .decrypt
          (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) (8 * (n / 8)))).2 →
      WP isa (.block (mask .x24 3)) s₂ (PhasePost s n) := by
    intro s₂ ptr reg rd wr fr data iv
    obtain ⟨s₃, run, c₃, g₃, m₃, rd₃, wr₃⟩ := mask24_ok s₂
    refine WP.of_runBlock ⟨s₃, run, ?_⟩
    have keep : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 →
        r ≠ .x24 → s₃.gpr r = s.gpr r := fun r a b c d e f i j => (g₃ r j).trans (reg r a b c d e f i)
    refine ⟨by rw [g₃ _ (by decide), ptr], ?_, fun r hr h1 h24 => ?_, fun r hr h24 => ?_,
      rd₃.trans rd, wr₃.trans wr, by rw [m₃]; exact fr, by rw [m₃]; exact data, by rw [m₃]; exact iv⟩
    · rw [c₃, reg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        count, ofNat_mask3 (by omega_arith)]
    · have : ∀ r ∈ kept, r ≠ .x1 → r ≠ .x24 → r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧
          r ≠ .x12 := by decide
      obtain ⟨a, b, c, d, e, f⟩ := this r hr h1 h24
      exact keep r h1 a b c d e f h24
    · have : ∀ r ∈ savedAcrossCall, r ≠ .x24 → r ≠ .x1 ∧ r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧
          r ≠ .x11 ∧ r ≠ .x12 := by decide
      obtain ⟨a, b, c, d, e, f, i⟩ := this r hr h24
      exact keep r a b c d e f i h24
  by_cases hg : n / 8 = 0
  · apply WP.ite true (by simp [eval, State.read, s₁, gpr_write_self, x10, hg])
    · intro _
      apply WP.block_nil
      apply finish s₁ (by rw [s₁g _ (by decide), hg]; exact (BitVec.add_zero _).symm) (fun g _ _ _ _ h _ _ => s₁g g h) rfl rfl
        (by rw [hg]; exact Frame.refl _ _)
      · rw [hg]; rfl
      · rw [hg]; rfl
    · intro h; cases h
  · apply WP.ite false (by
      simp [eval, State.read, s₁, gpr_write_self, x10]
      exact ofNat_ne_zero (by omega_arith) (by omega_arith))
    · intro h; cases h
    · intro _
      refine WP.mono (groups_ok s s₁ hp bound (by omega_arith) (by rw [← x10])) fun s₂ h => ?_
      obtain ⟨ptr, reg, rd, wr, _, fr, data, iv⟩ := h
      exact finish s₂ ptr reg rd wr fr data iv

/-- The groups, then the blocks left one at a time: CBC on all `n`. -/
theorem phaseLoop_ok (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 64) (hp : StepPre s n)
    (count : s.gpr .x24 = BitVec.ofNat 64 n) :
    WP isa (.seq Vec.phase (.ite (.zero .x .x24) (.block [])
      (.loop (Impl.Rc2.AArch64.Cbc.body .decrypt) (.nonzero .x .x24)))) s (LoopPost .decrypt s n) := by
  have strict : 8 * n < 2 ^ 64 := Region.len_lt_of_disjoint hp.keyData (show 0 < 128 by decide)
  apply WP.seq
  refine WP.mono (phase_ok s hp strict count) fun s' h' => ?_
  let g := n / 8
  have key' := h'.reg .x0 (by decide) (by decide) (by decide)
  have iv' := h'.reg .x23 (by decide) (by decide) (by decide)
  have buf' := h'.reg .x2 (by decide) (by decide) (by decide)
  have hp' : StepPre s' (n % 8) :=
    hp.slice (i := 8 * g) (by omega_arith) h'.rd h'.wr key' iv' buf' h'.ptr
  refine WP.mono (maybeLoop_ok .decrypt s' (n % 8) (by omega_arith) hp' h'.count) fun s'' h'' => ?_
  have subG : Region.Sub (dataR s (8 * g)) (dataR s n) := Region.sub_prefix (by omega_arith)
  have restSub : Region.Sub ⟨s.gpr .x1 + BitVec.ofNat 64 (8 * (8 * g)), 8 * (n % 8)⟩ (dataR s n) :=
    Offset.sub_base _ (by omega_arith)
  have keyFrame : Spec.Rc2.scheduleAt s'.mem (s.gpr .x0) = Spec.Rc2.scheduleAt s.mem (s.gpr .x0) :=
    scheduleAt_frame h'.mem _ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.keyIv
      · exact hp.keyData.sub_right subG)
  have restKeep : Spec.Rc2.blocksAt s'.mem (s.gpr .x1 + BitVec.ofNat 64 (8 * (8 * g))) (n % 8) =
      Spec.Rc2.blocksAt s.mem (s.gpr .x1 + BitVec.ofNat 64 (8 * (8 * g))) (n % 8) :=
    blocksAt_frame h'.mem _ _ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.ivData.sub_right restSub).symm
      · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith))
  have firstKeep : Spec.Rc2.blocksAt s''.mem (s.gpr .x1) (8 * g) =
      Spec.Rc2.blocksAt s'.mem (s.gpr .x1) (8 * g) :=
    blocksAt_frame h''.mem _ _ (by
      intro r hr
      simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only [ivR, iv']; exact (hp.ivData.sub_right subG).symm
      · simp only [dataR, h'.ptr]; exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)
      · simp only [buf']
        exact (hp.dataBuf.sub_left subG).sub_right (Region.sub_prefix (by decide : 264 ≤ 512)))
  have split : ∀ (mm : Mem) (q : Addr), Spec.Rc2.blocksAt mm q n =
      Spec.Rc2.blocksAt mm q (8 * g) ++ Spec.Rc2.blocksAt mm (q + BitVec.ofNat 64 (8 * (8 * g))) (n % 8) :=
    fun mm q => by rw [← blocksAt_add]; exact congrArg _ (by omega_arith)
  have data'' := h''.data
  have ivOut := h''.iv
  rw [h'.ptr, key', iv', keyFrame, h'.iv, restKeep] at data'' ivOut
  refine ⟨?_, h''.count, fun r hr h1 h24 => (h''.reg r hr h1 h24).trans (h'.reg r hr h1 h24),
    fun r hr h24 => (h''.callee r hr h24).trans (h'.callee r hr h24), h''.rd.trans h'.rd,
    h''.wr.trans h'.wr, ?_, ?_, ?_⟩
  · rw [h''.ptr, h'.ptr, Offset.add_add]
    exact congrArg _ (congrArg _ (by omega_arith))
  · refine (h'.mem.sub fun r hr => ?_).trans (loopFrame_slice (i := 8 * g) h''.mem (by omega_arith) iv' buf' h'.ptr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨ivR s, by simp [loopWrites], fun _ h => h⟩
    · exact ⟨dataR s n, by simp [loopWrites], subG⟩
  · rw [split, split, firstKeep, h'.data, cbc_append, data'']
  · rw [ivOut, split, cbc_append]

end VG.Proof.Rc2.AArch64.Cbc
