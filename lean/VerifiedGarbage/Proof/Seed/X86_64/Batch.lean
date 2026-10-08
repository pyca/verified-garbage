import VerifiedGarbage.Proof.Seed.X86_64.Copy
import VerifiedGarbage.Proof.Seed.Memory

/-!
# A batch on x86-64

`batch_ok`: a batch encrypts or decrypts the first `min n 16` blocks at
`rsi` in place (`n = rdx`), with the keys at `rdi` (`keysAt`), and moves
`rsi` and `rdx` past them.
-/

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Impl.Aes.X86_64 VG.Proof.Seed

/-! ## The batch size -/

theorem batchSize_ok (s : State) :
    WP isa batchSize s (fun s' => s'.gpr .rcx = BitVec.ofNat 64 (min (s.gpr .rdx).toNat 16) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr) := by
  let v := s.setReg .rcx (s.gpr .rdx)
  let c := decide ((v.gpr .rcx).toNat < ((16 : BitVec 32).signExtend 64).toNat)
  let s₁ := arithFlags v (v.gpr .rcx - (16 : BitVec 32).signExtend 64) c
    (subOverflow (v.gpr .rcx) ((16 : BitVec 32).signExtend 64) (v.gpr .rcx - (16 : BitVec 32).signExtend 64))
  have e₁ : runBlock isa [movR .rcx .rdx, .alu .cmp .rcx (.imm 16)] s = some s₁ := rfl
  have g₁ : ∀ r, s₁.gpr r = v.gpr r := fun r => by simp only [s₁, gpr_arithFlags]
  have hc : c = decide ((s.gpr .rdx).toNat < 16) := by
    simp only [c, v, gpr_setReg_self]; rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.ite c (by show s₁.cf = some c; rfl) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · rw [hc] at hb
    have hlt := of_decide_eq_true hb
    refine ⟨by rw [g₁, gpr_setReg_self, Nat.min_eq_left (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq],
      fun r hr => by rw [g₁, gpr_setReg_of_ne (s := s) _ hr], rfl, rfl, rfl⟩
  · rw [hc] at hb
    have hge := of_decide_eq_false hb
    let s₂ := s₁.setReg .rcx ((16 : BitVec 32).signExtend 64)
    refine WP.of_runBlock ⟨s₂, rfl, ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
    · rw [gpr_setReg_self, Nat.min_eq_right (by omega)]; rfl
    · rw [gpr_setReg_of_ne (s := s₁) _ hr, g₁, gpr_setReg_of_ne (s := s) _ hr]

/-! ## Small steps -/

theorem copyStart_ok (s : State) :
    ∃ t, runBlock isa copyStart s = some t ∧ t.gpr .r10 = s.gpr .rsi ∧ t.gpr .rbx = s.gpr .r9 ∧
      (∀ r, r ≠ .r10 → r ≠ .rbx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  ⟨_, rfl, by simp [gpr_setReg], by simp [gpr_setReg],
    fun r h1 h2 => by simp [gpr_setReg, h1, h2], rfl, rfl, rfl⟩

theorem exec_sub_reg (s : State) (d r : Reg) :
    ∃ t, exec (.alu .sub d (.reg r)) s = some t ∧ t.gpr d = s.gpr d - s.gpr r ∧
      t.zf = some (s.gpr d - s.gpr r == 0) ∧
      (∀ x, x ≠ d → t.gpr x = s.gpr x) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  ⟨_, rfl, by simp [gpr_setReg], rfl, fun r h => by simp [gpr_setReg, h, gpr_arithFlags], rfl, rfl, rfl⟩

theorem exec_movR (s : State) (d r : Reg) :
    ∃ t, exec (movR d r) s = some t ∧ t.gpr d = s.gpr r ∧
      (∀ x, x ≠ d → t.gpr x = s.gpr x) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.zf = s.zf :=
  ⟨_, rfl, by simp [gpr_setReg], fun r h => by simp [gpr_setReg, h], rfl, rfl, rfl, rfl⟩

theorem ofNat_zero_add (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-! ## Blocks and lanes -/

theorem roundsN_congr {k₁ k₂ : Nat → Spec.Seed.Word × Spec.Seed.Word} :
    ∀ (n : Nat) (q : Quad), (∀ j < n, k₁ j = k₂ j) → roundsN k₁ n q = roundsN k₂ n q
  | 0, _, _ => rfl
  | n + 1, q, h => by
    rw [roundsN_succ, roundsN_succ, h n (by omega), roundsN_congr n q fun j hj => h j (by omega)]

theorem crypt_congr {k₁ k₂ : Nat → Spec.Seed.Word × Spec.Seed.Word} (h : ∀ j < 16, k₁ j = k₂ j)
    (b : Spec.Seed.Block) : Spec.Seed.crypt k₁ b = Spec.Seed.crypt k₂ b := by
  rw [crypt_eq, crypt_eq, roundsN_congr 16 _ h]

theorem quad_of_lanes {t : State} {m : Mem} {p : Addr} {b : Nat}
    (h : ∀ w < 4, lv t (arrSlot w) b = bw m p b w) :
    quad t b = decodeQ (Spec.Seed.blockAt m (p + BitVec.ofNat 64 (16 * b))) := by
  rw [decodeQ_blockAt]
  simp only [quad, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), bw,
    Offset.add_ofNat_add_ofNat, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul]
  rfl

theorem encodeSwapped_get (t : State) (b : Nat) {i : Nat} (hi : i < 16) :
    (encodeSwapped (quad t b))[i] = outByte t b i := by
  have hk : ∀ w < 4, (#v[(quad t b).2.2.1, (quad t b).2.2.2, (quad t b).1, (quad t b).2.1] :
      Vector Spec.Seed.Word 4).getD w 0 = lv t (arrSlot ((w + 2) % 4)) b := by
    intro w hw
    rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  simp only [encodeSwapped, Vector.getElem_ofFn, outByte]
  rw [hk _ (by omega)]

theorem blockAt_of_bytes {m : Mem} {q : Addr} {v : Spec.Seed.Block}
    (h : ∀ i (hi : i < 16), m (q + BitVec.ofNat 64 i) = v[i]) : Spec.Seed.blockAt m q = v := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Seed.blockAt, Vector.getElem_ofFn]
  exact h i hi

/-- The masks are outside a region apart from the scratch buffer. -/
theorem masks_of_frame {s s' : State} {R : Region} (hm : MasksIn s) (hr9 : s'.gpr .r9 = s.gpr .r9)
    (hfr : Frame [R] s.mem s'.mem) (hd : R.Disjoint (scratchR s)) : MasksIn s' := by
  intro kv hkv
  have hlt := maskSlots_lt kv hkv
  rw [← hm kv hkv]
  show s'.mem.readW (Straight.wordAddr (s'.gpr .r9) kv.1) 64 = s.mem.readW (Straight.wordAddr (s.gpr .r9) kv.1) 64
  rw [hr9]
  refine hfr.readW (r := ⟨Straight.wordAddr (s.gpr .r9) kv.1, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  refine (hd.sub_right ?_).symm
  show Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 (8 * kv.1), 8⟩ ⟨s.gpr .r9, 8 * scratchSlots⟩
  exact Offset.sub_base _ (by unfold scratchSlots; omega)

/-! ## The batch -/

/-- What a batch needs: the scratch buffer and the masks; the batch's blocks
writable, and they and the keys apart from the scratch buffer and each other. -/
structure BatchPre (d : Spec.Seed.Direction) (s : State) : Prop where
  room : Room s
  masks : MasksIn s
  pos : 1 ≤ (s.gpr .rdx).toNat
  data : ∀ b < min (s.gpr .rdx).toNat 16, ∀ w < 4,
    InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (16 * b + 4 * w)) 4
  dataSep : Region.Disjoint ⟨s.gpr .rsi, 16 * min (s.gpr .rdx).toNat 16⟩ (scratchR s)
  keys : KeysOk d s (s.gpr .rdi)
  keyData : ∀ j < 16, Region.Disjoint ⟨kp d (s.gpr .rdi) j, 8⟩ ⟨s.gpr .rsi, 16 * min (s.gpr .rdx).toNat 16⟩

structure BatchPost (d : Spec.Seed.Direction) (s s' : State) : Prop where
  done : ∀ b < min (s.gpr .rdx).toNat 16,
    Spec.Seed.blockAt s'.mem (s.gpr .rsi + BitVec.ofNat 64 (16 * b)) =
      Spec.Seed.crypt (keysAt d s.mem (s.gpr .rdi))
        (Spec.Seed.blockAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (16 * b)))
  rsi : s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 (16 * min (s.gpr .rdx).toNat 16)
  rdx : s'.gpr .rdx = s.gpr .rdx - BitVec.ofNat 64 (min (s.gpr .rdx).toNat 16)
  zf : s'.zf = some (s.gpr .rdx - BitVec.ofNat 64 (min (s.gpr .rdx).toNat 16) == 0)
  regs : ∀ r ∈ [Reg.rdi, .r9, .rsp], s'.gpr r = s.gpr r
  masks : MasksIn s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [workR s, ⟨s.gpr .rsi, 16 * min (s.gpr .rdx).toNat 16⟩] s.mem s'.mem

theorem arraysR_sub_scratch (s : State) : Region.Sub (arraysR s) (scratchR s) := by
  show Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 (8 * 61), 8 * 64⟩ ⟨s.gpr .r9, 8 * scratchSlots⟩
  exact Offset.sub_base _ (by unfold scratchSlots; omega)

theorem arraysR_sub_work (s : State) : Region.Sub (arraysR s) (workR s) := by
  show Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 (8 * 61), 8 * 64⟩ ⟨s.gpr .r9, 8 * 125⟩
  exact Offset.sub_base _ (by omega)

theorem batch_ok (d : Spec.Seed.Direction) {s : State} (h : BatchPre d s) :
    WP isa (batch d) s (BatchPost d s) := by
  let n := (s.gpr .rdx).toNat
  let k := min n 16
  let p := s.gpr .rsi
  have hk1 : 1 ≤ k := by have := h.pos; omega
  have hk16 : k ≤ 16 := by omega
  have hpos := h.pos
  -- the copy in
  apply WP.seq
  apply WP.seq
  refine WP.mono (batchSize_ok s) fun s₁ ⟨c₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  apply WP.seq
  obtain ⟨s₂, e₂, r10₂, rbx₂, g₂, m₂, rd₂, wr₂⟩ := copyStart_ok s₁
  refine WP.of_runBlock ⟨s₂, e₂, ?_⟩
  have G₂ : ∀ r, r ≠ .rcx → r ≠ .r10 → r ≠ .rbx → s₂.gpr r = s.gpr r := fun r a b c =>
    (g₂ r b c).trans (g₁ r a)
  have r9₂ : s₂.gpr .r9 = s.gpr .r9 := G₂ _ (by decide) (by decide) (by decide)
  have scr₂ : scratchR s₂ = scratchR s := by simp only [scratchR, r9₂]
  have arr₂ : arraysR s₂ = arraysR s := by simp only [arraysR, r9₂]
  have room₂ : Room s₂ := room_congr h.room r9₂ (by rw [wr₂, wr₁])
  have pre₂ : CopyPre s₂ p k := by
    refine ⟨room₂, ⟨hk1, hk16⟩, fun b hb w hw => ?_, ?_⟩
    · obtain ⟨r, hr, hc⟩ := h.data b hb w hw
      exact ⟨r, by rw [rd₂, wr₂, rd₁, wr₁]; exact List.mem_append_right _ hr, hc⟩
    · rw [arr₂]; exact h.dataSep.sub_right (arraysR_sub_scratch s)
  have inv₂ : CopyInInv s₂ p k (k - k) s₂ := by
    refine ⟨by omega, ?_, ?_, ?_, fun w _ b hb => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩
    · rw [r10₂, Nat.sub_self, Nat.mul_zero, ofNat_zero_add, g₁ _ (by decide)]
    · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add, rbx₂, g₂ _ (by decide) (by decide)]
    · rw [Nat.sub_self, Nat.sub_zero, g₂ _ (by decide) (by decide), c₁]
  refine WP.mono (copyIn_loop pre₂ k s₂ inv₂ hk1 (Nat.le_refl _)) fun s₃ i₃ => ?_
  have r9₃ : s₃.gpr .r9 = s.gpr .r9 := (i₃.regs _ (by decide) (by decide) (by decide) (by decide)).trans r9₂
  have G₃ : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rsp], s₃.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .rax ∧ r ≠ .rbx ∧ r ≠ .rcx ∧ r ≠ .r10 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [i₃.regs _ this.1 this.2.1 this.2.2.1 this.2.2.2]
    exact G₂ _ this.2.2.1 this.2.2.2 this.2.1
  have rd₃ : s₃.rd = s.rd := by rw [i₃.rd, rd₂, rd₁]
  have wr₃ : s₃.wr = s.wr := by rw [i₃.wr, wr₂, wr₁]
  have room₃ : Room s₃ := room_congr h.room r9₃ wr₃
  have f₃ : Frame [arraysR s] s.mem s₃.mem := by
    have := i₃.frame; rw [arr₂, m₂, m₁] at this; exact this
  have masks₃ : MasksIn s₃ := masks_of_arrays h.masks r9₃ f₃
  have scr₃ : scratchR s₃ = scratchR s := by simp only [scratchR, r9₃]
  have keys₃ : KeysOk d s₃ (s₃.gpr .rdi) := by
    rw [G₃ .rdi (by simp)]
    intro j hj
    obtain ⟨a, b, c⟩ := h.keys j hj
    exact ⟨by rw [rd₃, wr₃]; exact a, by rw [rd₃, wr₃]; exact b, by rw [scr₃]; exact c⟩
  -- the keys are as on entry
  have hkeys : ∀ j < 16, keysAt d s₃.mem (s₃.gpr .rdi) j = keysAt d s.mem (s.gpr .rdi) j := by
    intro j hj
    rw [G₃ .rdi (by simp)]
    obtain ⟨-, -, hdis⟩ := h.keys j hj
    have hd : ∀ r ∈ [arraysR s], Region.Disjoint ⟨kp d (s.gpr .rdi) j, 8⟩ r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact hdis.sub_right (arraysR_sub_scratch s)
    simp only [keysAt]
    congr 1
    · exact f₃.readW (contains_prefix (by decide)) hd (by decide)
    · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
      exact f₃.readW (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by omega) (by omega)) hd (by decide)
  -- the blocks, in the lanes
  have hq₃ : ∀ b < k, quad s₃ b = decodeQ (Spec.Seed.blockAt s.mem (p + BitVec.ofNat 64 (16 * b))) := by
    intro b hb
    refine quad_of_lanes fun w hw => ?_
    rw [i₃.lanes w hw b hb, m₂, m₁]
  -- the rounds
  apply WP.seq
  refine WP.mono (rounds_ok d room₃ masks₃ keys₃) fun s₄ ⟨q₄, masks₄, room₄, rd₄, wr₄, g₄, f₄⟩ => ?_
  have G₄ : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .r9, .rsp], s₄.gpr r = s.gpr r := by
    intro r hr
    rw [g₄ r hr]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact G₃ _ (by simp)
    · exact G₃ _ (by simp)
    · exact G₃ _ (by simp)
    · exact r9₃
    · exact G₃ _ (by simp)
  have hq₄ : ∀ b < k, quad s₄ b = roundsN (keysAt d s.mem (s.gpr .rdi)) 16
      (decodeQ (Spec.Seed.blockAt s.mem (p + BitVec.ofNat 64 (16 * b)))) := by
    intro b hb
    rw [q₄ b (by omega), hq₃ b hb]
    exact roundsN_congr 16 _ hkeys
  -- the copy out
  apply WP.seq
  refine WP.mono (batchSize_ok s₄) fun s₅ ⟨c₅, g₅, m₅, rd₅, wr₅⟩ => ?_
  apply WP.seq
  obtain ⟨s₆, e₆, r10₆, rbx₆, g₆, m₆, rd₆, wr₆⟩ := copyStart_ok s₅
  refine WP.of_runBlock ⟨s₆, e₆, ?_⟩
  have G₆ : ∀ r, r ≠ .rcx → r ≠ .r10 → r ≠ .rbx → s₆.gpr r = s₄.gpr r := fun r a b c =>
    (g₆ r b c).trans (g₅ r a)
  have r9₆ : s₆.gpr .r9 = s.gpr .r9 := (G₆ _ (by decide) (by decide) (by decide)).trans (G₄ _ (by simp))
  have rdx₄ : s₄.gpr .rdx = s.gpr .rdx := G₄ _ (by simp)
  have rsi₄ : s₄.gpr .rsi = p := G₄ _ (by simp)
  have rd₆ : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₄, rd₃]
  have wr₆ : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, wr₃]
  have arr₆ : arraysR s₆ = arraysR s := by simp only [arraysR, r9₆]
  have pre₆ : CopyOutPre s₆ p k := by
    refine ⟨room_congr h.room r9₆ wr₆, ⟨hk1, hk16⟩, fun b hb w hw => ?_, ?_⟩
    · rw [wr₆]; exact h.data b hb w hw
    · rw [arr₆]; exact h.dataSep.sub_right (arraysR_sub_scratch s)
  have inv₆ : CopyOutInv s₆ p k (k - k) s₆ := by
    refine ⟨by omega, ?_, ?_, ?_, fun b hb => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩
    · rw [r10₆, Nat.sub_self, Nat.mul_zero, ofNat_zero_add, g₅ _ (by decide), rsi₄]
    · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add, rbx₆, g₆ _ (by decide) (by decide)]
    · rw [Nat.sub_self, Nat.sub_zero, g₆ _ (by decide) (by decide), c₅, rdx₄]
  have quad₆ : ∀ b, quad s₆ b = quad s₄ b := fun b => by
    simp only [quad, lv, laneA, m₆, m₅, r9₆, G₄ .r9 (by simp)]
  apply WP.seq
  refine WP.mono (copyOut_loop pre₆ k s₆ inv₆ hk1 (Nat.le_refl _)) fun s₇ i₇ => ?_
  apply WP.seq
  refine WP.mono (batchSize_ok s₇) fun s₈ ⟨c₈, g₈, m₈, rd₈, wr₈⟩ => ?_
  have G₇ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .r10 → s₇.gpr r = s₄.gpr r :=
    fun r a b c e => (i₇.regs r a b c e).trans (G₆ r c e b)
  have rdx₇ : s₇.gpr .rdx = s.gpr .rdx := (G₇ _ (by decide) (by decide) (by decide) (by decide)).trans rdx₄
  have c₈' : s₈.gpr .rcx = BitVec.ofNat 64 k := by rw [c₈, rdx₇]
  have r10₈ : s₈.gpr .r10 = p + BitVec.ofNat 64 (16 * k) := by rw [g₈ _ (by decide), i₇.r10]
  obtain ⟨s₉, e₉, rsi₉, g₉, m₉, rd₉, wr₉, -⟩ := exec_movR s₈ .rsi .r10
  obtain ⟨s', e', rdx', zf', g', m', rd', wr'⟩ := exec_sub_reg s₉ .rdx .rcx
  refine WP.of_runBlock ⟨s', by rw [runBlock_cons, e₉, runStep_some, runBlock_cons, e', runStep_some,
    runBlock_nil], ?_⟩
  have rdx₉ : s₉.gpr .rdx = s.gpr .rdx := by rw [g₉ _ (by decide), g₈ _ (by decide), rdx₇]
  have rcx₉ : s₉.gpr .rcx = BitVec.ofNat 64 k := by rw [g₉ _ (by decide), c₈']
  have mem' : s'.mem = s₇.mem := by rw [m', m₉, m₈]
  have G' : ∀ r ∈ [Reg.rdi, .r9, .rsp], s'.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .rcx ∧ r ≠ .rax ∧ r ≠ .rbx ∧ r ≠ .r10 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide
    rw [g' _ this.1, g₉ _ this.2.1, g₈ _ this.2.2.1, G₇ _ this.2.2.2.1 this.2.2.2.2.1 this.2.2.1 this.2.2.2.2.2]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    exact G₄ _ (by rcases hr with rfl | rfl | rfl <;> simp)
  have r9' : s'.gpr .r9 = s.gpr .r9 := G' _ (by simp)
  -- the memory
  have f₇ : Frame [⟨p, 16 * k⟩] s₄.mem s₇.mem := by
    have := i₇.frame; rw [m₆, m₅] at this; exact this
  have frame : Frame [workR s, ⟨p, 16 * k⟩] s.mem s'.mem := by
    rw [mem']
    have a : Frame [workR s, ⟨p, 16 * k⟩] s.mem s₃.mem :=
      (f₃.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨workR s, List.mem_cons_self, arraysR_sub_work s⟩)
    have b : Frame [workR s, ⟨p, 16 * k⟩] s₃.mem s₄.mem :=
      f₄.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [workR, r9₃]; exact List.mem_cons_self
    have c : Frame [workR s, ⟨p, 16 * k⟩] s₄.mem s₇.mem :=
      f₇.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact List.mem_cons_of_mem _ List.mem_cons_self
    exact (a.trans b).trans c
  refine ⟨fun b hb => ?_, ?_, ?_, ?_, G', ?_, by rw [rd', rd₉, rd₈, i₇.rd, rd₆],
    by rw [wr', wr₉, wr₈, i₇.wr, wr₆], frame⟩
  · rw [crypt_eq, ← hq₄ b hb, ← quad₆ b, mem']
    refine blockAt_of_bytes fun i hi => ?_
    rw [Offset.add_ofNat_add_ofNat, i₇.done b hb i hi, encodeSwapped_get _ _ hi]
  · rw [g' _ (by decide), rsi₉, r10₈]
  · rw [rdx', rdx₉, rcx₉]
  · rw [zf', rdx₉, rcx₉]
  · refine masks_of_frame masks₄ (r9'.trans (G₄ _ (by simp)).symm) (by rw [mem']; exact f₇) ?_
    simp only [scratchR, G₄ .r9 (by simp)]
    exact h.dataSep

end VG.Proof.Seed.X86_64
