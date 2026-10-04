import VerifiedGarbage.Proof.Argon2.Arm.Derive.Clear
import VerifiedGarbage.Proof.Argon2.MemoryInit
import VerifiedGarbage.Proof.Argon2.Matrix

/-!
# Argon2 on ARMv7: the memory's initialization

`memoryInit_ok`: after `memoryInit`, the memory matrix represents
`initMemory` (`Proof.Argon2.Represents`). The matrix is cleared, then each
lane's first two blocks are H′ of the 72 bytes at the start of the locals
(`initBlock_ok`), H₀ followed by the column and the lane, written there just
before the call. `LI s₀ h0 l` is the state after `l` lanes (`initCell`).
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_add wp_sub wp_cmp op2_imm op2_reg)
open VG.Spec.Blake2 (bytesAt)
open VG.Spec.Argon2 (Block blockAt zeroBlock parseBlock)
open VG.Impl.Argon2.Arm.Derive (ld st)

/-! ## Blocks in memory -/

/-- A block outside a frame's regions is kept. -/
theorem blockAt_keep {rs : List Region} {m m' : Mem} (f : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 1024⟩ r) : blockAt m' p = blockAt m p := by
  unfold blockAt
  exact congrArg Vector.ofFn (funext fun j => f.read (r := ⟨p, 1024⟩)
    (Offset.contains_base p (by have := j.isLt; omega) (by have := j.isLt; omega)) hd (by decide))

theorem read_zero {m : Mem} {a : Addr} {n : Nat} (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = 0) :
    m.read a n = 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have h0 : m a = 0 := by simpa using h 0 (by omega)
    have h1 : m.read (a + 1) n = 0 := ih fun i hi => by
      rw [BitVec.add_assoc, show (1 : Addr) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      exact h (1 + i) (by omega)
    simp only [Mem.read, h0, h1]
    exact BitVec.zero_append_zero

/-- A block of zero bytes. -/
theorem blockAt_zero {m : Mem} {p : Addr} (h : ∀ i < 1024, m (p + BitVec.ofNat 64 i) = 0) :
    blockAt m p = zeroBlock := by
  unfold blockAt zeroBlock
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn, Vector.getElem_replicate]
  exact read_zero fun i hi => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact h _ (by omega)

/-! ## The initialized cells -/

/-- Cell `k` after the first two blocks of the first `l` lanes are initialized. -/
def initCell (p : Spec.Argon2.Params) (h0 : List Byte) (l k : Nat) : Block :=
  if k / p.laneLen < l ∧ k % p.laneLen < 2 then
    parseBlock (initialBytes h0 (k / p.laneLen) (k % p.laneLen))
  else zeroBlock

theorem initCell_zero (p : Spec.Argon2.Params) (h0 : List Byte) (k : Nat) : initCell p h0 0 k = zeroBlock := by
  unfold initCell
  exact ite_eq_right fun h => Nat.not_lt_zero _ h.1

theorem cell_div {L l c : Nat} (hc : c < L) : (l * L + c) / L = l := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, Nat.zero_add]

theorem cell_mod {L l c : Nat} (hc : c < L) : (l * L + c) % L = c := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem initCell_new (p : Spec.Argon2.Params) (h0 : List Byte) {l c : Nat} (hL : 2 ≤ p.laneLen) (hc : c < 2) :
    initCell p h0 (l + 1) (l * p.laneLen + c) = parseBlock (initialBytes h0 l c) := by
  unfold initCell
  rw [cell_div (by omega), cell_mod (by omega)]
  exact ite_eq_left ⟨by omega, hc⟩

theorem initCell_old (p : Spec.Argon2.Params) (h0 : List Byte) {l k : Nat}
    (h₀ : k ≠ l * p.laneLen) (h₁ : k ≠ l * p.laneLen + 1) :
    initCell p h0 (l + 1) k = initCell p h0 l k := by
  unfold initCell
  have hdm := Nat.div_add_mod k p.laneLen
  by_cases hq : k / p.laneLen = l
  · rw [hq, Nat.mul_comm] at hdm
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · by_cases hc : k / p.laneLen < l ∧ k % p.laneLen < 2
    · rw [ite_eq_left (by omega), ite_eq_left hc]
    · rw [ite_eq_right (by omega), ite_eq_right hc]

/-- `a - b` is zero exactly when `a = b`, for 32-bit numbers. -/
theorem ofNat_sub_beq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : BitVec.ofNat 32 a - BitVec.ofNat 32 b ≠ 0 := by
      intro e
      have e' := congrArg BitVec.toNat e
      have z : (0 : BitVec 32).toNat = 0 := rfl
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, z] at e'
      omega
    rw [decide_eq_false h]
    exact beq_eq_false_iff_ne.mpr hne

/-! ## A lane's first blocks -/

/-- A store to the locals at `d` keeps their first `n ≤ d` bytes. -/
theorem loc_bytes_store {s₀ : State} (hp : DPre s₀) {m : Mem} {d n : Nat} (hn : n ≤ d) (hd : d + 4 ≤ 144)
    (v : BitVec 32) :
    bytesAt (m.writeW (State.addr (E s₀ + BitVec.ofNat 32 d)) v) (State.addr (E s₀)) n =
      bytesAt m (State.addr (E s₀)) n := by
  have := E_hi hp
  refine bytes_keep
    ((Frame.refl [⟨State.addr (E s₀ + BitVec.ofNat 32 d), 4⟩] m).writeW (List.mem_singleton_self _) v
      (Region.contains_self _ _))
    (fun r hr => ?_) (by omega)
  simp only [List.mem_singleton] at hr; subst hr
  exact disj32 (.inl (by rw [loc_nat hp (d := d) (by omega)]; omega)) (by omega)
    (by rw [loc_nat hp (d := d) (by omega)]; omega)

/-- The 72 bytes of H′'s input: H₀, then two words. -/
theorem bytes72 (m : Mem) (p : Addr) :
    bytesAt m p 72 = bytesAt m p 64 ++ Spec.Blake2.wordBytes (m.readW (p + BitVec.ofNat 64 64) 32) ++
      Spec.Blake2.wordBytes (m.readW (p + BitVec.ofNat 64 68) 32) := by
  rw [show (72 : Nat) = 64 + (4 + (4 + 0)) from rfl, Proof.Blake2.bytesAt_add, bytes_word, bytes_word,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  simp [bytesAt]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

omit hp in
/-- The call's frame lies in the body's regions. -/
theorem call_sub {O : Region} (hO : Region.Sub O (memR s₀) ∨ Region.Sub O (outR s₀)) :
    ∀ r ∈ [O, scrR s₀, callR s₀], ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hO with h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The first 64 bytes of the locals are outside a call's frame. -/
theorem h0_call {O : Region} (hO : Region.Sub O (memR s₀) ∨ Region.Sub O (outR s₀)) :
    ∀ r ∈ [O, scrR s₀, callR s₀], Region.Disjoint ⟨State.addr (E s₀), 64⟩ r := by
  have sub : Region.Sub ⟨State.addr (E s₀), 64⟩ (locR s₀) := Region.sub_prefix (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hO with h | h
    · exact ((loc_disj' hp (R := memR s₀) (by simp)).sub_left sub).sub_right h
    · exact ((loc_disj' hp (R := outR s₀) (by simp)).sub_left sub).sub_right h
  · exact (loc_disj' hp (R := scrR s₀) (by simp)).sub_left sub
  · exact (loc_call hp).sub_left sub

/-- A cell of the memory matrix is outside `scratch` and the stack below the locals. -/
theorem cell_disj {k : Nat} (hk : k < blocksN s₀) :
    ∀ r ∈ [scrR s₀, callR s₀], Region.Disjoint ⟨matrixCell (memB s₀) k, 1024⟩ r := by
  have sub : Region.Sub ⟨matrixCell (memB s₀) k, 1024⟩ (memR s₀) := matrixCell_sub _ _ _ hk
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.mem_scr.sub_left sub
  · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sub

theorem cell_addr {k : Nat} (hk : k < blocksN s₀) :
    State.addr (memP s₀ + BitVec.ofNat 32 (k * 1024)) = matrixCell (memB s₀) k := by
  have := hp.mem_fits
  have : k * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
  exact addr_add (by omega)

omit hp in
theorem cell_in_mem {k : Nat} (hk : k < blocksN s₀) :
    Region.Sub ⟨matrixCell (memB s₀) k, 1024⟩ (memR s₀) := matrixCell_sub _ _ _ hk

/-- Cells other than `k` are outside its region. -/
theorem cell_other {j k : Nat} (hj : j < blocksN s₀) (hk : k < blocksN s₀) (ne : j ≠ k) :
    Region.Disjoint ⟨matrixCell (memB s₀) j, 1024⟩ ⟨matrixCell (memB s₀) k, 1024⟩ :=
  matrixCell_disjoint _ _ _ _ (by have := hp.blocks_lt; omega) hj hk ne

/-- Block `c < 2` of lane `l`: H′ of H₀, `c` and `l`. -/
theorem initBlock_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem (State.addr (E s₀)) 64 = h0) {l c : Nat} (hl : l < lanesN s₀) (hc : c < 2)
    (r5 : s.gpr .r5 = BitVec.ofNat 32 l)
    (r6 : s.gpr .r6 = memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024)) :
    WP isa (Impl.Argon2.Arm.Derive.initBlock c) s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem (State.addr (E s₀)) 64 = h0 ∧ t.gpr .r5 = s.gpr .r5 ∧ t.gpr .r6 = s.gpr .r6 ∧
      blockAt t.mem (matrixCell (memB s₀) (l * (prm s₀).laneLen + c)) = parseBlock (initialBytes h0 l c) ∧
      ∀ k < blocksN s₀, k ≠ l * (prm s₀).laneLen + c →
        blockAt t.mem (matrixCell (memB s₀) k) = blockAt s.mem (matrixCell (memB s₀) k) := by
  have hE := E_hi hp
  have hs := hp.scr_fits
  have hm := hp.mem_fits
  have hlt := hp.lanes_lt
  have L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega
  have hcell : l * (prm s₀).laneLen + c < blocksN s₀ := by
    rw [hp.blocks_eq]
    have := Nat.mul_le_mul_right (prm s₀).laneLen (show l + 1 ≤ lanesN s₀ by omega)
    rw [Nat.succ_mul] at this
    omega
  have hec : encodable (BitVec.ofNat 32 c) = true := by
    rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> decide
  unfold Impl.Argon2.Arm.Derive.initBlock
  refine WP.seq (wp_mov (op2_imm hec) fun s₁ u₁ => ?_)
  have i₁ := h.upd u₁ (by decide)
  refine wp_stloc hp i₁ (d := 64) (by decide) fun s₂ i₂ v₂ o₂ g₂ m₂ => ?_
  refine wp_stloc hp i₂ (d := 68) (by decide) fun s₃ i₃ v₃ o₃ g₃ m₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_imm (by decide)) fun s₇ u₇ => ?_
  have i₇ := (((i₃.upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇ (by decide)
  refine wp_ldarg hp i₇ (i := 15) (by decide) fun s₈ u₈ => WP.block_nil ?_
  have i₈ := i₇.upd u₈ (by decide)
  have m₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have g₈ : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₈.gpr r = s.gpr r :=
    fun r a b d e f => by
      rw [u₈.other _ f, u₇.other _ e, u₆.other _ d, u₅.other _ b, u₄.other _ a, g₃, g₂, u₁.other _ a]
  have r0₈ : s₈.gpr .r0 = E s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      i₃.r11]
  have r1₈ : (s₈.gpr .r1).toNat = 72 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]; rfl
  have r3₈ : (s₈.gpr .r3).toNat = 1024 := by rw [u₈.other _ (by decide), u₇.gpr]; rfl
  have r2₈ : s₈.gpr .r2 = s.gpr .r6 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      g₃, g₂, u₁.other _ (by decide)]
  have O : State.addr (s₈.gpr .r2) = matrixCell (memB s₀) (l * (prm s₀).laneLen + c) := by
    rw [r2₈, r6, cell_addr hp hcell]
  have sO : Region.Sub ⟨State.addr (s₈.gpr .r2), (s₈.gpr .r3).toNat⟩ (memR s₀) := by
    rw [O, r3₈]; exact cell_in_mem hcell
  have hcell' : (l * (prm s₀).laneLen + c) * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
  refine hcall_ok hp i₈ u₈.gpr
    ⟨locR s₀, by simp, 0, by rw [r0₈]; simp, by rw [r1₈]; show 0 + 72 ≤ 144; omega⟩ (by rw [r0₈, r1₈]; omega)
    ⟨memR s₀, by simp, (l * (prm s₀).laneLen + c) * 1024, by rw [O]; rfl, by rw [r3₈]; exact hcell'⟩
    (by rw [r2₈, r6, r3₈, add_nat (x := memP s₀) (k := (l * (prm s₀).laneLen + c) * 1024) (by omega)]; omega)
    (by rw [r3₈]; decide)
    fun t it cs fr post => ⟨it, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The parameters.
    exact Prm.of_lw pr fun d hd => by
      have hd' := prm_offs d hd
      rw [lw_keep hp fr (call_sub (.inl sO)) hd'.1, lw_mem m₈, o₃ d (by omega) (by omega),
        o₂ d (by omega) (by omega), lw_mem u₁.mem]
  · rw [bytes_keep fr (h0_call hp (.inl sO)) (by omega), m₈, m₃,
      loc_bytes_store hp (by decide) (by decide), m₂, loc_bytes_store hp (by decide) (by decide), u₁.mem, b0]
  · rw [cs .r5 (by decide) (by decide), g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [cs .r6 (by decide) (by decide), g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · refine Proof.Argon2.blockAt_of_initialBytes _ _ _ _ _ ?_
    rw [← O, ← r3₈, post, r3₈, r0₈, r1₈, bytes72, m₈]
    have w64 : s₃.mem.readW (State.addr (E s₀) + BitVec.ofNat 64 64) 32 = BitVec.ofNat 32 c := by
      rw [← loc_addr hp (by omega)]
      show lw s₀ s₃ 64 = _
      rw [o₃ 64 (by decide) (by decide), v₂, u₁.gpr]
    have w68 : s₃.mem.readW (State.addr (E s₀) + BitVec.ofNat 64 68) 32 = BitVec.ofNat 32 l := by
      rw [← loc_addr hp (by omega)]
      show lw s₀ s₃ 68 = _
      rw [v₃, g₂, u₁.other _ (by decide), r5]
    rw [w64, w68, m₃, loc_bytes_store hp (by decide) (by decide), m₂, loc_bytes_store hp (by decide) (by decide),
      u₁.mem, b0]
    rfl
  · intro k hk ne
    have fs : Frame [⟨State.addr (E s₀ + BitVec.ofNat 32 64), 4⟩, ⟨State.addr (E s₀ + BitVec.ofNat 32 68), 4⟩]
        s.mem s₃.mem := by
      rw [m₃, m₂, u₁.mem]
      exact ((Frame.refl _ _).writeW (w := 32) List.mem_cons_self _ (Region.contains_self _ _)).writeW (w := 32)
        (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)
    rw [blockAt_keep fr (fun r hr => ?_), m₈]
    · -- The stores to the locals.
      refine blockAt_keep fs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ((loc_disj hp (d := 64) (by decide) (memR s₀) (by simp)).symm.sub_left (cell_in_mem hk))
      · exact ((loc_disj hp (d := 68) (by decide) (memR s₀) (by simp)).symm.sub_left (cell_in_mem hk))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [O, r3₈]; exact cell_other hp hk hcell ne
      · exact cell_disj hp hk _ (by simp)
      · exact cell_disj hp hk _ (by simp)

end

/-- The state after the first two blocks of `l` lanes. -/
structure LI (s₀ : State) (h0 : List Byte) (l : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  b0 : bytesAt s.mem (State.addr (E s₀)) 64 = h0
  r5 : s.gpr .r5 = BitVec.ofNat 32 l
  r6 : s.gpr .r6 = memP s₀ + BitVec.ofNat 32 (l * (prm s₀).laneLen * 1024)
  cells : ∀ k < blocksN s₀, blockAt s.mem (matrixCell (memB s₀) k) = initCell (prm s₀) h0 l k

theorem Prm.of_mem {s₀ s t : State} (pr : Prm s₀ s) (h : t.mem = s.mem) : Prm s₀ t :=
  Prm.of_lw pr fun d _ => lw_mem h d

theorem r6_next (x : BitVec 32) (a b : Nat) :
    x + BitVec.ofNat 32 a + 1024 + BitVec.ofNat 32 b - 1024 = x + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc (x + _) 1024, BitVec.add_comm 1024 (BitVec.ofNat 32 b), ← BitVec.add_assoc,
    BitVec.add_sub_cancel, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem lane_ok {h0 : List Byte} {l : Nat} {s : State} (hl : l < lanesN s₀) (h : LI s₀ h0 l s) :
    WP isa Impl.Argon2.Arm.Derive.initLane s fun t =>
      LI s₀ h0 (l + 1) t ∧ VG.Arm.eval .ne t = some (!decide (l + 1 = lanesN s₀)) := by
  have L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega
  have hlt := hp.lanes_lt
  unfold Impl.Argon2.Arm.Derive.initLane
  refine WP.seq ((initBlock_ok hp h.inv h.pr h.b0 hl (c := 0) (by decide) h.r5
    (by rw [h.r6, Nat.add_zero])).mono fun s₁ ⟨i₁, p₁, b₁, e₁, d₁, w₁, o₁⟩ => ?_)
  refine WP.seq (wp_add (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil ?_)
  have i₂ := i₁.upd u₂ (by decide)
  refine WP.seq ((initBlock_ok hp i₂ (p₁.of_mem u₂.mem) (h0 := h0) (by rw [u₂.mem]; exact b₁) hl (c := 1)
    (by decide) (by rw [u₂.other _ (by decide), e₁, h.r5])
    (by rw [u₂.gpr, d₁, h.r6, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat, Nat.succ_mul])).mono fun s₃ ⟨i₃, p₃, b₃, e₃, d₃, w₃, o₃⟩ => ?_)
  simp only [Impl.Argon2.Arm.Derive.nextLane]
  refine wp_ldloc hp i₃ (d := Impl.Argon2.Arm.Derive.strideOff) (by decide) fun s₄ u₄ =>
    wp_add (op2_reg _ _) fun s₅ u₅ => wp_sub (op2_imm (by decide)) fun s₆ u₆ =>
      wp_add (op2_imm (by decide)) fun s₇ u₇ => ?_
  have i₇ := (((i₃.upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇ (by decide)
  refine wp_ldarg hp i₇ (i := 7) (by decide) fun s₈ u₈ => ?_
  have i₈ := i₇.upd u₈ (by decide)
  have m₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have r5₈ : s₈.gpr .r5 = BitVec.ofNat 32 (l + 1) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), e₃,
      u₂.other _ (by decide), e₁, h.r5, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_add_ofNat]
  refine wp_cmp (op2_reg _ _) fun t f z => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact i₈.step f.sp (by rw [f.gpr]) f.rd f.wr (by rw [f.mem]; exact Frame.refl _ _)
  · exact p₃.of_mem (by rw [f.mem, m₈])
  · rw [f.mem, m₈, b₃]
  · rw [f.gpr, r5₈]
  · rw [f.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr, u₄.other _ (by decide), d₃,
      u₂.gpr, d₁, h.r6, p₃.stride, r6_next, Nat.succ_mul, Nat.add_mul]
  · intro k hk
    rw [f.mem, m₈]
    by_cases k1 : k = l * (prm s₀).laneLen + 1
    · rw [k1, w₃]; exact (initCell_new _ _ L2 (by decide)).symm
    rw [o₃ k hk k1]
    by_cases k0 : k = l * (prm s₀).laneLen
    · rw [u₂.mem, k0, show l * (prm s₀).laneLen = l * (prm s₀).laneLen + 0 from rfl, w₁]
      exact (initCell_new _ _ L2 (by decide)).symm
    rw [u₂.mem, o₁ k hk (by omega), h.cells k hk, initCell_old _ _ k0 k1]
  · rw [MdStream.Arm.eval_ne, z, u₈.gpr, r5₈, show arg s₀ 7 = BitVec.ofNat 32 (lanesN s₀) by simp,
      ofNat_sub_beq (by omega) (by omega)]

/-- `clear`, from the body with H₀ in the locals. -/
theorem clearW_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem (State.addr (E s₀)) 64 = h0) :
    WP isa Impl.Argon2.Arm.Derive.clear s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem (State.addr (E s₀)) 64 = h0 ∧ ∀ i < blocksN s₀ * 1024,
        t.mem (memB s₀ + BitVec.ofNat 64 i) = 0 := by
  refine (clear_ok hp h).mono fun s₁ ⟨i₁, f₁, z₁⟩ => ⟨i₁, ?_, ?_, z₁⟩
  · have fsub : ∀ r ∈ [memR s₀], ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' :=
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩
    exact Prm.of_lw pr fun d hd => lw_keep hp f₁ fsub (prm_offs d hd).1
  · rw [bytes_keep f₁ (fun r hr => ?_) (by omega), b0]
    simp only [List.mem_singleton] at hr; subst hr
    exact (loc_disj' hp (R := memR s₀) (by simp)).sub_left (Region.sub_prefix (by decide))

/-- The first lane's first block, after `clear`. -/
theorem laneStart_ok {s : State} {h0 : List Byte} (h : Inv s₀ s ∧ Prm s₀ s ∧
      bytesAt s.mem (State.addr (E s₀)) 64 = h0 ∧ ∀ i < blocksN s₀ * 1024,
        s.mem (memB s₀ + BitVec.ofNat 64 i) = 0) :
    WP isa (.block [ld .r6 (Impl.Argon2.Arm.Derive.argOff 13), .mov .r5 (.imm 0)]) s (LI s₀ h0 0) := by
  obtain ⟨i₁, p₁, b₁, z₁⟩ := h
  refine wp_ldarg hp i₁ (i := 13) (by decide) fun s₂ u₂ => wp_mov (op2_imm (by decide)) fun s₃ u₃ =>
    WP.block_nil ?_
  have i₃ := (i₁.upd u₂ (by decide)).upd u₃ (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem]
  refine ⟨i₃, p₁.of_mem m₃, by rw [m₃]; exact b₁, u₃.gpr, ?_, fun k hk => ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr]; simp
  · rw [initCell_zero, m₃]
    refine blockAt_zero fun i hi => ?_
    rw [matrixCell, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact z₁ _ (by omega)

theorem memoryInit_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem (State.addr (E s₀)) 64 = h0) :
    WP isa Impl.Argon2.Arm.Derive.memoryInit s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      Represents t.mem (memB s₀) (prm s₀).blocks (Spec.Argon2.initMemory (prm s₀) h0).memory := by
  have hlt := hp.lanes_lt
  have hl1 := hp.lanes_pos
  have hb := hp.blocks_lt
  unfold Impl.Argon2.Arm.Derive.memoryInit
  refine WP.seq ((clearW_ok hp h pr b0).mono fun s₁ h₁ => WP.seq ((laneStart_ok hp h₁).mono fun s₃ start => ?_))
  refine WP.loop (M := isa) (fun n t => ∃ l, n = lanesN s₀ - l ∧ l < lanesN s₀ ∧ LI s₀ h0 l t) ?_
    (lanesN s₀) s₃ ⟨0, by omega, by omega, start⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (lane_ok hp hl ht).mono fun u ⟨hu, cu⟩ => ?_
  by_cases done : l + 1 = lanesN s₀
  · refine .inl ⟨by show VG.Arm.eval .ne u = _; rw [cu]; simp [done], hu.inv, hu.pr, ?_⟩
    refine ⟨Proof.Argon2.initMemory_size _ _, fun k hk => ?_⟩
    have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
    rw [hu.cells k hk', Array.getElem?_eq_getElem (by rw [Proof.Argon2.initMemory_size]; exact hk),
      Option.getD_some, Proof.Argon2.initMemory_cell _ _ _ hk, initCell, done]
    have : k / (prm s₀).laneLen < lanesN s₀ := by
      rw [hp.blocks_eq] at hk'
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk')
    by_cases c2 : k % (prm s₀).laneLen < 2
    · rw [ite_eq_left ⟨this, c2⟩, ite_eq_left c2]
    · rw [ite_eq_right (fun h => c2 h.2), ite_eq_right c2]
  · refine .inr ⟨by show VG.Arm.eval .ne u = _; rw [cu]; simp [done], lanesN s₀ - (l + 1), by omega, l + 1, rfl, by omega, hu⟩

end

end VG.Proof.Argon2.Arm.Derive
