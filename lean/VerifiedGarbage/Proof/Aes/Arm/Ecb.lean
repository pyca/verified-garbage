import VerifiedGarbage.Proof.Aes.Arm.Decrypt
import VerifiedGarbage.Spec.Aes.Contract

/-!
# AES on whole blocks on ARMv7: the groups

A group of `blocks` loads (up to) two blocks of the data into the state
registers as `ortho` takes them, runs a transformation of two blocks
(`encrypt2` or `decrypt2`, whose proofs give `CryptOk`), and stores the
results back in place. The loaded blocks are named by the bytes of the
registers (`regBlock`), so that the last group needs no padding: its unused
block is whatever the registers held. The data's invariant (`EcbInv`) says
that the first `k` words hold the transformation of the original blocks,
and the others are still the original ones.
-/

namespace VG.Proof.Aes.Arm.Ecb

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_cmp
  wp_ldr wp_str)
open VG.Proof.Aes (getD_eq byte_ext)

/-- The state made of the bytes of the words: byte `i` of block `c` is byte
`i mod 4` of word `2 ⌊i / 4⌋ + c`, as `InRel` places them. -/
def regBlock (Q : Nat → BitVec 32) (c : Nat) : Spec.Aes.State :=
  Vector.ofFn fun i => (Q (2 * (i.1 / 4) + c)).extractLsb' (8 * (i.1 % 4)) 8

theorem inRel_regBlock (Q : Nat → BitVec 32) : InRel Q (regBlock Q) := by
  intro b _ i hi j hj
  rw [getD_eq _ hi]
  simp [regBlock, hj]

/-- What a transformation of two blocks does: `f R w` to each, with the
round keys as `EncPre` has them and the first one's address in slot
`fkSlot`. -/
def CryptOk (crypt2 : Prog isa) (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Prop :=
  ∀ {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}, EncPre s₀ R w →
    FirstKey s₀ s₀.mem → InRel (Q s₀) S →
    WP isa crypt2 s₀ fun s => Ctx s₀ s ∧ InRel (Q s) (fun b => f R w (S b))

theorem encrypt2_cryptOk : CryptOk encrypt2 Spec.Aes.cipher := fun hp _ hin => encrypt2_ok hp hin
theorem decrypt2_cryptOk : CryptOk decrypt2 Spec.Aes.invCipher := fun hp hfk hin => decrypt2_ok hp hfk hin

/-! ## The data -/

/-- The data after `k` words: the first `4 k` of the `16 n` bytes at `D` are
`F`'s (block by block), the others are still `m₀`'s. -/
def EcbInv (m₀ m : Mem) (D : Addr) (n k : Nat) (F : Nat → Spec.Aes.State) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    if i < 4 * k then (F (i / 16)).getD (i % 16) 0 else m₀ (D + BitVec.ofNat 64 i)

theorem writeW32_apply (m : Mem) (a x : Addr) (v : BitVec 32) :
    m.writeW a v x = if (x - a).toNat < 4 then v.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  rw [show m.writeW a v x = if (x - a).toNat < 32 / 8 then
      (v.setWidth (8 * (32 / 8))).extractLsb' (8 * (x - a).toNat) 8 else m x from rfl]
  rfl

/-- One more word stored. -/
theorem ecbInv_step {m₀ m : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State} {v : BitVec 32}
    (hn : 16 * n ≤ 2 ^ 32) (hk : k < 4 * n) (h : EcbInv m₀ m D n k F)
    (hv : ∀ t < 4, v.extractLsb' (8 * t) 8 = (F ((4 * k + t) / 16)).getD ((4 * k + t) % 16) 0) :
    EcbInv m₀ (m.writeW (D + BitVec.ofNat 64 (4 * k)) v) D n (k + 1) F ∧
      Frame [⟨D, 16 * n⟩] m (m.writeW (D + BitVec.ofNat 64 (4 * k)) v) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · rw [writeW32_apply, off_toNat D (by omega) (by omega)]
    by_cases h1 : 4 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 4 * k < 4
      · rw [ite_eq_left h2, hv _ h2, ite_eq_left (show i < 4 * (k + 1) by omega),
          show 4 * k + (i - 4 * k) = i by omega]
      · rw [ite_eq_right h2, h i hi, ite_eq_right (show ¬ i < 4 * k by omega),
          ite_eq_right (show ¬ i < 4 * (k + 1) by omega)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 4 * k < 4 by omega), h i hi,
        ite_eq_left (show i < 4 * k by omega), ite_eq_left (show i < 4 * (k + 1) by omega)]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx _ (List.mem_singleton_self _)
    rw [writeW32_apply, ite_eq_right]
    have : 4 * k < 2 ^ 64 := by omega
    have : (BitVec.ofNat 64 (4 * k)).toNat = 4 * k := by simp; omega
    bv_omega

theorem ecbInv_mono {m₀ m : Mem} {D : Addr} {n k k' : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n k F) (hk : 4 * n ≤ k) (hk' : 4 * n ≤ k') : EcbInv m₀ m D n k' F := by
  intro i hi
  rw [h i hi, ite_eq_left (show i < 4 * k by omega), ite_eq_left (show i < 4 * k' by omega)]

theorem ecbInv_frame {m₀ m m' : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State}
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r)
    (hn : 16 * n < 2 ^ 64) (h : EcbInv m₀ m D n k F) : EcbInv m₀ m' D n k F := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega) hi

/-- The output blocks: `f R w` of the original ones. -/
def ecbOut (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (D : Addr) (R : Nat)
    (w : List Byte) (j : Nat) : Spec.Aes.State :=
  f R w (Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j)))

/-! ## Loading -/

theorem regBlock_load {Q : Nat → BitVec 32} {m : Mem} {A : Addr} {c : Nat}
    (h : ∀ k < 4, Q (2 * k + c) = m.readW (A + BitVec.ofNat 64 (4 * k)) 32) :
    regBlock Q c = Spec.Aes.stateAt m A := by
  apply Vector.ext
  intro i hi
  refine byte_ext fun j hj => ?_
  simp only [regBlock, Spec.Aes.stateAt, Vector.getElem_ofFn, BitVec.getLsbD_extractLsb', hj,
    decide_true, Bool.true_and]
  rw [h _ (by omega), readW_bit _ _ (by omega) hj, Offset.add_add,
    show 4 * (i / 4) + i % 4 = i by omega]

/-- Block `j` of the data, while the first `k ≤ 4 j` words are written, is the original one. -/
theorem stateAt_ecbInv {m₀ m : Mem} {D : Addr} {n k j : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n k F) (hj : j < n) (hk : k ≤ 4 * j) :
    Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16 * j)) = Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j)) := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega), ite_eq_right (by omega)]

theorem q_blk : ∀ c < 2, ∀ k < 4, q (2 * k + c) ≠ .r10 ∧ q (2 * k + c) ≠ .r11 ∧ q (2 * k + c) ≠ .r12 ∧
    q (2 * k + c) ≠ sb ∧ q (2 * k + c) ≠ kp ∧ q (2 * k + c) ≠ .lr := by
  decide

theorem loadBlock_wp {s : State} {Dp : BitVec 32} {n g c : Nat} (hc : c < 2) (hgc : 2 * g + c < n)
    (hfit : Dp.toNat + 16 * n ≤ 2 ^ 32) (hdat : (⟨State.addr Dp, 16 * n⟩ : Region) ∈ s.wr)
    (h10 : s.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g)) {P : State → Prop}
    (h : ∀ s', (∀ k < 4, s'.gpr (q (2 * k + c)) =
        s.mem.readW (State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c)) + BitVec.ofNat 64 (4 * k)) 32) →
      (∀ r, (∀ k < 4, r ≠ q (2 * k + c)) → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa (.block (loadBlock c)) s P := by
  have ha : ∀ (s' : State), s'.gpr .r10 = s.gpr .r10 → s'.wr = s.wr → ∀ k < 4,
      State.addr (s'.gpr .r10 + BitVec.ofNat 32 (16 * c + 4 * k)) =
        State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c)) + BitVec.ofNat 64 (4 * k) ∧
      InRegions (s'.rd ++ s'.wr)
        (State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c)) + BitVec.ofNat 64 (4 * k)) 4 := by
    intro s' h1 h2 k hk
    have e : State.addr (s'.gpr .r10 + BitVec.ofNat 32 (16 * c + 4 * k)) =
        State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c)) + BitVec.ofNat 64 (4 * k) := by
      rw [h1, h10, add_ofNat_ofNat, addr_add (by omega), Offset.add_add]
      congr 2; omega
    refine ⟨e, ?_⟩
    have := in_off (List.mem_append_right s'.rd (h2 ▸ hdat)) hfit
      (off := 16 * (2 * g + c) + 4 * k) (n := 4) (by omega) (by omega)
    rwa [addr_add (by omega), ← Offset.add_add] at this
  have qb := q_blk c hc
  simp only [loadBlock, List.range, List.range.loop, List.map_cons, List.map_nil]
  obtain ⟨a0, i0⟩ := ha s rfl rfl 0 (by omega)
  refine wp_ldr (by omega) a0 i0 fun s₁ u₁ => ?_
  obtain ⟨a1, i1⟩ := ha s₁ (u₁.other _ (qb 0 (by omega)).1.symm) u₁.wr 1 (by omega)
  refine wp_ldr (by omega) a1 i1 fun s₂ u₂ => ?_
  obtain ⟨a2, i2⟩ := ha s₂ (by rw [u₂.other _ (qb 1 (by omega)).1.symm,
    u₁.other _ (qb 0 (by omega)).1.symm]) (by rw [u₂.wr, u₁.wr]) 2 (by omega)
  refine wp_ldr (by omega) a2 i2 fun s₃ u₃ => ?_
  obtain ⟨a3, i3⟩ := ha s₃ (by rw [u₃.other _ (qb 2 (by omega)).1.symm,
    u₂.other _ (qb 1 (by omega)).1.symm, u₁.other _ (qb 0 (by omega)).1.symm])
    (by rw [u₃.wr, u₂.wr, u₁.wr]) 3 (by omega)
  refine wp_ldr (by omega) a3 i3 fun s₄ u₄ => WP.block_nil (h s₄ (fun k hk => ?_) (fun r hr => ?_)
    (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]) (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]))
  · have hne : ∀ j < 4, j ≠ k → q (2 * k + c) ≠ q (2 * j + c) := fun j hj hjk =>
      q_inj c hc k (by omega) j hj (Ne.symm hjk)
    have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [u₄.other _ (hne 3 (by omega) (by omega)), u₃.other _ (hne 2 (by omega) (by omega)),
        u₂.other _ (hne 1 (by omega) (by omega)), u₁.gpr]
    · rw [u₄.other _ (hne 3 (by omega) (by omega)), u₃.other _ (hne 2 (by omega) (by omega)),
        u₂.gpr, u₁.mem]
    · rw [u₄.other _ (hne 3 (by omega) (by omega)), u₃.gpr, u₂.mem, u₁.mem]
    · rw [u₄.gpr, m₃]
  · rw [u₄.other _ (hr 3 (by omega)), u₃.other _ (hr 2 (by omega)), u₂.other _ (hr 1 (by omega)),
      u₁.other _ (hr 0 (by omega))]

/-! ## Storing -/

/-- Word `k` of a group of two blocks: data word `k` from `q (2 (k mod 4) + ⌊k / 4⌋)`. -/
def stw (k : Nat) : List Instr := [.str (q (2 * (k % 4) + k / 4)) .r10 (4 * k)]

theorem storeFull_eq : storeFull = stw 0 ++ stw 1 ++ stw 2 ++ stw 3 ++ stw 4 ++ stw 5 ++ stw 6 ++
    stw 7 ++ ([.dp .add .r10 .r10 (.imm 32), .dp .sub .r11 .r11 (.imm 2)] : List Instr) := rfl

theorem storeTail_eq : storeTail = stw 0 ++ stw 1 ++ stw 2 ++ stw 3 ++
    ([.mov .r11 (.imm 0)] : List Instr) := rfl

/-- After `k` words of the group have been stored, from `s₃`. -/
structure SS (m₀ : Mem) (D : Addr) (n g : Nat) (F : Nat → Spec.Aes.State) (s₃ : State) (k : Nat)
    (s : State) : Prop where
  data : EcbInv m₀ s.mem D n (8 * g + k) F
  frame : Frame [⟨D, 16 * n⟩] s₃.mem s.mem
  gpr : s.gpr = s₃.gpr
  rd : s.rd = s₃.rd
  wr : s.wr = s₃.wr
  sp : s.sp = s₃.sp

/-- Before the stores of group `g`: the results are in the words. -/
structure SPre (m₀ : Mem) (Dp : BitVec 32) (n g : Nat) (F : Nat → Spec.Aes.State) (s₃ : State) :
    Prop where
  hg : 2 * g < n
  fit : Dp.toNat + 16 * n ≤ 2 ^ 32
  dat : (⟨State.addr Dp, 16 * n⟩ : Region) ∈ s₃.wr
  r10 : s₃.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g)
  r11 : s₃.gpr .r11 = BitVec.ofNat 32 (n - 2 * g)
  data : EcbInv m₀ s₃.mem (State.addr Dp) n (8 * g) F
  vals : ∀ k < 8, 8 * g + k < 4 * n → ∀ t < 4,
    (s₃.gpr (q (2 * (k % 4) + k / 4))).extractLsb' (8 * t) 8 =
      (F ((4 * (8 * g + k) + t) / 16)).getD ((4 * (8 * g + k) + t) % 16) 0

section Store

variable {m₀ : Mem} {Dp : BitVec 32} {n g : Nat} {F : Nat → Spec.Aes.State} {s₃ : State}

theorem ss_step (hp : SPre m₀ Dp n g F s₃) {k : Nat} (hk : k < 8) (hkn : 8 * g + k < 4 * n) {s : State}
    (hs : SS m₀ (State.addr Dp) n g F s₃ k s) {is : List Instr} {P : State → Prop}
    (h : ∀ s', SS m₀ (State.addr Dp) n g F s₃ (k + 1) s' → WP isa (.block is) s' P) :
    WP isa (.block (stw k ++ is)) s P := by
  have hn := hp.fit
  have ha : State.addr (s.gpr .r10 + BitVec.ofNat 32 (4 * k)) =
      State.addr Dp + BitVec.ofNat 64 (4 * (8 * g + k)) := by
    rw [hs.gpr, hp.r10, add_ofNat_ofNat, addr_add (by omega)]
    congr 2; omega
  have hin : InRegions s.wr (State.addr Dp + BitVec.ofNat 64 (4 * (8 * g + k))) 4 := by
    have := in_off (hs.wr ▸ hp.dat) hp.fit (off := 4 * (8 * g + k)) (n := 4) (by omega) (by omega)
    rwa [addr_add (by omega)] at this
  simp only [stw, List.cons_append, List.nil_append]
  refine wp_str (by omega) ha hin fun s' u => ?_
  have hst := ecbInv_step (v := s.gpr (q (2 * (k % 4) + k / 4))) (by omega) hkn hs.data
    (fun t ht => by rw [hs.gpr]; exact hp.vals k hk hkn t ht)
  rw [← u.mem] at hst
  exact h s' ⟨by rw [show 8 * g + (k + 1) = 8 * g + k + 1 by omega]; exact hst.1,
    hs.frame.trans hst.2, by rw [u.gpr, hs.gpr], by rw [u.rd, hs.rd], by rw [u.wr, hs.wr],
    by rw [u.sp, hs.sp]⟩

/-- After the stores: `r11` is zero if no data is left. -/
def SDone (m₀ : Mem) (Dp : BitVec 32) (n g : Nat) (F : Nat → Spec.Aes.State) (s₃ s : State) : Prop :=
  Frame [⟨State.addr Dp, 16 * n⟩] s₃.mem s.mem ∧
    (∀ r, r ≠ kp → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₃.gpr r) ∧
    s.rd = s₃.rd ∧ s.wr = s₃.wr ∧ s.sp = s₃.sp ∧
    ((s.gpr .r11 = 0 ∧ EcbInv m₀ s.mem (State.addr Dp) n (4 * n) F) ∨
     (2 * g + 2 < n ∧ EcbInv m₀ s.mem (State.addr Dp) n (8 * (g + 1)) F ∧
      s.gpr .r10 = Dp + BitVec.ofNat 32 (32 * (g + 1)) ∧
      s.gpr .r11 = BitVec.ofNat 32 (n - 2 * (g + 1))))

theorem storePhase_wp (hp : SPre m₀ Dp n g F s₃) :
    WP isa (.block [.mov kp (lsrOp .r11 1), .cmp kp (.imm 0)]) s₃ fun s =>
      WP isa (.ite .ne (.block storeFull) (.block storeTail)) s (SDone m₀ Dp n g F s₃) := by
  have hg := hp.hg
  have hn := hp.fit
  refine wp_mov (op2_lsr (by decide)) fun s₄ u₄ => wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ =>
    WP.block_nil ?_
  have ev₅ : Arm.eval .ne s₅ = some (decide (2 ≤ n - 2 * g)) := by
    rw [Arm.eval, z₅, u₄.gpr, hp.r11, shr1_eq _ (by omega)]
  -- The stores start from `s₅`, which differs from `s₃` only in `kp` and the flags.
  let s₃' := s₅
  have x₀ : SS m₀ (State.addr Dp) n g F s₃' 0 s₅ :=
    ⟨by rw [f₅.mem, u₄.mem]; exact hp.data, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  have g₅ : ∀ r, r ≠ kp → s₅.gpr r = s₃.gpr r := fun r hr => by rw [f₅.gpr, u₄.other r hr]
  have hp' : SPre m₀ Dp n g F s₃' :=
    { hg := hg, fit := hn, dat := by rw [f₅.wr, u₄.wr]; exact hp.dat
      r10 := by rw [g₅ _ (by decide)]; exact hp.r10
      r11 := by rw [g₅ _ (by decide)]; exact hp.r11
      data := x₀.data
      vals := fun k hk hkn t ht => by
        rw [g₅ _ (q_ctr (k / 4) (by omega) (k % 4) (by omega)).2.2]; exact hp.vals k hk hkn t ht }
  have fin : ∀ s : State, Frame [⟨State.addr Dp, 16 * n⟩] s₅.mem s.mem →
      (∀ r, r ≠ kp → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₅.gpr r) →
      s.rd = s₅.rd → s.wr = s₅.wr → s.sp = s₅.sp →
      Frame [⟨State.addr Dp, 16 * n⟩] s₃.mem s.mem ∧
        (∀ r, r ≠ kp → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₃.gpr r) ∧
        s.rd = s₃.rd ∧ s.wr = s₃.wr ∧ s.sp = s₃.sp := fun s f o rd wr sp =>
    ⟨by rw [← u₄.mem, ← f₅.mem]; exact f, fun r h1 h2 h3 => by rw [o r h1 h2 h3, g₅ r h1],
      by rw [rd, f₅.rd, u₄.rd], by rw [wr, f₅.wr, u₄.wr], by rw [sp, f₅.sp, u₄.sp]⟩
  refine WP.ite (decide (2 ≤ n - 2 * g)) ev₅ (fun hb => ?_) (fun hb => ?_)
  · -- Two blocks.
    have h2 : 2 ≤ n - 2 * g := by simpa using hb
    rw [storeFull_eq]
    simp only [List.append_assoc]
    refine ss_step hp' (k := 0) (by omega) (by omega) x₀ fun s₆ x₆ => ?_
    refine ss_step hp' (k := 1) (by omega) (by omega) x₆ fun s₇ x₇ => ?_
    refine ss_step hp' (k := 2) (by omega) (by omega) x₇ fun s₈ x₈ => ?_
    refine ss_step hp' (k := 3) (by omega) (by omega) x₈ fun s₉ x₉ => ?_
    refine ss_step hp' (k := 4) (by omega) (by omega) x₉ fun s₁₀ x₁₀ => ?_
    refine ss_step hp' (k := 5) (by omega) (by omega) x₁₀ fun s₁₁ x₁₁ => ?_
    refine ss_step hp' (k := 6) (by omega) (by omega) x₁₁ fun s₁₂ x₁₂ => ?_
    refine ss_step hp' (k := 7) (by omega) (by omega) x₁₂ fun s₁₃ x₁₃ => ?_
    refine wp_add (op2_imm (by decide)) fun s₁₄ u₁₄ => wp_sub (op2_imm (by decide)) fun s₁₅ u₁₅ =>
      WP.block_nil ?_
    obtain ⟨c1, c2, c3, c4, c5⟩ := fin s₁₅ (by rw [u₁₅.mem, u₁₄.mem]; exact x₁₃.frame)
      (fun r _ h2 h3 => by rw [u₁₅.other _ h3, u₁₄.other _ h2, x₁₃.gpr])
      (by rw [u₁₅.rd, u₁₄.rd, x₁₃.rd]) (by rw [u₁₅.wr, u₁₄.wr, x₁₃.wr]) (by rw [u₁₅.sp, u₁₄.sp, x₁₃.sp])
    refine ⟨c1, c2, c3, c4, c5, ?_⟩
    have e₁₀ : s₁₅.gpr .r10 = Dp + BitVec.ofNat 32 (32 * (g + 1)) := by
      rw [u₁₅.other _ (by decide), u₁₄.gpr, x₁₃.gpr, hp'.r10]
      rw [BitVec.add_assoc, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, ← BitVec.ofNat_add]
      congr 2
    have e₁₁ : s₁₅.gpr .r11 = BitVec.ofNat 32 (n - 2 * (g + 1)) := by
      rw [u₁₅.gpr, u₁₄.other _ (by decide), x₁₃.gpr, hp'.r11]
      bv_omega
    have d : EcbInv m₀ s₁₅.mem (State.addr Dp) n (8 * (g + 1)) F := by
      rw [u₁₅.mem, u₁₄.mem]; exact x₁₃.data
    by_cases hl : n - 2 * g = 2
    · exact .inl ⟨by rw [e₁₁, show n - 2 * (g + 1) = 0 by omega]; rfl,
        ecbInv_mono d (by omega) (by omega)⟩
    · exact .inr ⟨by omega, d, e₁₀, e₁₁⟩
  · -- The last block.
    have h1 : n - 2 * g = 1 := by simp at hb; omega
    rw [storeTail_eq]
    simp only [List.append_assoc]
    refine ss_step hp' (k := 0) (by omega) (by omega) x₀ fun s₆ x₆ => ?_
    refine ss_step hp' (k := 1) (by omega) (by omega) x₆ fun s₇ x₇ => ?_
    refine ss_step hp' (k := 2) (by omega) (by omega) x₇ fun s₈ x₈ => ?_
    refine ss_step hp' (k := 3) (by omega) (by omega) x₈ fun s₉ x₉ => ?_
    refine wp_mov (op2_imm (by decide)) fun s₁₀ u₁₀ => WP.block_nil ?_
    obtain ⟨c1, c2, c3, c4, c5⟩ := fin s₁₀ (by rw [u₁₀.mem]; exact x₉.frame)
      (fun r _ _ h3 => by rw [u₁₀.other _ h3, x₉.gpr]) (by rw [u₁₀.rd, x₉.rd]) (by rw [u₁₀.wr, x₉.wr])
      (by rw [u₁₀.sp, x₉.sp])
    refine ⟨c1, c2, c3, c4, c5, .inl ⟨u₁₀.gpr, ?_⟩⟩
    rw [u₁₀.mem]; exact ecbInv_mono x₉.data (by omega) (by omega)

end Store

/-! ## A group -/

/-- What the group loop runs with: `s₂` is the state after the round keys
are bitsliced, `b` the scratch buffer, `Dp` the data (`n` blocks). -/
structure ESetup (s₂ : State) (b Dp : BitVec 32) (n R : Nat) (w : List Byte) : Prop where
  scr : (⟨State.addr b, 2048⟩ : Region) ∈ s₂.wr
  fit : b.toNat + 2048 ≤ 2 ^ 32
  dat : (⟨State.addr Dp, 16 * n⟩ : Region) ∈ s₂.wr
  fitD : Dp.toNat + 16 * n ≤ 2 ^ 32
  sep : Region.Disjoint ⟨State.addr Dp, 16 * n⟩ ⟨State.addr b, 2048⟩
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  keys : KeysAt s₂.mem (b + BitVec.ofNat 32 (lastKey - 32 * R)) R w

/-- Before group `g`. -/
structure EInv (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (s₂ : State)
    (b Dp : BitVec 32) (n R : Nat) (w : List Byte) (g : Nat) (s : State) : Prop where
  hg : 2 * g < n
  r10 : s.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g)
  r11 : s.gpr .r11 = BitVec.ofNat 32 (n - 2 * g)
  r12 : s.gpr .r12 = b + BitVec.ofNat 32 (lastKey - 32 * R)
  base : s.gpr sb = b
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (gRegions (State.addr b) (State.addr Dp) n) s₂.mem s.mem
  data : EcbInv m₀ s.mem (State.addr Dp) n (8 * g) (ecbOut f m₀ (State.addr Dp) R w)

/-- After the last group. -/
structure EDone (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (s₂ : State)
    (b Dp : BitVec 32) (n R : Nat) (w : List Byte) (s : State) : Prop where
  base : s.gpr sb = b
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (gRegions (State.addr b) (State.addr Dp) n) s₂.mem s.mem
  data : EcbInv m₀ s.mem (State.addr Dp) n (4 * n) (ecbOut f m₀ (State.addr Dp) R w)

/-- The memory after `groupSave`. -/
def saveMem (m : Mem) (B : Addr) (d l f : BitVec 32) : Mem :=
  ((m.writeW (slotA B dSlot) d).writeW (slotA B lSlot) l).writeW (slotA B fkSlot) f

theorem save_frame (m : Mem) (B : Addr) (d l f : BitVec 32) :
    Frame [⟨B + BitVec.ofNat 64 176, 16⟩] m (saveMem m B d l f) := by
  have c : ∀ k, 44 ≤ k → k < 48 →
      (⟨B + BitVec.ofNat 64 176, 16⟩ : Region).Contains (slotA B k) (32 / 8) := by
    intro k h1 h2
    simp only [Region.Contains, slotA]
    rw [show B + BitVec.ofNat 64 (4 * k) - (B + BitVec.ofNat 64 176) = BitVec.ofNat 64 (4 * k - 176) by
      bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  exact (((Frame.refl _ m).writeW (List.mem_singleton_self _) _ (c 45 (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (c 46 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (c 47 (by omega) (by omega))

theorem save_read (m : Mem) (B : Addr) (d l f : BitVec 32) :
    (saveMem m B d l f).readW (slotA B dSlot) 32 = d ∧
      (saveMem m B d l f).readW (slotA B lSlot) 32 = l ∧
      (saveMem m B d l f).readW (slotA B fkSlot) 32 = f := by
  simp only [saveMem]
  refine ⟨?_, ?_, Mem.readW_writeW_self32 _ _ _⟩
  · rw [readW_writeW_slot _ _ (by decide) (by decide) (by decide),
      readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

/-- `groupSave`, and whether two blocks are left. -/
theorem front_wp {s : State} {b : BitVec 32} (hb : s.gpr sb = b)
    (hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr) (hfit : b.toNat + 2048 ≤ 2 ^ 32) {P : State → Prop}
    (h : ∀ s', s'.gpr kp = s.gpr .r12 → (∀ r, r ≠ kp → r ≠ .lr → s'.gpr r = s.gpr r) →
      s'.mem = saveMem s.mem (State.addr b) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Arm.eval .ne s' = some (!(s.gpr .r11 >>> 1 - 0 == 0)) → P s') :
    WP isa (.block (groupSave ++ ([.mov .lr (lsrOp .r11 1), .cmp .lr (.imm 0)] : List Instr))) s P := by
  simp only [groupSave, List.cons_append, List.nil_append]
  refine wp_stS hb hscr hfit (by decide) fun s₁ u₁ => ?_
  refine wp_stS (u₁.gpr ▸ hb) (u₁.wr ▸ hscr) hfit (by decide) fun s₂ u₂ => ?_
  refine wp_stS (u₂.gpr ▸ u₁.gpr ▸ hb) (u₂.wr ▸ u₁.wr ▸ hscr) hfit (by decide) fun s₃ u₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₅ u₅ => wp_cmp (op2_imm (by decide)) fun s₆ f₆ z₆ =>
    WP.block_nil (h s₆ ?_ (fun r h1 h2 => ?_) ?_ ?_ ?_ ?_ ?_)
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [f₆.gpr, u₅.other _ h2, u₄.other _ h1, u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr]; rfl
  · rw [f₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [f₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [Arm.eval, z₆, u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr]

/-- The load phase: the blocks left (two, or the last one), in the words. -/
theorem load_wp {s : State} {Dp : BitVec 32} {n g : Nat} (hg : 2 * g < n)
    (hfit : Dp.toNat + 16 * n ≤ 2 ^ 32) (hdat : (⟨State.addr Dp, 16 * n⟩ : Region) ∈ s.wr)
    (h10 : s.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g))
    (hz : Arm.eval .ne s = some (decide (2 ≤ n - 2 * g))) {P : State → Prop}
    (h : ∀ s', (∀ c < 2, 2 * g + c < n → ∀ k < 4, s'.gpr (q (2 * k + c)) =
        s.mem.readW (State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c)) + BitVec.ofNat 64 (4 * k)) 32) →
      (∀ r, (∀ c < 2, ∀ k < 4, r ≠ q (2 * k + c)) → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa (.ite .ne (.block (loadBlock 0 ++ loadBlock 1)) (.block (loadBlock 0))) s P := by
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · have h2 : 2 ≤ n - 2 * g := by simpa using hb
    rw [WP.block_append_iff (M := isa)]
    refine loadBlock_wp (g := g) (c := 0) (by omega) (by omega) hfit hdat h10
      fun s₁ v₁ o₁ m₁ rd₁ wr₁ sp₁ => ?_
    refine loadBlock_wp (g := g) (c := 1) (by omega) (by omega) hfit (wr₁ ▸ hdat)
      (by rw [o₁ _ fun k hk => (q_blk 0 (by omega) k hk).1.symm]; exact h10)
      fun s₂ v₂ o₂ m₂ rd₂ wr₂ sp₂ => h s₂ (fun c hc _ k hk => ?_) (fun r hr => ?_)
        (by rw [m₂, m₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [sp₂, sp₁])
    · rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
      · rw [o₂ _ fun j hj => q_ne _ (by omega) _ (by omega) (by omega), v₁ k hk]
      · rw [v₂ k hk, m₁]
    · rw [o₂ _ (hr 1 (by omega)), o₁ _ (hr 0 (by omega))]
  · have h1 : n - 2 * g = 1 := by simp at hb; omega
    exact loadBlock_wp (g := g) (c := 0) (by omega) (by omega) hfit hdat h10
      fun s₁ v₁ o₁ m₁ rd₁ wr₁ sp₁ => h s₁ (fun c hc hcn k hk => by
        rcases (show c = 0 by omega) with rfl
        exact v₁ k hk) (fun r hr => o₁ _ (hr 0 (by omega))) m₁ rd₁ wr₁ sp₁

theorem q_keep (r : Reg) (hr : ∀ c < 2, ∀ k < 4, r ≠ q (2 * k + c)) : r ∉ layerWrites ∨ r = .r10 ∨
    r = .r11 ∨ r = .r12 ∨ r = .lr := by
  revert hr; cases r <;> decide

/-- One group: from before group `g`, to after the last group or before
group `g + 1`. -/
theorem group_ok {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt2 f) {m₀ : Mem} {s₂ : State} {b Dp : BitVec 32} {n R : Nat} {w : List Byte}
    (hs : ESetup s₂ b Dp n R w) {g : Nat} {s : State} (hi : EInv f m₀ s₂ b Dp n R w g s) :
    WP isa (blockGroup crypt2) s fun s' => (Arm.eval .ne s' = some false ∧ EDone f m₀ s₂ b Dp n R w s') ∨
      (Arm.eval .ne s' = some true ∧ EInv f m₀ s₂ b Dp n R w (g + 1) s') := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega
  have hfit := hs.fit
  have hfitD := hs.fitD
  have hg := hi.hg
  have hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr := hi.wr ▸ hs.scr
  have hdat : (⟨State.addr Dp, 16 * n⟩ : Region) ∈ s.wr := hi.wr ▸ hs.dat
  let F := ecbOut f m₀ (State.addr Dp) R w
  unfold blockGroup
  refine WP.seq (front_wp hi.base hscr hfit fun s₁ hkp₁ o₁ m₁ rd₁ wr₁ sp₁ z₁ => ?_)
  have hb₁ : s₁.gpr sb = b := (o₁ sb (by decide) (by decide)).trans hi.base
  have f₁ : Frame [⟨State.addr b + BitVec.ofNat 64 176, 16⟩] s.mem s₁.mem := by
    rw [m₁]; exact save_frame _ _ _ _ _
  have hf₁ : Frame (gRegions (State.addr b) (State.addr Dp) n) s₂.mem s₁.mem :=
    hi.frame.trans (f₁.mono fun r hr => by simp at hr; simp [hr])
  have z₁' : Arm.eval .ne s₁ = some (decide (2 ≤ n - 2 * g)) := by
    rw [z₁, hi.r11, shr1_eq _ (by omega)]
  have d₁ : EcbInv m₀ s₁.mem (State.addr Dp) n (8 * g) F :=
    ecbInv_frame f₁ (by simpa using hs.sep.sub_right (scr_sub _ (by omega))) (by omega) hi.data
  refine WP.seq (load_wp hg hfitD (wr₁ ▸ hdat) (by rw [o₁ _ (by decide) (by decide)]; exact hi.r10) z₁'
    fun s₂' v₂ o₂ m₂ rd₂ wr₂ sp₂ => ?_)
  have hkp₂ : s₂'.gpr kp = s.gpr .r12 := by
    rw [o₂ _ fun c hc k hk => (q_blk c hc k hk).2.2.2.2.1.symm, hkp₁]
  have hb₂ : s₂'.gpr sb = b := by
    rw [o₂ _ fun c hc k hk => (q_blk c hc k hk).2.2.2.1.symm, hb₁]
  have hp : EncPre s₂' R w :=
    ⟨by rw [hb₂, wr₂, wr₁, hi.wr]; exact hs.scr, by rw [hb₂]; exact hfit, hs.rounds,
      by rw [hkp₂, hi.r12, hb₂],
      by rw [hkp₂, hi.r12, m₂]; exact keysAt_frame hfit hR hf₁ (keys_disj_regions hs.sep) hs.keys⟩
  have hfk : FirstKey s₂' s₂'.mem := by
    rw [FirstKey, hb₂, hkp₂, m₂, m₁]; exact (save_read _ _ _ _ _).2.2
  -- The loaded blocks.
  have hld : ∀ c < 2, 2 * g + c < n → regBlock (Q s₂') c = Spec.Aes.stateAt m₀
      (State.addr Dp + BitVec.ofNat 64 (16 * (2 * g + c))) := fun c hc hcn => by
    rw [regBlock_load (m := s₁.mem) fun k hk => v₂ c hc hcn k hk]
    exact stateAt_ecbInv d₁ hcn (by omega)
  refine WP.seq (WP.mono (hcr hp hfk (inRel_regBlock (Q s₂'))) fun s₃ ⟨hc₃, hin₃⟩ => ?_)
  have fr₃ := hc₃.frame
  rw [hb₂] at fr₃
  have hb₃ : s₃.gpr sb = b := hc₃.base.trans hb₂
  have hscr₃ : (⟨State.addr b, 2048⟩ : Region) ∈ s₃.wr := by rw [hc₃.wr, wr₂, wr₁]; exact hscr
  have mslot : ∀ k, 45 ≤ k → k < 48 → s₃.mem.readW (slotA (State.addr b) k) 32 =
      s₁.mem.readW (slotA (State.addr b) k) 32 := fun k h1 h2 => by
    rw [← m₂]
    exact fr₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (scr_disj _ (by omega) (by omega)).symm)
      (by decide)
  obtain ⟨rd10, rd11, rd12⟩ := save_read s.mem (State.addr b) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12)
  refine WP.seq ?_
  simp only [groupLoad, List.cons_append, List.nil_append]
  refine wp_ldS hb₃ hscr₃ hfit (by decide) fun s₄ u₄ => ?_
  refine wp_ldS (by rw [u₄.other _ (by decide), hb₃]) (by rw [u₄.wr]; exact hscr₃) hfit (by decide)
    fun s₅ u₅ => ?_
  refine wp_ldS (by rw [u₅.other _ (by decide), u₄.other _ (by decide), hb₃])
    (by rw [u₅.wr, u₄.wr]; exact hscr₃) hfit (by decide) fun s₆ u₆ => ?_
  have e10 : s₆.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, mslot dSlot (by decide) (by decide), m₁,
      rd10, hi.r10]
  have e11 : s₆.gpr .r11 = BitVec.ofNat 32 (n - 2 * g) := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, mslot lSlot (by decide) (by decide), m₁, rd11, hi.r11]
  have e12 : s₆.gpr .r12 = b + BitVec.ofNat 32 (lastKey - 32 * R) := by
    rw [u₆.gpr, u₅.mem, u₄.mem, mslot fkSlot (by decide) (by decide), m₁, rd12, hi.r12]
  have mm₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  have gq₆ : ∀ i < 8, s₆.gpr (q i) = s₃.gpr (q i) := fun i hi' => by
    have : q i ≠ .r10 ∧ q i ≠ .r11 ∧ q i ≠ .r12 := by revert hi'; revert i; decide
    rw [u₆.other _ this.2.2, u₅.other _ this.2.1, u₄.other _ this.1]
  have d128 : Region.Disjoint ⟨State.addr Dp, 16 * n⟩ ⟨State.addr b, 128⟩ :=
    hs.sep.sub_right (Region.sub_prefix (by omega))
  have hx : SPre m₀ Dp n g F s₆ :=
    { hg := hg, fit := hfitD, dat := by rw [u₆.wr, u₅.wr, u₄.wr, hc₃.wr, wr₂, wr₁]; exact hdat
      r10 := e10, r11 := e11
      data := by
        rw [mm₆]
        exact ecbInv_frame fr₃ (by simpa using d128) (by omega) (by rw [m₂]; exact d₁)
      vals := fun k hk hkn t ht => by
        rw [gq₆ _ (by omega)]
        have hcn : 2 * g + k / 4 < n := by omega
        apply byte_ext
        intro j hj
        have := hin₃ (k / 4) (by omega) (4 * (k % 4) + t) (by omega) j hj
        dsimp only at this
        rw [show (4 * (k % 4) + t) / 4 = k % 4 by omega, show (4 * (k % 4) + t) % 4 = t by omega,
          hld _ (by omega) hcn] at this
        rw [BitVec.getLsbD_extractLsb', this, show (4 * (8 * g + k) + t) / 16 = 2 * g + k / 4 by omega,
          show (4 * (8 * g + k) + t) % 16 = 4 * (k % 4) + t by omega]
        simp [hj, F, ecbOut] }
  refine WP.mono (storePhase_wp hx) fun s₇ h₇ => WP.seq (WP.mono h₇ fun s₈ hd₈ => ?_)
  obtain ⟨f₈, o₈, rd₈, wr₈, sp₈, hz⟩ := hd₈
  refine wp_cmp (op2_imm (by decide)) fun s₉ f₉ z₉ => WP.block_nil ?_
  have keep : ∀ r, r ∉ layerWrites → r ≠ kp → s₉.gpr r = s.gpr r := by
    intro r h1 h2
    have : r ≠ .lr ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by revert h1 h2; cases r <;> decide
    have qw : ∀ c < 2, ∀ k < 4, q (2 * k + c) ∈ layerWrites := by decide
    have hq : ∀ c < 2, ∀ k < 4, r ≠ q (2 * k + c) := fun c hc k hk h => h1 (h ▸ qw c hc k hk)
    rw [f₉.gpr, o₈ r h2 this.2.1 this.2.2.1, u₆.other _ this.2.2.2, u₅.other _ this.2.2.1,
      u₄.other _ this.2.1, hc₃.keep r h1 h2, o₂ r hq, o₁ r h2 this.1]
  have base' : s₉.gpr sb = b := (keep sb (by decide) (by decide)).trans hi.base
  have rd' : s₉.rd = s₂.rd := by rw [f₉.rd, rd₈, u₆.rd, u₅.rd, u₄.rd, hc₃.rd, rd₂, rd₁, hi.rd]
  have wr' : s₉.wr = s₂.wr := by rw [f₉.wr, wr₈, u₆.wr, u₅.wr, u₄.wr, hc₃.wr, wr₂, wr₁, hi.wr]
  have sp' : s₉.sp = s₂.sp := by rw [f₉.sp, sp₈, u₆.sp, u₅.sp, u₄.sp, hc₃.sp, sp₂, sp₁, hi.sp]
  have frame' : Frame (gRegions (State.addr b) (State.addr Dp) n) s₂.mem s₉.mem := by
    rw [f₉.mem]
    refine hf₁.trans (?_ : Frame _ s₁.mem s₈.mem)
    rw [← m₂]
    refine (fr₃.mono fun r hr => by simp at hr; simp [hr]).trans ?_
    rw [← mm₆]
    exact f₈.mono fun r hr => by simp at hr; simp [hr]
  have ev : Arm.eval .ne s₉ = some (!(s₈.gpr .r11 == 0)) := by
    have e0 : ∀ x : BitVec 32, x - (0 : BitVec 32) = x := fun x => by bv_omega
    simp only [Arm.eval, z₉, e0]
  rcases hz with ⟨z, d⟩ | ⟨h4, d, x10, x11⟩
  · exact .inl ⟨by rw [ev, z]; rfl, base', rd', wr', sp', frame', by rw [f₉.mem]; exact d⟩
  · refine .inr ⟨?_, ⟨by omega, by rw [f₉.gpr]; exact x10, by rw [f₉.gpr]; exact x11,
      by rw [f₉.gpr, o₈ _ (by decide) (by decide) (by decide), e12], base', rd', wr', sp',
      frame', by rw [f₉.mem]; exact d⟩⟩
    have hne : BitVec.ofNat 32 (n - 2 * (g + 1)) ≠ 0 := by
      intro h; have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simp at this; omega
    rw [ev, x11]; simpa using hne

/-- The loop over the groups. -/
theorem groups_ok {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt2 f) {m₀ : Mem} {s₂ : State} {b Dp : BitVec 32} {n R : Nat} {w : List Byte}
    (hs : ESetup s₂ b Dp n R w) {s : State} (hi : EInv f m₀ s₂ b Dp n R w 0 s) :
    WP isa (.loop (blockGroup crypt2) .ne) s (EDone f m₀ s₂ b Dp n R w) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 2 * g ∧ EInv f m₀ s₂ b Dp n R w g s)
    (fun k s ⟨g, hk, hg⟩ => WP.mono (group_ok hcr hs hg) fun s' h => ?_) n s ⟨0, by omega, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, n - 2 * (g + 1), by have := hg.hg; omega, g + 1, rfl, d⟩

end VG.Proof.Aes.Arm.Ecb
