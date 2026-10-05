import VerifiedGarbage.Impl.Rc4.X86_64
import VerifiedGarbage.Proof.Rc4.Update
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc4.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.X86_64.Lookup`. -/
section

/-! # RC4 on x86-64: the table lookup, a quadword at a time -/

namespace VG.Proof.Rc4.X86_64
open VG VG.X86_64 VG.Impl.Rc4.X86_64 VG.Proof.Rc4
open VG.Proof.MlKem.X86_64 (Keep WP.keep sx_ofNat)

theorem eaAt (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_]
  congr 1

theorem eaIdx (s : State) (b i : Reg) : s.ea (atIdx b i) = s.gpr b + s.gpr i := by
  simp only [State.ea, atIdx]
  rw [show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.mul_one, show BitVec.ofInt 64 0 = 0#64 from rfl,
    BitVec.add_zero]

theorem sx (n : Nat) (h : n < 2 ^ 31 := by decide) :
    (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := sx_ofNat h

theorem byte_addr (b : Byte) : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- Steps a block of the RC4 code, from a state whose accesses the hypotheses permit. -/
syntax "rrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rrun) => `(tactic| rrun [])
  | `(tactic| rrun [$ls,*]) => `(tactic| (
      try unfold imm at *
      xrun [eaAt, eaIdx, sx 0, sx 1, sx 7, sx 8, sx 255, sx 256, List.cons_append,
        List.nil_append, $ls,*]))

/-! ## Visiting the quadwords -/

/-- The quadword holding byte `n`, once quadwords `0, …, k - 1` are visited. -/
def gather (m : Mem) (p : Addr) (n k : Nat) : BitVec 64 :=
  if n / 8 < k then m.readW (p + BitVec.ofNat 64 (8 * (n / 8))) 64 else 0

theorem gather_succ (m : Mem) (p : Addr) (n k : Nat) :
    VG.Proof.Rc4.X86_64.gather m p n k ||| (if n / 8 = k then m.readW (p + BitVec.ofNat 64 (8 * k)) 64 else 0) =
      VG.Proof.Rc4.X86_64.gather m p n (k + 1) := by
  unfold VG.Proof.Rc4.X86_64.gather
  by_cases h0 : n / 8 < k
  · simp [h0, show ¬ n / 8 = k by omega, show n / 8 < k + 1 by omega]
  · by_cases h1 : n / 8 = k
    · subst h1; simp
    · simp [h0, h1, show ¬ n / 8 < k + 1 by omega]

/-- The mask `rowMask` leaves. -/
theorem row_mask (idx : Byte) {k : Nat} (hk : k < 32) (y : BitVec 64) :
    (0#64 - (BitVec.ofBool (decide ((idx.setWidth 64 ^^^ BitVec.ofNat 64 (8 * k)).toNat <
      (BitVec.ofNat 64 8).toNat))).setWidth 64) &&& y = if idx.toNat / 8 = k then y else 0 := by
  rw [borrow_mask, show (BitVec.ofNat 64 8).toNat = 8 from rfl]
  by_cases h : idx.toNat / 8 = k
  · rw [decide_eq_true ((row_hit idx hk).mpr h), ite_eq_left rfl, BitVec.allOnes_and, ite_eq_left h]
  · rw [decide_eq_false (fun h' => h ((row_hit idx hk).mp h')), ite_eq_right (by decide), ite_eq_right h]
    exact BitVec.zero_and

/-- The mask `laneMask` leaves. -/
theorem lane_mask (idx : Byte) {j : Nat} (hj : j < 8) (y : BitVec 64) :
    (0#64 - (BitVec.ofBool (decide (((idx.setWidth 64 &&& BitVec.ofNat 64 7) ^^^
      BitVec.ofNat 64 j).toNat < (BitVec.ofNat 64 1).toNat))).setWidth 64) &&& y =
      if idx.toNat % 8 = j then y else 0 := by
  rw [borrow_mask, show (BitVec.ofNat 64 1).toNat = 1 from rfl]
  by_cases h : idx.toNat % 8 = j
  · rw [decide_eq_true ((lane_hit idx hj).mpr h), ite_eq_left rfl, BitVec.allOnes_and, ite_eq_left h]
  · rw [decide_eq_false (fun h' => h ((lane_hit idx hj).mp h')), ite_eq_right (by decide), ite_eq_right h]
    exact BitVec.zero_and

theorem gather_step (s : State) (idx : Byte) {k : Nat} (hk : k < 32)
    (h9 : s.gpr .r9 = idx.setWidth 64)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block (gatherStep k)) s fun t =>
      t.gpr .r11 = s.gpr .r11 |||
        (if idx.toNat / 8 = k then s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (8 * k)) 64 else 0) ∧
      t.gpr .r9 = s.gpr .r9 ∧ t.gpr .rdi = s.gpr .rdi ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  unfold gatherStep rowMask
  rrun [h9, hr, VG.Proof.Rc4.X86_64.sx (8 * k) (by omega)]
  rw [VG.Proof.Rc4.X86_64.row_mask idx hk]

def GInv (s₀ : State) (idx : Byte) (k : Nat) (t : State) : Prop :=
  t.gpr .r11 = VG.Proof.Rc4.X86_64.gather s₀.mem (s₀.gpr .rdi) idx.toNat k ∧ t.gpr .r9 = s₀.gpr .r9 ∧
    t.gpr .rdi = s₀.gpr .rdi ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr

theorem flatMap_succ {α : Type} (f : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem gather_steps (s₀ : State) (idx : Byte) (h9 : s₀.gpr .r9 = idx.setWidth 64)
    (hr : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi) 256) :
    ∀ n ≤ 32, ∀ s, VG.Proof.Rc4.X86_64.GInv s₀ idx 0 s →
      WP isa (.block ((List.range n).flatMap gatherStep)) s (VG.Proof.Rc4.X86_64.GInv s₀ idx n) := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [VG.Proof.Rc4.X86_64.flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun t ht => ?_
    obtain ⟨h11, h9', hdi, hm, hrd, hwr⟩ := ht
    have hq : InRegions (t.rd ++ t.wr) (t.gpr .rdi + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [hrd, hwr, hdi]
      exact region_offset _ _ _ _ _ (by omega) (by omega) hr
    refine WP.mono (VG.Proof.Rc4.X86_64.gather_step t idx (by omega) (h9'.trans h9) hq) fun u hu => ?_
    obtain ⟨u11, u9, udi, um, urd, uwr⟩ := hu
    refine ⟨?_, u9.trans h9', udi.trans hdi, um.trans hm, urd.trans hrd, uwr.trans hwr⟩
    rw [u11, h11, hdi, hm, VG.Proof.Rc4.X86_64.gather_succ]

/-! ## Picking the byte of the quadword -/

/-- The quadword shifted to byte `L`, once bytes `0, …, j - 1` are visited. -/
def pick (q : BitVec 64) (L j : Nat) : BitVec 64 := if L < j then q >>> (8 * L) else 0

theorem pick_succ (q : BitVec 64) (L j : Nat) :
    VG.Proof.Rc4.X86_64.pick q L j ||| (if L = j then q >>> (8 * j) else 0) = VG.Proof.Rc4.X86_64.pick q L (j + 1) := by
  unfold VG.Proof.Rc4.X86_64.pick
  by_cases h0 : L < j
  · simp [h0, show ¬ L = j by omega, show L < j + 1 by omega]
  · by_cases h1 : L = j
    · subst h1; simp
    · simp [h0, h1, show ¬ L < j + 1 by omega]

theorem pick_step (s : State) (idx : Byte) {j : Nat} (hj : j < 8)
    (h9 : s.gpr .r9 = idx.setWidth 64) :
    WP isa (.block (pickStep j)) s fun t =>
      t.gpr .rax = s.gpr .rax ||| (if idx.toNat % 8 = j then s.gpr .r11 else 0) ∧
      t.gpr .r11 = s.gpr .r11 >>> 8 ∧
      t.gpr .r9 = s.gpr .r9 ∧ t.gpr .rdi = s.gpr .rdi ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  unfold pickStep laneMask
  rrun [h9, VG.Proof.Rc4.X86_64.sx j (by omega)]
  rw [VG.Proof.Rc4.X86_64.lane_mask idx hj]

def PInv (s₀ : State) (q : BitVec 64) (L j : Nat) (t : State) : Prop :=
  t.gpr .rax = VG.Proof.Rc4.X86_64.pick q L j ∧ t.gpr .r11 = q >>> (8 * j) ∧ t.gpr .r9 = s₀.gpr .r9 ∧
    t.gpr .rdi = s₀.gpr .rdi ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr

theorem pick_steps (s₀ : State) (idx : Byte) (q : BitVec 64) (h9 : s₀.gpr .r9 = idx.setWidth 64) :
    ∀ n ≤ 8, ∀ s, VG.Proof.Rc4.X86_64.PInv s₀ q (idx.toNat % 8) 0 s →
      WP isa (.block ((List.range n).flatMap pickStep)) s (VG.Proof.Rc4.X86_64.PInv s₀ q (idx.toNat % 8) n) := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [VG.Proof.Rc4.X86_64.flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun t ht => ?_
    obtain ⟨hax, h11, h9', hdi, hm, hrd, hwr⟩ := ht
    refine WP.mono (VG.Proof.Rc4.X86_64.pick_step t idx (by omega) (h9'.trans h9)) fun u hu => ?_
    obtain ⟨uax, u11, u9, udi, um, urd, uwr⟩ := hu
    refine ⟨?_, ?_, u9.trans h9', udi.trans hdi, um.trans hm, urd.trans hrd, uwr.trans hwr⟩
    · rw [uax, hax, h11, VG.Proof.Rc4.X86_64.pick_succ]
    · rw [u11, h11, shr_byte]

/-! ## The lookup -/

theorem lookup_core (s : State) (idx : Byte) (h9 : s.gpr .r9 = idx.setWidth 64)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 256) :
    WP isa (.block lookup) s fun t =>
      t.gpr .rax = (s.mem (s.gpr .rdi + BitVec.ofNat 64 idx.toNat)).setWidth 64 ∧
      t.mem = s.mem := by
  have hn := idx.isLt
  simp only [lookup, List.append_assoc]
  rw [WP.block_append_iff]
  have h0 : WP isa (.block [.mov .r11 (imm 0)]) s (VG.Proof.Rc4.X86_64.GInv s idx 0) := by
    rrun [VG.Proof.Rc4.X86_64.GInv, VG.Proof.Rc4.X86_64.gather, Nat.not_lt_zero]
  refine WP.mono h0 fun t ht => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.X86_64.gather_steps s idx h9 hr 32 (by decide) t ht) fun u hu => ?_
  obtain ⟨u11, u9, udi, um, urd, uwr⟩ := hu
  let q := s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (8 * (idx.toNat / 8))) 64
  have hq : u.gpr .r11 = q := by
    rw [u11]; unfold VG.Proof.Rc4.X86_64.gather; rw [ite_eq_left (by omega)]
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.mov .rax (imm 0)]) u (VG.Proof.Rc4.X86_64.PInv s q (idx.toNat % 8) 0) := by
    rrun [VG.Proof.Rc4.X86_64.PInv, VG.Proof.Rc4.X86_64.pick, hq, u9, udi, um, urd, uwr, Nat.mul_zero, BitVec.ushiftRight_zero,
      Nat.not_lt_zero]
  refine WP.mono h1 fun v hv => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.X86_64.pick_steps s idx q h9 8 (by decide) v hv) fun w hw => ?_
  obtain ⟨wax, _, _, _, wm, _, _⟩ := hw
  have hL : idx.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  rrun [wax, wm]
  unfold VG.Proof.Rc4.X86_64.pick
  rw [ite_eq_left hL, qword_byte _ _ hL, row_lane]

end VG.Proof.Rc4.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.X86_64.Replace`. -/
section

/-! # RC4 on x86-64: replacing a secret-indexed byte of the table -/

namespace VG.Proof.Rc4.X86_64
open VG VG.X86_64 VG.Impl.Rc4.X86_64 VG.Proof.Rc4
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)

/-! ## Moving the difference to the byte's lane -/

/-- The difference `c`, once lanes `7, …, jj` are visited: shifted to lane `L`
by the lanes visited below it. -/
def spread (c : Byte) (L jj : Nat) : BitVec 64 :=
  if jj ≤ L then (c.setWidth 64) <<< (8 * (L - jj)) else 0

theorem zero_xor' (x : BitVec 64) : (0 : BitVec 64) ^^^ x = x := BitVec.zero_xor
theorem or_zero' (x : BitVec 64) : x ||| (0 : BitVec 64) = x := BitVec.or_zero
theorem zero_or' (x : BitVec 64) : (0 : BitVec 64) ||| x = x := BitVec.zero_or
theorem rot_zero : (0 : BitVec 64).rotateRight 56 = 0 := by decide

theorem spread_succ (c : Byte) {L j : Nat} (hL : L < 8) :
    (VG.Proof.Rc4.X86_64.spread c L (j + 1)).rotateRight 56 ||| (if L = j then c.setWidth 64 else 0) =
      VG.Proof.Rc4.X86_64.spread c L j := by
  unfold VG.Proof.Rc4.X86_64.spread
  by_cases h1 : j + 1 ≤ L
  · rw [ite_eq_left h1, rot_byte c (by omega), ite_eq_right (show ¬ L = j by omega),
      VG.Proof.Rc4.X86_64.or_zero', ite_eq_left (show j ≤ L by omega), show L - (j + 1) + 1 = L - j by omega]
  · rw [ite_eq_right h1, VG.Proof.Rc4.X86_64.rot_zero, VG.Proof.Rc4.X86_64.zero_or']
    by_cases h2 : L = j
    · rw [ite_eq_left h2, ite_eq_left (show j ≤ L by omega), h2, Nat.sub_self, Nat.mul_zero,
        BitVec.shiftLeft_zero]
    · rw [ite_eq_right h2, ite_eq_right (show ¬ j ≤ L by omega)]

theorem spread_step (s : State) (idx c : Byte) {j : Nat} (hj : j < 8)
    (h9 : s.gpr .r9 = idx.setWidth 64) (hax : s.gpr .rax = c.setWidth 64)
    (h11 : s.gpr .r11 = VG.Proof.Rc4.X86_64.spread c (idx.toNat % 8) (j + 1)) :
    WP isa (.block (spreadStep j)) s fun t =>
      t.gpr .r11 = VG.Proof.Rc4.X86_64.spread c (idx.toNat % 8) j ∧ t.gpr .rax = s.gpr .rax ∧
      t.gpr .r9 = s.gpr .r9 ∧ t.mem = s.mem := by
  unfold spreadStep laneMask
  rrun [h9, hax, h11, VG.Proof.Rc4.X86_64.sx j (by omega), VG.Proof.Rc4.X86_64.sx 56]
  rw [VG.Proof.Rc4.X86_64.lane_mask idx hj, VG.Proof.Rc4.X86_64.spread_succ c (Nat.mod_lt _ (by decide))]

theorem spread_steps (s₀ : State) (idx c : Byte) (h9 : s₀.gpr .r9 = idx.setWidth 64)
    (hax : s₀.gpr .rax = c.setWidth 64) :
    ∀ n ≤ 8, ∀ s, s.gpr .r11 = VG.Proof.Rc4.X86_64.spread c (idx.toNat % 8) n → s.gpr .rax = s₀.gpr .rax →
      s.gpr .r9 = s₀.gpr .r9 → s.mem = s₀.mem →
      WP isa (.block ((List.range n).reverse.flatMap spreadStep)) s fun t =>
        t.gpr .r11 = VG.Proof.Rc4.X86_64.spread c (idx.toNat % 8) 0 ∧ t.gpr .rax = s₀.gpr .rax ∧ t.mem = s₀.mem := by
  intro n hn
  induction n with
  | zero => intro s h11 hax' _ hm; exact WP.block_nil ⟨h11, hax', hm⟩
  | succ n ih =>
    intro s h11 hax' h9' hm
    rw [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (VG.Proof.Rc4.X86_64.spread_step s idx c (by omega) (h9'.trans h9) (hax'.trans hax) h11)
      fun t ⟨t11, tax, t9, tm⟩ => ?_
    exact ih (by omega) t t11 (tax.trans hax') (t9.trans h9') (tm.trans hm)

theorem lanesDown_eq : lanesDown = (List.range 8).reverse := rfl

/-! ## Storing back every quadword -/

/-- The memory once quadwords `0, …, k - 1` are stored back, XORed with `d`
where they hold byte `n`. -/
def scatter (m : Mem) (p : Addr) (n : Nat) (d : BitVec 64) (k : Nat) : Mem :=
  if n / 8 < k then
    m.writeW (p + BitVec.ofNat 64 (8 * (n / 8)))
      (m.readW (p + BitVec.ofNat 64 (8 * (n / 8))) 64 ^^^ d)
  else m

theorem scatter_succ (m : Mem) (p : Addr) (n : Nat) (d : BitVec 64) (k : Nat) :
    (VG.Proof.Rc4.X86_64.scatter m p n d k).writeW (p + BitVec.ofNat 64 (8 * k))
      ((if n / 8 = k then d else 0) ^^^
        (VG.Proof.Rc4.X86_64.scatter m p n d k).readW (p + BitVec.ofNat 64 (8 * k)) 64) = VG.Proof.Rc4.X86_64.scatter m p n d (k + 1) := by
  unfold VG.Proof.Rc4.X86_64.scatter
  by_cases h0 : n / 8 < k
  · rw [ite_eq_left h0, ite_eq_right (show ¬ n / 8 = k by omega), VG.Proof.Rc4.X86_64.zero_xor', writeW_readW,
      ite_eq_left (show n / 8 < k + 1 by omega)]
  · rw [ite_eq_right h0]
    by_cases h1 : n / 8 = k
    · rw [ite_eq_left h1, ite_eq_left (show n / 8 < k + 1 by omega), BitVec.xor_comm, h1]
    · rw [ite_eq_right h1, VG.Proof.Rc4.X86_64.zero_xor', writeW_readW,
        ite_eq_right (show ¬ n / 8 < k + 1 by omega)]

theorem scatter_step (s : State) (idx : Byte) {k : Nat} (hk : k < 32)
    (h9 : s.gpr .r9 = idx.setWidth 64)
    (hw : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block (scatterStep k)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .rdi + BitVec.ofNat 64 (8 * k))
        ((if idx.toNat / 8 = k then s.gpr .r11 else 0) ^^^
          s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (8 * k)) 64) ∧
      t.gpr .r11 = s.gpr .r11 ∧ t.gpr .r9 = s.gpr .r9 ∧ t.gpr .rdi = s.gpr .rdi ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (8 * k)) 8 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  unfold scatterStep rowMask
  rrun [h9, hr, hw, VG.Proof.Rc4.X86_64.sx (8 * k) (by omega)]
  rw [VG.Proof.Rc4.X86_64.row_mask idx hk]

theorem scatter_steps (s₀ : State) (idx : Byte) (d : BitVec 64)
    (h9 : s₀.gpr .r9 = idx.setWidth 64) (hw : InRegions s₀.wr (s₀.gpr .rdi) 256) :
    ∀ n ≤ 32, ∀ s, s.gpr .r11 = d → s.gpr .r9 = s₀.gpr .r9 → s.gpr .rdi = s₀.gpr .rdi →
      s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (.block ((List.range n).flatMap scatterStep)) s fun t =>
        t.mem = VG.Proof.Rc4.X86_64.scatter s₀.mem (s₀.gpr .rdi) idx.toNat d n ∧ t.gpr .r11 = d ∧
        t.gpr .r9 = s₀.gpr .r9 ∧ t.gpr .rdi = s₀.gpr .rdi ∧ t.wr = s₀.wr := by
  intro n hn
  induction n with
  | zero =>
    intro s h11 h9' hdi hwr hm
    refine WP.block_nil ⟨?_, h11, h9', hdi, hwr⟩
    rw [hm]; unfold VG.Proof.Rc4.X86_64.scatter; rw [ite_eq_right (Nat.not_lt_zero _)]
  | succ n ih =>
    intro s h11 h9' hdi hwr hm
    rw [VG.Proof.Rc4.X86_64.flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h11 h9' hdi hwr hm) fun t ⟨tm, t11, t9, tdi, twr⟩ => ?_
    have hq : InRegions t.wr (t.gpr .rdi + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [twr, tdi]
      exact region_offset _ _ _ _ _ (by omega) (by omega) hw
    refine WP.mono (VG.Proof.Rc4.X86_64.scatter_step t idx (by omega) (t9.trans h9) hq)
      fun u ⟨um, u11, u9, udi, _, uwr⟩ => ?_
    refine ⟨?_, u11.trans t11, u9.trans t9, udi.trans tdi, uwr.trans twr⟩
    rw [um, tm, t11, tdi, VG.Proof.Rc4.X86_64.scatter_succ]

/-! ## The replacement -/

theorem xor_byte (a b : Byte) : a.setWidth 64 ^^^ b.setWidth 64 = (a ^^^ b).setWidth 64 := by
  rw [BitVec.setWidth_xor]

theorem replace_core (s : State) (idx ii : Byte) (h9 : s.gpr .r9 = idx.setWidth 64)
    (hcx : s.gpr .rcx = ii.setWidth 64) (hw : InRegions s.wr (s.gpr .rdi) 256) :
    WP isa (.block replace) s fun t =>
      t.gpr .rax = (s.mem (s.gpr .rdi + BitVec.ofNat 64 idx.toNat)).setWidth 64 ∧
      t.mem = s.mem.write (s.gpr .rdi + BitVec.ofNat 64 idx.toNat) 1
        (s.mem (s.gpr .rdi + BitVec.ofNat 64 ii.toNat)) := by
  have hn := idx.isLt
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 256 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 ii.toNat) 1 :=
    region_offset _ _ _ _ _ (by have := ii.isLt; omega) (by have := ii.isLt; omega) hr
  let p := s.gpr .rdi
  let b := s.mem (p + BitVec.ofNat 64 idx.toNat)
  let v := s.mem (p + BitVec.ofNat 64 ii.toNat)
  simp only [replace, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .r10, .r11] (VG.Proof.Rc4.X86_64.lookup_core s idx h9 hr) (by decide +kernel))
    fun t ⟨⟨tax, tm⟩, tk⟩ => ?_
  have t9 : t.gpr .r9 = s.gpr .r9 := tk.gpr (by decide)
  have tdi : t.gpr .rdi = s.gpr .rdi := tk.gpr (by decide)
  have tcx : t.gpr .rcx = s.gpr .rcx := tk.gpr (by decide)
  have hit : InRegions (s.rd ++ s.wr) (s.gpr .rdi + s.gpr .rcx) 1 := by
    rw [hcx, VG.Proof.Rc4.X86_64.byte_addr]; exact hi
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.movzx8 .r11 (atIdx .rdi .rcx), .alu .xor .rax (.reg .r11),
      .mov .r11 (imm 0)]) t fun u =>
      u.gpr .rax = (b ^^^ v).setWidth 64 ∧ u.gpr .r11 = 0 ∧ u.gpr .r9 = s.gpr .r9 ∧
        u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rcx = s.gpr .rcx ∧ u.mem = s.mem ∧ u.rd = s.rd ∧
        u.wr = s.wr := by
    rrun [hit, tax, tm, t9, tdi, tcx, tk.2.1, tk.2.2]
    rw [hcx, VG.Proof.Rc4.X86_64.byte_addr ii, VG.Proof.Rc4.X86_64.xor_byte]
  refine WP.mono h1 fun u ⟨uax, u11, u9, udi, ucx, um, urd, uwr⟩ => ?_
  rw [WP.block_append_iff]
  have hsp := VG.Proof.Rc4.X86_64.spread_steps u idx (b ^^^ v) (u9.trans h9) uax 8 (by decide) u
    (by rw [u11]; unfold VG.Proof.Rc4.X86_64.spread; rw [ite_eq_right (by omega)]) rfl rfl rfl
  rw [← VG.Proof.Rc4.X86_64.lanesDown_eq] at hsp
  refine WP.mono (WP.keep [.r10, .r11] hsp (by decide +kernel)) fun w ⟨⟨w11, wax, wm⟩, wk⟩ => ?_
  have w9 : w.gpr .r9 = s.gpr .r9 := (wk.gpr (by decide)).trans u9
  have wdi : w.gpr .rdi = s.gpr .rdi := (wk.gpr (by decide)).trans udi
  have wcx : w.gpr .rcx = s.gpr .rcx := (wk.gpr (by decide)).trans ucx
  have wrd : w.rd = s.rd := wk.2.1.trans urd
  have wwr : w.wr = s.wr := wk.2.2.trans uwr
  have hiw : InRegions (s.rd ++ s.wr) (s.gpr .rdi + s.gpr .rcx) 1 := by
    rw [hcx, VG.Proof.Rc4.X86_64.byte_addr]; exact hi
  rw [WP.block_append_iff]
  have h2 : WP isa (.block [.movzx8 .r10 (atIdx .rdi .rcx), .alu .xor .rax (.reg .r10)]) w
      fun x => x.gpr .rax = b.setWidth 64 ∧ x.gpr .r11 = w.gpr .r11 ∧ x.gpr .r9 = s.gpr .r9 ∧
        x.gpr .rdi = s.gpr .rdi ∧ x.mem = s.mem ∧ x.wr = s.wr := by
    rrun [hiw, wax, uax, wm, um, w9, wdi, wcx, wwr, wrd]
    rw [hcx, VG.Proof.Rc4.X86_64.byte_addr ii, VG.Proof.Rc4.X86_64.xor_byte, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  refine WP.mono h2 fun x ⟨xax, x11, x9, xdi, xm, xwr⟩ => ?_
  refine WP.mono (WP.keep [.r10] (VG.Proof.Rc4.X86_64.scatter_steps s idx _ h9 hw 32 (by decide) x rfl x9 xdi xwr xm)
    (by decide +kernel)) fun y ⟨⟨ym, _⟩, yk⟩ => ?_
  refine ⟨(yk.gpr (by decide)).trans xax, ?_⟩
  rw [ym, x11, w11]
  unfold VG.Proof.Rc4.X86_64.scatter VG.Proof.Rc4.X86_64.spread
  rw [ite_eq_left (by omega), ite_eq_left (Nat.zero_le _), Nat.sub_zero, writeW_byte,
    ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end VG.Proof.Rc4.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.X86_64.Schedule`. -/
section

/-! # RC4 on x86-64: key scheduling -/

namespace VG.Proof.Rc4.X86_64
open VG VG.X86_64 VG.Impl.Rc4.X86_64 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)

theorem writeW_byte8 (m : Mem) (a : Addr) (v : Byte) : m.writeW a v = m.write a 1 v := by
  change m.write a 1 (v.setWidth 8) = _
  rw [BitVec.setWidth_eq]

theorem low_byte (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem ofNat_low (r : Nat) : (BitVec.ofNat 64 r).setWidth 8 = BitVec.ofNat 8 r := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem mask255 (x : BitVec 64) : x &&& BitVec.ofNat 64 255 = (x.setWidth 8).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (255 % 2 ^ 64 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem byte_add (a b : Byte) :
    a.setWidth 64 + b.setWidth 64 &&& BitVec.ofNat 64 255 = (a + b).setWidth 64 := by
  rw [VG.Proof.Rc4.X86_64.mask255]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega

theorem byte_add3 (j a k : Byte) :
    j.setWidth 64 + a.setWidth 64 + k.setWidth 64 &&& BitVec.ofNat 64 255 =
      (j + a + k).setWidth 64 := by
  rw [VG.Proof.Rc4.X86_64.mask255]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega

/-! ## The identity permutation -/

def IdentityInv (s₀ : State) (r : Nat) (s : State) : Prop :=
  s.mem = identityMem s₀.mem (s₀.gpr .rdi) r ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
    s.gpr .rdi = s₀.gpr .rdi ∧ s.gpr .rsi = s₀.gpr .rsi ∧ s.gpr .rdx = s₀.gpr .rdx ∧
    s.gpr .rcx = BitVec.ofNat 64 r

theorem identity_step (s₀ s : State) {r : Nat} (hr : r < 256)
    (hp : InRegions s₀.wr (s₀.gpr .rdi) 256) (h : VG.Proof.Rc4.X86_64.IdentityInv s₀ r s) :
    WP isa (.block identityStep) s fun t => VG.Proof.Rc4.X86_64.IdentityInv s₀ (r + 1) t ∧
      t.zf = some (BitVec.ofNat 64 (r + 1) - BitVec.ofNat 64 256 == 0#64) := by
  obtain ⟨hm, hrd, hwr, hdi, hsi, hdx, hcx⟩ := h
  have hw : InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofNat 64 r) 1 :=
    region_offset _ _ _ _ _ (by omega) (by omega) hp
  have hadd : BitVec.ofNat 64 r + BitVec.ofNat 64 1 = BitVec.ofNat 64 (r + 1) := by
    rw [← BitVec.ofNat_add]
  unfold identityStep
  rrun [hw, hm, hrd, hwr, hdi, hsi, hdx, hcx, hadd, VG.Proof.Rc4.X86_64.writeW_byte8, VG.Proof.Rc4.X86_64.ofNat_low, VG.Proof.Rc4.X86_64.IdentityInv]
  exact ⟨identityMem_store _ _ _ hr, rfl⟩

theorem identity_loop (s₀ s : State) {r : Nat} (hr : r < 256)
    (hp : InRegions s₀.wr (s₀.gpr .rdi) 256) (h : VG.Proof.Rc4.X86_64.IdentityInv s₀ r s) :
    WP isa (.loop (.block identityStep) .ne) s (VG.Proof.Rc4.X86_64.IdentityInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ VG.Proof.Rc4.X86_64.IdentityInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (VG.Proof.Rc4.X86_64.identity_step s₀ t hj hp ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    simp only [eval, hz, hend, Option.map_some]
    rfl
  · right
    have hnz : BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 256 ≠ 0#64 := by bv_omega
    refine ⟨?_, 256 - (j + 1), by omega, j + 1, by omega, rfl, hu⟩
    simp only [eval, hz, Option.map_some, beq_eq_false_iff_ne.mpr hnz, Bool.not_false]

/-! ## One round -/

theorem schedule_before (s : State) (i j : Byte)
    (hcx : s.gpr .rcx = i.setWidth 64) (h9 : s.gpr .r9 = j.setWidth 64)
    (hp : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 256)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .rsi + s.gpr .r8) 1) :
    WP isa (.block [.movzx8 .r10 (atIdx .rdi .rcx), .alu .add .r9 (.reg .r10),
      .movzx8 .r10 (atIdx .rsi .r8), .alu .add .r9 (.reg .r10), .alu .and .r9 (imm 255)]) s
      fun t => t.gpr .r9 = (j + s.mem (s.gpr .rdi + BitVec.ofNat 64 i.toNat) +
          s.mem (s.gpr .rsi + s.gpr .r8)).setWidth 64 ∧ Keep [.r9, .r10] s t ∧ t.mem = s.mem := by
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .rdi + i.setWidth 64) 1 := by
    rw [VG.Proof.Rc4.X86_64.byte_addr i]
    exact region_offset _ _ _ _ _ (by have := i.isLt; omega) (by have := i.isLt; omega) hp
  refine WP.mono (WP.keep (Q := fun t => t.gpr .r9 = (j + s.mem (s.gpr .rdi + BitVec.ofNat 64 i.toNat) +
      s.mem (s.gpr .rsi + s.gpr .r8)).setWidth 64 ∧ t.mem = s.mem) [.r9, .r10] ?_ (by decide +kernel))
    fun t ⟨h, hk⟩ => ⟨h.1, hk, h.2⟩
  rrun [hi, hk, h9, hcx]
  rw [VG.Proof.Rc4.X86_64.byte_addr i, VG.Proof.Rc4.X86_64.byte_add3]

theorem and_mask (x : BitVec 64) (p : Bool) :
    x &&& (0#64 - (BitVec.ofBool p).setWidth 64) = if p then x else 0 := by
  rw [borrow_mask]
  cases p
  · exact BitVec.and_zero
  · exact BitVec.and_allOnes

theorem schedule_after (s : State) (i b : Byte)
    (hcx : s.gpr .rcx = i.setWidth 64) (hax : s.gpr .rax = b.setWidth 64)
    (hw : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 i.toNat) 1) :
    WP isa (.block [.store8 (atIdx .rdi .rcx) .rax,
      .alu .add .r8 (imm 1), .mov .r10 (imm 0), .alu .cmp .r8 (.reg .rdx),
      .alu .sbb .r10 (.reg .r10),
      .alu .and .r8 (.reg .r10),
      .alu .add .rcx (imm 1), .alu .cmp .rcx (imm 256)]) s fun t =>
      t.mem = s.mem.write (s.gpr .rdi + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r8 = (if (s.gpr .r8 + 1#64).toNat < (s.gpr .rdx).toNat then s.gpr .r8 + 1#64
        else 0#64) ∧
      t.gpr .rcx = i.setWidth 64 + 1#64 ∧
      t.zf = some (i.setWidth 64 + 1#64 - BitVec.ofNat 64 256 == 0#64) ∧
      Keep [.rcx, .r8, .r10] s t := by
  have hw' : InRegions s.wr (s.gpr .rdi + i.setWidth 64) 1 := by rw [VG.Proof.Rc4.X86_64.byte_addr i]; exact hw
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .rdi + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r8 = (if (s.gpr .r8 + 1#64).toNat < (s.gpr .rdx).toNat then s.gpr .r8 + 1#64
        else 0#64) ∧
      t.gpr .rcx = i.setWidth 64 + 1#64 ∧
      t.zf = some (i.setWidth 64 + 1#64 - BitVec.ofNat 64 256 == 0#64)) [.rcx, .r8, .r10] ?_
    (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hk⟩
  rrun [hw', hcx, hax, VG.Proof.Rc4.X86_64.writeW_byte8, VG.Proof.Rc4.X86_64.low_byte, VG.Proof.Rc4.X86_64.and_mask]
  refine ⟨by rw [VG.Proof.Rc4.X86_64.byte_addr i], ?_, rfl⟩
  simp only [decide_eq_true_eq]
  rfl

/-- One concrete key-scheduling round, with both swap operands read before either write. -/
theorem schedule_step (s : State) (i j : Byte)
    (hcx : s.gpr .rcx = i.setWidth 64) (h9 : s.gpr .r9 = j.setWidth 64)
    (hp : InRegions s.wr (s.gpr .rdi) 256)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .rsi + s.gpr .r8) 1) :
    let a := s.mem (s.gpr .rdi + BitVec.ofNat 64 i.toNat)
    let jj := j + a + s.mem (s.gpr .rsi + s.gpr .r8)
    let b := s.mem (s.gpr .rdi + BitVec.ofNat 64 jj.toNat)
    WP isa (.block scheduleStep) s fun t =>
      t.mem = (s.mem.write (s.gpr .rdi + BitVec.ofNat 64 jj.toNat) 1 a).write
        (s.gpr .rdi + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r8 = (if (s.gpr .r8 + 1#64).toNat < (s.gpr .rdx).toNat then s.gpr .r8 + 1#64
        else 0#64) ∧
      t.gpr .r9 = jj.setWidth 64 ∧ t.gpr .rcx = i.setWidth 64 + 1#64 ∧
      t.zf = some (i.setWidth 64 + 1#64 - BitVec.ofNat 64 256 == 0#64) ∧
      Keep ([.r9, .r10] ++ [.rax, .r10, .r11] ++ [.rcx, .r8, .r10]) s t := by
  intro a jj b
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 256 := by
    obtain ⟨r, hr, hc⟩ := hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  unfold scheduleStep
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.X86_64.schedule_before s i j hcx h9 hr hk) fun t ⟨t9, tk, tm⟩ => ?_
  have tcx : t.gpr .rcx = i.setWidth 64 := (tk.gpr (by decide)).trans hcx
  have tdi : t.gpr .rdi = s.gpr .rdi := tk.gpr (by decide)
  have tr8 : t.gpr .r8 = s.gpr .r8 := tk.gpr (by decide)
  have tdx : t.gpr .rdx = s.gpr .rdx := tk.gpr (by decide)
  have htp : InRegions t.wr (t.gpr .rdi) 256 := by rw [tk.2.2, tdi]; exact hp
  refine WP.mono (WP.keep [.rax, .r10, .r11] (VG.Proof.Rc4.X86_64.replace_core t jj i t9 tcx htp) (by decide +kernel))
    fun u ⟨⟨uax, um⟩, uk⟩ => ?_
  have ucx : u.gpr .rcx = i.setWidth 64 := (uk.gpr (by decide)).trans tcx
  have udi : u.gpr .rdi = s.gpr .rdi := (uk.gpr (by decide)).trans tdi
  have ur8 : u.gpr .r8 = s.gpr .r8 := (uk.gpr (by decide)).trans tr8
  have udx : u.gpr .rdx = s.gpr .rdx := (uk.gpr (by decide)).trans tdx
  have u9 : u.gpr .r9 = jj.setWidth 64 := (uk.gpr (by decide)).trans t9
  rw [tm, tdi] at uax um
  have hw : InRegions u.wr (u.gpr .rdi + BitVec.ofNat 64 i.toNat) 1 := by
    rw [uk.2.2, tk.2.2, udi]
    exact region_offset _ _ _ _ _ (by have := i.isLt; omega) (by have := i.isLt; omega) hp
  refine WP.mono (VG.Proof.Rc4.X86_64.schedule_after u i b ucx uax hw) fun v ⟨vm, v8, vcx, vz, vk⟩ => ?_
  refine ⟨?_, ?_, (vk.gpr (by decide)).trans u9, vcx, vz, (tk.trans uk).trans vk⟩
  · rw [vm, um, udi]
  · rw [v8, ur8, udx]

/-- The key bytes, from the key pointer and length of a state. -/
def keyAt (s : State) : List Byte := bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat

structure ScheduleInv (s₀ : State) (r : Nat) (s : State) : Prop where
  frame : TableFrame (s₀.gpr .rdi) s₀.mem s.mem
  table : (contextAt s.mem (s₀.gpr .rdi)).table = (schedulePrefix (VG.Proof.Rc4.X86_64.keyAt s₀) r).1
  j : s.gpr .r9 = (schedulePrefix (VG.Proof.Rc4.X86_64.keyAt s₀) r).2.setWidth 64
  i : s.gpr .rcx = BitVec.ofNat 64 r
  off : s.gpr .r8 = BitVec.ofNat 64 (r % (s₀.gpr .rdx).toNat)
  p : s.gpr .rdi = s₀.gpr .rdi
  len : s.gpr .rdx = s₀.gpr .rdx
  key : s.gpr .rsi = s₀.gpr .rsi
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem schedule_inv_step (s₀ s : State) {r : Nat} (hr : r < 256)
    (hlen : 1 ≤ (s₀.gpr .rdx).toNat ∧ (s₀.gpr .rdx).toNat ≤ 256)
    (hp : InRegions s₀.wr (s₀.gpr .rdi) 256)
    (hk : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi) (s₀.gpr .rdx).toNat)
    (hs : Mem.Sep (s₀.gpr .rsi) (s₀.gpr .rdx).toNat (s₀.gpr .rdi) 256)
    (h : VG.Proof.Rc4.X86_64.ScheduleInv s₀ r s) :
    WP isa (.block scheduleStep) s fun t => VG.Proof.Rc4.X86_64.ScheduleInv s₀ (r + 1) t ∧
      t.zf = some (BitVec.ofNat 64 (r + 1) - BitVec.ofNat 64 256 == 0#64) := by
  let key := VG.Proof.Rc4.X86_64.keyAt s₀
  let st := schedulePrefix key r
  have hrt : (BitVec.ofNat 8 r).toNat = r := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hi : s.gpr .rcx = (BitVec.ofNat 8 r).setWidth 64 := by
    rw [h.i, VG.Proof.Rc4.X86_64.byte_addr, hrt]
  have hpoint : InRegions s.wr (s.gpr .rdi) 256 := by rw [h.wr, h.p]; exact hp
  have hmod := Nat.mod_lt r (show 0 < (s₀.gpr .rdx).toNat by omega)
  have hkeypoint : InRegions (s.rd ++ s.wr) (s.gpr .rsi + s.gpr .r8) 1 := by
    rw [h.rd, h.wr, h.key, h.off]
    exact region_offset _ _ _ _ _ (by omega) (by omega) hk
  have hkeybyte : s.mem (s.gpr .rsi + s.gpr .r8) = key.getD (r % key.length) 0 := by
    rw [h.key, h.off]
    have hsep := hs (s₀.gpr .rsi + BitVec.ofNat 64 (r % (s₀.gpr .rdx).toNat))
      (by rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hmod)
    rw [h.frame _ hsep]
    dsimp only [key, VG.Proof.Rc4.X86_64.keyAt]
    rw [bytes_length, bytes_get _ _ _ _ hmod]
  have htablebyte : s.mem (s.gpr .rdi + BitVec.ofNat 64 r) = st.1.getD r 0 := by
    rw [h.p]
    have hg := table_get s.mem (s₀.gpr .rdi) (BitVec.ofNat 8 r)
    rw [hrt, h.table] at hg
    exact hg.symm
  refine WP.mono (VG.Proof.Rc4.X86_64.schedule_step s _ _ hi h.j hpoint hkeypoint) fun t ⟨tm, t8, t9, tcx, tz, tk⟩ => ?_
  have hnext := schedule_succ key r
  dsimp only [scheduleRound] at hnext
  have hcast : (BitVec.ofNat 8 r).setWidth 64 + 1#64 = BitVec.ofNat 64 (r + 1) := by
    rw [VG.Proof.Rc4.X86_64.byte_addr, hrt, ← BitVec.ofNat_add]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, (tk.gpr (by decide)).trans h.p, (tk.gpr (by decide)).trans h.len,
    (tk.gpr (by decide)).trans h.key, tk.2.1.trans h.rd, tk.2.2.trans h.wr⟩, ?_⟩
  · rw [tm, h.p]
    exact h.frame.trans (swap_frame _ _ _ _)
  · rw [tm, h.p, table_swap, h.table, hnext, hrt]
    have hb := htablebyte
    rw [h.p] at hb
    rw [hb, hkeybyte]
  · rw [t9, hrt, htablebyte, hkeybyte, hnext]
  · rw [tcx, hcast]
  · rw [t8, h.off, h.len]
    exact key_next r _ (by omega) hlen.2
  · rw [tz, hcast]

/-- All 256 scheduling rounds realize the complete specified permutation. -/
theorem schedule_loop (s₀ s : State) {r : Nat} (hr : r < 256)
    (hlen : 1 ≤ (s₀.gpr .rdx).toNat ∧ (s₀.gpr .rdx).toNat ≤ 256)
    (hp : InRegions s₀.wr (s₀.gpr .rdi) 256)
    (hk : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi) (s₀.gpr .rdx).toNat)
    (hs : Mem.Sep (s₀.gpr .rsi) (s₀.gpr .rdx).toNat (s₀.gpr .rdi) 256)
    (h : VG.Proof.Rc4.X86_64.ScheduleInv s₀ r s) :
    WP isa (.loop (.block scheduleStep) .ne) s (VG.Proof.Rc4.X86_64.ScheduleInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ VG.Proof.Rc4.X86_64.ScheduleInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (VG.Proof.Rc4.X86_64.schedule_inv_step s₀ t hj hlen hp hk hs ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    simp only [eval, hz, hend, Option.map_some]
    rfl
  · right
    have hnz : BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 256 ≠ 0#64 := by bv_omega
    refine ⟨?_, 256 - (j + 1), by omega, j + 1, by omega, rfl, hu⟩
    simp only [eval, hz, Option.map_some, beq_eq_false_iff_ne.mpr hnz, Bool.not_false]

end VG.Proof.Rc4.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.X86_64.Init`. -/
section

/-! # RC4 on x86-64: checked initialization -/

namespace VG.Proof.Rc4.X86_64
open VG VG.X86_64 VG.Impl.Rc4.X86_64 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)

/-- Memory changed only within the 258-byte context at `p`. -/
def CtxFrame (p : Addr) (m m' : Mem) : Prop := ∀ x, ¬ (x - p).toNat < 258 → m' x = m x

theorem init_finish (s : State) (hp : InRegions s.wr (s.gpr .rdi) 258) :
    WP isa (.block [.mov .rax (imm 0), .store8 (at_ .rdi 256) .rax,
      .store8 (at_ .rdi 257) .rax]) s fun t => t.gpr .rax = 0#64 ∧
      t.mem = (s.mem.write (s.gpr .rdi + 256#64) 1 0#8).write (s.gpr .rdi + 257#64) 1 0#8 := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  rrun [h256, h257, VG.Proof.Rc4.X86_64.writeW_byte8]
  rfl

theorem ctx_frame_finish (m m' : Mem) (p : Addr) (h : TableFrame p m m') (a b : Byte) :
    VG.Proof.Rc4.X86_64.CtxFrame p m ((m'.write (p + 256#64) 1 a).write (p + 257#64) 1 b) := by
  intro x hx
  have h1 : x ≠ p + 256#64 := by
    intro he; apply hx; rw [he, Mem.sub_ofNat_toNat p (by decide)]; decide
  have h2 : x ≠ p + 257#64 := by
    intro he; apply hx; rw [he, Mem.sub_ofNat_toNat p (by decide)]; decide
  rw [write_byte, ite_eq_right h2, write_byte, ite_eq_right h1]
  exact h x (by omega)

theorem init_valid (s : State)
    (hlen : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 256)
    (hp : InRegions s.wr (s.gpr .rdx) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .rdi) (s.gpr .rsi).toNat)
    (hs : Mem.Sep (s.gpr .rdi) (s.gpr .rsi).toNat (s.gpr .rdx) 256) :
    WP isa initValid s fun t => t.gpr .rax = 0#64 ∧
      contextAt t.mem (s.gpr .rdx) =
        { table := keySchedule (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat), i := 0, j := 0 } ∧
      VG.Proof.Rc4.X86_64.CtxFrame (s.gpr .rdx) s.mem t.mem := by
  have hstart : WP isa (.block [.mov .rax (.reg .rdi), .mov .rdi (.reg .rdx), .mov .rdx (.reg .rsi),
      .mov .rsi (.reg .rax), .mov .rcx (imm 0)]) s fun a =>
      a.mem = s.mem ∧ a.rd = s.rd ∧ a.wr = s.wr ∧ a.gpr .rdi = s.gpr .rdx ∧
      a.gpr .rdx = s.gpr .rsi ∧ a.gpr .rsi = s.gpr .rdi ∧ a.gpr .rcx = 0#64 := by
    rrun
  unfold initValid
  refine WP.seq (WP.mono hstart fun a ha => ?_)
  obtain ⟨ham, har, haw, hadi, hadx, hasi, hacx⟩ := ha
  have hpa : InRegions a.wr (a.gpr .rdi) 256 := by
    rw [haw, hadi]
    have h' := region_offset _ _ _ 0 256 (by decide) (by decide) hp
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h'
  have hia : VG.Proof.Rc4.X86_64.IdentityInv a 0 a :=
    ⟨by rw [identityMem_zero], rfl, rfl, rfl, rfl, rfl, by rw [hacx]⟩
  refine WP.seq (WP.mono (VG.Proof.Rc4.X86_64.identity_loop a a (by decide) hpa hia) fun b hb => ?_)
  obtain ⟨hbm, hbr, hbw, hbdi, hbsi, hbdx, _⟩ := hb
  have hreset : WP isa (.block [.mov .rcx (imm 0), .mov .r8 (imm 0), .mov .r9 (imm 0)]) b
      fun c => c.mem = b.mem ∧ c.rd = b.rd ∧ c.wr = b.wr ∧ c.gpr .rdi = b.gpr .rdi ∧
        c.gpr .rsi = b.gpr .rsi ∧ c.gpr .rdx = b.gpr .rdx ∧ c.gpr .rcx = 0#64 ∧
        c.gpr .r8 = 0#64 ∧ c.gpr .r9 = 0#64 := by
    rrun
  refine WP.seq (WP.mono hreset fun c hc => ?_)
  obtain ⟨hcm, hcr, hcw, hcdi, hcsi, hcdx, hccx, hc8, hc9⟩ := hc
  have hlc : 1 ≤ (c.gpr .rdx).toNat ∧ (c.gpr .rdx).toNat ≤ 256 := by
    rw [hcdx, hbdx, hadx]; exact hlen
  have hpc : InRegions c.wr (c.gpr .rdi) 256 := by rw [hcw, hcdi, hbw, hbdi]; exact hpa
  have hkc : InRegions (c.rd ++ c.wr) (c.gpr .rsi) (c.gpr .rdx).toNat := by
    rw [hcr, hcw, hcsi, hcdx, hbr, hbw, hbsi, hbdx, har, haw, hasi, hadx]; exact hk
  have hsc : Mem.Sep (c.gpr .rsi) (c.gpr .rdx).toNat (c.gpr .rdi) 256 := by
    rw [hcsi, hcdx, hcdi, hbsi, hbdx, hbdi, hasi, hadx, hadi]; exact hs
  have hic : VG.Proof.Rc4.X86_64.ScheduleInv c 0 c := by
    refine ⟨TableFrame.refl _ _, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · rw [hcm, hbm, hcdi, hbdi, identityMem_table, schedule_zero]
    · rw [hc9]; rfl
    · rw [hccx]
    · rw [hc8, Nat.zero_mod]
  refine WP.seq (WP.mono (VG.Proof.Rc4.X86_64.schedule_loop c c (by decide) hlc hpc hkc hsc hic) fun d hd => ?_)
  have hpd : InRegions d.wr (d.gpr .rdi) 258 := by
    rw [hd.wr, hd.p, hcw, hcdi, hbw, hbdi, haw, hadi]; exact hp
  refine WP.mono (VG.Proof.Rc4.X86_64.init_finish d hpd) fun e ⟨heax, hem⟩ => ?_
  have hp0 : d.gpr .rdi = s.gpr .rdx := by rw [hd.p, hcdi, hbdi, hadi]
  have hkey : VG.Proof.Rc4.X86_64.keyAt c = bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat := by
    unfold VG.Proof.Rc4.X86_64.keyAt
    rw [hcm, hcsi, hcdx, hbsi, hbdx, hasi, hadx, hbm, ham]
    exact bytes_table_frame _ _ _ _ _ (s.gpr .rsi).isLt
      (identityMem_frame _ _ _ (by decide)) (by rw [hadi]; exact hs)
  refine ⟨heax, ?_, ?_⟩
  · rw [hem, hp0, context_finish, ← hp0, hd.p, hd.table, ← keySchedule_eq, hkey]
    rfl
  · rw [hem, hp0]
    refine VG.Proof.Rc4.X86_64.ctx_frame_finish _ _ _ ?_ _ _
    have hf := hd.frame
    rw [hcm, hbm, hcdi, hbdi, hadi, ham] at hf
    exact (identityMem_frame _ _ _ (by decide)).trans hf

theorem valid_length (len : BitVec 64) :
    (len - 1#64).toNat < 256 ↔ 1 ≤ len.toNat ∧ len.toNat ≤ 256 := by bv_omega

/-- The full checked initializer, including both key-length boundaries. -/
theorem init_ok (s : State)
    (hp : InRegions s.wr (s.gpr .rdx) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .rdi) (s.gpr .rsi).toNat)
    (hs : Mem.Sep (s.gpr .rdi) (s.gpr .rsi).toNat (s.gpr .rdx) 256) :
    WP isa VG.Impl.Rc4.X86_64.init s fun t =>
      (match VG.Spec.Rc4.init (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) with
      | .ok ctx => t.gpr .rax = 0#64 ∧ contextAt t.mem (s.gpr .rdx) = ctx
      | .error .invalidKeyLength => t.gpr .rax = 1#64) ∧
      VG.Proof.Rc4.X86_64.CtxFrame (s.gpr .rdx) s.mem t.mem := by
  have hcheck : WP isa (.block [.mov .rax (.reg .rsi), .alu .sub .rax (imm 1),
      .alu .cmp .rax (imm 256)]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .rdi = s.gpr .rdi ∧
      t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = s.gpr .rdx ∧
      t.cf = some (decide ((s.gpr .rsi - 1#64).toNat < 256)) := by
    rrun
    exact rfl
  unfold VG.Impl.Rc4.X86_64.init
  refine WP.seq (WP.mono hcheck fun t ht => ?_)
  obtain ⟨htm, htr, htw, htdi, htsi, htdx, htcf⟩ := ht
  let good := 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 256
  have hcond : isa.eval .ae t = some (decide (¬ good)) := by
    simp only [eval, htcf, Option.map_some]
    congr 1
    by_cases hg : good
    · rw [decide_eq_true ((VG.Proof.Rc4.X86_64.valid_length _).mpr hg), decide_eq_false (not_not_intro hg)]
      rfl
    · rw [decide_eq_false (fun h => hg ((VG.Proof.Rc4.X86_64.valid_length _).mp h)), decide_eq_true hg]
      rfl
  refine WP.ite (decide (¬ good)) hcond (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬ good := of_decide_eq_true hn
    change ¬ (1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 256) at hn'
    simp only [VG.Spec.Rc4.init, bytes_length, hn', ite_false]
    rrun [htm]
    exact fun _ _ => rfl
  · have hg : good := Classical.not_not.mp (of_decide_eq_false hy)
    change 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 256 at hg
    simp only [VG.Spec.Rc4.init, bytes_length, hg, and_self, ite_true]
    have hpt : InRegions t.wr (t.gpr .rdx) 258 := by rw [htw, htdx]; exact hp
    have hkt : InRegions (t.rd ++ t.wr) (t.gpr .rdi) (t.gpr .rsi).toNat := by
      rw [htr, htw, htdi, htsi]; exact hk
    have hst : Mem.Sep (t.gpr .rdi) (t.gpr .rsi).toNat (t.gpr .rdx) 256 := by
      rw [htdi, htsi, htdx]; exact hs
    have hlt : 1 ≤ (t.gpr .rsi).toNat ∧ (t.gpr .rsi).toNat ≤ 256 := htsi ▸ hg
    refine WP.mono (VG.Proof.Rc4.X86_64.init_valid t hlt hpt hkt hst) fun u ⟨hu0, huc, huf⟩ => ?_
    simp only [htm, htdi, htsi, htdx] at huc huf
    exact ⟨⟨hu0, huc⟩, huf⟩

end VG.Proof.Rc4.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.X86_64.ApplyStep`. -/
section

/-! # RC4 on x86-64: one PRGA step -/

namespace VG.Proof.Rc4.X86_64
open VG VG.X86_64 VG.Impl.Rc4.X86_64 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)

theorem byte_inc (i : Byte) :
    i.setWidth 64 + BitVec.ofNat 64 1 &&& BitVec.ofNat 64 255 = (i + 1#8).setWidth 64 := by
  have h := VG.Proof.Rc4.X86_64.byte_add i 1#8
  rwa [show (1#8).setWidth 64 = BitVec.ofNat 64 1 from rfl] at h

theorem apply_before (s : State) (i j : Byte)
    (hcx : s.gpr .rcx = i.setWidth 64) (h8 : s.gpr .r8 = j.setWidth 64)
    (hp : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 256) :
    WP isa (.block [.alu .add .rcx (imm 1), .alu .and .rcx (imm 255),
      .movzx8 .r10 (atIdx .rdi .rcx), .alu .add .r8 (.reg .r10), .alu .and .r8 (imm 255),
      .mov .r9 (.reg .r8)]) s fun t =>
      t.gpr .rcx = (i + 1#8).setWidth 64 ∧
      t.gpr .r8 = (j + s.mem (s.gpr .rdi + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.gpr .r9 = (j + s.mem (s.gpr .rdi + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      Keep [.rcx, .r8, .r9, .r10] s t ∧ t.mem = s.mem := by
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .rdi + (i + 1#8).setWidth 64) 1 := by
    rw [VG.Proof.Rc4.X86_64.byte_addr (i + 1#8)]
    exact region_offset _ _ _ _ _ (by have := (i + 1#8).isLt; omega)
      (by have := (i + 1#8).isLt; omega) hp
  refine WP.mono (WP.keep (Q := fun t => t.gpr .rcx = (i + 1#8).setWidth 64 ∧
      t.gpr .r8 = (j + s.mem (s.gpr .rdi + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.gpr .r9 = (j + s.mem (s.gpr .rdi + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.mem = s.mem) [.rcx, .r8, .r9, .r10] ?_ (by decide +kernel))
    fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, hk, h.2.2.2⟩
  rrun [hcx, h8, VG.Proof.Rc4.X86_64.byte_inc, hi]
  rw [VG.Proof.Rc4.X86_64.byte_addr (i + 1#8), VG.Proof.Rc4.X86_64.byte_add]
  exact ⟨rfl, rfl⟩

theorem apply_middle (s : State) (ii b : Byte)
    (hcx : s.gpr .rcx = ii.setWidth 64) (hax : s.gpr .rax = b.setWidth 64)
    (hw : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 ii.toNat) 1) :
    WP isa (.block [.movzx8 .r10 (atIdx .rdi .rcx), .store8 (atIdx .rdi .rcx) .rax,
      .alu .add .rax (.reg .r10), .alu .and .rax (imm 255), .mov .r9 (.reg .rax)]) s fun t =>
      t.mem = s.mem.write (s.gpr .rdi + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .r9 = (b + s.mem (s.gpr .rdi + BitVec.ofNat 64 ii.toNat)).setWidth 64 ∧
      Keep [.rax, .r9, .r10] s t := by
  have hw' : InRegions s.wr (s.gpr .rdi + ii.setWidth 64) 1 := by rw [VG.Proof.Rc4.X86_64.byte_addr ii]; exact hw
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi + ii.setWidth 64) 1 := by
    obtain ⟨r, hr, hc⟩ := hw'
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .rdi + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .r9 = (b + s.mem (s.gpr .rdi + BitVec.ofNat 64 ii.toNat)).setWidth 64)
      [.rax, .r9, .r10] ?_ (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  rrun [hcx, hax, hw', hr, VG.Proof.Rc4.X86_64.writeW_byte8, VG.Proof.Rc4.X86_64.low_byte, VG.Proof.Rc4.X86_64.byte_add]
  rw [VG.Proof.Rc4.X86_64.byte_addr ii]
  exact ⟨rfl, rfl⟩

theorem low_xor (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 = a ^^^ b := by
  rw [VG.Proof.Rc4.X86_64.xor_byte, VG.Proof.Rc4.X86_64.low_byte]

theorem apply_after (s : State) (k : Byte) (hax : s.gpr .rax = k.setWidth 64)
    (hd : InRegions s.wr (s.gpr .rsi) 1) :
    WP isa (.block [.movzx8 .r10 (at_ .rsi 0), .alu .xor .r10 (.reg .rax),
      .store8 (at_ .rsi 0) .r10, .alu .add .rsi (imm 1), .alu .sub .rdx (imm 1)]) s fun t =>
      t.mem = s.mem.write (s.gpr .rsi) 1 (s.mem (s.gpr .rsi) ^^^ k) ∧
      t.gpr .rsi = s.gpr .rsi + 1#64 ∧ t.gpr .rdx = s.gpr .rdx - 1#64 ∧
      t.zf = some (s.gpr .rdx - 1#64 == 0#64) ∧ Keep [.rsi, .rdx, .r10] s t := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1 := by
    obtain ⟨r, hr, hc⟩ := hd
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .rsi) 1 (s.mem (s.gpr .rsi) ^^^ k) ∧
      t.gpr .rsi = s.gpr .rsi + 1#64 ∧ t.gpr .rdx = s.gpr .rdx - 1#64 ∧
      t.zf = some (s.gpr .rdx - 1#64 == 0#64)) [.rsi, .rdx, .r10] ?_ (by decide +kernel))
    fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hk⟩
  rrun [hax, hd, hr, VG.Proof.Rc4.X86_64.writeW_byte8, VG.Proof.Rc4.X86_64.low_xor]
  rfl

/-- One iteration, with the writes expressed against the original memory.
Both swap operands are read before either write, including for a self-swap. -/
theorem apply_step (s : State) (i j : Byte)
    (hcx : s.gpr .rcx = i.setWidth 64) (h8 : s.gpr .r8 = j.setWidth 64)
    (hp : InRegions s.wr (s.gpr .rdi) 256) (hd : InRegions s.wr (s.gpr .rsi) 1) :
    let ii := i + 1#8
    let a := s.mem (s.gpr .rdi + BitVec.ofNat 64 ii.toNat)
    let jj := j + a
    let b := s.mem (s.gpr .rdi + BitVec.ofNat 64 jj.toNat)
    let swapped := (s.mem.write (s.gpr .rdi + BitVec.ofNat 64 jj.toNat) 1 a).write
      (s.gpr .rdi + BitVec.ofNat 64 ii.toNat) 1 b
    let k := swapped (s.gpr .rdi + BitVec.ofNat 64 (a + b).toNat)
    WP isa (.block applyStep) s fun t =>
      t.mem = swapped.write (s.gpr .rsi) 1 (swapped (s.gpr .rsi) ^^^ k) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .rdi = s.gpr .rdi ∧
      t.gpr .rsi = s.gpr .rsi + 1#64 ∧ t.gpr .rdx = s.gpr .rdx - 1#64 ∧
      t.zf = some (s.gpr .rdx - 1#64 == 0#64) ∧
      t.gpr .rcx = ii.setWidth 64 ∧ t.gpr .r8 = jj.setWidth 64 := by
  intro ii a jj b swapped k
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 256 := by
    obtain ⟨r, hr, hc⟩ := hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  simp only [applyStep, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.X86_64.apply_before s i j hcx h8 hr) fun t ⟨tcx, t8, t9, tk, tm⟩ => ?_
  have tdi : t.gpr .rdi = s.gpr .rdi := tk.gpr (by decide)
  have tsi : t.gpr .rsi = s.gpr .rsi := tk.gpr (by decide)
  have tdx : t.gpr .rdx = s.gpr .rdx := tk.gpr (by decide)
  have htp : InRegions t.wr (t.gpr .rdi) 256 := by rw [tk.2.2, tdi]; exact hp
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .r10, .r11] (VG.Proof.Rc4.X86_64.replace_core t jj ii t9 tcx htp) (by decide +kernel))
    fun u ⟨⟨uax, um⟩, uk⟩ => ?_
  rw [tm, tdi] at uax um
  have ucx : u.gpr .rcx = ii.setWidth 64 := (uk.gpr (by decide)).trans tcx
  have u8 : u.gpr .r8 = jj.setWidth 64 := (uk.gpr (by decide)).trans t8
  have udi : u.gpr .rdi = s.gpr .rdi := (uk.gpr (by decide)).trans tdi
  have usi : u.gpr .rsi = s.gpr .rsi := (uk.gpr (by decide)).trans tsi
  have udx : u.gpr .rdx = s.gpr .rdx := (uk.gpr (by decide)).trans tdx
  have urd : u.rd = s.rd := uk.2.1.trans tk.2.1
  have uwr : u.wr = s.wr := uk.2.2.trans tk.2.2
  have hw : InRegions u.wr (u.gpr .rdi + BitVec.ofNat 64 ii.toNat) 1 := by
    rw [uwr, udi]
    exact region_offset _ _ _ _ _ (by have := ii.isLt; omega) (by have := ii.isLt; omega) hp
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.X86_64.apply_middle u ii b ucx uax hw) fun v ⟨vm, v9, vk⟩ => ?_
  have ha : u.mem (u.gpr .rdi + BitVec.ofNat 64 ii.toNat) = a := by
    rw [um, udi, write_byte]
    split <;> rfl
  rw [ha] at v9
  rw [udi, um] at vm
  have hvm : v.mem = swapped := vm
  have v9' : v.gpr .r9 = (a + b).setWidth 64 := by rw [v9, BitVec.add_comm]
  have vdi : v.gpr .rdi = s.gpr .rdi := (vk.gpr (by decide)).trans udi
  have vrd : v.rd = s.rd := vk.2.1.trans urd
  have vwr : v.wr = s.wr := vk.2.2.trans uwr
  have hvp : InRegions (v.rd ++ v.wr) (v.gpr .rdi) 256 := by rw [vrd, vwr, vdi]; exact hr
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .r10, .r11] (VG.Proof.Rc4.X86_64.lookup_core v (a + b) v9' hvp) (by decide +kernel))
    fun w ⟨⟨wax, wm⟩, wk⟩ => ?_
  rw [hvm, vdi] at wax
  have wsi : w.gpr .rsi = s.gpr .rsi := (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans usi)
  have wdx : w.gpr .rdx = s.gpr .rdx := (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans udx)
  have wdi : w.gpr .rdi = s.gpr .rdi := (wk.gpr (by decide)).trans vdi
  have wrd : w.rd = s.rd := wk.2.1.trans vrd
  have wwr : w.wr = s.wr := wk.2.2.trans vwr
  have hwd : InRegions w.wr (w.gpr .rsi) 1 := by rw [wwr, wsi]; exact hd
  refine WP.mono (VG.Proof.Rc4.X86_64.apply_after w k wax hwd) fun z ⟨zm, zsi, zdx, zz, zk⟩ => ?_
  refine ⟨?_, zk.2.1.trans wrd, zk.2.2.trans wwr, (zk.gpr (by decide)).trans wdi, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [zm, wm, hvm, wsi]
  · rw [zsi, wsi]
  · rw [zdx, wdx]
  · rw [zz, wdx]
  · rw [zk.gpr (by decide), wk.gpr (by decide), vk.gpr (by decide), ucx]
  · rw [zk.gpr (by decide), wk.gpr (by decide), vk.gpr (by decide), u8]

end VG.Proof.Rc4.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.X86_64.Apply`. -/
section

/-! # RC4 on x86-64: the stream function -/

namespace VG.Proof.Rc4.X86_64
open VG VG.X86_64 VG.Impl.Rc4.X86_64 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)

/-- The concrete stream iteration realizes the abstract PRGA transition. -/
theorem apply_step_table (s : State) (i j : Byte)
    (hcx : s.gpr .rcx = i.setWidth 64) (h8 : s.gpr .r8 = j.setWidth 64)
    (hp : InRegions s.wr (s.gpr .rdi) 256) (hd : InRegions s.wr (s.gpr .rsi) 1)
    (hs : Mem.Sep (s.gpr .rdi) 256 (s.gpr .rsi) 1) :
    let next := step { table := (contextAt s.mem (s.gpr .rdi)).table, i, j }
    WP isa (.block applyStep) s fun t =>
      (contextAt t.mem (s.gpr .rdi)).table = next.1.table ∧
      t.gpr .rcx = next.1.i.setWidth 64 ∧ t.gpr .r8 = next.1.j.setWidth 64 ∧
      t.mem (s.gpr .rsi) = s.mem (s.gpr .rsi) ^^^ next.2 ∧
      StreamFrame (s.gpr .rdi) (s.gpr .rsi) 1 s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .rdi = s.gpr .rdi ∧
      t.gpr .rsi = s.gpr .rsi + 1#64 ∧ t.gpr .rdx = s.gpr .rdx - 1#64 ∧
      t.zf = some (s.gpr .rdx - 1#64 == 0#64) := by
  dsimp only
  rw [step_eq]
  dsimp only
  simp only [table_get]
  have hone : (1 : Byte) = 1#8 := rfl
  simp only [hone]
  refine WP.mono (VG.Proof.Rc4.X86_64.apply_step s i j hcx h8 hp hd) fun t ht => ?_
  obtain ⟨hmem, hrd, hwr, h0, h1, h2, hz, hi, hj⟩ := ht
  refine ⟨?_, hi, hj, ?_, ?_, hrd, hwr, h0, h1, h2, hz⟩
  · rw [hmem, table_write_sep _ _ _ _ hs, table_swap]
  · rw [hmem, write_byte, ite_eq_left rfl]
    have hne (idx : Byte) : s.gpr .rsi ≠ s.gpr .rdi + BitVec.ofNat 64 idx.toNat := by
      intro he
      have hn := hs (s.gpr .rsi) (by rw [he, Mem.sub_ofNat_toNat _ (by omega)]; exact idx.isLt)
      exact hn (by simp [BitVec.sub_self])
    rw [write_byte, ite_eq_right (hne _), write_byte, ite_eq_right (hne _)]
    have ht := table_swap s.mem (s.gpr .rdi) (i + 1#8)
      (j + s.mem (s.gpr .rdi + BitVec.ofNat 64 (i + 1#8).toNat))
    rw [← ht, table_get]
  · rw [hmem]
    exact stream_frame_step _ _ _ _ _ _

/-- The unconsumed data remains unchanged by a stream iteration. -/
theorem apply_step_tail (s : State) (i j : Byte) (n : Nat)
    (hn : n + 1 < 2 ^ 64)
    (hcx : s.gpr .rcx = i.setWidth 64) (h8 : s.gpr .r8 = j.setWidth 64)
    (hp : InRegions s.wr (s.gpr .rdi) 256) (hd : InRegions s.wr (s.gpr .rsi) 1)
    (hs : Mem.Sep (s.gpr .rdi) 256 (s.gpr .rsi) (n + 1)) :
    WP isa (.block applyStep) s fun t =>
      bytesAt t.mem (s.gpr .rsi + 1#64) n = bytesAt s.mem (s.gpr .rsi + 1#64) n := by
  refine WP.mono (VG.Proof.Rc4.X86_64.apply_step s i j hcx h8 hp hd) fun t ht => ?_
  rw [ht.1]
  rw [bytes_write_sep _ _ _ _ _ (by omega)
    (sep_symm (Offset.sep_base (s.gpr .rsi) (by decide) (by omega)))]
  exact bytes_table_frame _ _ _ _ _ (by omega) (swap_frame _ _ _ _)
    (sep_symm (sep_tail hn hs))

structure LoopPost (s : State) (ctx : Context) (n : Nat) (t : State) : Prop where
  table : (contextAt t.mem (s.gpr .rdi)).table =
    (update ctx (bytesAt s.mem (s.gpr .rsi) n)).1.table
  i : t.gpr .rcx = (update ctx (bytesAt s.mem (s.gpr .rsi) n)).1.i.setWidth 64
  j : t.gpr .r8 = (update ctx (bytesAt s.mem (s.gpr .rsi) n)).1.j.setWidth 64
  data : bytesAt t.mem (s.gpr .rsi) n = (update ctx (bytesAt s.mem (s.gpr .rsi) n)).2
  frame : StreamFrame (s.gpr .rdi) (s.gpr .rsi) n s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  p : t.gpr .rdi = s.gpr .rdi

/-- Streaming correctness by induction on the public byte count. -/
theorem apply_loop (n : Nat) (s : State) (ctx : Context)
    (hn : n + 1 < 2 ^ 64)
    (htable : (contextAt s.mem (s.gpr .rdi)).table = ctx.table)
    (hcx : s.gpr .rcx = ctx.i.setWidth 64) (h8 : s.gpr .r8 = ctx.j.setWidth 64)
    (hlen : s.gpr .rdx = BitVec.ofNat 64 (n + 1))
    (hp : InRegions s.wr (s.gpr .rdi) 256)
    (hd : InRegions s.wr (s.gpr .rsi) (n + 1))
    (hs : Mem.Sep (s.gpr .rdi) 256 (s.gpr .rsi) (n + 1)) :
    WP isa (.loop (.block applyStep) .ne) s (VG.Proof.Rc4.X86_64.LoopPost s ctx (n + 1)) := by
  induction n generalizing s ctx with
  | zero =>
    have hd1 : InRegions s.wr (s.gpr .rsi) 1 := hd
    have hctx : ({ table := (contextAt s.mem (s.gpr .rdi)).table, i := ctx.i, j := ctx.j } :
        Context) = ctx := context_ext htable rfl rfl
    have hstep := VG.Proof.Rc4.X86_64.apply_step_table s ctx.i ctx.j hcx h8 hp hd1 hs
    rw [hctx] at hstep
    obtain ⟨tr, t, he, ht⟩ := hstep
    obtain ⟨htab, hti, htj, hbyte, hf, hrd, hwr, hp0, _, hcount, hz⟩ := ht
    have hz' : t.zf = some true := by rw [hz, hlen]; rfl
    have hbytes (m : Mem) : bytesAt m (s.gpr .rsi) 1 = [m (s.gpr .rsi)] := by
      simp [bytesAt]
    refine ⟨_, t, .loopExit he ?_, ?_⟩
    · simp only [eval, hz', Option.map_some]
      rfl
    · constructor
      · simpa only [Nat.zero_add, hbytes, update] using htab
      · simpa only [Nat.zero_add, hbytes, update] using hti
      · simpa only [Nat.zero_add, hbytes, update] using htj
      · simp only [Nat.zero_add, hbytes, update, hbyte]
      · exact hf
      · exact hrd
      · exact hwr
      · exact hp0
  | succ n ih =>
    have hd1 : InRegions s.wr (s.gpr .rsi) 1 := by
      have hh := region_offset _ _ _ 0 1 (by decide) (by omega) hd
      simpa only [BitVec.add_zero] using hh
    have hs1 : Mem.Sep (s.gpr .rdi) 256 (s.gpr .rsi) 1 := fun x hx hy => hs x hx (by omega)
    have hctx : ({ table := (contextAt s.mem (s.gpr .rdi)).table, i := ctx.i, j := ctx.j } :
        Context) = ctx := context_ext htable rfl rfl
    have hstep := VG.Proof.Rc4.X86_64.apply_step_table s ctx.i ctx.j hcx h8 hp hd1 hs1
    rw [hctx] at hstep
    obtain ⟨tr, t, he, ht⟩ := hstep
    obtain ⟨htab, hti, htj, hbyte, hf, hrd, hwr, hp0, hdptr, hcount, hz⟩ := ht
    have htail : bytesAt t.mem (s.gpr .rsi + 1#64) (n + 1) =
        bytesAt s.mem (s.gpr .rsi + 1#64) (n + 1) := by
      obtain ⟨_, u, he', hh⟩ := VG.Proof.Rc4.X86_64.apply_step_tail s ctx.i ctx.j (n + 1) hn hcx h8 hp hd1 hs
      obtain ⟨_, rfl⟩ := Exec.det he' he
      exact hh
    have htlen : t.gpr .rdx = BitVec.ofNat 64 (n + 1) := by
      rw [hcount, hlen]
      exact Offset.ofNat_sub_ofNat (by omega)
    have hpt : InRegions t.wr (t.gpr .rdi) 256 := by rw [hwr, hp0]; exact hp
    have hdt : InRegions t.wr (t.gpr .rsi) (n + 1) := by
      rw [hwr, hdptr]
      exact region_offset _ _ _ 1 (n + 1) (by decide) (by omega) hd
    have hst : Mem.Sep (t.gpr .rdi) 256 (t.gpr .rsi) (n + 1) := by
      rw [hp0, hdptr]
      exact sep_tail hn hs
    have htab' : (contextAt t.mem (t.gpr .rdi)).table = (step ctx).1.table := by
      rw [hp0]; exact htab
    obtain ⟨tr', u, he', hu⟩ := ih t (step ctx).1 (by omega) htab' hti htj htlen hpt hdt hst
    refine ⟨_, u, .loopNext he ?_ he', ?_⟩
    · have hnz : BitVec.ofNat 64 (n + 1 + 1) - 1#64 ≠ 0#64 := by
        rw [Offset.ofNat_sub_ofNat (by omega)]
        intro hz0
        have hh := congrArg BitVec.toNat hz0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hh
        change n + 1 + 1 - 1 = 0 at hh
        omega
      rw [hlen] at hz
      simp only [eval, hz, Option.map_some, beq_eq_false_iff_ne.mpr hnz, Bool.not_false]
    · have hresult : update ctx (bytesAt s.mem (s.gpr .rsi) (n + 1 + 1)) =
          ((update (step ctx).1 (bytesAt t.mem (t.gpr .rsi) (n + 1))).1,
            (s.mem (s.gpr .rsi) ^^^ (step ctx).2) ::
              (update (step ctx).1 (bytesAt t.mem (t.gpr .rsi) (n + 1))).2) := by
        rw [bytes_cons, hdptr, htail]
        rfl
      constructor
      · rw [hresult, ← hp0]; exact hu.table
      · rw [hresult]; exact hu.i
      · rw [hresult]; exact hu.j
      · rw [bytes_cons, hresult]
        have hh : u.mem (s.gpr .rsi) = t.mem (s.gpr .rsi) := by
          have hf' := hu.frame
          rw [hp0, hdptr] at hf'
          exact stream_head _ _ _ _ _ hn hf' hs
        rw [hh, hbyte, ← hdptr, hu.data]
      · have hf' := hu.frame
        rw [hp0, hdptr] at hf'
        exact stream_frame_trans_tail hf hf'
      · exact hu.rd.trans hrd
      · exact hu.wr.trans hwr
      · exact hu.p.trans hp0

theorem apply_finish (s : State) (ctx : Context) (d : Addr) (n : Nat) (hn : n < 2 ^ 64)
    (htable : (contextAt s.mem (s.gpr .rdi)).table = ctx.table)
    (hcx : s.gpr .rcx = ctx.i.setWidth 64) (h8 : s.gpr .r8 = ctx.j.setWidth 64)
    (hp : InRegions s.wr (s.gpr .rdi) 258)
    (hs : Mem.Sep d n (s.gpr .rdi) 258) :
    WP isa (.block [.store8 (at_ .rdi 256) .rcx, .store8 (at_ .rdi 257) .r8]) s fun t =>
      contextAt t.mem (s.gpr .rdi) = ctx ∧ bytesAt t.mem d n = bytesAt s.mem d n ∧
      t.mem = (s.mem.write (s.gpr .rdi + 256#64) 1 ctx.i).write (s.gpr .rdi + 257#64) 1 ctx.j := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  rrun [h256, h257, hcx, h8, VG.Proof.Rc4.X86_64.writeW_byte8, VG.Proof.Rc4.X86_64.low_byte]
  refine ⟨?_, ?_⟩
  · rw [context_finish, htable]
  · rw [bytes_write_sep _ _ _ _ _ hn (sep_offset_right hs (by decide) (by decide)),
      bytes_write_sep _ _ _ _ _ hn (sep_offset_right hs (by decide) (by decide))]

theorem apply_start (s : State) (hp : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 258) :
    WP isa (.block [.movzx8 .rcx (at_ .rdi 256), .movzx8 .r8 (at_ .rdi 257),
      .alu .test .rdx (.reg .rdx)]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = s.gpr .rdx ∧
      t.gpr .rcx = (contextAt s.mem (s.gpr .rdi)).i.setWidth 64 ∧
      t.gpr .r8 = (contextAt s.mem (s.gpr .rdi)).j.setWidth 64 ∧
      t.zf = some (s.gpr .rdx &&& s.gpr .rdx == 0#64) := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  rrun [h256, h257, contextAt]
  exact ⟨rfl, rfl, rfl⟩

/-- Memory changed only within the context and the data. -/
def ApplyFrame (p d : Addr) (n : Nat) (m m' : Mem) : Prop :=
  ∀ x, ¬ (x - p).toNat < 258 → ¬ (x - d).toNat < n → m' x = m x

theorem apply_ok (s : State)
    (hp : InRegions s.wr (s.gpr .rdi) 258)
    (hd : InRegions s.wr (s.gpr .rsi) (s.gpr .rdx).toNat)
    (hs : Mem.Sep (s.gpr .rdi) 258 (s.gpr .rsi) (s.gpr .rdx).toNat) :
    WP isa VG.Impl.Rc4.X86_64.apply s fun t =>
      let result := update (contextAt s.mem (s.gpr .rdi))
        (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
      (contextAt t.mem (s.gpr .rdi) = result.1 ∧
        bytesAt t.mem (s.gpr .rsi) (s.gpr .rdx).toNat = result.2) ∧
      VG.Proof.Rc4.X86_64.ApplyFrame (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx).toNat s.mem t.mem := by
  have hpRead : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 258 := by
    obtain ⟨region, hr, hc⟩ := hp
    exact ⟨region, List.mem_append_right _ hr, hc⟩
  unfold VG.Impl.Rc4.X86_64.apply
  refine WP.seq (WP.mono (VG.Proof.Rc4.X86_64.apply_start s hpRead) fun a ha => ?_)
  obtain ⟨ham, har, haw, ha0, ha1, ha2, ha12, ha13, haz⟩ := ha
  refine WP.ite (s.gpr .rdx == 0#64) (by simp only [eval, haz, BitVec.and_self]) (fun hz => ?_)
    (fun hnz => ?_)
  · have hz' : s.gpr .rdx = 0#64 := beq_iff_eq.mp hz
    refine WP.block_nil ?_
    simp only [hz', ham]
    exact ⟨⟨context_ext rfl rfl rfl, rfl⟩, fun _ _ _ => rfl⟩
  · have hnz' : s.gpr .rdx ≠ 0#64 := beq_eq_false_iff_ne.mp hnz
    obtain ⟨n, hnEq⟩ := Nat.exists_eq_succ_of_ne_zero (show (s.gpr .rdx).toNat ≠ 0 by
      intro h; exact hnz' (BitVec.eq_of_toNat_eq h))
    change (s.gpr .rdx).toNat = n + 1 at hnEq
    have hbound : n + 1 < 2 ^ 64 := by rw [← hnEq]; exact (s.gpr .rdx).isLt
    have hpa : InRegions a.wr (a.gpr .rdi) 256 := by
      rw [haw, ha0]
      have hh := region_offset _ _ _ 0 256 (by decide) (by decide) hp
      simpa only [BitVec.add_zero] using hh
    have hda : InRegions a.wr (a.gpr .rsi) (n + 1) := by rw [haw, ha1, ← hnEq]; exact hd
    have hsa : Mem.Sep (a.gpr .rdi) 256 (a.gpr .rsi) (n + 1) := by
      rw [ha0, ha1, ← hnEq]
      exact fun x hx hy => hs x (by omega) hy
    have htable : (contextAt a.mem (a.gpr .rdi)).table = (contextAt s.mem (s.gpr .rdi)).table := by
      rw [ham, ha0]
    have hlen : a.gpr .rdx = BitVec.ofNat 64 (n + 1) := by
      rw [ha2, ← hnEq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine WP.seq (WP.mono (VG.Proof.Rc4.X86_64.apply_loop n a (contextAt s.mem (s.gpr .rdi)) hbound htable ha12 ha13
      hlen hpa hda hsa) fun b hb => ?_)
    have hpb : InRegions b.wr (b.gpr .rdi) 258 := by rw [hb.wr, hb.p, haw, ha0]; exact hp
    have hsb : Mem.Sep (s.gpr .rsi) (n + 1) (b.gpr .rdi) 258 := by
      rw [hb.p, ha0, ← hnEq]
      exact sep_symm hs
    have htab : (contextAt b.mem (b.gpr .rdi)).table =
        (update (contextAt s.mem (s.gpr .rdi)) (bytesAt a.mem (a.gpr .rsi) (n + 1))).1.table := by
      rw [hb.p]; exact hb.table
    refine WP.mono (VG.Proof.Rc4.X86_64.apply_finish b _ (s.gpr .rsi) (n + 1) (by omega) htab hb.i hb.j hpb hsb)
      fun t ⟨htc, htd, htm⟩ => ?_
    have hdata := hb.data
    rw [ha1, ham] at hdata
    rw [hb.p, ha0, ham, ha1] at htc
    rw [hnEq]
    refine ⟨⟨htc, htd.trans hdata⟩, ?_⟩
    intro x hx hy
    have hf := hb.frame
    rw [ha0, ha1, ham] at hf
    rw [htm, hb.p, ha0]
    have h1 : x ≠ s.gpr .rdi + 256#64 := by
      intro he; apply hx; rw [he, Mem.sub_ofNat_toNat _ (by decide)]; decide
    have h2 : x ≠ s.gpr .rdi + 257#64 := by
      intro he; apply hx; rw [he, Mem.sub_ofNat_toNat _ (by decide)]; decide
    rw [write_byte, ite_eq_right h2, write_byte, ite_eq_right h1]
    exact hf x (by omega) hy

end VG.Proof.Rc4.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.X86_64.Lit`. -/
section

/-! Literal code keeps unrolled table scans cheap for kernel-evaluated audits. -/
namespace VG.Impl.Rc4.X86_64
materialize_value lookup
materialize_value replace
materialize_value scheduleStep
materialize_value applyStep
materialize_code VG.Impl.Rc4.X86_64.init
materialize_code apply
end VG.Impl.Rc4.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.X86_64.Verified`. -/
section

/-! # RC4 on x86-64: verified against the shared contracts -/

namespace VG.Proof.Rc4.X86_64
open VG VG.X86_64 VG.Impl.Rc4.X86_64 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly gprPreserved_of)

/-! ## Initialization -/

/-- The contract the proof of `vg_rc4_init` is written against. -/
def initX : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let ctx : Region := ⟨s.gpr .rdx, 258⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [ctx] ∧ key.Disjoint ctx ∧ ret.Disjoint ctx
  post s s' :=
    match Spec.Rc4.init (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) with
    | .ok c => (s'.gpr .rax).setWidth 32 = 0 ∧ contextAt s'.mem (s.gpr .rdx) = c
    | .error .invalidKeyLength => (s'.gpr .rax).setWidth 32 = 1
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx

/-- The registers the code writes. -/
def written : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]

theorem init_correct (s : State) (hs : initX.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initX.post s s' := by
  obtain ⟨hrd, hwr, hkc, hrc⟩ := hs
  have hp : InRegions s.wr (s.gpr .rdx) 258 :=
    ⟨⟨s.gpr .rdx, 258⟩, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  have hk : InRegions (s.rd ++ s.wr) (s.gpr .rdi) (s.gpr .rsi).toNat :=
    ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      Region.contains_self _ _⟩
  have hsep : Mem.Sep (s.gpr .rdi) (s.gpr .rsi).toNat (s.gpr .rdx) 256 :=
    fun x hx hy => hkc x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)
  obtain ⟨tr, t, he, ⟨hpost, hf⟩, hkeep⟩ := WP.keep VG.Proof.Rc4.X86_64.written (VG.Proof.Rc4.X86_64.init_ok s hp hk hsep) (by lit_decide)
  have hframe : Frame s.wr s.mem t.mem := by
    intro x hx
    refine hf x fun hlt => hx ⟨s.gpr .rdx, 258⟩ (by rw [hwr]; exact List.mem_cons_self) ?_
    simp only [Region.Contains]
    omega
  refine ⟨tr, t, he, abiPreserved_of_exec (by lit_decide) he
    (gprPreserved_of hkeep (by decide) hframe ?_), ?_⟩
  · intro r hr
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact hrc
  · unfold VG.Proof.Rc4.X86_64.initX
    dsimp only
    revert hpost
    cases Spec.Rc4.init (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) with
    | ok c => intro hpost; exact ⟨by rw [hpost.1]; rfl, hpost.2⟩
    | error e => cases e; intro hpost; rw [hpost]; rfl

theorem init_ct : ConstantTime isa initX.pre initX.pub init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2

def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 258⟩]

theorem init_verified : Verified target init (Spec.Rc4.initContract abi) :=
  Verified.of_correct VG.Proof.Rc4.X86_64.init_correct VG.Proof.Rc4.X86_64.init_ct (by
    sig_implies [Spec.Rc4.initContract, Spec.Rc4.initSig, Spec.Rc4.initPost, VG.Proof.Rc4.X86_64.initX, abi, argRegs]
      [initSat]
      using VG.Proof.Rc4.X86_64.initSat)

/-! ## The stream function -/

/-- The contract the proof of `vg_rc4_apply` is written against. -/
def applyX : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .rdi, 258⟩
    let data : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [ctx, data] ∧ ctx.Disjoint data ∧ ret.Disjoint ctx ∧
      ret.Disjoint data
  post s s' :=
    let result := update (contextAt s.mem (s.gpr .rdi))
      (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
    contextAt s'.mem (s.gpr .rdi) = result.1 ∧
      bytesAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat = result.2
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧
    [(s₁.mem (s₁.gpr .rdi + 256)).toNat] = [(s₂.mem (s₂.gpr .rdi + 256)).toNat]

theorem apply_correct (s : State) (hs : applyX.pre s) :
    ∃ t s', Exec isa apply s t s' ∧ abiPreserved s s' ∧ applyX.post s s' := by
  obtain ⟨_, hwr, hcd, hrc, hrd⟩ := hs
  have hp : InRegions s.wr (s.gpr .rdi) 258 :=
    ⟨⟨s.gpr .rdi, 258⟩, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  have hd : InRegions s.wr (s.gpr .rsi) (s.gpr .rdx).toNat :=
    ⟨⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩, by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self,
      Region.contains_self _ _⟩
  have hsep : Mem.Sep (s.gpr .rdi) 258 (s.gpr .rsi) (s.gpr .rdx).toNat :=
    fun x hx hy => hcd x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)
  obtain ⟨tr, t, he, ⟨hpost, hf⟩, hkeep⟩ := WP.keep VG.Proof.Rc4.X86_64.written (VG.Proof.Rc4.X86_64.apply_ok s hp hd hsep) (by lit_decide)
  have hframe : Frame s.wr s.mem t.mem := by
    intro x hx
    refine hf x (fun hlt => hx ⟨s.gpr .rdi, 258⟩ (by rw [hwr]; exact List.mem_cons_self) ?_)
      (fun hlt => hx ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
        (by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self) ?_)
    · simp only [Region.Contains]; omega
    · simp only [Region.Contains]; omega
  refine ⟨tr, t, he, abiPreserved_of_exec (by lit_decide) he
    (gprPreserved_of hkeep (by decide) hframe ?_), hpost⟩
  intro r hr
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hrc
  · exact hrd

structure EntryAgree (a b : State) : Prop where
  p : a.gpr .rdi = b.gpr .rdi
  data : a.gpr .rsi = b.gpr .rsi
  len : a.gpr .rdx = b.gpr .rdx
  i : (contextAt a.mem (a.gpr .rdi)).i = (contextAt b.mem (b.gpr .rdi)).i

def ReadValid (s : State) : Prop := InRegions (s.rd ++ s.wr) (s.gpr .rdi) 258

def startBlock : List Instr :=
  [.movzx8 .rcx (at_ .rdi 256), .movzx8 .r8 (at_ .rdi 257), .alu .test .rdx (.reg .rdx)]

/-- The PRGA index `i` is loaded from the context, where the taint analysis
takes it for secret: it may leak, so it is public. -/
theorem apply_start_ct : RelCT isa (fun a b => VG.Proof.Rc4.X86_64.ReadValid a ∧ VG.Proof.Rc4.X86_64.ReadValid b ∧ VG.Proof.Rc4.X86_64.EntryAgree a b)
    (.block VG.Proof.Rc4.X86_64.startBlock) fun a b =>
      VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) a b ∧ a.zf = b.zf := by
  intro a b tr tr' a' b' ⟨hpa, hpb, hab⟩ ea eb
  have hct : RelCT isa (fun a b => VG.Proof.Rc4.X86_64.EntryAgree a b) (.block VG.Proof.Rc4.X86_64.startBlock) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx]) (fun a b h => by
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.p
      · exact h.data
      · exact h.len) (by taint_decide)
  obtain ⟨htrace, -⟩ := hct a b tr tr' a' b' hab ea eb
  obtain ⟨_, u, eu, hau⟩ := VG.Proof.Rc4.X86_64.apply_start a hpa
  obtain ⟨_, rfl⟩ := Exec.det eu ea
  obtain ⟨_, v, ev, hbv⟩ := VG.Proof.Rc4.X86_64.apply_start b hpb
  obtain ⟨_, rfl⟩ := Exec.det ev eb
  obtain ⟨_, _, _, ha0, ha1, ha2, ha12, _, haz⟩ := hau
  obtain ⟨_, _, _, hb0, hb1, hb2, hb12, _, hbz⟩ := hbv
  refine ⟨htrace, Taint.agree_ofRegs fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ha0.trans (hab.p.trans hb0.symm)
    · exact ha1.trans (hab.data.trans hb1.symm)
    · exact ha2.trans (hab.len.trans hb2.symm)
    · rw [ha12, hb12, hab.i]
  · rw [haz, hbz, hab.len]

theorem apply_ct : ConstantTime isa VG.Proof.Rc4.X86_64.ReadValid VG.Proof.Rc4.X86_64.EntryAgree apply := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold apply
  refine RelCT.seq VG.Proof.Rc4.X86_64.apply_start_ct (RelCT.ite ?_ ?_ ?_)
  · intro a b ⟨_, hz⟩
    simp only [eval, hz]
  · exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
      (by taint_decide)
  · exact RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) (fun _ _ h => h.1.1)
      (by taint_decide)

theorem apply_ct' : ConstantTime isa applyX.pre applyX.pub apply := by
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  have hv (s : State) (h : applyX.pre s) : VG.Proof.Rc4.X86_64.ReadValid s :=
    ⟨⟨s.gpr .rdi, 258⟩, List.mem_append_right _ (by rw [h.2.1]; exact List.mem_cons_self),
      Region.contains_self _ _⟩
  exact VG.Proof.Rc4.X86_64.apply_ct s₁ s₂ tr₁ tr₂ t₁ t₂ (hv s₁ h₁) (hv s₂ h₂)
    ⟨hp.1, hp.2.1, hp.2.2.1, BitVec.eq_of_toNat_eq (List.cons.inj hp.2.2.2).1⟩ e₁ e₂

def applySat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 1 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 258⟩, ⟨0x2000, 1⟩]

theorem apply_verified : Verified target apply (Spec.Rc4.applyContract abi) :=
  Verified.of_correct VG.Proof.Rc4.X86_64.apply_correct VG.Proof.Rc4.X86_64.apply_ct' (by
    sig_implies [Spec.Rc4.applyContract, Spec.Rc4.applySig, Spec.Rc4.applyPost, Spec.Rc4.applyLeak,
      VG.Proof.Rc4.X86_64.applyX, abi, argRegs] [applySat]
      using VG.Proof.Rc4.X86_64.applySat)

end VG.Proof.Rc4.X86_64

end
