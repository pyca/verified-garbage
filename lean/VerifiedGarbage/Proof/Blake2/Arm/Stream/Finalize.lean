module

public import VerifiedGarbage.Proof.Blake2.Arm.Stream.Update
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.Range

/-! ### `Blake2.Arm.Stream.Init`, which the modules that import this one used -/

section

/-!
# Streaming BLAKE2 on ARMv7: `init`

`initState` stores the initial hash value as 32-bit words (`word32`, two per
word of BLAKE2b), the first with the parameter block XORed in; for a key,
`keyBlock` zeroes the buffer and copies the key into it. `init` is a leaf
function writing only `r1`–`r3` and `r12`.
-/

@[expose] public section

namespace VG.Proof.Blake2.Arm.Stream.Init

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (N B ws ivWord movImm initState keyBlock init)
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg op2_lsl wp_mov wp_add wp_subs wp_cmp wp_str wp_ldrb wp_strb
  sub_ofNat cmp0 eval_eq eval_ne)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame writeBytes_before)
open VG.Proof.Blake2 (initArm repr_keyBlock stateAt_congr)

/-! ## 32-bit words of the hash value -/

theorem split64 (x : BitVec 64) : x = (x >>> 32).setWidth 32 ++ x.setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  split
  · simp [*]
  · simp [show i - 32 < 32 by omega_arith]; congr 1; omega_arith

theorem readW64_split (m : Mem) (a : Addr) :
    m.readW a 64 = m.readW (a + BitVec.ofNat 64 4) 32 ++ m.readW a 32 := by
  rw [← VG.Proof.Rc2.Word32.readW64_hi, ← VG.Proof.Rc2.Word32.readW64_lo]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  split
  · simp [*]
  · simp [show i - 32 < 32 by omega_arith]; congr 1; omega_arith

def word32 {w : Nat} (h : HashValue w) (j : Nat) : BitVec 32 :=
  ((h.toList.getD (j / (ws w / 4)) 0) >>> (32 * (j % (ws w / 4)))).setWidth 32

theorem ivWord_eq {w : Nat} (P : Params w) (j : Nat) : ivWord P j = word32 P.IV j := rfl

theorem word32_32 (h : HashValue 32) {k : Nat} (hk : k < 8) : word32 h k = h[k] := by
  simp [word32, ws, List.getD_eq_getElem?_getD, hk, Nat.mod_one]

theorem word32_64 (h : HashValue 64) {k : Nat} (hk : k < 8) :
    word32 h (2 * k + 1) ++ word32 h (2 * k) = h[k] := by
  simp only [word32, ws, show 64 / 8 / 4 = 2 from rfl, show (2 * k + 1) / 2 = k by omega_arith,
    show (2 * k + 1) % 2 = 1 by omega_arith, show 2 * k / 2 = k by omega_arith, show 2 * k % 2 = 0 by omega_arith]
  simp [List.getD_eq_getElem?_getD, hk]
  exact (split64 _).symm

theorem c_lt {nn kk : Nat} (hn : nn < 256) (hk : kk < 256) :
    ((16842752#64) ^^^ (BitVec.ofNat 64 kk <<< 8) ^^^ BitVec.ofNat 64 nn).toNat < 2 ^ 32 := by
  simp only [BitVec.toNat_xor, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (by decide) ?_) (by omega_arith)
  rw [Nat.shiftLeft_eq]; omega_arith

theorem word32_init {w : Nat} (hw : w = 32 ∨ w = 64) (P : Params w) {nn kk : Nat} (hn : nn < 256)
    (hk : kk < 256) {j : Nat} (hj : j < 8 * (ws w / 4)) :
    word32 (Spec.Blake2.init P nn kk) j = if j = 0 then
      word32 P.IV 0 ^^^ 0x01010000 ^^^ (BitVec.ofNat 32 kk <<< 8) ^^^ BitVec.ofNat 32 nn else word32 P.IV j := by
  rcases hw with rfl | rfl
  · have hj' : j < 8 := hj
    rw [word32_32 _ hj', Spec.Blake2.init, Vector.getElem_set]
    split
    · subst_vars; simp [word32_32 _ (show 0 < 8 by decide)]
    · rename_i h; simp [Ne.symm h, word32_32 _ hj']
  · have hj' : j < 16 := hj
    simp only [word32, ws, show 64 / 8 / 4 = 2 from rfl, Spec.Blake2.init, Vector.toList_set]
    obtain hl : P.IV.toList.length = 8 := by simp
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ 2 ≤ j) with rfl | rfl | h2
    · simp [List.getD_eq_getElem?_getD, BitVec.setWidth_xor]
    · simp [List.getD_eq_getElem?_getD]
      obtain hc : ((16842752#64) ^^^ (BitVec.ofNat 64 kk <<< 8) ^^^ BitVec.ofNat 64 nn) >>> 32 = 0 := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (c_lt hn hk)]
        rfl
      rw [BitVec.xor_assoc, BitVec.xor_assoc, ← BitVec.xor_assoc (16842752#64), BitVec.ushiftRight_xor_distrib, hc]
      simp
    · have hne : j / 2 ≠ 0 := by omega_arith
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hne), show j ≠ 0 by omega_arith]

theorem stateAt_of_words {w : Nat} (hw : w = 32 ∨ w = 64) {m : Mem} {p : Addr} {h : HashValue w}
    (H : ∀ j < 8 * (ws w / 4), m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = word32 h j) :
    stateAt w m p = h := by
  rcases hw with rfl | rfl
  · apply Vector.ext; intro k hk
    simp only [stateAt, Vector.getElem_ofFn]
    rw [show 32 / 8 * k = 4 * k by omega_arith, H k (by simp [ws]; omega_arith), word32_32 _ hk]
  · apply Vector.ext; intro k hk
    simp only [stateAt, Vector.getElem_ofFn]
    rw [readW64_split, Offset.add_add, show 64 / 8 * k = 4 * (2 * k) by omega_arith,
      show 4 * (2 * k) + 4 = 4 * (2 * k + 1) by omega_arith, H _ (by simp [ws]; omega_arith), H _ (by simp [ws]; omega_arith),
      word32_64 _ hk]

/-! ## The initial hash value -/

section
variable {w : Nat} (P : Params w)

/-- The store of IV word `j + 1`. -/
def ivStep (j : Nat) : List Instr := movImm (ivWord P (j + 1)) ++ [.str .r12 .r0 (4 * (j + 1))]

theorem initState_eq : initState P = (List.range (N w / 4 - 1)).flatMap (ivStep P) ++
    (movImm (ivWord P 0 ^^^ 0x01010000) ++ ([.dp .eor .r12 .r12 (.shifted .r3 .lsl 8),
      .dp .eor .r12 .r12 (.reg .r1), .str .r12 .r0 0] : List Instr)) := by
  rw [initState, List.append_assoc]
  rfl

/-- After storing IV words `1 … n`. -/
structure IvInv (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr (s₀.gpr .r0), bufOff w⟩] s₀.mem s.mem
  words : ∀ j < n, s.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (j + 1))) 32 = ivWord P (j + 1)

variable {P}

theorem wp_movImm {s : State} {v : BitVec 32} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' .r12 v → WP isa (.block rest) s' Q) :
    WP isa (.block (movImm v ++ rest)) s Q := by
  simp only [movImm, List.cons_append, List.nil_append]
  refine wp_movw fun s₁ u₁ => wp_movt fun s₂ u₂ => k s₂ ⟨?_, fun r h => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₂.gpr, u₁.gpr, movw_movt]
  · rw [u₂.other r h, u₁.other r h]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]
  · rw [u₂.sp, u₁.sp]

theorem iv_step (hw : w = 32 ∨ w = 64) {s₀ : State} (hfit : (s₀.gpr .r0).toNat + bufOff w ≤ 2 ^ 32)
    (hwr : ∀ a n, InRegions [⟨State.addr (s₀.gpr .r0), bufOff w⟩] a n → InRegions s₀.wr a n)
    (k : Nat) (s : State) (hk : k < bufOff w / 4 - 1) (h : IvInv P s₀ k s) :
    WP isa (.block (ivStep P k)) s (IvInv P s₀ (k + 1)) := by
  obtain hN : bufOff w ≤ 64 := by rcases hw with rfl | rfl <;> decide
  obtain hin : (⟨State.addr (s₀.gpr .r0), bufOff w⟩ : Region).Contains
      (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (k + 1))) 4 :=
    contains_off _ (by omega_arith) (by omega_arith)
  unfold ivStep
  refine wp_movImm fun s₁ u₁ => wp_str (a := State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (k + 1)))
    (by omega_arith) (by rw [u₁.other _ (by decide), h.gpr _ (by decide), addr_add (by omega_arith)])
    (by rw [u₁.wr, h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩) fun s₂ g₂ => WP.block_nil ?_
  refine ⟨fun r hr => by rw [g₂.gpr, u₁.other r hr, h.gpr r hr], by rw [g₂.rd, u₁.rd, h.rd],
    by rw [g₂.wr, u₁.wr, h.wr], by rw [g₂.sp, u₁.sp, h.sp], ?_, fun j hj => ?_⟩
  · rw [g₂.mem, u₁.mem]; exact h.frame.writeW (List.mem_singleton_self _) _ hin
  · rw [g₂.mem, u₁.gpr, u₁.mem]
    by_cases e : j = k
    · subst e; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact h.words j (by omega_arith)

/-- The state after `initState`. -/
structure StateOk (s₀ : State) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr (s₀.gpr .r0), bufOff w⟩] s₀.mem s.mem
  state : stateAt w s.mem (State.addr (s₀.gpr .r0)) =
    Spec.Blake2.init P (s₀.gpr .r1).toNat (s₀.gpr .r3).toNat

theorem initState_ok (hw : w = 32 ∨ w = 64) {s₀ : State} (hfit : (s₀.gpr .r0).toNat + bufOff w ≤ 2 ^ 32)
    (hwr : ∀ a n, InRegions [⟨State.addr (s₀.gpr .r0), bufOff w⟩] a n → InRegions s₀.wr a n)
    (hn : (s₀.gpr .r1).toNat < 256) (hk : (s₀.gpr .r3).toNat < 256) :
    WP isa (.block (initState P)) s₀ (StateOk (P := P) s₀) := by
  obtain hN : bufOff w ≤ 64 ∧ 8 ≤ bufOff w / 4 ∧ N w / 4 = bufOff w / 4 := by
    rcases hw with rfl | rfl <;> decide
  rw [initState_eq, WP.block_append_iff, hN.2.2]
  refine WP.mono (wp_range_flatMap (M := isa) (IvInv P s₀) (fun k s hk h => iv_step hw hfit hwr k s hk h)
    (bufOff w / 4 - 1) (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega_arith)⟩) fun s₇ h₇ => ?_
  obtain hin : (⟨State.addr (s₀.gpr .r0), bufOff w⟩ : Region).Contains (State.addr (s₀.gpr .r0)) 4 :=
    by simp [Region.Contains]; omega_arith
  refine wp_movImm fun s₁ u₁ => wp_eor (op2_lsl (by decide)) fun s₂ u₂ => wp_eor (op2_reg _ _) fun s₃ u₃ =>
    wp_str (a := State.addr (s₀.gpr .r0)) (by decide) ?_ ?_ fun s₄ g₄ => WP.block_nil ?_
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h₇.gpr _ (by decide),
      BitVec.add_zero]
  · rw [u₃.wr, u₂.wr, u₁.wr, h₇.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩
  obtain g : ∀ r, r ≠ .r12 → s₄.gpr r = s₀.gpr r := fun r h1 => by
    rw [g₄.gpr, u₃.other r h1, u₂.other r h1, u₁.other r h1, h₇.gpr r h1]
  obtain hv : s₃.gpr .r12 = word32 (Spec.Blake2.init P (s₀.gpr .r1).toNat (s₀.gpr .r3).toNat) 0 := by
    rw [word32_init hw P hn hk (by rcases hw with rfl | rfl <;> decide)]
    simp only [↓reduceIte]
    rw [u₃.gpr, u₂.gpr,
      u₁.gpr, u₂.other .r1 (by decide), u₁.other .r1 (by decide), u₁.other .r3 (by decide),
      h₇.gpr .r1 (by decide), h₇.gpr .r3 (by decide), BitVec.ofNat_toNat, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.setWidth_eq, ivWord_eq]
    rfl
  obtain hm : s₄.mem = s₇.mem.writeW (State.addr (s₀.gpr .r0)) (s₃.gpr .r12) := by
    rw [g₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨g, by rw [g₄.rd, u₃.rd, u₂.rd, u₁.rd, h₇.rd], by rw [g₄.wr, u₃.wr, u₂.wr, u₁.wr, h₇.wr],
    by rw [g₄.sp, u₃.sp, u₂.sp, u₁.sp, h₇.sp], ?_, ?_⟩
  · rw [hm]; exact h₇.frame.writeW (List.mem_singleton_self _) _ hin
  · refine stateAt_of_words hw fun j hj => ?_
    rw [hm]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [Nat.mul_zero, BitVec.add_zero, Mem.readW_writeW_self32, hv]
    · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega_arith⟩
      have hj' : j + 1 < 8 * (ws w / 4) := hj
      obtain e8 : 8 * (ws w / 4) = bufOff w / 4 := by rcases hw with rfl | rfl <;> decide
      obtain hs : Mem.Sep (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (j + 1))) (32 / 8)
          (State.addr (s₀.gpr .r0)) (32 / 8) := fun x h1 h2 =>
        Offset.sep_base (State.addr (s₀.gpr .r0)) (n := 4) (e := 4 * (j + 1)) (k := 4) (by omega_arith) (by omega_arith)
          x h2 h1
      rw [Mem.readW_writeW_sep hs (by decide), h₇.words j (by omega_arith), word32_init hw P hn hk hj']
      simp only [Nat.add_one_ne_zero, ite_false, ivWord_eq]

end

/-! ## The key block -/

section
variable {w : Nat}

/-- After zeroing the first `n` words of the buffer, from `s₁`. -/
structure ZInv (s₁ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₁.gpr
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  sp : s.sp = s₁.sp
  frame : Frame [⟨State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w), blockBytes w⟩] s₁.mem s.mem
  words : ∀ j < n, s.mem.readW (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 (4 * j)) 32 = 0

theorem zero_all (hw : w = 32 ∨ w = 64) {s₁ : State}
    (hfit : (s₁.gpr .r0).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32) (h12 : s₁.gpr .r12 = 0)
    (hwr : ∀ a n, InRegions [⟨State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w), blockBytes w⟩] a n →
      InRegions s₁.wr a n) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, ZInv (w := w) s₁ (blockBytes w / 4) s → WP isa (.block rest) s Q) :
    WP isa (.block ((List.range (B w / 4)).map (fun j => Instr.str .r12 .r0 (N w + 4 * j)) ++ rest)) s₁ Q := by
  obtain hs : bufOff w ≤ 64 ∧ blockBytes w ≤ 128 ∧ blockBytes w % 4 = 0 := by rcases hw with rfl | rfl <;> decide
  rw [WP.block_append_iff]
  refine WP.mono ?_ k
  rw [B_eq]
  suffices h : ∀ n ≤ blockBytes w / 4, WP isa (.block ((List.range n).map
      (fun j => Instr.str .r12 .r0 (N w + 4 * j)))) s₁ (ZInv (w := w) s₁ n) from h _ (Nat.le_refl _)
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega_arith)⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega_arith)) fun t h => ?_
    simp only [List.map_cons, List.map_nil]
    obtain hin : (⟨State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w), blockBytes w⟩ : Region).Contains
        (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 (4 * n)) 4 :=
      contains_off _ (by omega_arith) (by omega_arith)
    refine wp_str (a := State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 (4 * n))
      (by rw [N_eq]; omega_arith) (by rw [h.gpr, addr_add (by rw [N_eq]; omega_arith), N_eq, Offset.add_add])
      (by rw [h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩) fun t₁ g₁ => WP.block_nil ?_
    refine ⟨by rw [g₁.gpr, h.gpr], by rw [g₁.rd, h.rd], by rw [g₁.wr, h.wr], by rw [g₁.sp, h.sp], ?_,
      fun j hj => ?_⟩
    · rw [g₁.mem]; exact h.frame.writeW (List.mem_singleton_self _) _ hin
    · rw [g₁.mem, h.gpr, h12]
      by_cases e : j = n
      · subst e; exact Mem.readW_writeW_self32 _ _ _
      · rw [Offset.add_add, Offset.add_add,
          Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), ← Offset.add_add]
        exact h.words j (by omega_arith)

/-- The key loop's state after `j` of `k` bytes, from `s₂`. -/
structure KI (s₂ : State) (st key : BitVec 32) (k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  r1 : s.gpr .r1 = st + BitVec.ofNat 32 (bufOff w) + BitVec.ofNat 32 j
  r2 : s.gpr .r2 = key + BitVec.ofNat 32 j
  r3 : s.gpr .r3 = BitVec.ofNat 32 (k - j)
  other : ∀ x, x ≠ .r1 → x ≠ .r2 → x ≠ .r3 → x ≠ .r12 → s.gpr x = s₂.gpr x
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  mem : s.mem = writeBytes s₂.mem (State.addr st + BitVec.ofNat 64 (bufOff w))
    ((bytesAt s₂.mem (State.addr key) k).take j)

theorem keyLoop_ok {s₂ : State} {st key : BitVec 32} {k : Nat} (hk : 1 ≤ k) (hkb : k ≤ blockBytes w)
    (hfit : st.toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32) (hkf : key.toNat + k ≤ 2 ^ 32)
    (h : KI (w := w) s₂ st key k 0 s₂)
    (hsrc : ∀ i < k, InRegions (s₂.rd ++ s₂.wr) (State.addr key + BitVec.ofNat 64 i) 1)
    (hdst : ∀ i < k, InRegions s₂.wr (State.addr st + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨State.addr key, k⟩ ⟨State.addr st + BitVec.ofNat 64 (bufOff w), k⟩) :
    WP isa (.loop (.block [.ldrb .r12 .r2 0, .strb .r12 .r1 0, .dp .add .r2 .r2 (.imm 1),
      .dp .add .r1 .r1 (.imm 1), .subs .r3 .r3 (.imm 1)]) .ne) s₂ (KI (w := w) s₂ st key k k) := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧ KI (w := w) s₂ st key k j s) ?_ k s₂
    ⟨0, by omega_arith, by omega_arith, h⟩
  rintro n s ⟨j, rfl, hj, h⟩
  obtain hbyte : s.mem (State.addr key + BitVec.ofNat 64 j) = s₂.mem (State.addr key + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (writeBytes_frame s₂.mem _ _ (contains_prefix (k := k) _ (by simp; omega_arith))).bytes
      (R := ⟨State.addr key, k⟩) (by simpa using hd) (by show k ≤ 2 ^ 64; omega_arith) hj
  refine wp_ldrb (a := State.addr key + BitVec.ofNat 64 j) (by decide)
    (by rw [h.r2, BitVec.add_zero, addr_add (by omega_arith)]) (by rw [h.rd, h.wr]; exact hsrc j hj) fun s₁ u₁ => ?_
  obtain ht : (st + BitVec.ofNat 32 (bufOff w)).toNat = st.toNat + bufOff w := toNat_add_ofNat (by omega_arith)
  refine wp_strb (a := State.addr st + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 j) (by decide)
    (by rw [u₁.other _ (by decide), h.r1, BitVec.add_zero, addr_add (by omega_arith), addr_add (by omega_arith)])
    (by rw [u₁.wr, h.wr]; exact hdst j hj) fun s₃ g₃ => ?_
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ => WP.block_nil ?_
  obtain hr3 : s₆.gpr .r3 = BitVec.ofNat 32 (k - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₁.other _ (by decide), h.r3,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith), Nat.sub_sub]
  obtain hI : KI (w := w) s₂ st key k (j + 1) s₆ := by
    refine ⟨by omega_arith, ?_, ?_, hr3, fun x h1 h2 h3 h4 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₁.other _ (by decide), h.r1,
        BitVec.add_assoc (st + _), show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₁.other _ (by decide), h.r2,
        BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
    · rw [u₆.other x h3, u₅.other x h1, u₄.other x h2, g₃.gpr, u₁.other x h4, h.other x h1 h2 h3 h4]
    · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₁.rd, h.rd]
    · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₁.wr, h.wr]
    · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₁.sp, h.sp]
    · have hj' : j < (bytesAt s₂.mem (State.addr key) k).length := by rw [bytesAt_length]; omega_arith
      obtain hl : (List.take j (bytesAt s₂.mem (State.addr key) k)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₁.mem, u₁.gpr, hbyte, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some, writeBytes_snoc _ _ _ _ (by rw [hl]; omega_arith), hl,
        setWidth_byte]
      congr 1
      simp [bytesAt]
  obtain hz : isa.eval .ne s₆ = some (decide (k - (j + 1) ≠ 0)) :=
    ne_iff s₆ (by rw [z₆, ← u₆.gpr, hr3]) (by omega_arith)
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [hz]; simp; omega_arith, hjk ▸ hI⟩
  · exact .inr ⟨by rw [hz]; simp; omega_arith, k - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, hI⟩

theorem zero_byte {m : Mem} {a : Addr} (h : m.readW a 32 = 0) {j : Nat} (hj : j < 4) :
    m (a + BitVec.ofNat 64 j) = 0 := by
  rw [← Mem.extractLsb'_read m a hj]
  have : m.read a 4 = 0 := by simpa [Mem.readW] using h
  rw [this]; simp

theorem ZInv.byte {s₁ s : State} (h : ZInv (w := w) s₁ (blockBytes w / 4) s) (hb : blockBytes w % 4 = 0)
    {i : Nat} (hi : i < blockBytes w) :
    s.mem (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 i) = 0 := by
  obtain e : i = 4 * (i / 4) + i % 4 := (Nat.div_add_mod i 4).symm
  rw [e, ← Offset.add_add (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w)) (4 * (i / 4)) (i % 4)]
  exact zero_byte (h.words _ (by omega_arith)) (Nat.mod_lt _ (by decide))

theorem bytesAt_writeBytes_pad {m : Mem} {q : Addr} {xs : List Byte} {n : Nat} (hl : xs.length ≤ n)
    (hn : n < 2 ^ 64) (hz : ∀ i < n, xs.length ≤ i → m (q + BitVec.ofNat 64 i) = 0) :
    bytesAt (writeBytes m q xs) q n = xs ++ List.replicate (n - xs.length) 0 := by
  apply List.ext_getElem (by simp only [bytesAt_length, List.length_append, List.length_replicate]; omega_arith)
  intro i h1 _
  rw [bytesAt_length] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes, Offset.add_sub_cancel_left,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_arith)]
  by_cases hi : i < xs.length
  · simp only [hi, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
      List.getElem_append_left hi]
  · simp only [hi, ↓reduceIte, hz i h1 (by omega_arith), List.getElem_append_right (Nat.le_of_not_lt hi),
      List.getElem_replicate]

theorem contains_widen {p a : Addr} {d k n : Nat} (hd : d < 2 ^ 64)
    (h : (⟨p + BitVec.ofNat 64 d, k⟩ : Region).Contains a n) : (⟨p, d + k⟩ : Region).Contains a n := by
  unfold Region.Contains at *
  have : (a - p).toNat ≤ (a - (p + BitVec.ofNat 64 d)).toNat + d := by
    rw [← Offset.sub_add_sub_cancel a (p + BitVec.ofNat 64 d) p, BitVec.toNat_add, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
    exact Nat.mod_le _ _
  simp only at *
  omega_arith

theorem keyBlock_ok (hw : w = 32 ∨ w = 64) {s : State}
    (hfit : (s.gpr .r0).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32)
    (hkf : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32)
    (hk1 : (s.gpr .r3).toNat ≠ 0) (hkb : (s.gpr .r3).toNat ≤ blockBytes w)
    (hrd : s.rd = [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩])
    (hwr : s.wr = [⟨State.addr (s.gpr .r0), bufOff w + blockBytes w⟩])
    (hd : Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
      ⟨State.addr (s.gpr .r0), bufOff w + blockBytes w⟩) :
    WP isa (Impl.Blake2.Arm.Stream.keyBlock (w := w)) s fun s' =>
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      (∀ i < bufOff w, s'.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 i) =
        s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 i)) ∧
      bytesAt s'.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (bufOff w)) (blockBytes w) =
        bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat ++
          List.replicate (blockBytes w - (s.gpr .r3).toNat) 0 := by
  obtain hs : bufOff w ≤ 64 ∧ blockBytes w ≤ 128 ∧ blockBytes w % 4 = 0 ∧
      encodable (BitVec.ofNat 32 (N w)) = true := by
    rcases hw with rfl | rfl <;> decide
  obtain hsub : Region.Sub ⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 (bufOff w), blockBytes w⟩
      ⟨State.addr (s.gpr .r0), bufOff w + blockBytes w⟩ := Offset.sub_base _ (by omega_arith)
  obtain hdb := hd.sub_right hsub
  unfold Impl.Blake2.Arm.Stream.keyBlock
  refine WP.seq ?_
  rw [List.cons_append]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  obtain e0 : s₁.gpr .r0 = s.gpr .r0 := u₁.other _ (by decide)
  refine zero_all hw (by rw [e0]; omega_arith) u₁.gpr (fun a n h => ?_) fun s₂ z₂ => ?_
  · obtain ⟨R, hR, hc⟩ := h
    simp only [List.mem_singleton] at hR; subst hR
    rw [u₁.wr, hwr]
    exact ⟨_, List.mem_singleton_self _, contains_widen (by omega_arith) (by rw [e0] at hc; exact hc)⟩
  refine wp_add (op2_imm hs.2.2.2) fun s₃ u₃ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .r1 → r ≠ .r12 → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other r h1, z₂.gpr, u₁.other r h2]
  have hm₃ : s₃.mem = s₂.mem := u₃.mem
  obtain hrd₃ : s₃.rd = s.rd := by rw [u₃.rd, z₂.rd, u₁.rd]
  obtain hwr₃ : s₃.wr = s.wr := by rw [u₃.wr, z₂.wr, u₁.wr]
  obtain hk : (s.gpr .r2) + BitVec.ofNat 32 0 = s.gpr .r2 := BitVec.add_zero _
  obtain hI : KI (w := w) s₃ (s.gpr .r0) (s.gpr .r2) (s.gpr .r3).toNat 0 s₃ :=
    ⟨Nat.zero_le _, by rw [u₃.gpr, z₂.gpr, e0, N_eq]; exact (BitVec.add_zero _).symm,
      by rw [g _ (by decide) (by decide), hk],
      by rw [g _ (by decide) (by decide), Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl, by rw [List.take_zero, writeBytes_nil]⟩
  obtain hdk : Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
      ⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 (bufOff w), (s.gpr .r3).toNat⟩ :=
    hdb.sub_right (Offset.sub (e := bufOff w) (d := bufOff w) _ (Nat.le_refl _) (by omega_arith)) |>.sub_right
      (fun _ h => h)
  refine WP.mono (keyLoop_ok (Nat.one_le_iff_ne_zero.mpr hk1) hkb hfit (by omega_arith) hI
    (fun i hi => ⟨_, by rw [hrd₃, hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun i hi => ⟨_, by rw [hwr₃, hwr]; exact List.mem_singleton_self _,
      by rw [Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩) hdk) fun s' h => ?_
  obtain hfr : Frame [⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 (bufOff w), blockBytes w⟩] s.mem s₂.mem := by
    rw [← u₁.mem, ← e0]; exact z₂.frame
  obtain hkey : bytesAt s₃.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat := by
    rw [hm₃]
    exact bytesAt_congr fun i hi => hfr.bytes (R := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hdb) (by dsimp only; omega_arith) hi
  obtain hlen : (bytesAt s₃.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat).length = (s.gpr .r3).toNat :=
    bytesAt_length _ _ _
  have hmem := h.mem
  rw [List.take_of_length_le (Nat.le_of_eq hlen)] at hmem
  refine ⟨fun r h1 h2 h3 h4 => by rw [h.other r h1 h2 h3 h4, g r h1 h4], by rw [h.sp, u₃.sp, z₂.sp, u₁.sp],
    fun i hi => ?_, ?_⟩
  · rw [hmem, writeBytes_before _ _ _ hi (by rw [hlen]; omega_arith), hm₃]
    exact hfr.bytes (R := ⟨State.addr (s.gpr .r0), bufOff w⟩)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base _ (Nat.le_refl _) (by omega_arith)).symm) (by dsimp only; omega_arith) hi
  · rw [hmem, bytesAt_writeBytes_pad (by omega_arith) (by omega_arith) fun i hi _ => ?_, hlen, hkey]
    rw [hm₃, ← e0]; exact z₂.byte hs.2.2.1 hi

end

/-! ## `init` -/

section
variable {w : Nat} {P : Params w}

theorem correct (hP : Ok P) {s₀ : State} (hp : (initArm P).pre s₀) :
    WP isa (Impl.Blake2.Arm.Stream.init P) s₀ fun s' => abiPreserved s₀ s' ∧ (initArm P).post s₀ s' := by
  obtain ⟨hrd, hwr, hd, hfit, hkf, -, hn2, hkm⟩ := hp
  have hw : w = 32 ∨ w = 64 := hP.w.symm
  have hmax : P.maxBytes ≤ blockBytes w := hP.max
  obtain hbb : blockBytes w ≤ 128 := by rcases hw with rfl | rfl <;> decide
  obtain hsubSt : Region.Sub ⟨State.addr (s₀.gpr .r0), bufOff w⟩
      ⟨State.addr (s₀.gpr .r0), bufOff w + blockBytes w⟩ := fun a h => by
    unfold Region.Contains at h ⊢; dsimp only at h ⊢; omega_arith
  obtain hpres : ∀ r ∈ preserved, r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by decide
  unfold Impl.Blake2.Arm.Stream.init
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (initState_ok hw (by omega_arith) (fun a n h => ?_) (by omega_arith) (by omega_arith)) fun s₁ h₁ => ?_
  · obtain ⟨R, hR, hc⟩ := h
    simp only [List.mem_singleton] at hR; subst hR
    rw [hwr]
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    unfold Region.Contains at hc ⊢; dsimp only at hc ⊢; omega_arith
  refine wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ => WP.block_nil ?_
  obtain g₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [f₂.gpr, h₁.gpr r hr]
  have hm₂ : s₂.mem = s₁.mem := f₂.mem
  obtain hkey : bytesAt s₂.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat =
      bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat := by
    rw [hm₂]
    exact bytesAt_congr fun i hi => h₁.frame.bytes (R := ⟨State.addr (s₀.gpr .r2), (s₀.gpr .r3).toNat⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd.sub_right hsubSt)
      (by dsimp only; omega_arith) hi
  obtain e3 : s₀.gpr .r3 = BitVec.ofNat 32 (s₀.gpr .r3).toNat := by simp
  obtain hz : isa.eval .eq s₂ = some (decide ((s₀.gpr .r3).toNat = 0)) := by
    show VG.Arm.eval .eq s₂ = _
    rw [eval_eq, z₂, h₁.gpr _ (by decide), e3, cmp0 (BitVec.isLt _), ← e3]
  refine WP.ite _ hz (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine ⟨⟨fun r hr => g₂ r (hpres r hr).2.2.2, by rw [f₂.sp, h₁.sp]⟩, ?_⟩
    refine repr_keyBlock P hP.pos (by rw [bytesAt_length]; omega_arith) (by rw [hm₂]; exact h₁.state) fun h => ?_
    rw [bytesAt_length] at h; exact absurd hb h
  · simp only [decide_eq_false_iff_not] at hb
    obtain e0 := g₂ .r0 (by decide)
    obtain e2 := g₂ .r2 (by decide)
    obtain e3' := g₂ .r3 (by decide)
    refine WP.mono (keyBlock_ok hw (by rw [e0]; omega_arith) (by rw [e2, e3']; omega_arith) (by rw [e3']; exact hb)
      (by rw [e3']; omega_arith) (by rw [f₂.rd, h₁.rd, hrd, e2, e3']) (by rw [f₂.wr, h₁.wr, hwr, e0])
      (by rw [e0, e2, e3']; exact hd)) fun s' ⟨hg, hsp, hst, hbytes⟩ => ?_
    refine ⟨⟨fun r hr => by
        obtain ⟨h1, h2, h3, h4⟩ := hpres r hr
        rw [hg r h1 h2 h3 h4, g₂ r h4], by rw [hsp, f₂.sp, h₁.sp]⟩, ?_⟩
    rw [e0, e2, e3', hkey] at hbytes
    rw [e0] at hst
    refine repr_keyBlock P hP.pos (by rw [bytesAt_length]; omega_arith) ?_ fun _ => by rw [bytesAt_length]; exact hbytes
    rw [stateAt_congr hst, hm₂]; exact h₁.state

end

end VG.Proof.Blake2.Arm.Stream.Init

end

end

/-!
# Streaming BLAKE2 on ARMv7: `finalize`

The functional correctness of `finalize`, for either word size and any correct
compression function (`CalleeOk`), piece by piece, as for `update`: the
prologue, which zeroes the rest of the buffer and sets up the call (`pro_ok`),
the call (`call_ok'`) and the end, which copies the hash value to `out`
(`end_ok`).
-/

@[expose] public section

namespace VG.Proof.Blake2.Arm.Stream.Finalize

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (N B lbb saved save restore call zeroLoop finalizePro finalizeEnd finalize)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_sub wp_subs wp_cmp wp_ldr wp_str
  wp_ldrSp sub_ofNat cmp0 eval_eq eval_ne)
open VG.WriteBytes (writeBytes writeBytes_before writeBytes_frame)
open VG.Proof.Blake2 (bufLen bufLen_le bufLen_le_self final_eq stateAt_congr bytesAt_congr bytesAt_add
  bytesAt_state bytesAt_words wordBytes_readW finalizeArm countArm)
open VG.Proof.Blake2.Arm.Stream.Update (bufLen_ok)

variable {w : Nat} {P : Params w}

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev stA : Addr := State.addr (st s₀)
abbrev out : BitVec 32 := stackArg s₀ 0
abbrev outA : Addr := State.addr (out s₀)
abbrev scr : BitVec 32 := stackArg s₀ 1
abbrev scA : Addr := State.addr (scr s₀)
abbrev cnt : Nat := (countArm s₀).toNat
abbrev stR (w : Nat) : Region := ⟨stA s₀, bufOff w + blockBytes w⟩
abbrev outR (w : Nat) : Region := ⟨outA s₀, bufOff w⟩
abbrev scR : Region := ⟨scA s₀, 576⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩
/-- The buffer. -/
abbrev buf (w : Nat) : Addr := stA s₀ + BitVec.ofNat 64 (bufOff w)

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [stR s₀ w, outR s₀ w, scR s₀]
  st_out : (stR s₀ w).Disjoint (outR s₀ w)
  st_scr : (stR s₀ w).Disjoint (scR s₀)
  out_scr : (outR s₀ w).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀ w)
  a_out : (argR s₀).Disjoint (outR s₀ w)
  a_scr : (argR s₀).Disjoint (scR s₀)
  w_st : (below s₀).Disjoint (stR s₀ w)
  w_out : (below s₀).Disjoint (outR s₀ w)
  w_scr : (below s₀).Disjoint (scR s₀)
  st_fit : (st s₀).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32
  out_fit : (out s₀).toNat + bufOff w ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 576 ≤ 2 ^ 32
  sp16 : 16 ≤ s₀.sp.toNat
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : (finalizeArm P).pre s₀) : Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem cnt_lt (s₀ : State) : cnt s₀ < 2 ^ 64 := (countArm s₀).isLt

/-- What holds throughout. -/
structure Common (w : Nat) (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = st s₀
  r5 : s.gpr .r5 = scr s₀
  r6 : s.gpr .r6 = out s₀
  cn : s.gpr .r10 ++ s.gpr .r9 = BitVec.ofNat 64 (cnt s₀)
  frame : Frame [stR s₀ w, scR s₀, below s₀] s₀.mem s.mem
  saved : Saved (scA s₀) s₀.gpr s.mem

/-- The registers `Common` is about. -/
abbrev commonRegs : List Reg := [.r4, .r5, .r6, .r9, .r10]

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : Common w s₀ s)
    (hg : ∀ r ∈ commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common w s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  r4 := by rw [hg _ (by simp)]; exact h.r4
  r5 := by rw [hg _ (by simp)]; exact h.r5
  r6 := by rw [hg _ (by simp)]; exact h.r6
  cn := by rw [hg .r9 (by simp), hg .r10 (by simp)]; exact h.cn
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Common.of_upd {s₀ : State} {s s' : State} (h : Common w s₀ s) {d : Reg} {v : BitVec 32}
    (u : Upd s s' d v) (hd : d ∉ commonRegs := by decide) : Common w s₀ s' :=
  h.of_gpr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem u.rd u.wr u.sp

theorem saved_frame {s₀ : State} (hp : Pre w s₀) {m m' : Mem} (h : Saved (scA s₀) s₀.gpr m)
    (hf : Frame [stR s₀ w, ⟨scA s₀, 512⟩, below s₀] m m') : Saved (scA s₀) s₀.gpr m' := by
  have := hp.scr_fit
  refine h.frame saved_slots hf fun r' hr' => ?_
  obtain e : Region.Sub ⟨scA s₀ + BitVec.ofNat 64 512, 548 - 512⟩ (scR s₀) := Offset.sub_base _ (by omega_using [])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · exact hp.st_scr.symm.sub_left e
  · exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])
  · exact hp.w_scr.symm.sub_left e

/-! ## The prologue -/

abbrev prologue : List Instr :=
  [.ldrSp .r12 4] ++ save .r12 ++ [.mov .r4 (.reg .r0), .mov .r5 (.reg .r12), .ldrSp .r6 0,
    .mov .r9 (.reg .r2), .mov .r10 (.reg .r3)]

theorem argAddr_eq {s₀ : State} (hp : Pre w s₀) {k : Nat} (hk : k < 2) :
    stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega_using [hk, this])]
  simp

theorem arg_in {s₀ : State} (hp : Pre w s₀) {k : Nat} (hk : k < 2) :
    InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 :=
  ⟨argR s₀, by simp [hp.rd], by rw [argAddr_eq hp hk]; exact contains_off _ (by omega_using [hk]) (by omega_using [])⟩

theorem arg_sub {s₀ : State} (hp : Pre w s₀) {k : Nat} (hk : k < 2) :
    Region.Sub ⟨stackArgAddr s₀ k, 4⟩ (argR s₀) := by
  rw [argAddr_eq hp hk]; exact Offset.sub_base _ (by omega_using [hk])

theorem prologue_ok {s₀ : State} (hp : Pre w s₀) :
    WP isa (.block prologue) s₀ fun s => Common w s₀ s ∧
      ∀ i < bufOff w + blockBytes w, s.mem (stA s₀ + BitVec.ofNat 64 i) = s₀.mem (stA s₀ + BitVec.ofNat 64 i) := by
  have hsc := hp.scr_fit
  simp only [prologue, List.cons_append, List.nil_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (arg_in hp (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := u₁.gpr
  refine save_ok (by rw [h12]; omega_using [hsc]) (fun d hd₁ hd₂ => ⟨scR s₀, by simp [u₁.wr, hp.wr],
    by rw [h12]; exact contains_off _ (by omega_using [hd₂]) (by omega_using [])⟩) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  obtain hframe : Frame [scR s₀] s₀.mem s₂.mem := by
    rw [m₂, u₁.mem, h12]; exact saveMem_frame _ _ _
  obtain harg : ∀ k, k < 2 → s₂.mem.readW (stackArgAddr s₀ k) 32 = stackArg s₀ k := fun k hk =>
    hframe.readW (Region.contains_self _ _) (by simpa using (hp.a_scr.sub_left (arg_sub hp hk))) (by decide)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide)
    (by rw [u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact arg_in hp (by decide)) fun s₅ u₅ => ?_
  refine wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  obtain mm : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  refine ⟨⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp], ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, g₂, u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), g₂, h12]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, harg 0 (by decide)]
  · have h9 : s₇.gpr .r9 = s₀.gpr .r2 := by
      rw [u₇.other .r9 (by decide), u₆.gpr, u₅.other .r2 (by decide), u₄.other .r2 (by decide),
        u₃.other .r2 (by decide), g₂, u₁.other .r2 (by decide)]
    obtain h10 : s₇.gpr .r10 = s₀.gpr .r3 := by
      rw [u₇.gpr, u₆.other .r3 (by decide), u₅.other .r3 (by decide), u₄.other .r3 (by decide),
        u₃.other .r3 (by decide), g₂, u₁.other .r3 (by decide)]
    rw [h9, h10, cnt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rfl
  · rw [mm]; exact hframe.mono (by simp)
  · intro p hp'
    rw [mm, m₂, u₁.mem, h12, saveMem_saved _ _ _ p hp', u₁.other _ (Ne.symm ?_)]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  · intro i hi
    rw [mm]
    exact hframe.bytes (R := stR s₀ w) (by simpa using hp.st_scr)
      (by show bufOff w + blockBytes w ≤ 2 ^ 64; have := hp.st_fit; omega_using [this]) hi

/-! ## Padding the buffer with zeros -/

/-- The state, with its buffer padded: the hash value and the first `r`
bytes of the buffer as on entry, then zeros. -/
structure Padded (w : Nat) (s₀ : State) (s : State) : Prop extends Common w s₀ s where
  st : stateAt w s.mem (stA s₀) = stateAt w s₀.mem (stA s₀)
  buf : bytesAt s.mem (buf s₀ w) (blockBytes w) =
    bytesAt s₀.mem (buf s₀ w) (bufLen w (cnt s₀)) ++ List.replicate (blockBytes w - bufLen w (cnt s₀)) 0

theorem pad_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State} (hC : Common w s₀ s)
    (hst : ∀ i < bufOff w + blockBytes w, s.mem (stA s₀ + BitVec.ofNat 64 i) = s₀.mem (stA s₀ + BitVec.ofNat 64 i))
    (h8 : s.gpr .r8 = BitVec.ofNat 32 (bufLen w (cnt s₀))) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t, Padded w s₀ t → WP isa rest t Q) :
    WP isa (.seq (.block [.mov .r12 (.imm 0), .mov .r11 (.imm (BitVec.ofNat 32 (B w))), .subs .r11 .r11 (.reg .r8)])
      (.seq (.ite .eq (.block []) (zeroLoop (w := w))) rest)) s Q := by
  have hl := hP.len
  have hst' := hp.st_fit
  obtain hr := bufLen_le (w := w) hP.pos (cnt s₀)
  obtain ⟨r, hrr⟩ : ∃ r, r = bufLen w (cnt s₀) := ⟨_, rfl⟩
  rw [← hrr] at h8 hr
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm hP.encB) fun s₂ u₂ =>
    wp_subs (op2_reg _ _) fun s₃ u₃ z₃ => WP.block_nil ?_)
  obtain hC₃ : Common w s₀ s₃ := ((hC.of_upd u₁).of_upd u₂).of_upd u₃
  obtain hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain h11 : s₃.gpr .r11 = BitVec.ofNat 32 (blockBytes w - r) := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h8, B_eq, sub_ofNat hr]
  obtain hz : isa.eval .eq s₃ = some (decide (blockBytes w - r = 0)) := by
    show VG.Arm.eval .eq s₃ = _
    rw [eval_eq, z₃, ← u₃.gpr, h11, MdStream.Arm.ofNat_beq_zero (by omega_using [hl])]
  -- The facts about the bytes, from the memory after zeroing `k` bytes.
  obtain hpad : ∀ m : Mem, m = writeBytes s.mem (buf s₀ w + BitVec.ofNat 64 r) (List.replicate (blockBytes w - r) 0) →
      Frame [stR s₀ w] s.mem m ∧ stateAt w m (stA s₀) = stateAt w s₀.mem (stA s₀) ∧
      bytesAt m (buf s₀ w) (blockBytes w) =
        bytesAt s₀.mem (buf s₀ w) r ++ List.replicate (blockBytes w - r) 0 := by
    intro m hm
    obtain hwf : Frame [stR s₀ w] s.mem m := by
      rw [hm, Offset.add_add]
      exact writeBytes_frame _ _ _ (by simp only [List.length_replicate]; exact contains_off _ (by omega_using [hr]) (by omega_using [hst']))
    refine ⟨hwf, ?_, ?_⟩
    · rw [hm, Offset.add_add]
      refine (stateAt_congr fun i hi => ?_).trans (stateAt_congr fun i hi => hst i (by omega_using [hi]))
      exact writeBytes_before _ _ _ (by omega_using [hi]) (by simp; omega_using [hst', hr])
    · have := Arm.Stream.bytesAt_writeBytes s.mem (buf s₀ w) r (List.replicate (blockBytes w - r) 0)
        (by simp; omega_using [hst', hr])
      simp only [List.length_replicate, show r + (blockBytes w - r) = blockBytes w by omega_using [hr]] at this
      rw [hm, this]
      refine congrArg (· ++ _) (bytesAt_congr fun i hi => ?_)
      rw [Offset.add_add]; exact hst _ (by omega_using [hr, hi])
  refine WP.seq (WP.mono (Q := Padded w s₀) (WP.ite _ hz (fun hb => ?_) (fun hb => ?_)) k)
  · simp only [decide_eq_true_eq] at hb
    obtain ⟨hwf, h1, h2⟩ := hpad s₃.mem (by rw [hm₃, hb, List.replicate_zero, WriteBytes.writeBytes_nil])
    exact WP.block_nil ⟨hC₃, h1, by rw [← hrr]; exact h2⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine zeroLoop_ok (st := st s₀) (r := r) (k := blockBytes w - r) hl.2.1 (by omega_using [hb]) (by omega_using [hst', hb]) (hC₃.r4) (by
      rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h8]) h11
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr])
      (fun i hi => ⟨stR s₀ w, by simp [hC₃.wr, hp.wr], by
        rw [Offset.add_add]; exact contains_off _ (by omega_using [hi]) (by omega_using [hst'])⟩) fun s' h => ?_
    obtain hm' : s'.mem = writeBytes s.mem (buf s₀ w + BitVec.ofNat 64 r) (List.replicate (blockBytes w - r) 0) := by
      rw [h.mem, hm₃, Offset.add_add]
    obtain ⟨hwf, h1, h2⟩ := hpad s'.mem hm'
    obtain hg : ∀ x ∈ commonRegs, s'.gpr x = s₃.gpr x := fun x hx => h.other x
      (fun e => by subst e; simp at hx) (fun e => by subst e; simp at hx) (fun e => by subst e; simp at hx)
    refine ⟨⟨h.rd.trans hC₃.rd, h.wr.trans hC₃.wr, h.sp.trans hC₃.sp, by rw [hg _ (by simp)]; exact hC₃.r4,
      by rw [hg _ (by simp)]; exact hC₃.r5, by rw [hg _ (by simp)]; exact hC₃.r6,
      by rw [hg .r9 (by simp), hg .r10 (by simp)]; exact hC₃.cn,
      hC.frame.trans (hwf.mono (by simp)), saved_frame hp hC.saved (hwf.mono (by simp))⟩, h1,
      by rw [← hrr]; exact h2⟩

/-! ## Up to the call -/

/-- What holds before the call. -/
def PostPro (w : Nat) (s₀ s : State) : Prop :=
  Padded w s₀ s ∧
    CallArgs (w := w) s (st s₀) (scr s₀) (st s₀ + BitVec.ofNat 32 (bufOff w)) 1 (BitVec.ofNat 64 (cnt s₀)) 1

theorem pro_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) :
    WP isa (finalizePro (w := w)) s₀ (PostPro w s₀) := by
  have hl := hP.len
  obtain hst := hp.st_fit; have hsc := hp.scr_fit
  unfold finalizePro
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hC, hstb⟩ => ?_)
  refine WP.seq (WP.mono (bufLen_ok hP (cnt_lt s₀) hC.cn) fun s₂ ⟨h8, g, m, rd, wr, sp⟩ => ?_)
  obtain hC₂ := hC.of_gpr (fun r hr => g r (fun e => by subst e; simp at hr) (fun e => by subst e; simp at hr))
    m rd wr sp
  refine pad_ok hP hp hC₂ (fun i hi => by rw [m]; exact hstb i hi) h8 fun s₃ hP₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_add (op2_imm hP.encN) fun s₅ u₅ =>
    wp_mov (op2_imm (by decide)) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ =>
    wp_mov (op2_reg _ _) fun s₈ u₈ => wp_mov (op2_imm (by decide)) fun s₉ u₉ =>
    wp_mov (op2_reg _ _) fun s₁₀ u₁₀ => WP.block_nil ?_
  obtain hC' : Common w s₀ s₁₀ :=
    ((((((hP₃.toCommon.of_upd u₄).of_upd u₅).of_upd u₆).of_upd u₇).of_upd u₈).of_upd u₉).of_upd u₁₀
  obtain hm : s₁₀.mem = s₃.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  refine ⟨⟨hC', by rw [hm]; exact hP₃.st, by rw [hm]; exact hP₃.buf⟩, ?_⟩
  obtain eN : Region.Sub ⟨stA s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by omega_using [])
  obtain eS : Region.Sub ⟨scA s₀, 512⟩ (scR s₀) := Region.sub_prefix (by omega_using [])
  obtain eB : Region.Sub ⟨State.addr (st s₀ + BitVec.ofNat 32 (bufOff w)), blockBytes w * 1⟩ (stR s₀ w) := by
    rw [addr_add (by omega_using [hl, hst]), Nat.mul_one]; exact Offset.sub_base _ (by omega_using [])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide, by rw [hC'.sp]; exact hp.sp16, ?_, ?_,
    (hp.st_scr.sub_left eN).sub_right eS, ?_, (hp.st_scr.sub_left eB).sub_right eS, ?_, ?_, ?_, by omega_using [hst],
    by rw [toNat_add_ofNat (by omega_using [hl, hst])]; omega_using [hst], by omega_using [hsc]⟩
  all_goals try simp only [u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
    u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, ne_eq, reduceCtorEq, not_false_eq_true, hP₃.r4, hP₃.r5, N_eq]
  all_goals first | rfl | exact hP₃.cn | skip
  · rw [hC'.rd, hC'.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨stR s₀ w, by simp, bufOff w, addr_add (by omega_using [hl, hst]), by dsimp only; omega_using []⟩
  · rw [hC'.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · rw [addr_add (by omega_using [hl, hst]), Nat.mul_one]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hst])
  · rw [below, hC'.sp]; exact hp.w_st.sub_right eN
  · rw [below, hC'.sp]; exact hp.w_st.sub_right eB
  · rw [below, hC'.sp]; exact hp.w_scr.sub_right eS

/-! ## The call -/

/-- What holds after the call. -/
def Mid (P : Params w) (s₀ s : State) : Prop :=
  Common w s₀ s ∧ ∀ h0 d, Spec.Blake2.Repr P h0 s₀.mem (stA s₀) d → d.length < 2 ^ 64 →
    countArm s₀ = BitVec.ofNat 64 d.length →
    (stateAt w s.mem (stA s₀)).toList.flatMap wordBytes = finalHash P h0 d

theorem call_ok' (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) {s : State} (h : PostPro w s₀ s) : WP isa (call name code) s (Mid P s₀) := by
  have hl := hP.len
  obtain hst := hp.st_fit; have hsc := hp.scr_fit
  obtain ⟨hpd, hca⟩ := h
  refine call_ok hf hca fun s' ha hstate => ⟨?_, fun h0 d hr hl' hc => ?_⟩
  · have hf' : Frame [stR s₀ w, ⟨scA s₀, 512⟩, below s₀] s.mem s'.mem := by
      have := ha.frame
      rw [below, hpd.sp] at this
      exact this.sub fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨stR s₀ w, by simp, Region.sub_prefix (by omega_using [])⟩
        · exact ⟨⟨scA s₀, 512⟩, by simp, fun _ h => h⟩
        · exact ⟨below s₀, by simp, fun _ h => h⟩
    obtain hcp : ∀ r ∈ commonRegs, r ∈ preserved ∧ r ≠ .lr := by decide
    obtain hg : ∀ r ∈ commonRegs, s'.gpr r = s.gpr r := fun r hr => ha.cs r (hcp r hr).1 (hcp r hr).2
    exact ⟨ha.rd.trans hpd.rd, ha.wr.trans hpd.wr, ha.sp.trans hpd.sp, by rw [hg _ (by simp)]; exact hpd.r4,
      by rw [hg _ (by simp)]; exact hpd.r5, by rw [hg _ (by simp)]; exact hpd.r6,
      by rw [hg .r9 (by simp), hg .r10 (by simp)]; exact hpd.cn,
      hpd.frame.trans (hf'.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨stR s₀ w, by simp, fun _ h => h⟩
        · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega_using [])⟩
        · exact ⟨below s₀, by simp, fun _ h => h⟩),
      saved_frame hp hpd.saved hf'⟩
  · have ecnt : cnt s₀ = d.length := by
      rw [cnt, hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl']
    rw [hstate, Update.compressBlocks_one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (cnt_lt s₀), ecnt,
      addr_add (by omega_using [hl, hst])]
    refine final_eq P hP.pos hr hpd.st ?_
    rw [← ecnt]; exact hpd.buf

/-! ## The end -/

/-- Copying the first `n` words of the hash value to `out`. -/
structure CopyW (s₀ s : State) (n : Nat) (s' : State) : Prop where
  other : ∀ r, r ≠ .r12 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [outR s₀ w] s.mem s'.mem
  words : ∀ j < n, s'.mem.readW (outA s₀ + BitVec.ofNat 64 (4 * j)) 32 =
    s.mem.readW (stA s₀ + BitVec.ofNat 64 (4 * j)) 32

theorem copyW_all (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State} (hC : Common w s₀ s) :
    ∀ n ≤ bufOff w / 4, WP isa (.block ((List.range n).flatMap
      (fun k => [.ldr .r12 .r4 (4 * k), .str .r12 .r6 (4 * k)]))) s (CopyW (w := w) s₀ s n) := by
  have hl := hP.len
  obtain hst := hp.st_fit; have hof := hp.out_fit
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega_using [])⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn])) fun t h => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    obtain h4 : t.gpr .r4 = st s₀ := by rw [h.other _ (by decide), hC.r4]
    obtain h6 : t.gpr .r6 = out s₀ := by rw [h.other _ (by decide), hC.r6]
    refine wp_ldr (a := stA s₀ + BitVec.ofNat 64 (4 * n)) (by omega_using [hl, hn]) (by rw [h4, addr_add (by omega_using [hst, hn])])
      ⟨stR s₀ w, by simp [h.rd, h.wr, hC.rd, hC.wr, hp.wr], contains_off _ (by omega_using [hn]) (by omega_using [hst])⟩
      fun t₁ u₁ => ?_
    refine wp_str (a := outA s₀ + BitVec.ofNat 64 (4 * n)) (by omega_using [hl, hn])
      (by rw [u₁.other _ (by decide), h6, addr_add (by omega_using [hof, hn])])
      ⟨outR s₀ w, by simp [u₁.wr, h.wr, hC.wr, hp.wr], contains_off _ (by omega_using [hn]) (by omega_using [hof])⟩
      fun t₂ u₂ => WP.block_nil ?_
    obtain hfw : Frame [outR s₀ w] t.mem t₂.mem := by
      rw [u₂.mem, u₁.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_off _ (by omega_using [hn]) (by omega_using [hof]))
    -- The state is not in `out`.
    obtain hsb : ∀ j < bufOff w / 4, t.mem.readW (stA s₀ + BitVec.ofNat 64 (4 * j)) 32 =
        s.mem.readW (stA s₀ + BitVec.ofNat 64 (4 * j)) 32 := fun j hj =>
      h.frame.readW (r := ⟨stA s₀ + BitVec.ofNat 64 (4 * j), 4⟩) (Region.contains_self _ _)
        (by simp only [List.mem_singleton]; rintro r rfl
            exact hp.st_out.sub_left (Offset.sub_base _ (by omega_using [hj]))) (by decide)
    refine ⟨fun r hr => by rw [u₂.gpr, u₁.other r hr, h.other r hr], by rw [u₂.rd, u₁.rd, h.rd],
      by rw [u₂.wr, u₁.wr, h.wr], by rw [u₂.sp, u₁.sp, h.sp], h.frame.trans hfw, fun j hj => ?_⟩
    rw [u₂.mem, u₁.mem, u₁.gpr]
    by_cases e : j = n
    · subst e; rw [Mem.readW_writeW_self32, hsb j (by omega_using [hn])]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [e]) (by omega_using [hof, hn, hj]) (by omega_using [hof, hn])) (by decide)]
      exact h.words j (by omega_using [hj, e])

theorem end_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State} (h : Mid P s₀ s) :
    WP isa (.block (finalizeEnd (w := w))) s fun s' => abiPreserved s₀ s' ∧ (finalizeArm P).post s₀ s' := by
  have hl := hP.len
  obtain hst := hp.st_fit; have hof := hp.out_fit; have hsc := hp.scr_fit
  obtain ⟨hC, hfin⟩ := h
  unfold finalizeEnd
  rw [WP.block_append_iff]
  refine WP.mono (copyW_all hP hp hC _ (Nat.le_refl _)) fun t ht => ?_
  obtain h5 : t.gpr .r5 = scr s₀ := by rw [ht.other _ (by decide), hC.r5]
  obtain hsv : Saved (scA s₀) s₀.gpr t.mem := by
    intro p hp'
    obtain hoff := saved_bound p hp'
    rw [← hC.saved p hp']
    refine ht.frame.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton]; rintro r rfl
    exact hp.out_scr.symm.sub_left (Offset.sub_base _ (by omega_using [hoff]))
  refine restore_ok h5 hsc (fun d hd₁ hd₂ => ⟨scR s₀, by simp [ht.rd, ht.wr, hC.rd, hC.wr, hp.wr],
      contains_off _ (by omega_using [hd₂]) (by omega_using [])⟩) s₀.gpr hsv
    fun s' hs hmem _ _ hsp => ⟨⟨preserved_of hs, by rw [hsp, ht.sp, hC.sp]⟩, fun h0 d hr hl' hc => ?_⟩
  rw [← hfin h0 d hr hl' hc, ← bytesAt_state _ _ (by rcases hP.w with h | h <;> simp [h]), hmem]
  -- The words of `out` are those of the hash value.
  obtain e4 : bufOff w = 4 * (bufOff w / 4) := by omega_using [hl]
  rw [e4, show (4 : Nat) = 32 / 8 from rfl, bytesAt_words, bytesAt_words]
  rw [List.flatMap, List.flatMap]
  refine congrArg _ (List.map_congr_left fun j hj => ?_)
  obtain hj := List.mem_range.mp hj
  rw [← wordBytes_readW _ _ (.inl rfl), ← wordBytes_readW _ _ (.inl rfl)]
  exact congrArg _ (ht.words j hj)

/-! ## `finalize` -/

theorem correct (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) :
    WP isa (finalize (w := w) name code) s₀ fun s' => abiPreserved s₀ s' ∧ (finalizeArm P).post s₀ s' :=
  WP.seq (WP.mono (pro_ok hP hp) fun _ h₁ => WP.seq (WP.mono (call_ok' hP hf hp h₁) fun _ h₂ =>
    end_ok hP hp h₂))

end VG.Proof.Blake2.Arm.Stream.Finalize
