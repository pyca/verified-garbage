module

public import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Body
import VerifiedGarbage.Proof.Argon2.Initial
public import VerifiedGarbage.Proof.Argon2.HPrime
public import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Blake2.Arm.CompressB
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Blake2.Arm.Stream.Init
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Rc2.Select
public import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.Blake2.Arm.Blake2b
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
public import VerifiedGarbage.Proof.Framework.OmegaLit
public import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Arm.Isa
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import VerifiedGarbage.Spec.Blake2
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.TCB.Mem
public import Init.Core
public import VerifiedGarbage.Spec.Argon2

/-! ### `Argon2.Arm.HPrime.First`, which only this module used -/

section

/-!
# Argon2 H′ on ARMv7: the first digest

`first_ok`: `first` leaves H(min(out_len, 64), LE32(out_len) ‖ input) at the
start of the digest, `scratch[768, 832)`. The input is read before anything
is written to the output, so the two may overlap.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (init update finalize absorbFixed chooseLength absorbInput finishInput first
  cmpLeft)
open VG.Proof.MdStream.Arm (Upd Fupd wp_mov wp_add wp_sub wp_cmp op2_reg op2_imm op2_lsr eval_eq eval_ne
  ofNat_beq_zero)
open VG.Proof.Blake2.Arm.Stream (wp_adds wp_adc)

/-- `(x - 1) >> 6 = 0` exactly when `1 ≤ x ≤ 64`. -/
theorem le64_beq {x : Nat} (h₁ : 1 ≤ x) (h₂ : x < 2 ^ 32) :
    ((BitVec.ofNat 32 x - 1) >>> 6 - 0 == 0) = decide (x ≤ 64) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, MdStream.Arm.sub_ofNat h₁, show ∀ y : BitVec 32, y - 0 = y from fun y => BitVec.sub_zero y,
    MdStream.Arm.ofNat_shr (by omega_using [h₂]), ofNat_beq_zero (by omega_using [h₂])]
  by_cases h : x ≤ 64
  · simp only [h, decide_true, decide_eq_true_eq]; omega_using [h]
  · simp only [h, decide_false, decide_eq_false_iff_not]; omega_using [h]

/-- The comparisons with 64 of the bytes left (in `r8`). -/
theorem cmpLeft_ok {s : State} {x : Nat} (hx : s.gpr .r8 = BitVec.ofNat 32 x) (h₁ : 1 ≤ x) (h₂ : x < 2 ^ 32) :
    WP isa (.block cmpLeft) s fun t => isa.eval .eq t = some (decide (x ≤ 64)) ∧
      (∀ r, r ≠ .r0 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold cmpLeft
  refine wp_sub (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · show VG.Arm.eval .eq s₃ = _
    rw [eval_eq, z₃, u₂.gpr, u₁.gpr, hx]
    exact congrArg some (le64_beq h₁ h₂)
  · rw [f₃.gpr, u₂.other _ hr, u₁.other _ hr]
  · rw [f₃.mem, u₂.mem, u₁.mem]
  · rw [f₃.rd, u₂.rd, u₁.rd]
  · rw [f₃.wr, u₂.wr, u₁.wr]
  · rw [f₃.sp, u₂.sp, u₁.sp]

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- `r1 := min(out_len, 64)`. -/
theorem choose_ok {s : State} (_b : Body s₀ s) (o : Out s₀ s []) :
    WP isa chooseLength s fun t => t.gpr .r1 = BitVec.ofNat 32 (min (ol s₀) 64) ∧
      Keeps (scr s₀) (sp₀ s₀) s t := by
  have hol := (s₀.gpr .r3).isLt
  have hpos := hp.ol_pos
  have l₀ : s.gpr .r8 = BitVec.ofNat 32 (ol s₀) := by rw [o.left]; rfl
  unfold chooseLength
  refine WP.seq (wp_sub (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ?_)
  have k₃ : Keeps (scr s₀) (sp₀ s₀) s s₃ := Keeps.same (fun r hr => by
      rw [f₃.gpr, u₂.other _ (kept_ne r hr).2.1, u₁.other _ (kept_ne r hr).2.1])
    (by rw [f₃.sp, u₂.sp, u₁.sp]) (by rw [f₃.mem, u₂.mem, u₁.mem]) (by rw [f₃.rd, u₂.rd, u₁.rd])
    (by rw [f₃.wr, u₂.wr, u₁.wr])
  have r8₃ : s₃.gpr .r8 = BitVec.ofNat 32 (ol s₀) := by rw [k₃.gpr _ (by decide), l₀]
  refine WP.ite (decide (ol s₀ ≤ 64)) (by
      show VG.Arm.eval .eq s₃ = _
      rw [eval_eq, z₃, u₂.gpr, u₁.gpr, l₀]; exact congrArg some (le64_beq hpos hol))
    (fun h => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ⟨?_, ?_⟩)
    (fun h => wp_mov (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil ⟨?_, ?_⟩)
  · have : ol s₀ ≤ 64 := by simpa using h
    rw [u₄.gpr, r8₃, Nat.min_eq_left this]
  · exact k₃.trans (Keeps.same (fun r hr => u₄.other r (kept_ne r hr).2.1) u₄.sp u₄.mem u₄.rd u₄.wr)
  · have : 64 ≤ ol s₀ := by simp at h; omega_using [h]
    rw [u₄.gpr, Nat.min_eq_right this]; rfl
  · exact k₃.trans (Keeps.same (fun r hr => u₄.other r (kept_ne r hr).2.1) u₄.sp u₄.mem u₄.rd u₄.wr)

end

/-! ## The steps of `first` -/

/-- The state before and between the steps of `first`: the body, no output
yet, and the input kept. -/
structure F0 (s₀ s : State) : Prop where
  body : Body s₀ s
  out : Out s₀ s []
  input : bytesAt s.mem (State.addr (inp s₀)) (inl s₀) = bytesAt s₀.mem (State.addr (inp s₀)) (inl s₀)

/-- The length of the first digest. -/
abbrev nF (s₀ : State) : Nat := min (ol s₀) 64

/-- The input, on entry. -/
abbrev inB (s₀ : State) : List Byte := bytesAt s₀.mem (State.addr (inp s₀)) (inl s₀)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem F0.keeps {s t : State} (h : F0 s₀ s) (k : Keeps (scr s₀) (sp₀ s₀) s t) : F0 s₀ t := by
  refine ⟨h.body.keeps hp k, h.out.keeps hp k, ?_⟩
  have hif := hp.in_fits
  have := k.bytes (R := inR s₀) (by simp; omega_using [hif])
    (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in.symm
  simp only at this
  rw [this, h.input]

theorem nF_pos : 1 ≤ nF s₀ := by have := hp.ol_pos; simp only [nF]; omega_using [this]

theorem first_choose {s : State} (h : F0 s₀ s) :
    WP isa chooseLength s fun t => F0 s₀ t ∧ t.gpr .r1 = BitVec.ofNat 32 (nF s₀) :=
  (choose_ok hp h.body h.out).mono fun _ ⟨e, k⟩ => ⟨h.keeps hp k, e⟩

theorem first_init {s : State} (h : F0 s₀ s ∧ s.gpr .r1 = BitVec.ofNat 32 (nF s₀)) :
    WP isa init s fun t => F0 s₀ t ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) t.mem (P s₀) [] := by
  have c := h.1.body.ctx hp
  refine (init_ok c h.2 (nF_pos hp) (Nat.min_le_right _ _)).mono fun t ⟨r, cs, rd, wr, sp, f⟩ => ⟨?_, r⟩
  refine h.1.keeps hp (Keeps.of_call cs sp rd wr f fun r hr => ?_)
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩

theorem pfx_cov {s : State} (b : Body s₀ s) : Covers [⟨P s₀ + BitVec.ofNat 64 832, 4⟩] s.wr := by
  rw [b.wr, hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, 832, rfl, by simp⟩

theorem first_fixed {s : State}
    (h : F0 s₀ s ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) s.mem (P s₀) []) :
    WP isa (absorbFixed 832 4) s fun t => F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (nF s₀) 0) t.mem (P s₀) (Spec.Argon2.le32 (ol s₀)) := by
  have hs := hp.scr_fits
  refine (absorbFixed_ok (h.1.body.ctx hp) (offset := 832) (size := 4) (by decide) (by decide) (by omega_using [hs])
    (by decide) (by decide) (by decide) (pfx_cov hp h.1.body) (hp.stk_scr.sub_right (Offset.sub_base _ (by decide)))
    h.2).mono fun t ⟨r, k⟩ => ⟨h.1.keeps hp k, ?_⟩
  rw [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, h.1.body.pfx] at r
  exact r

theorem first_input {s : State}
    (h : F0 s₀ s ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) s.mem (P s₀) (Spec.Argon2.le32 (ol s₀))) :
    WP isa absorbInput s fun t => F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (nF s₀) 0) t.mem (P s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀) := by
  have hif := hp.in_fits
  have hil := (s₀.gpr .r1).isLt
  unfold absorbInput
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_)
  have o₄ : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other _ h4, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have k₄ : Keeps (scr s₀) (sp₀ s₀) s s₄ := Keeps.same (fun r hr => o₄ r (kept_ne r hr).2.2.1
      (kept_ne r hr).2.2.2.1 (kept_ne r hr).2.2.2.2.1 (kept_ne r hr).2.2.2.2.2.1)
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  have F₄ := h.1.keeps hp k₄
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have cnt₄ : s₄.gpr .r3 ++ s₄.gpr .r2 = BitVec.ofNat 64 (Spec.Argon2.le32 (ol s₀)).length := by
    rw [Proof.Argon2.le32_length, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl
  have r9 : s₄.gpr .r9 = inp s₀ := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.1.body.r5]
  have r10 : (s₄.gpr .r10).toNat = inl s₀ := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.1.body.r6]
  have hDc : Covers [⟨State.addr (inp s₀), inl s₀⟩] (s₄.rd ++ s₄.wr) := by
    rw [F₄.body.rd, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨inR s₀, by simp, 0, by simp, by simp⟩
  refine (update_ok (F₄.body.ctx hp) (h0 := Spec.Blake2.init Spec.Blake2.b (nF s₀) 0) r9 r10 hif hDc
    (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in (by rw [m₄]; exact h.2) cnt₄
    (by rw [Proof.Argon2.le32_length]; omega_using [hif])).mono fun s₅ ⟨r₅, cs₅, rd₅, wr₅, sp₅, f₅⟩ => ?_
  rw [F₄.input] at r₅
  refine ⟨F₄.keeps hp (Keeps.of_call cs₅ sp₅ rd₅ wr₅ f₅ fun r hr => ?_), r₅⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

omit hp in
theorem count4 (x : Nat) (hx : x < 2 ^ 32) :
    ((0 : BitVec 32) + 0 + (if decide (2 ^ 32 ≤ (BitVec.ofNat 32 x).toNat + (4 : BitVec 32).toNat) = true
      then 1 else 0)) ++ (BitVec.ofNat 32 x + 4) = BitVec.ofNat 64 (x + 4) := by
  rw [Proof.Blake2.Arm.Stream.add64]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, Proof.Blake2.Arm.Stream.toNat_append32]
  simp [Nat.mod_eq_of_lt hx] <;> omega

theorem first_finish {s : State}
    (h : F0 s₀ s ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) s.mem (P s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀)) :
    WP isa finishInput s fun t => F0 s₀ t ∧
      (digest s₀ t).take (nF s₀) = Spec.Argon2.H (nF s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀) := by
  have hif := hp.in_fits
  have hil := (s₀.gpr .r1).isLt
  unfold finishInput
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_adds (op2_imm (by decide)) fun s₂ u₂ c₂ =>
    wp_adc (op2_imm (by decide)) fun s₃ u₃ _ => WP.block_nil ?_)
  have o₃ : ∀ r, r ≠ .r2 → r ≠ .r3 → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other _ h2, u₂.other _ h1, u₁.other _ h2]
  have k₃ : Keeps (scr s₀) (sp₀ s₀) s s₃ := Keeps.same (fun r hr => o₃ r (kept_ne r hr).2.2.1
      (kept_ne r hr).2.2.2.1)
    (by rw [u₃.sp, u₂.sp, u₁.sp]) (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₃.wr, u₂.wr, u₁.wr])
  have F₃ := h.1.keeps hp k₃
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have r6 : s₁.gpr .r6 = BitVec.ofNat 32 (inl s₀) := by rw [u₁.other _ (by decide), h.1.body.r6]; simp
  have cnt : s₃.gpr .r3 ++ s₃.gpr .r2 = BitVec.ofNat 64 (Spec.Argon2.le32 (ol s₀) ++ inB s₀).length := by
    rw [u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₂.other _ (by decide), u₁.gpr, c₂, r6, List.length_append,
      Proof.Argon2.le32_length]
    simp only [inB, bytesAt, List.length_map, List.length_range]
    rw [show 4 + inl s₀ = inl s₀ + 4 by omega_using []]
    exact count4 _ hil
  refine (finalize_ok (F₃.body.ctx hp) (by rw [m₃]; exact h.2) cnt
    (by simp only [List.length_append, Proof.Argon2.le32_length, inB, bytesAt, List.length_map,
      List.length_range]; omega_using [hif])).mono ?_
  rintro t ⟨d, cs, rd, wr, sp, f⟩
  refine ⟨F₃.keeps hp (Keeps.of_call cs sp rd wr f fun r hr => ?_), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · show (bytesAt t.mem (P s₀ + 768) 64).take _ = _
    rw [d, Proof.Argon2.H_stream]

/-- `first` hashes the length prefix and the input. -/
theorem first_ok {s : State} (h : F0 s₀ s) :
    WP isa first s fun t => F0 s₀ t ∧
      (digest s₀ t).take (nF s₀) = Spec.Argon2.H (nF s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀) := by
  unfold first
  exact WP.seq ((first_choose hp h).mono fun _ h₁ => WP.seq ((first_init hp h₁).mono fun _ h₂ =>
    WP.seq ((first_fixed hp h₂).mono fun _ h₃ => WP.seq ((first_input hp h₃).mono fun _ h₄ =>
      first_finish hp h₄))))

end

end VG.Proof.Argon2.Arm.HPrime

end

end


/-!
# Argon2 H′ on ARMv7: the output from the first digest

`chain_ok`: after the first prefix V₁[0, 32) of a long output, each iteration
hashes the digest again and emits the prefix of the new one, while more than
64 bytes are left. `finish_ok`: `finishOutput` writes H′ to the output, from
the first digest: the digest itself for at most 64 bytes, and otherwise its
prefix, the chain and the last hash (`extend_ok`), of the 33 to 64 bytes left.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (next emitPrefix cmpLeft chain extendDigest finishOutput)
open VG.Proof.MdStream.Arm (Upd wp_mov op2_reg op2_imm)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

theorem chainDigest_succ' (j : Nat) (v : List Byte) :
    chainDigest (j + 1) v = Spec.Argon2.H 64 (chainDigest j v) := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih => exact ih (Spec.Argon2.H 64 v)

theorem chainPrefixes_succ' (j : Nat) (v : List Byte) :
    chainPrefixes (j + 1) v = chainPrefixes j v ++ (Spec.Argon2.H 64 (chainDigest j v)).take 32 := by
  induction j generalizing v with
  | zero => simp [chainPrefixes, chainDigest]
  | succ j ih =>
    rw [chainPrefixes, ih, chainPrefixes, chainDigest, List.append_assoc]

theorem finalHash_length (h0 : HashValue 64) (d : List Byte) : (finalHash b h0 d).length = 64 := by
  simp only [finalHash, Proof.Argon2.wordList_length, Vector.length_toList]

/-- The output after `j` iterations. -/
abbrev chainOut (V : List Byte) (j : Nat) : List Byte := V.take 32 ++ chainPrefixes j V

theorem chainOut_length {V : List Byte} (hV : V.length = 64) (j : Nat) :
    (chainOut V j).length = 32 + 32 * j := by
  simp only [chainOut, List.length_append, List.length_take, hV, Proof.Argon2.chainPrefixes_length]
  omega_arith

section
variable {s₀ : State} (hp : Pre s₀)
include hp

omit hp in
/-- `cmpLeft` on the output `xs`. -/
theorem cmp_ok {s : State} {xs : List Byte} (o : Out s₀ s xs) (hl : xs.length < ol s₀) :
    WP isa (.block cmpLeft) s fun t => isa.eval .eq t = some (decide (ol s₀ - xs.length ≤ 64)) ∧
      Keeps (scr s₀) (sp₀ s₀) s t ∧ t.mem = s.mem := by
  have hol := (s₀.gpr .r3).isLt
  refine (cmpLeft_ok o.left (by omega_arith) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hol)).mono
    fun t ⟨e, g, m, rd, wr, sp⟩ => ⟨e, Keeps.same (fun r hr => g r (kept_ne r hr).1) sp m rd wr, m⟩

/-- What the chain keeps between iterations. -/
structure ChainInv (s₀ : State) (e : BitVec 32) (V : List Byte) (j : Nat) (s : State) : Prop where
  body : Body s₀ s
  r11 : s.gpr .r11 = e
  out : Out s₀ s (chainOut V j)
  digest : digest s₀ s = chainDigest j V

/-- One iteration. -/
theorem iter_ok {e : BitVec 32} {V : List Byte} (hV : V.length = 64) {j : Nat} {s : State}
    (h : ChainInv s₀ e V j s) (hl : 32 + 32 * j + 32 ≤ ol s₀) (hl' : 32 + 32 * (j + 1) < ol s₀) :
    WP isa (.seq (.block [.mov .r1 (.imm 64)]) (.seq next (.seq emitPrefix (.block cmpLeft)))) s
      fun t => ChainInv s₀ e V (j + 1) t ∧
        isa.eval .eq t = some (decide (ol s₀ - (32 + 32 * (j + 1)) ≤ 64)) := by
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil ?_)
  have k₁ : Keeps (scr s₀) (sp₀ s₀) s s₁ := Keeps.same (fun r hr => u₁.other r (by
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.sp u₁.mem u₁.rd u₁.wr
  have b₁ := h.body.keeps hp k₁
  refine WP.seq ((next_ok (b₁.ctx hp) (n := 64) u₁.gpr (by decide) (by decide)).mono
    fun s₂ ⟨d₂, k₂⟩ => ?_)
  have K₂ := k₁.trans k₂
  have b₂ := h.body.keeps hp K₂
  have o₂ := h.out.keeps hp K₂
  have hlen := chainOut_length hV j
  refine WP.seq ((emit_ok hp b₂ o₂ (by rw [hlen]; exact hl)).mono fun s₃ ⟨b₃, e₃, o₃, d₃⟩ => ?_)
  have dg : digest s₀ s₂ = chainDigest (j + 1) V := by
    rw [chainDigest_succ', ← h.digest, Proof.Argon2.H_stream,
      List.take_of_length_le (by rw [finalHash_length])]
    rw [u₁.mem] at d₂
    exact d₂
  have xs₃ : chainOut V j ++ (digest s₀ s₂).take 32 = chainOut V (j + 1) := by
    rw [dg, chainDigest_succ', chainOut, chainOut, chainPrefixes_succ', List.append_assoc]
  rw [xs₃] at o₃
  refine (cmp_ok o₃ (by rw [chainOut_length hV]; exact hl')).mono fun t ⟨cf, k, m⟩ =>
    ⟨⟨b₃.keeps hp k, ?_, o₃.keeps hp k, ?_⟩, ?_⟩
  · rw [k.gpr _ (by decide), e₃, K₂.gpr _ (by decide), h.r11]
  · show bytesAt _ _ _ = _
    rw [m]
    exact d₃.trans dg
  · rw [cf, chainOut_length hV]

/-- The chain: iterations while more than 64 bytes are left. -/
theorem chain_ok {e : BitVec 32} {V : List Byte} (hV : V.length = 64) {j : Nat} {s : State}
    (h : ChainInv s₀ e V j s) (hl : 65 ≤ ol s₀ - (32 + 32 * j)) :
    WP isa chain s fun t => ∃ j', ChainInv s₀ e V j' t ∧ 33 ≤ ol s₀ - (32 + 32 * j') ∧
      ol s₀ - (32 + 32 * j') ≤ 64 ∧ 32 + 32 * j' ≤ ol s₀ := by
  unfold chain
  refine WP.loop (M := isa) (fun (m : Nat) (t : State) => ∃ j', m = ol s₀ - (32 + 32 * j') ∧
    ChainInv s₀ e V j' t ∧ 65 ≤ m) ?_ (ol s₀ - (32 + 32 * j)) s ⟨j, rfl, h, hl⟩
  rintro m t ⟨j', rfl, hi, hm⟩
  refine (iter_ok hp hV hi (by omega_arith) (by omega_arith)).mono fun u ⟨hu, cf⟩ => ?_
  have cf' : isa.eval .ne u = some (!decide (ol s₀ - (32 + 32 * (j' + 1)) ≤ 64)) := by
    have cf2 : VG.Arm.eval .eq u = _ := cf
    show VG.Arm.eval .ne u = _
    rw [MdStream.Arm.eval_eq, Option.some.injEq] at cf2
    rw [MdStream.Arm.eval_ne, cf2]
  by_cases hc : ol s₀ - (32 + 32 * (j' + 1)) ≤ 64
  · refine .inl ⟨by rw [cf']; simp [hc], j' + 1, hu, by omega_arith, by omega_arith, by omega_arith⟩
  · refine .inr ⟨by rw [cf']; simp [hc], _, by omega_arith, j' + 1, rfl, hu, by omega_arith⟩

/-- What the chain leaves: the output after `j` iterations and the last hash. -/
def Extended (s₀ : State) (e : BitVec 32) (V : List Byte) (t : State) : Prop :=
  ∃ j, Body s₀ t ∧ t.gpr .r11 = e ∧ Out s₀ t (chainOut V j) ∧
    (digest s₀ t).take (ol s₀ - (32 + 32 * j)) =
      Spec.Argon2.H (ol s₀ - (32 + 32 * j)) (chainDigest j V) ∧
    33 ≤ ol s₀ - (32 + 32 * j) ∧ ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ ol s₀

theorem extend_ok {s : State} (b : Body s₀ s) (o : Out s₀ s []) (hol : 65 ≤ ol s₀) :
    WP isa extendDigest s (Extended s₀ (s.gpr .r11) (digest s₀ s)) := by
  have hV : (digest s₀ s).length = 64 := by simp [digest, bytesAt]
  unfold extendDigest
  refine WP.seq ((emit_ok hp b o (by simp only [List.length_nil]; omega_arith)).mono
    fun s₁ ⟨b₁, e₁, o₁, d₁⟩ => ?_)
  rw [List.nil_append, show (digest s₀ s).take 32 = chainOut (digest s₀ s) 0 by
    simp [chainOut, chainPrefixes]] at o₁
  have i₁ : ChainInv s₀ (s.gpr .r11) (digest s₀ s) 0 s₁ := ⟨b₁, e₁, o₁, d₁⟩
  refine WP.seq ((cmp_ok o₁ (by rw [chainOut_length hV]; omega_arith)).mono fun s₂ ⟨cf₂, k₂, m₂⟩ => ?_)
  rw [chainOut_length hV] at cf₂
  have i₂ : ChainInv s₀ (s.gpr .r11) (digest s₀ s) 0 s₂ :=
    ⟨b₁.keeps hp k₂, (k₂.gpr _ (by decide)).trans e₁, o₁.keeps hp k₂,
      by show bytesAt _ _ _ = _; rw [m₂]; exact d₁⟩
  have hIte : WP isa (.ite .eq (.block []) chain) s₂ fun t => ∃ j, ChainInv s₀ (s.gpr .r11) (digest s₀ s) j t ∧
      33 ≤ ol s₀ - (32 + 32 * j) ∧ ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ ol s₀ := by
    refine WP.ite (decide (ol s₀ - (32 + 32 * 0) ≤ 64)) cf₂ (fun h => WP.block_nil ⟨0, i₂, ?_⟩)
      (fun h => (chain_ok hp hV i₂ ?_).mono fun t h => h)
    · simp only [decide_eq_true_eq] at h; omega_arith
    · simp only [decide_eq_false_iff_not] at h; omega_arith
  refine WP.seq (hIte.mono fun s₃ ⟨j, i₃, l₁, l₂, l₃⟩ => ?_)
  refine WP.seq (wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_)
  have k₄ : Keeps (scr s₀) (sp₀ s₀) s₃ s₄ := Keeps.same (fun r hr => u₄.other r (by
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₄.sp u₄.mem u₄.rd u₄.wr
  have b₄ := i₃.body.keeps hp k₄
  have r1₄ : s₄.gpr .r1 = BitVec.ofNat 32 (ol s₀ - (32 + 32 * j)) := by
    rw [u₄.gpr, i₃.out.left, chainOut_length hV]
  refine (next_ok (b₄.ctx hp) r1₄ (by omega_arith) l₂).mono fun t ⟨d, k⟩ => ?_
  have K := k₄.trans k
  refine ⟨j, i₃.body.keeps hp K, by rw [K.gpr _ (by decide), i₃.r11], i₃.out.keeps hp K, ?_, l₁, l₂, l₃⟩
  rw [Proof.Argon2.H_stream, ← i₃.digest]
  rw [u₄.mem] at d
  exact congrArg (List.take _) d

/-- `finishOutput` writes H′ of the input `I` from its first digest. -/
theorem finish_ok {s : State} (b : Body s₀ s) (o : Out s₀ s []) {I : List Byte}
    (hd : (digest s₀ s).take (min (ol s₀) 64) =
      Spec.Argon2.H (min (ol s₀) 64) (Spec.Argon2.le32 (ol s₀) ++ I)) :
    WP isa finishOutput s fun t => Body s₀ t ∧ t.gpr .r11 = s.gpr .r11 ∧
      bytesAt t.mem (State.addr (op s₀)) (ol s₀) = Spec.Argon2.hPrime (ol s₀) I := by
  have hpos := hp.ol_pos
  have hV : (digest s₀ s).length = 64 := by simp [digest, bytesAt]
  unfold finishOutput
  refine WP.seq ((cmp_ok o (by simp only [List.length_nil]; omega_arith)).mono fun s₁ ⟨cf₁, k₁, m₁⟩ => ?_)
  simp only [List.length_nil, Nat.sub_zero] at cf₁
  have b₁ := b.keeps hp k₁
  have o₁ := o.keeps hp k₁
  have d₁ : digest s₀ s₁ = digest s₀ s := by show bytesAt _ _ _ = _; rw [m₁]
  have hIte : WP isa (.ite .eq (.block []) extendDigest) s₁ fun t => Body s₀ t ∧ t.gpr .r11 = s.gpr .r11 ∧
      ∃ xs, Out s₀ t xs ∧ xs.length < ol s₀ ∧ ol s₀ - xs.length ≤ 64 ∧
        xs ++ (digest s₀ t).take (ol s₀ - xs.length) = Spec.Argon2.hPrime (ol s₀) I := by
    refine WP.ite (decide (ol s₀ ≤ 64)) cf₁ (fun h => WP.block_nil ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      refine ⟨b₁, k₁.gpr _ (by decide), [], o₁, by simp only [List.length_nil]; omega_arith,
        by simp only [List.length_nil]; omega_arith, ?_⟩
      rw [Nat.min_eq_left (by omega_arith)] at hd
      rw [List.nil_append, List.length_nil, Nat.sub_zero, d₁, hd]
      simp only [Spec.Argon2.hPrime, eq_true (by omega_arith : ol s₀ ≤ 64), ite_true]
    · simp only [decide_eq_false_iff_not] at h
      refine (extend_ok hp b₁ o₁ (by omega_arith)).mono fun t ⟨j, bt, et, ot, dt, l₁, l₂, l₃⟩ =>
        ⟨bt, et.trans (k₁.gpr _ (by decide)), _, ot, ?_, ?_, ?_⟩
      · rw [chainOut_length (by rw [d₁]; exact hV)]; omega_arith
      · rw [chainOut_length (by rw [d₁]; exact hV)]; omega_arith
      · have V₁ : digest s₀ s₁ = Spec.Argon2.H 64 (Spec.Argon2.le32 (ol s₀) ++ I) := by
          rw [d₁, ← List.take_of_length_le (l := digest s₀ s) (i := 64) (by rw [hV]),
            ← Nat.min_eq_right (by omega_arith : 64 ≤ ol s₀), hd]
        rw [chainOut_length (by rw [d₁]; exact hV), dt, chainOut, ← Proof.Argon2.longHash_chain, V₁]
        have hr : (ol s₀ + 31) / 32 - 2 = j + 1 := by omega_arith
        simp only [Spec.Argon2.hPrime, eq_false (by omega_arith : ¬ ol s₀ ≤ 64), ite_false]
        rw [hr, show ol s₀ - 32 * (j + 1) = ol s₀ - (32 + 32 * j) by omega_arith]
  refine WP.seq (hIte.mono fun s₂ ⟨b₂, e₂, xs, o₂, l₁, l₂, h₂⟩ => ?_)
  refine (copyRemaining_ok hp b₂ o₂ l₁ l₂).mono fun t ⟨bt, et, ht⟩ => ⟨bt, et.trans e₂, ?_⟩
  rw [ht, h₂]

end

end VG.Proof.Argon2.Arm.HPrime
