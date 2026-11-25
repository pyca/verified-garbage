module

public import VerifiedGarbage.Impl.P384.Linear
public import VerifiedGarbage.Proof.P384.Ops
public import VerifiedGarbage.Proof.Weierstrass.Cms
public import VerifiedGarbage.Proof.Mont.AArch64.P384Field.Reduce
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# P-384's small linear combinations on AArch64

`lin98_ok`, `lin41_ok`, `lin38_ok`: the code of `Impl/P384/Linear.lean` stores
`9A - 8B`, `4A - B` and `3A - 8B` modulo `p`. `shl_ok` is the shift of a number
in registers, `fold_ok` the reduction of its seventh word.
-/

@[expose] public section

set_option exponentiation.threshold 1024

namespace VG.Proof.P384.Linear

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.P384.Linear VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.P384.Ops (M)
open VG.Proof.Mont.AArch64.P384Field (regsVal_keep adds_ok subs_ok adc_ok sbc_ok regsVal_single Keeps.refl)
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.Cms
open VG.Proof.Weierstrass.AArch64.Mont (p384)
open VG.Proof.P384.Ops (clobX OpKeepX)
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-! ## Shifts -/

/-- `(n : b)`'s bits from `64 - k`. -/
theorem extrk_ok (s : State) (d n m : Reg) {k : Nat} (hk : 0 < k) :
    WP isa (.block [.extr .x d n m (64 - k)]) s fun t =>
      (t.gpr d).toNat = ((s.gpr n).toNat * 2 ^ 64 + (s.gpr m).toNat) / 2 ^ (64 - k) % 2 ^ 64 ∧ Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 64 - k < Size.x.bits from by simp only [Size.bits]; omega_using [hk], ite_true, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl, rfl⟩⟩
  rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.extractLsb'_toNat, BitVec.toNat_append,
    Nat.shiftRight_eq_div_pow, ← Nat.shiftLeft_add_eq_or_of_lt (s.gpr m).isLt, Nat.shiftLeft_eq]

theorem lsrk_ok (s : State) (d n : Reg) {k : Nat} (hk : 0 < k) :
    WP isa (.block [.lsr .x d n (64 - k)]) s fun t =>
      (t.gpr d).toNat = (s.gpr n).toNat / 2 ^ (64 - k) ∧ Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 64 - k < Size.x.bits from by simp only [Size.bits]; omega_using [hk], ite_true, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl, rfl⟩⟩
  rw [RegUpd.gpr_write_self]
  simp only [BitVec.setWidth_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem lslk_ok (s : State) (d n : Reg) {k : Nat} (hk : k < 64) :
    WP isa (.block [.lsl .x d n k]) s fun t =>
      (t.gpr d).toNat = (s.gpr n).toNat * 2 ^ k % 2 ^ 64 ∧ Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show k < Size.x.bits from hk, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl, rfl⟩⟩
  rw [RegUpd.gpr_write_self]
  simp only [BitVec.setWidth_eq, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Size.bits]

/-- The registers of a shift: a word is written after the words above it are. -/
def ShlOk : Reg → List Reg → List Reg → Prop
  | b, d :: ds, s :: ss => d ∉ ds ∧ b ∉ ds ∧ s ∉ ds ∧ ShlOk s ds ss
  | _, _, [] => True
  | _, [], _ => True

instance instDecidableShlOk : ∀ b ds ss, Decidable (ShlOk b ds ss)
  | _, [], [] => .isTrue (by simp [ShlOk])
  | _, [], _ :: _ => .isTrue (by simp [ShlOk])
  | _, _ :: _, [] => .isTrue (by simp [ShlOk])
  | _, _ :: ds, s :: ss => by
    have := instDecidableShlOk s ds ss
    unfold ShlOk; infer_instance

theorem shl_arith {x y k P V : Nat} (hk' : k < 64) (hy : y < 2 ^ 64) :
    (x * 2 ^ 64 + y) / 2 ^ (64 - k) % 2 ^ 64 + 2 ^ 64 * ((x / 2 ^ (64 - k) + 2 ^ k * V) % P) =
      (y / 2 ^ (64 - k) + 2 ^ k * (x + 2 ^ 64 * V)) % (2 ^ 64 * P) := by
  have hW : 2 ^ 64 = 2 ^ (64 - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
  have hQ : 0 < 2 ^ (64 - k) := Nat.pow_pos (by decide)
  have hK : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have e₁ : (x * 2 ^ 64 + y) / 2 ^ (64 - k) = y / 2 ^ (64 - k) + x * 2 ^ k := by
    rw [hW, show x * (2 ^ (64 - k) * 2 ^ k) + y = y + 2 ^ (64 - k) * (x * 2 ^ k) by
      rw [Nat.mul_left_comm, Nat.add_comm], Nat.add_mul_div_left _ _ hQ]
  have e₂ : y / 2 ^ (64 - k) + 2 ^ k * (x + 2 ^ 64 * V) = y / 2 ^ (64 - k) + x * 2 ^ k + 2 ^ 64 * (2 ^ k * V) := by
    rw [Nat.mul_add, Nat.mul_comm (2 ^ k) x, Nat.mul_left_comm]; omega
  have e₃ : (y / 2 ^ (64 - k) + x * 2 ^ k) / 2 ^ 64 = x / 2 ^ (64 - k) := by
    have hlt : y / 2 ^ (64 - k) < 2 ^ k := Nat.div_lt_of_lt_mul (hW ▸ hy)
    rw [hW, Nat.mul_comm (2 ^ (64 - k)), ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ hK,
      Nat.div_eq_of_lt hlt, Nat.zero_add]
  rw [e₁, e₂, Nat.mod_mul, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ (by decide : 0 < 2 ^ 64), e₃]

/-- The words above `b`. -/
theorem shlUp_ok {k : Nat} (hk : 0 < k) (hk' : k < 64) : ∀ (ds ss : List Reg) (b : Reg) {s : State}, ShlOk b ds ss →
    (ds.length = ss.length ∨ ds.length = ss.length + 1) →
    WP isa (.block (shlUp k b ds ss)) s fun t =>
      regsVal t ds = ((s.gpr b).toNat / 2 ^ (64 - k) + 2 ^ k * regsVal s ss) % 2 ^ (64 * ds.length) ∧ Keeps ds s t
  | [], [], _, s, _, _ => WP.block_nil ⟨by simp [regsVal, Nat.mod_one], Keeps.refl s⟩
  | [], _ :: _, _, _, _, h => absurd h (by simp)
  | [d], [], b, s, _, _ => by
    refine WP.mono (lsrk_ok s d b hk) fun t ⟨e, kt⟩ => ⟨?_, kt⟩
    have hb := (s.gpr b).isLt
    simp only [regsVal, e, Nat.mul_zero, Nat.add_zero, List.length_singleton, Nat.mul_one]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self ..) hb)).symm
  | _ :: _ :: _, [], _, _, _, h => absurd h (by simp)
  | d :: ds, r :: ss, b, s, ho, hl => by
    obtain ⟨o1, o2, o3, o4⟩ := ho
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [shlUp, WP.block_append_iff]
    refine WP.mono (shlUp_ok hk hk' ds ss r o4 (by omega)) fun u ⟨e₁, k₁⟩ => ?_
    refine WP.mono (extrk_ok u d r b hk) fun t ⟨e₂, k₂⟩ => ?_
    refine ⟨?_, (k₁.mono fun q h => List.mem_cons_of_mem _ h).trans (k₂.mono (by simp))⟩
    rw [regsVal, e₂, regsVal_keep k₂ (by intro q hq h; exact o1 (List.mem_singleton.mp h ▸ hq)), e₁,
      k₁.gpr r o3, k₁.gpr b o2, List.length_cons, pow64_succ]
    exact shl_arith hk' (s.gpr b).isLt
termination_by ds => ds.length

/-- `ds = 2^k ss`, for a number that fits. -/
theorem shl_ok {k : Nat} (hk : 0 < k) (hk' : k < 64) {d r : Reg} {ds ss : List Reg} {s : State}
    (ho : d ∉ ds ∧ r ∉ ds ∧ ShlOk r ds ss) (hl : ds.length = ss.length ∨ ds.length = ss.length + 1)
    (hfit : 2 ^ k * regsVal s (r :: ss) < 2 ^ (64 * (ds.length + 1))) :
    WP isa (.block (shl k (d :: ds) (r :: ss))) s fun t =>
      regsVal t (d :: ds) = 2 ^ k * regsVal s (r :: ss) ∧ Keeps (d :: ds) s t := by
  obtain ⟨o1, o2, o3⟩ := ho
  rw [shl, WP.block_append_iff]
  refine WP.mono (shlUp_ok hk hk' ds ss r o3 hl) fun u ⟨e₁, k₁⟩ => ?_
  refine WP.mono (lslk_ok u d r hk') fun t ⟨e₂, k₂⟩ => ?_
  refine ⟨?_, (k₁.mono fun q h => List.mem_cons_of_mem _ h).trans (k₂.mono (by simp))⟩
  rw [regsVal, e₂, regsVal_keep k₂ (by intro q hq h; exact o1 (List.mem_singleton.mp h ▸ hq)), e₁, k₁.gpr r o2]
  have h := shl_arith (x := (s.gpr r).toNat) (y := 0) (P := 2 ^ (64 * ds.length)) (V := regsVal s ss) hk' (by decide)
  rw [pow64_succ] at hfit
  rw [regsVal] at hfit
  rw [Nat.zero_div, Nat.zero_add, Nat.mod_eq_of_lt hfit] at h
  rw [regsVal, ← h, Nat.add_zero]
  congr 2
  rw [show 2 ^ 64 = 2 ^ k * 2 ^ (64 - k) by rw [← Nat.pow_add]; congr 1; omega, ← Nat.mul_assoc,
    Nat.mul_div_cancel _ (Nat.pow_pos (by decide))]

/-! ## The sum -/

/-- The registers the code changes. -/
abbrev linW : List Reg := [Reg.x2, .x7, .x14] ++ aw ++ bw ++ sw

/-- The operands, in registers: `A`, and `p - B`. -/
structure Opnd (s₀ : State) (A B : Nat) (s : State) : Prop where
  keep : Keeps linW s₀ s
  z : s.gpr .x7 = 0
  a : regsVal s aw = A
  b : regsVal s bw + B = p384

theorem Opnd.of_keeps {s₀ s t : State} {A B : Nat} (h : Opnd s₀ A B s) {W : List Reg} (k : Keeps W s t)
    (hW : ∀ r ∈ W, r ∈ linW) (h7 : .x7 ∉ W) (ha : ∀ r ∈ aw, r ∉ W) (hb : ∀ r ∈ bw, r ∉ W) : Opnd s₀ A B t :=
  ⟨h.keep.trans (k.mono hW), by rw [k.gpr _ h7, h.z], by rw [regsVal_keep k ha, h.a], by rw [regsVal_keep k hb, h.b]⟩

theorem operands_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hmo : M.mo + 48 ≤ size)
    (hmo8 : M.mo % 8 = 0) (hm : wordsVal s.mem base M.mo 6 = p384) {a b : Nat} (ha : a + 48 ≤ size) (hb : b + 48 ≤ size)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hB : wordsVal s.mem base b 6 < p384) :
    WP isa (.block (operands a b)) s fun t =>
      Opnd s (wordsVal s.mem base a 6) (wordsVal s.mem base b 6) t := by
  simp only [operands, List.append_assoc, List.cons_append, loads_eq]
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (Ops.zero7_ok s) fun s₁ ⟨z₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadsR_ok aw hs₁.ptr (by simpa using ha) ha8 (by decide) (by decide)) fun s₂ ⟨e₂, k₂, _⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadsR_ok bw hs₂.ptr (by simpa using hb) hb8 (by decide) (by decide)) fun s₃ ⟨e₃, k₃, _⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadsR_ok sw hs₃.ptr (by simpa using hmo) hmo8 (by decide) (by decide)) fun s₄ ⟨e₄, k₄, _⟩ => ?_
  refine WP.mono (subs_ok true bw sw bw (s := s₄) (.inr (by simp)) rfl rfl (by decide)) fun t ⟨e₅, k₅⟩ => ?_
  have k : Keeps linW s t := (k₁.mono (by decide)).trans <| (k₂.mono (by decide)).trans <|
    (k₃.mono (by decide)).trans <| (k₄.mono (by decide)).trans (k₅.mono (by decide))
  refine ⟨k, by rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), z₁], ?_, ?_⟩
  · rw [regsVal_keep k₅ (by decide), regsVal_keep k₄ (by decide), regsVal_keep k₃ (by decide), e₂, k₁.mem]; rfl
  · have em : regsVal s₄ sw = p384 := by rw [e₄, k₃.mem, k₂.mem, k₁.mem]; exact hm
    have eb : regsVal s₄ bw = wordsVal s.mem base b 6 := by
      rw [regsVal_keep k₄ (by decide), e₃, k₂.mem, k₁.mem]; rfl
    rw [em, eb] at e₅
    have hR := regsVal_lt t bw
    have hc := Bool.toNat_le (!t.c)
    simp only [ite_true, Bool.not_true, Bool.toNat_false, Nat.add_zero, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceMul] at e₅ hR
    omega_using [e₅, hR, hc, hB]

/-- The seven words of the sum. -/
def accVal (s : State) : Nat := regsVal s sw + 2 ^ 384 * (s.gpr .x14).toNat

theorem accVal_eq (s : State) : accVal s = regsVal s (sw ++ [.x14]) := by
  rw [regsVal_append, regsVal_single]; rfl

theorem more_ok {s₀ s : State} {A B : Nat} (h : Opnd s₀ A B s) (xs : List Reg) (hl : xs.length = 6)
    (hc : P384Field.ChainOk sw sw xs) (hfit : accVal s + regsVal s xs < 2 ^ 448) :
    WP isa (.block (more xs)) s fun t => accVal t = accVal s + regsVal s xs ∧ Opnd s₀ A B t := by
  rw [more, WP.block_append_iff]
  refine WP.mono (adds_ok true sw sw xs (s := s) (.inr (by simp)) rfl hl hc) fun u ⟨e₁, k₁⟩ => ?_
  refine WP.mono (adc_ok u .x14 .x14 .x7) fun t ⟨e₂, k₂, _⟩ => ?_
  have hu := h.of_keeps k₁ (by decide) (by decide) (by decide) (by decide)
  refine ⟨?_, hu.of_keeps k₂ (by decide) (by decide) (by decide) (by decide)⟩
  rw [hu.z, k₁.gpr .x14 (by decide)] at e₂
  simp only [ite_true, Bool.toNat_false, Nat.add_zero, show (0 : BitVec 64).toNat = 0 from rfl,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at e₁ e₂
  unfold accVal at hfit ⊢
  rw [regsVal_keep k₂ (by decide), e₂]
  have hR := regsVal_lt u sw
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at hR
  omega_using [e₁, hfit, hR]

theorem sum_ok {s₀ s : State} {A B : Nat} (h : Opnd s₀ A B s) (xs ys : List Reg) (hx : xs.length = 6) (hy : ys.length = 6)
    (hc : P384Field.ChainOk sw xs ys) :
    WP isa (.block (sum xs ys)) s fun t => accVal t = regsVal s xs + regsVal s ys ∧ Opnd s₀ A B t := by
  rw [sum, WP.block_append_iff]
  refine WP.mono (adds_ok true sw xs ys (s := s) (.inr (by simp)) hx hy hc) fun u ⟨e₁, k₁⟩ => ?_
  refine WP.mono (adc_ok u .x14 .x7 .x7) fun t ⟨e₂, k₂, _⟩ => ?_
  have hu := h.of_keeps k₁ (by decide) (by decide) (by decide) (by decide)
  refine ⟨?_, hu.of_keeps k₂ (by decide) (by decide) (by decide) (by decide)⟩
  rw [hu.z] at e₂
  have hb := Bool.toNat_le u.c
  simp only [ite_true, Bool.toNat_false, Nat.add_zero, show (0 : BitVec 64).toNat = 0 from rfl,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at e₁ e₂
  unfold accVal
  rw [regsVal_keep k₂ (by decide), e₂]
  omega_using [e₁, hb]

theorem shlAcc_ok {s₀ s : State} {A B k : Nat} (h : Opnd s₀ A B s) (hk : 0 < k) (hk' : k < 64)
    (hfit : 2 ^ k * accVal s < 2 ^ 448) :
    WP isa (.block (shl k (sw ++ [.x14]) (sw ++ [.x14]))) s fun t => accVal t = 2 ^ k * accVal s ∧ Opnd s₀ A B t := by
  refine WP.mono (shl_ok hk hk' (d := .x8) (r := .x8) (ds := [.x9, .x10, .x11, .x12, .x13, .x14])
    (ss := [.x9, .x10, .x11, .x12, .x13, .x14]) (s := s) (by decide) (.inl rfl)
    (by have := accVal_eq s; rw [this] at hfit; exact hfit)) fun t ⟨e, kt⟩ => ?_
  refine ⟨?_, h.of_keeps kt (by decide) (by decide) (by decide) (by decide)⟩
  rw [accVal_eq, accVal_eq]; exact e

theorem shlOf_ok {s₀ s : State} {A B k : Nat} (h : Opnd s₀ A B s) (hk : 0 < k) (hk' : k < 64) (r : Reg) (ss : List Reg)
    (hss : ss.length = 5) (ho : Reg.x8 ∉ ([.x9, .x10, .x11, .x12, .x13, .x14] : List Reg) ∧
      r ∉ ([.x9, .x10, .x11, .x12, .x13, .x14] : List Reg) ∧ ShlOk r [.x9, .x10, .x11, .x12, .x13, .x14] ss) :
    WP isa (.block (shl k (sw ++ [.x14]) (r :: ss))) s fun t =>
      accVal t = 2 ^ k * regsVal s (r :: ss) ∧ Opnd s₀ A B t := by
  have hlt := regsVal_lt s (r :: ss)
  rw [List.length_cons, hss] at hlt
  refine WP.mono (shl_ok hk hk' (d := .x8) (r := r) (ds := [.x9, .x10, .x11, .x12, .x13, .x14]) (ss := ss) (s := s) ho
    (.inr (by simp [hss])) ?_) fun t ⟨e, kt⟩ => ?_
  · have : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hk')
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ this) (by simp only [List.length_cons, List.length_nil]; omega_using [hlt])
  · refine ⟨?_, h.of_keeps kt (by decide) (by decide) (by decide) (by decide)⟩
    rw [accVal_eq]; exact e

/-! ## The reduction -/

theorem subz_ok (s : State) (d n m : Reg) : WP isa (.block [.sub .x d n m]) s fun t =>
    (t.gpr d).toNat = (2 ^ 64 + (s.gpr n).toNat - (s.gpr m).toNat) % 2 ^ 64 ∧ Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl, rfl⟩⟩
  rw [RegUpd.gpr_write_self]
  have hn := (s.gpr n).isLt
  have hm := (s.gpr m).isLt
  simp only [BitVec.setWidth_eq, BitVec.toNat_sub]
  omega_using [hn, hm]

theorem fold_arith {L t f e w0 w1 b V L' c : Nat} (ht : t < 2 ^ 31) (hf : f = t * 2 ^ 32 % 2 ^ 64)
    (he : e = (2 ^ 64 + f - t) % 2 ^ 64) (h0 : w0 + e = 2 ^ 64 * b) (hw0 : w0 < 2 ^ 64) (hb : b ≤ 1)
    (h1 : w1 = (2 ^ 64 + f - b) % 2 ^ 64) (hL : L < 2 ^ 384) (hV : V = L + 2 ^ 384 * t)
    (hs : L' + 2 ^ 384 * c = L + (w0 + 2 ^ 64 * w1 + 2 ^ 128 * t)) :
    L' + 2 ^ 384 * c < 2 * p384 ∧ (L' + 2 ^ 384 * c) % p384 = V % p384 := by
  obtain hf' : f = t * 2 ^ 32 := by omega_using [hf, ht]
  subst hf'
  obtain he' : e + t = t * 2 ^ 32 := by omega_using [he, ht]
  obtain hw1 : w1 + b = t * 2 ^ 32 := by omega_using [h1, h0, hw0, he', hb, ht]
  have hk : w0 + 2 ^ 64 * w1 + 2 ^ 128 * t = t * (2 ^ 384 - p384) := by
    rw [show 2 ^ 384 - p384 = 2 ^ 128 + 2 ^ 96 - 2 ^ 32 + 1 by decide]
    omega_using [h0, hw1, he']
  rw [hs, hk]
  have hp : 2 ^ 384 - p384 < 2 ^ 129 := by decide
  have hp' : 2 ^ 384 + 2 ^ 160 < 2 * p384 := by decide
  have hp'' : p384 + (2 ^ 384 - p384) = 2 ^ 384 := by decide
  generalize 2 ^ 384 - p384 = k at *
  refine ⟨?_, ?_⟩
  · have : t * k ≤ 2 ^ 31 * 2 ^ 129 := Nat.mul_le_mul (Nat.le_of_lt ht) (Nat.le_of_lt hp)
    omega_using [this, hL, hp']
  · rw [hV, ← hp'', show L + (p384 + k) * t = L + t * k + p384 * t by
      rw [Nat.add_mul, Nat.mul_comm k]; omega, Nat.add_mul_mod_self_left]

theorem fold_ok {s₀ s : State} {A B : Nat} (h : Opnd s₀ A B s) (ht : (s.gpr .x14).toNat < 2 ^ 31) :
    WP isa (.block fold) s fun t => accVal t < 2 * p384 ∧ accVal t % p384 = accVal s % p384 ∧
      Keeps linW s₀ t ∧ t.gpr .x7 = 0 := by
  simp only [fold, List.append_assoc, List.cons_append, List.nil_append]
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (lslk_ok s .x1 .x14 (by decide)) fun s₁ ⟨e₁, k₁⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (subz_ok s₁ .x2 .x1 .x14) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [show ∀ is : List Instr, Instr.subs .x .x3 .x7 .x2 :: is = P384Field.subs true [.x3] [.x7] [.x2] ++ is from
    fun _ => rfl, WP.block_append_iff]
  refine WP.mono (subs_ok true [.x3] [.x7] [.x2] (s := s₂) (.inr (by simp)) rfl rfl (by decide)) fun s₃ ⟨e₃, k₃⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (sbc_ok s₃ .x4 .x1 .x7) fun s₄ ⟨e₄, k₄, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adds_ok true sw sw [.x3, .x4, .x14, .x7, .x7, .x7] (s := s₄) (.inr (by simp)) rfl rfl (by decide))
    fun s₅ ⟨e₅, k₅⟩ => ?_
  refine WP.mono (adc_ok s₅ .x14 .x7 .x7) fun t ⟨e₆, k₆, _⟩ => ?_
  have K₄ : Keeps [.x1, .x2, .x3, .x4] s s₄ := (k₁.mono (by decide)).trans <| (k₂.mono (by decide)).trans <|
    (k₃.mono (by decide)).trans (k₄.mono (by decide))
  have K : Keeps linW s₀ t := h.keep.trans <| (K₄.mono (by decide)).trans <| (k₅.mono (by decide)).trans
    (k₆.mono (by decide))
  have z₄ : s₄.gpr .x7 = 0 := by rw [K₄.gpr _ (by decide), h.z]
  have z₅ : s₅.gpr .x7 = 0 := by rw [k₅.gpr _ (by decide), z₄]
  have z₃ : s₃.gpr .x7 = 0 := by
    rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide), h.z]
  have z₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), h.z]
  have z0 : (0 : BitVec 64).toNat = 0 := rfl
  rw [k₁.gpr .x14 (by decide)] at e₂
  rw [z₃, z0, Nat.sub_zero, k₃.gpr .x1 (by decide), k₂.gpr .x1 (by decide)] at e₄
  simp only [regsVal, z₂, z0, ite_true, Bool.not_true, Bool.toNat_false, Nat.add_zero, Nat.mul_zero, Nat.zero_add,
    List.length_singleton, Nat.mul_one] at e₃
  rw [z₅, z0, Nat.zero_add] at e₆
  have hc5 := Bool.toNat_le s₅.c
  rw [Nat.mod_eq_of_lt (by omega_using [hc5])] at e₆
  rw [regsVal_keep K₄ (by decide)] at e₅
  have x3 : s₄.gpr .x3 = s₃.gpr .x3 := k₄.gpr _ (by decide)
  have hk : regsVal s₄ [.x3, .x4, .x14, .x7, .x7, .x7] =
      (s₃.gpr .x3).toNat + 2 ^ 64 * (s₄.gpr .x4).toNat + 2 ^ 128 * (s.gpr .x14).toNat := by
    simp only [regsVal, z₄, z0, K₄.gpr .x14 (by decide), x3, Nat.mul_zero, Nat.add_zero, Nat.mul_add,
      ← Nat.mul_assoc, Nat.reduceMul, Nat.reducePow, Nat.add_assoc]
  rw [hk] at e₅
  have hL := regsVal_lt s sw
  have hr := fold_arith (V := accVal s) ht e₁ e₂ e₃ (s₃.gpr .x3).isLt (Bool.toNat_le _) e₄ hL rfl
    (L' := regsVal s₅ sw) (c := s₅.c.toNat) (by
      simpa only [ite_true, Bool.toNat_false, Nat.add_zero, List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceMul] using e₅)
  have hv : accVal t = regsVal s₅ sw + 2 ^ 384 * s₅.c.toNat := by
    unfold accVal; rw [regsVal_keep k₆ (by decide), e₆]
  rw [hv]
  exact ⟨hr.1, hr.2, K, by rw [k₆.gpr _ (by decide), z₅]⟩

/-- The sum `V`, below `2^415`, modulo `p`, stored. -/
theorem finish_ok {s₀ s : State} {base : Addr} {size A B : Nat} (hs : Scr s₀ base size)
    (hM : ModOkA M size p384 s₀.mem base) (hMA : ModA M) {o : Nat} (ho : o + 48 ≤ size) (ho8 : o % 8 = 0)
    (h : Opnd s₀ A B s) {V : Nat} (hV : accVal s = V) (hlt : V < 2 ^ 384 * 2 ^ 31) :
    WP isa (.block (finish o)) s fun t => OpKeepX base o s₀ t ∧ wordsVal t.mem base o 6 = V % p384 := by
  subst hV
  simp only [finish, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok h (by unfold accVal at hlt; omega_using [hlt])) fun s₁ ⟨l₁, e₁, k₁, z₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (csubR_ok hs₁ (M := M) (m := p384) (ts := sw) (top := .x14) rfl (by decide) (by decide)
    (by unfold Fresh; decide) hM.mo hMA.mo z₁ (by rw [k₁.mem]; exact hM.val) l₁) fun s₂ ⟨e₂, k₂⟩ => ?_
  have e₂' : regsVal s₂ sw = accVal s % p384 := e₂.trans e₁
  refine WP.mono (stores_ok sw (hs₁.of_keeps k₂ (by decide)) (by simpa using ho) ho8 (by decide))
    fun t ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [k₃.rd, k₂.rd, k₁.rd], by rw [k₃.wr, k₂.wr, k₁.wr], by rw [k₃.sp, k₂.sp, k₁.sp],
    fun x hx _ => by rw [O₃ x hx, k₂.mem, k₁.mem]⟩, e₃.trans e₂'⟩
  have sub₁ : ∀ q ∈ linW, q ∈ clobX := by decide
  have sub₂ : ∀ q ∈ Reg.x2 :: .x17 :: sw ++ dRegs M.n, q ∈ clobX := by decide
  rw [k₃.gpr r (by simp), k₂.gpr r fun h => hr (sub₂ r h), k₁.gpr r fun h => hr (sub₁ r h)]

/-! ## The combinations -/

theorem b_le {B' B : Nat} (h : B' + B = p384) : B' ≤ p384 := by omega_using [h]

/-- `[o] = 9 [a] - 8 [b]`, `8 (p - [b])` in place of `-8 [b]`. -/
theorem lin98_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hM : ModOkA M size p384 s.mem base)
    (hMA : ModA M) {o a b : Nat} (ho : o + 48 ≤ size) (ha : a + 48 ≤ size) (hb : b + 48 ≤ size) (ho8 : o % 8 = 0)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hA : wordsVal s.mem base a 6 < p384) (hB : wordsVal s.mem base b 6 < p384) :
    WP isa (.block (lin98 o a b)) s fun t => OpKeepX base o s t ∧
      wordsVal t.mem base o 6 = (9 * wordsVal s.mem base a 6 + 8 * (p384 - wordsVal s.mem base b 6)) % p384 := by
  simp only [lin98, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (operands_ok hs hM.mo hMA.mo hM.val ha hb ha8 hb8 hB) fun s₁ h₁ => ?_
  have hb' := h₁.b
  have hpl : p384 < 2 ^ 384 := by decide
  rw [WP.block_append_iff]
  refine WP.mono (sum_ok h₁ aw bw rfl rfl (by decide)) fun s₂ ⟨e₂, h₂⟩ => ?_
  rw [h₁.a] at e₂
  rw [WP.block_append_iff]
  refine WP.mono (shlAcc_ok h₂ (k := 3) (by decide) (by decide) (by rw [e₂]; omega_using [hA, hb', hpl]))
    fun s₃ ⟨e₃, h₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (more_ok h₃ aw rfl (by decide) (by rw [e₃, e₂, h₃.a]; omega_using [hA, hb', hpl]))
    fun s₄ ⟨e₄, h₄⟩ => ?_
  rw [e₃, e₂, h₃.a] at e₄
  exact finish_ok hs hM hMA ho ho8 h₄ (by rw [e₄]; omega_using [hb']) (by omega_using [hA, hpl])

/-- `[o] = 4 [a] - [b]`, `p - [b]` in place of `-[b]`. -/
theorem lin41_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hM : ModOkA M size p384 s.mem base)
    (hMA : ModA M) {o a b : Nat} (ho : o + 48 ≤ size) (ha : a + 48 ≤ size) (hb : b + 48 ≤ size) (ho8 : o % 8 = 0)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hA : wordsVal s.mem base a 6 < p384) (hB : wordsVal s.mem base b 6 < p384) :
    WP isa (.block (lin41 o a b)) s fun t => OpKeepX base o s t ∧
      wordsVal t.mem base o 6 = (4 * wordsVal s.mem base a 6 + 1 * (p384 - wordsVal s.mem base b 6)) % p384 := by
  simp only [lin41, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (operands_ok hs hM.mo hMA.mo hM.val ha hb ha8 hb8 hB) fun s₁ h₁ => ?_
  have hb' := h₁.b
  have hpl : p384 < 2 ^ 384 := by decide
  rw [WP.block_append_iff]
  refine WP.mono (shlOf_ok h₁ (k := 2) (by decide) (by decide) .x1 [.x3, .x4, .x5, .x6, .x16] rfl (by decide))
    fun s₂ ⟨e₂, h₂⟩ => ?_
  rw [show regsVal s₁ [.x1, .x3, .x4, .x5, .x6, .x16] = _ from h₁.a] at e₂
  rw [WP.block_append_iff]
  refine WP.mono (more_ok h₂ bw rfl (by decide) (by have := h₂.b; rw [e₂]; omega_using [hA, this, hpl]))
    fun s₃ ⟨e₃, h₃⟩ => ?_
  have hb₂ := h₂.b
  rw [e₂] at e₃
  exact finish_ok hs hM hMA ho ho8 h₃ (by rw [e₃]; omega_using [hb₂]) (by omega_using [hA, hpl])

/-- `[o] = 3 [a] - 8 [b]`, `8 (p - [b])` in place of `-8 [b]`. -/
theorem lin38_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hM : ModOkA M size p384 s.mem base)
    (hMA : ModA M) {o a b : Nat} (ho : o + 48 ≤ size) (ha : a + 48 ≤ size) (hb : b + 48 ≤ size) (ho8 : o % 8 = 0)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hA : wordsVal s.mem base a 6 < p384) (hB : wordsVal s.mem base b 6 < p384) :
    WP isa (.block (lin38 o a b)) s fun t => OpKeepX base o s t ∧
      wordsVal t.mem base o 6 = (3 * wordsVal s.mem base a 6 + 8 * (p384 - wordsVal s.mem base b 6)) % p384 := by
  simp only [lin38, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (operands_ok hs hM.mo hMA.mo hM.val ha hb ha8 hb8 hB) fun s₁ h₁ => ?_
  have hb' := h₁.b
  have hpl : p384 < 2 ^ 384 := by decide
  rw [WP.block_append_iff]
  refine WP.mono (shlOf_ok h₁ (k := 2) (by decide) (by decide) .x17 [.x21, .x22, .x23, .x24, .x25] rfl (by decide))
    fun s₂ ⟨e₂, h₂⟩ => ?_
  have e₂' : accVal s₂ = 2 ^ 2 * regsVal s₁ bw := e₂
  rw [WP.block_append_iff]
  refine WP.mono (more_ok h₂ aw rfl (by decide) (by rw [e₂', h₂.a]; omega_using [hA, hb', hpl])) fun s₃ ⟨e₃, h₃⟩ => ?_
  rw [e₂', h₂.a] at e₃
  rw [WP.block_append_iff]
  refine WP.mono (shlAcc_ok h₃ (k := 1) (by decide) (by decide) (by rw [e₃]; omega_using [hA, hb', hpl]))
    fun s₄ ⟨e₄, h₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (more_ok h₄ aw rfl (by decide) (by rw [e₄, e₃, h₄.a]; omega_using [hA, hb', hpl]))
    fun s₅ ⟨e₅, h₅⟩ => ?_
  rw [e₄, e₃, h₄.a] at e₅
  exact finish_ok hs hM hMA ho ho8 h₅ (by rw [e₅]; omega_using [hb']) (by omega_using [hA, hpl])

/-! ## In the window's field -/

/-- An operation's result as the window's field element. -/
theorem cms_ok {size m : Nat} [NeZero m] (hmp : m = p384) {Sl : Nat → Prop} (hL : Lay M size Sl) {base : Addr}
    {V : List Nat} {E : Nat → Fin m} {s t : State} (hI : Inv M base size m Sl V E s) {o a b c d : Nat} (ho : Sl o)
    (ha : a ∈ V) (hb : b ∈ V) (hk : OpKeepX base o s t)
    (he : wordsVal t.mem base o 6 = (c * wordsVal s.mem base a 6 + d * (p384 - wordsVal s.mem base b 6)) % p384) :
    Inv M base size m Sl (o :: V) (Function.update E o (smulN c (E a) - smulN d (E b))) t := by
  rw [← hmp] at he
  have hb' := hI.lt b hb
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have he' : wordsVal t.mem base o M.n = (c * wordsVal s.mem base a M.n + d * (m - wordsVal s.mem base b M.n)) % m := he
  refine Ops.Inv.updateX hL hI ho hk ?_ ?_
  · rw [he']; exact Nat.mod_lt _ hm
  · rw [he', toM_cms _ c _ d _ (Nat.le_of_lt hb'), hI.val a ha, hI.val b hb]

end VG.Proof.P384.Linear
