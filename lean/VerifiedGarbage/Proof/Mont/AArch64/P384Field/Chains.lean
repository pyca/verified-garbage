module

public import VerifiedGarbage.Impl.Mont.AArch64.P384Field
public import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# P-384's field arithmetic on AArch64: the chains

Each chain of `Impl/Mont/AArch64/P384Field.lean` run by induction on its
registers, any that do not overwrite what the rest of the chain reads: sums and
differences (`adds_ok`, `subs_ok`), masks (`ands_ok`), the low or high words of
a row of products added (`muls_ok`), and whole rows (`row0_ok`, `row_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.AArch64.P384Field

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P384Field
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut Word64.addCarry_value)

/-- The registers of a chain's operands are read before they are written. -/
def ChainOk : List Reg → List Reg → List Reg → Prop
  | d :: ds, _ :: ns, _ :: ms => d ∉ ds ∧ d ∉ ns ∧ d ∉ ms ∧ ChainOk ds ns ms
  | _, _, _ => True

instance : ∀ ds ns ms, Decidable (ChainOk ds ns ms)
  | [], _, _ => .isTrue (by simp [ChainOk])
  | _ :: _, [], _ => .isTrue (by simp [ChainOk])
  | _ :: _, _ :: _, [] => .isTrue (by simp [ChainOk])
  | d :: ds, _ :: ns, _ :: ms => by
    have := instDecidableChainOk ds ns ms
    unfold ChainOk; infer_instance

theorem Keeps.refl (s : State) : Keeps [] s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem regsVal_keep {W rs : List Reg} {s t : State} (k : Keeps W s t) (h : ∀ r ∈ rs, r ∉ W) :
    regsVal t rs = regsVal s rs := regsVal_congr fun r hr => k.gpr r (h r hr)

/-- `ds = ns + ms + c`, and the carry out. -/
theorem adds_ok : ∀ (first : Bool) (ds ns ms : List Reg) {s : State}, (first = false ∨ ds ≠ []) →
    ns.length = ds.length → ms.length = ds.length → ChainOk ds ns ms →
    WP isa (.block (adds first ds ns ms)) s fun t =>
      regsVal t ds + 2 ^ (64 * ds.length) * t.c.toNat =
        regsVal s ns + regsVal s ms + (if first then false else s.c).toNat ∧ Keeps ds s t
  | first, [], [], [], s, h, _, _, _ => by
    rcases h with rfl | h
    · exact WP.block_nil ⟨by simp [regsVal], Keeps.refl s⟩
    · exact absurd rfl h
  | _, [], _ :: _, _, _, _, hl, _, _ => absurd hl (by simp)
  | _, [], [], _ :: _, _, _, _, hl, _ => absurd hl (by simp)
  | _, _ :: _, [], _, _, _, hl, _, _ => absurd hl (by simp)
  | _, _ :: _, _ :: _, [], _, _, _, hl, _ => absurd hl (by simp)
  | first, d :: ds, n :: ns, m :: ms, s, _, hn, hm, ho => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hn hm
    obtain ⟨o1, o2, o3, o4⟩ := ho
    rw [adds, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (addc_ok s d n m first rfl) fun u ⟨e₁, c₁, k₁⟩ => ?_
    refine WP.mono (adds_ok false ds ns ms (.inl rfl) hn hm o4) fun t ⟨e₂, k₂⟩ => ?_
    have hv := Word64.addCarry_value (s.gpr n) (s.gpr m) (if first then false else s.c)
    rw [← e₁, ← c₁] at hv
    rw [regsVal_keep k₁ fun r hr h => o2 (List.mem_singleton.mp h ▸ hr),
      regsVal_keep k₁ fun r hr h => o3 (List.mem_singleton.mp h ▸ hr)] at e₂
    simp only [Bool.false_eq_true, ite_false] at e₂
    refine ⟨?_, (k₁.mono (by simp)).trans (k₂.mono fun r hr => List.mem_cons_of_mem _ hr)⟩
    simp only [regsVal, List.length_cons, pow64_succ, k₂.gpr d o1]
    rw [Nat.mul_assoc]
    omega_using [e₂, hv]

/-- `ds = ns - ms - b`, and the borrow out: the carry is its complement. -/
theorem subs_ok : ∀ (first : Bool) (ds ns ms : List Reg) {s : State}, (first = false ∨ ds ≠ []) →
    ns.length = ds.length → ms.length = ds.length → ChainOk ds ns ms →
    WP isa (.block (subs first ds ns ms)) s fun t =>
      regsVal t ds + regsVal s ms + (!(if first then true else s.c)).toNat =
        regsVal s ns + 2 ^ (64 * ds.length) * (!t.c).toNat ∧ Keeps ds s t
  | first, [], [], [], s, h, _, _, _ => by
    rcases h with rfl | h
    · exact WP.block_nil ⟨by simp [regsVal], Keeps.refl s⟩
    · exact absurd rfl h
  | _, [], _ :: _, _, _, _, hl, _, _ => absurd hl (by simp)
  | _, [], [], _ :: _, _, _, _, hl, _ => absurd hl (by simp)
  | _, _ :: _, [], _, _, _, hl, _, _ => absurd hl (by simp)
  | _, _ :: _, _ :: _, [], _, _, _, hl, _ => absurd hl (by simp)
  | first, d :: ds, n :: ns, m :: ms, s, _, hn, hm, ho => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hn hm
    obtain ⟨o1, o2, o3, o4⟩ := ho
    rw [subs, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (subc_ok s d n m first rfl) fun u ⟨e₁, c₁, k₁⟩ => ?_
    refine WP.mono (subs_ok false ds ns ms (.inl rfl) hn hm o4) fun t ⟨e₂, k₂⟩ => ?_
    have hv := sub_borrow (s.gpr n) (s.gpr m) (if first then true else s.c)
    rw [← e₁, ← c₁] at hv
    rw [regsVal_keep k₁ fun r hr h => o2 (List.mem_singleton.mp h ▸ hr),
      regsVal_keep k₁ fun r hr h => o3 (List.mem_singleton.mp h ▸ hr)] at e₂
    simp only [Bool.false_eq_true, ite_false] at e₂
    refine ⟨?_, (k₁.mono (by simp)).trans (k₂.mono fun r hr => List.mem_cons_of_mem _ hr)⟩
    simp only [regsVal, List.length_cons, pow64_succ, k₂.gpr d o1]
    rw [Nat.mul_assoc]
    omega_using [e₂, hv]

/-- `d = n + m + c`, its carry dropped. -/
theorem adc_ok (s : State) (d n m : Reg) :
    WP isa (.block [.adc .x d n m]) s fun t =>
      (t.gpr d).toNat = ((s.gpr n).toNat + (s.gpr m).toNat + s.c.toNat) % 2 ^ 64 ∧ Keeps [d] s t ∧
        t.c = s.c := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Size.bits]
    omega_using []
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr)

/-! ## Products -/

/-- The low words of `x bs`, or the high ones, as a number. -/
def part (hi : Bool) (x : Nat) (s : State) : List Reg → Nat
  | [] => 0
  | b :: bs => (if hi then x * (s.gpr b).toNat / 2 ^ 64 else x * (s.gpr b).toNat % 2 ^ 64) + 2 ^ 64 * part hi x s bs

theorem part_sum (x : Nat) (s : State) : ∀ bs, part false x s bs + 2 ^ 64 * part true x s bs = x * regsVal s bs
  | [] => by simp [part, regsVal]
  | b :: bs => by
    have := part_sum x s bs
    simp only [part, regsVal, Bool.false_eq_true, ite_true, ite_false, Nat.mul_add, Nat.mul_left_comm x] at this ⊢
    have := Nat.mod_add_div (x * (s.gpr b).toNat) (2 ^ 64)
    omega_using [‹part false x s bs + 2 ^ 64 * part true x s bs = x * regsVal s bs›, this]

theorem part_keep {hi : Bool} {x : Nat} {W : List Reg} {s t : State} (k : Keeps W s t) :
    ∀ {bs : List Reg}, (∀ b ∈ bs, b ∉ W) → part hi x t bs = part hi x s bs
  | [], _ => rfl
  | b :: bs, h => by
    simp only [part, k.gpr b (h b (List.mem_cons_self ..)),
      part_keep k fun r hr => h r (List.mem_cons_of_mem _ hr)]

theorem part_append (hi : Bool) (x : Nat) (s : State) : ∀ bs cs,
    part hi x s (bs ++ cs) = part hi x s bs + 2 ^ (64 * bs.length) * part hi x s cs
  | [], cs => by simp [part]
  | b :: bs, cs => by
    rw [List.cons_append, part, part_append hi x s bs cs, part, List.length_cons, pow64_succ, Nat.mul_add,
      Nat.mul_assoc]
    omega_using []

/-- The low or high word of a product, keeping the carry. -/
theorem mulh_ok (s : State) (hi : Bool) (d x b : Reg) :
    WP isa (.block [if hi then .umulh d x b else .mul .x d x b]) s fun t =>
      (t.gpr d).toNat = (if hi then (s.gpr x).toNat * (s.gpr b).toNat / 2 ^ 64
        else (s.gpr x).toNat * (s.gpr b).toNat % 2 ^ 64) ∧ Keeps [d] s t ∧ t.c = s.c := by
  apply WP.of_runBlock
  have hx := (s.gpr x).isLt
  have hb := (s.gpr b).isLt
  cases hi <;> simp only [Bool.false_eq_true, ite_false, ite_true, runBlock_cons, runStep_some, runBlock_nil, exec,
    read_x, Option.some.injEq, exists_eq_left']
  · refine ⟨?_, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl, rfl⟩, rfl⟩
    simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq]
    exact BitVec.toNat_mul ..
  · refine ⟨?_, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl, rfl⟩, rfl⟩
    simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (Nat.mul_lt_mul'' hx hb))

/-- The registers of a chain of products. -/
def MulOk (x : Reg) : List Reg → List Reg → Prop
  | d :: ds, _ :: bs => d ≠ x ∧ d ≠ .x2 ∧ d ∉ ds ∧ d ∉ bs ∧ Reg.x2 ∉ bs ∧ MulOk x ds bs
  | _, _ => True

instance : ∀ x ds bs, Decidable (MulOk x ds bs)
  | _, [], _ => .isTrue (by simp [MulOk])
  | _, _ :: _, [] => .isTrue (by simp [MulOk])
  | x, d :: ds, _ :: bs => by
    have := instDecidableMulOk x ds bs
    unfold MulOk; infer_instance

theorem MulOk_x2 {x : Reg} : ∀ {ds bs : List Reg}, MulOk x ds bs → bs.length = ds.length → ∀ r ∈ ds, r ≠ .x2
  | [], _, _, _ => by simp
  | _ :: _, [], _, hl => absurd hl (by simp)
  | d :: ds, _ :: bs, ⟨_, h, _, _, _, hr⟩, hl => by
    intro r hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact h
    · exact MulOk_x2 hr (by simpa using hl) r hm

/-- `ds += ` the low or high words of `x bs`, and the carry out. -/
theorem muls_ok {x : Reg} (hx : x ≠ .x2) (hi : Bool) : ∀ (first : Bool) (ds bs : List Reg) {s : State},
    (first = false ∨ ds ≠ []) → bs.length = ds.length → MulOk x ds bs →
    WP isa (.block (muls hi x first ds bs)) s fun t =>
      regsVal t ds + 2 ^ (64 * ds.length) * t.c.toNat =
        regsVal s ds + part hi (s.gpr x).toNat s bs + (if first then false else s.c).toNat ∧
      Keeps (.x2 :: ds) s t
  | first, [], [], s, h, _, _ => by
    rcases h with rfl | h
    · exact WP.block_nil ⟨by simp [regsVal, part], (Keeps.refl s).mono (by simp)⟩
    · exact absurd rfl h
  | _, [], _ :: _, _, _, hl, _ => absurd hl (by simp)
  | _, _ :: _, [], _, _, hl, _ => absurd hl (by simp)
  | first, d :: ds, b :: bs, s, _, hl, ho => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := ho
    rw [muls, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (mulh_ok s hi .x2 x b) fun u ⟨e₁, k₁, c₁⟩ => ?_
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (addc_ok u d d .x2 first rfl) fun v ⟨e₂, c₂, k₂⟩ => ?_
    refine WP.mono (muls_ok hx hi false ds bs (.inl rfl) hl o6) fun t ⟨e₃, k₃⟩ => ?_
    have hv := Word64.addCarry_value (u.gpr d) (u.gpr .x2) (if first then false else u.c)
    rw [← e₂, ← c₂, k₁.gpr d (by simpa using o2), e₁, c₁] at hv
    have kv : Keeps [.x2, d] s v := (k₁.mono (by simp)).trans (k₂.mono (by simp))
    rw [regsVal_keep kv (by
        intro r hr h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact absurd rfl (MulOk_x2 o6 (hl ▸ rfl) _ hr)
        · exact o3 hr),
      kv.gpr x (by simp [hx, Ne.symm o1]),
      part_keep kv (by
        intro r hr h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact o5 hr
        · exact o4 hr)] at e₃
    simp only [Bool.false_eq_true, ite_false] at e₃
    refine ⟨?_, (kv.mono (by simp)).trans (k₃.mono (by simp +contextual))⟩
    simp only [regsVal, part, List.length_cons, pow64_succ, k₃.gpr d (by simp [o2, o3])]
    rw [Nat.mul_assoc]
    omega_using [e₃, hv]

/-- `ds = ` the low words of `x bs`. -/
theorem lows_ok {x : Reg} : ∀ (ds bs : List Reg) {s : State}, bs.length = ds.length → x ∉ ds → ChainOk ds bs bs →
    WP isa (.block (lows x ds bs)) s fun t =>
      regsVal t ds = part false (s.gpr x).toNat s bs ∧ Keeps ds s t
  | [], [], s, _, _, _ => WP.block_nil ⟨rfl, Keeps.refl s⟩
  | [], _ :: _, _, hl, _, _ => absurd hl (by simp)
  | _ :: _, [], _, hl, _, _ => absurd hl (by simp)
  | d :: ds, b :: bs, s, hl, hx, ho => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    obtain ⟨o1, o2, -, o4⟩ := ho
    simp only [List.mem_cons, not_or] at hx
    rw [lows, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (mulh_ok s false d x b) fun u ⟨e₁, k₁, _⟩ => ?_
    refine WP.mono (lows_ok ds bs hl hx.2 o4) fun t ⟨e₂, k₂⟩ => ?_
    rw [k₁.gpr x (by simpa using hx.1), part_keep k₁ fun r hr h => o2 (List.mem_singleton.mp h ▸ hr)] at e₂
    refine ⟨?_, (k₁.mono (by simp)).trans (k₂.mono fun r hr => List.mem_cons_of_mem _ hr)⟩
    simp only [regsVal, part, k₂.gpr d o1, e₁, e₂, Bool.false_eq_true, ite_false]

theorem regsVal_single (s : State) (r : Reg) : regsVal s [r] = (s.gpr r).toNat := by simp [regsVal]

/-- The words of a row, the last of them taken modulo `2^64`, are all of a number that fits. -/
theorem row_arith {q Q₁ Q₂ H y c P V : Nat} (e : Q₂ + P * c = Q₁ + H)
    (hV : (q + 2 ^ 64 * Q₁) + 2 ^ 64 * (H + P * y) = V) (hlt : V < 2 ^ 64 * P * 2 ^ 64) :
    (q + 2 ^ 64 * Q₂) + 2 ^ 64 * P * ((y + c) % 2 ^ 64) = V := by
  have hs : (q + 2 ^ 64 * Q₂) + 2 ^ 64 * P * (y + c) = V := by
    rw [← hV, Nat.mul_add, Nat.mul_assoc, Nat.mul_assoc]
    omega_using [e]
  rw [Nat.mod_eq_of_lt, hs]
  exact Nat.lt_of_mul_lt_mul_left (a := 2 ^ 64 * P) (by omega_using [hs, hlt])

theorem prod_lt {x B n : Nat} (hx : x < 2 ^ 64) (hB : B < 2 ^ (64 * (n + 1))) :
    x * B < 2 ^ 64 * 2 ^ (64 * n) * 2 ^ 64 := by
  rw [pow64_succ] at hB
  rw [Nat.mul_comm _ (2 ^ 64)]
  exact Nat.mul_lt_mul'' hx hB

/-- The registers of a row. -/
def RowOk (x q : Reg) (qs : List Reg) (l : Reg) (bs : List Reg) (b : Reg) : Prop :=
  x ≠ .x2 ∧ x ≠ .x7 ∧ x ∉ q :: qs ∧ x ≠ l ∧ l ∉ q :: qs ∧ l ≠ .x2 ∧ l ≠ .x7 ∧ .x7 ∉ q :: qs ∧ .x2 ∉ bs ++ [b] ∧
  (∀ r ∈ bs ++ [b], r ∉ q :: qs ∧ r ≠ l) ∧ (q :: qs).Nodup ∧ .x2 ∉ q :: qs ∧ qs ≠ [] ∧
  MulOk x qs bs ∧ MulOk x (q :: qs) (bs ++ [b]) ∧ ChainOk (q :: qs) (bs ++ [b]) (bs ++ [b]) ∧ bs.length = qs.length

instance (x q : Reg) (qs : List Reg) (l : Reg) (bs : List Reg) (b : Reg) : Decidable (RowOk x q qs l bs b) := by
  unfold RowOk; infer_instance

/-- `q :: qs ++ [l] = x (bs ++ [b])`. -/
theorem row0_ok {s : State} {x q l b : Reg} {qs bs : List Reg} (h : RowOk x q qs l bs b) (hz : s.gpr .x7 = 0) :
    WP isa (.block (row0 x q qs l bs b)) s fun t =>
      regsVal t (q :: qs ++ [l]) = (s.gpr x).toNat * regsVal s (bs ++ [b]) ∧ Keeps (.x2 :: l :: q :: qs) s t := by
  obtain ⟨hx2, hx7, hxq, hxl, hlq, hl2, hl7, h7q, h2b, hbq, hnd, h2q, hqs, hm1, hm2, hc, hlen⟩ := h
  simp only [row0, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (lows_ok (q :: qs) (bs ++ [b]) (by simp [hlen]) hxq hc) fun s₁ ⟨e₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (muls_ok hx2 true true qs bs (.inr hqs) hlen hm1) fun s₂ ⟨e₂, k₂⟩ => ?_
  have xs : s₂.gpr x = s.gpr x := by
    rw [k₂.gpr x (by simp only [List.mem_cons, not_or] at hxq ⊢; exact ⟨hx2, hxq.2⟩), k₁.gpr x hxq]
  have bs' : s₂.gpr b = s.gpr b := by
    have := hbq b (by simp)
    rw [k₂.gpr b (by
      simp only [List.mem_cons, not_or] at this ⊢
      exact ⟨fun e => h2b (by simp [e]), this.1.2⟩), k₁.gpr b this.1]
  have q2 : s₂.gpr q = s₁.gpr q := k₂.gpr q (by
    simp only [List.mem_cons, not_or] at h2q ⊢
    exact ⟨Ne.symm h2q.1, (List.nodup_cons.mp hnd).1⟩)
  have z2 : s₂.gpr .x7 = 0 := by
    rw [k₂.gpr _ (by simp only [List.mem_cons, not_or] at h7q ⊢; exact ⟨by decide, h7q.2⟩), k₁.gpr _ h7q, hz]
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (mulh_ok s₂ true .x2 x b) fun s₃ ⟨e₃, k₃, c₃⟩ => ?_
  refine WP.mono (adc_ok s₃ l .x2 .x7) fun t ⟨e₄, k₄, _⟩ => ?_
  rw [k₁.gpr x hxq, part_keep k₁ (by intro r hr; exact (hbq r (by simp [hr])).1)] at e₂
  rw [e₃, k₃.gpr .x7 (by decide), z2, c₃, xs, bs'] at e₄
  have kt : Keeps (.x2 :: l :: q :: qs) s t :=
    (k₁.mono (by simp +contextual)).trans ((k₂.mono (by simp +contextual)).trans
      ((k₃.mono (by simp)).trans (k₄.mono (by simp))))
  refine ⟨?_, kt⟩
  have keepq : regsVal t (q :: qs) = regsVal s₂ (q :: qs) := by
    rw [regsVal_keep k₄ (by intro r hr h; exact hlq (List.mem_singleton.mp h ▸ hr)),
      regsVal_keep k₃ (by intro r hr h; exact h2q (List.mem_singleton.mp h ▸ hr))]
  rw [regsVal_append, regsVal_single, keepq, e₄]
  have hB := part_sum (s.gpr x).toNat s (bs ++ [b])
  have hlt := prod_lt (s.gpr x).isLt (regsVal_lt s (bs ++ [b]) |> fun h => by
    rw [List.length_append, List.length_singleton] at h; exact h)
  rw [part_append] at hB
  rw [part_append true] at hB
  simp only [part, ite_true, Nat.mul_zero, Nat.add_zero, hlen] at hB e₁ e₂ hlt e₄
  rw [part_append, hlen] at e₁
  simp only [part, Nat.mul_zero, Nat.add_zero] at e₁
  rw [← e₁, regsVal] at hB
  simp only [regsVal, List.length_cons, pow64_succ, q2, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero]
  exact row_arith (by simpa using e₂) hB hlt

/-- `q :: qs ++ [l] = (q :: qs) + x (bs ++ [b])`. -/
theorem row_ok {s : State} {x q l b : Reg} {qs bs : List Reg} (h : RowOk x q qs l bs b) (hz : s.gpr .x7 = 0)
    (hfit : regsVal s (q :: qs) + (s.gpr x).toNat * regsVal s (bs ++ [b]) < 2 ^ (64 * (qs.length + 2))) :
    WP isa (.block (rowAdd x q qs l bs b)) s fun t =>
      regsVal t (q :: qs ++ [l]) = regsVal s (q :: qs) + (s.gpr x).toNat * regsVal s (bs ++ [b]) ∧
      Keeps (.x2 :: l :: q :: qs) s t := by
  obtain ⟨hx2, hx7, hxq, hxl, hlq, hl2, hl7, h7q, h2b, hbq, hnd, h2q, hqs, hm1, hm2, hc, hlen⟩ := h
  simp only [rowAdd, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (muls_ok hx2 false true (q :: qs) (bs ++ [b]) (.inr (by simp)) (by simp [hlen]) hm2)
    fun s₁ ⟨e₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adc_ok s₁ l .x7 .x7) fun s₂ ⟨e₂, k₂, c₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (muls_ok hx2 true true qs bs (.inr hqs) hlen hm1) fun s₃ ⟨e₃, k₃⟩ => ?_
  have k12 : Keeps (.x2 :: l :: q :: qs) s s₂ := (k₁.mono (by simp +contextual)).trans (k₂.mono (by simp))
  have k13 : Keeps (.x2 :: l :: q :: qs) s s₃ := k12.trans (k₃.mono (by simp +contextual))
  simp only [List.mem_cons, not_or] at hxq hlq h7q h2q
  have hx' : x ∉ Reg.x2 :: l :: q :: qs := by simp [hx2, hxl, hxq]
  have h7' : Reg.x7 ∉ Reg.x2 :: l :: q :: qs := by simp [Ne.symm hl7, h7q]
  have hb' : ∀ r ∈ bs ++ [b], r ∉ Reg.x2 :: l :: q :: qs := fun r hr => by
    have := hbq r hr
    simp only [List.mem_cons, not_or] at this ⊢
    exact ⟨fun e => h2b (e ▸ hr), this.2, this.1⟩
  have q2 : s₃.gpr q = s₁.gpr q := by
    rw [k₃.gpr q (by simp [Ne.symm h2q.1, (List.nodup_cons.mp hnd).1]), k₂.gpr q (by simp [Ne.symm hlq.1])]
  have l3 : s₃.gpr l = s₂.gpr l := k₃.gpr l (by simp [hl2, hlq.2])
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (mulh_ok s₃ true .x2 x b) fun s₄ ⟨e₄, k₄, c₄⟩ => ?_
  refine WP.mono (adc_ok s₄ l l .x2) fun t ⟨e₅, k₅, _⟩ => ?_
  have k15 : Keeps (.x2 :: l :: q :: qs) s t :=
    k13.trans ((k₄.mono (by simp)).trans (k₅.mono (by simp)))
  refine ⟨?_, k15⟩
  have qs2 : regsVal s₂ qs = regsVal s₁ qs := regsVal_keep k₂ (by
    intro r hr h; exact hlq.2 (List.mem_singleton.mp h ▸ hr))
  have keepq : regsVal t (q :: qs) = regsVal s₃ (q :: qs) := by
    rw [regsVal_keep k₅ (by
        intro r hr h
        rw [List.mem_singleton.mp h] at hr
        simp only [List.mem_cons] at hr; exact hr.elim hlq.1 hlq.2),
      regsVal_keep k₄ (by
        intro r hr h
        rw [List.mem_singleton.mp h] at hr
        simp only [List.mem_cons] at hr; exact hr.elim h2q.1 h2q.2)]
  rw [k12.gpr x hx', part_keep k12 (fun r hr => hb' r (by simp [hr])), qs2] at e₃
  rw [e₄, k₄.gpr l (by simpa using hl2), l3, c₄, k13.gpr x hx', k13.gpr b (hb' b (by simp)), e₂,
    k₁.gpr .x7 (by simp [h7q]), hz] at e₅
  have hB := part_sum (s.gpr x).toNat s (bs ++ [b])
  rw [part_append] at hB
  rw [part_append true] at hB
  rw [part_append] at e₁
  simp only [part, ite_true, Nat.mul_zero, Nat.add_zero, hlen, Bool.toNat_false] at hB e₁ e₃
  rw [regsVal_append, regsVal_single, keepq, e₅]
  rw [show qs.length + 2 = (qs.length + 1) + 1 from rfl, pow64_succ, pow64_succ] at hfit
  simp only [regsVal, List.length_cons, pow64_succ, q2, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at e₁ ⊢
  have hc1 := Bool.toNat_le s₁.c
  simp only [Bool.false_eq_true, ite_false, ite_true, show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add] at *
  rw [Nat.mod_eq_of_lt (a := s₁.c.toNat) (by omega_using [hc1])] at *
  refine row_arith e₃ ?_ ?_
  · rw [Nat.mul_add (2 ^ (64 * qs.length)), Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc (2 ^ 64) (2 ^ _)]
    omega_using [e₁, hB]
  · rw [regsVal] at hfit; omega_using [hfit]

end VG.Proof.Mont.AArch64.P384Field
