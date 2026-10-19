module

public import VerifiedGarbage.Proof.Mont.X86.WindowBody
public import VerifiedGarbage.Proof.Mont.X86.Exponentiate

/-! # Exponentiation by fixed 4-bit windows, as `exponentiate` -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86

/-- The exponent's next window, from its top bits. -/
theorem window_exponent (X P : Nat) (hP : 0 < P) : X * 16 / P = 16 * (X / P) + X % P * 16 / P := by
  have e : X * 16 = X % P * 16 + P * (16 * (X / P)) := by
    have := Nat.mod_add_div X P
    calc X * 16 = (X % P + P * (X / P)) * 16 := by rw [this]
      _ = _ := by rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (X / P) 16]
  rw [e, Nat.add_mul_div_left _ _ hP, Nat.add_comm]

theorem window_power (b c w : Nat) : (b ^ c) ^ 16 * b ^ w = b ^ (16 * c + w) := by
  rw [← Nat.pow_mul, ← Nat.pow_add, Nat.mul_comm c 16]

/-- `8k` windows cover the exponent. -/
theorem window_all (E k : Nat) : E * 16 ^ (8 * k) / 2 ^ (32 * k) = E := by
  rw [show (16 : Nat) ^ (8 * k) = 2 ^ (32 * k) by
    rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_mul]; congr 1; omega]
  exact Nat.mul_div_cancel _ (Nat.two_pow_pos _)

def windowRanges (n expWords tab : Nat) : List (Nat × Nat) :=
  exponentRanges n expWords ++ [(tab, 128 * n)]

structure WindowInv (n size m k E b steps i tab : Nat) (base : Addr) (s t : State) : Prop where
  context : Context n m base size t
  counter : t.gpr .esi = BitVec.ofNat 32 (steps - i)
  exponent : val32 t.mem base (slot n 8) k = E * 16 ^ i % 2 ^ (32 * k)
  value : wordsVal t.mem base (slot n 6) n = b ^ (E * 16 ^ i / 2 ^ (32 * k)) * 2 ^ (64 * n) % m
  table : ∀ j < 16, wordsVal t.mem base (entry n tab j) n = b ^ j * 2 ^ (64 * n) % m
  mem : Outs base (exponentRanges n k) s.mem t.mem
  keeps : Keeps powerClob s t

theorem windowStep_ok {n size m tab k b y c : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (W : WinLay n tab size) (hk0 : 0 < k) (hk : k ≤ 2 * n)
    (ht : ∀ j < 16, wordsVal s.mem base (entry n tab j) n = b ^ j * 2 ^ (64 * n) % m)
    (hy : wordsVal s.mem base (slot n 6) n = y * 2 ^ (64 * n) % m)
    (hc0 : 0 < c) (hc32 : c < 2 ^ 32) (hc : s.gpr .esi = BitVec.ofNat 32 c) :
    WP isa (windowStep n k tab) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 (c - 1) ∧ t.zf = some (decide (c = 1)) ∧
      Context n m base size t ∧
      wordsVal t.mem base (slot n 6) n =
        y ^ 16 * b ^ (val32 s.mem base (slot n 8) k * 16 / 2 ^ (32 * k)) * 2 ^ (64 * n) % m ∧
      val32 t.mem base (slot n 8) k = val32 s.mem base (slot n 8) k * 16 % 2 ^ (32 * k) ∧
      (∀ j < 16, wordsVal t.mem base (entry n tab j) n = b ^ j * 2 ^ (64 * n) % m) ∧
      Outs base (exponentRanges n k) s.mem t.mem ∧ Keeps powerClob s t := by
  unfold windowStep
  refine WP.seq (WP.mono (windowBody_ok h W hk0 hk ht hy) fun u ⟨cu, Y, E, T, O, K⟩ => ?_)
  have count : u.gpr .esi = BitVec.ofNat 32 c := (K.1 .esi (by decide)).trans hc
  refine wp_subS rfl fun v uv _ => ?_
  refine wp_cmpS rfl fun t ft zt => WP.block_nil ?_
  have mt : t.mem = u.mem := ft.mem.trans uv.mem
  have kt : Keeps powerClob u t := (uv.keeps.mono (by decide)).trans (ft.keeps _)
  have ct : Context n m base size t := ⟨cu.scr.of_keeps kt (by decide), cu.size_le,
    mt ▸ cu.modulus, cu.gt_one, mt ▸ cu.inverse⟩
  refine ⟨?_, ?_, ct, mt ▸ Y, mt ▸ E, mt ▸ T, mt ▸ O, (K.mono (by decide)).trans kt⟩
  · rw [ft.gpr, uv.gpr, count, counter_sub hc32 hc0]
  · rw [zt, uv.gpr, count, counter_sub hc32 hc0, counter_zero hc32 hc0]

theorem windowLoop_ok {n size m tab k b : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (W : WinLay n tab size) (hk0 : 0 < k) (hk : k ≤ 2 * n)
    (ht : ∀ j < 16, wordsVal s.mem base (entry n tab j) n = b ^ j * 2 ^ (64 * n) % m)
    (hy : wordsVal s.mem base (slot n 6) n = 2 ^ (64 * n) % m)
    (hk32 : 8 * k < 2 ^ 32) (hc : s.gpr .esi = BitVec.ofNat 32 (8 * k)) :
    WP isa (.loop (windowStep n k tab) .ne) s
      (WindowInv n size m k (val32 s.mem base (slot n 8) k) b (8 * k) (8 * k) tab base s) := by
  let steps := 8 * k
  let E := val32 s.mem base (slot n 8) k
  have hE : E < 2 ^ (32 * k) := val32_lt _ _ _ _
  have hspos : 0 < steps := by dsimp [steps]; omega
  have init : WindowInv n size m k E b steps 0 tab base s s := by
    refine ⟨h, ?_, ?_, ?_, ht, Outs.refl _ _ _, Keeps.refl _ _⟩
    · simpa only [Nat.sub_zero] using hc
    · rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hE]
    · rw [Nat.pow_zero, Nat.mul_one, Nat.div_eq_of_lt hE, Nat.pow_zero, Nat.one_mul, hy]
  refine WP.loop (M := isa)
    (fun c t => ∃ i, c = steps - i ∧ i < steps ∧ WindowInv n size m k E b steps i tab base s t)
    ?_ steps s ⟨0, rfl, hspos, init⟩
  rintro c t ⟨i, rfl, hi, I⟩
  refine WP.mono (windowStep_ok I.context W hk0 hk I.table I.value (by omega)
    (by dsimp [steps] at *; omega) I.counter)
    fun u ⟨count, zf, C, Y', E', T', O, K⟩ => ?_
  have next : WindowInv n size m k E b steps (i + 1) tab base s u := by
    refine ⟨C, ?_, ?_, ?_, T', I.mem.trans O, I.keeps.trans K⟩
    · rw [count, show steps - i - 1 = steps - (i + 1) by omega]
    · rw [E', I.exponent, Nat.pow_succ, ← Nat.mul_assoc, Nat.mod_mul_mod]
    · rw [Y', I.exponent, window_power, Nat.pow_succ, ← Nat.mul_assoc,
        window_exponent (E * 16 ^ i) _ (Nat.two_pow_pos _)]
  by_cases hdone : i + 1 = steps
  · refine .inl ⟨?_, ?_⟩
    · have eq : steps - i = 1 := by omega
      simp only [eval, zf, eq, decide_true, Option.map_some, Bool.not_true]
    · change WindowInv n size m k E b steps steps tab base s u
      rw [hdone] at next
      exact next
  · refine .inr ⟨?_, steps - (i + 1), by omega, i + 1, rfl, by omega, next⟩
    have ne : steps - i ≠ 1 := by omega
    simp only [eval, zf, decide_eq_false ne, Option.map_some, Bool.not_false]

theorem windowExponentiate_ok {n size m expWords tab : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (W : WinLay n tab size) (he : 0 < expWords) (hen : expWords ≤ 2 * n)
    (hsteps : 8 * expWords < 2 ^ 32)
    (hone : wordsVal s.mem base (slot n 3) n = 1)
    (hr2 : wordsVal s.mem base (slot n 4) n = 2 ^ (128 * n) % m) :
    WP isa (windowExponentiate n expWords tab) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) expWords % m ∧
      Outs base (windowRanges n expWords tab) s.mem t.mem ∧ Keeps powerClob s t := by
  have hm0 : 0 < m := by have := h.gt_one; omega
  have cn : contextBytes n ≤ 2 ^ 64 := by have := h.size_le; have := h.scr.nowrap; omega
  have ctx := W.ctx
  unfold windowExponentiate
  refine WP.seq (WP.mono (context_mul_ok h (o := 6) (a := 4) (b := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hone]; exact h.gt_one)) fun s₁ ⟨c₁, K₁, lt₁, V₁⟩ => ?_)
  have Y₁ : wordsVal s₁.mem base (slot n 6) n = 2 ^ (64 * n) % m :=
    mont_one h.coprime lt₁ (by rw [V₁, hone, hr2, Nat.mul_one, Nat.mod_mod])
  have R₁ : wordsVal s₁.mem base (slot n 4) n = 2 ^ (128 * n) % m := by
    rw [context_slot_val h (by decide) (by decide) (by decide) (by decide) K₁, hr2]
  have B₁ := context_slot_val h (i := 5) (by decide) (by decide) (by decide) (by decide) K₁
  have E₁ := context_slot_val32 h (i := 8) (by decide) hen (by decide) (by decide) (by decide) K₁
  have O₁ := context_slot_val h (i := 3) (by decide) (by decide) (by decide) (by decide) K₁
  refine WP.seq (WP.mono (context_mul_ok c₁ (o := 5) (a := 5) (b := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [R₁]; exact Nat.mod_lt _ hm0)) fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  have B₂ : wordsVal s₂.mem base (slot n 5) n =
      wordsVal s.mem base (slot n 5) n * 2 ^ (64 * n) % m :=
    mont_encode h.coprime lt₂ (by rw [V₂, R₁, B₁])
  have Y₂ : wordsVal s₂.mem base (slot n 6) n = 2 ^ (64 * n) % m := by
    rw [context_slot_val c₁ (by decide) (by decide) (by decide) (by decide) K₂, Y₁]
  have E₂ : val32 s₂.mem base (slot n 8) expWords = val32 s.mem base (slot n 8) expWords := by
    rw [context_slot_val32 c₁ (by decide) hen (by decide) (by decide) (by decide) K₂, E₁]
  have O₂ : wordsVal s₂.mem base (slot n 3) n = 1 := by
    rw [context_slot_val c₁ (by decide) (by decide) (by decide) (by decide) K₂, O₁, hone]
  refine WP.seq (WP.mono (buildTable_ok c₂ W Y₂ B₂) fun s₃ ⟨c₃, T₃, Ot₃, K₃⟩ => ?_)
  have Y₃ : wordsVal s₃.mem base (slot n 6) n = 2 ^ (64 * n) % m := by
    rw [tableRanges_val Ot₃ (by decide) (by decide) (by decide) (by decide) ctx cn, Y₂]
  have E₃ : val32 s₃.mem base (slot n 8) expWords = val32 s.mem base (slot n 8) expWords := by
    rw [tableRanges_val32 Ot₃ (by decide) hen (by decide) (by decide) (by decide) ctx cn, E₂]
  have O₃ : wordsVal s₃.mem base (slot n 3) n = 1 := by
    rw [tableRanges_val Ot₃ (by decide) (by decide) (by decide) (by decide) ctx cn, O₂]
  refine WP.seq (wp_movS rfl fun s₄ u₄ _ => WP.block_nil ?_)
  have c₄ : Context n m base size s₄ := ⟨c₃.scr.of_keeps u₄.keeps (by decide), c₃.size_le,
    u₄.mem ▸ c₃.modulus, c₃.gt_one, u₄.mem ▸ c₃.inverse⟩
  refine WP.seq (WP.mono (windowLoop_ok c₄ W he hen (u₄.mem ▸ T₃) (u₄.mem ▸ Y₃) hsteps u₄.gpr)
    fun s₅ I => ?_)
  have O₅ : wordsVal s₅.mem base (slot n 3) n = 1 := by
    rw [exponentRanges_one I.mem cn, u₄.mem, O₃]
  refine WP.mono (context_mul_ok I.context (o := 6) (a := 6) (b := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [O₅]; exact h.gt_one)) fun t ⟨ct, Kt, ltt, Vt⟩ => ?_
  refine ⟨ct, ?_, ?_, ?_⟩
  · have fin := I.value
    rw [window_all, u₄.mem, E₃] at fin
    have v := VG.Proof.Dsa.mont_decode (A := wordsVal s₅.mem base (slot n 6) n)
      (out := wordsVal t.mem base (slot n 6) n) h.coprime
      (by rw [fin, Nat.mod_mod]) (by rw [Vt, O₅])
    rw [Nat.mod_eq_of_lt ltt] at v
    exact v
  · have sub (rs : List (Nat × Nat)) (hr : ∀ r ∈ rs, r ∈ windowRanges n expWords tab)
        {m m' : Mem} (O : Outs base rs m m') : Outs base (windowRanges n expWords tab) m m' := O.mono hr
    have o₁ := sub _ (fun r hr => List.mem_append_left _ hr) (exponentRanges_op (expWords := expWords) K₁ (.inr rfl))
    have o₂ := sub _ (fun r hr => List.mem_append_left _ hr) (exponentRanges_op (expWords := expWords) K₂ (.inl rfl))
    have o₃ := sub _ (by
      intro r hr
      simp only [tableRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [windowRanges, exponentRanges, productRanges]) Ot₃
    have o₄ : Outs base (windowRanges n expWords tab) s₃.mem s₄.mem := u₄.mem ▸ Outs.refl _ _ _
    have o₅ := sub _ (fun r hr => List.mem_append_left _ hr) I.mem
    have o₆ := sub _ (fun r hr => List.mem_append_left _ hr) (exponentRanges_op (expWords := expWords) Kt (.inr rfl))
    exact ((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆
  · exact ((((((OpKeep.keeps K₁).trans (OpKeep.keeps K₂)).trans K₃).mono (by decide)).widen u₄.keeps).trans
      I.keeps).trans ((OpKeep.keeps Kt).mono (by decide))

end VG.Proof.Mont.X86.Dynamic
