module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Entry
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# ChaCha20-Poly1305 on PPC64LE: the prologue

Saving the registers, moving the arguments, the ChaCha20 state for counter
0, the one-time key and the Poly1305 state for it; and what the later parts
use of memory and of the callees' regions.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.ChaCha20Poly1305.PPC64LE
open VG.Impl.ChaCha20.PPC64LE.Xor (mov)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Spec.ChaCha20 (stateAt)

variable {e : Bool}

theorem savOff_eq : savOff = 464 := rfl
theorem stOff_eq : stOff = 320 := rfl
theorem keyOff_eq : keyOff = 384 := rfl

/-- A register not callee-saved is not a callee-saved one. -/
theorem ne_of_pres {r d : Reg} (hr : r ∈ preserved) (hd : d ∉ preserved := by decide) : r ≠ d := by
  rintro rfl; exact hd hr

/-! ## Memory -/

theorem off_add (p : Addr) (a b : Nat) : off p a + BitVec.ofNat 64 b = off p (a + b) := off_off p a b

/-- A read at `p + d` after a write at `p + e`, elsewhere. -/
theorem readW_writeW_off (m : Mem) (p : Addr) {w w' : Nat} (v : BitVec w') {d e : Nat}
    (hd : d + w / 8 ≤ 2 ^ 64) (he : e + w' / 8 ≤ 2 ^ 64) (h : d + w / 8 ≤ e ∨ e + w' / 8 ≤ d)
    (hw : w / 8 < 2 ^ 64 := by decide) :
    (m.writeW (off p e) v).readW (off p d) w = m.readW (off p d) w :=
  Mem.readW_writeW_sep (Offset.sep p h hd he) hw

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- A Poly1305 state outside a frame is unchanged. -/
theorem Repr.frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr}
    (hd : ∀ r ∈ rs, (⟨P, 128⟩ : Region).Disjoint r) {key msg : List Byte} (h : Repr m P key msg) :
    Repr m' P key msg := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · rw [show (P + 24 : Addr) = P + BitVec.ofNat 64 24 from rfl,
      bytesAt_frame hf (n := 32) (fun r hr => (hd r hr).sub_left (Offset.sub_base P (d := 24) (by decide)))
      (by decide)]
    exact h2
  · rw [bytesAt_frame hf (n := 24) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by decide)))
      (by decide)]
    exact h3

/-- A ChaCha20 state outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (Offset.contains_base p (by omega) (by omega)) hd (by decide)

/-- Byte `i` of a little-endian doubleword. -/
theorem readW64_byte (m : Mem) (a : Addr) {i : Nat} (hi : i < 8) :
    m (a + BitVec.ofNat 64 i) = (m.readW a 64).extractLsb' (8 * i) 8 := by
  rw [← Mem.extractLsb'_read m a (n := 8) hi]
  simp only [Mem.readW]
  rfl

/-- Bytes equal byte by byte. -/
theorem bytesAt_eq_of {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ i < n, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    bytesAt m' q n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.ext_getElem (by simp)
  intro i h₁ _
  simp only [List.getElem_map, List.getElem_range]
  exact h i (by simpa using h₁)

/-- Doublewords copied are bytes copied. -/
theorem bytes_of_dwords {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ k < n, m'.readW (q + BitVec.ofNat 64 (8 * k)) 64 = m.readW (p + BitVec.ofNat 64 (8 * k)) 64) :
    bytesAt m' q (8 * n) = bytesAt m p (8 * n) := by
  refine bytesAt_eq_of fun i hi => ?_
  have e : ∀ a : Addr, a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (8 * (i / 8)) + BitVec.ofNat 64 (i % 8) := by
    intro a
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod]
  rw [e, e, readW64_byte m' _ (Nat.mod_lt _ (by decide)), readW64_byte m _ (Nat.mod_lt _ (by decide)),
    h _ (by omega)]

/-- The first `n ≤ 64` bytes of a ChaCha20 state in memory. -/
theorem bytesAt_serialize (m : Mem) (p : Addr) {n : Nat} (hn : n ≤ 64) :
    bytesAt m p n = (Spec.ChaCha20.serialize (stateAt m p)).take n := by
  apply List.ext_getElem
  · simp [bytesAt, VG.Proof.ChaCha20.length_serialize]; omega
  · intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    have e := VG.Proof.ChaCha20.serialize_stateAt m p (i := i) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [VG.Proof.ChaCha20.length_serialize]; omega), Option.getD_some] at e
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, e]

/-! ## Covering the callees' regions -/

theorem covers_right {rs rd wr : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) := fun a n hi =>
  let ⟨r, hr, hc⟩ := h a n hi; ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_sub {s₀ s : State} (hp : APre e s₀) (hwr : s.wr = s₀.wr) (rs : List Region)
    (h : ∀ r ∈ rs, ∃ k, r = sub s₀ k r.len ∧ k + r.len ≤ 648) : Covers rs s.wr := by
  refine Covers.of_sub fun r hr => ?_
  obtain ⟨k, hrk, hk⟩ := h r hr
  exact ⟨ctxR s₀, by rw [hwr]; exact hp.ctx_wr, k, by rw [hrk], hk⟩

/-- A callee's working space (at `ctx + a`, `n` bytes) and argument (at
`ctx + b`, `m` bytes) in the context. -/
theorem covers2 {s₀ s : State} (hp : APre e s₀) (hwr : s.wr = s₀.wr) {a n b m : Nat}
    (ha : a + n ≤ 648) (hb : b + m ≤ 648) :
    Covers ([sub s₀ b m] ++ [sub s₀ a n]) (s.rd ++ s.wr) :=
  covers_right (covers_sub hp hwr _ fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨b, rfl, hb⟩
    · exact ⟨a, rfl, ha⟩)

theorem covers1 {s₀ s : State} (hp : APre e s₀) (hwr : s.wr = s₀.wr) {a n : Nat} (ha : a + n ≤ 648) :
    Covers [sub s₀ a n] s.wr :=
  covers_sub hp hwr _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨a, rfl, ha⟩

/-! ## Saving the registers -/

/-- The first `n` registers saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [sub s₀ savOff 56] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (off (cx s₀) (savOff + 8 * i)) 64 = s₀.gpr (saved i)

theorem save_step {s₀ : State} (hp : APre e s₀) {n : Nat} (hn : n < 6) {s : State} (h : SI s₀ n s) :
    WP isa (.block [.store .d (saved n) .r10 (savOff + 8 * n)]) s (SI s₀ (n + 1)) := by
  refine wp_std (a := off (cx s₀) (savOff + 8 * n)) (by decide) (by rw [savOff_eq]; omega)
    (by rw [h.gpr]) (by rw [h.wr]; exact hp.in_ctx (by rw [savOff_eq]; omega)) fun s' u => WP.block_nil ?_
  refine ⟨by rw [u.gpr, h.gpr], by rw [u.sp, h.sp], by rw [u.lr, h.lr], by rw [u.rd, h.rd],
    by rw [u.wr, h.wr], ?_, fun i hi => ?_⟩
  · rw [u.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (w := 64 / 8) (by omega) (by omega) (by decide))
  · rw [u.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [readW_writeW_off _ _ _ (by rw [savOff_eq]; omega) (by rw [savOff_eq]; omega) (by omega)]
      exact h.saved i hi
    · rw [Mem.readW_writeW_self64, h.gpr]

/-- Saving the registers and the return address. -/
theorem save_ok {s₀ : State} (hp : APre e s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, (∀ r, r ≠ .r0 → s.gpr r = s₀.gpr r) → s.sp = s₀.sp → s.rd = s₀.rd → s.wr = s₀.wr →
      Saved s₀ s.mem → Frame [sub s₀ savOff 56] s₀.mem s.mem → WP isa (.block rest) s Q) :
    WP isa (.block (save ++ rest)) s₀ Q := by
  rw [save, List.append_assoc]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI s₀)
    (fun k s hk h => save_step hp hk h) 6 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s h => ?_)
  refine wp_mflr fun s₁ u₁ => ?_
  refine wp_std (a := off (cx s₀) (savOff + 48)) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), h.gpr]) (by rw [u₁.wr, h.wr]; exact hp.in_ctx (by decide))
    fun s₂ u₂ => ?_
  refine k s₂ (fun r hr => by rw [u₂.gpr, u₁.other r hr, h.gpr]) (by rw [u₂.sp, u₁.sp, h.sp])
    (by rw [u₂.rd, u₁.rd, h.rd]) (by rw [u₂.wr, u₁.wr, h.wr]) ⟨fun i hi => ?_, ?_⟩ ?_
  · rw [u₂.mem, readW_writeW_off _ _ _ (by rw [savOff_eq]; omega) (by decide) (by omega), u₁.mem]
    exact h.saved i hi
  · rw [u₂.mem, Mem.readW_writeW_self64, u₁.gpr, h.lr]
  · rw [u₂.mem, u₁.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (w := 64 / 8) (by omega) (by omega) (by decide))

/-! ## Moving the arguments -/

theorem moves_ok {s₀ s : State} (hg : ∀ r, r ≠ .r0 → s.gpr r = s₀.gpr r) :
    WP isa (.block moves) s fun s' => Regs s₀ s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ ∀ r, (∀ i < 6, r ≠ saved i) → s'.gpr r = s.gpr r := by
  unfold moves
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_mov fun s₅ u₅ => wp_mov fun s₆ u₆ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, hg _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · intro r hr
    rw [u₆.other r (hr 5 (by decide)), u₅.other r (hr 4 (by decide)), u₄.other r (hr 3 (by decide)),
      u₃.other r (hr 2 (by decide)), u₂.other r (hr 1 (by decide)), u₁.other r (hr 0 (by decide))]

/-- Saving the registers and moving the arguments. -/
theorem saveMoves_ok {s₀ : State} (hp : APre e s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, Regs s₀ s → (∀ r, (∀ i < 6, r ≠ saved i) → r ≠ .r0 → s.gpr r = s₀.gpr r) →
      s.gpr .r3 = kp s₀ → s.gpr .r4 = np s₀ → s.sp = s₀.sp → s.rd = s₀.rd →
      s.wr = s₀.wr → Saved s₀ s.mem → Frame [sub s₀ savOff 56] s₀.mem s.mem → WP isa (.block rest) s Q) :
    WP isa (.block (save ++ moves ++ rest)) s₀ Q := by
  rw [List.append_assoc]
  refine save_ok hp fun s₁ g₁ sp₁ rd₁ wr₁ sv₁ f₁ => ?_
  refine WP.block_append (WP.mono (moves_ok g₁) fun s₂ ⟨rg, m₂, rd₂, wr₂, sp₂, o₂⟩ => ?_)
  refine k s₂ rg (fun r hr h0 => by rw [o₂ r hr, g₁ r h0]) ?_ ?_ (by rw [sp₂, sp₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [m₂]; exact sv₁)
    (by rw [m₂]; exact f₁)
  · rw [o₂ _ (by decide), g₁ _ (by decide)]
  · rw [o₂ _ (by decide), g₁ _ (by decide)]

/-! ## Copying doublewords of the context -/

theorem copyWords_step (a b n : Nat) : copyWords a b (n + 1) =
    copyWords a b n ++ ([.load .d .r12 .r24 (a + 8 * n), .store .d .r12 .r24 (b + 8 * n)] : List Instr) := by
  simp [copyWords, List.range_succ, List.flatMap_append]

/-- `n` doublewords from `ctx + a` to `ctx + b`. -/
theorem copyWords_ok {s₀ : State} {a b n : Nat} (hab : a + 8 * n ≤ b ∨ b + 8 * n ≤ a)
    (ha : a + 8 * n ≤ 648) (hb : b + 8 * n ≤ 648) (ha4 : a % 4 = 0) (hb4 : b % 4 = 0) {s : State}
    (h14 : s.gpr .r24 = cx s₀) (hc : CtxOk s₀ s) :
    WP isa (.block (copyWords a b n)) s fun s' =>
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [sub s₀ b (8 * n)] s.mem s'.mem ∧
      ∀ i < n, s'.mem.readW (off (cx s₀) (b + 8 * i)) 64 = s.mem.readW (off (cx s₀) (a + 8 * i)) 64 := by
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩
  | succ n ih =>
    rw [copyWords_step]
    refine WP.block_append (WP.mono (ih (by omega) (by omega) (by omega))
      fun s₁ ⟨g₁, rd₁, wr₁, sp₁, f₁, w₁⟩ => ?_)
    have hc₁ : CtxOk s₀ s₁ := by rw [CtxOk, rd₁, wr₁]; exact hc
    have h14₁ : s₁.gpr .r24 = cx s₀ := by rw [g₁ _ (by decide), h14]
    refine wp_ld (a := off (cx s₀) (a + 8 * n)) (by decide) (by omega) (by rw [h14₁])
      (hc₁ _ 8 (by omega)).1 fun s₂ u₂ => ?_
    refine wp_std (a := off (cx s₀) (b + 8 * n)) (by decide) (by omega)
      (by rw [u₂.other _ (by decide), h14₁]) (by rw [u₂.wr]; exact (hc₁ _ 8 (by omega)).2)
      fun s₃ u₃ => WP.block_nil ?_
    refine ⟨fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr], by rw [u₃.rd, u₂.rd, rd₁],
      by rw [u₃.wr, u₂.wr, wr₁], by rw [u₃.sp, u₂.sp, sp₁], ?_, fun i hi => ?_⟩
    · rw [u₃.mem, u₂.mem]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr
        exact Region.sub_prefix (by omega)
      · exact contains_sub s₀ (w := 64 / 8) (by omega) (by omega) (by omega)
    · rw [u₃.mem, u₂.gpr, u₂.mem]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega), w₁ i hi]
      · rw [Mem.readW_writeW_self64]
        exact f₁.readW (contains_sub s₀ (k := a + 8 * i) (n := 8) (w := 64 / 8) (Nat.le_refl _) (by omega)
            (by omega))
          (by simp only [List.mem_singleton, forall_eq]; exact sub_disj s₀ (by omega) (by omega) (by omega))
          (by decide)

/-! ## The ChaCha20 state -/

/-- The word `stW k` stores, from memory `m`, the key at `kp` and the nonce at `np`. -/
def wordOf (m : Mem) (kp np : Addr) (k : Nat) : BitVec 32 :=
  if k < 4 then consts.getD k 0
  else if k < 12 then m.readW (off kp (4 * (k - 4))) 32
  else if k = 12 then 0
  else m.readW (off np (4 * (k - 13))) 32

theorem sw32 (v : BitVec 32) : (v.setWidth 64).setWidth 32 = v :=
  BitVec.setWidth_setWidth_of_le _ (by decide)

theorem stW_ok {s₀ : State} (hp : APre e s₀) {k : Nat} (hk : k < 16) {s : State}
    (h14 : s.gpr .r24 = cx s₀) (h3 : s.gpr .r3 = kp s₀) (h4 : s.gpr .r4 = np s₀) (hrd : s.rd = s₀.rd)
    (hc : CtxOk s₀ s) :
    WP isa (.block (stW k)) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) (stOff + 4 * k)) (wordOf s.mem (kp s₀) (np s₀) k) ∧
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have o := (hc (stOff + 4 * k) 4 (by rw [stOff_eq]; omega)).2
  have ho : stOff + 4 * k < 2 ^ 15 := by rw [stOff_eq]; omega
  unfold stW stSrc wordOf
  by_cases h₁ : k < 4
  · simp only [h₁, ite_true, List.cons_append, List.nil_append]
    refine wp_lis fun s₁ u₁ => wp_ori fun s₂ u₂ => ?_
    refine wp_stw (a := off (cx s₀) (stOff + 4 * k)) (by decide) ho
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h14]) (by rw [u₂.wr, u₁.wr]; exact o)
      fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, lis_ori], fun r hr => by
      rw [g₃.gpr, u₂.other r hr, u₁.other r hr], by rw [g₃.rd, u₂.rd, u₁.rd], by rw [g₃.wr, u₂.wr, u₁.wr],
      by rw [g₃.sp, u₂.sp, u₁.sp]⟩
  by_cases h₂ : k < 12
  · simp only [h₁, h₂, ite_true, ite_false, List.cons_append, List.nil_append]
    refine wp_lwz (a := off (kp s₀) (4 * (k - 4))) (by decide) (by omega) (by rw [h3])
      (hp.k_in (by omega) hrd) fun s₁ u₁ => ?_
    refine wp_stw (a := off (cx s₀) (stOff + 4 * k)) (by decide) ho
      (by rw [u₁.other _ (by decide), h14]) (by rw [u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem, sw32], fun r hr => by rw [g₃.gpr, u₁.other r hr],
      by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr], by rw [g₃.sp, u₁.sp]⟩
  by_cases h₃ : k = 12
  · subst h₃
    simp only [ite_true]
    refine wp_li (by decide) fun s₁ u₁ => ?_
    refine wp_stw (a := off (cx s₀) (stOff + 4 * 12)) (by decide) ho
      (by rw [u₁.other _ (by decide), h14]) (by rw [u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem]; rfl, fun r hr => by rw [g₃.gpr, u₁.other r hr],
      by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr], by rw [g₃.sp, u₁.sp]⟩
  · simp only [h₁, h₂, h₃, ite_false, List.cons_append, List.nil_append]
    refine wp_lwz (a := off (np s₀) (4 * (k - 13))) (by decide) (by omega) (by rw [h4])
      (hp.n_in (by omega) hrd) fun s₁ u₁ => ?_
    refine wp_stw (a := off (cx s₀) (stOff + 4 * k)) (by decide) ho
      (by rw [u₁.other _ (by decide), h14]) (by rw [u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem, sw32], fun r hr => by rw [g₃.gpr, u₁.other r hr],
      by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr], by rw [g₃.sp, u₁.sp]⟩

/-- A frame of `ctx[k, k + n)` is one of the context. -/
theorem frame_ctx {s₀ : State} {m m' : Mem} {k n : Nat} (hf : Frame [sub s₀ k n] m m') (h : k + n ≤ 648) :
    Frame [ctxR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨ctxR s₀, List.mem_singleton_self _, sub_ctx s₀ h⟩

/-- Words outside the context are unchanged by a frame of the context. -/
theorem readW_out {s₀ : State} {m m' : Mem} (hf : Frame [ctxR s₀] m m') {p : Addr} {n : Nat}
    (hd : (ctxR s₀).Disjoint ⟨p, n⟩) {a : Nat} (ha : a + 4 ≤ n) :
    m'.readW (off p a) 32 = m.readW (off p a) 32 :=
  hf.readW (r := ⟨off p a, 4⟩) (Region.contains_self _ _)
    (by simp only [List.mem_singleton, forall_eq]; exact (hd.sub_right (Offset.sub_base p (d := a) (n := 4) ha)).symm)
    (by decide)

theorem wordOf_frame {s₀ : State} (hp : APre e s₀) {m m' : Mem} (hf : Frame [ctxR s₀] m m') {k : Nat}
    (hk : k < 16) :
    wordOf m' (kp s₀) (np s₀) k = wordOf m (kp s₀) (np s₀) k := by
  unfold wordOf
  by_cases h₁ : k < 4
  · simp only [h₁, ite_true]
  by_cases h₂ : k < 12
  · simp only [h₁, h₂, ite_true, ite_false]; exact readW_out hf hp.k_c.symm (by omega)
  by_cases h₃ : k = 12
  · subst h₃; simp only [h₁, h₂, ite_true, ite_false]
  · simp only [h₁, h₂, h₃, ite_false]; exact readW_out hf hp.n_c.symm (by omega)

theorem initState_step (j : Nat) : (List.range (j + 1)).flatMap stW = (List.range j).flatMap stW ++ stW j := by
  simp [List.range_succ, List.flatMap_append]

/-- The first `j` words of the ChaCha20 state. -/
theorem initState_ok {s₀ : State} (hp : APre e s₀) {j : Nat} (hj : j ≤ 16) {s : State}
    (h14 : s.gpr .r24 = cx s₀) (h3 : s.gpr .r3 = kp s₀) (h4 : s.gpr .r4 = np s₀) (hrd : s.rd = s₀.rd)
    (hc : CtxOk s₀ s) :
    WP isa (.block ((List.range j).flatMap stW)) s fun s' =>
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [sub s₀ stOff (4 * j)] s.mem s'.mem ∧
      ∀ i < j, s'.mem.readW (off (cx s₀) (stOff + 4 * i)) 32 = wordOf s.mem (kp s₀) (np s₀) i := by
  induction j with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩
  | succ j ih =>
    rw [initState_step]
    refine WP.block_append (WP.mono (ih (by omega)) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, f₁, w₁⟩ => ?_)
    have hc₁ : CtxOk s₀ s₁ := by rw [CtxOk, rd₁, wr₁]; exact hc
    refine WP.mono (stW_ok hp (by omega) (by rw [g₁ _ (by decide), h14]) (by rw [g₁ _ (by decide), h3])
      (by rw [g₁ _ (by decide), h4]) (by rw [rd₁, hrd]) hc₁)
      fun s₂ ⟨m₂, g₂, rd₂, wr₂, sp₂⟩ => ?_
    refine ⟨fun r hr => by rw [g₂ r hr, g₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁],
      ?_, fun i hi => ?_⟩
    · rw [m₂]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)
      · exact contains_sub s₀ (w := 32 / 8) (by omega) (by omega) (by rw [stOff_eq]; omega)
    · rw [m₂, wordOf_frame hp (frame_ctx f₁ (by rw [stOff_eq]; omega)) (k := j) (by omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [readW_writeW_off _ _ _ (by rw [stOff_eq]; omega) (by rw [stOff_eq]; omega) (by omega)]
        exact w₁ i hi
      · exact Mem.readW_writeW_self32 _ _ _

theorem consts_eq : ∀ i < 4, consts.getD i 0 = Spec.ChaCha20.constants.getD i 0 := by decide +kernel

/-- The words stored are the initial ChaCha20 state for the key, counter 0
and the nonce, if the key and the nonce are as on entry. -/
theorem stateAt_initState {s₀ : State} (hp : APre e s₀) {m₁ m' : Mem} (hf₁ : Frame [ctxR s₀] s₀.mem m₁)
    (hw : ∀ i < 16, m'.readW (off (cx s₀) (stOff + 4 * i)) 32 = wordOf m₁ (kp s₀) (np s₀) i) :
    stateAt m' (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  rw [off_add, hw i hi, wordOf_frame hp hf₁ hi]
  unfold wordOf
  by_cases h₁ : i < 4
  · simp only [h₁, ite_true]; exact consts_eq i h₁
  by_cases h₂ : i < 12
  · simp only [h₁, h₂, ite_true, ite_false]
    rw [show (K s₀) = Spec.ChaCha20.bytesAt s₀.mem (kp s₀) 32 from rfl,
      wordLE_bytesAt s₀.mem (kp s₀) (n := 32) (j := i - 4) (by omega)]
  by_cases h₃ : i = 12
  · subst h₃; simp only [h₁, h₂, ite_true, ite_false]
  · simp only [h₁, h₂, h₃, ite_false]
    rw [show (N s₀) = Spec.ChaCha20.bytesAt s₀.mem (np s₀) 12 from rfl,
      wordLE_bytesAt s₀.mem (np s₀) (n := 12) (j := i - 13) (by omega)]

/-! ## The first block -/

/-- After the first block: the registers saved and moved, and the ChaCha20
state. -/
structure Post1 (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  st : stateAt s.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  fctx : Frame [ctxR s₀] s₀.mem s.mem

/-- The first block of both functions. -/
theorem block1_ok {s₀ : State} (hp : APre e s₀) :
    WP isa (.block (save ++ moves ++ initState)) s₀ (Post1 s₀) := by
  refine saveMoves_ok hp fun s₁ rg og h3 h4 sp rd wr sv f₁ => ?_
  have i₁ : Inv s₀ s₁ := ⟨rg, fun r hr hne => og r hne (ne_of_pres hr), sp, rd, wr, sv, f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨ctxR s₀, List.mem_cons_self, sub_ctx s₀ (by decide)⟩⟩
  have hf₁ := frame_ctx f₁ (by decide)
  refine WP.mono (initState_ok hp (j := 16) (Nat.le_refl _) rg.r24 h3 h4 rd (Inv.ctxOk hp rd wr))
    fun s₂ ⟨g₂, rd₂, wr₂, sp₂, f₂, w₂⟩ => ⟨?_, ?_, hf₁.trans (frame_ctx f₂ (by decide))⟩
  · exact i₁.step1 ⟨fun r hr => g₂ r (ne_of_pres hr), sp₂, rd₂, wr₂, f₂⟩ (by decide) (by decide)
  · exact stateAt_initState hp hf₁ w₂

/-! ## The one-time key -/

/-- `r3 = ctx + stOff`, `r4 = ctx`. -/
theorem kgA_ok {s₀ s : State} (h : Inv s₀ s) :
    WP isa (.block [.addi .r3 .r24 stOff, mov .r4 .r24]) s fun s' =>
      s'.gpr .r3 = off (cx s₀) stOff ∧ s'.gpr .r4 = cx s₀ ∧ Kept [] s s' :=
  wp_addi (by decide) (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil
    ⟨by rw [u₂.other _ (by decide), u₁.gpr, h.regs.r24], by rw [u₂.gpr, u₁.other _ (by decide), h.regs.r24],
      ⟨fun r hr => by rw [u₂.other r (ne_of_pres hr), u₁.other r (ne_of_pres hr)], by rw [u₂.sp, u₁.sp],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _⟩⟩

/-- After the one-time key is computed. -/
structure PostK (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  st : stateAt s.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  key : bytesAt s.mem (off (cx s₀) keyOff) 32 = otk s₀

theorem keyGen_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Post1 s₀ s) :
    WP isa keyGen s fun s' => PostK s₀ s' ∧ Frame [sub s₀ 0 256, sub s₀ keyOff 32] s.mem s'.mem := by
  unfold keyGen
  refine WP.seq (WP.mono (kgA_ok h.inv) fun s₁ ⟨h3, h4, k₁⟩ => ?_)
  have i₁ := h.inv.step0 k₁
  have m₁ := k₁.mem_eq
  have dj : (⟨cx s₀, 256⟩ : Region).Disjoint ⟨off (cx s₀) stOff, 64⟩ := by
    rw [← sub_zero s₀ 256]; exact sub_disj s₀ (by decide) (by decide) (by decide)
  have cv : Covers ([(⟨off (cx s₀) stOff, 64⟩ : Region)] ++ [⟨cx s₀, 256⟩]) (s₁.rd ++ s₁.wr) := by
    rw [← sub_zero s₀ 256]; exact covers2 hp i₁.wr (by decide) (by decide)
  have cw : Covers [(⟨cx s₀, 256⟩ : Region)] s₁.wr := by
    rw [← sub_zero s₀ 256]; exact covers1 hp i₁.wr (by decide)
  refine WP.seq (block_call h3 h4 dj cv cw fun s₂ k₂ blk₂ => ?_)
  rw [← sub_zero s₀ 256] at k₂
  have i₂ := i₁.step1 k₂ (by decide) (by decide)
  refine WP.mono (copyWords_ok (a := 0) (b := keyOff) (n := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) i₂.regs.r24 (Inv.ctxOk hp i₂.rd i₂.wr))
    fun s₃ ⟨g₃, rd₃, wr₃, sp₃, f₃, w₃⟩ => ?_
  have hk₃ : Kept [sub s₀ keyOff (8 * 4)] s₂ s₃ := ⟨fun r hr => g₃ r (ne_of_pres hr), sp₃, rd₃, wr₃, f₃⟩
  refine ⟨⟨i₂.step1 hk₃ (by decide) (by decide), ?_, ?_⟩, ?_⟩
  · -- The ChaCha20 state is outside both writes.
    rw [stateAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by decide) (by decide) (by decide)),
      stateAt_frame k₂.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (a := stOff) (n := 64) (b := 0) (m := 256) (by decide) (by decide)
          (by decide)), m₁, h.st]
  · have e : bytesAt s₃.mem (off (cx s₀) keyOff) (8 * 4) = bytesAt s₂.mem (off (cx s₀) 0) (8 * 4) :=
      bytes_of_dwords fun k hk => by rw [off_add, off_add]; exact w₃ k hk
    rw [show (32 : Nat) = 8 * 4 from rfl, e, off_zero, bytesAt_serialize _ _ (by decide), blk₂, m₁, h.st]
    rfl
  · refine (k₁.frame.sub fun _ hr => absurd hr List.not_mem_nil).trans ((k₂.frame.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact f₃.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩

/-! ## The Poly1305 state -/

/-- `r3 = ctx`, `r4 = ctx + keyOff`. -/
theorem piA_ok {s₀ s : State} (h : Inv s₀ s) :
    WP isa (.block [mov .r3 .r24, .addi .r4 .r24 keyOff]) s fun s' =>
      s'.gpr .r3 = cx s₀ ∧ s'.gpr .r4 = off (cx s₀) keyOff ∧ Kept [] s s' :=
  wp_mov fun s₁ u₁ => wp_addi (by decide) (by decide) fun s₂ u₂ => WP.block_nil
    ⟨by rw [u₂.other _ (by decide), u₁.gpr, h.regs.r24], by rw [u₂.gpr, u₁.other _ (by decide), h.regs.r24],
      ⟨fun r hr => by rw [u₂.other r (ne_of_pres hr), u₁.other r (ne_of_pres hr)], by rw [u₂.sp, u₁.sp],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _⟩⟩

theorem polyInit_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    (hkey : bytesAt s.mem (off (cx s₀) keyOff) 32 = otk s₀) :
    WP isa polyInit s fun s' => Inv s₀ s' ∧ Kept [sub s₀ 0 128] s s' ∧ Repr s'.mem (cx s₀) (otk s₀) [] := by
  unfold polyInit
  refine WP.seq (WP.mono (piA_ok h) fun s₁ ⟨h3, h4, k₁⟩ => ?_)
  have i₁ := h.step0 k₁
  have dj : (⟨cx s₀, 128⟩ : Region).Disjoint ⟨off (cx s₀) keyOff, 32⟩ := by
    rw [← sub_zero s₀ 128]; exact sub_disj s₀ (by decide) (by decide) (by decide)
  have cv : Covers ([(⟨off (cx s₀) keyOff, 32⟩ : Region)] ++ [⟨cx s₀, 128⟩]) (s₁.rd ++ s₁.wr) := by
    rw [← sub_zero s₀ 128]; exact covers2 hp i₁.wr (by decide) (by decide)
  have cw : Covers [(⟨cx s₀, 128⟩ : Region)] s₁.wr := by
    rw [← sub_zero s₀ 128]; exact covers1 hp i₁.wr (by decide)
  refine init_call h3 h4 dj cv cw fun s₂ k₂ repr₂ => ?_
  rw [← sub_zero s₀ 128] at k₂
  refine ⟨i₁.step1 k₂ (by decide) (by decide), (k₁.sub fun _ hr => absurd hr List.not_mem_nil).trans k₂, ?_⟩
  rw [k₁.mem_eq, hkey] at repr₂
  exact repr₂

end VG.Proof.ChaCha20Poly1305.PPC64LE
