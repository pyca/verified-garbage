module

public import VerifiedGarbage.Proof.Mont.X86.WordLoop
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# The word loops of the runtime-modulus arithmetic (x86, 32-bit)

What `zerosW`, `chainW`, `selectsW`, `csubW`, `addW` and `setConstW` compute
(`Impl/Mont/X86/Words.lean`), stated as the unrolled operations' lemmas are
(`Ops.lean`, `Chain.lean`, `Csub.lean`), each by `wordLoop_ok` with an
invariant on the words done so far.
-/

@[expose] public section

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Mont VG.Proof.Mont

/-- A carry or borrow as a mask. -/
abbrev cmask (c : Bool) : BitVec 32 := if c then BitVec.allOnes 32 else 0

/-- The working space ends below `2³²` (the stack is above it or below it). -/
theorem Scr.size_lt {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) : size < 2 ^ 32 := by
  have := hs.nowrap; have := hs.stk; have := (s.gpr .esp).isLt
  simp only [StkOk] at *
  omega

/-- `restore`: the carry flag from the mask in `ecx`. -/
theorem wp_restore {is : List Instr} {s : State} {Q : State → Prop} {c : Bool}
    (hc : s.gpr .ecx = cmask c) (k : ∀ t, Upd s t .edx 0 → t.cf = some c → WP isa (.block is) t Q) :
    WP isa (.block (restore ++ is)) s Q := by
  refine wp_movS rfl fun s₁ u₁ _ => wp_cmp fun s₂ f₂ c₂ _ => k s₂ ?_ ?_
  · exact ⟨by rw [f₂.gpr, u₁.gpr], fun r h => by rw [f₂.gpr, u₁.other r h], by rw [f₂.mem, u₁.mem],
      by rw [f₂.rd, u₁.rd], by rw [f₂.wr, u₁.wr], by rw [f₂.syms, u₁.syms]⟩
  · rw [c₂, u₁.gpr, u₁.other _ (by decide), hc]
    cases c <;> rfl

/-- `[ebp + d]`, at word `j` of the loop. -/
theorem Scr.ea_at' {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {j d : Nat}
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * j)) (hd : d + 4 * j < size) :
    s.ea (at_ .ebp d) = off base (d + 4 * j) := by
  rw [hs.ea_at hp (by omega), Nat.add_comm]

theorem readSrc_at' {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {j d : Nat}
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * j)) (hd : d + 4 * j + 4 ≤ size) :
    readSrc s (.mem (at_ .ebp d)) = some (s.mem.readW (off base (d + 4 * j)) 32) := by
  rw [readSrc_at hs hp (by omega), Nat.add_comm]

/-- A store of word `j` of `[o]` keeps its words below `j`, and its value
is read back. -/
theorem val32_store {m : Mem} {base : Addr} {size o j : Nat} (hn : base.toNat + size ≤ 2 ^ 32)
    (ho : o + 4 * j + 4 ≤ size) (v : BitVec 32) :
    val32 (m.writeW (off base (o + 4 * j)) v) base o (j + 1) = val32 m base o j + 2 ^ (32 * j) * v.toNat := by
  rw [val32_succ, w32_write_self, (writeW32_outside m base v (by omega)).val32 (by omega) (by omega)]

/-! ## Zeros -/

theorem zerosW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o k : Nat}
    (hk : 0 < k) (hsz : o + 4 * k ≤ size) :
    WP isa (zerosW o k) s fun u =>
      Outside base o (4 * k) s.mem u.mem ∧ val32 u.mem base o k = 0 ∧ Keeps [.eax, .ebp, .edx] s u := by
  have hn := hs.nowrap
  unfold zerosW
  refine WP.seq (wp_movS rfl fun s₁ u₁ _ => WP.block_nil ?_)
  refine wordLoop_ok (fun j t => Keeps [.eax, .ebp, .edx] s t ∧ t.gpr .eax = 0 ∧
      Outside base o (4 * k) s.mem t.mem ∧ val32 t.mem base o j = 0) hk (by have := hs.size_lt; omega)
    (fun j u u' ⟨K, e, O, V⟩ ⟨hm, hr, hw, hg⟩ =>
      ⟨⟨fun r h => (hg r (by simp_all) (by simp_all)).trans (K.1 r h), hr.trans K.2.1, hw.trans K.2.2⟩,
        by rw [hg _ (by decide) (by decide), e], hm ▸ O, hm ▸ V⟩)
    ⟨u₁.keeps.mono (by decide), u₁.gpr, u₁.mem ▸ VG.Proof.Mont.Outside.refl _ _ _ _, rfl⟩
    (fun j hj t ⟨K, e, O, V⟩ ej => ?_) (fun u ⟨K, _, O, V⟩ => ⟨O, V, K⟩)
  have ht := hs.of_keeps K (by decide)
  refine wp_storeS (ht.ea_at' ej (d := o) (by omega)) (ht.write (d := o + 4 * j) (n := 4) (by omega))
    fun u m => WP.block_nil ⟨⟨K.trans (m.keeps _), by rw [m.gpr, e], ?_, ?_⟩, by rw [m.gpr], by rw [m.gpr]⟩
  · rw [m.mem]
    exact O.trans ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
  · rw [m.mem, val32_store hn (by omega), V, e]; rfl

/-! ## Carry chains -/

theorem adc_rel (A B : BitVec 32) (c : Bool) :
    (A + B + (BitVec.ofBool c).setWidth 32).toNat + 2 ^ 32 * (decide (2 ^ 32 ≤ A.toNat + B.toNat + c.toNat)).toNat =
      A.toNat + B.toNat + c.toNat := by
  rw [add3_toNat]
  have := A.isLt; have := B.isLt; have : c.toNat ≤ 1 := Bool.toNat_le c
  by_cases h : 2 ^ 32 ≤ A.toNat + B.toNat + c.toNat
  · rw [decide_eq_true h, Bool.toNat_true]; omega
  · rw [decide_eq_false h, Bool.toNat_false]; omega

theorem sbb_rel (A B : BitVec 32) (c : Bool) :
    (A - B - (BitVec.ofBool c).setWidth 32).toNat + B.toNat + c.toNat =
      A.toNat + 2 ^ 32 * (decide (A.toNat < B.toNat + c.toNat)).toNat := by
  rw [sub3_toNat]
  have := A.isLt; have := B.isLt; have : c.toNat ≤ 1 := Bool.toNat_le c
  by_cases h : A.toNat < B.toNat + c.toNat
  · rw [decide_eq_true h, Bool.toNat_true]; omega
  · rw [decide_eq_false h, Bool.toNat_false]; omega

theorem chain_add_step {V VA VB P A B W c c' : Nat} (h : V + P * c = VA + VB)
    (hw : W + 2 ^ 32 * c' = A + B + c) :
    (V + P * W) + 2 ^ 32 * P * c' = (VA + P * A) + (VB + P * B) := by
  have e : P * W + P * (2 ^ 32 * c') = P * A + P * B + P * c := by
    rw [← Nat.mul_add, hw, Nat.mul_add, Nat.mul_add]
  rw [show 2 ^ 32 * P * c' = P * (2 ^ 32 * c') by rw [Nat.mul_comm (2 ^ 32), Nat.mul_assoc]]
  omega

theorem chain_sub_step {V VA VB P A B W c c' : Nat} (h : V + VB = VA + P * c)
    (hw : W + B + c = A + 2 ^ 32 * c') :
    (V + P * W) + (VB + P * B) = (VA + P * A) + 2 ^ 32 * P * c' := by
  have e : P * W + P * B + P * c = P * A + P * (2 ^ 32 * c') := by
    rw [← Nat.mul_add, ← Nat.mul_add, hw, Nat.mul_add]
  rw [show 2 ^ 32 * P * c' = P * (2 ^ 32 * c') by rw [Nat.mul_comm (2 ^ 32), Nat.mul_assoc]]
  omega

/-- What a carry chain keeps, and its invariant's shape. -/
theorem chain_stable {s : State} {o k : Nat} {base : Addr} (R : Nat → Mem → Nat → Prop) :
    LoopStable fun j t => Keeps [.eax, .ecx, .edx, .ebp] s t ∧ Outside base o (4 * k) s.mem t.mem ∧
      ∃ c : Bool, t.gpr .ecx = cmask c ∧ R j t.mem c.toNat :=
  fun j u u' ⟨K, O, c, e, V⟩ ⟨hm, hr, hw, hg⟩ =>
    ⟨⟨fun r h => (hg r (by simp_all) (by simp_all)).trans (K.1 r h), hr.trans K.2.1, hw.trans K.2.2⟩,
      hm ▸ O, c, by rw [hg _ (by decide) (by decide), e], hm ▸ V⟩

/-- One word of a chain: `[o + 4j] = [a + 4j] op' [b + 4j]` with the carry
`c` in, the carry `c'` out. -/
theorem chainStep_ok {t : State} {base : Addr} {size : Nat} (ht : Scr t base size) {op' : AluOp}
    (hop : op' = .adc ∨ op' = .sbb) {o a b j : Nat} {c : Bool}
    (hp : t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * j)) (hc : t.gpr .ecx = cmask c)
    (ho : o + 4 * j + 4 ≤ size) (ha : a + 4 * j + 4 ≤ size) (hb : b + 4 * j + 4 ≤ size) :
    WP isa (.block (([.mov .eax (.mem (at_ .ebp a))] : List Instr) ++ restore ++
      ([.alu op' .eax (.mem (at_ .ebp b)), .store (at_ .ebp o) .eax, .alu .sbb .ecx (.reg .ecx)] :
        List Instr))) t fun u =>
      u.mem = t.mem.writeW (off base (o + 4 * j)) (if op' = .adc then
        t.mem.readW (off base (a + 4 * j)) 32 + t.mem.readW (off base (b + 4 * j)) 32 + (BitVec.ofBool c).setWidth 32
        else t.mem.readW (off base (a + 4 * j)) 32 - t.mem.readW (off base (b + 4 * j)) 32 -
          (BitVec.ofBool c).setWidth 32) ∧
      u.gpr .ecx = cmask (if op' = .adc then decide (2 ^ 32 ≤ w32 t.mem base (a + 4 * j) +
          w32 t.mem base (b + 4 * j) + c.toNat)
        else decide (w32 t.mem base (a + 4 * j) < w32 t.mem base (b + 4 * j) + c.toNat)) ∧
      Keeps [.eax, .ecx, .edx] t u := by
  have hn := ht.nowrap
  simp only [List.singleton_append]
  refine wp_movS (readSrc_at' ht hp ha) fun s₁ u₁ _ => ?_
  refine wp_restore (by rw [u₁.other _ (by decide), hc]) fun s₂ u₂ c₂ => ?_
  have K₂ : Keeps [.eax, .ecx, .edx] t s₂ := (u₁.keeps.mono (by decide)).widen u₂.keeps
  have hs₂ := ht.of_keeps K₂ (by decide)
  have hp₂ : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (4 * j) := by
    rw [K₂.1 _ (by decide), K₂.1 _ (by decide)]; exact hp
  have m₂ : s₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  have eax₂ : s₂.gpr .eax = t.mem.readW (off base (a + 4 * j)) 32 := by rw [u₂.other _ (by decide), u₁.gpr]
  rcases hop with rfl | rfl
  · refine wp_adcS (readSrc_at' hs₂ hp₂ hb) c₂ fun s₃ u₃ c₃ => ?_
    have hs₃ := hs₂.of_keeps u₃.keeps (by decide)
    have hp₃ : s₃.gpr .ebp = s₃.gpr .edi + BitVec.ofNat 32 (4 * j) := by
      rw [u₃.other _ (by decide), u₃.other _ (by decide)]; exact hp₂
    refine wp_storeS (hs₃.ea_at' hp₃ (d := o) (by omega)) (hs₃.write (d := o + 4 * j) (n := 4) (by omega))
      fun s₄ m₄ => wp_sbb_self (by rw [m₄.cf]; exact c₃) fun s₅ u₅ => WP.block_nil ⟨?_, ?_, ?_⟩
    · rw [u₅.mem, m₄.mem, u₃.mem, u₃.gpr, eax₂, m₂]; rfl
    · rw [u₅.gpr, eax₂, m₂]; rfl
    · exact ((K₂.widen u₃.keeps).widen (m₄.keeps [])).widen u₅.keeps
  · refine wp_sbbS (readSrc_at' hs₂ hp₂ hb) c₂ fun s₃ u₃ c₃ => ?_
    have hs₃ := hs₂.of_keeps u₃.keeps (by decide)
    have hp₃ : s₃.gpr .ebp = s₃.gpr .edi + BitVec.ofNat 32 (4 * j) := by
      rw [u₃.other _ (by decide), u₃.other _ (by decide)]; exact hp₂
    refine wp_storeS (hs₃.ea_at' hp₃ (d := o) (by omega)) (hs₃.write (d := o + 4 * j) (n := 4) (by omega))
      fun s₄ m₄ => wp_sbb_self (by rw [m₄.cf]; exact c₃) fun s₅ u₅ => WP.block_nil ⟨?_, ?_, ?_⟩
    · rw [u₅.mem, m₄.mem, u₃.mem, u₃.gpr, eax₂, m₂]; rfl
    · rw [u₅.gpr, eax₂, m₂]; rfl
    · exact ((K₂.widen u₃.keeps).widen (m₄.keeps [])).widen u₅.keeps

/-- `[o] = [a] + [b]` (`k` words), and the carry, as a mask in `ecx`. -/
theorem chainAddW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {k o a b : Nat}
    (hk : 0 < k) (ho : o + 4 * k ≤ size) (ha : a + 4 * k ≤ size) (hb : b + 4 * k ≤ size)
    (hoa : o + 4 * k ≤ a ∨ a + 4 * k ≤ o) (hob : o + 4 * k ≤ b ∨ b + 4 * k ≤ o) :
    WP isa (chainW .adc k o a b) s fun u =>
      Outside base o (4 * k) s.mem u.mem ∧
      (∃ c : Bool, u.gpr .ecx = cmask c ∧
        val32 u.mem base o k + 2 ^ (32 * k) * c.toNat = val32 s.mem base a k + val32 s.mem base b k) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s u := by
  have hn := hs.nowrap
  unfold chainW
  refine WP.seq (wp_movS rfl fun s₁ u₁ _ => WP.block_nil ?_)
  refine wordLoop_ok _ hk (by have := hs.size_lt; omega) (chain_stable (s := s) (o := o) (k := k) (base := base)
      fun j mem c => val32 mem base o j + 2 ^ (32 * j) * c = val32 s.mem base a j + val32 s.mem base b j)
    ⟨u₁.keeps.mono (by decide), u₁.mem ▸ VG.Proof.Mont.Outside.refl _ _ _ _, false, u₁.gpr, rfl⟩
    (fun j hj t ⟨K, O, c, e, V⟩ ej => ?_) (fun u ⟨K, O, c, e, V⟩ => ⟨O, ⟨c, e, V⟩, K⟩)
  have ht := hs.of_keeps K (by decide)
  refine WP.mono (chainStep_ok ht (.inl rfl) ej e (o := o) (a := a) (b := b) (by omega) (by omega) (by omega))
    fun u ⟨mu, eu, Ku⟩ => ⟨⟨K.trans (Ku.mono (by decide)), ?_, _, eu, ?_⟩, Ku.1 _ (by decide), Ku.1 _ (by decide)⟩
  · rw [mu]
    exact O.trans ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
  · simp only [ite_true] at mu ⊢
    have ea : w32 t.mem base (a + 4 * j) = w32 s.mem base (a + 4 * j) := O.w32 (by omega) (by omega)
    have eb : w32 t.mem base (b + 4 * j) = w32 s.mem base (b + 4 * j) := O.w32 (by omega) (by omega)
    rw [mu, val32_store hn (by omega), val32_succ s.mem base a, val32_succ s.mem base b, pow32_succ]
    have h := adc_rel (t.mem.readW (off base (a + 4 * j)) 32) (t.mem.readW (off base (b + 4 * j)) 32) c
    have ea' : (t.mem.readW (off base (a + 4 * j)) 32).toNat = w32 s.mem base (a + 4 * j) := ea
    have eb' : (t.mem.readW (off base (b + 4 * j)) 32).toNat = w32 s.mem base (b + 4 * j) := eb
    rw [ea', eb'] at h
    rw [ea, eb]
    exact chain_add_step V h

/-- `[o] = [a] - [b]` (`k` words), and the borrow, as a mask in `ecx`. -/
theorem chainSubW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {k o a b : Nat}
    (hk : 0 < k) (ho : o + 4 * k ≤ size) (ha : a + 4 * k ≤ size) (hb : b + 4 * k ≤ size)
    (hoa : o + 4 * k ≤ a ∨ a + 4 * k ≤ o) (hob : o + 4 * k ≤ b ∨ b + 4 * k ≤ o) :
    WP isa (chainW .sbb k o a b) s fun u =>
      Outside base o (4 * k) s.mem u.mem ∧
      (∃ c : Bool, u.gpr .ecx = cmask c ∧
        val32 u.mem base o k + val32 s.mem base b k = val32 s.mem base a k + 2 ^ (32 * k) * c.toNat) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s u := by
  have hn := hs.nowrap
  unfold chainW
  refine WP.seq (wp_movS rfl fun s₁ u₁ _ => WP.block_nil ?_)
  refine wordLoop_ok _ hk (by have := hs.size_lt; omega) (chain_stable (s := s) (o := o) (k := k) (base := base)
      fun j mem c => val32 mem base o j + val32 s.mem base b j = val32 s.mem base a j + 2 ^ (32 * j) * c)
    ⟨u₁.keeps.mono (by decide), u₁.mem ▸ VG.Proof.Mont.Outside.refl _ _ _ _, false, u₁.gpr, rfl⟩
    (fun j hj t ⟨K, O, c, e, V⟩ ej => ?_) (fun u ⟨K, O, c, e, V⟩ => ⟨O, ⟨c, e, V⟩, K⟩)
  have ht := hs.of_keeps K (by decide)
  refine WP.mono (chainStep_ok ht (.inr rfl) ej e (o := o) (a := a) (b := b) (by omega) (by omega) (by omega))
    fun u ⟨mu, eu, Ku⟩ => ⟨⟨K.trans (Ku.mono (by decide)), ?_, _, eu, ?_⟩, Ku.1 _ (by decide), Ku.1 _ (by decide)⟩
  · rw [mu]
    exact O.trans ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
  · simp only [reduceCtorEq, ite_false] at mu ⊢
    have ea : w32 t.mem base (a + 4 * j) = w32 s.mem base (a + 4 * j) := O.w32 (by omega) (by omega)
    have eb : w32 t.mem base (b + 4 * j) = w32 s.mem base (b + 4 * j) := O.w32 (by omega) (by omega)
    rw [mu, val32_store hn (by omega), val32_succ s.mem base a, val32_succ s.mem base b, pow32_succ]
    have h := sbb_rel (t.mem.readW (off base (a + 4 * j)) 32) (t.mem.readW (off base (b + 4 * j)) 32) c
    have ea' : (t.mem.readW (off base (a + 4 * j)) 32).toNat = w32 s.mem base (a + 4 * j) := ea
    have eb' : (t.mem.readW (off base (b + 4 * j)) 32).toNat = w32 s.mem base (b + 4 * j) := eb
    rw [ea', eb'] at h
    rw [ea, eb]
    exact chain_sub_step V h

/-! ## Selection -/

/-- `[o] = [tmp]` if `k`, else `[src]`, under the mask `eax` (`n` words).
`[o]` may be `[src]` or `[tmp]`. -/
theorem selectsW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {src o tmp n : Nat}
    (k : Bool) (hm : s.gpr .ecx = if k then BitVec.allOnes 32 else 0) (hn0 : 0 < n)
    (hsrc : src + 4 * n ≤ size) (htmp : tmp + 4 * n ≤ size) (ho : o + 4 * n ≤ size)
    (hso : o = src ∨ o + 4 * n ≤ src ∨ src + 4 * n ≤ o) (hto : o = tmp ∨ o + 4 * n ≤ tmp ∨ tmp + 4 * n ≤ o) :
    WP isa (selectsW n src tmp o) s fun u =>
      Outside base o (4 * n) s.mem u.mem ∧
      val32 u.mem base o n = val32 s.mem base (if k then tmp else src) n ∧
      Keeps [.eax, .edx, .ebp] s u := by
  have hn := hs.nowrap
  unfold selectsW
  refine wordLoop_ok (fun j t => Keeps [.eax, .edx, .ebp] s t ∧ Outside base o (4 * j) s.mem t.mem ∧
      val32 t.mem base o j = val32 s.mem base (if k then tmp else src) j) hn0
    (by have := hs.size_lt; omega)
    (fun j u u' ⟨K, O, V⟩ ⟨hm', hr, hw, hg⟩ =>
      ⟨⟨fun r h => (hg r (by simp_all) (by simp_all)).trans (K.1 r h), hr.trans K.2.1, hw.trans K.2.2⟩,
        hm' ▸ O, hm' ▸ V⟩)
    ⟨Keeps.refl _ _, VG.Proof.Mont.Outside.refl _ _ _ _, rfl⟩
    (fun j hj t ⟨K, O, V⟩ ej => ?_) (fun u ⟨K, O, V⟩ => ⟨O, V, K⟩)
  have ht := hs.of_keeps K (by decide)
  refine wp_movS (readSrc_at' ht ej (d := src) (by omega)) fun s₂ u₂ _ => ?_
  have hs₂ := ht.of_keeps u₂.keeps (by decide)
  have ej₂ : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (4 * j) := by
    rw [u₂.other _ (by decide), u₂.other _ (by decide)]; exact ej
  refine wp_movS (readSrc_at' hs₂ ej₂ (d := tmp) (by omega)) fun s₃ u₃ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₄ u₄ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₅ u₅ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₆ u₆ => ?_
  have k₆ : Keeps [.eax, .edx] t s₆ := (((u₂.keeps.mono (by decide)).widen u₃.keeps).widen u₄.keeps |>.widen
    u₅.keeps).widen u₆.keeps
  have hs₆ := ht.of_keeps k₆ (by decide)
  have ej₆ : s₆.gpr .ebp = s₆.gpr .edi + BitVec.ofNat 32 (4 * j) := by
    rw [k₆.1 _ (by decide), k₆.1 _ (by decide)]; exact ej
  refine wp_storeS (hs₆.ea_at' ej₆ (d := o) (by omega)) (hs₆.write (d := o + 4 * j) (n := 4) (by omega))
    fun s₇ m₇ => WP.block_nil ⟨⟨K.trans ((k₆.mono (by decide)).widen (m₇.keeps [])), ?_, ?_⟩,
      by rw [m₇.gpr, k₆.1 _ (by decide)], by rw [m₇.gpr, k₆.1 _ (by decide)]⟩
  · have mem₆ : s₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    rw [m₇.mem, mem₆]
    exact (O.mono (Nat.le_refl _) (by omega)).trans ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
  · have mem₆ : s₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    have ecx₄ : s₄.gpr .ecx = s.gpr .ecx := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), K.1 _ (by decide)]
    have eax₆ : s₆.gpr .eax = t.mem.readW (off base (src + 4 * j)) 32 ^^^
        ((t.mem.readW (off base (tmp + 4 * j)) 32 ^^^ t.mem.readW (off base (src + 4 * j)) 32) &&&
          (if k then BitVec.allOnes 32 else 0)) := by
      rw [u₆.gpr, u₅.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₄.gpr, ecx₄, hm,
        u₃.other _ (by decide), u₃.gpr, u₂.gpr, u₂.mem]
      rfl
    rw [select_val] at eax₆
    rw [m₇.mem, mem₆, val32_store hn (by omega), V, eax₆, val32_succ]
    congr 1
    cases k
    · exact congrArg (2 ^ (32 * j) * ·) (O.w32 (d := src + 4 * j) (by omega) (by omega))
    · exact congrArg (2 ^ (32 * j) * ·) (O.w32 (d := tmp + 4 * j) (by omega) (by omega))

/-! ## Conditional subtraction -/

/-- `[o] = T mod m` for the number `T < 2m` at `[src]` (`N` words and the
top word), through `[tmp]`. -/
theorem csubW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {N src o m : Nat}
    (hNw : words M = N) (hN : 0 < N) (hsrc : src + 4 * (N + 1) ≤ size) (ho : o + 4 * N ≤ size)
    (htmp : M.tmp + 4 * N ≤ size) (hmo : M.mo + 4 * N ≤ size)
    (hts : M.tmp + 4 * N ≤ src ∨ src + 4 * (N + 1) ≤ M.tmp) (htm : M.tmp + 4 * N ≤ M.mo ∨ M.mo + 4 * N ≤ M.tmp)
    (hos : o + 4 * N ≤ src ∨ src + 4 * N ≤ o) (hot : o + 4 * N ≤ M.tmp ∨ M.tmp + 4 * N ≤ o)
    (hm : val32 s.mem base M.mo N = m) (hV : val32 s.mem base src (N + 1) < 2 * m) :
    WP isa (csubW M src o) s fun u =>
      Outs base [(M.tmp, 4 * N), (o, 4 * N)] s.mem u.mem ∧
      val32 u.mem base o N = val32 s.mem base src (N + 1) % m ∧
      Keeps [.eax, .ecx, .edx, .ebp] s u := by
  have hn := hs.nowrap
  unfold csubW
  rw [hNw]
  refine WP.seq (WP.mono (chainSubW_ok hs (o := M.tmp) (a := src) (b := M.mo) hN (by omega) (by omega)
    (by omega) (by omega) htm) fun s₁ ⟨O₁, ⟨c, hc, V₁⟩, K₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.seq (wp_movS (readSrc_sc hs₁ (d := src + 4 * N) (by omega)) fun s₂ u₂ _ => ?_)
  refine wp_restore (by rw [u₂.other _ (by decide), hc]) fun s₃ u₃ c₃ => ?_
  refine wp_sbbS rfl c₃ fun s₄ u₄ c₄ => ?_
  refine wp_sbbS rfl c₄ fun s₅ u₅ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₆ u₆ => ?_
  refine wp_movS rfl fun s₇ u₇ _ => WP.block_nil ?_
  have k₆ : Keeps [.eax, .ecx, .edx, .ebp] s s₇ :=
    (((((K₁.mono (by decide)).widen u₂.keeps).widen u₃.keeps |>.widen u₄.keeps).widen u₅.keeps).widen
      u₆.keeps).widen u₇.keeps
  have hs₆ := hs.of_keeps k₆ (by decide)
  have mask := u₆.gpr
  simp only [reduceCtorEq, ite_false] at mask
  rw [u₅.gpr, mask_val] at mask
  rw [← u₇.gpr] at mask
  have mem₆ : s₇.mem = s₁.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have z : (0 : BitVec 32).toNat = 0 := rfl
  have top : (s₄.gpr .eax).toNat + 0 = 0 + (s₄.gpr .eax).toNat := by omega
  have eax₃ : (s₃.gpr .eax).toNat = w32 s.mem base (src + 4 * N) := by
    rw [u₃.other _ (by decide), u₂.gpr, ← O₁.w32 (by omega) (by omega)]
  rw [eax₃, z, Nat.zero_add] at mask
  have hsrcN : val32 s₁.mem base src N = val32 s.mem base src N := O₁.val32 (by omega) (by omega)
  refine WP.mono (selectsW_ok hs₆ _ mask hN (src := src) (tmp := M.tmp) (o := o) (by omega) (by omega)
      (by omega) (by omega) (by omega))
    fun u ⟨O, V, K⟩ => ⟨(Outs.of_outside O₁ (by simp)).trans (Outs.of_outside (mem₆ ▸ O) (by simp)), ?_,
      k₆.trans (K.mono (by decide))⟩
  rw [V, mem₆]
  have hmX : m < 2 ^ (32 * N) := hm ▸ val32_lt _ _ _ _
  have := csub_arith (T := val32 s.mem base src N) (D := val32 s₁.mem base M.tmp N)
    (top := w32 s.mem base (src + 4 * N)) (b := c) hmX (val32_lt _ _ _ _)
    (by rw [← val32_succ]; exact hV) (by rw [← hm]; exact V₁)
  rw [val32_succ s.mem base src N, ← this]
  by_cases h : w32 s.mem base (src + 4 * N) < c.toNat
  · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, hsrcN]
  · simp only [h, decide_false, Bool.not_false, ite_true, ite_false]

end VG.Proof.Mont.X86
