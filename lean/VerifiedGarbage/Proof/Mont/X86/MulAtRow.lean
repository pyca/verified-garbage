module

public import VerifiedGarbage.Impl.Mont.X86.MulAt
public import VerifiedGarbage.Proof.Mont.X86.Dynamic
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Framework.Omega

/-! # The rows of the callable multiplication, reading `a` through its argument

`rowAt` is `row` but for its first block, which reads the row's multiplier
`a_i` at `edi + a + 4i` for the argument `a` (`rowAt_ok`, from `rowTail_ok`);
`loopAt_ok` runs the rows as `loop_ok` does. The argument stays readable and
unchanged while the rows write only the working space (`readSrc_keep`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Mont VG.Proof.Mont
open VG.Proof.Mont.X86

/-- The 4 bytes a memory operand reads lie past the working space. -/
def ArgFar (s : State) (base : Addr) (size : Nat) (m : MemOp) : Prop :=
  ∀ j < 4, size ≤ ofs base (s.ea m + BitVec.ofNat 64 j)

/-- A memory operand past the working space reads the same after changes
within ranges of the working space, with its base register and the
permissions as they were. -/
theorem readSrc_keep {s t : State} {base : Addr} {size : Nat} {rs : List (Nat × Nat)} {m : MemOp}
    (hf : ArgFar s base size m) (O : Outs base rs s.mem t.mem) (hr : ∀ r ∈ rs, r.1 + r.2 ≤ size)
    (hb : t.gpr m.base = s.gpr m.base) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    readSrc t (.mem m) = readSrc s (.mem m) := by
  have he : t.ea m = s.ea m := by simp only [State.ea, hb]
  show t.load32 (t.ea m) = s.load32 (s.ea m)
  simp only [State.load32, he, hrd, hwr]
  congr 1
  refine congrArg some (Mem.readW_congr fun i hi => O _ fun r hr' => .inr ?_)
  have := hf i (by omega)
  have := hr r hr'
  omega

theorem ArgFar.keep {s t : State} {base : Addr} {size : Nat} {m : MemOp} (hf : ArgFar s base size m)
    (hb : t.gpr m.base = s.gpr m.base) : ArgFar t base size m := by
  intro j hj
  have he : t.ea m = s.ea m := by simp only [State.ea, hb]
  rw [he]; exact hf j hj

/-- A load through a register `D` bytes into the working space. -/
theorem readSrc_ptr {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {r : Reg} {D : Nat}
    (hp : s.gpr r = s.gpr .edi + BitVec.ofNat 32 D) (hD : D + 4 ≤ size) :
    readSrc s (.mem { base := r }) = some (s.mem.readW (off base D) 32) := by
  have he : s.ea { base := r } = off base D := by
    change ((s.gpr r + BitVec.ofNat 32 0).setWidth 64) = _
    rw [BitVec.add_zero, hp]
    exact hs.ea (by omega)
  show s.load32 (s.ea _) = _
  rw [he, State.load32, ite_eq_left_iff.mpr fun h => absurd (hs.read hD) h]

/-- A memory operand reads the same after a write of another register. -/
theorem readSrc_upd {s t : State} {d : Reg} {v : BitVec 32} (u : Upd s t d v) {m : MemOp} (h : m.base ≠ d) :
    readSrc t (.mem m) = readSrc s (.mem m) := by
  show t.load32 (t.ea m) = s.load32 (s.ea m)
  have he : t.ea m = s.ea m := by simp only [State.ea, u.other _ h]
  rw [he]
  simp only [State.load32, u.mem, u.rd, u.wr]

theorem add_ofNat (x : BitVec 32) (d e : Nat) :
    x + BitVec.ofNat 32 d + BitVec.ofNat 32 e = x + BitVec.ofNat 32 (d + e) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- An iteration of the loop of `mulAt`. -/
theorem rowAt_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {N acc a b mo inv mult i m : Nat}
    (hL : MulLay N size acc a b mo) (hX : MultLay N size acc a b mo inv mult)
    (hv : inv + 4 ≤ size) (hsepInv : inv + 4 ≤ acc ∨ acc + 4 * (2 * N + 1) ≤ inv) (hi : i < N)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hm : val32 s.mem base mo N = m) (hinv : (m * w32 s.mem base inv + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base b N < m)
    (hT : val32 s.mem base (acc + 4 * i) (2 * N + 1 - i) < 2 * m)
    (hA : readSrc s (.mem argA) = some (BitVec.ofNat 32 a)) :
    WP isa (rowAt N acc b mo inv mult) s fun u =>
      u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * (i + 1)) ∧
      u.zf = some (decide (i + 1 = N)) ∧
      Outs base [(acc, 4 * (2 * N + 1)), (mult, 4)] s.mem u.mem ∧
      (∃ q, 2 ^ 32 * val32 u.mem base (acc + 4 * (i + 1)) (2 * N + 1 - (i + 1)) =
        val32 s.mem base (acc + 4 * i) (2 * N + 1 - i) + w32 s.mem base (a + 4 * i) * val32 s.mem base b N +
          q * m) ∧
      val32 u.mem base (acc + 4 * (i + 1)) (2 * N + 1 - (i + 1)) < 2 * m ∧
      Keeps clobW s u := by
  have hn := hs.nowrap
  have := hL.acc_le
  have := hL.a_le
  have := hL.b_le
  have := hL.mo_le
  have := hX.le
  unfold rowAt loadArgA
  refine WP.seq (wp_movS hA fun s₀ u₀ _ => ?_)
  refine wp_addS rfl fun s₁ u₁ _ => ?_
  have K₁ : Keeps [.eax] s s₁ := u₀.keeps.widen u₁.keeps
  have hs₁ := hs.of_keeps K₁ (by decide)
  have eax₁ : s₁.gpr .eax = s₁.gpr .edi + BitVec.ofNat 32 (4 * i + a) := by
    rw [u₁.gpr, u₀.gpr, u₀.other .ebp (by decide), K₁.1 .edi (by decide), hp, BitVec.add_comm, add_ofNat]
  refine wp_movS (readSrc_ptr hs₁ eax₁ (by omega_arith)) fun s₂ u₂ _ => ?_
  have K₂ : Keeps [.eax] s s₂ := K₁.widen u₂.keeps
  have hs₂ := hs.of_keeps K₂ (by decide)
  refine wp_storeS (hs₂.ea (d := mult) (by omega_arith)) (hs₂.write (d := mult) (n := 4) (by omega_arith))
    fun s₃ m₃ => WP.block_nil ?_
  have k₃ : Keeps clobW s s₃ := (K₂.mono (by decide)).trans (m₃.keeps _)
  have hs₃ := hs.of_keeps k₃ (by decide)
  have hp₃ : s₃.gpr .ebp = s₃.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [m₃.gpr, K₂.1 _ (by decide), K₂.1 _ (by decide)]; exact hp
  have mem₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem, u₀.mem]
  have O₃ : Outside base mult 4 s.mem s₃.mem := by
    rw [m₃.mem, mem₂]; exact writeW32_outside _ _ _ (by omega_arith)
  have mult₃ : w32 s₃.mem base mult = w32 s.mem base (a + 4 * i) := by
    rw [m₃.mem, w32_write_self, u₂.gpr, u₁.mem, u₀.mem, Nat.add_comm a]
  have win₃ : val32 s₃.mem base (acc + 4 * i) (2 * N + 1 - i) = val32 s.mem base (acc + 4 * i) (2 * N + 1 - i) :=
    O₃.val32 (by have := hX.sacc; omega_arith) (by omega_arith)
  have b₃ : val32 s₃.mem base b N = val32 s.mem base b N :=
    O₃.val32 (by have := hX.sb; omega_arith) (by omega_arith)
  have mo₃ : val32 s₃.mem base mo N = m := by
    rw [O₃.val32 (by have := hX.smo; omega_arith) (by omega_arith), hm]
  have inv₃ : w32 s₃.mem base inv = w32 s.mem base inv :=
    O₃.w32 (by have := hX.sinv; omega_arith) (by omega_arith)
  refine WP.mono (rowTail_ok hs₃ hL hX hv hsepInv hi hp₃ mo₃ (by rw [inv₃]; exact hinv) (by rw [b₃]; exact hB)
    (by rw [win₃]; exact hT)) fun u ⟨hp', hz, O, ⟨q, hq⟩, hT', K⟩ =>
      ⟨hp', hz, (Outs.of_outside O₃ (by simp)).trans O, ⟨q, by rw [hq, win₃, mult₃, b₃]⟩, hT', k₃.trans K⟩

/-- The loop of `mulAt`, as `loop_ok`. -/
theorem loopAt_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {N acc a b mo inv mult m : Nat}
    (hL : MulLay N size acc a b mo) (hX : MultLay N size acc a b mo inv mult)
    (hv : inv + 4 ≤ size) (hsepInv : inv + 4 ≤ acc ∨ acc + 4 * (2 * N + 1) ≤ inv) (hN : 0 < N)
    (hm : val32 s.mem base mo N = m) (hinv : (m * w32 s.mem base inv + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base b N < m) (hA : readSrc s (.mem argA) = some (BitVec.ofNat 32 a))
    (hf : ArgFar s base size argA) {t : State} (h0 : LoopInvW base N acc a b m mult 0 s t) :
    WP isa (.loop (rowAt N acc b mo inv mult) .ne) t fun u =>
      LoopInvW base N acc a b m mult N s u := by
  have := hL.acc_le
  have := hL.a_le
  have := hL.b_le
  have := hL.mo_le
  have := hX.le
  have hn := hs.nowrap
  refine WP.loop (M := isa)
    (fun n t' => ∃ i, n = N - i ∧ i < N ∧ LoopInvW base N acc a b m mult i s t') ?_ N t ⟨0, rfl, hN, h0⟩
  rintro n t' ⟨i, rfl, hi, I⟩
  have ht := hs.of_keeps I.keeps (by decide)
  have hm' : val32 t'.mem base mo N = m := by
    rw [outs2_val32 I.out (by have := hL.smo; omega_arith) (by have := hX.smo; omega_arith) (by omega_arith), hm]
  have hb' : val32 t'.mem base b N = val32 s.mem base b N :=
    outs2_val32 I.out (by have := hL.sb; omega_arith) (by have := hX.sb; omega_arith) (by omega_arith)
  have ha' : w32 t'.mem base (a + 4 * i) = w32 s.mem base (a + 4 * i) :=
    outs2_w32 I.out (by have := hL.sa; omega_arith) (by have := hX.sa; omega_arith) (by omega_arith)
  have hinv' : (m * w32 t'.mem base inv + 1) % 2 ^ 32 = 0 := by
    rw [outs2_w32 I.out hsepInv (by have := hX.sinv; omega_arith) (by omega_arith)]; exact hinv
  have hA' : readSrc t' (.mem argA) = some (BitVec.ofNat 32 a) := by
    rw [readSrc_keep hf I.out (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (I.keeps.1 _ (by decide)) I.keeps.2.1 I.keeps.2.2]
    exact hA
  refine WP.mono (rowAt_ok ht hL hX hv hsepInv hi I.ebp hm' hinv' (hb' ▸ hB) I.lt hA')
    fun u ⟨hp, hz, O, ⟨q, hq⟩, hT, K⟩ => ?_
  rw [hb', ha'] at hq
  have I' : LoopInvW base N acc a b m mult (i + 1) s u := by
    refine ⟨hp, I.out.trans O, I.keeps.trans K, hT, ?_⟩
    obtain ⟨U, hU⟩ := I.cong
    refine ⟨U + 2 ^ (32 * i) * q, ?_⟩
    rw [pow32_succ, val32_succ, Nat.mul_assoc, Nat.mul_left_comm, hq]
    generalize 2 ^ (32 * i) = P at *
    grind
  by_cases hNi : i + 1 = N
  · refine .inl ⟨by simp only [eval, hz, hNi, decide_true, Option.map_some, Bool.not_true], hNi ▸ I'⟩
  · exact .inr ⟨by simp only [eval, hz, decide_eq_false hNi, Option.map_some, Bool.not_false],
      N - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, hNi], I'⟩

end VG.Proof.Mont.X86.Dynamic
