import VerifiedGarbage.Proof.Mont.X86.Ops
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86.MontCall

/-!
# Field operations by calls, on x86 (32-bit)

The field operations of the curves' code are calls of the functions of a
modulus `F` (`Impl/Weierstrass/X86/Mont.lean`): `mulC_ok`, `addC_ok` and
`subC_ok` state `mulCall_ok`, `addCall_ok` and `subCall_ok` (`MontCall.lean`)
for numbers of `M.n` 64-bit words modulo `m`, as `Proof/Mont/X86/Ops.lean`'s
`mul_ok`, `add_ok` and `sub_ok` state the inline operations: the functions'
own working space is at `wk`, above the operands (`CallCfg`), and an
operation writing `[o]` keeps the registers but `clob`, and the memory but
`[o]`, the temporary area of `M`, the own working space and memory past the
working space (`CKeep`).
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Proof.Mont.X86 VG.Proof.Mont

/-- The `z` bytes below `sp` (`z ≥ 20`), apart from the `size` bytes at
`base`, as `Scr` has them. -/
theorem stkOk_of {sp : BitVec 32} {base : Addr} {size z : Nat} (hz : 20 ≤ z) (hsp : z ≤ sp.toNat)
    (hn : base.toNat + size ≤ 2 ^ 32) (hs : 0 < size)
    (hd : Region.Disjoint ⟨sp.setWidth 64 - BitVec.ofNat 64 z, z⟩ ⟨base, size⟩) : StkOk sp base size := by
  refine ⟨by omega, ?_⟩
  by_contra h
  simp only [not_or, Nat.not_le] at h
  have hb := sp.isLt
  by_cases hc : base.toNat + z ≤ sp.toNat
  · refine hd (sp.setWidth 64 - BitVec.ofNat 64 z) ?_ ?_
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
    · simp only [Region.Contains]
      bv_omega
  · refine hd base ?_ ?_
    · simp only [Region.Contains]
      bv_omega
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

/-- The functions of `F` compute modulo `m` on numbers of `M.n` words, in a
working space of 8192 bytes, with their own working space at `wk`. -/
structure CallCfg (F : Spec.Weierstrass.Mont.Modulus) (M : Mod) (m size wk : Nat) : Prop where
  fn : Mont.FnOk F
  k : F.k = M.n
  fm : F.m = m
  size : size = 8192
  own : wk = Mont.own M.n

theorem CallCfg.own_le {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {m size wk : Nat}
    (h : CallCfg F M m size wk) : wk + 64 * M.n = 4096 := by
  have := (Mont.saveAt_le (k := M.n) (by rw [← h.k]; exact h.fn.mul.k0) (by rw [← h.k]; exact h.fn.k9)).2
  rw [h.own]; exact this

/-- What an operation writing `[o]` keeps: the registers but `clob`, the
regions, and the memory but `[o]`, the temporary area, the own working space
at `wk` and memory past the working space. -/
structure CKeep (M : Mod) (base : Addr) (wk o : Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outs base [(o, 8 * M.n), (M.tmp, 8 * M.n), (wk, 64 * M.n), Mont.outW] s.mem s'.mem

theorem CKeep.scr {M : Mod} {base : Addr} {wk o size : Nat} {s s' : State}
    (h : CKeep M base wk o s s') (hs : Scr s base size) : Scr s' base size :=
  hs.of_eq (h.gpr _ (by decide)) (h.gpr _ (by decide)) h.wr

theorem CKeep.unch {M : Mod} {base : Addr} {wk o : Nat} {s s' : State} (h : CKeep M base wk o s s') :
    VG.Proof.Weierstrass.Unch base [(o, 8 * M.n), (M.tmp, 8 * M.n), (wk, 64 * M.n), Mont.outW] s.mem s'.mem :=
  h.mem

theorem CKeep.keeps {M : Mod} {base : Addr} {wk o : Nat} {s s' : State} (h : CKeep M base wk o s s') :
    Keeps clob s s' := ⟨h.gpr, h.rd, h.wr⟩

theorem CKeep.of_call {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr} {wk o : Nat}
    {s s' : State} (hk : F.k = M.n) (hwk : wk = Mont.own M.n) (h : Mont.CallKeep F.k base o s s') :
    CKeep M base wk o s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl <;> decide), h.rd, h.wr, h.mem.mono (by
    intro r hr
    simp only [Mont.callW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [hk, hwk])⟩

section
variable {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {m size wk : Nat} (hC : CallCfg F M m size wk)
  {s : State} {base : Addr} (hs : Scr s base size) {o a b : Nat} (ho : o + 8 * M.n ≤ wk)
  (ha : a + 8 * M.n ≤ wk) (hb : b + 8 * M.n ≤ wk)
include hC hs ho ha hb

theorem mulC_ok (hB : wordsVal s.mem base b M.n < m) :
    WP isa (Mont.mulCall F o a b) s fun s' => CKeep M base wk o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  have hk := hC.k; have hfm := hC.fm; have hwk := hC.own
  refine WP.mono (Mont.mulCall_ok hC.fn (hC.size ▸ hs) (by rw [hk, ← hwk]; exact ho)
    (by rw [hk, ← hwk]; exact ha) (by rw [hk, ← hwk]; exact hb) (by rw [hk, hfm]; exact hB))
    fun s' ⟨K, L, E⟩ => ?_
  rw [hk, hfm] at L E
  exact ⟨CKeep.of_call hk hwk K, L, E⟩

theorem addC_ok (hAB : wordsVal s.mem base a M.n + wordsVal s.mem base b M.n < 2 * m) :
    WP isa (Mont.addCall F o a b) s fun s' => CKeep M base wk o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + wordsVal s.mem base b M.n) % m := by
  have hk := hC.k; have hfm := hC.fm; have hwk := hC.own
  refine WP.mono (Mont.addCall_ok hC.fn (hC.size ▸ hs) (by rw [hk, ← hwk]; exact ho)
    (by rw [hk, ← hwk]; exact ha) (by rw [hk, ← hwk]; exact hb) (by rw [hk, hfm]; exact hAB))
    fun s' ⟨K, E⟩ => ?_
  rw [hk, hfm] at E
  exact ⟨CKeep.of_call hk hwk K, E⟩

theorem subC_ok (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (Mont.subCall F o a b) s fun s' => CKeep M base wk o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n) % m := by
  have hk := hC.k; have hfm := hC.fm; have hwk := hC.own
  refine WP.mono (Mont.subCall_ok hC.fn (hC.size ▸ hs) (by rw [hk, ← hwk]; exact ho)
    (by rw [hk, ← hwk]; exact ha) (by rw [hk, ← hwk]; exact hb) (by rw [hk, hfm]; exact hA)
    (by rw [hk, hfm]; exact hB))
    fun s' ⟨K, E⟩ => ?_
  rw [hk, hfm] at E
  exact ⟨CKeep.of_call hk hwk K, E⟩

end

/-! ## Frames from the code

Memory past the working space changes only in the stack the calls use: code
that never writes `esp` changes memory only in the writable regions and the
`n` bytes below `esp`, if its calls and frames use no more (`WP.withFrame`). -/

theorem NoSp.seq_left {a b : Prog isa} (h : NoSp (.seq a b)) : NoSp a :=
  fun i hi => h i (List.mem_append_left _ hi)

theorem NoSp.seq_right {a b : Prog isa} (h : NoSp (.seq a b)) : NoSp b :=
  fun i hi => h i (List.mem_append_right _ hi)

theorem NoSp.loop {b : Prog isa} {cc : Cond} (h : NoSp (.loop b cc)) : NoSp b := h

theorem WP.withFrame {c : Prog isa} {s : State} {Q : State → Prop} {n : Nat} (hsp : NoSp c)
    (hn : stackUse c ≤ n) (hd : n ≤ (s.gpr .esp).toNat) (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ Frame (s.wr ++ [below (s.gpr .esp) n]) s.mem s'.mem := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Frame.below_mono (Exec.frameSp he hsp (by omega)) hn hd⟩

/-- Code that never writes `esp`, whose calls and frames use at most `n` bytes
of stack. -/
abbrev SpOk (c : Prog isa) (n : Nat) : Prop := NoSp c ∧ stackUse c ≤ n

theorem SpOk.left {a b : Prog isa} {n : Nat} (h : SpOk (.seq a b) n) : SpOk a n :=
  ⟨NoSp.seq_left h.1, Nat.le_trans (Nat.le_max_left _ _) h.2⟩

theorem SpOk.right {a b : Prog isa} {n : Nat} (h : SpOk (.seq a b) n) : SpOk b n :=
  ⟨NoSp.seq_right h.1, Nat.le_trans (Nat.le_max_right _ _) h.2⟩

theorem SpOk.seq {a b : Prog isa} {n : Nat} (ha : SpOk a n) (hb : SpOk b n) : SpOk (.seq a b) n :=
  ⟨fun i hi => (List.mem_append.mp hi).elim (ha.1 i) (hb.1 i), Nat.max_le.mpr ⟨ha.2, hb.2⟩⟩

/-- `SpOk` of the parts `WP.split` makes. -/
theorem SpOk.split {n : Nat} (l : List (Prog isa)) (b r : Prog isa) (h : SpOk (l.foldr .seq (.seq b r)) n) :
    SpOk (l.foldr .seq b) n ∧ SpOk r n := by
  induction l with
  | nil => exact ⟨h.left, h.right⟩
  | cons a l ih =>
    obtain ⟨h₁, h₂⟩ := ih h.right
    exact ⟨h.left.seq h₁, h₂⟩

theorem WP.spFrame {c : Prog isa} {s : State} {Q : State → Prop} {n : Nat} (hsp : SpOk c n)
    (hd : n ≤ (s.gpr .esp).toNat) (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ Frame (s.wr ++ [below (s.gpr .esp) n]) s.mem s'.mem :=
  WP.withFrame hsp.1 hsp.2 hd h

/-- The `a` bytes below `sp` are among its `b` bytes below it. -/
theorem below_le_sub {sp : BitVec 32} {a b : Nat} (hab : a ≤ b) (hb : b ≤ sp.toNat) :
    Region.Sub (below sp a) (below sp b) := by
  have := below_inner (sp := sp) (k := 0) (a := a) (b := b) (by omega) hb
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using this

/-- `WP.spFrame`, for a postcondition that takes the frame. -/
theorem WP.withSp {c : Prog isa} {s : State} {Q : State → Prop} {n : Nat} (hsp : SpOk c n)
    (hd : n ≤ (s.gpr .esp).toNat)
    (h : WP isa c s fun s' => Frame (s.wr ++ [below (s.gpr .esp) n]) s.mem s'.mem → Q s') :
    WP isa c s Q :=
  WP.mono (WP.spFrame hsp hd h) fun _ ⟨q, f⟩ => q f

/-- A chain of code, `l` then `b` then `r`, as the code `l` then `b`, then
`r`: so that the frame of a prefix (`WP.spFrame`) is known where `r` starts. -/
theorem WP.split (l : List (Prog isa)) (b r : Prog isa) {s : State} {Q : State → Prop} :
    WP isa (l.foldr .seq (.seq b r)) s Q ↔ WP isa (.seq (l.foldr .seq b) r) s Q := by
  induction l generalizing s Q with
  | nil => exact Iff.rfl
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, WP.seq_iff, WP.seq_iff, WP.seq_iff]
    constructor
    · exact fun h => WP.mono h fun _ h' => WP.seq_iff.mp (ih.mp h')
    · exact fun h => WP.mono h fun _ h' => ih.mpr (WP.seq_iff.mpr h')

/-- Code then nothing. -/
theorem WP.seq_nil {c : Prog isa} {s : State} {Q : State → Prop} :
    WP isa (.seq c (.block [])) s Q ↔ WP isa c s Q := by
  rw [WP.seq_iff]
  exact ⟨fun h => WP.mono h fun _ h' => WP.block_nil_iff.mp h', fun h => WP.mono h fun _ h' => WP.block_nil h'⟩

end VG.Proof.Weierstrass.X86
