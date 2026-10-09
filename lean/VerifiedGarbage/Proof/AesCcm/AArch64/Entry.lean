import VerifiedGarbage.Proof.AesCcm.AArch64.Callee

/-!
# AES-CCM on AArch64: the arguments and the entry

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the facts the proofs use about the arguments (`Args`,
`args_of_seal`, `args_of_open`). `entry` loads `work`, the tag length and
`tag` from the stack, saves our caller's registers at `W + 128` and keeps the
arguments in registers and in `W` (`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm save saved)
open VG.Proof.AesGcm.AArch64 (savedMem savedR SavedAt save_ok readW_writeW_other savedMem_slot savedMem_frame
  covers_of_mem covers_left in_off)

/-- The public values of the arguments of `s`. -/
def cxOf (s : State) : Cx where
  K := s.gpr .x0
  W := stackArg s 2
  D := s.gpr .x6
  A := s.gpr .x4
  R := (s.gpr .x1).toNat
  tl := (stackArg s 1).toNat
  n := (s.gpr .x7).toNat
  al := (s.gpr .x5).toNat
  nl := (s.gpr .x3).toNat
  SP := s.sp
  T := stackArg s 0

/-- What `seal` and `open` are given: the public values `c`, and the nonce at
`N`. -/
structure Args (c : Cx) (N : Addr) (s : State) : Prop where
  lay : Lay c
  x0 : s.gpr .x0 = c.K
  x1 : s.gpr .x1 = BitVec.ofNat 64 c.R
  x2 : s.gpr .x2 = N
  x3 : s.gpr .x3 = BitVec.ofNat 64 c.nl
  x4 : s.gpr .x4 = c.A
  x5 : s.gpr .x5 = BitVec.ofNat 64 c.al
  x6 : s.gpr .x6 = c.D
  x7 : s.gpr .x7 = BitVec.ofNat 64 c.n
  sp : s.sp = c.SP
  w : stackArg s 2 = c.W
  tl : stackArg s 1 = BitVec.ofNat 64 c.tl
  t : stackArg s 0 = c.T
  perm : Perm c s
  nonce : Buf c s N c.nl
  nd : (⟨N, c.nl⟩ : Region).Disjoint ⟨c.D, c.n⟩
  argsC : Covers [args s] (s.rd ++ s.wr)
  argsW : (args s).Disjoint ⟨c.W, 2560⟩
  argsD : (args s).Disjoint ⟨c.D, c.n⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- `Args` from the layout, with the buffers covered as each function's
permissions say. -/
theorem args_of_lay {s : State} (h : oneLay s)
    (hk : Covers [⟨s.gpr .x0, 240⟩] (s.rd ++ s.wr)) (hN : Covers [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨s.gpr .x4, (s.gpr .x5).toNat⟩] (s.rd ++ s.wr)) (ha : Covers [args s] (s.rd ++ s.wr))
    (hT : Covers [⟨stackArg s 0, (stackArg s 1).toNat⟩] (s.rd ++ s.wr))
    (hD : Covers [⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.wr) (hW : Covers [⟨stackArg s 2, 2560⟩] s.wr) :
    Args (cxOf s) (s.gpr .x2) s := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, b1, b2, b3, b4, b5, b6, _, hR, hv⟩ := h
  simp only [Spec.Ccm.valid, Spec.Ccm.tagLenOk, Spec.Ccm.nonceLenOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨ht4, ht16⟩, hte⟩, hn7, hn13⟩, hp⟩, -⟩ := hv
  rw [Nat.pow_mul] at hp
  exact {
    lay := ⟨b1, b6, b4, b3, d2, d1, d9, d6, d5, hR, BitVec.isLt _, BitVec.isLt _, ht4, ht16, hte, hn7, hn13, hp,
      b5, d8, d7⟩
    x0 := rfl
    x1 := (ofNat_toNat64 _).symm
    x2 := rfl
    x3 := (ofNat_toNat64 _).symm
    x4 := rfl
    x5 := (ofNat_toNat64 _).symm
    x6 := rfl
    x7 := (ofNat_toNat64 _).symm
    sp := rfl
    w := rfl
    tl := (ofNat_toNat64 _).symm
    t := rfl
    perm := ⟨hk, hW, hD, hA, hT⟩
    nonce := ⟨hN, BitVec.isLt _, b2, d4⟩
    nd := d3
    argsC := ha
    argsW := d11.symm
    argsD := d10.symm }

/-- `seal`'s arguments, and its tag, to write. -/
theorem args_of_seal {s : State} (h : sealPre s) :
    Args (cxOf s) (s.gpr .x2) s ∧ Covers [⟨stackArg s 0, (stackArg s 1).toNat⟩] s.wr := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .x0, 240⟩ : Region), ⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x4, (s.gpr .x5).toNat⟩,
      args s], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region), ⟨stackArg s 0, (stackArg s 1).toNat⟩,
      ⟨stackArg s 2, 2560⟩], Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp))
    (covers_left (mwr _ (by simp))) (mwr _ (by simp)) (mwr _ (by simp)), mwr _ (by simp)⟩

/-- `open`'s arguments, with its received tag, to read. -/
theorem args_of_open {s : State} (h : openPre s) : Args (cxOf s) (s.gpr .x2) s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .x0, 240⟩ : Region), ⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x4, (s.gpr .x5).toNat⟩,
      ⟨stackArg s 0, (stackArg s 1).toNat⟩, args s], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region), ⟨stackArg s 2, 2560⟩], Covers [r] s.wr :=
    fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp))
    (mwr _ (by simp)) (mwr _ (by simp))

/-! ## The entry -/

/-- The memory after the entry: the registers saved and the arguments kept. -/
def entryMem (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Mem :=
  ((((savedMem m W g).writeW (W + BitVec.ofNat 64 216) (g .x4)).writeW (W + BitVec.ofNat 64 224) (g .x5)).writeW
    (W + BitVec.ofNat 64 232) (g .x3)).writeW (W + BitVec.ofNat 64 240) (g .x11)

/-- What the entry writes. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 120⟩

theorem entry_contains (W : Addr) {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 248) :
    (entryR W).Contains (W + BitVec.ofNat 64 d) 8 := by
  rw [show W + BitVec.ofNat 64 d = (W + BitVec.ofNat 64 128) + BitVec.ofNat 64 (d - 128) from
    (Offset.add_add_eq W (by omega_arith)).symm]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem entryMem_frame (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Frame [entryR W] m (entryMem m W g) := by
  have c (d : Nat) (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 248) := entry_contains W h₁ h₂
  exact (((((savedMem_frame m W g).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩).writeW
    (List.mem_singleton_self _) _ (c 216 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 224 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 232 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 240 (by decide) (by decide))

theorem entryMem_saved (m : Mem) (W : Addr) {g : Reg → BitVec 64} {s₀ : State}
    (hg : ∀ p ∈ saved, g p.1 = s₀.gpr p.1) : SavedAt (entryMem m W g) W s₀ := by
  have h₀ : SavedAt (savedMem m W g) W s₀ := fun p hp => (savedMem_slot m W g p hp).trans (hg p hp)
  refine h₀.frame (rs := [⟨W + BitVec.ofNat 64 216, 32⟩]) ?_ ?_
  · have c (d : Nat) (h₁ : 216 ≤ d) (h₂ : d + 8 ≤ 248) :
        (⟨W + BitVec.ofNat 64 216, 32⟩ : Region).Contains (W + BitVec.ofNat 64 d) 8 := by
      rw [show W + BitVec.ofNat 64 d = (W + BitVec.ofNat 64 216) + BitVec.ofNat 64 (d - 216) from
        (Offset.add_add_eq W (by omega_arith)).symm]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 216 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 224 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 232 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 240 (by decide) (by decide))
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)

theorem entryMem_slot (m : Mem) (W : Addr) (g : Reg → BitVec 64) :
    (entryMem m W g).readW (W + BitVec.ofNat 64 216) 64 = g .x4 ∧
    (entryMem m W g).readW (W + BitVec.ofNat 64 224) 64 = g .x5 ∧
    (entryMem m W g).readW (W + BitVec.ofNat 64 232) 64 = g .x3 ∧
    (entryMem m W g).readW (W + BitVec.ofNat 64 240) 64 = g .x11 := by
  simp only [entryMem]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  repeat (first
    | rw [Mem.readW_writeW_self64]
    | rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)])

/-- What the entry leaves. -/
structure Entered (c : Cx) (N : Addr) (s s₁ : State) : Prop where
  env : Env c s₁
  slots : Slots c s₁.mem
  saved : SavedAt s₁.mem c.W s
  frame : Frame [entryR c.W] s.mem s₁.mem
  x2 : s₁.gpr .x2 = N
  x3 : s₁.gpr .x3 = BitVec.ofNat 64 c.nl
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

/-- The loads of `work`, the tag length and `tag`. -/
theorem ldr_ok {c : Cx} {N : Addr} {s : State} (Ar : Args c N s) :
    WP isa (.block [.ldrSp .x9 16, .ldrSp .x10 8, .ldrSp .x11 0]) s fun s₀ => s₀.gpr .x9 = c.W ∧
      s₀.gpr .x10 = BitVec.ofNat 64 c.tl ∧ s₀.gpr .x11 = c.T ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s₀.gpr r = s.gpr r) ∧ s₀.sp = s.sp ∧
      s₀.mem = s.mem ∧ s₀.rd = s.rd ∧ s₀.wr = s.wr := by
  have hA : Covers [⟨s.sp, 24⟩] (s.rd ++ s.wr) := by
    have := Ar.argsC
    simpa [args, stackArgAddr] using this
  have a₀ : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa using in_off (d := 0) (n := 8) hA (by decide) (by decide)
  have a₈ : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 :=
    in_off (d := 8) (n := 8) hA (by decide) (by decide)
  have a₁₆ : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 16) 8 :=
    in_off (d := 16) (n := 8) hA (by decide) (by decide)
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [a₀, a₈, a₁₆], rfl⟩ fun s₀ hs₀ => ?_
  subst hs₀
  refine ⟨?_, ?_, ?_, fun r h₁ h₂ h₃ => by simp [gpr_write, h₁, h₂, h₃], rfl, rfl, rfl, rfl⟩
  · rw [← Ar.w]
    simp [gpr_write, stackArg, stackArgAddr, Mem.readW]
  · rw [← Ar.tl]
    simp [gpr_write, stackArg, stackArgAddr, Mem.readW]
  · rw [← Ar.t]
    simp [gpr_write, stackArg, stackArgAddr, Mem.readW]

/-- After the entry. -/
theorem entry_ok {c : Cx} {N : Addr} {s : State} (Ar : Args c N s) :
    WP isa (.block entry) s (Entered c N s) := by
  refine WP.block_append (WP.block_append (WP.mono (ldr_ok Ar) fun s₀ ⟨x9₀, x10₀, x11₀, g₀, sp₀, m₀, rd₀, wr₀⟩ => ?_))
  have hperm₀ : Perm c s₀ := Ar.perm.of_eq rd₀ wr₀
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s₀ .x9 x9₀ hperm₀.w
  have w (d : Nat) (h : d + 8 ≤ 2560) := in_off hperm₀.w h (by decide)
  rw [← wr₁] at w
  have gx : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s₁.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by rw [g₁, g₀ r h₁ h₂ h₃]
  have x9₁ : s₁.gpr .x9 = c.W := by rw [g₁, x9₀]
  have x10₁ : s₁.gpr .x10 = BitVec.ofNat 64 c.tl := by rw [g₁, x10₀]
  have w₁ := w 216 (by decide)
  have w₂ := w 224 (by decide)
  have w₃ := w 232 (by decide)
  have w₄ := w 240 (by decide)
  obtain ⟨s₂, run₂, m₂, y19, y20, y21, y22, y27, y28, y2, y3, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x9, mov .x20 .x10, mov .x21 .x0, mov .x22 .x1, .str .x .x4 .x19 aadO,
        .str .x .x5 .x19 alenO, .str .x .x3 .x19 nlenO, .str .x .x11 .x19 tagO, mov .x27 .x6, mov .x28 .x7] s₁ =
        some s₂ ∧
      s₂.mem = (((s₁.mem.writeW (c.W + BitVec.ofNat 64 216) (s₁.gpr .x4)).writeW (c.W + BitVec.ofNat 64 224)
        (s₁.gpr .x5)).writeW (c.W + BitVec.ofNat 64 232) (s₁.gpr .x3)).writeW (c.W + BitVec.ofNat 64 240)
        (s₁.gpr .x11) ∧
      s₂.gpr .x19 = s₁.gpr .x9 ∧ s₂.gpr .x20 = s₁.gpr .x10 ∧ s₂.gpr .x21 = s₁.gpr .x0 ∧
      s₂.gpr .x22 = s₁.gpr .x1 ∧ s₂.gpr .x27 = s₁.gpr .x6 ∧ s₂.gpr .x28 = s₁.gpr .x7 ∧
      s₂.gpr .x2 = s₁.gpr .x2 ∧ s₂.gpr .x3 = s₁.gpr .x3 ∧
      s₂.sp = s₁.sp ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by carun [tagO, x9₁, w₁, w₂, w₃, w₄], ?_⟩
    simp only [Mem.writeW, gpr_write, mem_write, sp_write, rd_write, wr_write, ite_true, ite_false, reduceCtorEq,
      x9₁, and_self, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq, true_and]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have hm : s₂.mem = entryMem s.mem c.W s₀.gpr := by
    rw [m₂, m₁, m₀, entryMem, g₁]
  obtain ⟨e₁, e₂, e₃, e₄⟩ := entryMem_slot s.mem c.W s₀.gpr
  rw [g₀ .x4 (by decide) (by decide) (by decide)] at e₁
  rw [g₀ .x5 (by decide) (by decide) (by decide)] at e₂
  rw [g₀ .x3 (by decide) (by decide) (by decide)] at e₃
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [y19, x9₁]
  · rw [y20, x10₁]
  · rw [y21, gx .x0 (by decide) (by decide) (by decide), Ar.x0]
  · rw [y22, gx .x1 (by decide) (by decide) (by decide), Ar.x1]
  · rw [y27, gx .x6 (by decide) (by decide) (by decide), Ar.x6]
  · rw [y28, gx .x7 (by decide) (by decide) (by decide), Ar.x7]
  · rw [sp₂, sp₁, sp₀, Ar.sp]
  · exact Ar.perm.of_eq (by rw [rd₂, rd₁, rd₀]) (by rw [wr₂, wr₁, wr₀])
  · rw [hm, e₁, Ar.x4]
  · rw [hm, e₂, Ar.x5]
  · rw [hm, e₃, Ar.x3]
  · rw [hm, e₄, x11₀]
  · rw [hm]
    exact entryMem_saved s.mem c.W fun p hp => by
      have h9 : p.1 ≠ .x9 ∧ p.1 ≠ .x10 ∧ p.1 ≠ .x11 := by
        revert hp; revert p; decide
      exact g₀ p.1 h9.1 h9.2.1 h9.2.2
  · rw [hm]; exact entryMem_frame _ _ _
  · rw [y2, gx .x2 (by decide) (by decide) (by decide), Ar.x2]
  · rw [y3, gx .x3 (by decide) (by decide) (by decide), Ar.x3]
  · rw [rd₂, rd₁, rd₀]
  · rw [wr₂, wr₁, wr₀]

end VG.Proof.AesCcm.AArch64
