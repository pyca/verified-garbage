module

public import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesCcm.RISCV64
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# AES-CCM on RISC-V: the arguments and the entry

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesCcm/PPC64LE/Entry.lean`): the preconditions `sealPre` and
`openPre` give the facts the proofs use about the arguments (`Args`,
`args_of_seal`, `args_of_open`). `entry` loads `work` from the stack, saves
our caller's registers and the return address at `W + 128`, then loads the
tag length and `tag` and keeps the arguments in registers and in `W`
(`entry_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesCcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.RISCV64.Spill (saveCode saveMem Saved saveMem_saved save_ok)

/-- The public values of the arguments of `s`. -/
def cxOf (s : State) : Cx where
  K := s.gpr .a0
  W := stackArg s 2
  D := s.gpr .a6
  A := s.gpr .a4
  R := (s.gpr .a1).toNat
  tl := (stackArg s 1).toNat
  n := (s.gpr .a7).toNat
  al := (s.gpr .a5).toNat
  nl := (s.gpr .a3).toNat
  T := stackArg s 0

/-- What `seal` and `open` are given: the public values `c`, and the nonce at
`N`. -/
structure Args (c : Cx) (N : Addr) (s : State) : Prop where
  lay : Lay c
  a0 : s.gpr .a0 = c.K
  a1 : s.gpr .a1 = BitVec.ofNat 64 c.R
  a2 : s.gpr .a2 = N
  a3 : s.gpr .a3 = BitVec.ofNat 64 c.nl
  a4 : s.gpr .a4 = c.A
  a5 : s.gpr .a5 = BitVec.ofNat 64 c.al
  a6 : s.gpr .a6 = c.D
  a7 : s.gpr .a7 = BitVec.ofNat 64 c.n
  w : stackArg s 2 = c.W
  tl : stackArg s 1 = BitVec.ofNat 64 c.tl
  t : stackArg s 0 = c.T
  perm : Perm c s
  nonce : Buf c s N c.nl
  nd : (⟨N, c.nl⟩ : Region).Disjoint ⟨c.D, c.n⟩
  argsC : Covers [args s] (s.rd ++ s.wr)
  argsW : (args s).Disjoint ⟨c.W, 2560⟩
  argsD : (args s).Disjoint ⟨c.D, c.n⟩
  argsFit : (stackArgAddr s 0).toNat + 24 ≤ 2 ^ 64
  spal : s.sp.toNat % 8 = 0

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem covers_of_mem {r : Region} {rs : List Region} (h : r ∈ rs) : Covers [r] rs := fun _ _ ⟨r', hr', hc⟩ => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact ⟨_, h, hc⟩

/-- `Args` from the layout, with the buffers covered as each function's
permissions say. -/
theorem args_of_lay {s : State} (h : oneLay s)
    (hk : Covers [⟨s.gpr .a0, 240⟩] (s.rd ++ s.wr)) (hN : Covers [⟨s.gpr .a2, (s.gpr .a3).toNat⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨s.gpr .a4, (s.gpr .a5).toNat⟩] (s.rd ++ s.wr)) (ha : Covers [args s] (s.rd ++ s.wr))
    (hT : Covers [⟨stackArg s 0, (stackArg s 1).toNat⟩] (s.rd ++ s.wr))
    (hD : Covers [⟨s.gpr .a6, (s.gpr .a7).toNat⟩] s.wr) (hW : Covers [⟨stackArg s 2, 2560⟩] s.wr) :
    Args (cxOf s) (s.gpr .a2) s := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, b1, b2, b3, b4, b5, b6, b7, hsp, hwal, hR, hv⟩ := h
  simp only [Spec.Ccm.valid, Spec.Ccm.tagLenOk, Spec.Ccm.nonceLenOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨ht4, ht16⟩, hte⟩, hn7, hn13⟩, hp⟩, -⟩ := hv
  rw [Nat.pow_mul] at hp
  exact {
    lay := ⟨b1, b6, hwal, b4, b3, d2, d1, d9, d6, d5, hR, BitVec.isLt _, BitVec.isLt _, ht4, ht16, hte, hn7, hn13,
      hp, b5, d8, d7⟩
    a0 := rfl
    a1 := (ofNat_toNat64 _).symm
    a2 := rfl
    a3 := (ofNat_toNat64 _).symm
    a4 := rfl
    a5 := (ofNat_toNat64 _).symm
    a6 := rfl
    a7 := (ofNat_toNat64 _).symm
    w := rfl
    tl := (ofNat_toNat64 _).symm
    t := rfl
    perm := ⟨hk, hW, hD, hA, hT⟩
    nonce := ⟨hN, BitVec.isLt _, b2, d4⟩
    nd := d3
    argsC := ha
    argsW := d11.symm
    argsD := d10.symm
    argsFit := b7
    spal := by omega }

/-- `seal`'s arguments, and its tag, to write. -/
theorem args_of_seal {s : State} (h : sealPre s) :
    Args (cxOf s) (s.gpr .a2) s ∧ Covers [⟨stackArg s 0, (stackArg s 1).toNat⟩] s.wr := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .a0, 240⟩ : Region), ⟨s.gpr .a2, (s.gpr .a3).toNat⟩, ⟨s.gpr .a4, (s.gpr .a5).toNat⟩,
      args s], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .a6, (s.gpr .a7).toNat⟩ : Region), ⟨stackArg s 0, (stackArg s 1).toNat⟩,
      ⟨stackArg s 2, 2560⟩], Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp))
    (Covers.right (mwr _ (by simp))) (mwr _ (by simp)) (mwr _ (by simp)), mwr _ (by simp)⟩

/-- `open`'s arguments, with the received tag to read. -/
theorem args_of_open {s : State} (h : openPre s) : Args (cxOf s) (s.gpr .a2) s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .a0, 240⟩ : Region), ⟨s.gpr .a2, (s.gpr .a3).toNat⟩, ⟨s.gpr .a4, (s.gpr .a5).toNat⟩,
      ⟨stackArg s 0, (stackArg s 1).toNat⟩, args s], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .a6, (s.gpr .a7).toNat⟩ : Region), ⟨stackArg s 2, 2560⟩], Covers [r] s.wr :=
    fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp))
    (mwr _ (by simp)) (mwr _ (by simp))

/-! ## The entry -/

/-- What the entry writes: the saved registers, the return address and the
slots. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 120⟩

/-- The slots of our caller's registers and of the return address, in the
order the entry saves them. -/
abbrev savedL : List (Reg × Nat) := saved ++ [(.ra, raO)]

/-- Our caller's registers the entry does not save, since nothing writes them. -/
abbrev otherRegs : List Reg := [.s0, .s11]

/-- What the entry leaves. -/
structure Entered (c : Cx) (N : Addr) (s s₁ : State) : Prop where
  env : Env c s₁
  slots : Slots c s₁.mem
  saved : Saved c.W s.gpr savedL s₁.mem
  frame : Frame [entryR c.W] s.mem s₁.mem
  a2 : s₁.gpr .a2 = N
  a3 : s₁.gpr .a3 = BitVec.ofNat 64 c.nl
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp
  others : ∀ r ∈ otherRegs, s₁.gpr r = s.gpr r

theorem stackArgAddr_succ (s : State) (i : Nat) :
    stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) := by
  unfold stackArgAddr; rw [Offset.add_add]; congr 2; omega

theorem savedL_bound : ∀ p ∈ savedL, 128 ≤ p.2 ∧ p.2 + 8 ≤ 128 + 120 := by decide

theorem savedL_fits : Spill.Fits savedL := by decide

theorem savedL_off : ∀ p ∈ savedL, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

theorem entry_code : entry = ([.addSp .t0 0, .load .d .t1 .t0 16] : List Instr) ++ saveCode .t1 savedL ++
    ([Impl.AesCbc.RISCV64.mov .s1 .t1, .load .d .s2 .t0 8, .load .d .t1 .t0 0,
      Impl.AesCbc.RISCV64.mov .s3 .a0, Impl.AesCbc.RISCV64.mov .s4 .a1, .store .d .a4 .s1 aadO,
      .store .d .a5 .s1 alenO, .store .d .a3 .s1 nlenO, .store .d .t1 .s1 tagO,
      Impl.AesCbc.RISCV64.mov .s9 .a6, Impl.AesCbc.RISCV64.mov .s10 .a7] : List Instr) := rfl

theorem entry_wp {c : Cx} {N : Addr} {s : State} (Ar : Args c N s) :
    WP isa (.block entry) s (Entered c N s) := by
  have L := Ar.lay
  have hww := L.ww
  have inA : ∀ {t : State} {i : Nat}, t.rd = s.rd → t.wr = s.wr → i < 3 →
      InRegions (t.rd ++ t.wr) (stackArgAddr s i) 8 := fun hrd hwr hi => by
    rw [hrd, hwr, stackArgAddr_succ]; exact in_off Ar.argsC (by omega) (by decide)
  have alA : ∀ i, (stackArgAddr s i).toNat % 8 = 0 := fun i => Spill.al8 Ar.spal (by omega)
  rw [entry_code]
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp (by decide) fun s₁ u₁ => ?_
  have t0₁ : s₁.gpr .t0 = s.sp := by rw [u₁.gpr, BitVec.add_zero]
  refine wp_ld (a := stackArgAddr s 2) (by decide) (by rw [t0₁]; rfl) (alA 2) (inA u₁.rd u₁.wr (by decide))
    fun s₂ u₂ => ?_
  have W₂ : s₂.gpr .t1 = c.W := by rw [u₂.gpr, u₁.mem, ← Ar.w]; rfl
  have rd₂ : s₂.rd = s.rd := by rw [u₂.rd, u₁.rd]
  have wr₂ : s₂.wr = s.wr := by rw [u₂.wr, u₁.wr]
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine save_ok (b := .t1) (by rw [W₂]; exact L.wal) savedL_off (fun p hp => by
    rw [W₂, wr₂]; exact Ar.perm.wW (by have := savedL_bound p hp; omega)) ?_
  rw [W₂]
  generalize hs₃ : ({ s₂ with mem := saveMem s₂.mem c.W s₂.gpr savedL } : State) = s₃
  have g₃ : s₃.gpr = s₂.gpr := by rw [← hs₃]
  have rd₃ : s₃.rd = s.rd := by rw [← hs₃]; exact rd₂
  have wr₃ : s₃.wr = s.wr := by rw [← hs₃]; exact wr₂
  have sp₃ : s₃.sp = s.sp := by rw [← hs₃]; show s₂.sp = _; rw [u₂.sp, u₁.sp]
  have mS : s₃.mem = saveMem s.mem c.W s₂.gpr savedL := by rw [← hs₃, m₂]
  have fS : Frame [entryR c.W] s.mem s₃.mem := by
    rw [mS]; exact Spill.saveMem_frame savedL_bound (by omega) _ _ _
  have svS : Saved c.W s₂.gpr savedL s₃.mem := by rw [mS]; exact saveMem_saved savedL_fits _ _ _
  have hAW : ∀ r ∈ [entryR c.W], (args s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Ar.argsW.sub_right (Offset.sub_base _ (by decide))
  refine wp_mv fun s₄ u₄ => ?_
  refine wp_ld (a := stackArgAddr s 1) (by decide)
    (by rw [u₄.other _ (by decide), g₃, u₂.other _ (by decide), t0₁]; rfl) (alA 1)
    (by rw [u₄.rd, u₄.wr]; exact inA rd₃ wr₃ (by decide)) fun s₅ u₅ => ?_
  refine wp_ld (a := stackArgAddr s 0) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃, u₂.other _ (by decide), t0₁]; rfl) (alA 0)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact inA rd₃ wr₃ (by decide)) fun s₆ u₆ => ?_
  refine wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => ?_
  have m₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have rdA : ∀ {i : Nat}, i < 3 → s₃.mem.readW (stackArgAddr s i) 64 = stackArg s i := fun hi => by
    rw [fS.readW (r := args s) (by rw [stackArgAddr_succ]; exact Offset.contains_base _ (by omega) (by omega))
      hAW (by decide)]; rfl
  have g₈ : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s₈.gpr r = s.gpr r := by
    intro r h0 h1 h11 h2 h3 h4
    rw [u₈.other _ h4, u₇.other _ h3, u₆.other _ h1, u₅.other _ h2, u₄.other _ h11, g₃, u₂.other _ h1,
      u₁.other _ h0]
  have s1₈ : s₈.gpr .s1 = c.W := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      g₃, W₂]
  have t1₈ : s₈.gpr .t1 = c.T := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, rdA (by decide), Ar.t]
  have s2₈ : s₈.gpr .s2 = BitVec.ofNat 64 c.tl := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, rdA (by decide),
      Ar.tl]
  have s3₈ : s₈.gpr .s3 = c.K := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      g₃, u₂.other _ (by decide), u₁.other _ (by decide), Ar.a0]
  have s4₈ : s₈.gpr .s4 = BitVec.ofNat 64 c.R := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      g₃, u₂.other _ (by decide), u₁.other _ (by decide), Ar.a1]
  have wr₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃]
  have inW : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions s₈.wr (c.W + BitVec.ofNat 64 d) 8 := fun hd => by
    rw [wr₈]; exact Ar.perm.wW hd
  refine wp_sd (a := c.W + BitVec.ofNat 64 216) (by decide) (by rw [s1₈]; rfl) (L.alW (by decide) (by decide))
    (inW (by decide)) fun s₉ u₉ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 224) (by decide) (by rw [u₉.gpr, s1₈]; rfl)
    (L.alW (by decide) (by decide)) (by rw [u₉.wr]; exact inW (by decide)) fun s₁₀ u₁₀ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 232) (by decide) (by rw [u₁₀.gpr, u₉.gpr, s1₈]; rfl)
    (L.alW (by decide) (by decide)) (by rw [u₁₀.wr, u₉.wr]; exact inW (by decide)) fun s₁₁ u₁₁ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 240) (by decide) (by rw [u₁₁.gpr, u₁₀.gpr, u₉.gpr, s1₈]; rfl)
    (L.alW (by decide) (by decide)) (by rw [u₁₁.wr, u₁₀.wr, u₉.wr]; exact inW (by decide)) fun s₁₂ u₁₂ => ?_
  refine wp_mv fun s₁₃ u₁₃ => wp_mv fun s₁₄ u₁₄ => WP.block_nil ?_
  have g₁₂ : s₁₂.gpr = s₈.gpr := by rw [u₁₂.gpr, u₁₁.gpr, u₁₀.gpr, u₉.gpr]
  have gF : ∀ r, r ≠ .s9 → r ≠ .s10 → s₁₄.gpr r = s₈.gpr r := fun r h9 h10 => by
    rw [u₁₄.other _ h10, u₁₃.other _ h9, g₁₂]
  -- The memory.
  have mF : s₁₄.mem = (((s₃.mem.writeW (c.W + BitVec.ofNat 64 216) c.A).writeW (c.W + BitVec.ofNat 64 224)
      (BitVec.ofNat 64 c.al)).writeW (c.W + BitVec.ofNat 64 232) (BitVec.ofNat 64 c.nl)).writeW
      (c.W + BitVec.ofNat 64 240) c.T := by
    rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₁₁.gpr, u₁₀.gpr, u₉.gpr, t1₈,
      g₈ .a4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₈ .a5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₈ .a3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), Ar.a4, Ar.a5, Ar.a3, m₈]
  have cE : ∀ d, 128 ≤ d → d + 8 ≤ 248 → (entryR c.W).Contains (c.W + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ =>
    Offset.contains c.W h₁ (by omega) (by omega)
  have fF : Frame [entryR c.W] s.mem s₁₄.mem := by
    rw [mF]
    exact (((fS.writeW (List.mem_singleton_self _) _ (cE 216 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cE 224 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cE 232 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cE 240 (by decide) (by decide))
  have sep : ∀ {a b : Nat}, a + 8 ≤ b ∨ b + 8 ≤ a → a + 8 ≤ 2560 → b + 8 ≤ 2560 →
      Mem.Sep (c.W + BitVec.ofNat 64 a) (64 / 8) (c.W + BitVec.ofNat 64 b) (64 / 8) := fun h ha hb =>
    (L.w_w (n := 8) (k := 8) h ha hb).sep (Region.contains_self _ _) (Region.contains_self _ _)
  have rdF : s₁₄.rd = s.rd := by
    rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃]
  have wrF : s₁₄.wr = s.wr := by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, wr₈]
  refine ⟨⟨by rw [gF _ (by decide) (by decide), s1₈], by rw [gF _ (by decide) (by decide), s2₈],
      by rw [gF _ (by decide) (by decide), s3₈], by rw [gF _ (by decide) (by decide), s4₈], ?_, ?_,
      Ar.perm.of_eq rdF wrF⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, fF, ?_, ?_, rdF, wrF, ?_, ?_⟩
  · rw [u₁₄.other _ (by decide), u₁₃.gpr, g₁₂, g₈ .a6 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), Ar.a6]
  · rw [u₁₄.gpr, u₁₃.other _ (by decide), g₁₂, g₈ .a7 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), Ar.a7]
  · rw [mF, Mem.readW_writeW_sep (sep (a := 216) (b := 240) (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep (a := 216) (b := 232) (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep (a := 216) (b := 224) (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [mF, Mem.readW_writeW_sep (sep (a := 224) (b := 240) (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep (a := 224) (b := 232) (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [mF, Mem.readW_writeW_sep (sep (a := 232) (b := 240) (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [mF, Mem.readW_writeW_self64]
  · -- The slots, which the later stores miss.
    have fT : Frame [⟨c.W + BitVec.ofNat 64 216, 32⟩] s₃.mem s₁₄.mem := by
      rw [mF]
      have c' : ∀ d, 216 ≤ d → d + 8 ≤ 248 →
          (⟨c.W + BitVec.ofNat 64 216, 32⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) (64 / 8) :=
        fun d h₁ h₂ => Offset.contains c.W h₁ (by omega) (by omega)
      exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c' 216 (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (c' 224 (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (c' 232 (by decide) (by decide)) |>.writeW
        (List.mem_singleton_self _) _ (c' 240 (by decide) (by decide))
    have sv := svS.frame fT fun q hq r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have := savedL_bound q hq
      have h216 : q.2 + 8 ≤ 216 := (show ∀ p ∈ savedL, p.2 + 8 ≤ 216 by decide) q hq
      exact L.w_w (.inl h216) (by omega) (by decide)
    intro p hp
    rw [sv p hp]
    have h1 : p.1 ≠ .t0 ∧ p.1 ≠ .t1 := (show ∀ q ∈ savedL, q.1 ≠ .t0 ∧ q.1 ≠ .t1 by decide) p hp
    rw [u₂.other _ h1.2, u₁.other _ h1.1]
  · rw [gF _ (by decide) (by decide), g₈ .a2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), Ar.a2]
  · rw [gF _ (by decide) (by decide), g₈ .a3 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), Ar.a3]
  · rw [u₁₄.sp, u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, sp₃]
  · intro r hr
    simp only [otherRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      rw [gF _ (by decide) (by decide), g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]

end VG.Proof.AesCcm.RISCV64
