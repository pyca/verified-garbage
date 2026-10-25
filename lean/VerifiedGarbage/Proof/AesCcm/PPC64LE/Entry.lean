module

public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Env
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Contract
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Gather.Fn
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesCcm.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# AES-CCM on PPC64LE: the arguments and the entry

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the facts the proofs use about the arguments (`Args`,
`args_of_seal`, `args_of_open`). `entry` loads `work`, the tag length and
`tag` from the stack, saves our caller's registers and the return address
at `W + 128` and keeps the arguments in registers and in `W` (`entry_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCcm.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.PPC64LE.Spill (saveCode saveMem Saved saveMem_saved save_ok)
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_ld wp_std wp_mflr)
open VG.Proof.ChaCha20Poly1305.PPC64LE.Gather (wp_addSp)
open VG.Proof.Gather.PPC64LE (covers_off in_off)

/-- The public values of the arguments of `s`. -/
def cxOf (s : State) : Cx where
  K := s.gpr .r3
  W := stackArg s 2
  D := s.gpr .r9
  A := s.gpr .r7
  R := (s.gpr .r4).toNat
  tl := (stackArg s 1).toNat
  n := (s.gpr .r10).toNat
  al := (s.gpr .r8).toNat
  nl := (s.gpr .r6).toNat
  T := stackArg s 0

/-- What `seal` and `open` are given: the public values `c`, and the nonce at
`N`. -/
structure Args (c : Cx) (N : Addr) (s : State) : Prop where
  lay : Lay c
  r3 : s.gpr .r3 = c.K
  r4 : s.gpr .r4 = BitVec.ofNat 64 c.R
  r5 : s.gpr .r5 = N
  r6 : s.gpr .r6 = BitVec.ofNat 64 c.nl
  r7 : s.gpr .r7 = c.A
  r8 : s.gpr .r8 = BitVec.ofNat 64 c.al
  r9 : s.gpr .r9 = c.D
  r10 : s.gpr .r10 = BitVec.ofNat 64 c.n
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

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem covers_of_mem {r : Region} {rs : List Region} (h : r ∈ rs) : Covers [r] rs := fun _ _ ⟨r', hr', hc⟩ => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact ⟨_, h, hc⟩

/-- `Args` from the layout, with the buffers covered as each function's
permissions say. -/
theorem args_of_lay {s : State} (h : oneLay s)
    (hk : Covers [⟨s.gpr .r3, 240⟩] (s.rd ++ s.wr)) (hN : Covers [⟨s.gpr .r5, (s.gpr .r6).toNat⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨s.gpr .r7, (s.gpr .r8).toNat⟩] (s.rd ++ s.wr)) (ha : Covers [args s] (s.rd ++ s.wr))
    (hT : Covers [⟨stackArg s 0, (stackArg s 1).toNat⟩] (s.rd ++ s.wr))
    (hD : Covers [⟨s.gpr .r9, (s.gpr .r10).toNat⟩] s.wr) (hW : Covers [⟨stackArg s 2, 2560⟩] s.wr) :
    Args (cxOf s) (s.gpr .r5) s := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, b1, b2, b3, b4, b5, b6, b7, hR, hv⟩ := h
  simp only [Spec.Ccm.valid, Spec.Ccm.tagLenOk, Spec.Ccm.nonceLenOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨ht4, ht16⟩, hte⟩, hn7, hn13⟩, hp⟩, -⟩ := hv
  rw [Nat.pow_mul] at hp
  exact {
    lay := ⟨b1, b6, b4, b3, d2, d1, d9, d6, d5, hR, BitVec.isLt _, BitVec.isLt _, ht4, ht16, hte, hn7, hn13, hp,
      b5, d8, d7⟩
    r3 := rfl
    r4 := (ofNat_toNat64 _).symm
    r5 := rfl
    r6 := (ofNat_toNat64 _).symm
    r7 := rfl
    r8 := (ofNat_toNat64 _).symm
    r9 := rfl
    r10 := (ofNat_toNat64 _).symm
    w := rfl
    tl := (ofNat_toNat64 _).symm
    t := rfl
    perm := ⟨hk, hW, hD, hA, hT⟩
    nonce := ⟨hN, BitVec.isLt _, b2, d4⟩
    nd := d3
    argsC := ha
    argsW := d11.symm
    argsD := d10.symm
    argsFit := b7 }

/-- `seal`'s arguments, and its tag, to write. -/
theorem args_of_seal {s : State} (h : sealPre s) :
    Args (cxOf s) (s.gpr .r5) s ∧ Covers [⟨stackArg s 0, (stackArg s 1).toNat⟩] s.wr := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .r3, 240⟩ : Region), ⟨s.gpr .r5, (s.gpr .r6).toNat⟩, ⟨s.gpr .r7, (s.gpr .r8).toNat⟩,
      args s], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .r9, (s.gpr .r10).toNat⟩ : Region), ⟨stackArg s 0, (stackArg s 1).toNat⟩,
      ⟨stackArg s 2, 2560⟩], Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp))
    (Covers.right (mwr _ (by simp))) (mwr _ (by simp)) (mwr _ (by simp)), mwr _ (by simp)⟩

/-- `open`'s arguments, with the received tag to read. -/
theorem args_of_open {s : State} (h : openPre s) : Args (cxOf s) (s.gpr .r5) s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .r3, 240⟩ : Region), ⟨s.gpr .r5, (s.gpr .r6).toNat⟩, ⟨s.gpr .r7, (s.gpr .r8).toNat⟩,
      ⟨stackArg s 0, (stackArg s 1).toNat⟩, args s], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .r9, (s.gpr .r10).toNat⟩ : Region), ⟨stackArg s 2, 2560⟩], Covers [r] s.wr :=
    fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp))
    (mwr _ (by simp)) (mwr _ (by simp))

/-! ## The entry -/

/-- What the entry writes: the saved registers, the return address and the
slots. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 120⟩

/-- Our caller's registers, with the return address in `r0`'s place. -/
abbrev saveG (s : State) : Reg → BitVec 64 := (s.write .r0 s.lr).gpr

/-- The slots of our caller's registers and the return address. -/
abbrev savedL : List (Reg × Nat) := (.r0, lrO) :: saved

/-- Our caller's registers the entry does not save, since nothing writes them. -/
abbrev otherRegs : List Reg := [.r2, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- What the entry leaves. -/
structure Entered (c : Cx) (N : Addr) (s s₁ : State) : Prop where
  env : Env c s₁
  slots : Slots c s₁.mem
  saved : Saved c.W (saveG s) savedL s₁.mem
  frame : Frame [entryR c.W] s.mem s₁.mem
  r5 : s₁.gpr .r5 = N
  r6 : s₁.gpr .r6 = BitVec.ofNat 64 c.nl
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp
  lr : s₁.lr = s.lr
  others : ∀ r ∈ otherRegs, s₁.gpr r = s.gpr r

theorem stackArgAddr_succ (s : State) (i : Nat) :
    stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) := by
  unfold stackArgAddr; rw [Offset.add_add]; congr 2; omega_arith

theorem saved_bound : ∀ p ∈ saved, 128 ≤ p.2 ∧ p.2 + 8 ≤ 128 + 80 := by decide

theorem entry_wp {c : Cx} {N : Addr} {s : State} (Ar : Args c N s) :
    WP isa (.block entry) s (Entered c N s) := by
  have L := Ar.lay
  have hww := L.ww
  have inA : ∀ {t : State} {i : Nat}, t.rd = s.rd → t.wr = s.wr → i < 3 →
      InRegions (t.rd ++ t.wr) (stackArgAddr s i) 8 := fun hrd hwr hi => by
    rw [hrd, hwr, stackArgAddr_succ]; exact in_off Ar.argsC (by omega_arith) (by decide)
  unfold entry
  change WP isa (.block ([.addSp .r12 0, .load .d .r11 .r12 112, .mflr .r0] ++ saveCode .r11 saved ++ _)) s _
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp (by decide) fun s₁ u₁ => ?_
  have r12₁ : s₁.gpr .r12 = s.sp := by rw [u₁.gpr, BitVec.add_zero]
  refine wp_ld (a := stackArgAddr s 2) (by decide) (by decide) (by rw [r12₁]; rfl) (inA u₁.rd u₁.wr (by decide))
    fun s₂ u₂ => wp_mflr fun s₃ u₃ => ?_
  have W₃ : s₃.gpr .r11 = c.W := by rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, ← Ar.w]; rfl
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  refine save_ok (b := .r11) (by decide) (by decide) (fun p hp => by
    rw [W₃, wr₃]; exact Ar.perm.wW (by have := saved_bound p hp; omega_arith)) ?_
  rw [W₃]
  generalize hmS : saveMem s₃.mem c.W s₃.gpr saved = mS
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have fS : Frame [⟨c.W + BitVec.ofNat 64 128, 80⟩] s.mem mS := by
    rw [← hmS, m₃]; exact Spill.saveMem_frame saved_bound (by omega_arith) _ _ _
  have svS : Saved c.W s₃.gpr saved mS := by rw [← hmS]; exact saveMem_saved (by decide) _ _ _
  refine wp_std (a := c.W + BitVec.ofNat 64 208) (by decide) (by decide) (by show s₃.gpr .r11 + _ = _; rw [W₃]; rfl)
    (by show InRegions s₃.wr _ 8; rw [wr₃]; exact Ar.perm.wW (by decide)) fun s₅ u₅ => ?_
  refine wp_mv fun s₆ u₆ => ?_
  have m₆ : s₆.mem = mS.writeW (c.W + BitVec.ofNat 64 208) (s.lr) := by
    rw [u₆.mem, u₅.mem]; show mS.writeW _ (s₃.gpr .r0) = _; rw [u₃.gpr, u₂.lr, u₁.lr]
  have c208 : (entryR c.W).Contains (c.W + BitVec.ofNat 64 208) (64 / 8) := by
    rw [show c.W + BitVec.ofNat 64 208 = c.W + BitVec.ofNat 64 128 + BitVec.ofNat 64 80 from
      (Offset.add_add c.W 128 80).symm]
    exact Offset.contains_base _ (by decide) (by decide)
  have f₆ : Frame [entryR c.W] s.mem s₆.mem := by
    rw [m₆]
    exact (fS.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩).writeW (List.mem_singleton_self _) _ c208
  have hAW : ∀ r ∈ [entryR c.W], (args s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Ar.argsW.sub_right (Offset.sub_base _ (by decide))
  have rdA : ∀ {i : Nat}, i < 3 → s₆.mem.readW (stackArgAddr s i) 64 = stackArg s i := fun hi => by
    rw [f₆.readW (r := args s) (by rw [stackArgAddr_succ]; exact Offset.contains_base _ (by omega_arith) (by omega_arith))
      hAW (by decide)]; rfl
  have rd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd]; exact rd₃
  have wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr]; exact wr₃
  have r12₆ : s₆.gpr .r12 = s.sp := by
    rw [u₆.other _ (by decide), u₅.gpr]; show s₃.gpr .r12 = _
    rw [u₃.other _ (by decide), u₂.other _ (by decide), r12₁]
  refine wp_ld (a := stackArgAddr s 1) (by decide) (by decide) (by rw [r12₆]; rfl) (inA rd₆ wr₆ (by decide))
    fun s₇ u₇ => ?_
  refine wp_ld (a := stackArgAddr s 0) (by decide) (by decide) (by rw [u₇.other _ (by decide), r12₆]; rfl)
    (by rw [u₇.rd, u₇.wr]; exact inA rd₆ wr₆ (by decide)) fun s₈ u₈ => ?_
  refine wp_mv fun s₉ u₉ => wp_mv fun s₁₀ u₁₀ => ?_
  have r14₁₀ : s₁₀.gpr .r14 = c.W := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
      u₅.gpr]; exact W₃
  have wr₁₀ : s₁₀.wr = s.wr := by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆]
  have inW : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions s₁₀.wr (c.W + BitVec.ofNat 64 d) 8 := fun hd => by
    rw [wr₁₀]; exact Ar.perm.wW hd
  have g₈ : ∀ r, r ≠ .r15 → r ≠ .r11 → r ≠ .r14 → r ≠ .r0 → r ≠ .r12 → s₈.gpr r = s.gpr r := by
    intro r h15 h11 h14 h0 h12
    rw [u₈.other _ h11, u₇.other _ h15, u₆.other _ h14, u₅.gpr]
    show s₃.gpr r = _
    rw [u₃.other _ h0, u₂.other _ h11, u₁.other _ h12]
  refine wp_std (a := c.W + BitVec.ofNat 64 216) (by decide) (by decide) (by rw [r14₁₀]; rfl) (inW (by decide))
    fun s₁₁ u₁₁ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 224) (by decide) (by decide) (by rw [u₁₁.gpr, r14₁₀]; rfl)
    (by rw [u₁₁.wr]; exact inW (by decide)) fun s₁₂ u₁₂ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 232) (by decide) (by decide) (by rw [u₁₂.gpr, u₁₁.gpr, r14₁₀]; rfl)
    (by rw [u₁₂.wr, u₁₁.wr]; exact inW (by decide)) fun s₁₃ u₁₃ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 240) (by decide) (by decide)
    (by rw [u₁₃.gpr, u₁₂.gpr, u₁₁.gpr, r14₁₀]; rfl)
    (by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr]; exact inW (by decide)) fun s₁₄ u₁₄ => ?_
  refine wp_mv fun s₁₅ u₁₅ => wp_mv fun s₁₆ u₁₆ => WP.block_nil ?_
  -- The registers.
  have g₁₀ : ∀ r, r ≠ .r15 → r ≠ .r11 → r ≠ .r14 → r ≠ .r0 → r ≠ .r12 → r ≠ .r16 → r ≠ .r17 →
      s₁₀.gpr r = s.gpr r := fun r h15 h11 h14 h0 h12 h16 h17 => by
    rw [u₁₀.other _ h17, u₉.other _ h16, g₈ r h15 h11 h14 h0 h12]
  have g₁₄ : s₁₄.gpr = s₁₀.gpr := by rw [u₁₄.gpr, u₁₃.gpr, u₁₂.gpr, u₁₁.gpr]
  have r11₁₀ : s₁₀.gpr .r11 = c.T := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.mem, rdA (by decide), Ar.t]
  have r15₁₀ : s₁₀.gpr .r15 = BitVec.ofNat 64 c.tl := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, rdA (by decide), Ar.tl]
  have r16₁₀ : s₁₀.gpr .r16 = c.K := by
    rw [u₁₀.other _ (by decide), u₉.gpr, g₈ .r3 (by decide) (by decide) (by decide) (by decide) (by decide), Ar.r3]
  have r17₁₀ : s₁₀.gpr .r17 = BitVec.ofNat 64 c.R := by
    rw [u₁₀.gpr, u₉.other _ (by decide), g₈ .r4 (by decide) (by decide) (by decide) (by decide) (by decide), Ar.r4]
  have gF : ∀ r, r ≠ .r22 → r ≠ .r23 → s₁₆.gpr r = s₁₀.gpr r := fun r h22 h23 => by
    rw [u₁₆.other _ h23, u₁₅.other _ h22, g₁₄]
  have r22F : s₁₆.gpr .r22 = c.D := by
    rw [u₁₆.other _ (by decide), u₁₅.gpr, g₁₄, g₁₀ .r9 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), Ar.r9]
  have r23F : s₁₆.gpr .r23 = BitVec.ofNat 64 c.n := by
    rw [u₁₆.gpr, u₁₅.other _ (by decide), g₁₄, g₁₀ .r10 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), Ar.r10]
  -- The memory.
  have mF : s₁₆.mem = (((s₆.mem.writeW (c.W + BitVec.ofNat 64 216) c.A).writeW (c.W + BitVec.ofNat 64 224)
      (BitVec.ofNat 64 c.al)).writeW (c.W + BitVec.ofNat 64 232) (BitVec.ofNat 64 c.nl)).writeW
      (c.W + BitVec.ofNat 64 240) c.T := by
    rw [u₁₆.mem, u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₃.gpr, u₁₂.gpr, u₁₁.gpr, r11₁₀, g₁₀ .r7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₁₀ .r8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₁₀ .r6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), Ar.r7, Ar.r8,
      Ar.r6, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]
  have cE : ∀ d, 128 ≤ d → d + 8 ≤ 248 → (entryR c.W).Contains (c.W + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ =>
    Offset.contains c.W h₁ (by omega_arith) (by omega_arith)
  have fF : Frame [entryR c.W] s.mem s₁₆.mem := by
    rw [mF]
    exact (((f₆.writeW (List.mem_singleton_self _) _ (cE 216 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cE 224 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cE 232 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cE 240 (by decide) (by decide))
  have sep : ∀ {a b : Nat}, a + 8 ≤ b ∨ b + 8 ≤ a → a + 8 ≤ 2560 → b + 8 ≤ 2560 →
      Mem.Sep (c.W + BitVec.ofNat 64 a) (64 / 8) (c.W + BitVec.ofNat 64 b) (64 / 8) := fun h ha hb =>
    (L.w_w (n := 8) (k := 8) h ha hb).sep (Region.contains_self _ _) (Region.contains_self _ _)
  refine ⟨⟨by rw [gF _ (by decide) (by decide), r14₁₀], by rw [gF _ (by decide) (by decide), r15₁₀],
      by rw [gF _ (by decide) (by decide), r16₁₀], by rw [gF _ (by decide) (by decide), r17₁₀], r22F, r23F,
      Ar.perm.of_eq ?_ ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, fF, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆]
  · rw [u₁₆.wr, u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, wr₁₀]
  · rw [mF, Mem.readW_writeW_sep (sep (a := 216) (b := 240) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep (a := 216) (b := 232) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep (a := 216) (b := 224) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [mF, Mem.readW_writeW_sep (sep (a := 224) (b := 240) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep (a := 224) (b := 232) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [mF, Mem.readW_writeW_sep (sep (a := 232) (b := 240) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [mF, Mem.readW_writeW_self64]
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · show s₁₆.mem.readW (c.W + BitVec.ofNat 64 208) 64 = _
      rw [mF, Mem.readW_writeW_sep (sep (a := 208) (b := 240) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (sep (a := 208) (b := 232) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (sep (a := 208) (b := 224) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (sep (a := 208) (b := 216) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), m₆,
        Mem.readW_writeW_self64]
      simp [saveG, State.write]
    · have fT : Frame [⟨c.W + BitVec.ofNat 64 208, 40⟩] mS s₁₆.mem := by
        rw [mF, m₆]
        have c' : ∀ d, 208 ≤ d → d + 8 ≤ 248 →
            (⟨c.W + BitVec.ofNat 64 208, 40⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) (64 / 8) :=
          fun d h₁ h₂ => Offset.contains c.W h₁ (by omega_arith) (by omega_arith)
        exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c' 208 (by decide) (by decide))).writeW
          (List.mem_singleton_self _) _ (c' 216 (by decide) (by decide))).writeW
          (List.mem_singleton_self _) _ (c' 224 (by decide) (by decide))).writeW
          (List.mem_singleton_self _) _ (c' 232 (by decide) (by decide)) |>.writeW
          (List.mem_singleton_self _) _ (c' 240 (by decide) (by decide))
      have hv := (svS.frame fT fun q hq r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := saved_bound q hq
        exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)) p hp
      rw [hv]
      have h1 : p.1 ≠ .r0 ∧ p.1 ≠ .r11 ∧ p.1 ≠ .r12 :=
        (show ∀ q ∈ saved, q.1 ≠ .r0 ∧ q.1 ≠ .r11 ∧ q.1 ≠ .r12 by decide) p hp
      rw [u₃.other _ h1.1, u₂.other _ h1.2.1, u₁.other _ h1.2.2]
      simp [saveG, State.write, h1.1]
  · rw [gF _ (by decide) (by decide), g₁₀ .r5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), Ar.r5]
  · rw [gF _ (by decide) (by decide), g₁₀ .r6 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), Ar.r6]
  · rw [u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆]
  · rw [u₁₆.wr, u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, wr₁₀]
  · rw [u₁₆.sp, u₁₅.sp, u₁₄.sp, u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp]
    show s₃.sp = _
    rw [u₃.sp, u₂.sp, u₁.sp]
  · rw [u₁₆.lr, u₁₅.lr, u₁₄.lr, u₁₃.lr, u₁₂.lr, u₁₁.lr, u₁₀.lr, u₉.lr, u₈.lr, u₇.lr, u₆.lr, u₅.lr]
    show s₃.lr = _
    rw [u₃.lr, u₂.lr, u₁.lr]
  · intro r hr
    simp only [otherRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [gF _ (by decide) (by decide), g₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]

end VG.Proof.AesCcm.PPC64LE
