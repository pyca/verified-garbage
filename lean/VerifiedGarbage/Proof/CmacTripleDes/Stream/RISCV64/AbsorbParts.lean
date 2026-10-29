module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Streaming TDEA-CMAC on RISC-V: `absorb`, before the paths

The precondition by name (`APre`), the registers saved (`absSave_wp`), and
the number `h` of bytes held back with the room `8 - h` after them and
whether the data fit there (`flag_wp`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacTripleDes.Stream.RISCV64
open VG.Proof.CmacTripleDes.Stream (held)

/-- The precondition, by name: the state `St`, `count = n`, the `L` bytes of
data at `D` and the scratch buffer `S`. -/
structure APre (s₀ : State) (St D S : Addr) (n L : Nat) : Prop where
  a0 : s₀.gpr .a0 = St
  a1 : s₀.gpr .a1 = BitVec.ofNat 64 n
  a2 : s₀.gpr .a2 = D
  a3 : s₀.gpr .a3 = BitVec.ofNat 64 L
  a4 : s₀.gpr .a4 = S
  hn : n < 2 ^ 64
  hL : L < 2 ^ 64
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 416⟩, ⟨S, 688⟩]
  st_d : (⟨St, 416⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 416⟩ : Region).Disjoint ⟨S, 688⟩
  d_s : (⟨D, L⟩ : Region).Disjoint ⟨S, 688⟩
  stk_st : (⟨s₀.sp - 944, 944⟩ : Region).Disjoint ⟨St, 416⟩
  stk_d : (⟨s₀.sp - 944, 944⟩ : Region).Disjoint ⟨D, L⟩
  stk_s : (⟨s₀.sp - 944, 944⟩ : Region).Disjoint ⟨S, 688⟩
  wSt : St.toNat + 416 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : S.toNat + 688 ≤ 2 ^ 64
  al : s₀.sp.toNat % 16 = 0
  sp : 944 ≤ s₀.sp.toNat

theorem APre.of {s₀ : State} (h : absorbRISCV64.pre s₀) :
    APre s₀ (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a4) (s₀.gpr .a1).toNat (s₀.gpr .a3).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := h
  ⟨rfl, ofNat_toNat_eq rfl, rfl, ofNat_toNat_eq rfl, rfl, (s₀.gpr .a1).isLt, (s₀.gpr .a3).isLt,
    a, b, c, d, e, f, g, h, i, j, k, l, m⟩

/-- What the code saves: the registers, with `t0` the slots' base. -/
abbrev absG (s₀ : State) (S : Addr) : Reg → BitVec 64 := (s₀.write .t0 (sv S)).gpr

theorem abs_bound : ∀ p ∈ absSaved, p.2 + 8 ≤ 48 := by decide

/-- What `absSave` leaves. -/
structure AMid (s₀ : State) (St D S : Addr) (n L : Nat) (s : State) : Prop where
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  s3 : s.gpr .s3 = D
  a1 : s.gpr .a1 = BitVec.ofNat 64 n
  a3 : s.gpr .a3 = BitVec.ofNat 64 L
  other : ∀ r ∈ preserved, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s.gpr r = s₀.gpr r
  mem : s.mem = Spill.saveMem s₀.mem (sv S) (absG s₀ S) absSaved
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem absSave_wp {s₀ : State} {St D S : Addr} {n L : Nat} (hp : APre s₀ St D S n L) :
    WP isa (.block absSave) s₀ (AMid s₀ St D S n L) := by
  rw [absSave, saveRegs, List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr_ok .a4) fun s₁ e => ?_
  subst e
  rw [hp.a4, show absSaved.map (fun (r, d) => Instr.store .d r .t0 d) = Spill.saveCode .t0 absSaved from rfl]
  have t₀ : (s₀.write .t0 (sv S)).gpr .t0 = sv S := RegUpd.gpr_write_self _ _ _
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (sv S)).gpr r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := .t0) (l := absSaved) (by rw [t₀]; exact Align.align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · have := abs_bound p hp'
    rw [t₀]
    show InRegions s₀.wr _ 8
    rw [hp.wr]
    exact ⟨⟨S, 688⟩, by simp, sv_contains S (by omega) (by decide)⟩
  generalize ht : ({ (s₀.write .t0 (sv S)) with
    mem := Spill.saveMem (s₀.write .t0 (sv S)).mem ((s₀.write .t0 (sv S)).gpr .t0)
      (s₀.write .t0 (sv S)).gpr absSaved } : State) = t
  have gt (r : Reg) (hr : r ≠ .t0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact g₀ r hr
  have memt : t.mem = Spill.saveMem s₀.mem (sv S) (absG s₀ S) absSaved := by
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [t₀, RegUpd.mem_write]
  have rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  have wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  have spt : t.sp = s₀.sp := by rw [← ht]; rfl
  unfold mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr h1 h2 h3 => ?_, ?_, by rw [u₃.rd, u₂.rd, u₁.rd, rdt],
    by rw [u₃.wr, u₂.wr, u₁.wr, wrt], by rw [u₃.sp, u₂.sp, u₁.sp, spt]⟩
  · simp (disch := decide) only [u₃.other, u₂.other, u₁.gpr, gt, hp.a0]
  · simp (disch := decide) only [u₃.other, u₂.gpr, u₁.other, gt, hp.a4]
  · simp (disch := decide) only [u₃.gpr, u₂.other, u₁.other, gt, hp.a2]
  · simp (disch := decide) only [u₃.other, u₂.other, u₁.other, gt, hp.a1]
  · simp (disch := decide) only [u₃.other, u₂.other, u₁.other, gt, hp.a3]
  · obtain ⟨h0, -⟩ := preserved_ne r hr
    rw [u₃.other _ h3, u₂.other _ h2, u₁.other _ h1, gt _ h0]
  · rw [u₃.mem, u₂.mem, u₁.mem, memt]

/-- What `heldCode` and `absFlag` leave: the number `h` of bytes held back,
the room after them, and whether the data do not fit there. -/
structure AFl (St D S : Addr) (n L : Nat) (u s : State) : Prop where
  t0 : s.gpr .t0 = BitVec.ofNat 64 (held n)
  t1 : s.gpr .t1 = BitVec.ofNat 64 (8 - held n)
  t2 : s.gpr .t2 = if 8 - held n < L then 1 else 0
  keep : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → s.gpr r = u.gpr r
  mem : s.mem = u.mem
  rd : s.rd = u.rd
  wr : s.wr = u.wr
  sp : s.sp = u.sp

theorem absFlag_wp {u t : State} {n L : Nat} {St D S : Addr} (hL : L < 2 ^ 64)
    (h3 : u.gpr .a3 = BitVec.ofNat 64 L) (t0 : t.gpr .t0 = BitVec.ofNat 64 (held n))
    (g : ∀ r, r ≠ .t0 → t.gpr r = u.gpr r) (m : t.mem = u.mem) (rd : t.rd = u.rd) (wr : t.wr = u.wr)
    (sp : t.sp = u.sp) : WP isa (.block absFlag) t (AFl St D S n L u) := by
  have hl := Proof.CmacTripleDes.Stream.held_le n
  unfold absFlag
  refine wp_li (imm := 8) (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_sltu fun s₃ u₃ => WP.block_nil ?_
  have t1₂ : s₂.gpr .t1 = BitVec.ofNat 64 (8 - held n) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), t0]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  refine ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), t0],
    by rw [u₃.other _ (by decide), t1₂], ?_, fun r a b c => ?_, by rw [u₃.mem, u₂.mem, u₁.mem, m],
    by rw [u₃.rd, u₂.rd, u₁.rd, rd], by rw [u₃.wr, u₂.wr, u₁.wr, wr], by rw [u₃.sp, u₂.sp, u₁.sp, sp]⟩
  · rw [u₃.gpr, t1₂, u₂.other _ (by decide), u₁.other _ (by decide), g _ (by decide), h3]
    congr 1
    simp only [BitVec.lt_def, toNat_ofNat (show 8 - held n < 2 ^ 64 by omega), toNat_ofNat hL]
  · rw [u₃.other _ c, u₂.other _ b, u₁.other _ b, g _ a]

theorem flag_wp {u : State} {n L : Nat} {St D S : Addr} (hn : n < 2 ^ 64) (hL : L < 2 ^ 64)
    (h1 : u.gpr .a1 = BitVec.ofNat 64 n) (h3 : u.gpr .a3 = BitVec.ofNat 64 L) {rest : Prog isa}
    {Q : State → Prop} (k : ∀ s, AFl St D S n L u s → WP isa rest s Q) :
    WP isa (.seq heldCode (.seq (.block absFlag) rest)) u Q :=
  WP.seq (WP.mono (heldCode_wp hn h1) fun _ ⟨t0, g, m, rd, wr, sp⟩ =>
    WP.seq (WP.mono (absFlag_wp hL h3 t0 g m rd wr sp) k))

end VG.Proof.CmacTripleDes.Stream.RISCV64
