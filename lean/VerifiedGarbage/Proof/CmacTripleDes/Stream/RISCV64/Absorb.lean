module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Finish
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.TripleDes.Schedule
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Calls

/-! ### `CmacTripleDes.Stream.RISCV64.AbsorbChain`, which only this module used -/

section

/-! ### `CmacTripleDes.Stream.RISCV64.AbsorbParts`, which only this module used -/

section

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
    exact ⟨⟨S, 688⟩, by simp, sv_contains S (by omega_using [this]) (by decide)⟩
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
    omega_using [hl]
  refine ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), t0],
    by rw [u₃.other _ (by decide), t1₂], ?_, fun r a b c => ?_, by rw [u₃.mem, u₂.mem, u₁.mem, m],
    by rw [u₃.rd, u₂.rd, u₁.rd, rd], by rw [u₃.wr, u₂.wr, u₁.wr, wr], by rw [u₃.sp, u₂.sp, u₁.sp, sp]⟩
  · rw [u₃.gpr, t1₂, u₂.other _ (by decide), u₁.other _ (by decide), g _ (by decide), h3]
    congr 1
    simp only [BitVec.lt_def, toNat_ofNat (show 8 - held n < 2 ^ 64 by omega_using []), toNat_ofNat hL]
  · rw [u₃.other _ c, u₂.other _ b, u₁.other _ b, g _ a]

theorem flag_wp {u : State} {n L : Nat} {St D S : Addr} (hn : n < 2 ^ 64) (hL : L < 2 ^ 64)
    (h1 : u.gpr .a1 = BitVec.ofNat 64 n) (h3 : u.gpr .a3 = BitVec.ofNat 64 L) {rest : Prog isa}
    {Q : State → Prop} (k : ∀ s, AFl St D S n L u s → WP isa rest s Q) :
    WP isa (.seq heldCode (.seq (.block absFlag) rest)) u Q :=
  WP.seq (WP.mono (heldCode_wp hn h1) fun _ ⟨t0, g, m, rd, wr, sp⟩ =>
    WP.seq (WP.mono (absFlag_wp hL h3 t0 g m rd wr sp) k))

end VG.Proof.CmacTripleDes.Stream.RISCV64

end

end


/-!
# Streaming TDEA-CMAC on RISC-V: `absorb`'s chaining path

When the data do not fit in the `r = 8 - h` bytes after the `h` bytes held
back, the code copies their first `r` bytes there (`chainCopy_wp`), XORs the
completed block into the chaining value and enciphers it in place
(`setup_wp`, `ecb_call`), then each of the `nb` whole blocks of the rest but
its last 1 to 8 bytes (`loop_ok`, with `CInv`), and copies those to the
start of the bytes held back (`chain_wp`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacTripleDes.Stream.RISCV64
open VG.WriteBytes (writeBytes)

/-- The whole blocks chained after the completed one. -/
abbrev nbOf (L r : Nat) : Nat := (L - r - 1) / 8

/-- The bytes held back after them. -/
abbrev tailOf (L r : Nat) : Nat := L - r - 8 * nbOf L r

/-- Where the chaining path starts, by name: the state `St`, the data `D` of
`L` bytes, the scratch buffer `S`, `h` bytes held back and `r = 8 - h` after
them, fewer than `L`. -/
structure CPre (s₀ : State) (St D S : Addr) (h L : Nat) (u : State) : Prop where
  s1 : u.gpr .s1 = St
  s2 : u.gpr .s2 = S
  s3 : u.gpr .s3 = D
  a3 : u.gpr .a3 = BitVec.ofNat 64 L
  t0 : u.gpr .t0 = BitVec.ofNat 64 h
  t1 : u.gpr .t1 = BitVec.ofNat 64 (8 - h)
  hh : h ≤ 8
  lt : 8 - h < L
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr
  sp : u.sp = s₀.sp

/-- After the first copy: the block held back completed. -/
structure CCopy (s₀ : State) (St D S : Addr) (h L : Nat) (u s : State) : Prop where
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  s3 : s.gpr .s3 = D
  s4 : s.gpr .s4 = BitVec.ofNat 64 (L - (8 - h))
  t1 : s.gpr .t1 = BitVec.ofNat 64 (8 - h)
  keep : ∀ r ∈ preserved, r ≠ .s4 → s.gpr r = u.gpr r
  mem : s.mem = writeBytes u.mem (St + BitVec.ofNat 64 408 + BitVec.ofNat 64 h)
    (Spec.Aes.bytesAt u.mem D (8 - h))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- After the first block of the chaining path: the copy's arguments. -/
structure C1 (s₀ : State) (St D S : Addr) (h L : Nat) (u s : State) : Prop where
  s4 : s.gpr .s4 = BitVec.ofNat 64 (L - (8 - h))
  t3 : s.gpr .t3 = St + BitVec.ofNat 64 408 + BitVec.ofNat 64 h
  t4 : s.gpr .t4 = D
  t5 : s.gpr .t5 = BitVec.ofNat 64 (8 - h)
  keep : ∀ r, r ≠ .s4 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → s.gpr r = u.gpr r
  mem : s.mem = u.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem pre1_wp {s₀ u : State} {St D S : Addr} {h L : Nat} (hc : CPre s₀ St D S h L u) :
    WP isa (.block (([.sub .s4 .a3 .t1] : List Instr) ++ toHeld .t1)) u (C1 s₀ St D S h L u) := by
  have hl := hc.lt
  have hh := hc.hh
  unfold toHeld mov
  simp only [List.cons_append, List.nil_append]
  refine wp_sub fun s₁ u₁ => wp_addi (imm := 408) (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    wp_mv fun s₅ u₅ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, fun r a b c d => ?_, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hc.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hc.wr],
    by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hc.sp]⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
      hc.a3, hc.t1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_using [hl]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), u₁.other _ (by decide), hc.s1, hc.t0]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hc.s3]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hc.t1]
  · rw [u₅.other _ d, u₄.other _ c, u₃.other _ b, u₂.other _ b, u₁.other _ a]

theorem copy1_wp {s₀ u s₅ : State} {St D S : Addr} {h L n : Nat} (hp : APre s₀ St D S n L)
    (hc : CPre s₀ St D S h L u) (h₅ : C1 s₀ St D S h L u s₅) :
    WP isa (copy .t6 .t4 .t3 .t5) s₅ (CCopy s₀ St D S h L u) := by
  have hl := hc.lt
  have hh := hc.hh
  have hL := hp.hL
  have hw := hp.wSt
  have stW : (⟨St, 416⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have dR : (⟨D, L⟩ : Region) ∈ s₀.rd := by rw [hp.rd]; simp
  refine WP.mono (wp_sp (copy_ok (tmp := .t6) (src := .t4) (dst := .t3) (cnt := .t5) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) s₅ (P := D)
    (C := St + BitVec.ofNat 64 408 + BitVec.ofNat 64 h) (L := 8 - h) (by omega_using []) h₅.t4 h₅.t3 h₅.t5
    (fun i hi => by
      rw [h₅.rd, h₅.wr]
      exact ⟨_, List.mem_append_left _ dR, Offset.contains_base _ (by omega_using [hl, hi]) (by omega_using [hi])⟩)
    (fun i hi => by
      rw [h₅.wr, Offset.add_add, Offset.add_add]
      exact ⟨_, stW, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)
    (by
      rw [Offset.add_add]
      exact (hp.st_d.sub_left (Offset.sub_base St (by omega_using [hh]))).symm.sub_left
        (Region.sub_prefix (by omega_using [hl]))))) fun s₆ ⟨c, sp₆⟩ => ?_
  refine ⟨by rw [c.other _ (by decide) (by decide) (by decide) (by decide), h₅.keep _ (by decide) (by decide)
      (by decide) (by decide), hc.s1],
    by rw [c.other _ (by decide) (by decide) (by decide) (by decide), h₅.keep _ (by decide) (by decide)
      (by decide) (by decide), hc.s2],
    by rw [c.other _ (by decide) (by decide) (by decide) (by decide), h₅.keep _ (by decide) (by decide)
      (by decide) (by decide), hc.s3],
    by rw [c.other _ (by decide) (by decide) (by decide) (by decide), h₅.s4],
    by rw [c.other _ (by decide) (by decide) (by decide) (by decide), h₅.keep _ (by decide) (by decide)
      (by decide) (by decide), hc.t1],
    fun r hr h4 => ?_, by rw [c.mem, h₅.mem], by rw [c.rd, h₅.rd], by rw [c.wr, h₅.wr], by rw [sp₆, h₅.sp]⟩
  obtain ⟨-, -, -, h3, h4', h5, h6, -⟩ := preserved_ne r hr
  rw [c.other r h6 h4' h3 h5, h₅.keep r h4 h3 h4' h5]

theorem chainCopy_wp {s₀ u : State} {St D S : Addr} {h L n : Nat} (hp : APre s₀ St D S n L)
    (hc : CPre s₀ St D S h L u) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ c, CCopy s₀ St D S h L u c → WP isa rest c Q) :
    WP isa (.seq (.block (([.sub .s4 .a3 .t1] : List Instr) ++ toHeld .t1)) (.seq (copy .t6 .t4 .t3 .t5) rest)) u Q :=
  WP.seq (WP.mono (pre1_wp hc) fun _ h₅ => WP.seq (WP.mono (copy1_wp hp hc h₅) k))

theorem shr3_ofNat {x : Nat} (hx : x < 2 ^ 64) : BitVec.ofNat 64 x >>> 3 = BitVec.ofNat 64 (x / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by have := Nat.div_le_self x 8; omega_using [hx])]

theorem shl3_ofNat {x : Nat} (hx : 8 * x < 2 ^ 64) : BitVec.ofNat 64 x <<< 3 = BitVec.ofNat 64 (8 * x) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega_using [hx] : x < 2 ^ 64)]
  omega_using []

/-- After `chainSetup`: the completed block XORed into the chaining value,
the data pointer past the bytes that completed it, the blocks to chain and
the bytes to hold back after them, and ECB's arguments. -/
structure CSet (s₀ : State) (St D S : Addr) (h L : Nat) (c s : State) : Prop where
  args : EArgs s St 400
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  s3 : s.gpr .s3 = D + BitVec.ofNat 64 (8 - h)
  s4 : s.gpr .s4 = BitVec.ofNat 64 (tailOf L (8 - h))
  s5 : s.gpr .s5 = BitVec.ofNat 64 (nbOf L (8 - h))
  keep : ∀ r ∈ preserved, r ≠ .s3 → r ≠ .s4 → r ≠ .s5 → s.gpr r = c.gpr r
  frame : Frame [⟨St + BitVec.ofNat 64 400, 8⟩] c.mem s.mem
  out : Spec.Aes.bytesAt s.mem (St + BitVec.ofNat 64 400) 8 =
    Spec.Cmac.xor (Spec.Aes.bytesAt c.mem (St + BitVec.ofNat 64 400) 8)
      (Spec.Aes.bytesAt c.mem (St + BitVec.ofNat 64 408) 8)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem setup_wp {s₀ u c : State} {St D S : Addr} {h L n : Nat} (hp : APre s₀ St D S n L)
    (hc : CPre s₀ St D S h L u) (hcc : CCopy s₀ St D S h L u c) :
    WP isa (.block chainSetup) c (CSet s₀ St D S h L c) := by
  have hl := hc.lt
  have hh := hc.hh
  have hL := hp.hL
  have hw := hp.wSt
  have stW : (⟨St, 416⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  unfold chainSetup
  simp only [List.cons_append, List.nil_append]
  refine wp_add fun s₁ u₁ => wp_subi (imm := 1) (by decide) fun s₂ u₂ => wp_srl (by decide) fun s₃ u₃ =>
    wp_sll (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => wp_addi (imm := 400) (by decide) fun s₆ u₆ =>
    wp_addi (imm := 408) (by decide) fun s₇ u₇ => ?_
  have g₇ : ∀ r, r ≠ .s3 → r ≠ .t2 → r ≠ .s5 → r ≠ .s4 → r ≠ .a0 → r ≠ .a1 → s₇.gpr r = c.gpr r :=
    fun r a b d e f g => by
      rw [u₇.other _ g, u₆.other _ f, u₅.other _ e, u₄.other _ b, u₃.other _ d, u₂.other _ b, u₁.other _ a]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hcc.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hcc.wr]
  have sp₇ : s₇.sp = s₀.sp := by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hcc.sp]
  have m₇ : s₇.mem = c.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have t2₂ : s₂.gpr .t2 = BitVec.ofNat 64 (L - (8 - h) - 1) := by
    rw [u₂.gpr, u₁.other _ (by decide), hcc.s4]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_using [hl]
  have s5₃ : s₃.gpr .s5 = BitVec.ofNat 64 (nbOf L (8 - h)) := by
    rw [u₃.gpr, t2₂, shr3_ofNat (by omega_using [hL])]
  have t2₄ : s₄.gpr .t2 = BitVec.ofNat 64 (8 * nbOf L (8 - h)) := by
    rw [u₄.gpr, s5₃, shl3_ofNat (by unfold nbOf; omega_using [hL])]
  have s4₅ : s₅.gpr .s4 = BitVec.ofNat 64 (tailOf L (8 - h)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      hcc.s4, t2₄]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    unfold tailOf nbOf; omega_using []
  have s1₇ : s₇.gpr .s1 = St := by rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    hcc.s1]
  have a0₇ : s₇.gpr .a0 = St + BitVec.ofNat 64 400 := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hcc.s1]
  have a1₇ : s₇.gpr .a1 = St + BitVec.ofNat 64 408 := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hcc.s1]
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.xorBytes_ok (t := .t0) (u := .t1) (dst := .a0) (src := .a1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi => by rw [a1₇, rd₇, wr₇, Offset.add_add]; exact in_wr ⟨_, stW, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)
    (fun i hi => by rw [a0₇, wr₇, Offset.add_add]; exact ⟨_, stW, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)
    (by rw [a0₇, a1₇]; exact nsep (Offset.disjoint St (.inl (by omega_using [])) (by omega_using []) (by omega_using [])))) fun s₈ x₈ => ?_
  unfold ecbArgs mov
  refine wp_mv fun s₉ u₉ => wp_addi (imm := 400) (by decide) fun s₁₀ u₁₀ => ?_
  refine WP.cons (exec_li (show imm12 1 by decide)) (WP.block_nil ?_)
  have g₁₀ : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .a0 → r ≠ .a1 → s₁₀.gpr r = s₇.gpr r := fun r a b d e => by
    rw [u₁₀.other _ e, u₉.other _ d, x₈.gpr _ a b]
  have s1₁₀ : s₁₀.gpr .s1 = St := by rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), s1₇]
  have sp₁₀ : s₁₀.sp = s₀.sp := by rw [u₁₀.sp, u₉.sp, x₈.sp, sp₇]
  have fx : Frame [⟨St + BitVec.ofNat 64 400, 8⟩] c.mem s₁₀.mem := by
    have := x₈.frame; rw [a0₇, m₇] at this; rw [u₁₀.mem, u₉.mem]; exact this
  refine ⟨⟨?_, ?_, by simp [RegUpd.gpr_write], by decide, by decide, hw,
      by simp only [RegUpd.sp_write]; rw [sp₁₀]; exact hp.al, by simp only [RegUpd.sp_write]; rw [sp₁₀]; exact hp.sp,
      by simp only [RegUpd.sp_write]; rw [sp₁₀]; exact hp.stk_st,
      by simp only [RegUpd.wr_write]; rw [u₁₀.wr, u₉.wr, x₈.wr, wr₇]; exact stW⟩,
    ?_, ?_, ?_, ?_, ?_, fun r hr a b d => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.a0 ≠ .a2 by decide)]; rw [u₁₀.other _ (by decide), u₉.gpr,
      x₈.gpr _ (by decide) (by decide), s1₇]
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.a1 ≠ .a2 by decide)]; rw [u₁₀.gpr, u₉.other _ (by decide),
      x₈.gpr _ (by decide) (by decide), s1₇]
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.s1 ≠ .a2 by decide)]; exact s1₁₀
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.s2 ≠ .a2 by decide)]
    rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), g₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hcc.s2]
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.s3 ≠ .a2 by decide)]
    rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
      hcc.s3, hcc.t1]
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.s4 ≠ .a2 by decide)]
    rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), u₇.other _ (by decide), u₆.other _ (by decide), s4₅]
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.s5 ≠ .a2 by decide)]
    rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), s5₃]
  · obtain ⟨h0, h1, h2, -, -, -, -, -, ha0, ha1, ha2, -⟩ := preserved_ne r hr
    simp only [RegUpd.gpr_write_of_ne _ _ ha2]
    rw [g₁₀ r h0 h1 ha0 ha1, g₇ r a h2 d b ha0 ha1]
  · simp only [RegUpd.mem_write]; exact fx
  · simp only [RegUpd.mem_write]
    have e := xorBytes_bytes x₈
    rw [a0₇, a1₇, m₇] at e
    rw [u₁₀.mem, u₉.mem, e]
  · simp only [RegUpd.rd_write]; rw [u₁₀.rd, u₉.rd, x₈.rd, rd₇]
  · simp only [RegUpd.wr_write]; rw [u₁₀.wr, u₉.wr, x₈.wr, wr₇]
  · simp only [RegUpd.sp_write]; exact sp₁₀


/-! ## The loop -/

/-- After `k` whole blocks chained, from the state `e` after the completed
block's. -/
structure CInv (s₀ : State) (St D S : Addr) (h L : Nat) (e : State) (k : Nat) (s : State) : Prop where
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  s3 : s.gpr .s3 = D + BitVec.ofNat 64 (8 - h + 8 * k)
  s4 : s.gpr .s4 = BitVec.ofNat 64 (tailOf L (8 - h))
  s5 : s.gpr .s5 = BitVec.ofNat 64 (nbOf L (8 - h) - k)
  keep : ∀ r ∈ preserved, r ≠ .s3 → r ≠ .s5 → s.gpr r = e.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨St + BitVec.ofNat 64 400, 8⟩, ⟨s₀.sp - 944, 944⟩] e.mem s.mem
  cv : Spec.Aes.bytesAt s.mem (St + BitVec.ofNat 64 400) 8 =
    Spec.Cmac.chain (Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt e.mem St))
      (Spec.Aes.bytesAt e.mem (St + BitVec.ofNat 64 400) 8)
      (Spec.Cmac.blocksAt e.mem (D + BitVec.ofNat 64 (8 - h)) 8 k)

/-- What the block of the loop's body leaves: one more block XORed into the
chaining value, and ECB's arguments. -/
structure BMid (s₀ : State) (St D S : Addr) (h L : Nat) (e : State) (k : Nat) (s s' : State) : Prop where
  args : EArgs s' St 400
  s1 : s'.gpr .s1 = St
  s3 : s'.gpr .s3 = D + BitVec.ofNat 64 (8 - h + 8 * (k + 1))
  s5 : s'.gpr .s5 = BitVec.ofNat 64 (nbOf L (8 - h) - (k + 1))
  keep : ∀ r ∈ preserved, r ≠ .s3 → r ≠ .s5 → s'.gpr r = s.gpr r
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  sp : s'.sp = s₀.sp
  frame : Frame [⟨St + BitVec.ofNat 64 400, 8⟩] s.mem s'.mem
  cv : Spec.Aes.bytesAt s'.mem (St + BitVec.ofNat 64 400) 8 =
    Spec.Cmac.xor (Spec.Aes.bytesAt s.mem (St + BitVec.ofNat 64 400) 8)
      (Spec.Aes.bytesAt s.mem (D + BitVec.ofNat 64 (8 - h + 8 * k)) 8)

theorem bodyBlk_wp {s₀ e : State} {St D S : Addr} {h L n : Nat} (hp : APre s₀ St D S n L) {k : Nat}
    (hk : k < nbOf L (8 - h)) {s : State} (hi : CInv s₀ St D S h L e k s) :
    WP isa (.block (([.addi .t3 .s1 400] : List Instr) ++ Impl.Words.RISCV64.xorBytes .t0 .t1 .t3 .s3 8 ++
      ([.addi .s3 .s3 8, .addi .s5 .s5 (-1)] : List Instr) ++ ecbArgs 400)) s (BMid s₀ St D S h L e k s) := by
  have hL := hp.hL
  have hw := hp.wSt
  have hwd := hp.wD
  have stW : (⟨St, 416⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have dR : (⟨D, L⟩ : Region) ∈ s₀.rd := by rw [hp.rd]; simp
  have hb : 8 - h + 8 * k + 8 ≤ L := by unfold nbOf at hk; omega_using [hk]
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_addi (imm := 400) (by decide) fun s₁ u₁ => ?_
  have t3₁ : s₁.gpr .t3 = St + BitVec.ofNat 64 400 := by rw [u₁.gpr, hi.s1]
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.xorBytes_ok (t := .t0) (u := .t1) (dst := .t3) (src := .s3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi' => by
      rw [u₁.other _ (by decide), hi.s3, u₁.rd, u₁.wr, hi.rd, hi.wr, Offset.add_add]
      exact ⟨_, List.mem_append_left _ dR, Offset.contains_base _ (by omega_using [hb, hi']) (by omega_using [hL, hb, hi'])⟩)
    (fun i hi' => by rw [t3₁, u₁.wr, hi.wr, Offset.add_add]; exact ⟨_, stW, Offset.contains_base _ (by omega_using [hi']) (by omega_using [hi'])⟩)
    (by
      rw [t3₁, u₁.other _ (by decide), hi.s3]
      exact nsep ((hp.st_d.sub_left (Offset.sub_base St (by decide))).sub_right (Offset.sub_base D (by omega_using [hb])))))
    fun s₂ x₂ => ?_
  refine wp_addi (imm := 8) (by decide) fun s₃ u₃ => wp_subi (imm := 1) (by decide) fun s₄ u₄ => ?_
  unfold ecbArgs mov
  refine wp_mv fun s₅ u₅ => wp_addi (imm := 400) (by decide) fun s₆ u₆ => ?_
  refine WP.cons (exec_li (show imm12 1 by decide)) (WP.block_nil ?_)
  have g₆ : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t3 → r ≠ .s3 → r ≠ .s5 → r ≠ .a0 → r ≠ .a1 →
      s₆.gpr r = s.gpr r := fun r a b c d f g i => by
    rw [u₆.other _ i, u₅.other _ g, u₄.other _ f, u₃.other _ d, x₂.gpr _ a b, u₁.other _ c]
  have sp₆ : s₆.sp = s₀.sp := by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, x₂.sp, u₁.sp, hi.sp]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, x₂.wr, u₁.wr, hi.wr]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, x₂.rd, u₁.rd, hi.rd]
  have s1₆ : s₆.gpr .s1 = St := by
    rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hi.s1]
  have m₆ : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  refine ⟨⟨by simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.a0 ≠ .a2 by decide)]; rw [u₆.other _ (by decide), u₅.gpr,
        u₄.other _ (by decide), u₃.other _ (by decide), x₂.gpr _ (by decide) (by decide), u₁.other _ (by decide), hi.s1],
      by simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.a1 ≠ .a2 by decide)]; rw [u₆.gpr, s1₆.symm.trans
        (by rw [u₆.other _ (by decide)])], by simp [RegUpd.gpr_write], by decide, by decide, hw,
      by simp only [RegUpd.sp_write]; rw [sp₆]; exact hp.al, by simp only [RegUpd.sp_write]; rw [sp₆]; exact hp.sp,
      by simp only [RegUpd.sp_write]; rw [sp₆]; exact hp.stk_st,
      by simp only [RegUpd.wr_write]; rw [wr₆]; exact stW⟩, ?_, ?_, ?_, fun r hr a b => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.s1 ≠ .a2 by decide)]; exact s1₆
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.s3 ≠ .a2 by decide)]
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, x₂.gpr _ (by decide) (by decide),
      u₁.other _ (by decide), hi.s3, Offset.add_add, show 8 - h + 8 * k + 8 = 8 - h + 8 * (k + 1) by omega_using []]
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.s5 ≠ .a2 by decide)]
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), x₂.gpr _ (by decide) (by decide),
      u₁.other _ (by decide), hi.s5]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    unfold nbOf at hk ⊢; omega_using [hk]
  · obtain ⟨h0, h1, -, h3, -, -, -, -, ha0, ha1, ha2, -⟩ := preserved_ne r hr
    simp only [RegUpd.gpr_write_of_ne _ _ ha2]
    rw [g₆ r h0 h1 h3 a b ha0 ha1]
  · simp only [RegUpd.rd_write]; exact rd₆
  · simp only [RegUpd.wr_write]; exact wr₆
  · simp only [RegUpd.sp_write]; exact sp₆
  · simp only [RegUpd.mem_write, m₆]
    have := x₂.frame; rwa [t3₁, u₁.mem] at this
  · simp only [RegUpd.mem_write, m₆]
    have e₂ := xorBytes_bytes x₂
    rw [t3₁, u₁.other _ (by decide), hi.s3, u₁.mem] at e₂
    exact e₂

theorem body_ok {s₀ e : State} {St D S : Addr} {h L n : Nat} (hp : APre s₀ St D S n L) {k : Nat}
    (hk : k < nbOf L (8 - h)) {s : State} (hi : CInv s₀ St D S h L e k s) :
    WP isa chainBody s (CInv s₀ St D S h L e (k + 1)) := by
  have hL := hp.hL
  have hw := hp.wSt
  have hwd := hp.wD
  have hb : 8 - h + 8 * k + 8 ≤ L := by unfold nbOf at hk; omega_using [hk]
  unfold chainBody
  refine WP.seq (WP.mono (bodyBlk_wp hp hk hi) fun s₆ hm => ?_)
  refine WP.mono (ecb_call hm.args) fun s₇ h₇ => ?_
  -- The memory.
  have f₇ : Frame [⟨St + BitVec.ofNat 64 400, 8⟩, ⟨s₀.sp - 944, 944⟩] s₆.mem s₇.mem := by
    have := h₇.frame; rwa [hm.sp] at this
  have big : Frame [⟨St + BitVec.ofNat 64 400, 8⟩, ⟨s₀.sp - 944, 944⟩] e.mem s₇.mem :=
    (hi.frame.trans (hm.frame.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩)).trans f₇
  have dSch : ∀ r ∈ [(⟨St + BitVec.ofNat 64 400, 8⟩ : Region), ⟨s₀.sp - 944, 944⟩], (⟨St, 384⟩ : Region).Disjoint r :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.base_disjoint St (by decide) (by omega_using [])
      · exact (hp.stk_st.sub_right (Region.sub_prefix (by decide))).symm
  have sch : Spec.TripleDes.scheduleAt s₆.mem St = Spec.TripleDes.scheduleAt e.mem St := by
    rw [Proof.TripleDes.scheduleAt_eq_of_frame St hm.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dSch _ (by simp)),
      Proof.TripleDes.scheduleAt_eq_of_frame St hi.frame dSch]
  have blk : Spec.Aes.bytesAt s.mem (D + BitVec.ofNat 64 (8 - h + 8 * k)) 8 =
      Spec.Aes.bytesAt e.mem (D + BitVec.ofNat 64 (8 - h + 8 * k)) 8 :=
    Proof.Cmac.bytesAt_frame hi.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.st_d.sub_left (Offset.sub_base St (by decide))).symm.sub_left (Offset.sub_base D (by omega_using [hb]))
      · exact hp.stk_d.symm.sub_left (Offset.sub_base D (by omega_using [hb]))) (by decide)
  refine ⟨by rw [h₇.saved _ (by decide), hm.s1], by rw [h₇.saved _ (by decide), hm.keep _ (by decide) (by decide)
      (by decide), hi.s2], by rw [h₇.saved _ (by decide), hm.s3],
    by rw [h₇.saved _ (by decide), hm.keep _ (by decide) (by decide) (by decide), hi.s4],
    by rw [h₇.saved _ (by decide), hm.s5], fun r hr a b => by rw [h₇.saved r hr, hm.keep r hr a b, hi.keep r hr a b],
    by rw [h₇.rd, hm.rd], by rw [h₇.wr, hm.wr], by rw [h₇.sp, hm.sp], big, ?_⟩
  rw [h₇.out, hm.cv, sch, hi.cv, blk, blocksAt_succ, Proof.Cmac.chain_append, Proof.Cmac.chain_single,
    Offset.add_add]

theorem loop_ok {s₀ e : State} {St D S : Addr} {h L n : Nat} (hp : APre s₀ St D S n L) {k : Nat} (hk : k < nbOf L (8 - h)) {s : State} (hi : CInv s₀ St D S h L e k s) :
    WP isa (.loop chainBody (.nonzero .s5)) s (CInv s₀ St D S h L e (nbOf L (8 - h))) := by
  have hN : nbOf L (8 - h) < 2 ^ 64 := by have := hp.hL; unfold nbOf; omega_using [this]
  refine WP.loop (M := isa) (body := chainBody) (c := .nonzero .s5) (Q := CInv s₀ St D S h L e (nbOf L (8 - h)))
    (fun (m : Nat) (t : State) => ∃ j, m = nbOf L (8 - h) - j ∧ j < nbOf L (8 - h) ∧ CInv s₀ St D S h L e j t) ?_
    (nbOf L (8 - h) - k) s ⟨k, rfl, hk, hi⟩
  rintro m t ⟨j, rfl, hj, h'⟩
  refine WP.mono (body_ok hp hj h') fun t' h'' => ?_
  have ev := eval_nonzero_ofNat t' .s5 (k := nbOf L (8 - h) - (j + 1)) (by omega_using [hN]) h''.s5
  by_cases hz : nbOf L (8 - h) - (j + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show nbOf L (8 - h) = j + 1 by omega_using [hj, hz]]
  · right
    refine ⟨by rw [ev]; simp [hz], nbOf L (8 - h) - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hz], h''⟩

theorem chainLoop_wp {s₀ e : State} {St D S : Addr} {h L n : Nat} (hp : APre s₀ St D S n L) {s : State} (hi : CInv s₀ St D S h L e 0 s) :
    WP isa chainLoop s (CInv s₀ St D S h L e (nbOf L (8 - h))) := by
  have hN : nbOf L (8 - h) < 2 ^ 64 := by have := hp.hL; unfold nbOf; omega_using [this]
  have ev := eval_zero_ofNat s .s5 (k := nbOf L (8 - h) - 0) (by omega_using [hN]) hi.s5
  rw [Nat.sub_zero] at ev
  unfold chainLoop
  by_cases hn : nbOf L (8 - h) = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact hi
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hp (by omega_using [hn]) hi


/-! ## The whole path -/

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 8 * n⟩ : Region).Disjoint r) (hn : 8 * n ≤ 2 ^ 64) :
    Spec.Cmac.blocksAt m' p 8 n = Spec.Cmac.blocksAt m p 8 n := by
  rw [Proof.CmacTripleDes.Stream.blocksAt_eq, Proof.CmacTripleDes.Stream.blocksAt_eq,
    Proof.Cmac.bytesAt_frame hf hd hn]

/-- What the chaining path leaves, from the state `u` it starts in. -/
structure CDone (s₀ : State) (St D S : Addr) (h L : Nat) (u s : State) : Prop where
  keep : ∀ r ∈ preserved, r ≠ .s3 → r ≠ .s4 → r ≠ .s5 → s.gpr r = u.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] u.mem s.mem
  cv : Spec.Aes.bytesAt s.mem (St + BitVec.ofNat 64 400) 8 =
    Spec.Cmac.chain (Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt u.mem St))
      (Spec.Aes.bytesAt u.mem (St + BitVec.ofNat 64 400) 8)
      ([Spec.Aes.bytesAt u.mem (St + BitVec.ofNat 64 408) h ++ Spec.Aes.bytesAt u.mem D (8 - h)] ++
        Spec.Cmac.blocksAt u.mem (D + BitVec.ofNat 64 (8 - h)) 8 (nbOf L (8 - h)))
  held : Spec.Aes.bytesAt s.mem (St + BitVec.ofNat 64 408) (tailOf L (8 - h)) =
    Spec.Aes.bytesAt u.mem (D + BitVec.ofNat 64 (8 - h + 8 * nbOf L (8 - h))) (tailOf L (8 - h))

theorem chain_wp {s₀ u : State} {St D S : Addr} {h L n : Nat} (hp : APre s₀ St D S n L)
    (hc : CPre s₀ St D S h L u) : WP isa chainPath u (CDone s₀ St D S h L u) := by
  have hl := hc.lt
  have hh := hc.hh
  have hL := hp.hL
  have hw := hp.wSt
  have hwd := hp.wD
  have stW : (⟨St, 416⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have dR : (⟨D, L⟩ : Region) ∈ s₀.rd := by rw [hp.rd]; simp
  unfold chainPath
  refine chainCopy_wp hp hc fun c hcc => ?_
  refine WP.seq (WP.mono (setup_wp hp hc hcc) fun z hz => ?_)
  refine WP.seq (WP.mono (ecb_call hz.args) fun e he => ?_)
  have spe : e.sp = s₀.sp := by rw [he.sp, hz.sp]
  have ie : CInv s₀ St D S h L e 0 e := by
    refine ⟨by rw [he.saved _ (by decide), hz.s1], by rw [he.saved _ (by decide), hz.s2],
      by rw [he.saved _ (by decide), hz.s3, Nat.mul_zero, Nat.add_zero], by rw [he.saved _ (by decide), hz.s4],
      by rw [he.saved _ (by decide), hz.s5, Nat.sub_zero], fun _ _ _ _ => rfl, by rw [he.rd, hz.rd], by rw [he.wr, hz.wr], spe,
      Frame.refl _ _, rfl⟩
  refine WP.seq (WP.mono (chainLoop_wp hp ie) fun l hi => ?_)
  refine WP.seq ?_
  unfold mov
  refine wp_addi (imm := 408) (by decide) fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => WP.block_nil ?_
  have g₃ : ∀ r, r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → s₃.gpr r = l.gpr r := fun r a b c => by
    rw [u₃.other _ c, u₂.other _ b, u₁.other _ a]
  have hnb : 8 - h + 8 * nbOf L (8 - h) + tailOf L (8 - h) = L := by unfold tailOf nbOf; omega_using [hl]
  have htl : 0 < tailOf L (8 - h) ∧ tailOf L (8 - h) ≤ 8 := by unfold tailOf nbOf; omega_using [hl]
  refine WP.mono (wp_sp (copy_ok (tmp := .t6) (src := .t4) (dst := .t3) (cnt := .t5) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) s₃ (P := D + BitVec.ofNat 64 (8 - h + 8 * nbOf L (8 - h)))
    (C := St + BitVec.ofNat 64 408) (L := tailOf L (8 - h)) (by omega_using [htl])
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hi.s3])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hi.s1])
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hi.s4])
    (fun i hi' => by
      rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hi.rd, hi.wr, Offset.add_add]
      exact ⟨_, List.mem_append_left _ dR, Offset.contains_base _ (by omega_using [hnb, hi']) (by omega_using [hL, hnb, hi'])⟩)
    (fun i hi' => by
      rw [u₃.wr, u₂.wr, u₁.wr, hi.wr, Offset.add_add]
      exact ⟨_, stW, Offset.contains_base _ (by omega_using [htl, hi']) (by omega_using [htl, hi'])⟩)
    ((hp.st_d.sub_left (Offset.sub_base St (by omega_using [htl]))).symm.sub_left (Offset.sub_base D (by omega_using [hnb])))))
    fun f ⟨cf, spf⟩ => ?_
  -- The memory, step by step.
  have reg16 : ∀ r ∈ [(⟨St + BitVec.ofNat 64 400, 16⟩ : Region), ⟨s₀.sp - 944, 944⟩], r ∈
      [(⟨St + BitVec.ofNat 64 400, 16⟩ : Region), ⟨s₀.sp - 944, 944⟩] := fun _ h => h
  have s8 : ∀ r ∈ [(⟨St + BitVec.ofNat 64 400, 8⟩ : Region), ⟨s₀.sp - 944, 944⟩],
      ∃ r' ∈ [(⟨St + BitVec.ofNat 64 400, 16⟩ : Region), ⟨s₀.sp - 944, 944⟩], Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨St + BitVec.ofNat 64 400, 16⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨⟨s₀.sp - 944, 944⟩, by simp, fun _ h => h⟩
  have Fc : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] u.mem c.mem := by
    rw [hcc.mem]
    exact (WriteBytes.writeBytes_frame u.mem _ _ (R := ⟨St + BitVec.ofNat 64 400, 16⟩) (by
      rw [Proof.Cmac.bytesAt_length, Offset.add_add]
      exact Offset.contains St (by omega_using []) (by omega_using [hh]) (by omega_using []))).mono (by simp)
  have Fz : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] c.mem z.mem :=
    hz.frame.sub fun r hr => ⟨⟨St + BitVec.ofNat 64 400, 16⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩
  have Fe : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] z.mem e.mem := by
    have := he.frame; rw [hz.sp] at this; exact this.sub s8
  have Fl : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] e.mem l.mem := hi.frame.sub s8
  have Ful := ((Fc.trans Fz).trans Fe).trans Fl
  have m₃ : s₃.mem = l.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have Ff : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] l.mem f.mem := by
    rw [cf.mem, m₃]
    exact (WriteBytes.writeBytes_frame l.mem _ _ (R := ⟨St + BitVec.ofNat 64 400, 16⟩) (by
      rw [Proof.Cmac.bytesAt_length]
      exact Offset.contains St (by omega_using []) (by omega_using [htl]) (by omega_using []))).mono (by simp)
  -- What the data and the schedule are, from `u` on.
  have dD : ∀ a k, a + k ≤ L → ∀ r ∈ [(⟨St + BitVec.ofNat 64 400, 16⟩ : Region), ⟨s₀.sp - 944, 944⟩],
      (⟨D + BitVec.ofNat 64 a, k⟩ : Region).Disjoint r := fun a k hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.st_d.sub_left (Offset.sub_base St (by decide))).symm.sub_left (Offset.sub_base D hk)
    · exact hp.stk_d.symm.sub_left (Offset.sub_base D hk)
  have dSch : ∀ r ∈ [(⟨St + BitVec.ofNat 64 400, 16⟩ : Region), ⟨s₀.sp - 944, 944⟩], (⟨St, 384⟩ : Region).Disjoint r :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.base_disjoint St (by decide) (by omega_using [])
      · exact (hp.stk_st.sub_right (Region.sub_prefix (by decide))).symm
  refine ⟨fun r hr a b d => ?_, ?_, ?_, ?_, Ful.trans Ff, ?_, ?_⟩
  · obtain ⟨-, -, -, h3, h4, h5, h6, -⟩ := preserved_ne r hr
    rw [cf.other r h6 h4 h3 h5, g₃ r h3 h4 h5, hi.keep r hr a d, he.saved r hr, hz.keep r hr a b d, hcc.keep r hr b]
  · rw [cf.rd, u₃.rd, u₂.rd, u₁.rd, hi.rd]
  · rw [cf.wr, u₃.wr, u₂.wr, u₁.wr, hi.wr]
  · rw [spf, u₃.sp, u₂.sp, u₁.sp, hi.sp]
  · have e₁ : Spec.Aes.bytesAt f.mem (St + BitVec.ofNat 64 400) 8 = Spec.Aes.bytesAt l.mem (St + BitVec.ofNat 64 400) 8 := by
      have Fw : Frame [⟨St + BitVec.ofNat 64 408, tailOf L (8 - h)⟩] l.mem f.mem := by
        rw [cf.mem, m₃]
        exact WriteBytes.writeBytes_frame _ _ _ (by
          rw [Proof.Cmac.bytesAt_length]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [])
      exact Proof.Cmac.bytesAt_frame Fw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint St (.inl (by omega_using [])) (by omega_using []) (by omega_using [htl])) (by decide)
    have sch : Spec.TripleDes.scheduleAt z.mem St = Spec.TripleDes.scheduleAt u.mem St :=
      Proof.TripleDes.scheduleAt_eq_of_frame St (Fc.trans Fz) dSch
    have sche : Spec.TripleDes.scheduleAt e.mem St = Spec.TripleDes.scheduleAt u.mem St :=
      Proof.TripleDes.scheduleAt_eq_of_frame St ((Fc.trans Fz).trans Fe) dSch
    have cvc : Spec.Aes.bytesAt c.mem (St + BitVec.ofNat 64 400) 8 = Spec.Aes.bytesAt u.mem (St + BitVec.ofNat 64 400) 8 := by
      have Fw : Frame [⟨St + BitVec.ofNat 64 (408 + h), 8 - h⟩] u.mem c.mem := by
        rw [hcc.mem, Offset.add_add]
        exact WriteBytes.writeBytes_frame _ _ _ (by
          rw [Proof.Cmac.bytesAt_length]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [])
      exact Proof.Cmac.bytesAt_frame Fw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint St (.inl (by omega_using [])) (by omega_using []) (by omega_using [hh])) (by decide)
    have blkc : Spec.Aes.bytesAt c.mem (St + BitVec.ofNat 64 408) 8 =
        Spec.Aes.bytesAt u.mem (St + BitVec.ofNat 64 408) h ++ Spec.Aes.bytesAt u.mem D (8 - h) := by
      rw [hcc.mem]
      have := bytesAt_writeBytes u.mem (St + BitVec.ofNat 64 408) h (Spec.Aes.bytesAt u.mem D (8 - h))
        (by rw [Proof.Cmac.bytesAt_length]; omega_using [hh])
      rwa [Proof.Cmac.bytesAt_length, show h + (8 - h) = 8 by omega_using [hh]] at this
    rw [e₁, hi.cv, he.out, hz.out, cvc, blkc, sch, sche,
      blocksAt_frame ((Fc.trans Fz).trans Fe) (dD (8 - h) (8 * nbOf L (8 - h)) (by omega_using [hnb])) (by omega_using [hL, hnb]),
      Proof.Cmac.chain_append, Proof.Cmac.chain_single]
  · rw [cf.mem, m₃]
    have := bytesAt_writeBytes_self l.mem (St + BitVec.ofNat 64 408)
      (xs := Spec.Aes.bytesAt l.mem (D + BitVec.ofNat 64 (8 - h + 8 * nbOf L (8 - h))) (tailOf L (8 - h)))
      (by rw [Proof.Cmac.bytesAt_length]; omega_using [htl])
    rw [Proof.Cmac.bytesAt_length] at this
    rw [this, Proof.Cmac.bytesAt_frame Ful (dD _ _ (by omega_using [hnb])) (by omega_using [htl])]

end VG.Proof.CmacTripleDes.Stream.RISCV64

end

end


/-!
# Streaming TDEA-CMAC on RISC-V: `absorb`

The code saves the registers (`absSave_wp`), computes the number `h` of
bytes held back and whether the data fit in the `8 - h` bytes after them
(`flag_wp`); if they do, it copies them there (`Proof.CmacTripleDes.Stream.repr_fill`),
else it takes the chaining path (`chain_wp`, `repr_chain`); then it restores
the registers (`absorb_wp`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacTripleDes.Stream.RISCV64
open VG.WriteBytes (writeBytes)
open VG.Proof.CmacTripleDes.Stream (held)

/-- What the paths leave, from the state `u` after the flag: the state then
represents the message followed by the data. -/
structure PDone (s₀ : State) (St D : Addr) (n L : Nat) (u s : State) : Prop where
  keep : ∀ r ∈ preserved, r ≠ .s3 → r ≠ .s4 → r ≠ .s5 → s.gpr r = u.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] u.mem s.mem
  repr : ∀ key msg, Spec.Cmac.tdesRepr u.mem St key msg → msg.length = n →
    Spec.Cmac.tdesRepr s.mem St key (msg ++ Spec.Aes.bytesAt u.mem D L)

/-- The first 400 bytes of the state, apart from what the paths write. -/
theorem keep400 {s₀ : State} {St : Addr} {m m' : Mem}
    (hstk : (⟨s₀.sp - 944, 944⟩ : Region).Disjoint ⟨St, 416⟩)
    (hf : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] m m') :
    ∀ i < 400, m' (St + BitVec.ofNat 64 i) = m (St + BitVec.ofNat 64 i) := fun i hi =>
  hf _ fun r hr hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint St (d := i) (n := 1) (.inl (by omega_using [hi])) (by omega_using [hi]) (by omega_using []) _
        (Region.contains_self _ _) hc
    · exact hstk _ hc (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))

theorem paths_wp {s₀ s₁ u : State} {St D S : Addr} {n L : Nat} (hp : APre s₀ St D S n L)
    (h₁ : AMid s₀ St D S n L s₁) (hu : AFl St D S n L s₁ u) :
    WP isa (.ite (.nonzero .t2) chainPath fillPath) u (PDone s₀ St D n L u) := by
  have hL := hp.hL
  have hw := hp.wSt
  have hwd := hp.wD
  have hl := Proof.CmacTripleDes.Stream.held_le n
  have stW : (⟨St, 416⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have dR : (⟨D, L⟩ : Region) ∈ s₀.rd := by rw [hp.rd]; simp
  have s1u : u.gpr .s1 = St := by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.s1]
  have s2u : u.gpr .s2 = S := by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.s2]
  have s3u : u.gpr .s3 = D := by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.s3]
  have a3u : u.gpr .a3 = BitVec.ofNat 64 L := by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.a3]
  have rdu : u.rd = s₀.rd := by rw [hu.rd, h₁.rd]
  have wru : u.wr = s₀.wr := by rw [hu.wr, h₁.wr]
  have spu : u.sp = s₀.sp := by rw [hu.sp, h₁.sp]
  have ev : isa.eval (.nonzero .t2) u = some (decide (8 - held n < L)) := by
    rw [eval_nonzero, hu.t2]; split <;> simp_all
  by_cases hc : 8 - held n < L
  · -- The data do not fit: chain.
    refine WP.ite true (by rw [ev]; simp [hc]) (fun _ => ?_) (fun h => by cases h)
    refine WP.mono (chain_wp hp ⟨s1u, s2u, s3u, a3u, hu.t0, hu.t1, hl, hc, rdu, wru, spu⟩) fun s hs => ?_
    refine ⟨hs.keep, hs.rd, hs.wr, hs.sp, hs.frame, fun key msg hr hn => ?_⟩
    subst hn
    have hsch : Spec.TripleDes.scheduleAt u.mem St = Spec.TripleDes.expandKey key := hr.2.1
    have dl : (Spec.Aes.bytesAt u.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    have hnb := Proof.CmacTripleDes.Stream.held_chain_pos (n := msg.length) (l := L) hc
    refine Proof.CmacTripleDes.Stream.repr_chain hr (keep400 hp.stk_st hs.frame) (by rw [dl]; exact hc) ?_ ?_
    · rw [dl, show St + 400 = St + BitVec.ofNat 64 400 from rfl, show St + 408 = St + BitVec.ofNat 64 408 from rfl,
        hs.cv, hsch, bytesAt_take u.mem D (by omega_using [hc]), bytesAt_drop_take u.mem D (by unfold Proof.CmacTripleDes.Stream.nblocks; omega_using [hc]),
        ← Proof.CmacTripleDes.Stream.blocksAt_eq]
      rfl
    · rw [dl, show St + 408 = St + BitVec.ofNat 64 408 from rfl, List.drop_drop,
        bytesAt_drop u.mem D (by unfold Proof.CmacTripleDes.Stream.nblocks; omega_using [hc])]
      have e : L - (8 - held msg.length) - 8 * Proof.CmacTripleDes.Stream.nblocks msg.length L =
          tailOf L (8 - held msg.length) := rfl
      rw [e, hs.held]
      unfold tailOf nbOf Proof.CmacTripleDes.Stream.nblocks
      congr 1; omega_using []
  · -- The data fit: copy them after the bytes held back.
    refine WP.ite false (by rw [ev]; simp [hc]) (fun h => by cases h) fun _ => ?_
    unfold fillPath toHeld mov
    refine WP.seq ?_
    refine wp_addi (imm := 408) (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ => wp_mv fun s₄ u₄ =>
      wp_mv fun s₅ u₅ => WP.block_nil ?_
    have g₅ : ∀ r, r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → s₅.gpr r = u.gpr r := fun r a b c => by
      rw [u₅.other _ c, u₄.other _ b, u₃.other _ a, u₂.other _ a]
    refine WP.mono (wp_sp (copy_ok (tmp := .t6) (src := .t4) (dst := .t3) (cnt := .t5) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) s₅ (P := D)
      (C := St + BitVec.ofNat 64 408 + BitVec.ofNat 64 (held n)) (L := L) hL
      (by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), s3u])
      (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), s1u, hu.t0])
      (by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), a3u])
      (fun i hi => by
        rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, rdu, wru]
        exact ⟨_, List.mem_append_left _ dR, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hL, hi])⟩)
      (fun i hi => by
        rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wru, Offset.add_add, Offset.add_add]
        exact ⟨_, stW, Offset.contains_base _ (by omega_using [hc, hi]) (by omega_using [hc, hi])⟩)
      (by
        rw [Offset.add_add]
        exact (hp.st_d.sub_left (Offset.sub_base St (by omega_using [hl, hc]))).symm))) fun s ⟨cs, sps⟩ => ?_
    have m₅ : s₅.mem = u.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    have Fw : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] u.mem s.mem := by
      rw [cs.mem, m₅]
      exact (WriteBytes.writeBytes_frame u.mem _ _ (R := ⟨St + BitVec.ofNat 64 400, 16⟩) (by
        rw [Proof.Cmac.bytesAt_length, Offset.add_add]
        exact Offset.contains St (by omega_using []) (by omega_using [hl, hc]) (by omega_using []))).mono (by simp)
    refine ⟨fun r hr _ _ _ => ?_, by rw [cs.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rdu],
      by rw [cs.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wru], by rw [sps, u₅.sp, u₄.sp, u₃.sp, u₂.sp, spu], Fw,
      fun key msg hr hn => ?_⟩
    · obtain ⟨-, -, -, h3, h4, h5, h6, -⟩ := preserved_ne r hr
      rw [cs.other r h6 h4 h3 h5, g₅ r h3 h4 h5]
    subst hn
    have dl : (Spec.Aes.bytesAt u.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    refine Proof.CmacTripleDes.Stream.repr_fill hr (keep400 hp.stk_st Fw) (by rw [dl]; omega_using [hc]) ?_ ?_
    · rw [show St + 400 = St + BitVec.ofNat 64 400 from rfl]
      have Fw2 : Frame [⟨St + BitVec.ofNat 64 (408 + held msg.length), L⟩] u.mem s.mem := by
        rw [cs.mem, m₅, Offset.add_add]
        exact WriteBytes.writeBytes_frame _ _ _ (by
          rw [Proof.Cmac.bytesAt_length]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [])
      exact Proof.Cmac.bytesAt_frame Fw2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint St (.inl (by omega_using [])) (by omega_using []) (by omega_using [hl, hc])) (by decide)
    · rw [show St + 408 = St + BitVec.ofNat 64 408 from rfl, cs.mem, m₅]
      have := bytesAt_writeBytes u.mem (St + BitVec.ofNat 64 408) (held msg.length) (Spec.Aes.bytesAt u.mem D L)
        (by rw [dl]; omega_using [hl, hc])
      rw [dl] at this ⊢
      exact this


theorem absorb_wp {s₀ : State} (h0 : absorbRISCV64.pre s₀) :
    WP isa absorb s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.sp = s₀.sp ∧ absorbRISCV64.post s₀ s' := by
  have hp := APre.of h0
  generalize s₀.gpr .a0 = St at hp
  generalize s₀.gpr .a2 = D at hp
  generalize s₀.gpr .a4 = S at hp
  generalize (s₀.gpr .a1).toNat = n at hp
  generalize (s₀.gpr .a3).toNat = L at hp
  have hsw := hp.wS
  unfold absorb
  refine WP.seq (WP.mono (absSave_wp hp) fun s₁ h₁ => ?_)
  refine flag_wp (St := St) (D := D) (S := S) hp.hn hp.hL h₁.a1 h₁.a3 fun u hu => ?_
  refine WP.seq (WP.mono (paths_wp hp h₁ hu) fun s₂ h₂ => ?_)
  have s2₂ : s₂.gpr .s2 = S := by
    rw [h₂.keep _ (by decide) (by decide) (by decide) (by decide), hu.keep _ (by decide) (by decide) (by decide), h₁.s2]
  rw [restoreRegs, WP.block_append_iff]
  refine WP.mono (savePtr_ok .s2) fun s₃ e => ?_
  subst e
  rw [s2₂]
  have dSv (p : Reg × Nat) (hp' : p ∈ absSaved) (r : Region) (hr : r ∈ [⟨St + BitVec.ofNat 64 400, 16⟩,
      ⟨s₀.sp - 944, 944⟩]) : (⟨sv S + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint r := by
    have hb := abs_bound p hp'
    have sub : Region.Sub ⟨sv S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 688⟩ := fun a ha =>
      Region.sub_prefix (by decide) a (sv_sub S (d := p.2) (n := 8) (by omega_using [hb]) a ha)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
    · exact hp.stk_s.symm.sub_left sub
  have F₂ : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] s₁.mem s₂.mem := by
    have := h₂.frame; rwa [hu.mem] at this
  have sv₂ : Spill.Saved (sv S) (absG s₀ S) absSaved s₂.mem := by
    have sv₁ : Spill.Saved (sv S) (absG s₀ S) absSaved s₁.mem := by
      rw [h₁.mem]; exact Spill.saveMem_saved (by decide) s₀.mem (sv S) _
    exact sv₁.frame F₂ fun p hp' r hr => dSv p hp' r hr
  rw [show absSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 absSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := absSaved) (B := sv S) (Align.align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) sv₂) fun s₄ r₄ => ?_
  · have := abs_bound p hp'
    show InRegions (s₂.rd ++ s₂.wr) _ 8
    rw [h₂.rd, h₂.wr, hp.rd, hp.wr]
    exact ⟨⟨S, 688⟩, by simp, sv_contains S (by omega_using [this]) (by decide)⟩
  have g₀ (r : Reg) (hr : r ≠ .t0) : absG s₀ S r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have h0 := (preserved_ne r hr).1
    rw [r₄.gpr_of (r := r) ?_, g₀ r h0]
    by_cases hv : r = .s1 ∨ r = .s2 ∨ r = .s3 ∨ r = .s4 ∨ r = .s5
    · left; rcases hv with rfl | rfl | rfl | rfl | rfl <;> decide
    · right
      obtain ⟨-, h1, h2, -⟩ := preserved_ne r hr
      rw [RegUpd.gpr_write_of_ne _ _ h0, h₂.keep r hr (fun e => hv (.inr (.inr (.inl e))))
        (fun e => hv (.inr (.inr (.inr (.inl e))))) (fun e => hv (.inr (.inr (.inr (.inr e))))),
        hu.keep r h0 h1 h2, h₁.other r hr (fun e => hv (.inl e)) (fun e => hv (.inr (.inl e)))
          (fun e => hv (.inr (.inr (.inl e)))), g₀ r h0]
  · rw [r₄.gpr (.ra, 0) (by decide), g₀ .ra (by decide)]
  · rw [r₄.sp, RegUpd.sp_write, h₂.sp]
  · intro key msg hr ha1 hlen
    rw [hp.a0] at hr ⊢
    rw [hp.a2] at ⊢
    rw [r₄.mem, RegUpd.mem_write]
    have hn : n = msg.length := by
      have := congrArg BitVec.toNat (hp.a1.symm.trans ha1)
      rwa [toNat_ofNat hp.hn, toNat_ofNat (by omega_using [hlen])] at this
    have hL : (s₀.gpr .a3).toNat = L := by rw [hp.a3, toNat_ofNat hp.hL]
    rw [hL]
    -- The state and the data on entry, through the saves.
    have f₁ : Frame [⟨sv S, 48⟩] s₀.mem u.mem := by
      rw [hu.mem, h₁.mem]
      exact Spill.saveMem_frame_base (l := absSaved) (n := 48) abs_bound (by decide) s₀.mem (sv S) (absG s₀ S)
    have dS : Region.Sub ⟨sv S, 48⟩ ⟨S, 688⟩ := by
      have := sv_sub S (d := 0) (n := 48) (by decide)
      rw [BitVec.add_zero] at this
      exact fun a ha => Region.sub_prefix (by decide) a (this a ha)
    have hru : Spec.Cmac.tdesRepr u.mem St key msg :=
      Proof.CmacTripleDes.Stream.repr_congr_416 (fun i hi => f₁ _ fun r hr hc => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_s _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) (dS _ hc)) hr
    have hd : Spec.Aes.bytesAt u.mem D L = Spec.Aes.bytesAt s₀.mem D L :=
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.d_s.sub_right dS) (by have := hp.wD; omega_using [hL])
    rw [← hd]
    exact h₂.repr key msg hru hn.symm

end VG.Proof.CmacTripleDes.Stream.RISCV64
