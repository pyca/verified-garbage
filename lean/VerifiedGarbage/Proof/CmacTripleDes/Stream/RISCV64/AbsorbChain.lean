module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.AbsorbParts
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Finish
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.TripleDes.Schedule
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Calls

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
    omega
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
    (C := St + BitVec.ofNat 64 408 + BitVec.ofNat 64 h) (L := 8 - h) (by omega) h₅.t4 h₅.t3 h₅.t5
    (fun i hi => by
      rw [h₅.rd, h₅.wr]
      exact ⟨_, List.mem_append_left _ dR, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => by
      rw [h₅.wr, Offset.add_add, Offset.add_add]
      exact ⟨_, stW, Offset.contains_base _ (by omega) (by omega)⟩)
    (by
      rw [Offset.add_add]
      exact (hp.st_d.sub_left (Offset.sub_base St (by omega))).symm.sub_left
        (Region.sub_prefix (by omega))))) fun s₆ ⟨c, sp₆⟩ => ?_
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
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by have := Nat.div_le_self x 8; omega)]

theorem shl3_ofNat {x : Nat} (hx : 8 * x < 2 ^ 64) : BitVec.ofNat 64 x <<< 3 = BitVec.ofNat 64 (8 * x) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : x < 2 ^ 64)]
  omega

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
    omega
  have s5₃ : s₃.gpr .s5 = BitVec.ofNat 64 (nbOf L (8 - h)) := by
    rw [u₃.gpr, t2₂, shr3_ofNat (by omega)]
  have t2₄ : s₄.gpr .t2 = BitVec.ofNat 64 (8 * nbOf L (8 - h)) := by
    rw [u₄.gpr, s5₃, shl3_ofNat (by unfold nbOf; omega)]
  have s4₅ : s₅.gpr .s4 = BitVec.ofNat 64 (tailOf L (8 - h)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      hcc.s4, t2₄]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    unfold tailOf nbOf; omega
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
    (fun i hi => by rw [a1₇, rd₇, wr₇, Offset.add_add]; exact in_wr ⟨_, stW, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => by rw [a0₇, wr₇, Offset.add_add]; exact ⟨_, stW, Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [a0₇, a1₇]; exact nsep (Offset.disjoint St (.inl (by omega)) (by omega) (by omega)))) fun s₈ x₈ => ?_
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
  have hb : 8 - h + 8 * k + 8 ≤ L := by unfold nbOf at hk; omega
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_addi (imm := 400) (by decide) fun s₁ u₁ => ?_
  have t3₁ : s₁.gpr .t3 = St + BitVec.ofNat 64 400 := by rw [u₁.gpr, hi.s1]
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.xorBytes_ok (t := .t0) (u := .t1) (dst := .t3) (src := .s3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi' => by
      rw [u₁.other _ (by decide), hi.s3, u₁.rd, u₁.wr, hi.rd, hi.wr, Offset.add_add]
      exact ⟨_, List.mem_append_left _ dR, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi' => by rw [t3₁, u₁.wr, hi.wr, Offset.add_add]; exact ⟨_, stW, Offset.contains_base _ (by omega) (by omega)⟩)
    (by
      rw [t3₁, u₁.other _ (by decide), hi.s3]
      exact nsep ((hp.st_d.sub_left (Offset.sub_base St (by decide))).sub_right (Offset.sub_base D (by omega)))))
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
      u₁.other _ (by decide), hi.s3, Offset.add_add, show 8 - h + 8 * k + 8 = 8 - h + 8 * (k + 1) by omega]
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.s5 ≠ .a2 by decide)]
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), x₂.gpr _ (by decide) (by decide),
      u₁.other _ (by decide), hi.s5]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    unfold nbOf at hk ⊢; omega
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
  have hb : 8 - h + 8 * k + 8 ≤ L := by unfold nbOf at hk; omega
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
      · exact Offset.base_disjoint St (by decide) (by omega)
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
      · exact (hp.st_d.sub_left (Offset.sub_base St (by decide))).symm.sub_left (Offset.sub_base D (by omega))
      · exact hp.stk_d.symm.sub_left (Offset.sub_base D (by omega))) (by decide)
  refine ⟨by rw [h₇.saved _ (by decide), hm.s1], by rw [h₇.saved _ (by decide), hm.keep _ (by decide) (by decide)
      (by decide), hi.s2], by rw [h₇.saved _ (by decide), hm.s3],
    by rw [h₇.saved _ (by decide), hm.keep _ (by decide) (by decide) (by decide), hi.s4],
    by rw [h₇.saved _ (by decide), hm.s5], fun r hr a b => by rw [h₇.saved r hr, hm.keep r hr a b, hi.keep r hr a b],
    by rw [h₇.rd, hm.rd], by rw [h₇.wr, hm.wr], by rw [h₇.sp, hm.sp], big, ?_⟩
  rw [h₇.out, hm.cv, sch, hi.cv, blk, blocksAt_succ, Proof.Cmac.chain_append, Proof.Cmac.chain_single,
    Offset.add_add]

theorem loop_ok {s₀ e : State} {St D S : Addr} {h L n : Nat} (hp : APre s₀ St D S n L) {k : Nat} (hk : k < nbOf L (8 - h)) {s : State} (hi : CInv s₀ St D S h L e k s) :
    WP isa (.loop chainBody (.nonzero .s5)) s (CInv s₀ St D S h L e (nbOf L (8 - h))) := by
  have hN : nbOf L (8 - h) < 2 ^ 64 := by have := hp.hL; unfold nbOf; omega
  refine WP.loop (M := isa) (body := chainBody) (c := .nonzero .s5) (Q := CInv s₀ St D S h L e (nbOf L (8 - h)))
    (fun (m : Nat) (t : State) => ∃ j, m = nbOf L (8 - h) - j ∧ j < nbOf L (8 - h) ∧ CInv s₀ St D S h L e j t) ?_
    (nbOf L (8 - h) - k) s ⟨k, rfl, hk, hi⟩
  rintro m t ⟨j, rfl, hj, h'⟩
  refine WP.mono (body_ok hp hj h') fun t' h'' => ?_
  have ev := eval_nonzero_ofNat t' .s5 (k := nbOf L (8 - h) - (j + 1)) (by omega) h''.s5
  by_cases hz : nbOf L (8 - h) - (j + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show nbOf L (8 - h) = j + 1 by omega]
  · right
    refine ⟨by rw [ev]; simp [hz], nbOf L (8 - h) - (j + 1), by omega, j + 1, rfl, by omega, h''⟩

theorem chainLoop_wp {s₀ e : State} {St D S : Addr} {h L n : Nat} (hp : APre s₀ St D S n L) {s : State} (hi : CInv s₀ St D S h L e 0 s) :
    WP isa chainLoop s (CInv s₀ St D S h L e (nbOf L (8 - h))) := by
  have hN : nbOf L (8 - h) < 2 ^ 64 := by have := hp.hL; unfold nbOf; omega
  have ev := eval_zero_ofNat s .s5 (k := nbOf L (8 - h) - 0) (by omega) hi.s5
  rw [Nat.sub_zero] at ev
  unfold chainLoop
  by_cases hn : nbOf L (8 - h) = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact hi
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hp (by omega) hi


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
  have hnb : 8 - h + 8 * nbOf L (8 - h) + tailOf L (8 - h) = L := by unfold tailOf nbOf; omega
  have htl : 0 < tailOf L (8 - h) ∧ tailOf L (8 - h) ≤ 8 := by unfold tailOf nbOf; omega
  refine WP.mono (wp_sp (copy_ok (tmp := .t6) (src := .t4) (dst := .t3) (cnt := .t5) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) s₃ (P := D + BitVec.ofNat 64 (8 - h + 8 * nbOf L (8 - h)))
    (C := St + BitVec.ofNat 64 408) (L := tailOf L (8 - h)) (by omega)
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hi.s3])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hi.s1])
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hi.s4])
    (fun i hi' => by
      rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hi.rd, hi.wr, Offset.add_add]
      exact ⟨_, List.mem_append_left _ dR, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi' => by
      rw [u₃.wr, u₂.wr, u₁.wr, hi.wr, Offset.add_add]
      exact ⟨_, stW, Offset.contains_base _ (by omega) (by omega)⟩)
    ((hp.st_d.sub_left (Offset.sub_base St (by omega))).symm.sub_left (Offset.sub_base D (by omega)))))
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
      exact Offset.contains St (by omega) (by omega) (by omega))).mono (by simp)
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
      exact Offset.contains St (by omega) (by omega) (by omega))).mono (by simp)
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
      · exact Offset.base_disjoint St (by decide) (by omega)
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
          rw [Proof.Cmac.bytesAt_length]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
      exact Proof.Cmac.bytesAt_frame Fw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint St (.inl (by omega)) (by omega) (by omega)) (by decide)
    have sch : Spec.TripleDes.scheduleAt z.mem St = Spec.TripleDes.scheduleAt u.mem St :=
      Proof.TripleDes.scheduleAt_eq_of_frame St (Fc.trans Fz) dSch
    have sche : Spec.TripleDes.scheduleAt e.mem St = Spec.TripleDes.scheduleAt u.mem St :=
      Proof.TripleDes.scheduleAt_eq_of_frame St ((Fc.trans Fz).trans Fe) dSch
    have cvc : Spec.Aes.bytesAt c.mem (St + BitVec.ofNat 64 400) 8 = Spec.Aes.bytesAt u.mem (St + BitVec.ofNat 64 400) 8 := by
      have Fw : Frame [⟨St + BitVec.ofNat 64 (408 + h), 8 - h⟩] u.mem c.mem := by
        rw [hcc.mem, Offset.add_add]
        exact WriteBytes.writeBytes_frame _ _ _ (by
          rw [Proof.Cmac.bytesAt_length]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
      exact Proof.Cmac.bytesAt_frame Fw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint St (.inl (by omega)) (by omega) (by omega)) (by decide)
    have blkc : Spec.Aes.bytesAt c.mem (St + BitVec.ofNat 64 408) 8 =
        Spec.Aes.bytesAt u.mem (St + BitVec.ofNat 64 408) h ++ Spec.Aes.bytesAt u.mem D (8 - h) := by
      rw [hcc.mem]
      have := bytesAt_writeBytes u.mem (St + BitVec.ofNat 64 408) h (Spec.Aes.bytesAt u.mem D (8 - h))
        (by rw [Proof.Cmac.bytesAt_length]; omega)
      rwa [Proof.Cmac.bytesAt_length, show h + (8 - h) = 8 by omega] at this
    rw [e₁, hi.cv, he.out, hz.out, cvc, blkc, sch, sche,
      blocksAt_frame ((Fc.trans Fz).trans Fe) (dD (8 - h) (8 * nbOf L (8 - h)) (by omega)) (by omega),
      Proof.Cmac.chain_append, Proof.Cmac.chain_single]
  · rw [cf.mem, m₃]
    have := bytesAt_writeBytes_self l.mem (St + BitVec.ofNat 64 408)
      (xs := Spec.Aes.bytesAt l.mem (D + BitVec.ofNat 64 (8 - h + 8 * nbOf L (8 - h))) (tailOf L (8 - h)))
      (by rw [Proof.Cmac.bytesAt_length]; omega)
    rw [Proof.Cmac.bytesAt_length] at this
    rw [this, Proof.Cmac.bytesAt_frame Ful (dD _ _ (by omega)) (by omega)]

end VG.Proof.CmacTripleDes.Stream.RISCV64
