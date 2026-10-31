module

public import VerifiedGarbage.Proof.Cast5.RISCV64.KeySteps
import VerifiedGarbage.Proof.Cast5.RISCV64.Ecb
public import VerifiedGarbage.Proof.Cast5.Table
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Cast5.RISCV64.Run
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep

/-!
# CAST5 key expansion on RISC-V: a step

`step` chooses the step's bytes by the step's number in `stp` (`sel_ok`),
gathers them into `s0`–`s3` (`gather_ok`), scans `VG_CAST5_S5678`, and
chooses what to do with the four values (`postE_ok`, `postL_ok`): the step of
the spec's `stepRun`, as on PPC64LE (`Proof/Cast5/PPC64LE/KeyStep.lean`).
The working space is rounded up to a multiple of 8, so its words take
aligned accesses; a quadruple of `x` or `z` is read and written big-endian a
byte at a time (`writeBytes_beBytes`: as PPC64LE's byte-reversed store), and
a subkey little-endian a byte at a time.
-/

@[expose] public section

namespace VG.Proof.Cast5.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Cast5 VG.Impl.Cast5.RISCV64 VG.Proof.Cast5
open VG.WriteBytes (writeBytes)

/-! ## The chain of comparisons -/

/-- The code chosen by the step's number `j` in `stp`: `cs[j - i]`. -/
theorem sel_ok (cs : List (List Instr)) (i : Nat) {s : State} {j : Nat} (hij : i ≤ j) (hj : j < i + cs.length)
    (hlen : i + cs.length ≤ 2048) (h2 : s.gpr stp = BitVec.ofNat 64 j) {Q : State → Prop}
    (hQ : ∀ u : State, Keep [tmp] s u → u.mem = s.mem → WP isa (.block (cs.getD (j - i) [])) u Q) :
    WP isa (sel cs i) s Q := by
  induction cs generalizing i s with
  | nil => simp at hj; omega_arith
  | cons c cs ih =>
    unfold sel
    simp only [List.length_cons] at hj hlen
    refine WP.seq (wp_subi (imm := i) (by omega_arith) fun u hu => WP.block_nil ?_)
    have uk : Keep [tmp] s u := ⟨fun r hr => hu.other r (by simpa using hr), hu.rd, hu.wr⟩
    have ev : isa.eval (.zero tmp) u = some (decide (j = i)) := by
      rw [eval_zero, hu.gpr, h2]
      congr 1
      by_cases e : j = i
      · subst e; simp
      · rw [decide_eq_false e]
        have : BitVec.ofNat 64 j - BitVec.ofNat 64 i ≠ 0 := fun h0 => e (by
          have := congrArg BitVec.toNat h0
          rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
          simp at this; omega_arith)
        simpa using this
    by_cases e : j = i
    · subst e
      refine WP.ite true (by rw [ev, decide_eq_true rfl]) (fun _ => ?_) (fun h => absurd h (by decide))
      have := hQ u uk hu.mem
      rwa [Nat.sub_self, List.getD_cons_zero] at this
    · refine WP.ite false (by rw [ev, decide_eq_false e]) (fun h => absurd h (by decide)) (fun _ => ?_)
      refine ih (i + 1) (by omega_arith) (by omega_arith) (by omega_arith) (by rw [hu.other _ (by decide), h2])
        fun v vk vm => ?_
      have := hQ v ((uk.trans vk).mono (by decide)) (vm.trans hu.mem)
      rwa [show j - i = (j - (i + 1)) + 1 by omega_arith, List.getD_cons_succ] at this

/-! ## The state of key expansion -/

/-- The registers a step writes. -/
def stepRegs : List Reg := [tmp, wd, .t2, ep, .s4, .s5, .s6, .s7, .s0, .s1, .s2, .s3, vI, vKr, msk, stp]

/-- The state of key expansion from the memory `m0`: the working space,
rounded up to a multiple of 8, at `cb` in `wkK` (its first 152 bytes, which
the code uses, writable), the schedule at `kb`, the arrays, subkeys and
extra lookups of `k` in memory; and the table `VG_CAST5_S5678` at `T` in
`tbl`, readable, 64-byte aligned, held in `m0` and apart from the working
space's first 64 bytes and the schedule. -/
structure KS (m0 : Mem) (cb kb T : Addr) (s : State) (k : KSt) : Prop where
  wk : s.gpr wkK = cb
  mem : KMem m0 s.mem cb kb k.xz k.ws
  ex : ∀ i < 4, s.mem.readW (cb + BitVec.ofNat 64 (extraOff + 4 * i)) 32 = k.ex i
  len : k.ws.length ≤ 32
  al : cb.toNat % 8 = 0
  cfit : cb.toNat + 152 ≤ 2 ^ 64
  kfit : kb.toNat + 128 ≤ 2 ^ 64
  scr : ∀ {off w : Nat}, off + w ≤ 152 → InRegions s.wr (cb + BitVec.ofNat 64 off) w
  sch : (⟨kb, 128⟩ : Region) ∈ s.wr
  dKS : Region.Disjoint ⟨kb, 128⟩ ⟨cb, 152⟩
  tblR : s.gpr tbl = T
  trd : (⟨T, 4096⟩ : Region) ∈ s.rd ++ s.wr
  tal : T.toNat % 64 = 0
  held0 : Held m0 T s5678
  dTS : Region.Disjoint ⟨T, 4096⟩ ⟨cb, 64⟩
  dTK : Region.Disjoint ⟨T, 4096⟩ ⟨kb, 128⟩

theorem s5678_len : 8 * s5678.length = 4096 := by rw [s5678, table_length]

section
variable {m0 : Mem} {cb kb T : Addr} {s : State} {k : KSt} (h : KS m0 cb kb T s k)
include h

theorem KS.inS {off w : Nat} (hw : off + w ≤ 152) : InRegions s.wr (cb + BitVec.ofNat 64 off) w :=
  h.scr hw

theorem KS.inS' {off w : Nat} (hw : off + w ≤ 152) : InRegions (s.rd ++ s.wr) (cb + BitVec.ofNat 64 off) w :=
  let ⟨r, hr, hc⟩ := h.scr hw; ⟨r, List.mem_append_right _ hr, hc⟩

theorem KS.dKS64 : Region.Disjoint ⟨kb, 128⟩ ⟨cb, 64⟩ :=
  h.dKS.sub_right (Region.sub_prefix (by decide))

/-- A word of the working space at an offset that is a multiple of 4 is aligned. -/
theorem KS.al4 {off : Nat} (ho : off % 4 = 0) : (cb + BitVec.ofNat 64 off).toNat % 4 = 0 :=
  Align.al_add h.al (by decide) ho

/-- The same state, later: other registers and memory. -/
theorem KS.update {u : State} {k' : KSt} {rs : List Reg} (hk : Keep rs s u)
    (hm : KMem m0 u.mem cb kb k'.xz k'.ws)
    (he : ∀ i < 4, u.mem.readW (cb + BitVec.ofNat 64 (extraOff + 4 * i)) 32 = k'.ex i)
    (hl : k'.ws.length ≤ 32) (hrs : wkK ∉ rs ∧ tbl ∉ rs := by decide) : KS m0 cb kb T u k' :=
  ⟨(hk.gpr hrs.1).trans h.wk, hm, he, hl, h.al, h.cfit, h.kfit, fun hw => by rw [hk.2.2]; exact h.scr hw,
    by rw [hk.2.2]; exact h.sch, h.dKS, (hk.gpr hrs.2).trans h.tblR,
    by rw [hk.2.1, hk.2.2]; exact h.trd, h.tal, h.held0, h.dTS, h.dTK⟩

/-- The table, still held. -/
theorem KS.held : Held s.mem T s5678 := by
  refine held_frame h.mem.fr (fun r hr => ?_) (by rw [s5678_len]; decide) h.held0
  rw [s5678_len]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.dTS
  · exact h.dTK

end

theorem srcOff_lt {q : Pos} (hq : q.2 < 16) : srcOff q + 1 ≤ 48 := by
  obtain ⟨a, i⟩ := q
  have := off_lt a
  simp only [srcOff] at hq ⊢
  omega_arith

/-! ## Gathering the bytes -/

theorem gather_ok {m0 : Mem} {cb kb T : Addr} {s : State} {k : KSt} (h : KS m0 cb kb T s k)
    {a b c d : Pos} (ha : a.2 < 16) (hb : b.2 < 16) (hc : c.2 < 16) (hd : d.2 < 16) :
    WP isa (.block (gather a b c d)) s fun u =>
      u.gpr .s0 = (k.xz.get d).setWidth 64 ∧ u.gpr .s1 = (k.xz.get c).setWidth 64 ∧
      u.gpr .s2 = (k.xz.get b).setWidth 64 ∧ u.gpr .s3 = (k.xz.get a).setWidth 64 ∧
      Keep [.s0, .s1, .s2, .s3] s u ∧ u.mem = s.mem := by
  have ia := h.inS' (off := srcOff a) (w := 1) (by have := srcOff_lt ha; omega_arith)
  have ib := h.inS' (off := srcOff b) (w := 1) (by have := srcOff_lt hb; omega_arith)
  have ic := h.inS' (off := srcOff c) (w := 1) (by have := srcOff_lt hc; omega_arith)
  have id := h.inS' (off := srcOff d) (w := 1) (by have := srcOff_lt hd; omega_arith)
  have xa := h.mem.xz.pos ha
  have xb := h.mem.xz.pos hb
  have xc := h.mem.xz.pos hc
  have xd := h.mem.xz.pos hd
  have oa : srcOff a < 2048 := by have := srcOff_lt ha; omega_arith
  have ob : srcOff b < 2048 := by have := srcOff_lt hb; omega_arith
  have oc : srcOff c < 2048 := by have := srcOff_lt hc; omega_arith
  have od : srcOff d < 2048 := by have := srcOff_lt hd; omega_arith
  have hw := h.wk
  unfold gather
  refine wp_lbu od (by rw [hw]) id fun u₁ h₁ => wp_lbu oc (by rw [h₁.other _ (by decide), hw])
    (by rw [h₁.rd, h₁.wr]; exact ic) fun u₂ h₂ => wp_lbu ob (by rw [h₂.other _ (by decide),
      h₁.other _ (by decide), hw]) (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact ib) fun u₃ h₃ =>
    wp_lbu oa (by rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide), hw])
      (by rw [h₃.rd, h₃.wr, h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact ia) fun u₄ h₄ => WP.block_nil ?_
  have m₃ : u₃.mem = s.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  have m₂ : u₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  refine ⟨?_, ?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), show u₁.gpr .s0 = _ from h₁.gpr, xd]
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), show u₂.gpr .s1 = _ from h₂.gpr, h₁.mem, xc]
  · rw [h₄.other _ (by decide), show u₃.gpr .s2 = _ from h₃.gpr, m₂, xb]
  · rw [show u₄.gpr .s3 = _ from h₄.gpr, m₃, xa]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [h₄.other _ hr.2.2.2, h₃.other _ hr.2.2.1, h₂.other _ hr.2.1, h₁.other _ hr.1]
  · rw [h₄.rd, h₃.rd, h₂.rd, h₁.rd]
  · rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr]
  · rw [h₄.mem, m₃]

/-! ## What a step does with the values -/

theorem ex_off {i : Nat} (hi : i < 4) : extraOff + 4 * i + 4 ≤ 64 := by unfold extraOff; omega_arith

/-- The extra lookups of a group to their slots. -/
theorem postE_ok {m0 : Mem} {cb kb T : Addr} {u : State} {k : KSt} (h : KS m0 cb kb T u k) (a b c d : Pos)
    (v : Nat → Spec.Cast5.Word) (hv : ∀ i < 4, lo (u.gpr (accReg i)) = v i) :
    WP isa (.block (Step.extras a b c d).post) u fun w =>
      KS m0 cb kb T w { k with ex := v } ∧ Keep [] u w := by
  have v0 : (u.gpr .s4).setWidth 32 = v 0 := hv 0 (by decide)
  have v1 : (u.gpr .s5).setWidth 32 = v 1 := hv 1 (by decide)
  have v2 : (u.gpr .s6).setWidth 32 = v 2 := hv 2 (by decide)
  have v3 : (u.gpr .s7).setWidth 32 = v 3 := hv 3 (by decide)
  have hw := h.wk
  have dKS := h.dKS64
  have hl := h.len
  simp only [Step.post]
  unfold extraOff
  refine wp_sw (a := cb + BitVec.ofNat 64 48) (by decide) (by rw [hw]) (h.al4 (by decide)) (h.inS (by decide))
    fun u₁ h₁ => ?_
  refine wp_sw (a := cb + BitVec.ofNat 64 52) (by decide) (by rw [h₁.gpr, hw]) (h.al4 (by decide))
    (by rw [h₁.wr]; exact h.inS (by decide)) fun u₂ h₂ => ?_
  refine wp_sw (a := cb + BitVec.ofNat 64 56) (by decide) (by rw [h₂.gpr, h₁.gpr, hw]) (h.al4 (by decide))
    (by rw [h₂.wr, h₁.wr]; exact h.inS (by decide)) fun u₃ h₃ => ?_
  refine wp_sw (a := cb + BitVec.ofNat 64 60) (by decide) (by rw [h₃.gpr, h₂.gpr, h₁.gpr, hw])
    (h.al4 (by decide)) (by rw [h₃.wr, h₂.wr, h₁.wr]; exact h.inS (by decide)) fun u₄ h₄ => WP.block_nil ?_
  have g : u₄.gpr = u.gpr := by rw [h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr]
  have hm : u₄.mem = (((u.mem.writeW (cb + BitVec.ofNat 64 48) (v 0)).writeW (cb + BitVec.ofNat 64 52) (v 1)).writeW
      (cb + BitVec.ofNat 64 56) (v 2)).writeW (cb + BitVec.ofNat 64 60) (v 3) := by
    rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
    simp only [h₃.gpr, h₂.gpr, h₁.gpr, accReg_0, accReg_1, accReg_2, accReg_3, v0, v1, v2, v3]
  have hk : Keep [] u u₄ := ⟨fun r _ => by rw [g], by rw [h₄.rd, h₃.rd, h₂.rd, h₁.rd],
    by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr]⟩
  refine ⟨h.update hk ?_ (fun i hi => ?_) hl, hk⟩
  · rw [hm]
    exact (((h.mem.write dKS hl _ (by decide) (by decide)).write dKS hl _ (by decide) (by decide)).write dKS hl _
      (by decide) (by decide)).write dKS hl _ (by decide) (by decide)
  · rw [hm]
    simp only [extraOff]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceMul, Nat.reduceAdd] <;>
    repeat (first
      | rw [Mem.readW_writeW_self32]
      | rw [Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)])

/-- The XORs of a line's lookups and its extra lookup, into `vI`. -/
theorem lineHead_ok {m0 : Mem} {cb kb T : Addr} {u : State} {k : KSt} (h : KS m0 cb kb T u k) {e : Nat}
    (he : 5 ≤ e ∧ e ≤ 8) :
    WP isa (.block [.logic .xor vI (accReg 0) (accReg 1), .logic .xor vI vI (accReg 2),
      .logic .xor vI vI (accReg 3), .load .w tmp wkK (extraOff + 4 * (8 - e)), .logic .xor vI vI tmp]) u fun w =>
      lo (w.gpr vI) = lo (u.gpr .s4) ^^^ lo (u.gpr .s5) ^^^ lo (u.gpr .s6) ^^^ lo (u.gpr .s7) ^^^
        k.ex (8 - e) ∧ Keep [vI, tmp] u w ∧ w.mem = u.mem := by
  have ho : extraOff + 4 * (8 - e) < 2048 := by unfold extraOff; omega_arith
  have hin := h.inS' (off := extraOff + 4 * (8 - e)) (w := 4) (by unfold extraOff; omega_arith)
  have hal := h.al4 (off := extraOff + 4 * (8 - e)) (by unfold extraOff; omega_arith)
  have hx := h.ex (8 - e) (by omega_arith)
  have hw := h.wk
  c5run [↓read_four, hw, hin, hx, ho, hal]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · simp only [lo_xor, lo_ext]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2, ite_false]

/-- The quadruple a line XORs in, if any. -/
def wordCode : Option (Arr × Nat) → List Instr
  | some (a, q) => Impl.Words.RISCV64.loadBE32 tmp wd wkK (off a + 4 * q) ++ [.logic .xor vI vI tmp]
  | none => []

/-- `v` with the quadruple `wd` of the arrays XORed in, if any. -/
def withQuad (xz : XZ) (v : Spec.Cast5.Word) : Option (Arr × Nat) → Spec.Cast5.Word
  | some (a, q) => v ^^^ quadOf (xz.arr a) q
  | none => v

/-- A quadruple of `x` or `z`, read big-endian a byte at a time. -/
theorem holdsXZ_beWord {m : Mem} {p : Addr} {st : XZ} (h : HoldsXZ m p st) (a : Arr) {q : Nat} (hq : q < 4) :
    ByteLoad.beWord m p (off a + 4 * q) = quadOf (st.arr a) q := by
  rw [ByteLoad.beWord, quadOf, show off a + 4 * q + 1 = off a + (4 * q + 1) by omega,
    show off a + 4 * q + 2 = off a + (4 * q + 2) by omega, show off a + 4 * q + 3 = off a + (4 * q + 3) by omega,
    h a _ (by omega), h a _ (by omega), h a _ (by omega), h a _ (by omega)]

theorem wordCode_ok {m0 : Mem} {cb kb T : Addr} {u : State} {k : KSt} (h : KS m0 cb kb T u k)
    (w : Option (Arr × Nat)) (hq : ∀ a q, w = some (a, q) → q < 4) :
    WP isa (.block (wordCode w)) u fun v =>
      lo (v.gpr vI) = withQuad k.xz (lo (u.gpr vI)) w ∧ Keep [vI, tmp, wd] u v ∧ v.mem = u.mem := by
  cases w with
  | none => exact WP.block_nil ⟨rfl, Keep.refl _ _, rfl⟩
  | some aq =>
    obtain ⟨a, q⟩ := aq
    have hq4 := hq a q rfl
    have := off_lt a
    have hin := h.inS' (off := off a + 4 * q) (w := 4) (by omega_arith)
    have hx := holdsXZ_beWord h.mem.xz a hq4
    have hw := h.wk
    unfold wordCode
    rw [WP.block_append_iff]
    refine WP.mono (ByteLoad.loadBE32_ok (d := tmp) (tmp := wd) (n := wkK) (off := off a + 4 * q) (by decide)
      (by decide) (by decide) (by omega_arith) (by rw [hw]; exact hin)) fun v e => ?_
    subst e
    refine wp_xor fun v₁ h₁ => WP.block_nil ?_
    refine ⟨?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
    · rw [h₁.gpr]
      simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, lo_xor, lo_ext, hw, hx,
        withQuad]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [h₁.other _ hr.1]
      simp only [RegUpd.gpr_write, hr.2.1, hr.2.2, ite_false]
    · rw [h₁.rd]; rfl
    · rw [h₁.wr]; rfl
    · rw [h₁.mem]; rfl

/-- A word stored big-endian a byte at a time is PPC64LE's byte-reversed
store of its low word. -/
theorem writeBytes_beBytes (m : Mem) (a : Addr) (x : BitVec 64) :
    writeBytes m a (ByteLoad.beBytes 4 x) = m.writeW a (byteRev32 (lo x)) := by
  funext y
  simp only [writeBytes, Mem.writeW, Mem.write, ByteLoad.beBytes_length]
  split
  · rename_i hy
    rw [List.getD_eq_getElem?_getD]
    simp only [ByteLoad.beBytes, List.getElem?_map, List.getElem?_range hy, Option.map_some, Option.getD_some,
      BitVec.setWidth_eq]
    rw [Proof.Cast5.byteRev32_byte _ hy, shr_lo _ (by omega)]
  · rfl

/-- Where a line's value goes. -/
def storeCode : Store → List Instr
  | .quad a q => Impl.Words.RISCV64.storeBE 4 vI wd wkK (off a + 4 * q)
  | .key k => Impl.Words.RISCV64.storeLE32 vI tmp out (4 * k)

theorem post_line (l : Impl.Cast5.Line) (st : Store) :
    (Step.line l st).post = ([.logic .xor vI (accReg 0) (accReg 1), .logic .xor vI vI (accReg 2),
      .logic .xor vI vI (accReg 3), .load .w tmp wkK (extraOff + 4 * (8 - l.extra.1)),
      .logic .xor vI vI tmp] : List Instr) ++ wordCode l.word ++ storeCode st := by
  obtain ⟨main, extra, word⟩ := l
  rcases word with _ | ⟨a, q⟩ <;> cases st <;> rfl

theorem storeQuad_ok {m0 : Mem} {cb kb T : Addr} {u : State} {k : KSt} (h : KS m0 cb kb T u k) (a : Arr)
    {q : Nat} (hq : q < 4) {v : Spec.Cast5.Word} (h0 : lo (u.gpr vI) = v) :
    WP isa (.block (storeCode (.quad a q))) u fun w =>
      KS m0 cb kb T w { k with xz := k.xz.put a q v } ∧ Keep [wd] u w := by
  have := off_lt a
  have := off_ge a
  have hw := h.wk
  unfold storeCode
  refine WP.mono (ByteLoad.storeBE_ok (v := vI) (tmp := wd) (n := wkK) (off := off a + 4 * q) (w := 4)
    (by decide) (by decide) (by decide) (by decide) (by omega_arith) fun j hj => by
      rw [hw]; exact h.inS (by omega_arith)) fun w e => ?_
  subst e
  have hm : ({ u with mem := (writeBytes u.mem (u.gpr wkK + BitVec.ofNat 64 (off a + 4 * q))
      (ByteLoad.beBytes 4 (u.gpr vI))) } : State).mem =
      u.mem.writeW (cb + BitVec.ofNat 64 (off a + 4 * q)) (byteRev32 v) := by
    show writeBytes _ _ _ = _
    rw [writeBytes_beBytes, hw, h0]
  refine ⟨h.update (rs := [wd]) ⟨fun r hr => ?_, rfl, rfl⟩ ?_ (fun i hi => ?_) h.len, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · simp only [List.mem_singleton] at hr; simp only [RegUpd.gpr_write, hr, ite_false]
  · rw [RegUpd.mem_write, hm]
    exact h.mem.quad h.dKS64 h.len a hq v
  · rw [RegUpd.mem_write, hm, Mem.readW_writeW_sep (Offset.sep _ (d := extraOff + 4 * i) (n := 32 / 8)
      (e := off a + 4 * q) (k := 32 / 8) (by unfold extraOff; omega_arith) (by unfold extraOff; omega_arith)
      (by omega_arith)) (by decide)]
    exact h.ex i hi
  · simp only [List.mem_singleton] at hr; simp only [RegUpd.gpr_write, hr, ite_false]

theorem storeKey_ok {m0 : Mem} {cb kb T : Addr} {u : State} {k : KSt} (h : KS m0 cb kb T u k) {j hh : Nat}
    (hj : j < 16) (hout : u.gpr out = kb + BitVec.ofNat 64 (64 * hh)) (hlen : k.ws.length = 16 * hh + j)
    (hl : k.ws.length < 32) {v : Spec.Cast5.Word} (h0 : lo (u.gpr vI) = v) :
    WP isa (.block (storeCode (.key j))) u fun w =>
      KS m0 cb kb T w { k with ws := k.ws ++ [v] } ∧ Keep [tmp] u w := by
  have hkf := h.kfit
  have ea : u.gpr out + BitVec.ofNat 64 (4 * j) = kb + BitVec.ofNat 64 (4 * k.ws.length) := by
    rw [hout, Offset.add_add, hlen]; congr 2; omega_arith
  have hin : InRegions u.wr (u.gpr out + BitVec.ofNat 64 (4 * j)) 4 :=
    ea ▸ ⟨_, h.sch, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  unfold storeCode
  refine WP.mono (ByteLoad.storeLE32_ok (v := vI) (tmp := tmp) (n := out) (off := 4 * j) (by decide) (by decide)
    (by omega_arith) hin) fun w e => ?_
  subst e
  have hm : (({ u with mem := (u.mem.writeW (u.gpr out + BitVec.ofNat 64 (4 * j)) ((u.gpr vI).setWidth 32)) } :
      State).write tmp (u.gpr vI >>> 24)).mem = u.mem.writeW (kb + BitVec.ofNat 64 (4 * k.ws.length)) v := by
    rw [RegUpd.mem_write]; show Mem.writeW _ _ _ = _; rw [ea]; exact congrArg _ h0
  have hk : Keep [tmp] u (({ u with mem := (u.mem.writeW (u.gpr out + BitVec.ofNat 64 (4 * j))
      ((u.gpr vI).setWidth 32)) } : State).write tmp (u.gpr vI >>> 24)) :=
    ⟨fun r hr => by simp only [List.mem_singleton] at hr; simp only [RegUpd.gpr_write, hr, ite_false],
      rfl, rfl⟩
  refine ⟨h.update hk (by rw [hm]; exact h.mem.key h.dKS64 hl v) (fun i hi => ?_) (by simp; omega_arith), hk⟩
  rw [hm, Mem.readW_writeW_sep (h.dKS.symm.sep (Offset.contains_base _ (by have := ex_off hi; omega_arith)
      (by unfold extraOff; omega_arith))
    (Offset.contains_base _ (by omega_arith) (by omega_arith))) (by decide)]
  exact h.ex i hi

/-- What a step needs to be run by the code: bytes of `x` and `z`, a line
`lineOk`, a quadruple of four, a subkey of the half's sixteen. -/
def stepOk : Step → Bool
  | .extras a b c d => a.2 < 16 && b.2 < 16 && c.2 < 16 && d.2 < 16
  | .line l (.quad _ q) => lineOk l && q < 4
  | .line l (.key j) => lineOk l && j < 16

/-- A line, after the scan of its bytes: its value, then its store. -/
theorem postL_ok {m0 : Mem} {cb kb T : Addr} {u : State} {k : KSt} (h : KS m0 cb kb T u k)
    {l : Impl.Cast5.Line} {st : Store} (hok : stepOk (.line l st) = true)
    (h8 : lo (u.gpr .s4) = Spec.Cast5.S8 (k.xz.get l.main.2.2.2))
    (h9 : lo (u.gpr .s5) = Spec.Cast5.S7 (k.xz.get l.main.2.2.1))
    (h10 : lo (u.gpr .s6) = Spec.Cast5.S6 (k.xz.get l.main.2.1))
    (h11 : lo (u.gpr .s7) = Spec.Cast5.S5 (k.xz.get l.main.1))
    {hh : Nat} (hout : u.gpr out = kb + BitVec.ofNat 64 (64 * hh))
    (hkey : ∀ j, st = .key j → k.ws.length = 16 * hh + j ∧ k.ws.length < 32) :
    WP isa (.block (Step.line l st).post) u fun w =>
      KS m0 cb kb T w (stepRun (.line l st) k) ∧ Keep [vI, tmp, wd] u w := by
  have hl : lineOk l = true := by cases st <;> simp only [stepOk, Bool.and_eq_true] at hok <;> exact hok.1
  have he := hl
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at he
  have hq : ∀ a q, l.word = some (a, q) → q < 4 := by
    intro a q hw
    have := he.2
    rw [hw] at this
    simpa using this
  rw [post_line, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (lineHead_ok h ⟨he.1.1.2, he.1.2⟩) fun v ⟨v0, vk, vm⟩ => ?_
  have hv : KS m0 cb kb T v k := h.update vk (by rw [vm]; exact h.mem)
    (fun i hi => by rw [vm]; exact h.ex i hi) h.len
  refine WP.mono (wordCode_ok hv l.word hq) fun w ⟨w0, wk, wm⟩ => ?_
  have hw : KS m0 cb kb T w k := hv.update wk (by rw [wm]; exact hv.mem)
    (fun i hi => by rw [wm]; exact hv.ex i hi) hv.len
  have wv : lo (w.gpr vI) = lineE k.xz k.ex l := by
    rw [w0, v0, h8, h9, h10, h11]
    unfold lineE
    clear hq he hok hl hkey h8 h9 h10 h11
    obtain ⟨main, extra, word⟩ := l
    rcases word with _ | ⟨a, q⟩ <;> rfl
  have kuw := vk.trans wk
  cases st with
  | quad a q =>
    have hq4 : q < 4 := by simp only [stepOk, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.2
    exact WP.mono (storeQuad_ok hw a hq4 wv) fun x ⟨hx, xk⟩ => ⟨hx, (kuw.trans xk).mono (by decide)⟩
  | key j =>
    have hj : j < 16 := by simp only [stepOk, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.2
    obtain ⟨hlen, hl32⟩ := hkey j rfl
    exact WP.mono (storeKey_ok hw hj (by rw [kuw.gpr (by decide)]; exact hout) hlen hl32 wv)
      fun x ⟨hx, xk⟩ => ⟨hx, (kuw.trans xk).mono (by decide)⟩

end VG.Proof.Cast5.RISCV64
