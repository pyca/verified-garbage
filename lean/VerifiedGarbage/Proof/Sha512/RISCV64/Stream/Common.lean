module

public import VerifiedGarbage.Impl.Sha512.RISCV64.Stream
public import VerifiedGarbage.Proof.Sha512.RISCV64.Contract
public import VerifiedGarbage.Proof.Sha512.Stream
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Sha512.RISCV64.Compress
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.TCB.RISCV64.Isa
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad

/-!
# Streaming SHA-512 on RISC-V: common lemmas

Untrusted: everything here is checked by Lean. Weakest-precondition rules for
the instruction forms used, the call of the compression function
(`compressAt`), and saving and restoring our caller's registers in the
frame. The structure of SHA-256's proof
(`Proof/Sha256/RISCV64/Stream/Common.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha512.RISCV64.Stream

open VG VG.RISCV64 VG.Impl.Sha512.RISCV64.Stream
open VG.Proof.Sha512.RISCV64 (compress_verified)
open VG.Spec.Sha512 (HashValue stateAt blockAt compressBlocks compress parseBlock bytesAt)

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v`. -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd.write (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.write d v) d v :=
  ⟨RegUpd.gpr_write_self _ _ _, fun _ h => RegUpd.gpr_write_of_ne _ _ h, rfl, rfl, rfl, rfl⟩

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

theorem ofInt_ofNat (imm : Nat) : BitVec.ofInt 64 (imm : Int) = BitVec.ofNat 64 imm := by
  simp

theorem add_ofInt_neg (x : BitVec 64) (imm : Nat) :
    x + BitVec.ofInt 64 (-(imm : Int)) = x - BitVec.ofNat 64 imm := by
  rw [BitVec.ofInt_neg, ofInt_ofNat, ← BitVec.sub_eq_add_neg]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_addi {d n : Reg} {imm : Nat} (h : imm < 2048)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n (imm : Int) :: is)) s Q := by
  refine WP.cons (exec_addi (by unfold imm12; omega)) ?_
  rw [ofInt_ofNat]; exact k _ (Upd.write _ _ _)

theorem wp_mov {d n : Reg} (k : ∀ s', Upd s s' d (s.gpr n) → WP isa (.block is) s' Q) :
    WP isa (.block (mov d n :: is)) s Q :=
  wp_addi (imm := 0) (by decide) fun s' u => k s' (by simpa using u)

theorem wp_subi {d n : Reg} {imm : Nat} (h : imm ≤ 2048)
    (k : ∀ s', Upd s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n (-(imm : Int)) :: is)) s Q := by
  refine WP.cons (exec_addi (by unfold imm12; omega)) ?_
  rw [add_ofInt_neg]; exact k _ (Upd.write _ _ _)

theorem wp_li {d : Reg} {imm : Nat} (h : imm < 2048)
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.li d (imm : Int) :: is)) s Q := by
  refine WP.cons (exec_li (by unfold imm12; omega)) ?_
  rw [ofInt_ofNat]; exact k _ (Upd.write _ _ _)

theorem wp_add {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add d n m :: is)) s Q :=
  WP.cons exec_add (k _ (Upd.write _ _ _))

theorem wp_sub {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n - s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.sub d n m :: is)) s Q :=
  WP.cons exec_sub (k _ (Upd.write _ _ _))

/-- `x &&& 127`. -/
theorem and127 (x : BitVec 64) : x &&& BitVec.ofInt 64 127 = BitVec.ofNat 64 (x.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 127).toNat = 2 ^ 7 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  omega

theorem wp_andi127 {d n : Reg}
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 ((s.gpr n).toNat % 128)) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .and d n 127 :: is)) s Q := by
  refine WP.cons (exec_logicImm (by decide)) ?_
  simp only
  rw [and127]; exact k _ (Upd.write _ _ _)

theorem wp_srl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .srl .d d n sh :: is)) s Q :=
  WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

theorem wp_sll {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .sll .d d n sh :: is)) s Q :=
  WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

theorem wp_addSp {d : Reg} {imm : Nat} (h : imm < 2048)
    (k : ∀ s', Upd s s' d (s.sp + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addSp d imm :: is)) s Q :=
  WP.cons (exec_addSp h) (k _ (Upd.write _ _ _))

theorem wp_lbu {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .b t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem a).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_b ho (by rw [ha]; exact hin), ha, ByteLoad.read_one]

theorem wp_sb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .b t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_b ho (by rw [ha]; exact hout), ha]
  rfl

theorem wp_sd {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hal : a.toNat % 8 = 0) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_d ho (by rw [ha]; exact hal) (by rw [ha]; exact hout), ha]

theorem wp_ld {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hal : a.toNat % 8 = 0)
    (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t (s.mem.readW a 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_d ho (by rw [ha]; exact hal) (by rw [ha]; exact hin), ha]

end

/-- `eval` of the branch conditions. -/
theorem eval_zero (s : State) (r : Reg) : eval (.zero r) s = some (s.gpr r == 0) := rfl

theorem eval_nonzero (s : State) (r : Reg) : eval (.nonzero r) s = some (s.gpr r != 0) := rfl

/-! ## The called compression function -/

theorem compressBlocks_one (H : HashValue) (m : Mem) (p : Addr) :
    compressBlocks H m p 1 = compress H (blockAt m p) := by
  simp [compressBlocks]

theorem one_toNat : (BitVec.ofNat 64 1).toNat = 1 := rfl

theorem compress_noFrames : Impl.Sha512.RISCV64.compress.noFrames = true := by decide +kernel

/-- Compressing the block at `a1` into the hash value at `s1`, with scratch
space at `s2`: the callee-saved registers are kept. -/
theorem compressAt_ok {s : State} {st scr src : Addr}
    (h1 : s.gpr .s1 = st) (h2 : s.gpr .s2 = scr) (ha1 : s.gpr .a1 = src)
    (d₁ : Region.Disjoint ⟨st, 64⟩ ⟨scr, 144⟩) (d₂ : Region.Disjoint ⟨src, 128⟩ ⟨st, 64⟩)
    (d₃ : Region.Disjoint ⟨src, 128⟩ ⟨scr, 144⟩)
    (hc : Covers [⟨src, 128⟩, ⟨st, 64⟩, ⟨scr, 144⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, 64⟩, ⟨scr, 144⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨st, 64⟩, ⟨scr, 144⟩] s.mem s'.mem →
      stateAt s'.mem st = compress (stateAt s.mem st) (blockAt s.mem src) → Q s') :
    WP isa compressAt s Q := by
  unfold compressAt
  refine WP.seq (wp_mov fun s₁ u₁ => wp_li (imm := 1) (by decide) fun s₂ u₂ =>
    wp_mov fun s₃ u₃ => WP.block_nil ?_)
  have e0 : s₃.gpr .a0 = st := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h1]
  have e1 : s₃.gpr .a1 = src := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ha1]
  have e2 : s₃.gpr .a2 = BitVec.ofNat 64 1 := by
    rw [u₃.other _ (by decide), u₂.gpr]
  have e3 : s₃.gpr .a3 = scr := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h2]
  have keep : ∀ r ∈ preserved, s₃.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .a0 ∧ r ≠ .a2 ∧ r ≠ .a3 := by
      revert r; decide
    rw [u₃.other _ this.2.2, u₂.other _ this.2.1, u₁.other _ this.1]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have sp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  have c0 : s₃.callEntry.gpr .a0 = st := (State.callEntry_gpr _ (by decide)).trans e0
  have c1 : s₃.callEntry.gpr .a1 = src := (State.callEntry_gpr _ (by decide)).trans e1
  have c2 : s₃.callEntry.gpr .a2 = BitVec.ofNat 64 1 :=
    (State.callEntry_gpr _ (by decide)).trans e2
  have c3 : s₃.callEntry.gpr .a3 = scr := (State.callEntry_gpr _ (by decide)).trans e3
  refine WP.call (k := Proof.Sha512.compressRISCV64) compress_verified.1
    (rd := [⟨src, 128 * 1⟩]) (wr := [⟨st, 64⟩, ⟨scr, 144⟩]) ?_ ?_ ?_ ?_ compress_noFrames
  · simp only [Proof.Sha512.compressRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1, c2, c3, one_toNat]
    exact ⟨trivial, trivial, d₁, d₂, d₃⟩
  · rw [rd₃, wr₃]; simpa using hc
  · rw [wr₃]; exact hw
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [Proof.Sha512.compressRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, one_toNat, compressBlocks_one, m₃] at hpost
    exact hQ s' (hrd.trans rd₃) (hwr.trans wr₃) (fun r hr => (hcs r hr).trans (keep r hr))
      (hsp.trans sp₃) (m₃ ▸ hf) hpost

/-! ## Arithmetic -/

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
  rw [BitVec.ofNat_add]; rfl

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  conv_lhs => rw [show a = (a - b) + b by omega, BitVec.ofNat_add]
  rw [BitVec.add_sub_cancel]

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    change _ = 0 at this
    omega

/-- `x >>> 7`, of a number below 2⁶⁴. -/
theorem ofNat_shr7 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 7 = BitVec.ofNat 64 (a / 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem bytesAt_getD {m : Mem} {p : Addr} {n : Nat} {l : List Byte} (h : bytesAt m p n = l) {k : Nat}
    (hk : k < n) : m (p + BitVec.ofNat 64 k) = l.getD k 0 := by
  subst h; simp [bytesAt, List.getD_eq_getElem?_getD, hk]

/-! ## Saving the caller's registers -/

/-- The memory after saving `ra` and `s1`–`s6` (values `g`) at `b + 144 … b + 192`. -/
def saveMem (m : Mem) (b : Addr) (g : Reg → BitVec 64) : Mem :=
  ((((((m.writeW (b + BitVec.ofNat 64 144) (g .ra)).writeW (b + BitVec.ofNat 64 152) (g .s1)).writeW
    (b + BitVec.ofNat 64 160) (g .s2)).writeW (b + BitVec.ofNat 64 168) (g .s3)).writeW
    (b + BitVec.ofNat 64 176) (g .s4)).writeW (b + BitVec.ofNat 64 184) (g .s5)).writeW
    (b + BitVec.ofNat 64 192) (g .s6)

theorem readW_writeW_save (m : Mem) (b : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 =
      m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep b h (by omega) (by omega)) (by decide)

theorem saveMem_saved (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    ∀ p ∈ saved, (saveMem m b g).readW (b + BitVec.ofNat 64 p.2) 64 = g p.1 := by
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [saveMem, Mem.readW_writeW_self64, readW_writeW_save, Nat.reduceAdd, Nat.reducePow,
    Nat.reduceLT, Nat.reduceLeDiff, true_or]

theorem saveMem_frame (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    Frame [⟨b, frameBytes⟩] m (saveMem m b g) := by
  have c : ∀ d : Nat, d + 8 ≤ 208 → (⟨b, frameBytes⟩ : Region).Contains (b + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => Offset.contains_base b (by simp only [frameBytes]; omega) (by omega)
  simp only [saveMem]
  exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 144 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 152 (by omega))).writeW (List.mem_singleton_self _) _
    (c 160 (by omega))).writeW (List.mem_singleton_self _) _ (c 168 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 176 (by omega))).writeW (List.mem_singleton_self _) _
    (c 184 (by omega)) |>.writeW (List.mem_singleton_self _) _ (c 192 (by omega))

theorem save_eq : save = [.addSp .t0 0, .store .d .ra .t0 144, .store .d .s1 .t0 152,
    .store .d .s2 .t0 160, .store .d .s3 .t0 168, .store .d .s4 .t0 176, .store .d .s5 .t0 184,
    .store .d .s6 .t0 192] := rfl

/-- An 8-byte aligned offset of a 16-byte aligned frame. -/
theorem frame_al {b : Addr} (hb : b.toNat % 16 = 0) {d : Nat} (hd : d % 8 = 0) (hd' : d < 2 ^ 32) :
    (b + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega)]
  have := b.isLt
  omega

/-- Saving `ra` and `s1`–`s6` in the frame at the stack pointer, whose
address is left in `t0`. -/
theorem save_ok {rest : List Instr} {s : State} {Q : State → Prop} (hal : s.sp.toNat % 16 = 0)
    (hin : ∀ d, 144 ≤ d → d + 8 ≤ 208 → InRegions s.wr (s.sp + BitVec.ofNat 64 d) 8)
    (k : ∀ s', s'.gpr .t0 = s.sp → (∀ r, r ≠ .t0 → s'.gpr r = s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → s'.sp = s.sp → s'.mem = saveMem s.mem s.sp s.gpr → WP isa (.block rest) s' Q) :
    WP isa (.block (save ++ rest)) s Q := by
  rw [save_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp (by decide) fun s₀ u₀ => ?_
  have g0 : s₀.gpr .t0 = s.sp := by rw [u₀.gpr]; exact BitVec.add_zero _
  have st : ∀ d, d % 8 = 0 → 144 ≤ d → d + 8 ≤ 208 → ∀ s' : State, s'.gpr .t0 = s.sp → s'.wr = s.wr →
      s'.gpr .t0 + BitVec.ofNat 64 d = s.sp + BitVec.ofNat 64 d ∧
      (s.sp + BitVec.ofNat 64 d).toNat % 8 = 0 ∧ InRegions s'.wr (s.sp + BitVec.ofNat 64 d) 8 :=
    fun d hd h₁ h₂ s' h₀ hw => ⟨by rw [h₀], frame_al hal hd (by omega), by rw [hw]; exact hin d h₁ h₂⟩
  have w0 : s₀.wr = s.wr := u₀.wr
  obtain ⟨a1, l1, i1⟩ := st 144 (by decide) (by omega) (by omega) s₀ g0 w0
  refine wp_sd (by decide) a1 l1 i1 fun s₁ g₁ => ?_
  have t1 : s₁.gpr .t0 = s.sp := by rw [g₁.gpr, g0]
  obtain ⟨a2, l2, i2⟩ := st 152 (by decide) (by omega) (by omega) s₁ t1 (by rw [g₁.wr, w0])
  refine wp_sd (by decide) a2 l2 i2 fun s₂ g₂ => ?_
  have t2 : s₂.gpr .t0 = s.sp := by rw [g₂.gpr, t1]
  obtain ⟨a3, l3, i3⟩ := st 160 (by decide) (by omega) (by omega) s₂ t2 (by rw [g₂.wr, g₁.wr, w0])
  refine wp_sd (by decide) a3 l3 i3 fun s₃ g₃ => ?_
  have t3 : s₃.gpr .t0 = s.sp := by rw [g₃.gpr, t2]
  obtain ⟨a4, l4, i4⟩ := st 168 (by decide) (by omega) (by omega) s₃ t3
    (by rw [g₃.wr, g₂.wr, g₁.wr, w0])
  refine wp_sd (by decide) a4 l4 i4 fun s₄ g₄ => ?_
  have t4 : s₄.gpr .t0 = s.sp := by rw [g₄.gpr, t3]
  obtain ⟨a5, l5, i5⟩ := st 176 (by decide) (by omega) (by omega) s₄ t4
    (by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr, w0])
  refine wp_sd (by decide) a5 l5 i5 fun s₅ g₅ => ?_
  have t5 : s₅.gpr .t0 = s.sp := by rw [g₅.gpr, t4]
  obtain ⟨a6, l6, i6⟩ := st 184 (by decide) (by omega) (by omega) s₅ t5
    (by rw [g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr, w0])
  refine wp_sd (by decide) a6 l6 i6 fun s₆ g₆ => ?_
  have t6 : s₆.gpr .t0 = s.sp := by rw [g₆.gpr, t5]
  obtain ⟨a7, l7, i7⟩ := st 192 (by decide) (by omega) (by omega) s₆ t6
    (by rw [g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr, w0])
  refine wp_sd (by decide) a7 l7 i7 fun s₇ g₇ => ?_
  have gg : s₇.gpr = s₀.gpr := by rw [g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr]
  refine k s₇ (by rw [gg, g0]) (fun r hr => by rw [gg, u₀.other r hr])
    (by rw [g₇.rd, g₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, g₁.rd, u₀.rd])
    (by rw [g₇.wr, g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr, w0])
    (by rw [g₇.sp, g₆.sp, g₅.sp, g₄.sp, g₃.sp, g₂.sp, g₁.sp, u₀.sp]) ?_
  have o : ∀ r, r ≠ .t0 → s₀.gpr r = s.gpr r := fun r hr => u₀.other r hr
  rw [g₇.mem, g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem, g₁.mem, u₀.mem]
  simp only [saveMem, g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr, o _ (show Reg.ra ≠ .t0 by decide),
    o _ (show Reg.s1 ≠ .t0 by decide), o _ (show Reg.s2 ≠ .t0 by decide),
    o _ (show Reg.s3 ≠ .t0 by decide), o _ (show Reg.s4 ≠ .t0 by decide),
    o _ (show Reg.s5 ≠ .t0 by decide), o _ (show Reg.s6 ≠ .t0 by decide)]

theorem restore_eq : restore = [.load .d .ra .s2 144, .load .d .s1 .s2 152, .load .d .s3 .s2 168,
    .load .d .s4 .s2 176, .load .d .s5 .s2 184, .load .d .s6 .s2 192, .load .d .s2 .s2 160] := rfl

/-- Restoring `ra` and `s1`–`s6` from the frame at `scr` (in `s2`). -/
theorem restore_ok {s : State} {scr : Addr} (h2 : s.gpr .s2 = scr) (hal : scr.toNat % 16 = 0)
    (hin : ∀ d, 144 ≤ d → d + 8 ≤ 208 → InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 d) 8)
    (g : Reg → BitVec 64) (hsv : ∀ p ∈ saved, s.mem.readW (scr + BitVec.ofNat 64 p.2) 64 = g p.1)
    {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved, s'.gpr p.1 = g p.1) → (∀ r, r ∉ saved.map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block restore) s Q := by
  have v : ∀ r d, (r, d) ∈ saved → s.mem.readW (scr + BitVec.ofNat 64 d) 64 = g r :=
    fun r d h => hsv (r, d) h
  have al : ∀ d, d % 8 = 0 → d < 2 ^ 32 → (scr + BitVec.ofNat 64 d).toNat % 8 = 0 :=
    fun d hd hd' => frame_al hal hd hd'
  rw [restore_eq]
  refine wp_ld (by decide) (by rw [h2]) (al 144 (by decide) (by decide)) (hin 144 (by omega) (by omega))
    fun s₁ u₁ => ?_
  refine wp_ld (by decide) (by rw [u₁.other _ (by decide), h2]) (al 152 (by decide) (by decide))
    (by rw [u₁.rd, u₁.wr]; exact hin 152 (by omega) (by omega)) fun s₂ u₂ => ?_
  refine wp_ld (by decide) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h2])
    (al 168 (by decide) (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 168 (by omega) (by omega)) fun s₃ u₃ => ?_
  refine wp_ld (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h2])
    (al 176 (by decide) (by decide))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 176 (by omega) (by omega))
    fun s₄ u₄ => ?_
  refine wp_ld (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h2])
    (al 184 (by decide) (by decide))
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 184 (by omega) (by omega))
    fun s₅ u₅ => ?_
  refine wp_ld (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h2])
    (al 192 (by decide) (by decide))
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact hin 192 (by omega) (by omega))
    fun s₆ u₆ => ?_
  refine wp_ld (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h2])
    (al 160 (by decide) (by decide))
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact hin 160 (by omega) (by omega))
    fun s₇ u₇ => WP.block_nil ?_
  have m6 : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine k s₇ (fun p hp => ?_) (fun r hr => ?_) (by rw [u₇.mem, m6])
    (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp])
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
        v .ra 144 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, v .s1 152 (by simp [saved])]
    · rw [u₇.gpr, m6, v .s2 160 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, v .s3 168 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem,
        u₂.mem, u₁.mem, v .s4 176 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem,
        v .s5 184 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem,
        v .s6 192 (by simp [saved])]
  · simp only [saved, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    obtain ⟨h1, h2', h3, h4, h5, h6, h7⟩ := hr
    rw [u₇.other _ h3, u₆.other _ h7, u₅.other _ h6, u₄.other _ h5, u₃.other _ h4, u₂.other _ h2',
      u₁.other _ h1]

/-! ## Registers -/

/-- Registers that no instruction writes keep their values, as a postcondition. -/
theorem WP.gprs {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rs : List Reg}
    (hc : ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r)
    (hn : c.noCalls = true ∨ ∀ r ∈ rs, r ∉ linkRegs :=
      by first | exact .inr (by decide) | exact .inl (by decide +kernel)) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => Exec.gpr (hc r hr) he (hn.imp id fun h => h r hr)⟩

/-- The callee-saved registers no instruction writes, including those of
the compression function. -/
def untouched : List Reg := [.s7, .s8, .s9, .s10, .s11]

/-- The callee-saved register only the compression function writes (it
saves and restores it). -/
def nvRegs : List Reg := [.s0]

theorem nv_pres : ∀ r ∈ nvRegs, r ∈ preserved := by decide

/-- `untouched.all fun r => o != some r` as one `match`, which the kernel
evaluates several times faster on the inlined compression function. -/
def keepsU : Option Reg → Bool
  | some .s7 | some .s8 | some .s9 | some .s10 | some .s11 => false
  | _ => true

theorem keepsU_all (l : List Instr) (h : (l.all fun i => keepsU (dstOf i)) = true) :
    ∀ r ∈ untouched, ∀ i ∈ l, dstOf i ≠ some r := by
  intro r hr i hi e
  have h := List.all_eq_true.mp h i hi
  rw [e] at h
  simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [keepsU] at h

/-- `s0` (`nvRegs`) is not written. -/
def keepsN : Option Reg → Bool
  | some .s0 => false
  | _ => true

theorem keepsN_all (l : List Instr) (h : (l.all fun i => keepsN (dstOf i)) = true) :
    ∀ r ∈ nvRegs, ∀ i ∈ l, dstOf i ≠ some r := by
  intro r hr i hi e
  have h := List.all_eq_true.mp h i hi
  rw [e] at h
  simp only [nvRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; simp [keepsN] at h

/-! ## The frame -/

/-- The frame's region in the state its body starts in. -/
theorem allocd_wr (n : Nat) (s : State) :
    (allocd n s).wr = ⟨s.sp - BitVec.ofNat 64 n, n⟩ :: s.wr := rfl

theorem allocd_sp (n : Nat) (s : State) : (allocd n s).sp = s.sp - BitVec.ofNat 64 n := rfl

theorem allocd_gpr (n : Nat) (s : State) : (allocd n s).gpr = s.gpr := rfl
theorem allocd_mem (n : Nat) (s : State) : (allocd n s).mem = s.mem := rfl
theorem allocd_rd (n : Nat) (s : State) : (allocd n s).rd = s.rd := rfl

/-- The frame is 16-byte aligned. -/
theorem frame_aligned {sp : Addr} (h : sp.toNat % 16 = 0) (h' : 208 ≤ sp.toNat) :
    (sp - BitVec.ofNat 64 208).toNat % 16 = 0 := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
  omega

end VG.Proof.Sha512.RISCV64.Stream
