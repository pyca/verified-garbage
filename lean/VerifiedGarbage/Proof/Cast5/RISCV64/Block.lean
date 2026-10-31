module

public import VerifiedGarbage.Proof.Cast5.RISCV64.Round
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Spec.Cast5

/-!
# CAST5 on RISC-V: the block function

`crypt up pr` encrypts (`up`) or decrypts the block at `pr` in place, with
the schedule at `sch` and the number of rounds in `rnd` (`crypt_ok`): it
loads the halves, a byte at a time, big-endian (`load_ok`), runs the rounds
in a loop (`rounds_ok`), each from the state of the rounds (`RInv`), and
stores them, a byte at a time (`finish_ok`). It writes no memory but the
block's. As on PPC64LE (`Proof/Cast5/PPC64LE/Block.lean`).
-/

@[expose] public section

namespace VG.Proof.Cast5.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Cast5.RISCV64
open VG.Proof.Cast5 (encFold decFold encFold_succ decFold_succ encryptBlock_eq decryptBlock_eq f_eq roundI)
open VG.WriteBytes (writeBytes)

/-- `fT` of round `i`'s number modulo 3 is the spec's `f`. -/
theorem fT_eq (i : Nat) (km kr d : Spec.Cast5.Word) : fT (i % 3) km kr d = Spec.Cast5.f i d km kr := by
  rw [f_eq]; rfl

/-- The block's cipher. -/
def cipher (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) : Spec.Cast5.Block → Spec.Cast5.Block :=
  if up then Spec.Cast5.encryptBlock k n else Spec.Cast5.decryptBlock k n

/-- What the block function needs: the block at `p` in `pr` (a register
the rounds keep), writable; the schedule at `kb` in `sch`, readable; the
number of rounds `n` in `rnd`; and the table `VG_CAST5_S1234` at `tbl`,
readable and 64-byte aligned. -/
structure BPre (s : State) (pr : Reg) (p kb : Addr) (n : Nat) : Prop where
  ptr : s.gpr pr = p
  prOk : pr ∉ roundRegs
  sched : s.gpr sch = kb
  rounds : s.gpr rnd = BitVec.ofNat 64 n
  nv : n = 12 ∨ n = 16
  trd : (⟨s.gpr tbl, 4096⟩ : Region) ∈ s.rd ++ s.wr
  tal : (s.gpr tbl).toNat % 64 = 0
  held : Held s.mem (s.gpr tbl) Impl.Cast5.s1234
  inP : InRegions s.wr p 8
  inK : (⟨kb, 128⟩ : Region) ∈ s.rd ++ s.wr
  kfit : kb.toNat + 128 ≤ 2 ^ 64

section
variable {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n)
include h

theorem BPre.inK' {off w : Nat} (hw : off + w ≤ 128) :
    InRegions (s.rd ++ s.wr) (kb + BitVec.ofNat 64 off) w :=
  ⟨_, h.inK, Offset.contains_base _ hw (by have := h.kfit; omega_arith)⟩

theorem BPre.inP' : InRegions (s.rd ++ s.wr) p 8 :=
  let ⟨r, hr, hc⟩ := h.inP; ⟨r, List.mem_append_right _ hr, hc⟩

end

/-! ## The rounds -/

/-- The state of a block's rounds, from `s`: the halves `lr`, the next
round's subkeys at `kp`, its number modulo 3 `t` and `left` rounds left. -/
structure RInv (s : State) (lr : Spec.Cast5.Word × Spec.Cast5.Word) (kp : Addr) (t nl : Nat)
    (u : State) : Prop where
  vL : lo (u.gpr xL) = lr.1
  vR : lo (u.gpr xR) = lr.2
  vkm : u.gpr km = kp
  vtyp : u.gpr typ = BitVec.ofNat 64 t
  vleft : u.gpr left = BitVec.ofNat 64 nl
  keep : Keep roundRegs s u
  mem : u.mem = s.mem

/-- Subkey `j` at `kb + 4 j`. -/
theorem key_at (s : State) (kb : Addr) {j : Nat} (hj : j < 32) :
    s.mem.readW (kb + BitVec.ofNat 64 (4 * j)) 32 = (Spec.Cast5.scheduleAt s.mem kb).getD j 0 :=
  (Proof.Cast5.scheduleAt_getD _ _ hj).symm

/-- The low five bits of a little-endian word are those of its first byte. -/
theorem readW_mod32 (m : Mem) (a : Addr) : (m.readW a 32).toNat % 32 = (m a).toNat % 32 := by
  have e : (m.readW a 32).setWidth 8 = m a := by
    rw [Proof.Cast5.readW32]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, hi, decide_true, Bool.true_and, ite_true]
  have h8 : ((m.readW a 32).setWidth 8).toNat = (m.readW a 32).toNat % 256 := by
    rw [BitVec.toNat_setWidth]
  rw [← e, h8]
  omega

/-- A round, from the state of the rounds. -/
theorem round_step {s u : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n)
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} {nl i : Nat}
    (hu : RInv s lr (kb + BitVec.ofNat 64 (4 * (i - 1))) (i % 3) nl u) (up : Bool)
    (hi : 1 ≤ i ∧ i ≤ 16) (hl : 1 ≤ nl ∧ nl < 2 ^ 64) :
    WP isa (round up) u fun v =>
      RInv s (Spec.Cast5.round (Spec.Cast5.scheduleAt s.mem kb) i lr)
        (if up then kb + BitVec.ofNat 64 (4 * (i - 1)) + 4#64 else kb + BitVec.ofNat 64 (4 * (i - 1)) - 4#64)
        (nextT up (i % 3)) (nl - 1) v := by
  have g (q : Reg) (hq : q ∉ roundRegs := by decide) : u.gpr q = s.gpr q := hu.keep.gpr hq
  have e64 : u.gpr km + BitVec.ofNat 64 64 = kb + BitVec.ofNat 64 (4 * (15 + i)) := by
    rw [hu.vkm, Offset.add_add]; congr 2; omega_arith
  have pre : RoundPre u ((Spec.Cast5.scheduleAt s.mem kb).getD (i - 1) 0)
      ((Spec.Cast5.scheduleAt s.mem kb).getD (15 + i) 0) lr.1 lr.2 (i % 3) :=
    { xL := hu.vL
      xR := hu.vR
      inM := by rw [hu.vkm, hu.keep.2.1, hu.keep.2.2]; exact h.inK' (by omega_arith)
      valM := by rw [hu.vkm, hu.mem]; exact key_at s kb (by omega_arith)
      inR := by rw [e64, hu.keep.2.1, hu.keep.2.2]; exact h.inK' (by omega_arith)
      valR := by rw [e64, hu.mem, ← key_at s kb (by omega_arith), readW_mod32]
      ht := Nat.mod_lt _ (by decide)
      typ := hu.vtyp
      trd := by rw [g tbl, hu.keep.2.1, hu.keep.2.2]; exact h.trd
      tal := by rw [g tbl]; exact h.tal
      held := by rw [g tbl, hu.mem]; exact h.held }
  refine WP.mono (round_ok u up pre) fun v ⟨v1, v2, vkm, vt, vl, vk, vm⟩ => ⟨v1, ?_, ?_, vt, ?_,
    (hu.keep.trans vk).mono (by decide), vm.trans hu.mem⟩
  · rw [v2, show (Spec.Cast5.round (Spec.Cast5.scheduleAt s.mem kb) i lr).2 =
      lr.1 ^^^ Spec.Cast5.f i lr.2 _ _ from rfl, fT_eq]
  · rw [vkm, hu.vkm]
  · rw [vl, hu.vleft]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith

/-- The rounds loop, for any order of the rounds: round `idx i` is the
`i`-th, with its subkeys at `kpf i`, and the halves before it `fold i`. -/
theorem rounds_ok {s u : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) (up : Bool)
    (idx : Nat → Nat) (kpf : Nat → Addr) (fold : Nat → Spec.Cast5.Word × Spec.Cast5.Word)
    (hidx : ∀ i < n, 1 ≤ idx i ∧ idx i ≤ 16) (hkp : ∀ i < n, kpf i = kb + BitVec.ofNat 64 (4 * (idx i - 1)))
    (hfold : ∀ i < n, fold (i + 1) = Spec.Cast5.round (Spec.Cast5.scheduleAt s.mem kb) (idx i) (fold i))
    (hnext : ∀ i, i + 1 < n → kpf (i + 1) = (if up then kpf i + 4#64 else kpf i - 4#64) ∧
      idx (i + 1) % 3 = nextT up (idx i % 3))
    (h0 : RInv s (fold 0) (kpf 0) (idx 0 % 3) n u) :
    WP isa (.loop (round up) (.nonzero left)) u fun v => ∃ kp t, RInv s (fold n) kp t 0 v := by
  have hn : n = 12 ∨ n = 16 := h.nv
  refine WP.loop (M := isa) (fun m (v : State) => ∃ i, m = n - i ∧ i < n ∧
      RInv s (fold i) (kpf i) (idx i % 3) (n - i) v) ?_ n u ⟨0, rfl, by omega_arith, by rw [Nat.sub_zero]; exact h0⟩
  rintro m v ⟨i, rfl, hi, hv⟩
  rw [hkp i hi] at hv
  refine WP.mono (round_step h hv up (hidx i hi) (by omega_arith)) fun w hw => ?_
  rw [← hfold i hi, ← hkp i hi] at hw
  have ev : isa.eval (.nonzero left) w = some (BitVec.ofNat 64 (n - i - 1) != 0) := by
    rw [eval_nonzero, hw.vleft]
  by_cases hlast : i + 1 = n
  · refine .inl ⟨?_, _, _, by rw [hlast] at hw; rw [show n - i - 1 = 0 by omega_arith] at hw; exact hw⟩
    rw [ev, show n - i - 1 = 0 by omega_arith]; rfl
  · obtain ⟨hk, htn⟩ := hnext i (by omega_arith)
    refine .inr ⟨?_, n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, ?_⟩
    · rw [ev]
      congr 1
      have : BitVec.ofNat 64 (n - i - 1) ≠ 0 := by
        intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
        omega_arith
      simpa using this
    · rw [hk, htn, show n - (i + 1) = n - i - 1 by omega_arith]
      exact hw


/-! ## The block function -/

theorem _root_.VG.RISCV64.Steps.Upd.keep {s s' : State} {d : Reg} {v : BitVec 64} (h : Upd s s' d v) :
    Keep [d] s s' :=
  ⟨fun r hr => h.other r (by simpa using hr), h.rd, h.wr⟩

theorem BPre.ne {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) {r : Reg}
    (hr : r ∈ roundRegs) : pr ≠ r := fun e => h.prOk (e ▸ hr)

/-- The halves of the block at `p`: big-endian words, a byte at a time. -/
theorem decodeBlock_beWord (m : Mem) (p : Addr) :
    Spec.Cast5.decodeBlock (Spec.Cast5.blockAt m p) = (ByteLoad.beWord m p 0, ByteLoad.beWord m p 4) := by
  simp only [Spec.Cast5.decodeBlock, ByteLoad.beWord, Proof.Cast5.blockAt_get m p (show 0 < 8 by decide),
    Proof.Cast5.blockAt_get m p (show 1 < 8 by decide), Proof.Cast5.blockAt_get m p (show 2 < 8 by decide),
    Proof.Cast5.blockAt_get m p (show 3 < 8 by decide), Proof.Cast5.blockAt_get m p (show 4 < 8 by decide),
    Proof.Cast5.blockAt_get m p (show 5 < 8 by decide), Proof.Cast5.blockAt_get m p (show 6 < 8 by decide),
    Proof.Cast5.blockAt_get m p (show 7 < 8 by decide), Nat.reduceAdd]

/-- The halves into `xL`, `xR`. -/
theorem load_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ u, Keep [xL, tmp, xR] s u → u.mem = s.mem →
      lo (u.gpr xL) = (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p)).1 →
      lo (u.gpr xR) = (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p)).2 → WP isa (.block is) u Q) :
    WP isa (.block (loadBlock pr ++ is)) s Q := by
  have in0 : InRegions (s.rd ++ s.wr) (s.gpr pr + BitVec.ofNat 64 0) 4 := by
    rw [h.ptr]; exact CallLay.inRegions_sub h.inP' (by decide) (by decide)
  have in4 : InRegions (s.rd ++ s.wr) (s.gpr pr + BitVec.ofNat 64 4) 4 := by
    rw [h.ptr]; exact CallLay.inRegions_sub h.inP' (by decide) (by decide)
  rw [loadBlock, List.append_assoc, WP.block_append_iff]
  refine WP.mono (ByteLoad.loadBE32_ok (d := xL) (tmp := tmp) (n := pr) (off := 0) (h.ne (by decide)).symm
    (h.ne (by decide)).symm (by decide) (by decide) in0) fun u₁ e₁ => ?_
  subst e₁
  rw [WP.block_append_iff]
  refine WP.mono (ByteLoad.loadBE32_ok (d := xR) (tmp := tmp) (n := pr) (off := 4) (h.ne (by decide)).symm
    (h.ne (by decide)).symm (by decide) (by decide) (by
      simp only [RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, h.ne (show xL ∈ roundRegs by decide),
        h.ne (show tmp ∈ roundRegs by decide), ite_false]
      exact in4)) fun u₂ e₂ => ?_
  subst e₂
  refine k _ ⟨fun r hr => ?_, rfl, rfl⟩ rfl ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, lo_ext, decodeBlock_beWord, h.ptr]
  · simp only [RegUpd.gpr_write, ite_true, lo_ext, RegUpd.mem_write, decodeBlock_beWord,
      h.ne (show xL ∈ roundRegs by decide), h.ne (show tmp ∈ roundRegs by decide), ite_false, h.ptr]

theorem startEnc_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) :
    WP isa (.block (startEnc pr)) s (RInv s (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p))
      (kb + BitVec.ofNat 64 (4 * 0)) ((0 + 1) % 3) n) := by
  refine load_ok h fun u uk um uL uR => ?_
  refine wp_mv fun u₁ h₁ => wp_mv fun u₂ h₂ => wp_li (imm := 1) (by decide) fun u₃ h₃ => WP.block_nil ?_
  exact
    { vL := by rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]; exact uL
      vR := by rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]; exact uR
      vkm := by rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, uk.gpr (by decide), h.sched]; simp
      vtyp := by rw [h₃.gpr]
      vleft := by rw [h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide), uk.gpr (by decide), h.rounds]
      keep := ⟨fun r hr => by
          rw [h₃.other r (fun e => hr (e ▸ by decide)), h₂.other r (fun e => hr (e ▸ by decide)),
            h₁.other r (fun e => hr (e ▸ by decide)), uk.gpr (fun e => hr (by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at e
              rcases e with rfl | rfl | rfl <;> decide))],
        by rw [h₃.rd, h₂.rd, h₁.rd, uk.2.1], by rw [h₃.wr, h₂.wr, h₁.wr, uk.2.2]⟩
      mem := by rw [h₃.mem, h₂.mem, h₁.mem, um] }

theorem startDec_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) :
    WP isa (.block (startDec pr)) s (RInv s (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p))
      (kb + BitVec.ofNat 64 (4 * ((n - 0) - 1))) ((n - 0) % 3) n) := by
  refine load_ok h fun u uk um uL uR => ?_
  refine wp_sll (by decide) fun u₁ h₁ => wp_add fun u₂ h₂ => wp_subi (imm := 4) (by decide) fun u₃ h₃ =>
    wp_mv fun u₄ h₄ => wp_srl (by decide) fun u₅ h₅ => wp_subi (imm := 3) (by decide) fun u₆ h₆ =>
    WP.block_nil ?_
  have r4 : u.gpr rnd = BitVec.ofNat 64 n := by rw [uk.gpr (by decide), h.rounds]
  have r3 : u.gpr sch = kb := by rw [uk.gpr (by decide), h.sched]
  have kmv : u₃.gpr km = kb + (BitVec.ofNat 64 n <<< 2) - BitVec.ofNat 64 4 := by
    rw [h₃.gpr, h₂.gpr, h₁.other _ (by decide), h₁.gpr, r3, r4]
  have tv : u₆.gpr typ = (BitVec.ofNat 64 n >>> 2) - BitVec.ofNat 64 3 := by
    rw [h₆.gpr, h₅.gpr, h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide),
      h₁.other _ (by decide), r4]
  have ko : ∀ r, r ∉ roundRegs → u₆.gpr r = s.gpr r := fun r hr => by
    have h' : ∀ q ∈ [tmp, km, left, typ, xL, xR], r ≠ q := fun q hq e => hr (by
      subst e; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    rw [h₆.other r (h' _ (by decide)), h₅.other r (h' _ (by decide)), h₄.other r (h' _ (by decide)),
      h₃.other r (h' _ (by decide)), h₂.other r (h' _ (by decide)), h₁.other r (h' _ (by decide)),
      uk.gpr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h' _ (by decide), h' _ (by decide), h' _ (by decide)⟩)]
  exact
    { vL := by
        rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
          h₂.other _ (by decide), h₁.other _ (by decide)]; exact uL
      vR := by
        rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
          h₂.other _ (by decide), h₁.other _ (by decide)]; exact uR
      vkm := by
        rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), kmv]
        rcases h.nv with rfl | rfl
        · rw [show (BitVec.ofNat 64 12 <<< 2) = BitVec.ofNat 64 48 by decide, Offset.add_ofNat_sub _ (by decide)]
        · rw [show (BitVec.ofNat 64 16 <<< 2) = BitVec.ofNat 64 64 by decide, Offset.add_ofNat_sub _ (by decide)]
      vtyp := by rw [tv]; rcases h.nv with rfl | rfl <;> decide
      vleft := by
        rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.gpr, h₃.other _ (by decide),
          h₂.other _ (by decide), h₁.other _ (by decide), r4]
      keep := ⟨ko, by rw [h₆.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd, uk.2.1],
        by rw [h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr, uk.2.2]⟩
      mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem, um] }

/-- What the block function does: the block at `p` is `out`, and nothing
else in memory changed. -/
structure BPost (s : State) (p : Addr) (out : Spec.Cast5.Block) (t : State) : Prop where
  blk : Spec.Cast5.blockAt t.mem p = out
  frame : Frame [⟨p, 8⟩] s.mem t.mem
  keep : Keep roundRegs s t

theorem shr_lo (x : BitVec 64) {k : Nat} (hk : k ≤ 24) :
    (x >>> k).setWidth 8 = (lo x >>> k).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi, show k + i < 32 by omega]

/-- What the stores leave: the block `(x, y)`. -/
theorem stored_block (m : Mem) (q : Addr) (x y : BitVec 64) :
    Spec.Cast5.blockAt (writeBytes m q (ByteLoad.beBytes 4 x ++ ByteLoad.beBytes 4 y)) q =
      Spec.Cast5.encodeBlock (lo x, lo y) := by
  apply Vector.ext
  intro i hi
  rw [Proof.Cast5.blockAt_get _ _ hi]
  simp only [Spec.Cast5.encodeBlock, Vector.getElem_ofFn, writeBytes, Offset.add_sub_cancel_left,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), List.length_append,
    ByteLoad.beBytes_length, show i < 4 + 4 by omega, ite_true]
  by_cases h4 : i < 4
  · rw [ite_eq_left h4, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [ByteLoad.beBytes_length]; exact h4)]
    simp only [ByteLoad.beBytes, List.getElem?_map, List.getElem?_range h4, Option.map_some, Option.getD_some]
    rw [shr_lo _ (by omega), Nat.mod_eq_of_lt h4]
  · rw [ite_eq_right h4, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [ByteLoad.beBytes_length]; omega), ByteLoad.beBytes_length]
    simp only [ByteLoad.beBytes, List.getElem?_map, List.getElem?_range (show i - 4 < 4 by omega), Option.map_some,
      Option.getD_some]
    rw [shr_lo _ (by omega)]
    congr 3; omega

theorem finish_ok {s u : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n)
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} {kp : Addr} {t : Nat} (hu : RInv s lr kp t 0 u) :
    WP isa (.block (finish pr)) u (BPost s p (Spec.Cast5.encodeBlock (lr.2, lr.1))) := by
  have g (q : Reg) (hq : q ∉ roundRegs) : u.gpr q = s.gpr q := hu.keep.gpr hq
  have hp : u.gpr pr = p := by rw [g _ h.prOk, h.ptr]
  have hw : ∀ j < 8, InRegions u.wr (p + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hu.keep.2.2]; exact CallLay.inRegions_sub h.inP (by omega) (by decide)
  rw [finish, WP.block_append_iff]
  refine WP.mono (ByteLoad.storeBE_ok (v := xR) (tmp := tmp) (n := pr) (off := 0) (w := 4) (by decide)
    (h.ne (by decide)).symm (by decide) (by decide) (by decide) fun j hj => by
      rw [hp, Nat.zero_add]; exact hw j (by omega)) fun u₁ e₁ => ?_
  subst e₁
  have hp₁ : ∀ (m : Mem) (v : BitVec 64), ({ u with mem := m }.write tmp v).gpr pr = p := fun m v => by
    rw [RegUpd.gpr_write_of_ne _ _ (h.ne (by decide))]; exact hp
  refine WP.mono (ByteLoad.storeBE_ok (v := xL) (tmp := tmp) (n := pr) (off := 4) (w := 4) (by decide)
    (h.ne (by decide)).symm (by decide) (by decide) (by decide) fun j hj => by
      rw [hp₁]; exact hw (4 + j) (by omega)) fun u₂ e₂ => ?_
  subst e₂
  simp only [RegUpd.gpr_write, RegUpd.mem_write, RegUpd.write_mem, hp, h.ne (show tmp ∈ roundRegs by decide),
    show xL ≠ tmp by decide, ite_false, BitVec.add_zero]
  have hm := WriteBytes.writeBytes_append u.mem p (ByteLoad.beBytes 4 (u.gpr xR)) (ByteLoad.beBytes 4 (u.gpr xL))
    (by simp only [ByteLoad.beBytes_length]; decide)
  rw [ByteLoad.beBytes_length] at hm
  refine ⟨?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩⟩
  · simp only [State.write]
    rw [hm, stored_block]
    exact congrArg _ (Prod.ext hu.vR hu.vL)
  · simp only [State.write]
    rw [hm, ← hu.mem]
    exact WriteBytes.writeBytes_frame _ _ _ (by
      simp only [List.length_append, ByteLoad.beBytes_length]
      exact Region.contains_self p 8)
  · have ht : r ≠ tmp := fun e => hr (by rw [e]; decide)
    simp only [State.write, ht, ite_false]
    exact hu.keep.gpr hr
  · exact hu.keep.2.1
  · exact hu.keep.2.2

theorem crypt_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) (up : Bool) :
    WP isa (crypt up pr) s (BPost s p (cipher up (Spec.Cast5.scheduleAt s.mem kb) n
      (Spec.Cast5.blockAt s.mem p))) := by
  have hn := h.nv
  cases up
  · unfold crypt
    simp only [Bool.false_eq_true, ite_false]
    refine WP.seq (WP.mono (startDec_ok h) fun u hu => ?_)
    refine WP.seq (WP.mono (rounds_ok h false (fun i => n - i) (fun i => kb + BitVec.ofNat 64 (4 * (n - i - 1)))
      (fun i => decFold _ n i _) (fun i hi => by omega_arith) (fun i hi => rfl)
      (fun i hi => decFold_succ _ _ _ _) (fun i hi => ⟨?_, ?_⟩) hu) fun v ⟨kp, t, hv⟩ => ?_)
    · simp only [Bool.false_eq_true, ite_false]
      rw [show n - i - 1 = n - (i + 1) - 1 + 1 by omega_arith, Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc]
      exact (BitVec.add_sub_cancel _ _).symm
    · simp only [nextT, Bool.false_eq_true, ite_false]
      split <;> omega_arith
    refine WP.mono (finish_ok h hv) fun w hw => ?_
    rw [cipher, ite_eq_right Bool.false_ne_true, decryptBlock_eq]
    exact hw
  · unfold crypt
    simp only [ite_true]
    refine WP.seq (WP.mono (startEnc_ok h) fun u hu => ?_)
    refine WP.seq (WP.mono (rounds_ok h true (fun i => i + 1) (fun i => kb + BitVec.ofNat 64 (4 * i))
      (fun i => encFold _ i _) (fun i hi => by omega_arith)
      (fun i hi => by rw [Nat.add_sub_cancel]) (fun i hi => encFold_succ _ _ _) (fun i hi => ⟨?_, ?_⟩) hu)
      fun v ⟨kp, t, hv⟩ => ?_)
    · simp only [ite_true]
      rw [Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc]
    · simp only [nextT, ite_true]
      split <;> omega_arith
    refine WP.mono (finish_ok h hv) fun w hw => ?_
    rw [cipher, ite_eq_left rfl, encryptBlock_eq]
    exact hw

end VG.Proof.Cast5.RISCV64
