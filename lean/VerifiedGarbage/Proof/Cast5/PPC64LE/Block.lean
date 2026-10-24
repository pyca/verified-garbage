module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.Round
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Spec.Cast5

/-!
# CAST5 on PPC64LE: the block function

`crypt up pr` encrypts (`up`) or decrypts the block at `pr` in place, with
the schedule at `sch` and the number of rounds in `rnd` (`crypt_ok`): it
loads the halves, runs the rounds in a loop (`rounds_ok`), each from the
state of the rounds (`RInv`), and stores them. It writes no memory but the
block's.
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5.PPC64LE
open VG.Proof.Cast5 (encFold decFold encFold_succ decFold_succ encryptBlock_eq decryptBlock_eq f_eq roundI)

/-- `fT` of round `i`'s number modulo 3 is the spec's `f`. -/
theorem fT_eq (i : Nat) (km kr d : Spec.Cast5.Word) : fT (i % 3) km kr d = Spec.Cast5.f i d km kr := by
  rw [f_eq]; rfl

/-- The block's cipher. -/
def cipher (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) : Spec.Cast5.Block → Spec.Cast5.Block :=
  if up then Spec.Cast5.encryptBlock k n else Spec.Cast5.decryptBlock k n

/-- What the block function needs: the block at `p` in `pr` (a register
the rounds keep), writable; the schedule at `kb` in `sch`, readable; the
number of rounds `n` in `rnd`; zero and 255 in their registers; and the
table `VG_CAST5_S1234` at `tbl`, readable. -/
structure BPre (s : State) (pr : Reg) (p kb : Addr) (n : Nat) : Prop where
  ptr : s.gpr pr = p
  prOk : pr ∉ roundRegs ∧ pr ≠ .r0
  sched : s.gpr sch = kb
  rounds : s.gpr rnd = BitVec.ofNat 64 n
  nv : n = 12 ∨ n = 16
  zero : s.gpr .r0 = 0
  c255 : s.gpr c255 = 255#64
  trd : (⟨s.gpr tbl, 4096⟩ : Region) ∈ s.rd ++ s.wr
  held : Held s.mem (s.gpr tbl) Impl.Cast5.s1234
  inP : ∃ r ∈ s.wr, ∀ off, off + 4 ≤ 8 → r.Contains (p + BitVec.ofNat 64 off) 4
  inK : (⟨kb, 128⟩ : Region) ∈ s.rd ++ s.wr
  kfit : kb.toNat + 128 ≤ 2 ^ 64

section
variable {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n)
include h

theorem BPre.inK' {off w : Nat} (hw : off + w ≤ 128) :
    InRegions (s.rd ++ s.wr) (kb + BitVec.ofNat 64 off) w :=
  ⟨_, h.inK, Offset.contains_base _ hw (by have := h.kfit; omega_arith)⟩

theorem BPre.inP' {off : Nat} (hw : off + 4 ≤ 8) : InRegions s.wr (p + BitVec.ofNat 64 off) 4 :=
  let ⟨r, hr, hc⟩ := h.inP; ⟨r, hr, hc off hw⟩

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

/-- The subkeys of round `i` (`1 … 16`) at `kp`. -/
theorem key_at (s : State) (kb : Addr) {j : Nat} (hj : j < 32) :
    s.mem.readW (kb + BitVec.ofNat 64 (4 * j)) 32 = (Spec.Cast5.scheduleAt s.mem kb).getD j 0 :=
  (Proof.Cast5.scheduleAt_getD _ _ hj).symm

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
      valR := by rw [e64, hu.mem]; exact key_at s kb (by omega_arith)
      ht := Nat.mod_lt _ (by decide)
      typ := hu.vtyp
      zero := by rw [g _]; exact h.zero
      c255 := by rw [g _]; exact h.c255
      trd := by rw [g tbl, hu.keep.2.1, hu.keep.2.2]; exact h.trd
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
    WP isa (.loop (round up) (.nonzero .d left)) u fun v => ∃ kp t, RInv s (fold n) kp t 0 v := by
  have hn : n = 12 ∨ n = 16 := h.nv
  refine WP.loop (M := isa) (fun m (v : State) => ∃ i, m = n - i ∧ i < n ∧
      RInv s (fold i) (kpf i) (idx i % 3) (n - i) v) ?_ n u ⟨0, rfl, by omega_arith, by rw [Nat.sub_zero]; exact h0⟩
  rintro m v ⟨i, rfl, hi, hv⟩
  rw [hkp i hi] at hv
  refine WP.mono (round_step h hv up (hidx i hi) (by omega_arith)) fun w hw => ?_
  rw [← hfold i hi, ← hkp i hi] at hw
  have ev : isa.eval (.nonzero .d left) w = some (BitVec.ofNat 64 (n - i - 1) != 0) := by
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

theorem _root_.VG.PPC64LE.Upd.keep {s s' : State} {d : Reg} {v : BitVec 64} (h : Upd s s' d v) : Keep [d] s s' :=
  ⟨fun r hr => h.other r (by simpa using hr), h.rd, h.wr⟩

theorem rev32_eq (x : BitVec 32) : rev32 x = byteRev32 x := rfl

theorem BPre.ne {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) {r : Reg}
    (hr : r ∈ roundRegs) : pr ≠ r := fun e => h.prOk.1 (e ▸ hr)

/-- The halves into `xL`, `xR`. -/
theorem load_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ u, Keep [xL, tmp, xR] s u → u.mem = s.mem →
      lo (u.gpr xL) = (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p)).1 →
      lo (u.gpr xR) = (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p)).2 → WP isa (.block is) u Q) :
    WP isa (.block (([.loadRev .w xL pr zero, .addi tmp pr 4, .loadRev .w xR tmp zero] : List Instr) ++ is)) s Q := by
  have in0 : InRegions (s.rd ++ s.wr) p 4 := by
    obtain ⟨g, hg, hc⟩ := h.inP' (off := 0) (by decide)
    exact ⟨g, List.mem_append_right _ hg, by simpa using hc⟩
  have in4 : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 4) 4 := by
    obtain ⟨g, hg, hc⟩ := h.inP' (off := 4) (by decide)
    exact ⟨g, List.mem_append_right _ hg, hc⟩
  have dec := Proof.Cast5.decodeBlock_blockAt s.mem p
  refine wp_lwbrx (ea := p) h.prOk.2 (by rw [h.ptr, h.zero]; simp) in0 fun u₁ h₁ => ?_
  refine wp_addi h.prOk.2 (by decide) fun u₂ h₂ => ?_
  have p₂ : u₂.gpr tmp = p + BitVec.ofNat 64 4 := by rw [h₂.gpr, h₁.other _ (h.ne (by decide)), h.ptr]
  refine wp_lwbrx (ea := p + BitVec.ofNat 64 4) (by decide) (by rw [p₂, h₂.other _ (by decide), h₁.other _ (by decide), h.zero]; simp) (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact in4) fun u₃ h₃ => ?_
  refine k u₃ ((h₁.keep.trans (h₂.keep.trans h₃.keep)).mono (by decide)) (by rw [h₃.mem, h₂.mem, h₁.mem])
    ?_ ?_
  · rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, dec, lo_ext, rev32_eq]
  · rw [h₃.gpr, h₂.mem, h₁.mem, dec, lo_ext, rev32_eq]

theorem startEnc_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) :
    WP isa (.block (startEnc pr)) s (RInv s (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p))
      (kb + BitVec.ofNat 64 (4 * 0)) ((0 + 1) % 3) n) := by
  refine load_ok h fun u uk um uL uR => ?_
  refine wp_mr fun u₁ h₁ => wp_mr fun u₂ h₂ => wp_li (by decide) fun u₃ h₃ => wp_nil ?_
  exact
    { vL := by rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]; exact uL
      vR := by rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]; exact uR
      vkm := by rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, uk.gpr (by decide), h.sched]; simp
      vtyp := by rw [h₃.gpr]
      vleft := by rw [h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide), uk.gpr (by decide), h.rounds]
      keep := (((uk.trans h₁.keep).trans h₂.keep).trans h₃.keep).mono (by decide)
      mem := by rw [h₃.mem, h₂.mem, h₁.mem, um] }

theorem startDec_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) :
    WP isa (.block (startDec pr)) s (RInv s (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p))
      (kb + BitVec.ofNat 64 (4 * ((n - 0) - 1))) ((n - 0) % 3) n) := by
  refine load_ok h fun u uk um uL uR => ?_
  refine wp_lsl (by decide) fun u₁ h₁ => wp_add fun u₂ h₂ => wp_subi (by decide) (by decide) fun u₃ h₃ =>
    wp_mr fun u₄ h₄ => wp_lsr (by decide) fun u₅ h₅ => wp_subi (by decide) (by decide) fun u₆ h₆ => wp_nil ?_
  have r4 : u.gpr rnd = BitVec.ofNat 64 n := by rw [uk.gpr (by decide), h.rounds]
  have r3 : u.gpr sch = kb := by rw [uk.gpr (by decide), h.sched]
  have kmv : u₃.gpr km = kb + (BitVec.ofNat 64 n <<< 2) - BitVec.ofNat 64 4 := by
    rw [h₃.gpr, h₂.gpr, h₁.other _ (by decide), h₁.gpr, r3, r4]
  have tv : u₆.gpr typ = (BitVec.ofNat 64 n >>> 2) - BitVec.ofNat 64 3 := by
    rw [h₆.gpr, h₅.gpr, h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide),
      h₁.other _ (by decide), r4]
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
      keep := (((((((uk.trans h₁.keep).trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans
        h₆.keep)).mono (by decide)
      mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem, um] }

/-- What the block function does: the block at `p` is `out`, and nothing
else in memory changed. -/
structure BPost (s : State) (p : Addr) (out : Spec.Cast5.Block) (t : State) : Prop where
  blk : Spec.Cast5.blockAt t.mem p = out
  frame : Frame [⟨p, 8⟩] s.mem t.mem
  keep : Keep roundRegs s t

theorem finish_ok {s u : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n)
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} {kp : Addr} {t : Nat} (hu : RInv s lr kp t 0 u) :
    WP isa (.block (finish pr)) u (BPost s p (Spec.Cast5.encodeBlock (lr.2, lr.1))) := by
  have g (q : Reg) (hq : q ∉ roundRegs) : u.gpr q = s.gpr q := hu.keep.gpr hq
  have hp : u.gpr pr = p := by rw [g _ h.prOk.1, h.ptr]
  have h0 : u.gpr .r0 = 0 := by rw [g _ (by decide), h.zero]
  have o0 : InRegions u.wr p 4 := by rw [hu.keep.2.2]; simpa using h.inP' (off := 0) (by decide)
  have o4 : InRegions u.wr (p + BitVec.ofNat 64 4) 4 := by rw [hu.keep.2.2]; exact h.inP' (by decide)
  refine wp_stwbrx (ea := p) h.prOk.2 (by rw [hp, h0]; simp) o0 fun u₁ h₁ => ?_
  refine wp_addi h.prOk.2 (by decide) fun u₂ h₂ => ?_
  have p₂ : u₂.gpr tmp = p + BitVec.ofNat 64 4 := by rw [h₂.gpr, h₁.gpr, hp]
  refine wp_stwbrx (ea := p + BitVec.ofNat 64 4) (by decide)
    (by rw [p₂, h₂.other _ (by decide), h₁.gpr, h0]; simp) (by rw [h₂.wr, h₁.wr]; exact o4) fun u₃ h₃ => ?_
  refine wp_nil ⟨?_, ?_, ?_⟩
  · rw [h₃.mem, h₂.mem, h₁.mem, h₂.other _ (by decide), h₁.gpr, rev32_eq, rev32_eq, hu.mem,
      Proof.Cast5.blockAt_write]
    exact congrArg _ (Prod.ext hu.vR hu.vL)
  · rw [h₃.mem, h₂.mem, h₁.mem, hu.mem]
    have f1 := (Frame.refl [(⟨p, 8⟩ : Region)] s.mem).writeW List.mem_cons_self
      (rev32 ((u.gpr xR).setWidth 32)) (Offset.contains_base p (d := 0) (n := 4) (k := 8) (by decide) (by decide))
    rw [BitVec.add_zero] at f1
    exact f1.writeW List.mem_cons_self _
      (Offset.contains_base p (d := 4) (n := 4) (k := 8) (by decide) (by decide))
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · rw [h₃.gpr, h₂.other r fun e => hr (e ▸ by decide), h₁.gpr]; exact hu.keep.gpr hr
    · rw [h₃.rd, h₂.rd, h₁.rd]; exact hu.keep.2.1
    · rw [h₃.wr, h₂.wr, h₁.wr]; exact hu.keep.2.2

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

end VG.Proof.Cast5.PPC64LE
