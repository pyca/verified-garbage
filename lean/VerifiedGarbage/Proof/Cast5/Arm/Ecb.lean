module

public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Cast5.Arm.Round
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-! ### `Cast5.Arm.Block`, which this module and modules that import it used -/

section

/-!
# CAST5 on ARMv7: the block function

`crypt up` encrypts (`up`) or decrypts the block whose address is in the
data slot of the working space at `r12`, in place, with the schedule and the
number of rounds in their slots (`crypt_ok`). Besides the block it writes
only the slots of the count and type of rounds (`cntOff`, `typeOff`) and the
scan's ten words after them, and it keeps `r12`: this is the block function
a mode reuses.
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5.Arm
open VG.Impl.Cast5 (s1234Sym)
open VG.Proof.Cast5 (encFold decFold encFold_succ decFold_succ encryptBlock_eq decryptBlock_eq f_eq roundI)

/-- `fT` of the type of round `i` is the spec's `f`. -/
theorem fT_eq {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hti : t % 3 = i % 3) (km kr d : Spec.Cast5.Word) :
    fT t km kr d = Spec.Cast5.f i d km kr := by
  rw [f_eq]
  unfold fT roundI
  rcases ht with rfl | rfl | rfl <;> rw [← hti] <;> rfl

theorem rev_eq (x : BitVec 32) : rev x = byteRev32 x := rfl

/-- The block's cipher. -/
def cipher (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) : Spec.Cast5.Block → Spec.Cast5.Block :=
  if up then Spec.Cast5.encryptBlock k n else Spec.Cast5.decryptBlock k n

/-- The slots of the count and type of rounds, and the scan's ten words. -/
abbrev ctRegion (c : BitVec 32) : Region := ⟨State.addr c + BitVec.ofNat 64 16, 48⟩

/-- What the block function needs: the working space at `c` in `r12`, the
block at `p` (in the data slot), the schedule at `kb` (in its slot) and the
number of rounds `n` (in its slot); and the table `VG_CAST5_S1234`, readable
and apart from the working space. -/
structure BPre (s : State) (c p kb : BitVec 32) (n : Nat) : Prop where
  r12 : s.gpr .r12 = c
  cfit : c.toNat + 256 ≤ 2 ^ 32
  pfit : p.toNat + 8 ≤ 2 ^ 32
  kfit : kb.toNat + 128 ≤ 2 ^ 32
  scr : (⟨State.addr c, 256⟩ : Region) ∈ s.wr
  blk : ∀ {off w : Nat}, off + w ≤ 8 → InRegions s.wr (State.addr p + BitVec.ofNat 64 off) w
  sch : (⟨State.addr kb, 128⟩ : Region) ∈ s.rd ++ s.wr
  dPS : Region.Disjoint ⟨State.addr p, 8⟩ ⟨State.addr c, 256⟩
  dKS : Region.Disjoint ⟨State.addr kb, 128⟩ ⟨State.addr c, 256⟩
  dKP : Region.Disjoint ⟨State.addr kb, 128⟩ ⟨State.addr p, 8⟩
  data : s.mem.readW (State.addr c + BitVec.ofNat 64 0) 32 = p
  sched : s.mem.readW (State.addr c + BitVec.ofNat 64 8) 32 = kb
  rounds : s.mem.readW (State.addr c + BitVec.ofNat 64 12) 32 = BitVec.ofNat 32 n
  nv : n = 12 ∨ n = 16
  tfit : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  trd : (⟨State.addr (s.syms s1234Sym), 4096⟩ : Region) ∈ s.rd ++ s.wr
  held : Held s.mem (State.addr (s.syms s1234Sym)) Impl.Cast5.s1234
  dTS : Region.Disjoint ⟨State.addr (s.syms s1234Sym), 4096⟩ ⟨State.addr c, 256⟩

section
variable {s : State} {c p kb : BitVec 32} {n : Nat} (h : BPre s c p kb n)
include h

theorem BPre.inS {off w : Nat} (hw : off + w ≤ 256) : InRegions s.wr (State.addr c + BitVec.ofNat 64 off) w :=
  ⟨_, h.scr, Offset.contains_base _ hw (by omega_arith)⟩

theorem BPre.inS' {off w : Nat} (hw : off + w ≤ 256) :
    InRegions (s.rd ++ s.wr) (State.addr c + BitVec.ofNat 64 off) w :=
  ⟨_, List.mem_append_right _ h.scr, Offset.contains_base _ hw (by omega_arith)⟩

theorem BPre.inP {off w : Nat} (hw : off + w ≤ 8) : InRegions s.wr (State.addr p + BitVec.ofNat 64 off) w :=
  h.blk hw

theorem BPre.inP' {off w : Nat} (hw : off + w ≤ 8) :
    InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 off) w := by
  obtain ⟨g, hg, hc⟩ := h.blk hw; exact ⟨g, List.mem_append_right _ hg, hc⟩

theorem BPre.inK {off w : Nat} (hw : off + w ≤ 128) :
    InRegions (s.rd ++ s.wr) (State.addr kb + BitVec.ofNat 64 off) w :=
  ⟨_, h.sch, Offset.contains_base _ hw (by omega_arith)⟩

theorem BPre.aS : ∀ off, off < 256 → State.addr (c + BitVec.ofNat 32 off) = State.addr c + BitVec.ofNat 64 off :=
  addr_off h.cfit

theorem BPre.aP : ∀ off, off < 8 → State.addr (p + BitVec.ofNat 32 off) = State.addr p + BitVec.ofNat 64 off :=
  addr_off h.pfit

end

/-! ## The rounds -/

/-- The state of a block's rounds, from `s`: the halves `lr`, the next
round's subkeys at `kp`, its type `t` and `left` rounds left. -/
structure RInv (s : State) (c : BitVec 32) (lr : Spec.Cast5.Word × Spec.Cast5.Word) (kp : BitVec 32) (t left : Nat)
    (u : State) : Prop where
  r2 : u.gpr .r2 = lr.1
  r3 : u.gpr .r3 = lr.2
  lr : u.gpr .lr = kp
  r12 : u.gpr .r12 = c
  fr : Frame [ctRegion c] s.mem u.mem
  cnt : u.mem.readW (State.addr c + BitVec.ofNat 64 16) 32 = BitVec.ofNat 32 left
  typ : u.mem.readW (State.addr c + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 t
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  sp : u.sp = s.sp
  syms : u.syms = s.syms

theorem RInv_iff {s : State} {c : BitVec 32} {lr : Spec.Cast5.Word × Spec.Cast5.Word} {kp : BitVec 32}
    {t left : Nat} {u : State} : RInv s c lr kp t left u ↔
      (u.gpr .r2 = lr.1 ∧ u.gpr .r3 = lr.2 ∧ u.gpr .lr = kp ∧ u.gpr .r12 = c ∧ Frame [ctRegion c] s.mem u.mem ∧
        u.mem.readW (State.addr c + BitVec.ofNat 64 16) 32 = BitVec.ofNat 32 left ∧
        u.mem.readW (State.addr c + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 t ∧
        u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ u.syms = s.syms) :=
  ⟨fun h => ⟨h.r2, h.r3, h.lr, h.r12, h.fr, h.cnt, h.typ, h.rd, h.wr, h.sp, h.syms⟩,
   fun ⟨a, b, c, d, e, f, g, i, j, k, l⟩ => ⟨a, b, c, d, e, f, g, i, j, k, l⟩⟩

/-- The subkeys of round `i` (`1 … 16`) at `kp`, read through a frame. -/
theorem key_at {s u : State} {c p kb : BitVec 32} {n : Nat} (h : BPre s c p kb n)
    (hf : Frame [ctRegion c] s.mem u.mem) {i : Nat} (hi : 1 ≤ i ∧ i ≤ 16) {j : Nat} (hj : j = i - 1 ∨ j = 15 + i) :
    u.mem.readW (State.addr kb + BitVec.ofNat 64 (4 * j)) 32 =
      (Spec.Cast5.scheduleAt s.mem (State.addr kb)).getD j 0 := by
  rw [Proof.Cast5.scheduleAt_getD _ _ (by omega_arith)]
  refine hf.readW (r := ⟨State.addr kb, 128⟩) (Offset.contains_base _ (by omega_arith) (by omega_arith)) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h.dKS.sub_right (Offset.sub_base _ (by decide))

theorem kp_addr {kb : BitVec 32} (hk : kb.toNat + 128 ≤ 2 ^ 32) {j : Nat} (off : Nat)
    (hjo : 4 * j + off + 4 ≤ 128) :
    State.addr (kb + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 off) =
      State.addr kb + BitVec.ofNat 64 (4 * j + off) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact addr_add (by omega_arith)

/-- A round, from the state of the rounds. -/
theorem round_step {s u : State} {c p kb : BitVec 32} {n : Nat} (h : BPre s c p kb n) {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    {t left i : Nat} (hu : RInv s c lr (kb + BitVec.ofNat 32 (4 * (i - 1))) t left u) (up : Bool)
    (ht : t = 1 ∨ t = 2 ∨ t = 3) (hti : t % 3 = i % 3) (hi : 1 ≤ i ∧ i ≤ 16) (hl : 1 ≤ left ∧ left < 2 ^ 32) :
    WP isa (round up) u fun v =>
      RInv s c (Spec.Cast5.round (Spec.Cast5.scheduleAt s.mem (State.addr kb)) i lr)
        (if up then kb + BitVec.ofNat 32 (4 * (i - 1)) + 4 else kb + BitVec.ofNat 32 (4 * (i - 1)) - 4)
        (nextT up t) (left - 1) v ∧ v.z = (BitVec.ofNat 32 left - 1 == 0) := by
  have aS := h.aS
  have e0 : State.addr (u.gpr .lr + BitVec.ofNat 32 0) = State.addr kb + BitVec.ofNat 64 (4 * (i - 1)) := by
    rw [hu.lr, kp_addr h.kfit 0 (by omega_arith), Nat.add_zero]
  have e64 : State.addr (u.gpr .lr + BitVec.ofNat 32 64) = State.addr kb + BitVec.ofNat 64 (4 * (15 + i)) := by
    rw [hu.lr, kp_addr h.kfit 64 (by omega_arith)]; congr 2; omega_arith
  have es (off : Nat) (ho : off < 256) : slot u off = State.addr c + BitVec.ofNat 64 off := by
    rw [hu.r12, aS off ho]
  have pre : RoundPre u ((Spec.Cast5.scheduleAt s.mem (State.addr kb)).getD (i - 1) 0)
      ((Spec.Cast5.scheduleAt s.mem (State.addr kb)).getD (15 + i) 0) lr.1 lr.2 t (BitVec.ofNat 32 left) :=
    { r2 := hu.r2
      r3 := hu.r3
      inM := by rw [e0, hu.rd, hu.wr]; exact h.inK (by omega_arith)
      valM := by rw [e0]; exact key_at h hu.fr hi (.inl rfl)
      inR := by rw [e64, hu.rd, hu.wr]; exact h.inK (by omega_arith)
      valR := by rw [e64]; exact key_at h hu.fr hi (.inr rfl)
      ht := ht
      inT := by rw [es 20 (by decide), hu.wr]; exact h.inS (by decide)
      valT := by rw [es 20 (by decide)]; exact hu.typ
      inC := by rw [es 16 (by decide), hu.wr]; exact h.inS (by decide)
      valC := by rw [es 16 (by decide)]; exact hu.cnt
      sep := by rw [es 16 (by decide), es 20 (by decide)]; exact Offset.sep _ (by decide) (by decide) (by decide)
      cfit := by rw [hu.r12]; have := h.cfit; omega_arith
      inS := fun {off w} hw => by
        rw [hu.r12, hu.wr, Offset.add_add]; exact h.inS (by omega_using [hw])
      tfit := by rw [hu.syms]; exact h.tfit
      trd := by rw [hu.syms, hu.rd, hu.wr]; exact h.trd
      held := by
        rw [hu.syms]
        refine held_frame hu.fr (fun r hr => ?_) (by rw [Impl.Cast5.s1234, table_length]; decide) h.held
        simp only [List.mem_singleton] at hr; subst hr
        rw [Impl.Cast5.s1234, table_length]
        exact h.dTS.sub_right (Offset.sub_base _ (by decide))
      dTS := by rw [hu.syms, hu.r12]; exact h.dTS.sub_right (Offset.sub_base _ (by decide)) }
  refine VG.Arm.WP.mono_syms (round_ok u up pre) fun v ⟨v2, v3, vlr, ⟨m₁, f₁, vm⟩, vz, vk⟩ vsy => ⟨⟨v2, ?_, ?_, ?_, ?_, ?_, ?_,
    vk.rd.trans hu.rd, vk.wr.trans hu.wr, vk.sp.trans hu.sp, vsy.trans hu.syms⟩, vz⟩
  · rw [v3, fT_eq ht hti]; rfl
  · rw [vlr, hu.lr]
  · rw [vk.gpr _ (by decide), hu.r12]
  · rw [vm, es 16 (by decide), es 20 (by decide)]
    rw [hu.r12] at f₁
    exact ((hu.fr.trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩)).writeW
      List.mem_cons_self _ (Offset.contains _ (by decide) (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains _ (by decide) (by decide) (by decide))
  · rw [vm, es 16 (by decide), es 20 (by decide), Mem.readW_writeW_self32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega_arith
  · rw [vm, es 16 (by decide), es 20 (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

/-- The rounds loop, for any order of the rounds: round `idx i` is the
`i`-th, with its subkeys at `kpf i` and its type `tf i`, and the halves
before it `fold i`. -/
theorem rounds_ok {s u : State} {c p kb : BitVec 32} {n : Nat} (h : BPre s c p kb n) (up : Bool)
    (idx : Nat → Nat) (kpf : Nat → BitVec 32) (tf : Nat → Nat) (fold : Nat → Spec.Cast5.Word × Spec.Cast5.Word)
    (hidx : ∀ i < n, 1 ≤ idx i ∧ idx i ≤ 16) (hkp : ∀ i < n, kpf i = kb + BitVec.ofNat 32 (4 * (idx i - 1)))
    (ht : ∀ i < n, tf i = 1 ∨ tf i = 2 ∨ tf i = 3) (hti : ∀ i < n, tf i % 3 = idx i % 3)
    (hfold : ∀ i < n, fold (i + 1) = Spec.Cast5.round (Spec.Cast5.scheduleAt s.mem (State.addr kb)) (idx i) (fold i))
    (hnext : ∀ i, i + 1 < n → kpf (i + 1) = (if up then kpf i + 4 else kpf i - 4) ∧ tf (i + 1) = nextT up (tf i))
    (h0 : RInv s c (fold 0) (kpf 0) (tf 0) n u) :
    WP isa (.loop (round up) .ne) u fun v => ∃ kp t, RInv s c (fold n) kp t 0 v := by
  have hn : n = 12 ∨ n = 16 := h.nv
  refine WP.loop (M := isa) (fun m (v : State) => ∃ i, m = n - i ∧ i < n ∧ RInv s c (fold i) (kpf i) (tf i) (n - i) v)
    ?_ n u ⟨0, rfl, by omega_arith, by rw [Nat.sub_zero]; exact h0⟩
  rintro m v ⟨i, rfl, hi, hv⟩
  rw [hkp i hi] at hv
  refine WP.mono (round_step h hv up (ht i hi) (hti i hi) (hidx i hi) (by omega_arith)) fun w ⟨hw, wz⟩ => ?_
  rw [← hfold i hi, ← hkp i hi] at hw
  by_cases hlast : i + 1 = n
  · refine .inl ⟨?_, _, _, by rw [hlast] at hw; rw [show n - i - 1 = 0 by omega_arith] at hw; exact hw⟩
    show some (!w.z) = _; rw [wz]
    congr 1
    rw [show n - i = 1 by omega_arith]
    rfl
  · obtain ⟨hk, htn⟩ := hnext i (by omega_arith)
    refine .inr ⟨?_, n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, ?_⟩
    · show some (!w.z) = _; rw [wz]
      congr 1
      have : BitVec.ofNat 32 (n - i) - 1 ≠ 0 := by
        intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl,
          show (0 : BitVec 32).toNat = 0 from rfl] at this
        omega_arith
      simpa using this
    · rw [hk, htn, show n - (i + 1) = n - i - 1 by omega_arith]
      exact hw

theorem nextT_up (i : Nat) : nextT true (i % 3 + 1) = (i + 1) % 3 + 1 := by
  simp only [nextT, ite_true]
  split <;> omega_arith

/-! ## The block function -/

/-- Storing the word read: nothing changes. -/
theorem writeW_readW (m : Mem) (a : Addr) : m.writeW a (m.readW a 32) = m := by
  funext x
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq, show 32 / 8 = 4 from rfl]
  split
  · rename_i h
    rw [← Mem.readW_byte m a h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  · rfl


/-- The memory after the start of a block: the count and type of rounds. -/
theorem start_frame {m : Mem} {c : BitVec 32} (x y : BitVec 32) :
    Frame [ctRegion c] m ((m.writeW (State.addr c + BitVec.ofNat 64 16) x).writeW
      (State.addr c + BitVec.ofNat 64 20) y) :=
  ((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains _ (by decide) (by decide) (by decide))).writeW
    List.mem_cons_self _ (Offset.contains _ (by decide) (by decide) (by decide))

theorem start_cnt (m : Mem) (c x y : BitVec 32) :
    ((m.writeW (State.addr c + BitVec.ofNat 64 16) x).writeW (State.addr c + BitVec.ofNat 64 20) y).readW
      (State.addr c + BitVec.ofNat 64 16) 32 = x := by
  rw [Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem start_typ (m : Mem) (c x y : BitVec 32) :
    ((m.writeW (State.addr c + BitVec.ofNat 64 16) x).writeW (State.addr c + BitVec.ofNat 64 20) y).readW
      (State.addr c + BitVec.ofNat 64 20) 32 = y := Mem.readW_writeW_self32 _ _ _

theorem decode_start (s : State) (p : BitVec 32) :
    (byteRev32 (s.mem.readW (State.addr p + BitVec.ofNat 64 0) 32),
      byteRev32 (s.mem.readW (State.addr p + BitVec.ofNat 64 4) 32)) =
      Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (State.addr p)) := by
  rw [Proof.Cast5.decodeBlock_blockAt, BitVec.add_zero]

theorem startEnc_ok {s : State} {c p kb : BitVec 32} {n : Nat} (h : BPre s c p kb n) :
    WP isa (.block startEnc) s (RInv s c (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (State.addr p)))
      (kb + BitVec.ofNat 32 (4 * 0)) (0 % 3 + 1) n) := by
  have aS := h.aS
  have aP := h.aP
  have inS := fun {off w : Nat} (hw : off + w ≤ 256) => h.inS (off := off) (w := w) hw
  have inS' := fun {off w : Nat} (hw : off + w ≤ 256) => h.inS' (off := off) (w := w) hw
  have inP' := fun {off w : Nat} (hw : off + w ≤ 8) => h.inP' (off := off) (w := w) hw
  unfold startEnc
  crun [dataOff, schedOff, roundsOff, cntOff, typeOff, h.r12, aS, aP, inS, inS', inP', h.data, h.sched,
    h.rounds, rev_eq, RInv_iff, syms_setReg, syms_mem]
  exact ⟨by rw [← decode_start s p], by rw [← decode_start s p], by bv_omega, start_frame _ _, start_cnt _ _ _ _,
    start_typ _ _ _ _⟩

theorem startDec_ok {s : State} {c p kb : BitVec 32} {n : Nat} (h : BPre s c p kb n) :
    WP isa (.block startDec) s (RInv s c (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (State.addr p)))
      (kb + BitVec.ofNat 32 (4 * (n - 1 - 0))) ((n - 1 - 0) % 3 + 1) n) := by
  have aS := h.aS
  have aP := h.aP
  have inS := fun {off w : Nat} (hw : off + w ≤ 256) => h.inS (off := off) (w := w) hw
  have inS' := fun {off w : Nat} (hw : off + w ≤ 256) => h.inS' (off := off) (w := w) hw
  have inP' := fun {off w : Nat} (hw : off + w ≤ 8) => h.inP' (off := off) (w := w) hw
  unfold startDec
  crun [dataOff, schedOff, roundsOff, cntOff, typeOff, h.r12, aS, aP, inS, inS', inP', h.data, h.sched,
    h.rounds, rev_eq, RInv_iff, syms_setReg, syms_mem]
  refine ⟨by rw [← decode_start s p], by rw [← decode_start s p], ?_, start_frame _ _, start_cnt _ _ _ _, ?_⟩
  · rcases h.nv with rfl | rfl <;> bv_omega
  · rw [start_typ]
    rcases h.nv with rfl | rfl <;> rfl

/-- What the block function does. -/
def BPost (s : State) (c p : BitVec 32) (out : Spec.Cast5.Block) (t : State) : Prop :=
  Spec.Cast5.blockAt t.mem (State.addr p) = out ∧
  Frame [⟨State.addr p, 8⟩, ctRegion c] s.mem t.mem ∧ t.gpr .r12 = c ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp

theorem finish_ok {s u : State} {c p kb : BitVec 32} {n : Nat} (h : BPre s c p kb n)
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} {kp : BitVec 32} {t : Nat} (hu : RInv s c lr kp t 0 u) :
    WP isa (.block finish) u (BPost s c p (Spec.Cast5.encodeBlock (lr.2, lr.1))) := by
  have aS := h.aS
  have aP := h.aP
  have sl (off : Nat) (ho : off + 4 ≤ 16) :
      u.mem.readW (State.addr c + BitVec.ofNat 64 off) 32 = s.mem.readW (State.addr c + BitVec.ofNat 64 off) 32 :=
    hu.fr.readW (r := ⟨State.addr c + BitVec.ofNat 64 off, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by decide)) (by decide)
  have hd : u.mem.readW (State.addr c + BitVec.ofNat 64 0) 32 = p := (sl 0 (by decide)).trans h.data
  have inS' : ∀ {off w : Nat}, off + w ≤ 256 → InRegions (u.rd ++ u.wr) (State.addr c + BitVec.ofNat 64 off) w :=
    fun hw => by rw [hu.rd, hu.wr]; exact h.inS' hw
  have inS : ∀ {off w : Nat}, off + w ≤ 256 → InRegions u.wr (State.addr c + BitVec.ofNat 64 off) w :=
    fun hw => by rw [hu.wr]; exact h.inS hw
  have inP0 : InRegions u.wr (State.addr p + BitVec.ofNat 64 0) 4 := by rw [hu.wr]; exact h.inP (by decide)
  have inP4 : InRegions u.wr (State.addr p + BitVec.ofNat 64 4) 4 := by rw [hu.wr]; exact h.inP (by decide)
  -- The block's stores leave the slots alone.
  obtain ⟨m', hm'⟩ : ∃ m', (u.mem.writeW (State.addr p + BitVec.ofNat 64 0) (byteRev32 lr.2)).writeW
      (State.addr p + BitVec.ofNat 64 4) (byteRev32 lr.1) = m' := ⟨_, rfl⟩
  have ms (off : Nat) (ho : off + 4 ≤ 16) :
      m'.readW (State.addr c + BitVec.ofNat 64 off) 32 = u.mem.readW (State.addr c + BitVec.ofNat 64 off) 32 := by
    have dPC : Region.Disjoint ⟨State.addr p, 8⟩ ⟨State.addr c + BitVec.ofNat 64 off, 4⟩ :=
      h.dPS.sub_right (Offset.sub_base _ (by omega_arith))
    rw [← hm', Mem.readW_writeW_sep (dPC.symm.sep (Region.contains_self _ _)
        (Offset.contains_base _ (by decide) (by decide))) (by decide),
      Mem.readW_writeW_sep (dPC.symm.sep (Region.contains_self _ _)
        (Offset.contains_base _ (by decide) (by decide))) (by decide)]
  unfold finish
  crun [dataOff, nOff, schedOff, roundsOff, hu.r12, aS, aP, inS, inS', inP0, inP4, hd, hu.r2, hu.r3, rev_eq, hm']
  have e : (((m'.writeW (State.addr c + BitVec.ofNat 64 0) p).writeW (State.addr c + BitVec.ofNat 64 4)
      (u.mem.readW (State.addr c + BitVec.ofNat 64 4) 32)).writeW (State.addr c + BitVec.ofNat 64 8)
      (u.mem.readW (State.addr c + BitVec.ofNat 64 8) 32)).writeW (State.addr c + BitVec.ofNat 64 12)
      (u.mem.readW (State.addr c + BitVec.ofNat 64 12) 32) = m' := by
    rw [← ms 4 (by decide), ← ms 8 (by decide), ← ms 12 (by decide),
      show p = m'.readW (State.addr c + BitVec.ofNat 64 0) 32 from ((ms 0 (by decide)).trans hd).symm,
      writeW_readW, writeW_readW, writeW_readW, writeW_readW]
  rw [e]
  refine ⟨?_, ?_, by simp only [gpr_setReg, reduceCtorEq, ite_false, hu.r12], hu.rd, hu.wr, hu.sp⟩
  · show Spec.Cast5.blockAt m' _ = _
    rw [← hm', BitVec.add_zero, Proof.Cast5.blockAt_write]
  · show Frame _ s.mem m'
    rw [← hm']
    have f1 := (hu.fr.mono (rs' := [⟨State.addr p, 8⟩, ctRegion c]) (by simp)).writeW List.mem_cons_self
      (byteRev32 lr.2) (Offset.contains_base (State.addr p) (d := 0) (n := 4) (k := 8) (by decide) (by decide))
    exact f1.writeW List.mem_cons_self (byteRev32 lr.1)
      (Offset.contains_base (State.addr p) (d := 4) (n := 4) (k := 8) (by decide) (by decide))

theorem crypt_ok {s : State} {c p kb : BitVec 32} {n : Nat} (h : BPre s c p kb n) (up : Bool) :
    WP isa (crypt up) s (BPost s c p (cipher up (Spec.Cast5.scheduleAt s.mem (State.addr kb)) n
      (Spec.Cast5.blockAt s.mem (State.addr p)))) := by
  have hn := h.nv
  cases up
  · unfold crypt
    simp only [Bool.false_eq_true, ite_false]
    refine WP.seq (WP.mono (startDec_ok h) fun u hu => ?_)
    refine WP.seq (WP.mono (rounds_ok h false (fun i => n - i) (fun i => kb + BitVec.ofNat 32 (4 * (n - 1 - i)))
      (fun i => (n - 1 - i) % 3 + 1) (fun i => decFold _ n i _) (fun i hi => by omega_arith)
      (fun i hi => by congr 2; omega_arith) (fun i hi => by omega_arith) (fun i hi => by omega_arith)
      (fun i hi => decFold_succ _ _ _ _) (fun i hi => ⟨?_, ?_⟩) hu) fun v ⟨kp, t, hv⟩ => ?_)
    · simp only [Bool.false_eq_true, ite_false]
      rw [show n - 1 - i = n - 1 - (i + 1) + 1 by omega_arith, Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc]
      exact (BitVec.add_sub_cancel _ _).symm
    · rw [show n - 1 - i = n - 1 - (i + 1) + 1 by omega_arith]
      simp only [nextT, Bool.false_eq_true, ite_false]
      split <;> omega_arith
    refine WP.mono (finish_ok h hv) fun w hw => ?_
    rw [cipher, ite_eq_right Bool.false_ne_true, decryptBlock_eq]
    exact hw
  · unfold crypt
    simp only [ite_true]
    refine WP.seq (WP.mono (startEnc_ok h) fun u hu => ?_)
    refine WP.seq (WP.mono (rounds_ok h true (fun i => i + 1) (fun i => kb + BitVec.ofNat 32 (4 * i))
      (fun i => i % 3 + 1) (fun i => encFold _ i _) (fun i hi => by omega_arith)
      (fun i hi => by rw [Nat.add_sub_cancel]) (fun i hi => by omega_arith) (fun i hi => by omega_arith)
      (fun i hi => encFold_succ _ _ _) (fun i hi => ⟨?_, (nextT_up i).symm⟩) hu) fun v ⟨kp, t, hv⟩ => ?_)
    · simp only [ite_true]
      rw [Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    refine WP.mono (finish_ok h hv) fun w hw => ?_
    rw [cipher, ite_eq_left rfl, encryptBlock_eq]
    exact hw

end VG.Proof.Cast5.Arm

end

end

/-!
# CAST5 on ARMv7: ECB

`ecb up` takes the working space from the stack, saves the callee-saved
registers in it, keeps its arguments in their slots, runs the block function
on each block in turn (`ecbLoop_ok`) and restores the registers
(`ecb_correct`).
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5.Arm
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)

/-! ## Frames of the layouts -/

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Q : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨Q, 8⟩ r) : Spec.Cast5.blockAt m' Q = Spec.Cast5.blockAt m Q := by
  apply Vector.ext
  intro j hj
  rw [Proof.Cast5.blockAt_get _ _ hj, Proof.Cast5.blockAt_get _ _ hj]
  exact hf.bytes (R := ⟨Q, 8⟩) hd (by show (8 : Nat) ≤ 2 ^ 64; decide) hj

theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨K, 128⟩ r) : Spec.Cast5.scheduleAt m' K = Spec.Cast5.scheduleAt m K := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Cast5.scheduleAt, Vector.getElem_ofFn]
  rw [hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 3 < 128 by omega_arith),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 2 < 128 by omega_arith),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 1 < 128 by omega_arith),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i < 128 by omega_arith)]

/-! ## The saved registers -/

def savedSlots : List (Reg × Nat) := saved.zipIdx.map fun (r, i) => (r, savedOff + 4 * i)

theorem save_eq : save = savedSlots.map fun p => Instr.str p.1 .r12 p.2 := rfl
theorem restore_eq : restore = savedSlots.map fun p => Instr.ldr p.1 .r12 p.2 := rfl
theorem savedSlots_ok : Spill.Slots 64 100 savedSlots := by decide
theorem savedSlots_restorable : Spill.Restorable .r12 savedSlots := by decide
theorem savedSlots_preserved : ∀ r ∈ preserved, r ∈ savedSlots.map Prod.fst := by decide
/-! ## The loop over the blocks -/

/-- The state of ECB with `j` of the `N` blocks at `d` done, from the memory
`m0` after the setup: the slots, the blocks, and nothing else written but the
data and the first 64 bytes of the working space at `c`; the table
`VG_CAST5_S1234` still held. -/
structure LInv (s : State) (m0 : Mem) (up : Bool) (k : Spec.Cast5.Schedule) (c d kb : BitVec 32) (n N j : Nat)
    (u : State) : Prop where
  r12 : u.gpr .r12 = c
  fr : Frame [⟨State.addr d, 8 * N⟩, ⟨State.addr c, 64⟩] m0 u.mem
  blocks : ∀ i < N, Spec.Cast5.blockAt u.mem (State.addr d + BitVec.ofNat 64 (8 * i)) =
    if i < j then cipher up k n (Spec.Cast5.blockAt m0 (State.addr d + BitVec.ofNat 64 (8 * i)))
    else Spec.Cast5.blockAt m0 (State.addr d + BitVec.ofNat 64 (8 * i))
  dslot : u.mem.readW (State.addr c + BitVec.ofNat 64 0) 32 = d + BitVec.ofNat 32 (8 * j)
  nslot : u.mem.readW (State.addr c + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 (N - j)
  sslot : u.mem.readW (State.addr c + BitVec.ofNat 64 8) 32 = kb
  rslot : u.mem.readW (State.addr c + BitVec.ofNat 64 12) 32 = BitVec.ofNat 32 n
  sk : Spec.Cast5.scheduleAt u.mem (State.addr kb) = k
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  sp : u.sp = s.sp
  syms : u.syms = s.syms
  held : Held u.mem (State.addr (s.syms s1234Sym)) s1234

/-- What the loop needs of the layout: the schedule at `kb`, the `N` blocks at
`d` and the working space at `c`, separate and within the address space;
the table `VG_CAST5_S1234`, readable, within the address space and apart
from the blocks and the working space. -/
structure Lay (s : State) (c d kb : BitVec 32) (n N : Nat) : Prop where
  cfit : c.toNat + 256 ≤ 2 ^ 32
  dfit : d.toNat + 8 * N ≤ 2 ^ 32
  kfit : kb.toNat + 128 ≤ 2 ^ 32
  scr : (⟨State.addr c, 256⟩ : Region) ∈ s.wr
  dat : (⟨State.addr d, 8 * N⟩ : Region) ∈ s.wr
  sch : (⟨State.addr kb, 128⟩ : Region) ∈ s.rd ++ s.wr
  dDS : Region.Disjoint ⟨State.addr d, 8 * N⟩ ⟨State.addr c, 256⟩
  dKS : Region.Disjoint ⟨State.addr kb, 128⟩ ⟨State.addr c, 256⟩
  dKD : Region.Disjoint ⟨State.addr kb, 128⟩ ⟨State.addr d, 8 * N⟩
  nv : n = 12 ∨ n = 16
  tfit : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  trd : (⟨State.addr (s.syms s1234Sym), 4096⟩ : Region) ∈ s.rd ++ s.wr
  dTD : Region.Disjoint ⟨State.addr (s.syms s1234Sym), 4096⟩ ⟨State.addr d, 8 * N⟩
  dTS : Region.Disjoint ⟨State.addr (s.syms s1234Sym), 4096⟩ ⟨State.addr c, 256⟩

theorem addr_blk {d : BitVec 32} {N j : Nat} (hd : d.toNat + 8 * N ≤ 2 ^ 32) (hj : j < N) :
    State.addr (d + BitVec.ofNat 32 (8 * j)) = State.addr d + BitVec.ofNat 64 (8 * j) := addr_add (by omega_arith)

theorem sub_blk (D : Addr) {N j : Nat} (hj : j < N) :
    Region.Sub ⟨D + BitVec.ofNat 64 (8 * j), 8⟩ ⟨D, 8 * N⟩ := Offset.sub_base _ (by omega_arith)

theorem sub_c64 (C : Addr) : Region.Sub ⟨C, 64⟩ ⟨C, 256⟩ := fun x hx => by
  simp only [Region.Contains] at hx ⊢; omega_arith

theorem sub_ct256 (C : Addr) : Region.Sub ⟨C + BitVec.ofNat 64 16, 48⟩ ⟨C, 256⟩ := Offset.sub_base _ (by decide)

theorem sub_ct (C : Addr) : Region.Sub ⟨C + BitVec.ofNat 64 16, 48⟩ ⟨C, 64⟩ := Offset.sub_base _ (by decide)

theorem s1234_len : 8 * s1234.length = 4096 := by rw [s1234, table_length]

/-- The block function's precondition, at block `j`. -/
theorem LInv.bpre {s u : State} {m0 : Mem} {up : Bool} {k : Spec.Cast5.Schedule} {c d kb : BitVec 32} {n N j : Nat}
    (hl : Lay s c d kb n N) (h : LInv s m0 up k c d kb n N j u) (hj : j < N) :
    BPre u c (d + BitVec.ofNat 32 (8 * j)) kb n where
  r12 := h.r12
  cfit := hl.cfit
  pfit := by
    have := hl.dfit
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * j) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  kfit := hl.kfit
  scr := by rw [h.wr]; exact hl.scr
  blk := fun {off w} hw => by
    have := hl.dfit
    rw [addr_blk hl.dfit hj, Proof.Cast5.add_ofNat_add, h.wr]
    exact ⟨_, hl.dat, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  sch := by rw [h.rd, h.wr]; exact hl.sch
  dPS := by rw [addr_blk hl.dfit hj]; exact hl.dDS.sub_left (sub_blk _ hj)
  dKS := hl.dKS
  dKP := by rw [addr_blk hl.dfit hj]; exact hl.dKD.sub_right (sub_blk _ hj)
  data := h.dslot
  sched := h.sslot
  rounds := h.rslot
  nv := hl.nv
  tfit := by rw [h.syms]; exact hl.tfit
  trd := by rw [h.syms, h.rd, h.wr]; exact hl.trd
  held := by rw [h.syms]; exact h.held
  dTS := by rw [h.syms]; exact hl.dTS

theorem ofNat_sub_one {a : Nat} (ha : 1 ≤ a) (hb : a < 2 ^ 32) :
    BitVec.ofNat 32 a - 1 = BitVec.ofNat 32 (a - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
  omega_arith

/-- `advance`: on to the next block. -/
theorem advance_ok (v : State) {c : BitVec 32} (hc : v.gpr .r12 = c) (hcf : c.toNat + 256 ≤ 2 ^ 32)
    (hin : ∀ {off w : Nat}, off + w ≤ 256 → InRegions v.wr (State.addr c + BitVec.ofNat 64 off) w) {x y : BitVec 32}
    (hx : v.mem.readW (State.addr c + BitVec.ofNat 64 0) 32 = x)
    (hy : (v.mem.writeW (State.addr c + BitVec.ofNat 64 0) (x + 8)).readW (State.addr c + BitVec.ofNat 64 4) 32 = y) :
    WP isa (.block advance) v fun w =>
      w.mem = (v.mem.writeW (State.addr c + BitVec.ofNat 64 0) (x + 8)).writeW (State.addr c + BitVec.ofNat 64 4) (y - 1) ∧
      w.z = (y - 1 == 0) ∧ w.gpr .r12 = c ∧ w.rd = v.rd ∧ w.wr = v.wr ∧ w.sp = v.sp := by
  obtain aS := addr_off hcf
  obtain hin' : ∀ {off w : Nat}, off + w ≤ 256 → InRegions (v.rd ++ v.wr) (State.addr c + BitVec.ofNat 64 off) w :=
    fun hw => by obtain ⟨g, hg, hcg⟩ := hin hw; exact ⟨g, List.mem_append_right _ hg, hcg⟩
  unfold advance
  crun [dataOff, nOff, hc, aS, hin, hin', hx, hy]

/-- A block and another, or the working space. -/
theorem blk_disj_blk (D : Addr) {N i j : Nat} (hi : i < N) (hj : j < N) (hN : 8 * N ≤ 2 ^ 32) (hij : i ≠ j) :
    Region.Disjoint ⟨D + BitVec.ofNat 64 (8 * i), 8⟩ ⟨D + BitVec.ofNat 64 (8 * j), 8⟩ :=
  Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- One block, then on to the next. -/
theorem step_ok {s u : State} {m0 : Mem} {up : Bool} {k : Spec.Cast5.Schedule} {c d kb : BitVec 32} {n N j : Nat}
    (hl : Lay s c d kb n N) (h : LInv s m0 up k c d kb n N j u) (hj : j < N) :
    WP isa (.seq (crypt up) (.block advance)) u fun w => LInv s m0 up k c d kb n N (j + 1) w ∧
      w.z = decide (j + 1 = N) := by
  have hcf := hl.cfit
  have hdf := hl.dfit
  obtain eP := addr_blk hdf hj
  refine WP.seq (VG.Arm.WP.mono_syms (crypt_ok (h.bpre hl hj) up) fun v ⟨vb, vf, v12, vrd, vwr, vsp⟩ vsy => ?_)
  rw [eP] at vb vf
  -- The regions the block function wrote, against the slots and the other blocks.
  have dCt (off : Nat) (ho : off + 4 ≤ 16) : ∀ r ∈ [(⟨State.addr d + BitVec.ofNat 64 (8 * j), 8⟩ : Region), ctRegion c],
      Region.Disjoint ⟨State.addr c + BitVec.ofNat 64 off, 4⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hl.dDS.sub_left (sub_blk _ hj)).symm.sub_left (Offset.sub_base _ (by omega_arith))
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by decide)
  have vslot (off : Nat) (ho : off + 4 ≤ 16) :
      v.mem.readW (State.addr c + BitVec.ofNat 64 off) 32 = u.mem.readW (State.addr c + BitVec.ofNat 64 off) 32 :=
    vf.readW (Region.contains_self _ _) (dCt off ho) (by decide)
  obtain hin : ∀ {off w : Nat}, off + w ≤ 256 → InRegions v.wr (State.addr c + BitVec.ofNat 64 off) w :=
    fun hw => by rw [vwr, h.wr]; exact ⟨_, hl.scr, Offset.contains_base _ hw (by omega_arith)⟩
  refine VG.Arm.WP.mono_syms (advance_ok v v12 hcf hin (x := d + BitVec.ofNat 32 (8 * j)) (y := BitVec.ofNat 32 (N - j))
    (by rw [vslot 0 (by decide)]; exact h.dslot)
    (by rw [Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      vslot 4 (by decide)]; exact h.nslot)) fun w ⟨wm, wz, w12, wrd, wwr, wsp⟩ wsy => ?_
  -- The writes of `advance`.
  obtain fw : Frame [⟨State.addr c, 64⟩] v.mem w.mem := by
    rw [wm]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
  have dC24 (R : Region) (hR : Region.Disjoint R ⟨State.addr c, 256⟩) : ∀ r ∈ [(⟨State.addr c, 64⟩ : Region)],
      Region.Disjoint R r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hR.sub_right (sub_c64 _)
  obtain frK : ∀ r ∈ [(⟨State.addr d + BitVec.ofNat 64 (8 * j), 8⟩ : Region), ctRegion c],
      Region.Disjoint ⟨State.addr kb, 128⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hl.dKD.sub_right (sub_blk _ hj)
    · exact hl.dKS.sub_right (sub_ct256 _)
  refine ⟨⟨w12, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, wrd.trans (vrd.trans h.rd), wwr.trans (vwr.trans h.wr),
    wsp.trans (vsp.trans h.sp), wsy.trans (vsy.trans h.syms), ?_⟩, ?_⟩
  · refine h.fr.trans ((vf.sub fun r hr => ?_).trans (fw.mono (by simp)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, sub_blk _ hj⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, sub_ct _⟩
  · have hdi : Region.Disjoint ⟨State.addr d + BitVec.ofNat 64 (8 * i), 8⟩ ⟨State.addr c, 256⟩ :=
      hl.dDS.sub_left (sub_blk _ hi)
    rw [blockAt_frame fw (dC24 _ hdi)]
    by_cases hij : i = j
    · subst hij
      rw [vb, ite_eq_left (by omega_arith), h.blocks i hi, ite_eq_right (by omega_arith), h.sk]
    · rw [blockAt_frame vf ?_, h.blocks i hi]
      · by_cases hlt : i < j
        · rw [ite_eq_left hlt, ite_eq_left (by omega_arith)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega_arith)]
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact blk_disj_blk _ hi hj (by omega_arith) hij
        · exact hdi.sub_right (sub_ct256 _)
  · rw [wm, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32, BitVec.add_assoc, Nat.mul_add, BitVec.ofNat_add (8 * j)]
    rfl
  · rw [wm, Mem.readW_writeW_self32, ofNat_sub_one (by omega_arith) (by omega_arith), Nat.sub_sub]
  · rw [wm, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), vslot 8 (by decide)]
    exact h.sslot
  · rw [wm, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), vslot 12 (by decide)]
    exact h.rslot
  · rw [scheduleAt_frame fw (dC24 _ hl.dKS), scheduleAt_frame vf frK]
    exact h.sk
  · refine held_frame fw (by rw [s1234_len]; exact dC24 _ hl.dTS) (by rw [s1234_len]; decide)
      (held_frame vf (fun r hr => ?_) (by rw [s1234_len]; decide) h.held)
    rw [s1234_len]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hl.dTD.sub_right (sub_blk _ hj)
    · exact hl.dTS.sub_right (sub_ct256 _)
  · rw [wz, ofNat_sub_one (by omega_arith) (by omega_arith)]
    by_cases he : j + 1 = N
    · rw [decide_eq_true he, show N - j - 1 = 0 by omega_arith]; rfl
    · rw [decide_eq_false he]
      have : BitVec.ofNat 32 (N - j - 1) ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl] at this
        omega_arith
      simpa using this

/-- The loop over the blocks, from `j = 0`: afterwards every block is done. -/
theorem ecbLoop_ok {s u : State} {m0 : Mem} {up : Bool} {k : Spec.Cast5.Schedule} {c d kb : BitVec 32} {n N : Nat}
    (hl : Lay s c d kb n N) (hN : 0 < N) (h : LInv s m0 up k c d kb n N 0 u) :
    WP isa (.loop (.seq (crypt up) (.block advance)) .ne) u (LInv s m0 up k c d kb n N N) := by
  refine WP.loop (M := isa) (fun m (v : State) => ∃ j, m = N - j ∧ j < N ∧ LInv s m0 up k c d kb n N j v)
    ?_ N u ⟨0, rfl, hN, h⟩
  rintro m v ⟨j, rfl, hj, hv⟩
  refine WP.mono (step_ok hl hv hj) fun w ⟨hw, wz⟩ => ?_
  by_cases he : j + 1 = N
  · exact .inl ⟨by show some (!w.z) = _; rw [wz, decide_eq_true he]; rfl, he ▸ hw⟩
  · exact .inr ⟨by show some (!w.z) = _; rw [wz, decide_eq_false he]; rfl, N - (j + 1), by omega_arith, j + 1, rfl,
      by omega_arith, hw⟩

/-! ## The whole function -/

section
variable {name : String} {ws : List (BitVec 64)} {st : Nat} {s : State}

/-- What the contract says of a function's one table: its words. -/
theorem ConstsOk.held1 (h : ConstsOk [(name, ws)] st s) : Held s.mem (State.addr (s.syms name)) ws :=
  h.2.1 _ List.mem_cons_self

/-- The code may read it. -/
theorem ConstsOk.rd1 (h : ConstsOk [(name, ws)] st s) :
    (⟨State.addr (s.syms name), 8 * ws.length⟩ : Region) ∈ s.rd := by
  obtain hm : (⟨State.addr (s.syms name), 8 * ws.length⟩ : Region) ∈
      s.rd.drop (s.rd.length - [(name, ws)].length) := by
    rw [h.1]; exact List.mem_cons_self
  exact List.mem_of_mem_drop hm

/-- No writable region overlaps it. -/
theorem ConstsOk.wr1 (h : ConstsOk [(name, ws)] st s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr (s.syms name), 8 * ws.length⟩ r :=
  (h.2.2.1 _ List.mem_cons_self).2.1

end

theorem stackArg_strip (K : List (String × List (BitVec 64))) (s : State) (i : Nat) :
    stackArg (stripConsts K s) i = stackArg s i := rfl
theorem stackArgAddr_strip (K : List (String × List (BitVec 64))) (s : State) (i : Nat) :
    stackArgAddr (stripConsts K s) i = stackArgAddr s i := rfl

/-- The ECB functions' contract on ARMv7, as their proof states it. -/
def ecbArm (up : Bool) : Contract isa where
  pre s :=
    let sch : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let dat : Region := ⟨State.addr (s.gpr .r2), 8 * (s.gpr .r3).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 0), 256⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [sch, args] ∧ s.wr = [dat, scr] ∧ sch.Disjoint dat ∧ sch.Disjoint scr ∧ dat.Disjoint scr ∧
      args.Disjoint dat ∧ args.Disjoint scr ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8 * (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 256 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 16)
  post s s' :=
    Spec.Cast5.blocksAt s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      Spec.Cast5.ecb (Spec.Cast5.scheduleAt s.mem (State.addr (s.gpr .r0))) (s.gpr .r1).toNat
        (if up then .encrypt else .decrypt) (Spec.Cast5.blocksAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

theorem cipher_map (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (bs : List Spec.Cast5.Block) :
    bs.map (cipher up k n) = Spec.Cast5.ecb k n (if up then .encrypt else .decrypt) bs := by
  cases up <;> rfl

/-- What the end needs: every block done, and nothing else written since the
setup but the first 64 bytes of the working space. -/
structure Done (s : State) (m0 : Mem) (up : Bool) (k : Spec.Cast5.Schedule) (c d : BitVec 32) (n N : Nat)
    (u : State) : Prop where
  r12 : u.gpr .r12 = c
  fr : Frame [⟨State.addr d, 8 * N⟩, ⟨State.addr c, 64⟩] m0 u.mem
  blocks : ∀ i < N, Spec.Cast5.blockAt u.mem (State.addr d + BitVec.ofNat 64 (8 * i)) =
    cipher up k n (Spec.Cast5.blockAt m0 (State.addr d + BitVec.ofNat 64 (8 * i)))
  rd : u.rd = s.rd
  wr : u.wr = s.wr

theorem LInv.done {s u : State} {m0 : Mem} {up : Bool} {k : Spec.Cast5.Schedule} {c d kb : BitVec 32} {n N : Nat}
    (h : LInv s m0 up k c d kb n N N u) : Done s m0 up k c d n N u :=
  ⟨h.r12, h.fr, fun i hi => by rw [h.blocks i hi, ite_eq_left hi], h.rd, h.wr⟩

/-- The end: the registers restored, and the blocks as the contract says. -/
theorem restore_ok {s u : State} {m0 : Mem} {up : Bool} {c : BitVec 32} (hc : c = stackArg s 0)
    (hs : (ecbArm up).pre (stripConsts ecbConsts s))
    (hsv : Spill.Saved m0 (State.addr c) (s.setReg .r12 c).gpr savedSlots)
    (hm0 : Frame [⟨State.addr c, 256⟩] s.mem m0)
    (h : Done s m0 up (Spec.Cast5.scheduleAt s.mem (State.addr (s.gpr .r0))) c (s.gpr .r2)
      (s.gpr .r1).toNat (s.gpr .r3).toNat u) :
    WP isa (.block restore) u fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (ecbArm up).post s s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dDS, _, _, _, hdf, hcf, _, _⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stackArg_strip] at hwr dKS dDS hdf hcf
  rw [← hc] at hcf dKS dDS hwr
  obtain hsv' : Spill.Saved u.mem (State.addr (u.gpr .r12)) (s.setReg .r12 c).gpr savedSlots := by
    rw [h.r12]
    refine hsv.frame savedSlots_ok h.fr fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dDS.sub_right (Offset.sub_base _ (by decide))).symm
    · exact Offset.disjoint_base _ (by decide) (by decide)
  rw [restore_eq]
  refine WP.mono (Spill.restore_block_ok savedSlots_ok savedSlots_restorable (by rw [h.r12]; omega_arith)
    (fun d _ hd => by
      rw [h.rd, h.wr, hwr, h.r12]
      exact ⟨⟨State.addr c, 256⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    hsv') fun s' ⟨hg, _, hm, _, _, _⟩ => ⟨fun r hr => ?_, ?_⟩
  · rw [Spill.restored_reg hg (savedSlots_preserved r hr)]
    exact gpr_setReg_of_ne _ _ (by intro e; subst e; exact absurd hr (by decide))
  · show Spec.Cast5.blocksAt s'.mem _ _ = _
    rw [hm, ← cipher_map]
    unfold Spec.Cast5.blocksAt
    rw [List.map_map]
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    simp only [Function.comp]
    rw [h.blocks i hi, blockAt_frame hm0 fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dDS.sub_left (sub_blk _ hi)]

/-- The arguments to their slots, then whether there are blocks. -/
theorem slots_ok (u : State) {c : BitVec 32} (hc : u.gpr .r12 = c) (hcf : c.toNat + 256 ≤ 2 ^ 32)
    (hin : ∀ {off w : Nat}, off + w ≤ 256 → InRegions u.wr (State.addr c + BitVec.ofNat 64 off) w) :
    WP isa (.block [.str .r2 .r12 dataOff, .str .r3 .r12 nOff, .str .r0 .r12 schedOff, .str .r1 .r12 roundsOff,
      .cmp .r3 (.imm 0)]) u fun w =>
      w.mem = (((u.mem.writeW (State.addr c + BitVec.ofNat 64 0) (u.gpr .r2)).writeW (State.addr c + BitVec.ofNat 64 4)
        (u.gpr .r3)).writeW (State.addr c + BitVec.ofNat 64 8) (u.gpr .r0)).writeW (State.addr c + BitVec.ofNat 64 12)
          (u.gpr .r1) ∧
      w.z = (u.gpr .r3 - 0 == 0) ∧ w.gpr = u.gpr ∧ w.rd = u.rd ∧ w.wr = u.wr ∧ w.sp = u.sp := by
  obtain aS := addr_off hcf
  unfold dataOff nOff schedOff roundsOff
  crun [hc, aS, hin]
  rfl

theorem slot_frame (m : Mem) (C : Addr) (a b x y : BitVec 32) :
    Frame [⟨C, 16⟩] m ((((m.writeW (C + BitVec.ofNat 64 0) a).writeW (C + BitVec.ofNat 64 4) b).writeW
      (C + BitVec.ofNat 64 8) x).writeW (C + BitVec.ofNat 64 12) y) :=
  ((((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
    List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
    List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
    List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))

theorem ecb_correct (up : Bool) (s : State) (hs : (ecbArm up).pre (stripConsts ecbConsts s))
    (hk : ConstsOk ecbConsts 0 s) :
    WP isa (ecb up) s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (ecbArm up).post s s' := by
  have hs₀ := hs
  obtain ⟨hrd, hwr, dKD, dKS, dDS, _, _, hkf, hdf, hcf, _, hn⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stackArg_strip, stackArgAddr_strip] at hrd hwr dKD dKS dDS hkf
  simp only [stripConsts_gpr, stackArg_strip] at hdf hcf hn
  obtain tfit : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32 := s1234_len ▸ hk.fit List.mem_cons_self
  obtain trd : (⟨State.addr (s.syms s1234Sym), 4096⟩ : Region) ∈ s.rd := s1234_len ▸ ConstsOk.rd1 hk
  obtain twr : ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr (s.syms s1234Sym), 4096⟩ r := s1234_len ▸ ConstsOk.wr1 hk
  obtain held : Held s.mem (State.addr (s.syms s1234Sym)) s1234 := ConstsOk.held1 hk
  obtain ⟨c, hc⟩ : ∃ c, c = stackArg s 0 := ⟨_, rfl⟩
  rw [← hc] at hcf dKS dDS hwr
  obtain hargs : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 0)) 4 :=
    ⟨⟨stackArgAddr s 0, 4⟩, List.mem_append_left _ (stripConsts_rd_mem (by rw [hrd]; simp)), Region.contains_self _ _⟩
  obtain inC : ∀ {off w : Nat}, off + w ≤ 256 → InRegions s.wr (State.addr c + BitVec.ofNat 64 off) w :=
    fun hw => ⟨⟨State.addr c, 256⟩, by rw [hwr]; simp, Offset.contains_base _ hw (by omega_arith)⟩
  unfold ecb
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  -- The working space, and the saved registers.
  obtain h1 : WP isa (.block [.ldrSp .r12 0]) s fun s₁ => s₁ = s.setReg .r12 c := by
    crun [hargs]
    rw [hc]; rfl
  refine WP.mono h1 fun s₁ e₁ => ?_
  subst e₁
  rw [WP.block_append_iff, save_eq]
  refine VG.Arm.WP.mono_syms (WP.keep [] (Spill.save_block_ok savedSlots_ok (s := s.setReg .r12 c)
    (by simp only [gpr_setReg_self]; omega_arith) fun d _ hd => by simp only [gpr_setReg_self, wr_setReg]; exact inC (by omega_arith))
    (by decide)) fun s₂ ⟨⟨g₂, rd₂, wr₂, m₂⟩, k₂⟩ sy₂ => ?_
  simp only [gpr_setReg_self] at m₂
  obtain c₂ : s₂.gpr .r12 = c := by rw [g₂, gpr_setReg_self]
  refine VG.Arm.WP.mono_syms (slots_ok s₂ c₂ hcf fun hw => by rw [wr₂]; exact inC hw)
    fun s₃ ⟨m₃, z₃, g₃, rd₃, wr₃, sp₃⟩ sy₃ => ?_
  -- The memory after the setup.
  obtain ⟨m0, hm0e⟩ : ∃ m0, s₃.mem = m0 := ⟨_, rfl⟩
  obtain hsv : Spill.Saved m0 (State.addr c) (s.setReg .r12 c).gpr savedSlots := by
    rw [← hm0e, m₃, m₂]
    refine (Spill.saveMem_saved _ _ _ _ savedSlots_ok).frame savedSlots_ok (slot_frame _ _ _ _ _ _) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (by decide) (by decide)
  obtain hm0 : Frame [⟨State.addr c, 256⟩] s.mem m0 := by
    rw [← hm0e, m₃, m₂]
    exact (Spill.saveMem_frame _ _ _ (by decide) _ (by decide)).trans
      ((slot_frame _ _ _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, fun x hx => by simp only [Region.Contains] at hx ⊢; omega_arith⟩)
  have g₃' (r : Reg) (hr : r ≠ .r12) : s₃.gpr r = s.gpr r := by
    rw [g₃, g₂]; exact gpr_setReg_of_ne _ _ hr
  obtain rd₃' : s₃.rd = s.rd := rd₃.trans rd₂
  obtain wr₃' : s₃.wr = s.wr := wr₃.trans wr₂
  obtain sp₃' : s₃.sp = s.sp := sp₃.trans k₂.sp
  obtain lay : Lay s c (s.gpr .r2) (s.gpr .r0) (s.gpr .r1).toNat (s.gpr .r3).toNat :=
    { cfit := hcf, dfit := hdf, kfit := hkf, scr := by rw [hwr]; simp, dat := by rw [hwr]; simp,
      sch := List.mem_append_left _ (stripConsts_rd_mem (by rw [hrd]; simp)), dDS := dDS, dKS := dKS, dKD := dKD,
      nv := hn, tfit := tfit, trd := List.mem_append_left _ trd, dTD := twr _ (by rw [hwr]; simp),
      dTS := twr _ (by rw [hwr]; simp) }
  obtain done : ∀ u : State, Done s m0 up (Spec.Cast5.scheduleAt s.mem (State.addr (s.gpr .r0))) c (s.gpr .r2)
      (s.gpr .r1).toNat (s.gpr .r3).toNat u → WP isa (.block restore) u fun s' =>
        (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (ecbArm up).post s s' :=
    fun u hu => restore_ok hc hs₀ hsv hm0 hu
  refine WP.seq (WP.mono (Q := Done s m0 up (Spec.Cast5.scheduleAt s.mem (State.addr (s.gpr .r0))) c (s.gpr .r2)
    (s.gpr .r1).toNat (s.gpr .r3).toNat) ?_ done)
  refine wp_ite_eq (fun hz => WP.block_nil ⟨by rw [g₃, g₂, gpr_setReg_self], by rw [hm0e]; exact Frame.refl _ _,
      fun i hi => ?_, rd₃', wr₃'⟩) (fun hz => ?_)
  · rw [z₃, g₂, gpr_setReg_of_ne _ _ (by decide)] at hz
    obtain h0 : s.gpr .r3 - 0 = 0 := beq_iff_eq.mp hz
    have : (s.gpr .r3).toNat = 0 := by bv_omega_arith
    omega_arith
  · have hN : 0 < (s.gpr .r3).toNat := by
      rw [z₃, g₂, gpr_setReg_of_ne _ _ (by decide)] at hz
      obtain h0 : s.gpr .r3 - 0 ≠ 0 := fun e => by rw [e] at hz; exact absurd hz (by decide)
      bv_omega_arith
    obtain l0 : LInv s m0 up (Spec.Cast5.scheduleAt s.mem (State.addr (s.gpr .r0))) c (s.gpr .r2) (s.gpr .r0)
        (s.gpr .r1).toNat (s.gpr .r3).toNat 0 s₃ :=
      { r12 := by rw [g₃, g₂, gpr_setReg_self]
        fr := by rw [hm0e]; exact Frame.refl _ _
        blocks := fun i hi => by rw [ite_eq_right (Nat.not_lt_zero _), hm0e]
        dslot := by
          rw [hm0e, ← hm0e, m₃, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
            Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
            Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
            Mem.readW_writeW_self32, g₂, gpr_setReg_of_ne _ _ (by decide)]
          exact (BitVec.add_zero _).symm
        nslot := by
          rw [hm0e, ← hm0e, m₃, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
            Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
            Mem.readW_writeW_self32, g₂, gpr_setReg_of_ne _ _ (by decide), Nat.sub_zero, BitVec.ofNat_toNat,
            BitVec.setWidth_eq]
        sslot := by
          rw [hm0e, ← hm0e, m₃, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
            Mem.readW_writeW_self32, g₂, gpr_setReg_of_ne _ _ (by decide)]
        rslot := by
          rw [hm0e, ← hm0e, m₃, Mem.readW_writeW_self32, g₂, gpr_setReg_of_ne _ _ (by decide), BitVec.ofNat_toNat,
            BitVec.setWidth_eq]
        sk := by
          rw [hm0e]
          exact scheduleAt_frame hm0 fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKS
        rd := rd₃'
        wr := wr₃'
        sp := sp₃'
        syms := by rw [sy₃, sy₂]; rfl
        held := by
          rw [hm0e]
          refine held_frame hm0 (fun r hr => ?_) (by rw [s1234_len]; decide) held
          simp only [List.mem_singleton] at hr; subst hr
          rw [s1234_len]; exact twr _ (by rw [hwr]; simp) }
    exact WP.mono (ecbLoop_ok lay hN l0) fun u hu => hu.done

end VG.Proof.Cast5.Arm
