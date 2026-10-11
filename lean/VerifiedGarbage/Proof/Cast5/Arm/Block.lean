import VerifiedGarbage.Proof.Cast5.Arm.Round
import VerifiedGarbage.Proof.Cast5.Memory

/-!
# CAST5 on ARMv7: the block function

`crypt up` encrypts (`up`) or decrypts the block whose address is in the
data slot of the working space at `r12`, in place, with the schedule and the
number of rounds in their slots (`crypt_ok`). Besides the block it writes
only the slots of the count and type of rounds (`cntOff`, `typeOff`), and it
keeps `r12`: this is the block function a mode reuses.
-/

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5.Arm
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

/-- The slots of the count and type of rounds. -/
abbrev ctRegion (c : BitVec 32) : Region := ⟨State.addr c + BitVec.ofNat 64 16, 8⟩

/-- What the block function needs: the working space at `c` in `r12`, the
block at `p` (in the data slot), the schedule at `kb` (in its slot) and the
number of rounds `n` (in its slot). -/
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

section
variable {s : State} {c p kb : BitVec 32} {n : Nat} (h : BPre s c p kb n)
include h

theorem BPre.inS {off w : Nat} (hw : off + w ≤ 256) : InRegions s.wr (State.addr c + BitVec.ofNat 64 off) w :=
  ⟨_, h.scr, Offset.contains_base _ hw (by omega)⟩

theorem BPre.inS' {off w : Nat} (hw : off + w ≤ 256) :
    InRegions (s.rd ++ s.wr) (State.addr c + BitVec.ofNat 64 off) w :=
  ⟨_, List.mem_append_right _ h.scr, Offset.contains_base _ hw (by omega)⟩

theorem BPre.inP {off w : Nat} (hw : off + w ≤ 8) : InRegions s.wr (State.addr p + BitVec.ofNat 64 off) w :=
  h.blk hw

theorem BPre.inP' {off w : Nat} (hw : off + w ≤ 8) :
    InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 off) w := by
  obtain ⟨g, hg, hc⟩ := h.blk hw; exact ⟨g, List.mem_append_right _ hg, hc⟩

theorem BPre.inK {off w : Nat} (hw : off + w ≤ 128) :
    InRegions (s.rd ++ s.wr) (State.addr kb + BitVec.ofNat 64 off) w :=
  ⟨_, h.sch, Offset.contains_base _ hw (by omega)⟩

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

theorem RInv_iff {s : State} {c : BitVec 32} {lr : Spec.Cast5.Word × Spec.Cast5.Word} {kp : BitVec 32}
    {t left : Nat} {u : State} : RInv s c lr kp t left u ↔
      (u.gpr .r2 = lr.1 ∧ u.gpr .r3 = lr.2 ∧ u.gpr .lr = kp ∧ u.gpr .r12 = c ∧ Frame [ctRegion c] s.mem u.mem ∧
        u.mem.readW (State.addr c + BitVec.ofNat 64 16) 32 = BitVec.ofNat 32 left ∧
        u.mem.readW (State.addr c + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 t ∧
        u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp) :=
  ⟨fun h => ⟨h.r2, h.r3, h.lr, h.r12, h.fr, h.cnt, h.typ, h.rd, h.wr, h.sp⟩,
   fun ⟨a, b, c, d, e, f, g, i, j, k⟩ => ⟨a, b, c, d, e, f, g, i, j, k⟩⟩

/-- The subkeys of round `i` (`1 … 16`) at `kp`, read through a frame. -/
theorem key_at {s u : State} {c p kb : BitVec 32} {n : Nat} (h : BPre s c p kb n)
    (hf : Frame [ctRegion c] s.mem u.mem) {i : Nat} (hi : 1 ≤ i ∧ i ≤ 16) {j : Nat} (hj : j = i - 1 ∨ j = 15 + i) :
    u.mem.readW (State.addr kb + BitVec.ofNat 64 (4 * j)) 32 =
      (Spec.Cast5.scheduleAt s.mem (State.addr kb)).getD j 0 := by
  rw [Proof.Cast5.scheduleAt_getD _ _ (by omega)]
  refine hf.readW (r := ⟨State.addr kb, 128⟩) (Offset.contains_base _ (by omega) (by omega)) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h.dKS.sub_right (Offset.sub_base _ (by decide))

theorem kp_addr {kb : BitVec 32} (hk : kb.toNat + 128 ≤ 2 ^ 32) {j : Nat} (off : Nat)
    (hjo : 4 * j + off + 4 ≤ 128) :
    State.addr (kb + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 off) =
      State.addr kb + BitVec.ofNat 64 (4 * j + off) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact addr_add (by omega)

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
    rw [hu.lr, kp_addr h.kfit 0 (by omega), Nat.add_zero]
  have e64 : State.addr (u.gpr .lr + BitVec.ofNat 32 64) = State.addr kb + BitVec.ofNat 64 (4 * (15 + i)) := by
    rw [hu.lr, kp_addr h.kfit 64 (by omega)]; congr 2; omega
  have es (off : Nat) (ho : off < 256) : slot u off = State.addr c + BitVec.ofNat 64 off := by
    rw [hu.r12, aS off ho]
  have pre : RoundPre u ((Spec.Cast5.scheduleAt s.mem (State.addr kb)).getD (i - 1) 0)
      ((Spec.Cast5.scheduleAt s.mem (State.addr kb)).getD (15 + i) 0) lr.1 lr.2 t (BitVec.ofNat 32 left) :=
    { r2 := hu.r2
      r3 := hu.r3
      inM := by rw [e0, hu.rd, hu.wr]; exact h.inK (by omega)
      valM := by rw [e0]; exact key_at h hu.fr hi (.inl rfl)
      inR := by rw [e64, hu.rd, hu.wr]; exact h.inK (by omega)
      valR := by rw [e64]; exact key_at h hu.fr hi (.inr rfl)
      ht := ht
      inT := by rw [es 20 (by decide), hu.wr]; exact h.inS (by decide)
      valT := by rw [es 20 (by decide)]; exact hu.typ
      inC := by rw [es 16 (by decide), hu.wr]; exact h.inS (by decide)
      valC := by rw [es 16 (by decide)]; exact hu.cnt
      sep := by rw [es 16 (by decide), es 20 (by decide)]; exact Offset.sep _ (by decide) (by decide) (by decide) }
  refine WP.mono (round_ok u up pre) fun v ⟨v2, v3, vlr, vm, vz, vk⟩ => ⟨⟨v2, ?_, ?_, ?_, ?_, ?_, ?_,
    vk.rd.trans hu.rd, vk.wr.trans hu.wr, vk.sp.trans hu.sp⟩, vz⟩
  · rw [v3, fT_eq ht hti]; rfl
  · rw [vlr, hu.lr]
  · rw [vk.gpr _ (by decide), hu.r12]
  · rw [vm, es 16 (by decide), es 20 (by decide)]
    exact (hu.fr.writeW List.mem_cons_self _ (Offset.contains _ (by decide) (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains _ (by decide) (by decide) (by decide))
  · rw [vm, es 16 (by decide), es 20 (by decide), Mem.readW_writeW_self32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega
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
    ?_ n u ⟨0, rfl, by omega, by rw [Nat.sub_zero]; exact h0⟩
  rintro m v ⟨i, rfl, hi, hv⟩
  rw [hkp i hi] at hv
  refine WP.mono (round_step h hv up (ht i hi) (hti i hi) (hidx i hi) (by omega)) fun w ⟨hw, wz⟩ => ?_
  rw [← hfold i hi, ← hkp i hi] at hw
  by_cases hlast : i + 1 = n
  · refine .inl ⟨?_, _, _, by rw [hlast] at hw; rw [show n - i - 1 = 0 by omega] at hw; exact hw⟩
    show some (!w.z) = _; rw [wz]
    congr 1
    rw [show n - i = 1 by omega]
    rfl
  · obtain ⟨hk, htn⟩ := hnext i (by omega)
    refine .inr ⟨?_, n - (i + 1), by omega, i + 1, rfl, by omega, ?_⟩
    · show some (!w.z) = _; rw [wz]
      congr 1
      have : BitVec.ofNat 32 (n - i) - 1 ≠ 0 := by
        intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl,
          show (0 : BitVec 32).toNat = 0 from rfl] at this
        omega
      simpa using this
    · rw [hk, htn, show n - (i + 1) = n - i - 1 by omega]
      exact hw

theorem nextT_up (i : Nat) : nextT true (i % 3 + 1) = (i + 1) % 3 + 1 := by
  simp only [nextT, ite_true]
  split <;> omega

theorem nextT_down {i : Nat} (hi : 1 ≤ i) : nextT false ((i - 1 + 1) % 3 + 1) = (i - 1) % 3 + 1 := by
  simp only [nextT, Bool.false_eq_true, ite_false]
  split <;> omega

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
    h.rounds, rev_eq, RInv_iff]
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
    h.rounds, rev_eq, RInv_iff]
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
      exact Offset.disjoint _ (by omega) (by omega) (by decide)) (by decide)
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
      h.dPS.sub_right (Offset.sub_base _ (by omega))
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
      (fun i => (n - 1 - i) % 3 + 1) (fun i => decFold _ n i _) (fun i hi => by omega)
      (fun i hi => by congr 2; omega) (fun i hi => by omega) (fun i hi => by omega)
      (fun i hi => decFold_succ _ _ _ _) (fun i hi => ⟨?_, ?_⟩) hu) fun v ⟨kp, t, hv⟩ => ?_)
    · simp only [Bool.false_eq_true, ite_false]
      rw [show n - 1 - i = n - 1 - (i + 1) + 1 by omega, Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc]
      exact (BitVec.add_sub_cancel _ _).symm
    · rw [show n - 1 - i = n - 1 - (i + 1) + 1 by omega]
      simp only [nextT, Bool.false_eq_true, ite_false]
      split <;> omega
    refine WP.mono (finish_ok h hv) fun w hw => ?_
    rw [cipher, ite_eq_right Bool.false_ne_true, decryptBlock_eq]
    exact hw
  · unfold crypt
    simp only [ite_true]
    refine WP.seq (WP.mono (startEnc_ok h) fun u hu => ?_)
    refine WP.seq (WP.mono (rounds_ok h true (fun i => i + 1) (fun i => kb + BitVec.ofNat 32 (4 * i))
      (fun i => i % 3 + 1) (fun i => encFold _ i _) (fun i hi => by omega)
      (fun i hi => by rw [Nat.add_sub_cancel]) (fun i hi => by omega) (fun i hi => by omega)
      (fun i hi => encFold_succ _ _ _) (fun i hi => ⟨?_, (nextT_up i).symm⟩) hu) fun v ⟨kp, t, hv⟩ => ?_)
    · simp only [ite_true]
      rw [Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    refine WP.mono (finish_ok h hv) fun w hw => ?_
    rw [cipher, ite_eq_left rfl, encryptBlock_eq]
    exact hw

end VG.Proof.Cast5.Arm
