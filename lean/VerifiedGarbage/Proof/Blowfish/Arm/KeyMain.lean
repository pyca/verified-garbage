module

import VerifiedGarbage.Proof.Rc4.Scan32
public import VerifiedGarbage.Proof.Blowfish.KeyTable
public import VerifiedGarbage.Proof.Blowfish.Arm.Cipher
public import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Blowfish.Arm.Ecb
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Blowfish.Arm
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Blowfish.Arm.Run
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.RegUpd

/-! ### `Blowfish.Arm.KeyEnc`, which only this module used -/

section

/-!
# Blowfish on ARMv7: key expansion's 521 encryptions

Each encryption runs the block function under the schedule as written so
far, and its output replaces the next two entries: the P-array's, as words
(`encryptP_run`), then the S-boxes', a byte per plane (`encryptS_run`). The
pointer to the next entries and the encryptions left are in the working
space, at `lr + 36` and `lr + 40`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

/-- What the encryptions need of the state they start in. -/
structure EncEnv (K B : BitVec 32) (s₀ : State) : Prop where
  fitK : K.toNat + 4168 ≤ 2 ^ 32
  fitB : B.toNat + 64 ≤ 2 ^ 32
  wrK : InRegions s₀.wr (State.addr K) 4168
  wrB : InRegions s₀.wr (State.addr B) 64
  sep : Region.Disjoint ⟨State.addr K, 4168⟩ ⟨State.addr B, 64⟩

/-- After `j` encryptions. -/
structure EncInv (key : List Byte) (K B : BitVec 32) (g : Reg → BitVec 32) (s₀ : State) (j : Nat)
    (u : State) : Prop where
  le : j ≤ 521
  r0 : u.gpr .r0 = K
  r3 : u.gpr .r3 = B
  sched : scheduleAt u.mem (State.addr K) = (ksIter key j).1
  halves : (u.gpr .r1, u.gpr .r2) = (ksIter key j).2
  saved : Spill.Saved u.mem (State.addr B) g saved
  frame : Frame [⟨State.addr K, 4168⟩, ⟨State.addr B, 64⟩] s₀.mem u.mem
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr

theorem ord_true : ord true = id := rfl

/-- The encryption of the last output. -/
theorem enc_cipher {key : List Byte} {K B : BitVec 32} {g : Reg → BitVec 32} {s₀ : State}
    (E : EncEnv K B s₀) {j : Nat} {u : State} (I : EncInv key K B g s₀ j u) :
    WP isa (cipher true) u fun u' =>
      (u'.gpr .r1, u'.gpr .r2) = encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2 ∧
        Keep cRegs u u' ∧ u'.mem = u.mem := by
  have CE : CipherEnv u := by
    refine ⟨by rw [I.r0]; exact E.fitK, fun o ho => ?_⟩
    rw [I.r0, I.wr]
    exact region_in (inRegions_off E.wrK (by omega_arith))
  refine WP.mono (cipher_run CE true) fun u' ⟨h, k, m⟩ => ⟨?_, k, m⟩
  rw [h, I.r0, I.sched, ord_true, ← I.halves]; rfl

theorem ksIter_step (key : List Byte) {j : Nat} (hj : j < 521) :
    ksIter key (j + 1) =
      (((ksIter key j).1.set (2 * j) (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1
          (by omega_arith)).set (2 * j + 1)
          (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2 (by omega_arith),
        (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1,
        (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2) := by
  rw [ksIter_succ, ksStep, set!_eq_set _ (by omega_arith), set!_eq_set _ (by omega_arith)]

/-- The working space's pointer and counter, written. -/
theorem slots_facts (m : Mem) (Ba : Addr) (P C : BitVec 32) :
    let M := (m.writeW (Ba + BitVec.ofNat 64 36) P).writeW (Ba + BitVec.ofNat 64 40) C
    M.readW (Ba + BitVec.ofNat 64 36) 32 = P ∧ M.readW (Ba + BitVec.ofNat 64 40) 32 = C ∧
      Frame [⟨Ba + BitVec.ofNat 64 36, 8⟩] m M := by
  intro M
  have s36 : Mem.Sep (Ba + BitVec.ofNat 64 36) 4 (Ba + BitVec.ofNat 64 40) 4 :=
    Offset.sep Ba (by decide) (by decide) (by decide)
  refine ⟨by rw [Mem.readW_writeW_sep s36 (by decide), Mem.readW_writeW_self32],
    Mem.readW_writeW_self32 _ _ _, ?_⟩
  exact ((Frame.refl _ m).writeW List.mem_cons_self _
    (Offset.contains (e := 36) (k := 8) (d := 36) (n := 4) _ (by decide) (by decide) (by decide))).writeW
    List.mem_cons_self _ (Offset.contains (e := 36) (k := 8) (d := 40) (n := 4) _ (by decide) (by decide) (by decide))

/-- The output's words to the P-array entries at the pointer, the next pair's
pointer, and the counter less one. -/
theorem storeP_run (u : State) {B P C : BitVec 32} {Ba Pa : Addr} (hlr : u.gpr .r3 = B)
    (eB : State.addr (B + BitVec.ofNat 32 36) = Ba + BitVec.ofNat 64 36)
    (eC : State.addr (B + BitVec.ofNat 32 40) = Ba + BitVec.ofNat 64 40)
    (e0 : State.addr (P + BitVec.ofNat 32 0) = Pa) (e4 : State.addr (P + BitVec.ofNat 32 4) = Pa + BitVec.ofNat 64 4)
    (wB : InRegions u.wr (Ba + BitVec.ofNat 64 36) 8)
    (w0 : InRegions u.wr Pa 8) (dj : Region.Disjoint ⟨Ba + BitVec.ofNat 64 36, 8⟩ ⟨Pa, 8⟩)
    (hP : u.mem.readW (Ba + BitVec.ofNat 64 36) 32 = P) (hC : u.mem.readW (Ba + BitVec.ofNat 64 40) 32 = C) :
    WP isa (.block storeP) u fun t =>
      t.mem = (((u.mem.writeW Pa (u.gpr .r1)).writeW (Pa + BitVec.ofNat 64 4) (u.gpr .r2)).writeW
          (Ba + BitVec.ofNat 64 36) (P + BitVec.ofNat 32 8)).writeW (Ba + BitVec.ofNat 64 40) (C - 1#32) ∧
        t.z = (C - 1#32 == 0#32) := by
  have s36 : Mem.Sep (Ba + BitVec.ofNat 64 40) 4 (Ba + BitVec.ofNat 64 36) 4 :=
    Offset.sep Ba (by decide) (by decide) (by decide)
  have sP : ∀ o, o ≤ 4 → Mem.Sep (Ba + BitVec.ofNat 64 40) 4 (Pa + BitVec.ofNat 64 o) 4 := fun o ho =>
    sep_of_disjoint ((dj.sub_left (Offset.sub Ba (d := 40) (n := 4) (e := 36) (k := 8) (by decide)
      (by decide))).sub_right (Offset.sub_base Pa (d := o) (n := 4) (k := 8) (by omega_arith)))
  have rB := inRegions_pre (n := 4) wB (by decide)
  have rC := inRegions_off (o := 4) (n := 4) wB (by decide)
  rw [Offset.add_add] at rC
  have r0 := inRegions_pre (n := 4) w0 (by decide)
  have r4 := inRegions_off (o := 4) (n := 4) w0 (by decide)
  unfold storeP countDown
  brun [hlr, ptrOff, cntOff, eB, eC, e0, e4, rB, rC, r0, r4, region_in (rs := u.rd) rB,
    region_in (rs := u.rd) rC, hP, hC]

/-- The P-array phase: after `j` encryptions, the pointer at P-array entry
`2 j` and `9 - j` left. -/
structure PInv (key : List Byte) (K B : BitVec 32) (g : Reg → BitVec 32) (s₀ : State) (j : Nat)
    (u : State) : Prop where
  enc : EncInv key K B g s₀ j u
  le : j ≤ 9
  ptr : u.mem.readW (State.addr B + BitVec.ofNat 64 36) 32 = K + BitVec.ofNat 32 (4096 + 8 * j)
  cnt : u.mem.readW (State.addr B + BitVec.ofNat 64 40) 32 = BitVec.ofNat 32 (9 - j)

theorem EncEnv.wK {K B : BitVec 32} {s₀ u : State} (E : EncEnv K B s₀) (hw : u.wr = s₀.wr) {o n : Nat}
    (h : o + n ≤ 4168) : InRegions u.wr (State.addr K + BitVec.ofNat 64 o) n := by
  rw [hw]; exact inRegions_off E.wrK h

theorem EncEnv.wB {K B : BitVec 32} {s₀ u : State} (E : EncEnv K B s₀) (hw : u.wr = s₀.wr) {o n : Nat}
    (h : o + n ≤ 64) : InRegions u.wr (State.addr B + BitVec.ofNat 64 o) n := by
  rw [hw]; exact inRegions_off E.wrB h

theorem saved_frame {m m' : Mem} {Ba Ka : Addr} {g : Reg → BitVec 32} (h : Spill.Saved m Ba g saved)
    (hf : Frame [⟨Ka, 4168⟩, ⟨Ba + BitVec.ofNat 64 36, 8⟩] m m')
    (sep : Region.Disjoint ⟨Ka, 4168⟩ ⟨Ba, 64⟩) : Spill.Saved m' Ba g saved :=
  h.frame saved_slots hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [BitVec.add_zero]; exact sep.symm.sub_left (Region.sub_prefix (by decide))
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)

theorem encP_step {key : List Byte} {K B : BitVec 32} {g : Reg → BitVec 32} {s₀ : State}
    (E : EncEnv K B s₀) {j : Nat} (hj : j < 9) {u : State} (I : PInv key K B g s₀ j u) :
    WP isa (.seq (cipher true) (.block storeP)) u fun u' =>
      PInv key K B g s₀ (j + 1) u' ∧ u'.z = (BitVec.ofNat 32 (9 - (j + 1)) == 0#32) := by
  have fK := E.fitK
  have fB := E.fitB
  have J := I.enc
  apply WP.seq
  refine WP.mono (enc_cipher E J) fun u₁ ⟨c12, ck, cm⟩ => ?_
  let out := encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2
  have eB : State.addr (B + BitVec.ofNat 32 36) = State.addr B + BitVec.ofNat 64 36 := addr_add (by omega_arith)
  have eC : State.addr (B + BitVec.ofNat 32 40) = State.addr B + BitVec.ofNat 64 40 := addr_add (by omega_arith)
  have e0 : State.addr (K + BitVec.ofNat 32 (4096 + 8 * j) + BitVec.ofNat 32 0) =
      State.addr K + BitVec.ofNat 64 (4096 + 4 * (2 * j)) := by
    rw [BitVec.add_zero, addr_add (by omega_arith)]; congr 2; omega_arith
  have e4 : State.addr (K + BitVec.ofNat 32 (4096 + 8 * j) + BitVec.ofNat 32 4) =
      State.addr K + BitVec.ofNat 64 (4096 + 4 * (2 * j)) + BitVec.ofNat 64 4 := by
    rw [ofs_add, addr_add (by omega_arith), Offset.add_add]; congr 2; omega_arith
  have dj : Region.Disjoint ⟨State.addr B + BitVec.ofNat 64 36, 8⟩
      ⟨State.addr K + BitVec.ofNat 64 (4096 + 4 * (2 * j)), 8⟩ :=
    (E.sep.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by omega_arith))
  have w₁ : u₁.wr = s₀.wr := by rw [ck.2.2.1, J.wr]
  refine WP.mono (WP.keep [.r11, .r12] (storeP_run u₁ (C := BitVec.ofNat 32 (9 - j))
    (by rw [ck.gpr (by decide), J.r3]) eB eC e0 e4 (E.wB w₁ (by decide)) (E.wK w₁ (by omega_arith)) dj
    (by rw [cm]; exact I.ptr) (by rw [cm]; exact I.cnt)) (by decide)) fun u₂ ⟨⟨sm, sz⟩, sk⟩ => ?_
  obtain ⟨M36, M40, MF⟩ := slots_facts (((u₁.mem.writeW (State.addr K + BitVec.ofNat 64 (4096 + 4 * (2 * j)))
    (u₁.gpr .r1)).writeW (State.addr K + BitVec.ofNat 64 (4096 + 4 * (2 * j)) + BitVec.ofNat 64 4) (u₁.gpr .r2)))
    (State.addr B) (K + BitVec.ofNat 32 (4096 + 8 * j) + BitVec.ofNat 32 8) (BitVec.ofNat 32 (9 - j) - 1#32)
  rw [← sm] at M36 M40 MF
  have F2 : Frame [⟨State.addr K, 4168⟩] u₁.mem ((u₁.mem.writeW (State.addr K +
      BitVec.ofNat 64 (4096 + 4 * (2 * j))) (u₁.gpr .r1)).writeW (State.addr K +
      BitVec.ofNat 64 (4096 + 4 * (2 * j)) + BitVec.ofNat 64 4) (u₁.gpr .r2)) :=
    ((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_arith))).writeW
      List.mem_cons_self _ (by rw [Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith))
  have FF : Frame [⟨State.addr K, 4168⟩, ⟨State.addr B + BitVec.ofNat 64 36, 8⟩] u.mem u₂.mem := by
    rw [← cm]
    exact (F2.mono (by simp)).trans (MF.mono (by simp))
  have hsched : scheduleAt u₂.mem (State.addr K) = (ksIter key (j + 1)).1 := by
    rw [scheduleAt_eq_of_frame _ MF (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact E.sep.sub_right (Offset.sub_base _ (by decide))),
      Offset.add_add, show 4096 + 4 * (2 * j) + 4 = 4096 + 4 * (2 * j + 1) by omega_arith,
      scheduleAt_writeW_P _ _ (by omega_arith), scheduleAt_writeW_P _ _ (by omega_arith), cm, J.sched,
      ksIter_step key (by omega_arith)]
    have h1 : u₁.gpr .r1 = out.1 := congrArg Prod.fst c12
    have h2 : u₁.gpr .r2 = out.2 := congrArg Prod.snd c12
    rw [h1, h2]
  refine ⟨⟨⟨by omega_arith, by rw [sk.gpr (by decide), ck.gpr (by decide), J.r0],
    by rw [sk.gpr (by decide), ck.gpr (by decide), J.r3], hsched, ?_,
    saved_frame J.saved FF E.sep, J.frame.trans (FF.sub fun r hr => ?_), by rw [sk.2.1, ck.2.1, J.rd],
    by rw [sk.2.2.1, w₁]⟩, by omega_arith, by rw [M36, ofs_add]; congr 2, ?_⟩, ?_⟩
  · rw [sk.gpr (by decide), sk.gpr (by decide), c12, ksIter_step key (by omega_arith)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub_base _ (by decide)⟩
  · rw [M40]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_arith
  · rw [sz]; congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_arith

/-- Writing the working space's pointer and counter keeps an encryption's
invariant. -/
theorem EncInv.slots {key : List Byte} {K B : BitVec 32} {g : Reg → BitVec 32} {s₀ : State}
    (E : EncEnv K B s₀) {j : Nat} {u u' : State} (I : EncInv key K B g s₀ j u) {P C : BitVec 32}
    (hm : u'.mem = (u.mem.writeW (State.addr B + BitVec.ofNat 64 36) P).writeW
      (State.addr B + BitVec.ofNat 64 40) C)
    (k : Keep [.r11, .r12] u u') :
    EncInv key K B g s₀ j u' ∧ u'.mem.readW (State.addr B + BitVec.ofNat 64 36) 32 = P ∧
      u'.mem.readW (State.addr B + BitVec.ofNat 64 40) 32 = C := by
  obtain ⟨M36, M40, MF⟩ := slots_facts u.mem (State.addr B) P C
  rw [← hm] at M36 M40 MF
  refine ⟨⟨I.le, by rw [k.gpr (by decide), I.r0], by rw [k.gpr (by decide), I.r3], ?_,
    by rw [k.gpr (by decide), k.gpr (by decide), I.halves], saved_frame I.saved (MF.mono (by simp)) E.sep,
    I.frame.trans (MF.sub fun r hr => ?_), by rw [k.2.1, I.rd], by rw [k.2.2.1, I.wr]⟩, M36, M40⟩
  · rw [scheduleAt_eq_of_frame _ MF (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact E.sep.sub_right (Offset.sub_base _ (by decide))), I.sched]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub_base _ (by decide)⟩

theorem encryptP_run {key : List Byte} {K B : BitVec 32} {g : Reg → BitVec 32} {s₀ : State}
    (E : EncEnv K B s₀) {u : State} (I : EncInv key K B g s₀ 0 u) :
    WP isa encryptP u (EncInv key K B g s₀ 9) := by
  have fK := E.fitK
  have fB := E.fitB
  have eB : State.addr (B + BitVec.ofNat 32 36) = State.addr B + BitVec.ofNat 64 36 := addr_add (by omega_arith)
  have eC : State.addr (B + BitVec.ofNat 32 40) = State.addr B + BitVec.ofNat 64 40 := addr_add (by omega_arith)
  have rB := E.wB I.wr (o := 36) (n := 4) (by decide)
  have rC := E.wB I.wr (o := 40) (n := 4) (by decide)
  unfold encryptP
  apply WP.seq
  refine WP.mono (WP.keep [.r11, .r12] (Q := fun t => t.mem = (u.mem.writeW (State.addr B + BitVec.ofNat 64 36)
      (K + BitVec.ofNat 32 4096)).writeW (State.addr B + BitVec.ofNat 64 40) (BitVec.ofNat 32 9))
    (by brun [I.r0, I.r3, eB, eC, rB, rC, ptrOff, cntOff, pOff]) (by decide)) fun u₁ ⟨m₁, k₁⟩ => ?_
  obtain ⟨J, j36, j40⟩ := I.slots E m₁ k₁
  refine WP.mono (WP.loop (M := isa) (Q := PInv key K B g s₀ 9)
    (fun (n : Nat) (v : State) => ∃ j, j < 9 ∧ n = 9 - j ∧ PInv key K B g s₀ j v) ?_ 9 u₁
    ⟨0, by decide, rfl, ⟨J, by decide, by rw [j36], by rw [j40]⟩⟩) fun v V => V.enc
  intro n v ⟨j, hj, hn, P⟩
  refine WP.mono (encP_step E hj P) fun v' ⟨P', hz⟩ => ?_
  rw [eval_ne, hz]
  by_cases e : j + 1 = 9
  · left
    exact ⟨by rw [e]; rfl, e ▸ P'⟩
  · right
    have nz : BitVec.ofNat 32 (9 - (j + 1)) ≠ 0#32 := by
      intro h'; have := congrArg BitVec.toNat h'; simp at this; omega_arith
    exact ⟨by rw [beq_eq_false_iff_ne.mpr nz]; rfl, _, by omega_arith, j + 1, by omega_arith, rfl, P'⟩

/-- The offset of S-box entry `sDone j`'s first plane. -/
def sOff (j : Nat) : Nat := 1024 * (sDone j / 256) + sDone j % 256

theorem sOff_entry {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) {b k : Nat} (hk : k < 2) :
    sOff j + (256 * b + k) = entryOff (2 * j + k) b := by
  rw [← entryOff_sbox h9 hj k hk, sOff]

theorem sOff_lt {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) : sOff j ≤ 3326 := by
  unfold sOff sDone; omega_arith

theorem sOff_succ {j : Nat} (h9 : 9 ≤ j) :
    sOff (j + 1) = if (sOff j + 2) % 256 = 0 then sOff j + 2 + 768 else sOff j + 2 := by
  unfold sOff sDone; split <;> omega_arith

/-- The bytes of `x` and `y` into the planes of S-box entries `q` and `q + 1`. -/
def sWrites (m : Mem) (Ka : Addr) (q : Nat) (x y : BitVec 32) : Mem :=
  (((((((m.writeW (Ka + BitVec.ofNat 64 (q + 0)) (BitVec.setWidth 8 x)).writeW
    (Ka + BitVec.ofNat 64 (q + 256)) (BitVec.setWidth 8 (x >>> 8))).writeW
    (Ka + BitVec.ofNat 64 (q + 512)) (BitVec.setWidth 8 (x >>> 16))).writeW
    (Ka + BitVec.ofNat 64 (q + 768)) (BitVec.setWidth 8 (x >>> 24))).writeW
    (Ka + BitVec.ofNat 64 (q + 1)) (BitVec.setWidth 8 y)).writeW
    (Ka + BitVec.ofNat 64 (q + 257)) (BitVec.setWidth 8 (y >>> 8))).writeW
    (Ka + BitVec.ofNat 64 (q + 513)) (BitVec.setWidth 8 (y >>> 16))).writeW
    (Ka + BitVec.ofNat 64 (q + 769)) (BitVec.setWidth 8 (y >>> 24))

theorem low_byte (x : BitVec 32) : x.setWidth 8 = x.extractLsb' 0 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem sWrites_sched (m : Mem) (Ka : Addr) {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) (x y : BitVec 32) :
    scheduleAt (sWrites m Ka (sOff j) x y) Ka = ((scheduleAt m Ka).set (2 * j) x (by omega_arith)).set (2 * j + 1) y
      (by omega_arith) := by
  have e : ∀ b k, k < 2 → sOff j + (256 * b + k) = entryOff (2 * j + k) b := fun b k hk => sOff_entry h9 hj hk
  unfold sWrites
  simp only [Proof.Rc4.writeW_byte8]
  simp only [shr_byte]
  simp only [low_byte]
  rw [show sOff j + 0 = entryOff (2 * j + 0) 0 from e 0 0 (by decide),
    show sOff j + 256 = entryOff (2 * j + 0) 1 from e 1 0 (by decide),
    show sOff j + 512 = entryOff (2 * j + 0) 2 from e 2 0 (by decide),
    show sOff j + 768 = entryOff (2 * j + 0) 3 from e 3 0 (by decide),
    show sOff j + 1 = entryOff (2 * j + 1) 0 from e 0 1 (by decide),
    show sOff j + 257 = entryOff (2 * j + 1) 1 from e 1 1 (by decide),
    show sOff j + 513 = entryOff (2 * j + 1) 2 from e 2 1 (by decide),
    show sOff j + 769 = entryOff (2 * j + 1) 3 from e 3 1 (by decide)]
  rw [scheduleAt_write_bytes _ _ (by omega_arith), Nat.add_zero, scheduleAt_write_bytes _ _ (by omega_arith)]

theorem sWrites_frame (m : Mem) (Ka : Addr) {q : Nat} (hq : q + 770 ≤ 4168) (x y : BitVec 32) :
    Frame [⟨Ka, 4168⟩] m (sWrites m Ka q x y) := by
  have c : ∀ e, e < 770 → Region.Contains ⟨Ka, 4168⟩ (Ka + BitVec.ofNat 64 (q + e)) (8 / 8) :=
    fun e he => Offset.contains_base _ (by omega_arith) (by omega_arith)
  unfold sWrites
  exact (((((((((Frame.refl _ m).writeW List.mem_cons_self _ (c 0 (by decide))).writeW List.mem_cons_self _
    (c 256 (by decide))).writeW List.mem_cons_self _ (c 512 (by decide))).writeW List.mem_cons_self _
    (c 768 (by decide))).writeW List.mem_cons_self _ (c 1 (by decide))).writeW List.mem_cons_self _
    (c 257 (by decide))).writeW List.mem_cons_self _ (c 513 (by decide))).writeW List.mem_cons_self _
    (c 769 (by decide)))

def storeSHead : List Instr :=
  [.ldr pPtr .r3 ptrOff, .ldr .r11 .r3 cntOff] ++ storeEntry xL 0 ++ storeEntry xR 1 ++
    [.dp .add pPtr pPtr (imm 2), .dp .sub tmp pPtr (.reg sch), .dp .and tmp tmp (imm 255), .cmp tmp (imm 0)]

theorem storeSHead_run (u : State) {B K C : BitVec 32} {Ka Ba : Addr} {q : Nat} (hlr : u.gpr .r3 = B)
    (h0 : u.gpr .r0 = K)
    (eB : State.addr (B + BitVec.ofNat 32 36) = Ba + BitVec.ofNat 64 36)
    (eC : State.addr (B + BitVec.ofNat 32 40) = Ba + BitVec.ofNat 64 40)
    (rB : InRegions (u.rd ++ u.wr) (Ba + BitVec.ofNat 64 36) 8)
    (hP : u.mem.readW (Ba + BitVec.ofNat 64 36) 32 = K + BitVec.ofNat 32 q)
    (hC : u.mem.readW (Ba + BitVec.ofNat 64 40) 32 = C)
    (eK : ∀ c, c < 770 → State.addr (K + BitVec.ofNat 32 q + BitVec.ofNat 32 c) = Ka + BitVec.ofNat 64 (q + c))
    (w : ∀ c, c < 770 → InRegions u.wr (Ka + BitVec.ofNat 64 (q + c)) 1) :
    WP isa (.block storeSHead) u fun t => t.mem = sWrites u.mem Ka q (u.gpr .r1) (u.gpr .r2) ∧
      t.gpr .r12 = K + BitVec.ofNat 32 q + 2#32 ∧ t.gpr .r11 = C ∧
      t.z = ((K + BitVec.ofNat 32 q + 2#32 - K &&& 255#32) - 0#32 == 0#32) := by
  have rB4 := inRegions_pre (n := 4) rB (by decide)
  have rC := inRegions_off (o := 4) (n := 4) rB (by decide)
  rw [Offset.add_add] at rC
  have e1 := eK 0 (by decide)
  have e2 := eK 256 (by decide)
  have e3 := eK 512 (by decide)
  have e4 := eK 768 (by decide)
  have e5 := eK 1 (by decide)
  have e6 := eK 257 (by decide)
  have e7 := eK 513 (by decide)
  have e8 := eK 769 (by decide)
  unfold storeSHead storeEntry
  have w1 := w 0 (by decide)
  have w2 := w 256 (by decide)
  have w3 := w 512 (by decide)
  have w4 := w 768 (by decide)
  have w5 := w 1 (by decide)
  have w6 := w 257 (by decide)
  have w7 := w 513 (by decide)
  have w8 := w 769 (by decide)
  brun [hlr, h0, eB, eC, rB4, rC, hP, hC, ptrOff, cntOff, e1, e2, e3, e4, e5, e6, e7, e8, w1, w2, w3, w4,
    w5, w6, w7, w8]
  rfl

theorem sAnd_z (K : BitVec 32) (q : Nat) :
    ((K + BitVec.ofNat 32 q + 2#32 - K &&& 255#32) - 0#32 == 0#32) = decide ((q + 2) % 256 = 0) := by
  have e : K + BitVec.ofNat 32 q + 2#32 - K &&& 255#32 = BitVec.ofNat 32 ((q + 2) % 256) := by
    rw [show (2#32 : BitVec 32) = BitVec.ofNat 32 2 from rfl, ofs_add, ofs_diff]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [show (255 % 2 ^ 32 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega_arith
  rw [e, BitVec.sub_zero]
  by_cases h : (q + 2) % 256 = 0
  · rw [h]; simp
  · have : BitVec.ofNat 32 ((q + 2) % 256) ≠ 0#32 := by
      intro e'; have := congrArg BitVec.toNat e'; simp at this; omega_arith
    simp [this, h]

theorem storeSTail_run (u : State) {B C : BitVec 32} {Ba : Addr} (hlr : u.gpr .r3 = B)
    (eB : State.addr (B + BitVec.ofNat 32 36) = Ba + BitVec.ofNat 64 36)
    (eC : State.addr (B + BitVec.ofNat 32 40) = Ba + BitVec.ofNat 64 40)
    (wB : InRegions u.wr (Ba + BitVec.ofNat 64 36) 8) (h11 : u.gpr .r11 = C) :
    WP isa (.block (([.str pPtr .r3 ptrOff] : List Instr) ++ countDown)) u fun t =>
      t.mem = (u.mem.writeW (Ba + BitVec.ofNat 64 36) (u.gpr .r12)).writeW (Ba + BitVec.ofNat 64 40) (C - 1#32) ∧
        t.z = (C - 1#32 == 0#32) := by
  have rB := inRegions_pre (n := 4) wB (by decide)
  have rC := inRegions_off (o := 4) (n := 4) wB (by decide)
  rw [Offset.add_add] at rC
  unfold countDown
  brun [hlr, ptrOff, cntOff, eB, eC, rB, rC, h11]

/-- The S-box phase: after `j` encryptions, the pointer at S-box entry
`sDone j` and `521 - j` left. -/
structure SInv (key : List Byte) (K B : BitVec 32) (g : Reg → BitVec 32) (s₀ : State) (j : Nat)
    (u : State) : Prop where
  enc : EncInv key K B g s₀ j u
  ge : 9 ≤ j
  ptr : u.mem.readW (State.addr B + BitVec.ofNat 64 36) 32 = K + BitVec.ofNat 32 (sOff j)
  cnt : u.mem.readW (State.addr B + BitVec.ofNat 64 40) 32 = BitVec.ofNat 32 (521 - j)

theorem encS_step {key : List Byte} {K B : BitVec 32} {g : Reg → BitVec 32} {s₀ : State}
    (E : EncEnv K B s₀) {j : Nat} (hj : j < 521) {u : State} (I : SInv key K B g s₀ j u) :
    WP isa (.seq (cipher true) storeS) u fun u' =>
      SInv key K B g s₀ (j + 1) u' ∧ u'.z = (BitVec.ofNat 32 (521 - (j + 1)) == 0#32) := by
  have fK := E.fitK
  have fB := E.fitB
  have J := I.enc
  have h9 := I.ge
  have hq := sOff_lt h9 hj
  apply WP.seq
  refine WP.mono (enc_cipher E J) fun u₁ ⟨c12, ck, cm⟩ => ?_
  have eB : State.addr (B + BitVec.ofNat 32 36) = State.addr B + BitVec.ofNat 64 36 := addr_add (by omega_arith)
  have eC : State.addr (B + BitVec.ofNat 32 40) = State.addr B + BitVec.ofNat 64 40 := addr_add (by omega_arith)
  have w₁ : u₁.wr = s₀.wr := by rw [ck.2.2.1, J.wr]
  unfold storeS
  apply WP.seq
  refine WP.mono (WP.keep [.r9, .r11, .r12] (storeSHead_run u₁ (K := K) (Ka := State.addr K) (q := sOff j)
    (C := BitVec.ofNat 32 (521 - j))
    (by rw [ck.gpr (by decide), J.r3]) (by rw [ck.gpr (by decide), J.r0]) eB eC
    (region_in (E.wB w₁ (by decide))) (by rw [cm]; exact I.ptr) (by rw [cm]; exact I.cnt)
    (fun c hc => by rw [ofs_add, addr_add (by omega_arith)])
    (fun c hc => E.wK w₁ (by omega_arith))) (by decide)) fun u₂ ⟨⟨hm, h12, h11, hz⟩, hk⟩ => ?_
  rw [sAnd_z K] at hz
  -- past the other planes after an S-box's last entry
  apply WP.seq
  have hite : WP isa (.ite .eq (.block [.dp .add pPtr pPtr (imm 768)]) (.block [])) u₂ fun u₃ =>
      u₃.gpr .r12 = K + BitVec.ofNat 32 (sOff (j + 1)) ∧ u₃.mem = u₂.mem ∧ Keep [.r12] u₂ u₃ := by
    refine WP.ite _ (by rw [eval_eq, hz]) (fun h => ?_) (fun h => ?_)
    · refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = u₂.gpr .r12 + BitVec.ofNat 32 768 ∧
        t.mem = u₂.mem) (by brun) (by decide)) fun t ⟨⟨t12, tm⟩, tk⟩ => ⟨?_, tm, tk⟩
      rw [t12, h12, show (2#32 : BitVec 32) = BitVec.ofNat 32 2 from rfl, ofs_add, ofs_add, sOff_succ h9,
        ite_eq_left (of_decide_eq_true h)]
    · refine WP.block_nil ⟨?_, rfl, Keep.refl _ _⟩
      rw [h12, show (2#32 : BitVec 32) = BitVec.ofNat 32 2 from rfl, ofs_add, sOff_succ h9,
        ite_eq_right (of_decide_eq_false h)]
  refine WP.mono hite fun u₃ ⟨g12, gm, gk⟩ => ?_
  have k₃ : Keep cRegs u u₃ := ((ck.trans hk).trans gk).mono (by decide)
  have w₃ : u₃.wr = s₀.wr := by rw [k₃.2.2.1, J.wr]
  have F8 := sWrites_frame u₁.mem (State.addr K) (q := sOff j) (by omega_arith) (u₁.gpr .r1) (u₁.gpr .r2)
  rw [← hm, ← gm] at F8
  refine WP.mono (WP.keep [.r11] (storeSTail_run u₃ (C := BitVec.ofNat 32 (521 - j)) (by rw [k₃.gpr (by decide), J.r3]) eB eC
    (E.wB w₃ (by decide)) (by rw [gk.gpr (by decide), h11])) (by decide)) fun u₄ ⟨⟨tm, tz⟩, tk⟩ => ?_
  obtain ⟨M36, M40, MF⟩ := slots_facts u₃.mem (State.addr B) (u₃.gpr .r12)
    (BitVec.ofNat 32 (521 - j) - 1#32)
  rw [← tm] at M36 M40 MF
  have FF : Frame [⟨State.addr K, 4168⟩, ⟨State.addr B + BitVec.ofNat 64 36, 8⟩] u.mem u₄.mem := by
    rw [← cm]
    exact (F8.mono (by simp)).trans (MF.mono (by simp))
  have hsched : scheduleAt u₄.mem (State.addr K) = (ksIter key (j + 1)).1 := by
    rw [scheduleAt_eq_of_frame _ MF (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact E.sep.sub_right (Offset.sub_base _ (by decide))), gm, hm,
      sWrites_sched _ _ h9 hj, cm, J.sched, ksIter_step key hj]
    have h1 : u₁.gpr .r1 = (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1 :=
      congrArg Prod.fst c12
    have h2 : u₁.gpr .r2 = (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2 :=
      congrArg Prod.snd c12
    rw [h1, h2]
  have k₄ : Keep cRegs u u₄ := k₃.trans_sub tk (by decide)
  refine ⟨⟨⟨by omega_arith, by rw [k₄.gpr (by decide), J.r0], by rw [k₄.gpr (by decide), J.r3], hsched, ?_,
    saved_frame J.saved FF E.sep, J.frame.trans (FF.sub fun r hr => ?_), by rw [k₄.2.1, J.rd],
    by rw [k₄.2.2.1, J.wr]⟩, by omega_arith, by rw [M36, g12], ?_⟩, ?_⟩
  · rw [tk.gpr (by decide), tk.gpr (by decide), gk.gpr (by decide), gk.gpr (by decide), hk.gpr (by decide),
      hk.gpr (by decide), c12, ksIter_step key hj]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub_base _ (by decide)⟩
  · rw [M40]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_arith
  · rw [tz]; congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_arith

theorem encryptS_run {key : List Byte} {K B : BitVec 32} {g : Reg → BitVec 32} {s₀ : State}
    (E : EncEnv K B s₀) {u : State} (I : EncInv key K B g s₀ 9 u) :
    WP isa encryptS u (EncInv key K B g s₀ 521) := by
  have fB := E.fitB
  have eB : State.addr (B + BitVec.ofNat 32 36) = State.addr B + BitVec.ofNat 64 36 := addr_add (by omega_arith)
  have eC : State.addr (B + BitVec.ofNat 32 40) = State.addr B + BitVec.ofNat 64 40 := addr_add (by omega_arith)
  have rB := E.wB I.wr (o := 36) (n := 4) (by decide)
  have rC := E.wB I.wr (o := 40) (n := 4) (by decide)
  unfold encryptS
  apply WP.seq
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.mem = (u.mem.writeW (State.addr B + BitVec.ofNat 64 36)
      K).writeW (State.addr B + BitVec.ofNat 64 40) (BitVec.ofNat 32 512))
    (by brun [I.r0, I.r3, eB, eC, rB, rC, ptrOff, cntOff]; rfl) (by decide)) fun u₁ ⟨m₁, k₁⟩ => ?_
  obtain ⟨J, j36, j40⟩ := I.slots E m₁ (k₁.mono (by decide))
  refine WP.loop (M := isa) (Q := EncInv key K B g s₀ 521)
    (fun (n : Nat) (v : State) => ∃ j, j < 521 ∧ n = 521 - j ∧ SInv key K B g s₀ j v) ?_ 512 u₁
    ⟨9, by decide, rfl, ⟨J, by decide, by rw [j36, show sOff 9 = 0 by decide, BitVec.add_zero], by rw [j40]⟩⟩
  intro n v ⟨j, hj, hn, P⟩
  refine WP.mono (encS_step E hj P) fun v' ⟨P', hz⟩ => ?_
  rw [eval_ne, hz]
  by_cases e : j + 1 = 521
  · left
    exact ⟨by rw [e]; rfl, e ▸ P'.enc⟩
  · right
    have nz : BitVec.ofNat 32 (521 - (j + 1)) ≠ 0#32 := by
      intro h'; have := congrArg BitVec.toNat h'; simp at this; omega_arith
    exact ⟨by rw [beq_eq_false_iff_ne.mpr nz]; rfl, _, by omega_arith, j + 1, by omega_arith, rfl, P'⟩

end VG.Proof.Blowfish.Arm

end

end

/-! ### `Blowfish.Arm.KeyP`, which only this module used -/

section

/-!
# Blowfish on ARMv7: the key into the P-array

`keyP_run`: Pᵢ ^= the `i`-th 32 bits of the key (at `r0`, `r1` bytes long),
cycling through its bytes, for the 18 entries of the schedule at `r2`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

/-- The key offset after `c`, advanced: back to 0 at the key length. -/
theorem key_next (c L : Nat) (hL : 0 < L) (hL' : L < 2 ^ 32) :
    (if (BitVec.ofNat 32 (c % L) + 1#32 - BitVec.ofNat 32 L == 0#32) = true then 0#32
      else BitVec.ofNat 32 (c % L) + 1#32) = BitVec.ofNat 32 ((c + 1) % L) := by
  have hb := Nat.mod_lt c hL
  have ht : (BitVec.ofNat 32 (c % L) + 1#32).toNat = c % L + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c % L < 2 ^ 32 by omega_arith)]
    change (c % L + 1) % 2 ^ 32 = _
    omega_arith
  have ha : (c + 1) % L = (c % L + 1) % L := by simp only [Nat.add_mod, Nat.mod_mod]
  have e : (BitVec.ofNat 32 (c % L) + 1#32 - BitVec.ofNat 32 L == 0#32) = decide (c % L + 1 = L) := by
    rw [show BitVec.ofNat 32 (c % L) + 1#32 = BitVec.ofNat 32 (c % L + 1) from
      BitVec.eq_of_toNat_eq (by rw [ht, BitVec.toNat_ofNat]; omega_arith)]
    exact ofNat_sub_beq (by omega_arith) hL'
  rw [e]
  by_cases h : c % L + 1 = L
  · simp only [decide_eq_true h, ↓reduceIte]; rw [ha, h, Nat.mod_self]
  · rw [decide_eq_false h]
    simp only [Bool.false_eq_true, ite_false]
    apply BitVec.eq_of_toNat_eq
    rw [ht, BitVec.toNat_ofNat, ha, Nat.mod_eq_of_lt (show c % L + 1 < L by omega_arith),
      Nat.mod_eq_of_lt (show c % L + 1 < 2 ^ 32 by omega_arith)]

/-- The key bytes: `key` at `Kk`, `L` bytes long. -/
structure KeyEnv (Kk : BitVec 32) (L : Nat) (u : State) : Prop where
  r0 : u.gpr .r0 = Kk
  r1 : u.gpr .r1 = BitVec.ofNat 32 L
  pos : 0 < L
  small : L ≤ 56
  fit : Kk.toNat + L ≤ 2 ^ 32
  rd : InRegions (u.rd ++ u.wr) (State.addr Kk) L

theorem keyByte_run (u : State) {Kk : BitVec 32} {L : Nat} (E : KeyEnv Kk L u) (c : Nat)
    (h4 : u.gpr .r4 = BitVec.ofNat 32 (c % L)) :
    WP isa keyByte u fun t =>
      t.gpr .r5 = (u.gpr .r5 <<< 8) ||| (u.mem (State.addr Kk + BitVec.ofNat 64 (c % L))).setWidth 32 ∧
        t.gpr .r4 = BitVec.ofNat 32 ((c + 1) % L) ∧ t.mem = u.mem ∧ Keep [.r4, .r5, .r6, .r7] u t := by
  have hc := Nat.mod_lt c E.pos
  have fit := E.fit
  have ea : State.addr (Kk + BitVec.ofNat 32 (c % L) + BitVec.ofNat 32 0) =
      State.addr Kk + BitVec.ofNat 64 (c % L) := by rw [BitVec.add_zero, addr_add (by omega_arith)]
  have hr : InRegions (u.rd ++ u.wr) (State.addr Kk + BitVec.ofNat 64 (c % L)) 1 := inRegions_off E.rd (by omega_arith)
  unfold keyByte
  apply WP.seq
  refine WP.mono (WP.keep [.r4, .r5, .r6, .r7] (Q := fun t =>
      t.gpr .r5 = (u.gpr .r5 <<< 8) ||| (u.mem (State.addr Kk + BitVec.ofNat 64 (c % L))).setWidth 32 ∧
      t.gpr .r4 = BitVec.ofNat 32 (c % L) + 1#32 ∧
      t.z = (BitVec.ofNat 32 (c % L) + 1#32 - BitVec.ofNat 32 L == 0#32) ∧ t.mem = u.mem)
    (by brun [E.r0, E.r1, h4, ea, hr]) (by decide)) fun v ⟨⟨v5, v4, vz, vm⟩, vk⟩ => ?_
  have nx := key_next c L E.pos (by have := E.small; omega_arith)
  refine WP.ite _ (by rw [eval_eq, vz]) (fun hz => ?_) (fun hz => ?_)
  · rw [hz] at nx
    refine WP.mono (WP.keep [.r4] (Q := fun t => t.gpr .r4 = 0#32 ∧ t.gpr .r5 = v.gpr .r5 ∧ t.mem = v.mem)
      (by brun) (by decide)) fun t ⟨⟨t4, t5, tm⟩, tk⟩ =>
        ⟨by rw [t5, v5], by rw [t4, ← nx]; rfl, by rw [tm, vm], vk.trans_sub tk (by decide)⟩
  · rw [hz] at nx
    exact WP.block_nil ⟨v5, by rw [v4, ← nx]; rfl, vm, vk⟩

theorem KeyEnv.keep {Kk : BitVec 32} {L : Nat} {u t : State} (E : KeyEnv Kk L u) {rs : List Reg}
    (h : Keep rs u t) (h0 : Reg.r0 ∉ rs) (h1 : Reg.r1 ∉ rs) : KeyEnv Kk L t :=
  ⟨by rw [h.gpr h0, E.r0], by rw [h.gpr h1, E.r1], E.pos, E.small, E.fit, by rw [keep_reads h]; exact E.rd⟩

/-- The key's byte `c` (mod its length) in memory `m`. -/
abbrev kb (m : Mem) (Kk : BitVec 32) (L c : Nat) : Word :=
  (m (State.addr Kk + BitVec.ofNat 64 (c % L))).setWidth 32

/-- The tail of `keyWord`. -/
def keyTail : List Instr :=
  [.ldr .r6 .r12 0, .dp .eor .r6 .r6 (.reg .r5), .str .r6 .r12 0, .dp .add .r12 .r12 (imm 4),
   .subs .r8 .r8 (imm 1)]

/-- The key word of entry `w`: four bytes, the first the most significant,
then `keyTail`. -/
theorem keyWord_run (u : State) {Kk : BitVec 32} {L : Nat} (E : KeyEnv Kk L u) (w : Nat)
    (h4 : u.gpr .r4 = BitVec.ofNat 32 ((4 * w) % L)) {Q : State → Prop}
    (hQ : ∀ t, t.gpr .r5 = (((((0 : Word) <<< 8 ||| kb u.mem Kk L (4 * w + 0)) <<< 8 |||
          kb u.mem Kk L (4 * w + 1)) <<< 8 ||| kb u.mem Kk L (4 * w + 2)) <<< 8 ||| kb u.mem Kk L (4 * w + 3)) →
        t.gpr .r4 = BitVec.ofNat 32 ((4 * (w + 1)) % L) → t.mem = u.mem → Keep [.r4, .r5, .r6, .r7] u t →
        WP isa (.block keyTail) t Q) :
    WP isa Impl.Blowfish.Arm.keyWord u Q := by
  unfold Impl.Blowfish.Arm.keyWord
  apply WP.seq
  refine WP.mono (WP.keep [.r5] (Q := fun t => t.gpr .r5 = 0 ∧ t.mem = u.mem) (by brun; rfl) (by decide))
    fun t0 ⟨⟨a5, am⟩, ak⟩ => ?_
  apply WP.seq
  refine WP.mono (keyByte_run t0 (E.keep ak (by decide) (by decide)) (4 * w + 0)
    (by rw [ak.gpr (by decide), h4, Nat.add_zero])) fun t1 ⟨b5, b4, bm, bk⟩ => ?_
  apply WP.seq
  refine WP.mono (keyByte_run t1 ((E.keep ak (by decide) (by decide)).keep bk (by decide) (by decide))
    (4 * w + 1) b4) fun t2 ⟨c5, c4, cm, ck⟩ => ?_
  apply WP.seq
  refine WP.mono (keyByte_run t2 (((E.keep ak (by decide) (by decide)).keep bk (by decide) (by decide)).keep ck
    (by decide) (by decide)) (4 * w + 2) c4) fun t3 ⟨d5, d4, dm, dk⟩ => ?_
  apply WP.seq
  refine WP.mono (keyByte_run t3 ((((E.keep ak (by decide) (by decide)).keep bk (by decide) (by decide)).keep ck
    (by decide) (by decide)).keep dk (by decide) (by decide)) (4 * w + 3) d4) fun t4 ⟨e5, e4, em, ek⟩ => ?_
  exact hQ t4 (by rw [e5, d5, c5, b5, a5, dm, cm, bm, am]) (by rw [e4]; congr 2)
    (by rw [em, dm, cm, bm, am]) (((((ak.trans bk).trans ck).trans dk).trans ek).mono (by decide))

theorem kb_keyWord (m : Mem) (Kk : BitVec 32) {L : Nat} (hL : 0 < L) (w : Nat) :
    (((((0 : Word) <<< 8 ||| kb m Kk L (4 * w + 0)) <<< 8 ||| kb m Kk L (4 * w + 1)) <<< 8 |||
      kb m Kk L (4 * w + 2)) <<< 8 ||| kb m Kk L (4 * w + 3)) = Spec.Blowfish.keyWord (bytesAt m (State.addr Kk) L) w := by
  have hl : (bytesAt m (State.addr Kk) L).length = L := by simp [bytesAt]
  rw [keyWord_eq, hl, bytesAt_getD _ _ (Nat.mod_lt _ hL), bytesAt_getD _ _ (Nat.mod_lt _ hL),
    bytesAt_getD _ _ (Nat.mod_lt _ hL), bytesAt_getD _ _ (Nat.mod_lt _ hL)]

theorem keyTail_run (t : State) {K V : BitVec 32} {a : Addr} (w : Nat)
    (h12 : t.gpr .r12 = K + BitVec.ofNat 32 (4096 + 4 * w)) (h5 : t.gpr .r5 = V)
    (ea : State.addr (K + BitVec.ofNat 32 (4096 + 4 * w) + BitVec.ofNat 32 0) = a)
    (hw : InRegions t.wr a 4) :
    WP isa (.block keyTail) t fun t' =>
      t'.mem = t.mem.writeW a (t.mem.readW a 32 ^^^ V) ∧
      t'.gpr .r12 = K + BitVec.ofNat 32 (4096 + 4 * (w + 1)) ∧
      t'.gpr .r8 = t.gpr .r8 - 1#32 ∧ t'.z = (t.gpr .r8 - 1#32 == 0#32) := by
  have hr := region_in (rs := t.rd) hw
  unfold keyTail
  brun [h12, h5, ea, hw, hr]
  rw [ofs_add]; congr 2

/-- After the key words of entries `0, …, w - 1`, from `u₀`. -/
structure KPInv (u₀ : State) (K Kk : BitVec 32) (L w : Nat) (t : State) : Prop where
  le : w ≤ 18
  r4 : t.gpr .r4 = BitVec.ofNat 32 ((4 * w) % L)
  r12 : t.gpr .r12 = K + BitVec.ofNat 32 (4096 + 4 * w)
  r8 : t.gpr .r8 = BitVec.ofNat 32 (18 - w)
  keep : Keep [.r4, .r5, .r6, .r7, .r8, .r12] u₀ t
  done : ∀ j < w, t.mem.readW (State.addr K + BitVec.ofNat 64 (4096 + 4 * j)) 32 =
    u₀.mem.readW (State.addr K + BitVec.ofNat 64 (4096 + 4 * j)) 32 ^^^
      Spec.Blowfish.keyWord (bytesAt u₀.mem (State.addr Kk) L) j
  rest : ∀ j, w ≤ j → j < 18 → t.mem.readW (State.addr K + BitVec.ofNat 64 (4096 + 4 * j)) 32 =
    u₀.mem.readW (State.addr K + BitVec.ofNat 64 (4096 + 4 * j)) 32
  frame : Frame [⟨State.addr K + BitVec.ofNat 64 4096, 72⟩] u₀.mem t.mem

theorem keyStep {u₀ : State} {K Kk : BitVec 32} {L : Nat} (E : KeyEnv Kk L u₀) (fit : K.toNat + 4168 ≤ 2 ^ 32)
    (hw : InRegions u₀.wr (State.addr K + BitVec.ofNat 64 4096) 72)
    (hd : Region.Disjoint ⟨State.addr Kk, L⟩ ⟨State.addr K + BitVec.ofNat 64 4096, 72⟩)
    {w : Nat} (hw18 : w < 18) {t : State} (I : KPInv u₀ K Kk L w t) :
    WP isa Impl.Blowfish.Arm.keyWord t fun t' =>
      KPInv u₀ K Kk L (w + 1) t' ∧ t'.z = (BitVec.ofNat 32 (18 - (w + 1)) == 0#32) := by
  have Et := E.keep I.keep (by decide) (by decide)
  refine keyWord_run t Et w I.r4 fun v v5 v4 vm vk => ?_
  have ea : State.addr (K + BitVec.ofNat 32 (4096 + 4 * w) + BitVec.ofNat 32 0) =
      State.addr K + BitVec.ofNat 64 (4096 + 4 * w) := by rw [BitVec.add_zero, addr_add (by omega_arith)]
  have hwv : InRegions v.wr (State.addr K + BitVec.ofNat 64 (4096 + 4 * w)) 4 := by
    rw [vk.2.2.1, I.keep.2.2.1, ← Offset.add_add]; exact inRegions_off hw (by omega_arith)
  refine WP.mono (WP.keep [.r6, .r8, .r12] (keyTail_run v w (by rw [vk.gpr (by decide), I.r12]) v5 ea hwv)
    (by decide)) fun t' ⟨⟨tm, t12, t8, tz⟩, tk⟩ => ?_
  -- the key's bytes are where they were
  have hkey : bytesAt t.mem (State.addr Kk) L = bytesAt u₀.mem (State.addr Kk) L :=
    bytesAt_frame I.frame fun c hc r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact fun h => hd _ (Offset.contains_base _ (by omega_arith) (by have := E.fit; omega_arith)) h
  have hv8 : v.gpr .r8 = BitVec.ofNat 32 (18 - w) := by rw [vk.gpr (by decide), I.r8]
  have h8 : BitVec.ofNat 32 (18 - w) - 1#32 = BitVec.ofNat 32 (18 - (w + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_arith
  have sepw : ∀ j, j < 18 → j ≠ w → Mem.Sep (State.addr K + BitVec.ofNat 64 (4096 + 4 * j)) (32 / 8)
      (State.addr K + BitVec.ofNat 64 (4096 + 4 * w)) (32 / 8) :=
    fun j hj hne => Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine ⟨⟨by omega_arith, by rw [tk.gpr (by decide), v4], t12, by rw [t8, hv8, h8],
    (I.keep.trans (vk.trans tk)).mono (by decide), fun j hj => ?_, fun j h1 h2 => ?_, ?_⟩, by rw [tz, hv8, h8]⟩
  · rw [tm, vm]
    by_cases e : j = w
    · subst e
      rw [Mem.readW_writeW_self32, I.rest j (by omega_arith) hw18, kb_keyWord _ _ E.pos, hkey]
    · rw [Mem.readW_writeW_sep (sepw j (by omega_arith) e) (by decide)]; exact I.done j (by omega_arith)
  · rw [tm, vm, Mem.readW_writeW_sep (sepw j h2 (by omega_arith)) (by decide)]; exact I.rest j (by omega_arith) h2
  · rw [tm, vm]
    exact I.frame.writeW List.mem_cons_self _ (Offset.contains (e := 4096) (k := 72) (d := 4096 + 4 * w)
      (n := 4) _ (by omega_arith) (by omega_arith) (by omega_arith))

theorem keyP_run {u₀ : State} {K Kk : BitVec 32} {L : Nat} (E : KeyEnv Kk L u₀) (h2 : u₀.gpr .r2 = K)
    (fit : K.toNat + 4168 ≤ 2 ^ 32)
    (hw : InRegions u₀.wr (State.addr K + BitVec.ofNat 64 4096) 72)
    (hd : Region.Disjoint ⟨State.addr Kk, L⟩ ⟨State.addr K + BitVec.ofNat 64 4096, 72⟩) :
    WP isa keyP u₀ (KPInv u₀ K Kk L 18) := by
  unfold keyP
  apply WP.seq
  refine WP.mono (WP.keep [.r4, .r8, .r12] (Q := fun t => t.gpr .r4 = 0#32 ∧
      t.gpr .r12 = K + BitVec.ofNat 32 4096 ∧ t.gpr .r8 = BitVec.ofNat 32 18 ∧ t.mem = u₀.mem)
    (by brun [h2, pOff]) (by decide)) fun u₁ ⟨⟨a4, a12, a8, am⟩, ak⟩ => ?_
  have I0 : KPInv u₀ K Kk L 0 u₁ :=
    ⟨by decide, by rw [a4, Nat.mul_zero, Nat.zero_mod], by rw [a12], by rw [a8], ak.mono (by decide),
      fun j hj => absurd hj (Nat.not_lt_zero _), fun j _ _ => by rw [am], by rw [am]; exact Frame.refl _ _⟩
  refine WP.loop (M := isa) (Q := KPInv u₀ K Kk L 18)
    (fun (n : Nat) (v : State) => ∃ w, w < 18 ∧ n = 18 - w ∧ KPInv u₀ K Kk L w v) ?_ 18 u₁ ⟨0, by decide, rfl, I0⟩
  intro n v ⟨w, hw', hn, J⟩
  refine WP.mono (keyStep E fit hw hd hw' J) fun v' ⟨J', hz⟩ => ?_
  rw [eval_ne, hz]
  by_cases e : w + 1 = 18
  · left
    exact ⟨by rw [e]; rfl, e ▸ J'⟩
  · right
    have nz : BitVec.ofNat 32 (18 - (w + 1)) ≠ 0#32 := by
      intro h'; have := congrArg BitVec.toNat h'; simp at this; omega_arith
    exact ⟨by rw [beq_eq_false_iff_ne.mpr nz]; rfl, _, by omega_arith, w + 1, by omega_arith, rfl, J'⟩

end VG.Proof.Blowfish.Arm

end

end

/-! ### `Blowfish.Arm.KeyInit`, which only this module used -/

section

/-!
# Blowfish on ARMv7: the initial schedule

`initSchedule_run`: the 4168 bytes of the initial schedule's image, copied
from the table at `initSym` into the schedule at `r2`, seven words a step
(`copyWords_run`: the loads, then the stores) and six at the end.
-/

@[expose] public section

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

theorem copyReg_nodup : ∀ i < 7, ∀ j < 7, copyReg i = copyReg j → i = j := by decide

theorem copyReg_mem : ∀ i < 7, copyReg i ∈ copyRegs := by decide

theorem ldr_exec (u : State) (t b : Reg) {off : Nat} (ho : off < 4096)
    (hr : InRegions (u.rd ++ u.wr) (State.addr (u.gpr b + BitVec.ofNat 32 off)) 4) :
    exec (.ldr t b off) u = some (u.setReg t (u.mem.readW (State.addr (u.gpr b + BitVec.ofNat 32 off)) 32)) := by
  simp only [exec, ho, ↓reduceIte, State.load32, hr, Option.map_some]

theorem str_exec (u : State) (t b : Reg) {off : Nat} (ho : off < 4096)
    (hw : InRegions u.wr (State.addr (u.gpr b + BitVec.ofNat 32 off)) 4) :
    exec (.str t b off) u = some (withMem u (u.mem.writeW (State.addr (u.gpr b + BitVec.ofNat 32 off)) (u.gpr t))) := by
  simp only [exec, ho, ↓reduceIte, store32_eq, hw]

theorem map_range_succ {α : Type} (f : Nat → α) (n : Nat) :
    (List.range (n + 1)).map f = (List.range n).map f ++ ([f n] : List α) := by
  rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The loads of `copyWords k`: word `i` at `S + 4 i` into `copyReg i`. -/
theorem copyLoads_run (u : State) {S : BitVec 32} (h9 : u.gpr .r9 = S) :
    ∀ k ≤ 7, (∀ i < k, InRegions (u.rd ++ u.wr) (State.addr (S + BitVec.ofNat 32 (4 * i))) 4) →
    WP isa (.block ((List.range k).map fun i => Instr.ldr (copyReg i) .r9 (4 * i))) u fun t =>
      (∀ i < k, t.gpr (copyReg i) = u.mem.readW (State.addr (S + BitVec.ofNat 32 (4 * i))) 32) ∧
      t.mem = u.mem ∧ Keep copyRegs u t := by
  intro k hk hr
  induction k with
  | zero => exact WP.block_nil ⟨fun i hi => absurd hi (Nat.not_lt_zero _), rfl, Keep.refl _ _⟩
  | succ k ih =>
    rw [map_range_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hk]) fun i hi => hr i (by omega_using [hi])) fun t ⟨tg, tm, tk⟩ => ?_
    have t9 : t.gpr .r9 = S := by rw [tk.gpr (by decide), h9]
    have hrt : InRegions (t.rd ++ t.wr) (State.addr (t.gpr .r9 + BitVec.ofNat 32 (4 * k))) 4 := by
      rw [keep_reads tk, t9]; exact hr k (by omega_using [])
    refine WP.of_runBlock ⟨_, by rw [runBlock_cons, ldr_exec t _ _ (by omega_using [hk]) hrt, runStep_some, runBlock_nil], ?_⟩
    refine ⟨fun i hi => ?_, by rw [mem_setReg, tm], ?_⟩
    · by_cases e : i = k
      · subst e; rw [gpr_setReg_self, t9, tm]
      · rw [gpr_setReg_of_ne _ _ (fun h => e (copyReg_nodup i (by omega_using [hk, hi]) k (by omega_using [hk]) h)), tg i (by omega_using [hi, e])]
    · refine ⟨fun r hr' => ?_, tk.2.1, tk.2.2.1, tk.2.2.2⟩
      rw [gpr_setReg_of_ne _ _ (fun (h : r = copyReg k) => hr' (h ▸ copyReg_mem k (by omega_using [hk]))), tk.gpr hr']

/-- The stores of `copyWords k`: `copyReg i`, holding `w i`, at `D + 4 i`,
within `N` bytes from `D`. -/
theorem copyStores_run (v : State) {D : BitVec 32} {N : Nat} (h11 : v.gpr .r11 = D)
    (fit : D.toNat + N ≤ 2 ^ 32) (hw : InRegions v.wr (State.addr D) N) (w : Nat → BitVec 32) :
    ∀ k ≤ 7, 4 * k ≤ N → (∀ i < k, v.gpr (copyReg i) = w i) →
    WP isa (.block ((List.range k).map fun i => Instr.str (copyReg i) .r11 (4 * i))) v fun t =>
      (∀ o < 4 * k, t.mem (State.addr D + BitVec.ofNat 64 o) = (w (o / 4)).extractLsb' (8 * (o % 4)) 8) ∧
      Frame [⟨State.addr D, N⟩] v.mem t.mem ∧ Keep [] v t := by
  intro k hk hN hv
  induction k with
  | zero => exact WP.block_nil ⟨fun o ho => absurd ho (by omega_using []), Frame.refl _ _, Keep.refl _ _⟩
  | succ k ih =>
    rw [map_range_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hk]) (by omega_using [hN]) fun i hi => hv i (by omega_using [hi])) fun t ⟨tb, tf, tk⟩ => ?_
    have ea : State.addr (t.gpr .r11 + BitVec.ofNat 32 (4 * k)) = State.addr D + BitVec.ofNat 64 (4 * k) := by
      rw [tk.gpr (by decide), h11]; exact addr_add (by omega_using [fit, hN])
    have hwt : InRegions t.wr (State.addr (t.gpr .r11 + BitVec.ofNat 32 (4 * k))) 4 := by
      rw [ea, tk.2.2.1]; exact inRegions_off hw (by omega_using [hN])
    refine WP.of_runBlock ⟨_, by rw [runBlock_cons, str_exec t _ _ (by omega_using [hk]) hwt, runStep_some, runBlock_nil], ?_⟩
    have tv : t.gpr (copyReg k) = w k := by rw [tk.gpr (List.not_mem_nil), hv k (by omega_using [])]
    rw [ea, tv]
    refine ⟨fun o ho => ?_, ?_, ⟨fun r hr => tk.gpr hr, tk.2.1, tk.2.2.1, tk.2.2.2⟩⟩
    · rw [mem_store]
      by_cases hl : o < 4 * k
      · rw [writeW32_other _ (Offset.disjoint _ (by omega_using [hl]) (by omega_using [hk, ho]) (by omega_using [hk])), tb o hl]
      · rw [show o = 4 * k + (o - 4 * k) by omega_using [hl], ← Offset.add_add, st_byte _ _ _ (by omega_using [ho]),
          show (4 * k + (o - 4 * k)) / 4 = k by omega_using [ho], show (4 * k + (o - 4 * k)) % 4 = o - 4 * k by omega_using [ho]]
    · rw [mem_store]
      exact tf.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_using [hN]) (by omega_using [hk]))

/-- `copyWords k`: `4 k` bytes from `S` (readable) to `D` (writable). -/
theorem copyWords_run (u : State) {S D : BitVec 32} {k : Nat} (hk : k ≤ 7) (h9 : u.gpr .r9 = S)
    (h11 : u.gpr .r11 = D) (fitS : S.toNat + 4 * k ≤ 2 ^ 32) (fitD : D.toNat + 4 * k ≤ 2 ^ 32)
    (hr : InRegions (u.rd ++ u.wr) (State.addr S) (4 * k)) (hw : InRegions u.wr (State.addr D) (4 * k)) :
    WP isa (.block (copyWords k)) u fun t =>
      (∀ o < 4 * k, t.mem (State.addr D + BitVec.ofNat 64 o) = u.mem (State.addr S + BitVec.ofNat 64 o)) ∧
      Frame [⟨State.addr D, 4 * k⟩] u.mem t.mem ∧ Keep copyRegs u t := by
  unfold copyWords
  rw [WP.block_append_iff]
  have ea : ∀ i < k, State.addr (S + BitVec.ofNat 32 (4 * i)) = State.addr S + BitVec.ofNat 64 (4 * i) :=
    fun i hi => addr_add (by omega_using [fitS, hi])
  refine WP.mono (copyLoads_run u h9 k hk fun i hi => by
    rw [ea i hi]; exact inRegions_off hr (by omega_using [hi])) fun v ⟨vg, vm, vk⟩ => ?_
  refine WP.mono (copyStores_run v (by rw [vk.gpr (by decide), h11]) fitD (by rw [vk.2.2.1]; exact hw)
    (fun i => u.mem.readW (State.addr (S + BitVec.ofNat 32 (4 * i))) 32) k hk (by omega_using []) vg)
    fun t ⟨tb, tf, tk⟩ => ⟨fun o ho => ?_, by rw [← vm]; exact tf, (vk.trans tk).mono (by simp)⟩
  rw [tb o ho, ea _ (by omega_using [ho]), ← Mem.readW_byte _ _ (Nat.mod_lt _ (by decide)), Offset.add_add,
    show 4 * (o / 4) + o % 4 = o by omega_using []]

/-- What the copy assumes: the table at `T`, holding the initial schedule's
image, readable and apart from the schedule at `K`, which is writable. -/
structure CopyEnv (T K : BitVec 32) (u₀ : State) : Prop where
  fitT : T.toNat + 4168 ≤ 2 ^ 32
  fitK : K.toNat + 4168 ≤ 2 ^ 32
  table : ∀ o < 4168, u₀.mem (State.addr T + BitVec.ofNat 64 o) = initByte o
  rdT : InRegions (u₀.rd ++ u₀.wr) (State.addr T) 4168
  wrK : InRegions u₀.wr (State.addr K) 4168
  sep : Region.Disjoint ⟨State.addr T, 4168⟩ ⟨State.addr K, 4168⟩

/-- The registers the copy changes. -/
def copyKeep : List Reg := copyRegs ++ [.r9, .r11, .r12]

/-- After `n` steps of seven words, from `u₀`. -/
structure CopyInv (T K : BitVec 32) (u₀ : State) (n : Nat) (t : State) : Prop where
  le : n ≤ 148
  r9 : t.gpr .r9 = T + BitVec.ofNat 32 (28 * n)
  r11 : t.gpr .r11 = K + BitVec.ofNat 32 (28 * n)
  r12 : t.gpr .r12 = BitVec.ofNat 32 (148 - n)
  keep : Keep copyKeep u₀ t
  bytes : ∀ o < 28 * n, t.mem (State.addr K + BitVec.ofNat 64 o) = initByte o
  frame : Frame [⟨State.addr K, 4168⟩] u₀.mem t.mem

/-- The copy's result. -/
structure InitInv (u₀ : State) (K : BitVec 32) (t : State) : Prop where
  bytes : ∀ o < 4168, t.mem (State.addr K + BitVec.ofNat 64 o) = initByte o
  frame : Frame [⟨State.addr K, 4168⟩] u₀.mem t.mem
  keep : Keep copyKeep u₀ t

/-- `copyWords k` at step `n` of the copy: the table's bytes from offset
`28 n` to the schedule. -/
theorem copyAt_run {T K : BitVec 32} {u₀ : State} (E : CopyEnv T K u₀) {n k : Nat} (hk : k ≤ 7)
    (hnk : 28 * n + 4 * k ≤ 4168) {t : State} (I : CopyInv T K u₀ n t) :
    WP isa (.block (copyWords k)) t fun t' =>
      (∀ o < 28 * n + 4 * k, t'.mem (State.addr K + BitVec.ofNat 64 o) = initByte o) ∧
      Frame [⟨State.addr K, 4168⟩] u₀.mem t'.mem ∧ Keep copyRegs t t' := by
  have fT := E.fitT
  have fK := E.fitK
  have eT : State.addr (T + BitVec.ofNat 32 (28 * n)) = State.addr T + BitVec.ofNat 64 (28 * n) :=
    addr_add (by omega_using [hnk, fT])
  have eK : State.addr (K + BitVec.ofNat 32 (28 * n)) = State.addr K + BitVec.ofNat 64 (28 * n) :=
    addr_add (by omega_using [hnk, fK])
  have fS : (T + BitVec.ofNat 32 (28 * n)).toNat + 4 * k ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 28 * n) (by omega_using [hnk]),
      Nat.mod_eq_of_lt (by omega_using [hnk, fT])]; omega_using [hnk, fT]
  have fD : (K + BitVec.ofNat 32 (28 * n)).toNat + 4 * k ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 28 * n) (by omega_using [hnk]),
      Nat.mod_eq_of_lt (by omega_using [hnk, fK])]; omega_using [hnk, fK]
  refine WP.mono (copyWords_run t hk I.r9 I.r11 fS fD
    (by rw [eT, keep_reads I.keep]; exact inRegions_off E.rdT (by omega_using [hnk]))
    (by rw [eK, I.keep.2.2.1]; exact inRegions_off E.wrK (by omega_using [hnk])))
    fun t' ⟨tb, tf, tk⟩ => ⟨fun o ho => ?_, I.frame.trans (tf.sub fun r hr => ?_), tk⟩
  · by_cases hl : o < 28 * n
    · rw [← I.bytes o hl]
      refine tf _ fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      rw [eK]
      exact fun h => (Offset.disjoint _ (d := o) (n := 1) (e := 28 * n) (k := 4 * k) (by omega_using [hl]) (by omega_using [hnk, ho])
        (by omega_using [hnk])) _ (Region.contains_self _ _) h
    · rw [show o = 28 * n + (o - 28 * n) by omega_using [hl], ← Offset.add_add, ← eK, tb _ (by omega_using [ho, hl]), eT,
        Offset.add_add, ← E.table _ (by omega_using [hnk, ho])]
      refine I.frame _ fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact E.sep _ (Offset.contains_base _ (by omega_using [hnk, ho]) (by omega_using [hnk, ho]))
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, by rw [eK]; exact Offset.sub_base _ (by omega_using [hnk])⟩

/-- One step of seven words. -/
theorem copyStep_run {T K : BitVec 32} {u₀ : State} (E : CopyEnv T K u₀) {n : Nat} (hn : n < 148) {t : State}
    (I : CopyInv T K u₀ n t) :
    WP isa (.block copyStep) t fun t' =>
      CopyInv T K u₀ (n + 1) t' ∧ t'.z = (BitVec.ofNat 32 (148 - (n + 1)) == 0#32) := by
  unfold copyStep
  rw [WP.block_append_iff]
  refine WP.mono (copyAt_run E (k := 7) (by decide) (by omega_using [hn]) I) fun v ⟨vb, vf, vk⟩ => ?_
  have v9 : v.gpr .r9 = T + BitVec.ofNat 32 (28 * n) := by rw [vk.gpr (by decide), I.r9]
  have v11 : v.gpr .r11 = K + BitVec.ofNat 32 (28 * n) := by rw [vk.gpr (by decide), I.r11]
  have v12 : v.gpr .r12 = BitVec.ofNat 32 (148 - n) := by rw [vk.gpr (by decide), I.r12]
  have h12 : BitVec.ofNat 32 (148 - n) - 1#32 = BitVec.ofNat 32 (148 - (n + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_using [hn]
  refine WP.mono (WP.keep [.r9, .r11, .r12] (Q := fun t' => t'.gpr .r9 = T + BitVec.ofNat 32 (28 * (n + 1)) ∧
      t'.gpr .r11 = K + BitVec.ofNat 32 (28 * (n + 1)) ∧ t'.gpr .r12 = BitVec.ofNat 32 (148 - (n + 1)) ∧
      t'.z = (BitVec.ofNat 32 (148 - (n + 1)) == 0#32) ∧ t'.mem = v.mem)
    (by brun [v9, v11, v12, ofs_add, h12]; refine ⟨?_, ?_⟩ <;> congr 2) (by decide))
    fun t' ⟨⟨a9, a11, a12, az, am⟩, ak⟩ => ⟨⟨by omega_using [hn], a9, a11, a12, (I.keep.trans (vk.trans ak)).mono
      (by decide), fun o ho => by rw [am]; exact vb o (by omega_using [ho]), by rw [am]; exact vf⟩, az⟩

theorem initSchedule_run (u₀ : State) {K : BitVec 32} (h2 : u₀.gpr .r2 = K)
    (E : CopyEnv (u₀.syms initSym) K u₀) : WP isa initSchedule u₀ (InitInv u₀ K) := by
  unfold initSchedule
  apply WP.seq
  refine WP.mono (WP.keep [.r9, .r11, .r12] (Q := fun t => t.gpr .r9 = u₀.syms initSym ∧
      t.gpr .r11 = K + BitVec.ofNat 32 0 ∧ t.gpr .r12 = BitVec.ofNat 32 148 ∧ t.mem = u₀.mem)
    (by brun [h2, syms_setReg]) (by decide)) fun u₁ ⟨⟨a9, a11, a12, am⟩, ak⟩ => ?_
  have I0 : CopyInv (u₀.syms initSym) K u₀ 0 u₁ :=
    ⟨by decide, by rw [a9, Nat.mul_zero, BitVec.add_zero], by rw [a11], by rw [a12], ak.mono (by decide),
      fun o ho => absurd ho (by omega_using []), by rw [am]; exact Frame.refl _ _⟩
  apply WP.seq
  refine WP.mono (WP.loop (M := isa) (Q := CopyInv (u₀.syms initSym) K u₀ 148)
    (fun (m : Nat) (v : State) => ∃ n, n < 148 ∧ m = 148 - n ∧ CopyInv (u₀.syms initSym) K u₀ n v) ?_ 148 u₁
    ⟨0, by decide, rfl, I0⟩) fun v J => ?_
  · intro m v ⟨n, hn, hm, J⟩
    refine WP.mono (copyStep_run E hn J) fun v' ⟨J', hz⟩ => ?_
    rw [eval_ne, hz]
    by_cases e : n + 1 = 148
    · left
      exact ⟨by rw [e]; rfl, e ▸ J'⟩
    · right
      have nz : BitVec.ofNat 32 (148 - (n + 1)) ≠ 0#32 := by
        intro h'; have := congrArg BitVec.toNat h'; simp at this; omega_using [hn, e, this]
      exact ⟨by rw [beq_eq_false_iff_ne.mpr nz]; rfl, _, by omega_using [hn, hm], n + 1, by omega_using [hn, e], rfl, J'⟩
  · refine WP.mono (copyAt_run E (k := 6) (by decide) (by decide) J) fun t ⟨tb, tf, tk⟩ =>
      ⟨fun o ho => tb o (by omega_using [ho]), tf, (J.keep.trans tk).mono (by decide)⟩

end VG.Proof.Blowfish.Arm

end

end


/-!
# Blowfish on ARMv7: key expansion

`expandKey_correct`: our caller's registers saved, the initial schedule
written, the key XORed into the P-array, the 521 encryptions, and the
registers restored.
-/

@[expose] public section

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

/-- What key expansion may assume: the key and the table of the initial
schedule readable, the schedule and the working space writable, apart, none
wrapping around, and a valid key length. -/
structure KeyPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, ⟨State.addr (s.syms initSym), 4168⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r2), 4168⟩, ⟨State.addr (s.gpr .r3), 64⟩]
  keySch : (⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 4168⟩
  keyBuf : (⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 64⟩
  schBuf : (⟨State.addr (s.gpr .r2), 4168⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 64⟩
  fitKey : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  fitSch : (s.gpr .r2).toNat + 4168 ≤ 2 ^ 32
  fitBuf : (s.gpr .r3).toNat + 64 ≤ 2 ^ 32
  valid : validKey (s.gpr .r1).toNat
  held : ∀ i < 521, s.mem.readW (State.addr (s.syms initSym) + BitVec.ofNat 64 (8 * i)) 64 =
    Impl.Blowfish.initWords.getD i 0
  fitT : (s.syms initSym).toNat + 4168 ≤ 2 ^ 32
  tSch : (⟨State.addr (s.syms initSym), 4168⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 4168⟩
  tBuf : (⟨State.addr (s.syms initSym), 4168⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 64⟩

/-- What key expansion guarantees. -/
structure KeyPost (s t : State) : Prop where
  regs : ∀ r ∈ preserved, t.gpr r = s.gpr r
  sched : scheduleAt t.mem (State.addr (s.gpr .r2)) =
    expandKey (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)

theorem expandKey_correct {s : State} (h : KeyPre s) : WP isa Impl.Blowfish.Arm.expandKey s (KeyPost s) := by
  obtain ⟨hrd, hwr, ks, kb, sb, fKey, fSch, fBuf, valid, held, fitT, tSch, tBuf⟩ := h
  have hL := valid.1
  have hL' := valid.2
  have bR : (⟨State.addr (s.gpr .r3), 64⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have sR : (⟨State.addr (s.gpr .r2), 4168⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  let key := bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
  unfold Impl.Blowfish.Arm.expandKey
  apply WP.seq
  rw [show save = saved.map (fun p => Instr.str p.1 .r3 p.2) ++ [] from rfl]
  refine Spill.save_slots_ok saved_slots (by omega_using [fBuf]) (fun d _ hd =>
    ⟨_, bR, Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])⟩) (WP.block_nil ?_)
  let s₁ : State := { s with mem := Spill.saveMem s.mem (State.addr (s.gpr .r3)) s.gpr saved }
  have F₁ : Frame [⟨State.addr (s.gpr .r3), 64⟩] s.mem s₁.mem :=
    (Spill.saveMem_frame s.mem _ s.gpr (L := 36) (by decide) saved (by decide)).sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  have S₁ : Spill.Saved s₁.mem (State.addr (s.gpr .r3)) s.gpr saved :=
    Spill.saveMem_saved _ _ _ _ saved_slots
  -- the initial schedule, from the table
  have CE : CopyEnv (s₁.syms initSym) (s.gpr .r2) s₁ := by
    refine ⟨fitT, fSch, fun o ho => ?_, ?_, ⟨_, sR, Region.contains_self _ _⟩, tSch⟩
    · rw [← table_byte held ho]
      refine F₁ _ fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact tBuf _ (Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho]))
    · show InRegions (s.rd ++ s.wr) _ _
      rw [hrd]; exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self), Region.contains_self _ _⟩
  apply WP.seq
  refine WP.mono (initSchedule_run s₁ rfl CE) fun u₃ I₃ => ?_
  have k₃ : Keep copyKeep s u₃ := I₃.keep
  -- the key into the P-array
  have KE : KeyEnv (s.gpr .r0) (s.gpr .r1).toNat u₃ :=
    ⟨by rw [k₃.gpr (by decide)], by rw [k₃.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by omega_using [hL], hL', fKey, by rw [keep_reads k₃, hrd]; exact ⟨_, List.mem_cons_self, Region.contains_self _ _⟩⟩
  have dKP : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
      ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 4096, 72⟩ := ks.sub_right (Offset.sub_base _ (by decide))
  apply WP.seq
  refine WP.mono (keyP_run KE (by rw [k₃.gpr (by decide)]) fSch
    (by rw [k₃.2.2.1]; exact ⟨_, sR, Offset.contains_base _ (by decide) (by omega_using [])⟩) dKP) fun u₄ I₄ => ?_
  have k₄ : Keep (copyKeep ++ [.r4, .r5, .r6, .r7, .r8]) s u₄ := (k₃.trans I₄.keep).mono (by decide)
  -- the memory so far
  have m₃ : Frame [⟨State.addr (s.gpr .r3), 64⟩, ⟨State.addr (s.gpr .r2), 4168⟩] s.mem u₃.mem := by
    refine (F₁.mono (by simp)).trans ?_
    exact I₃.frame.mono (by simp [s₁])
  have hkey : bytesAt u₃.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat = key :=
    bytesAt_frame m₃ fun c hc r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact kb _ (Offset.contains_base _ (by omega_using [hc]) (by omega_using [hc]))
      · exact ks _ (Offset.contains_base _ (by omega_using [hc]) (by omega_using [hc]))
  have hP : ∀ i < 18, u₄.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4096 + 4 * i)) 32 =
      initial.getD i 0 ^^^ Spec.Blowfish.keyWord key i := fun i hi => by
    rw [I₄.done i hi, hkey, table_P I₃.bytes hi]
  have hS : ∀ o < 4096, u₄.mem (State.addr (s.gpr .r2) + BitVec.ofNat 64 o) = initByte o := fun o ho => by
    rw [I₄.frame _ fun r hr => ?_, I₃.bytes o (by omega_using [ho])]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact (Offset.disjoint _ (d := o) (n := 1) (e := 4096) (k := 72) (by omega_using [ho]) (by omega_using [ho]) (by decide)) _
      (Region.contains_self _ _)
  have hK : scheduleAt u₄.mem (State.addr (s.gpr .r2)) = keyed key := keyed_of_mem hS hP
  -- the encryptions
  have EE : EncEnv (s.gpr .r2) (s.gpr .r3) s :=
    ⟨fSch, fBuf, ⟨_, sR, Region.contains_self _ _⟩, ⟨_, bR, Region.contains_self _ _⟩, sb⟩
  have F₄ : Frame [⟨State.addr (s.gpr .r2), 4168⟩] s₁.mem u₄.mem := by
    exact I₃.frame.trans (I₄.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩)
  apply WP.seq
  refine WP.mono (WP.keep [.r0, .r1, .r2] (Q := fun t => t.gpr .r0 = s.gpr .r2 ∧ t.gpr .r1 = 0#32 ∧
      t.gpr .r2 = 0#32 ∧ t.mem = u₄.mem)
    (by brun [k₄.gpr (show Reg.r2 ∉ copyKeep ++ [Reg.r4, Reg.r5, Reg.r6, Reg.r7, Reg.r8] by decide)])
    (by decide)) fun u₅ ⟨⟨a0, a1, a2, am⟩, ak⟩ => ?_
  have I₅ : EncInv key (s.gpr .r2) (s.gpr .r3) s.gpr s 0 u₅ := by
    refine ⟨by decide, a0, ?_, by rw [am, hK, ksIter_zero], by rw [a1, a2, ksIter_zero]; rfl,
      saved_frame S₁ (by rw [am]; exact F₄.mono (by simp)) sb, ?_, by rw [ak.2.1, I₄.keep.2.1, I₃.keep.2.1],
      by rw [ak.2.2.1, I₄.keep.2.2.1, I₃.keep.2.2.1]⟩
    · rw [ak.gpr (by decide), I₄.keep.gpr (by decide), I₃.keep.gpr (by decide)]
    · rw [am]
      have F₄' : Frame [⟨State.addr (s.gpr .r3), 64⟩, ⟨State.addr (s.gpr .r2), 4168⟩] u₃.mem u₄.mem := by
        refine I₄.frame.sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub_base _ (by decide)⟩
      exact (m₃.trans F₄').mono (by simp)
  apply WP.seq
  refine WP.mono (encryptP_run EE I₅) fun u₆ I₆ => ?_
  apply WP.seq
  refine WP.mono (encryptS_run EE I₆) fun u₇ I₇ => ?_
  refine WP.mono (restore_run (u := u₇) (by rw [I₇.r3]; omega_using [fBuf]) (fun d hd => ?_)
    (by rw [I₇.r3]; exact I₇.saved)) fun t ⟨tr, tm⟩ => ⟨tr, by rw [tm, I₇.sched, expandKey_eq]⟩
  rw [I₇.rd, I₇.wr, I₇.r3]
  exact region_in (inRegions_off EE.wrB (by omega_using [hd]))

end VG.Proof.Blowfish.Arm
