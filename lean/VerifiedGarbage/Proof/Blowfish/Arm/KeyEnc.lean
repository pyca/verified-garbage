import VerifiedGarbage.Proof.Blowfish.Arm.KeyP
import VerifiedGarbage.Proof.Blowfish.KeySched
import VerifiedGarbage.Proof.Rc4.Scan32

/-!
# Blowfish on ARMv7: key expansion's 521 encryptions

Each encryption runs the block function under the schedule as written so
far, and its output replaces the next two entries: the P-array's, as words
(`encryptP_run`), then the S-boxes', a byte per plane (`encryptS_run`). The
pointer to the next entries and the encryptions left are in the working
space, at `lr + 36` and `lr + 40`.
-/

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
    exact region_in (inRegions_off E.wrK (by omega))
  refine WP.mono (cipher_run CE true) fun u' ⟨h, k, m⟩ => ⟨?_, k, m⟩
  rw [h, I.r0, I.sched, ord_true, ← I.halves]; rfl

theorem ksIter_step (key : List Byte) {j : Nat} (hj : j < 521) :
    ksIter key (j + 1) =
      (((ksIter key j).1.set (2 * j) (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1
          (by omega)).set (2 * j + 1)
          (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2 (by omega),
        (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1,
        (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2) := by
  rw [ksIter_succ, ksStep, set!_eq_set _ (by omega), set!_eq_set _ (by omega)]

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
      (by decide))).sub_right (Offset.sub_base Pa (d := o) (n := 4) (k := 8) (by omega)))
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
  have eB : State.addr (B + BitVec.ofNat 32 36) = State.addr B + BitVec.ofNat 64 36 := addr_add (by omega)
  have eC : State.addr (B + BitVec.ofNat 32 40) = State.addr B + BitVec.ofNat 64 40 := addr_add (by omega)
  have e0 : State.addr (K + BitVec.ofNat 32 (4096 + 8 * j) + BitVec.ofNat 32 0) =
      State.addr K + BitVec.ofNat 64 (4096 + 4 * (2 * j)) := by
    rw [BitVec.add_zero, addr_add (by omega)]; congr 2; omega
  have e4 : State.addr (K + BitVec.ofNat 32 (4096 + 8 * j) + BitVec.ofNat 32 4) =
      State.addr K + BitVec.ofNat 64 (4096 + 4 * (2 * j)) + BitVec.ofNat 64 4 := by
    rw [ofs_add, addr_add (by omega), Offset.add_add]; congr 2; omega
  have dj : Region.Disjoint ⟨State.addr B + BitVec.ofNat 64 36, 8⟩
      ⟨State.addr K + BitVec.ofNat 64 (4096 + 4 * (2 * j)), 8⟩ :=
    (E.sep.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by omega))
  have w₁ : u₁.wr = s₀.wr := by rw [ck.2.2.1, J.wr]
  refine WP.mono (WP.keep [.r11, .r12] (storeP_run u₁ (C := BitVec.ofNat 32 (9 - j))
    (by rw [ck.gpr (by decide), J.r3]) eB eC e0 e4 (E.wB w₁ (by decide)) (E.wK w₁ (by omega)) dj
    (by rw [cm]; exact I.ptr) (by rw [cm]; exact I.cnt)) (by decide)) fun u₂ ⟨⟨sm, sz⟩, sk⟩ => ?_
  obtain ⟨M36, M40, MF⟩ := slots_facts (((u₁.mem.writeW (State.addr K + BitVec.ofNat 64 (4096 + 4 * (2 * j)))
    (u₁.gpr .r1)).writeW (State.addr K + BitVec.ofNat 64 (4096 + 4 * (2 * j)) + BitVec.ofNat 64 4) (u₁.gpr .r2)))
    (State.addr B) (K + BitVec.ofNat 32 (4096 + 8 * j) + BitVec.ofNat 32 8) (BitVec.ofNat 32 (9 - j) - 1#32)
  rw [← sm] at M36 M40 MF
  have F2 : Frame [⟨State.addr K, 4168⟩] u₁.mem ((u₁.mem.writeW (State.addr K +
      BitVec.ofNat 64 (4096 + 4 * (2 * j))) (u₁.gpr .r1)).writeW (State.addr K +
      BitVec.ofNat 64 (4096 + 4 * (2 * j)) + BitVec.ofNat 64 4) (u₁.gpr .r2)) :=
    ((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))).writeW
      List.mem_cons_self _ (by rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega))
  have FF : Frame [⟨State.addr K, 4168⟩, ⟨State.addr B + BitVec.ofNat 64 36, 8⟩] u.mem u₂.mem := by
    rw [← cm]
    exact (F2.mono (by simp)).trans (MF.mono (by simp))
  have hsched : scheduleAt u₂.mem (State.addr K) = (ksIter key (j + 1)).1 := by
    rw [scheduleAt_eq_of_frame _ MF (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact E.sep.sub_right (Offset.sub_base _ (by decide))),
      Offset.add_add, show 4096 + 4 * (2 * j) + 4 = 4096 + 4 * (2 * j + 1) by omega,
      scheduleAt_writeW_P _ _ (by omega), scheduleAt_writeW_P _ _ (by omega), cm, J.sched,
      ksIter_step key (by omega)]
    have h1 : u₁.gpr .r1 = out.1 := congrArg Prod.fst c12
    have h2 : u₁.gpr .r2 = out.2 := congrArg Prod.snd c12
    rw [h1, h2]
  refine ⟨⟨⟨by omega, by rw [sk.gpr (by decide), ck.gpr (by decide), J.r0],
    by rw [sk.gpr (by decide), ck.gpr (by decide), J.r3], hsched, ?_,
    saved_frame J.saved FF E.sep, J.frame.trans (FF.sub fun r hr => ?_), by rw [sk.2.1, ck.2.1, J.rd],
    by rw [sk.2.2.1, w₁]⟩, by omega, by rw [M36, ofs_add]; congr 2, ?_⟩, ?_⟩
  · rw [sk.gpr (by decide), sk.gpr (by decide), c12, ksIter_step key (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub_base _ (by decide)⟩
  · rw [M40]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · rw [sz]; congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

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
  have eB : State.addr (B + BitVec.ofNat 32 36) = State.addr B + BitVec.ofNat 64 36 := addr_add (by omega)
  have eC : State.addr (B + BitVec.ofNat 32 40) = State.addr B + BitVec.ofNat 64 40 := addr_add (by omega)
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
      intro h'; have := congrArg BitVec.toNat h'; simp at this; omega
    exact ⟨by rw [beq_eq_false_iff_ne.mpr nz]; rfl, _, by omega, j + 1, by omega, rfl, P'⟩

/-- The offset of S-box entry `sDone j`'s first plane. -/
def sOff (j : Nat) : Nat := 1024 * (sDone j / 256) + sDone j % 256

theorem sOff_entry {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) {b k : Nat} (hk : k < 2) :
    sOff j + (256 * b + k) = entryOff (2 * j + k) b := by
  rw [← entryOff_sbox h9 hj k hk, sOff]

theorem sOff_lt {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) : sOff j ≤ 3326 := by
  unfold sOff sDone; omega

theorem sOff_succ {j : Nat} (h9 : 9 ≤ j) :
    sOff (j + 1) = if (sOff j + 2) % 256 = 0 then sOff j + 2 + 768 else sOff j + 2 := by
  unfold sOff sDone; split <;> omega

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
    scheduleAt (sWrites m Ka (sOff j) x y) Ka = ((scheduleAt m Ka).set (2 * j) x (by omega)).set (2 * j + 1) y
      (by omega) := by
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
  rw [scheduleAt_write_bytes _ _ (by omega), Nat.add_zero, scheduleAt_write_bytes _ _ (by omega)]

theorem sWrites_frame (m : Mem) (Ka : Addr) {q : Nat} (hq : q + 770 ≤ 4168) (x y : BitVec 32) :
    Frame [⟨Ka, 4168⟩] m (sWrites m Ka q x y) := by
  have c : ∀ e, e < 770 → Region.Contains ⟨Ka, 4168⟩ (Ka + BitVec.ofNat 64 (q + e)) (8 / 8) :=
    fun e he => Offset.contains_base _ (by omega) (by omega)
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
    omega
  rw [e, BitVec.sub_zero]
  by_cases h : (q + 2) % 256 = 0
  · rw [h]; simp
  · have : BitVec.ofNat 32 ((q + 2) % 256) ≠ 0#32 := by
      intro e'; have := congrArg BitVec.toNat e'; simp at this; omega
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
  have eB : State.addr (B + BitVec.ofNat 32 36) = State.addr B + BitVec.ofNat 64 36 := addr_add (by omega)
  have eC : State.addr (B + BitVec.ofNat 32 40) = State.addr B + BitVec.ofNat 64 40 := addr_add (by omega)
  have w₁ : u₁.wr = s₀.wr := by rw [ck.2.2.1, J.wr]
  unfold storeS
  apply WP.seq
  refine WP.mono (WP.keep [.r9, .r11, .r12] (storeSHead_run u₁ (K := K) (Ka := State.addr K) (q := sOff j)
    (C := BitVec.ofNat 32 (521 - j))
    (by rw [ck.gpr (by decide), J.r3]) (by rw [ck.gpr (by decide), J.r0]) eB eC
    (region_in (E.wB w₁ (by decide))) (by rw [cm]; exact I.ptr) (by rw [cm]; exact I.cnt)
    (fun c hc => by rw [ofs_add, addr_add (by omega)])
    (fun c hc => E.wK w₁ (by omega))) (by decide)) fun u₂ ⟨⟨hm, h12, h11, hz⟩, hk⟩ => ?_
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
  have F8 := sWrites_frame u₁.mem (State.addr K) (q := sOff j) (by omega) (u₁.gpr .r1) (u₁.gpr .r2)
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
  refine ⟨⟨⟨by omega, by rw [k₄.gpr (by decide), J.r0], by rw [k₄.gpr (by decide), J.r3], hsched, ?_,
    saved_frame J.saved FF E.sep, J.frame.trans (FF.sub fun r hr => ?_), by rw [k₄.2.1, J.rd],
    by rw [k₄.2.2.1, J.wr]⟩, by omega, by rw [M36, g12], ?_⟩, ?_⟩
  · rw [tk.gpr (by decide), tk.gpr (by decide), gk.gpr (by decide), gk.gpr (by decide), hk.gpr (by decide),
      hk.gpr (by decide), c12, ksIter_step key hj]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub_base _ (by decide)⟩
  · rw [M40]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · rw [tz]; congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem encryptS_run {key : List Byte} {K B : BitVec 32} {g : Reg → BitVec 32} {s₀ : State}
    (E : EncEnv K B s₀) {u : State} (I : EncInv key K B g s₀ 9 u) :
    WP isa encryptS u (EncInv key K B g s₀ 521) := by
  have fB := E.fitB
  have eB : State.addr (B + BitVec.ofNat 32 36) = State.addr B + BitVec.ofNat 64 36 := addr_add (by omega)
  have eC : State.addr (B + BitVec.ofNat 32 40) = State.addr B + BitVec.ofNat 64 40 := addr_add (by omega)
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
      intro h'; have := congrArg BitVec.toNat h'; simp at this; omega
    exact ⟨by rw [beq_eq_false_iff_ne.mpr nz]; rfl, _, by omega, j + 1, by omega, rfl, P'⟩

end VG.Proof.Blowfish.Arm