import VerifiedGarbage.Proof.Blowfish.Arm.Cipher
import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Framework.Arm.Bytes

/-!
# Blowfish on ARMv7: ECB

`ecb_correct`: every block becomes its encryption or decryption, one at a
time; our caller's registers are saved in the working space and restored.
-/

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

/-! ## Blocks in and out of the halves -/

theorem rev_byte (x : BitVec 32) {b : Nat} (hb : b < 4) :
    (rev x).extractLsb' (8 * b) 8 = x.extractLsb' (8 * (3 - b)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  exact rev_bit x hb hi

/-- The big-endian word at offset `o` of the block at `q`. -/
theorem rev_load (m : Mem) (q : Addr) {o : Nat} (ho : o ≤ 4) :
    rev (m.readW (q + BitVec.ofNat 64 o) 32) = decodeWord (blockAt m q) o := by
  refine word_ext fun b hb => ?_
  rw [rev_byte _ hb, decodeWord_byte _ _ hb, blockAt_getD _ _ (by omega),
    ← Mem.readW_byte m _ (by omega), Offset.add_add]

theorem sep_of_disjoint {a b : Addr} {n k : Nat} (h : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) :
    Mem.Sep a n b k :=
  fun x h₁ h₂ => h x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 8⟩) hd (by show 8 ≤ 2 ^ 64; decide) hi

theorem inRegions_off {rs : List Region} {a : Addr} {N o n : Nat} (h : InRegions rs a N) (hon : o + n ≤ N) :
    InRegions rs (a + BitVec.ofNat 64 o) n := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : a + BitVec.ofNat 64 o - r.base = (a - r.base) + BitVec.ofNat 64 o := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 o),
      ← BitVec.add_assoc]
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((a - r.base).toNat + o % 2 ^ 64) (2 ^ 64)
  have := Nat.mod_le o (2 ^ 64)
  omega

theorem inRegions_pre {rs : List Region} {a : Addr} {N n : Nat} (h : InRegions rs a N) (hn : n ≤ N) :
    InRegions rs a n := by
  have := inRegions_off (o := 0) (n := n) h (by omega)
  rwa [BitVec.add_zero] at this

/-- The block at the data pointer (in the working space) into the halves. -/
theorem loadBlock_run (u : State) {B P : BitVec 32} {Ba Pa : Addr} (hlr : u.gpr .r3 = B)
    (eB : State.addr (B + BitVec.ofNat 32 36) = Ba + BitVec.ofNat 64 36)
    (e0 : State.addr (P + BitVec.ofNat 32 0) = Pa) (e4 : State.addr (P + BitVec.ofNat 32 4) = Pa + BitVec.ofNat 64 4)
    (rB : InRegions (u.rd ++ u.wr) (Ba + BitVec.ofNat 64 36) 4)
    (r0 : InRegions (u.rd ++ u.wr) Pa 4) (r4 : InRegions (u.rd ++ u.wr) (Pa + BitVec.ofNat 64 4) 4)
    (hP : u.mem.readW (Ba + BitVec.ofNat 64 36) 32 = P) :
    WP isa (.block loadBlock) u fun t =>
      t.gpr .r1 = decodeWord (blockAt u.mem Pa) 0 ∧ t.gpr .r2 = decodeWord (blockAt u.mem Pa) 4 ∧
        t.mem = u.mem := by
  have l0 := rev_load u.mem Pa (o := 0) (by decide)
  have l4 := rev_load u.mem Pa (o := 4) (by decide)
  rw [BitVec.add_zero] at l0
  unfold loadBlock
  brun [hlr, ptrOff, eB, e0, e4, rB, r0, r4, hP, l0, l4]

/-- The halves to the block at the data pointer, the next block's pointer,
and the counter less one. -/
theorem storeBlock_run (u : State) {B P C : BitVec 32} {Ba Pa : Addr} (hlr : u.gpr .r3 = B)
    (eB : State.addr (B + BitVec.ofNat 32 36) = Ba + BitVec.ofNat 64 36)
    (eC : State.addr (B + BitVec.ofNat 32 40) = Ba + BitVec.ofNat 64 40)
    (e0 : State.addr (P + BitVec.ofNat 32 0) = Pa) (e4 : State.addr (P + BitVec.ofNat 32 4) = Pa + BitVec.ofNat 64 4)
    (wB : InRegions u.wr (Ba + BitVec.ofNat 64 36) 8)
    (w0 : InRegions u.wr Pa 8) (dj : Region.Disjoint ⟨Ba + BitVec.ofNat 64 36, 8⟩ ⟨Pa, 8⟩)
    (hP : u.mem.readW (Ba + BitVec.ofNat 64 36) 32 = P) (hC : u.mem.readW (Ba + BitVec.ofNat 64 40) 32 = C) :
    WP isa (.block storeBlock) u fun t =>
      t.mem = (((u.mem.writeW Pa (rev (u.gpr .r1))).writeW (Pa + BitVec.ofNat 64 4) (rev (u.gpr .r2))).writeW
          (Ba + BitVec.ofNat 64 36) (P + BitVec.ofNat 32 8)).writeW (Ba + BitVec.ofNat 64 40) (C - 1#32) ∧
        t.z = (C - 1#32 == 0#32) ∧ t.gpr .r3 = B ∧ t.gpr .r0 = u.gpr .r0 := by
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
  unfold storeBlock countDown
  brun [hlr, ptrOff, cntOff, eB, eC, e0, e4, rB, rC, r0, r4, region_in (rs := u.rd) rB,
    region_in (rs := u.rd) rC, hP, hC]

/-- What the stores leave: the block's bytes, the pointer and the counter. -/
theorem stored_facts (m : Mem) (Ba Pa : Addr) (L R P C : BitVec 32)
    (dj : Region.Disjoint ⟨Ba + BitVec.ofNat 64 36, 8⟩ ⟨Pa, 8⟩) :
    let M := (((m.writeW Pa (rev L)).writeW (Pa + BitVec.ofNat 64 4) (rev R)).writeW
          (Ba + BitVec.ofNat 64 36) P).writeW (Ba + BitVec.ofNat 64 40) C
    M.readW (Ba + BitVec.ofNat 64 36) 32 = P ∧ M.readW (Ba + BitVec.ofNat 64 40) 32 = C ∧
      Frame [⟨Pa, 8⟩, ⟨Ba + BitVec.ofNat 64 36, 8⟩] m M ∧ blockAt M Pa = encodeBlock L R := by
  intro M
  have s36 : Mem.Sep (Ba + BitVec.ofNat 64 36) 4 (Ba + BitVec.ofNat 64 40) 4 :=
    Offset.sep Ba (by decide) (by decide) (by decide)
  refine ⟨by rw [Mem.readW_writeW_sep s36 (by decide), Mem.readW_writeW_self32],
    Mem.readW_writeW_self32 _ _ _, ?_, ?_⟩
  · have c0 : Region.Contains ⟨Pa, 8⟩ Pa (32 / 8) := Offset.contains_base Pa (d := 0) (n := 4) (k := 8)
      (by decide) (by decide) |> fun h => by rwa [BitVec.add_zero] at h
    have c4 : Region.Contains ⟨Pa, 8⟩ (Pa + BitVec.ofNat 64 4) (32 / 8) :=
      Offset.contains_base Pa (by decide) (by decide)
    have c36 : Region.Contains ⟨Ba + BitVec.ofNat 64 36, 8⟩ (Ba + BitVec.ofNat 64 36) (32 / 8) := by
      have := Offset.contains_base (Ba + BitVec.ofNat 64 36) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
      rwa [BitVec.add_zero] at this
    have c40 : Region.Contains ⟨Ba + BitVec.ofNat 64 36, 8⟩ (Ba + BitVec.ofNat 64 40) (32 / 8) := by
      have := Offset.contains_base (Ba + BitVec.ofNat 64 36) (d := 4) (n := 4) (k := 8) (by decide) (by decide)
      rwa [Offset.add_add] at this
    exact ((((Frame.refl _ m).writeW List.mem_cons_self _ c0).writeW List.mem_cons_self _ c4).writeW
      (List.mem_cons_of_mem _ List.mem_cons_self) _ c36).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ c40
  · refine blockAt_eq _ _ _ fun i hi => ?_
    have dk : ∀ o, o < 8 → Region.Disjoint ⟨Pa + BitVec.ofNat 64 o, 1⟩ ⟨Ba + BitVec.ofNat 64 36, 8⟩ :=
      fun o ho => (dj.sub_right (Offset.sub_base Pa (d := o) (n := 1) (k := 8) (by omega))).symm
    have d36 := (dk i hi).sub_right (Offset.sub (e := 36) (k := 8) (d := 36) (n := 4) Ba (by decide) (by decide))
    have d40 := (dk i hi).sub_right (Offset.sub (e := 36) (k := 8) (d := 40) (n := 4) Ba (by decide) (by decide))
    simp only [M]
    rw [writeW32_other _ d40, writeW32_other _ d36, encodeBlock_getD _ _ hi]
    by_cases h4 : i < 4
    · rw [ite_eq_left h4, writeW32_other _ (Offset.disjoint Pa (d := i) (n := 1) (e := 4) (k := 4) (by omega)
        (by omega) (by decide)), st_byte _ _ _ h4, rev_byte _ h4]
    · rw [ite_eq_right h4, show i = 4 + (i - 4) by omega, ← Offset.add_add, st_byte _ _ _ (by omega),
        rev_byte _ (by omega)]
      congr 2; omega

/-! ## The loop -/

/-- A block's encryption (`up`) or decryption. -/
def blockOut (K : Schedule) (up : Bool) (b : Block) : Block :=
  if up then encryptBlock K b else decryptBlock K b

theorem blockOut_eq (K : Schedule) (up : Bool) (b : Block) :
    blockOut K up b = encodeBlock (feistel K (ord up) (decodeWord b 0) (decodeWord b 4)).1
      (feistel K (ord up) (decodeWord b 0) (decodeWord b 4)).2 := by
  cases up <;> rfl

/-- The block `b` of the data at `D`. -/
abbrev wAt (D : Addr) (b : Nat) : Addr := D + BitVec.ofNat 64 (8 * b)

/-- What ECB may assume: the schedule readable, the `n` blocks and the
working space writable, apart, none wrapping around. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r0), 4168⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩, ⟨State.addr (s.gpr .r3), 256⟩]
  keyData : (⟨State.addr (s.gpr .r0), 4168⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩
  keyBuf : (⟨State.addr (s.gpr .r0), 4168⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 256⟩
  dataBuf : (⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 256⟩
  fitK : (s.gpr .r0).toNat + 4168 ≤ 2 ^ 32
  fitD : (s.gpr .r1).toNat + 8 * (s.gpr .r2).toNat ≤ 2 ^ 32
  fitB : (s.gpr .r3).toNat + 256 ≤ 2 ^ 32

/-- After `k` blocks from `s`. -/
structure EInv (s : State) (up : Bool) (k : Nat) (u : State) : Prop where
  le : k ≤ (s.gpr .r2).toNat
  r3 : u.gpr .r3 = s.gpr .r3
  r0 : u.gpr .r0 = s.gpr .r0
  ptr : u.mem.readW (State.addr (s.gpr .r3) + BitVec.ofNat 64 36) 32 = s.gpr .r1 + BitVec.ofNat 32 (8 * k)
  cnt : u.mem.readW (State.addr (s.gpr .r3) + BitVec.ofNat 64 40) 32 =
    BitVec.ofNat 32 ((s.gpr .r2).toNat - k)
  saved : Spill.Saved u.mem (State.addr (s.gpr .r3)) s.gpr saved
  done : ∀ b < k, blockAt u.mem (wAt (State.addr (s.gpr .r1)) b) =
    blockOut (scheduleAt s.mem (State.addr (s.gpr .r0))) up (blockAt s.mem (wAt (State.addr (s.gpr .r1)) b))
  rest : ∀ b, k ≤ b → b < (s.gpr .r2).toNat →
    blockAt u.mem (wAt (State.addr (s.gpr .r1)) b) = blockAt s.mem (wAt (State.addr (s.gpr .r1)) b)
  frame : Frame [⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩, ⟨State.addr (s.gpr .r3), 256⟩] s.mem u.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr

theorem saved_slots : Spill.Slots 0 36 saved := by decide

theorem ecb_step {s : State} (h : EcbPre s) (up : Bool) {k : Nat} (hk : k < (s.gpr .r2).toNat) {u : State}
    (I : EInv s up k u) :
    WP isa (.seq (.block loadBlock) (.seq (cipher up) (.block storeBlock))) u fun u' =>
      EInv s up (k + 1) u' ∧ u'.z = (BitVec.ofNat 32 ((s.gpr .r2).toNat - (k + 1)) == 0#32) := by
  obtain ⟨hrd, hwr, kd, kb, db, fK, fD, fB⟩ := h
  have hrw : u.rd ++ u.wr = [⟨State.addr (s.gpr .r0), 4168⟩,
      ⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩, ⟨State.addr (s.gpr .r3), 256⟩] := by
    rw [I.rd, I.wr, hrd, hwr]; rfl
  have dR : (⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩ : Region) ∈ u.wr := by
    rw [I.wr, hwr]; exact List.mem_cons_self
  have bR : (⟨State.addr (s.gpr .r3), 256⟩ : Region) ∈ u.wr := by
    rw [I.wr, hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  -- addresses
  have eB : State.addr (s.gpr .r3 + BitVec.ofNat 32 36) = State.addr (s.gpr .r3) + BitVec.ofNat 64 36 :=
    addr_add (by omega)
  have eC : State.addr (s.gpr .r3 + BitVec.ofNat 32 40) = State.addr (s.gpr .r3) + BitVec.ofNat 64 40 :=
    addr_add (by omega)
  have eP : State.addr (s.gpr .r1 + BitVec.ofNat 32 (8 * k)) = wAt (State.addr (s.gpr .r1)) k :=
    addr_add (by omega)
  have e0 : State.addr (s.gpr .r1 + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 0) =
      wAt (State.addr (s.gpr .r1)) k := by rw [BitVec.add_zero, eP]
  have e4 : State.addr (s.gpr .r1 + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 4) =
      wAt (State.addr (s.gpr .r1)) k + BitVec.ofNat 64 4 := by
    rw [ofs_add, addr_add (by omega), Offset.add_add]
  have wK : InRegions u.wr (wAt (State.addr (s.gpr .r1)) k) 8 :=
    ⟨_, dR, Offset.contains_base _ (by omega) (by omega)⟩
  have wB : InRegions u.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 36) 8 :=
    ⟨_, bR, Offset.contains_base _ (by omega) (by omega)⟩
  have subK : Region.Sub ⟨wAt (State.addr (s.gpr .r1)) k, 8⟩ ⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩ :=
    Offset.sub_base _ (by omega)
  have subB : Region.Sub ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 36, 8⟩ ⟨State.addr (s.gpr .r3), 256⟩ :=
    Offset.sub_base _ (by omega)
  have dj : Region.Disjoint ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 36, 8⟩ ⟨wAt (State.addr (s.gpr .r1)) k, 8⟩ :=
    ((db.sub_left subK).sub_right subB).symm
  -- the block in
  apply WP.seq
  refine WP.mono (WP.keep [.r1, .r2, .r12] (loadBlock_run u I.r3 eB e0 e4
    (region_in (inRegions_pre wB (by decide))) (region_in (inRegions_pre wK (by decide)))
    (region_in (inRegions_off (o := 4) (n := 4) wK (by decide))) I.ptr) (by decide))
    fun u₁ ⟨⟨l1, l2, lm⟩, lk⟩ => ?_
  -- the cipher
  have hK : scheduleAt u.mem (State.addr (s.gpr .r0)) = scheduleAt s.mem (State.addr (s.gpr .r0)) :=
    scheduleAt_eq_of_frame _ I.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact kd
      · exact kb
  have CE : CipherEnv u₁ := by
    refine ⟨by rw [lk.gpr (by decide), I.r0]; exact fK, fun o ho => ?_⟩
    rw [keep_reads lk, hrw, lk.gpr (by decide), I.r0]
    exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by omega)⟩
  apply WP.seq
  refine WP.mono (cipher_run CE up) fun u₂ ⟨c12, ck, cm⟩ => ?_
  -- the block out
  have k₂ : Keep cRegs u u₂ := (lk.trans ck).mono (by decide)
  refine WP.mono (WP.keep [.r1, .r2, .r11, .r12] (storeBlock_run u₂ (C := BitVec.ofNat 32 ((s.gpr .r2).toNat - k))
    (by rw [k₂.gpr (by decide), I.r3]) eB eC e0 e4 (by rw [k₂.2.2.1]; exact wB) (by rw [k₂.2.2.1]; exact wK) dj
    (by rw [cm, lm]; exact I.ptr) (by rw [cm, lm]; exact I.cnt)) (by decide)) fun u₃ ⟨⟨sm, sz, slr, s0⟩, sk⟩ => ?_
  obtain ⟨M36, M40, MF, MB⟩ := stored_facts u₂.mem (State.addr (s.gpr .r3)) (wAt (State.addr (s.gpr .r1)) k)
    (u₂.gpr .r1) (u₂.gpr .r2) (s.gpr .r1 + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 8)
    (BitVec.ofNat 32 ((s.gpr .r2).toNat - k) - 1#32) dj
  rw [← sm] at M36 M40 MF MB
  have m₂ : u₂.mem = u.mem := by rw [cm, lm]
  rw [m₂] at MF
  have hcnt : BitVec.ofNat 32 ((s.gpr .r2).toNat - k) - 1#32 = BitVec.ofNat 32 ((s.gpr .r2).toNat - (k + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have dOther : ∀ b, b < (s.gpr .r2).toNat → b ≠ k → ∀ r ∈ [(⟨wAt (State.addr (s.gpr .r1)) k, 8⟩ : Region),
      ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 36, 8⟩], (⟨wAt (State.addr (s.gpr .r1)) b, 8⟩ : Region).Disjoint r :=
    fun b hb hne r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact (db.sub_left (Offset.sub_base _ (by omega))).sub_right subB
  have other : ∀ b, b < (s.gpr .r2).toNat → b ≠ k →
      blockAt u₃.mem (wAt (State.addr (s.gpr .r1)) b) = blockAt u.mem (wAt (State.addr (s.gpr .r1)) b) :=
    fun b hb hne => blockAt_frame MF (dOther b hb hne)
  have u₁r0 : u₁.gpr .r0 = s.gpr .r0 := by rw [lk.gpr (by decide), I.r0]
  refine ⟨⟨by omega, slr, by rw [s0, k₂.gpr (by decide), I.r0], by rw [M36, ofs_add]; congr 2,
    by rw [M40, hcnt], ?_, fun b hb => ?_, fun b h1 h2 => ?_, ?_, ?_, ?_⟩, by rw [sz, hcnt]⟩
  · refine I.saved.frame saved_slots MF fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [BitVec.add_zero]
      exact (db.symm.sub_left (Region.sub_prefix (by decide))).sub_right subK
    · exact Offset.disjoint _ (by decide) (by omega) (by omega)
  · by_cases hbk : b = k
    · subst hbk
      rw [lm, u₁r0, l1, l2] at c12
      rw [MB, blockOut_eq, ← I.rest b (by omega) hk, ← hK, ← c12]
    · rw [other b (by omega) hbk]; exact I.done b (by omega)
  · rw [other b h2 (by omega)]; exact I.rest b (by omega) h2
  · refine I.frame.trans (MF.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, subK⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subB⟩
  · rw [sk.2.1, k₂.2.1, I.rd]
  · rw [sk.2.2.1, k₂.2.2.1, I.wr]


theorem saved_restorable : Spill.Restorable .r3 saved := by decide

theorem restore_eq : restore = saved.map (fun (p : Reg × Nat) => Instr.ldr p.1 .r3 p.2) := rfl
theorem save_eq (rest : List Instr) :
    save ++ rest = saved.map (fun p => Instr.str p.1 .r3 p.2) ++ rest := rfl

/-- Restoring our caller's registers from the working space at `r3`. -/
theorem restore_run {u : State} {g : Reg → BitVec 32}
    (fit : (u.gpr .r3).toNat + 36 ≤ 2 ^ 32)
    (hin : ∀ d, d + 4 ≤ 36 → InRegions (u.rd ++ u.wr) (State.addr (u.gpr .r3) + BitVec.ofNat 64 d) 4)
    (hsv : Spill.Saved u.mem (State.addr (u.gpr .r3)) g saved) :
    WP isa (.block restore) u fun t => (∀ r ∈ preserved, t.gpr r = g r) ∧ t.mem = u.mem := by
  rw [restore_eq]
  refine WP.mono (Spill.restore_block_ok saved_slots saved_restorable fit (fun d _ h => hin d h) hsv)
    fun t ⟨ht, _, hm, _⟩ => ⟨fun r hr => ?_, hm⟩
  have : r ∈ saved.map Prod.fst := by revert r; decide
  exact Spill.restored_reg ht this

theorem ecb_blocks (K : Schedule) (up : Bool) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, blockAt m' (wAt D b) = blockOut K up (blockAt m (wAt D b))) :
    blocksAt m' D n = Spec.Blowfish.ecb K (if up then .encrypt else .decrypt) (blocksAt m D n) := by
  simp only [blocksAt, Spec.Blowfish.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  rw [Function.comp_apply, h b (List.mem_range.mp hb)]
  cases up <;> rfl

/-- What ECB guarantees. -/
structure EcbPost (s : State) (up : Bool) (t : State) : Prop where
  regs : ∀ r ∈ preserved, t.gpr r = s.gpr r
  blocks : blocksAt t.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
    Spec.Blowfish.ecb (scheduleAt s.mem (State.addr (s.gpr .r0))) (if up then .encrypt else .decrypt)
      (blocksAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)

theorem ecb_correct {s : State} (h : EcbPre s) (up : Bool) : WP isa (Impl.Blowfish.Arm.ecb up) s (EcbPost s up) := by
  have H := h
  obtain ⟨hrd, hwr, kd, kb, db, fK, fD, fB⟩ := H
  have bR : (⟨State.addr (s.gpr .r3), 256⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have subB : Region.Sub ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 36, 8⟩ ⟨State.addr (s.gpr .r3), 256⟩ :=
    Offset.sub_base _ (by omega)
  have wB : InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 36) 8 :=
    ⟨_, bR, Offset.contains_base _ (by omega) (by omega)⟩
  unfold Impl.Blowfish.Arm.ecb
  apply WP.seq
  rw [save_eq]
  refine Spill.save_slots_ok saved_slots (by omega) (fun d _ hd =>
    ⟨_, bR, Offset.contains_base _ (by omega) (by omega)⟩) ?_
  let s₁ : State := { s with mem := Spill.saveMem s.mem (State.addr (s.gpr .r3)) s.gpr saved }
  have eB : State.addr (s.gpr .r3 + BitVec.ofNat 32 36) = State.addr (s.gpr .r3) + BitVec.ofNat 64 36 :=
    addr_add (by omega)
  have eC : State.addr (s.gpr .r3 + BitVec.ofNat 32 40) = State.addr (s.gpr .r3) + BitVec.ofNat 64 40 :=
    addr_add (by omega)
  have w36 : InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 36) 4 := inRegions_pre wB (by decide)
  have w40 : InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 40) 4 := by
    have := inRegions_off (o := 4) (n := 4) wB (by decide); rwa [Offset.add_add] at this
  have g₁ : s₁.gpr = s.gpr := rfl
  refine WP.mono (WP.keep [.lr] (Q := fun u => u.mem = ((Spill.saveMem s.mem (State.addr (s.gpr .r3)) s.gpr saved).writeW (State.addr (s.gpr .r3) + BitVec.ofNat 64 36)
      (s.gpr .r1)).writeW (State.addr (s.gpr .r3) + BitVec.ofNat 64 40) (s.gpr .r2) ∧
      u.z = (s.gpr .r2 - 0#32 == 0#32)) (by brun [g₁, eB, eC, w36, w40, ptrOff, cntOff]) (by decide))
    fun u₀ ⟨⟨um, uz⟩, uk⟩ => ?_
  -- the loop's start
  have s36 : Mem.Sep (State.addr (s.gpr .r3) + BitVec.ofNat 64 36) 4 (State.addr (s.gpr .r3) + BitVec.ofNat 64 40) 4 :=
    Offset.sep _ (by decide) (by decide) (by decide)
  have F0 : Frame [⟨State.addr (s.gpr .r3), 256⟩] s.mem u₀.mem := by
    have f₁ : Frame [⟨State.addr (s.gpr .r3), 256⟩] s.mem s₁.mem :=
      (Spill.saveMem_frame s.mem _ s.gpr (L := 36) (by decide) saved (by decide)).sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    rw [um]
    exact (f₁.writeW List.mem_cons_self _ (Offset.contains_base _ (d := 36) (n := 4) (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (d := 40) (n := 4) (by decide) (by decide))
  have I0 : EInv s up 0 u₀ := by
    refine ⟨Nat.zero_le _, by rw [uk.gpr (by decide)], by rw [uk.gpr (by decide)], ?_, ?_, ?_, fun b hb => absurd hb (Nat.not_lt_zero _),
      fun b _ hb => blockAt_frame F0 fun r hr => ?_, F0.mono fun r hr => ?_, uk.2.1, uk.2.2.1⟩
    · rw [um, Mem.readW_writeW_sep s36 (by decide), Mem.readW_writeW_self32, Nat.mul_zero]; simp
    · rw [um, Mem.readW_writeW_self32, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · have sv := Spill.saveMem_saved (State.addr (s.gpr .r3)) s.gpr s.mem saved saved_slots
      refine sv.frame saved_slots (rs := [⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 36, 8⟩]) ?_ fun r hr => ?_
      · rw [um]
        exact ((Frame.refl _ _).writeW List.mem_cons_self _
          (Offset.contains (e := 36) (k := 8) (d := 36) (n := 4) _ (by decide) (by decide) (by decide))).writeW
          List.mem_cons_self _ (Offset.contains (e := 36) (k := 8) (d := 40) (n := 4) _ (by decide) (by decide) (by decide))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact Offset.disjoint _ (by decide) (by decide) (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact (db.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact List.mem_cons_of_mem _ List.mem_cons_self
  -- the end
  have fin : ∀ u, EInv s up (s.gpr .r2).toNat u → WP isa (.block restore) u (EcbPost s up) := fun u I => by
    refine WP.mono (restore_run (u := u) (by rw [I.r3]; omega) (fun d hd => ?_) (by rw [I.r3]; exact I.saved))
      fun t ⟨tr, tm⟩ =>
      ⟨tr, ecb_blocks _ _ _ _ _ _ fun b hb => by rw [tm]; exact I.done b hb⟩
    rw [I.rd, I.wr, hrd, hwr, I.r3]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      Offset.contains_base _ (by omega) (by omega)⟩
  apply WP.seq
  refine WP.ite (s.gpr .r2 - 0#32 == 0#32) (by rw [eval_eq, uz]) (fun hz => ?_) (fun hz => ?_)
  · have hn : (s.gpr .r2).toNat = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz); simpa using this
    exact WP.block_nil (fin u₀ (by rw [hn]; exact I0))
  · have hn : 0 < (s.gpr .r2).toNat := by
      have h0 : s.gpr .r2 ≠ 0#32 := by intro e; rw [e] at hz; simp at hz
      have : (s.gpr .r2).toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq e)
      omega
    refine WP.mono (WP.loop (M := isa) (Q := EInv s up (s.gpr .r2).toNat)
      (fun (m : Nat) (u : State) => ∃ k, k < (s.gpr .r2).toNat ∧ m = (s.gpr .r2).toNat - k ∧ EInv s up k u)
      ?_ _ u₀ ⟨0, hn, rfl, I0⟩) fin
    intro m u ⟨k, hk, hm, I⟩
    refine WP.mono (ecb_step h up hk I) fun u' ⟨I', zu⟩ => ?_
    rw [eval_ne, zu]
    by_cases e : k + 1 = (s.gpr .r2).toNat
    · left
      exact ⟨by rw [e, Nat.sub_self]; rfl, e ▸ I'⟩
    · right
      have nz : BitVec.ofNat 32 ((s.gpr .r2).toNat - (k + 1)) ≠ 0#32 := by
        intro h'; have := congrArg BitVec.toNat h'; simp at this; omega
      exact ⟨by rw [beq_eq_false_iff_ne.mpr nz]; rfl, _, by omega, k + 1, by omega, rfl, I'⟩

end VG.Proof.Blowfish.Arm
