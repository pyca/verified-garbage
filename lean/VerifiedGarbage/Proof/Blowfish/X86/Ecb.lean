module

public import VerifiedGarbage.Proof.Blowfish.X86.Cipher
import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Blowfish.X86.Run
import VerifiedGarbage.Proof.Blowfish.Schedule

/-!
# Blowfish on x86 (32-bit): ECB

`ecb_correct`: every block becomes its encryption or decryption, one at a
time; our caller's registers are saved in the working space and restored.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86

open VG VG.X86 VG.Impl.Blowfish.X86 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-! ## Blocks in and out of the halves -/

theorem bswap_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (bswap v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  unfold bswap
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  repeat' split
  all_goals first | omega_arith | (rw [decide_eq_true (by omega_arith), Bool.true_and]; congr 1; omega_arith)

theorem bswap_byte (x : BitVec 32) {b : Nat} (hb : b < 4) :
    (bswap x).extractLsb' (8 * b) 8 = x.extractLsb' (8 * (3 - b)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  exact bswap_bit x hb hi

/-- The big-endian word at offset `o` of the block at `q`. -/
theorem bswap_load (m : Mem) (q : Addr) {o : Nat} (ho : o ≤ 4) :
    bswap (m.readW (q + BitVec.ofNat 64 o) 32) = decodeWord (blockAt m q) o := by
  refine word_ext fun b hb => ?_
  rw [bswap_byte _ hb, decodeWord_byte _ _ hb, blockAt_getD _ _ (by omega_arith),
    ← Mem.readW_byte m _ (by omega_arith), Offset.add_add]

/-- The block at the data pointer (in the working space) into the halves. -/
theorem loadBlock_run (u : State) {B P : BitVec 32} {Pa : Addr} (hb : u.gpr .ebp = B)
    (bfit : B.toNat + 40 ≤ 2 ^ 32) (w16 : InRegions u.wr (slot B 16) 4) (w20 : InRegions u.wr (slot B 20) 4)
    (r32 : InRegions (u.rd ++ u.wr) (slot B 32) 4) (hP : u.mem.readW (slot B 32) 32 = P)
    (e0 : addr P 0 = Pa) (e4 : addr P 4 = Pa + BitVec.ofNat 64 4)
    (r0 : InRegions (u.rd ++ u.wr) Pa 4) (r4 : InRegions (u.rd ++ u.wr) (Pa + BitVec.ofNat 64 4) 4)
    (sep : Mem.Sep (Pa + BitVec.ofNat 64 4) (32 / 8) (slot B 16) (32 / 8)) :
    WP isa (.block loadBlock) u fun t =>
      t.mem = (u.mem.writeW (slot B 16) (decodeWord (blockAt u.mem Pa) 0)).writeW (slot B 20)
        (decodeWord (blockAt u.mem Pa) 4) := by
  have l0 := bswap_load u.mem Pa (o := 0) (by decide)
  have l4 := bswap_load u.mem Pa (o := 4) (by decide)
  rw [BitVec.add_zero] at l0
  have e : ∀ v : BitVec 32, (u.mem.writeW (slot B 16) v).readW (Pa + BitVec.ofNat 64 4) 32 =
      u.mem.readW (Pa + BitVec.ofNat 64 4) 32 := fun v => Mem.readW_writeW_sep sep (by decide)
  unfold loadBlock
  brun [hb, addr_slot bfit, w16, w20, r32, hP, e0, e4, r0, r4, e, l0, l4]

/-- The halves to the block at the data pointer, the next block's pointer,
and the counter less one. -/
theorem storeBlock_run (u : State) {B P C : BitVec 32} {Pa : Addr} (hb : u.gpr .ebp = B)
    (bfit : B.toNat + 40 ≤ 2 ^ 32) (r16 : InRegions (u.rd ++ u.wr) (slot B 16) 4)
    (r20 : InRegions (u.rd ++ u.wr) (slot B 20) 4) (w32 : InRegions u.wr (slot B 32) 4)
    (w36 : InRegions u.wr (slot B 36) 4) (hP : u.mem.readW (slot B 32) 32 = P)
    (hC : u.mem.readW (slot B 36) 32 = C) (e0 : addr P 0 = Pa) (e4 : addr P 4 = Pa + BitVec.ofNat 64 4)
    (w0 : InRegions u.wr Pa 4) (w4 : InRegions u.wr (Pa + BitVec.ofNat 64 4) 4)
    (sep : Mem.Sep (slot B 20) (32 / 8) Pa (32 / 8)) :
    WP isa (.block storeBlock) u fun t =>
      t.mem = (((u.mem.writeW Pa (bswap (u.mem.readW (slot B 16) 32))).writeW (Pa + BitVec.ofNat 64 4)
          (bswap (u.mem.readW (slot B 20) 32))).writeW (slot B 32) (P + BitVec.ofNat 32 8)).writeW (slot B 36)
          (C - BitVec.ofNat 32 1) ∧
        t.zf = some (C - BitVec.ofNat 32 1 == 0) := by
  have r32 := region_in (rs := u.rd) w32
  have r36 := region_in (rs := u.rd) w36
  have e : ∀ v : BitVec 32, (u.mem.writeW Pa v).readW (slot B 20) 32 = u.mem.readW (slot B 20) 32 :=
    fun v => Mem.readW_writeW_sep sep (by decide)
  unfold storeBlock
  brun [hb, addr_slot bfit, r16, r20, r32, r36, w32, w36, hP, hC, e0, e4, w0, w4, e]

theorem st_byte (m : Mem) (a : Addr) (v : BitVec 32) {t : Nat} (ht : t < 4) :
    m.writeW a v (a + BitVec.ofNat 64 t) = v.extractLsb' (8 * t) 8 := by
  rw [Mem.readW_byte (m.writeW a v) a ht, Mem.readW_writeW_self32]

theorem writeW32_other {m : Mem} {a x : Addr} (v : BitVec 32) (h : Region.Disjoint ⟨x, 1⟩ ⟨a, 4⟩) :
    m.writeW a v x = m x :=
  Mem.write_apply fun h' => h x (Region.contains_self _ _) ((Region.contains_self a 4).byte h')

/-- What the stores leave: the block's bytes, the pointer and the counter. -/
theorem stored_facts (m : Mem) (B : BitVec 32) (Pa : Addr) (L R P C : BitVec 32)
    (dj : Region.Disjoint ⟨slot B 32, 8⟩ ⟨Pa, 8⟩) :
    let M := (((m.writeW Pa (bswap L)).writeW (Pa + BitVec.ofNat 64 4) (bswap R)).writeW (slot B 32) P).writeW
      (slot B 36) C
    M.readW (slot B 32) 32 = P ∧ M.readW (slot B 36) 32 = C ∧
      Frame [⟨Pa, 8⟩, ⟨slot B 32, 8⟩] m M ∧ blockAt M Pa = encodeBlock L R := by
  intro M
  refine ⟨by rw [Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32],
    Mem.readW_writeW_self32 _ _ _, ?_, ?_⟩
  · have c0 : Region.Contains ⟨Pa, 8⟩ Pa (32 / 8) := Offset.contains_base Pa (d := 0) (n := 4) (k := 8)
      (by decide) (by decide) |> fun h => by rwa [BitVec.add_zero] at h
    have c4 : Region.Contains ⟨Pa, 8⟩ (Pa + BitVec.ofNat 64 4) (32 / 8) :=
      Offset.contains_base Pa (by decide) (by decide)
    have c32 : Region.Contains ⟨slot B 32, 8⟩ (slot B 32) (32 / 8) :=
      Offset.contains (e := 32) (k := 8) (d := 32) (n := 4) _ (by decide) (by decide) (by decide)
    have c36 : Region.Contains ⟨slot B 32, 8⟩ (slot B 36) (32 / 8) :=
      Offset.contains (e := 32) (k := 8) (d := 36) (n := 4) _ (by decide) (by decide) (by decide)
    exact ((((Frame.refl _ m).writeW List.mem_cons_self _ c0).writeW List.mem_cons_self _ c4).writeW
      (List.mem_cons_of_mem _ List.mem_cons_self) _ c32).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ c36
  · refine blockAt_eq _ _ _ fun i hi => ?_
    have dk : ∀ o, o < 8 → Region.Disjoint ⟨Pa + BitVec.ofNat 64 o, 1⟩ ⟨slot B 32, 8⟩ :=
      fun o ho => (dj.sub_right (Offset.sub_base Pa (d := o) (n := 1) (k := 8) (by omega_arith))).symm
    have d32 := (dk i hi).sub_right (Offset.sub (e := 32) (k := 8) (d := 32) (n := 4) (B.setWidth 64)
      (by decide) (by decide))
    have d36 := (dk i hi).sub_right (Offset.sub (e := 32) (k := 8) (d := 36) (n := 4) (B.setWidth 64)
      (by decide) (by decide))
    simp only [M]
    rw [writeW32_other _ d36, writeW32_other _ d32, encodeBlock_getD _ _ hi]
    by_cases h4 : i < 4
    · rw [ite_eq_left h4, writeW32_other _ (Offset.disjoint Pa (d := i) (n := 1) (e := 4) (k := 4) (by omega_arith)
        (by omega_arith) (by decide)), st_byte _ _ _ h4, bswap_byte _ h4]
    · rw [ite_eq_right h4, show i = 4 + (i - 4) by omega_arith, ← Offset.add_add, st_byte _ _ _ (by omega_arith),
        bswap_byte _ (by omega_arith)]
      congr 2; omega_arith

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

/-- The schedule, the data, the working space and the arguments of `s`. -/
abbrev schR (s : State) : Region := ⟨(arg s 0).setWidth 64, 4168⟩
abbrev dataR (s : State) : Region := ⟨(arg s 1).setWidth 64, 8 * (arg s 2).toNat⟩
abbrev scrR (s : State) : Region := ⟨(arg s 3).setWidth 64, 256⟩
abbrev argR (s : State) : Region := ⟨argAddr s 0, 16⟩
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩

/-- What ECB may assume: the schedule and the arguments readable, the `n`
blocks and the working space writable, apart, none wrapping around. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [schR s, argR s]
  wr : s.wr = [dataR s, scrR s]
  kd : (schR s).Disjoint (dataR s)
  kb : (schR s).Disjoint (scrR s)
  db : (dataR s).Disjoint (scrR s)
  ad : (argR s).Disjoint (dataR s)
  ab : (argR s).Disjoint (scrR s)
  retD : (retR s).Disjoint (dataR s)
  retB : (retR s).Disjoint (scrR s)
  fK : (arg s 0).toNat + 4168 ≤ 2 ^ 32
  fD : (arg s 1).toNat + 8 * (arg s 2).toNat ≤ 2 ^ 32
  fB : (arg s 3).toNat + 256 ≤ 2 ^ 32
  fsp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32

/-- Our caller's `ebx`, `esi`, `edi` and `ebp` (of `s₀`) in the working space at `B`. -/
def Saved (m : Mem) (B : BitVec 32) (s₀ : State) : Prop :=
  m.readW (slot B 0) 32 = s₀.gpr .ebx ∧ m.readW (slot B 4) 32 = s₀.gpr .esi ∧
    m.readW (slot B 8) 32 = s₀.gpr .edi ∧ m.readW (slot B 12) 32 = s₀.gpr .ebp

/-- The saved registers survive writes outside their 16 bytes. -/
theorem Saved.frame {m m' : Mem} {B : BitVec 32} {s₀ : State} {rs : List Region} (h : Saved m B s₀)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨B.setWidth 64, 16⟩ r) : Saved m' B s₀ := by
  have e (d : Nat) (hd' : d + 4 ≤ 16) : m'.readW (slot B d) 32 = m.readW (slot B d) 32 :=
    hf.readW (Offset.contains_base _ hd' (by omega_arith)) hd (by decide)
  obtain ⟨h0, h4, h8, h12⟩ := h
  exact ⟨(e 0 (by decide)).trans h0, (e 4 (by decide)).trans h4, (e 8 (by decide)).trans h8,
    (e 12 (by decide)).trans h12⟩

/-- After `k` blocks from `s`. -/
structure EInv (s : State) (up : Bool) (k : Nat) (u : State) : Prop where
  le : k ≤ (arg s 2).toNat
  esp : u.gpr .esp = s.gpr .esp
  ebp : u.gpr .ebp = arg s 3
  ptr : u.mem.readW (slot (arg s 3) 32) 32 = arg s 1 + BitVec.ofNat 32 (8 * k)
  cnt : u.mem.readW (slot (arg s 3) 36) 32 = BitVec.ofNat 32 ((arg s 2).toNat - k)
  saved : Saved u.mem (arg s 3) s
  done : ∀ b < k, blockAt u.mem (wAt ((arg s 1).setWidth 64) b) =
    blockOut (scheduleAt s.mem ((arg s 0).setWidth 64)) up (blockAt s.mem (wAt ((arg s 1).setWidth 64) b))
  rest : ∀ b, k ≤ b → b < (arg s 2).toNat →
    blockAt u.mem (wAt ((arg s 1).setWidth 64) b) = blockAt s.mem (wAt ((arg s 1).setWidth 64) b)
  frame : Frame [dataR s, scrR s] s.mem u.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 8⟩) hd (by show 8 ≤ 2 ^ 64; decide) hi

theorem contains_pre (a : Addr) {n k : Nat} (h : n ≤ k) : Region.Contains ⟨a, k⟩ a n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith

theorem mem_two {α : Type} {a b x : α} (h : x ∈ [a, b]) : x = a ∨ x = b := by
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using h

theorem ecb_step {s : State} (h : EcbPre s) (up : Bool) {k : Nat} (hk : k < (arg s 2).toNat) {u : State}
    (I : EInv s up k u) :
    WP isa (.seq (.block loadBlock) (.seq (cipher 4 up) (.block storeBlock))) u fun u' =>
      EInv s up (k + 1) u' ∧ u'.zf = some (BitVec.ofNat 32 ((arg s 2).toNat - (k + 1)) == 0) := by
  obtain ⟨hrd, hwr, kd, kb, db, ad, ab, retD, retB, fK, fD, fB, fsp⟩ := h
  let S := arg s 0
  let D := arg s 1
  let B := arg s 3
  have eD : D.toNat = (arg s 1).toNat := rfl
  have eB : B.toNat = (arg s 3).toNat := rfl
  have bfit : B.toNat + 40 ≤ 2 ^ 32 := by omega_arith
  have hrw : u.rd ++ u.wr = [schR s, argR s, dataR s, scrR s] := by rw [I.rd, I.wr, hrd, hwr]; rfl
  have dR : dataR s ∈ u.wr := by rw [I.wr, hwr]; exact List.mem_cons_self
  have bR : scrR s ∈ u.wr := by rw [I.wr, hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  let Pa := wAt (D.setWidth 64) k
  have eP : addr (D + BitVec.ofNat 32 (8 * k)) 0 = Pa := by
    rw [addr_of_fit (by omega_arith), BitVec.add_zero, ← addr, addr_of_fit (by omega_arith)]
  have e4 : addr (D + BitVec.ofNat 32 (8 * k)) 4 = Pa + BitVec.ofNat 64 4 := by
    unfold addr
    rw [ofs_add, ← addr, addr_of_fit (by omega_arith), Offset.add_add]
  have wK : InRegions u.wr Pa 8 := ⟨_, dR, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have wS : ∀ d, d + 4 ≤ 40 → InRegions u.wr (slot B d) 4 := fun d hd =>
    ⟨_, bR, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have subK : Region.Sub ⟨Pa, 8⟩ (dataR s) := Offset.sub_base _ (by omega_arith)
  have subW : Region.Sub ⟨slot B 16, 24⟩ (scrR s) := Offset.sub_base _ (by omega_arith)
  have djK : Region.Disjoint ⟨slot B 16, 24⟩ ⟨Pa, 8⟩ := ((db.sub_left subK).sub_right subW).symm
  have sep16 : ∀ d, 16 ≤ d → d + 4 ≤ 40 → ∀ o, o ≤ 4 →
      Mem.Sep (slot B d) (32 / 8) (Pa + BitVec.ofNat 64 o) (32 / 8) := fun d h1 h2 o ho =>
    djK.sep (Offset.contains _ h1 (by omega_arith) (by omega_arith)) (Offset.contains_base _ (by omega_arith) (by omega_arith))
  -- the block in
  apply WP.seq
  refine WP.mono (WP.keep [.eax, .ebx] (loadBlock_run u (B := B) I.ebp bfit (wS 16 (by decide)) (wS 20 (by decide))
    (region_in (wS 32 (by decide))) I.ptr eP e4 (region_in (inRegions_pre wK (by decide)))
    (region_in (inRegions_off (o := 4) (n := 4) wK (by decide)))
    (sep_symm (sep16 16 (by decide) (by decide) 4 (by decide)))) (by decide))
    fun u₁ ⟨lm, lk⟩ => ?_
  have F1 : Frame (cRegion B) u.mem u₁.mem := by
    rw [lm]; exact frame_slot (frame_slot (Frame.refl _ _) (by decide) (by decide) _) (by decide) (by decide) _
  -- what stays: the arguments, the schedule, the data
  have argOk : ∀ {m : Mem}, Frame [dataR s, scrR s] s.mem m → m.readW (argAddr s 0) 32 = S := fun hf =>
    hf.readW (contains_pre _ (by decide)) (fun r hr => (mem_two hr).elim (· ▸ ad) (· ▸ ab)) (by decide)
  have schOk : ∀ {m : Mem}, Frame [dataR s, scrR s] s.mem m →
      scheduleAt m (S.setWidth 64) = scheduleAt s.mem (S.setWidth 64) := fun hf =>
    scheduleAt_eq_of_frame _ hf fun r hr => (mem_two hr).elim (· ▸ kd) (· ▸ kb)
  have wide : ∀ {m m' : Mem}, Frame (cRegion B) m m' → Frame [dataR s, scrR s] m m' := fun hf =>
    hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub_base _ (by omega_arith)⟩
  have hF1 : Frame [dataR s, scrR s] s.mem u₁.mem := I.frame.trans (wide F1)
  -- the cipher
  have CE : CipherEnv 4 S B u₁ := by
    have e1 : u₁.gpr .esp = s.gpr .esp := (lk.gpr (by decide)).trans I.esp
    refine ⟨(lk.gpr (by decide)).trans I.ebp, bfit, ?_, ?_, ?_, fK, fun o ho => ?_, ?_, ?_⟩
    · rw [lk.2.2]; exact inRegions_pre (N := 256) ⟨_, bR, Region.contains_self _ _⟩ (by decide)
    · rw [keep_reads lk, hrw, e1]
      exact ⟨argR s, List.mem_cons_of_mem _ List.mem_cons_self, contains_pre _ (by decide)⟩
    · rw [e1]; exact argOk hF1
    · rw [keep_reads lk, hrw]
      exact ⟨schR s, List.mem_cons_self, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · exact (kb.symm.sub_left (Region.sub_prefix (by decide)))
    · rw [e1]; exact (ab.symm.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
  apply WP.seq
  refine WP.mono (cipher_run CE up) fun u₂ ⟨c12, ck, cf⟩ => ?_
  -- the block out
  have k₂ : Keep lookRegs u u₂ := (lk.trans ck).mono (by decide)
  have F2 : Frame (cRegion B) u.mem u₂.mem := F1.trans cf
  have past : ∀ d, 32 ≤ d → d + 4 ≤ 40 → u₂.mem.readW (slot B d) 32 = u.mem.readW (slot B d) 32 :=
    fun d h1 h2 => F2.readW (r := ⟨slot B d, 4⟩) (contains_pre _ (by decide)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint (B.setWidth 64) (d := d) (n := 4) (e := 16) (k := 16) (by omega_arith) (by omega_arith)
        (by omega_arith)) (by decide)
  have w₂ : ∀ d, d + 4 ≤ 40 → InRegions u₂.wr (slot B d) 4 := fun d hd => by rw [k₂.2.2]; exact wS d hd
  refine WP.mono (WP.keep [.eax, .ebx, .edx] (storeBlock_run u₂ (C := BitVec.ofNat 32 ((arg s 2).toNat - k))
    ((k₂.gpr (by decide)).trans I.ebp) bfit (region_in (w₂ 16 (by decide))) (region_in (w₂ 20 (by decide)))
    (w₂ 32 (by decide)) (w₂ 36 (by decide)) (by rw [past 32 (by decide) (by decide)]; exact I.ptr)
    (by rw [past 36 (by decide) (by decide)]; exact I.cnt) eP e4 (by rw [k₂.2.2]; exact inRegions_pre wK (by decide))
    (by rw [k₂.2.2]; exact inRegions_off (o := 4) (n := 4) wK (by decide))
    (sep16 20 (by decide) (by decide) 0 (by decide) |> fun h => by rwa [BitVec.add_zero] at h)) (by
      decide))
    fun u₃ ⟨⟨sm, sz⟩, sk⟩ => ?_
  have dj : Region.Disjoint ⟨slot B 32, 8⟩ ⟨Pa, 8⟩ := djK.sub_left (Offset.sub _ (by decide) (by decide))
  obtain ⟨M32, M36, MF, MB⟩ := stored_facts u₂.mem B Pa (u₂.mem.readW (slot B 16) 32)
    (u₂.mem.readW (slot B 20) 32) (D + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 8)
    (BitVec.ofNat 32 ((arg s 2).toNat - k) - BitVec.ofNat 32 1) dj
  rw [← sm] at M32 M36 MF MB
  have hcnt : BitVec.ofNat 32 ((arg s 2).toNat - k) - BitVec.ofNat 32 1 =
      BitVec.ofNat 32 ((arg s 2).toNat - (k + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_arith
  -- the step's writes: the block and the working space's bytes 16–39
  have FS : Frame [⟨Pa, 8⟩, ⟨slot B 16, 24⟩] u.mem u₃.mem := by
    refine (F2.sub fun r hr => ?_).trans (MF.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
    · rcases mem_two hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
  have dOther : ∀ b, b < (arg s 2).toNat → b ≠ k → ∀ r ∈ [(⟨Pa, 8⟩ : Region), ⟨slot B 16, 24⟩],
      (⟨wAt (D.setWidth 64) b, 8⟩ : Region).Disjoint r := fun b hb hne r hr => by
    rcases mem_two hr with rfl | rfl
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · exact (db.sub_left (Offset.sub_base _ (by omega_arith))).sub_right subW
  have other : ∀ b, b < (arg s 2).toNat → b ≠ k →
      blockAt u₃.mem (wAt (D.setWidth 64) b) = blockAt u.mem (wAt (D.setWidth 64) b) :=
    fun b hb hne => blockAt_frame FS (dOther b hb hne)
  have k₃ : Keep [.eax, .ebx, .ecx, .edx, .esi, .edi] u u₃ := (k₂.trans sk).mono (by decide)
  refine ⟨⟨by omega_arith, (k₃.gpr (by decide)).trans I.esp, (k₃.gpr (by decide)).trans I.ebp,
    by rw [M32, ofs_add]; congr 2, by rw [M36, hcnt], ?_, fun b hb => ?_, fun b h1 h2 => ?_, ?_, ?_, ?_⟩,
    by rw [sz, hcnt]⟩
  · refine I.saved.frame FS fun r hr => ?_
    rcases mem_two hr with rfl | rfl
    · exact (db.symm.sub_left (Region.sub_prefix (by decide))).sub_right subK
    · exact Offset.base_disjoint _ (by decide) (by omega_arith)
  · by_cases hbk : b = k
    · subst hbk
      have e16 : u₁.mem.readW (slot B 16) 32 = decodeWord (blockAt u.mem Pa) 0 := by
        rw [lm, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
          Mem.readW_writeW_self32]
      have e20 : u₁.mem.readW (slot B 20) 32 = decodeWord (blockAt u.mem Pa) 4 := by
        rw [lm, Mem.readW_writeW_self32]
      rw [e16, e20, schOk hF1] at c12
      rw [MB, blockOut_eq, ← I.rest b (by omega_arith) hk, ← c12]
    · rw [other b (by omega_arith) hbk]; exact I.done b (by omega_arith)
  · rw [other b h2 (by omega_arith)]; exact I.rest b (by omega_arith) h2
  · refine I.frame.trans (FS.sub fun r hr => ?_)
    rcases mem_two hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, subK⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subW⟩
  · rw [k₃.2.1, I.rd]
  · rw [k₃.2.2, I.wr]

/-- The memory once `save` has stored `b`, `si`, `di` and `bp` at `B`. -/
def savedMem (m : Mem) (B : BitVec 32) (b si di bp : BitVec 32) : Mem :=
  (((m.writeW (slot B 0) b).writeW (slot B 4) si).writeW (slot B 8) di).writeW (slot B 12) bp

theorem savedMem_frame (m : Mem) (B : BitVec 32) (b si di bp : BitVec 32) :
    Frame [⟨B.setWidth 64, 16⟩] m (savedMem m B b si di bp) := by
  unfold savedMem
  refine Frame.writeW ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine Frame.writeW ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine Frame.writeW ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))

theorem saved_savedMem (m : Mem) (B : BitVec 32) (s₀ : State) :
    Saved (savedMem m B (s₀.gpr .ebx) (s₀.gpr .esi) (s₀.gpr .edi) (s₀.gpr .ebp)) B s₀ := by
  unfold savedMem Saved
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Mem.readW_writeW_sep (slot_sep B (d := 0) (e := 12) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (slot_sep B (d := 0) (e := 8) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (slot_sep B (d := 0) (e := 4) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (slot_sep B (d := 4) (e := 12) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (slot_sep B (d := 4) (e := 8) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (slot_sep B (d := 8) (e := 12) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

theorem ecb_start {s : State} (h : EcbPre s) :
    WP isa (.block (save ++ ([.mov .ecx (.mem (at_ .esp 8)), .store (at_ .ebp ptrOff) .ecx,
        .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp cntOff) .ecx, .alu .test .ecx (.reg .ecx)] : List Instr)))
      s fun u =>
      u.mem = ((savedMem s.mem (arg s 3) (s.gpr .ebx) (s.gpr .esi) (s.gpr .edi) (s.gpr .ebp)).writeW
        (slot (arg s 3) 32) (arg s 1)).writeW (slot (arg s 3) 36) (arg s 2) ∧
      u.gpr .ebp = arg s 3 ∧ u.zf = some (arg s 2 &&& arg s 2 == 0) := by
  obtain ⟨hrd, hwr, kd, kb, db, ad, ab, retD, retB, fK, fD, fB, fsp⟩ := h
  have bfit : (arg s 3).toNat + 40 ≤ 2 ^ 32 := by omega_arith
  have bR : scrR s ∈ s.wr := by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have wS : ∀ d, d + 4 ≤ 40 → InRegions s.wr (slot (arg s 3) d) 4 := fun d hd =>
    ⟨_, bR, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have rA : ∀ i, i < 4 → InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 := fun i hi => by
    rw [hrd]
    refine ⟨argR s, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    show Region.Contains ⟨addr (s.gpr .esp) 4, 16⟩ (addr (s.gpr .esp) (4 + 4 * i)) 4
    rw [addr_of_fit (by omega_arith), addr_of_fit (by omega_arith), ← Offset.add_add]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  have argF : ∀ {m : Mem}, Frame [scrR s] s.mem m → ∀ i, i < 4 →
      m.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = arg s i := fun hf i hi => by
    refine hf.readW (r := argR s) ?_ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ab) (by decide)
    show Region.Contains ⟨addr (s.gpr .esp) 4, 16⟩ (addr (s.gpr .esp) (4 + 4 * i)) 4
    rw [addr_of_fit (by omega_arith), addr_of_fit (by omega_arith), ← Offset.add_add]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  have a3 : s.mem.readW (addr (s.gpr .esp) 16) 32 = arg s 3 := rfl
  have r16 := rA 3 (by decide)
  have r8 := rA 1 (by decide)
  have r12 := rA 2 (by decide)
  have fM := fun bx si di bp => (savedMem_frame s.mem (arg s 3) bx si di bp).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  have m8 := fun bx si di bp => argF (fM bx si di bp) 1 (by decide)
  have m12 := fun bx si di bp (v : BitVec 32) => argF (m := (savedMem s.mem (arg s 3) bx si di bp).writeW (slot (arg s 3) 32) v)
    ((fM bx si di bp).writeW (List.mem_singleton_self _) _
      (Offset.contains_base (d := 32) (n := 4) (k := 256) _ (by decide) (by decide))) 2
    (by decide)
  simp only [savedMem] at m8 m12
  simp only [Nat.mul_one, Nat.reduceAdd, Nat.reduceMul] at r8 r12 r16 m8 m12
  unfold save
  brun [addr_slot bfit, a3, r16, r8, r12, wS 0 (by decide), wS 4 (by decide), wS 8 (by decide),
    wS 12 (by decide), wS 32 (by decide), wS 36 (by decide), m8, m12, savedMem]

/-- Restoring our caller's registers from the working space at `ebp`. -/
theorem restore_run (u s₀ : State) {B : BitVec 32} (hb : u.gpr .ebp = B) (bfit : B.toNat + 40 ≤ 2 ^ 32)
    (hr : ∀ d, d + 4 ≤ 16 → InRegions (u.rd ++ u.wr) (slot B d) 4) (hs : Saved u.mem B s₀) :
    WP isa (.block restore) u fun t =>
      t.gpr .ebx = s₀.gpr .ebx ∧ t.gpr .esi = s₀.gpr .esi ∧ t.gpr .edi = s₀.gpr .edi ∧
        t.gpr .ebp = s₀.gpr .ebp ∧ t.mem = u.mem := by
  obtain ⟨h0, h4, h8, h12⟩ := hs
  unfold restore
  brun [hb, addr_slot bfit, hr 0 (by decide), hr 4 (by decide), hr 8 (by decide), hr 12 (by decide),
    h0, h4, h8, h12]

theorem ecb_blocks (K : Schedule) (up : Bool) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, blockAt m' (wAt D b) = blockOut K up (blockAt m (wAt D b))) :
    blocksAt m' D n = Spec.Blowfish.ecb K (if up then .encrypt else .decrypt) (blocksAt m D n) := by
  simp only [blocksAt, Spec.Blowfish.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  rw [Function.comp_apply, h b (List.mem_range.mp hb)]
  cases up <;> rfl

/-- What ECB guarantees. -/
def EcbPost (s : State) (up : Bool) (t : State) : Prop :=
  abiPreserved s t ∧
    blocksAt t.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      Spec.Blowfish.ecb (scheduleAt s.mem ((arg s 0).setWidth 64)) (if up then .encrypt else .decrypt)
        (blocksAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)

theorem ecb_correct {s : State} (h : EcbPre s) (up : Bool) :
    WP isa (Impl.Blowfish.X86.ecb up) s (EcbPost s up) := by
  have H := h
  obtain ⟨hrd, hwr, kd, kb, db, ad, ab, retD, retB, fK, fD, fB, fsp⟩ := H
  let B := arg s 3
  have eB : B.toNat = (arg s 3).toNat := rfl
  have bfit : B.toNat + 40 ≤ 2 ^ 32 := by omega_arith
  unfold Impl.Blowfish.X86.ecb
  apply WP.seq
  refine WP.mono (WP.keep [.eax, .ecx, .ebp] (ecb_start h) (by decide))
    fun u₀ ⟨⟨um, ubp, uz⟩, uk⟩ => ?_
  have F0 : Frame [scrR s] s.mem u₀.mem := by
    rw [um]
    refine ((savedMem_frame s.mem B _ _ _ _).sub fun r hr => ?_).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (d := 32) (n := 4) (by decide) (by decide)) |>.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (d := 36) (n := 4) (by decide) (by decide))
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  have I0 : EInv s up 0 u₀ := by
    refine ⟨Nat.zero_le _, uk.gpr (by decide), ubp, ?_, ?_, ?_, fun b hb => absurd hb (Nat.not_lt_zero _),
      fun b _ hb => blockAt_frame F0 fun r hr => ?_, F0.mono fun r hr => ?_, uk.2.1, uk.2.2⟩
    · rw [um, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self32, Nat.mul_zero]; simp
    · rw [um, Mem.readW_writeW_self32, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · refine (saved_savedMem s.mem B s).frame (rs := [⟨slot B 32, 8⟩]) ?_ fun r hr => ?_
      · rw [um]
        exact ((Frame.refl _ _).writeW List.mem_cons_self _
          (Offset.contains (e := 32) (k := 8) (d := 32) (n := 4) _ (by decide) (by decide) (by decide))).writeW
          List.mem_cons_self _ (Offset.contains (e := 32) (k := 8) (d := 36) (n := 4) _ (by decide) (by decide)
            (by decide))
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by decide) (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      exact db.sub_left (Offset.sub_base _ (by omega_arith))
    · simp only [List.mem_singleton] at hr; subst hr
      exact List.mem_cons_of_mem _ List.mem_cons_self
  -- the end
  have fin : ∀ u, EInv s up (arg s 2).toNat u → WP isa (.block restore) u (EcbPost s up) := fun u I => by
    have hr : ∀ d, d + 4 ≤ 16 → InRegions (u.rd ++ u.wr) (slot B d) 4 := fun d hd => by
      rw [I.rd, I.wr, hrd, hwr]
      exact ⟨scrR s, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    refine WP.mono (WP.keep [.ebx, .esi, .edi, .ebp] (restore_run u s I.ebp bfit hr I.saved) (by
        decide))
      fun t ⟨⟨tb, ts, td, tp, tm⟩, tk⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ecb_blocks _ _ _ _ _ _ fun b hb => by
        rw [tm]; exact I.done b hb⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [tb, ts, td, tp, (tk.gpr (by decide)).trans I.esp]
    · rw [tm]
      refine I.frame.readW (r := retR s) (contains_pre _ (by decide)) (fun r hr => ?_) (by decide)
      rcases mem_two hr with rfl | rfl
      exacts [retD, retB]
  apply WP.seq
  rw [BitVec.and_self] at uz
  refine WP.ite (arg s 2 == 0) (by rw [eval_e, uz]) (fun hz => ?_) (fun hz => ?_)
  · have hn : (arg s 2).toNat = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz); simpa using this
    exact WP.block_nil (fin u₀ (by rw [hn]; exact I0))
  · have hn : 0 < (arg s 2).toNat := by
      have h0 : arg s 2 ≠ 0 := by intro e; rw [e] at hz; simp at hz
      have : (arg s 2).toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq e)
      omega_arith
    refine WP.mono (WP.loop (M := isa) (Q := EInv s up (arg s 2).toNat)
      (fun (m : Nat) (u : State) => ∃ k, k < (arg s 2).toNat ∧ m = (arg s 2).toNat - k ∧ EInv s up k u)
      ?_ _ u₀ ⟨0, hn, rfl, I0⟩) fin
    intro m u ⟨k, hk, hm, I⟩
    refine WP.mono (ecb_step h up hk I) fun u' ⟨I', zu⟩ => ?_
    rw [eval_ne, zu]
    by_cases e : k + 1 = (arg s 2).toNat
    · left
      exact ⟨by rw [e, Nat.sub_self]; rfl, e ▸ I'⟩
    · right
      have nz : BitVec.ofNat 32 ((arg s 2).toNat - (k + 1)) ≠ 0 := by
        intro h'; have := congrArg BitVec.toNat h'; simp at this; omega_arith
      exact ⟨by rw [beq_eq_false_iff_ne.mpr nz]; rfl, _, by omega_arith, k + 1, by omega_arith, rfl, I'⟩

end VG.Proof.Blowfish.X86
