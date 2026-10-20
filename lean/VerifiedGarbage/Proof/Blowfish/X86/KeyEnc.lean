module

import VerifiedGarbage.Proof.Rc4.Scan32
public import VerifiedGarbage.Proof.Blowfish.KeyTable
public import VerifiedGarbage.Proof.Blowfish.X86.Ecb
import VerifiedGarbage.Proof.Blowfish.X86.Run

/-!
# Blowfish on x86 (32-bit): key expansion's 521 encryptions

Each encryption runs the block function under the schedule as written so
far, and its output replaces the next two entries: the P-array's, as words
(`encryptP_run`), then the S-boxes', a byte per plane (`encryptS_run`). The
pointer to the next entries and the encryptions left are in the working
space, at `ebp + 32` and `ebp + 36`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86

open VG VG.X86 VG.Impl.Blowfish VG.Impl.Blowfish.X86 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-- What the encryptions need of the state they start in: the schedule at
`K` (its address the third argument) and the working space at `B`, writable,
apart from each other and from the argument. -/
structure EncEnv (K B : BitVec 32) (s₀ : State) : Prop where
  fitK : K.toNat + 4168 ≤ 2 ^ 32
  fitB : B.toNat + 64 ≤ 2 ^ 32
  wrK : InRegions s₀.wr (K.setWidth 64) 4168
  wrB : InRegions s₀.wr (B.setWidth 64) 64
  sep : Region.Disjoint ⟨K.setWidth 64, 4168⟩ ⟨B.setWidth 64, 64⟩
  rdA : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) 12) 4
  valA : s₀.mem.readW (addr (s₀.gpr .esp) 12) 32 = K
  sepKA : Region.Disjoint ⟨K.setWidth 64, 4168⟩ ⟨addr (s₀.gpr .esp) 12, 4⟩
  sepBA : Region.Disjoint ⟨B.setWidth 64, 64⟩ ⟨addr (s₀.gpr .esp) 12, 4⟩

/-- After `j` encryptions. -/
structure EncInv (key : List Byte) (K B : BitVec 32) (s₀ : State) (j : Nat) (u : State) : Prop where
  le : j ≤ 521
  esp : u.gpr .esp = s₀.gpr .esp
  ebp : u.gpr .ebp = B
  sched : scheduleAt u.mem (K.setWidth 64) = (ksIter key j).1
  halves : (u.mem.readW (slot B 16) 32, u.mem.readW (slot B 20) 32) = (ksIter key j).2
  saved : Saved u.mem B s₀
  frame : Frame [⟨K.setWidth 64, 4168⟩, ⟨B.setWidth 64, 64⟩] s₀.mem u.mem
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr

theorem EncEnv.wK {K B : BitVec 32} {s₀ u : State} (E : EncEnv K B s₀) (hw : u.wr = s₀.wr) {o n : Nat}
    (h : o + n ≤ 4168) : InRegions u.wr (K.setWidth 64 + BitVec.ofNat 64 o) n := by
  rw [hw]; exact inRegions_off E.wrK h

theorem EncEnv.wB {K B : BitVec 32} {s₀ u : State} (E : EncEnv K B s₀) (hw : u.wr = s₀.wr) {o n : Nat}
    (h : o + n ≤ 64) : InRegions u.wr (slot B o) n := by
  rw [hw]; exact inRegions_off E.wrB h

/-- The schedule's address on the stack, after writes to the schedule and the working space. -/
theorem EncEnv.arg {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {m : Mem}
    (hf : Frame [⟨K.setWidth 64, 4168⟩, ⟨B.setWidth 64, 64⟩] s₀.mem m) :
    m.readW (addr (s₀.gpr .esp) 12) 32 = K := by
  rw [hf.readW (Region.contains_self _ _) (fun r hr => (mem_two hr).elim (· ▸ E.sepKA.symm) (· ▸ E.sepBA.symm))
    (by decide)]
  exact E.valA

theorem EncInv.cenv {key : List Byte} {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {j : Nat} {u : State}
    (I : EncInv key K B s₀ j u) : CipherEnv 12 K B u := by
  have fK := E.fitK
  have fB := E.fitB
  refine ⟨I.ebp, by omega, by rw [I.wr]; exact inRegions_pre E.wrB (by decide), ?_, ?_, fK, fun o ho => ?_,
    E.sep.symm.sub_left (Region.sub_prefix (by decide)), ?_⟩
  · rw [I.rd, I.wr, I.esp]; exact E.rdA
  · rw [I.esp]; exact E.arg I.frame
  · rw [I.rd, I.wr]; exact region_in (inRegions_off E.wrK (by omega))
  · rw [I.esp]; exact E.sepBA.sub_left (Region.sub_prefix (by decide))

/-- The schedule after the block function's writes to the working space. -/
theorem EncEnv.sched_c {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {m m' : Mem}
    (hf : Frame (cRegion B) m m') : scheduleAt m' (K.setWidth 64) = scheduleAt m (K.setWidth 64) :=
  scheduleAt_eq_of_frame _ hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact E.sep.sub_right (Offset.sub_base _ (by decide))

/-- An address at an offset of a pointer at an offset of `K`. -/
theorem addr_ofs {K : BitVec 32} {a b : Nat} (h : K.toNat + a + b < 2 ^ 32) :
    addr (K + BitVec.ofNat 32 a) b = K.setWidth 64 + BitVec.ofNat 64 (a + b) := by
  unfold addr; rw [ofs_add, ← addr, addr_of_fit (by omega)]

theorem ord_true : ord true = id := rfl

/-- The encryption of the last output. -/
theorem enc_cipher {key : List Byte} {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {j : Nat} {u : State}
    (I : EncInv key K B s₀ j u) :
    WP isa (cipher 12 true) u fun u' =>
      (u'.mem.readW (slot B 16) 32, u'.mem.readW (slot B 20) 32) =
        encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2 ∧
        Keep lookRegs u u' ∧ Frame (cRegion B) u.mem u'.mem := by
  refine WP.mono (cipher_run (I.cenv E) true) fun u' ⟨h, k, m⟩ => ⟨?_, k, m⟩
  rw [h, I.sched, ord_true, ← I.halves]; rfl

theorem ksIter_step (key : List Byte) {j : Nat} (hj : j < 521) :
    ksIter key (j + 1) =
      (((ksIter key j).1.set (2 * j) (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1
          (by omega)).set (2 * j + 1)
          (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2 (by omega),
        (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1,
        (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2) := by
  rw [ksIter_succ, ksStep, set!_eq_set _ (by omega), set!_eq_set _ (by omega)]

/-- The working space's pointer and counter, written. -/
theorem slots_facts (m : Mem) (B : BitVec 32) (P C : BitVec 32) :
    let M := (m.writeW (slot B 32) P).writeW (slot B 36) C
    M.readW (slot B 32) 32 = P ∧ M.readW (slot B 36) 32 = C ∧ Frame [⟨slot B 32, 8⟩] m M := by
  intro M
  refine ⟨by rw [Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32], Mem.readW_writeW_self32 _ _ _, ?_⟩
  exact ((Frame.refl _ m).writeW List.mem_cons_self _
    (Offset.contains (e := 32) (k := 8) (d := 32) (n := 4) _ (by decide) (by decide) (by decide))).writeW
    List.mem_cons_self _ (Offset.contains (e := 32) (k := 8) (d := 36) (n := 4) _ (by decide) (by decide) (by decide))

/-- The output's words to the P-array entries at the pointer, the next pair's
pointer, and the counter less one. -/
theorem storeP_run (u : State) {B P C : BitVec 32} {Pa : Addr} (hb : u.gpr .ebp = B)
    (bfit : B.toNat + 40 ≤ 2 ^ 32) (r16 : InRegions (u.rd ++ u.wr) (slot B 16) 4)
    (r20 : InRegions (u.rd ++ u.wr) (slot B 20) 4) (w32 : InRegions u.wr (slot B 32) 4)
    (w36 : InRegions u.wr (slot B 36) 4) (hP : u.mem.readW (slot B 32) 32 = P)
    (hC : u.mem.readW (slot B 36) 32 = C) (e0 : addr P 0 = Pa) (e4 : addr P 4 = Pa + BitVec.ofNat 64 4)
    (w0 : InRegions u.wr Pa 4) (w4 : InRegions u.wr (Pa + BitVec.ofNat 64 4) 4)
    (sep : Mem.Sep (slot B 20) (32 / 8) Pa (32 / 8)) :
    WP isa (.block storeP) u fun t =>
      t.mem = (((u.mem.writeW Pa (u.mem.readW (slot B 16) 32)).writeW (Pa + BitVec.ofNat 64 4)
          (u.mem.readW (slot B 20) 32)).writeW (slot B 32) (P + BitVec.ofNat 32 8)).writeW (slot B 36)
          (C - BitVec.ofNat 32 1) ∧
        t.zf = some (C - BitVec.ofNat 32 1 == 0) := by
  have r32 := region_in (rs := u.rd) w32
  have r36 := region_in (rs := u.rd) w36
  have e : ∀ v : BitVec 32, (u.mem.writeW Pa v).readW (slot B 20) 32 = u.mem.readW (slot B 20) 32 :=
    fun v => Mem.readW_writeW_sep sep (by decide)
  unfold storeP
  brun [hb, addr_slot bfit, r16, r20, r32, r36, w32, w36, hP, hC, e0, e4, w0, w4, e]

/-- The P-array phase: after `j` encryptions, the pointer at P-array entry
`2 j` and `9 - j` left. -/
structure PInv (key : List Byte) (K B : BitVec 32) (s₀ : State) (j : Nat) (u : State) : Prop where
  enc : EncInv key K B s₀ j u
  le : j ≤ 9
  ptr : u.mem.readW (slot B 32) 32 = K + BitVec.ofNat 32 (4096 + 8 * j)
  cnt : u.mem.readW (slot B 36) 32 = BitVec.ofNat 32 (9 - j)

/-- The block function's writes, and the stores' to the working space. -/
abbrev wRegions (K B : BitVec 32) : List Region := [⟨K.setWidth 64, 4168⟩, ⟨slot B 16, 24⟩]

theorem saved_frame {m m' : Mem} {K B : BitVec 32} {s₀ : State} (h : Saved m B s₀) (hf : Frame (wRegions K B) m m')
    (sep : Region.Disjoint ⟨K.setWidth 64, 4168⟩ ⟨B.setWidth 64, 64⟩) (fB : B.toNat + 64 ≤ 2 ^ 32) : Saved m' B s₀ :=
  h.frame hf fun r hr => by
    rcases mem_two hr with rfl | rfl
    · exact sep.symm.sub_left (Region.sub_prefix (by decide))
    · exact Offset.base_disjoint _ (by decide) (by have := fB; omega)

theorem wRegions_sub {K B : BitVec 32} {r : Region} (hr : r ∈ wRegions K B) :
    ∃ r' ∈ [(⟨K.setWidth 64, 4168⟩ : Region), ⟨B.setWidth 64, 64⟩], Region.Sub r r' := by
  rcases mem_two hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub_base _ (by decide)⟩

/-- A slot of the working space, apart from the schedule. -/
theorem EncEnv.sepKB {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {d o : Nat} (hd : d + 4 ≤ 64)
    (ho : o + 4 ≤ 4168) : Mem.Sep (slot B d) (32 / 8) (K.setWidth 64 + BitVec.ofNat 64 o) (32 / 8) :=
  E.sep.symm.sep (Offset.contains_base _ hd (by omega)) (Offset.contains_base _ ho (by omega))

/-- The block function's writes leave the working space's pointer and counter. -/
theorem cipher_past {B : BitVec 32} {m m' : Mem} (hf : Frame (cRegion B) m m') {d : Nat} (h1 : 32 ≤ d)
    (h2 : d + 4 ≤ 40) : m'.readW (slot B d) 32 = m.readW (slot B d) 32 :=
  hf.readW (r := ⟨slot B d, 4⟩) (contains_pre _ (by decide)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint (B.setWidth 64) (d := d) (n := 4) (e := 16) (k := 16) (by omega) (by omega)
      (by omega)) (by decide)

theorem cipher_wide {K B : BitVec 32} {m m' : Mem} (hf : Frame (cRegion B) m m') : Frame (wRegions K B) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩

theorem slots_wide {K B : BitVec 32} {m m' : Mem} (hf : Frame [⟨slot B 32, 8⟩] m m') : Frame (wRegions K B) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩

theorem encP_step {key : List Byte} {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {j : Nat} (hj : j < 9)
    {u : State} (I : PInv key K B s₀ j u) :
    WP isa (.seq (cipher 12 true) (.block storeP)) u fun u' =>
      PInv key K B s₀ (j + 1) u' ∧ u'.zf = some (BitVec.ofNat 32 (9 - (j + 1)) == 0) := by
  have fK := E.fitK
  have fB := E.fitB
  have J := I.enc
  apply WP.seq
  refine WP.mono (enc_cipher E J) fun u₁ ⟨c12, ck, cf⟩ => ?_
  let out := encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2
  let a := 4096 + 4 * (2 * j)
  have e0 : addr (K + BitVec.ofNat 32 (4096 + 8 * j)) 0 = K.setWidth 64 + BitVec.ofNat 64 a := by
    rw [addr_ofs (by omega)]; congr 2; omega
  have e4 : addr (K + BitVec.ofNat 32 (4096 + 8 * j)) 4 = K.setWidth 64 + BitVec.ofNat 64 a + BitVec.ofNat 64 4 := by
    rw [addr_ofs (by omega), Offset.add_add]; congr 2; omega
  have w₁ : u₁.wr = s₀.wr := by rw [ck.2.2, J.wr]
  refine WP.mono (WP.keep [.eax, .ebx, .edx] (storeP_run u₁ (C := BitVec.ofNat 32 (9 - j))
    ((ck.gpr (by decide)).trans J.ebp) (by omega) (region_in (E.wB w₁ (by decide)))
    (region_in (E.wB w₁ (by decide))) (E.wB w₁ (by decide)) (E.wB w₁ (by decide))
    (by rw [cipher_past cf (by decide) (by decide)]; exact I.ptr)
    (by rw [cipher_past cf (by decide) (by decide)]; exact I.cnt) e0 e4 (E.wK w₁ (by omega))
    (by rw [Offset.add_add]; exact E.wK w₁ (by omega)) (E.sepKB (by decide) (by omega))) (by
      decide))
    fun u₂ ⟨⟨sm, sz⟩, sk⟩ => ?_
  rw [Offset.add_add] at sm
  obtain ⟨M32, M36, MF⟩ := slots_facts ((u₁.mem.writeW (K.setWidth 64 + BitVec.ofNat 64 a)
    (u₁.mem.readW (slot B 16) 32)).writeW (K.setWidth 64 + BitVec.ofNat 64 (a + 4)) (u₁.mem.readW (slot B 20) 32))
    B (K + BitVec.ofNat 32 (4096 + 8 * j) + BitVec.ofNat 32 8) (BitVec.ofNat 32 (9 - j) - BitVec.ofNat 32 1)
  rw [← sm] at M32 M36 MF
  have F2 : Frame [⟨K.setWidth 64, 4168⟩] u₁.mem ((u₁.mem.writeW (K.setWidth 64 + BitVec.ofNat 64 a)
      (u₁.mem.readW (slot B 16) 32)).writeW (K.setWidth 64 + BitVec.ofNat 64 (a + 4)) (u₁.mem.readW (slot B 20) 32)) :=
    ((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))
  have FF : Frame (wRegions K B) u.mem u₂.mem :=
    ((cipher_wide cf).trans (F2.mono (by simp))).trans (slots_wide MF)
  have h1 : u₁.mem.readW (slot B 16) 32 = out.1 := congrArg Prod.fst c12
  have h2 : u₁.mem.readW (slot B 20) 32 = out.2 := congrArg Prod.snd c12
  have hsched : scheduleAt u₂.mem (K.setWidth 64) = (ksIter key (j + 1)).1 := by
    rw [scheduleAt_eq_of_frame _ MF (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact E.sep.sub_right (Offset.sub_base _ (by decide))),
      show a + 4 = 4096 + 4 * (2 * j + 1) by omega,
      scheduleAt_writeW_P _ _ (by omega), scheduleAt_writeW_P _ _ (by omega),
      E.sched_c cf, J.sched, ksIter_step key (by omega), h1, h2]
  have rd2 : ∀ d, d + 4 ≤ 32 → u₂.mem.readW (slot B d) 32 = u₁.mem.readW (slot B d) 32 := fun d hd => by
    rw [sm, Mem.readW_writeW_sep (slot_sep B (by omega) (by omega) (by decide)) (by decide),
      Mem.readW_writeW_sep (slot_sep B (by omega) (by omega) (by decide)) (by decide),
      Mem.readW_writeW_sep (E.sepKB (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (E.sepKB (by omega) (by omega)) (by decide)]
  refine ⟨⟨⟨by omega, (sk.gpr (by decide)).trans ((ck.gpr (by decide)).trans J.esp),
    (sk.gpr (by decide)).trans ((ck.gpr (by decide)).trans J.ebp), hsched, ?_,
    saved_frame J.saved FF E.sep fB, J.frame.trans (FF.sub fun r hr => wRegions_sub hr), by rw [sk.2.1, ck.2.1, J.rd],
    by rw [sk.2.2, w₁]⟩, by omega, by rw [M32, ofs_add]; congr 2, ?_⟩, ?_⟩
  · rw [rd2 16 (by decide), rd2 20 (by decide), c12, ksIter_step key (by omega)]
  · rw [M36]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · rw [sz]; congr 2; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- Writing the working space's pointer and counter keeps an encryption's
invariant. -/
theorem EncInv.slots {key : List Byte} {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {j : Nat}
    {u u' : State} (I : EncInv key K B s₀ j u) {P C : BitVec 32}
    (hm : u'.mem = (u.mem.writeW (slot B 32) P).writeW (slot B 36) C) {rs : List Reg} (k : Keep rs u u')
    (hsp : Reg.esp ∉ rs) (hbp : Reg.ebp ∉ rs) :
    EncInv key K B s₀ j u' ∧ u'.mem.readW (slot B 32) 32 = P ∧ u'.mem.readW (slot B 36) 32 = C := by
  obtain ⟨M32, M36, MF⟩ := slots_facts u.mem B P C
  rw [← hm] at M32 M36 MF
  have rd : ∀ d, d + 4 ≤ 32 → u'.mem.readW (slot B d) 32 = u.mem.readW (slot B d) 32 := fun d hd => by
    rw [hm, Mem.readW_writeW_sep (slot_sep B (by omega) (by omega) (by decide)) (by decide),
      Mem.readW_writeW_sep (slot_sep B (by omega) (by omega) (by decide)) (by decide)]
  refine ⟨⟨I.le, (k.gpr hsp).trans I.esp, (k.gpr hbp).trans I.ebp, ?_, by rw [rd 16 (by decide),
    rd 20 (by decide), I.halves], saved_frame I.saved (slots_wide MF) E.sep E.fitB,
    I.frame.trans ((slots_wide MF).sub fun r hr => wRegions_sub hr), by rw [k.2.1, I.rd], by rw [k.2.2, I.wr]⟩,
    M32, M36⟩
  rw [scheduleAt_eq_of_frame _ MF (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact E.sep.sub_right (Offset.sub_base _ (by decide))), I.sched]

theorem encryptP_run {key : List Byte} {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {u : State}
    (I : EncInv key K B s₀ 0 u) : WP isa encryptP u (EncInv key K B s₀ 9) := by
  have fB := E.fitB
  have w32 := E.wB I.wr (o := 32) (n := 4) (by decide)
  have w36 := E.wB I.wr (o := 36) (n := 4) (by decide)
  have rA : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) 12) 4 := by rw [I.rd, I.wr, I.esp]; exact E.rdA
  have vA : u.mem.readW (addr (u.gpr .esp) 12) 32 = K := by rw [I.esp]; exact E.arg I.frame
  unfold encryptP
  apply WP.seq
  refine WP.mono (WP.keep [.ebx, .ecx] (Q := fun t => t.mem = (u.mem.writeW (slot B 32)
      (K + BitVec.ofNat 32 4096)).writeW (slot B 36) (BitVec.ofNat 32 9))
    (by brun [I.ebp, addr_slot (show B.toNat + 40 ≤ 2 ^ 32 by omega), w32, w36, rA, vA, pOff]) (by
      decide))
    fun u₁ ⟨m₁, k₁⟩ => ?_
  obtain ⟨J, j32, j36⟩ := I.slots E m₁ k₁ (by decide) (by decide)
  refine WP.mono (WP.loop (M := isa) (Q := PInv key K B s₀ 9)
    (fun (n : Nat) (v : State) => ∃ j, j < 9 ∧ n = 9 - j ∧ PInv key K B s₀ j v) ?_ 9 u₁
    ⟨0, by decide, rfl, ⟨J, by decide, by rw [j32], by rw [j36]⟩⟩) fun v V => V.enc
  intro n v ⟨j, hj, hn, P⟩
  refine WP.mono (encP_step E hj P) fun v' ⟨P', hz⟩ => ?_
  rw [eval_ne, hz]
  by_cases e : j + 1 = 9
  · left
    exact ⟨by rw [e]; rfl, e ▸ P'⟩
  · right
    have nz : BitVec.ofNat 32 (9 - (j + 1)) ≠ 0 := by
      intro h'; have := congrArg BitVec.toNat h'; simp at this; omega
    exact ⟨by rw [beq_eq_false_iff_ne.mpr nz]; rfl, _, by omega, j + 1, by omega, rfl, P'⟩

/-- The bytes of `x` and `y` into the planes of S-box entries `q` and `q + 1`. -/
def sWrites (m : Mem) (Ka : Addr) (q : Nat) (x y : BitVec 32) : Mem :=
  (((((((m.writeW (Ka + BitVec.ofNat 64 (q + 0)) (BitVec.setWidth 8 x)).writeW
    (Ka + BitVec.ofNat 64 (q + 256)) (BitVec.setWidth 8 (x >>> 8))).writeW
    (Ka + BitVec.ofNat 64 (q + 512)) (BitVec.setWidth 8 (x >>> 8 >>> 8))).writeW
    (Ka + BitVec.ofNat 64 (q + 768)) (BitVec.setWidth 8 (x >>> 8 >>> 8 >>> 8))).writeW
    (Ka + BitVec.ofNat 64 (q + 1)) (BitVec.setWidth 8 y)).writeW
    (Ka + BitVec.ofNat 64 (q + 257)) (BitVec.setWidth 8 (y >>> 8))).writeW
    (Ka + BitVec.ofNat 64 (q + 513)) (BitVec.setWidth 8 (y >>> 8 >>> 8))).writeW
    (Ka + BitVec.ofNat 64 (q + 769)) (BitVec.setWidth 8 (y >>> 8 >>> 8 >>> 8))

/-- A byte written into the schedule. -/
theorem frame_byte {m m' : Mem} {Ka : Addr} (hf : Frame [⟨Ka, 4168⟩] m m') {o : Nat} (ho : o < 4168)
    (v : Byte) : Frame [⟨Ka, 4168⟩] m (m'.writeW (Ka + BitVec.ofNat 64 o) v) :=
  hf.writeW List.mem_cons_self _ (Offset.contains_base _ (by show o + 1 ≤ 4168; omega) (by omega))

/-- What four byte writes into the schedule leave: four bytes apart from it. -/
theorem read_past_bytes {m : Mem} {Ka a : Addr} (hd : Region.Disjoint ⟨a, 4⟩ ⟨Ka, 4168⟩) {o0 o1 o2 o3 : Nat}
    (h0 : o0 < 4168) (h1 : o1 < 4168) (h2 : o2 < 4168) (h3 : o3 < 4168) (v0 v1 v2 v3 : Byte) :
    ((((m.writeW (Ka + BitVec.ofNat 64 o0) v0).writeW (Ka + BitVec.ofNat 64 o1) v1).writeW
      (Ka + BitVec.ofNat 64 o2) v2).writeW (Ka + BitVec.ofNat 64 o3) v3).readW a 32 = m.readW a 32 :=
  (frame_byte (frame_byte (frame_byte (frame_byte (Frame.refl _ m) h0 v0) h1 v1) h2 v2) h3 v3).readW
    (r := ⟨a, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd) (by decide)

theorem read_past_sWrites {m : Mem} {Ka a : Addr} (hd : Region.Disjoint ⟨a, 4⟩ ⟨Ka, 4168⟩) {q : Nat}
    (hq : q + 770 ≤ 4168) (x y : BitVec 32) : (sWrites m Ka q x y).readW a 32 = m.readW a 32 := by
  unfold sWrites
  rw [read_past_bytes hd (by omega) (by omega) (by omega) (by omega),
    read_past_bytes hd (by omega) (by omega) (by omega) (by omega)]

theorem sWrites_frame (m : Mem) (Ka : Addr) {q : Nat} (hq : q + 770 ≤ 4168) (x y : BitVec 32) :
    Frame [⟨Ka, 4168⟩] m (sWrites m Ka q x y) := by
  unfold sWrites
  exact frame_byte (frame_byte (frame_byte (frame_byte (frame_byte (frame_byte (frame_byte (frame_byte
    (Frame.refl _ _) (by omega) _) (by omega) _) (by omega) _) (by omega) _) (by omega) _) (by omega) _)
    (by omega) _) (by omega) _

/-- The head of `storeS`. -/
def storeSHead : List Instr :=
  [.mov .ebx (.mem (at_ .ebp ptrOff)), .mov .edx (.mem (at_ .ebp cntOff)), .mov .eax (.mem (at_ .ebp xlOff))] ++
    storeEntry 0 ++ [.mov .eax (.mem (at_ .ebp xrOff))] ++ storeEntry 1 ++
    [.alu .add .ebx (imm 2), .mov .ecx (.mem (at_ .esp 12)), .alu .sub .ecx (.reg .ebx), .alu .test .ecx (imm 255)]

theorem storeSHead_run (u : State) {B K C : BitVec 32} {q : Nat} (hb : u.gpr .ebp = B)
    (bfit : B.toNat + 40 ≤ 2 ^ 32) (r16 : InRegions (u.rd ++ u.wr) (slot B 16) 4)
    (r20 : InRegions (u.rd ++ u.wr) (slot B 20) 4) (r32 : InRegions (u.rd ++ u.wr) (slot B 32) 4)
    (r36 : InRegions (u.rd ++ u.wr) (slot B 36) 4)
    (hP : u.mem.readW (slot B 32) 32 = K + BitVec.ofNat 32 q) (hC : u.mem.readW (slot B 36) 32 = C)
    (rA : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) 12) 4)
    (eK : ∀ c, c < 770 → addr (K + BitVec.ofNat 32 q) c = K.setWidth 64 + BitVec.ofNat 64 (q + c))
    (w : ∀ c, c < 770 → InRegions u.wr (K.setWidth 64 + BitVec.ofNat 64 (q + c)) 1) (hq : q + 770 ≤ 4168)
    (d20 : Region.Disjoint ⟨slot B 20, 4⟩ ⟨K.setWidth 64, 4168⟩)
    (dA : Region.Disjoint ⟨addr (u.gpr .esp) 12, 4⟩ ⟨K.setWidth 64, 4168⟩) :
    WP isa (.block storeSHead) u fun t =>
      t.mem = sWrites u.mem (K.setWidth 64) q (u.mem.readW (slot B 16) 32) (u.mem.readW (slot B 20) 32) ∧
      t.gpr .ebx = K + BitVec.ofNat 32 q + BitVec.ofNat 32 2 ∧ t.gpr .edx = C ∧
      t.zf = some ((u.mem.readW (addr (u.gpr .esp) 12) 32 - (K + BitVec.ofNat 32 q + BitVec.ofNat 32 2) &&&
        BitVec.ofNat 32 255) == 0) := by
  have p20 := read_past_bytes (m := u.mem) d20 (o0 := q + 0) (o1 := q + 256) (o2 := q + 512) (o3 := q + 768)
    (by omega) (by omega) (by omega) (by omega)
  have pA' := fun v0 v1 v2 v3 v4 v5 v6 v7 => (read_past_bytes (m := (((u.mem.writeW
    (K.setWidth 64 + BitVec.ofNat 64 (q + 0)) v0).writeW (K.setWidth 64 + BitVec.ofNat 64 (q + 256)) v1).writeW
    (K.setWidth 64 + BitVec.ofNat 64 (q + 512)) v2).writeW (K.setWidth 64 + BitVec.ofNat 64 (q + 768)) v3)
    dA (o0 := q + 1) (o1 := q + 257) (o2 := q + 513) (o3 := q + 769) (by omega) (by omega) (by omega) (by omega)
    v4 v5 v6 v7).trans (read_past_bytes (m := u.mem) dA (o0 := q + 0) (o1 := q + 256) (o2 := q + 512)
    (o3 := q + 768) (by omega) (by omega) (by omega) (by omega) v0 v1 v2 v3)
  unfold sWrites
  have e1 := eK 0 (by decide)
  have e2 := eK 256 (by decide)
  have e3 := eK 512 (by decide)
  have e4 := eK 768 (by decide)
  have e5 := eK 1 (by decide)
  have e6 := eK 257 (by decide)
  have e7 := eK 513 (by decide)
  have e8 := eK 769 (by decide)
  have w1 := w 0 (by decide)
  have w2 := w 256 (by decide)
  have w3 := w 512 (by decide)
  have w4 := w 768 (by decide)
  have w5 := w 1 (by decide)
  have w6 := w 257 (by decide)
  have w7 := w 513 (by decide)
  have w8 := w 769 (by decide)
  unfold storeSHead storeEntry
  brun [hb, addr_slot bfit, r16, r20, r32, r36, hP, hC, rA, e1, e2, e3, e4, e5, e6, e7, e8, w1, w2, w3, w4,
    w5, w6, w7, w8, Nat.reduceAdd, p20, pA']

theorem sAnd_z (K : BitVec 32) (q : Nat) (hq : q + 2 < 2 ^ 32) :
    (K - (K + BitVec.ofNat 32 q + BitVec.ofNat 32 2) &&& BitVec.ofNat 32 255 == 0) =
      decide ((q + 2) % 256 = 0) := by
  have e : K - (K + BitVec.ofNat 32 q + BitVec.ofNat 32 2) &&& BitVec.ofNat 32 255 =
      BitVec.ofNat 32 ((2 ^ 32 - (q + 2)) % 256) := by
    rw [ofs_add, ofs_neg]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [show (255 % 2 ^ 32 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [e]
  by_cases h : (q + 2) % 256 = 0
  · have : (2 ^ 32 - (q + 2)) % 256 = 0 := by omega
    rw [this]; simp [h]
  · have : BitVec.ofNat 32 ((2 ^ 32 - (q + 2)) % 256) ≠ 0 := by
      intro e'; have := congrArg BitVec.toNat e'; simp at this; omega
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem storeSTail_run (u : State) {B C : BitVec 32} (hb : u.gpr .ebp = B) (bfit : B.toNat + 40 ≤ 2 ^ 32)
    (w32 : InRegions u.wr (slot B 32) 4) (w36 : InRegions u.wr (slot B 36) 4) (hd : u.gpr .edx = C) :
    WP isa (.block [.store (at_ .ebp ptrOff) .ebx, .alu .sub .edx (imm 1), .store (at_ .ebp cntOff) .edx]) u
      fun t => t.mem = (u.mem.writeW (slot B 32) (u.gpr .ebx)).writeW (slot B 36) (C - BitVec.ofNat 32 1) ∧
        t.zf = some (C - BitVec.ofNat 32 1 == 0) := by
  brun [hb, addr_slot bfit, w32, w36, hd]

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

theorem shr_shr (x : BitVec 32) : x >>> 8 >>> 8 = x >>> 16 := by rw [← BitVec.shiftRight_add]
theorem shr_shr_shr (x : BitVec 32) : x >>> 8 >>> 8 >>> 8 = x >>> 24 := by
  rw [shr_shr, ← BitVec.shiftRight_add]

theorem low_byte (x : BitVec 32) : x.setWidth 8 = x.extractLsb' 0 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem sWrites_sched (m : Mem) (Ka : Addr) {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) (x y : BitVec 32) :
    scheduleAt (sWrites m Ka (sOff j) x y) Ka = ((scheduleAt m Ka).set (2 * j) x (by omega)).set (2 * j + 1) y
      (by omega) := by
  have e : ∀ b k, k < 2 → sOff j + (256 * b + k) = entryOff (2 * j + k) b := fun b k hk => sOff_entry h9 hj hk
  unfold sWrites
  simp only [Proof.Rc4.writeW_byte8, shr_shr_shr]
  simp only [shr_shr]
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

/-- The S-box phase: after `j` encryptions, the pointer at S-box entry
`sDone j` and `521 - j` left. -/
structure SInv (key : List Byte) (K B : BitVec 32) (s₀ : State) (j : Nat) (u : State) : Prop where
  enc : EncInv key K B s₀ j u
  ge : 9 ≤ j
  ptr : u.mem.readW (slot B 32) 32 = K + BitVec.ofNat 32 (sOff j)
  cnt : u.mem.readW (slot B 36) 32 = BitVec.ofNat 32 (521 - j)

theorem encS_step {key : List Byte} {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {j : Nat}
    (hj : j < 521) {u : State} (I : SInv key K B s₀ j u) :
    WP isa (.seq (cipher 12 true) storeS) u fun u' =>
      SInv key K B s₀ (j + 1) u' ∧ u'.zf = some (BitVec.ofNat 32 (521 - (j + 1)) == 0) := by
  have fK := E.fitK
  have fB := E.fitB
  have J := I.enc
  have h9 := I.ge
  have hq := sOff_lt h9 hj
  apply WP.seq
  refine WP.mono (enc_cipher E J) fun u₁ ⟨c12, ck, cf⟩ => ?_
  have w₁ : u₁.wr = s₀.wr := by rw [ck.2.2, J.wr]
  have e1 : u₁.gpr .esp = s₀.gpr .esp := (ck.gpr (by decide)).trans J.esp
  have F1 : Frame [⟨K.setWidth 64, 4168⟩, ⟨B.setWidth 64, 64⟩] s₀.mem u₁.mem :=
    J.frame.trans ((cipher_wide cf).sub fun r hr => wRegions_sub hr)
  unfold storeS
  apply WP.seq
  refine WP.mono (WP.keep [.eax, .ebx, .ecx, .edx] (storeSHead_run u₁ (K := K) (q := sOff j)
    (C := BitVec.ofNat 32 (521 - j)) ((ck.gpr (by decide)).trans J.ebp) (by omega)
    (region_in (E.wB w₁ (by decide))) (region_in (E.wB w₁ (by decide))) (region_in (E.wB w₁ (by decide)))
    (region_in (E.wB w₁ (by decide))) (by rw [cipher_past cf (by decide) (by decide)]; exact I.ptr)
    (by rw [cipher_past cf (by decide) (by decide)]; exact I.cnt)
    (by rw [ck.2.1, ck.2.2, J.rd, J.wr, e1]; exact E.rdA) (fun c hc => addr_ofs (by omega))
    (fun c hc => E.wK w₁ (by omega)) (by omega) (E.sep.symm.sub_left (Offset.sub_base _ (by decide)))
    (by rw [e1]; exact E.sepKA.symm)) (by decide))
    fun u₂ ⟨⟨hm, hbx, hdx, hz⟩, hk⟩ => ?_
  rw [e1, E.arg F1, sAnd_z K _ (by omega)] at hz
  -- past the other planes after an S-box's last entry
  apply WP.seq
  have hite : WP isa (.ite .e (.block [.alu .add .ebx (imm 768)]) (.block [])) u₂ fun u₃ =>
      u₃.gpr .ebx = K + BitVec.ofNat 32 (sOff (j + 1)) ∧ u₃.mem = u₂.mem ∧ Keep [.ebx] u₂ u₃ := by
    refine WP.ite _ (by rw [eval_e, hz]) (fun h => ?_) (fun h => ?_)
    · refine WP.mono (WP.keep [.ebx] (Q := fun t => t.gpr .ebx = u₂.gpr .ebx + BitVec.ofNat 32 768 ∧
        t.mem = u₂.mem) (by brun) (by decide)) fun t ⟨⟨t12, tm⟩, tk⟩ => ⟨?_, tm, tk⟩
      rw [t12, hbx, ofs_add, ofs_add, sOff_succ h9, ite_eq_left (of_decide_eq_true h)]
    · refine WP.block_nil ⟨?_, rfl, Keep.refl _ _⟩
      rw [hbx, ofs_add, sOff_succ h9, ite_eq_right (of_decide_eq_false h)]
  refine WP.mono hite fun u₃ ⟨g12, gm, gk⟩ => ?_
  have k₃ : Keep lookRegs u u₃ := ((ck.trans hk).trans gk).mono (by decide)
  have w₃ : u₃.wr = s₀.wr := by rw [k₃.2.2, J.wr]
  have F8 := sWrites_frame u₁.mem (K.setWidth 64) (q := sOff j) (by omega) (u₁.mem.readW (slot B 16) 32)
    (u₁.mem.readW (slot B 20) 32)
  rw [← hm, ← gm] at F8
  refine WP.mono (WP.keep [.edx] (storeSTail_run u₃ (C := BitVec.ofNat 32 (521 - j))
    ((k₃.gpr (by decide)).trans J.ebp) (by omega) (E.wB w₃ (by decide)) (E.wB w₃ (by decide))
    (by rw [gk.gpr (by decide), hdx])) (by decide))
    fun u₄ ⟨⟨tm, tz⟩, tk⟩ => ?_
  obtain ⟨M32, M36, MF⟩ := slots_facts u₃.mem B (u₃.gpr .ebx) (BitVec.ofNat 32 (521 - j) - BitVec.ofNat 32 1)
  rw [← tm] at M32 M36 MF
  have FF : Frame (wRegions K B) u.mem u₄.mem :=
    ((cipher_wide cf).trans (F8.mono (by simp))).trans (slots_wide MF)
  have h1 : u₁.mem.readW (slot B 16) 32 = (encryptWords (ksIter key j).1 (ksIter key j).2.1
      (ksIter key j).2.2).1 := congrArg Prod.fst c12
  have h2 : u₁.mem.readW (slot B 20) 32 = (encryptWords (ksIter key j).1 (ksIter key j).2.1
      (ksIter key j).2.2).2 := congrArg Prod.snd c12
  have hsched : scheduleAt u₄.mem (K.setWidth 64) = (ksIter key (j + 1)).1 := by
    rw [scheduleAt_eq_of_frame _ MF (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact E.sep.sub_right (Offset.sub_base _ (by decide))), gm, hm,
      sWrites_sched _ _ h9 hj, E.sched_c cf, J.sched, ksIter_step key hj, h1, h2]
  have rd4 : ∀ d, d + 4 ≤ 32 → u₄.mem.readW (slot B d) 32 = u₁.mem.readW (slot B d) 32 := fun d hd => by
    rw [tm, Mem.readW_writeW_sep (slot_sep B (by omega) (by omega) (by decide)) (by decide),
      Mem.readW_writeW_sep (slot_sep B (by omega) (by omega) (by decide)) (by decide), gm, hm,
      read_past_sWrites (E.sep.symm.sub_left (Offset.sub_base _ (by omega))) (by omega)]
  have k₄ : Keep lookRegs u u₄ := (k₃.trans tk).mono (by decide)
  refine ⟨⟨⟨by omega, (k₄.gpr (by decide)).trans J.esp, (k₄.gpr (by decide)).trans J.ebp, hsched, ?_,
    saved_frame J.saved FF E.sep fB, J.frame.trans (FF.sub fun r hr => wRegions_sub hr), by rw [k₄.2.1, J.rd],
    by rw [k₄.2.2, J.wr]⟩, by omega, by rw [M32, g12], ?_⟩, ?_⟩
  · rw [rd4 16 (by decide), rd4 20 (by decide), c12, ksIter_step key hj]
  · rw [M36]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · rw [tz]; congr 2; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem encryptS_run {key : List Byte} {K B : BitVec 32} {s₀ : State} (E : EncEnv K B s₀) {u : State}
    (I : EncInv key K B s₀ 9 u) : WP isa encryptS u (EncInv key K B s₀ 521) := by
  have fB := E.fitB
  have w32 := E.wB I.wr (o := 32) (n := 4) (by decide)
  have w36 := E.wB I.wr (o := 36) (n := 4) (by decide)
  have rA : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) 12) 4 := by rw [I.rd, I.wr, I.esp]; exact E.rdA
  have vA : u.mem.readW (addr (u.gpr .esp) 12) 32 = K := by rw [I.esp]; exact E.arg I.frame
  unfold encryptS
  apply WP.seq
  refine WP.mono (WP.keep [.ebx, .ecx] (Q := fun t => t.mem = (u.mem.writeW (slot B 32) K).writeW (slot B 36)
      (BitVec.ofNat 32 512))
    (by brun [I.ebp, addr_slot (show B.toNat + 40 ≤ 2 ^ 32 by omega), w32, w36, rA, vA]) (by
      decide))
    fun u₁ ⟨m₁, k₁⟩ => ?_
  obtain ⟨J, j32, j36⟩ := I.slots E m₁ k₁ (by decide) (by decide)
  refine WP.loop (M := isa) (Q := EncInv key K B s₀ 521)
    (fun (n : Nat) (v : State) => ∃ j, j < 521 ∧ n = 521 - j ∧ SInv key K B s₀ j v) ?_ 512 u₁
    ⟨9, by decide, rfl, ⟨J, by decide, by rw [j32, show sOff 9 = 0 by decide, BitVec.add_zero], by rw [j36]⟩⟩
  intro n v ⟨j, hj, hn, P⟩
  refine WP.mono (encS_step E hj P) fun v' ⟨P', hz⟩ => ?_
  rw [eval_ne, hz]
  by_cases e : j + 1 = 521
  · left
    exact ⟨by rw [e]; rfl, e ▸ P'.enc⟩
  · right
    have nz : BitVec.ofNat 32 (521 - (j + 1)) ≠ 0 := by
      intro h'; have := congrArg BitVec.toNat h'; simp at this; omega
    exact ⟨by rw [beq_eq_false_iff_ne.mpr nz]; rfl, _, by omega, j + 1, by omega, rfl, P'⟩

end VG.Proof.Blowfish.X86
