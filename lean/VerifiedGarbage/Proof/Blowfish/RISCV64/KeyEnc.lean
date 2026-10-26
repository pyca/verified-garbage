module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.Cipher
public import VerifiedGarbage.Proof.Blowfish.RISCV64.Frame
public import VerifiedGarbage.Proof.Blowfish.KeySched
public import VerifiedGarbage.Proof.Blowfish.KeyTable
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Blowfish.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Blowfish.RISCV64.KeyInit

/-!
# Blowfish on RISCV64, key expansion: the encryptions

`encryptP_run` and `encryptS_run`: the 521 encryptions of the key schedule,
each under the schedule as written so far, their outputs into the P-array
and then the S-boxes' planes (`ksIter`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- The registers the encryptions write. -/
def encRegs : List Reg := [.a0, .a1, .a3, .a4, .a5, .a6, .t0, .t1, .t2, .t3, .t4, .t5, .t6]

/-- After `j` encryptions, from the state `s₀` before them: the schedule at
`S` and the last output. -/
structure EncInv (key : List Byte) (S : Addr) (s₀ : State) (j : Nat) (u : State) : Prop where
  sched : scheduleAt u.mem S = (ksIter key j).1
  halves : (lo (u.gpr .a3), lo (u.gpr .a4)) = ((ksIter key j).2.1, (ksIter key j).2.2)
  keep : Keep encRegs s₀ u
  frame : Frame [⟨S, 4168⟩] s₀.mem u.mem

/-- What the encryptions need of the state before them. -/
structure EncEnv (S : Addr) (s₀ : State) : Prop where
  sch : s₀.gpr .a7 = S
  al : S.toNat % 4 = 0
  al8 : S.toNat % 8 = 0
  wS : Writable s₀.wr S

theorem ord_true : ord true = id := rfl

/-- The encryption of the last output. -/
theorem enc_cipher {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀) {j : Nat} {u : State}
    (I : EncInv key S s₀ j u) :
    WP isa (cipher true) u fun u' =>
      (lo (u'.gpr .a3), lo (u'.gpr .a4)) =
        encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2 ∧
        Keep cRegs u u' ∧ u'.mem = u.mem := by
  have LE : LookEnv u := by
    refine ⟨fun o _ ho => ?_, fun o _ ho => ?_, by rw [I.keep.gpr (by decide), E.sch]; exact E.al,
      by rw [I.keep.gpr (by decide), E.sch]; exact E.al8⟩
    · rw [I.keep.gpr (by decide), E.sch, I.keep.2.1, I.keep.2.2]
      obtain ⟨r, hr, hc⟩ := E.wS o 4 ho (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [I.keep.gpr (by decide), E.sch, I.keep.2.1, I.keep.2.2]
      obtain ⟨r, hr, hc⟩ := E.wS o 8 ho (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (cipher_run LE true) fun u' ⟨h, k, m⟩ => ⟨?_, k, m⟩
  have e1 := congrArg Prod.fst I.halves
  have e2 := congrArg Prod.snd I.halves
  simp only at e1 e2
  rw [h, I.keep.gpr (by decide), E.sch, I.sched, ord_true, e1, e2]; rfl

theorem ksIter_step (key : List Byte) {j : Nat} (hj : j < 521) :
    ksIter key (j + 1) =
      (((ksIter key j).1.set (2 * j) (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1
          (by omega)).set (2 * j + 1)
          (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2 (by omega),
        (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1,
        (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2) := by
  rw [ksIter_succ, ksStep, set!_eq_set _ (by omega), set!_eq_set _ (by omega)]

/-! ## The P-array -/

theorem storeP_run (u : State) {a : Addr} (h16 : u.gpr .a1 = a) (w0 : InRegions u.wr a 4)
    (w4 : InRegions u.wr (a + BitVec.ofNat 64 4) 4) (al0 : a.toNat % 4 = 0)
    (al4 : (a + BitVec.ofNat 64 4).toNat % 4 = 0) :
    WP isa (.block storeP) u fun t =>
      t.mem = (u.mem.writeW a (lo (u.gpr .a3))).writeW (a + BitVec.ofNat 64 4) (lo (u.gpr .a4)) ∧
      t.gpr .a1 = a + 8#64 ∧ t.gpr .a0 = u.gpr .a0 - 1#64 ∧ Keep [.a1, .a0] u t := by
  refine WP.mono (WP.keep [.a1, .a0] (Q := fun t =>
      t.mem = (u.mem.writeW a (lo (u.gpr .a3))).writeW (a + BitVec.ofNat 64 4) (lo (u.gpr .a4)) ∧
      t.gpr .a1 = a + 8#64 ∧ t.gpr .a0 = u.gpr .a0 - 1#64) ?_ (by decide) rfl)
    fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  unfold storeP
  brun [h16, w0, w4, al0, al4]

/-- After `j` of the first nine encryptions. -/
structure PInv (key : List Byte) (S : Addr) (s₀ : State) (j : Nat) (u : State) : Prop extends
    EncInv key S s₀ j u where
  le : j ≤ 9
  ptr : u.gpr .a1 = S + BitVec.ofNat 64 (4096 + 8 * j)
  cnt : u.gpr .a0 = BitVec.ofNat 64 (9 - j)

theorem encP_step {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀) {j : Nat} (hj : j < 9)
    {u : State} (I : PInv key S s₀ j u) :
    WP isa (.seq (cipher true) (.block storeP)) u fun u' =>
      PInv key S s₀ (j + 1) u' ∧ u'.gpr .a0 = BitVec.ofNat 64 (9 - (j + 1)) := by
  apply WP.seq
  refine WP.mono (enc_cipher E I.toEncInv) fun v ⟨hv, kv, mv⟩ => ?_
  have wr : v.wr = s₀.wr := by rw [kv.2.2, I.keep.2.2]
  have a0 : S + BitVec.ofNat 64 (4096 + 8 * j) = S + BitVec.ofNat 64 (4096 + 4 * (2 * j)) := by
    congr 2; omega
  have a4 : S + BitVec.ofNat 64 (4096 + 8 * j) + BitVec.ofNat 64 4 =
      S + BitVec.ofNat 64 (4096 + 4 * (2 * j + 1)) := Offset.add_add_eq _ (by omega)
  refine WP.mono (storeP_run v (a := S + BitVec.ofNat 64 (4096 + 8 * j)) (by rw [kv.gpr (by decide), I.ptr])
    (by rw [wr, a0]; exact E.wS _ _ (by omega) (by omega))
    (by rw [wr, a4]; exact E.wS _ _ (by omega) (by omega))
    (by rw [a0, show 4096 + 4 * (2 * j) = 4 * (1024 + 2 * j) by omega]; exact al4 E.al _ (by omega))
    (by rw [a4, show 4096 + 4 * (2 * j + 1) = 4 * (1024 + 2 * j + 1) by omega]; exact al4 E.al _ (by omega)))
    fun t ⟨tm, t16, t17, tk⟩ => ?_
  have c17 : t.gpr .a0 = BitVec.ofNat 64 (9 - (j + 1)) := by
    rw [t17, kv.gpr (by decide), I.cnt]; apply BitVec.eq_of_toNat_eq; simp; omega
  refine ⟨⟨⟨?_, ?_, ((I.keep.trans kv).trans tk).mono (by decide), ?_⟩, by omega, ?_, c17⟩, c17⟩
  · rw [tm, a4, a0, scheduleAt_writeW_P _ _ (by omega), scheduleAt_writeW_P _ _ (by omega), mv, I.sched,
      ksIter_step key (by omega), ← hv]
  · rw [tk.gpr (by decide), tk.gpr (by decide), ksIter_step key (by omega), ← hv]
  · rw [tm, mv]
    refine (I.frame.writeW List.mem_cons_self _ ?_).writeW List.mem_cons_self _ ?_
    · rw [a0]; exact Offset.contains_base S (by omega) (by omega)
    · rw [a4]; exact Offset.contains_base S (by omega) (by omega)
  · rw [t16, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, Offset.add_add]
    congr 2

theorem encryptP_run {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀) {u : State}
    (I : EncInv key S s₀ 0 u) :
    WP isa encryptP u (PInv key S s₀ 9) := by
  unfold encryptP
  apply WP.seq
  refine WP.mono (WP.keep [.a1, .a0] (Q := fun t => t.gpr .a1 = S + BitVec.ofNat 64 4096 ∧
      t.gpr .a0 = BitVec.ofNat 64 9 ∧ t.mem = u.mem)
    (by brun [I.keep.gpr (show Reg.a7 ∉ encRegs by decide), E.sch, pOff]; rw [Offset.add_add, Offset.add_add]) (by decide) rfl)
    fun t ⟨⟨a, b, c⟩, k⟩ => ?_
  have I₀ : PInv key S s₀ 0 t :=
    ⟨⟨by rw [c]; exact I.sched, by rw [k.gpr (by decide), k.gpr (by decide)]; exact I.halves,
      (I.keep.trans k).mono (by decide), by rw [c]; exact I.frame⟩, by omega, a, b⟩
  refine WP.loop (M := isa) (fun m v => ∃ j, j < 9 ∧ m = 9 - j ∧ PInv key S s₀ j v)
    ?_ 9 t ⟨0, by omega, rfl, I₀⟩
  intro m v ⟨j, hj, hm, J⟩
  refine WP.mono (encP_step E hj J) fun v' ⟨J', z'⟩ => ?_
  rw [Steps.eval_nonzero_ofNat _ _ (by omega) z']
  by_cases h : j + 1 = 9
  · left; exact ⟨by simp [h], h ▸ J'⟩
  · right
    exact ⟨by simp; omega, 9 - (j + 1), by omega, j + 1, by omega, rfl, J'⟩

/-! ## The S-boxes -/

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

/-- The bytes of `x` and `y` into the planes of S-box entries `q` and `q + 1`
of the schedule at `S`. -/
def sW (m : Mem) (S : Addr) (q : Nat) (x y : BitVec 32) : Mem :=
  (((((((m.write (S + BitVec.ofNat 64 q) 1 (x.extractLsb' 0 8)).write
    (S + BitVec.ofNat 64 q + BitVec.ofNat 64 256) 1 (x.extractLsb' 8 8)).write
    (S + BitVec.ofNat 64 q + BitVec.ofNat 64 512) 1 (x.extractLsb' 16 8)).write
    (S + BitVec.ofNat 64 q + BitVec.ofNat 64 768) 1 (x.extractLsb' 24 8)).write
    (S + BitVec.ofNat 64 q + BitVec.ofNat 64 1) 1 (y.extractLsb' 0 8)).write
    (S + BitVec.ofNat 64 q + BitVec.ofNat 64 257) 1 (y.extractLsb' 8 8)).write
    (S + BitVec.ofNat 64 q + BitVec.ofNat 64 513) 1 (y.extractLsb' 16 8)).write
    (S + BitVec.ofNat 64 q + BitVec.ofNat 64 769) 1 (y.extractLsb' 24 8)

theorem sW_sched (m : Mem) (S : Addr) {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) (x y : BitVec 32) :
    scheduleAt (sW m S (sOff j) x y) S = ((scheduleAt m S).set (2 * j) x (by omega)).set (2 * j + 1) y
      (by omega) := by
  have e : ∀ b k, k < 2 → S + BitVec.ofNat 64 (sOff j) + BitVec.ofNat 64 (256 * b + k) =
      S + BitVec.ofNat 64 (entryOff (2 * j + k) b) := fun b k hk => by
    rw [Offset.add_add, sOff_entry h9 hj hk]
  have e' : ∀ o b k, k < 2 → o = 256 * b + k → S + BitVec.ofNat 64 (sOff j) + BitVec.ofNat 64 o =
      S + BitVec.ofNat 64 (entryOff (2 * j + k) b) := fun o b k hk ho => by rw [ho]; exact e b k hk
  have e0 : S + BitVec.ofNat 64 (sOff j) = S + BitVec.ofNat 64 (entryOff (2 * j + 0) 0) := by
    have := e 0 0 (by decide); rwa [BitVec.add_zero] at this
  unfold sW
  rw [e' 256 1 0 (by decide) rfl, e' 512 2 0 (by decide) rfl, e' 768 3 0 (by decide) rfl,
    e' 1 0 1 (by decide) rfl, e' 257 1 1 (by decide) rfl, e' 513 2 1 (by decide) rfl,
    e' 769 3 1 (by decide) rfl, e0, scheduleAt_write_bytes _ _ (by omega), Nat.add_zero,
    scheduleAt_write_bytes _ _ (by omega)]

theorem write1_eq (m : Mem) (a : Addr) (v : BitVec 8) : m.write a 1 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

theorem sW_frame (m : Mem) (S : Addr) {q : Nat} (hq : q + 770 ≤ 4168) (x y : BitVec 32) :
    Frame [⟨S, 4168⟩] m (sW m S q x y) := by
  have c : ∀ e, e < 770 → Region.Contains ⟨S, 4168⟩ (S + BitVec.ofNat 64 q + BitVec.ofNat 64 e) (8 / 8) :=
    fun e he => by rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
  have c0 : Region.Contains ⟨S, 4168⟩ (S + BitVec.ofNat 64 q) (8 / 8) :=
    Offset.contains_base _ (by omega) (by omega)
  unfold sW
  simp only [write1_eq]
  exact (((((((((Frame.refl _ m).writeW List.mem_cons_self _ c0).writeW List.mem_cons_self _
    (c 256 (by decide))).writeW List.mem_cons_self _ (c 512 (by decide))).writeW List.mem_cons_self _
    (c 768 (by decide))).writeW List.mem_cons_self _ (c 1 (by decide))).writeW List.mem_cons_self _
    (c 257 (by decide))).writeW List.mem_cons_self _ (c 513 (by decide))).writeW List.mem_cons_self _
    (c 769 (by decide)))

theorem byte0 (g : BitVec 64) : g.setWidth 8 = (lo g).extractLsb' 0 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi, show i < 32 by omega]

theorem extract_shr (x : BitVec 32) {k : Nat} (hk : k + 8 ≤ 32) :
    (x >>> k).extractLsb' 0 8 = x.extractLsb' k 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi, show i < 32 by omega, show k + i < 32 by omega, Nat.add_comm]

def storeSHead : List Instr :=
  storeEntry xL 0 ++ storeEntry xR 1 ++ [.addi ptr ptr 2, .sub tmp ptr sch, .shift .sll .d tmp tmp 56]

theorem storeSHead_run (u : State) {S : Addr} {q : Nat} (hq : q + 770 ≤ 4168) (h16 : u.gpr .a1 = S + BitVec.ofNat 64 q)
    (h3 : u.gpr .a7 = S) (hw : Writable u.wr S) :
    WP isa (.block storeSHead) u fun t =>
      t.mem = sW u.mem S q (lo (u.gpr .a3)) (lo (u.gpr .a4)) ∧ t.gpr .a1 = S + BitVec.ofNat 64 (q + 2) ∧
      t.gpr .t4 = BitVec.ofNat 64 (q + 2) <<< 56 ∧ Keep [.t4, .a1] u t := by
  refine WP.mono (WP.keep [.t4, .a1] (Q := fun t =>
      t.mem = sW u.mem S q (lo (u.gpr .a3)) (lo (u.gpr .a4)) ∧ t.gpr .a1 = S + BitVec.ofNat 64 (q + 2) ∧
      t.gpr .t4 = BitVec.ofNat 64 (q + 2) <<< 56) ?_ (by decide) rfl) fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  have c : ∀ e, e < 770 → InRegions u.wr (S + BitVec.ofNat 64 q + BitVec.ofNat 64 e) 1 :=
    fun e he => by rw [Offset.add_add]; exact hw _ _ (by omega) (by omega)
  have c0 : InRegions u.wr (S + BitVec.ofNat 64 q) 1 := hw _ _ (by omega) (by omega)
  have w256 := c 256 (by decide); have w512 := c 512 (by decide); have w768 := c 768 (by decide)
  have w1 := c 1 (by decide); have w257 := c 257 (by decide); have w513 := c 513 (by decide)
  have w769 := c 769 (by decide)
  unfold storeSHead storeEntry
  brun [h16, h3, c0, w256, w512, w768, w1, w257, w513, w769]
  refine ⟨?_, ?_, ?_⟩
  · simp only [sW, byte0, lo_sext, extract_shr _ (k := 8) (by decide), extract_shr _ (k := 16) (by decide),
      extract_shr _ (k := 24) (by decide)]
  · rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, Offset.add_add]
  · rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, Offset.add_add, Offset.add_sub_cancel_left]

/-- `n << 56` is zero iff the low byte of `n` is. -/
theorem shl56_beq {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n <<< 56 == (0 : BitVec 64)) = decide (n % 256 = 0) := by
  have e : (BitVec.ofNat 64 n <<< 56 = 0#64) ↔ n % 256 = 0 := by
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, 
        Nat.mod_eq_of_lt hn] at this
      omega
    · intro h
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, 
        Nat.mod_eq_of_lt hn]
      omega
  by_cases h : n % 256 = 0
  · simp [e.mpr h, h]
  · have : ¬ BitVec.ofNat 64 n <<< 56 = 0#64 := fun h' => h (e.mp h')
    simp [this, h]

/-- After `j` encryptions, the first nine into the P-array. -/
structure SInv (key : List Byte) (S : Addr) (s₀ : State) (j : Nat) (u : State) : Prop extends
    EncInv key S s₀ j u where
  ge : 9 ≤ j
  le : j ≤ 521
  ptr : u.gpr .a1 = S + BitVec.ofNat 64 (sOff j)
  cnt : u.gpr .a0 = BitVec.ofNat 64 (521 - j)

theorem encS_step {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀) {j : Nat} (hj : j < 521)
    {u : State} (I : SInv key S s₀ j u) :
    WP isa (.seq (cipher true) storeS) u fun u' =>
      SInv key S s₀ (j + 1) u' ∧ u'.gpr .a0 = BitVec.ofNat 64 (521 - (j + 1)) := by
  have h9 := I.ge
  have hq := sOff_lt h9 hj
  apply WP.seq
  refine WP.mono (enc_cipher E I.toEncInv) fun v ⟨hv, kv, mv⟩ => ?_
  have Kv : Keep encRegs s₀ v := (I.keep.trans kv).mono (by decide)
  unfold storeS
  apply WP.seq
  refine WP.mono (storeSHead_run v (S := S) (q := sOff j) (by omega) (by rw [kv.gpr (by decide), I.ptr])
    (by rw [Kv.gpr (by decide), E.sch]) (by rw [Kv.2.2]; exact E.wS)) fun t ⟨tm, t16, t12, tk⟩ => ?_
  have Kt : Keep encRegs s₀ t := (Kv.trans tk).mono (by decide)
  have hsch : scheduleAt t.mem S = (ksIter key (j + 1)).1 := by
    rw [tm, sW_sched _ _ h9 hj, mv, I.sched, ksIter_step key hj, ← hv]
  have hhalf : (lo (t.gpr .a3), lo (t.gpr .a4)) = ((ksIter key (j + 1)).2.1, (ksIter key (j + 1)).2.2) := by
    rw [tk.gpr (by decide), tk.gpr (by decide), ksIter_step key hj, ← hv]
  have hfr : Frame [⟨S, 4168⟩] s₀.mem t.mem := by
    rw [tm, mv]; exact I.frame.trans (sW_frame _ _ (by omega) _ _)
  have h17 : t.gpr .a0 = BitVec.ofNat 64 (521 - j) := by
    rw [tk.gpr (by decide), kv.gpr (by decide), I.cnt]
  apply WP.seq
  refine WP.mono (Q := fun (w : State) => w.gpr .a1 = S + BitVec.ofNat 64 (sOff (j + 1)) ∧ w.mem = t.mem ∧
      Keep [.a1] t w) ?_ fun w ⟨w16, wm, wk⟩ => ?_
  · refine WP.ite (decide ((sOff j + 2) % 256 = 0)) (by show isa.eval (.zero .t4) t = _; rw [Steps.eval_zero, t12, shl56_beq (by omega)])
      (fun h => ?_) (fun h => ?_)
    · have h' : (sOff j + 2) % 256 = 0 := by simpa using h
      refine WP.mono (WP.keep [.a1] (Q := fun (w : State) =>
        w.gpr .a1 = S + BitVec.ofNat 64 (sOff (j + 1)) ∧ w.mem = t.mem) ?_ (by decide) rfl)
        fun w ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
      brun [t16]
      rw [show (768#64 : BitVec 64) = BitVec.ofNat 64 768 from rfl, Offset.add_add, sOff_succ h9,
        ite_eq_left h']
    · have h' : ¬ (sOff j + 2) % 256 = 0 := by simpa using h
      exact WP.block_nil ⟨by rw [t16, sOff_succ h9, ite_eq_right h'], rfl, Keep.refl _ _⟩
  · have Kw : Keep encRegs s₀ w := (Kt.trans wk).mono (by decide)
    refine WP.mono (WP.keep [.a0] (Q := fun x => x.gpr .a0 = BitVec.ofNat 64 (521 - (j + 1)) ∧
        x.mem = w.mem) ?_ (by decide) rfl) fun x ⟨⟨x17, xm⟩, xk⟩ => ?_
    · brun [wk.gpr (show Reg.a0 ∉ [Reg.a1] by decide), h17]
      apply BitVec.eq_of_toNat_eq; simp; omega
    refine ⟨⟨⟨by rw [xm, wm]; exact hsch, ?_, (Kw.trans xk).mono (by decide), by rw [xm, wm]; exact hfr⟩,
      by omega, by omega, by rw [xk.gpr (by decide)]; exact w16, x17⟩, x17⟩
    rw [xk.gpr (by decide), xk.gpr (by decide), wk.gpr (by decide), wk.gpr (by decide)]
    exact hhalf

theorem encryptS_run {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀) {u : State}
    (I : PInv key S s₀ 9 u) :
    WP isa encryptS u (SInv key S s₀ 521) := by
  unfold encryptS
  apply WP.seq
  refine WP.mono (WP.keep [.a1, .a0] (Q := fun t => t.gpr .a1 = S ∧
      t.gpr .a0 = BitVec.ofNat 64 512 ∧ t.mem = u.mem)
    (by brun [I.keep.gpr (show Reg.a7 ∉ encRegs by decide), E.sch, BitVec.or_self]) (by decide) rfl)
    fun t ⟨⟨a, b, c⟩, k⟩ => ?_
  have I₀ : SInv key S s₀ 9 t :=
    ⟨⟨by rw [c]; exact I.sched, by rw [k.gpr (by decide), k.gpr (by decide)]; exact I.halves,
      (I.keep.trans k).mono (by decide), by rw [c]; exact I.frame⟩, by omega, by omega,
      by rw [a]; simp [sOff, sDone], b⟩
  refine WP.loop (M := isa) (fun m v => ∃ j, 9 ≤ j ∧ j < 521 ∧ m = 521 - j ∧ SInv key S s₀ j v)
    ?_ 512 t ⟨9, by omega, by omega, rfl, I₀⟩
  intro m v ⟨j, hj9, hj, hm, J⟩
  refine WP.mono (encS_step E hj J) fun v' ⟨J', z'⟩ => ?_
  rw [Steps.eval_nonzero_ofNat _ _ (by omega) z']
  by_cases h : j + 1 = 521
  · left; exact ⟨by simp [h], h ▸ J'⟩
  · right
    exact ⟨by simp; omega, 521 - (j + 1), by omega, j + 1, by omega, by omega, rfl, J'⟩

end VG.Proof.Blowfish.RISCV64
