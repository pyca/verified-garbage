module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Cipher
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Blowfish on PPC64LE: ECB

`ecb_wp`: every block becomes its encryption or decryption, one at a time;
our caller's `r14`–`r17` are saved in the working space and restored.
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE VG.Spec.Blowfish VG.Proof.Blowfish

/-! ## Blocks in and out of the halves -/

theorem rev32_byte (x : BitVec 32) {b : Nat} (hb : b < 4) :
    (rev32 x).extractLsb' (8 * b) 8 = x.extractLsb' (8 * (3 - b)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [rev32, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, BitVec.getLsbD_append]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) [ite_eq_left, ite_eq_right, show i < 8 from hi] <;>
    rw [decide_eq_true (by omega), Bool.true_and] <;> congr 1 <;> omega

/-- The big-endian word at offset `o` of the block at `q`. -/
theorem rev_load (m : Mem) (q : Addr) {o : Nat} (ho : o ≤ 4) :
    rev32 (m.readW (q + BitVec.ofNat 64 o) 32) = decodeWord (blockAt m q) o := by
  refine word_ext fun b hb => ?_
  rw [rev32_byte _ hb, decodeWord_byte _ _ hb, blockAt_getD _ _ (by omega),
    ← Mem.readW_byte m _ (by omega), Offset.add_add]

/-- The block at `r16` into the halves, as big-endian words. -/
theorem loadBlock_run (u : State) {q : Addr} (hq : u.gpr .r16 = q) (h0 : u.gpr .r0 = 0#64)
    (r0 : InRegions (u.rd ++ u.wr) q 4) (r4 : InRegions (u.rd ++ u.wr) (q + BitVec.ofNat 64 4) 4) :
    WP isa (.block loadBlock) u fun t =>
      lo (t.gpr .r4) = decodeWord (blockAt u.mem q) 0 ∧ lo (t.gpr .r5) = decodeWord (blockAt u.mem q) 4 ∧
        t.mem = u.mem := by
  have l0 := rev_load u.mem q (o := 0) (by decide)
  have l4 := rev_load u.mem q (o := 4) (by decide)
  rw [BitVec.add_zero] at l0
  unfold loadBlock
  brun [hq, h0, r0, r4, addrX, lo_ext, l0, l4]

theorem st_byte (m : Mem) (a : Addr) (v : BitVec 32) {t : Nat} (ht : t < 4) :
    m.writeW a v (a + BitVec.ofNat 64 t) = v.extractLsb' (8 * t) 8 := by
  rw [Mem.readW_byte (m.writeW a v) a ht, Mem.readW_writeW_self32]

theorem writeW32_other {m : Mem} {a x : Addr} (v : BitVec 32) (h : Region.Disjoint ⟨x, 1⟩ ⟨a, 4⟩) :
    m.writeW a v x = m x :=
  Mem.write_apply fun h' => h x (Region.contains_self _ _) ((Region.contains_self a 4).byte h')

/-- The halves to the block at `r16`, the next block's pointer, and the
counter less one. -/
theorem storeBlock_run (u : State) {q : Addr} (hq : u.gpr .r16 = q) (h0 : u.gpr .r0 = 0#64)
    (w0 : InRegions u.wr q 4) (w4 : InRegions u.wr (q + BitVec.ofNat 64 4) 4) :
    WP isa (.block storeBlock) u fun t =>
      t.mem = (u.mem.writeW q (rev32 (lo (u.gpr .r4)))).writeW (q + BitVec.ofNat 64 4)
        (rev32 (lo (u.gpr .r5))) ∧
      t.gpr .r16 = q + 8#64 ∧ t.gpr .r17 = u.gpr .r17 - 1#64 ∧ Keep [.r12, .r16, .r17] u t := by
  refine WP.mono (WP.keep [.r12, .r16, .r17] (Q := fun t =>
      t.mem = (u.mem.writeW q (rev32 (lo (u.gpr .r4)))).writeW (q + BitVec.ofNat 64 4)
        (rev32 (lo (u.gpr .r5))) ∧ t.gpr .r16 = q + 8#64 ∧ t.gpr .r17 = u.gpr .r17 - 1#64) ?_
    (by decide) rfl) fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  unfold storeBlock
  brun [hq, h0, w0, w4, addrX]

/-- What the stores leave: the block. -/
theorem stored_block (m : Mem) (q : Addr) (L R : BitVec 32) :
    blockAt ((m.writeW q (rev32 L)).writeW (q + BitVec.ofNat 64 4) (rev32 R)) q = encodeBlock L R := by
  refine blockAt_eq _ _ _ fun i hi => ?_
  rw [encodeBlock_getD _ _ hi]
  by_cases h4 : i < 4
  · rw [ite_eq_left h4, writeW32_other _ (Offset.disjoint q (d := i) (n := 1) (e := 4) (k := 4) (by omega)
      (by omega) (by decide)), st_byte _ _ _ h4, rev32_byte _ h4]
  · rw [ite_eq_right h4, show i = 4 + (i - 4) by omega, ← Offset.add_add, st_byte _ _ _ (by omega),
      rev32_byte _ (by omega)]
    congr 2; omega

theorem stored_frame (m : Mem) (q : Addr) (L R : BitVec 32) :
    Frame [⟨q, 8⟩] m ((m.writeW q (rev32 L)).writeW (q + BitVec.ofNat 64 4) (rev32 R)) := by
  have c0 : Region.Contains ⟨q, 8⟩ q (32 / 8) := by
    have := Offset.contains_base q (d := 0) (n := 4) (k := 8) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  have c4 : Region.Contains ⟨q, 8⟩ (q + BitVec.ofNat 64 4) (32 / 8) :=
    Offset.contains_base q (by decide) (by decide)
  exact ((Frame.refl _ m).writeW List.mem_cons_self _ c0).writeW List.mem_cons_self _ c4

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 8⟩) hd (by show 8 ≤ 2 ^ 64; decide) hi

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

/-- The registers the loop writes. -/
def loopRegs : List Reg := [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17]

/-- The loop's fixed facts, about the state `s₀` before it. -/
structure LoopEnv (S D : Addr) (n : Nat) (s₀ : State) : Prop where
  r3 : s₀.gpr .r3 = S
  r0 : s₀.gpr .r0 = 0#64
  key : (⟨S, 4168⟩ : Region) ∈ s₀.rd ++ s₀.wr
  data : (⟨D, 8 * n⟩ : Region) ∈ s₀.wr
  keyData : (⟨S, 4168⟩ : Region).Disjoint ⟨D, 8 * n⟩
  fit : D.toNat + 8 * n ≤ 2 ^ 64

/-- After `k` blocks. -/
structure EInv (S D : Addr) (n : Nat) (up : Bool) (s₀ : State) (k : Nat) (u : State) : Prop where
  le : k ≤ n
  ptr : u.gpr .r16 = wAt D k
  cnt : u.gpr .r17 = BitVec.ofNat 64 (n - k)
  keep : Keep loopRegs s₀ u
  done : ∀ b < k, blockAt u.mem (wAt D b) = blockOut (scheduleAt s₀.mem S) up (blockAt s₀.mem (wAt D b))
  rest : ∀ b, k ≤ b → b < n → blockAt u.mem (wAt D b) = blockAt s₀.mem (wAt D b)
  frame : Frame [⟨D, 8 * n⟩] s₀.mem u.mem

theorem ecb_step {S D : Addr} {n : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D n s₀) {k : Nat}
    (hk : k < n) {u : State} (I : EInv S D n up s₀ k u) :
    WP isa (.seq (.block loadBlock) (.seq (cipher up) (.block storeBlock))) u
      (fun u' => EInv S D n up s₀ (k + 1) u' ∧ u'.gpr .r17 = BitVec.ofNat 64 (n - (k + 1))) := by
  have fit := L.fit
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [I.keep.2.1, I.keep.2.2]
  have dR : (⟨D, 8 * n⟩ : Region) ∈ u.wr := by rw [I.keep.2.2]; exact L.data
  have inD : ∀ o, o + 4 ≤ 8 → InRegions u.wr (wAt D k + BitVec.ofNat 64 o) 4 := fun o ho =>
    ⟨_, dR, by rw [Offset.add_add]; exact Offset.contains_base D (by omega) (by omega)⟩
  have inD' : ∀ o, o + 4 ≤ 8 → InRegions (u.rd ++ u.wr) (wAt D k + BitVec.ofNat 64 o) 4 := fun o ho =>
    let ⟨r, hr, hc⟩ := inD o ho; ⟨r, List.mem_append_right _ hr, hc⟩
  have u0 : u.gpr .r0 = 0#64 := by rw [I.keep.gpr (by decide)]; exact L.r0
  have i0 := inD' 0 (by decide)
  rw [BitVec.add_zero] at i0
  apply WP.seq
  refine WP.mono (WP.keep [.r4, .r5, .r12] (loadBlock_run u I.ptr u0 i0 (inD' 4 (by decide)))
    (by decide) rfl) fun u₁ ⟨⟨l₁, h₁, m₁⟩, k₁⟩ => ?_
  have hK : scheduleAt u.mem S = scheduleAt s₀.mem S :=
    scheduleAt_eq_of_frame S I.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.keyData
  have Ku₁ : Keep loopRegs s₀ u₁ := (I.keep.trans k₁).mono (by decide)
  have E : LookEnv u₁ := by
    refine ⟨fun o ho => ?_, by rw [Ku₁.gpr (by decide)]; exact L.r0⟩
    rw [Ku₁.gpr (by decide), L.r3, Ku₁.2.1, Ku₁.2.2]
    exact ⟨_, L.key, Offset.contains_base S ho (by omega)⟩
  apply WP.seq
  refine WP.mono (cipher_run E up) fun u₂ ⟨c₂, k₂, m₂⟩ => ?_
  have Ku₂ : Keep loopRegs s₀ u₂ := (Ku₁.trans k₂).mono (by decide)
  have wr₂ : u₂.wr = u.wr := by rw [k₂.2.2, k₁.2.2]
  have p₂ : u₂.gpr .r16 = wAt D k := by rw [k₂.gpr (by decide), k₁.gpr (by decide), I.ptr]
  have z₂ : u₂.gpr .r0 = 0#64 := by rw [Ku₂.gpr (by decide)]; exact L.r0
  have w0 := inD 0 (by decide)
  rw [BitVec.add_zero] at w0
  refine WP.mono (storeBlock_run u₂ p₂ z₂ (by rw [wr₂]; exact w0) (by rw [wr₂]; exact inD 4 (by decide)))
    fun u₃ ⟨m₃, p₃, c₃, k₃⟩ => ?_
  have subK : Region.Sub ⟨wAt D k, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega)
  have hc₂ : u₂.gpr .r17 = BitVec.ofNat 64 (n - k) := by
    rw [k₂.gpr (by decide), k₁.gpr (by decide), I.cnt]
  have other : ∀ b, b < n → b ≠ k → blockAt u₃.mem (wAt D b) = blockAt u.mem (wAt D b) := fun b hb hne => by
    rw [m₃, blockAt_frame (stored_frame _ _ _ _) fun r hr => ?_, m₂, m₁]
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint D (by omega) (by omega) (by omega)
  have c₃' : u₃.gpr .r17 = BitVec.ofNat 64 (n - (k + 1)) := by
    rw [c₃, hc₂]; apply BitVec.eq_of_toNat_eq; simp; omega
  refine ⟨⟨by omega, ?_, c₃', (Ku₂.trans k₃).mono (by decide), fun b hb => ?_, fun b h1 h2 => ?_, ?_⟩, c₃'⟩
  · rw [p₃, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, wAt, wAt, Offset.add_add]
    congr 2
  · by_cases hbk : b = k
    · subst hbk
      have e1 := congrArg Prod.fst c₂
      have e2 := congrArg Prod.snd c₂
      simp only at e1 e2
      rw [m₃, stored_block, e1, e2, l₁, h₁, m₁, Ku₁.gpr (by decide), L.r3, hK, I.rest b (by omega) hk,
        blockOut_eq]
    · rw [other b (by omega) hbk]; exact I.done b (by omega)
  · rw [other b h2 (by omega)]; exact I.rest b (by omega) h2
  · rw [m₃]
    refine I.frame.trans ?_
    rw [← m₁, ← m₂]
    exact (stored_frame _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, subK⟩

theorem loop_run {S D : Addr} {n : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D n s₀) (hn : 0 < n)
    {u : State} (I : EInv S D n up s₀ 0 u) :
    WP isa (.loop (.seq (.block loadBlock) (.seq (cipher up) (.block storeBlock))) (.nonzero .d cnt)) u
      (EInv S D n up s₀ n) := by
  refine WP.loop (M := isa) (Q := EInv S D n up s₀ n)
    (fun m v => ∃ k, k < n ∧ m = n - k ∧ EInv S D n up s₀ k v) ?_ n u ⟨0, hn, rfl, I⟩
  intro m v ⟨k, hk, hm, J⟩
  refine WP.mono (ecb_step L hk J) fun v' ⟨J', hz⟩ => ?_
  have hn64 : n < 2 ^ 64 := by have := L.fit; omega
  rw [cnt, eval_nonzero, hz, ofNat_bne_zero (by omega)]
  by_cases e : k + 1 = n
  · left
    exact ⟨by simp [e], e ▸ J'⟩
  · right
    exact ⟨by simp; omega, n - (k + 1), by omega, k + 1, by omega, rfl, J'⟩

/-! ## The function -/

theorem save_eq : save = Spill.saveCode .r6 saved := rfl
theorem restore_eq : restore = Spill.restoreCode .r6 saved := rfl
theorem saved_fits : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide
theorem saved_lt : ∀ p ∈ saved, p.2 + 8 ≤ 32 := by decide

/-- What ECB may assume: the schedule readable, the `n` blocks and the
working space writable, apart, the blocks not wrapping around. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r3, 4168⟩]
  wr : s.wr = [⟨s.gpr .r4, 8 * (s.gpr .r5).toNat⟩, ⟨s.gpr .r6, 256⟩]
  keyData : (⟨s.gpr .r3, 4168⟩ : Region).Disjoint ⟨s.gpr .r4, 8 * (s.gpr .r5).toNat⟩
  keyBuf : (⟨s.gpr .r3, 4168⟩ : Region).Disjoint ⟨s.gpr .r6, 256⟩
  dataBuf : (⟨s.gpr .r4, 8 * (s.gpr .r5).toNat⟩ : Region).Disjoint ⟨s.gpr .r6, 256⟩
  fit : (s.gpr .r4).toNat + 8 * (s.gpr .r5).toNat ≤ 2 ^ 64

/-- What ECB guarantees. -/
structure EcbPost (up : Bool) (s s' : State) : Prop where
  done : ∀ b < (s.gpr .r5).toNat, blockAt s'.mem (wAt (s.gpr .r4) b) =
    blockOut (scheduleAt s.mem (s.gpr .r3)) up (blockAt s.mem (wAt (s.gpr .r4) b))
  saved : ∀ r ∈ saved.map Prod.fst, s'.gpr r = s.gpr r

theorem ecb_wp (up : Bool) {s : State} (h : EcbPre s) :
    WP isa (Impl.Blowfish.PPC64LE.ecb up) s (EcbPost up s) := by
  have fit := h.fit
  have bR : (⟨s.gpr .r6, 256⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  have slot : ∀ p ∈ saved, Region.Sub ⟨s.gpr .r6 + BitVec.ofNat 64 p.2, 8⟩ ⟨s.gpr .r6, 256⟩ := fun p hp =>
    Offset.sub_base _ (by have := saved_lt p hp; omega)
  unfold Impl.Blowfish.PPC64LE.ecb
  apply WP.seq
  rw [save_eq]
  refine Spill.save_ok (by decide) saved_fits (fun p hp =>
    ⟨_, bR, Offset.contains_base _ (by have := saved_lt p hp; omega) (by have := saved_lt p hp; omega)⟩) ?_
  let M₀ := Spill.saveMem s.mem (s.gpr .r6) s.gpr saved
  refine WP.mono (WP.keep [.r0, .r16, .r17] (Q := fun t => t.gpr .r0 = 0#64 ∧ t.gpr .r16 = s.gpr .r4 ∧
      t.gpr .r17 = s.gpr .r5 ∧ t.mem = M₀) (by brun [BitVec.or_self]; rfl) (by decide) rfl)
    fun s₀ ⟨⟨z₀, p₀, c₀, m₀⟩, k₀⟩ => ?_
  have F₀ : Frame [⟨s.gpr .r6, 32⟩] s.mem M₀ :=
    Spill.saveMem_frame_base (fun p hp => saved_lt p hp) (by decide) _ _ _
  have r₀ : s₀.rd = s.rd ∧ s₀.wr = s.wr := ⟨k₀.2.1, k₀.2.2⟩
  have sub32 : Region.Sub ⟨s.gpr .r6, 32⟩ ⟨s.gpr .r6, 256⟩ := Region.sub_prefix (by decide)
  have L : LoopEnv (s.gpr .r3) (s.gpr .r4) (s.gpr .r5).toNat s₀ := by
    refine ⟨by rw [k₀.gpr (by decide)], z₀, ?_, ?_, h.keyData, fit⟩
    · rw [r₀.1, r₀.2, h.rd]; simp
    · rw [r₀.2, h.wr]; simp
  have I0 : EInv (s.gpr .r3) (s.gpr .r4) (s.gpr .r5).toNat up s₀ 0 s₀ :=
    ⟨by omega, by rw [p₀]; simp [wAt], by rw [c₀]; simp, Keep.refl _ _, fun b hb => absurd hb (by omega),
      fun _ _ _ => rfl, Frame.refl _ _⟩
  apply WP.seq
  refine WP.mono (Q := EInv (s.gpr .r3) (s.gpr .r4) (s.gpr .r5).toNat up s₀ (s.gpr .r5).toNat) ?_
    fun u U => ?_
  · refine WP.ite (s.gpr .r5 == 0#64) (by rw [cnt, eval_zero, c₀]) (fun hz => ?_) (fun hz => ?_)
    · have hn : (s.gpr .r5).toNat = 0 := by simp only [beq_iff_eq] at hz; simp [hz]
      exact WP.block_nil (hn ▸ I0)
    · have hn : 0 < (s.gpr .r5).toNat := by
        have : s.gpr .r5 ≠ 0#64 := by simpa using hz
        have : (s.gpr .r5).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
        omega
      exact loop_run L hn I0
  · rw [restore_eq]
    have r6 : u.gpr .r6 = s.gpr .r6 := by rw [U.keep.gpr (by decide), k₀.gpr (by decide)]
    have hsv : Spill.Saved (s.gpr .r6) s.gpr saved u.mem := by
      have : Spill.Saved (s.gpr .r6) s.gpr saved s₀.mem := by
        rw [m₀]; exact Spill.saveMem_saved (by decide) s.mem (s.gpr .r6) s.gpr
      exact this.frame U.frame fun p hp r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.dataBuf.symm.sub_left (slot p hp))
    refine WP.mono (Spill.restore_wp (by decide) r6 saved_fits (by decide) (fun p hp => ?_) hsv)
      fun s' R => ⟨fun b hb => ?_, fun r hr => ?_⟩
    · rw [U.keep.2.1, U.keep.2.2, r₀.1, r₀.2]
      exact ⟨_, List.mem_append_right _ bR, Offset.contains_base _ (by have := saved_lt p hp; omega)
        (by have := saved_lt p hp; omega)⟩
    · have dK : ∀ r ∈ [(⟨s.gpr .r6, 32⟩ : Region)], (⟨s.gpr .r3, 4168⟩ : Region).Disjoint r := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.keyBuf.sub_right sub32
      have dB : ∀ r ∈ [(⟨s.gpr .r6, 32⟩ : Region)], (⟨wAt (s.gpr .r4) b, 8⟩ : Region).Disjoint r :=
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (h.dataBuf.sub_left (Offset.sub_base _ (by omega))).sub_right sub32
      rw [R.mem, U.done b hb, m₀, scheduleAt_eq_of_frame _ F₀ dK, blockAt_frame F₀ dB]
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
      exact R.gpr p hp

end VG.Proof.Blowfish.PPC64LE
