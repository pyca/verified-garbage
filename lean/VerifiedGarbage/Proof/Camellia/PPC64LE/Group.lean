module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.Prologue
public import VerifiedGarbage.Proof.Camellia.Common
public import VerifiedGarbage.Proof.Camellia.PPC64LE.Keys
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Camellia.PPC64LE.Copy
import VerifiedGarbage.Proof.Camellia.PPC64LE.Crypt8
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# A group of blocks of Camellia ECB on PPC64LE

`dataGroup_wp`: one iteration of the data loop copies the group's blocks
(eight, or the last one to seven) to the tail buffer, transforms it
(`crypt8_ok`, which keeps the data pointer, the blocks left and the
postwhitening's address in `r5`–`r7`), copies the blocks back and steps to
the next group.
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.Camellia.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 kp movR ldS stS shrI)

/-! ## Small blocks -/

theorem lsr3_beq {v : Nat} (hv : v < 2 ^ 64) : (BitVec.ofNat 64 v >>> 3 == 0) = decide (v < 8) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow] at this
    simp at this
    omega_arith
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow]
    simp
    omega_arith

/-- `r12 := min(r6, 8)`. -/
theorem groupCount_wp {s : State} {v : Nat} (hr : s.gpr .r6 = BitVec.ofNat 64 v) (hv : v < 2 ^ 64) :
    WP isa groupCount s fun s' => s'.gpr .r12 = BitVec.ofNat 64 (min v 8) ∧
      (∀ r, r ≠ .r12 → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write t0 (s.gpr .r6 >>> 3)
  have e₁ : runBlock isa [shrI t0 .r6 3] s = some s₁ := by
    simp only [shrI, runBlock_cons, runStep_some, runBlock_nil, exec_lsr_d (show 3 < 64 by decide)]; rfl
  have t₁ : s₁.gpr t0 = BitVec.ofNat 64 v >>> 3 := by
    rw [RegUpd.gpr_write_self, hr]
  have o₁ : ∀ r, r ≠ t0 → s₁.gpr r = s.gpr r := fun r hr => RegUpd.gpr_write_of_ne _ _ hr
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.ite (decide (8 ≤ v)) ((eval_nonzero s₁ t0).trans (by rw [t₁, lsr3_beq hv]; by_cases h : v < 8 <;> simp [h] <;> omega_arith))
    (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := li_ok s₁ .r12 (v := 8) (by decide)
    refine WP.of_runBlock ⟨s₂, e₂, ?_, fun r h1 h2 => by rw [o₂ r h1, o₁ r h2], m₂, rd₂, wr₂⟩
    rw [r₂, Nat.min_eq_right (by simp at h; omega_arith)]
  · obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ .r12 .r6
    refine WP.of_runBlock ⟨s₂, e₂, ?_, fun r h1 h2 => by rw [o₂ r h1, o₁ r h2], m₂, rd₂, wr₂⟩
    rw [r₂, o₁ _ (by decide), hr, Nat.min_eq_left (by simp at h; omega_arith)]

/-- `tailAddr r`. -/
theorem tailAddr_ok (s : State) (r : Reg) :
    ∃ s', runBlock isa (tailAddr r) s = some s' ∧ s'.gpr r = s.gpr sb + BitVec.ofNat 64 (8 * tailSlot) ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  addI_ok s r sb (imm := 8 * tailSlot) (by decide)

/-! ## The scratch buffer's contents -/

/-- The masks, in the memory at `b`. -/
def MasksAt (m : Mem) (b : Addr) : Prop := ∀ kv ∈ layerMasks, m.readW (wordAddr b kv.1) 64 = kv.2

theorem MasksOk.at {s : State} {b : Addr} (h : MasksOk s) (hb : s.gpr sb = b) : MasksAt s.mem b :=
  fun kv hkv => by rw [← hb]; exact h kv hkv

theorem MasksAt.ok {s : State} {b : Addr} (h : MasksAt s.mem b) (hb : s.gpr sb = b) : MasksOk s :=
  fun kv hkv => by show s.mem.readW (wordAddr (s.gpr sb) kv.1) 64 = kv.2; rw [hb]; exact h kv hkv

/-- What the data loop keeps in the scratch buffer: the masks, the table and
the saved registers. -/
structure ScrOk (s₀ : State) (b : Addr) (g : Nat) (E : Nat → BitVec 64) (m : Mem) : Prop where
  masks : MasksAt m b
  keys : ∀ i < 8 * g + 2, EntryOk m b i (E i)
  saved : Saved s₀ b m

/-- The slots `ScrOk` reads: 48–52, 96–367 and 368–377. -/
abbrev scrRegions (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 (8 * 48), 40⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot), 8 * 272⟩,
    ⟨b + BitVec.ofNat 64 (8 * savedSlot), 144⟩]

theorem ScrOk.frame {s₀ : State} {b : Addr} {g : Nat} {E : Nat → BitVec 64} {m m' : Mem}
    (h : ScrOk s₀ b g E m) (hg : g ≤ 4) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ t ∈ scrRegions b, ∀ r ∈ rs, Region.Disjoint t r) :
    ScrOk s₀ b g E m' := by
  have hR : ∀ t ∈ scrRegions b, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
      m'.readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 := fun t ht d hs =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd _ ht r hr).sub_left hs) (by decide)
  refine ⟨fun kv hkv => ?_, fun i hi => (h.keys i hi).congr fun j hj => ?_, fun i hi => ?_⟩
  · have hk : 48 ≤ kv.1 ∧ kv.1 < 53 := by
      simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
        simp [evenSlot, oddSlot, m4Slot, m2Slot, m3Slot]
    rw [← h.masks kv hkv]
    exact hR _ List.mem_cons_self (8 * kv.1) (VG.Offset.sub b (by omega_arith) (by omega_arith))
  · exact hR _ (List.mem_cons_of_mem _ List.mem_cons_self) (8 * keySlot + 64 * i + 8 * j)
      (VG.Offset.sub b (by omega_arith) (by rw [keySlot_eq]; omega_arith))
  · rw [← h.saved i hi]
    exact hR _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (8 * (savedSlot + i))
      (VG.Offset.sub b (by omega_arith) (by omega_arith))

theorem ScrOk.frame2 {s₀ : State} {b : Addr} {g : Nat} {E : Nat → BitVec 64} {m m' : Mem}
    (h : ScrOk s₀ b g E m) (hg : g ≤ 4) {rs : List Region} (hf : Frame rs m m') (hm : MasksAt m' b)
    (hd : ∀ t ∈ (scrRegions b).tail, ∀ r ∈ rs, Region.Disjoint t r) : ScrOk s₀ b g E m' := by
  have hR : ∀ t ∈ (scrRegions b).tail, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
      m'.readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 := fun t ht d hs =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd _ ht r hr).sub_left hs) (by decide)
  refine ⟨hm, fun i hi => (h.keys i hi).congr fun j hj => ?_, fun i hi => ?_⟩
  · exact hR _ List.mem_cons_self (8 * keySlot + 64 * i + 8 * j)
      (VG.Offset.sub b (by omega_arith) (by rw [keySlot_eq]; omega_arith))
  · rw [← h.saved i hi]
    exact hR _ (List.mem_cons_of_mem _ List.mem_cons_self) (8 * (savedSlot + i))
      (VG.Offset.sub b (by omega_arith) (by omega_arith))

/-! ## The data loop -/

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure GPre (s₀ : State) (b D : Addr) (n g : Nat) : Prop where
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 8 * slots⟩
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  fitD : D.toNat + 16 * n ≤ 2 ^ 64
  hg : g = 3 ∨ g = 4

/-- `copyBlocks` from `r9` to `r10`, `r11` blocks, set up. -/
theorem copy_wp {s : State} {X Y : Addr} {c : Nat} (hc : 0 < c) (hc8 : c ≤ 8)
    (hx : s.gpr .r9 = X) (hy : s.gpr .r10 = Y) (hcx : s.gpr .r11 = BitVec.ofNat 64 c)
    (hX : ∀ t < 2 * c, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (8 * t)) 8)
    (hY : ∀ t < 2 * c, InRegions s.wr (Y + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨X, 16 * c⟩ ⟨Y, 16 * c⟩) :
    WP isa copyBlocks s fun s' => (∀ t < 16 * c, s'.mem (Y + BitVec.ofNat 64 t) = s.mem (X + BitVec.ofNat 64 t)) ∧
      Frame [⟨Y, 16 * c⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (copyBlocks_wp hc hc8 hX hY hsep ⟨by rw [hx]; simp, by rw [hy]; simp, by rw [hcx, Nat.sub_zero],
    fun t ht => by omega_arith, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩)
    fun s' h => ⟨h.copied, h.frame, h.regs, h.rd, h.wr⟩

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : Addr) (n g : Nat) (E : Nat → BitVec 64) (k : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  r5 : s.gpr .r5 = D + BitVec.ofNat 64 (128 * k)
  r6 : s.gpr .r6 = BitVec.ofNat 64 (n - 8 * k)
  lt : 8 * k < n
  r7 : s.gpr .r7 = b + BitVec.ofNat 64 (8 * keySlot + 512 * g)
  scr : ScrOk s₀ b g E s.mem
  data : DInv s₀.mem s.mem D n (8 * k) (outF s₀.mem D g E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : Addr) (n g : Nat) (E : Nat → BitVec 64) (s : State) : Prop where
  base : s.gpr sb = b
  scr : ScrOk s₀ b g E s.mem
  data : DInv s₀.mem s.mem D n n (outF s₀.mem D g E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

theorem dataGroup_wp {s₀ : State} {b D : Addr} {n g : Nat} {E : Nat → BitVec 64} (hp : GPre s₀ b D n g)
    {k : Nat} {s : State} (hi : GInv s₀ b D n g E k s) :
    WP isa Impl.Camellia.PPC64LE.group s fun s' => (s'.gpr .r6 = 0 ∧ GDone s₀ b D n g E s') ∨
      (s'.gpr .r6 ≠ 0 ∧ GInv s₀ b D n g E (k + 1) s') := by
  have hfit := hp.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  have hg4 : g ≤ 4 := by rcases hp.hg with h | h <;> omega_arith
  rw [slots_eq] at hfit
  let v := n - 8 * k
  let c := min v 8
  have hv : v < 2 ^ 64 := by omega_arith
  have hc0 : 0 < c := by omega_arith
  have hc8 : c ≤ 8 := by omega_arith
  have hkc : 128 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 64 (128 * k)
  let T := b + BitVec.ofNat 64 (8 * tailSlot)
  have hwS : (⟨b, 8 * slots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have inT : ∀ t, t < 16 → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwS, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base b (by rw [slots_eq, tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  have inA : ∀ t, t < 2 * c → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega_arith) (by omega_arith)
  have sepAT : Region.Disjoint ⟨A, 16 * c⟩ ⟨T, 16 * c⟩ :=
    (hp.sep.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right
      (VG.Offset.sub_base b (by rw [slots_eq, tailSlot_eq]; omega_arith))
  unfold Impl.Camellia.PPC64LE.group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.r6 hv) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a⟩ := movR_ok s₁ .r9 .r5
  obtain ⟨s₂b, e₂b, r₂b, o₂b, m₂b, rd₂b, wr₂b⟩ := tailAddr_ok s₂a .r10
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₂b .r11 .r12
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂b, rd₂a, rd₁]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂b, wr₂a, wr₁]
  have mem₂ : s₂.mem = s.mem := by rw [m₂, m₂b, m₂a, m₁]
  have g₂ : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → r ≠ t0 → s₂.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₂ r h3, o₂b r h2, o₂a r h1, o₁ r h4 h5]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [runBlock_append', runBlock_append', e₂a, Option.bind_some, e₂b, Option.bind_some, e₂], ?_⟩)
  refine WP.mono (copy_wp (X := A) (Y := T) hc0 hc8
    (by rw [o₂ _ (by decide), o₂b _ (by decide), r₂a, o₁ _ (by decide) (by decide), hi.r5])
    (by rw [o₂ _ (by decide), r₂b, o₂a _ (by decide), o₁ _ (by decide) (by decide), hi.base])
    (by rw [r₂, o₂b _ (by decide), o₂a _ (by decide), c₁])
    (fun t ht => by rw [rd₂', wr₂']; exact inRd (inA t ht))
    (fun t ht => by rw [wr₂']; exact inT t (by omega_arith)) sepAT) fun s₃ ⟨cp₃, f₃, g₃, rd₃, wr₃⟩ => ?_
  have f₃' : Frame [⟨T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact f₃
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂']
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂']
  have g₃' : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → r ≠ t0 → s₃.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [g₃ r h1 h2 h3 h5, g₂ r h1 h2 h3 h4 h5]
  have base₃ : s₃.gpr sb = b := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.base]
  have sc₃ : ScrOk s₀ b g E s₃.mem := by
    refine hi.scr.frame hg4 (mem₂ ▸ f₃) fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> refine VG.Offset.disjoint b (Or.inl ?_) ?_ ?_ <;>
      (try simp only [tailSlot_eq, keySlot_eq, savedSlot_eq]) <;> omega_arith
  -- The eight blocks.
  have hcore : CorePre s₃ g E :=
    { scr := by rw [base₃, wr₃']; exact hwS
      fit := by rw [base₃, slots_eq]; exact hfit
      hg := hp.hg
      nk34 := by rcases hp.hg with h | h <;> omega_arith
      masks := sc₃.masks.ok base₃
      bound := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.r7, base₃]
      keys := fun i hi' => by rw [base₃]; exact sc₃.keys i hi' }
  refine WP.seq (WP.mono (crypt8_ok hcore) fun s₅ ⟨c₅, b₅⟩ => ?_)
  have base₅ : s₅.gpr sb = b := by rw [c₅.base, base₃]
  have f₅ : Frame [⟨b, 8 * keySlot⟩, ⟨T, 128⟩] s₃.mem s₅.mem := by
    have := c₅.frame; rw [ctxRegions, base₃] at this; exact this
  have hT : T = b + BitVec.ofNat 64 (8 * tailSlot) := rfl
  have sc₅ : ScrOk s₀ b g E s₅.mem := by
    refine sc₃.frame2 hg4 f₅ (c₅.masks.at base₅) fun t ht r hr => ?_
    simp only [scrRegions, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at ht hr
    rcases ht with rfl | rfl <;> rcases hr with rfl | rfl
    · exact VG.Offset.disjoint_base b (by rw [keySlot_eq]) (by rw [keySlot_eq] <;> omega_arith)
    · rw [hT]; exact VG.Offset.disjoint b (Or.inl (by rw [keySlot_eq, tailSlot_eq] <;> omega_arith))
        (by rw [keySlot_eq] <;> omega_arith) (by rw [tailSlot_eq] <;> omega_arith)
    · exact VG.Offset.disjoint_base b (by rw [keySlot_eq, savedSlot_eq] <;> omega_arith) (by rw [savedSlot_eq] <;> omega_arith)
    · rw [hT]; exact VG.Offset.disjoint b (Or.inl (by rw [savedSlot_eq, tailSlot_eq]))
        (by rw [savedSlot_eq] <;> omega_arith) (by rw [tailSlot_eq] <;> omega_arith)
  have k₅ : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .r3 → s₅.gpr r = s₃.gpr r := fun r h1 h2 h3 => c₅.keep r h1 h2 h3
  have r5₅ : s₅.gpr .r5 = A := by
    rw [k₅ _ (by decide) (by decide) (by decide), g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hi.r5]
  have r6₅ : s₅.gpr .r6 = BitVec.ofNat 64 v := by
    rw [k₅ _ (by decide) (by decide) (by decide), g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hi.r6]
  have r7₅ : s₅.gpr .r7 = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) := by
    rw [k₅ _ (by decide) (by decide) (by decide), g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hi.r7]
  have wr₅' : s₅.wr = s.wr := by rw [c₅.wr, wr₃']
  have rd₅' : s₅.rd = s.rd := by rw [c₅.rd, rd₃']
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp r6₅ hv) fun s₇ ⟨c₇, o₇, m₇, rd₇, wr₇⟩ => ?_))
  obtain ⟨s₈a, e₈a, r₈a, o₈a, m₈a, rd₈a, wr₈a⟩ := tailAddr_ok s₇ .r9
  obtain ⟨s₈b, e₈b, r₈b, o₈b, m₈b, rd₈b, wr₈b⟩ := movR_ok s₈a .r10 .r5
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := movR_ok s₈b .r11 .r12
  refine WP.seq (WP.of_runBlock ⟨s₈, by
    rw [runBlock_append', e₈a, Option.bind_some,
      show ([movR .r10 .r5, movR .r11 .r12] : List Instr) = [movR .r10 .r5] ++ [movR .r11 .r12] from rfl,
      runBlock_append', e₈b, Option.bind_some, e₈], ?_⟩)
  have mem₈ : s₈.mem = s₅.mem := by rw [m₈, m₈b, m₈a, m₇]
  have wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₈b, wr₈a, wr₇, wr₅']
  have rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₈b, rd₈a, rd₇, rd₅']
  have g₈ : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → r ≠ t0 → s₈.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₈ r h3, o₈b r h2, o₈a r h1, o₇ r h4 h5]
  refine WP.mono (copy_wp (X := T) (Y := A) hc0 hc8
    (by rw [o₈ _ (by decide), o₈b _ (by decide), r₈a, o₇ _ (by decide) (by decide), base₅])
    (by rw [o₈ _ (by decide), r₈b, o₈a _ (by decide), o₇ _ (by decide) (by decide), r5₅])
    (by rw [r₈, o₈b _ (by decide), o₈a _ (by decide), c₇])
    (fun t ht => by rw [rd₈', wr₈']; exact inRd (inT t (by omega_arith)))
    (fun t ht => by rw [wr₈']; exact inA t ht) sepAT.symm) fun s₉ ⟨cp₉, f₉, g₉, rd₉, wr₉⟩ => ?_
  have g₉' : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → r ≠ t0 → s₉.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [g₉ r h1 h2 h3 h5, g₈ r h1 h2 h3 h4 h5]
  have r12₉ : s₉.gpr .r12 = BitVec.ofNat 64 c := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide), o₈ _ (by decide), o₈b _ (by decide),
      o₈a _ (by decide), c₇]
  have base₉ : s₉.gpr sb = b := by rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), base₅]
  have r5₉ : s₉.gpr .r5 = A := by rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), r5₅]
  have r6₉ : s₉.gpr .r6 = BitVec.ofNat 64 v := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), r6₅]
  have r7₉ : s₉.gpr .r7 = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), r7₅]
  have wr₉' : s₉.wr = s₀.wr := by rw [wr₉, wr₈', hi.wr]
  have rd₉' : s₉.rd = s₀.rd := by rw [rd₉, rd₈', hi.rd]
  -- The scratch buffer and the frame.
  have subS : ∀ {d l : Nat}, d + l ≤ 8 * slots → Region.Sub ⟨b + BitVec.ofNat 64 d, l⟩ ⟨b, 8 * slots⟩ :=
    fun h => VG.Offset.sub_base b h
  have sc₉ : ScrOk s₀ b g E s₉.mem := by
    refine (mem₈ ▸ sc₅).frame hg4 f₉ fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hsub : Region.Sub t ⟨b, 8 * slots⟩ := by
      simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> refine subS ?_ <;> (try simp only [keySlot_eq, savedSlot_eq]) <;>
        rw [slots_eq] <;> omega_arith
    exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right hsub).symm
  have fr₉ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s.mem s₉.mem := by
    refine (((mem₂ ▸ f₃).sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((f₅.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((mem₈ ▸ f₉).sub fun r hr => ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩)))
    · simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Region.sub_prefix (by rw [slots_eq, keySlot_eq]; omega_arith)
      · exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub_base D (by omega_arith)
  -- The blocks the eight-block code read are the group's, as on entry.
  have hblk : ∀ j < c, blk s₃ j = Spec.Camellia.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * (8 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [blk, Spec.Camellia.blockAt, Vector.getElem_ofFn]
    rw [base₃, addr_add]
    have ht : 16 * j + u < 16 * c := by omega_arith
    have := cp₃ (16 * j + u) ht
    rw [addr_add, show 8 * tailSlot + (16 * j + u) = 8 * tailSlot + 16 * j + u by omega_arith] at this
    rw [this, mem₂, addr_add, hi.data _ (by omega_arith), ite_eq_right (by omega_arith),
      show 128 * k + (16 * j + u) = 16 * (8 * k + j) + u by omega_arith, addr_add]
  have hdata : DInv s₀.mem s₉.mem D n (8 * k + c) (outF s₀.mem D g E) := by
    intro i hin
    by_cases hin1 : 128 * k ≤ i ∧ i < 128 * k + 16 * c
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 128 * k) := by
        rw [addr_add, show 128 * k + (i - 128 * k) = i by omega_arith]
      rw [e1, cp₉ _ (by omega_arith), mem₈, ite_eq_left (show i < 16 * (8 * k + c) by omega_arith),
        show i / 16 = 8 * k + (i - 128 * k) / 16 by omega_arith, show i % 16 = (i - 128 * k) % 16 by omega_arith]
      have hj : (i - 128 * k) / 16 < c := by omega_arith
      have eT : T + BitVec.ofNat 64 (i - 128 * k) = s₅.gpr sb + BitVec.ofNat 64 (8 * tailSlot + 16 * ((i - 128 * k) / 16)) +
          BitVec.ofNat 64 ((i - 128 * k) % 16) := by
        rw [base₅, addr_add, addr_add, show 8 * tailSlot + 16 * ((i - 128 * k) / 16) + (i - 128 * k) % 16 =
          8 * tailSlot + (i - 128 * k) by omega_arith]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (blk s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega_arith), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨A, 16 * c⟩ : Region)], ¬ r.Contains (D + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off D (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      have hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b, 8 * slots⟩) →
          ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
      rw [f₉ _ hout, mem₈,
        f₅.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Region.sub_prefix (by rw [slots_eq, keySlot_eq]; omega_arith)
          · exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith)) (by simp only; omega_arith) hin,
        f₃'.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith))
          (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 128 * k
      · rw [ite_eq_left (show i < 16 * (8 * k) by omega_arith), ite_eq_left (show i < 16 * (8 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (8 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (8 * k + c) by omega_arith)]
  have fr : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₉.mem := hi.frame.trans fr₉
  -- On to the next group.
  obtain ⟨s₁₀, e₁₀, r₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := subR_ok s₉ .r6 .r6 .r12
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := addI_ok s₁₀ .r5 .r5 (imm := 128) (by decide)
  refine WP.of_runBlock ⟨s₁₁, by
    rw [show ([Instr.sub .r6 .r6 .r12, .addi .r5 .r5 128] : List Instr) =
      [.sub .r6 .r6 .r12] ++ [.addi .r5 .r5 128] from rfl, runBlock_append', e₁₀,
      Option.bind_some, e₁₁], ?_⟩
  have hm : s₁₁.mem = s₉.mem := by rw [m₁₁, m₁₀]
  have r6₁₁ : s₁₁.gpr .r6 = BitVec.ofNat 64 (v - c) := by
    rw [o₁₁ _ (by decide), r₁₀, r6₉, r12₉, VG.Offset.ofNat_sub_ofNat (by omega_arith)]
  have base₁₁ : s₁₁.gpr sb = b := by rw [o₁₁ _ (by decide), o₁₀ _ (by decide), base₉]
  have rd₁₁' : s₁₁.rd = s₀.rd := by rw [rd₁₁, rd₁₀, rd₉']
  have wr₁₁' : s₁₁.wr = s₀.wr := by rw [wr₁₁, wr₁₀, wr₉']
  by_cases hlt : v ≤ 8
  · have hn : 8 * k + c = n := by omega_arith
    refine .inl ⟨by rw [r6₁₁, show v - c = 0 by omega_arith]; rfl, base₁₁, hm ▸ sc₉,
      fun i hi' => by rw [hm, hdata i hi', hn], hm ▸ fr, rd₁₁', wr₁₁'⟩
  · have hc : c = 8 := by omega_arith
    refine .inr ⟨fun h => ?_, base₁₁, ?_, ?_, by omega_arith, ?_, hm ▸ sc₉, ?_, hm ▸ fr, rd₁₁', wr₁₁'⟩
    · have hne : v - c ≠ 0 := by omega_arith
      rw [r6₁₁] at h
      apply hne
      have := congrArg BitVec.toNat h
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
    · rw [r₁₁, o₁₀ _ (by decide), r5₉, addr_add, show 128 * k + 128 = 128 * (k + 1) by omega_arith]
    · rw [r6₁₁, show v - c = n - 8 * (k + 1) by omega_arith]
    · rw [o₁₁ _ (by decide), o₁₀ _ (by decide), r7₉]
    · rw [hm, show 8 * (k + 1) = 8 * k + c by omega_arith]; exact hdata

end VG.Proof.Camellia.PPC64LE
