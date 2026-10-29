module


public import VerifiedGarbage.Proof.Sm4.RISCV64.Prologue
public import VerifiedGarbage.Proof.Sm4.Common
public import VerifiedGarbage.Proof.Sm4.RISCV64.Core
import VerifiedGarbage.Proof.Sm4.RISCV64.Keys
import VerifiedGarbage.Proof.Sm4.RISCV64.Crypt16
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.CopyFast
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit

/-!
# A group of blocks of SM4 ECB on RISCV64

`dataGroup_wp`: one iteration of the data loop copies the group's blocks
(sixteen, or the last one to fifteen) to the tail buffer, a byte at a time
(`copyAny_ok`), transforms it (`crypt16_wp`, which keeps the data pointer,
the blocks left and the table's end in `a1`, `a2` and `a0`), copies the
blocks back and steps to the next group. As on PPC64LE
(`Proof/Sm4/PPC64LE/Group.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Sm4.RISCV64
open VG.Proof.Sm4 (DInv quads ofBlock outBlock not_contains_off blockAt_getD)
open VG.Impl.Aes.RISCV64 (q sb t0 t1 movR ldS stS shrI shlI)
open VG.Impl.Words.RISCV64 (copyAny)
open VG.Proof.Aes.RISCV64 (sboxWrites)

/-! ## Small blocks -/

theorem lsr4_beq {v : Nat} (hv : v < 2 ^ 64) : (BitVec.ofNat 64 v >>> 4 == 0) = decide (v < 16) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow] at this
    simp at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow]
    simp
    omega

theorem movR_ok (s : State) (d n : Reg) :
    ∃ s', runBlock isa [movR d n] s = some s' ∧ s'.gpr d = s.gpr n ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write d (s.gpr n + BitVec.ofInt 64 0), by
    simp only [movR, runBlock_cons, exec_addi (show imm12 0 by decide), runStep_some, runBlock_nil],
    (RegUpd.gpr_write_self _ _ _).trans (by simp), fun _ h => RegUpd.gpr_write_of_ne _ _ h, rfl, rfl, rfl⟩

theorem shl4_ok (s : State) (d n : Reg) :
    ∃ s', runBlock isa [shlI d n 4] s = some s' ∧ s'.gpr d = s.gpr n <<< 4 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, by simp only [shlI, runBlock_cons, exec_shift_d (show 4 < 64 by decide), runStep_some, runBlock_nil],
    RegUpd.gpr_write_self _ _ _, fun _ h => RegUpd.gpr_write_of_ne _ _ h, rfl, rfl, rfl⟩

theorem ofNat_shl4 {c : Nat} (h : c < 2 ^ 60) : BitVec.ofNat 64 c <<< 4 = BitVec.ofNat 64 (16 * c) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (a := c) (by omega)]
  congr 1; omega

/-- `a4 := min(a2, 16)`. -/
theorem groupCount_wp {s : State} {v : Nat} (hr : s.gpr .a2 = BitVec.ofNat 64 v) (hv : v < 2 ^ 64) :
    WP isa groupCount s fun s' => s'.gpr .a4 = BitVec.ofNat 64 (min v 16) ∧
      (∀ r, r ≠ .a4 → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write t0 (s.gpr .a2 >>> 4)
  have e₁ : runBlock isa [shrI t0 .a2 4] s = some s₁ := by
    simp only [shrI, runBlock_cons, exec_shift_d (show 4 < 64 by decide), runStep_some, runBlock_nil, s₁]
  have t₁ : s₁.gpr t0 = BitVec.ofNat 64 v >>> 4 := by rw [RegUpd.gpr_write_self, hr]
  have o₁ : ∀ r, r ≠ t0 → s₁.gpr r = s.gpr r := fun _ h => RegUpd.gpr_write_of_ne _ _ h
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.ite (decide (16 ≤ v)) ((eval_nonzero s₁ t0).trans (by rw [t₁, lsr4_beq hv]; by_cases h : v < 16 <;> simp [h] <;> omega))
    (fun h => ?_) (fun h => ?_)
  · refine WP.of_runBlock ⟨s₁.write .a4 (BitVec.ofInt 64 16), by
      simp only [runBlock_cons, exec_li (show imm12 16 by decide), runStep_some, runBlock_nil], ?_, fun r h1 h2 => by rw [RegUpd.gpr_write_of_ne _ _ h1, o₁ r h2], rfl, rfl, rfl⟩
    rw [RegUpd.gpr_write_self, Nat.min_eq_right (by simp at h; omega)]; rfl
  · obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ .a4 .a2
    refine WP.of_runBlock ⟨s₂, e₂, ?_, fun r h1 h2 => by rw [o₂ r h1, o₁ r h2], m₂, rd₂, wr₂⟩
    rw [r₂, o₁ _ (by decide), hr, Nat.min_eq_left (by simp at h; omega)]

theorem readW_slot_write {m : Mem} {b : Addr} {j k : Nat} (v : BitVec 64) (hj : j < slots) (hk : k < slots) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 64 = if j = k then v else m.readW (wordAddr b j) 64 := by
  rw [slots_eq] at hj hk
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self64 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega) (by omega) h) (by decide)

/-! ## The scratch buffer's contents -/

/-- The masks, in the memory at `b`. -/
def MasksAt (m : Mem) (b : Addr) : Prop := ∀ kv ∈ maskCs, m.readW (wordAddr b kv.1) 64 = kv.2

theorem MasksOk.at {s : State} {b : Addr} (h : MasksOk s) (hb : s.gpr sb = b) : MasksAt s.mem b :=
  fun kv hkv => by rw [← hb]; exact h kv hkv

theorem MasksAt.ok {s : State} {b : Addr} (h : MasksAt s.mem b) (hb : s.gpr sb = b) : MasksOk s :=
  fun kv hkv => by show s.mem.readW (wordAddr (s.gpr sb) kv.1) 64 = kv.2; rw [hb]; exact h kv hkv

/-- What the data loop keeps in the scratch buffer: the masks, the table and
the saved registers. -/
structure ScrOk (s₀ : State) (b : Addr) (E : Nat → Spec.Sm4.Word) (m : Mem) : Prop where
  masks : MasksAt m b
  keys : ∀ e < 32, VG.Proof.Sm4.WordRel (entryW m b e) fun _ => E e
  saved : Saved s₀ b m

/-- The slots `ScrOk` reads: 40–50, the table (128–383) and 384–395. -/
abbrev scrRegions (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 (8 * 40), 88⟩, ⟨b + BitVec.ofNat 64 (8 * tableSlot), 8 * 256⟩,
    ⟨b + BitVec.ofNat 64 (8 * savedSlot), 96⟩]

theorem masks_range : ∀ kv ∈ maskCs, 40 ≤ kv.1 ∧ kv.1 < 51 := by decide

theorem mask_range {kv : Nat × BitVec 64} (hkv : kv ∈ maskCs) : 40 ≤ kv.1 ∧ kv.1 < 51 := masks_range kv hkv

theorem ScrOk.frame {s₀ : State} {b : Addr} {E : Nat → Spec.Sm4.Word} {m m' : Mem}
    (h : ScrOk s₀ b E m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ t ∈ scrRegions b, ∀ r ∈ rs, Region.Disjoint t r) :
    ScrOk s₀ b E m' := by
  have hR : ∀ t ∈ scrRegions b, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
      m'.readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 := fun t ht d hs =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd _ ht r hr).sub_left hs) (by decide)
  refine ⟨fun kv hkv => ?_, fun i hi => (h.keys i hi).congr fun j hj => ?_, fun i hi => ?_⟩
  · have hk := mask_range hkv
    rw [← h.masks kv hkv]
    exact hR _ List.mem_cons_self (8 * kv.1) (VG.Offset.sub b (by omega) (by omega))
  · exact hR _ (List.mem_cons_of_mem _ List.mem_cons_self) (8 * tableSlot + 64 * i + 8 * j)
      (VG.Offset.sub b (by omega) (by rw [tableSlot_eq]; omega))
  · rw [← h.saved i hi]
    exact hR _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (8 * (savedSlot + i))
      (VG.Offset.sub b (by omega) (by omega))

theorem ScrOk.frame2 {s₀ : State} {b : Addr} {E : Nat → Spec.Sm4.Word} {m m' : Mem}
    (h : ScrOk s₀ b E m) {rs : List Region} (hf : Frame rs m m') (hm : MasksAt m' b)
    (hd : ∀ t ∈ (scrRegions b).tail, ∀ r ∈ rs, Region.Disjoint t r) : ScrOk s₀ b E m' := by
  have hR : ∀ t ∈ (scrRegions b).tail, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
      m'.readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 := fun t ht d hs =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd _ ht r hr).sub_left hs) (by decide)
  refine ⟨hm, fun i hi => (h.keys i hi).congr fun j hj => ?_, fun i hi => ?_⟩
  · exact hR _ List.mem_cons_self (8 * tableSlot + 64 * i + 8 * j)
      (VG.Offset.sub b (by omega) (by rw [tableSlot_eq]; omega))
  · rw [← h.saved i hi]
    exact hR _ (List.mem_cons_of_mem _ List.mem_cons_self) (8 * (savedSlot + i))
      (VG.Offset.sub b (by omega) (by omega))

/-! ## The data loop -/

/-- Each block, transformed: the output of the 32 rounds with the round keys `E`. -/
def outF (m₀ : Mem) (D : Addr) (E : Nat → Spec.Sm4.Word) (j : Nat) : Spec.Sm4.Block :=
  outBlock (quads .enc E 8 (ofBlock (Spec.Sm4.blockAt m₀ (D + BitVec.ofNat 64 (16 * j)))))

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure GPre (s₀ : State) (b D : Addr) (n : Nat) : Prop where
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 8 * slots⟩
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  fitD : D.toNat + 16 * n ≤ 2 ^ 64
  al : b.toNat % 8 = 0

/-- `copyAny` of `c` blocks from `t1` to `t2`, `t3 = 16 c` bytes, set up. -/
theorem copy_wp {s : State} {X Y : Addr} {c : Nat} (hc : 0 < c) (hc16 : c ≤ 16)
    (hx : s.gpr .t1 = X) (hy : s.gpr .t2 = Y) (hcx : s.gpr .t3 = BitVec.ofNat 64 (16 * c))
    (hX : ∀ i n, i + n ≤ 16 * c → i < 16 * c → InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 i) n)
    (hY : ∀ i n, i + n ≤ 16 * c → i < 16 * c → InRegions s.wr (Y + BitVec.ofNat 64 i) n)
    (hsep : Region.Disjoint ⟨X, 16 * c⟩ ⟨Y, 16 * c⟩) :
    WP isa (copyAny .t4 .t1 .t2 .t3) s fun s' =>
      (∀ t < 16 * c, s'.mem (Y + BitVec.ofNat 64 t) = s.mem (X + BitVec.ofNat 64 t)) ∧
      Frame [⟨Y, 16 * c⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (copyAny_ok (tmp := .t4) (src := .t1) (dst := .t2) (cnt := .t3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) s (N := 16 * c) (by omega) (by omega) (by omega) hcx
    (by rw [hx]; exact fun i hi => hX i 1 (by omega) hi) (by rw [hy]; exact fun i hi => hY i 1 (by omega) hi)
    (by rw [hx]; exact fun i hi _ => hX (8 * i) 8 (by omega) (by omega))
    (by rw [hy]; exact fun i hi _ => hY (8 * i) 8 (by omega) (by omega))
    (by rw [hx, hy]; exact hsep.symm.sep (Region.contains_self _ _) (Region.contains_self _ _)))
    fun t ⟨tc, tf, tk⟩ => ⟨by rw [← hx, ← hy]; exact tc, by rw [← hy]; exact tf,
      fun r h1 h2 h3 h4 => tk.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h4, h1, h2, h3⟩),
      tk.2.1, tk.2.2⟩

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : Addr) (n : Nat) (E : Nat → Spec.Sm4.Word) (k : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  a1 : s.gpr .a1 = D + BitVec.ofNat 64 (256 * k)
  a2 : s.gpr .a2 = BitVec.ofNat 64 (n - 16 * k)
  lt : 16 * k < n
  a0 : s.gpr .a0 = b + BitVec.ofNat 64 (8 * tableEnd)
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem D n (16 * k) (outF s₀.mem D E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : Addr) (n : Nat) (E : Nat → Spec.Sm4.Word) (s : State) : Prop where
  base : s.gpr sb = b
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem D n n (outF s₀.mem D E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

theorem dataGroup_wp {s₀ : State} {b D : Addr} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {k : Nat} {s : State} (hi : GInv s₀ b D n E k s) :
    WP isa Impl.Sm4.RISCV64.group s fun s' => (s'.gpr .a2 = 0 ∧ GDone s₀ b D n E s') ∨
      (s'.gpr .a2 ≠ 0 ∧ GInv s₀ b D n E (k + 1) s') := by
  have hfit := hp.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  rw [slots_eq] at hfit
  let v := n - 16 * k
  let c := min v 16
  have hv : v < 2 ^ 64 := by omega_arith
  have hc0 : 0 < c := by omega_arith
  have hc16 : c ≤ 16 := by omega_arith
  have hkc : 256 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 64 (256 * k)
  let T := b + BitVec.ofNat 64 (8 * tailSlot)
  have hwS : (⟨b, 8 * slots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have inT : ∀ t n, t + n ≤ 256 → t < 256 → InRegions s.wr (T + BitVec.ofNat 64 t) n := by
    intro t n ht ht'
    refine ⟨_, hwS, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base b (by rw [slots_eq, tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  have inA : ∀ t n, t + n ≤ 16 * c → t < 16 * c → InRegions s.wr (A + BitVec.ofNat 64 t) n := by
    intro t n ht ht'
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega_arith) (by omega_arith)
  have sepAT : Region.Disjoint ⟨A, 16 * c⟩ ⟨T, 16 * c⟩ :=
    (hp.sep.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right
      (VG.Offset.sub_base b (by rw [slots_eq, tailSlot_eq]; omega_arith))
  unfold Impl.Sm4.RISCV64.group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.a2 hv) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a⟩ := movR_ok s₁ .t1 .a1
  obtain ⟨s₂b, e₂b, r₂b, o₂b, m₂b, rd₂b, wr₂b⟩ := slotAddr_ok s₂a .t2 tailSlot
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := shl4_ok s₂b .t3 .a4
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂b, rd₂a, rd₁]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂b, wr₂a, wr₁]
  have mem₂ : s₂.mem = s.mem := by rw [m₂, m₂b, m₂a, m₁]
  have g₂ : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .a4 → r ≠ t0 → s₂.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₂ r h3, o₂b r h2, o₂a r h1, o₁ r h4 h5]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [Interleave.runBlock_append, Interleave.runBlock_append, e₂a, Option.bind_some, e₂b, Option.bind_some,
      e₂], ?_⟩)
  refine WP.mono (copy_wp (X := A) (Y := T) hc0 hc16
    (by rw [o₂ _ (by decide), o₂b _ (by decide), r₂a, o₁ _ (by decide) (by decide), hi.a1])
    (by rw [o₂ _ (by decide), r₂b, o₂a _ (by decide), o₁ _ (by decide) (by decide), hi.base])
    (by rw [r₂, o₂b _ (by decide), o₂a _ (by decide), c₁, ofNat_shl4 (by omega_arith)])
    (fun t n ht ht' => by rw [rd₂', wr₂']; exact inRd (inA t n ht ht'))
    (fun t n ht ht' => by rw [wr₂']; exact inT t n (by omega_arith) (by omega_arith)) sepAT) fun s₃ ⟨cp₃, f₃, g₃, rd₃, wr₃⟩ => ?_
  have f₃' : Frame [⟨T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact f₃
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂']
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂']
  have g₃' : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .a4 → r ≠ t0 → s₃.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by rw [g₃ r h1 h2 h3 h4, g₂ r h1 h2 h3 h5 h6]
  have base₃ : s₃.gpr sb = b := by
    rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hi.base]
  have sc₃ : ScrOk s₀ b E s₃.mem := by
    refine hi.scr.frame (mem₂ ▸ f₃) fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> refine VG.Offset.disjoint b ?_ ?_ ?_ <;>
      (try simp only [tailSlot_eq, tableSlot_eq, savedSlot_eq]) <;> omega_arith
  -- The sixteen blocks.
  have hkey : KeyCtx s₃ E :=
    { scr := by rw [base₃, wr₃']; exact hwS
      fit := by rw [base₃, slots_eq]; exact hfit
      al := by rw [base₃]; exact hp.al
      keys := fun e he => by rw [base₃]; exact sc₃.keys e he }
  have ha0₃ : s₃.gpr .a0 = s₃.gpr sb + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hi.a0, base₃]
  refine WP.seq (WP.mono (crypt16_wp hkey (sc₃.masks.ok base₃) ha0₃) fun s₅ ⟨c₅, b₅⟩ => ?_)
  have base₅ : s₅.gpr sb = b := by rw [c₅.base, base₃]
  have f₅ : Frame [⟨b, 8 * tableSlot⟩] s₃.mem s₅.mem := by have := c₅.frame; rw [base₃] at this; exact this
  have sc₅ : ScrOk s₀ b E s₅.mem := by
    refine sc₃.frame2 f₅ (c₅.masks.at base₅) fun t ht r hr => ?_
    simp only [scrRegions, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at ht hr
    subst hr
    rcases ht with rfl | rfl
    · exact VG.Offset.disjoint_base b (by rw [tableSlot_eq]) (by rw [tableSlot_eq]; omega_arith)
    · exact VG.Offset.disjoint_base b (by rw [tableSlot_eq, savedSlot_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith)
  have k₅ : ∀ r, r ∉ sboxWrites → r ≠ kr → s₅.gpr r = s₃.gpr r := fun r h1 h2 => c₅.keep r h1 h2
  have g₅ : ∀ r, r ∉ sboxWrites → r ≠ kr → r ≠ .a4 → s₅.gpr r = s.gpr r := fun r h1 h2 h3 => by
    have hsub : ∀ x ∈ ([.t1, .t2, .t3, .t4, t0] : List Reg), x ∈ sboxWrites := by decide
    have h' : r ∉ ([.t1, .t2, .t3, .t4, t0] : List Reg) := fun h => h1 (hsub r h)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h'
    rw [k₅ r h1 h2, g₃' r h'.1 h'.2.1 h'.2.2.1 h'.2.2.2.1 h3 h'.2.2.2.2]
  have a1₅ : s₅.gpr .a1 = A := by rw [g₅ _ (by decide) (by decide) (by decide), hi.a1]
  have a2₅ : s₅.gpr .a2 = BitVec.ofNat 64 v := by rw [g₅ _ (by decide) (by decide) (by decide), hi.a2]
  have a0₅ : s₅.gpr .a0 = b + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₅ _ (by decide) (by decide) (by decide), hi.a0]
  have wr₅' : s₅.wr = s.wr := by rw [c₅.wr, wr₃']
  have rd₅' : s₅.rd = s.rd := by rw [c₅.rd, rd₃']
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp a2₅ hv) fun s₇ ⟨c₇, o₇, m₇, rd₇, wr₇⟩ => ?_))
  obtain ⟨s₈a, e₈a, r₈a, o₈a, m₈a, rd₈a, wr₈a⟩ := slotAddr_ok s₇ .t1 tailSlot
  obtain ⟨s₈b, e₈b, r₈b, o₈b, m₈b, rd₈b, wr₈b⟩ := movR_ok s₈a .t2 .a1
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := shl4_ok s₈b .t3 .a4
  refine WP.seq (WP.of_runBlock ⟨s₈, by
    rw [Interleave.runBlock_append, e₈a, Option.bind_some,
      show ([movR .t2 .a1, shlI .t3 .a4 4] : List Instr) = [movR .t2 .a1] ++ [shlI .t3 .a4 4] from rfl,
      Interleave.runBlock_append, e₈b, Option.bind_some, e₈], ?_⟩)
  have mem₈ : s₈.mem = s₅.mem := by rw [m₈, m₈b, m₈a, m₇]
  have wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₈b, wr₈a, wr₇, wr₅']
  have rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₈b, rd₈a, rd₇, rd₅']
  have g₈ : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .a4 → r ≠ t0 → s₈.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₈ r h3, o₈b r h2, o₈a r h1, o₇ r h4 h5]
  refine WP.mono (copy_wp (X := T) (Y := A) hc0 hc16
    (by rw [o₈ _ (by decide), o₈b _ (by decide), r₈a, o₇ _ (by decide) (by decide), base₅])
    (by rw [o₈ _ (by decide), r₈b, o₈a _ (by decide), o₇ _ (by decide) (by decide), a1₅])
    (by rw [r₈, o₈b _ (by decide), o₈a _ (by decide), c₇, ofNat_shl4 (by omega_arith)])
    (fun t n ht ht' => by rw [rd₈', wr₈']; exact inRd (inT t n (by omega_arith) (by omega_arith)))
    (fun t n ht ht' => by rw [wr₈']; exact inA t n ht ht') sepAT.symm) fun s₉ ⟨cp₉, f₉, g₉, rd₉, wr₉⟩ => ?_
  have g₉' : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .a4 → r ≠ t0 → s₉.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by rw [g₉ r h1 h2 h3 h4, g₈ r h1 h2 h3 h5 h6]
  have a4₉ : s₉.gpr .a4 = BitVec.ofNat 64 c := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide), o₈ _ (by decide), o₈b _ (by decide),
      o₈a _ (by decide), c₇]
  have base₉ : s₉.gpr sb = b := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), base₅]
  have a1₉ : s₉.gpr .a1 = A := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a1₅]
  have a2₉ : s₉.gpr .a2 = BitVec.ofNat 64 v := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a2₅]
  have a0₉ : s₉.gpr .a0 = b + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a0₅]
  have wr₉' : s₉.wr = s₀.wr := by rw [wr₉, wr₈', hi.wr]
  have rd₉' : s₉.rd = s₀.rd := by rw [rd₉, rd₈', hi.rd]
  -- The scratch buffer and the frame.
  have subS : ∀ {d l : Nat}, d + l ≤ 8 * slots → Region.Sub ⟨b + BitVec.ofNat 64 d, l⟩ ⟨b, 8 * slots⟩ :=
    fun h => VG.Offset.sub_base b h
  have sc₉ : ScrOk s₀ b E s₉.mem := by
    refine (mem₈ ▸ sc₅).frame f₉ fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hsub : Region.Sub t ⟨b, 8 * slots⟩ := by
      simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> refine subS ?_ <;> (try simp only [tableSlot_eq, savedSlot_eq]) <;>
        rw [slots_eq] <;> omega_arith
    exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right hsub).symm
  have fr₉ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s.mem s₉.mem := by
    refine (((mem₂ ▸ f₃).sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((f₅.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((mem₈ ▸ f₉).sub fun r hr => ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩)))
    · simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub_base D (by omega_arith)
  -- The blocks the sixteen-block code read are the group's, as on entry.
  have hblk : ∀ j < c, tailBlock s₃ j = Spec.Sm4.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * (16 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [tailBlock, Spec.Sm4.blockAt, Vector.getElem_ofFn]
    rw [base₃, addr_add, addr_add]
    have ht : 16 * j + u < 16 * c := by omega_arith
    have := cp₃ (16 * j + u) ht
    rw [addr_add] at this
    rw [show 8 * tailSlot + 16 * j + u = 8 * tailSlot + (16 * j + u) by omega_arith, this, mem₂, addr_add,
      hi.data _ (by omega_arith), ite_eq_right (by omega_arith),
      show 256 * k + (16 * j + u) = 16 * (16 * k + j) + u by omega_arith]
  have hdata : DInv s₀.mem s₉.mem D n (16 * k + c) (outF s₀.mem D E) := by
    intro i hin
    by_cases hin1 : 256 * k ≤ i ∧ i < 256 * k + 16 * c
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 256 * k) := by
        rw [addr_add, show 256 * k + (i - 256 * k) = i by omega_arith]
      rw [e1, cp₉ _ (by omega_arith), mem₈, ite_eq_left (show i < 16 * (16 * k + c) by omega_arith),
        show i / 16 = 16 * k + (i - 256 * k) / 16 by omega_arith, show i % 16 = (i - 256 * k) % 16 by omega_arith]
      have hj : (i - 256 * k) / 16 < c := by omega_arith
      have eT : T + BitVec.ofNat 64 (i - 256 * k) = s₅.gpr sb + BitVec.ofNat 64 (8 * tailSlot + 16 * ((i - 256 * k) / 16)) +
          BitVec.ofNat 64 ((i - 256 * k) % 16) := by
        rw [base₅, addr_add, addr_add, show 8 * tailSlot + 16 * ((i - 256 * k) / 16) + (i - 256 * k) % 16 =
          8 * tailSlot + (i - 256 * k) by omega_arith]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (tailBlock s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega_arith), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨A, 16 * c⟩ : Region)], ¬ r.Contains (D + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off D (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      have hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b, 8 * slots⟩) →
          ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
      rw [f₉ _ hout, mem₈,
        f₅.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)) (by simp only; omega_arith) hin,
        f₃'.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith))
          (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 256 * k
      · rw [ite_eq_left (show i < 16 * (16 * k) by omega_arith), ite_eq_left (show i < 16 * (16 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (16 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (16 * k + c) by omega_arith)]
  have fr : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₉.mem := hi.frame.trans fr₉
  -- On to the next group.
  obtain ⟨s₁₀, e₁₀, r₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := subR_ok s₉ .a2 .a2 .a4
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := addI_ok s₁₀ .a1 .a1 (imm := 256) (by decide)
  refine WP.of_runBlock ⟨s₁₁, by
    rw [show ([Instr.sub .a2 .a2 .a4, .addi .a1 .a1 256] : List Instr) =
      [.sub .a2 .a2 .a4] ++ [.addi .a1 .a1 256] from rfl, Interleave.runBlock_append, e₁₀,
      Option.bind_some, e₁₁], ?_⟩
  have hm : s₁₁.mem = s₉.mem := by rw [m₁₁, m₁₀]
  have a2₁₁ : s₁₁.gpr .a2 = BitVec.ofNat 64 (v - c) := by
    rw [o₁₁ _ (by decide), r₁₀, a2₉, a4₉, VG.Offset.ofNat_sub_ofNat (by omega_arith)]
  have base₁₁ : s₁₁.gpr sb = b := by rw [o₁₁ _ (by decide), o₁₀ _ (by decide), base₉]
  have rd₁₁' : s₁₁.rd = s₀.rd := by rw [rd₁₁, rd₁₀, rd₉']
  have wr₁₁' : s₁₁.wr = s₀.wr := by rw [wr₁₁, wr₁₀, wr₉']
  by_cases hlt : v ≤ 16
  · have hn : 16 * k + c = n := by omega_arith
    refine .inl ⟨by rw [a2₁₁, show v - c = 0 by omega_arith]; rfl, base₁₁, hm ▸ sc₉,
      fun i hi' => by rw [hm, hdata i hi', hn], hm ▸ fr, rd₁₁', wr₁₁'⟩
  · have hc : c = 16 := by omega_arith
    refine .inr ⟨fun h => ?_, base₁₁, ?_, ?_, by omega_arith, ?_, hm ▸ sc₉, ?_, hm ▸ fr, rd₁₁', wr₁₁'⟩
    · have hne : v - c ≠ 0 := by omega_arith
      rw [a2₁₁] at h
      apply hne
      have := congrArg BitVec.toNat h
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
    · rw [r₁₁, o₁₀ _ (by decide), a1₉, show BitVec.ofInt 64 256 = BitVec.ofNat 64 256 from rfl, addr_add,
        show 256 * k + 256 = 256 * (k + 1) by omega_arith]
    · rw [a2₁₁, show v - c = n - 16 * (k + 1) by omega_arith]
    · rw [o₁₁ _ (by decide), o₁₀ _ (by decide), a0₉]
    · rw [hm, show 16 * (k + 1) = 16 * k + c by omega_arith]; exact hdata

end VG.Proof.Sm4.RISCV64
