module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Sm4.X86.Prologue
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Sm4.X86.LayersLit
import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Sm4.Common
import VerifiedGarbage.Proof.Sm4.X86.Copy
import VerifiedGarbage.Proof.Sm4.X86.Crypt8
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Sm4.X86.Group`, which this module and modules that import it used -/

section

/-!
# A group of blocks of SM4 ECB on x86 (32-bit)

As on ARMv7 (`Proof/Sm4/Arm/Group.lean`): `dataGroup_wp`, one iteration of
the data loop, copies the group's blocks (eight, or the last one to seven)
to the tail buffer, transforms it (`crypt8_wp`), copies the blocks back and
steps to the next group. The data pointer and the blocks left live in their
slots (`dSlot`, `nSlot`) between the steps, which use every other register.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Proof.Sm4 (DInv quads ofBlock outBlock not_contains_off blockAt_getD)
open VG.Impl.Aes.X86 (sb slotAt movS st movR addI subI subR movI)

/-! ## Small blocks -/

/-- `ecx := min(ebp, 8)`. -/
theorem countR_wp {s : State} {v : Nat} (hn : s.gpr .ebp = BitVec.ofNat 32 v) (hv : v < 2 ^ 32) :
    WP isa countR s fun s' => s'.gpr .ecx = BitVec.ofNat 32 (min v 8) ∧
      (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁, -, -⟩ := movR_ok s .ecx .ebp
  let s₂ := arithFlags s₁ (s₁.gpr .ebp - 8) ((s₁.gpr .ebp).toNat < (8 : BitVec 32).toNat)
    (subOverflow (s₁.gpr .ebp) 8 (s₁.gpr .ebp - 8))
  obtain e₂ : runBlock isa [movR .ecx .ebp, .alu .cmp .ebp (.imm 8)] s = some s₂ := by
    rw [show ([movR .ecx .ebp, .alu .cmp .ebp (.imm 8)] : List Instr) =
      [movR .ecx .ebp] ++ [.alu .cmp .ebp (.imm 8)] from rfl, runBlock_app, e₁, Option.bind_some]
    rfl
  obtain ebp₂ : s₂.gpr .ebp = BitVec.ofNat 32 v := by rw [RegUpd.gpr_arithFlags, o₁ _ (by decide), hn]
  obtain cf₂ : s₂.cf = some (decide (v < 8)) := by
    rw [RegUpd.cf_arithFlags, o₁ _ (by decide), hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]; rfl
  obtain o₂ : ∀ r, r ≠ .ecx → s₂.gpr r = s.gpr r := fun r hr => by rw [RegUpd.gpr_arithFlags, o₁ r hr]
  obtain m₂ : s₂.mem = s.mem := by rw [RegUpd.mem_arithFlags, m₁]
  obtain rd₂ : s₂.rd = s.rd := by rw [RegUpd.rd_arithFlags, rd₁]
  obtain wr₂ : s₂.wr = s.wr := by rw [RegUpd.wr_arithFlags, wr₁]
  unfold countR
  refine WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)
  refine WP.ite (decide (v < 8)) ((eval_b s₂).trans cf₂) (fun h => ?_) (fun h => ?_)
  · refine WP.block_nil ⟨?_, o₂, m₂, rd₂, wr₂⟩
    rw [RegUpd.gpr_arithFlags, r₁, hn, Nat.min_eq_left (by simp at h; omega_using [h])]
  · obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movI_ok s₂ .ecx 8
    refine WP.of_runBlock ⟨s₃, e₃, ?_, fun r hr => by rw [o₃ r hr, o₂ r hr], by rw [m₃, m₂],
      by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩
    rw [r₃, Nat.min_eq_right (by simp at h; omega_using [h])]; rfl

/-- The data pointer and the blocks left from their slots to `esi` and
`ebp`, and `ecx := min(ebp, 8)`. -/
theorem groupCount_wp {s : State} {b A : BitVec 32} {v : Nat} (hb : s.gpr .edi = b) (hw : ScrIn s.wr b)
    (hd : s.mem.readW (wordAddr b dSlot) 32 = A) (hn : s.mem.readW (wordAddr b nSlot) 32 = BitVec.ofNat 32 v)
    (hv : v < 2 ^ 32) :
    WP isa groupCount s fun s' => s'.gpr .esi = A ∧ s'.gpr .ebp = BitVec.ofNat 32 v ∧
      s'.gpr .ecx = BitVec.ofNat 32 (min v 8) ∧
      (∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok s .esi .edi (k := dSlot) hb (by decide) hw
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, -, -⟩ := ldSlot_ok s₁ .ebp .edi (k := nSlot)
    (by rw [o₁ _ (by decide), hb]) (by decide) (by rw [wr₁]; exact hw)
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₂, ?_, WP.mono (countR_wp (by rw [r₂, m₁, hn]) hv)
    fun s₃ ⟨c₃, o₃, m₃, rd₃, wr₃⟩ => ?_⟩)
  · rw [show ([movS .esi dSlot, movS .ebp nSlot] : List Instr) =
      [.mov .esi (.mem (slotAt .edi dSlot))] ++ [.mov .ebp (.mem (slotAt .edi nSlot))] from rfl,
      runBlock_app, e₁, Option.bind_some, e₂]
  · exact ⟨by rw [o₃ _ (by decide), o₂ _ (by decide), r₁, hd], by rw [o₃ _ (by decide), r₂, m₁, hn], c₃,
      fun r h1 h2 h3 => by rw [o₃ r h3, o₂ r h2, o₁ r h1], by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁],
      by rw [wr₃, wr₂, wr₁]⟩

/-- `st dSlot, esi; st nSlot, ebp`. -/
theorem stDN_ok (s : State) {b : BitVec 32} (hb : s.gpr .edi = b) (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [st dSlot .esi, st nSlot .ebp] s = some s' ∧
      s'.mem.readW (wordAddr b dSlot) 32 = s.gpr .esi ∧ s'.mem.readW (wordAddr b nSlot) 32 = s.gpr .ebp ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧
      Frame [⟨wordAddr b dSlot, 4⟩, ⟨wordAddr b nSlot, 4⟩] s.mem s'.mem := by
  have hfit : b.toNat + 4 * slots ≤ 2 ^ 32 := hw.fit
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, z₁, -, f₁⟩ := stSlot_ok s .esi .edi (k := dSlot) hb (by decide) hw
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, z₂, -, f₂⟩ := stSlot_ok s₁ .ebp .edi (k := nSlot) (by rw [g₁, hb])
    (by decide) (by rw [wr₁]; exact hw)
  refine ⟨s₂, ?_, ?_, ?_, by rw [g₂, g₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [z₂, z₁],
    (f₁.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (f₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)⟩
  · rw [show ([st dSlot .esi, st nSlot .ebp] : List Instr) =
      [.store (slotAt .edi dSlot) .esi] ++ [.store (slotAt .edi nSlot) .ebp] from rfl, runBlock_app, e₁,
      Option.bind_some, e₂]
  · rw [m₂, readW_slot_write hfit _ (by decide) (by decide), ite_eq_right (by decide), m₁,
      readW_slot_write hfit _ (by decide) (by decide), ite_eq_left rfl]
  · rw [m₂, readW_slot_write hfit _ (by decide) (by decide), ite_eq_left rfl, g₁]

theorem toNat_add32 (D : BitVec 32) {d : Nat} (h : D.toNat + d < 2 ^ 32) :
    (D + BitVec.ofNat 32 d).toNat = D.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h] : d < 2 ^ 32), Nat.mod_eq_of_lt h]

theorem setWidth_add {D : BitVec 32} {d : Nat} (h : D.toNat + d < 2 ^ 32) :
    (D + BitVec.ofNat 32 d).setWidth 64 = D.setWidth 64 + BitVec.ofNat 64 d := addr_eq h

/-! ## The scratch buffer's contents -/

/-- The slots `lo … hi - 1` of the scratch buffer at `b`. -/
abbrev slotsRegion (b : BitVec 32) (lo hi : Nat) : Region :=
  ⟨b.setWidth 64 + BitVec.ofNat 64 (4 * lo), 4 * (hi - lo)⟩

/-- A slot outside a frame. -/
theorem slot_keep {rs : List Region} {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    {lo hi : Nat} (hhi : hi ≤ slots) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsRegion b lo hi).Disjoint r)
    {k : Nat} (hk1 : lo ≤ k) (hk2 : k < hi) :
    m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  rw [slots_eq] at hfit hhi
  rw [slot_addr (by omega_using [hfit, hhi, hk2])]
  exact hf.readW (VG.Offset.contains _ (by omega_using [hk1]) (by omega_using [hk2]) (by omega_using [hhi, hk1, hk2])) hd (by decide)

/-- What the data loop keeps in the scratch buffer: the table and the saved
registers, in the slots from `tableSlot` to `dSlot`. -/
structure ScrOk (s₀ : State) (b : BitVec 32) (E : Nat → Spec.Sm4.Word) (m : Mem) : Prop where
  keys : ∀ e < 32, W32.WordRel (entryW m b e) fun _ => E e
  saved : Saved s₀ b m

theorem ScrOk.frame {s₀ : State} {b : BitVec 32} {E : Nat → Spec.Sm4.Word} {m m' : Mem}
    (h : ScrOk s₀ b E m) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsRegion b tableSlot dSlot).Disjoint r) : ScrOk s₀ b E m' := by
  refine ⟨fun e he => (h.keys e he).congr fun j hj => ?_, fun i hi => ?_⟩
  · exact slot_keep hfit (by decide) hf hd (by omega_using []) (by rw [dSlot_eq, tableSlot_eq]; omega_using [he, hj])
  · rw [← h.saved i hi]
    exact slot_keep hfit (by decide) hf hd (by rw [savedSlot_eq, tableSlot_eq]; omega_using [])
      (by rw [savedSlot_eq, dSlot_eq]; omega_using [hi])

/-- The slots of the data pointer and the count are in the scratch buffer. -/
theorem dn_sub {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) :
    ∀ r ∈ [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩],
      Region.Sub r ⟨b.setWidth 64, 4 * slots⟩ := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact slot_sub hfit (by decide)
  · exact slot_sub hfit (by decide)

/-- … and apart from the table and the saved registers. -/
theorem dn_disj {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) :
    ∀ r ∈ [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩],
      (slotsRegion b tableSlot dSlot).Disjoint r := fun r hr => by
  rw [slots_eq] at hfit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> rw [slot_addr (by (try simp only [dSlot_eq, nSlot_eq]); omega_using [hfit])] <;>
    exact VG.Offset.disjoint _ (by (try simp only [tableSlot_eq, dSlot_eq, nSlot_eq]); omega_using [])
      (by (try simp only [tableSlot_eq, dSlot_eq]); omega_using []) (by (try simp only [dSlot_eq, nSlot_eq]); omega_using [])

/-! ## The data loop -/

/-- Each block, transformed: the output of the 32 rounds with the round keys `E`. -/
def outF (m₀ : Mem) (D : Addr) (E : Nat → Spec.Sm4.Word) (j : Nat) : Spec.Sm4.Block :=
  outBlock (quads .enc E 8 (ofBlock (Spec.Sm4.blockAt m₀ (D + BitVec.ofNat 64 (16 * j)))))

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure GPre (s₀ : State) (b D : BitVec 32) (n : Nat) : Prop where
  scr : ScrIn s₀.wr b
  dat : (⟨D.setWidth 64, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D.setWidth 64, 16 * n⟩ ⟨b.setWidth 64, 4 * slots⟩
  fitD : D.toNat + 16 * n ≤ 2 ^ 32

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : BitVec 32) (n : Nat) (E : Nat → Spec.Sm4.Word) (k : Nat) (s : State) :
    Prop where
  base : s.gpr .edi = b
  esp : s.gpr .esp = s₀.gpr .esp
  dp : s.mem.readW (wordAddr b dSlot) 32 = D + BitVec.ofNat 32 (128 * k)
  np : s.mem.readW (wordAddr b nSlot) 32 = BitVec.ofNat 32 (n - 8 * k)
  lt : 8 * k < n
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem (D.setWidth 64) n (8 * k) (outF s₀.mem (D.setWidth 64) E)
  frame : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨D.setWidth 64, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : BitVec 32) (n : Nat) (E : Nat → Spec.Sm4.Word) (s : State) : Prop where
  base : s.gpr .edi = b
  esp : s.gpr .esp = s₀.gpr .esp
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem (D.setWidth 64) n n (outF s₀.mem (D.setWidth 64) E)
  frame : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨D.setWidth 64, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem dataGroup_wp {s₀ : State} {b D : BitVec 32} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {k : Nat} {s : State} (hi : GInv s₀ b D n E k s) :
    WP isa group s fun s' => (s'.zf = some true ∧ GDone s₀ b D n E s') ∨
      (s'.zf = some false ∧ GInv s₀ b D n E (k + 1) s') := by
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  obtain hb := setWidth_toNat b
  rw [slots_eq] at hfit
  obtain hfit' : b.toNat + 4 * slots ≤ 2 ^ 32 := by rw [slots_eq]; omega_arith
  let v := n - 8 * k
  let c := min v 8
  obtain hv : v < 2 ^ 32 := by omega_arith
  obtain hc0 : 0 < c := by omega_arith
  obtain hc8 : c ≤ 8 := by omega_arith
  obtain hkc : 128 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 32 (128 * k)
  let T := b + BitVec.ofNat 32 (4 * tailSlot)
  obtain hA : A.setWidth 64 = D.setWidth 64 + BitVec.ofNat 64 (128 * k) := setWidth_add (by omega_arith)
  obtain hT : T.setWidth 64 = b.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot) :=
    setWidth_add (by rw [tailSlot_eq]; omega_arith)
  obtain hAn : A.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by omega_arith)]; omega_arith
  obtain hTn : T.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by rw [tailSlot_eq]; omega_arith), tailSlot_eq]; omega_arith
  obtain hwS : ScrIn s.wr b := by rw [hi.wr]; exact hp.scr
  obtain hwD : (⟨D.setWidth 64, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain inT : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (T.setWidth 64 + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    obtain ⟨n', hn', hf', hr'⟩ := hwS.mem
    refine ⟨_, hr', ?_⟩
    rw [hT, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by rw [slots_eq] at hn'; rw [tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain inA : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (A.setWidth 64 + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwD, ?_⟩
    rw [hA, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain subA : Region.Sub ⟨A.setWidth 64, 16 * c⟩ ⟨D.setWidth 64, 16 * n⟩ := by
    rw [hA]; exact VG.Offset.sub_base _ (by omega_arith)
  obtain subT : Region.Sub ⟨T.setWidth 64, 16 * c⟩ ⟨b.setWidth 64, 4 * slots⟩ := by
    rw [hT]; exact VG.Offset.sub_base _ (by rw [slots_eq, tailSlot_eq]; omega_arith)
  obtain sepAT : Region.Disjoint ⟨A.setWidth 64, 16 * c⟩ ⟨T.setWidth 64, 16 * c⟩ :=
    (hp.sep.sub_left subA).sub_right subT
  -- The regions the steps write keep the slots from `tableSlot`.
  obtain dT : (slotsRegion b tableSlot slots).Disjoint ⟨T.setWidth 64, 16 * c⟩ := by
    rw [hT]; exact VG.Offset.disjoint _ (by rw [tableSlot_eq, tailSlot_eq]; omega_arith)
      (by rw [tableSlot_eq, slots_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain dA : (slotsRegion b tableSlot slots).Disjoint ⟨A.setWidth 64, 16 * c⟩ :=
    ((hp.sep.sub_left subA).sub_right (VG.Offset.sub_base _ (by rw [tableSlot_eq, slots_eq]))).symm
  obtain dTab : (slotsRegion b tableSlot slots).Disjoint ⟨b.setWidth 64, 4 * tableSlot⟩ :=
    VG.Offset.disjoint_base _ (by omega_arith) (by rw [tableSlot_eq, slots_eq]; omega_arith)
  obtain subTab : (slotsRegion b tableSlot dSlot).Sub (slotsRegion b tableSlot slots) :=
    VG.Offset.sub _ (by decide) (by decide)
  obtain dD : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b.setWidth 64, 4 * slots⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨D.setWidth 64, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  obtain hsub := dn_sub hfit'
  obtain dsTab := dn_disj hfit'
  unfold group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.base hwS hi.dp hi.np hv)
    fun s₁ ⟨esi₁, ebp₁, ecx₁, o₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a, -, -⟩ := movR_ok s₁ .edx .esi
  obtain ⟨s₂b, e₂b, r₂b, o₂b, m₂b, rd₂b, wr₂b, -, -⟩ := movR_ok s₂a .ebx .edi
  obtain ⟨s₂, e₂, r₂, -, o₂, m₂, rd₂, wr₂⟩ := addI_ok s₂b .ebx (BitVec.ofNat 32 (4 * tailSlot))
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂b, rd₂a, rd₁]
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂b, wr₂a, wr₁]
  obtain mem₂ : s₂.mem = s.mem := by rw [m₂, m₂b, m₂a, m₁]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [tailAddr, show ([movR .edx .esi] ++ [movR .ebx .edi, addI .ebx (BitVec.ofNat 32 (4 * tailSlot))] :
        List Instr) = [movR .edx .esi] ++ ([movR .ebx .edi] ++ [addI .ebx (BitVec.ofNat 32 (4 * tailSlot))])
        from rfl, runBlock_app, e₂a, Option.bind_some, runBlock_app, e₂b, Option.bind_some, e₂], ?_⟩)
  refine WP.seq (WP.mono (copyBlocks_wp (A := A) (B := T) hc0 hc8 hAn hTn
    (fun t ht h4 => by rw [rd₂', wr₂']; exact inRd (inA t ht h4))
    (fun t ht h4 => by rw [wr₂']; exact inT t ht h4) sepAT
    ⟨by rw [o₂ _ (by decide), o₂b _ (by decide), r₂a, esi₁]; simp [A],
      by rw [r₂, r₂b, o₂a _ (by decide), o₁ _ (by decide) (by decide) (by decide), hi.base]; simp [T],
      by rw [o₂ _ (by decide), o₂b _ (by decide), o₂a _ (by decide), ecx₁, Nat.sub_zero],
      ⟨fun t ht => by omega_arith, Frame.refl _ _⟩, fun _ _ _ _ _ => rfl, rfl, rfl⟩) fun s₃ h₃ => ?_)
  obtain f₃ : Frame [⟨T.setWidth 64, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact h₃.cp.frame
  obtain g₃ : ∀ r, r ≠ .edx → r ≠ .ebx → r ≠ .ecx → r ≠ .eax → s₃.gpr r = s₁.gpr r :=
    fun r h0 h1 h2 h3 => by rw [h₃.regs r h0 h1 h2 h3, o₂ r h1, o₂b r h1, o₂a r h0]
  obtain base₃ : s₃.gpr .edi = b := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide), o₁ _ (by decide) (by decide) (by decide), hi.base]
  obtain sc₃ : ScrOk s₀ b E s₃.mem := hi.scr.frame hfit' f₃ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dT.sub_left subTab
  obtain wr₃ : s₃.wr = s.wr := by rw [h₃.wr, wr₂']
  obtain rd₃ : s₃.rd = s.rd := by rw [h₃.rd, rd₂']
  obtain hwS₃ : ScrIn s₃.wr b := by rw [wr₃]; exact hwS
  -- The data pointer and the blocks left back to their slots.
  obtain ⟨s₄, e₄, dp₄, np₄, g₄, rd₄, wr₄, -, fs⟩ := stDN_ok s₃ base₃ hwS₃
  refine WP.of_runBlock ⟨s₄, e₄, ?_⟩
  obtain esi₃ : s₃.gpr .esi = A := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), esi₁]
  obtain ebp₃ : s₃.gpr .ebp = BitVec.ofNat 32 v := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide), ebp₁]
  rw [esi₃] at dp₄
  rw [ebp₃] at np₄
  obtain sc₄ : ScrOk s₀ b E s₄.mem := sc₃.frame hfit' fs dsTab
  obtain base₄ : s₄.gpr sb = b := by rw [g₄]; exact base₃
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃]
  -- The eight blocks.
  obtain hkey : KeyCtx s₄ E :=
    { scr := by rw [base₄, wr₄']; exact hwS
      keys := fun e he => by rw [base₄]; exact sc₄.keys e he }
  refine WP.seq (WP.mono (crypt8_wp hkey) fun s₅ ⟨c₅, b₅⟩ => ?_)
  obtain base₅ : s₅.gpr .edi = b := c₅.base.trans base₄
  obtain f₅ : Frame [⟨b.setWidth 64, 4 * tableSlot⟩] s₄.mem s₅.mem := by
    have := c₅.frame; rw [base₄] at this; exact this
  obtain keep₅ : ∀ j, tableSlot ≤ j → j < slots →
      s₅.mem.readW (wordAddr b j) 32 = s₄.mem.readW (wordAddr b j) 32 :=
    fun j h1 h2 => slot_keep hfit' (Nat.le_refl _) f₅
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dTab) h1 h2
  obtain sc₅ : ScrOk s₀ b E s₅.mem := sc₄.frame hfit' f₅ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dTab.sub_left subTab
  obtain wr₅ : s₅.wr = s.wr := by rw [c₅.wr, wr₄']
  obtain rd₅ : s₅.rd = s.rd := by rw [c₅.rd, rd₄, rd₃]
  obtain hwS₅ : ScrIn s₅.wr b := by rw [wr₅]; exact hwS
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp (A := A) base₅ hwS₅
    (by rw [keep₅ _ (by decide) (by decide)]; exact dp₄) (by rw [keep₅ _ (by decide) (by decide)]; exact np₄) hv)
    fun s₆ ⟨esi₆, ebp₆, ecx₆, o₆, m₆, rd₆, wr₆⟩ => ?_))
  obtain ⟨s₇a, e₇a, r₇a, o₇a, m₇a, rd₇a, wr₇a, -, -⟩ := movR_ok s₆ .edx .edi
  obtain ⟨s₇b, e₇b, r₇b, -, o₇b, m₇b, rd₇b, wr₇b⟩ := addI_ok s₇a .edx (BitVec.ofNat 32 (4 * tailSlot))
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇, -, -⟩ := movR_ok s₇b .ebx .esi
  obtain mem₇ : s₇.mem = s₅.mem := by rw [m₇, m₇b, m₇a, m₆]
  obtain rd₇' : s₇.rd = s.rd := by rw [rd₇, rd₇b, rd₇a, rd₆, rd₅]
  obtain wr₇' : s₇.wr = s.wr := by rw [wr₇, wr₇b, wr₇a, wr₆, wr₅]
  refine WP.seq (WP.of_runBlock ⟨s₇, by
    rw [tailAddr, show ([movR .edx .edi, addI .edx (BitVec.ofNat 32 (4 * tailSlot))] ++ [movR .ebx .esi] :
        List Instr) = [movR .edx .edi] ++ ([addI .edx (BitVec.ofNat 32 (4 * tailSlot))] ++ [movR .ebx .esi])
        from rfl, runBlock_app, e₇a, Option.bind_some, runBlock_app, e₇b, Option.bind_some, e₇], ?_⟩)
  refine WP.mono (copyBlocks_wp (A := T) (B := A) hc0 hc8 hTn hAn
    (fun t ht h4 => by rw [rd₇', wr₇']; exact inRd (inT t ht h4))
    (fun t ht h4 => by rw [wr₇']; exact inA t ht h4) sepAT.symm
    ⟨by rw [o₇ _ (by decide), r₇b, r₇a, o₆ _ (by decide) (by decide) (by decide), base₅]; simp [T],
      by rw [r₇, o₇b _ (by decide), o₇a _ (by decide), esi₆]; simp [A],
      by rw [o₇ _ (by decide), o₇b _ (by decide), o₇a _ (by decide), ecx₆, Nat.sub_zero],
      ⟨fun t ht => by omega_arith, Frame.refl _ _⟩, fun _ _ _ _ _ => rfl, rfl, rfl⟩) fun s₈ h₈ => ?_
  obtain f₈ : Frame [⟨A.setWidth 64, 16 * c⟩] s₅.mem s₈.mem := by rw [← mem₇]; exact h₈.cp.frame
  obtain g₈ : ∀ r, r ≠ .edx → r ≠ .ebx → r ≠ .ecx → r ≠ .eax → s₈.gpr r = s₆.gpr r :=
    fun r h0 h1 h2 h3 => by rw [h₈.regs r h0 h1 h2 h3, o₇ r h1, o₇b r h0, o₇a r h0]
  obtain sc₈ : ScrOk s₀ b E s₈.mem := sc₅.frame hfit' f₈ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dA.sub_left subTab
  obtain wr₈ : s₈.wr = s.wr := by rw [h₈.wr, wr₇']
  obtain rd₈ : s₈.rd = s.rd := by rw [h₈.rd, rd₇']
  -- The blocks the eight-block code read are the group's, as on entry.
  obtain hblk : ∀ j < c, tailBlock s₄ j =
      Spec.Sm4.blockAt s₀.mem (D.setWidth 64 + BitVec.ofNat 64 (16 * (8 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [tailBlock, Spec.Sm4.blockAt, Vector.getElem_ofFn]
    have := h₃.cp.copied (16 * j + u) (by omega_arith)
    rw [hT, VG.Offset.add_add, hA, VG.Offset.add_add] at this
    obtain hout : ∀ r ∈ [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩],
        ¬ r.Contains (b.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + (16 * j + u))) 1 := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> rw [slot_addr (by (try simp only [dSlot_eq, nSlot_eq]); omega_arith)] <;>
        exact not_contains_off _ (by (try simp only [tailSlot_eq, dSlot_eq, nSlot_eq]); omega_arith)
          (by rw [tailSlot_eq]; omega_arith) (by omega_arith) (by (try simp only [dSlot_eq, nSlot_eq]); omega_arith)
    rw [base₄, VG.Offset.add_add, show 4 * tailSlot + 16 * j + u = 4 * tailSlot + (16 * j + u) by omega_arith,
      fs _ hout, this, mem₂, hi.data _ (by omega_arith), ite_eq_right (by omega_arith), VG.Offset.add_add,
      show 128 * k + (16 * j + u) = 16 * (8 * k + j) + u by omega_arith]
  obtain hdata : DInv s₀.mem s₈.mem (D.setWidth 64) n (8 * k + c) (outF s₀.mem (D.setWidth 64) E) := by
    intro i hin
    by_cases hin1 : 128 * k ≤ i ∧ i < 128 * k + 16 * c
    · have e1 : D.setWidth 64 + BitVec.ofNat 64 i = A.setWidth 64 + BitVec.ofNat 64 (i - 128 * k) := by
        rw [hA, VG.Offset.add_add, show 128 * k + (i - 128 * k) = i by omega_arith]
      rw [e1, h₈.cp.copied _ (by omega_arith), mem₇, ite_eq_left (show i < 16 * (8 * k + c) by omega_arith),
        show i / 16 = 8 * k + (i - 128 * k) / 16 by omega_arith, show i % 16 = (i - 128 * k) % 16 by omega_arith]
      obtain hj : (i - 128 * k) / 16 < c := by omega_arith
      obtain eT : T.setWidth 64 + BitVec.ofNat 64 (i - 128 * k) =
          (s₅.gpr sb).setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * ((i - 128 * k) / 16)) +
            BitVec.ofNat 64 ((i - 128 * k) % 16) := by
        rw [show s₅.gpr sb = b from base₅, hT, VG.Offset.add_add, VG.Offset.add_add,
          show 4 * tailSlot + 16 * ((i - 128 * k) / 16) + (i - 128 * k) % 16 = 4 * tailSlot + (i - 128 * k) by omega_arith]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (tailBlock s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega_arith), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨A.setWidth 64, 16 * c⟩ : Region)],
          ¬ r.Contains (D.setWidth 64 + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hA]
        exact not_contains_off _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      rw [f₈ _ hout,
        f₅.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)) (by simp only; omega_arith) hin,
        fs.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (dD hsub) (by simp only; omega_arith) hin,
        f₃.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subT) (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 128 * k
      · rw [ite_eq_left (show i < 16 * (8 * k) by omega_arith), ite_eq_left (show i < 16 * (8 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (8 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (8 * k + c) by omega_arith)]
  -- On to the next group.
  obtain esi₈ : s₈.gpr .esi = A := by rw [g₈ _ (by decide) (by decide) (by decide) (by decide), esi₆]
  obtain ebp₈ : s₈.gpr .ebp = BitVec.ofNat 32 v := by
    rw [g₈ _ (by decide) (by decide) (by decide) (by decide), ebp₆]
  unfold advance
  refine WP.seq (WP.mono (countR_wp ebp₈ hv) fun s₉ ⟨ecx₉, o₉, m₉, rd₉, wr₉⟩ => ?_)
  obtain ⟨s₁₀a, e₁₀a, r₁₀a, -, o₁₀a, m₁₀a, rd₁₀a, wr₁₀a⟩ := addI_ok s₉ .esi 128
  obtain ⟨s₁₀b, e₁₀b, r₁₀b, z₁₀b, o₁₀b, m₁₀b, rd₁₀b, wr₁₀b⟩ := subI_ok s₁₀a .ebp (s₁₀a.gpr .ecx)
  obtain base₁₀b : s₁₀b.gpr .edi = b := by
    rw [o₁₀b _ (by decide), o₁₀a _ (by decide), o₉ _ (by decide),
      g₈ _ (by decide) (by decide) (by decide) (by decide), o₆ _ (by decide) (by decide) (by decide), base₅]
  obtain wr₁₀b' : s₁₀b.wr = s.wr := by rw [wr₁₀b, wr₁₀a, wr₉, wr₈]
  obtain ⟨s₁₀, e₁₀, dp₁₀, np₁₀, g₁₀, rd₁₀, wr₁₀, z₁₀, fa⟩ := stDN_ok s₁₀b base₁₀b (by rw [wr₁₀b']; exact hwS)
  refine WP.of_runBlock ⟨s₁₀, by
    rw [show ([addI .esi 128, subR .ebp .ecx, st dSlot .esi, st nSlot .ebp] : List Instr) =
      [addI .esi 128] ++ ([subR .ebp .ecx] ++ [st dSlot .esi, st nSlot .ebp]) from rfl,
      runBlock_app, e₁₀a, Option.bind_some, runBlock_app,
      show runBlock isa [subR .ebp .ecx] s₁₀a = runBlock isa [subI .ebp (s₁₀a.gpr .ecx)] s₁₀a from rfl,
      e₁₀b, Option.bind_some, e₁₀], ?_⟩
  obtain ecx₁₀a : s₁₀a.gpr .ecx = BitVec.ofNat 32 c := by rw [o₁₀a _ (by decide), ecx₉]
  obtain ebp₁₀a : s₁₀a.gpr .ebp = BitVec.ofNat 32 v := by rw [o₁₀a _ (by decide), o₉ _ (by decide), ebp₈]
  obtain zz : s₁₀.zf = some (decide (v = c)) := by
    rw [z₁₀, z₁₀b, ebp₁₀a, ecx₁₀a, ofNat32_sub_beq (by omega_arith) (by omega_arith)]
  obtain hmem : ∀ i < 16 * n, s₁₀.mem (D.setWidth 64 + BitVec.ofNat 64 i) = s₈.mem (D.setWidth 64 + BitVec.ofNat 64 i) :=
    fun i hi' => by
      rw [fa.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (dD hsub) (by simp only; omega_arith) hi', m₁₀b, m₁₀a, m₉]
  obtain hdata' : DInv s₀.mem s₁₀.mem (D.setWidth 64) n (8 * k + c) (outF s₀.mem (D.setWidth 64) E) :=
    fun i hi' => by rw [hmem i hi']; exact hdata i hi'
  obtain mem₉' : s₁₀b.mem = s₈.mem := by rw [m₁₀b, m₁₀a, m₉]
  obtain sc₁₀ : ScrOk s₀ b E s₁₀.mem := (mem₉' ▸ sc₈).frame hfit' fa dsTab
  obtain g₁₀' : ∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .ecx → r ≠ .edx → r ≠ .ebx → r ≠ .eax → s₁₀.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by
      rw [g₁₀, o₁₀b r h2, o₁₀a r h1, o₉ r h3, g₈ r h4 h5 h3 h6, o₆ r h1 h2 h3, c₅.keep r
        (by simp only [VG.Impl.Aes.X86.tmpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
            exact ⟨h6, h5, h3, h4, h2⟩) h1, g₄, g₃ r h4 h5 h3 h6, o₁ r h1 h2 h3]
  obtain base₁₀ : s₁₀.gpr .edi = b := by
    rw [g₁₀' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hi.base]
  obtain esp₁₀ : s₁₀.gpr .esp = s₀.gpr .esp := by
    rw [g₁₀' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hi.esp]
  obtain rd₁₀' : s₁₀.rd = s₀.rd := by rw [rd₁₀, rd₁₀b, rd₁₀a, rd₉, rd₈, hi.rd]
  obtain wr₁₀' : s₁₀.wr = s₀.wr := by rw [wr₁₀, wr₁₀b', hi.wr]
  obtain fr : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨D.setWidth 64, 16 * n⟩] s₀.mem s₁₀.mem := by
    refine hi.frame.trans ((f₃.sub fun r hr => ⟨⟨b.setWidth 64, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((fs.sub fun r hr => ⟨⟨b.setWidth 64, 4 * slots⟩, List.mem_cons_self, hsub r hr⟩).trans
      ((f₅.sub fun r hr => ⟨⟨b.setWidth 64, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((f₈.sub fun r hr => ⟨⟨D.setWidth 64, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩).trans
      (mem₉' ▸ fa.sub fun r hr => ⟨⟨b.setWidth 64, 4 * slots⟩, List.mem_cons_self, hsub r hr⟩)))))
    · simp only [List.mem_singleton] at hr; subst hr; exact subT
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact subA
  by_cases hlt : v ≤ 8
  · have hn : 8 * k + c = n := by omega_arith
    refine .inl ⟨by rw [zz]; simp; omega_arith, base₁₀, esp₁₀, sc₁₀, by have := hdata'; rw [hn] at this; exact this, fr, rd₁₀', wr₁₀'⟩
  · have hc : c = 8 := by omega_arith
    refine .inr ⟨by rw [zz]; simp; omega_arith, base₁₀, esp₁₀, ?_, ?_, by omega_arith, sc₁₀,
      by rw [show 8 * (k + 1) = 8 * k + c by omega_arith]; exact hdata', fr, rd₁₀', wr₁₀'⟩
    · rw [dp₁₀, o₁₀b _ (by decide), r₁₀a, o₉ _ (by decide), esi₈]
      simp only [A]
      rw [show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, VG.Offset.add_add,
        show 128 * k + 128 = 128 * (k + 1) by omega_arith]
    · rw [np₁₀, r₁₀b, ebp₁₀a, ecx₁₀a, VG.Offset.ofNat_sub_ofNat (by omega_arith), show v - c = n - 8 * (k + 1) by omega_arith]

/-- The data loop. -/
theorem dataLoop_wp {s₀ : State} {b D : BitVec 32} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {s : State} (hi : GInv s₀ b D n E 0 s) :
    WP isa (.loop group .ne) s (GDone s₀ b D n E) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 8 * k ∧ GInv s₀ b D n E k s) (fun m s hs => ?_) n s
    ⟨0, by omega_using [], hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (dataGroup_wp hp hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨(eval_ne s').trans (by rw [z]; rfl), d⟩
  · exact .inr ⟨(eval_ne s').trans (by rw [z]; rfl), n - 8 * (k + 1),
      by have := d.lt; have := hk.lt; omega_arith, k + 1, rfl, d⟩

end VG.Proof.Sm4.X86

end

end

/-!
# SM4 ECB on x86 (32-bit): the whole function

`ecb_wp`: with the working space as an argument (`ecbX86`), `ecb dir`
saves the callee-saved registers, builds the table of round keys in the
order `dir` uses them, keeps the data pointer and the count in their slots,
transforms the blocks a group at a time (`dataLoop_wp`) and restores the
registers.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.X86 VG.Impl.Sm4.X86

/-- The specification's direction. -/
def specDirX86 : Dir → Spec.Sm4.Direction
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- ECB on x86 with its working space as the fourth argument. -/
def ecbX86 (dir : Dir) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let data : Region := ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 4 * slots⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 * (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 4 * slots ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    Spec.Sm4.blocksAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      Spec.Sm4.ecb (Spec.Sm4.scheduleAt s.mem ((arg s 0).setWidth 64)) (specDirX86 dir)
        (Spec.Sm4.blocksAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

end VG.Proof.Sm4

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Impl.Aes.X86 (sb slotAt st argOp at_)
open VG.Proof.Sm4 (DInv blocksAt_of_dinv ecb_eq blockFn specDirX86 ecbX86 crypt_eq quads ofBlock outBlock)

theorem outF_spec (dir : Dir) (m : Mem) (sch : Spec.Sm4.Schedule) (D : Addr) (j : Nat) :
    outF m D (dirKeys dir sch) j =
      blockFn sch (specDirX86 dir) (Spec.Sm4.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  cases dir
  · simp only [outF, blockFn, specDirX86, Spec.Sm4.encryptBlock, crypt_eq]; rfl
  · simp only [outF, blockFn, specDirX86, Spec.Sm4.decryptBlock, crypt_eq]; rfl

/-! ## The arguments -/

theorem ea_arg {s₀ s : State} (h : s.gpr .esp = s₀.gpr .esp) (i : Nat) : s.ea (argOp i) = argAddr s₀ i := by
  show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = _
  rw [h]; rfl

/-- Argument `i` is in the arguments' region. -/
theorem arg_contains (s : State) (hfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat} (hi : i < 4) :
    (⟨argAddr s 0, 16⟩ : Region).Contains (argAddr s i) 4 := by
  obtain hs := setWidth_toNat (s.gpr .esp)
  rw [show argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) from addr_eq (by omega_using [hfit, hi]),
    show argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from addr_eq (by omega_using [hfit])]
  exact VG.Offset.contains _ (by omega_using []) (by omega_using [hi]) (by omega_using [])

/-- `mov eax, [esp + 4 + 4 i]; mov [edi + 4 k], eax`. -/
theorem argSlot_ok (s : State) {b : BitVec 32} {i k : Nat} (hb : s.gpr .edi = b) (hk : k < slots)
    (hw : ScrIn s.wr b) (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (argOp i)), .store (slotAt .edi k) .eax] s = some s' ∧
      s'.gpr .eax = s.mem.readW (s.ea (argOp i)) 32 ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (wordAddr b k) (s.mem.readW (s.ea (argOp i)) 32) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨wordAddr b k, 4⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax i ha
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, -, -, f₂⟩ := stSlot_ok s₁ .eax .edi (k := k) (by rw [o₁ _ (by decide), hb]) hk
    (by rw [wr₁]; exact hw)
  refine ⟨s₂, ?_, by rw [g₂, v₁], fun r hr => by rw [g₂, o₁ r hr], by rw [m₂, v₁, m₁], by rw [rd₂, rd₁],
    by rw [wr₂, wr₁], by rw [← m₁]; exact f₂⟩
  rw [show ([.mov .eax (.mem (argOp i)), .store (slotAt .edi k) .eax] : List Instr) =
    [.mov .eax (.mem (argOp i))] ++ [.store (slotAt .edi k) .eax] from rfl, runBlock_app, e₁, Option.bind_some, e₂]

/-! ## The function -/

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : (ecbX86 dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => abiPreserved s₀ s' ∧ (ecbX86 dir).post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dDS, dAD, dAS, dRD, dRS, fitK, fitD, fitB, fitE⟩ := hp
  let sched := arg s₀ 0
  let D := arg s₀ 1
  let n := (arg s₀ 2).toNat
  let b := arg s₀ 3
  have hfit' : b.toNat + 4 * slots ≤ 2 ^ 32 := fitB
  obtain hwS : ScrIn s₀.wr b := .exact (by rw [hwr]; simp [b]) fitB
  obtain hwD : (⟨D.setWidth 64, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  obtain hrK : (⟨sched.setWidth 64, 128⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  obtain hrA : (⟨argAddr s₀ 0, 16⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  -- The arguments, through writes of the scratch buffer.
  obtain argR : ∀ {m : Mem}, Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem m → ∀ i < 4,
      m.readW (argAddr s₀ i) 32 = arg s₀ i := fun hf i hi =>
    hf.readW (arg_contains s₀ fitE hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAS) (by decide)
  obtain argIn : ∀ {s : State}, s.rd = s₀.rd → s.wr = s₀.wr → s.gpr .esp = s₀.gpr .esp → ∀ i < 4,
      InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4 := fun h1 h2 h3 i hi => by
    rw [h1, h2, ea_arg h3]; exact ⟨_, List.mem_append_left _ hrA, arg_contains s₀ fitE hi⟩
  obtain subS : ∀ k < slots, Region.Sub ⟨wordAddr b k, 4⟩ ⟨b.setWidth 64, 4 * slots⟩ :=
    fun k hk => slot_sub hfit' hk
  unfold ecb
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, rd₁, wr₁, f₁, -⟩ := save_ok (k := 3) hwS (argIn rfl rfl rfl 3 (by decide))
    (by rw [ea_arg rfl]; rfl)
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  obtain esp₁ : s₁.gpr .esp = s₀.gpr .esp := g₁ _ (by decide) (by decide)
  obtain hk₁ : SchedPre s₁ b sched :=
    ⟨b₁, by rw [wr₁]; exact hwS, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dKS⟩
  -- The table.
  refine WP.seq (WP.mono (keys_wp dir hk₁ (argIn rd₁ wr₁ esp₁ 0 (by decide))
    (by rw [ea_arg esp₁]; exact argR f₁ 0 (by decide))) fun s₂ k₂ => ?_)
  let E : Nat → Spec.Sm4.Word := dirKeys dir (Spec.Sm4.scheduleAt s₀.mem (sched.setWidth 64))
  obtain hsch : Spec.Sm4.scheduleAt s₁.mem (sched.setWidth 64) = Spec.Sm4.scheduleAt s₀.mem (sched.setWidth 64) :=
    hk₁.sched_eq (Nat.le_refl _) f₁
  obtain f₀₂ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₂.mem :=
    f₁.trans (k₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [tableEnd_eq, slots_eq]; omega_using [])⟩)
  have base₂ : s₂.gpr sb = b := k₂.pre.base
  obtain esp₂ : s₂.gpr .esp = s₀.gpr .esp := by
    rw [k₂.regs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), esp₁]
  obtain sc₂ : ScrOk s₀ b E s₂.mem := by
    refine ⟨fun e he => ?_, fun i hi => ?_⟩
    · have := k₂.key.keys e he
      rw [base₂, hsch] at this
      exact this
    · rw [← sv₁ i hi]
      exact slot_keep hfit' (lo := tableEnd) (hi := slots) (Nat.le_refl _) k₂.frame
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by rw [tableEnd_eq, slots_eq]; decide))
        (by rw [savedSlot_eq, tableEnd_eq]; omega_using []) (by rw [savedSlot_eq, slots_eq]; omega_using [hi])
  obtain rd₂ : s₂.rd = s₀.rd := by rw [k₂.rd, rd₁]
  obtain wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, wr₁]
  -- The data pointer and the count to their slots.
  obtain ⟨s₃a, e₃a, a₃a, o₃a, m₃a, rd₃a, wr₃a, f₃a⟩ := argSlot_ok s₂ (i := 1) (k := dSlot) base₂ (by decide)
    (by rw [wr₂]; exact hwS) (argIn rd₂ wr₂ esp₂ 1 (by decide))
  obtain f₀₃a : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₃a.mem :=
    f₀₂.trans (f₃a.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact subS _ (by decide)⟩)
  obtain esp₃a : s₃a.gpr .esp = s₀.gpr .esp := by rw [o₃a _ (by decide), esp₂]
  obtain ⟨s₃b, e₃b, a₃b, o₃b, m₃b, rd₃b, wr₃b, f₃b⟩ := argSlot_ok s₃a (i := 2) (k := nSlot)
    ((o₃a _ (by decide)).trans base₂) (by decide) (by rw [wr₃a, wr₂]; exact hwS)
    (argIn (by rw [rd₃a, rd₂]) (by rw [wr₃a, wr₂]) esp₃a 2 (by decide))
  let s₃ := arithFlags s₃b (s₃b.gpr .eax &&& s₃b.gpr .eax) false false
  obtain e₃ : runBlock isa [.mov .eax (.mem (argOp 1)), st dSlot .eax, .mov .eax (.mem (argOp 2)), st nSlot .eax,
      .alu .test .eax (.reg .eax)] s₂ = some s₃ := by
    rw [show ([.mov .eax (.mem (argOp 1)), st dSlot .eax, .mov .eax (.mem (argOp 2)), st nSlot .eax,
        .alu .test .eax (.reg .eax)] : List Instr) =
      [.mov .eax (.mem (argOp 1)), .store (slotAt .edi dSlot) .eax] ++
        ([.mov .eax (.mem (argOp 2)), .store (slotAt .edi nSlot) .eax] ++ [.alu .test .eax (.reg .eax)]) from rfl,
      runBlock_app, e₃a, Option.bind_some, runBlock_app, e₃b, Option.bind_some]
    rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  obtain eax₃ : s₃b.gpr .eax = arg s₀ 2 := by
    rw [a₃b, ea_arg esp₃a]; exact argR f₀₃a 2 (by decide)
  obtain dp₃ : s₃.mem.readW (wordAddr b dSlot) 32 = D := by
    show s₃b.mem.readW _ 32 = _
    rw [m₃b, readW_slot_write hfit' (j := dSlot) (k := nSlot) _ (by decide) (by decide), ite_eq_right (by decide),
      m₃a, readW_slot_write hfit' (j := dSlot) (k := dSlot) _ (by decide) (by decide), ite_eq_left rfl,
      ea_arg esp₂]
    exact argR f₀₂ 1 (by decide)
  obtain np₃ : s₃.mem.readW (wordAddr b nSlot) 32 = BitVec.ofNat 32 n := by
    show s₃b.mem.readW _ 32 = _
    rw [m₃b, readW_slot_write hfit' (j := nSlot) (k := nSlot) _ (by decide) (by decide), ite_eq_left rfl,
      ← a₃b, eax₃]
    simp only [n, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain f₃ : Frame [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩] s₂.mem s₃.mem :=
    (f₃a.sub fun r hr => ⟨r, by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self, fun _ h => h⟩).trans
      (f₃b.sub fun r hr => ⟨r, by
        rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩)
  obtain sc₃ : ScrOk s₀ b E s₃.mem := sc₂.frame hfit' f₃ (dn_disj hfit')
  obtain f₀₃ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₃.mem :=
    f₀₂.trans (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, dn_sub hfit' r hr⟩)
  obtain data₃ : ∀ i < 16 * n, s₃.mem (D.setWidth 64 + BitVec.ofNat 64 i) = s₀.mem (D.setWidth 64 + BitVec.ofNat 64 i) :=
    fun i hi => f₀₃.bytes (R := ⟨D.setWidth 64, 16 * n⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS) (by simp only; omega_using []) hi
  obtain fr₃ : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨D.setWidth 64, 16 * n⟩] s₀.mem s₃.mem :=
    f₀₃.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  obtain g₃ : ∀ r, r ≠ .eax → s₃.gpr r = s₂.gpr r := fun r hr => by
    show s₃b.gpr r = _; rw [o₃b r hr, o₃a r hr]
  obtain base₃ : s₃.gpr .edi = b := by rw [g₃ _ (by decide)]; exact base₂
  obtain esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [g₃ _ (by decide), esp₂]
  obtain rd₃ : s₃.rd = s₀.rd := by show s₃b.rd = _; rw [rd₃b, rd₃a, rd₂]
  obtain wr₃ : s₃.wr = s₀.wr := by show s₃b.wr = _; rw [wr₃b, wr₃a, wr₂]
  obtain hz₃ : s₃.zf = some (decide (n = 0)) := by
    rw [RegUpd.zf_arithFlags, eax₃, BitVec.and_self]
    refine congrArg some (Bool.eq_iff_iff.mpr ?_)
    rw [beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by simp only [n, h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  -- The groups.
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n E)
    (WP.ite (decide (n = 0)) ((eval_e s₃).trans hz₃) (fun h0 => ?_) (fun h0 => ?_)) fun s₅ d₅ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨base₃, esp₃, sc₃, fun i hi => by omega, fr₃, rd₃, wr₃⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS, fitD⟩ ⟨base₃, esp₃, by rw [dp₃]; simp,
      by rw [np₃, Nat.mul_zero, Nat.sub_zero], by omega_using [hn0], sc₃, fun i hi => ?_, fr₃, rd₃, wr₃⟩
    rw [data₃ i hi, ite_eq_right (by omega_using [])]
  -- The epilogue.
  obtain ⟨s₆, e₆, rg₆, o₆, m₆, -, -⟩ := restore_ok (s₀ := s₀) (b := b) (by rw [d₅.wr]; exact hwS) d₅.base
    d₅.scr.saved
  refine WP.of_runBlock ⟨s₆, e₆, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rg₆ 0 (by decide)
    · exact rg₆ 1 (by decide)
    · exact rg₆ 2 (by decide)
    · exact rg₆ 3 (by decide)
    · rw [o₆ _ (fun i hi => by revert i; decide), d₅.esp]
  · rw [m₆]
    exact d₅.frame.readW (r := ⟨(s₀.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dRS
      · exact dRD) (by decide)
  · have hd₆ : DInv s₀.mem s₆.mem (D.setWidth 64) n n (outF s₀.mem (D.setWidth 64) E) := fun i hi => by
      rw [m₆]; exact d₅.data i hi
    show Spec.Sm4.blocksAt s₆.mem (D.setWidth 64) n = _
    rw [blocksAt_of_dinv hd₆, ecb_eq]
    simp only [Spec.Sm4.blocksAt, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    exact outF_spec dir s₀.mem _ _ j

end VG.Proof.Sm4.X86
