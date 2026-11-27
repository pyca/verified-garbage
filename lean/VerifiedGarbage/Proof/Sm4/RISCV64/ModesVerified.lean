module

public import VerifiedGarbage.Proof.Sm4.RISCV64.ModesConstantTime
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Spec.Sm4.Cfb
public import VerifiedGarbage.Spec.Sm4.Ofb
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Modes.RISCV64.Modes
import VerifiedGarbage.Proof.Modes.RISCV64.Wide
import VerifiedGarbage.Proof.Modes.RISCV64.WideCtr
public import VerifiedGarbage.Proof.Modes.RISCV64.Seq
public import VerifiedGarbage.Proof.Modes.Steps
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sm4.RISCV64.ModesConstantTime
meta import VerifiedGarbage.Spec.Sm4.Cbc
meta import VerifiedGarbage.Spec.Sm4.Cfb
meta import VerifiedGarbage.Spec.Sm4.Ofb
meta import VerifiedGarbage.Spec.Sm4.Ctr
meta import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Modes.RISCV64.Shared
public import VerifiedGarbage.Impl.Sm4.RISCV64.Modes
public import VerifiedGarbage.Proof.Sm4.RISCV64.Ecb
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit
public import VerifiedGarbage.Impl.Sm4.RISCV64.Prepared
import VerifiedGarbage.Proof.Sm4.Planes
public import VerifiedGarbage.Proof.Sm4.Prepared
meta import VerifiedGarbage.Proof.Modes.RISCV64.Shared
meta import VerifiedGarbage.Impl.Sm4.RISCV64.Modes
meta import VerifiedGarbage.Proof.Sm4.RISCV64.Ecb
meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.Interleave
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Sm4.CtrCipher
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit
meta import VerifiedGarbage.Impl.Sm4.RISCV64.Prepared
meta import VerifiedGarbage.Proof.Sm4.Planes
meta import VerifiedGarbage.Proof.Sm4.Prepared

/-! ### `Sm4.RISCV64.ModeCore`, which only this module used -/

section

/-! ### `Sm4.RISCV64.PreparedBody`, which this module and modules that import it used -/

section

/-!
# SM4's prepared round keys and batches on RISCV64: two facts

`entryW_eq`: an entry of the table, as a word of the working space.
`quads_spec`: the rounds with the round keys in the order of a direction
are its cipher.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Sm4.RISCV64
open VG.Impl.Aes.RISCV64 (sb t0 t1 movR stS)
open VG.Proof.Sm4 (WordRel specDirRISCV64)

/-! ## The encoding -/

theorem entryW_eq (m : Mem) (B : Addr) (e j : Nat) :
    entryW m B e j = m.readW (wordAddr B (tableSlot + 8 * e + j)) 64 := by
  rw [entryW, wordAddr, show 8 * (tableSlot + 8 * e + j) = 8 * tableSlot + 64 * e + 8 * j by omega_arith]

/-! ## The bodies -/

/-- The rounds with the round keys in the order of `d` are its cipher. -/
theorem quads_spec (d : Dir) (sch : Spec.Sm4.Schedule) (blk : Spec.Sm4.Block) :
    Proof.Sm4.outBlock (Proof.Sm4.quads .enc (dirKeys d sch) 8 (Proof.Sm4.ofBlock blk)) =
      Proof.Sm4.blockFn sch (specDirRISCV64 d) blk := by
  cases d
  · simp only [Proof.Sm4.blockFn, specDirRISCV64, Spec.Sm4.encryptBlock, Proof.Sm4.crypt_eq]; rfl
  · simp only [Proof.Sm4.blockFn, specDirRISCV64, Spec.Sm4.decryptBlock, Proof.Sm4.crypt_eq]; rfl

end VG.Proof.Sm4.RISCV64

end

end

/-!
# SM4's core for the modes on RISC-V

`inlineCoreSpec d`: SM4's core for the direction `d`
(`Impl.Sm4.RISCV64.inlineCore d`) meets what the modes need of a core
(`Proof.Modes.RISCV64.CoreSpec`), with the key a schedule, its cipher
`Spec.Sm4.cipher` for encryption and `Spec.Sm4.invCipher` for decryption,
as on PPC64LE (`Proof/Sm4/PPC64LE/ModesVerified.lean`).

The core runs ECB's code on ECB's scratch buffer `ecbOff` bytes into the
frame (at `E`), which ECB's proofs take for one writable region: they run
from the state with that region added (`WP.narrow`), whose runs are runs
from the state itself (`Exec.widen`). `prepare` (`prepare_wp`) is ECB's
prologue, the table (`keys_wp`) and ECB's epilogue; `crypt` (`crypt_wp`) is
ECB's prologue, the sixteen blocks (`crypt16_wp`) and its epilogue. Around
them the modes' `s1`–`s3` wait in `a1`, `a2` and `a4` (`unpark_wp`), and the
key argument in the core's first slot. `Ready` is ECB's masks and table at
`E`, which the mode, writing outside the core's slots or within its buffer,
keeps.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64.Mode

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Straight VG.Impl.Sm4.RISCV64 VG.Proof.Sm4.RISCV64
open VG.Impl.Aes.RISCV64 (sb movR t0 t1)
open VG.Proof.Modes.RISCV64 (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept KeptBut)
open VG.Proof.Sm4 (specDirRISCV64)
open VG.Spec.Aes (bytesAt)

/-! ## Running ECB's code with its scratch buffer one region -/

/-- A run from `s` with the region `R`, inside a writable region of `s`,
added to its writable regions is a run from `s`. -/
theorem WP.narrow {c : Prog isa} {s : State} {R : Region} (hR : InRegions s.wr R.base R.len)
    {Q : State → Prop} (h : WP isa c (s.withRegions s.rd (R :: s.wr)) fun u => Q (u.withRegions s.rd s.wr)) :
    WP isa c s Q := by
  obtain ⟨t, u, he, hq⟩ := h
  obtain hw : Covers (R :: s.wr) s.wr := Covers.cons (Covers.one hR) (Covers.refl _)
  have := Exec.widen he (rd := s.rd) (wr := s.wr) (Covers.append (Covers.refl _) hw) hw
  rw [State.withRegions_withRegions, State.withRegions_self] at this
  exact ⟨t, _, this, hq⟩

/-- ECB's base in the frame at `B`. -/
abbrev ecbA (B : Addr) : Addr := B + BitVec.ofNat 64 56

/-- The key argument's slot in the frame at `B`. -/
abbrev keyA (B : Addr) : Addr := B + BitVec.ofNat 64 48

theorem ecbOff_eq : ecbOff = 56 := rfl
theorem keySlot_eq : keySlot = 6 := rfl

theorem preserved_sreg : RISCV64.preserved = (List.range 12).map sreg := by decide

/-- ECB's epilogue: the caller's registers from their slots, the modes' state
from `a1`, `a2` and `a4`, the frame's base, and the key argument from its
slot. -/
theorem unpark_wp {s₀ s : State} {B : Addr} {Q : State → Prop} (hb : s.gpr sb = ecbA B)
    (hw : (⟨ecbA B, 8 * slots⟩ : Region) ∈ s.wr) (hal : (ecbA B).toNat % 8 = 0) (hs : Saved s₀ (ecbA B) s.mem)
    (hk : InRegions (s.rd ++ s.wr) (keyA B) 8) (hkal : (keyA B).toNat % 8 = 0)
    (k : ∀ s', s'.gpr .s1 = s.gpr .a1 → s'.gpr .s2 = s.gpr .a2 → s'.gpr .s3 = s.gpr .a4 → s'.gpr .s4 = B →
      s'.gpr .a0 = s.mem.readW (keyA B) 64 →
      (∀ r ∈ RISCV64.preserved, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s'.gpr r = s₀.gpr r) →
      (∀ r, r ∉ RISCV64.preserved → r ≠ t0 → r ≠ .a0 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block unpark) s Q := by
  obtain ⟨s₁, e₁, rg₁, o₁, m₁, rd₁, wr₁⟩ := restore_ok hw hb hal hs
  rw [unpark, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, e₁, ?_⟩
  obtain nsreg : ∀ r, r ∉ RISCV64.preserved → ∀ i < 12, r ≠ sreg i := fun r hr i hi h =>
    hr (by rw [preserved_sreg, h]; exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  obtain o₁' : ∀ r, r ∉ RISCV64.preserved → r ≠ t0 → s₁.gpr r = s.gpr r := fun r hr h0 =>
    o₁ r (nsreg r hr) h0
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => ?_
  refine wp_subi (by decide) fun s₅ u₅ => ?_
  obtain s4₅ : s₅.gpr Impl.Modes.RISCV64.sb = B := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      o₁' _ (by decide) (by decide), hb, ecbOff_eq, BitVec.add_sub_cancel]
  refine wp_ld (a := keyA B) (by decide) (by rw [s4₅, keySlot_eq]) hkal
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, rd₁, wr₁]; exact hk) fun s₆ u₆ => ?_
  obtain m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  refine WP.block_nil (k s₆ ?_ ?_ ?_ ?_ ?_ (fun r hr h1 h2 h3 h4 => ?_) (fun r hr h0 ha => ?_) ?_ ?_ ?_)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, o₁' _ (by decide) (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), o₁' _ (by decide) (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), o₁' _ (by decide) (by decide)]
  · exact (u₆.other _ (by decide)).trans s4₅
  · rw [u₆.gpr, m₅]
  · have ha : r ≠ .a0 := by rintro rfl; exact absurd hr (by decide)
    rw [preserved_sreg] at hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    rw [u₆.other _ ha, u₅.other _ h4, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1,
      rg₁ i (List.mem_range.mp hi)]
  · have h1 : r ≠ .s1 := by rintro rfl; exact hr (by decide)
    obtain h2 : r ≠ .s2 := by rintro rfl; exact hr (by decide)
    obtain h3 : r ≠ .s3 := by rintro rfl; exact hr (by decide)
    obtain h4 : r ≠ .s4 := by rintro rfl; exact hr (by decide)
    rw [u₆.other _ ha, u₅.other _ h4, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, o₁' r hr h0]
  · rw [u₆.mem, m₅]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]

/-- ECB's base and prologue: the caller's registers in their slots. -/
theorem coreIn_wp {s : State} {B : Addr} {rest : List Instr} {Q : State → Prop}
    (hB : s.gpr Impl.Modes.RISCV64.sb = B) (hw : (⟨ecbA B, 8 * slots⟩ : Region) ∈ s.wr)
    (hal : (ecbA B).toNat % 8 = 0)
    (k : ∀ s', s'.gpr sb = ecbA B → Saved s (ecbA B) s'.mem → (∀ r, r ≠ sb → r ≠ t0 → s'.gpr r = s.gpr r) →
      Frame [⟨ecbA B + BitVec.ofNat 64 (8 * savedSlot), 96⟩] s.mem s'.mem →
      (∀ j, j < savedSlot → s'.mem.readW (wordAddr (ecbA B) j) 64 = s.mem.readW (wordAddr (ecbA B) j) 64) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block rest) s' Q) :
    WP isa (.block (coreIn ++ rest)) s Q := by
  rw [coreIn, List.append_assoc, List.singleton_append]
  refine wp_addi (by decide) fun s₁ u₁ => ?_
  obtain b₁ : s₁.gpr sb = ecbA B := by rw [u₁.gpr, hB]; rfl
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, -, k₂, f₂⟩ := save_ok (b := ecbA B) (by rw [u₁.wr]; exact hw) b₁ hal
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₂, e₂, k s₂ (by rw [g₂ _ sb_ne_t0, b₁]) (fun i hi => ?_) (fun r h1 h2 => ?_)
    (by rw [← u₁.mem]; exact f₂) (fun j hj => ?_) (by rw [rd₂, u₁.rd]) (by rw [wr₂, u₁.wr])⟩
  · rw [sv₂ i hi, u₁.other _ (sreg_ne_sb i hi)]
  · rw [g₂ r h2, u₁.other r h1]
  · have := k₂ j hj
    simp only [slotW, g₂ _ sb_ne_t0, b₁] at this
    rw [this, u₁.mem]

/-- The modes' state to `a1`, `a2` and `a4`. -/
theorem park_wp {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .a1 = s.gpr .s1 → s'.gpr .a2 = s.gpr .s2 → s'.gpr .a4 = s.gpr .s3 →
      (∀ r, r ≠ .a1 → r ≠ .a2 → r ≠ .a4 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block rest) s' Q) :
    WP isa (.block (park ++ rest)) s Q := by
  rw [park]
  simp only [movR, List.cons_append, List.nil_append]
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => ?_
  refine k s₃ ?_ ?_ ?_ (fun r h1 h2 h4 => by rw [u₃.other r h4, u₂.other r h2, u₁.other r h1])
    (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]

/-! ## The key -/

/-- The schedule at `a0`. -/
abbrev keyR (s : State) : Region := ⟨s.gpr .a0, 128⟩

/-- The schedule at `a0` is `k`, readable, not wrapping around, and apart
from the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Sm4.Schedule) : Prop :=
  Spec.Sm4.scheduleAt s.mem (s.gpr .a0) = k ∧ keyR s ∈ s.rd ++ s.wr ∧ (s.gpr .a0).toNat + 128 ≤ 2 ^ 64 ∧
    ∀ r ∈ rs, (keyR s).Disjoint r

/-- ECB's masks and its table of the round keys `k` in the order of `d`, in
ECB's scratch buffer in the frame at `B`. -/
def Ready (d : Dir) (s : State) (B : Addr) (_ws : List Region) (k : Spec.Sm4.Schedule) : Prop :=
  (∀ kv ∈ maskCs, s.mem.readW (wordAddr (ecbA B) kv.1) 64 = kv.2) ∧
    (∀ e < 32, VG.Proof.Sm4.WordRel (entryW s.mem (ecbA B) e) fun _ => dirKeys d k e) ∧
    s.mem.readW (keyA B) 64 = s.gpr .a0

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Sm4.Schedule} (h : KeyArgs s rs k)
    (e : s'.gpr .a0 = s.gpr .a0) (hrd : s'.rd = s.rd) (hwr : ∃ ws, s'.wr = ws ++ s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨hk, hin, hfit, hd⟩ := h
  obtain ⟨ws, hw⟩ := hwr
  refine ⟨?_, ?_, by rw [e]; exact hfit, by rw [keyR, e]; exact hd⟩
  · rw [e, Proof.Sm4.scheduleAt_frame hf hd, hk]
  · rw [hrd, hw, keyR, e]
    rcases List.mem_append.mp hin with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_append_right _ h)

/-- The cipher of the direction `d`. -/
def dirCipher : Dir → Spec.Sm4.Schedule → Spec.Cbc.Cipher
  | .encrypt => Spec.Sm4.cipher
  | .decrypt => Spec.Sm4.invCipher

theorem dirCipher_bytes (d : Dir) (k : Spec.Sm4.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (bytesAt m p 16) = (Proof.Sm4.blockFn k (specDirRISCV64 d) (Spec.Sm4.blockAt m p)).toList := by
  cases d
  · rw [dirCipher, Spec.Sm4.cipher, Proof.Sm4.bytesAt_eq_blockAt, Proof.Sm4.ofFn_toList]; rfl
  · rw [dirCipher, Spec.Sm4.invCipher, Proof.Sm4.bytesAt_eq_blockAt, Proof.Sm4.ofFn_toList]; rfl

theorem inlineLayout (d : Dir) : Layout (inlineCore d) :=
  ⟨by cases d <;> decide, .inr rfl, by cases d <;> decide, by cases d <;> decide, by cases d <;> decide,
    by cases d <;> decide, by cases d <;> decide⟩

/-- A word of ECB's scratch buffer outside the core's buffer, apart from what
the mode writes. -/
theorem word_apart (d : Dir) {B : Addr} {k : Nat} (hk : k < slots)
    (hkb : k < tailSlot ∨ tailSlot + 32 ≤ k) {r : Region}
    (hr : Region.Disjoint (coreRegion (inlineCore d) B) r ∨ Region.Sub r (blkRegion (inlineCore d) B)) :
    Region.Disjoint ⟨wordAddr (ecbA B) k, 8⟩ r := by
  rw [slots_eq] at hk
  rw [tailSlot_eq] at hkb
  obtain e : wordAddr (ecbA B) k = B + BitVec.ofNat 64 (56 + 8 * k) := by rw [wordAddr, Offset.add_add]
  rw [e]
  rcases hr with hr | hr
  · refine hr.sub_left ?_
    show Region.Sub _ ⟨B + BitVec.ofNat 64 (8 * 6), 8 * (404 - 6)⟩
    exact Offset.sub B (by omega_using []) (by omega_using [hk])
  · refine Region.Disjoint.sub_right ?_ hr
    show Region.Disjoint _ ⟨B + BitVec.ofNat 64 (8 * 103), 4 * 4 * 16⟩
    exact Offset.disjoint B (by omega_using [hkb]) (by omega_using [hk]) (by omega_using [])

theorem ready_frame (d : Dir) {s s' : State} {B : Addr} {ws : List Region} {k : Spec.Sm4.Schedule}
    {rs : List Region} (h : Ready d s B ws k) (ha : s'.gpr .a0 = s.gpr .a0) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (inlineCore d) B) r ∨ Region.Sub r (blkRegion (inlineCore d) B)) :
    Ready d s' B ws k := by
  obtain ⟨hm, hk, hka⟩ := h
  obtain keep : ∀ j < slots, (j < tailSlot ∨ tailSlot + 32 ≤ j) →
      s'.mem.readW (wordAddr (ecbA B) j) 64 = s.mem.readW (wordAddr (ecbA B) j) 64 := fun j hj hjb =>
    hf.readW (Region.contains_self _ _) (fun r hr => word_apart d hj hjb (hd r hr)) (by decide)
  refine ⟨fun kv hkv => ?_, fun e he => (hk e he).congr fun j hj => ?_, ?_⟩
  · have := masks_range kv hkv
    rw [keep _ (by rw [slots_eq]; omega_using [this]) (.inl (by rw [tailSlot_eq]; omega_using [this]))]
    exact hm kv hkv
  · rw [entryW_eq, entryW_eq, keep _ (by rw [tableSlot_eq, slots_eq]; omega_using [he, hj])
      (.inr (by rw [tableSlot_eq, tailSlot_eq]; omega_using []))]
  · rw [ha, ← hka]
    refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases hd r hr with h | h
    · exact h.sub_left (show Region.Sub ⟨B + BitVec.ofNat 64 48, 8⟩ ⟨B + BitVec.ofNat 64 (8 * 6), 8 * (404 - 6)⟩
        from Offset.sub B (by decide) (by decide))
    · exact Region.Disjoint.sub_right (show Region.Disjoint _ ⟨B + BitVec.ofNat 64 (8 * 103), 4 * 4 * 16⟩ from
        Offset.disjoint B (.inl (by decide)) (by decide) (by decide)) h

/-! ## The core's code -/

theorem toNat_off {B : Addr} {o n : Nat} (h : B.toNat + n ≤ 2 ^ 64) (ho : o < n) :
    (B + BitVec.ofNat 64 o).toNat = B.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [h, ho]), Nat.mod_eq_of_lt (by omega_using [h, ho])]

theorem ecbA_add (B : Addr) (o : Nat) : ecbA B + BitVec.ofNat 64 o = B + BitVec.ofNat 64 (56 + o) :=
  Offset.add_add B 56 o

/-- A range of the frame within the core's slots. -/
theorem sub_core (d : Dir) (B : Addr) {o n : Nat} (h₁ : 48 ≤ o) (h₂ : o + n ≤ 3232) :
    Region.Sub ⟨B + BitVec.ofNat 64 o, n⟩ (coreRegion (inlineCore d) B) := by
  show Region.Sub _ ⟨B + BitVec.ofNat 64 (8 * 6), 8 * (404 - 6)⟩
  exact Offset.sub B (by omega_using [h₁]) (by omega_using [h₂])

theorem key_apart (B : Addr) {n : Nat} (hn : 56 + n ≤ 2 ^ 64) : Region.Disjoint ⟨keyA B, 8⟩ ⟨ecbA B, n⟩ :=
  Offset.disjoint B (.inl (by decide)) (by decide) hn

/-- ECB's code `body` and its epilogue, from the state `t` with the caller's
registers (those of `s₀`) saved, after parking. -/
theorem tail_wp {s₀ t : State} {B : Addr} {body : Prog isa} {P Q : State → Prop}
    (hbody : WP isa body t P)
    (hpost : ∀ u, P u → u.gpr sb = ecbA B ∧ (∀ r ∈ ([.ra, .a1, .a2, .a4] : List Reg), u.gpr r = t.gpr r) ∧
      Frame [⟨ecbA B, 8 * tableEnd⟩] t.mem u.mem ∧ u.rd = t.rd ∧ u.wr = t.wr)
    (hw : (⟨ecbA B, 8 * slots⟩ : Region) ∈ t.wr) (hal : (ecbA B).toNat % 8 = 0)
    (hsv : Saved s₀ (ecbA B) t.mem) (hk : InRegions (t.rd ++ t.wr) (keyA B) 8) (hkal : (keyA B).toNat % 8 = 0)
    (k : ∀ u v, P u → v.gpr .s1 = t.gpr .a1 → v.gpr .s2 = t.gpr .a2 → v.gpr .s3 = t.gpr .a4 → v.gpr .s4 = B →
      v.gpr .a0 = t.mem.readW (keyA B) 64 → v.gpr .ra = t.gpr .ra →
      (∀ r ∈ RISCV64.preserved, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → v.gpr r = s₀.gpr r) →
      v.mem = u.mem → v.rd = t.rd → v.wr = t.wr → v.mem.readW (keyA B) 64 = t.mem.readW (keyA B) 64 → Q v) :
    WP isa (.seq body (.block unpark)) t Q := by
  refine WP.seq (WP.mono hbody fun u hu => ?_)
  obtain ⟨hb, hr, hf, hrd, hwr⟩ := hpost u hu
  obtain sv : Saved s₀ (ecbA B) u.mem := fun i hi => by
    rw [← hsv i hi]
    refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base (ecbA B) (d := 8 * (savedSlot + i)) (by rw [tableEnd_eq, savedSlot_eq]; omega_using [])
      (by rw [savedSlot_eq]; omega_using [hi])
  obtain ka : u.mem.readW (keyA B) 64 = t.mem.readW (keyA B) 64 :=
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact key_apart B (by rw [tableEnd_eq]; decide)) (by decide)
  refine unpark_wp hb (by rw [hwr]; exact hw) hal sv (by rw [hrd, hwr]; exact hk) hkal
    fun v s1 s2 s3 s4 a0 pr ot m rd wr => k u v hu ?_ ?_ ?_ s4 ?_ ?_ pr m (by rw [rd, hrd]) (by rw [wr, hwr])
      (by rw [m, ka])
  · rw [s1, hr .a1 (by decide)]
  · rw [s2, hr .a2 (by decide)]
  · rw [s3, hr .a4 (by decide)]
  · rw [a0, ka]
  · rw [ot .ra (by decide) (by decide) (by decide), hr .ra (by decide)]

theorem prepare_wp (d : Dir) {s : State} {B : Addr} {rs : List Region} {k : Spec.Sm4.Schedule}
    (hB : s.gpr Impl.Modes.RISCV64.sb = B) (hS : ScrIn s B (inlineCore d).total)
    (hm : (⟨B, 8 * (inlineCore d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa (inlineCore d).prepare s fun s' => Ready d s' B rs k ∧ s'.gpr Impl.Modes.RISCV64.sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (inlineCore d) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hkk, hin, hkfit, hd⟩ := hk
  have hfit : B.toNat + 8 * 404 ≤ 2 ^ 64 := hS.fit
  have hal : B.toNat % 16 = 0 := hS.al
  obtain hW : (⟨B, 8 * 404⟩ : Region) ∈ s.wr := hS.whole (by show 8 * 404 ≤ 4064; decide)
  obtain dK : (keyR s).Disjoint ⟨B, 8 * 404⟩ := hd _ hm
  obtain halE : (ecbA B).toNat % 8 = 0 := by rw [toNat_off hfit (by decide)]; omega_using [hal]
  obtain halK : (keyA B).toNat % 8 = 0 := by rw [toNat_off hfit (by decide)]; omega_using [hal]
  refine WP.narrow (R := ⟨ecbA B, 8 * slots⟩) ⟨_, hW, Offset.contains_base B (by show 56 + 8 * 396 ≤ 8 * 404; decide) (by decide)⟩ ?_
  show WP isa (corePrepare d) _ _
  rw [corePrepare]
  simp only [List.append_assoc, List.singleton_append]
  refine WP.seq ?_
  refine wp_sd (a := keyA B) (by decide) (by show s.gpr _ + _ = _; rw [hB, keySlot_eq]) halK
    ⟨_, List.mem_cons_of_mem _ hW, Offset.contains_base B (by decide) (by decide)⟩ fun s₁ u₁ => ?_
  obtain b₁ : s₁.gpr Impl.Modes.RISCV64.sb = B := by rw [u₁.gpr]; exact hB
  refine coreIn_wp b₁ (by rw [u₁.wr]; exact List.mem_cons_self) halE fun s₂ b₂ sv₂ g₂ f₂ k₂ rd₂ wr₂ => ?_
  obtain hwE : (⟨ecbA B, 8 * slots⟩ : Region) ∈ s₂.wr := by rw [wr₂, u₁.wr]; exact List.mem_cons_self
  obtain ⟨s₃, e₃, v₃, -, g₃, rd₃, wr₃, f₃⟩ := setSlots_ok (keyMasks ++ bsKs) b₂ hwE halE
    (fun kv hkv => by have := masks_lt kv hkv; rw [tableSlot_eq]; omega_using [this]) (by decide)
  obtain b₃ : s₃.gpr sb = ecbA B := by rw [g₃ _ sb_ne_t0 sb_ne_t1, b₂]
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, e₃, ?_⟩
  rw [← List.append_nil park]
  refine park_wp fun s₄ a1₄ a2₄ a4₄ g₄ m₄ rd₄ wr₄ => WP.block_nil_iff.mpr ?_
  obtain sb₄ : s₄.gpr sb = ecbA B := by rw [g₄ _ (by decide) (by decide) (by decide), b₃]
  obtain rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, u₁.rd]; rfl
  obtain wr₄' : s₄.wr = ⟨ecbA B, 8 * slots⟩ :: s.wr := by rw [wr₄, wr₃, wr₂, u₁.wr]; rfl
  obtain gs : ∀ r, r ≠ .a1 → r ≠ .a2 → r ≠ .a4 → r ≠ sb → r ≠ t0 → r ≠ t1 → s₄.gpr r = s.gpr r :=
    fun r h1 h2 h4 hb h0 ht1 => by rw [g₄ r h1 h2 h4, g₃ r h0 ht1, g₂ r hb h0, u₁.gpr]; rfl
  obtain hm₄ : MasksOk s₄ := fun kv hkv => by
    show s₄.mem.readW (wordAddr (s₄.gpr sb) kv.1) 64 = kv.2
    have := v₃ kv hkv
    simp only [slotW, b₃] at this
    rw [sb₄, m₄]; exact this
  obtain hp : SchedPre s₄ (ecbA B) (s.gpr .a0) :=
    ⟨⟨sb₄, by rw [wr₄']; exact List.mem_cons_self, by rw [toNat_off hfit (by decide), slots_eq]; omega_using [hfit], halE⟩,
      by
        rw [rd₄', wr₄']
        rcases List.mem_append.mp hin with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h),
      hkfit, Region.Disjoint.sub_right dK (Offset.sub_base B (by rw [slots_eq]; decide))⟩
  obtain F₄ : Frame [coreRegion (inlineCore d) B] s.mem s₄.mem := by
    obtain h1 : Frame [⟨keyA B, 8⟩] s.mem s₁.mem := by
      rw [u₁.mem]; exact (Frame.refl _ s.mem).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have h2 := f₂
    rw [ecbA_add] at h2
    rw [m₄]
    refine ((h1.sub fun r hr => ?_).trans (h2.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;>
      refine ⟨_, List.mem_singleton_self _, sub_core d B ?_ ?_⟩ <;>
      (try simp only [savedSlot_eq, tableSlot_eq]) <;> decide
  obtain hsch : Spec.Sm4.scheduleAt s₄.mem (s.gpr .a0) = k := by
    rw [Proof.Sm4.scheduleAt_frame F₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.Disjoint.sub_right dK (show Region.Sub ⟨B + BitVec.ofNat 64 (8 * 6), 8 * (404 - 6)⟩
        ⟨B, 8 * 404⟩ from Offset.sub_base B (by decide)), hkk]
  obtain ka₄ : s₄.mem.readW (keyA B) 64 = s.gpr .a0 := by
    rw [m₄, f₃.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact key_apart B (by rw [tableSlot_eq]; decide))
        (by decide),
      f₂.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [ecbA_add]
        exact Offset.disjoint B (.inl (by decide)) (by decide) (by rw [savedSlot_eq]; decide)) (by decide),
      u₁.mem, Mem.readW_writeW_self64]
    rfl
  refine tail_wp (s₀ := s₁) (keys_wp d hp (gs _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) hm₄)
    (fun u hu => ⟨hu.pre.base, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hu.regs _ (by decide) (by decide) (by decide),
      hu.frame, hu.rd, hu.wr⟩)
    (by rw [wr₄']; exact List.mem_cons_self) halE
    (fun i hi => by
      rw [m₄, ← sv₂ i hi]
      refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base (ecbA B) (d := 8 * (savedSlot + i)) (by rw [tableSlot_eq, savedSlot_eq]; omega_using [])
        (by rw [savedSlot_eq]; omega_using [hi]))
    ⟨_, by rw [wr₄']; exact List.mem_append_right _ (List.mem_cons_of_mem _ hW),
      Offset.contains_base B (by decide) (by decide)⟩ halK
    fun u v hu s1 s2 s3 s4 a0 ra pr mv rd wr kv => ?_
  have hb : u.gpr sb = ecbA B := hu.pre.base
  refine ⟨⟨fun kv hkv => ?_, fun e he => ?_, by show v.mem.readW _ _ = v.gpr _; rw [kv, a0]⟩, s4.trans hB.symm |>.trans hB, fun r hr => ?_, ?_, rfl, rfl⟩
  · have := hu.masks kv hkv
    simp only [slotW, hb] at this
    show v.mem.readW _ _ = _
    rw [mv]; exact this
  · have := hu.key.keys e he
    rw [hb, hsch] at this
    show VG.Proof.Sm4.WordRel (entryW v.mem _ e) _
    rw [mv]; exact this
  · show v.gpr r = s.gpr r
    simp only [kept, List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · rw [a0, ka₄]
    · rw [ra, gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    · by_cases h1 : r = .s1
      · subst h1; rw [s1, a1₄, g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide), u₁.gpr]; rfl
      by_cases h2 : r = .s2
      · subst h2; rw [s2, a2₄, g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide), u₁.gpr]; rfl
      by_cases h3 : r = .s3
      · subst h3; rw [s3, a4₄, g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide), u₁.gpr]; rfl
      by_cases h4 : r = .s4
      · subst h4; rw [s4, ← hB]; rfl
      rw [pr r hr h1 h2 h3 h4, u₁.gpr]; rfl
  · show Frame _ s.mem v.mem
    rw [mv]
    refine F₄.trans (hu.frame.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, sub_core d B (by decide) (by rw [tableEnd_eq]; decide)⟩

/-- A block, through memory that differs only apart from it. -/
theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 16⟩ r) : Spec.Sm4.blockAt m' p = Spec.Sm4.blockAt m p := by
  simp only [Spec.Sm4.blockAt]
  congr 1
  funext j
  exact hf.bytes (R := ⟨p, 16⟩) hd (by show 16 ≤ 2 ^ 64; omega_using []) j.isLt

theorem crypt_wp (d : Dir) {s : State} {B : Addr} {ws : List Region} {k : Spec.Sm4.Schedule}
    (hB : s.gpr Impl.Modes.RISCV64.sb = B) (hS : ScrIn s B (inlineCore d).total) (hR : Ready d s B ws k) :
    WP isa (inlineCore d).crypt s fun s' => s'.gpr Impl.Modes.RISCV64.sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Ready d s' B ws k ∧ Frame [coreRegion (inlineCore d) B] s.mem s'.mem ∧
      (∀ j < (inlineCore d).G, bytesAt s'.mem (blkAddr (inlineCore d) B j) (4 * (inlineCore d).bw) =
        dirCipher d k (bytesAt s.mem (blkAddr (inlineCore d) B j) (4 * (inlineCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hmk, hek, hka⟩ := hR
  have hfit : B.toNat + 8 * 404 ≤ 2 ^ 64 := hS.fit
  have hal : B.toNat % 16 = 0 := hS.al
  obtain hW : (⟨B, 8 * 404⟩ : Region) ∈ s.wr := hS.whole (by show 8 * 404 ≤ 4064; decide)
  obtain halE : (ecbA B).toNat % 8 = 0 := by rw [toNat_off hfit (by decide)]; omega_using [hal]
  obtain halK : (keyA B).toNat % 8 = 0 := by rw [toNat_off hfit (by decide)]; omega_using [hal]
  refine WP.narrow (R := ⟨ecbA B, 8 * slots⟩) ⟨_, hW, Offset.contains_base B (by show 56 + 8 * 396 ≤ 8 * 404; decide) (by decide)⟩ ?_
  show WP isa coreCrypt _ _
  rw [coreCrypt]
  simp only [List.append_assoc]
  refine WP.seq ?_
  refine coreIn_wp (s := s.withRegions s.rd (⟨ecbA B, 8 * slots⟩ :: s.wr)) hB List.mem_cons_self halE
    fun s₂ b₂ sv₂ g₂ f₂ k₂ rd₂ wr₂ => ?_
  refine park_wp fun s₃ a1₃ a2₃ a4₃ g₃ m₃ rd₃ wr₃ => ?_
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := slotAddr_ok s₃ .a0 tableEnd
  refine WP.of_runBlock ⟨s₄, e₄, ?_⟩
  obtain sb₄ : s₄.gpr sb = ecbA B := by rw [o₄ _ (by decide), g₃ _ (by decide) (by decide) (by decide), b₂]
  obtain mem₄ : s₄.mem = s₂.mem := by rw [m₄, m₃]
  obtain rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂]; rfl
  obtain wr₄' : s₄.wr = ⟨ecbA B, 8 * slots⟩ :: s.wr := by rw [wr₄, wr₃, wr₂]; rfl
  obtain slot₄ : ∀ j < savedSlot, s₄.mem.readW (wordAddr (ecbA B) j) 64 = s.mem.readW (wordAddr (ecbA B) j) 64 :=
    fun j hj => by rw [mem₄]; exact k₂ j hj
  obtain gs : ∀ r, r ≠ .a1 → r ≠ .a2 → r ≠ .a4 → r ≠ sb → r ≠ t0 → r ≠ .a0 → s₄.gpr r = s.gpr r :=
    fun r h1 h2 h4 hb h0 ha => by rw [o₄ r ha, g₃ r h1 h2 h4, g₂ r hb h0]; rfl
  obtain hkey : KeyCtx s₄ (dirKeys d k) :=
    { scr := by rw [sb₄, wr₄']; exact List.mem_cons_self
      fit := by rw [sb₄, toNat_off hfit (by decide), slots_eq]; omega_using [hfit]
      al := by rw [sb₄]; exact halE
      keys := fun e he => (hek e he).congr fun j hj => by
        rw [sb₄, entryW_eq, entryW_eq, slot₄ _ (by rw [tableSlot_eq, savedSlot_eq]; omega_using [he, hj])] }
  obtain hm₄ : MasksOk s₄ := fun kv hkv => by
    show s₄.mem.readW (wordAddr (s₄.gpr sb) kv.1) 64 = kv.2
    rw [sb₄, slot₄ _ (by have := masks_lt kv hkv; rw [savedSlot_eq]; omega_using [this])]
    exact hmk kv hkv
  obtain ha0 : s₄.gpr .a0 = s₄.gpr sb + BitVec.ofNat 64 (8 * tableEnd) := by rw [r₄, o₄ sb (by decide)]
  obtain ka₄ : s₄.mem.readW (keyA B) 64 = s.gpr .a0 := by
    rw [mem₄, f₂.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [ecbA_add]
        exact Offset.disjoint B (.inl (by decide)) (by decide) (by rw [savedSlot_eq]; decide)) (by decide)]
    exact hka
  refine tail_wp (s₀ := s.withRegions s.rd (⟨ecbA B, 8 * slots⟩ :: s.wr)) (crypt16_wp hkey hm₄ ha0)
    (fun u hu => ⟨by rw [hu.1.base, sb₄], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hu.1.keep _ (by decide) (by decide),
      by
        have cf := hu.1.frame
        rw [sb₄] at cf
        exact cf.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_singleton_self _, Offset.sub B (Nat.le_refl _)
            (by rw [tableSlot_eq, tableEnd_eq]; decide)⟩,
      hu.1.rd, hu.1.wr⟩)
    (by rw [wr₄']; exact List.mem_cons_self) halE (fun i hi => by rw [mem₄]; exact sv₂ i hi)
    ⟨_, by rw [wr₄']; exact List.mem_append_right _ (List.mem_cons_of_mem _ hW),
      Offset.contains_base B (by decide) (by decide)⟩ halK
    fun u v ⟨c, o⟩ s1 s2 s3 s4 a0 ra pr mv rd wr kv => ?_
  obtain hb : u.gpr sb = ecbA B := by rw [c.base, sb₄]
  obtain cf : Frame [⟨ecbA B, 8 * tableSlot⟩] s₄.mem u.mem := by have := c.frame; rw [sb₄] at this; exact this
  refine ⟨s4, fun r hr => ?_, ⟨fun kv hkv => ?_, fun e he => ?_, by show v.mem.readW _ _ = v.gpr _; rw [kv, a0]⟩,
    ?_, fun j hj => ?_, rfl, rfl⟩
  · show v.gpr r = s.gpr r
    simp only [kept, List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · rw [a0, ka₄]
    · rw [ra, gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    · by_cases h1 : r = .s1
      · subst h1; rw [s1, o₄ _ (by decide), a1₃, g₂ _ (by decide) (by decide)]; rfl
      by_cases h2 : r = .s2
      · subst h2; rw [s2, o₄ _ (by decide), a2₃, g₂ _ (by decide) (by decide)]; rfl
      by_cases h3 : r = .s3
      · subst h3; rw [s3, o₄ _ (by decide), a4₃, g₂ _ (by decide) (by decide)]; rfl
      by_cases h4 : r = .s4
      · subst h4; rw [s4, ← hB]; rfl
      rw [pr r hr h1 h2 h3 h4]; rfl
  · have := c.masks kv hkv
    simp only [slotW, hb] at this
    show v.mem.readW _ _ = _
    rw [mv]; exact this
  · show VG.Proof.Sm4.WordRel (entryW v.mem _ e) _
    rw [mv]
    refine (hek e he).congr fun j hj => ?_
    rw [entryW_eq, entryW_eq, ← slot₄ _ (by rw [tableSlot_eq, savedSlot_eq]; omega_using [he, hj])]
    refine cf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [wordAddr]
    exact Offset.disjoint_base (ecbA B) (by rw [tableSlot_eq]; omega_using []) (by rw [tableSlot_eq]; omega_using [he, hj])
  · show Frame _ s.mem v.mem
    rw [mv]
    have h2 := f₂
    rw [ecbA_add] at h2
    rw [← mem₄] at h2
    refine (h2.sub fun r hr => ?_).trans (cf.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;>
      refine ⟨_, List.mem_singleton_self _, sub_core d B ?_ ?_⟩ <;>
      (try simp only [savedSlot_eq, tableSlot_eq]) <;> decide
  · have hj' : j < 16 := hj
    obtain hP : blkAddr (inlineCore d) B j = s₄.gpr sb + BitVec.ofNat 64 (8 * tailSlot + 16 * j) := by
      rw [sb₄]
      show B + BitVec.ofNat 64 (8 * 103) + BitVec.ofNat 64 (4 * 4 * j) = B + BitVec.ofNat 64 56 + _
      rw [Offset.add_add, Offset.add_add, tailSlot_eq, show 8 * 103 + 4 * 4 * j = 56 + (8 * 96 + 16 * j) by omega_using []]
    show bytesAt v.mem _ 16 = dirCipher d k (bytesAt s.mem _ 16)
    have := o j hj'
    simp only [tailBlock, hb, sb₄] at this
    rw [hP, dirCipher_bytes, Proof.Sm4.bytesAt_eq_blockAt, mv, sb₄, this, quads_spec, mem₄]
    rw [blockAt_frame f₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [ecbA_add, ecbA_add]
      exact Offset.disjoint B (.inl (by rw [tailSlot_eq, savedSlot_eq]; omega_using [hj'])) (by rw [tailSlot_eq]; omega_using [hj'])
        (by rw [savedSlot_eq]; decide)]
    rfl

/-- SM4's core for the direction `d` meets what the modes need. -/
def inlineCoreSpec (d : Dir) : CoreSpec (inlineCore d) where
  Key := Spec.Sm4.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready := Ready d
  cipher_len k b := by cases d <;> simp [dirCipher, Spec.Sm4.cipher, Spec.Sm4.invCipher, inlineCore]
  layout := inlineLayout d
  keyArgs_congr h e r w _ f := keyArgs_congr h e.a0 r w f
  ready_frame h e _ _ _ f _ hc := ready_frame d h e.a0 f hc
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

open VG.Proof.Modes.RISCV64 (KeyMove ReadyMove)

theorem shared_key (d : Dir) : KeyMove (inlineCoreSpec d) := by
  intro s t rs ts k hk ha rd wr hf hs
  obtain ⟨hk, hin, fit, hd⟩ := keyArgs_congr hk ha rd wr hf
  exact ⟨hk, hin, fit, fun r hr => by
    obtain ⟨r', hr', sub⟩ := hs r hr
    exact (hd r' hr').sub_right sub⟩

theorem shared_ready (d : Dir) : ReadyMove (inlineCoreSpec d) := by
  intro s t B ws k rs hr ha rd wr hf hs hd
  exact ready_frame (ws := ws) d hr ha hf hd

def dirCoreSpec (d : Dir) : CoreSpec (dirCore d) :=
  (inlineCoreSpec d).shared (by dsimp only [inlineCore]; decide) (by dsimp only [inlineCore]; decide) (shared_key d) (shared_ready d) (by cases d <;> rfl) rfl _ _

theorem layout (d : Dir) : Layout (dirCore d) :=
  VG.Proof.Modes.RISCV64.shared_layout (inlineLayout d) (by dsimp only [inlineCore]; decide) _ _

end VG.Proof.Sm4.RISCV64.Mode

end

end

/-!
# SM4's modes on RISC-V meet their contracts

`cbcEncryptChained_verified`, `ctr_verified`, … : the modes of
`Proof/Modes/RISCV64/` over SM4's core (`Mode.dirCoreSpec`) meet the
shared contracts, with `stack := 3248`: the mode's frame of 406 slots below
the stack pointer, which holds ECB's scratch buffer and which it zeroes
before returning. The proofs are written against `modeContract`, which
states the frame.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64.Modes

open VG VG.RISCV64 VG.Impl.Sm4.RISCV64 VG.Impl.Modes
open VG.Proof.Modes.RISCV64 (SeqPre ivR scrRegion Fb)
open VG.Proof.Sm4.RISCV64.Mode (dirCoreSpec KeyArgs layout dirCipher)
open VG.Proof.Sm4.RISCV64 (modePub)

/-- The frame's bytes. -/
abbrev frameBytes : Nat := 3248

/-- SM4 under the schedule at `a0`, and its inverse. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher := Spec.Sm4.cipher (Spec.Sm4.scheduleAt s.mem (s.gpr .a0))
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.Sm4.invCipher (Spec.Sm4.scheduleAt s.mem (s.gpr .a0))
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m (s.gpr .a1) 16
/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) := Spec.Cbc.blocksAt m (s.gpr .a2) (s.gpr .a3).toNat

/-- The functions' postconditions. -/
def cbcEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cbcDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (invCiph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def ofbPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ofb.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ofb.next (ciph s) (ivAt s.mem s) (s.gpr .a3).toNat
def cfbEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def ctrPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ctr.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ctr.next (ivAt s.mem s) (s.gpr .a3).toNat

/-- A mode's function on RISC-V, with its frame below the stack pointer,
and the postcondition `post`. -/
def modeContract (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 128⟩
    let iv : Region := ⟨s.gpr .a1, 16⟩
    let data : Region := ⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩
    let stack : Region := ⟨s.sp - frameBytes, frameBytes⟩
    s.rd = [key] ∧ s.wr = [iv, data] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ iv.Disjoint data ∧
      (s.gpr .a0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 16 * (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ frameBytes ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint iv ∧
      stack.Disjoint data
  post := post
  pub := modePub

/-- `modeContract`'s precondition gives the modes'. -/
theorem seqPre_of {post : State → State → Prop} {M : Mode} (d : Dir) (hstep : M.step = 16)
    {s : State} (h : (modeContract post).pre s) : SeqPre (dirCore d) M s := by
  obtain ⟨-, hwr, -, -, dVD, -, fV, fD, al, sp, -, dSV, dSD⟩ := h
  have e16 : 4 * (dirCore d).bw = 16 := rfl
  have eS : scrRegion (dirCore d) (Fb s (dirCore d)) = ⟨s.sp - frameBytes, frameBytes⟩ := rfl
  have eV : ivR s (dirCore d) = ⟨s.gpr .a1, 16⟩ := rfl
  refine ⟨al, sp, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp, by rw [e16]; exact fV,
    by rw [hwr, hstep]; simp, by rw [hstep]; exact fD, by rw [hstep, eS]; exact dSD.symm,
    by rw [eV, eS]; exact dSV.symm, fun _ => by rw [eV, hstep]; exact dVD, ⟨by omega_using [hstep], by rw [e16]; omega_using [hstep]⟩,
    Mode.layout d⟩

theorem keyArgs_of {post : State → State → Prop} {M : Mode} (d : Dir) (hstep : M.step = 16)
    {s : State} (h : (modeContract post).pre s) :
    KeyArgs s (Proof.Modes.RISCV64.wrs0 (dirCore d) M s) (Spec.Sm4.scheduleAt s.mem (s.gpr .a0)) := by
  obtain ⟨hrd, -, -, dKD, -, fK, -, -, -, -, dSK, -, -⟩ := h
  refine ⟨rfl, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), fK, fun r hr => ?_⟩
  simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .a0) 128).Disjoint ⟨s.gpr .a2, M.step * (s.gpr .a3).toNat⟩
    rw [hstep]; exact dKD
  · exact dSK.symm

/-! ## Correctness -/

theorem cipher_enc (k : Spec.Sm4.Schedule) : (dirCoreSpec .encrypt).cipher k = Spec.Sm4.cipher k := by kernel_rfl
theorem cipher_dec (k : Spec.Sm4.Schedule) : (dirCoreSpec .decrypt).cipher k = Spec.Sm4.invCipher k := by kernel_rfl

theorem cbcEncryptChained_correct (s : State) (hs : (modeContract cbcEncPost).pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract cbcEncPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cbcEncChained_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cbcEncChained 4) rfl hs)
    (keyArgs_of .encrypt (M := Mode.cbcEncChained 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

theorem cbcDecryptChained_correct (s : State) (hs : (modeContract cbcDecPost).pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract cbcDecPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cbcDecLevels_wp (dirCoreSpec .decrypt) (by decide)
    (seqPre_of .decrypt (M := Mode.cbcDecChained 4) rfl hs)
    (keyArgs_of .decrypt (M := Mode.cbcDecChained 4) rfl hs))
    fun _ ⟨h1, h2, h3, _⟩ => by simp only [cipher_dec] at h2 h3; exact ⟨h1, h2, h3⟩

theorem ofb_correct (s : State) (hs : (modeContract ofbPost).pre s) :
    ∃ t s', Exec isa ofb s t s' ∧ abiPreserved s s' ∧ (modeContract ofbPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.ofb_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.ofb 4) rfl hs)
    (keyArgs_of .encrypt (M := Mode.ofb 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

theorem cfbEncrypt_correct (s : State) (hs : (modeContract cfbEncPost).pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ (modeContract cfbEncPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbEnc_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cfbEnc 4) rfl hs)
    (keyArgs_of .encrypt (M := Mode.cfbEnc 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

theorem cfbDecrypt_correct (s : State) (hs : (modeContract cfbDecPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ (modeContract cfbDecPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbDecLevels_wp (dirCoreSpec .encrypt) (by decide)
    (seqPre_of .encrypt (M := Mode.cfbDecEarly 4) rfl hs)
    (keyArgs_of .encrypt (M := Mode.cfbDecEarly 4) rfl hs))
    fun _ ⟨h1, h2, h3, _⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

theorem ctr_correct (s : State) (hs : (modeContract ctrPost).pre s) :
    ∃ t s', Exec isa ctr s t s' ∧ abiPreserved s s' ∧ (modeContract ctrPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.ctrLevels_wp (dirCoreSpec .encrypt) rfl (by decide)
    (seqPre_of .encrypt (M := Mode.ctrEarly) rfl hs)
    (keyArgs_of .encrypt (M := Mode.ctrEarly) rfl hs))
    fun _ ⟨h1, h2, h3, _⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

/-! ## The contracts -/

/-- A state satisfying the modes' precondition: the schedule at `0x1000`,
the IV at `0x3000`, no data at `0x4000`, and the stack below `0x8000`. -/
def modeSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a2 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 0⟩]

theorem modePub_iff (s₁ s₂ : State) : modePub s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 := by
  simp [modePub]

theorem cbcEncryptChained_verified :
    Verified RISCV64.target cbcEncryptChained (Spec.Sm4.cbcEncryptChainedContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cbcEncryptChained_correct (cbcEncryptChained_constantTime _) ?_
  contract_implies [Spec.Sm4.cbcEncryptChainedContract, Spec.Sm4.cbcChainedSig,
    RISCV64.abi, RISCV64.argRegs, modeContract, cbcEncPost, modePub_iff] [modeSat] using modeSat

theorem cbcDecryptChained_verified :
    Verified RISCV64.target cbcDecryptChained (Spec.Sm4.cbcDecryptChainedContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cbcDecryptChained_correct (cbcDecryptChained_constantTime _) ?_
  contract_implies [Spec.Sm4.cbcDecryptChainedContract, Spec.Sm4.cbcChainedSig,
    RISCV64.abi, RISCV64.argRegs, modeContract, cbcDecPost, modePub_iff] [modeSat] using modeSat

theorem ofb_verified : Verified RISCV64.target ofb (Spec.Sm4.ofbContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct ofb_correct (ofb_constantTime _) ?_
  contract_implies [Spec.Sm4.ofbContract, Spec.Sm4.ofbSig, RISCV64.abi, RISCV64.argRegs,
    modeContract, ofbPost, modePub_iff] [modeSat] using modeSat

theorem cfbEncrypt_verified :
    Verified RISCV64.target cfbEncrypt (Spec.Sm4.cfbEncryptContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cfbEncrypt_correct (cfbEncrypt_constantTime _) ?_
  contract_implies [Spec.Sm4.cfbEncryptContract, Spec.Sm4.cfbSig, RISCV64.abi,
    RISCV64.argRegs, modeContract, cfbEncPost, modePub_iff] [modeSat] using modeSat

theorem cfbDecrypt_verified :
    Verified RISCV64.target cfbDecrypt (Spec.Sm4.cfbDecryptContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cfbDecrypt_correct (cfbDecrypt_constantTime _) ?_
  contract_implies [Spec.Sm4.cfbDecryptContract, Spec.Sm4.cfbSig, RISCV64.abi,
    RISCV64.argRegs, modeContract, cfbDecPost, modePub_iff] [modeSat] using modeSat

theorem ctr_verified : Verified RISCV64.target ctr (Spec.Sm4.ctrContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct ctr_correct (ctr_constantTime _) ?_
  contract_implies [Spec.Sm4.ctrContract, Spec.Sm4.ctrSig, RISCV64.abi, RISCV64.argRegs,
    modeContract, ctrPost, modePub_iff] [modeSat] using modeSat

end VG.Proof.Sm4.RISCV64.Modes
