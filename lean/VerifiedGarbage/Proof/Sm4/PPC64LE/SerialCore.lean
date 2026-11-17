module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.SerialSbox
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PPC64LE.VectorBytes
public import VerifiedGarbage.Proof.Sm4.Rounds
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Aes.Vector
import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.Proof.Modes.PPC64LE.Core
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Sm4.PPC64LE.Core
import VerifiedGarbage.Proof.Aes.Bitsliced
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Modes
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Ecb
import VerifiedGarbage.Proof.Sm4.PPC64LE.PreparedVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.PreparedBody
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Sm4.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.Proof.Sm4.Prepared

/-! ### `Sm4.PPC64LE.ModeCore`, which this module and modules that import it used -/

section

/-!
# SM4's core for the modes on PPC64LE

`dirCoreSpec d`: SM4's core for the direction `d`
(`Impl.Sm4.PPC64LE.dirCore d`) meets what the modes need of a core
(`Proof.Modes.PPC64LE.CoreSpec`), with the key a schedule, its cipher
`Spec.Sm4.cipher` for encryption and `Spec.Sm4.invCipher` for decryption,
and the key ready when the working space's table encodes the round keys in
`d`'s order (`Proof.Sm4.Prepared.Holds`).

`prepare` and `crypt` call `vg_sm4_prepare_keys` and
`vg_sm4_crypt_prepared` (`WP.call`, with their contracts on PPC64LE,
`prepPPC64LE` and `cryptPPC64LE`) on the functions' 402 slots, the core's.
Neither function writes `sb` (`r5`) or `r7`, which keeps `r3` across each
call (`prep_keeps`, `crypt_keeps`).
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4.PPC64LE
open VG.Impl.Modes.PPC64LE (sb)
open VG.Proof.Modes.PPC64LE (ScrIn coreRegion blkRegion blkAddr slotA Layout CoreSpec kept)
open VG.Proof.Sm4 (specDirPPC64LE)
open VG.Spec.Aes (bytesAt)

/-- The schedule at `r3`, outside the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Sm4.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .r3 = p ∧ k = Spec.Sm4.scheduleAt s.mem p ∧ (⟨p, 128⟩ : Region) ∈ s.rd ∧
    p.toNat + 128 ≤ 2 ^ 64 ∧ ∀ r ∈ rs, Region.Disjoint ⟨p, 128⟩ r

/-- The cipher of the direction `d`. -/
def dirCipher : Dir → Spec.Sm4.Schedule → Spec.Cbc.Cipher
  | .encrypt => Spec.Sm4.cipher
  | .decrypt => Spec.Sm4.invCipher

theorem dirCipher_bytes (d : Dir) (k : Spec.Sm4.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (bytesAt m p 16) = (Proof.Sm4.blockFn k (specDirPPC64LE d) (Spec.Sm4.blockAt m p)).toList := by
  cases d
  · rw [dirCipher, Spec.Sm4.cipher, Proof.Sm4.bytesAt_eq_blockAt, Proof.Sm4.ofFn_toList]; rfl
  · rw [dirCipher, Spec.Sm4.invCipher, Proof.Sm4.bytesAt_eq_blockAt, Proof.Sm4.ofFn_toList]; rfl

theorem core_slots (d : Dir) : (dirCore d).slots = slots := rfl
theorem core_total (d : Dir) : (dirCore d).total = slots + 6 := rfl

/-- A byte outside the regions of a frame keeps its value. -/
theorem byte_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, 1⟩ r) : m' a = m a :=
  hf a fun r hr hc => hd r hr a (Region.contains_self _ _) hc

/-- The table's offsets: in the functions' slots, outside the tail buffer. -/
theorem table_off {r : Nat × Nat} (hr : r ∈ layout.table) {i : Nat} (hi : i < r.2) :
    r.1 + i + 1 ≤ 8 * slots ∧ (r.1 + i + 1 ≤ 8 * tailSlot ∨ 8 * tailSlot + 256 ≤ r.1 + i) := by
  rw [layout_table] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [slots_eq, tailSlot_eq]
  rcases hr with rfl | rfl <;> dsimp only at hi ⊢ <;> omega_using [hi]

/-- The table survives what a mode writes: outside the core's slots or within its buffer. -/
theorem holds_frame {d : Dir} {m m' : Mem} {B : Addr} {k : Spec.Sm4.Schedule} {sd : Spec.Sm4.Direction}
    {rs : List Region} (h : Proof.Sm4.Prepared.Holds layout m B k sd) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (blkRegion (dirCore d) B)) :
    Proof.Sm4.Prepared.Holds layout m' B k sd := fun r hr i hi => by
  obtain ⟨h1, h2⟩ := table_off hr hi
  rw [byte_frame hf fun q hq => ?_]
  · exact h r hr i hi
  rcases hd q hq with hq' | hq'
  · exact hq'.sub_left (VG.Offset.sub_base B (by rw [core_slots]; exact h1))
  · refine Region.Disjoint.sub_right ?_ hq'
    show Region.Disjoint ⟨B + BitVec.ofNat 64 (r.1 + i), 1⟩ ⟨B + BitVec.ofNat 64 (8 * tailSlot), 4 * 4 * 16⟩
    exact VG.Offset.disjoint B (by rw [tailSlot_eq] at h2 ⊢; omega_using [h2]) (by rw [slots_eq] at h1; omega_using [h1])
      (by rw [tailSlot_eq]; omega_using [])

/-- The table survives what a batch keeps. -/
theorem holds_of_keeps {m m' : Mem} {B : Addr} {k : Spec.Sm4.Schedule} {sd : Spec.Sm4.Direction}
    (h : Proof.Sm4.Prepared.Holds layout m B k sd)
    (hk : Proof.Sm4.Prepared.Keeps B slots layout.cryptScratch m m') :
    Proof.Sm4.Prepared.Holds layout m' B k sd := fun r hr i hi => by
  have hr' := hr
  rw [layout_table] at hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rw [hk (r.1 + i) (by rw [slots_eq]; rcases hr' with rfl | rfl <;> dsimp only at hi ⊢ <;> omega_using [hi]) (by
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [evenSlot_eq, grpSlot_eq, tableSlot_eq, savedSlot_eq, slots_eq]
    rcases hr' with rfl | rfl <;> dsimp only at hi ⊢ <;> omega_using [hi])]
  exact h r hr i hi

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Sm4.Schedule} (h : KeyArgs s rs k)
    (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [e, hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hk]
  exact (Proof.Sm4.scheduleAt_congr fun i hi =>
    hf.bytes (R := ⟨p, 128⟩) hdis (by show 128 ≤ 2 ^ 64; omega_using []) hi).symm

/-! ## Around the calls -/

/-- The functions' slots, the core's, as the calls' working space. -/
theorem ws_covers {s : State} {B : Addr} {d : Dir} (hs : ScrIn s B (dirCore d).total) :
    Covers [⟨B, 8 * slots⟩] s.wr := Covers.of_sub fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, hs.wr, 0, by rw [BitVec.add_zero], by
    show 0 + 8 * slots ≤ 8 * (slots + 6)
    omega_using []⟩

/-- `vg_sm4_prepare_keys` writes neither `r5` nor `r7`. -/
theorem prep_keeps : ∀ i ∈ instrs prepareKeys, dstOf i ≠ some .r5 ∧ dstOf i ≠ some .r7 := by
  have h : (instrs prepareKeys).all (fun i => dstOf i != some .r5 && dstOf i != some .r7) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  have := List.all_eq_true.mp h i hi
  simpa using this

/-- `vg_sm4_crypt_prepared` writes neither `r5` nor `r7`. -/
theorem crypt_keeps : ∀ i ∈ instrs cryptPrepared, dstOf i ≠ some .r5 ∧ dstOf i ≠ some .r7 := by
  have h : (instrs cryptPrepared).all (fun i => dstOf i != some .r5 && dstOf i != some .r7) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  have := List.all_eq_true.mp h i hi
  simpa using this

theorem slots_lt : slots < 2 ^ 15 := by rw [slots_eq]; decide

theorem toNat_slots : (BitVec.ofNat 64 slots).toNat = slots := by rw [BitVec.toNat_ofNat, slots_eq]

theorem directionOf_dirBit (d : Dir) : Proof.Sm4.directionOf (BitVec.ofNat 64 (dirBit d)).toNat = specDirPPC64LE d := by
  cases d <;> rfl

/-- What the modes keep, kept through a head that writes `r4`, `r6` and `r7`
(and `r3`, restored), a call that preserves the callee-saved registers, and
`r3` restored. -/
theorem kept_of {s s₁ s₂ s₃ : State} (h₁ : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → s₁.gpr r = s.gpr r)
    (hp : ∀ r ∈ preserved, s₂.gpr r = s₁.gpr r) (h3 : s₃.gpr .r3 = s.gpr .r3)
    (ho : ∀ r, r ≠ .r3 → s₃.gpr r = s₂.gpr r) :
    ∀ r ∈ kept, s₃.gpr r = s.gpr r := by
  intro r hr
  by_cases e3 : r = .r3
  · subst e3; exact h3
  have hp' : r ∈ preserved := by
    simp only [kept, List.mem_cons] at hr
    rcases hr with rfl | h
    · exact absurd rfl e3
    · exact h
  have hne : ∀ r ∈ preserved, r ≠ .r4 ∧ r ≠ .r6 ∧ r ≠ .r7 := by decide
  rw [ho r e3, hp r hp', h₁ r e3 (hne r hp').1 (hne r hp').2.1 (hne r hp').2.2]

theorem prepare_wp (d : Dir) {s : State} {B : Addr} {rs : List Region} {k : Spec.Sm4.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hR : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => Proof.Sm4.Prepared.Holds layout s'.mem B k (specDirPPC64LE d) ∧
      s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, rfl, hin, hfit, hdis⟩ := hk
  have hfB : B.toNat + 8 * (dirCore d).total ≤ 2 ^ 64 := hs.fit
  have hsep : Region.Disjoint ⟨p, 128⟩ ⟨B, 8 * slots⟩ :=
    (hdis _ hR).sub_right (Region.sub_prefix (by have := core_total d; omega_using [this]))
  show WP isa (prepareCall d) s _
  refine WP.seq (wp_mr fun s₁ u₁ => wp_li (by cases d <;> decide) fun s₂ u₂ =>
    wp_li slots_lt fun s₃ u₃ => wp_nil ?_)
  have g₃ : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → s₃.gpr r = s.gpr r := fun r _ h4 h6 h7 => by
    rw [u₃.other r h6, u₂.other r h4, u₁.other r h7]
  have r3₃ : s₃.gpr .r3 = p := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hp]
  have r4₃ : s₃.gpr .r4 = BitVec.ofNat 64 (dirBit d) := by rw [u₃.other _ (by decide), u₂.gpr]
  have r5₃ : s₃.gpr .r5 = B := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact hB
  have r6₃ : s₃.gpr .r6 = BitVec.ofNat 64 slots := u₃.gpr
  have r7₃ : s₃.gpr .r7 = p := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hp]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have c3 : (s₃.callEntry.withRegions [⟨p, 128⟩] [⟨B, 8 * slots⟩]).gpr .r3 = p := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r3₃]
  have c4 : (s₃.callEntry.withRegions [⟨p, 128⟩] [⟨B, 8 * slots⟩]).gpr .r4 = BitVec.ofNat 64 (dirBit d) := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r4₃]
  have c5 : (s₃.callEntry.withRegions [⟨p, 128⟩] [⟨B, 8 * slots⟩]).gpr .r5 = B := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r5₃]
  have c6 : ((s₃.callEntry.withRegions [⟨p, 128⟩] [⟨B, 8 * slots⟩]).gpr .r6).toNat = slots := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r6₃, toNat_slots]
  have hm₀ : (s₃.callEntry.withRegions [⟨p, 128⟩] [⟨B, 8 * slots⟩]).mem = s.mem := by
    rw [State.withRegions_mem, State.callEntry_mem, m₃]
  have cov : Covers [⟨B, 8 * slots⟩] s₃.wr := by rw [wr₃]; exact ws_covers hs
  refine WP.seq (WP.call (k := prepPPC64LE) prep_correct (rd := [⟨p, 128⟩]) (wr := [⟨B, 8 * slots⟩]) ?_
    (Covers.append_left (Covers.left (Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [rd₃]; exact hin)) (Covers.right cov))
    cov (fun s' hrd hwr _ hf hpres hnw hpost => ?_) (by lit_decide))
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [State.withRegions_rd, c3]
    · rw [State.withRegions_wr, c5, c6, Nat.mul_comm]
    · rw [c3, c5, c6, Nat.mul_comm]; exact hsep
    · rw [c3]; exact hfit
    · rw [c5, c6]; have := core_total d; omega_using [hfB, this]
    · rw [c4]; cases d <;> decide
    · rw [c6, size_eq]
  · obtain ⟨hH, -⟩ := hpost
    have hm : (s'.withRegions [⟨p, 128⟩] [⟨B, 8 * slots⟩]).mem = s'.mem := rfl
    change Proof.Sm4.Prepared.Holds layout _ _ _ _ at hH
    rw [hm, hm₀, c3, c4, c5, directionOf_dirBit] at hH
    have r5' : s'.gpr .r5 = B := by
      rw [hnw .r5 (by decide) fun i hi => (prep_keeps i hi).1, r5₃]
    have r7' : s'.gpr .r7 = p := by
      rw [hnw .r7 (by decide) fun i hi => (prep_keeps i hi).2, r7₃]
    refine wp_mr fun s₄ u₄ => wp_nil ⟨by rw [u₄.mem]; exact hH, by rw [u₄.other _ (by decide)]; exact r5',
      kept_of g₃ hpres (by rw [u₄.gpr, r7', hp]) fun r h => u₄.other r h,
      by rw [u₄.mem, ← m₃]; exact hf, by rw [u₄.rd, hrd, rd₃], by rw [u₄.wr, hwr, wr₃]⟩

/-- Block `j` of blocks transformed by ECB. -/
theorem blockAt_of_ecb {K : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction} {m m' : Mem} {D : Addr} {n : Nat}
    (h : Spec.Sm4.blocksAt m' D n = Spec.Sm4.ecb K d (Spec.Sm4.blocksAt m D n)) {j : Nat} (hj : j < n) :
    Spec.Sm4.blockAt m' (D + BitVec.ofNat 64 (16 * j)) =
      Proof.Sm4.blockFn K d (Spec.Sm4.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  have := congrArg (fun l => l[j]?) h
  rw [Proof.Sm4.ecb_eq] at this
  simpa [Spec.Sm4.blocksAt, hj] using this

theorem crypt_wp (d : Dir) {s : State} {B : Addr} {k : Spec.Sm4.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hr : Proof.Sm4.Prepared.Holds layout s.mem B k (specDirPPC64LE d)) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Proof.Sm4.Prepared.Holds layout s'.mem B k (specDirPPC64LE d) ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, bytesAt s'.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw) =
        dirCipher d k (bytesAt s.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfB : B.toNat + 8 * (dirCore d).total ≤ 2 ^ 64 := hs.fit
  show WP isa cryptCall s _
  refine WP.seq (wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_li slots_lt fun s₃ u₃ => wp_nil ?_)
  have g₃ : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → s₃.gpr r = s.gpr r := fun r h3 h4 _ h7 => by
    rw [u₃.other r h4, u₂.other r h3, u₁.other r h7]
  have r3₃ : s₃.gpr .r3 = B := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]; exact hB
  have r4₃ : s₃.gpr .r4 = BitVec.ofNat 64 slots := u₃.gpr
  have r5₃ : s₃.gpr .r5 = B := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact hB
  have r7₃ : s₃.gpr .r7 = s.gpr .r3 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have c3 : (s₃.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .r3 = B := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r3₃]
  have c4 : ((s₃.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .r4).toNat = slots := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r4₃, toNat_slots]
  have hm₀ : (s₃.callEntry.withRegions [] [⟨B, 8 * slots⟩]).mem = s.mem := by
    rw [State.withRegions_mem, State.callEntry_mem, m₃]
  have cov : Covers [⟨B, 8 * slots⟩] s₃.wr := by rw [wr₃]; exact ws_covers hs
  refine WP.seq (WP.call (k := cryptPPC64LE) crypt_correct (rd := []) (wr := [⟨B, 8 * slots⟩]) ?_
    (Covers.append_left Covers.nil (Covers.right cov)) cov (fun s' hrd hwr _ hf hpres hnw hpost => ?_)
    (by lit_decide))
  · refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · rw [State.withRegions_wr, c3, c4, Nat.mul_comm]
    · rw [c3, c4]; have := core_total d; omega_using [hfB, this]
    · rw [c4, size_eq]
    · rw [c3, hm₀]; exact ⟨k, specDirPPC64LE d, hr⟩
  · obtain ⟨hE, hK⟩ := hpost
    have hm : (s'.withRegions [] [⟨B, 8 * slots⟩]).mem = s'.mem := rfl
    rw [hm, hm₀, c3] at hE
    rw [hm, hm₀, c3, c4] at hK
    have hE' := hE k (specDirPPC64LE d) hr
    have r5' : s'.gpr .r5 = B := by
      rw [hnw .r5 (by decide) fun i hi => (crypt_keeps i hi).1, r5₃]
    have r7' : s'.gpr .r7 = s.gpr .r3 := by
      rw [hnw .r7 (by decide) fun i hi => (crypt_keeps i hi).2, r7₃]
    refine wp_mr fun s₄ u₄ => wp_nil ⟨by rw [u₄.other _ (by decide)]; exact r5',
      kept_of g₃ hpres (by rw [u₄.gpr, r7']) fun r h => u₄.other r h,
      by rw [u₄.mem]; exact holds_of_keeps hr hK, by rw [u₄.mem, ← m₃]; exact hf, fun j hj => ?_,
      by rw [u₄.rd, hrd, rd₃], by rw [u₄.wr, hwr, wr₃]⟩
    have hj16 : j < 16 := hj
    have ha : blkAddr (dirCore d) B j = B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j) := rfl
    show bytesAt s₄.mem (blkAddr (dirCore d) B j) 16 = dirCipher d k (bytesAt s.mem (blkAddr (dirCore d) B j) 16)
    rw [dirCipher_bytes, Proof.Sm4.bytesAt_eq_blockAt, u₄.mem, ha, blockAt_of_ecb hE' hj16]

/-- SM4's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Dir) : CoreSpec (dirCore d) where
  Key := Spec.Sm4.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready s B _ k := Proof.Sm4.Prepared.Holds layout s.mem B k (specDirPPC64LE d)
  cipher_len _ _ := by
    show _ = 16
    cases d <;> simp [dirCipher, Spec.Sm4.cipher, Spec.Sm4.invCipher]
  layout := ⟨by cases d <;> decide, .inr rfl, by cases d <;> decide, by cases d <;> decide,
    by cases d <;> decide⟩
  keyArgs_congr h e hrd hwr _ hf := keyArgs_congr h e.r3 hrd hwr hf
  ready_frame h _ _ _ _ hf _ hd := holds_frame h hf hd
  prepare_wp hB hs hR hk := prepare_wp d hB hs hR hk
  crypt_wp hB hs hR := crypt_wp d hB hs hR

end VG.Proof.Sm4.PPC64LE

end

end

/-!
# The single-block SM4 core on PPC64LE

`coreSpec`: the single-block core (`Impl.Sm4.PPC64LE.Serial.core`) meets
what the modes need of a core (`Proof.Modes.PPC64LE.CoreSpec`), with the
key the schedule at `r3`, read in place (`KeyArgs`, apart from the core's
slots and the mode's regions), and its cipher `Spec.Sm4.cipher`.

* `affine_run`: the nibble-table lookups of an affine map (`Serial.affine`)
  put, in bytes `4 … 7` of `v0`, the map (`aff`) of the bytes of `r9`'s low
  word. `tau_run`: SM4's S-box layer (`Serial.tau`), from `sbox_affine`.
* `linear_run`, `round_run` and `rounds_run`: the linear map, a round, and
  the 32.
* `crypt_wp`: the tables to `v12`–`v15` (`loadTables_run`), the block's
  big-endian words (`loads_run`), the 32 rounds, and the words back in
  reverse order (`stores_run`) encipher the block of the buffer.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE.Serial

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.PPC64LE.Bytes
open VG.Impl.Sm4.PPC64LE.Serial
open VG.Impl.Sm4.PPC64LE (Dir)

/-! ## Bytes -/

/-- The mask `0x0f0f0f0f` has `0x0f` in each byte of its low word. -/
theorem gbyte_mask {k : Nat} (hk : k < 4) : gbyte 0x0f0f0f0f k = 0x0f := by
  rcases k with _ | _ | _ | _ | k
  all_goals first | decide | omega

/-- The high nibble of each byte of the low word, by the word's shift right
by 4, masked. -/
theorem gbyte_lsr4 (x : BitVec 64) {k : Nat} (hk : k < 4) :
    gbyte ((x.setWidth 32 >>> 4).setWidth 64 &&& 0x0f0f0f0f) k = gbyte x k >>> 4 := by
  rw [gbyte_and, gbyte_mask hk]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  rcases k with _ | _ | _ | _ | k <;> rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    first | omega | simp

/-! ## The affine maps -/

/-- What the core keeps in registers: the four tables in `v12`–`v15` and the
mask in `r12`. -/
structure Consts (s : State) : Prop where
  inLo : TabOk (s.vpr (treg 0)) inLo
  inHi : TabOk (s.vpr (treg 1)) inHi
  outLo : TabOk (s.vpr (treg 2)) outLo
  outHi : TabOk (s.vpr (treg 3)) outHi
  mask : s.gpr .r12 = 0x0f0f0f0f

theorem Consts.of_eq {s t : State} (h : Consts s) (hv : ∀ v, v ≠ .v0 → v ≠ .v1 → t.vpr v = s.vpr v)
    (hg : t.gpr .r12 = s.gpr .r12) : Consts t := by
  obtain e : ∀ k < 4, t.vpr (treg k) = s.vpr (treg k) := fun k hk => by
    rcases k with _ | _ | _ | _ | k
    all_goals first | omega | exact hv _ (by decide) (by decide)
  exact ⟨by rw [e 0 (by decide)]; exact h.inLo, by rw [e 1 (by decide)]; exact h.inHi,
    by rw [e 2 (by decide)]; exact h.outLo, by rw [e 3 (by decide)]; exact h.outHi, by rw [hg]; exact h.mask⟩

/-- The registers `affine` writes are not the tables. -/
theorem treg_ne (k : Nat) : treg k ≠ .v0 ∧ treg k ≠ .v1 := by
  rcases k with _ | _ | _ | _ | k <;> simp [treg]

theorem affine_run (s : State) {lo hi : VReg} {tl th : Vector Byte 16} (hlo : TabOk (s.vpr lo) tl)
    (hhi : TabOk (s.vpr hi) th) (hl : lo ≠ .v0 ∧ lo ≠ .v1) (hh : hi ≠ .v0 ∧ hi ≠ .v1)
    (hm : s.gpr .r12 = 0x0f0f0f0f) :
    ∃ t, runBlock isa (affine lo hi) s = some t ∧
      (∀ k < 4, vbyte (t.vpr .v0) (7 - k) = aff tl th (gbyte (s.gpr .r9) k)) ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r) ∧
      (∀ v, v ≠ .v0 → v ≠ .v1 → t.vpr v = s.vpr v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  let a := s.write .r10 (s.gpr .r9 &&& s.gpr .r12)
  let b := a.write .r11 (((a.gpr .r9).setWidth 32 >>> 4).setWidth 64)
  let c := b.write .r11 (b.gpr .r11 &&& b.gpr .r12)
  let d : State := { c.writeV .v0 (c.gpr .r10 ++ c.undef (c.unknowns 0) (c.gpr .r10) (c.vpr .v0)) with unknowns := fun i => c.unknowns (i + 1) }
  let e : State := { d.writeV .v1 (d.gpr .r11 ++ d.undef (d.unknowns 0) (d.gpr .r11) (d.vpr .v1)) with unknowns := fun i => d.unknowns (i + 1) }
  let f := e.writeV .v0 (ofVBytes fun i =>
      let j := (vbyte (e.vpr .v0) i).toNat % 32
      if j < 16 then vbyte (e.vpr lo) j else vbyte (e.vpr lo) (j - 16))
  let g := f.writeV .v1 (ofVBytes fun i =>
      let j := (vbyte (f.vpr .v1) i).toNat % 32
      if j < 16 then vbyte (f.vpr hi) j else vbyte (f.vpr hi) (j - 16))
  let h := g.writeV .v0 (g.vpr .v0 ^^^ g.vpr .v1)
  refine ⟨h, ?_, fun k hk => ?_, fun r h10 h11 => ?_, fun v h0 h1 => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [affine, runBlock_cons, exec_logic, exec_lsr_w (by decide : 4 < 32), exec_mtvsrd, exec_vperm,
      exec_vxor, runStep_some, runBlock_nil]
    rfl
  · have g9 : a.gpr .r9 = s.gpr .r9 := gpr_write_of_ne _ _ (by decide)
    obtain r10 : gbyte (h.gpr .r10) k = gbyte (s.gpr .r9) k &&& 0x0f := by
      show gbyte (s.gpr .r9 &&& s.gpr .r12) k = _
      rw [gbyte_and, hm, gbyte_mask hk]
    obtain r11 : gbyte (h.gpr .r11) k = gbyte (s.gpr .r9) k >>> 4 := by
      show gbyte ((((a.gpr .r9).setWidth 32 >>> 4).setWidth 64) &&& s.gpr .r12) k = _
      rw [g9, hm, gbyte_lsr4 _ hk]
    obtain v0e : vbyte (e.vpr .v0) (7 - k) = gbyte (s.gpr .r9) k &&& 0x0f := by
      show vbyte (c.gpr .r10 ++ _) (7 - k) = _
      rw [vbyte_append _ _ (by omega_using [hk])]; exact r10
    obtain v1f : vbyte (f.vpr .v1) (7 - k) = gbyte (s.gpr .r9) k >>> 4 := by
      show vbyte (d.gpr .r11 ++ _) (7 - k) = _
      rw [vbyte_append _ _ (by omega_using [hk])]; exact r11
    obtain elo : TabOk (e.vpr lo) tl := by
      show TabOk (if lo = .v1 then _ else if lo = .v0 then _ else s.vpr lo) tl
      simp only [hl.2, hl.1, ite_false]; exact hlo
    obtain fhi : TabOk (f.vpr hi) th := by
      show TabOk (if hi = .v0 then _ else if hi = .v1 then _ else if hi = .v0 then _ else s.vpr hi) th
      simp only [hh.1, hh.2, ite_false]; exact hhi
    obtain gv0 : g.vpr .v0 = ofVBytes fun i =>
        let j := (vbyte (e.vpr .v0) i).toNat % 32
        if j < 16 then vbyte (e.vpr lo) j else vbyte (e.vpr lo) (j - 16) := rfl
    obtain gv1 : g.vpr .v1 = ofVBytes fun i =>
        let j := (vbyte (f.vpr .v1) i).toNat % 32
        if j < 16 then vbyte (f.vpr hi) j else vbyte (f.vpr hi) (j - 16) := rfl
    have hv : h.vpr .v0 = g.vpr .v0 ^^^ g.vpr .v1 := rfl
    rw [hv, vbyte_xor', gv0, gv1, vperm_byte elo (by omega_using []) (by rw [v0e]; exact toNat_and_0f _),
      vperm_byte fhi (by omega_using []) (by rw [v1f]; exact toNat_shr4 _), v0e, v1f]
    rfl
  · change c.gpr r = s.gpr r
    rw [gpr_write_of_ne _ _ h11, gpr_write_of_ne _ _ h11, gpr_write_of_ne _ _ h10]
  · change (g.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e h0)]
    change (f.writeV .v1 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e h1)]
    change (e.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e h0)]
    change (d.writeV .v1 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e h1)]
    change (c.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e h0)]
    rfl

/-! ## The S-box layer -/

/-- A word from its bytes. -/
theorem setWidth_of_gbytes {x : BitVec 64} {y : BitVec 32}
    (h : ∀ k < 4, gbyte x k = y.extractLsb' (8 * k) 8) : x.setWidth 32 = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain e := congrArg (BitVec.getLsbD · (i % 8)) (h (i / 8) (by omega_using [hi]))
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega_using [], decide_true, Bool.true_and] at e
  rw [show 8 * (i / 8) + i % 8 = i by omega_using []] at e
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]; exact e

theorem bytes4 (a3 a2 a1 a0 : BitVec 8) :
    (a3 ++ a2 ++ a1 ++ a0).extractLsb' 0 8 = a0 ∧ (a3 ++ a2 ++ a1 ++ a0).extractLsb' 8 8 = a1 ∧
    (a3 ++ a2 ++ a1 ++ a0).extractLsb' 16 8 = a2 ∧ (a3 ++ a2 ++ a1 ++ a0).extractLsb' 24 8 = a3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
    repeat' split
    all_goals first | omega | (congr 1; omega_using [])

/-- Byte `k` of `τ(w)`. -/
theorem tau_byte (w : BitVec 32) {k : Nat} (hk : k < 4) :
    (Spec.Sm4.tau w).extractLsb' (8 * k) 8 = Spec.Sm4.sbox.getD (w.extractLsb' (8 * k) 8).toNat 0 := by
  obtain e : ∀ j, (w >>> (8 * j)).setWidth 8 = w.extractLsb' (8 * j) 8 := fun j => by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [BitVec.getLsbD_ushiftRight, hi]
  unfold Spec.Sm4.tau
  simp only [e]
  obtain h := bytes4 (Spec.Sm4.sbox.getD (w.extractLsb' (8 * 3) 8).toNat 0)
    (Spec.Sm4.sbox.getD (w.extractLsb' (8 * 2) 8).toNat 0) (Spec.Sm4.sbox.getD (w.extractLsb' (8 * 1) 8).toNat 0)
    (Spec.Sm4.sbox.getD (w.extractLsb' (8 * 0) 8).toNat 0)
  rcases k with _ | _ | _ | _ | k
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2
  · omega

theorem gbyte_setWidth (x : BitVec 64) {k : Nat} (hk : k < 4) :
    (x.setWidth 32).extractLsb' (8 * k) 8 = gbyte x k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_setWidth, hi]; omega_using [hk, hi]

theorem tau_run (s : State) (hc : Consts s) :
    ∃ t, runBlock isa tau s = some t ∧
      (t.gpr .r9).setWidth 32 = Spec.Sm4.tau ((s.gpr .r9).setWidth 32) ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r) ∧
      (∀ v, v ≠ .v0 → v ≠ .v1 → t.vpr v = s.vpr v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  obtain ⟨a, ae, ab, ag, av, am, ard, awr, asp, asy⟩ :=
    affine_run s hc.inLo hc.inHi (treg_ne 0) (treg_ne 1) hc.mask
  let b := a.writeV .v0 (ofVBytes fun i => VectorCrypto.aesSbox (vbyte (a.vpr .v0) i))
  let c := b.write .r9 (vdword (b.vpr .v0) 0)
  obtain bv : ∀ v, b.vpr v = if v = .v0 then ofVBytes (fun i => VectorCrypto.aesSbox (vbyte (a.vpr .v0) i))
      else a.vpr v := fun v => vpr_writeV _ _ _ _
  obtain cv : ∀ v, c.vpr v = b.vpr v := fun _ => rfl
  obtain cc : Consts c := hc.of_eq (fun v h0 h1 => by
      rw [cv, bv, ite_eq_right_iff.mpr (fun e => absurd e h0)]; exact av v h0 h1)
    ((gpr_write_of_ne _ _ (by decide)).trans (ag _ (by decide) (by decide)))
  obtain cb : ∀ k < 4, gbyte (c.gpr .r9) k =
      VectorCrypto.aesSbox (aff inLo inHi (gbyte (s.gpr .r9) k)) := fun k hk => by
    rw [show c.gpr .r9 = vdword (b.vpr .v0) 0 from gpr_write_self _ _ _, gbyte_vdword _ (by omega_using [hk]), bv]
    simp only [↓reduceIte]
    rw [vbyte_packed _ (by omega_using []), ab k hk]
  obtain ⟨d, de, db, dg, dv, dm, drd, dwr, dsp, dsy⟩ :=
    affine_run c cc.outLo cc.outHi (treg_ne 2) (treg_ne 3) cc.mask
  let e := d.write .r9 (vdword (d.vpr .v0) 0)
  refine ⟨e, ?_, ?_, fun r h9 h10 h11 => ?_, fun v h0 h1 => ?_, dm.trans am, drd.trans ard, dwr.trans awr,
    dsp.trans asp, dsy.trans asy⟩
  · have hb : runBlock isa ([.vop (.sbox .v0 .v0), .mfvsrd .r9 .v0] : List Instr) a = some c := by
      rw [runBlock_cons, exec_vsbox, runStep_some, runBlock_cons, exec_mfvsrd, runStep_some, runBlock_nil]
    obtain hd : runBlock isa ([.mfvsrd .r9 .v0] : List Instr) d = some e := by
      rw [runBlock_cons, exec_mfvsrd, runStep_some, runBlock_nil]
    rw [tau, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, ae,
      Option.bind_some, hb, Option.bind_some, de, Option.bind_some, hd]
  · refine setWidth_of_gbytes fun k hk => ?_
    rw [tau_byte _ hk, gbyte_setWidth _ hk]
    rw [show e.gpr .r9 = vdword (d.vpr .v0) 0 from gpr_write_self _ _ _, gbyte_vdword _ (by omega_using [hk]), db k hk,
      cb k hk, Proof.Aes.Vector.sbox_eq, sbox_affine]
  · rw [gpr_write_of_ne _ _ h9, dg r h10 h11, gpr_write_of_ne _ _ h9]
    exact ag r h10 h11
  · rw [show e.vpr v = d.vpr v from rfl, dv v h0 h1, cv, bv, ite_eq_right_iff.mpr (fun e => absurd e h0)]
    exact av v h0 h1

/-! ## The linear map -/

theorem rotate_complement (x : BitVec 32) (r : Nat) (hr : 0 < r) (hr' : r < 32) :
    x.rotateRight (32 - r) = x.rotateLeft r := by
  rw [BitVec.rotateRight_def, BitVec.rotateLeft_def, Nat.mod_eq_of_lt hr',
    Nat.mod_eq_of_lt (show 32 - r < 32 by omega_using [hr]), Nat.sub_sub_self (by omega_using [hr'] : r ≤ 32)]
  exact BitVec.or_comm _ _

theorem linear_eq (x : BitVec 32) :
    x ^^^ x.rotateRight 30 ^^^ x.rotateRight 22 ^^^ x.rotateRight 14 ^^^ x.rotateRight 8 =
      Spec.Sm4.linear x := by
  rw [show 30 = 32 - 2 by rfl, rotate_complement x 2 (by decide) (by decide),
    show 22 = 32 - 10 by rfl, rotate_complement x 10 (by decide) (by decide),
    show 14 = 32 - 18 by rfl, rotate_complement x 18 (by decide) (by decide),
    show 8 = 32 - 24 by rfl, rotate_complement x 24 (by decide) (by decide)]
  rfl

theorem setWidth_rot (x : BitVec 32) (k : Nat) : ((x.rotateRight k).setWidth 64).setWidth 32 = x.rotateRight k := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]

theorem linear_run (s : State) :
    ∃ t, runBlock isa linear s = some t ∧
      (t.gpr .r11).setWidth 32 = Spec.Sm4.linear ((s.gpr .r9).setWidth 32) ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r) ∧
      t.vpr = s.vpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  let x := (s.gpr .r9).setWidth 32
  let a1 := s.write .r10 ((x.rotateRight 30).setWidth 64)
  let a2 := a1.write .r11 (a1.gpr .r9 ^^^ a1.gpr .r10)
  let b1 := a2.write .r10 (((a2.gpr .r9).setWidth 32 |>.rotateRight 22).setWidth 64)
  let b2 := b1.write .r11 (b1.gpr .r11 ^^^ b1.gpr .r10)
  let c1 := b2.write .r10 (((b2.gpr .r9).setWidth 32 |>.rotateRight 14).setWidth 64)
  let c2 := c1.write .r11 (c1.gpr .r11 ^^^ c1.gpr .r10)
  let d1 := c2.write .r10 (((c2.gpr .r9).setWidth 32 |>.rotateRight 8).setWidth 64)
  let d2 := d1.write .r11 (d1.gpr .r11 ^^^ d1.gpr .r10)
  refine ⟨d2, ?_, ?_, fun r h10 h11 => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [linear, runBlock_cons, exec_logic, exec_rotr_w (by decide : 30 < 32),
      exec_rotr_w (by decide : 22 < 32), exec_rotr_w (by decide : 14 < 32), exec_rotr_w (by decide : 8 < 32),
      runStep_some, runBlock_nil]
    rfl
  · have e1 : a1.gpr .r9 = s.gpr .r9 := gpr_write_of_ne _ _ (by decide)
    obtain e2 : a2.gpr .r9 = s.gpr .r9 := (gpr_write_of_ne _ _ (by decide)).trans e1
    obtain e3 : b1.gpr .r9 = s.gpr .r9 := (gpr_write_of_ne _ _ (by decide)).trans e2
    obtain e4 : b2.gpr .r9 = s.gpr .r9 := (gpr_write_of_ne _ _ (by decide)).trans e3
    obtain e5 : c1.gpr .r9 = s.gpr .r9 := (gpr_write_of_ne _ _ (by decide)).trans e4
    obtain e6 : c2.gpr .r9 = s.gpr .r9 := (gpr_write_of_ne _ _ (by decide)).trans e5
    obtain f2 : (a2.gpr .r11).setWidth 32 = x ^^^ x.rotateRight 30 := by
      rw [show a2.gpr .r11 = a1.gpr .r9 ^^^ a1.gpr .r10 from gpr_write_self _ _ _, e1,
        show a1.gpr .r10 = _ from gpr_write_self _ _ _, BitVec.setWidth_xor, setWidth_rot]
    obtain f4 : (b2.gpr .r11).setWidth 32 = x ^^^ x.rotateRight 30 ^^^ x.rotateRight 22 := by
      rw [show b2.gpr .r11 = b1.gpr .r11 ^^^ b1.gpr .r10 from gpr_write_self _ _ _,
        show b1.gpr .r11 = a2.gpr .r11 from gpr_write_of_ne _ _ (by decide),
        show b1.gpr .r10 = _ from gpr_write_self _ _ _, e2, BitVec.setWidth_xor, setWidth_rot, f2]
    obtain f6 : (c2.gpr .r11).setWidth 32 = x ^^^ x.rotateRight 30 ^^^ x.rotateRight 22 ^^^ x.rotateRight 14 := by
      rw [show c2.gpr .r11 = c1.gpr .r11 ^^^ c1.gpr .r10 from gpr_write_self _ _ _,
        show c1.gpr .r11 = b2.gpr .r11 from gpr_write_of_ne _ _ (by decide),
        show c1.gpr .r10 = _ from gpr_write_self _ _ _, e4, BitVec.setWidth_xor, setWidth_rot, f4]
    rw [show d2.gpr .r11 = d1.gpr .r11 ^^^ d1.gpr .r10 from gpr_write_self _ _ _,
      show d1.gpr .r11 = c2.gpr .r11 from gpr_write_of_ne _ _ (by decide),
      show d1.gpr .r10 = _ from gpr_write_self _ _ _, e6, BitVec.setWidth_xor, setWidth_rot, f6, ← linear_eq]
  · simp only [d2, d1, c2, c1, b2, b1, a2, a1, gpr_write_of_ne _ _ h10, gpr_write_of_ne _ _ h11]

/-! ## A round -/

/-- The block's words, in `wordReg 0 … 3`. -/
def words (s : State) (w : Nat) : BitVec 32 := (s.gpr (wordReg w)).setWidth 32

theorem wordReg_ne (j : Nat) : wordReg j ≠ .r9 ∧ wordReg j ≠ .r10 ∧ wordReg j ≠ .r11 ∧ wordReg j ≠ .r12 ∧
    wordReg j ≠ .r3 ∧ wordReg j ≠ .r0 := by
  obtain h := Nat.mod_lt j (by decide : 4 > 0)
  unfold wordReg
  generalize j % 4 = k at h
  rcases k with _ | _ | _ | _ | k <;> first | omega | decide

theorem wordReg_inj : ∀ a < 4, ∀ b < 4, wordReg a = wordReg b → a = b := by decide

theorem wordReg_mod (j : Nat) : wordReg (j % 4) = wordReg j := by simp [wordReg]

/-- The round key `i` from the schedule at `r3`. -/
def rkey (s : State) (i : Nat) : BitVec 32 := s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (4 * i)) 32

theorem keyIdx_lt (dir : Dir) {i : Nat} (hi : i < 32) : rkIdx dir i < 32 := by
  cases dir <;> simp only [rkIdx] <;> omega_arith

theorem round_run (dir : Dir) {s : State} {i : Nat} (hi : i < 32) (hc : Consts s)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (4 * rkIdx dir i)) 4) :
    ∃ t, runBlock isa (round dir i) s = some t ∧
      (∀ w < 4, words t w = Proof.Sm4.sround .enc (rkey s (rkIdx dir i)) (i % 4) (words s) w) ∧
      Consts t ∧
      (∀ r, r ≠ wordReg i → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r) ∧
      (∀ v, v ≠ .v0 → v ≠ .v1 → t.vpr v = s.vpr v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  let q1 := wordReg (i + 1)
  let q2 := wordReg (i + 2)
  let q3 := wordReg (i + 3)
  let ra := wordReg i
  obtain hki := keyIdx_lt dir hi
  let a := s.write .r9 ((rkey s (rkIdx dir i)).setWidth 64)
  let b := a.write .r9 (a.gpr .r9 ^^^ a.gpr q1)
  let c := b.write .r9 (b.gpr .r9 ^^^ b.gpr q2)
  let d := c.write .r9 (c.gpr .r9 ^^^ c.gpr q3)
  obtain hm : runBlock isa ([.load .w .r9 .r3 (4 * rkIdx dir i), .logic .xor .r9 .r9 q1, .logic .xor .r9 .r9 q2,
      .logic .xor .r9 .r9 q3] : List Instr) s = some d := by
    rw [runBlock_cons, exec_load_w (by decide) (by omega_using [hki]) hr, runStep_some, runBlock_cons, exec_logic, runStep_some,
      runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_nil]
    rfl
  obtain dg : ∀ r, r ≠ .r9 → d.gpr r = s.gpr r := fun r h => by
    rw [gpr_write_of_ne _ _ h, gpr_write_of_ne _ _ h, gpr_write_of_ne _ _ h, gpr_write_of_ne _ _ h]
  obtain ag : ∀ r, r ≠ .r9 → a.gpr r = s.gpr r := fun r h => gpr_write_of_ne _ _ h
  obtain bg : ∀ r, r ≠ .r9 → b.gpr r = s.gpr r := fun r h => (gpr_write_of_ne _ _ h).trans (ag r h)
  obtain cg : ∀ r, r ≠ .r9 → c.gpr r = s.gpr r := fun r h => (gpr_write_of_ne _ _ h).trans (bg r h)
  obtain d9 : (d.gpr .r9).setWidth 32 = rkey s (rkIdx dir i) ^^^ words s (i + 1) ^^^ words s (i + 2) ^^^ words s (i + 3) := by
    rw [show d.gpr .r9 = c.gpr .r9 ^^^ c.gpr q3 from gpr_write_self _ _ _,
      show c.gpr .r9 = b.gpr .r9 ^^^ b.gpr q2 from gpr_write_self _ _ _,
      show b.gpr .r9 = a.gpr .r9 ^^^ a.gpr q1 from gpr_write_self _ _ _,
      show a.gpr .r9 = _ from gpr_write_self _ _ _, cg _ (wordReg_ne _).1, bg _ (wordReg_ne _).1,
      ag _ (wordReg_ne _).1, BitVec.setWidth_xor, BitVec.setWidth_xor, BitVec.setWidth_xor,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    rfl
  obtain dc : Consts d := hc.of_eq (fun _ _ _ => rfl) (dg _ (by decide))
  obtain ⟨e, ee, e9, eg, ev, em, erd, ewr, esp, esy⟩ := tau_run d dc
  obtain ⟨f, fe, f11, fg, fv, fm, frd, fwr, fsp, fsy⟩ := linear_run e
  let t := f.write ra (f.gpr ra ^^^ f.gpr .r11)
  obtain tg : ∀ r, r ≠ ra → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r := fun r ha h9 h10 h11 => by
    rw [gpr_write_of_ne _ _ ha, fg r h10 h11, eg r h9 h10 h11, dg r h9]
  obtain tv : ∀ v, v ≠ .v0 → v ≠ .v1 → t.vpr v = s.vpr v := fun v h0 h1 => by
    rw [show t.vpr v = f.vpr v from rfl, fv, ev v h0 h1]; rfl
  refine ⟨t, ?_, fun w hw => ?_, hc.of_eq tv (tg _ (wordReg_ne i).2.2.2.1.symm (by decide) (by decide) (by decide)), tg, tv,
    fm.trans (em.trans rfl), frd.trans (erd.trans rfl), fwr.trans (ewr.trans rfl), fsp.trans (esp.trans rfl),
    fsy.trans (esy.trans rfl)⟩
  · rw [round, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, hm,
      Option.bind_some, ee, Option.bind_some, fe, Option.bind_some, runBlock_cons, exec_logic, runStep_some,
      runBlock_nil]
  · by_cases h : w = i % 4
    · subst w
      obtain ha := wordReg_ne i
      rw [words, wordReg_mod, show t.gpr ra = f.gpr ra ^^^ f.gpr .r11 from gpr_write_self _ _ _,
        fg _ ha.2.1 ha.2.2.1, eg _ ha.1 ha.2.1 ha.2.2.1, dg _ ha.1, BitVec.setWidth_xor, f11, e9, d9]
      obtain e : ∀ k, wordReg (i % 4 + k) = wordReg (i + k) := fun k => by
        rw [← wordReg_mod (i % 4 + k), ← wordReg_mod (i + k), Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      simp only [Proof.Sm4.sround, ite_true, Impl.Sm4.Lin.t_enc, words, wordReg_mod, e, Spec.Sm4.t]
      ac_rfl
    · have hreg : wordReg w ≠ ra := fun e => h (wordReg_inj w hw _ (Nat.mod_lt _ (by decide))
        (e.trans (wordReg_mod i).symm))
      obtain hn := wordReg_ne w
      rw [words, tg _ hreg hn.1 hn.2.1 hn.2.2.1]
      simp only [Proof.Sm4.sround, h, ite_false, words]

/-! ## The rounds -/

open VG.Proof.Sm4 (sround quads)

/-- The first `n` rounds, in place. -/
def steps (K : Nat → BitVec 32) (n : Nat) (x : Nat → BitVec 32) : Nat → BitVec 32 :=
  (List.range n).foldl (fun z i => sround .enc (K i) (i % 4) z) x

theorem steps_succ (K : Nat → BitVec 32) (n : Nat) (x : Nat → BitVec 32) :
    steps K (n + 1) x = sround .enc (K n) (n % 4) (steps K n x) := by
  simp only [steps, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem sround_congr (k : BitVec 32) {a w : Nat} {x y : Nat → BitVec 32}
    (ha : a < 4) (h : ∀ j < 4, x j = y j) (hw : w < 4) :
    sround .enc k a x w = sround .enc k a y w := by
  unfold sround
  split
  · rw [h a ha, h _ (Nat.mod_lt _ (by decide)), h _ (Nat.mod_lt _ (by decide)), h _ (Nat.mod_lt _ (by decide))]
  · exact h w hw

theorem steps_quads (K : Nat → BitVec 32) (x : Nat → BitVec 32) (n : Nat) :
    steps K (4 * n) x = quads .enc K n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [steps, Proof.Sm4.range_four, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change sround .enc (K (4 * n + 3)) ((4 * n + 3) % 4)
      (sround .enc (K (4 * n + 2)) ((4 * n + 2) % 4)
        (sround .enc (K (4 * n + 1)) ((4 * n + 1) % 4)
          (sround .enc (K (4 * n)) ((4 * n) % 4) (steps K (4 * n) x)))) = _
    rw [ih, show (4 * n) % 4 = 0 by omega_using [], show (4 * n + 1) % 4 = 1 by omega_using [],
      show (4 * n + 2) % 4 = 2 by omega_using [], show (4 * n + 3) % 4 = 3 by omega_using []]
    rfl

/-- The registers the rounds write. -/
def written : List Reg := [.r4, .r6, .r7, .r8, .r9, .r10, .r11]

theorem wordReg_mem (j : Nat) : wordReg j ∈ written := by
  obtain h := Nat.mod_lt j (by decide : 4 > 0)
  unfold wordReg
  generalize j % 4 = k at h
  rcases k with _ | _ | _ | _ | k <;> first | omega | decide

theorem rounds_run (dir : Dir) (s : State) (n : Nat) (hn : n ≤ 32) (hc : Consts s)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (4 * i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap (round dir)) s = some t ∧
      (∀ w < 4, words t w = steps (fun i => rkey s (rkIdx dir i)) n (words s) w) ∧
      Consts t ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      (∀ v, v ≠ .v0 → v ≠ .v1 → t.vpr v = s.vpr v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  induction n with
  | zero => exact ⟨s, rfl, fun _ _ => rfl, hc, fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨a, ae, aw, ac, ag, av, am, ard, awr, asp, asy⟩ := ih (by omega_using [hn])
    obtain ab : a.gpr .r3 = s.gpr .r3 := ag _ (by decide)
    obtain ar : InRegions (a.rd ++ a.wr) (a.gpr .r3 + BitVec.ofNat 64 (4 * rkIdx dir n)) 4 := by
      rw [ard, awr, ab]; exact hr _ (keyIdx_lt dir (by omega_using [hn]))
    obtain ⟨b, be, bw, bc, bg, bv, bm, brd, bwr, bsp, bsy⟩ := round_run dir (by omega_using [hn]) ac ar
    refine ⟨b, ?_, fun w hw => ?_, bc, fun r hr => ?_, fun v h0 h1 => (bv v h0 h1).trans (av v h0 h1),
      bm.trans am, brd.trans ard, bwr.trans awr, bsp.trans asp, bsy.trans asy⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        VG.Interleave.runBlock_append, ae, Option.bind_some, be]
    · rw [bw w hw, steps_succ, show rkey a (rkIdx dir n) = rkey s (rkIdx dir n) by rw [rkey, rkey, am, ab]]
      exact sround_congr _ (Nat.mod_lt _ (by decide)) aw hw
    · have hreg : r ≠ wordReg n := fun he => hr (he ▸ wordReg_mem n)
      obtain h9 : r ≠ .r9 := fun he => hr (by simp [written, he])
      obtain h10 : r ≠ .r10 := fun he => hr (by simp [written, he])
      obtain h11 : r ≠ .r11 := fun he => hr (by simp [written, he])
      exact (bg r hreg h9 h10 h11).trans (ag r hr)

open VG.Impl.Modes.PPC64LE (sb)
open VG.Impl.Sm4.PPC64LE (tailSlot slots)
open VG.Proof.Modes.PPC64LE (ScrIn coreRegion blkRegion blkAddr Layout CoreSpec kept KeptBut)
open VG.Spec.Aes (bytesAt)
/-! ## The tables -/

/-- Table `k` as `lxvd2xTbl` loads it. -/
abbrev tval (k : Nat) : BitVec 128 := tableWords.getD (2 * k) 0 ++ tableWords.getD (2 * k + 1) 0

theorem tval_ok : TabOk (tval 0) inLo ∧ TabOk (tval 1) inHi ∧ TabOk (tval 2) outLo ∧ TabOk (tval 3) outHi := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro j hj; revert j; decide)

theorem tableWords_length : tableWords.length = 8 := rfl

theorem treg_inj : ∀ a < 4, ∀ b < 4, treg a = treg b → a = b := by decide

/-- After loading the tables `0 … n - 1`. -/
theorem loadT_run (s : State) (n : Nat) (hn : n ≤ 4) (h10 : s.gpr .r10 = s.syms tableSym) :
    ∃ t, runBlock isa ((List.range n).flatMap fun k =>
        [.li .r11 (16 * k), .lxvd2xTbl (treg k) .r10 .r11 tableSym tableWords]) s = some t ∧
      (∀ k < n, t.vpr (treg k) = tval k) ∧
      (∀ v, (∀ k < n, v ≠ treg k) → t.vpr v = s.vpr v) ∧
      (∀ r, r ≠ .r11 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms ∧ t.lr = s.lr ∧
      t.unknowns = s.unknowns := by
  induction n with
  | zero => exact ⟨s, rfl, fun _ h => absurd h (by omega_using []), fun _ _ => rfl, fun _ _ => rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨a, ae, av, avo, ag, am, ard, awr, asp, asy, alr, aun⟩ := ih (by omega_using [hn])
    let b := a.write .r11 (BitVec.ofNat 64 (16 * n))
    let c := b.writeV (treg n) (tval n)
    obtain hb10 : b.gpr .r10 = b.syms tableSym := by
      rw [show b.syms = s.syms from asy, gpr_write_of_ne _ _ (by decide), ag _ (by decide), h10]
    obtain hb11 : (b.gpr .r11).toNat = 16 * n := by
      rw [gpr_write_self, BitVec.toNat_ofNat]; omega_using [hn]
    obtain hc : exec (.lxvd2xTbl (treg n) .r10 .r11 tableSym tableWords) b = some c := by
      obtain e1 : 16 * n / 8 = 2 * n := by omega_using []
      obtain e2 : 16 * n % 8 = 0 := by omega_using []
      obtain e3 : 2 * n + 2 ≤ 8 := by omega_using [hn]
      obtain e4 : (Reg.r10 ≠ .r0) := by decide
      simp only [exec, hb10, hb11, e1, e2, e3, e4, tableWords_length, ne_eq, not_false_eq_true, and_self,
        ↓reduceIte]
      rfl
    refine ⟨c, ?_, fun k hk => ?_, fun v hv => ?_, fun r hr => ?_, am, ard, awr, asp, asy, alr, aun⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        VG.Interleave.runBlock_append, ae, Option.bind_some, runBlock_cons, exec_li (by omega_using [hn]), runStep_some,
        runBlock_cons, hc, runStep_some, runBlock_nil]
    · rw [vpr_writeV]
      by_cases e : k = n
      · subst e; simp
      · rw [ite_eq_right_iff.mpr (fun h => absurd (treg_inj k (by omega_using [hn, hk]) n (by omega_using [hn]) h) e)]
        exact av k (by omega_using [hk, e])
    · rw [vpr_writeV, ite_eq_right_iff.mpr (fun h => absurd h (hv n (by omega_using [])))]
      exact avo v fun k hk => hv k (by omega_using [hk])
    · exact (gpr_write_of_ne _ _ hr).trans (ag r hr)

theorem mask_eq : ((0x0f0f : BitVec 16) ++ (0 : BitVec 16)).signExtend 64 ||| (0x0f0f : BitVec 16).setWidth 64 =
    (0x0f0f0f0f : BitVec 64) := by decide

theorem loadTables_run (s : State) :
    ∃ t, runBlock isa loadTables s = some t ∧ Consts t ∧
      (∀ v, v ≠ .v12 → v ≠ .v13 → v ≠ .v14 → v ≠ .v15 → t.vpr v = s.vpr v) ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  let a : State := { s.write .r10 (s.syms tableSym) with lr := s.unknowns 0, unknowns := fun n => s.unknowns (n + 1) }
  obtain a10 : a.gpr .r10 = a.syms tableSym := by
    show (s.write .r10 (s.syms tableSym)).gpr .r10 = s.syms tableSym; exact gpr_write_self _ _ _
  obtain ⟨b, be, bv, bvo, bg, bm, brd, bwr, bsp, bsy, _, _⟩ := loadT_run a 4 (by decide) a10
  let c := b.write .r12 (((0x0f0f : BitVec 16) ++ (0 : BitVec 16)).signExtend 64)
  let d := c.write .r12 (c.gpr .r12 ||| (0x0f0f : BitVec 16).setWidth 64)
  obtain dv : ∀ v, d.vpr v = b.vpr v := fun _ => rfl
  obtain dg : ∀ r, r ≠ .r12 → d.gpr r = b.gpr r := fun r h => (gpr_write_of_ne _ _ h).trans (gpr_write_of_ne _ _ h)
  have ok := tval_ok
  refine ⟨d, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, fun v h12 h13 h14 h15 => ?_, fun r h10 h11 h12 => ?_, bm, brd, bwr, bsp, bsy⟩
  · rw [loadTables, List.cons_append, runBlock_cons]
    simp only [exec, ne_eq, show ¬(Reg.r10 = .r0) by decide, not_false_eq_true, ↓reduceIte]
    rw [runStep_some, VG.Interleave.runBlock_append, be, Option.bind_some, runBlock_cons, exec_lis, runStep_some,
      runBlock_cons, exec_ori, runStep_some, runBlock_nil]
  · rw [dv, bv 0 (by decide)]; exact ok.1
  · rw [dv, bv 1 (by decide)]; exact ok.2.1
  · rw [dv, bv 2 (by decide)]; exact ok.2.2.1
  · rw [dv, bv 3 (by decide)]; exact ok.2.2.2
  · rw [gpr_write_self, gpr_write_self, mask_eq]
  · rw [dv, bvo v fun k hk => ?_]
    · rfl
    · rcases k with _ | _ | _ | _ | k
      all_goals first | omega | (intro e; subst e; contradiction)
  · rw [dg r h12, bg r h11]
    exact gpr_write_of_ne _ _ h10

/-! ## The block -/

theorem readBE_word (m : Mem) (p : Addr) (i : Nat) (hi : i < 4) :
    rev32 (m.readW (p + BitVec.ofNat 64 (4 * i)) 32) = Spec.Sm4.wordAt (Spec.Sm4.blockAt m p) (4 * i) := by
  rw [rev32_readW, Spec.Sm4.wordAt]
  rw [Proof.Sm4.blockAt_getD _ _ (by omega_using [hi]), Proof.Sm4.blockAt_getD _ _ (by omega_using [hi]),
    Proof.Sm4.blockAt_getD _ _ (by omega_using [hi]), Proof.Sm4.blockAt_getD _ _ (by omega_using [hi])]
  have add1 (j : Nat) : p + BitVec.ofNat 64 (j + 1) = p + BitVec.ofNat 64 j + 1 := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  simp only [show 4 * i + 2 = (4 * i + 1) + 1 by omega_using [], show 4 * i + 3 = ((4 * i + 1) + 1) + 1 by omega_using [], add1]

theorem wordReg_ne_sb (j : Nat) : wordReg j ≠ sb ∧ wordReg j ≠ .r0 := by
  obtain h := Nat.mod_lt j (by decide : 4 > 0)
  unfold wordReg
  generalize j % 4 = k at h
  rcases k with _ | _ | _ | _ | k <;> first | omega | decide

/-- The offset of word `i` of the block. -/
abbrev woff (i : Nat) : Nat := 8 * tailSlot + 4 * i

theorem loads_run (s : State) (n : Nat) (hn : n ≤ 4)
    (hr : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofNat 64 (woff i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap fun i =>
        [.li .r0 (woff i), .loadRev .w (wordReg i) sb .r0]) s = some t ∧
      (∀ j < n, words t j = rev32 (s.mem.readW (s.gpr sb + BitVec.ofNat 64 (woff j)) 32)) ∧
      (∀ r, r ≠ .r0 → (∀ j < n, r ≠ wordReg j) → t.gpr r = s.gpr r) ∧
      t.vpr = s.vpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  induction n with
  | zero => exact ⟨s, rfl, fun _ h => absurd h (by omega_using []), fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨a, ae, aw, ag, av, am, ard, awr, asp, asy⟩ := ih (by omega_using [hn])
    obtain ab : a.gpr sb = s.gpr sb := ag _ (by decide) (fun j _ => (wordReg_ne_sb j).1.symm)
    let b := a.write .r0 (BitVec.ofNat 64 (woff n))
    obtain bb : b.gpr sb + b.gpr .r0 = s.gpr sb + BitVec.ofNat 64 (woff n) := by
      rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, ab]
    obtain br : InRegions (b.rd ++ b.wr) (b.gpr sb + b.gpr .r0) 4 := by
      rw [bb]; show InRegions (a.rd ++ a.wr) _ 4; rw [ard, awr]; exact hr n (by omega_using [hn])
    let c := b.write (wordReg n) ((rev32 (b.mem.readW (b.gpr sb + b.gpr .r0) 32)).setWidth 64)
    obtain hw := wordReg_ne_sb n
    refine ⟨c, ?_, fun j hj => ?_, fun r h0 hr' => ?_, av, am, ard, awr, asp, asy⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        VG.Interleave.runBlock_append, ae, Option.bind_some, runBlock_cons,
        exec_li (by rw [woff, tailSlot_eq]; omega_using [hn]), runStep_some, runBlock_cons,
        exec_loadRev_w (by decide) br, runStep_some, runBlock_nil]
    · by_cases h : j = n
      · subst j
        rw [words, show c.gpr (wordReg n) = _ from gpr_write_self _ _ _, bb,
          BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
        show rev32 (a.mem.readW _ 32) = _
        rw [am]
      · rw [words, gpr_write_of_ne _ _ (fun e => h (wordReg_inj j (by omega_using [hn, hj]) n (by omega_using [hn]) e)),
          gpr_write_of_ne _ _ (wordReg_ne_sb j).2]
        exact aw j (by omega_using [hj, h])
    · rw [gpr_write_of_ne _ _ (hr' n (by omega_using [])), gpr_write_of_ne _ _ h0]
      exact ag r h0 fun j hj => hr' j (by omega_using [hj])

theorem frame_write_word (m : Mem) (p : Addr) (v : BitVec 32) : Frame [⟨p, 4⟩] m (m.writeW p v) := by
  intro x hx
  simp only [Mem.writeW, Mem.write]
  exact ite_eq_right (fun h => hx _ List.mem_cons_self h)

theorem stores_run (s : State) (n : Nat) (hn : n ≤ 4)
    (hw : ∀ i < 4, InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (woff i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap fun i =>
        [.li .r0 (woff i), .storeRev .w (wordReg (3 - i)) sb .r0]) s = some t ∧
      (∀ j < n, t.mem.readW (s.gpr sb + BitVec.ofNat 64 (woff j)) 32 = rev32 (words s (3 - j))) ∧
      (∀ r, r ≠ .r0 → t.gpr r = s.gpr r) ∧
      Frame [⟨s.gpr sb + BitVec.ofNat 64 (8 * tailSlot), 16⟩] s.mem t.mem ∧
      t.vpr = s.vpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  induction n with
  | zero => exact ⟨s, rfl, fun _ h => absurd h (by omega_using []), fun _ _ => rfl, Frame.refl _ _, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨a, ae, aw, ag, af, av, ard, awr, asp, asy⟩ := ih (by omega_using [hn])
    obtain ab : a.gpr sb = s.gpr sb := ag _ (by decide)
    let b := a.write .r0 (BitVec.ofNat 64 (woff n))
    obtain bb : b.gpr sb + b.gpr .r0 = s.gpr sb + BitVec.ofNat 64 (woff n) := by
      rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, ab]
    obtain br : InRegions b.wr (b.gpr sb + b.gpr .r0) 4 := by
      rw [bb]; show InRegions a.wr _ 4; rw [awr]; exact hw n (by omega_using [hn])
    obtain bv : b.gpr (wordReg (3 - n)) = s.gpr (wordReg (3 - n)) :=
      (gpr_write_of_ne _ _ (wordReg_ne_sb _).2).trans (ag _ (wordReg_ne_sb _).2)
    let m' := b.mem.writeW (s.gpr sb + BitVec.ofNat 64 (woff n)) (rev32 (words s (3 - n)))
    let c : State := { b with mem := m' }
    obtain bf : Frame [⟨s.gpr sb + BitVec.ofNat 64 (woff n), 4⟩] a.mem c.mem := frame_write_word _ _ _
    refine ⟨c, ?_, fun j hj => ?_, fun r h0 => (gpr_write_of_ne _ _ h0).trans (ag r h0), ?_, av, ard, awr,
      asp, asy⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        VG.Interleave.runBlock_append, ae, Option.bind_some, runBlock_cons,
        exec_li (by rw [woff, tailSlot_eq]; omega_using [hn]), runStep_some, runBlock_cons,
        exec_storeRev_w (by decide) br, runStep_some, runBlock_nil, bb, bv]
      rfl
    · by_cases h : j = n
      · subst j; exact Mem.readW_writeW_self32 _ _ _
      · rw [bf.readW (w := 32) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          exact VG.Offset.disjoint (s.gpr sb) (by rw [woff, woff, tailSlot_eq]; omega_using [h])
            (by rw [woff, tailSlot_eq]; omega_using [hn, hj]) (by rw [woff, tailSlot_eq]; omega_using [hn])) (by decide)]
        exact aw j (by omega_using [hj, h])
    · refine af.trans (bf.sub (fun r hr => ?_))
      simp only [List.mem_singleton] at hr; subst r
      refine ⟨_, List.mem_cons_self, ?_⟩
      rw [woff, ← VG.Offset.add_add (s.gpr sb) (8 * tailSlot) (4 * n)]
      exact VG.Offset.sub_base _ (by omega_using [hn] : 4 * n + 4 ≤ 16)

theorem stored_bytes {m : Mem} {p : Addr} {z : Nat → BitVec 32}
    (h : ∀ i < 4, m.readW (p + BitVec.ofNat 64 (4 * i)) 32 = rev32 (z (3 - i))) :
    bytesAt m p 16 = (Proof.Sm4.outBlock z).toList := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i hi _
  obtain hi16 : i < 16 := by simpa [bytesAt] using hi
  simp only [bytesAt, List.getElem_map, List.getElem_range, Vector.getElem_toList]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain b := Mem.readW_byte m (p + BitVec.ofNat 64 (4 * (i / 4))) (i := i % 4) (by omega_using [])
  rw [VG.Offset.add_add, show 4 * (i / 4) + i % 4 = i by omega_using [], h (i / 4) (by omega_using [hi16])] at b
  rw [b, BitVec.getLsbD_extractLsb', Proof.Sm4.getLsbD_outBlock' z hi16 hj]
  simp only [hj, decide_true, Bool.true_and]
  change (byteRev32 (z (3 - i / 4))).getLsbD (8 * (i % 4) + j) = _
  rw [byteRev32_getLsbD _ (by omega_using [hj])]
  congr 1 <;> omega_using [hj]

/-- Bit `i` of a little-endian 32-bit word is bit `i % 8` of its byte `i / 8`. -/
theorem getLsbD_readW32' (m : Mem) (a : Addr) {i : Nat} (hi : i < 32) :
    (m.readW a 32).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8) := by
  rw [← Mem.extractLsb'_read m a (n := 4) (by omega_using [hi]), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
    show i % 8 < 8 from Nat.mod_lt _ (by decide)]
  congr 1; omega_using []

theorem schedule_readW (m : Mem) (p : Addr) (i : Nat) (hi : i < 32) :
    m.readW (p + BitVec.ofNat 64 (4 * i)) 32 = (Spec.Sm4.scheduleAt m p).getD i 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [Proof.Aes.getD_eq _ hi, getLsbD_readW32' m _ hj, VG.Offset.add_add]
  obtain h := Proof.Sm4.getLsbD_scheduleAt m p (i := i) (c := j / 8) (j := j % 8) hi (by omega_using [hj]) (by omega_using [])
  rw [show 8 * (j / 8) + j % 8 = j by omega_using []] at h
  rw [h]

theorem steps_congr (K L : Nat → BitVec 32) (n : Nat) (x y : Nat → BitVec 32)
    (hk : ∀ i < n, K i = L i) (hx : ∀ j < 4, x j = y j) :
    ∀ w < 4, steps K n x w = steps L n y w := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    intro w hw
    rw [steps_succ, steps_succ, hk n (by omega_using [])]
    exact sround_congr _ (Nat.mod_lt _ (by decide)) (ih (fun i hi => hk i (by omega_using [hi]))) hw

/-! ## The key, in place -/

/-- The key is ready: the schedule at `r3`, apart from the core's slots and
the regions `ws`. -/
def Ready (s : State) (B : Addr) (ws : List Region) (k : Spec.Sm4.Schedule) : Prop :=
  Proof.Sm4.PPC64LE.KeyArgs s (⟨B, 8 * slots⟩ :: ws) k

/-- The schedule survives a frame within its regions. -/
theorem keyArgs_frame {s s' : State} {rs rs' : List Region} {k : Spec.Sm4.Schedule}
    (h : Proof.Sm4.PPC64LE.KeyArgs s rs k) (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd)
    (hf : Frame rs' s.mem s'.mem) (hs : ∀ r ∈ rs', ∃ r' ∈ rs, Region.Sub r r') :
    Proof.Sm4.PPC64LE.KeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [e, hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hk]
  refine (Proof.Sm4.scheduleAt_congr fun i hi => hf.bytes (R := ⟨p, 128⟩) (fun r hr => ?_)
    (by show 128 ≤ 2 ^ 64; omega_using []) hi).symm
  obtain ⟨r', hr', hsub⟩ := hs r hr
  exact (hdis r' hr').sub_right hsub

theorem kept_ne : ∀ r ∈ kept, r ≠ .r0 ∧ r ∉ written ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 ∧ r ≠ sb := by decide

/-! ## The block -/

theorem invCipher_bytes (k : Spec.Sm4.Schedule) (m : Mem) (p : Addr) :
    Spec.Sm4.invCipher k (bytesAt m p 16) =
      (Proof.Sm4.outBlock (Proof.Sm4.quads .enc (fun i => k.getD (31 - i) 0) 8
        (Proof.Sm4.ofBlock (Spec.Sm4.blockAt m p)))).toList := by
  rw [Spec.Sm4.invCipher, Proof.Sm4.bytesAt_eq_blockAt, Proof.Sm4.ofFn_toList, Spec.Sm4.decryptBlock,
    Proof.Sm4.crypt_eq]

theorem dirCipher_bytes (dir : Dir) (k : Spec.Sm4.Schedule) (m : Mem) (p : Addr) :
    Proof.Sm4.PPC64LE.dirCipher dir k (bytesAt m p 16) =
      (Proof.Sm4.outBlock (Proof.Sm4.quads .enc (fun i => k.getD (rkIdx dir i) 0) 8
        (Proof.Sm4.ofBlock (Spec.Sm4.blockAt m p)))).toList := by
  cases dir
  · exact Proof.Sm4.cipher_bytes k m p
  · exact invCipher_bytes k m p

theorem crypt_wp (dir : Dir) {s : State} {B : Addr} {ws : List Region} {k : Spec.Sm4.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (core dir).total) (hk : Ready s B ws k) :
    WP isa (core dir).crypt s fun t => t.gpr sb = B ∧ (∀ r ∈ kept, t.gpr r = s.gpr r) ∧ Ready t B ws k ∧
      Frame [coreRegion (core dir) B] s.mem t.mem ∧
      (∀ j < (core dir).G, bytesAt t.mem (blkAddr (core dir) B j) (4 * (core dir).bw) =
        Proof.Sm4.PPC64LE.dirCipher dir k (bytesAt s.mem (blkAddr (core dir) B j) (4 * (core dir).bw))) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have hfB : B.toNat + 8 * (slots + 6) ≤ 2 ^ 64 := hs.fit
  have hwr : (⟨B, 8 * (slots + 6)⟩ : Region) ∈ s.wr := hs.wr
  have hk' := hk
  obtain ⟨p, hp, hsched, hin, hfit, _⟩ := hk'
  change WP isa (.block (loadTables ++ loadBlock ++ rounds dir ++ storeBlock)) s _
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨a, ae, ac, _, ag, am, ard, awr, _, _⟩ := loadTables_run s
  refine WP.of_runBlock ⟨a, ae, ?_⟩
  obtain ab : a.gpr sb = B := (ag _ (by decide) (by decide) (by decide)).trans hB
  obtain ar : ∀ i < 4, InRegions (a.rd ++ a.wr) (a.gpr sb + BitVec.ofNat 64 (woff i)) 4 := fun i hi => by
    rw [ard, awr, ab]
    exact ⟨_, List.mem_append_right _ hwr, VG.Offset.contains_base B
      (by rw [woff, tailSlot_eq, slots_eq]; omega_using [hi]) (by rw [woff, tailSlot_eq]; omega_using [hi])⟩
  obtain ⟨b, be, bw, bg, bv, bm, brd, bwr, _, _⟩ := loads_run a 4 (by decide) ar
  refine WP.of_runBlock ⟨b, be, ?_⟩
  obtain bc : Consts b := ac.of_eq (fun v _ _ => by rw [bv]) (bg _ (by decide) (fun j _ => (wordReg_ne j).2.2.2.1.symm))
  obtain b3 : b.gpr .r3 = p := by
    rw [bg _ (by decide) (fun j _ => (wordReg_ne j).2.2.2.2.1.symm), ag _ (by decide) (by decide) (by decide), hp]
  obtain bmem : b.mem = s.mem := bm.trans am
  obtain br : ∀ i < 32, InRegions (b.rd ++ b.wr) (b.gpr .r3 + BitVec.ofNat 64 (4 * i)) 4 := fun i hi => by
    rw [brd, ard, b3]
    exact ⟨_, List.mem_append_left _ hin, VG.Offset.contains_base p (by omega_using [hi]) (by omega_using [hi])⟩
  obtain ⟨d, de, dw, _, dg, _, dm, drd, dwr, _, _⟩ := rounds_run dir b 32 (by decide) bc br
  refine WP.of_runBlock ⟨d, de, ?_⟩
  obtain dbase : d.gpr sb = B := by
    rw [dg _ (by decide), bg _ (by decide) (fun j _ => (wordReg_ne_sb j).1.symm), ab]
  obtain dmem : d.mem = s.mem := dm.trans bmem
  let A := B + BitVec.ofNat 64 (8 * tailSlot)
  let init := Proof.Sm4.ofBlock (Spec.Sm4.blockAt s.mem A)
  let z := Proof.Sm4.quads .enc (fun i => k.getD (rkIdx dir i) 0) 8 init
  obtain initial : ∀ w < 4, words b w = init w := fun w hw => by
    rw [bw w hw, am, ab, woff, ← VG.Offset.add_add B (8 * tailSlot) (4 * w), readBE_word _ _ w hw]
    rfl
  obtain dwords : ∀ w < 4, words d w = z w := fun w hw => by
    rw [dw w hw, steps_congr (fun i => rkey b (rkIdx dir i)) (fun i => k.getD (rkIdx dir i) 0) 32 (words b) init
      (fun i hi => by rw [rkey, bmem, b3, hsched, schedule_readW _ _ _ (keyIdx_lt dir hi)]) initial w hw]
    change steps (fun i => k.getD (rkIdx dir i) 0) (4 * 8) init w = z w
    rw [steps_quads]
  obtain dr : ∀ i < 4, InRegions d.wr (d.gpr sb + BitVec.ofNat 64 (woff i)) 4 := fun i hi => by
    rw [dwr, bwr, awr, dbase]
    exact ⟨_, hwr, VG.Offset.contains_base B
      (by rw [woff, tailSlot_eq, slots_eq]; omega_using [hi]) (by rw [woff, tailSlot_eq]; omega_using [hi])⟩
  obtain ⟨e, ee, ew, eg, ef, _, erd, ewr, _, _⟩ := stores_run d 4 (by decide) dr
  refine WP.of_runBlock ⟨e, ee, ?_⟩
  obtain keptE : ∀ r ∈ kept, e.gpr r = s.gpr r := fun r hr => by
    obtain h := kept_ne r hr
    rw [eg r h.1, dg r h.2.1, bg r h.1 (fun j _ he => h.2.1 (he ▸ wordReg_mem j)), ag r h.2.2.1 h.2.2.2.1 h.2.2.2.2.1]
  obtain frame : Frame [coreRegion (core dir) B] s.mem e.mem := by
    rw [← dmem]
    refine ef.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨_, List.mem_cons_self, ?_⟩
    rw [dbase]
    exact VG.Offset.sub_base B (by rw [tailSlot_eq]; show 768 + 16 ≤ 8 * slots; rw [slots_eq]; omega_using [])
  obtain output : bytesAt e.mem A 16 = (Proof.Sm4.outBlock z).toList := by
    apply stored_bytes
    intro i hi
    rw [VG.Offset.add_add, ← dbase, show 8 * tailSlot + 4 * i = woff i from rfl, ew i hi, dwords (3 - i) (by omega_using [])]
  refine ⟨(eg _ (by decide)).trans dbase, keptE, keyArgs_frame hk (keptE .r3 (by decide)) ?_ frame
    (fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst r; exact List.mem_cons_self, fun _ h => h⟩),
    frame, fun j hj => ?_, ?_, ?_⟩
  · rw [erd, drd, brd, ard]
  · have hj0 : j = 0 := by have : j < 1 := hj; omega_using [this]
    subst hj0
    obtain ha : blkAddr (core dir) B 0 = A := by
      show B + BitVec.ofNat 64 (8 * tailSlot) + BitVec.ofNat 64 (4 * 4 * 0) = A
      rw [VG.Offset.add_add, Nat.mul_zero, Nat.add_zero]
    show bytesAt e.mem (blkAddr (core dir) B 0) 16 =
      Proof.Sm4.PPC64LE.dirCipher dir k (bytesAt s.mem (blkAddr (core dir) B 0) 16)
    rw [ha, output, dirCipher_bytes]
  · rw [erd, drd, brd, ard]
  · rw [ewr, dwr, bwr, awr]

/-! ## The core -/

theorem prepare_wp (dir : Dir) {s : State} {B : Addr} {rs : List Region} {k : Spec.Sm4.Schedule}
    (_hs : ScrIn s B (core dir).total) (hR : (⟨B, 8 * (core dir).total⟩ : Region) ∈ rs)
    (hk : Proof.Sm4.PPC64LE.KeyArgs s rs k) (hB : s.gpr sb = B) :
    WP isa (core dir).prepare s fun s' => Ready s' B rs k ∧ s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [coreRegion (core dir) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.of_runBlock ⟨s, rfl, ?_, hB, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩
  obtain ⟨p, hp, hk', hin, hfit, hdis⟩ := hk
  refine ⟨p, hp, hk', hin, hfit, fun r hr => ?_⟩
  simp only [List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact (hdis _ hR).sub_right (Region.sub_prefix (by show 8 * slots ≤ 8 * (slots + 6); omega_using []))
  · exact hdis r hr

theorem ready_frame (dir : Dir) {s s' : State} {B : Addr} {ws : List Region} {k : Spec.Sm4.Schedule} {rs : List Region}
    (h : Ready s B ws k) (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd) (hf : Frame rs s.mem s'.mem)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (core dir) B) r ∨ Region.Sub r (blkRegion (core dir) B)) :
    Ready s' B ws k := keyArgs_frame h e hrd hf fun r hr => by
  rcases hd r hr with _ | h'
  · obtain ⟨r', hr', hs'⟩ := hsub r hr
    exact ⟨r', List.mem_cons_of_mem _ hr', hs'⟩
  · have hb : Region.Sub (blkRegion (core dir) B) (coreRegion (core dir) B) :=
      VG.Offset.sub_base B (by show 8 * tailSlot + 4 * 4 * 1 ≤ 8 * slots; rw [tailSlot_eq, slots_eq]; omega_using [])
    exact ⟨_, List.mem_cons_self, fun x hx => hb x (h' x hx)⟩

/-- The single-block core meets what the modes need. -/
def coreSpec (dir : Dir) : CoreSpec (core dir) where
  Key := Spec.Sm4.Schedule
  cipher := Proof.Sm4.PPC64LE.dirCipher dir
  KeyArgs := Proof.Sm4.PPC64LE.KeyArgs
  Ready := Ready
  cipher_len _ _ := by
    show _ = 16; cases dir <;> simp [Proof.Sm4.PPC64LE.dirCipher, Spec.Sm4.cipher, Spec.Sm4.invCipher]
  layout := ⟨Nat.one_pos, .inr rfl, by simp only [core]; decide, by simp only [core]; decide,
    by simp only [core]; decide⟩
  keyArgs_congr h e hrd hwr _ hf := Proof.Sm4.PPC64LE.keyArgs_congr h e.r3 hrd hwr hf
  ready_frame h e hrd _ _ hf hsub hd := ready_frame dir h e.r3 hrd hf hsub hd
  prepare_wp hB hs hR hk := prepare_wp dir hs hR hk hB
  crypt_wp hB hs hR := crypt_wp dir hB hs hR

end VG.Proof.Sm4.PPC64LE.Serial
