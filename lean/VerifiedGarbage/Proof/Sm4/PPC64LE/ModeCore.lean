module

public import VerifiedGarbage.Proof.Modes.PPC64LE.Core
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Modes
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Ecb
import VerifiedGarbage.Proof.Sm4.PPC64LE.PreparedVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.PreparedBody
import VerifiedGarbage.Proof.Sm4.PPC64LE.Core
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Sm4.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.Proof.Sm4.Prepared

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
open VG.Proof.Sm4 (specDirA)
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
    dirCipher d k (bytesAt m p 16) = (Proof.Sm4.blockFn k (specDirA d) (Spec.Sm4.blockAt m p)).toList := by
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
    r.1 + i + 1 ≤ 8 * slots ∧ (r.1 + i + 1 ≤ 8 * tailSlot ∨ 8 * tailSlot + 16 ≤ r.1 + i) := by
  rw [layout_table] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [slots_eq, tailSlot_eq]
  rcases hr with rfl | rfl <;> dsimp only at hi ⊢ <;> omega

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
    show Region.Disjoint ⟨B + BitVec.ofNat 64 (r.1 + i), 1⟩ ⟨B + BitVec.ofNat 64 (8 * tailSlot), 4 * 4 * 1⟩
    exact VG.Offset.disjoint B (by rw [tailSlot_eq] at h2 ⊢; omega) (by rw [slots_eq] at h1; omega)
      (by rw [tailSlot_eq]; omega)

/-- The table survives what a batch keeps. -/
theorem holds_of_keeps {m m' : Mem} {B : Addr} {k : Spec.Sm4.Schedule} {sd : Spec.Sm4.Direction}
    (h : Proof.Sm4.Prepared.Holds layout m B k sd)
    (hk : Proof.Sm4.Prepared.Keeps B slots layout.cryptScratch m m') :
    Proof.Sm4.Prepared.Holds layout m' B k sd := fun r hr i hi => by
  have hr' := hr
  rw [layout_table] at hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rw [hk (r.1 + i) (by rw [slots_eq]; rcases hr' with rfl | rfl <;> dsimp only at hi ⊢ <;> omega) (by
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [evenSlot_eq, grpSlot_eq, tableSlot_eq, savedSlot_eq, slots_eq]
    rcases hr' with rfl | rfl <;> dsimp only at hi ⊢ <;> omega)]
  exact h r hr i hi

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Sm4.Schedule} (h : KeyArgs s rs k)
    (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [e, hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hk]
  exact (Proof.Sm4.scheduleAt_congr fun i hi =>
    hf.bytes (R := ⟨p, 128⟩) hdis (by show 128 ≤ 2 ^ 64; omega) hi).symm

/-! ## Around the calls -/

theorem inRegions_right {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- The functions' slots, the core's, as the calls' working space. -/
theorem ws_covers {s : State} {B : Addr} {d : Dir} (hs : ScrIn s B (dirCore d).total) :
    Covers [⟨B, 8 * slots⟩] s.wr := Covers.of_sub fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, hs.wr, 0, by rw [BitVec.add_zero], by
    show 0 + 8 * slots ≤ 8 * (slots + 6)
    omega⟩

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

theorem directionOf_dirBit (d : Dir) : Proof.Sm4.directionOf (BitVec.ofNat 64 (dirBit d)).toNat = specDirA d := by
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
    WP isa (dirCore d).prepare s fun s' => Proof.Sm4.Prepared.Holds layout s'.mem B k (specDirA d) ∧
      s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, rfl, hin, hfit, hdis⟩ := hk
  have hfB : B.toNat + 8 * (dirCore d).total ≤ 2 ^ 64 := hs.fit
  have hsep : Region.Disjoint ⟨p, 128⟩ ⟨B, 8 * slots⟩ :=
    (hdis _ hR).sub_right (Region.sub_prefix (by have := core_total d; omega))
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
    · rw [c5, c6]; have := core_total d; omega
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
    (hs : ScrIn s B (dirCore d).total) (hr : Proof.Sm4.Prepared.Holds layout s.mem B k (specDirA d)) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Proof.Sm4.Prepared.Holds layout s'.mem B k (specDirA d) ∧
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
    · rw [c3, c4]; have := core_total d; omega
    · rw [c4, size_eq]
    · rw [c3, hm₀]; exact ⟨k, specDirA d, hr⟩
  · obtain ⟨hE, hK⟩ := hpost
    have hm : (s'.withRegions [] [⟨B, 8 * slots⟩]).mem = s'.mem := rfl
    rw [hm, hm₀, c3] at hE
    rw [hm, hm₀, c3, c4] at hK
    have hE' := hE k (specDirA d) hr
    have r5' : s'.gpr .r5 = B := by
      rw [hnw .r5 (by decide) fun i hi => (crypt_keeps i hi).1, r5₃]
    have r7' : s'.gpr .r7 = s.gpr .r3 := by
      rw [hnw .r7 (by decide) fun i hi => (crypt_keeps i hi).2, r7₃]
    refine wp_mr fun s₄ u₄ => wp_nil ⟨by rw [u₄.other _ (by decide)]; exact r5',
      kept_of g₃ hpres (by rw [u₄.gpr, r7']) fun r h => u₄.other r h,
      by rw [u₄.mem]; exact holds_of_keeps hr hK, by rw [u₄.mem, ← m₃]; exact hf, fun j hj => ?_,
      by rw [u₄.rd, hrd, rd₃], by rw [u₄.wr, hwr, wr₃]⟩
    obtain rfl : j = 0 := by have : (dirCore d).G = 1 := rfl; omega
    have ha : blkAddr (dirCore d) B 0 = B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * 0) := rfl
    show bytesAt s₄.mem (blkAddr (dirCore d) B 0) 16 = dirCipher d k (bytesAt s.mem (blkAddr (dirCore d) B 0) 16)
    rw [dirCipher_bytes, Proof.Sm4.bytesAt_eq_blockAt, u₄.mem, ha, blockAt_of_ecb hE' (by decide)]

/-- SM4's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Dir) : CoreSpec (dirCore d) where
  Key := Spec.Sm4.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready s B _ k := Proof.Sm4.Prepared.Holds layout s.mem B k (specDirA d)
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
