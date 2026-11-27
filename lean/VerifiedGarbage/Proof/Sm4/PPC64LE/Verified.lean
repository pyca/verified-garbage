module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.Ecb
public import VerifiedGarbage.Proof.Sm4.PPC64LE.PreparedVerified
public import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaintMono
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Prepared
public import VerifiedGarbage.Proof.Sm4.Scratch
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
import VerifiedGarbage.Proof.Sm4.Common
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Ecb
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.PreparedVerified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaintMono
meta import VerifiedGarbage.Impl.Sm4.PPC64LE.Prepared
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# SM4 ECB on PPC64LE meets its contracts

`ecb_verified`: `ecb dir` (`Impl/Sm4/PPC64LE/Prepared.lean`) is correct
(`ecb_wp`): `vg_sm4_prepare_keys` (`ecbPrepare_wp`, from its contract
`prepPPC64LE`) builds the table of `dir`, each group of up to sixteen blocks
is copied to the tail buffer, transformed by `vg_sm4_crypt_prepared`
(`ecbCrypt_wp`, from `cryptPPC64LE`) and copied back (`ecbGroup_wp`), and the
caller's `r30`, `r31` and return address come back from their slots, past the
functions' 402. It is constant time by the analysis with public slots
(`slotTaint`), which analyses the two functions' code at the calls: the
pointers, `n` and the stack pointer are public, and so is everything the
code computes from them, which it keeps in registers, the scratch buffer's
address in `r7`, which no call writes. `ecb_framed` runs it with its working
space on the stack, zeroed on return: 3280 bytes, for the 406 words of the
scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.PPC64LE VG.Impl.Sm4.PPC64LE

/-- ECB on PPC64LE with its working space, `ecbSlots` slots, at `r6`. -/
def ecbPPC64LE (dir : Dir) : Contract PPC64LE.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 128⟩
    let data : Region := ⟨s.gpr .r4, 16 * (s.gpr .r5).toNat⟩
    let scratch : Region := ⟨s.gpr .r6, 8 * ecbSlots⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      data.Disjoint scratch ∧
      (s.gpr .r3).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 16 * (s.gpr .r5).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 8 * ecbSlots ≤ 2 ^ 64
  post s s' :=
    Spec.Sm4.blocksAt s'.mem (s.gpr .r4) (s.gpr .r5).toNat =
      Spec.Sm4.ecb (Spec.Sm4.scheduleAt s.mem (s.gpr .r3)) (specDirPPC64LE dir)
        (Spec.Sm4.blocksAt s.mem (s.gpr .r4) (s.gpr .r5).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4.PPC64LE
open VG.Proof.Sm4 (specDirPPC64LE ecbPPC64LE DInv blocksAt_of_dinv ecb_eq blockFn not_contains_off)
open VG.Proof.Sm4.Prepared (Holds)
open VG.Impl.Aes.PPC64LE (sb movR)
open VG.PPC64LE.StraightK (wordAddr slot_sep)

theorem ecbSlots_eq : ecbSlots = 406 := rfl

/-! ## The calls -/

/-- `vg_sm4_prepare_keys(r3, d, r7, slots)` from `ecbPrepare`: the table of
`d` in the scratch buffer at `r7`, `n` (from `r30`) back in `r5`. -/
theorem ecbPrepare_wp (d : Dir) {s : State} {b K : Addr} (h7 : s.gpr .r7 = b) (h3 : s.gpr .r3 = K)
    (hK : (⟨K, 128⟩ : Region) ∈ s.rd) (hS : Covers [⟨b, 8 * slots⟩] s.wr)
    (fK : K.toNat + 128 ≤ 2 ^ 64) (fb : b.toNat + 8 * slots ≤ 2 ^ 64)
    (dKS : Region.Disjoint ⟨K, 128⟩ ⟨b, 8 * slots⟩) :
    WP isa (ecbPrepare d) s fun s' =>
      Holds layout s'.mem b (Spec.Sm4.scheduleAt s.mem K) (specDirPPC64LE d) ∧
      s'.gpr .r5 = s.gpr .r30 ∧ s'.gpr .r7 = b ∧ s'.gpr sb = b ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      Frame [⟨b, 8 * slots⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_li (by cases d <;> decide) fun s₁ u₁ => wp_mr fun s₂ u₂ =>
    wp_li slots_lt fun s₃ u₃ => wp_nil ?_)
  obtain g₃ : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s₃.gpr r = s.gpr r := fun r h4 h5 h6 => by
    rw [u₃.other r h6, u₂.other r h5, u₁.other r h4]
  obtain r3₃ : s₃.gpr .r3 = K := by rw [g₃ _ (by decide) (by decide) (by decide), h3]
  obtain r4₃ : s₃.gpr .r4 = BitVec.ofNat 64 (dirBit d) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  obtain r5₃ : s₃.gpr .r5 = b := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h7]
  obtain r6₃ : s₃.gpr .r6 = BitVec.ofNat 64 slots := u₃.gpr
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain c3 : (s₃.callEntry.withRegions [⟨K, 128⟩] [⟨b, 8 * slots⟩]).gpr .r3 = K := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r3₃]
  obtain c4 : (s₃.callEntry.withRegions [⟨K, 128⟩] [⟨b, 8 * slots⟩]).gpr .r4 = BitVec.ofNat 64 (dirBit d) := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r4₃]
  obtain c5 : (s₃.callEntry.withRegions [⟨K, 128⟩] [⟨b, 8 * slots⟩]).gpr .r5 = b := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r5₃]
  obtain c6 : ((s₃.callEntry.withRegions [⟨K, 128⟩] [⟨b, 8 * slots⟩]).gpr .r6).toNat = slots := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r6₃, toNat_slots]
  obtain hm₀ : (s₃.callEntry.withRegions [⟨K, 128⟩] [⟨b, 8 * slots⟩]).mem = s.mem := by
    rw [State.withRegions_mem, State.callEntry_mem, m₃]
  obtain cov : Covers [⟨b, 8 * slots⟩] s₃.wr := by rw [wr₃]; exact hS
  refine WP.seq (WP.call (k := prepPPC64LE) prep_correct (rd := [⟨K, 128⟩]) (wr := [⟨b, 8 * slots⟩]) ?_
    (Covers.append_left (Covers.left (Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [rd₃]; exact hK)) (Covers.right cov))
    cov (fun s' hrd hwr _ hf hpres hnw hpost => ?_) (by lit_decide))
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [State.withRegions_rd, c3]
    · rw [State.withRegions_wr, c5, c6, Nat.mul_comm]
    · rw [c3, c5, c6, Nat.mul_comm]; exact dKS
    · rw [c3]; exact fK
    · rw [c5, c6]; omega_using [fb]
    · rw [c4]; cases d <;> decide
    · rw [c6, size_eq]
  · obtain ⟨hH, -⟩ := hpost
    obtain hm : (s'.withRegions [⟨K, 128⟩] [⟨b, 8 * slots⟩]).mem = s'.mem := rfl
    change Holds layout _ _ _ _ at hH
    rw [hm, hm₀, c3, c4, c5, directionOf_dirBit] at hH
    obtain r7' : s'.gpr .r7 = b := by
      rw [hnw .r7 (by decide) fun i hi => (prep_keeps i hi).2, g₃ _ (by decide) (by decide) (by decide), h7]
    obtain p30 : s'.gpr .r30 = s.gpr .r30 := by
      rw [hpres _ (by decide), g₃ _ (by decide) (by decide) (by decide)]
    refine wp_mr fun s₄ u₄ => wp_mr fun s₅ u₅ => wp_nil ⟨?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · rw [u₅.mem, u₄.mem]; exact hH
    · rw [u₅.other _ (by decide), u₄.gpr, p30]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), r7']
    · rw [u₅.gpr, u₄.other _ (by decide), r7']
    · obtain hne : r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ sb :=
        (by decide : ∀ r ∈ preserved, r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ sb) r hr
      rw [u₅.other r hne.2.2.2, u₄.other r hne.2.1, hpres r hr, g₃ r hne.1 hne.2.1 hne.2.2.1]
    · rw [u₅.mem, u₄.mem, ← m₃]; exact hf
    · rw [u₅.rd, u₄.rd, hrd, rd₃]
    · rw [u₅.wr, u₄.wr, hwr, wr₃]

/-- `vg_sm4_crypt_prepared(r7, slots)` from `ecbCrypt`: the sixteen blocks of
the tail buffer transformed, the table kept. -/
theorem ecbCrypt_wp {s : State} {b : Addr} {K : Spec.Sm4.Schedule} {sd : Spec.Sm4.Direction}
    (h7 : s.gpr .r7 = b) (hS : Covers [⟨b, 8 * slots⟩] s.wr) (fb : b.toNat + 8 * slots ≤ 2 ^ 64)
    (hH : Holds layout s.mem b K sd) :
    WP isa ecbCrypt s fun s' => s'.gpr .r5 = s.gpr .r5 ∧ s'.gpr .r7 = b ∧ s'.gpr sb = b ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ Holds layout s'.mem b K sd ∧
      Frame [⟨b, 8 * slots⟩] s.mem s'.mem ∧
      (∀ j < 16, Spec.Sm4.blockAt s'.mem (b + BitVec.ofNat 64 (8 * tailSlot + 16 * j)) =
        blockFn K sd (Spec.Sm4.blockAt s.mem (b + BitVec.ofNat 64 (8 * tailSlot + 16 * j)))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_mr fun s₁ u₁ => wp_li slots_lt fun s₂ u₂ => wp_nil ?_)
  obtain g₂ : ∀ r, r ≠ .r3 → r ≠ .r4 → s₂.gpr r = s.gpr r := fun r h3 h4 => by
    rw [u₂.other r h4, u₁.other r h3]
  obtain r3₂ : s₂.gpr .r3 = b := by rw [u₂.other _ (by decide), u₁.gpr, h7]
  obtain r4₂ : s₂.gpr .r4 = BitVec.ofNat 64 slots := u₂.gpr
  obtain m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  obtain rd₂ : s₂.rd = s.rd := by rw [u₂.rd, u₁.rd]
  obtain wr₂ : s₂.wr = s.wr := by rw [u₂.wr, u₁.wr]
  obtain c3 : (s₂.callEntry.withRegions [] [⟨b, 8 * slots⟩]).gpr .r3 = b := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r3₂]
  obtain c4 : ((s₂.callEntry.withRegions [] [⟨b, 8 * slots⟩]).gpr .r4).toNat = slots := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r4₂, toNat_slots]
  obtain hm₀ : (s₂.callEntry.withRegions [] [⟨b, 8 * slots⟩]).mem = s.mem := by
    rw [State.withRegions_mem, State.callEntry_mem, m₂]
  obtain cov : Covers [⟨b, 8 * slots⟩] s₂.wr := by rw [wr₂]; exact hS
  refine WP.seq (WP.call (k := cryptPPC64LE) crypt_correct (rd := []) (wr := [⟨b, 8 * slots⟩]) ?_
    (Covers.append_left Covers.nil (Covers.right cov)) cov (fun s' hrd hwr _ hf hpres hnw hpost => ?_)
    (by lit_decide))
  · refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · rw [State.withRegions_wr, c3, c4, Nat.mul_comm]
    · rw [c3, c4]; omega_using [fb]
    · rw [c4, size_eq]
    · rw [c3, hm₀]; exact ⟨K, sd, hH⟩
  · obtain ⟨hE, hK⟩ := hpost
    obtain hm : (s'.withRegions [] [⟨b, 8 * slots⟩]).mem = s'.mem := rfl
    rw [hm, hm₀, c3] at hE
    rw [hm, hm₀, c3, c4] at hK
    obtain hE' := hE K sd hH
    obtain r5' : s'.gpr .r5 = s.gpr .r5 := by
      rw [hnw .r5 (by decide) fun i hi => (crypt_keeps i hi).1, g₂ _ (by decide) (by decide)]
    obtain r7' : s'.gpr .r7 = b := by
      rw [hnw .r7 (by decide) fun i hi => (crypt_keeps i hi).2, g₂ _ (by decide) (by decide), h7]
    refine wp_mr fun s₃ u₃ => wp_nil ⟨by rw [u₃.other _ (by decide), r5'], by rw [u₃.other _ (by decide), r7'],
      by rw [u₃.gpr, r7'], fun r hr => ?_, by rw [u₃.mem]; exact holds_of_keeps hH hK,
      by rw [u₃.mem, ← m₂]; exact hf, fun j hj => ?_, by rw [u₃.rd, hrd, rd₂], by rw [u₃.wr, hwr, wr₂]⟩
    · obtain hne : r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ sb :=
        (by decide : ∀ r ∈ preserved, r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ sb) r hr
      rw [u₃.other r hne.2.2, hpres r hr, g₂ r hne.1 hne.2.1]
    · obtain ha : b + BitVec.ofNat 64 (8 * tailSlot + 16 * j) =
          b + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j) := by
        rw [VG.Offset.add_add]; rfl
      rw [u₃.mem, ha, blockAt_of_ecb hE' hj]


/-! ## The data loop -/

/-- Block `j` of the data at `D` in `m₀`, transformed. -/
def outE (m₀ : Mem) (D : Addr) (K : Spec.Sm4.Schedule) (sd : Spec.Sm4.Direction) (j : Nat) : Spec.Sm4.Block :=
  blockFn K sd (Spec.Sm4.blockAt m₀ (D + BitVec.ofNat 64 (16 * j)))

/-- The table survives a write to the tail buffer. -/
theorem holds_tail {m m' : Mem} {b : Addr} {K : Spec.Sm4.Schedule} {sd : Spec.Sm4.Direction} {l : Nat}
    (h : Holds layout m b K sd) (hl : l ≤ 256)
    (hf : Frame [⟨b + BitVec.ofNat 64 (8 * tailSlot), l⟩] m m') : Holds layout m' b K sd := fun r hr i hi => by
  obtain ⟨h1, h2⟩ := table_off hr hi
  rw [hf _ fun q hq hc => ?_]
  · exact h r hr i hi
  simp only [List.mem_singleton] at hq; subst hq
  rw [slots_eq] at h1
  rw [tailSlot_eq] at h2
  exact VG.Offset.disjoint b (d := r.1 + i) (n := 1) (e := 8 * tailSlot) (k := l)
    (by rw [tailSlot_eq]; omega_using [h2, hl]) (by omega_using [h1]) (by rw [tailSlot_eq]; omega_using [hl])
    _ (Region.contains_self _ _) hc

/-- The table survives a write apart from the functions' slots. -/
theorem holds_out {m m' : Mem} {b : Addr} {K : Spec.Sm4.Schedule} {sd : Spec.Sm4.Direction} {R : Region}
    (h : Holds layout m b K sd) (hR : Region.Disjoint ⟨b, 8 * slots⟩ R) (hf : Frame [R] m m') :
    Holds layout m' b K sd := fun r hr i hi => by
  obtain ⟨h1, -⟩ := table_off hr hi
  rw [hf _ fun q hq hc => ?_]
  · exact h r hr i hi
  simp only [List.mem_singleton] at hq; subst hq
  exact (hR.sub_left (VG.Offset.sub_base b (d := r.1 + i) (n := 1) h1)) _ (Region.contains_self _ _) hc

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure EPre (S : State) (b D : Addr) (n : Nat) : Prop where
  scr : (⟨b, 8 * ecbSlots⟩ : Region) ∈ S.wr
  dat : (⟨D, 16 * n⟩ : Region) ∈ S.wr
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 8 * ecbSlots⟩
  fit : b.toNat + 8 * ecbSlots ≤ 2 ^ 64
  fitD : D.toNat + 16 * n ≤ 2 ^ 64

/-- The data loop, before group `k`, from the state `S` the loop starts in
and the data's memory `m₀`. -/
structure EInv (m₀ : Mem) (S : State) (b D : Addr) (n : Nat) (K : Spec.Sm4.Schedule) (sd : Spec.Sm4.Direction)
    (k : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  r7 : s.gpr .r7 = b
  r31 : s.gpr .r31 = D + BitVec.ofNat 64 (256 * k)
  r5 : s.gpr .r5 = BitVec.ofNat 64 (n - 16 * k)
  lt : 16 * k < n
  ready : Holds layout s.mem b K sd
  data : DInv m₀ s.mem D n (16 * k) (outE m₀ D K sd)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] S.mem s.mem
  pres : ∀ r ∈ preserved, r ≠ .r31 → s.gpr r = S.gpr r
  rd : s.rd = S.rd
  wr : s.wr = S.wr

/-- The data loop, done. -/
structure EDone (m₀ : Mem) (S : State) (b D : Addr) (n : Nat) (K : Spec.Sm4.Schedule) (sd : Spec.Sm4.Direction)
    (s : State) : Prop where
  r7 : s.gpr .r7 = b
  data : DInv m₀ s.mem D n n (outE m₀ D K sd)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] S.mem s.mem
  pres : ∀ r ∈ preserved, r ≠ .r31 → s.gpr r = S.gpr r
  rd : s.rd = S.rd
  wr : s.wr = S.wr

theorem ecbGroup_wp {m₀ : Mem} {S : State} {b D : Addr} {n : Nat} {K : Spec.Sm4.Schedule}
    {sd : Spec.Sm4.Direction} (hp : EPre S b D n) {k : Nat} {s : State} (hi : EInv m₀ S b D n K sd k s) :
    WP isa ecbGroup s fun s' => (s'.gpr .r5 = 0 ∧ EDone m₀ S b D n K sd s') ∨
      (s'.gpr .r5 ≠ 0 ∧ EInv m₀ S b D n K sd (k + 1) s') := by
  obtain hfit := hp.fit
  obtain hfitD := hp.fitD
  obtain hk := hi.lt
  rw [ecbSlots_eq] at hfit
  let v := n - 16 * k
  let c := min v 16
  obtain hv : v < 2 ^ 64 := by omega_arith
  obtain hc0 : 0 < c := by omega_arith
  obtain hc16 : c ≤ 16 := by omega_arith
  obtain hkc : 256 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 64 (256 * k)
  let T := b + BitVec.ofNat 64 (8 * tailSlot)
  obtain hwS : (⟨b, 8 * ecbSlots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr
  obtain hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain fb : b.toNat + 8 * slots ≤ 2 ^ 64 := by rw [slots_eq]; omega_arith
  obtain inT : ∀ t, t < 32 → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwS, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base b (by rw [ecbSlots_eq, tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain inA : ∀ t, t < 2 * c → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega_arith) (by omega_arith)
  obtain sepS : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 8 * slots⟩ :=
    hp.sep.sub_right (Region.sub_prefix (by rw [ecbSlots_eq, slots_eq]; omega_arith))
  obtain sepAT : Region.Disjoint ⟨A, 16 * c⟩ ⟨T, 16 * c⟩ :=
    (sepS.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right
      (VG.Offset.sub_base b (by rw [slots_eq, tailSlot_eq]; omega_arith))
  obtain covS : ∀ {t : State}, t.wr = s.wr → Covers [⟨b, 8 * slots⟩] t.wr := fun ht =>
    Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by rw [ht]; exact hwS, 0, by rw [BitVec.add_zero], by
        show 0 + 8 * slots ≤ 8 * ecbSlots
        rw [ecbSlots_eq, slots_eq]; omega_arith⟩
  unfold ecbGroup copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.r5 hv) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a⟩ := movR_ok s₁ .r6 .r31
  obtain ⟨s₂b, e₂b, r₂b, o₂b, m₂b, rd₂b, wr₂b⟩ := slotAddr_ok s₂a .r10 tailSlot (by decide)
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₂b .r3 .r12
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂b, rd₂a, rd₁]
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂b, wr₂a, wr₁]
  obtain mem₂ : s₂.mem = s.mem := by rw [m₂, m₂b, m₂a, m₁]
  obtain g₂ : ∀ r, r ≠ .r6 → r ≠ .r10 → r ≠ .r3 → r ≠ .r12 → r ≠ .r9 → s₂.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₂ r h3, o₂b r h2, o₂a r h1, o₁ r h4 h5]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [runBlock_app, runBlock_app, e₂a, Option.bind_some, e₂b, Option.bind_some, e₂], ?_⟩)
  refine WP.mono (copy_wp (X := A) (Y := T) hc0 hc16
    (by rw [o₂ _ (by decide), o₂b _ (by decide), r₂a, o₁ _ (by decide) (by decide), hi.r31])
    (by rw [o₂ _ (by decide), r₂b, o₂a _ (by decide), o₁ _ (by decide) (by decide), hi.base])
    (by rw [r₂, o₂b _ (by decide), o₂a _ (by decide), c₁])
    (fun t ht => by rw [rd₂', wr₂']; exact inRd (inA t ht))
    (fun t ht => by rw [wr₂']; exact inT t (by omega_arith)) sepAT) fun s₃ ⟨cp₃, f₃, g₃, rd₃, wr₃⟩ => ?_
  obtain f₃' : Frame [⟨T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact f₃
  obtain wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂']
  obtain rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂']
  obtain g₃' : ∀ r, r ≠ .r6 → r ≠ .r10 → r ≠ .r3 → r ≠ .r12 → r ≠ .r9 → s₃.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [g₃ r h1 h2 h3 h5, g₂ r h1 h2 h3 h4 h5]
  obtain r7₃ : s₃.gpr .r7 = b := by
    rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.r7]
  obtain H₃ : Holds layout s₃.mem b K sd := holds_tail hi.ready (by omega_arith) f₃'
  -- The sixteen blocks.
  refine WP.seq (WP.mono (ecbCrypt_wp r7₃ (covS wr₃') fb H₃)
    fun s₅ ⟨r5₅, r7₅, base₅, p₅, H₅, f₅, blk₅, rd₅, wr₅⟩ => ?_)
  obtain r31₅ : s₅.gpr .r31 = A := by
    rw [p₅ _ (by decide), g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.r31]
  obtain r5₅' : s₅.gpr .r5 = BitVec.ofNat 64 v := by
    rw [r5₅, g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.r5]
  obtain wr₅' : s₅.wr = s.wr := by rw [wr₅, wr₃']
  obtain rd₅' : s₅.rd = s.rd := by rw [rd₅, rd₃']
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp r5₅' hv) fun s₇ ⟨c₇, o₇, m₇, rd₇, wr₇⟩ => ?_))
  obtain ⟨s₈a, e₈a, r₈a, o₈a, m₈a, rd₈a, wr₈a⟩ := slotAddr_ok s₇ .r6 tailSlot (by decide)
  obtain ⟨s₈b, e₈b, r₈b, o₈b, m₈b, rd₈b, wr₈b⟩ := movR_ok s₈a .r10 .r31
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := movR_ok s₈b .r3 .r12
  refine WP.seq (WP.of_runBlock ⟨s₈, by
    rw [runBlock_app, e₈a, Option.bind_some,
      show ([movR .r10 .r31, movR .r3 .r12] : List Instr) = [movR .r10 .r31] ++ [movR .r3 .r12] from rfl,
      runBlock_app, e₈b, Option.bind_some, e₈], ?_⟩)
  obtain mem₈ : s₈.mem = s₅.mem := by rw [m₈, m₈b, m₈a, m₇]
  obtain wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₈b, wr₈a, wr₇, wr₅']
  obtain rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₈b, rd₈a, rd₇, rd₅']
  obtain g₈ : ∀ r, r ≠ .r6 → r ≠ .r10 → r ≠ .r3 → r ≠ .r12 → r ≠ .r9 → s₈.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₈ r h3, o₈b r h2, o₈a r h1, o₇ r h4 h5]
  refine WP.mono (copy_wp (X := T) (Y := A) hc0 hc16
    (by rw [o₈ _ (by decide), o₈b _ (by decide), r₈a, o₇ _ (by decide) (by decide), base₅])
    (by rw [o₈ _ (by decide), r₈b, o₈a _ (by decide), o₇ _ (by decide) (by decide), r31₅])
    (by rw [r₈, o₈b _ (by decide), o₈a _ (by decide), c₇])
    (fun t ht => by rw [rd₈', wr₈']; exact inRd (inT t (by omega_arith)))
    (fun t ht => by rw [wr₈']; exact inA t ht) sepAT.symm) fun s₉ ⟨cp₉, f₉, g₉, rd₉, wr₉⟩ => ?_
  obtain g₉' : ∀ r, r ≠ .r6 → r ≠ .r10 → r ≠ .r3 → r ≠ .r12 → r ≠ .r9 → s₉.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [g₉ r h1 h2 h3 h5, g₈ r h1 h2 h3 h4 h5]
  obtain r12₉ : s₉.gpr .r12 = BitVec.ofNat 64 c := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide), o₈ _ (by decide), o₈b _ (by decide),
      o₈a _ (by decide), c₇]
  obtain base₉ : s₉.gpr sb = b := by rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), base₅]
  obtain r7₉ : s₉.gpr .r7 = b := by rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), r7₅]
  obtain r31₉ : s₉.gpr .r31 = A := by rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), r31₅]
  obtain r5₉ : s₉.gpr .r5 = BitVec.ofNat 64 v := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), r5₅']
  obtain wr₉' : s₉.wr = S.wr := by rw [wr₉, wr₈', hi.wr]
  obtain rd₉' : s₉.rd = S.rd := by rw [rd₉, rd₈', hi.rd]
  obtain H₉ : Holds layout s₉.mem b K sd :=
    holds_out (mem₈ ▸ H₅) ((sepS.sub_left (VG.Offset.sub_base D (by omega_arith))).symm) f₉
  obtain fr₉ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s.mem s₉.mem := by
    refine ((f₃'.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((f₅.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((mem₈ ▸ f₉).sub fun r hr => ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩)))
    · simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base b (by rw [slots_eq, tailSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub_base D (by omega_arith)
  -- The blocks the batch read are the group's, as on entry.
  obtain hblk : ∀ j < c, Spec.Sm4.blockAt s₃.mem (b + BitVec.ofNat 64 (8 * tailSlot + 16 * j)) =
      Spec.Sm4.blockAt m₀ (D + BitVec.ofNat 64 (16 * (16 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn]
    rw [addr_add]
    obtain ht : 16 * j + u < 16 * c := by omega_arith
    have := cp₃ (16 * j + u) ht
    rw [addr_add] at this
    rw [show 8 * tailSlot + 16 * j + u = 8 * tailSlot + (16 * j + u) by omega_arith, this, mem₂, addr_add,
      hi.data _ (by omega_arith), ite_eq_right (by omega_arith), addr_add,
      show 256 * k + (16 * j + u) = 16 * (16 * k + j) + u by omega_arith]
  obtain hdata : DInv m₀ s₉.mem D n (16 * k + c) (outE m₀ D K sd) := by
    intro i hin
    by_cases hin1 : 256 * k ≤ i ∧ i < 256 * k + 16 * c
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 256 * k) := by
        rw [addr_add, show 256 * k + (i - 256 * k) = i by omega_arith]
      rw [e1, cp₉ _ (by omega_arith), mem₈, ite_eq_left (show i < 16 * (16 * k + c) by omega_arith),
        show i / 16 = 16 * k + (i - 256 * k) / 16 by omega_arith, show i % 16 = (i - 256 * k) % 16 by omega_arith]
      obtain hj : (i - 256 * k) / 16 < c := by omega_arith
      obtain eT : T + BitVec.ofNat 64 (i - 256 * k) = b + BitVec.ofNat 64 (8 * tailSlot + 16 * ((i - 256 * k) / 16)) +
          BitVec.ofNat 64 ((i - 256 * k) % 16) := by
        rw [addr_add, addr_add, show 8 * tailSlot + 16 * ((i - 256 * k) / 16) + (i - 256 * k) % 16 =
          8 * tailSlot + (i - 256 * k) by omega_arith]
      rw [eT, ← VG.Proof.Sm4.blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide)), blk₅ _ (by omega_arith), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨A, 16 * c⟩ : Region)], ¬ r.Contains (D + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off D (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      rw [f₉ _ hout, mem₈,
        f₅.bytes (R := ⟨D, 16 * n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sepS)
          (by simp only; omega_arith) hin,
        f₃'.bytes (R := ⟨D, 16 * n⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sepS.sub_right (VG.Offset.sub_base b (by rw [slots_eq, tailSlot_eq]; omega_arith)))
          (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 256 * k
      · rw [ite_eq_left (show i < 16 * (16 * k) by omega_arith), ite_eq_left (show i < 16 * (16 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (16 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (16 * k + c) by omega_arith)]
  obtain fr : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] S.mem s₉.mem := hi.frame.trans fr₉
  obtain pres₉ : ∀ r ∈ preserved, r ≠ .r31 → s₉.gpr r = S.gpr r := fun r hr h31 => by
    obtain hne : r ≠ .r6 ∧ r ≠ .r10 ∧ r ≠ .r3 ∧ r ≠ .r12 ∧ r ≠ .r9 :=
      (by decide : ∀ r ∈ preserved, r ≠ .r6 ∧ r ≠ .r10 ∧ r ≠ .r3 ∧ r ≠ .r12 ∧ r ≠ .r9) r hr
    rw [g₉' r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2, p₅ r hr,
      g₃' r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2, hi.pres r hr h31]
  -- On to the next group.
  obtain ⟨s₁₀, e₁₀, r₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := subR_ok s₉ .r5 .r5 .r12
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := addI_ok s₁₀ .r31 .r31 (imm := 256) (by decide)
  refine WP.of_runBlock ⟨s₁₁, by
    rw [show ([Instr.sub .r5 .r5 .r12, .addi .r31 .r31 256] : List Instr) =
      [.sub .r5 .r5 .r12] ++ [.addi .r31 .r31 256] from rfl, runBlock_app, e₁₀,
      Option.bind_some, e₁₁], ?_⟩
  obtain hm : s₁₁.mem = s₉.mem := by rw [m₁₁, m₁₀]
  obtain r5₁₁ : s₁₁.gpr .r5 = BitVec.ofNat 64 (v - c) := by
    rw [o₁₁ _ (by decide), r₁₀, r5₉, r12₉, VG.Offset.ofNat_sub_ofNat (by omega_arith)]
  obtain base₁₁ : s₁₁.gpr sb = b := by rw [o₁₁ _ (by decide), o₁₀ _ (by decide), base₉]
  obtain r7₁₁ : s₁₁.gpr .r7 = b := by rw [o₁₁ _ (by decide), o₁₀ _ (by decide), r7₉]
  obtain rd₁₁' : s₁₁.rd = S.rd := by rw [rd₁₁, rd₁₀, rd₉']
  obtain wr₁₁' : s₁₁.wr = S.wr := by rw [wr₁₁, wr₁₀, wr₉']
  obtain pres₁₁ : ∀ r ∈ preserved, r ≠ .r31 → s₁₁.gpr r = S.gpr r := fun r hr h31 => by
    rw [o₁₁ r h31, o₁₀ r ((by decide : ∀ r ∈ preserved, r ≠ .r5) r hr), pres₉ r hr h31]
  by_cases hlt : v ≤ 16
  · have hn : 16 * k + c = n := by omega_arith
    refine .inl ⟨by rw [r5₁₁, show v - c = 0 by omega_arith]; rfl, r7₁₁,
      fun i hi' => by rw [hm, hdata i hi', hn], hm ▸ fr, pres₁₁, rd₁₁', wr₁₁'⟩
  · have hc : c = 16 := by omega_arith
    refine .inr ⟨fun h => ?_, base₁₁, r7₁₁, ?_, ?_, by omega_arith, hm ▸ H₉, ?_, hm ▸ fr, pres₁₁, rd₁₁', wr₁₁'⟩
    · have hne : v - c ≠ 0 := by omega_arith
      rw [r5₁₁] at h
      apply hne
      have := congrArg BitVec.toNat h
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
    · rw [r₁₁, o₁₀ _ (by decide), r31₉, addr_add, show 256 * k + 256 = 256 * (k + 1) by omega_arith]
    · rw [r5₁₁, show v - c = n - 16 * (k + 1) by omega_arith]
    · rw [hm, show 16 * (k + 1) = 16 * k + c by omega_arith]; exact hdata

theorem ecbLoop_wp {m₀ : Mem} {S : State} {b D : Addr} {n : Nat} {K : Spec.Sm4.Schedule}
    {sd : Spec.Sm4.Direction} (hp : EPre S b D n) {s : State} (hi : EInv m₀ S b D n K sd 0 s) :
    WP isa (.loop ecbGroup (.nonzero .d .r5)) s (EDone m₀ S b D n K sd) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 16 * k ∧ EInv m₀ S b D n K sd k s) (fun m s hs => ?_) n s
    ⟨0, by omega_using [], hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (ecbGroup_wp hp hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨(eval_nonzero s' .r5).trans (by rw [z]; rfl), d⟩
  · exact .inr ⟨(eval_nonzero s' .r5).trans (by rw [beq_false_of_ne z]; rfl), n - 16 * (k + 1),
      by have := d.lt; have := hk.lt; omega_arith, k + 1, rfl, d⟩

/-! ## The whole function -/

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : (ecbPPC64LE dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧
      (ecbPPC64LE dir).post s₀ s' := by
  obtain ⟨hrd, hwr, -, dKS, dDS, fitK, fitD, fitB⟩ := hp
  let b := s₀.gpr .r6
  let D := s₀.gpr .r4
  let n := (s₀.gpr .r5).toNat
  let K := s₀.gpr .r3
  obtain hwS : (⟨b, 8 * ecbSlots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  obtain hwD : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  obtain hrK : (⟨K, 128⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [K]
  obtain fitB' : b.toNat + 8 * 406 ≤ 2 ^ 64 := by rw [← ecbSlots_eq]; exact fitB
  obtain fb : b.toNat + 8 * slots ≤ 2 ^ 64 := by rw [slots_eq]; omega_arith
  obtain inS : ∀ j, slots ≤ j → j < ecbSlots → InRegions s₀.wr (wordAddr b j) 8 := fun j _ hj =>
    ⟨_, hwS, VG.Offset.contains_base b (by rw [ecbSlots_eq] at hj ⊢; omega_arith) (by rw [ecbSlots_eq] at hj; omega_arith)⟩
  -- The saved words' region: apart from the functions' slots, the schedule and the data.
  let SV : Region := ⟨wordAddr b ecbR30, 24⟩
  obtain svS : Region.Sub SV ⟨b, 8 * ecbSlots⟩ := VG.Offset.sub_base b (by rw [ecbSlots_eq]; decide)
  obtain svK : Region.Disjoint ⟨K, 128⟩ SV := dKS.sub_right svS
  obtain svD : Region.Disjoint ⟨D, 16 * n⟩ SV := dDS.sub_right svS
  obtain svF : Region.Disjoint ⟨b, 8 * slots⟩ SV := (VG.Offset.disjoint_base b (by rw [slots_eq]; decide)
    (by decide)).symm
  obtain wSV : ∀ j, ecbR30 ≤ j → j < ecbR30 + 3 → SV.Contains (wordAddr b j) (64 / 8) := fun j h1 h2 => by
    show (⟨b + BitVec.ofNat 64 (8 * ecbR30), 24⟩ : Region).Contains (b + BitVec.ofNat 64 (8 * j)) 8
    rw [show b + BitVec.ofNat 64 (8 * j) = b + BitVec.ofNat 64 (8 * ecbR30) + BitVec.ofNat 64 (8 * (j - ecbR30)) by
      rw [addr_add, show 8 * ecbR30 + 8 * (j - ecbR30) = 8 * j by omega_arith]]
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
  -- The entry.
  unfold ecb ecbEntry
  obtain u₁ := Upd.write s₀ .r0 s₀.lr
  refine WP.seq (WP.cons exec_mflr (wp_std (a := wordAddr b ecbLr) (by decide) (by decide)
    (by rw [u₁.other _ (by decide)]) (by rw [u₁.wr]; exact inS _ (by decide) (by decide)) fun s₂ u₂ =>
    wp_std (a := wordAddr b ecbR30) (by decide) (by decide) (by rw [u₂.gpr, u₁.other _ (by decide)])
      (by rw [u₂.wr, u₁.wr]; exact inS _ (by decide) (by decide)) fun s₃ u₃ =>
    wp_std (a := wordAddr b ecbR31) (by decide) (by decide) (by rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide)])
      (by rw [u₃.wr, u₂.wr, u₁.wr]; exact inS _ (by decide) (by decide)) fun s₄ u₄ =>
    wp_mr fun s₅ u₅ => wp_mr fun s₆ u₆ => wp_mr fun s₇ u₇ => wp_nil ?_))
  obtain g₄ : ∀ r, r ≠ .r0 → s₄.gpr r = s₀.gpr r := fun r h => by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other r h]
  obtain g₇ : ∀ r, r ≠ .r0 → r ≠ .r7 → r ≠ .r31 → r ≠ .r30 → s₇.gpr r = s₀.gpr r := fun r h0 h7 h31 h30 => by
    rw [u₇.other r h30, u₆.other r h31, u₅.other r h7, g₄ r h0]
  obtain r7₇ : s₇.gpr .r7 = b := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄ _ (by decide)]
  obtain r31₇ : s₇.gpr .r31 = D := by rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄ _ (by decide)]
  obtain r30₇ : s₇.gpr .r30 = s₀.gpr .r5 := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g₄ _ (by decide)]
  obtain r3₇ : s₇.gpr .r3 = K := g₇ _ (by decide) (by decide) (by decide) (by decide)
  obtain rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain mem₇ : s₇.mem = ((s₀.mem.writeW (wordAddr b ecbLr) s₀.lr).writeW (wordAddr b ecbR30) (s₀.gpr .r30)).writeW
      (wordAddr b ecbR31) (s₀.gpr .r31) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₂.gpr, u₁.other _ (by decide), u₃.mem, u₂.gpr,
      u₁.other _ (by decide), u₂.mem, u₁.gpr, u₁.mem]
  obtain fr₇ : Frame [SV] s₀.mem s₇.mem := by
    rw [mem₇]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (wSV _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (wSV _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (wSV _ (by decide) (by decide))
  obtain sep12 : Mem.Sep (wordAddr b ecbR30) (64 / 8) (wordAddr b ecbR31) (64 / 8) :=
    slot_sep b (by decide) (by decide) (by decide)
  obtain sep02 : Mem.Sep (wordAddr b ecbLr) (64 / 8) (wordAddr b ecbR30) (64 / 8) :=
    slot_sep b (by decide) (by decide) (by decide)
  obtain sep01 : Mem.Sep (wordAddr b ecbLr) (64 / 8) (wordAddr b ecbR31) (64 / 8) :=
    slot_sep b (by decide) (by decide) (by decide)
  obtain sv30 : s₇.mem.readW (wordAddr b ecbR30) 64 = s₀.gpr .r30 := by
    rw [mem₇, Mem.readW_writeW_sep sep12 (by decide), Mem.readW_writeW_self64]
  obtain sv31 : s₇.mem.readW (wordAddr b ecbR31) 64 = s₀.gpr .r31 := by
    rw [mem₇, Mem.readW_writeW_self64]
  obtain svLr : s₇.mem.readW (wordAddr b ecbLr) 64 = s₀.lr := by
    rw [mem₇, Mem.readW_writeW_sep sep01 (by decide), Mem.readW_writeW_sep sep02 (by decide),
      Mem.readW_writeW_self64]
  -- The table.
  obtain covS : Covers [⟨b, 8 * slots⟩] s₇.wr := Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by rw [wr₇]; exact hwS, 0, by rw [BitVec.add_zero], by
      show 0 + 8 * slots ≤ 8 * ecbSlots
      rw [ecbSlots_eq, slots_eq]; omega_arith⟩
  obtain dKS' : Region.Disjoint ⟨K, 128⟩ ⟨b, 8 * slots⟩ :=
    dKS.sub_right (Region.sub_prefix (by rw [ecbSlots_eq, slots_eq]; omega_arith))
  refine WP.seq (WP.mono (ecbPrepare_wp dir r7₇ r3₇ (by rw [rd₇]; exact hrK) covS fitK fb dKS')
    fun s₉ ⟨H₉, r5₉, r7₉, base₉, p₉, f₉, rd₉, wr₉⟩ => ?_)
  obtain hK₇ : Spec.Sm4.scheduleAt s₇.mem K = Spec.Sm4.scheduleAt s₀.mem K :=
    Proof.Sm4.scheduleAt_frame fr₇ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact svK
  rw [hK₇] at H₉
  obtain r31₉ : s₉.gpr .r31 = D := by rw [p₉ _ (by decide), r31₇]
  obtain r5₉' : s₉.gpr .r5 = BitVec.ofNat 64 n := by
    rw [r5₉, r30₇]; simp only [n, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain sepS : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 8 * slots⟩ :=
    dDS.sub_right (Region.sub_prefix (by rw [ecbSlots_eq, slots_eq]; omega_arith))
  obtain data₉ : ∀ i < 16 * n, s₉.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi => by
    rw [f₉.bytes (R := ⟨D, 16 * n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sepS)
        (by simp only; omega_arith) hi,
      fr₇.bytes (R := ⟨D, 16 * n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact svD)
        (by simp only; omega_arith) hi]
  obtain hep : EPre s₉ b D n := ⟨by rw [wr₉, wr₇]; exact hwS, by rw [wr₉, wr₇]; exact hwD,
    dDS, fitB, fitD⟩
  -- Any blocks?
  obtain hz : (s₉.gpr .r5 == 0) = decide (n = 0) := by
    rw [r5₉', ofNat_beq_zero (by omega_arith)]
  let sd := specDirPPC64LE dir
  let KK := Spec.Sm4.scheduleAt s₀.mem K
  refine WP.seq (WP.mono (M := isa) (Q := EDone s₀.mem s₉ b D n KK sd)
    (WP.ite (decide (n = 0)) ((eval_zero s₉ .r5).trans (by rw [hz])) (fun h0 => ?_) (fun h0 => ?_))
    fun s₁₀ d₁₀ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact wp_nil ⟨r7₉, fun i hi => by omega_arith, Frame.refl _ _, fun _ _ _ => rfl, rfl, rfl⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine ecbLoop_wp hep ⟨base₉, r7₉, by rw [r31₉]; simp, by rw [r5₉']; simp, by omega_arith, H₉,
      fun i hi => ?_, Frame.refl _ _, fun _ _ _ => rfl, rfl, rfl⟩
    rw [data₉ i hi, ite_eq_right (by omega_arith)]
  -- The exit.
  obtain svOut : ∀ j, ecbR30 ≤ j → j < ecbR30 + 3 →
      s₁₀.mem.readW (wordAddr b j) 64 = s₇.mem.readW (wordAddr b j) 64 := fun j h1 h2 => by
    rw [d₁₀.frame.readW (r := SV) (wSV j h1 h2) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact svF.symm
        · exact svD.symm) (by decide),
      f₉.readW (r := SV) (wSV j h1 h2) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact svF.symm) (by decide)]
  obtain r7₁₀ : s₁₀.gpr .r7 = b := d₁₀.r7
  obtain inR : ∀ j, slots ≤ j → j < ecbSlots → InRegions (s₁₀.rd ++ s₁₀.wr) (wordAddr b j) 8 := fun j h1 h2 => by
    rw [d₁₀.rd, d₁₀.wr, rd₉, wr₉, rd₇, wr₇]; exact inRd (inS j h1 h2)
  unfold ecbExit
  refine wp_ld (a := wordAddr b ecbR30) (by decide) (by decide) (by rw [r7₁₀]) (inR _ (by decide) (by decide))
    fun s₁₁ u₁₁ => wp_ld (a := wordAddr b ecbLr) (by decide) (by decide) (by rw [u₁₁.other _ (by decide), r7₁₀])
      (by rw [u₁₁.rd, u₁₁.wr]; exact inR _ (by decide) (by decide)) fun s₁₂ u₁₂ => WP.cons exec_mtlr ?_
  let t : State := { s₁₂ with lr := s₁₂.gpr .r0 }
  obtain hin : InRegions (t.rd ++ t.wr) (t.gpr .r7 + BitVec.ofNat 64 (8 * ecbR31)) 8 := by
    show InRegions (s₁₂.rd ++ s₁₂.wr) (s₁₂.gpr .r7 + BitVec.ofNat 64 (8 * ecbR31)) 8
    rw [u₁₂.rd, u₁₂.wr, u₁₁.rd, u₁₁.wr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), r7₁₀]
    exact inR _ (by decide) (by decide)
  obtain u₁₃ := Upd.write t .r31 (t.mem.readW (t.gpr .r7 + BitVec.ofNat 64 (8 * ecbR31)) 64)
  refine WP.cons (exec_load_d (show Reg.r7 ≠ .r0 by decide) ⟨by decide, by decide⟩ hin)
    (wp_nil ⟨fun r hr => ?_, ?_, ?_⟩)
  · by_cases e31 : r = .r31
    · subst e31
      rw [u₁₃.gpr]; show s₁₂.mem.readW (s₁₂.gpr .r7 + BitVec.ofNat 64 (8 * ecbR31)) 64 = _
      rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), r7₁₀, u₁₂.mem, u₁₁.mem,
        svOut _ (by decide) (by decide), sv31]
    by_cases e30 : r = .r30
    · subst e30
      rw [u₁₃.other _ (by decide)]; show s₁₂.gpr .r30 = _
      rw [u₁₂.other _ (by decide), u₁₁.gpr, svOut _ (by decide) (by decide), sv30]
    have h0 : r ≠ .r0 := (by decide : ∀ r ∈ preserved, r ≠ .r0) r hr
    have h7 : r ≠ .r7 := (by decide : ∀ r ∈ preserved, r ≠ .r7) r hr
    rw [u₁₃.other r e31]; show s₁₂.gpr r = _
    rw [u₁₂.other r h0, u₁₁.other r e30, d₁₀.pres r hr e31, p₉ r hr, g₇ r h0 h7 e31 e30]
  · show s₁₂.gpr .r0 = s₀.lr
    rw [u₁₂.gpr, u₁₁.mem, svOut _ (by decide) (by decide), svLr]
  · show Spec.Sm4.blocksAt s₁₂.mem D n = _
    rw [show s₁₂.mem = s₁₀.mem by rw [u₁₂.mem, u₁₁.mem], blocksAt_of_dinv d₁₀.data, ecb_eq]
    simp only [Spec.Sm4.blocksAt, List.map_map]
    rfl

/-- The taint on entry: the arguments public, the data and the scratch
buffer the writable regions at `r4` and `r6`, the scratch buffer's whole
length known. -/
def ecbTaint : SlotTaint.T := SlotTaint.mk' [.r3, .r4, .r5, .r6] [0, 8 * ecbSlots] [(.r4, 0), (.r6, 1)]

theorem ecbTaint_agree (dir : Dir) (s₁ s₂ : State) (h₁ : (ecbPPC64LE dir).pre s₁) (h₂ : (ecbPPC64LE dir).pre s₂)
    (hp : (ecbPPC64LE dir).pub s₁ s₂) : SlotTaint.Agree ecbTaint s₁ s₂ := by
  obtain ⟨-, hw₁, -, -, dDS, -, fD, fS⟩ := h₁
  obtain ⟨-, hw₂, -⟩ := h₂
  obtain ⟨r3, r4, r5, r6, hsp⟩ := hp
  refine SlotTaint.agree_mk' hsp (fun r h => ?_) (by rw [hw₁, hw₂, r4, r5, r6]) ?_ ?_ ?_ ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [hw₁]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · rw [hw₁]
    exact .cons (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS)
      (.cons (fun r hr => absurd hr List.not_mem_nil) .nil)
  · rw [hw₁]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> omega_arith
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [SlotTaint.region, hw₁]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [SlotTaint.region, hw₂]

theorem ecb_ct (dir : Dir) : ConstantTime isa (ecbPPC64LE dir).pre (ecbPPC64LE dir).pub (ecb dir) := by
  cases dir
  · exact VG.Taint.constantTime_of_exists (A := slotTaint) ecbTaint (ecbTaint_agree .encrypt) (by taint_decide_sum [])
  · exact VG.Taint.constantTime_of_exists (A := slotTaint) ecbTaint (ecbTaint_agree .decrypt) (by taint_decide_sum [])

theorem ecb_correct (dir : Dir) (s : State) (hs : (ecbPPC64LE dir).pre s) :
    ∃ t s', Exec isa (ecb dir) s t s' ∧ abiPreserved s s' ∧ (ecbPPC64LE dir).post s s' := by
  obtain ⟨t, s', he, hpres, hlr, hpost⟩ := ecb_wp dir hs
  exact ⟨t, s', he, ⟨hpres, Exec.sp he, hlr⟩, hpost⟩

/-- A state satisfying the precondition (one block). -/
def ecbSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r5 => 1 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 8 * 406⟩]

theorem ecb_verified (dir : Dir) :
    Verified target (ecb dir) (Proof.Sm4.ecbScratchContract abi (specDirPPC64LE dir) ecbSlots) :=
  Verified.of_correct (ecb_correct dir) (ecb_ct dir) (by
    cases dir <;>
    sig_implies [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, ecbPPC64LE, specDirPPC64LE,
      abi, argRegs, ecbSlots, slots, savedSlot, tableEnd, tableSlot] [ecbSat] using ecbSat)

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000`, one block at `0x3000`. -/
def ecbFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r5 => 1 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩]

theorem ecbFrameSat_pre (d : Spec.Sm4.Direction) :
    ∃ s, (Spec.Sm4.ecbContract abi d 3280).pre s := by
  implies_sat [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, Spec.Sm4.ecbPost, abi, argRegs]
    [ecbFrameSat] using ecbFrameSat

/-- ECB in the direction `dir`, with its working space on the stack. -/
theorem ecb_framed (dir : Dir) :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3280 .r6 406 (ecb dir))
      (Spec.Sm4.ecbContract abi (specDirPPC64LE dir) 3280) :=
  Verified.stackScratchWiped (sig := Spec.Sm4.ecbSig) (nm := "scratch") (e := .u64)
    (n := 406) (post := Spec.Sm4.ecbPost (specDirPPC64LE dir) abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3280) (words := 406) (ecb_verified dir) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm4.ecbPost_local _ _)
    (Proof.Sm4.ecbPostOut_local _ _) (ecbFrameSat_pre _)

end VG.Proof.Sm4.PPC64LE
