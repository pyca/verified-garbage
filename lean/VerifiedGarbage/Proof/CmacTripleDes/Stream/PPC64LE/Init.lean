module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Calls
public import VerifiedGarbage.Spec.Cmac.TripleDesContract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Verified
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Ecb.Call
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.CbcBlocks
import VerifiedGarbage.Proof.CmacTripleDes.Stream
import VerifiedGarbage.Proof.CmacTripleDes.Cmac
public import VerifiedGarbage.Proof.CmacTripleDes.Block
import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.CmacTripleDes.Bytes

/-!
# Streaming TDEA-CMAC on PPC64LE: `stream_init`

`init_wp`: `streamInit` makes the state represent the empty message under
the key (`Spec.Cmac.tdesRepr`): the key expansion's call writes the
schedule, the block function's call enciphers the zero block, and its
doubling and the doubling of that are the subkeys (`subkeys_tdes`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE
open VG.Proof.Cmac (le8)

/-- `stream_init`'s precondition, with the working space of 640 bytes at `r6`. -/
structure InitPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, (s.gpr .r5).toNat⟩]
  wr : s.wr = [⟨s.gpr .r3, 416⟩, ⟨s.gpr .r6, 640⟩]
  keyState : Region.Disjoint ⟨s.gpr .r4, (s.gpr .r5).toNat⟩ ⟨s.gpr .r3, 416⟩
  keyScr : Region.Disjoint ⟨s.gpr .r4, (s.gpr .r5).toNat⟩ ⟨s.gpr .r6, 640⟩
  stateScr : Region.Disjoint ⟨s.gpr .r3, 416⟩ ⟨s.gpr .r6, 640⟩
  valid : Spec.TripleDes.validKey (s.gpr .r5).toNat
  stateFit : (s.gpr .r3).toNat + 416 ≤ 2 ^ 64
  scrFit : (s.gpr .r6).toNat + 640 ≤ 2 ^ 64

/-- The zero block, as a block. -/
theorem zero_block (m : Mem) (p : Addr) (h : Spec.Aes.bytesAt m p 8 = Spec.Cmac.zeros 8) :
    Spec.TripleDes.blockAt m p = Vector.ofFn fun i => (le8 0).getD i.val 0 := by
  rw [Proof.Cmac.le8_zero, ← h, VG.Proof.TripleDes.ofFn_bytesAt]

/-- `L`, from the block function's output on the zero block. -/
theorem l_eq {m : Mem} {p : Addr} {S : Spec.TripleDes.Schedule}
    (h : Spec.TripleDes.blockAt m p = Spec.TripleDes.encryptBlock S (Vector.ofFn fun i => (le8 0).getD i.val 0)) :
    rev64 (m.readW p 64) = Proof.CmacTripleDes.tdes S 0 := by
  have e : le8 (m.readW p 64) = le8 (byteRev64 (Proof.CmacTripleDes.tdes S (byteRev64 0))) := by
    rw [← Proof.CmacTripleDes.tdesWith_le8, Proof.Cmac.le8_readW, VG.Proof.TripleDes.bytesAt_eq, h]
    rfl
  rw [le8_inj e, ← rev64_eq, rev64_rev64]
  rfl


/-- After `initSave`: the return address and the caller's `r30`, `r31` in
the working space, and the key expansion's arguments. -/
structure Saved (s t : State) : Prop where
  r3 : t.gpr .r3 = s.gpr .r4
  r4 : t.gpr .r4 = s.gpr .r5
  r5 : t.gpr .r5 = s.gpr .r3
  r30 : t.gpr .r30 = s.gpr .r6
  r31 : t.gpr .r31 = s.gpr .r3
  regs : ∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r30 → r ≠ .r31 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : t.mem = ((s.mem.writeW (s.gpr .r6 + BitVec.ofNat 64 lrOff) s.lr).writeW
    (s.gpr .r6 + BitVec.ofNat 64 r30Off) (s.gpr .r30)).writeW (s.gpr .r6 + BitVec.ofNat 64 r31Off) (s.gpr .r31)

theorem initSave_wp {s : State} (hp : InitPre s) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Saved s t → WP isa (.block is) t Q) : WP isa (.block (initSave ++ is)) s Q := by
  have hW : (⟨s.gpr .r6, 640⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  simp only [initSave, mr, List.cons_append, List.nil_append]
  refine wp_mflr fun s₁ u₁ => ?_
  refine wp_std (a := s.gpr .r6 + BitVec.ofNat 64 lrOff) (by decide) (by decide) (by rw [u₁.other _ (by decide)])
    (by rw [u₁.wr]; exact scr_in hW (by decide)) fun s₂ u₂ => ?_
  refine wp_std (a := s.gpr .r6 + BitVec.ofNat 64 r30Off) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr]; exact scr_in hW (by decide)) fun s₃ u₃ => ?_
  refine wp_std (a := s.gpr .r6 + BitVec.ofNat 64 r31Off) (by decide) (by decide)
    (by rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide)]) (by rw [u₃.wr, u₂.wr, u₁.wr]; exact scr_in hW (by decide))
    fun s₄ u₄ => ?_
  refine wp_mr fun s₅ u₅ => wp_mr fun s₆ u₆ => wp_mr fun s₇ u₇ => wp_mr fun s₈ u₈ => wp_mr fun s₉ u₉ => ?_
  have g₄ : ∀ r, r ≠ .r0 → s₄.gpr r = s.gpr r := fun r h => by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other r h]
  refine k s₉ ⟨?_, ?_, ?_, ?_, ?_, fun r h0 h3 h4 h5 h30 h31 => ?_, ?_, ?_, ?_⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      g₄ _ (by decide)]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      g₄ _ (by decide)]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄ _ (by decide)]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      g₄ _ (by decide)]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      g₄ _ (by decide)]
  · rw [u₉.other r h5, u₈.other r h4, u₇.other r h3, u₆.other r h30, u₅.other r h31, g₄ r h0]
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr,
      u₁.other _ (by decide), u₁.other _ (by decide)]

theorem initZero_wp {t : State} {S B : Addr} (h31 : t.gpr .r31 = S) (h30 : t.gpr .r30 = B)
    (hW : (⟨B, 640⟩ : Region) ∈ t.wr) {Q : State → Prop}
    (k : ∀ u, u.gpr .r3 = S → u.gpr .r4 = B + BitVec.ofNat 64 512 → u.gpr .r5 = B →
      (∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → u.gpr r = t.gpr r) →
      u.mem = t.mem.writeW (B + BitVec.ofNat 64 512) (0 : BitVec 64) → u.rd = t.rd → u.wr = t.wr → Q u) :
    WP isa (.block initZero) t Q := by
  simp only [initZero, mr]
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_addi (by decide) (by decide) fun s₃ u₃ =>
    wp_li (by decide) fun s₄ u₄ => ?_
  refine wp_std (a := B + BitVec.ofNat 64 512) (by decide) (by decide)
    (by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h30, bufOff]; exact BitVec.add_zero _)
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact scr_in hW (by decide)) fun s₅ u₅ => wp_nil ?_
  refine k s₅ ?_ ?_ ?_ (fun r h0 h3 h4 h5 => ?_) ?_ (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h31]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h30, bufOff]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h30]
  · rw [u₅.gpr, u₄.other r h0, u₃.other r h4, u₂.other r h5, u₁.other r h3]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.gpr]
    rfl

/-- The subkeys from `L = rev64 [r4]`, the chaining value zeroed, and the
return address and the caller's `r30`, `r31` restored. -/
theorem initTail_wp {u : State} {S B : Addr} (h3 : u.gpr .r3 = S) (h4 : u.gpr .r4 = B + BitVec.ofNat 64 512)
    (h30 : u.gpr .r30 = B) (hS : (⟨S, 416⟩ : Region) ∈ u.wr) (hW : (⟨B, 640⟩ : Region) ∈ u.wr)
    (hd : Region.Disjoint ⟨S, 416⟩ ⟨B, 640⟩) {Q : State → Prop}
    (k : ∀ f, let L := rev64 (u.mem.readW (B + BitVec.ofNat 64 512) 64)
      f.mem = ((u.mem.writeW (S + BitVec.ofNat 64 384) (rev64 (dbl64 L))).writeW
        (S + BitVec.ofNat 64 384 + BitVec.ofNat 64 8) (rev64 (dbl64 (dbl64 L)))).writeW
        (S + BitVec.ofNat 64 400) (0 : BitVec 64) →
      f.gpr .r30 = u.mem.readW (B + BitVec.ofNat 64 r30Off) 64 →
      f.gpr .r31 = u.mem.readW (B + BitVec.ofNat 64 r31Off) 64 →
      f.lr = u.mem.readW (B + BitVec.ofNat 64 lrOff) 64 →
      (∀ r ∈ preserved, r ≠ .r30 → r ≠ .r31 → f.gpr r = u.gpr r) → Q f) :
    WP isa (.block (initSubkeys ++ initRestore)) u Q := by
  have inS : ∀ off, off + 8 ≤ 416 → InRegions u.wr (S + BitVec.ofNat 64 off) 8 := fun off h =>
    ⟨_, hS, VG.Offset.contains_base _ h (by omega)⟩
  -- The slots of the working space are apart from the state's.
  have sep : ∀ off, off + 8 ≤ 640 → ∀ off', off' + 8 ≤ 416 →
      Region.Disjoint ⟨B + BitVec.ofNat 64 off, 8⟩ ⟨S + BitVec.ofNat 64 off', 8⟩ := fun off h off' h' =>
    (hd.sub_left (VG.Offset.sub_base _ h')).symm.sub_left (VG.Offset.sub_base _ h)
  simp only [initSubkeys, initRestore, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s₁ u₁ => ?_
  refine wp_ldbrx (ea := B + BitVec.ofNat 64 512) (by decide)
    (by rw [u₁.gpr, u₁.other _ (by decide), h4, BitVec.add_zero]) (by rw [u₁.rd, u₁.wr]; exact scr_rd hW (by decide))
    fun s₂ u₂ => ?_
  refine dblCode_wp (by rw [u₂.other _ (by decide), u₁.gpr]; rfl) fun s₃ g₃ o₃ m₃ rd₃ wr₃ => ?_
  refine wp_li (by decide) fun s₄ u₄ => ?_
  refine wp_stdbrx (ea := S + BitVec.ofNat 64 384) (by decide)
    (by rw [u₄.gpr, u₄.other _ (by decide), o₃ _ (by decide) (by decide) (by decide) (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h3])
    (by rw [u₄.wr, wr₃, u₂.wr, u₁.wr]; exact inS 384 (by decide)) fun s₅ u₅ => ?_
  refine dblCode_wp (by rw [u₅.gpr, u₄.other _ (by decide), o₃ _ (by decide) (by decide) (by decide) (by decide),
      u₂.other _ (by decide), u₁.gpr]; rfl) fun s₆ g₆ o₆ m₆ rd₆ wr₆ => ?_
  refine wp_li (by decide) fun s₇ u₇ => ?_
  refine wp_stdbrx (ea := S + BitVec.ofNat 64 384 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₇.gpr, u₇.other _ (by decide), o₆ _ (by decide) (by decide) (by decide) (by decide), u₅.gpr,
      u₄.other _ (by decide), o₃ _ (by decide) (by decide) (by decide) (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h3, VG.Offset.add_add])
    (by rw [u₇.wr, wr₆, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr, VG.Offset.add_add]; exact inS 392 (by decide))
    fun s₈ u₈ => ?_
  refine wp_li (by decide) fun s₉ u₉ => ?_
  have r3₉ : s₉.gpr .r3 = S := by
    rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), o₆ _ (by decide) (by decide) (by decide) (by decide),
      u₅.gpr, u₄.other _ (by decide), o₃ _ (by decide) (by decide) (by decide) (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h3]
  have r30₉ : s₉.gpr .r30 = B := by
    rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), o₆ _ (by decide) (by decide) (by decide) (by decide),
      u₅.gpr, u₄.other _ (by decide), o₃ _ (by decide) (by decide) (by decide) (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h30]
  have wr₉ : s₉.wr = u.wr := by rw [u₉.wr, u₈.wr, u₇.wr, wr₆, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr]
  have rd₉ : s₉.rd = u.rd := by rw [u₉.rd, u₈.rd, u₇.rd, rd₆, u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd]
  refine wp_std (a := S + BitVec.ofNat 64 400) (by decide) (by decide) (by rw [r3₉])
    (by rw [wr₉]; exact inS 400 (by decide)) fun s₁₀ u₁₀ => ?_
  have hR : ∀ off, off + 8 ≤ 640 → InRegions (s₁₀.rd ++ s₁₀.wr) (B + BitVec.ofNat 64 off) 8 := fun off h => by
    rw [u₁₀.rd, u₁₀.wr, rd₉, wr₉]; exact scr_rd hW h
  refine wp_ld (a := B + BitVec.ofNat 64 lrOff) (by decide) (by decide) (by rw [u₁₀.gpr, r30₉])
    (hR lrOff (by decide)) fun s₁₁ u₁₁ => ?_
  refine wp_ld (a := B + BitVec.ofNat 64 r31Off) (by decide) (by decide)
    (by rw [u₁₁.other _ (by decide), u₁₀.gpr, r30₉]) (by rw [u₁₁.rd, u₁₁.wr]; exact hR r31Off (by decide))
    fun s₁₂ u₁₂ => ?_
  refine wp_ld (a := B + BitVec.ofNat 64 r30Off) (by decide) (by decide)
    (by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, r30₉])
    (by rw [u₁₂.rd, u₁₂.wr, u₁₁.rd, u₁₁.wr]; exact hR r30Off (by decide)) fun s₁₃ u₁₃ => wp_mtlr (wp_nil ?_)
  -- The memory.
  have v₄ : s₄.gpr .r7 = dbl64 (rev64 (u.mem.readW (B + BitVec.ofNat 64 512) 64)) := by
    rw [u₄.other _ (by decide), g₃, u₂.gpr, u₁.mem]
  have v₇ : s₇.gpr .r7 = dbl64 (dbl64 (rev64 (u.mem.readW (B + BitVec.ofNat 64 512) 64))) := by
    rw [u₇.other _ (by decide), g₆, u₅.gpr, v₄]
  have m₁₀ : s₁₀.mem = ((u.mem.writeW (S + BitVec.ofNat 64 384)
      (rev64 (dbl64 (rev64 (u.mem.readW (B + BitVec.ofNat 64 512) 64))))).writeW
      (S + BitVec.ofNat 64 384 + BitVec.ofNat 64 8)
      (rev64 (dbl64 (dbl64 (rev64 (u.mem.readW (B + BitVec.ofNat 64 512) 64)))))).writeW
      (S + BitVec.ofNat 64 400) (0 : BitVec 64) := by
    rw [u₁₀.mem, u₉.gpr, u₉.mem, u₈.mem, u₇.mem, m₆, u₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem, ← v₇, ← v₄]
    rfl
  have rdB : ∀ off, off + 8 ≤ 640 → s₁₀.mem.readW (B + BitVec.ofNat 64 off) 64 =
      u.mem.readW (B + BitVec.ofNat 64 off) 64 := fun off h => by
    rw [m₁₀, readW_sep64 (sep off h 400 (by decide)),
      readW_sep64 (by rw [VG.Offset.add_add]; exact sep off h 392 (by decide)), readW_sep64 (sep off h 384 (by decide))]
  refine k _ (by show s₁₃.mem = _; rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀]) ?_ ?_ ?_ (fun r hr h30' h31' => ?_)
  · show s₁₃.gpr .r30 = _; rw [u₁₃.gpr, u₁₂.mem, u₁₁.mem, rdB r30Off (by decide)]
  · show s₁₃.gpr .r31 = _; rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.mem, rdB r31Off (by decide)]
  · show s₁₃.gpr .r0 = _; rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, rdB lrOff (by decide)]
  · obtain ⟨h0, -, -, -, h6, h7, h8, h9, h10, h11, -⟩ := preserved_ne r hr
    show s₁₃.gpr r = _
    rw [u₁₃.other r h30', u₁₂.other r h31', u₁₁.other r h0, u₁₀.gpr, u₉.other r h0, u₈.gpr, u₇.other r h11,
      o₆ r h7 h8 h9 h10, u₅.gpr, u₄.other r h11, o₃ r h7 h8 h9 h10, u₂.other r h7, u₁.other r h6]

/-- The state after `stream_init`: the schedule, the subkeys and the chaining
value of the empty message. -/
theorem repr_init {m : Mem} {S : Addr} {key : List Byte} (hv : Spec.TripleDes.validKey key.length)
    (hs : Spec.TripleDes.scheduleAt m S = Spec.TripleDes.expandKey key)
    (hk : Spec.Aes.bytesAt m (S + 384) 16 =
      le8 (rev64 (dbl64 (Proof.CmacTripleDes.tdes (Spec.TripleDes.expandKey key) 0))) ++
        le8 (rev64 (dbl64 (dbl64 (Proof.CmacTripleDes.tdes (Spec.TripleDes.expandKey key) 0)))))
    (hc : Spec.Aes.bytesAt m (S + 400) 8 = le8 0) : Spec.Cmac.tdesRepr m S key [] := by
  refine ⟨hv, hs, ?_, ?_, ?_⟩
  · rw [hk, Spec.Cmac.tdes, Proof.CmacTripleDes.subkeys_tdes]; rfl
  · rw [hc, Proof.Cmac.le8_zero]; rfl
  · rfl

theorem init_wp (s : State) (hp : InitPre s) :
    WP isa streamInit s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.lr = s.lr ∧
      Spec.Cmac.tdesRepr s'.mem (s.gpr .r3) (Spec.TripleDes.bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat) [] := by
  have hS : (⟨s.gpr .r3, 416⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hW : (⟨s.gpr .r6, 640⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hfitB := hp.scrFit
  have hfitS := hp.stateFit
  -- The working space's slots are apart from the schedule and the key.
  have slotSched : ∀ off, off + 8 ≤ 640 → Region.Disjoint ⟨s.gpr .r6 + BitVec.ofNat 64 off, 8⟩ ⟨s.gpr .r3, 384⟩ :=
    fun off h => (hp.stateScr.sub_left (Region.sub_prefix (by decide))).symm.sub_left (VG.Offset.sub_base _ h)
  unfold streamInit
  refine WP.seq ?_
  rw [← List.append_nil initSave]
  refine initSave_wp hp fun t ht => wp_nil ?_
  have keyIn : (⟨s.gpr .r4, (s.gpr .r5).toNat⟩ : Region) ∈ t.rd := by rw [ht.rd, hp.rd]; simp
  refine WP.seq (keyCall_wp (K := s.gpr .r4) (S := s.gpr .r3) (len := (s.gpr .r5).toNat) ht.r3
    (by rw [ht.r4, BitVec.ofNat_toNat, BitVec.setWidth_eq]) ht.r5 (s.gpr .r5).isLt keyIn (by rw [ht.wr]; exact hS)
    hp.keyState hp.valid fun t₁ rd₁ wr₁ f₁ c₁ sch₁ => ?_)
  have r31₁ : t₁.gpr .r31 = s.gpr .r3 := by rw [c₁ _ (by decide), ht.r31]
  have r30₁ : t₁.gpr .r30 = s.gpr .r6 := by rw [c₁ _ (by decide), ht.r30]
  refine WP.seq (initZero_wp r31₁ r30₁ (by rw [wr₁, ht.wr]; exact hW) fun u h3 h4 h5 hu mu rdu wru => ?_)
  have wru' : u.wr = s.wr := by rw [wru, wr₁, ht.wr]
  have rdu' : u.rd = s.rd := by rw [rdu, rd₁, ht.rd]
  refine WP.seq (encCall_wp h3 h4 h5 ⟨_, List.mem_append_right _ (by rw [wru']; exact hS),
      VG.Offset.contains_base _ (show 0 + 384 ≤ 416 by decide) (by decide) |> fun h => by simpa using h⟩
    (by rw [wru']; exact hW) (Nat.le_refl _) (hp.stateScr.sub_left (Region.sub_prefix (by decide)))
    fun v rdv wrv cv v3 v4 v5 fv outv => ?_)
  have wrv' : v.wr = s.wr := by rw [wrv, wru']
  refine initTail_wp v3 v4 (by rw [cv _ (by decide), hu _ (by decide) (by decide) (by decide) (by decide), r30₁])
    (by rw [wrv']; exact hS) (by rw [wrv']; exact hW) hp.stateScr fun f mf r30f r31f lrf rf => ?_
  -- The working space's saved slots, through the calls and the writes.
  have slot : ∀ off, 520 ≤ off → off + 8 ≤ 640 → v.mem.readW (s.gpr .r6 + BitVec.ofNat 64 off) 64 =
      t.mem.readW (s.gpr .r6 + BitVec.ofNat 64 off) 64 := fun off h1 h2 => by
    rw [fv.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.disjoint_base _ (by omega) (by omega)) (by decide),
      mu, readW_sep64 (VG.Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)),
      f₁.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact slotSched off h2) (by decide)]
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · by_cases e30 : r = .r30
    · subst e30
      rw [r30f, slot r30Off (by decide) (by decide), ht.mem,
        readW_sep64 (VG.Offset.disjoint _ (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]
    by_cases e31 : r = .r31
    · subst e31
      rw [r31f, slot r31Off (by decide) (by decide), ht.mem, Mem.readW_writeW_self64]
    obtain ⟨h0, h3', h4', h5', -⟩ := preserved_ne r hr
    rw [rf r hr e30 e31, cv r hr, hu r h0 h3' h4' h5', c₁ r hr, ht.regs r h0 h3' h4' h5' e30 e31]
  · rw [lrf, slot lrOff (by decide) (by decide), ht.mem,
      readW_sep64 (VG.Offset.disjoint _ (by decide) (by decide) (by decide)),
      readW_sep64 (VG.Offset.disjoint _ (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]
  · -- Frames of the memory through the steps.
    have cB : ∀ off, off + 8 ≤ 640 → (⟨s.gpr .r6, 640⟩ : Region).Contains (s.gpr .r6 + BitVec.ofNat 64 off) (64 / 8) :=
      fun off h => VG.Offset.contains_base _ h (by omega)
    have F0 : Frame [⟨s.gpr .r6, 640⟩] s.mem t.mem := by
      rw [ht.mem]
      exact (((Frame.refl _ _).writeW List.mem_cons_self _ (cB lrOff (by decide))).writeW List.mem_cons_self _
        (cB r30Off (by decide))).writeW List.mem_cons_self _ (cB r31Off (by decide))
    have F2 : Frame [⟨s.gpr .r6, 640⟩] t₁.mem u.mem := by
      rw [mu]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (cB 512 (by decide))
    have F3 : Frame [⟨s.gpr .r6, 640⟩] u.mem v.mem :=
      fv.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    have cS : ∀ off, 384 ≤ off → off + 8 ≤ 408 →
        (⟨s.gpr .r3 + BitVec.ofNat 64 384, 24⟩ : Region).Contains (s.gpr .r3 + BitVec.ofNat 64 off) (64 / 8) :=
      fun off h1 h2 => VG.Offset.contains _ h1 (by omega) (by omega)
    have F4 : Frame [⟨s.gpr .r3 + BitVec.ofNat 64 384, 24⟩] v.mem f.mem := by
      rw [mf, VG.Offset.add_add]
      exact (((Frame.refl _ _).writeW List.mem_cons_self _ (cS 384 (by decide) (by decide))).writeW
        List.mem_cons_self _ (cS 392 (by decide) (by decide))).writeW List.mem_cons_self _ (cS 400 (by decide) (by decide))
    have schedOut : ∀ r ∈ [(⟨s.gpr .r3 + BitVec.ofNat 64 384, 24⟩ : Region), ⟨s.gpr .r6, 640⟩],
        Region.Disjoint ⟨s.gpr .r3, 384⟩ r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Offset.base_disjoint _ (by decide) (by omega)
      · exact hp.stateScr.sub_left (Region.sub_prefix (by decide))
    have Fu : Frame [⟨s.gpr .r3 + BitVec.ofNat 64 384, 24⟩, ⟨s.gpr .r6, 640⟩] t₁.mem u.mem := F2.mono (by simp)
    have Ff : Frame [⟨s.gpr .r3 + BitVec.ofNat 64 384, 24⟩, ⟨s.gpr .r6, 640⟩] t₁.mem f.mem :=
      (Fu.trans (F3.mono (by simp))).trans (F4.mono (by simp))
    have keyEq : Spec.TripleDes.bytesAt t.mem (s.gpr .r4) (s.gpr .r5).toNat =
        Spec.TripleDes.bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat :=
      List.map_congr_left fun i hi => F0.bytes (R := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.keyScr)
        (by have := (s.gpr .r5).isLt; show (s.gpr .r5).toNat ≤ 2 ^ 64; omega) (List.mem_range.mp hi)
    rw [keyEq] at sch₁
    have schU : Spec.TripleDes.scheduleAt u.mem (s.gpr .r3) =
        Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat) := by
      rw [Proof.TripleDes.scheduleAt_eq_of_frame _ Fu schedOut, sch₁]
    -- `L`.
    have zero : Spec.Aes.bytesAt u.mem (s.gpr .r6 + BitVec.ofNat 64 512) 8 = Spec.Cmac.zeros 8 := by
      rw [← Proof.Cmac.le8_readW, mu, Mem.readW_writeW_self64, Proof.Cmac.le8_zero]
    rw [schU, zero_block _ _ zero] at outv
    have hL := l_eq outv
    refine repr_init (by simpa [Spec.TripleDes.bytesAt] using hp.valid)
      (by rw [Proof.TripleDes.scheduleAt_eq_of_frame _ Ff schedOut, sch₁]) ?_ ?_
    · have drop : ∀ m : Mem, Spec.Aes.bytesAt (m.writeW (s.gpr .r3 + BitVec.ofNat 64 400) (0 : BitVec 64))
          (s.gpr .r3 + BitVec.ofNat 64 384) 16 = Spec.Aes.bytesAt m (s.gpr .r3 + BitVec.ofNat 64 384) 16 :=
        fun m => List.map_congr_left fun i hi =>
          ((Frame.refl [(⟨s.gpr .r3 + BitVec.ofNat 64 400, 8⟩ : Region)] m).writeW List.mem_cons_self
            (0 : BitVec 64) (Region.contains_self _ _)).bytes (R := ⟨s.gpr .r3 + BitVec.ofNat 64 384, 16⟩)
            (fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr
              exact VG.Offset.disjoint _ (.inl (by decide)) (by omega) (by omega)) (by show 16 ≤ 2 ^ 64; decide)
            (List.mem_range.mp hi)
      show Spec.Aes.bytesAt f.mem (s.gpr .r3 + BitVec.ofNat 64 384) 16 = _
      rw [mf, drop, Proof.Cmac.bytesAt_store2, hL]
    · show Spec.Aes.bytesAt f.mem (s.gpr .r3 + BitVec.ofNat 64 400) 8 = _
      rw [← Proof.Cmac.le8_readW, mf, Mem.readW_writeW_self64]

end VG.Proof.CmacTripleDes.Stream.PPC64LE
