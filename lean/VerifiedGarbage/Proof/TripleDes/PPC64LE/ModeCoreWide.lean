module
-- separate module: the core on 64 blocks, as `ModeCore.lean` is the core on one; it alone imports the bitsliced ECB

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModeCore
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Ecb64
public import VerifiedGarbage.Proof.Modes.PPC64LE.Wide
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.Covers

/-!
# Triple DES's core on 64 blocks for the modes on PPC64LE

`wideCoreSpec d`: the core of the bitsliced ECB on 64 blocks
(`Impl.TripleDes.PPC64LE.wideCore d`) meets what the modes need of a core
(`Proof.Modes.PPC64LE.CoreSpec`), as the core of one block does
(`ModeCore.lean`), with the same key and ciphers, its schedule apart from
its 200 slots. ECB on 64 blocks (`Bitsliced.ecb64_wp`) runs on the buffer, with the first
128 slots as its working space, and leaves the working space's and the
schedule's addresses in `r10` and `r7`, from which `sb` and `r3` come back.

`wideOne_ok d`: the block function on the buffer's first block
(`Impl.TripleDes.PPC64LE.wideOne d`) enciphers it as the core does
(`Proof.Modes.PPC64LE.OneOk`), for the blocks left after the groups of 64,
as the core of one block's code does (`crypt_wp`), with the block at slot
128 rather than 64.
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Mode

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE
open VG.Impl.Modes.PPC64LE (sb)
open VG.Proof.Modes.PPC64LE (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept OneOk)
open VG.Spec.Aes (bytesAt)
open VG.Spec.TripleDes (Direction)
open VG.Proof.TripleDes (dirCipher bytesAt_eq scheduleAt_eq_of_frame)

/-- The key's arguments, apart from the wide core's scratch buffer at `B` too. -/
def ReadyW (s : State) (B : Addr) (ws : List Region) (k : Spec.TripleDes.Schedule) : Prop :=
  KeyArgs s ws k ∧ (keyR s).Disjoint ⟨B, 8 * 200⟩

theorem readyW_frame {s s' : State} {B : Addr} {ws : List Region} {k : Spec.TripleDes.Schedule}
    {rs : List Region} (h : ReadyW s B ws k) (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r') :
    ReadyW s' B ws k := by
  obtain ⟨⟨hk, hin, hd⟩, hB⟩ := h
  have hd' : ∀ r ∈ rs, (keyR s).Disjoint r := fun r hr => by
    obtain ⟨r', hr', hsub⟩ := hs r hr
    exact (hd r' hr').sub_right hsub
  refine ⟨⟨?_, by rw [hrd, hwr, e]; exact hin, by rw [keyR, e]; exact hd⟩, by rw [keyR, e]; exact hB⟩
  rw [e, scheduleAt_eq_of_frame _ hf hd', hk]

theorem layoutW (d : Direction) : Layout (wideCore d) :=
  ⟨by cases d <;> decide, .inl rfl, by cases d <;> decide, by cases d <;> decide, by cases d <;> decide⟩

theorem prepareW_wp (d : Direction) {s : State} {B : Addr} {rs : List Region} {k : Spec.TripleDes.Schedule}
    (hB : s.gpr sb = B) (_hS : ScrIn s B (wideCore d).total) (hm : (⟨B, 8 * (wideCore d).total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa (wideCore d).prepare s fun s' => ReadyW s' B rs k ∧ s'.gpr sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (wideCore d) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  wp_nil ⟨⟨hk, hk.2.2 _ hm⟩, hB, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩

theorem blockOut_eq (k : Spec.TripleDes.Schedule) (d : Direction) (b : Spec.TripleDes.Block) :
    VG.Proof.TripleDes.Bitslice.blockOut k d b = blockResult k d b := by
  cases d <;> rfl

/-- A call of code that keeps the link register. -/
theorem WP.callOf {name : String} {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s.callEntry fun s₂ => s₂.lr = s.callEntry.lr ∧ Q s₂) : WP isa (.call name c) s Q := by
  obtain ⟨t, s₂, he, hlr, hq⟩ := h
  refine ⟨_, _, Exec.call (call_callEntry s) he ?_, hq⟩
  simp only [isa, ret]
  exact ite_eq_left_of_eq_true _ _ (eq_true hlr)

theorem ecb64Call_wp (d : Direction) {s : State} {Q : State → Prop}
    (h : WP isa (Bitslice.ecb64 d) s.callEntry fun s₂ => s₂.lr = s.callEntry.lr ∧ Q s₂) :
    WP isa (ecb64Call d) s Q := by
  cases d <;> exact WP.callOf h

/-- `kept` but `r3`: the callee-saved registers. -/
theorem kept_cases : ∀ r ∈ kept, r = .r3 ∨ r ∈ preserved := by decide

theorem cryptW_wp (d : Direction) {s : State} {B : Addr} {ws : List Region} {k : Spec.TripleDes.Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B (wideCore d).total) (hR : ReadyW s B ws k) :
    WP isa (wideCore d).crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      ReadyW s' B ws k ∧ Frame [coreRegion (wideCore d) B] s.mem s'.mem ∧
      (∀ j < (wideCore d).G, bytesAt s'.mem (blkAddr (wideCore d) B j) (4 * (wideCore d).bw) =
        dirCipher d k (bytesAt s.mem (blkAddr (wideCore d) B j) (4 * (wideCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 200 ≤ 2 ^ 64 := hS.fit
  have hW : (⟨B, 8 * 200⟩ : Region) ∈ s.wr := hS.wr
  obtain ⟨⟨hk, hin, hd⟩, hkB⟩ := hR
  simp only [wideCore]
  refine WP.seq (wp_mr fun s₁ u₁ => wp_addi (n := sb) (by decide) (by decide) fun s₃ u₃ => wp_nil ?_)
  have g₃ : ∀ r, r ≠ .r6 → r ≠ .r4 → s₃.gpr r = s.gpr r := fun r a b => by
    rw [u₃.other r b, u₁.other r a]
  have r6₃ : s₃.gpr .r6 = B := by rw [u₃.other _ (by decide), u₁.gpr]; exact hB
  have r4₃ : s₃.gpr .r4 = B + BitVec.ofNat 64 1024 := by
    rw [u₃.gpr, u₁.other _ (by decide), hB]; rfl
  have r3₃ : s₃.gpr .r3 = s.gpr .r3 := g₃ _ (by decide) (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₁.wr]
  have pre : Bitsliced.Ecb64Pre s₃ := by
    refine ⟨by rw [r3₃, rd₃, wr₃]; exact hin, ?_, ?_, ?_, ?_, ?_⟩
    · rw [r4₃, wr₃]
      exact Bitsliced.covers_of_sub hW (off := 1024) rfl (by show 1024 + 512 ≤ 8 * 200; omega_using [])
    · rw [r6₃, wr₃]
      exact ⟨_, hW, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using []⟩
    · rw [r4₃, r3₃]; exact hkB.sub_right (VG.Offset.sub_base _ (by show 1024 + 512 ≤ 8 * 200; omega_using []))
    · rw [r6₃, r3₃]; exact hkB.sub_right (Region.sub_prefix (by show 1024 ≤ 8 * 200; omega_using []))
    · rw [r4₃, r6₃]; exact VG.Offset.disjoint_base _ (by omega_using []) (by omega_using [])
  -- the call: its entry changes only `r0`, `r11`, `r12` and the link register
  have ce : ∀ r, r ∉ linkRegs → s₃.callEntry.gpr r = s₃.gpr r := fun r h => State.callEntry_gpr s₃ h
  have e3 := ce .r3 (by decide)
  have e4 := ce .r4 (by decide)
  have e6 := ce .r6 (by decide)
  have pre' : Bitsliced.Ecb64Pre s₃.callEntry :=
    ⟨by rw [State.callEntry_rd, State.callEntry_wr, e3]; exact pre.key,
      by rw [State.callEntry_wr, e4]; exact pre.data, by rw [State.callEntry_wr, e6]; exact pre.buf,
      by rw [e3, e4]; exact pre.keyData, by rw [e3, e6]; exact pre.keyBuf, by rw [e4, e6]; exact pre.dataBuf⟩
  apply WP.seq
  refine ecb64Call_wp d (WP.mono (Bitsliced.WP.rdwr (Bitsliced.ecb64_wp d pre'))
    fun s₄ ⟨⟨p₄, l₄, r10₄, r7₄, f₄, b₄⟩, rd₄, wr₄, _⟩ => ⟨l₄, ?_⟩)
  simp only [State.callEntry_rd, State.callEntry_wr, State.callEntry_mem, e3, e4, e6] at rd₄ wr₄ f₄ b₄ r10₄ r7₄
  have p₄' : ∀ r ∈ preserved, s₄.gpr r = s₃.gpr r := fun r hr => by
    rw [p₄ r hr, ce r (preserved_not_link r hr)]
  refine wp_mr fun s₅ u₅ => wp_mr fun s₆ u₆ => wp_nil ?_
  rw [r10₄, r6₃] at u₅
  have r5₆ : s₆.gpr .r5 = B := by rw [u₆.other _ (by decide)]; exact u₅.gpr
  have r3₆ : s₆.gpr .r3 = s.gpr .r3 := by rw [u₆.gpr, u₅.other _ (by decide), r7₄, r3₃]
  have m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  have g₆ : ∀ r ∈ kept, s₆.gpr r = s.gpr r := fun r hr => by
    rcases kept_cases r hr with rfl | h
    · exact r3₆
    · have h3 : r ≠ .r3 := by revert h; decide +revert
      have h5 : r ≠ .r5 := by revert h; decide +revert
      have h4 : r ≠ .r4 := by revert h; decide +revert
      have h6 : r ≠ .r6 := by revert h; decide +revert
      rw [u₆.other r h3, u₅.other r h5, p₄' r h, g₃ r h6 h4]
  have sub : ∀ r ∈ [(⟨s₃.gpr .r6, 1024⟩ : Region), ⟨s₃.gpr .r4, 512⟩],
      Region.Sub r ⟨B, 8 * (wideBuf + 64)⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [r6₃]; exact Region.sub_prefix (by decide)
    · rw [r4₃]; exact VG.Offset.sub_base _ (by decide)
  have f₆ : Frame [⟨s₃.gpr .r6, 1024⟩, ⟨s₃.gpr .r4, 512⟩] s.mem s₆.mem := by
    rw [m₆, ← m₃]; exact f₄
  have hkB' : ∀ r ∈ [(⟨s₃.gpr .r6, 1024⟩ : Region), ⟨s₃.gpr .r4, 512⟩],
      (keyR s).Disjoint r := fun r hr =>
      (hkB.sub_right (Region.sub_prefix (by decide))).sub_right (sub r hr)
  have sched : Spec.TripleDes.scheduleAt s₆.mem (s₆.gpr .r3) = k := by
    rw [r3₆, scheduleAt_eq_of_frame _ f₆ hkB', hk]
  refine ⟨r5₆, g₆, ⟨⟨sched, by rw [u₆.rd, u₅.rd, rd₄, rd₃, u₆.wr, u₅.wr, wr₄, wr₃, r3₆]; exact hin,
      by rw [keyR, r3₆]; exact hd⟩, by rw [keyR, r3₆]; exact hkB⟩,
    f₆.sub fun r hr => ⟨_, List.mem_singleton_self _, sub r hr⟩, fun j hj => ?_,
    by rw [u₆.rd, u₅.rd, rd₄, rd₃], by rw [u₆.wr, u₅.wr, wr₄, wr₃]⟩
  have hj64 : j < 64 := hj
  have e : blkAddr (wideCore d) B j = VG.Proof.TripleDes.Bitslice.wAt (s₃.gpr .r4) j := by
    rw [r4₃]; simp only [blkAddr, slotA, wideCore, wideBuf, VG.Proof.TripleDes.Bitslice.wAt]
  have b := b₄ j hj64
  simp only [wideCore] at e
  rw [e, bytesAt_eq, m₆, b, blockOut_eq, ← dirCipher_bytes, m₃, r3₃, hk]

/-- Triple DES's core on 64 blocks for the direction `d` meets what the modes need. -/
def wideCoreSpec (d : Direction) : CoreSpec (wideCore d) where
  Key := Spec.TripleDes.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready := ReadyW
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher, wideCore]
  layout := layoutW d
  keyArgs_congr h e r w _ f := keyArgs_congr h e.r3 r w f
  ready_frame h e r w _ f hs _ := readyW_frame h e.r3 r w f hs
  prepare_wp := prepareW_wp d
  crypt_wp := cryptW_wp d

/-- The block function on the wide core's first block. -/
theorem wideOne_ok (d : Direction) : OneOk (wideCoreSpec d) (wideOne d) := by
  intro s B ws (k : Spec.TripleDes.Schedule) hB hS hR
  have hfit : B.toNat + 8 * 200 ≤ 2 ^ 64 := hS.fit
  have hW : (⟨B, 8 * 200⟩ : Region) ∈ s.wr := hS.wr
  obtain ⟨⟨hk, hin, hd⟩, hkB⟩ := hR
  refine WP.seq (wp_addi (n := sb) (by decide) (by decide) fun s₁ u₁ => wp_nil ?_)
  have r4₁ : s₁.gpr .r4 = B + BitVec.ofNat 64 1024 := by rw [u₁.gpr, hB]; rfl
  have g₁ : ∀ r, r ≠ .r4 → s₁.gpr r = s.gpr r := u₁.other
  have m₁ : s₁.mem = s.mem := u₁.mem
  have rd₁ : s₁.rd = s.rd := u₁.rd
  have wr₁ : s₁.wr = s.wr := u₁.wr
  have r3₁ : s₁.gpr .r3 = s.gpr .r3 := g₁ _ (by decide)
  have r5₁ : s₁.gpr .r5 = B := by rw [g₁ _ (by decide)]; exact hB
  have cw : VG.Covers [⟨s₁.gpr .r4, 8⟩, ⟨s₁.gpr .r5, 512⟩] s₁.wr := VG.Covers.of_sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨B, 8 * 200⟩, by rw [wr₁]; exact hW, 1024, r4₁, by show 1024 + 8 ≤ 8 * 200; omega_using []⟩
    · exact ⟨⟨B, 8 * 200⟩, by rw [wr₁]; exact hW, 0, by simp [r5₁], by show 0 + 512 ≤ 8 * 200; omega_using []⟩
  have hp : Ecb.CallPre s₁ :=
    ⟨VG.Covers.cons (by rw [r3₁, rd₁, wr₁]; exact VG.Covers.one hin) (VG.Covers.right cw), cw,
      by rw [r3₁, r5₁]; exact hkB.sub_right (Region.sub_prefix (by decide)),
      by rw [r4₁, r5₁]; exact VG.Offset.disjoint_base _ (by decide) (by omega_using [hfit])⟩
  refine WP.mono (Ecb.call_ok d s₁ hp) fun s₂ h₂ => ?_
  have g₂ : ∀ r ∈ kept, s₂.gpr r = s.gpr r := fun r hr => by
    have h4 : r ≠ .r4 := by revert hr; decide +revert
    rcases kept_sub r hr with h | h
    · rw [h₂.reg r h, g₁ r h4]
    · rw [h₂.callee r h, g₁ r h4]
  have r3₂ : s₂.gpr .r3 = s.gpr .r3 := g₂ _ (by decide)
  have sub₂ : ∀ r ∈ [(⟨s₁.gpr .r4, 8⟩ : Region), ⟨s₁.gpr .r5, 512⟩], Region.Sub r ⟨B, 8 * 200⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [r4₁]; exact VG.Offset.sub_base _ (by decide)
    · rw [r5₁]; exact Region.sub_prefix (by decide)
  have f₂ : Frame [⟨s₁.gpr .r4, 8⟩, ⟨s₁.gpr .r5, 512⟩] s.mem s₂.mem := by rw [← m₁]; exact h₂.mem
  have sched : Spec.TripleDes.scheduleAt s₂.mem (s₂.gpr .r3) = k := by
    rw [r3₂, scheduleAt_eq_of_frame _ f₂ fun r hr => hkB.sub_right (sub₂ r hr), hk]
  refine ⟨by rw [show sb = .r5 from rfl, h₂.reg _ (by decide), r5₁], g₂,
    ⟨⟨sched, by rw [h₂.rd, h₂.wr, rd₁, wr₁, r3₂]; exact hin, by rw [keyR, r3₂]; exact hd⟩,
      by rw [keyR, r3₂]; exact hkB⟩, f₂.sub fun r hr => ?_, ?_,
    by rw [h₂.rd, rd₁], by rw [h₂.wr, wr₁]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, by
        rw [r4₁]; exact VG.Offset.sub_base _ (by show 1024 + 8 ≤ 8 * (wideBuf + 64); decide)⟩
    · exact ⟨_, List.mem_singleton_self _, by
        rw [r5₁]; exact Region.sub_prefix (by show 512 ≤ 8 * (wideBuf + 64); decide)⟩
  · have e : blkAddr (wideCore d) B 0 = s₁.gpr .r4 := by
      rw [r4₁]; simp [blkAddr, slotA, wideCore, wideBuf]
    change bytesAt s₂.mem (blkAddr (wideCore d) B 0) 8 = dirCipher d k (bytesAt s.mem (blkAddr (wideCore d) B 0) 8)
    rw [e, bytesAt_eq, h₂.output, dirCipher_bytes, m₁, r3₁, hk]

end VG.Proof.TripleDes.PPC64LE.Mode
