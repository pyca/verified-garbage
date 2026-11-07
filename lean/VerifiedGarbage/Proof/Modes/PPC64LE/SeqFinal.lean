module

public import VerifiedGarbage.Impl.Modes.PPC64LE.SeqFinal
public import VerifiedGarbage.Proof.Modes.PPC64LE.Seq
public import VerifiedGarbage.Proof.Modes.FbFinal
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Modes.Ctr

/-!
# CFB of a message's last piece on PPC64LE, for any core

`seqFinal_wp`: `c.seqFinal M`, for a core `c` with `CoreSpec c` and a mode
`M` whose `pre` copies the chaining value to the buffer and whose
operations compute the step function `F` (`Computes`), with its arguments
in registers (`f(key = r3, iv = r4, data = r5, len = r6, scratch = r7)`),
replaces the `len / L` whole blocks of `L = 4 bw` bytes at `data` with the
outputs of `F` from the IV, XORs the `r = len % L` bytes after them with the
first bytes of `CIPH_K` of the chaining value after them, and replaces the
IV with that chaining value if `r = 0` and with its encryption otherwise; it
keeps the registers the caller expects preserved, the stack pointer and the
return address. `cfbEncFinal_wp` and `cfbDecFinal_wp` state these as CFB's
(`Spec.Cfb.EncryptFinal`, …).

The loop over segments (`seg_wp`) is `seq`'s step (`Step.lean`: `regs`,
`cont`, `cryptBuf`), with the data's area within the `len` bytes
(`FixedF`, as the whole blocks and as the partial segment, a step of `r`
bytes) and the key ready for writes within the `len` bytes and the scratch
buffer (`MidF`), the bytes left in `r30`, and the partial segment's bytes
XORed by `tailLoop_wp`.
-/

@[expose] public section

namespace VG.Proof.Modes.PPC64LE

open VG VG.PPC64LE VG.Impl.Modes VG.Impl.Modes.PPC64LE
open VG.Spec.Aes (bytesAt)

/-! ## The partial segment's bytes

`tailLoop_wp`: from the `r > 0` bytes at `K` (in `r8`) and `R` (in `r31`,
their count in `r30`), the loop of `tailByte` XORs each byte at `K` into the
byte at the same offset of `R`, and changes memory only there.
-/

/-- What the loop works on. -/
structure XPre (s₀ : State) (K R : Addr) (r : Nat) : Prop where
  pos : 0 < r
  fitK : K.toNat + r ≤ 2 ^ 64
  fitR : R.toNat + r ≤ 2 ^ 64
  disj : Region.Disjoint ⟨K, r⟩ ⟨R, r⟩
  rdK : ∀ q < r, InRegions (s₀.rd ++ s₀.wr) (K + BitVec.ofNat 64 q) 1
  wrR : ∀ q < r, InRegions s₀.wr (R + BitVec.ofNat 64 q) 1

/-- The loop, before byte `j`. -/
structure XInv (s₀ : State) (K R : Addr) (r j : Nat) (s : State) : Prop where
  r8 : s.gpr .r8 = K + BitVec.ofNat 64 j
  r31 : s.gpr .r31 = R + BitVec.ofNat 64 j
  r30 : s.gpr .r30 = BitVec.ofNat 64 (r - j)
  lt : j < r
  data : ∀ q < r, s.mem (R + BitVec.ofNat 64 q) =
    if q < j then s₀.mem (R + BitVec.ofNat 64 q) ^^^ s₀.mem (K + BitVec.ofNat 64 q)
    else s₀.mem (R + BitVec.ofNat 64 q)
  frame : Frame [⟨R, r⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  gpr : ∀ x, x ≠ .r8 → x ≠ .r9 → x ≠ .r10 → x ≠ .r30 → x ≠ .r31 → s.gpr x = s₀.gpr x

/-- The loop, done. -/
structure XDone (s₀ : State) (K R : Addr) (r : Nat) (s : State) : Prop where
  r30 : s.gpr .r30 = 0
  data : ∀ q < r, s.mem (R + BitVec.ofNat 64 q) =
    s₀.mem (R + BitVec.ofNat 64 q) ^^^ s₀.mem (K + BitVec.ofNat 64 q)
  frame : Frame [⟨R, r⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  gpr : ∀ x, x ≠ .r8 → x ≠ .r9 → x ≠ .r10 → x ≠ .r30 → x ≠ .r31 → s.gpr x = s₀.gpr x

theorem inRdWr {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem tailByte_wp {s₀ : State} {K R : Addr} {r : Nat} (hp : XPre s₀ K R r) {j : Nat} {s : State}
    (hi : XInv s₀ K R r j s) :
    WP isa (.block tailByte) s fun s' => XDone s₀ K R r s' ∨
      (s'.gpr .r30 ≠ 0 ∧ XInv s₀ K R r (j + 1) s') := by
  have hj := hi.lt
  have hR := hp.fitR
  have eK : s.gpr .r8 + BitVec.ofNat 64 0 = K + BitVec.ofNat 64 j := by rw [hi.r8]; exact BitVec.add_zero _
  have eR : s.gpr .r31 + BitVec.ofNat 64 0 = R + BitVec.ofNat 64 j := by rw [hi.r31]; exact BitVec.add_zero _
  unfold tailByte
  refine wp_lbz (a := R + BitVec.ofNat 64 j) (by decide) (by decide) eR (by rw [hi.rd, hi.wr]; exact inRdWr (hp.wrR j hj)) fun s₁ u₁ => ?_
  refine wp_lbz (a := K + BitVec.ofNat 64 j) (by decide) (by decide) (by rw [u₁.other _ (by decide)]; exact eK)
    (by rw [u₁.rd, u₁.wr, hi.rd, hi.wr]; exact hp.rdK j hj) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  have e₃ : s₃.gpr .r31 = s.gpr .r31 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  refine wp_stb (a := R + BitVec.ofNat 64 j) (by decide) (by decide) (by rw [e₃]; exact eR)
    (by rw [u₃.wr, u₂.wr, u₁.wr, hi.wr]; exact hp.wrR j hj) fun s₄ u₄ => ?_
  refine wp_addi (by decide) (by decide) fun s₅ u₅ => wp_addi (by decide) (by decide) fun s₆ u₆ =>
    wp_subi (by decide) (by decide) fun s₇ u₇ => wp_nil ?_
  -- Registers.
  have g₄ : ∀ x, x ≠ .r9 → x ≠ .r10 → s₄.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₄.gpr, u₃.other x h1, u₂.other x h2, u₁.other x h1]
  have gR : ∀ x, x ≠ .r8 → x ≠ .r9 → x ≠ .r10 → x ≠ .r30 → x ≠ .r31 → s₇.gpr x = s.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [u₇.other x h4, u₆.other x h5, u₅.other x h1, g₄ x h2 h3]
  have r8₇ : s₇.gpr .r8 = K + BitVec.ofNat 64 (j + 1) := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄ _ (by decide) (by decide), hi.r8,
      VG.Offset.add_add]
  have r31₇ : s₇.gpr .r31 = R + BitVec.ofNat 64 (j + 1) := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄ _ (by decide) (by decide), hi.r31,
      VG.Offset.add_add]
  have r30₇ : s₇.gpr .r30 = BitVec.ofNat 64 (r - (j + 1)) := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g₄ _ (by decide) (by decide), hi.r30,
      ofNat_pred64 (by omega_using [hj]), Nat.sub_sub]
  -- Memory.
  have r9₃ : (s₃.gpr .r9).setWidth 8 = s.mem (R + BitVec.ofNat 64 j) ^^^ s.mem (K + BitVec.ofNat 64 j) := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.mem, setWidth_xor8]
  have mem₇ : s₇.mem = s.mem.writeW (R + BitVec.ofNat 64 j)
      (s.mem (R + BitVec.ofNat 64 j) ^^^ s.mem (K + BitVec.ofNat 64 j)) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact congrArg _ r9₃
  have hRj : Region.Sub ⟨R + BitVec.ofNat 64 j, 1⟩ ⟨R, r⟩ := VG.Offset.sub_base _ (by omega_using [hj])
  have hKk : ∀ q < r, s.mem (K + BitVec.ofNat 64 q) = s₀.mem (K + BitVec.ofNat 64 q) :=
    fun q hq => hi.frame.bytes (R := ⟨K, r⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact hp.disj) (by show r ≤ 2 ^ 64; omega_using [hR]) hq
  have data₇ : ∀ q < r, s₇.mem (R + BitVec.ofNat 64 q) =
      if q < j + 1 then s₀.mem (R + BitVec.ofNat 64 q) ^^^ s₀.mem (K + BitVec.ofNat 64 q)
      else s₀.mem (R + BitVec.ofNat 64 q) := fun q hq => by
    rw [mem₇, write1_apply]
    by_cases hqj : q = j
    · subst hqj
      rw [ite_eq_left (by rw [BitVec.sub_self]; decide), ite_eq_left (Nat.lt_succ_self _), hi.data q hq,
        ite_eq_right (Nat.lt_irrefl _), hKk q hq]
    · have hne : ¬ (R + BitVec.ofNat 64 q - (R + BitVec.ofNat 64 j)).toNat < 1 := by
        rw [VG.Offset.sub_toNat' _ (by omega_using [hR, hj]) (by omega_using [hR, hq])]
        split <;> omega_arith
      rw [ite_eq_right hne, hi.data q hq]
      by_cases h1 : q < j
      · rw [ite_eq_left h1, ite_eq_left (by omega_using [h1])]
      · rw [ite_eq_right h1, ite_eq_right (by omega_using [h1, hqj])]
  have fr₇ : Frame [⟨R, r⟩] s₀.mem s₇.mem := by
    rw [mem₇]
    exact hi.frame.writeW List.mem_cons_self _ (hRj _ (Region.contains_self _ _) |> fun h => by
      simpa [Region.Contains] using h)
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hi.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hi.wr]
  have hz : (BitVec.ofNat 64 (r - (j + 1)) == 0) = decide (j + 1 = r) := by
    rw [ofNat_beq_zero (by omega_using [hR])]
    exact decide_eq_decide.mpr (by omega_using [hj])
  have gpr₇ : ∀ x, x ≠ .r8 → x ≠ .r9 → x ≠ .r10 → x ≠ .r30 → x ≠ .r31 → s₇.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [gR x h1 h2 h3 h4 h5, hi.gpr x h1 h2 h3 h4 h5]
  by_cases hdone : j + 1 = r
  · refine .inl ⟨by rw [r30₇, hdone, Nat.sub_self]; rfl, fun q hq => ?_, fr₇, rd₇, wr₇, gpr₇⟩
    rw [data₇ q hq, ite_eq_left (by omega_using [hq, hdone])]
  · refine .inr ⟨fun h => ?_, r8₇, r31₇, r30₇, by omega_using [hj, hdone], data₇, fr₇, rd₇, wr₇, gpr₇⟩
    rw [r30₇] at h
    have := congrArg (· == 0) h
    simp only [hz, decide_eq_false hdone] at this
    exact absurd this (by decide)

/-- The loop, from its first byte. -/
theorem tailLoop_wp {s₀ : State} {K R : Addr} {r : Nat} (hp : XPre s₀ K R r) (h0 : XInv s₀ K R r 0 s₀) :
    WP isa (.loop (.block tailByte) (.nonzero .d .r30)) s₀ (XDone s₀ K R r) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = r - j ∧ XInv s₀ K R r j s) (fun m s hs => ?_) r s₀
    ⟨0, by simp, h0⟩
  obtain ⟨j, rfl, hj⟩ := hs
  refine WP.mono (tailByte_wp hp hj) fun s' h => ?_
  rcases h with d | ⟨z, d⟩
  · exact .inl ⟨by rw [eval_nonzero, d.r30]; rfl, d⟩
  · exact .inr ⟨by rw [eval_nonzero]; simpa using z, r - (j + 1),
      by have := d.lt; have := hj.lt; omega_arith, j + 1, rfl, d⟩

/-! ## A step within the `len` bytes

`seq`'s step (`Step.lean`), with the data's area at `Dd = D + e`, `n` steps
of `st` bytes within the `len` bytes at `D` (`FixedF`: the whole blocks, and
the partial segment as one step of `r` bytes), and the key ready for writes
within the `len` bytes and the scratch buffer (`MidF`).
-/

variable {c : Core}

/-- What a run of steps keeps fixed: `Fixed`'s, with the data `n` steps of
`st` bytes at `Dd = D + e`, within the `len` bytes at `D`. -/
structure FixedF (c : Core) (s₀ : State) (B D : Addr) (len : Nat) (Dd : Addr) (n st e : Nat) : Prop where
  scr : ScrIn s₀ B c.total
  dataW : dataRegion D 1 len ∈ s₀.wr
  dataFit : D.toNat + len ≤ 2 ^ 64
  base : Dd = D + BitVec.ofNat 64 e
  inLen : e + st * n ≤ len
  small : len < 2 ^ 64
  dataScr : Region.Disjoint (dataRegion D 1 len) (scrRegion c B)
  step : 0 < st ∧ st ≤ 4 * c.bw
  layout : Layout c

/-- `omega_arith`, with the mode's slots unfolded. -/
local macro "slot_omega" : tactic =>
  `(tactic| plain_simp_names ((try simp only [Core.chnSlot, Core.lrSlot, Core.savedSlot]); omega_arith))

/-- The data's steps, within the `len` bytes. -/
theorem FixedF.sub {s₀ : State} {B D Dd : Addr} {len n st e : Nat} (hF : FixedF c s₀ B D len Dd n st e) :
    Region.Sub (dataRegion Dd st n) (dataRegion D 1 len) := by
  have := hF.inLen
  rw [hF.base]; exact VG.Offset.sub_base _ (by omega_arith)

/-- The regions of a step, as `seq`'s (`regs`). -/
theorem FixedF.regs {s₀ : State} {B D Dd : Addr} {len n st e : Nat} (hF : FixedF c s₀ B D len Dd n st e) {j : Nat}
    (hj : j < n) : Regs c B Dd n st j := by
  have hl := hF.inLen
  have hD := hF.dataFit
  have hsm := hF.small
  have hst := hF.step
  have hn : n ≤ st * n := Nat.le_mul_of_pos_left _ hst.1
  have hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have hDd : Dd.toNat = D.toNat + e := by
    rw [hF.base, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := e) (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
  exact Proof.Modes.PPC64LE.regs (s₀ := { s₀ with wr := dataRegion Dd st n :: s₀.wr })
    ⟨⟨List.mem_cons_of_mem _ hF.scr.wr, hF.scr.fit⟩, List.mem_cons_self, by rw [hDd]; omega_arith,
      hF.dataScr.sub_left hF.sub, by omega_arith, hst, hF.layout⟩ hj

/-- Every byte of the areas at step `j`, as the code addresses them (`areasOk`). -/
theorem FixedF.areasOk {s₀ s : State} {B D Dd : Addr} {len n st e j : Nat} (hF : FixedF c s₀ B D len Dd n st e)
    (hj : j < n) (hb : s.gpr sb = B) (hdp : s.gpr .r31 = Dd + BitVec.ofNat 64 (st * j)) (hwr : s.wr = s₀.wr) :
    AreasOk c s (lens c st) (areas c B Dd st j) allLocs := by
  have hL := hF.layout
  have hfit := hF.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hdisp := hL.disp
  have hst := hF.step
  have hD := hF.dataFit
  have hl := hF.inLen
  have hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  have hb4 : 8 * c.buf + 4 * c.bw ≤ 8 * c.slots :=
    Nat.le_trans (Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hL.G_pos) _) hbuf
  have hW : ∀ l off w, 0 < w → off + w ≤ lens c st l →
      InRegions s.wr (areas c B Dd st j l + BitVec.ofNat 64 off) w := by
    intro l off w hw0 ho
    rw [hwr]
    cases l
    · simp only [lens, areas] at ho ⊢
      refine ⟨_, hF.dataW, ?_⟩
      rw [hF.base, VG.Offset.add_add, VG.Offset.add_add]
      exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
    · simp only [lens, areas] at ho ⊢
      refine ⟨_, hF.scr.wr, ?_⟩
      rw [VG.Offset.add_add]; exact slot_contains hdisp (by slot_omega)
    · simp only [lens, areas] at ho ⊢
      refine ⟨_, hF.scr.wr, ?_⟩
      rw [VG.Offset.add_add]; exact slot_contains hdisp (by omega_using [hroom, hb4, ho])
  refine ⟨fun l off ho => ?_, fun l off ho => ?_, fun l off w hw0 ho => ?_, fun l _ off w hw0 ho => hW l off w hw0 ho,
    fun l l' hne => ?_, fun l => ?_⟩
  · cases l
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hdp, Nat.zero_add]
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hb, VG.Offset.add_add]
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hb, VG.Offset.add_add]
  · cases l
    · simp only [Core.loc, lens] at ho ⊢; omega_using [ho, hst, hbw]
    · simp only [Core.loc, lens] at ho ⊢; slot_omega
    · simp only [Core.loc, lens] at ho ⊢; omega_using [ho, hb4, hroom, hdisp]
  · obtain ⟨r, hr, hc⟩ := hW l off w hw0 ho
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · have dD : ∀ d m, d + m ≤ 8 * c.total →
        Region.Disjoint ⟨Dd + BitVec.ofNat 64 (st * j), st⟩ ⟨B + BitVec.ofNat 64 d, m⟩ :=
      fun d m h => ((hF.dataScr.sub_left hF.sub).sub_left (VG.Offset.sub_base _ hjn)).sub_right (slot_sub h)
    have dCB : Region.Disjoint ⟨slotA B c.chnSlot, 4 * c.bw⟩ ⟨slotA B c.buf, 4 * c.bw⟩ :=
      VG.Offset.disjoint _ (.inr (by slot_omega)) (by slot_omega) (by omega_using [hdisp, hroom, hb4])
    cases l <;> cases l' <;> simp only [ne_eq, not_true_eq_false] at hne <;> simp only [lens, areas]
    · exact dD _ _ (by slot_omega)
    · exact dD _ _ (by omega_using [hroom, hb4])
    · exact (dD _ _ (by slot_omega)).symm
    · exact dCB
    · exact (dD _ _ (by omega_using [hroom, hb4])).symm
    · exact dCB.symm
  · cases l <;> simp only [lens] <;> omega_using [hst, hbw]

/-- The regions the function writes: the `len` bytes and the scratch buffer. -/
abbrev fws (c : Core) (B D : Addr) (len : Nat) : List Region := wrs c B D len 1

/-- A step's areas, within the regions the function writes. -/
theorem FixedF.toWs {s₀ : State} {B D Dd : Addr} {len n st e j : Nat} (hF : FixedF c s₀ B D len Dd n st e)
    (hR : Regs c B Dd n st j) :
    ∀ r ∈ areaRegions (lens c st) (areas c B Dd st j) allLocs, ∃ r' ∈ fws c B D len, Region.Sub r r' := by
  intro r hr
  obtain ⟨r', hr', hs⟩ := hR.areasW r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · exact ⟨_, List.mem_cons_self, fun x hx => hF.sub x (hs x hx)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hs⟩

/-- In the middle of a step from `s` (`Mid`, with the key ready for writes
within the `len` bytes and the scratch buffer). -/
structure MidF (cs : CoreSpec c) (s₀ : State) (B D : Addr) (len : Nat) (Dd : Addr) (st j : Nat) (k : cs.Key)
    (s : State) (a : Areas) (s' : State) : Prop where
  b : s'.gpr sb = B
  kept : ∀ r ∈ kept, s'.gpr r = s.gpr r
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  ready : cs.Ready s' B (fws c B D len) k
  agree : Agree (lens c st) (cont (areas c B Dd st j) s'.mem) a
  frame : Frame (fine c B Dd st j) s.mem s'.mem

/-- `pre`, as `pre_wp`. -/
theorem preF_wp (cs : CoreSpec c) {M : Mode} {s₀ : State} {B D Dd : Addr} {len n st e : Nat} {k : cs.Key}
    (hF : FixedF c s₀ B D len Dd n st e) (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st)) {j : Nat} (hj : j < n)
    {s : State} (hb : s.gpr sb = B) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hdp : s.gpr .r31 = Dd + BitVec.ofNat 64 (st * j)) (hready : cs.Ready s B (fws c B D len) k) :
    WP isa (.block (c.opsCode M.pre)) s
      (MidF cs s₀ B D len Dd st j k s (applyOps M.pre (cont (areas c B Dd st j) s.mem))) := by
  have hR := hF.regs hj
  have hA : AreasOk c s (lens c st) (areas c B Dd st j) allLocs := hF.areasOk hj hb hdp hwr
  rw [← List.append_nil (c.opsCode M.pre)]
  refine VG.PPC64LE.WP.of_syms (opsCode_wp c (ops_ok hpre) hA fun s₂ a₂ f₂ g₂ rd₂ wr₂ => wp_nil fun sy₂ => ?_)
  exact ⟨by rw [g₂ _ (by decide) (by decide)]; exact hb,
    fun r hr => g₂ r (kept_ne r hr).1 (kept_ne r hr).2,
    by rw [rd₂, hrd], by rw [wr₂, hwr],
    cs.ready_frame hready (fun r hr _ _ _ => g₂ r (kept_ne r hr).1 (kept_ne r hr).2) rd₂ wr₂ sy₂ f₂
      (hF.toWs hR) hR.areasCore, a₂,
    f₂.sub hR.areasFine⟩

/-- The core's `crypt`, as `crypt_step`. -/
theorem cryptF_step (cs : CoreSpec c) {s₀ : State} {B D Dd : Addr} {len n st e : Nat} {k : cs.Key}
    (hF : FixedF c s₀ B D len Dd n st e) {j : Nat} (hj : j < n) {s s₂ : State} {a : Areas}
    (hm : MidF cs s₀ B D len Dd st j k s a s₂) :
    WP isa c.crypt s₂ (MidF cs s₀ B D len Dd st j k s (cryptBuf (4 * c.bw) (cs.cipher k) a)) := by
  have hR := hF.regs hj
  have hst := hF.step
  have hbw : c.bw ≤ 4 := by rcases hF.layout.bw with h | h <;> omega_using [h]
  refine WP.mono (cs.crypt_wp hm.b ⟨by rw [hm.wr]; exact hF.scr.wr, hF.scr.fit⟩ hm.ready)
    fun s₃ ⟨b₃, kept₃, ready₃, f₃, enc₃, rd₃, wr₃⟩ => ?_
  refine ⟨b₃, fun r hr => by rw [kept₃ r hr, hm.kept r hr], by rw [rd₃, hm.rd], by rw [wr₃, hm.wr], ready₃, ?_,
    hm.frame.trans (f₃.sub fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)⟩
  refine Agree.trans (b := cryptBuf (4 * c.bw) (cs.cipher k) (cont (areas c B Dd st j) s₂.mem)) ?_
    (cryptBuf_agree (by simp [lens]) _ hm.agree)
  intro l i hi
  cases l
  · simp only [cryptBuf, cont, areas, lens] at hi ⊢
    exact f₃.bytes (R := datRegion Dd st j) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hR.datCore) (by show st ≤ 2 ^ 64; omega_using [hst, hbw]) hi
  · simp only [cryptBuf, cont, areas, lens] at hi ⊢
    exact f₃.bytes (R := chnRegion c B) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hR.chnCore) (by show 4 * c.bw ≤ 2 ^ 64; omega_using [hbw]) hi
  · simp only [lens] at hi
    have e := enc₃ 0 hF.layout.G_pos
    rw [blkAddr_zero] at e
    simp only [cryptBuf, cont, areas, ite_true]
    rw [← bytesAt_getD s₃.mem (slotA B c.buf) hi, e]
    rfl

/-- A register write that no `kept` register and no area's base sees. -/
theorem MidF.congr {cs : CoreSpec c} {s₀ s s₁ s₂ : State} {B D Dd : Addr} {len st j : Nat} {k : cs.Key}
    {a : Areas} (h : MidF cs s₀ B D len Dd st j k s a s₁) (hb : s₂.gpr sb = s₁.gpr sb)
    (hk : ∀ r ∈ Proof.Modes.PPC64LE.kept, s₂.gpr r = s₁.gpr r) (hm : s₂.mem = s₁.mem) (hrd : s₂.rd = s₁.rd) (hwr : s₂.wr = s₁.wr)
    (hsy : s₂.syms = s₁.syms) : MidF cs s₀ B D len Dd st j k s a s₂ :=
  ⟨by rw [hb]; exact h.b, fun r hr => by rw [hk r hr]; exact h.kept r hr, by rw [hrd]; exact h.rd,
    by rw [hwr]; exact h.wr,
    cs.ready_frame (rs := []) h.ready (fun r hr _ _ _ => hk r hr) hrd hwr hsy (fun x _ => by rw [hm])
      (fun _ h => nomatch h) (fun _ h => nomatch h),
    by rw [hm]; exact h.agree, by rw [hm]; exact h.frame⟩

end VG.Proof.Modes.PPC64LE
