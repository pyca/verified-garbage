module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Lookup
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Lookup
meta import VerifiedGarbage.Proof.Rc2.Memory
meta import VerifiedGarbage.Proof.Rc2.CbcMemory
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Lit
public import VerifiedGarbage.Impl.Rc2.PPC64LE.Cbc
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Rc2.CbcList
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Block
import VerifiedGarbage.Proof.Rc2.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Block
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.Proof.Rc2.CbcList
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Impl.Rc2.PPC64LE.Cbc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline

/-! ### `Rc2.PPC64LE.Cbc.Body`, which only this module used -/

section

/-! ### `Rc2.PPC64LE.Cbc.Call`, which only this module used -/

section

/-! # RC2-CBC on PPC64LE: the calls of the block function -/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE.Cbc

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE VG.Impl.Rc2.PPC64LE.Cbc

theorem block_exec (d : Spec.Rc2.Direction) : ∀ s, (blockC d).pre s →
    ∃ t s', Exec isa (blockCode d) s t s' ∧ abiPreserved s s' ∧ (blockC d).post s s' := by
  cases d
  · exact block_ok .encrypt (by lit_decide) (by lit_decide) (by rw [← Code.allInstrs_eq]; lit_decide)
  · exact block_ok .decrypt (by lit_decide) (by lit_decide) (by rw [← Code.allInstrs_eq]; lit_decide)

theorem blockCall_eq (d : Spec.Rc2.Direction) :
    ∃ nm, blockCall d = .call nm (blockCode d) := by cases d <;> exact ⟨_, rfl⟩

theorem blockCode_noFrames (d : Spec.Rc2.Direction) : (blockCode d).noFrames = true := by
  cases d
  · exact (by lit_decide : encryptBlock.noFrames = true)
  · exact (by lit_decide : decryptBlock.noFrames = true)

/-- A call of the block function on the block at `p`, with the schedule at
`T` and the working space at `W`. -/
theorem call_run (d : Spec.Rc2.Direction) (u : State) {T p W : Addr} (h3 : u.gpr .r3 = T) (h4 : u.gpr .r4 = p)
    (h5 : u.gpr .r5 = W) (hc : Covers ([⟨T, 128⟩] ++ [⟨p, 8⟩, ⟨W, 256⟩]) (u.rd ++ u.wr))
    (hw : Covers [⟨p, 8⟩, ⟨W, 256⟩] u.wr) :
    WP isa (blockCall d) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
      Frame [⟨p, 8⟩, ⟨W, 256⟩] u.mem u'.mem ∧ (∀ r ∈ preserved, u'.gpr r = u.gpr r) ∧
      Spec.Rc2.blockAt u'.mem p = cipher d (Spec.Rc2.scheduleAt u.mem T) (Spec.Rc2.blockAt u.mem p) := by
  obtain ⟨nm, e⟩ := blockCall_eq d
  rw [e]
  refine WP.call (k := blockC d) (block_exec d) (rd := [⟨T, 128⟩]) (wr := [⟨p, 8⟩, ⟨W, 256⟩]) ?_ hc hw
    (fun s' hr hwr _ hf hp _ hpost => ⟨hr, hwr, hf, hp, ?_⟩) (blockCode_noFrames d)
  · show [(⟨T, 128⟩ : Region)] = [⟨u.callEntry.gpr .r3, 128⟩] ∧
      [(⟨p, 8⟩ : Region), ⟨W, 256⟩] = [⟨u.callEntry.gpr .r4, 8⟩, ⟨u.callEntry.gpr .r5, 256⟩]
    rw [State.callEntry_gpr u (by decide), State.callEntry_gpr u (by decide), State.callEntry_gpr u (by decide),
      h3, h4, h5]
    exact ⟨rfl, rfl⟩
  · have := hpost
    simp only [blockC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem] at this
    rw [State.callEntry_gpr u (by decide), State.callEntry_gpr u (by decide), h3, h4] at this
    exact this

end VG.Proof.Rc2.PPC64LE.Cbc

end

end

/-! ### `Rc2.PPC64LE.Cbc.Step`, which only this module used -/

section

/-!
# RC2-CBC on PPC64LE: one block

`body_run`: an iteration of the loop takes the invariant `Inv` from `j` blocks
done to `j + 1`.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE.Cbc

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE VG.Impl.Rc2.PPC64LE.Cbc

/-- The buffers: the schedule at `T`, the chaining value at `I`, `n` blocks
at `D` and the working space at `W`, apart. -/
structure Regions (T I D W : Addr) (n : Nat) : Prop where
  TI : (⟨T, 128⟩ : Region).Disjoint ⟨I, 8⟩
  TD : (⟨T, 128⟩ : Region).Disjoint ⟨D, 8 * n⟩
  TW : (⟨T, 128⟩ : Region).Disjoint ⟨W, 512⟩
  ID : (⟨I, 8⟩ : Region).Disjoint ⟨D, 8 * n⟩
  IW : (⟨I, 8⟩ : Region).Disjoint ⟨W, 512⟩
  DW : (⟨D, 8 * n⟩ : Region).Disjoint ⟨W, 512⟩
  fit : 8 * n ≤ 2 ^ 64

/-- After `j` of the `n` blocks, from memory `m₀` and with our caller's
registers `g`. -/
structure Inv (d : Spec.Rc2.Direction) (T I D W : Addr) (n : Nat) (g : Reg → BitVec 64) (m₀ : Mem)
    (s₀ : State) (j : Nat) (t : State) : Prop where
  rd : t.rd = [⟨T, 128⟩]
  wr : t.wr = [⟨I, 8⟩, ⟨D, 8 * n⟩, ⟨W, 512⟩]
  r26 : t.gpr .r26 = T
  r27 : t.gpr .r27 = I
  r28 : t.gpr .r28 = D + BitVec.ofNat 64 (8 * j)
  r29 : t.gpr .r29 = BitVec.ofNat 64 (n - j)
  r30 : t.gpr .r30 = W
  pres : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → t.gpr r = s₀.gpr r
  saved : Spill.Saved W g saved t.mem
  sched : Spec.Rc2.scheduleAt t.mem T = Spec.Rc2.scheduleAt m₀ T
  done : Spec.Rc2.blocksAt t.mem D j =
    (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt m₀ T) d (Spec.Rc2.blockAt m₀ I) (Spec.Rc2.blocksAt m₀ D j)).1
  iv : Spec.Rc2.blockAt t.mem I =
    (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt m₀ T) d (Spec.Rc2.blockAt m₀ I) (Spec.Rc2.blocksAt m₀ D j)).2
  rest : ∀ i, j ≤ i → i < n → Spec.Rc2.blockAt t.mem (D + BitVec.ofNat 64 (8 * i)) =
    Spec.Rc2.blockAt m₀ (D + BitVec.ofNat 64 (8 * i))

theorem saved_fits : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide
theorem saved_in : ∀ p ∈ saved, 256 ≤ p.2 ∧ p.2 + 8 ≤ 312 := by decide

/-- What a step leaves alone: anything apart from the block, the chaining
value and the block function's working space. -/
theorem step_frame {T I D W : Addr} {n j : Nat} (R : Regions T I D W n) (hj : j < n) {m m' : Mem}
    (F : Frame [⟨D + BitVec.ofNat 64 (8 * j), 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] m m') :
    Spec.Rc2.scheduleAt m' T = Spec.Rc2.scheduleAt m T ∧
    (∀ g, Spill.Saved W g saved m → Spill.Saved W g saved m') ∧
    (∀ i, i < n → i ≠ j → Spec.Rc2.blockAt m' (D + BitVec.ofNat 64 (8 * i)) =
      Spec.Rc2.blockAt m (D + BitVec.ofNat 64 (8 * i))) ∧
    Spec.Rc2.blocksAt m' D j = Spec.Rc2.blocksAt m D j := by
  have hf := R.fit
  obtain bj : Region.Sub ⟨D + BitVec.ofNat 64 (8 * j), 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega_using [hj])
  obtain W256 : Region.Sub ⟨W, 256⟩ ⟨W, 512⟩ := Region.sub_prefix (by decide)
  refine ⟨Proof.Rc2.scheduleAt_frame F T ?_, fun g sv => sv.frame F ?_, fun i hi hne => Proof.Rc2.blockAt_frame F _ ?_,
    Proof.Rc2.blocksAt_frame F D j ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact R.TD.sub_right bj
    · exact R.TI
    · exact R.TW.sub_right W256
  · intro p hp r hr
    obtain hb := saved_in p hp
    obtain slot : Region.Sub ⟨W + BitVec.ofNat 64 p.2, 8⟩ ⟨W, 512⟩ := Offset.sub_base W (by omega_using [hb])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (R.DW.sub_left bj).symm.sub_left slot
    · exact (R.IW.symm.sub_left slot)
    · exact Offset.disjoint_base W (by omega_using [hb]) (by omega_using [hb])
  · have bi : Region.Sub ⟨D + BitVec.ofNat 64 (8 * i), 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega_using [hi])
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact Offset.disjoint D (by omega_using [hne]) (by omega_using [hf, hi]) (by omega_using [hj, hf])
    · exact (R.ID.sub_right bi).symm
    · exact (R.DW.sub_left bi).sub_right W256
  · have bp : Region.Sub ⟨D, 8 * j⟩ ⟨D, 8 * n⟩ := Region.sub_prefix (by omega_using [hj])
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact Offset.base_disjoint D (by omega_using []) (by omega_using [hj, hf])
    · exact (R.ID.sub_right bp).symm
    · exact (R.DW.sub_left bp).sub_right W256

theorem blocksAt_one (m : Mem) (p : Addr) : Spec.Rc2.blocksAt m p 1 = [Spec.Rc2.blockAt m p] := by
  simp [Spec.Rc2.blocksAt]

/-- The done blocks, one more. -/
theorem done_succ (m : Mem) (D : Addr) (j : Nat) :
    Spec.Rc2.blocksAt m D (j + 1) = Spec.Rc2.blocksAt m D j ++ [Spec.Rc2.blockAt m (D + BitVec.ofNat 64 (8 * j))] := by
  rw [Proof.Rc2.blocksAt_add, blocksAt_one]

theorem covers {T I D W : Addr} {n j : Nat} (hj : j < n) :
    Covers ([⟨T, 128⟩] ++ [⟨D + BitVec.ofNat 64 (8 * j), 8⟩, ⟨W, 256⟩])
      ([⟨T, 128⟩] ++ [⟨I, 8⟩, ⟨D, 8 * n⟩, ⟨W, 512⟩]) := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨⟨D, 8 * n⟩, by simp, 8 * j, rfl, by simp; omega_using [hj]⟩
  · exact ⟨⟨W, 512⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩

theorem covers_wr {I D W : Addr} {n j : Nat} (hj : j < n) :
    Covers [⟨D + BitVec.ofNat 64 (8 * j), 8⟩, ⟨W, 256⟩] [⟨I, 8⟩, ⟨D, 8 * n⟩, ⟨W, 512⟩] := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨D, 8 * n⟩, by simp, 8 * j, rfl, by simp; omega_using [hj]⟩
  · exact ⟨⟨W, 512⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩

end VG.Proof.Rc2.PPC64LE.Cbc

end

end


/-! # RC2-CBC on PPC64LE: an iteration of the loop -/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE.Cbc

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE VG.Impl.Rc2.PPC64LE.Cbc

theorem count_sub {n j : Nat} (hj : j < n) :
    BitVec.ofNat 64 (n - j) - 1#64 = BitVec.ofNat 64 (n - (j + 1)) := by
  rw [Offset.ofNat_sub_ofNat (by omega_using [hj])]; congr 1

theorem preserved_not : ∀ r ∈ preserved, r ∉ saved.map Prod.fst →
    r ∉ [Reg.r3, .r4, .r5, .r10, .r11, .r28, .r29, .r31] := by decide

theorem enc_spec (k : Spec.Rc2.Schedule) (iv b : Spec.Rc2.Block) :
    Proof.Rc2.cbcBlocks k .encrypt iv [b] =
      ([Spec.Rc2.encryptBlock k (Proof.Rc2.xorBlock b iv)], Spec.Rc2.encryptBlock k (Proof.Rc2.xorBlock b iv)) := rfl

theorem dec_spec (k : Spec.Rc2.Schedule) (iv b : Spec.Rc2.Block) :
    Proof.Rc2.cbcBlocks k .decrypt iv [b] = ([Proof.Rc2.xorBlock (Spec.Rc2.decryptBlock k b) iv], b) := rfl

theorem body_run (d : Spec.Rc2.Direction) {T I D W : Addr} {n : Nat} {g : Reg → BitVec 64} {m₀ : Mem} {s₀ : State}
    (R : Regions T I D W n) {j : Nat} (hj : j < n) (t : State) (H : Inv d T I D W n g m₀ s₀ j t) :
    WP isa (body d) t fun t' => Inv d T I D W n g m₀ s₀ (j + 1) t' ∧
      (t'.gpr .r29 != 0#64) = !decide (j + 1 = n) := by
  have hf := R.fit
  let p := D + BitVec.ofNat 64 (8 * j)
  obtain pIn : InRegions t.wr p 8 := by
    rw [H.wr]; exact ⟨⟨D, 8 * n⟩, by simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj, hf])⟩
  obtain pIn' : InRegions (t.rd ++ t.wr) p 8 := by
    obtain ⟨r, hr, hc⟩ := pIn; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain iIn : InRegions t.wr I 8 := by rw [H.wr]; exact ⟨⟨I, 8⟩, by simp, Region.contains_self _ _⟩
  obtain iIn' : InRegions (t.rd ++ t.wr) I 8 := by
    obtain ⟨r, hr, hc⟩ := iIn; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain bj : Region.Sub ⟨p, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega_using [hj])
  obtain pI : (⟨p, 8⟩ : Region).Disjoint ⟨I, 8⟩ := (R.ID.sub_right bj).symm
  have r28 : t.gpr .r28 = p := H.r28
  obtain b₀ : Spec.Rc2.blockAt t.mem p = Spec.Rc2.blockAt m₀ p := H.rest j (Nat.le_refl _) hj
  obtain spec := Proof.Rc2.cbc_append (Spec.Rc2.scheduleAt m₀ T) d (Spec.Rc2.blockAt m₀ I)
    (Spec.Rc2.blocksAt m₀ D j) [Spec.Rc2.blockAt m₀ p]
  unfold body
  cases d with
  | encrypt =>
    apply WP.seq
    refine WP.mono (WP.keep [.r3, .r4, .r5, .r10, .r11] (c := .block (before .encrypt)) (Q := fun t₁ =>
        t₁.gpr .r3 = T ∧ t₁.gpr .r4 = p ∧ t₁.gpr .r5 = W ∧
        t₁.mem = t.mem.writeW p (t.mem.readW p 64 ^^^ t.mem.readW I 64))
      (by unfold before xorIv args; rrun [mov, H.r26, H.r27, r28, H.r30, pIn, pIn', iIn'])
      (by rfl) rfl)
      fun t₁ ⟨⟨a3, a4, a5, m₁⟩, k₁⟩ => ?_
    apply WP.seq
    refine WP.mono (call_run .encrypt t₁ a3 a4 a5 (by rw [k₁.2.1, k₁.2.2, H.rd, H.wr]; exact covers hj)
      (by rw [k₁.2.2, H.wr]; exact covers_wr hj)) fun t₂ ⟨rd₂, wr₂, F₂, P₂, c₂⟩ => ?_
    obtain g2 : ∀ r, r ∈ preserved → r ∉ [Reg.r3, .r4, .r5, .r10, .r11] → t₂.gpr r = t.gpr r := fun r hr hn => by
      rw [P₂ r hr, k₁.gpr hn]
    obtain h27 : t₂.gpr .r27 = I := by rw [g2 _ (by decide) (by decide), H.r27]
    obtain h28 : t₂.gpr .r28 = p := by rw [g2 _ (by decide) (by decide), H.r28]
    obtain h29 : t₂.gpr .r29 = BitVec.ofNat 64 (n - j) := by rw [g2 _ (by decide) (by decide), H.r29]
    obtain pIn₂ : InRegions (t₂.rd ++ t₂.wr) p 8 := by rw [rd₂, wr₂, k₁.2.1, k₁.2.2]; exact pIn'
    obtain iIn₂ : InRegions t₂.wr I 8 := by rw [wr₂, k₁.2.2]; exact iIn
    refine WP.mono (WP.keep [.r10, .r28, .r29] (c := .block (after .encrypt ++ advance)) (Q := fun t₃ =>
        t₃.gpr .r28 = p + 8#64 ∧ t₃.gpr .r29 = BitVec.ofNat 64 (n - j) - 1#64 ∧
        t₃.mem = t₂.mem.writeW I (t₂.mem.readW p 64))
      (by unfold after advance; rrun [h27, h28, h29, pIn₂, iIn₂])
      (by rfl) rfl)
      fun t₃ ⟨⟨a28, a29, m₃⟩, k₃⟩ => ?_
    -- the frame of the whole step
    obtain F : Frame [⟨p, 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] t.mem t₃.mem := by
      refine Frame.trans (Frame.trans ?_ (F₂.mono (by simp))) ?_
      · rw [m₁]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
      · rw [m₃]; exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
    obtain ⟨fS, fV, fB, fD⟩ := step_frame R hj F
    -- the new block and chaining value
    obtain out : Spec.Rc2.blockAt t₂.mem p =
        Spec.Rc2.encryptBlock (Spec.Rc2.scheduleAt m₀ T) (Proof.Rc2.xorBlock (Spec.Rc2.blockAt m₀ p)
          (Spec.Rc2.blockAt t.mem I)) := by
      obtain hs₁ : Spec.Rc2.scheduleAt t₁.mem T = Spec.Rc2.scheduleAt m₀ T := by
        rw [m₁, Proof.Rc2.scheduleAt_frame (Proof.Rc2.frame_store64 _ _ _) T (by simpa using R.TD.sub_right bj),
          H.sched]
      rw [c₂, hs₁, m₁, Proof.Rc2.blockAt_xor, b₀]; rfl
    obtain b₃ : Spec.Rc2.blockAt t₃.mem p = Spec.Rc2.blockAt t₂.mem p := by
      rw [m₃]; exact Proof.Rc2.blockAt_frame (Proof.Rc2.frame_store64 _ _ _) _ (by simpa using pI)
    obtain i₃ : Spec.Rc2.blockAt t₃.mem I = Spec.Rc2.blockAt t₂.mem p := by rw [m₃, Proof.Rc2.blockAt_copy]
    refine ⟨⟨by rw [k₃.2.1, rd₂, k₁.2.1, H.rd], by rw [k₃.2.2, wr₂, k₁.2.2, H.wr],
      by rw [k₃.gpr (by decide), g2 _ (by decide) (by decide), H.r26], by rw [k₃.gpr (by decide), h27],
      by rw [a28, Offset.add_add]; congr 2,
      by rw [a29, count_sub hj], by rw [k₃.gpr (by decide), g2 _ (by decide) (by decide), H.r30],
      fun r hr hn => ?_, fV g H.saved, by rw [fS, H.sched], ?_, ?_, fun i hi hn => ?_⟩, ?_⟩
    · have hn' := preserved_not r hr hn
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn'
      rw [k₃.gpr (by simp [hn']), g2 r hr (by simp [hn']), H.pres r hr hn]
    · rw [done_succ, done_succ, fD, H.done, spec, enc_spec, ← H.iv, b₃, out]
    · rw [done_succ, spec, enc_spec, ← H.iv, i₃, out]
    · rw [fB i hn (by omega_using [hi]), H.rest i (by omega_using [hi]) hn]
    · rw [a29, count_sub hj, ofNat_bne_zero (by omega_using [hf])]
      congr 1
      exact decide_eq_decide.mpr (by omega_using [hj])
  | decrypt =>
    apply WP.seq
    refine WP.mono (WP.keep [.r3, .r4, .r5, .r31] (c := .block (before .decrypt)) (Q := fun t₁ =>
        t₁.gpr .r3 = T ∧ t₁.gpr .r4 = p ∧ t₁.gpr .r5 = W ∧ t₁.gpr .r31 = t.mem.readW p 64 ∧ t₁.mem = t.mem)
      (by unfold before args; rrun [mov, H.r26, r28, H.r30, pIn'])
      (by rfl) rfl)
      fun t₁ ⟨⟨a3, a4, a5, a31, m₁⟩, k₁⟩ => ?_
    apply WP.seq
    refine WP.mono (call_run .decrypt t₁ a3 a4 a5 (by rw [k₁.2.1, k₁.2.2, H.rd, H.wr]; exact covers hj)
      (by rw [k₁.2.2, H.wr]; exact covers_wr hj)) fun t₂ ⟨rd₂, wr₂, F₂, P₂, c₂⟩ => ?_
    obtain g2 : ∀ r, r ∈ preserved → r ∉ [Reg.r3, .r4, .r5, .r31] → t₂.gpr r = t.gpr r := fun r hr hn => by
      rw [P₂ r hr, k₁.gpr hn]
    obtain h27 : t₂.gpr .r27 = I := by rw [g2 _ (by decide) (by decide), H.r27]
    obtain h28 : t₂.gpr .r28 = p := by rw [g2 _ (by decide) (by decide), H.r28]
    obtain h29 : t₂.gpr .r29 = BitVec.ofNat 64 (n - j) := by rw [g2 _ (by decide) (by decide), H.r29]
    obtain h31 : t₂.gpr .r31 = t.mem.readW p 64 := by rw [P₂ _ (by decide), a31]
    obtain pIn₂ : InRegions (t₂.rd ++ t₂.wr) p 8 := by rw [rd₂, wr₂, k₁.2.1, k₁.2.2]; exact pIn'
    obtain pW₂ : InRegions t₂.wr p 8 := by rw [wr₂, k₁.2.2]; exact pIn
    obtain iIn₂ : InRegions t₂.wr I 8 := by rw [wr₂, k₁.2.2]; exact iIn
    obtain iIn₂' : InRegions (t₂.rd ++ t₂.wr) I 8 := by rw [rd₂, wr₂, k₁.2.1, k₁.2.2]; exact iIn'
    refine WP.mono (WP.keep [.r10, .r11, .r28, .r29] (c := .block (after .decrypt ++ advance)) (Q := fun t₃ =>
        t₃.gpr .r28 = p + 8#64 ∧ t₃.gpr .r29 = BitVec.ofNat 64 (n - j) - 1#64 ∧
        t₃.mem = (t₂.mem.writeW p (t₂.mem.readW p 64 ^^^ t₂.mem.readW I 64)).writeW I (t.mem.readW p 64))
      (by unfold after xorIv advance; rrun [h27, h28, h29, h31, pIn₂, pW₂, iIn₂, iIn₂'])
      (by rfl) rfl)
      fun t₃ ⟨⟨a28, a29, m₃⟩, k₃⟩ => ?_
    obtain F : Frame [⟨p, 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] t.mem t₃.mem := by
      rw [← m₁]
      refine Frame.trans (F₂.mono (by simp)) ?_
      rw [m₃]
      obtain f₁ : Frame [⟨p, 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] t₂.mem
          (t₂.mem.writeW p (t₂.mem.readW p 64 ^^^ t₂.mem.readW I 64)) :=
        (Frame.refl _ _).writeW (r := ⟨p, 8⟩) (by simp) _ (Region.contains_self _ _)
      exact f₁.writeW (r := ⟨I, 8⟩) (by simp) _ (Region.contains_self _ _)
    obtain ⟨fS, fV, fB, fD⟩ := step_frame R hj F
    obtain i₂ : Spec.Rc2.blockAt t₂.mem I = Spec.Rc2.blockAt t.mem I := by
      rw [Proof.Rc2.blockAt_frame F₂ I (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact pI.symm
        · exact R.IW.sub_right (Region.sub_prefix (by decide))), m₁]
    obtain hs₁ : Spec.Rc2.scheduleAt t₁.mem T = Spec.Rc2.scheduleAt m₀ T := by rw [m₁, H.sched]
    obtain b₃ : Spec.Rc2.blockAt t₃.mem p =
        Proof.Rc2.xorBlock (Spec.Rc2.decryptBlock (Spec.Rc2.scheduleAt m₀ T) (Spec.Rc2.blockAt m₀ p))
          (Spec.Rc2.blockAt t.mem I) := by
      rw [m₃, Proof.Rc2.blockAt_frame (Proof.Rc2.frame_store64 _ _ _) _ (by simpa using pI),
        Proof.Rc2.blockAt_xor, i₂, c₂, hs₁, m₁, b₀]; rfl
    obtain i₃ : Spec.Rc2.blockAt t₃.mem I = Spec.Rc2.blockAt m₀ p := by
      rw [m₃, Proof.Rc2.blockAt_store64, ← Proof.Rc2.blockAt_read64, b₀]
    refine ⟨⟨by rw [k₃.2.1, rd₂, k₁.2.1, H.rd], by rw [k₃.2.2, wr₂, k₁.2.2, H.wr],
      by rw [k₃.gpr (by decide), g2 _ (by decide) (by decide), H.r26], by rw [k₃.gpr (by decide), h27],
      by rw [a28, Offset.add_add]; congr 2,
      by rw [a29, count_sub hj], by rw [k₃.gpr (by decide), g2 _ (by decide) (by decide), H.r30],
      fun r hr hn => ?_, fV g H.saved, by rw [fS, H.sched], ?_, ?_, fun i hi hn => ?_⟩, ?_⟩
    · have hn' := preserved_not r hr hn
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn'
      rw [k₃.gpr (by simp [hn']), g2 r hr (by simp [hn']), H.pres r hr hn]
    · rw [done_succ, done_succ, fD, H.done, spec, dec_spec, ← H.iv, b₃]
    · rw [done_succ, spec, dec_spec, i₃]
    · rw [fB i hn (by omega_using [hi]), H.rest i (by omega_using [hi]) hn]
    · rw [a29, count_sub hj, ofNat_bne_zero (by omega_using [hf])]
      congr 1
      exact decide_eq_decide.mpr (by omega_using [hj])

end VG.Proof.Rc2.PPC64LE.Cbc

end

end

/-! # Verified RC2-CBC on PPC64LE -/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE.Cbc

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE VG.Impl.Rc2.PPC64LE.Cbc

/-- The CBC contract as the code sees it. -/
def cbcC (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 128⟩
    let iv : Region := ⟨s.gpr .r4, 8⟩
    let data : Region := ⟨s.gpr .r5, 8 * (s.gpr .r6).toNat⟩
    let buf : Region := ⟨s.gpr .r7, 512⟩
    s.rd = [key] ∧ s.wr = [iv, data, buf] ∧ key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧
      (s.gpr .r5).toNat + 8 * (s.gpr .r6).toNat ≤ 2 ^ 64
  post s s' :=
    let result := Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt s.mem (s.gpr .r3)) d (Spec.Rc2.blockAt s.mem (s.gpr .r4))
      (Spec.Rc2.blocksAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    Spec.Rc2.blocksAt s'.mem (s.gpr .r5) (s.gpr .r6).toNat = result.1 ∧
      Spec.Rc2.blockAt s'.mem (s.gpr .r4) = result.2
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

theorem save_eq : save = .mflr .r0 :: Spill.saveCode .r7 saved := rfl
theorem restore_eq : restore = Spill.restoreCode .r30 saved ++ ([.mtlr .r0] : List Instr) := rfl

theorem cbc_wp (d : Spec.Rc2.Direction) (s : State) (hs : (cbcC d).pre s) :
    WP isa (cbc d) s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.lr = s.lr ∧ (cbcC d).post s s' := by
  obtain ⟨hrd, hwr, TI, TD, TW, ID, IW, DW, fit⟩ := hs
  let T := s.gpr .r3
  let I := s.gpr .r4
  let D := s.gpr .r5
  let n := (s.gpr .r6).toNat
  let W := s.gpr .r7
  have R : Regions T I D W n := ⟨TI, TD, TW, ID, IW, DW, by omega_arith⟩
  let s₁ := s.write .r0 s.lr
  let g := s₁.gpr
  have wW : ∀ p ∈ saved, InRegions s₁.wr (s₁.gpr .r7 + BitVec.ofNat 64 p.2) 8 := fun p hp => by
    have hb := saved_in p hp
    show InRegions s.wr (W + BitVec.ofNat 64 p.2) 8
    rw [hwr]; exact ⟨⟨W, 512⟩, by simp [W], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  unfold cbc
  apply WP.seq
  rw [save_eq, List.cons_append]
  refine WP.block_cons_iff.mpr ⟨s₁, exec_mflr, ?_⟩
  refine Spill.save_ok (by decide) saved_fits wW ?_
  let M₀ := Spill.saveMem s₁.mem (s₁.gpr .r7) g saved
  have F₀ : Frame [⟨W, 512⟩] s.mem M₀ := Spill.saveMem_frame_base (fun p hp => by have := saved_in p hp; omega_arith)
    (by decide) _ _ _
  refine WP.mono (WP.keep [.r26, .r27, .r28, .r29, .r30] (c := .block setup) (Q := fun t =>
      t.gpr .r26 = T ∧ t.gpr .r27 = I ∧ t.gpr .r28 = D ∧ t.gpr .r29 = s.gpr .r6 ∧ t.gpr .r30 = W ∧ t.mem = M₀)
    (by unfold setup; rrun [mov, s₁, T, I, D, W, M₀, g]) (by rfl) rfl)
    fun t₀ ⟨⟨a26, a27, a28, a29, a30, m₀⟩, k₀⟩ => ?_
  have H₀ : Inv d T I D W n g M₀ s 0 t₀ := by
    refine ⟨by rw [k₀.2.1]; exact hrd, by rw [k₀.2.2]; exact hwr, a26, a27, by rw [a28]; simp, by
      rw [a29, Nat.sub_zero]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm, a30,
      fun r hr hn => ?_, by rw [m₀]; exact Spill.saveMem_saved (by decide) _ _ _, by rw [m₀], by rw [m₀]; rfl,
      by rw [m₀]; rfl, fun i _ _ => by rw [m₀]⟩
    have hr0 : r ≠ .r0 := by revert r; decide
    rw [k₀.gpr (by revert hn; revert r; decide)]
    simp only [s₁, State.write, hr0, ite_false]
  apply WP.seq
  have loop : WP isa (.ite (.zero .d .r29) (.block []) (.loop (body d) (.nonzero .d .r29))) t₀
      (Inv d T I D W n g M₀ s n) := by
    have hz : isa.eval (.zero .d .r29) t₀ = some (decide (n = 0)) := by
      rw [eval_zero, H₀.r29, Nat.sub_zero, ofNat_beq_zero (by omega_arith)]
    refine WP.ite _ hz (fun h => WP.block_nil ?_) (fun h => countLoop _ _ _ n
      (fun j hj t H => body_run d R hj t H) 0 (by have := of_decide_eq_false h; omega_arith) t₀ H₀)
    have e : n = 0 := of_decide_eq_true h
    rw [e]; rw [e] at H₀; exact H₀
  refine WP.mono loop fun t H => ?_
  rw [restore_eq, WP.block_append_iff]
  refine WP.mono (Spill.restore_wp (by decide) H.r30 saved_fits (by decide) (fun p hp => ?_) H.saved)
    fun t' Rs => WP.block_cons_iff.mpr ⟨_, exec_mtlr, WP.block_nil ⟨fun r hr => ?_, ?_, ?_⟩⟩
  · have hb := saved_in p hp
    rw [H.rd, H.wr]
    exact ⟨⟨W, 512⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · show t'.gpr r = s.gpr r
    by_cases h : r ∈ saved.map Prod.fst
    · have hr0 : r ≠ .r0 := by revert r; decide
      rw [Rs.gpr_of (.inl h)]
      simp only [g, s₁, State.write, hr0, ite_false]
    · rw [Rs.other r h, H.pres r hr h]
  · show t'.gpr .r0 = s.lr
    rw [Rs.gpr (.r0, 304) (by decide)]
    simp [g, s₁, State.write]
  · have hS : Spec.Rc2.scheduleAt M₀ T = Spec.Rc2.scheduleAt s.mem T :=
      Proof.Rc2.scheduleAt_frame F₀ T (by simpa using TW)
    have hI : Spec.Rc2.blockAt M₀ I = Spec.Rc2.blockAt s.mem I := Proof.Rc2.blockAt_frame F₀ I (by simpa using IW)
    have hD : Spec.Rc2.blocksAt M₀ D n = Spec.Rc2.blocksAt s.mem D n :=
      Proof.Rc2.blocksAt_frame F₀ D n (by simpa using DW)
    show Spec.Rc2.blocksAt t'.mem D n = _ ∧ Spec.Rc2.blockAt t'.mem I = _
    rw [Rs.mem, H.done, H.iv, hS, hI, hD]
    exact ⟨rfl, rfl⟩

theorem cbc_ok (d : Spec.Rc2.Direction) (s : State) (hs : (cbcC d).pre s) :
    ∃ t s', Exec isa (cbc d) s t s' ∧ abiPreserved s s' ∧ (cbcC d).post s s' := by
  obtain ⟨t, s', he, hp, hl, hq⟩ := cbc_wp d s hs
  exact ⟨t, s', he, ⟨hp, Exec.sp he, hl⟩, hq⟩

end VG.Proof.Rc2.PPC64LE.Cbc
