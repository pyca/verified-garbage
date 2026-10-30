module

public import VerifiedGarbage.Impl.TripleDes.AArch64.Cbc
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Block
public import VerifiedGarbage.Proof.Modes.CbcEnc
public import VerifiedGarbage.Proof.TripleDes.CbcScratch
import VerifiedGarbage.Proof.TripleDes.CbcBlocks
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Update
import VerifiedGarbage.Proof.CmacTripleDes.Bytes
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Modes.CbcNext
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Cbc
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: the CBC loop proof reuses the expensive CMAC block proof and is independent of the scalar mode proofs.

@[expose] public section

namespace VG.Impl.TripleDes.AArch64.TablesCbc
materialize_code encrypt
end VG.Impl.TripleDes.AArch64.TablesCbc

namespace VG.Proof.TripleDes.AArch64.TablesCbc

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.CmacTripleDes.AArch64
open VG.Impl.TripleDes.AArch64.TablesCbc
open VG.Proof.CmacTripleDes VG.Proof.CmacTripleDes.AArch64
open VG.Proof.Modes
open VG.Proof.Cmac

abbrev W (s : State) : Addr := s.gpr .x0
abbrev P (s : State) : Addr := s.gpr .x1
abbrev D (s : State) : Addr := s.gpr .x2
abbrev N (s : State) : Nat := (s.gpr .x3).toNat
abbrev S (s : State) : Addr := s.gpr .x4
abbrev keyR (s : State) : Region := ⟨W s, 384⟩
abbrev ivR (s : State) : Region := ⟨P s, 8⟩
abbrev dataR (s : State) : Region := ⟨D s, 8 * N s⟩
abbrev scrR (s : State) : Region := ⟨S s, 464⟩
abbrev changes (s : State) : List Region := [ivR s, dataR s, ⟨S s, 456⟩]
abbrev cipher (s : State) : Spec.Cbc.Cipher := Spec.TripleDes.cipher (Spec.TripleDes.scheduleAt s.mem (W s))
abbrev iv (s : State) : List Byte := Spec.Aes.bytesAt s.mem (P s) 8
abbrev out (s : State) : Nat → List Byte := cbcEncC 8 (cipher s) s.mem (D s) (iv s)
abbrev prev (s : State) : Nat → List Byte := cbcEncPrev 8 (cipher s) s.mem (D s) (iv s)

structure Pre (s : State) : Prop where
  rd : s.rd = [keyR s]
  wr : s.wr = [ivR s, dataR s, scrR s]
  key_iv : (keyR s).Disjoint (ivR s)
  key_data : (keyR s).Disjoint (dataR s)
  key_scr : (keyR s).Disjoint (scrR s)
  data_iv : (dataR s).Disjoint (ivR s)
  data_scr : (dataR s).Disjoint (scrR s)
  iv_scr : (ivR s).Disjoint (scrR s)
  key_fit : (W s).toNat + 384 ≤ 2 ^ 64
  iv_fit : (P s).toNat + 8 ≤ 2 ^ 64
  data_fit : (D s).toNat + 8 * N s ≤ 2 ^ 64
  scr_fit : (S s).toNat + 464 ≤ 2 ^ 64

structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  x14 : s.gpr .x14 = W s₀
  x15 : s.gpr .x15 = S s₀
  x1 : s.gpr .x1 = P s₀
  x2 : s.gpr .x2 = D s₀ + BitVec.ofNat 64 (8 * k)
  x3 : s.gpr .x3 = BitVec.ofNat 64 (N s₀ - k)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (changes s₀) s₀.mem s.mem
  consts : Consts s
  masks : Masks s
  keys : ∀ i < 48, s.mem.readW (S s₀ + BitVec.ofNat 64 (8 * i)) 64 =
    spread ((Spec.TripleDes.scheduleAt s₀.mem (W s₀)).getD i 0)
  slots : VG.AArch64.Spill.Saved (S s₀) s₀.gpr saveSlots s.mem
  data : ∀ j < N s₀, Spec.Aes.bytesAt s.mem (D s₀ + BitVec.ofNat 64 (8 * j)) 8 =
    if j < k then out s₀ j else Spec.Aes.bytesAt s₀.mem (D s₀ + BitVec.ofNat 64 (8 * j)) 8
  state : Spec.Aes.bytesAt s.mem (P s₀) 8 = prev s₀ k

section
variable {s₀ : State}

theorem scr_sub {d n : Nat} (h : d + n ≤ 464) :
    Region.Sub ⟨S s₀ + BitVec.ofNat 64 d, n⟩ (scrR s₀) := Offset.sub_base _ h

theorem data_sub {j : Nat} (hj : j < N s₀) :
    Region.Sub ⟨D s₀ + BitVec.ofNat 64 (8*j), 8⟩ (dataR s₀) := Offset.sub_base _ (by omega)

theorem sched_frame (hp : Pre s₀) {m : Mem} (hf : Frame (changes s₀) s₀.mem m) :
    Spec.TripleDes.scheduleAt m (W s₀) = Spec.TripleDes.scheduleAt s₀.mem (W s₀) :=
  scheduleAt_frame hf fun r hr => by
    simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.key_iv
    · exact hp.key_data
    · exact hp.key_scr.sub_right (Region.sub_prefix (by decide))

theorem block_pre (hp : Pre s₀) {s : State} (h14 : s.gpr .x14 = W s₀) (h15 : s.gpr .x15 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) : BlockPre s where
  sched := ⟨keyR s₀, by rw [hrd, hwr, hp.rd]; simp, by rw [h14], by show 384 ≤ 384; decide, by show 384 < 2 ^ 64; decide⟩
  scr := ⟨scrR s₀, by rw [hwr, hp.wr]; simp, by rw [h15], by show 456 ≤ 464; decide, by show 464 < 2 ^ 64; decide⟩
  disj := by rw [h14, h15]; exact hp.key_scr.symm.sub_left (Region.sub_prefix (by decide))

end

/-- Store one encrypted word to the output and IV, then advance the public loop state. -/
theorem store_ok (s : State) {p q : Addr} (hp : s.gpr .x1 = p) (hq : s.gpr .x2 = q)
    (wp : InRegions s.wr p 8) (wq : InRegions s.wr q 8) :
    ∃ s', runBlock isa store s = some s' ∧
      s'.gpr .x2 = s.gpr .x2 + 8 ∧ s'.gpr .x3 = s.gpr .x3 - 1 ∧
      (∀ r, r ∉ [Reg.x2, .x3, .x5] → s'.gpr r = s.gpr r) ∧
      s'.mem = (s.mem.writeW q (byteRev64 (s.gpr .x5))).writeW p (byteRev64 (s.gpr .x5)) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .x .x5 (rev64 (s.read .x .x5))
  have wq' : InRegions s₁.wr (s₁.gpr .x2 + BitVec.ofNat 64 0) 8 := by
    rw [BitVec.add_zero, gpr_write_of_ne _ _ _ (by decide), hq]; exact wq
  let s₂ := { s₁ with mem := s₁.mem.writeW (s₁.gpr .x2 + BitVec.ofNat 64 0) (s₁.gpr .x5) }
  have wp' : InRegions s₂.wr (s₂.gpr .x1 + BitVec.ofNat 64 0) 8 := by
    change InRegions s.wr (s₁.gpr .x1 + BitVec.ofNat 64 0) 8
    rw [BitVec.add_zero, gpr_write_of_ne _ _ _ (by decide), hp]; exact wp
  refine ⟨_, by
    rw [store, runBlock_cons, exec_rev, runStep_some, runBlock_cons,
      exec_str_x (by decide) wq', runStep_some, runBlock_cons,
      exec_str_x (by decide) wp', runStep_some, runBlock_cons,
      exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, ?_, rfl, rfl, rfl⟩
  · simp [s₂, s₁, gpr_write, State.read]
  · simp [s₂, s₁, gpr_write, State.read]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [s₂, s₁, gpr_write, hr.1, hr.2.1, hr.2.2]
  · simp only [s₂, s₁, mem_write, State.read, gpr_write, BitVec.setWidth_eq, rev64_eq, hp, hq, BitVec.add_zero,
      reduceCtorEq, ↓reduceIte]

theorem store_v : store.all (fun i => vdstOf i == none) = true := by decide

/-- One block with shared setup. -/
theorem body_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : Inv s₀ k s) :
    WP isa (.seq (.block chainIn) (.seq enc (.block store))) s (Inv s₀ (k+1)) := by
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
  have hdw := hp.data_fit
  have rdwr : s.rd ++ s.wr = [keyR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain ⟨s₁, run₁, ax₁, keep₁, sp₁, mem₁, rd₁, wr₁⟩ := chainIn_ok s h.x1 h.x2
    (by rw [rdwr]; exact in_rw (r := ivR s₀) (by simp) (Region.contains_self _ _))
    (by rw [rdwr]; exact in_rw (r := dataR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega)))
  have vec₁ := VG.AArch64.Tbl.runBlock_v chainIn_v run₁
  have x14₁ : s₁.gpr .x14 = W s₀ := by rw [keep₁ _ (by decide) (by decide), h.x14]
  have x15₁ : s₁.gpr .x15 = S s₀ := by rw [keep₁ _ (by decide) (by decide), h.x15]
  have bp : BlockPre s₁ := block_pre hp x14₁ x15₁ (rd₁.trans h.rd) (wr₁.trans h.wr)
  have sch₁ : sch s₁ = Spec.TripleDes.scheduleAt s₀.mem (W s₀) := by
    rw [sch, x14₁, mem₁]; exact sched_frame hp h.frame
  have ready : TInv s₁ s₁ := ⟨Same.refl _, rfl, rfl, h.consts.congr (fun w _ _ _ _ => by rw [vec₁]),
    h.masks.congr (fun p hp' => by
      obtain ⟨n5, -, -, -, -, n6, -⟩ := maskRegs_ne p hp'
      exact keep₁ _ n5 n6), fun i hi => by rw [x15₁, sch₁, mem₁]; exact h.keys i hi⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (enc_ok bp ready) fun s₂ ⟨same₂, x14₂, ax₂, const₂, mask₂, keys₂⟩ => ?_)
  have fr₂ : Frame [⟨S s₀, 384⟩] s.mem s₂.mem := by rw [← mem₁, ← x15₁]; exact same₂.frame
  have wr₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [same₂.wr, wr₁, h.wr, hp.wr]
  have x1₂ : s₂.gpr .x1 = P s₀ := by
    rw [same₂.keep .x1 (by simp [outer]), keep₁ _ (by decide) (by decide), h.x1]
  have x2₂ : s₂.gpr .x2 = D s₀ + BitVec.ofNat 64 (8*k) := by
    rw [same₂.keep .x2 (by simp [outer]), keep₁ _ (by decide) (by decide), h.x2]
  obtain ⟨s₃, run₃, x2₃, x3₃, keep₃, mem₃, sp₃, rd₃, wr₃⟩ := store_ok s₂ x1₂ x2₂
    (by rw [wr₂]; exact in_rw (r := ivR s₀) (by simp) (Region.contains_self _ _))
    (by rw [wr₂]; exact in_rw (r := dataR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega)))
  have vec₃ := VG.AArch64.Tbl.runBlock_v store_v run₃
  have vals₂ : ∀ j < N s₀, Spec.Aes.bytesAt s₂.mem (D s₀ + BitVec.ofNat 64 (8*j)) 8 =
      if j < k then out s₀ j else Spec.Aes.bytesAt s₀.mem (D s₀ + BitVec.ofNat 64 (8*j)) 8 := by
    intro j hj
    rw [bytesAt_frame fr₂ (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (hp.data_scr.sub_left (data_sub hj)).sub_right (Region.sub_prefix (by decide))) (by decide)]
    exact h.data j hj
  have value : le8 (byteRev64 (s₂.gpr .x5)) = out s₀ k := by
    rw [ax₂, ax₁, BitVec.xor_comm, ← tdesWith_le8, sch₁, le8_xor, le8_readW, le8_readW,
      h.data k hk, ite_eq_right (Nat.lt_irrefl _), h.state]
    exact (cbcEncC_eq 8 (cipher s₀) s₀.mem (D s₀) (iv s₀) k).symm
  let mid := s₂.mem.writeW (D s₀ + BitVec.ofNat 64 (8*k)) (byteRev64 (s₂.gpr .x5))
  have fData : Frame [⟨D s₀ + BitVec.ofNat 64 (8*k), 8⟩] s₂.mem mid :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fIv : Frame [ivR s₀] mid s₃.mem := by
    rw [mem₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fStore : Frame [ivR s₀, ⟨D s₀ + BitVec.ofNat 64 (8*k), 8⟩] s₂.mem s₃.mem :=
    (fData.mono (fun _ hr => List.mem_cons_of_mem _ hr)).trans
      (fIv.mono (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_self))
  have stD : ∀ {d n : Nat}, d+n ≤ 464 → ∀ r ∈ [ivR s₀, ⟨D s₀ + BitVec.ofNat 64 (8*k), 8⟩],
      (⟨S s₀ + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    intro d n hdn r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (hp.iv_scr.sub_right (scr_sub hdn)).symm
    · obtain rfl := List.mem_singleton.mp hr
      exact ((hp.data_scr.sub_left (data_sub hk)).sub_right (scr_sub hdn)).symm
  refine WP.of_runBlock ⟨s₃, run₃, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [keep₃ _ (by decide), x14₂, x14₁]
  · rw [keep₃ _ (by decide), same₂.x15, x15₁]
  · rw [keep₃ _ (by decide), x1₂]
  · rw [x2₃, x2₂]
    exact x2_succ _ _
  · rw [x3₃, same₂.keep .x3 (by simp [outer]), keep₁ _ (by decide) (by decide), h.x3,
      ofNat_sub_one (by omega) (by omega)]
    congr 1
  · rw [sp₃, same₂.sp, sp₁, h.sp]
  · rw [rd₃, same₂.rd, rd₁, h.rd]
  · rw [wr₃, same₂.wr, wr₁, h.wr]
  · exact (h.frame.trans (fr₂.sub (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨S s₀,456⟩, by simp [changes], Region.sub_prefix (by decide)⟩))).trans
        (fStore.sub (fun r hr => by
          rcases List.mem_cons.mp hr with rfl | hr
          · exact ⟨ivR s₀, by simp [changes], fun _ h => h⟩
          · obtain rfl := List.mem_singleton.mp hr
            exact ⟨dataR s₀, by simp [changes], data_sub hk⟩))
  · exact const₂.congr (fun w _ _ _ _ => by rw [vec₃])
  · exact mask₂.congr (fun p hp' => keep₃ _ (by
      obtain ⟨n5, -, -, -, -, -, -, -, -, -, n2, n3, -⟩ := maskRegs_ne p hp'
      simp [n2,n3,n5]))
  · intro i hi
    rw [fStore.readW (Region.contains_self _ _) (stD (by omega)) (by decide)]
    have e := keys₂ i hi
    rw [x15₁, sch₁] at e
    exact e
  · exact (h.slots.frame_in (lo := 384) (n := 72) saveSlots_facts.1 fr₂ (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint_base _ (by decide) (by decide))).frame fStore
        (fun q hq => stD (by have := saveSlots_facts.1 q hq; omega))
  · intro j hj
    rw [bytesAt_frame fIv (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hp.data_iv.sub_left (data_sub hj)) (by decide)]
    by_cases he : j = k
    · subst j
      change Spec.Aes.bytesAt (s₂.mem.writeW _ _) _ 8 = _
      rw [← le8_readW, Mem.readW_writeW_self64, value, ite_eq_left (by omega)]
    · rw [bytesAt_frame fData (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact Offset.disjoint (D s₀) (by omega) (by omega) (by omega)) (by decide)]
      rw [vals₂ j hj]
      by_cases hlt : j < k
      · rw [ite_eq_left hlt, ite_eq_left (by omega)]
      · rw [ite_eq_right hlt, ite_eq_right (by omega)]
  · rw [mem₃, ← le8_readW, Mem.readW_writeW_self64, value]
    simp [prev, cbcEncPrev, out]

/-- Counted CBC loop, retaining the prepared cipher context. -/
theorem loop_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : Inv s₀ k s) :
    WP isa (.loop (.seq (.block chainIn) (.seq enc (.block store))) (.nonzero .x .x3)) s (Inv s₀ (N s₀)) := by
  refine WP.loop (M := isa) (c := .nonzero .x .x3) (Q := Inv s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀-j ∧ j < N s₀ ∧ Inv s₀ j t) ?_ (N s₀-k) s
      ⟨k,rfl,hk,h⟩
  rintro n s ⟨k,rfl,hk,h⟩
  refine WP.mono (body_ok hp hk h) fun s' h' => ?_
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
  have ev := eval_nonzero (r := .x3) (x := N s₀-(k+1)) (by omega) h'.x3
  by_cases hz : N s₀-(k+1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = k+1 by omega]
  · right
    exact ⟨by rw [ev]; simp [hz], N s₀-(k+1), by omega, k+1,rfl,by omega,h'⟩

/-- The shared API's data and chaining-value postcondition. -/
def Result (s₀ s : State) : Prop :=
  Spec.TripleDes.cbcBlocksAt s.mem (D s₀) (N s₀) =
    Spec.Cbc.encrypt (cipher s₀) (iv s₀) (Spec.TripleDes.cbcBlocksAt s₀.mem (D s₀) (N s₀)) ∧
  Spec.Aes.bytesAt s.mem (P s₀) 8 =
    Spec.Cbc.next (iv s₀) (Spec.Cbc.encrypt (cipher s₀) (iv s₀)
      (Spec.TripleDes.cbcBlocksAt s₀.mem (D s₀) (N s₀)))

theorem result_of_inv {s₀ s : State} (h : Inv s₀ (N s₀) s) (hn : N s₀ ≠ 0) : Result s₀ s := by
  constructor
  · rw [cbcBlocksAt_eq, cbcBlocksAt_eq, encrypt_eq]
    apply List.map_congr_left
    intro j hj
    rw [h.data j (List.mem_range.mp hj), ite_eq_left (List.mem_range.mp hj)]
  · rw [cbcBlocksAt_eq, next_encrypt _ _ _ _ hn, h.state]
    simp [prev, cbcEncPrev, hn]

/-- The complete CBC encryption, preserving the registers saved by the DES kernel. -/
theorem encrypt_wp {s₀ : State} (hp : Pre s₀) :
    WP isa encrypt s₀ fun s => Result s₀ s ∧ ∀ i < 9, s.gpr (savedReg i) = s₀.gpr (savedReg i) := by
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
  let s₁ := (s₀.write .x .x14 (s₀.gpr .x0)).write .x .x15 ((s₀.write .x .x14 (s₀.gpr .x0)).gpr .x4)
  have g₁ : ∀ r, r ≠ .x14 → r ≠ .x15 → s₁.gpr r = s₀.gpr r := fun r h14 h15 => by
    simp only [s₁, gpr_write_of_ne _ _ _ h15, gpr_write_of_ne _ _ _ h14]
  have x14₁ : s₁.gpr .x14 = W s₀ := by simp [s₁, gpr_write]
  have x15₁ : s₁.gpr .x15 = S s₀ := by simp [s₁, gpr_write]
  change WP isa (.seq _ _) _ _
  refine WP.seq (WP.of_runBlock ⟨s₁, by
    rw [runBlock_cons, exec_mov, runStep_some, runBlock_cons, exec_mov, runStep_some, runBlock_nil], ?_⟩)
  have ev := eval_zero (r := .x3) (x := N s₀) hN (by
    rw [g₁ _ (by decide) (by decide)]; simp [N])
  have savedNe : ∀ i < 9, savedReg i ≠ .x14 ∧ savedReg i ≠ .x15 := by decide
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev,hn]; rfl) (fun _ => WP.block_nil ⟨?_,fun i hi => ?_⟩) (fun h => by cases h)
    · simp [Result, hn, Spec.TripleDes.cbcBlocksAt, Spec.TripleDes.blocksAt, Spec.Cbc.encrypt,
        Spec.Cbc.next, s₁, iv, mem_write]
    · exact g₁ _ (savedNe i hi).1 (savedNe i hi).2
  refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
  have bp : BlockPre s₁ := block_pre hp x14₁ x15₁ rfl rfl
  apply WP.seq
  refine WP.mono (prep_ok bp) fun s₂ h₂ => ?_
  have outer₂ : ∀ r ∈ outer, s₂.gpr r = s₀.gpr r := by
    intro r hr
    rw [h₂.same.keep r hr]
    simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)
  have hS : sch s₁ = Spec.TripleDes.scheduleAt s₀.mem (W s₀) := by rw [sch, x14₁]; rfl
  have inv₂ : Inv s₀ 0 s₂ := by
    refine ⟨by rw [h₂.x14,x14₁], by rw [h₂.same.x15,x15₁], outer₂ .x1 (by simp [outer]),
      by rw [outer₂ .x2 (by simp [outer])]; exact (BitVec.add_zero _).symm,
      by rw [outer₂ .x3 (by simp [outer])]; simp [N],
      h₂.same.sp, h₂.same.rd, h₂.same.wr, ?_, h₂.consts,h₂.masks, ?_, ?_, ?_, ?_⟩
    · exact h₂.same.frame.sub (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨⟨S s₀,456⟩,by simp [changes],by rw [x15₁]; exact fun _ h => h⟩)
    · intro i hi
      have e := h₂.keys i hi
      rw [x15₁,hS] at e
      exact e
    · intro p hp'
      rw [← x15₁,h₂.slots p hp']
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp'
      exact g₁ _ (savedNe j (List.mem_range.mp hj)).1 (savedNe j (List.mem_range.mp hj)).2
    · intro j hj
      rw [ite_eq_right (Nat.not_lt_zero _)]
      exact bytesAt_frame h₂.same.frame (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        rw [x15₁]
        exact (hp.data_scr.sub_left (data_sub hj)).sub_right (Region.sub_prefix (by decide))) (by decide)
    · change Spec.Aes.bytesAt s₂.mem (P s₀) 8 = iv s₀
      exact bytesAt_frame h₂.same.frame (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        rw [x15₁]; exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))) (by decide)
  apply WP.seq
  refine WP.mono (loop_ok hp (by omega) inv₂) fun s₃ h₃ => ?_
  refine WP.mono (restore_ok' bp (by rw [h₃.x15,x15₁]) h₃.rd h₃.wr (by
    rw [x15₁]
    intro p hp'
    rw [h₃.slots p hp']
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp'
    exact (g₁ _ (savedNe j (List.mem_range.mp hj)).1 (savedNe j (List.mem_range.mp hj)).2).symm))
    fun s₄ h₄ => ⟨?_, fun i hi => ?_⟩
  · have result := result_of_inv h₃ hn
    simpa only [Result, h₄.mem] using result
  · rw [h₄.gpr_of (.inl (List.mem_map.mpr ⟨_,mem_saveSlots hi,rfl⟩))]
    exact g₁ _ (savedNe i hi).1 (savedNe i hi).2

def rawPre (s : State) : Prop :=
  s.rd = [keyR s] ∧ s.wr = [ivR s,dataR s,scrR s] ∧
    (keyR s).Disjoint (ivR s) ∧ (keyR s).Disjoint (dataR s) ∧ (keyR s).Disjoint (scrR s) ∧
    (dataR s).Disjoint (ivR s) ∧ (dataR s).Disjoint (scrR s) ∧ (ivR s).Disjoint (scrR s) ∧
    (W s).toNat + 384 ≤ 2 ^ 64 ∧ (P s).toNat + 8 ≤ 2 ^ 64 ∧
    (D s).toNat + 8*N s ≤ 2 ^ 64 ∧ (S s).toNat + 464 ≤ 2 ^ 64

theorem Pre.of {s : State} (hp : rawPre s) : Pre s :=
  let ⟨a,b,c,d,e,f,g,h,i,j,k,l⟩ := hp
  ⟨a,b,c,d,e,f,g,h,i,j,k,l⟩

def contract : Contract isa where
  pre := rawPre
  post := Result
  pub s t := s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧
    s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4 ∧ s.sp = t.sp

theorem correct (s : State) (hp : contract.pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ contract.post s s' := by
  have w : WP isa encrypt s (fun s' => Result s s' ∧ ∀ r ∈ VG.Proof.CmacTripleDes.AArch64.savedRegs, s'.gpr r = s.gpr r) :=
    WP.mono (encrypt_wp (Pre.of hp)) fun s' ⟨post,sv⟩ =>
    ⟨post, fun r (hr : r ∈ VG.Proof.CmacTripleDes.AArch64.savedRegs) => by
      obtain ⟨i,hi,rfl⟩ := mem_savedRegs hr
      exact sv i hi⟩
  obtain ⟨t,s',he,⟨post,sv⟩,other⟩ := WP.gprs w
    (by lit_decide : encrypt.allInstrs (fun i =>
      (preserved.filter (· ∉ VG.Proof.CmacTripleDes.AArch64.savedRegs)).all (fun r => !clobbers i r)) = true)
    (by lit_decide)
  refine ⟨t,s',he,⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩,post⟩
  by_cases hs : r ∈ VG.Proof.CmacTripleDes.AArch64.savedRegs
  · exact sv r hs
  · exact other r (List.mem_filter.mpr ⟨hr,by simpa using hs⟩)

theorem constantTime : ConstantTime isa contract.pre contract.pub encrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4]) ?_ (by taint_decide)
  intro s t _ _ ⟨h0,h1,h2,h3,h4,hsp⟩
  refine ⟨hsp,fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000,384⟩]
  wr := [⟨0x2000,8⟩,⟨0x3000,8⟩,⟨0x4000,464⟩]

theorem verified : Verified target encrypt (Proof.TripleDes.cbcEncChainedScratchContract abi 58) := by
  refine Verified.of_correct correct constantTime ?_
  sig_implies [Proof.TripleDes.cbcEncChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig,
    Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcEncChainedPost, contract, rawPre, Result,
    cipher, iv, W, P, D, N, S, keyR, ivR, dataR, scrR, abi, argRegs] [sat] using sat

def frameSat : State := { sat with wr := [⟨0x2000,8⟩,⟨0x3000,8⟩] }

theorem frameSat_pre : ∃ s, (Spec.TripleDes.cbcEncryptChainedContract abi 464).pre s := by
  implies_sat [Spec.TripleDes.cbcEncryptChainedContract,Spec.TripleDes.cbcChainedSig,abi,argRegs]
    [frameSat,sat] using frameSat

theorem framed :
    Verified target (Impl.StackScratch.AArch64.withStackScratchWiped 464 .x4 58 encrypt)
      (Spec.TripleDes.cbcEncryptChainedContract abi 464) :=
  VG.AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 58) (post := Proof.TripleDes.cbcEncChainedPost abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 464) verified (by decide) (by decide) (by decide)
    (Proof.TripleDes.cbcEncChainedPostOut_local _) frameSat_pre

end VG.Proof.TripleDes.AArch64.TablesCbc
