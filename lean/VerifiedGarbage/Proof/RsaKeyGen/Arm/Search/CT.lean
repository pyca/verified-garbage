module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.CTLoop
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Correct
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.CTLoop
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Correct
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The search is constant time (ARMv7) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins two_taint two_post two_piece two_ite two_map)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Search

/-- The loop's first point. -/
def startPt (p : SearchPublic) : Pt := (0, p.remaining, [])

/-- A run's state after the push, at the first point. -/
def StartCT (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) : Prop :=
  q = startPt p ∧ ∃ o, s = pushed pushRegs o ∧ SearchInput p o ∧ (searchResult o).trace = T

/-- After the load of the state's pointer. -/
def Start' (p : SearchPublic) (_T : List Nat) (_q : Pt) (t : State) : Prop :=
  ∃ o, SearchInput p o ∧ t.gpr .r12 = p.stp ∧ ∀ r ∈ [Reg.r0, .r1, .r2, .r3], t.gpr r = o.gpr r

theorem start_load (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) (h : StartCT p T q s) :
    WP isa (.block [arg .r12 0 7]) s (Start' p T q) := by
  obtain ⟨-, o, rfl, hi, -⟩ := h
  have hroom : 40 ≤ o.sp.toNat := Nat.le_trans (by decide) hi.1.1
  have top := hi.1.2.1
  have a68 : State.addr (o.sp - BitVec.ofNat 32 40 + BitVec.ofNat 32 (pushBytes + 0 + 4 * 7)) = stackArgAddr o 7 := by
    rw [show pushBytes + 0 + 4 * 7 = 40 + 4 * 7 from rfl, sub_add_ofNat]; rfl
  have r68 : InRegions (o.rd ++ ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ :: o.wr) (stackArgAddr o 7) 4 := by
    refine ⟨inArgs o, List.mem_append_left _ (by rw [hi.rd]; simp [inReads]), ?_⟩
    have e : stackArgAddr o 7 = stackArgAddr o 0 + BitVec.ofNat 64 28 := by
      simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
      exact VG.Arm.addr_add (by omega)
    rw [e]; exact Offset.contains_base _ (by decide) (by decide)
  have v68 : (pushed pushRegs o).mem.readW (stackArgAddr o 7) 32 = p.stp := by
    rw [hi.arg_frame (push_frame hi) (by decide), ← hi.2]; rfl
  have c : pushBytes + 0 + 4 * 7 < 4096 := by decide
  refine WP.mono (withRest_all [.r12] (Q := fun t => t.gpr .r12 = p.stp) ?_ (by rfl) (by rfl))
    fun t ⟨h12, k⟩ => ⟨o, hi, h12, fun r hr => by
      rw [k.gpr r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl | rfl <;> decide)]; rfl⟩
  unfold arg
  ffrun [pushed_gpr, pushed_sp, pushed_rd, pushed_wr, a68, r68, v68, c, show 4 * pushRegs.length = 40 from rfl]

theorem start_pins (p : SearchPublic) (T : List Nat) : Pins (Start' p T) [.r0, .r1, .r2, .r3, .r12] := by
  rintro q s₁ s₂ ⟨o₁, h₁, a₁, g₁⟩ ⟨o₂, h₂, a₂, g₂⟩ r hr
  have e (r : Reg) (hr : r ∈ [Reg.r0, .r1, .r2, .r3]) : o₁.gpr r = o₂.gpr r := by
    have b₁ := h₁.2
    have b₂ := h₂.2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (congrArg SearchPublic.op b₁).trans (congrArg SearchPublic.op b₂).symm
    · have := (congrArg SearchPublic.len b₁).trans (congrArg SearchPublic.len b₂).symm
      exact BitVec.eq_of_toNat_eq this
    · exact (congrArg SearchPublic.up b₁).trans (congrArg SearchPublic.up b₂).symm
    · exact (congrArg SearchPublic.ep b₁).trans (congrArg SearchPublic.ep b₂).symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (g₁ _ (by simp)).trans ((e _ (by simp)).trans (g₂ _ (by simp)).symm)
  · exact (g₁ _ (by simp)).trans ((e _ (by simp)).trans (g₂ _ (by simp)).symm)
  · exact (g₁ _ (by simp)).trans ((e _ (by simp)).trans (g₂ _ (by simp)).symm)
  · exact (g₁ _ (by simp)).trans ((e _ (by simp)).trans (g₂ _ (by simp)).symm)
  · exact a₁.trans a₂.symm

theorem entry_ct (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (StartCT p T)) (.block entry) (Two (LiveCT p T)) := by
  refine two_post ?_ fun q s ⟨hq, o, hs, hi, hT⟩ => ?_
  · change RelCT isa _ (.block ([arg .r12 0 7] ++ entry.drop 1)) _
    exact RelCT.block_append (RelCT.seq (ldrSp_ct (start_load p T)) (two_taint _ (start_pins p T) (by taint_decide)))
  · subst hq hs
    refine WP.mono (entry_ok hi) fun t ht => ⟨o, hT, ht, ?_⟩
    obtain ⟨-, rfl⟩ := id hi
    exact (consume_zero _).symm

/-- A finished run after the load of the state's pointer. -/
def Fin' (p : SearchPublic) (T : List Nat) (_q : Pt) (t : State) : Prop :=
  t.gpr .r12 = p.stp ∧ t.gpr .r6 = p.up ∧ ∃ o, (searchResult o).trace = T

theorem fin_load (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) (h : DoneCT p T q s) :
    WP isa (.block [arg .r12 0 7]) s (Fin' p T q) := by
  obtain ⟨o, hT, hd⟩ := h
  have hb := hd.toSearchBase
  have v : stackArg o 7 = p.stp := by rw [← hb.input.2]; rfl
  refine WP.mono (withRest_all [.r12] (Q := fun t => t.gpr .r12 = p.stp) ?_ (by rfl) (by rfl))
    fun t ⟨h12, k⟩ => ⟨h12, (k.gpr .r6 (by decide)).trans hb.r6, o, hT⟩
  unfold arg
  have c : pushBytes + 0 + 4 * 7 < 4096 := by decide
  ffrun [hb.arg_addr 7, hb.arg_read (j := 7) (by decide), hb.arg_value (j := 7) (by decide), v, c]

theorem fin_pins (p : SearchPublic) (T : List Nat) : Pins (Fin' p T) [.r6, .r12] := by
  rintro q s₁ s₂ ⟨a₁, b₁, -⟩ ⟨a₂, b₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [b₁.trans b₂.symm, a₁.trans a₂.symm]

theorem finish_ct (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (DoneCT p T)) (.block finish) (fun _ _ => True) := by
  change RelCT isa _ (.block ([arg .r12 0 7] ++ (results.drop 1 ++ restore))) _
  refine RelCT.block_append (RelCT.seq (ldrSp_ct (fin_load p T)) (RelCT.block_append (RelCT.seq
    (VG.Proof.Bignum.Arm.relCT_keep_sp (two_taint _ (fin_pins p T) (by taint_decide)) fun _ _ ⟨_, _, _, sp⟩ => sp) ?_)))
  exact (VG.Proof.Bignum.Arm.stackLoads_ct [(.r5, 4), (.r6, 8), (.r7, 12), (.r8, 16), (.r9, 20),
    (.r10, 24), (.r11, 28), (.lr, 36)]).mono (fun _ _ h => h) fun _ _ _ => trivial

/-! ## The whole search -/

theorem body_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (StartCT p T)) (body c.call) (fun _ _ => True) := by
  unfold body
  exact RelCT.seq (entry_ct p T) (RelCT.seq (loop_ct c p T) (finish_ct p T))

theorem pub_same {s t : State} (h : searchPub s t) : searchOfState s = searchOfState t := by
  obtain ⟨hsp, r0, r1, r2, r3, ha, he, hw, -⟩ := h
  have h0 : s.mem.readW (State.addr (stackArg t 7)) 64 = t.mem.readW (State.addr (stackArg t 7)) 64 := by
    have := congrArg List.head? hw
    rw [ha 7 (by decide)] at this
    simpa [Spec.Rsa.wordsAt, List.range_succ] using this
  unfold searchOfState
  simp only [searchRemaining, searchLen, hsp, r0, r1, r2, r3, he, ha 0 (by decide), ha 1 (by decide),
    ha 2 (by decide), ha 3 (by decide), ha 4 (by decide), ha 5 (by decide), ha 6 (by decide),
    ha 7 (by decide), h0]

theorem code_ct (c : Cand) :
    RelCT isa (fun s t => searchPre s ∧ searchPre t ∧ searchPub s t) (code c.call) (fun _ _ => True) := by
  unfold code
  refine RelCT.frame (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb u v ⟨s, t, ⟨hs, ht, hp⟩, ea, eb⟩ e1 e2
  have rs : 184 ≤ s.sp.toNat := hs.1
  have rt : 184 ≤ t.sp.toNat := ht.1
  rw [push_pushed (by decide) (by simp only [List.length_cons, List.length_nil]; omega)] at ea eb
  cases ea
  cases eb
  have hpt := pub_same hp
  exact body_ct c (searchOfState s) (searchResult s).trace _ _ ta tb u v
    ⟨startPt _, ⟨rfl, s, rfl, ⟨hs, rfl⟩, rfl⟩, ⟨by rw [hpt], t, rfl, ⟨ht, hpt.symm⟩,
      hp.2.2.2.2.2.2.2.2.2.2.2.symm⟩, by simp only [pushed_sp, hp.1]⟩ e1 e2

theorem search_constantTime (c : Cand) :
    ConstantTime isa searchContract.pre searchContract.pub (code c.call) :=
  RelCT.constantTime (code_ct c)

end VG.Proof.RsaKeyGen.Arm.Search
