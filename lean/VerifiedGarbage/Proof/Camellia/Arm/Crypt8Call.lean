module

public import VerifiedGarbage.Proof.Camellia.Arm.Crypt8
public import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # The shared Camellia eight-block kernel

The arithmetic retains `crypt8_ok`'s original frame. The call additionally
uses unused slot 629 for its return address; neither the key table nor the
caller's saved registers and loop state occupy that slot.
-/

@[expose] public section
namespace VG.Proof.Camellia.Arm
open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Impl.Aes.Arm (sb ldS stS)
open VG.Proof.Camellia (cryptWords)

def callRegions (b : BitVec 32) : List Region :=
  ⟨wordAddr b 629, 4⟩ :: ctxRegions b

structure CallCtx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  base : s.gpr sb = s₀.gpr sb
  frame : Frame (callRegions (s₀.gpr sb)) s₀.mem s.mem

theorem CallCtx.slot {s₀ s : State} (hc : CallCtx s₀ s)
    (hfit : (s₀.gpr sb).toNat + 4 * slots ≤ 2 ^ 32) {k : Nat}
    (hk : k < slots) (h1 : keySlot ≤ k) (h2 : k ≠ grpSlot)
    (h3 : k < tailSlot ∨ tailSlot + 32 ≤ k) (h4 : k ≠ 629) :
    slotW s k = slotW s₀ k := by
  simp only [slotW, hc.base]
  refine hc.frame.readW (r := ⟨wordAddr (s₀.gpr sb) k, 4⟩)
    (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [callRegions, ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact slot_sep _ (by rw [slots_eq] at hfit hk; omega_arith)
      (by rw [slots_eq] at hfit; omega_arith) h4
  · exact slot_disjoint_base hfit hk h1
  · simpa using slot_disjoint hfit (a := grpSlot) (n := 1) hk
      (by rw [slots_eq, grpSlot_eq]; omega_arith) (by decide) (by omega_arith)
  · simpa using slot_disjoint hfit (a := tailSlot) (n := 32) hk
      (by rw [slots_eq, tailSlot_eq]; omega_arith) (by decide) (by omega_arith)

theorem call_sub_scr {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) :
    ∀ r ∈ callRegions b, Region.Sub r ⟨State.addr b, 4 * slots⟩ := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [wordAddr, VG.Arm.addr_add (by rw [slots_eq] at hfit; omega_arith)]
    exact VG.Offset.sub_base _ (by rw [slots_eq]; omega_arith)
  · exact ctx_sub_scr hfit r hr

theorem crypt8Call_ok {s₀ : State} {g : Nat} {E : Nat → BitVec 64}
    (hp : CorePre s₀ g E) :
    WP isa crypt8Call s₀ fun s' => CallCtx s₀ s' ∧
      ∀ b < 8, blk s' b = Spec.Camellia.encodeBlock
        (cryptWords g E (Spec.Camellia.decodeBlock (blk s₀ b))) := by
  let s := s₀.callEntry
  have bs : s.gpr sb = s₀.gpr sb := State.callEntry_gpr _ (by decide)
  have hw : ScrIn s.wr (s.gpr sb) := by rw [bs]; exact ⟨hp.scr.wr, hp.scr.fit⟩
  have hf : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32 := by rw [bs]; exact hp.scr.fit
  obtain ⟨a, ea, ma, ga, ra, wa, spa, -, fa⟩ := stSlot_ok s .lr sb (k := 629) rfl (by decide) hw
  have ba : a.gpr sb = s.gpr sb := congrFun ga _
  have slots_kept (j : Nat) (hj : j < slots) (hne : j ≠ 629) :
      slotW a j = slotW s j := by
    rw [slotW, ba, ma, readW_slot_write hf _ hj (by decide), ite_eq_right hne]
  have pre : CorePre a g E :=
    { scr := ⟨by rw [ba, wa]; exact hp.scr.wr, by rw [ba]; exact hf⟩
      nk34 := hp.nk34
      keys := fun i hi => (hp.keys i hi).congr fun j hj => by
        show slotW a (keySlot + 16 * i + j) = _
        rw [slots_kept _ (by have := hp.nk34; rw [slots_eq, keySlot_eq]; omega_arith)
          (by have := hp.nk34; rw [keySlot_eq]; omega_arith)]
        simp only [slotW, bs, s, State.callEntry_mem]; rfl
      hg := hp.hg
      bound := by rw [slots_kept _ (by decide) (by decide), slotW, ba, bs]
                  exact hp.bound }
  have block_kept (b : Nat) (hb : b < 8) : blk a b = blk s₀ b := by
    apply blk_of_words (by rw [ba]; exact hf) (B := fun b => blk s₀ b) (b := b) (hb := hb)
    intro b hb c hc j hj
    change (slotW a (tailSlot + (4 * b + c / 4))).getLsbD _ = _
    rw [slots_kept _ (by rw [slots_eq, tailSlot_eq]; omega_arith)
      (by rw [tailSlot_eq]; omega_arith)]
    change (slotW s (tailSlot + (4 * b + c / 4))).getLsbD _ = _
    simp only [slotW, bs, s, State.callEntry_mem]
    exact data_words s₀ hp.scr.fit b hb c hc j hj
  have body : WP isa crypt8Fn s fun t =>
      t.gpr .lr = s.gpr .lr ∧ CallCtx s₀ t ∧
        ∀ b < 8, blk t b = Spec.Camellia.encodeBlock
          (cryptWords g E (Spec.Camellia.decodeBlock (blk s₀ b))) := by
    refine WP.seq (WP.of_runBlock ⟨a, ea, ?_⟩)
    refine WP.seq (WP.mono (crypt8_ok pre) fun u ⟨cu, bu⟩ => ?_)
    have bu0 : u.gpr sb = s₀.gpr sb := by rw [cu.base, ba, bs]
    have ret_slot : slotW u 629 = s.gpr .lr := by
      rw [cu.slot (by rw [ba]; exact hf) (by decide) (by decide) (by decide) (.inl (by decide)),
        slotW, ba, ma, Mem.readW_writeW_self32]
    have wu : ScrIn u.wr (u.gpr sb) := by rw [cu.wr, wa, bu0]; exact ⟨hp.scr.wr, hp.scr.fit⟩
    obtain ⟨t, et, rt, ot, mt, rdt, wrt, spt⟩ := ldSlot_ok u .lr sb (k := 629) rfl (by decide) wu
    refine WP.of_runBlock ⟨t, et, ?_, ?_, ?_⟩
    · rw [rt]; exact ret_slot
    · refine ⟨by rw [rdt, cu.rd, ra]; rfl, by rw [wrt, cu.wr, wa]; rfl,
        by rw [ot _ (by decide), bu0], ?_⟩
      have f := (fa.mono (rs' := callRegions (s.gpr sb)) (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact List.mem_cons_self)).trans
        (cu.frame.mono (rs' := callRegions (s.gpr sb)) (by
          rw [ba]; intro r hr; exact List.mem_cons_of_mem _ hr))
      rw [bs] at f
      simpa only [mt, s, State.callEntry_mem] using f
    · intro b hb
      have bt : blk t b = blk u b := by simp only [blk, mt, ot sb (by decide)]
      rw [bt, bu b hb, block_kept b hb]
  obtain ⟨trace, t, he, hlr, hc, hb⟩ := body
  refine ⟨_, _, Exec.call (call_callEntry s₀) he ?_, hc, hb⟩
  simp only [isa, ret, hlr, s, ite_true]

end VG.Proof.Camellia.Arm
