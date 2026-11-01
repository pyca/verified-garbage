module

import VerifiedGarbage.Proof.Ed25519.PPC64LE.FieldVerified
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Point
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.FieldProg
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ed25519.Point32Contract
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field

/-!
# Ed25519 on PPC64LE: calls of the point addition, and doubling

A call of `vg_ed25519_r32_point_add` (`addCall_ok`), from a working space of
8192 bytes with `d` in slot 16, leaves in slots 0–3 the sum of the points in
slots 0–3 and 4–7, keeps every slot but 0–3 and the temporaries 8–15
(`Keeps`, `env_keeps`), and keeps `Keep`: no register but `fclob`, no memory
but the field area. A doubling (`doubleCall_ok`) copies the point to slots
4–7 and adds.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE

/-- The point addition's working space: `ws` in `r6`, its 8192 bytes writable. -/
structure Ctx8 (b : Addr) (s : State) : Prop where
  r6 : s.gpr .r6 = b
  wr : (⟨b, 8192⟩ : Region) ∈ s.wr

theorem Ctx8.ctx {b : Addr} {s : State} (h : Ctx8 b s) : Ctx b s := ⟨h.r6, 8192, by decide, h.wr⟩

theorem Ctx8.of_keep {b : Addr} {s t : State} (h : Ctx8 b s) (k : Keep b s t) : Ctx8 b t :=
  ⟨by rw [k.rest.gpr _ (by decide), h.r6], by rw [k.rest.wr]; exact h.wr⟩

/-- The slots the point addition keeps: all but the sum's and the temporaries'. -/
def Kept (i : Slot) : Prop := 4 ≤ i.val ∧ i.val < 8 ∨ 16 ≤ i.val

instance (i : Slot) : Decidable (Kept i) := by unfold Kept; infer_instance

theorem env_keeps {b : Addr} {m m' : Mem} (h : Proof.Ed25519.Point32.Keeps b m m') {i : Slot} (hi : Kept i) :
    env m' b i = env m b i := by
  have hs := slot_range i
  have hA := ACC_eq
  unfold env FS
  rw [← read_V, ← read_V]
  refine congrArg (fun v : BitVec (8 * 32) => Proof.X25519.toFe v.toNat) (Mem.read_congr fun j hj => ?_)
  have hi' := hi
  unfold Kept at hi'
  have ho : offset i = 64 + 32 * i.val := rfl
  rw [Offset.add_add]
  refine (h (offset i + j) (by simp only [Proof.Ed25519.Point32.wsBytes]; omega)
    (by simp only [Proof.Ed25519.Point32.pAt, Proof.Ed25519.Point32.elemBytes]; omega) (by omega) (by omega))

/-- The registers `vg_ed25519_r32_point_add` never writes. -/
def keptRegs : List Reg := [.r2, .r3, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23,
  .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- **A call of the point addition**. -/
theorem addCall_ok {b : Addr} {s : State} (hc : Ctx8 b s) (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa addCall s fun t => Keep b s t ∧
      point (env t.mem b) 0 1 2 3 = Spec.Ed25519.pointAdd (point (env s.mem b) 0 1 2 3) (point (env s.mem b) 4 5 6 7) ∧
      ∀ i : Slot, Kept i → env t.mem b i = env s.mem b i := by
  unfold addCall
  refine WP.seq (wp_addi (by decide) (by decide) fun s1 u1 => WP.block_nil ?_)
  have e3 : s1.gpr .r3 = b := by rw [u1.gpr, hc.r6, BitVec.add_zero]
  have g : ∀ q, q ∉ linkRegs → (s1.callEntry.withRegions [] [⟨b, 8192⟩]).gpr q = s1.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have hsub : ∀ r ∈ ([⟨b, 8192⟩] : List Region), ∃ r' ∈ s1.wr, ∃ off,
      r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len := fun r hr => by
    rw [List.mem_singleton.mp hr, u1.wr]
    exact ⟨_, hc.wr, 0, by simp, by simp⟩
  have hd' : Proof.Ed25519.Point32.elemAt s1.mem b Proof.Ed25519.Point32.dAt = Spec.Ed25519.d := by
    rw [u1.mem, show Proof.Ed25519.Point32.dAt = offset 16 from rfl, elemAt_eq]; exact hd
  refine WP.seq (WP.call (k := addPPC) add_ok' (rd := []) (wr := [⟨b, 8192⟩])
    ⟨⟨rfl, by rw [State.withRegions_wr, g _ (by decide), e3]⟩, by
      rw [State.withRegions_mem, State.callEntry_mem, g _ (by decide), e3]; exact hd'⟩
    (Covers.of_sub fun r hr => by
      obtain ⟨r', hr', h'⟩ := hsub r (by simpa using hr)
      exact ⟨r', List.mem_append_right _ hr', h'⟩)
    (Covers.of_sub hsub) ?_ (by decide +kernel))
  intro t hrd hwr hsp hfr _ hkeep ⟨hpt, hks⟩
  have c3 : (s1.callEntry.withRegions [] [⟨b, 8192⟩]).gpr .r3 = b := by rw [g _ (by decide), e3]
  simp only [State.withRegions_mem, State.callEntry_mem, c3] at hpt hks
  rw [u1.mem] at hpt hks
  -- The registers the callee never writes.
  have nw : ((instrs addFn).all fun i => (keptRegs).all fun r => dstOf i != some r) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  have hk : ∀ q ∈ keptRegs, t.gpr q = s1.gpr q := fun q hq => by
    refine hkeep q (by revert hq; cases q <;> decide) fun i hi => ?_
    have := List.all_eq_true.mp (List.all_eq_true.mp nw i hi) q hq
    simpa using this
  refine wp_addi (by decide) (by decide) fun t1 v1 => WP.block_nil ⟨⟨⟨fun q hq => ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · by_cases h6 : q = .r6
    · subst h6
      rw [v1.gpr, hk _ (by decide), e3, BitVec.add_zero, hc.r6]
    · rw [v1.other _ h6, hk _ (by revert hq h6; cases q <;> decide), u1.other _ (by revert hq; cases q <;> decide)]
  · rw [v1.rd, hrd, u1.rd]
  · rw [v1.wr, hwr, u1.wr]
  · rw [v1.sp, hsp, u1.sp]
  · rw [v1.mem]
    intro x hx
    have hnf := hx _ (List.mem_singleton_self _)
    by_cases hw : (⟨b, 8192⟩ : Region).Contains x 1
    · have hi : (x - b).toNat + 1 ≤ 8192 := hw
      have hx' : x = b + BitVec.ofNat 64 (x - b).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have hlo : (x - b).toNat < 64 ∨ 1024 ≤ (x - b).toNat := by
        by_contra hc
        refine hnf ?_
        rw [hx']
        exact Offset.contains _ (by omega) (by omega) (by omega)
      rw [hx']
      exact hks _ (by simp only [Proof.Ed25519.Point32.wsBytes]; omega)
        (by simp only [Proof.Ed25519.Point32.pAt, Proof.Ed25519.Point32.elemBytes]; omega) (by omega) (by omega)
    · rw [← u1.mem]
      exact hfr x fun r hr => by rw [List.mem_singleton.mp hr]; exact hw
  · rw [v1.mem, ← pointAt_eq, hpt, pointAt_eq, pointAt_q]
  · intro i hi
    rw [v1.mem]
    exact env_keeps hks hi

end VG.Proof.Ed25519.PPC64LE
