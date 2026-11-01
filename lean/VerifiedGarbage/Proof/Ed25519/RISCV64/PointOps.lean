module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointAdd
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Point
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Spec.Ed25519.Point32
import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Ed25519 on RISC-V: calls of the point addition, and doubling

A call of `vg_ed25519_r32_point_add` (`addCall_ok`), from an aligned working
space of 8192 bytes with `d` in slot 16, leaves in slots 0–3 the sum of the
points in slots 0–3 and 4–7, keeps every slot but 0–3 and the temporaries
8–15 (`Keeps`, `env_keeps`), and keeps `Keep`: no register but `fclob`, no
memory but the field area.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64

/-- The point addition's working space: `ws` in `a3`, a multiple of 8, its 8192 bytes writable. -/
structure Ctx8 (b : Addr) (s : State) : Prop where
  a3 : s.gpr .a3 = b
  al : b.toNat % 8 = 0
  wr : (⟨b, 8192⟩ : Region) ∈ s.wr

theorem Ctx8.ctx {b : Addr} {s : State} (h : Ctx8 b s) : Ctx b s :=
  ⟨h.a3, h.al, fun d n hd => in_base h.wr (by omega) (by omega)⟩

theorem Ctx8.ws {b : Addr} {s : State} (h : Ctx8 b s) : WS b s :=
  Covers.of_sub fun r hr => ⟨_, h.wr, 0, by rw [List.mem_singleton.mp hr]; simp, by
    rw [List.mem_singleton.mp hr]; simp⟩

theorem Ctx8.of_keep {b : Addr} {s t : State} (h : Ctx8 b s) (k : Keep b s t) : Ctx8 b t :=
  ⟨by rw [k.rest.gpr _ (by decide), h.a3], h.al, by rw [k.rest.wr]; exact h.wr⟩

/-- The slots the point addition keeps: all but the sum's and the temporaries'. -/
def Kept (i : Slot) : Prop := 4 ≤ i.val ∧ i.val < 8 ∨ 16 ≤ i.val

instance (i : Slot) : Decidable (Kept i) := by unfold Kept; infer_instance

theorem env_keeps {b : Addr} {m m' : Mem} (h : Spec.Ed25519.Point32.Keeps b m m') {i : Slot} (hi : Kept i) :
    env m' b i = env m b i := by
  have hs := slot_range i
  unfold env FS
  rw [← read_V, ← read_V]
  refine congrArg (fun v : BitVec (8 * 32) => Proof.X25519.toFe v.toNat) (Mem.read_congr fun j hj => ?_)
  have hi' := hi
  unfold Kept at hi'
  have ho : offset i = 64 + 32 * i.val := rfl
  rw [Offset.add_add]
  refine (h (offset i + j) (by simp only [Spec.Ed25519.Point32.wsBytes]; omega)
    (by simp only [Spec.Ed25519.Point32.pAt, Spec.Ed25519.Point32.elemBytes]; omega) (by omega) (by omega))

/-- What a call of `vg_ed25519_r32_point_add` asks of the function: its working space, aligned,
with `d` at `dAt`. -/
def addK (b : Addr) : Contract isa where
  pre t := t.wr = [⟨b, 8192⟩] ∧ t.gpr .a0 = b ∧ b.toNat % 8 = 0 ∧
    Spec.Ed25519.Point32.elemAt t.mem b Spec.Ed25519.Point32.dAt = Spec.Ed25519.d
  post t t' :=
    Spec.Ed25519.Point32.pointAt t'.mem b Spec.Ed25519.Point32.pAt =
        Spec.Ed25519.pointAdd (Spec.Ed25519.Point32.pointAt t.mem b Spec.Ed25519.Point32.pAt)
          (Spec.Ed25519.Point32.pointAt t.mem b Spec.Ed25519.Point32.qAt) ∧
      Spec.Ed25519.Point32.Keeps b t.mem t'.mem
  pub _ _ := True

theorem addK_ok (b : Addr) :
    ∀ t, (addK b).pre t → ∃ tr t', VG.Exec isa addFn t tr t' ∧ abiPreserved t t' ∧ (addK b).post t t' :=
  fun t ⟨hwr, h0, hal, hd⟩ => by
    obtain ⟨tr, t', he, hp, hk⟩ := WP.keep [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t3, .t4, .t5, .t6]
      (addFn_ok (by rw [hwr, h0]) (by rw [h0]; exact hal) (by rw [h0]; exact hd)) (by decide +kernel)
    rw [h0] at hp
    exact ⟨tr, t', he, abiPreserved_of_keep he hk (by decide) (by decide), hp⟩

/-- **A call of the point addition**. -/
theorem addCall_ok {b : Addr} {s : State} (hc : Ctx8 b s) (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa addCall s fun t => Keep b s t ∧
      point (env t.mem b) 0 1 2 3 = Spec.Ed25519.pointAdd (point (env s.mem b) 0 1 2 3) (point (env s.mem b) 4 5 6 7) ∧
      ∀ i : Slot, Kept i → env t.mem b i = env s.mem b i := by
  unfold addCall
  refine WP.seq (wp_mv fun s1 u1 => WP.block_nil ?_)
  have e0 : s1.gpr .a0 = b := by rw [u1.gpr, hc.a3]
  have g : ∀ q, q ∉ linkRegs → (s1.callEntry.withRegions [] [⟨b, 8192⟩]).gpr q = s1.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have hw1 : Covers [⟨b, 8192⟩] s1.wr := Covers.of_mem fun r hr => by
    rw [List.mem_singleton.mp hr, u1.wr]; exact hc.wr
  have hd' : Spec.Ed25519.Point32.elemAt s1.mem b Spec.Ed25519.Point32.dAt = Spec.Ed25519.d := by
    rw [u1.mem, show Spec.Ed25519.Point32.dAt = offset 16 from rfl, elemAt_eq]; exact hd
  refine WP.seq (WP.call (k := addK b) (addK_ok b) (rd := []) (wr := [⟨b, 8192⟩])
    ⟨rfl, by rw [g _ (by decide), e0], hc.al, by
      rw [State.withRegions_mem, State.callEntry_mem]; exact hd'⟩
    (by rw [List.nil_append]; exact hw1.right) hw1 ?_ (by decide +kernel))
  intro t hrd hwr hsp hfr _ hkeep ⟨hpt, hks⟩
  simp only [State.withRegions_mem, State.callEntry_mem] at hpt hks
  rw [u1.mem] at hpt hks
  have ha0 : t.gpr .a0 = b := by rw [hkeep _ (by decide) (by decide +kernel), e0]
  refine wp_mv fun t1 v1 => WP.block_nil ⟨⟨⟨fun q hq => ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · by_cases h3 : q = .a3
    · subst h3
      rw [v1.gpr, ha0, hc.a3]
    · have hl : q ∉ linkRegs := by revert hq; cases q <;> decide
      have hd : ∀ i ∈ instrs addFn, dstOf i ≠ some q := by
        revert hq h3; cases q <;> first | decide +kernel | (intro h; exact absurd (by decide) h)
      rw [v1.other _ h3, hkeep _ hl hd, u1.other _ (by revert hq; cases q <;> decide)]
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
      exact hks _ (by simp only [Spec.Ed25519.Point32.wsBytes]; omega)
        (by simp only [Spec.Ed25519.Point32.pAt, Spec.Ed25519.Point32.elemBytes]; omega) (by omega) (by omega)
    · rw [← u1.mem]
      exact hfr x fun r hr => by rw [List.mem_singleton.mp hr]; exact hw
  · rw [v1.mem, ← pointAt_eq, hpt, pointAt_eq, pointAt_q]
  · intro i hi
    rw [v1.mem]
    exact env_keeps hks hi

end VG.Proof.Ed25519.RISCV64
