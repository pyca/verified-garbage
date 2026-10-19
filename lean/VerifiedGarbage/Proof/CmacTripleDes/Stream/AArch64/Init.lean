module

import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Common
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Contract
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.AArch64
public import VerifiedGarbage.Proof.CmacTripleDes.AArch64.RoundLit
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Streaming TDEA-CMAC on AArch64: `vg_cmac_triple_des_stream_init`

The code zeroes the chaining value and runs `init` with the state as its
`out`, which writes the key schedule and the subkeys before it: the state
then represents the empty message.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacTripleDes.Stream.AArch64
open VG.Impl.CmacTripleDes.AArch64 (mov)

/-- The precondition, by name: the state `St`, the key `Kp` of `KL` bytes
and the scratch buffer `S`. -/
structure IPre (s₀ : State) (St Kp S : Addr) (KL : Nat) : Prop where
  x0 : s₀.gpr .x0 = St
  x1 : s₀.gpr .x1 = Kp
  x2 : (s₀.gpr .x2).toNat = KL
  x3 : s₀.gpr .x3 = S
  rd : s₀.rd = [⟨Kp, KL⟩]
  wr : s₀.wr = [⟨St, 416⟩, ⟨S, 640⟩]
  st_k : (⟨St, 416⟩ : Region).Disjoint ⟨Kp, KL⟩
  st_s : (⟨St, 416⟩ : Region).Disjoint ⟨S, 640⟩
  k_s : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 640⟩
  wSt : St.toNat + 416 ≤ 2 ^ 64
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wS : S.toNat + 640 ≤ 2 ^ 64
  klen : Spec.TripleDes.validKey KL

theorem IPre.of {s₀ : State} (h : initAArch64.pre s₀) :
    IPre s₀ (s₀.gpr .x0) (s₀.gpr .x1) (s₀.gpr .x3) (s₀.gpr .x2).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

/-- The memory after zeroing the chaining value. -/
def zeroCv (m : Mem) (St : Addr) : Mem := m.writeW (St + BitVec.ofNat 64 400) (0 : BitVec 64)

theorem zeroCv_bytes (m : Mem) (St : Addr) :
    Spec.Aes.bytesAt (zeroCv m St) (St + BitVec.ofNat 64 400) 8 = Spec.Cmac.zeros 8 := by
  rw [zeroCv, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64]; decide

theorem zeroCv_frame (m : Mem) (St : Addr) : Frame [⟨St + BitVec.ofNat 64 400, 8⟩] m (zeroCv m St) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem initPre_ok {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL) :
    ∃ s₁, runBlock isa initPre s₀ = some s₁ ∧ s₁.gpr .x0 = Kp ∧ s₁.gpr .x1 = BitVec.ofNat 64 KL ∧
      s₁.gpr .x2 = St ∧ s₁.gpr .x3 = S ∧ (∀ r ∈ preserved, s₁.gpr r = s₀.gpr r) ∧ s₁.sp = s₀.sp ∧
      s₁.mem = zeroCv s₀.mem St ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have hKL : s₀.gpr .x2 = BitVec.ofNat 64 KL := ofNat_toNat_eq hp.x2
  have w : InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 400) 8 := by
    rw [hp.wr, hp.x0]; exact ⟨⟨St, 416⟩, by simp, Offset.contains_base _ (by decide) (by have := hp.wSt; omega)⟩
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, initPre, mov,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes, Size.bits, State.read,
      gpr_write, mem_write, rd_write, wr_write, Option.bind_some, BitVec.setWidth_eq, w]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, hp.x1], by simp [gpr_write, hKL], by simp [gpr_write, hp.x0],
    by simp [gpr_write, hp.x3], fun r hr => ?_, rfl, ?_, rfl, rfl⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
  · simp [mem_write, zeroCv, Mem.writeW, hp.x0]

theorem init_wp {s₀ : State} (h0 : initAArch64.pre s₀) :
    WP isa streamInit s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧
      initAArch64.post s₀ s' := by
  have hp := IPre.of h0
  generalize s₀.gpr .x0 = St at hp
  generalize s₀.gpr .x1 = Kp at hp
  generalize s₀.gpr .x3 = S at hp
  generalize (s₀.gpr .x2).toNat = KL at hp
  have hw := hp.wSt
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, sv₁, sp₁, m₁, rd₁, wr₁⟩ := initPre_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have oSt : Region.Sub ⟨St, 400⟩ ⟨St, 416⟩ := Region.sub_prefix (by decide)
  have args : IArgs s₁ Kp St S KL :=
    { x0 := x0₁, x1 := x1₁, x2 := x2₁, x3 := x3₁, klen := hp.klen
      ko := (hp.st_k.sub_left oSt).symm
      ks := hp.k_s
      os := hp.st_s.sub_left oSt
      wrapK := hp.wK
      wrapO := by omega
      wrapS := hp.wS
      reads := by
        rw [rd₁, wr₁, hp.rd, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨Kp, KL⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨St, 416⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 640⟩, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₁, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨St, 416⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 640⟩, by simp, 0, by simp, by simp⟩ }
  refine WP.mono (init_inline_wp args) fun s₂ h₂ => ?_
  have f₁ : Frame [⟨St + BitVec.ofNat 64 400, 8⟩] s₀.mem s₁.mem := by rw [m₁]; exact zeroCv_frame _ _
  refine ⟨fun r hr => by rw [h₂.saved r hr, sv₁ r hr], by rw [h₂.sp, sp₁], ?_⟩
  show Spec.Cmac.tdesRepr s₂.mem (s₀.gpr .x0) (Spec.TripleDes.bytesAt s₀.mem (s₀.gpr .x1) (s₀.gpr .x2).toNat) []
  rw [hp.x0, hp.x1, hp.x2, Proof.CmacTripleDes.Stream.repr_iff]
  have hkey : Spec.TripleDes.bytesAt s₁.mem Kp KL = Spec.TripleDes.bytesAt s₀.mem Kp KL := by
    simp only [Spec.TripleDes.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact f₁.bytes (R := ⟨Kp, KL⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_k.symm.sub_right (Offset.sub_base St (by decide)))
      (by show KL ≤ 2 ^ 64; have := hp.wK; omega) (List.mem_range.mp hi)
  have hlen : (Spec.TripleDes.bytesAt s₀.mem Kp KL).length = KL := by simp [Spec.TripleDes.bytesAt]
  obtain ⟨hs, hk⟩ := h₂.out
  rw [hkey] at hs hk
  refine ⟨⟨by rw [hlen]; exact hp.klen, hs, hk⟩, ?_, by
    simp [Proof.CmacTripleDes.Stream.held_zero, Spec.Aes.bytesAt]⟩
  rw [show St + 400 = St + BitVec.ofNat 64 400 from rfl,
    Proof.Cmac.bytesAt_frame h₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base St (d := 400) (by decide) (by decide)
      · exact (hp.st_s.sub_left (Offset.sub_base St (by decide)))) (by decide), m₁, zeroCv_bytes]
  rfl

end VG.Proof.CmacTripleDes.Stream.AArch64
