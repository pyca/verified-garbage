module
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.AArch64
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Implies
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Common
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Contract
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.RoundLit
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.CmacTripleDes.Stream
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacTripleDes.Scratch
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.CT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/-! ### `CmacTripleDes.Stream.AArch64.Verified`, which only this module used -/

section

/-! ### `CmacTripleDes.Stream.AArch64.Init`, which only this module used -/

section

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
  obtain hKL : s₀.gpr .x2 = BitVec.ofNat 64 KL := ofNat_toNat_eq hp.x2
  obtain w : InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 400) 8 := by
    rw [hp.wr, hp.x0]; exact ⟨⟨St, 416⟩, by simp, Offset.contains_base _ (by decide) (by have := hp.wSt; omega_using [])⟩
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
  obtain hp := IPre.of h0
  generalize s₀.gpr .x0 = St at hp
  generalize s₀.gpr .x1 = Kp at hp
  generalize s₀.gpr .x3 = S at hp
  generalize (s₀.gpr .x2).toNat = KL at hp
  have hw := hp.wSt
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, sv₁, sp₁, m₁, rd₁, wr₁⟩ := initPre_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain oSt : Region.Sub ⟨St, 400⟩ ⟨St, 416⟩ := Region.sub_prefix (by decide)
  obtain args : IArgs s₁ Kp St S KL :=
    { x0 := x0₁, x1 := x1₁, x2 := x2₁, x3 := x3₁, klen := hp.klen
      ko := (hp.st_k.sub_left oSt).symm
      ks := hp.k_s
      os := hp.st_s.sub_left oSt
      wrapK := hp.wK
      wrapO := by omega_using [hw]
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
  obtain f₁ : Frame [⟨St + BitVec.ofNat 64 400, 8⟩] s₀.mem s₁.mem := by rw [m₁]; exact zeroCv_frame _ _
  refine ⟨fun r hr => by rw [h₂.saved r hr, sv₁ r hr], by rw [h₂.sp, sp₁], ?_⟩
  show Spec.Cmac.tdesRepr s₂.mem (s₀.gpr .x0) (Spec.TripleDes.bytesAt s₀.mem (s₀.gpr .x1) (s₀.gpr .x2).toNat) []
  rw [hp.x0, hp.x1, hp.x2, Proof.CmacTripleDes.Stream.repr_iff]
  obtain hkey : Spec.TripleDes.bytesAt s₁.mem Kp KL = Spec.TripleDes.bytesAt s₀.mem Kp KL := by
    simp only [Spec.TripleDes.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact f₁.bytes (R := ⟨Kp, KL⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_k.symm.sub_right (Offset.sub_base St (by decide)))
      (by show KL ≤ 2 ^ 64; have := hp.wK; omega_using [this]) (List.mem_range.mp hi)
  obtain hlen : (Spec.TripleDes.bytesAt s₀.mem Kp KL).length = KL := by simp [Spec.TripleDes.bytesAt]
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

end

end

/-! ### `CmacTripleDes.Stream.AArch64.Finish`, which only this module used -/

section

/-!
# Streaming TDEA-CMAC on AArch64: `vg_cmac_triple_des_finish`

The code copies the chaining value to `out`, computes the number of bytes
held back, and runs `finalize` with the state as its key and `out` as its
state: its result is the MAC of the message the state represents
(`repr_finish`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacTripleDes.Stream.AArch64
open VG.Impl.CmacTripleDes.AArch64 (mov)
open VG.Proof.CmacTripleDes.Stream (held held_le)

/-- The precondition, by name: the state `St`, `out` (`O`) and the scratch
buffer `S`. -/
structure HPre (s₀ : State) (St O S : Addr) : Prop where
  x0 : s₀.gpr .x0 = St
  x2 : s₀.gpr .x2 = O
  x3 : s₀.gpr .x3 = S
  rd : s₀.rd = []
  wr : s₀.wr = [⟨St, 416⟩, ⟨O, 8⟩, ⟨S, 640⟩]
  st_o : (⟨St, 416⟩ : Region).Disjoint ⟨O, 8⟩
  st_s : (⟨St, 416⟩ : Region).Disjoint ⟨S, 640⟩
  o_s : (⟨O, 8⟩ : Region).Disjoint ⟨S, 640⟩
  wSt : St.toNat + 416 ≤ 2 ^ 64
  wO : O.toNat + 8 ≤ 2 ^ 64
  wS : S.toNat + 640 ≤ 2 ^ 64

theorem HPre.of {s₀ : State} (h : finishAArch64.pre s₀) : HPre s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) :=
  let ⟨a, b, c, d, e, f, g, h⟩ := h
  ⟨rfl, rfl, rfl, a, b, c, d, e, f, g, h⟩

/-- The memory after copying the chaining value to `out`. -/
def copyCv (m : Mem) (O St : Addr) : Mem := m.writeW O (m.readW (St + BitVec.ofNat 64 400) 64)

theorem copyCv_bytes (m : Mem) (O St : Addr) :
    Spec.Aes.bytesAt (copyCv m O St) O 8 = Spec.Aes.bytesAt m (St + BitVec.ofNat 64 400) 8 := by
  rw [copyCv, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, Proof.Cmac.le8_readW]

theorem copyCv_frame (m : Mem) (O St : Addr) : Frame [⟨O, 8⟩] m (copyCv m O St) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem finishPre_ok {s₀ : State} {St O S : Addr} (hp : HPre s₀ St O S) :
    ∃ s₁, runBlock isa finishPre s₀ = some s₁ ∧ s₁.gpr .x0 = St ∧ s₁.gpr .x1 = O ∧
      s₁.gpr .x2 = St + BitVec.ofNat 64 408 ∧ s₁.gpr .x3 = s₀.gpr .x1 ∧ s₁.gpr .x4 = S ∧
      (∀ r ∈ preserved, s₁.gpr r = s₀.gpr r) ∧
      s₁.sp = s₀.sp ∧ s₁.mem = copyCv s₀.mem O St ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have hw := hp.wSt
  obtain r₁ : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 400) 8 := by
    rw [hp.rd, hp.wr, hp.x0]; exact ⟨⟨St, 416⟩, by simp, Offset.contains_base _ (by decide) (by omega_using [])⟩
  obtain w₁ : InRegions s₀.wr (s₀.gpr .x2 + BitVec.ofNat 64 0) 8 := by
    rw [hp.wr, hp.x2, BitVec.add_zero]; exact ⟨⟨O, 8⟩, by simp, Region.contains_self _ _⟩
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, finishPre, mov,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bytes, Size.bits,
      State.read, gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some,
      BitVec.setWidth_eq, r₁, w₁]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, hp.x0], by simp [gpr_write, hp.x2], by simp [gpr_write, hp.x0],
    by simp [gpr_write], by simp [gpr_write, hp.x3], fun r hr => ?_, rfl, ?_, rfl, rfl⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
  · simp only [mem_write, copyCv, Mem.writeW, Mem.readW, BitVec.setWidth_eq, BitVec.add_zero, hp.x0, hp.x2,
      Nat.reduceDiv]

/-- What the code before `finalize` leaves. -/
structure HMid (s₀ : State) (St O S : Addr) (s : State) : Prop where
  args : FArgs s St O (St + BitVec.ofNat 64 408) S (held (s₀.gpr .x1).toNat)
  mem : s.mem = copyCv s₀.mem O St
  saved : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp

theorem HPre.fargs {s₀ s : State} {St O S : Addr} {L : Nat} (hp : HPre s₀ St O S) (hL : L ≤ 8)
    (x0 : s.gpr .x0 = St) (x1 : s.gpr .x1 = O) (x2 : s.gpr .x2 = St + BitVec.ofNat 64 408)
    (x3 : s.gpr .x3 = BitVec.ofNat 64 L) (x4 : s.gpr .x4 = S) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    FArgs s St O (St + BitVec.ofNat 64 408) S L := by
  have hw := hp.wSt
  obtain pSt : Region.Sub ⟨St + BitVec.ofNat 64 408, L⟩ ⟨St, 416⟩ := Offset.sub_base St (by omega_using [hL])
  exact
  { x0 := x0, x1 := x1, x2 := x2, x3 := x3, x4 := x4, len := hL
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := hp.st_s.sub_left (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    ps := hp.st_s.sub_left pSt
    sts := hp.o_s
    wrapK := by omega_using [hw]
    wrapSt := hp.wO
    wrapP := by rw [toNat_add_lt St hw (by decide)]; omega_using [hL, hw]
    wrapS := hp.wS
    reads := by
      rw [rd, wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 416⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 416⟩, by simp, 408, rfl, by simp; omega_using [hL]⟩
      · exact ⟨⟨O, 8⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 640⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨O, 8⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 640⟩, by simp, 0, by simp, by simp⟩ }

theorem lastLen_ok (s : State) {c : BitVec 64} (h3 : s.gpr .x3 = c) (hc : c ≠ 0) :
    ∃ s', runBlock isa [.subImm .x .x3 .x3 1, .movz .x .x9 7 0, .logic .and .x .x3 .x3 .x9,
        .addImm .x .x3 .x3 1] s = some s' ∧ s'.gpr .x3 = BitVec.ofNat 64 (held c.toNat) ∧
      (∀ r, r ≠ .x3 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil,
      exec, Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl, rfl, rfl⟩
  simp only [gpr_write, ite_true, BitVec.setWidth_eq, h3]
  exact held_bv c hc

theorem finPre_wp {s₀ : State} {St O S : Addr} (hp : HPre s₀ St O S) :
    WP isa finPre s₀ (HMid s₀ St O S) := by
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x4₁, sv₁, sp₁, m₁, rd₁, wr₁⟩ := finishPre_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain hc := (s₀.gpr .x1).isLt
  obtain h1 : s₀.gpr .x1 = BitVec.ofNat 64 (s₀.gpr .x1).toNat := ofNat_toNat_eq rfl
  by_cases h0 : (s₀.gpr .x1).toNat = 0
  · refine WP.ite true (by rw [eval_zero hc (by rw [x3₁]; exact h1), h0]; rfl)
      (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨hp.fargs (held_le _) x0₁ x1₁ x2₁ ?_ x4₁ rd₁ wr₁, m₁, sv₁, sp₁⟩
    rw [x3₁, h1, h0]; rfl
  · refine WP.ite false (by rw [eval_zero hc (by rw [x3₁]; exact h1)]; simp [h0])
      (fun h => by cases h) fun _ => ?_
    obtain hne : s₀.gpr .x1 ≠ 0 := fun e => h0 (by rw [e]; rfl)
    obtain ⟨s₂, run₂, x3₂, g₂, sp₂, m₂, rd₂, wr₂⟩ := lastLen_ok s₁ x3₁ hne
    refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
    obtain hc : ∀ r ∈ preserved, r ≠ .x3 ∧ r ≠ .x9 := by decide
    refine ⟨hp.fargs (held_le _) (by rw [g₂ _ (by decide) (by decide), x0₁])
      (by rw [g₂ _ (by decide) (by decide), x1₁]) (by rw [g₂ _ (by decide) (by decide), x2₁])
      x3₂ (by rw [g₂ _ (by decide) (by decide), x4₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]), by rw [m₂, m₁],
      fun r hr => by rw [g₂ r (hc r hr).1 (hc r hr).2, sv₁ r hr], by rw [sp₂, sp₁]⟩

theorem finish_wp {s₀ : State} (h0 : finishAArch64.pre s₀) :
    WP isa finish s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧
      finishAArch64.post s₀ s' := by
  obtain hp := HPre.of h0
  generalize s₀.gpr .x0 = St at hp
  generalize s₀.gpr .x2 = O at hp
  generalize s₀.gpr .x3 = S at hp
  have hw := hp.wSt
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.mono (fin_wp h₁.args) fun s₂ h₂ => ?_
  obtain f₁ : Frame [⟨O, 8⟩] s₀.mem s₁.mem := by rw [h₁.mem]; exact copyCv_frame _ _ _
  refine ⟨fun r hr => by rw [h₂.saved r hr, h₁.saved r hr], by rw [h₂.sp, h₁.sp], ?_⟩
  intro key msg hr hc hlen
  rw [hp.x0] at hr
  rw [hp.x2]
  obtain hr₁ : Spec.Cmac.tdesRepr s₁.mem St key msg :=
    Proof.CmacTripleDes.Stream.repr_congr_416 (fun i hi => f₁.bytes (R := ⟨St, 416⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.st_o) (by show 416 ≤ 2 ^ 64; decide) hi) hr
  obtain ⟨hm, hne, hst, happ⟩ := Proof.CmacTripleDes.Stream.repr_finish hr₁
  rw [Proof.CmacTripleDes.Stream.repr_iff] at hr₁
  obtain ⟨⟨_, hks, hsk⟩, -, -⟩ := hr₁
  obtain hn : (s₀.gpr .x1).toNat = msg.length := by rw [hc, toNat_ofNat hlen]
  obtain hciph : Proof.CmacTripleDes.AArch64.ciphAt s₁.mem St = Spec.Cmac.tdes key := by
    simp only [Proof.CmacTripleDes.AArch64.ciphAt, hks, Spec.Cmac.tdes]
  obtain e₂ : Spec.Aes.bytesAt s₁.mem O 8 = Spec.Aes.bytesAt s₁.mem (St + 400) 8 := by
    rw [h₁.mem, copyCv_bytes, show St + 400 = St + BitVec.ofNat 64 400 from rfl]
    exact (Proof.Cmac.bytesAt_frame (copyCv_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_o.sub_left (Offset.sub_base St (d := 400) (n := 8) (by decide))) (by decide)).symm
  obtain out := h₂.out (by rw [hciph]; exact hsk) _ hm (by rw [hn]; exact hne)
    (by rw [hciph, e₂]; exact hst)
  rw [out, hciph, hn, show St + BitVec.ofNat 64 408 = St + 408 from rfl, happ,
    Proof.CmacTripleDes.Stream.tdesCmac_eq]

end VG.Proof.CmacTripleDes.Stream.AArch64

end

end

/-! ### `CmacTripleDes.Stream.AArch64.AbsorbCorrect`, which only this module used -/

section

/-! ### `CmacTripleDes.Stream.AArch64.AbsorbBlocks`, which only this module used -/

section

/-!
# Streaming TDEA-CMAC on AArch64: `vg_cmac_triple_des_absorb`'s straight-line code

What each piece of code between the copies and the runs of `update` computes, in terms of
`count` (`c`) and `len` (`L`): the bytes held back `h = held c`, the bytes
copied after them `f = min L (8 - h)`, the data left `L - f`, whether to
chain the block held back (`b1`), the blocks chained after it (`nb`), and the
rest (`rest`); and the registers `absorb` saves at `scratch + 640`, where the
code it runs does not write, and restores at the end.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacTripleDes.Stream.AArch64
open VG.Impl.CmacTripleDes.AArch64 (mov)
open VG.Proof.CmacTripleDes.Stream (held held_le)

/-! ## The numbers -/

/-- The bytes copied after the `held c` held back. -/
def fOf (c L : Nat) : Nat := min L (8 - held c)

/-- The data left after them. -/
def leftOf (c L : Nat) : Nat := L - fOf c L

/-- The number of blocks the first run of `update` chains: the block held
back, if data is left. -/
def b1Of (c L : Nat) : Nat := if leftOf c L = 0 then 0 else 1

/-- The number of blocks the second run chains: those of the data left but
its last 1 to 8 bytes. -/
def nbOf (c L : Nat) : Nat := if leftOf c L = 0 then 0 else (leftOf c L - 1) / 8

/-- The bytes copied to the start of the bytes held back at the end. -/
def restOf (c L : Nat) : Nat := leftOf c L - 8 * nbOf c L

theorem f_le (c L : Nat) : fOf c L ≤ L ∧ fOf c L + held c ≤ 8 := by
  have := held_le c; unfold fOf; omega_using [this]

theorem nb_le (c L : Nat) : fOf c L + 8 * nbOf c L + restOf c L = L := by
  have := f_le c L; unfold restOf nbOf leftOf; split <;> omega_using [this]

/-! ## Arithmetic on registers -/

theorem shr_ofNat {n k : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by have := Nat.div_le_self n (2 ^ k); omega_using [hn, this])]

/-- The sign of `m - k`, for `m` and `k` of at most 8. -/
theorem lsr63 {m k : Nat} (hm : m ≤ 8) (hk : k ≤ 8) :
    (BitVec.ofNat 64 m - BitVec.ofNat 64 k) >>> 63 = BitVec.ofNat 64 (if m < k then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega_arith

/-- `8 nb` for the data left `x > 0`, as `sub 1; and 7; sub` computes it. -/
theorem nb8_bv {x : Nat} (hx : 0 < x) (hx' : x < 2 ^ 64) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 1 - ((BitVec.ofNat 64 x - BitVec.ofNat 64 1) &&& 7) =
      BitVec.ofNat 64 (8 * ((x - 1) / 8)) := by
  apply BitVec.eq_of_toNat_eq
  obtain e : (BitVec.ofNat 64 x - BitVec.ofNat 64 1).toNat = x - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_using [hx, hx']
  rw [BitVec.toNat_sub, and7, e, BitVec.toNat_ofNat]
  omega_using []

/-! ## Saving and restoring the registers -/

/-- The memory after saving the registers at `S + 640`. -/
abbrev absSavedMem (s : State) (S : Addr) : Mem := Spill.saveMem s.mem S s.gpr saved

/-- Each slot holds the register saved there. -/
theorem absSaved_slot (s : State) (S : Addr) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (absSavedMem s S).readW (S + BitVec.ofNat 64 d) 64 = s.gpr r :=
  Spill.saveMem_saved (l := saved) (by decide) s.mem S s.gpr (r, d) h

/-- Saving the registers changes only their slots. -/
theorem absSavedMem_frame (s : State) (S : Addr) :
    Frame [⟨S + BitVec.ofNat 64 640, 40⟩] s.mem (absSavedMem s S) :=
  Spill.saveMem_frame (by decide) (by decide) _ _ _

theorem save_ok (s : State) {S : Addr} (hS : s.gpr .x4 = S)
    (hw : ∀ d, 640 ≤ d → d + 8 ≤ 680 → InRegions s.wr (S + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa save s = some s' ∧
      s'.gpr .x19 = s.gpr .x0 ∧ s'.gpr .x21 = s.gpr .x2 ∧ s'.gpr .x22 = s.gpr .x3 ∧ s'.gpr .x23 = S ∧
      (∀ r, r ≠ .x19 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = absSavedMem s S ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [← hS] at hw ⊢
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, save, saved, mov,
      List.map, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
      State.store, Size.bytes, Size.bits, State.read, gpr_write, Option.bind_some,
      hw 640 (by decide) (by decide), hw 648 (by decide) (by decide), hw 656 (by decide) (by decide),
      hw 664 (by decide) (by decide), hw 672 (by decide) (by decide)]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    fun r h₁ h₂ h₃ h₄ => ?_, rfl, ?_, rfl, rfl⟩
  · simp [gpr_write, h₁, h₂, h₃, h₄]
  · simp only [mem_write, absSavedMem, saved, Spill.saveMem, Mem.writeW, BitVec.setWidth_eq]

theorem restore_ok (s : State) {B : Addr} (hb : s.gpr .x23 = B)
    (hr : ∀ d, 640 ≤ d → d + 8 ≤ 680 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa restore s = some s' ∧
      (∀ r d, (r, d) ∈ saved → s'.gpr r = s.mem.readW (B + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, restore, saved,
      List.map, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits,
      gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some, hb,
      hr 640 (by decide) (by decide), hr 648 (by decide) (by decide), hr 656 (by decide) (by decide),
      hr 664 (by decide) (by decide), hr 672 (by decide) (by decide)]
    rfl, ?_⟩
  refine ⟨fun r d h => ?_, fun r h₁ h₂ h₃ h₄ h₅ => ?_, rfl, rfl⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [gpr_write, Mem.readW]
  · simp [gpr_write, h₁, h₂, h₃, h₄, h₅]

/-! ## `held`: the bytes held back -/

theorem held_wp {s : State} {c : Nat} (hc : c < 2 ^ 64) (hd : s.gpr .x1 = BitVec.ofNat 64 c) :
    WP isa Impl.CmacTripleDes.Stream.AArch64.held s fun s' => s'.gpr .x9 = BitVec.ofNat 64 (held c) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  by_cases h0 : c = 0
  · subst h0
    refine WP.ite true (by rw [eval_zero hc hd]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine WP.of_runBlock ⟨_, rfl, ?_⟩
    exact ⟨by simp [gpr_write]; rfl, fun r h _ => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
  · have hne : BitVec.ofNat 64 c ≠ 0 := fun e => h0 (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat hc] at this)
    refine WP.ite false (by rw [eval_zero hc hd]; simp [h0]) (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, rfl, ?_⟩
    refine ⟨?_, fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl, rfl, rfl⟩
    simp only [State.read, gpr_write, ↓reduceIte, BitVec.setWidth_eq, mz7, hd, reduceCtorEq]
    rw [held_bv _ hne, toNat_ofNat hc]

/-! ## `fill`: how many bytes to copy, and where -/

theorem clamp_wp {s : State} {L : Nat} (hL : L < 2 ^ 64) (h22 : s.gpr .x22 = BitVec.ofNat 64 L) :
    WP isa clamp s fun s' => s'.gpr .x10 = BitVec.ofNat 64 (min L 8) ∧
      (∀ r, r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, x10₁, g₁⟩ : ∃ s₁, runBlock isa [.lsr .x .x10 .x22 3] s = some s₁ ∧
      s₁.gpr .x10 = BitVec.ofNat 64 (L / 8) ∧ s₁ = s.write .x .x10 (BitVec.ofNat 64 (L / 8)) := by
    refine ⟨_, rfl, by simp [gpr_write, State.read, h22, shr_ofNat hL], ?_⟩
    simp only [State.read, h22, BitVec.setWidth_eq, shr_ofNat hL]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain ev := eval_zero (s := s₁) (x := L / 8) (by omega_using [hL]) x10₁
  subst g₁
  by_cases hl : L < 8
  · refine WP.ite true (by rw [ev]; simp; omega_using [hl]) (fun _ => ?_) (fun h => by cases h)
    refine WP.of_runBlock ⟨_, rfl, ?_⟩
    refine ⟨?_, fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
    simp [gpr_write, State.read, h22, Nat.min_eq_left (Nat.le_of_lt hl)]
  · refine WP.ite false (by rw [ev]; simp; omega_using [hl]) (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, rfl, ?_⟩
    refine ⟨?_, fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
    simp only [gpr_write, ↓reduceIte, mz8, BitVec.setWidth_eq, Nat.min_eq_right (Nat.le_of_not_lt hl)]

theorem fill_wp {s : State} {St D : Addr} {c L : Nat} (hL : L < 2 ^ 64)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 (held c)) (h22 : s.gpr .x22 = BitVec.ofNat 64 L)
    (h19 : s.gpr .x19 = St) (h21 : s.gpr .x21 = D) :
    WP isa fill s fun s' => s'.gpr .x8 = BitVec.ofNat 64 (fOf c L) ∧
      s'.gpr .x10 = BitVec.ofNat 64 (fOf c L) ∧ s'.gpr .x6 = St + BitVec.ofNat 64 (408 + held c) ∧
      s'.gpr .x7 = D ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x10 → r ≠ .x11 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hh := held_le c
  refine WP.seq (WP.mono (clamp_wp hL h22) fun s₁ ⟨x10₁, g₁, sp₁, m₁, rd₁, wr₁⟩ => ?_)
  obtain x9₁ : s₁.gpr .x9 = BitVec.ofNat 64 (held c) := by rw [g₁ _ (by decide), h9]
  obtain ⟨s₂, run₂, x8₂, x10₂, x11₂, g₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa [.movz .x .x8 8 0,
      .sub .x .x8 .x8 .x9, .sub .x .x11 .x10 .x8, .lsr .x .x11 .x11 63] s₁ = some s₂ ∧
      s₂.gpr .x8 = BitVec.ofNat 64 (8 - held c) ∧ s₂.gpr .x10 = BitVec.ofNat 64 (min L 8) ∧
      s₂.gpr .x11 = BitVec.ofNat 64 (if min L 8 < 8 - held c then 1 else 0) ∧
      (∀ r, r ≠ .x8 → r ≠ .x11 → s₂.gpr r = s₁.gpr r) ∧ s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, rfl, ?_, ?_, ?_, fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl, rfl, rfl⟩
    · simp only [State.read, gpr_write, ↓reduceIte, reduceCtorEq, BitVec.setWidth_eq, mz8, x9₁,
        Offset.ofNat_sub_ofNat hh]
    · simp only [gpr_write, ↓reduceIte, reduceCtorEq, x10₁]
    · simp only [State.read, gpr_write, ↓reduceIte, reduceCtorEq, BitVec.setWidth_eq, mz8, x9₁, x10₁,
        Offset.ofNat_sub_ofNat hh]
      exact lsr63 (by omega_using []) (by omega_using [])
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  obtain hf : fOf c L = min (min L 8) (8 - held c) := by unfold fOf; omega_using []
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .x8 = BitVec.ofNat 64 (fOf c L) ∧
    (∀ r, r ≠ .x8 → s₃.gpr r = s₂.gpr r) ∧ s₃.sp = s₂.sp ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧
      s₃.wr = s₂.wr) ?_ fun s₃ h₃ => ?_)
  · have ev := eval_zero (s := s₂) (x := if min L 8 < 8 - held c then 1 else 0) (by split <;> omega_using []) x11₂
    by_cases hl : min L 8 < 8 - held c
    · refine WP.ite false (by rw [ev]; simp [hl]) (fun h => by cases h) fun _ => ?_
      refine WP.of_runBlock ⟨_, rfl, ?_⟩
      refine ⟨?_, fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
      simp [gpr_write, State.read, x10₂, hf, Nat.min_eq_left (Nat.le_of_lt hl)]
    · refine WP.ite true (by rw [ev]; simp [hl]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [x8₂, hf, Nat.min_eq_right (Nat.le_of_not_lt hl)], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨x8₃, g₃, sp₃, m₃, rd₃, wr₃⟩ := h₃
    have g (r : Reg) (a : r ≠ .x8) (b : r ≠ .x11) (d : r ≠ .x10) : s₃.gpr r = s.gpr r := by
      rw [g₃ r a, g₂ r a b, g₁ r d]
    refine WP.of_runBlock ⟨_, rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, fun r a b d e f => ?_, by simp only [sp_write, sp₃, sp₂, sp₁],
      by simp only [mem_write, m₃, m₂, m₁], by simp only [rd_write, rd₃, rd₂, rd₁],
      by simp only [wr_write, wr₃, wr₂, wr₁]⟩
    · simp [gpr_write, State.read, x8₃]
    · simp [gpr_write, State.read, x8₃]
    · simp only [State.read, gpr_write, ↓reduceIte, reduceCtorEq, Size.bits, BitVec.setWidth_eq,
        g .x19 (by decide) (by decide) (by decide), g .x9 (by decide) (by decide) (by decide), h19, h9]
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]
    · simp [gpr_write, State.read, g .x21 (by decide) (by decide) (by decide), h21]
    · simp only [gpr_write, a, b, e, ite_false]
      exact g r d f e

/-! ## `chain1`: the arguments of the first run of `update` -/

theorem chain1_wp {s : State} {St D S : Addr} {f L : Nat} (hf : f ≤ L) (hL : L < 2 ^ 64)
    (h21 : s.gpr .x21 = D) (h10 : s.gpr .x10 = BitVec.ofNat 64 f) (h22 : s.gpr .x22 = BitVec.ofNat 64 L)
    (h19 : s.gpr .x19 = St) (h23 : s.gpr .x23 = S) :
    WP isa chain1 s fun s' => s'.gpr .x21 = D + BitVec.ofNat 64 f ∧ s'.gpr .x22 = BitVec.ofNat 64 (L - f) ∧
      s'.gpr .x3 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧ s'.gpr .x0 = St ∧
      s'.gpr .x1 = St + BitVec.ofNat 64 400 ∧ s'.gpr .x2 = St + BitVec.ofNat 64 408 ∧ s'.gpr .x4 = S ∧
      (∀ r ∈ preserved, r ≠ .x21 → r ≠ .x22 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, x21₁, x22₁, x3₁, g₁, sp₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.add .x .x21 .x21 .x10,
      .sub .x .x22 .x22 .x10, .movz .x .x3 0 0] s = some s₁ ∧
      s₁.gpr .x21 = D + BitVec.ofNat 64 f ∧ s₁.gpr .x22 = BitVec.ofNat 64 (L - f) ∧
      s₁.gpr .x3 = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .x21 → r ≠ .x22 → r ≠ .x3 → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, rfl, ?_, ?_, ?_, fun r a b c => by simp [gpr_write, a, b, c], rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, State.read, h21, h10]
    · simp only [State.read, gpr_write, ↓reduceIte, reduceCtorEq, BitVec.setWidth_eq, h22, h10,
        Offset.ofNat_sub_ofNat hf]
    · simp only [gpr_write, ↓reduceIte, mz0]; rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .x3 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧
    (∀ r, r ≠ .x3 → s₂.gpr r = s₁.gpr r) ∧ s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr) ?_ fun s₂ h₂ => ?_)
  · have ev := eval_zero (s := s₁) (x := L - f) (by omega_using [hL]) x22₁
    by_cases h0 : L - f = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [x3₁]; simp [h0], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine WP.of_runBlock ⟨_, rfl, ?_⟩
      refine ⟨?_, fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
      simp only [gpr_write, ↓reduceIte, mz1, h0]; rfl
  · obtain ⟨x3₂, g₂, sp₂, m₂, rd₂, wr₂⟩ := h₂
    have g (r : Reg) (a : r ≠ .x21) (b : r ≠ .x22) (c : r ≠ .x3) : s₂.gpr r = s.gpr r := by
      rw [g₂ r c, g₁ r a b c]
    refine WP.of_runBlock ⟨_, rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr a b => ?_, by simp only [sp_write, sp₂, sp₁],
      by simp only [mem_write, m₂, m₁], by simp only [rd_write, rd₂, rd₁],
      by simp only [wr_write, wr₂, wr₁]⟩
    · simp [gpr_write, g₂ _ (by decide : Reg.x21 ≠ .x3), x21₁]
    · simp [gpr_write, g₂ _ (by decide : Reg.x22 ≠ .x3), x22₁]
    · simp [gpr_write, x3₂]
    · simp [gpr_write, State.read, g .x19 (by decide) (by decide) (by decide), h19]
    · simp [gpr_write, State.read, g .x19 (by decide) (by decide) (by decide), h19]
    · simp [gpr_write, State.read, g .x19 (by decide) (by decide) (by decide), h19]
    · simp [gpr_write, State.read, g .x23 (by decide) (by decide) (by decide), h23]
    · have hc : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 := by decide
      obtain ⟨n0, n1, n2, n3, n4⟩ := hc r hr
      simp only [gpr_write, n0, n1, n2, n4, ite_false]
      exact g r a b n3

/-! ## `chain2`: the arguments of the second run of `update` -/

theorem chain2_wp {s : State} {x : Nat} (hx : x < 2 ^ 64) (h22 : s.gpr .x22 = BitVec.ofNat 64 x) :
    WP isa chain2 s fun s' =>
      s'.gpr .x20 = BitVec.ofNat 64 (8 * (if x = 0 then 0 else (x - 1) / 8)) ∧
      s'.gpr .x3 = BitVec.ofNat 64 (if x = 0 then 0 else (x - 1) / 8) ∧ s'.gpr .x0 = s.gpr .x19 ∧
      s'.gpr .x1 = s.gpr .x19 + BitVec.ofNat 64 400 ∧ s'.gpr .x2 = s.gpr .x21 ∧ s'.gpr .x4 = s.gpr .x23 ∧
      (∀ r ∈ preserved, r ≠ .x20 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, x20₁, g₁⟩ : ∃ s₁, runBlock isa [.movz .x .x20 0 0] s = some s₁ ∧
      s₁.gpr .x20 = BitVec.ofNat 64 0 ∧ s₁ = s.write .x .x20 (BitVec.ofNat 64 0) :=
    ⟨_, rfl, by simp [gpr_write], by simp only [mz0]; rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  subst g₁
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
    s₂.gpr .x20 = BitVec.ofNat 64 (8 * (if x = 0 then 0 else (x - 1) / 8)) ∧
    (∀ r, r ≠ .x20 → r ≠ .x9 → s₂.gpr r = s.gpr r) ∧ s₂.sp = s.sp ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧
      s₂.wr = s.wr) ?_ fun s₂ h₂ => ?_)
  · have ev := eval_zero (s := s.write .x .x20 (BitVec.ofNat 64 0)) (r := .x22) (x := x) hx
      (by simp only [gpr_write, reduceCtorEq, ite_false, h22])
    by_cases h0 : x = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [x20₁]; simp [h0], fun r h _ => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine WP.of_runBlock ⟨_, rfl, ?_⟩
      refine ⟨?_, fun r a b => by simp [gpr_write, a, b], rfl, rfl, rfl, rfl⟩
      simp only [State.read, gpr_write, ↓reduceIte, reduceCtorEq, BitVec.setWidth_eq, mz7, h22, h0]
      exact nb8_bv (by omega_using [h0]) hx
  · obtain ⟨x20₂, g₂, sp₂, m₂, rd₂, wr₂⟩ := h₂
    refine WP.of_runBlock ⟨_, rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr a => ?_, by simp only [sp_write, sp₂],
      by simp only [mem_write, m₂], by simp only [rd_write, rd₂], by simp only [wr_write, wr₂]⟩
    · simp [gpr_write, x20₂]
    · simp only [State.read, gpr_write, ↓reduceIte, reduceCtorEq, BitVec.setWidth_eq, x20₂]
      exact (shr_ofNat (by split <;> omega_arith)).trans (by congr 1; omega_using [])
    · simp [gpr_write, State.read, g₂ _ (by decide : Reg.x19 ≠ .x20) (by decide)]
    · simp [gpr_write, State.read, g₂ _ (by decide : Reg.x19 ≠ .x20) (by decide)]
    · simp [gpr_write, State.read, g₂ _ (by decide : Reg.x21 ≠ .x20) (by decide)]
    · simp [gpr_write, State.read, g₂ _ (by decide : Reg.x23 ≠ .x20) (by decide)]
    · have hc : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x9 := by
        decide
      obtain ⟨n0, n1, n2, n3, n4, n9⟩ := hc r hr
      simp only [gpr_write, n0, n1, n2, n3, n4, ite_false]
      exact g₂ r a n9

/-! ## `rest`: the arguments of the last copy -/

theorem rest_ok {s : State} {D : Addr} {a x n : Nat} (hn : 8 * n ≤ x)
    (h21 : s.gpr .x21 = D + BitVec.ofNat 64 a) (h20 : s.gpr .x20 = BitVec.ofNat 64 (8 * n))
    (h22 : s.gpr .x22 = BitVec.ofNat 64 x) :
    ∃ s', runBlock isa rest s = some s' ∧ s'.gpr .x21 = D + BitVec.ofNat 64 (a + 8 * n) ∧
      s'.gpr .x22 = BitVec.ofNat 64 (x - 8 * n) ∧ s'.gpr .x6 = s.gpr .x19 + BitVec.ofNat 64 408 ∧
      s'.gpr .x7 = D + BitVec.ofNat 64 (a + 8 * n) ∧ s'.gpr .x8 = BitVec.ofNat 64 (x - 8 * n) ∧
      (∀ r ∈ preserved, r ≠ .x21 → r ≠ .x22 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain e : D + BitVec.ofNat 64 a + BitVec.ofNat 64 (8 * n) = D + BitVec.ofNat 64 (a + 8 * n) :=
    Offset.add_add _ _ _
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, fun r hr a b => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [State.read, gpr_write, ↓reduceIte, reduceCtorEq, BitVec.setWidth_eq, h21, h20, e]
  · simp only [State.read, gpr_write, ↓reduceIte, reduceCtorEq, BitVec.setWidth_eq, h22, h20,
      Offset.ofNat_sub_ofNat hn]
  · simp [State.read, gpr_write]
  · simp only [State.read, gpr_write, ↓reduceIte, reduceCtorEq, BitVec.setWidth_eq,
      BitVec.add_zero, h21, h20, e]
  · simp only [State.read, gpr_write, ↓reduceIte, reduceCtorEq, BitVec.setWidth_eq,
      BitVec.add_zero, h22, h20, Offset.ofNat_sub_ofNat hn]
  · have hc : ∀ r ∈ preserved, r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 := by decide
    obtain ⟨n6, n7, n8⟩ := hc r hr
    simp only [gpr_write, a, b, n6, n7, n8, ite_false]

end VG.Proof.CmacTripleDes.Stream.AArch64

end

end


@[expose] public section

section

/-!
# Streaming TDEA-CMAC on AArch64: `vg_cmac_triple_des_absorb` up to the first `update`

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 8 - h)` bytes after them, and sets up the first run of `update`,
which chains the block held back if data is left (`AMid₁`).
-/

namespace VG.Proof.CmacTripleDes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacTripleDes.Stream.AArch64 VG.WriteBytes
open VG.Proof.CmacTripleDes.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`
and the scratch buffer `S`. -/
structure APre (s₀ : State) (St D S : Addr) (L : Nat) : Prop where
  x0 : s₀.gpr .x0 = St
  x2 : s₀.gpr .x2 = D
  x3 : (s₀.gpr .x3).toNat = L
  x4 : s₀.gpr .x4 = S
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 416⟩, ⟨S, 688⟩]
  st_d : (⟨St, 416⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 416⟩ : Region).Disjoint ⟨S, 688⟩
  d_s : (⟨D, L⟩ : Region).Disjoint ⟨S, 688⟩
  wSt : St.toNat + 416 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : S.toNat + 688 ≤ 2 ^ 64

theorem APre.of {s₀ : State} (h : absorbAArch64.pre s₀) :
    APre s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x4) (s₀.gpr .x3).toNat :=
  let ⟨a, b, c, d, e, f, g, h⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h⟩

section
variable {s₀ : State} {St D S : Addr} {L : Nat} (hp : APre s₀ St D S L)
include hp

theorem APre.lt : L < 2 ^ 64 := by rw [← hp.x3]; exact BitVec.isLt _

theorem APre.x3' : s₀.gpr .x3 = BitVec.ofNat 64 L := ofNat_toNat_eq hp.x3

theorem APre.inSt {d n : Nat} (h : d + n ≤ 416) : InRegions s₀.wr (St + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨St, 416⟩, by simp, Offset.contains_base _ h (by have := hp.wSt; omega_using [h])⟩

theorem APre.inS {d n : Nat} (h : d + n ≤ 688) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨S, 688⟩, by simp, Offset.contains_base _ h (by have := hp.wS; omega_using [h])⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ h (by have := hp.lt; omega_using [h, this])⟩

/-- The arguments of a run of `update` on `n` blocks at `Dd`, from a state
with the permissions of `s₀`. -/
theorem APre.uargs {s : State} {Dd : Addr} {n : Nat} (hx0 : s.gpr .x0 = St)
    (hx1 : s.gpr .x1 = St + BitVec.ofNat 64 400) (hx2 : s.gpr .x2 = Dd)
    (hx3 : s.gpr .x3 = BitVec.ofNat 64 n) (hx4 : s.gpr .x4 = S)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 8 * n < 2 ^ 64)
    (hdc : (⟨Dd, 8 * n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 400, 8⟩)
    (hds : (⟨Dd, 8 * n⟩ : Region).Disjoint ⟨S, 640⟩) (hwrap : Dd.toNat + 8 * n ≤ 2 ^ 64)
    (hcov : ∃ r' ∈ ([⟨D, L⟩, ⟨St, 416⟩, ⟨S, 688⟩] : List Region), ∃ off, Dd = r'.base + BitVec.ofNat 64 off ∧
      off + 8 * n ≤ r'.len) :
    UArgs s St (St + BitVec.ofNat 64 400) Dd S n := by
  have hw := hp.wSt
  obtain c400 : Region.Sub ⟨St + BitVec.ofNat 64 400, 8⟩ ⟨St, 416⟩ := Offset.sub_base St (by decide)
  obtain s640 : Region.Sub ⟨S, 640⟩ ⟨S, 688⟩ := Region.sub_prefix (by decide)
  exact
  { x0 := hx0, x1 := hx1, x2 := hx2, x3 := hx3, x4 := hx4, hn := hn
    wc := Offset.base_disjoint St (by decide) (by omega_using [])
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right s640
    dc := hdc, ds := hds
    cs := (hp.st_s.sub_left c400).sub_right s640
    wrapC := by rw [toNat_add_lt St hw (by decide)]; omega_using [hw]
    wrapD := hwrap
    wrapS := by have := hp.wS; omega_using [this]
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 416⟩, by simp, 0, by simp, by simp⟩
      · exact hcov
      · exact ⟨⟨St, 416⟩, by simp, 400, rfl, by simp⟩
      · exact ⟨⟨S, 688⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St, 416⟩, by simp, 400, rfl, by simp⟩
      · exact ⟨⟨S, 688⟩, by simp, 0, by simp, by simp⟩ }

end

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) (St D S : Addr) (c L : Nat) : Mem :=
  writeBytes (absSavedMem s₀ S) (St + BitVec.ofNat 64 (408 + held c))
    (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf c L))

/-- What the code before the first run of `update` leaves. -/
structure AMid₁ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 64 400) (St + BitVec.ofNat 64 408) S (b1Of (s₀.gpr .x1).toNat L)
  x19 : s.gpr .x19 = St
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (fOf (s₀.gpr .x1).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (leftOf (s₀.gpr .x1).toNat L)
  x23 : s.gpr .x23 = S
  other : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = m4 s₀ St D S (s₀.gpr .x1).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : Addr} {L : Nat} (hp : APre s₀ St D S L) :
    WP isa absorbPre s₀ (AMid₁ s₀ St D S L) := by
  generalize hc : (s₀.gpr .x1).toNat = c
  obtain hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  obtain hdx : s₀.gpr .x1 = BitVec.ofNat 64 c := ofNat_toNat_eq hc
  have hL := hp.lt
  have hw := hp.wSt
  have ⟨hfL, hfh⟩ := f_le c L
  obtain hh := held_le c
  obtain ⟨s₁, run₁, x19₁, x21₁, x22₁, x23₁, g₁, sp₁, m₁, rd₁, wr₁⟩ :=
    save_ok s₀ hp.x4 fun d _ h => hp.inS (by omega_using [h])
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (held_wp hcl (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), hdx]))
    fun s₂ ⟨x9₂, g₂, sp₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (fill_wp (St := St) (D := D) hL x9₂ (by rw [g₂ _ (by decide) (by decide), x22₁, hp.x3'])
    (by rw [g₂ _ (by decide) (by decide), x19₁, hp.x0]) (by rw [g₂ _ (by decide) (by decide), x21₁, hp.x2]))
    fun s₃ ⟨x8₃, x10₃, x6₃, x7₃, g₃, sp₃, m₃, rd₃, wr₃⟩ => ?_)
  obtain dCp : Region.Sub ⟨St + BitVec.ofNat 64 (408 + held c), fOf c L⟩ ⟨St, 416⟩ :=
    Offset.sub_base St (by omega_using [hfh])
  refine WP.seq (WP.mono (copy_ok s₃ (P := D) (C := St + BitVec.ofNat 64 (408 + held c)) (L := fOf c L)
    (by omega_using [hfh]) x7₃ x6₃ x8₃
    (fun i hi => by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact hp.inD (by omega_using [hfL, hi]))
    (fun i hi => by rw [wr₃, wr₂, wr₁, Offset.add_add]; exact hp.inSt (by omega_using [hfh, hi]))
    ((hp.st_d.sub_left dCp).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  -- The registers `chain1` reads, unchanged since `save`.
  have g (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x8) (d : r ≠ .x9) (e : r ≠ .x10) (f : r ≠ .x11) :
      s₄.gpr r = s₁.gpr r := by
    rw [h₄.other r a b c d, g₃ r a b c e f, g₂ r d e]
  refine WP.mono (chain1_wp (St := St) (S := S) hfL hL
    (by rw [g .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x21₁, hp.x2])
    (by rw [h₄.other _ (by decide) (by decide) (by decide) (by decide), x10₃])
    (by rw [g .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x22₁, hp.x3'])
    (by rw [g .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x19₁, hp.x0])
    (by rw [g .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x23₁]))
    fun s₅ h₅ => ?_
  obtain ⟨x21₅, x22₅, x3₅, x0₅, x1₅, x2₅, x4₅, sv₅, sp₅, m₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (hr : r ∈ preserved) (a : r ≠ .x21) (b : r ≠ .x22) : s₅.gpr r = s₁.gpr r := by
    obtain hcc : ∀ r ∈ preserved, r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 := by decide
    obtain hc := hcc r hr
    rw [sv₅ r hr a b, g r hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2]
  obtain hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃, rd₂, rd₁]
  obtain hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃, wr₂, wr₁]
  obtain hb1 : 8 * b1Of c L ≤ 8 := by unfold b1Of; split <;> omega_using []
  obtain c408 : Region.Sub ⟨St + BitVec.ofNat 64 408, 8 * b1Of c L⟩ ⟨St, 416⟩ :=
    Offset.sub_base St (by omega_using [hb1])
  obtain m₀ : s₅.mem = m4 s₀ St D S c L := by rw [m₅, h₄.mem, m₃, m₂, m₁, m4]
  subst hc
  refine ⟨hp.uargs x0₅ x1₅ x2₅ (by rw [x3₅, b1Of, leftOf]) x4₅ hrd hwr (by omega_using [hb1])
      (Offset.disjoint St (by omega_using []) (by omega_using [hb1]) (by omega_using []))
      ((hp.st_s.sub_left c408).sub_right (Region.sub_prefix (by decide)))
      (by rw [toNat_add_lt St hw (by decide)]; omega_using [hw, hb1])
      ⟨⟨St, 416⟩, by simp, 408, rfl, by simp; omega_using [hb1]⟩,
    by rw [k .x19 (by simp [preserved]) (by decide) (by decide), x19₁, hp.x0],
    x21₅, by rw [x22₅]; rfl, by rw [k .x23 (by simp [preserved]) (by decide) (by decide), x23₁],
    fun r hr a b c d => by rw [k r hr b c, g₁ r a b c d],
    by rw [sp₅, h₄.sp, sp₃, sp₂, sp₁], m₀, hrd, hwr⟩

end VG.Proof.CmacTripleDes.Stream.AArch64

end

/-!
# Streaming TDEA-CMAC on AArch64: `vg_cmac_triple_des_absorb` is correct

After `absorbPre`, the first run of `update` chains the block held back if
data is left (`b1`), the second the whole blocks of the data left but its
last 1 to 8 bytes (`nb`), and the last copy holds those back. If no data is
left (`len ≤ 8 - h`), the runs chain nothing and the copy copies nothing,
and the data is appended to the bytes held back (`repr_fill`); otherwise
`repr_chain`.
-/

namespace VG.Proof.CmacTripleDes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacTripleDes.Stream.AArch64 VG.WriteBytes
open VG.Proof.Cmac (bytesAt_frame)
open VG.Proof.CmacTripleDes.Stream (held held_le)

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega_using [hi]) (by omega_using [hp, hi])) hc

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 8 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 8 1 = [Spec.Aes.bytesAt m p 8] := by
  simp [Spec.Cmac.blocksAt]

/-- What the first part of `absorb` (up to and with the first run of `update`)
leaves, for the second. -/
structure AAfter₁ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = St
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (fOf (s₀.gpr .x1).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (leftOf (s₀.gpr .x1).toNat L)
  x23 : s.gpr .x23 = S
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorb₁_after {s₀ : State} {St D S : Addr} {L : Nat} (hp : APre s₀ St D S L) :
    WP isa absorb₁ s₀ (AAfter₁ s₀ St D S L) :=
  WP.seq (WP.mono (absorbPre_wp hp) fun _ h =>
    WP.mono (upd_wp h.args) fun _ h₆ =>
      ⟨by rw [h₆.saved _ (by simp [preserved]), h.x19], by rw [h₆.saved _ (by simp [preserved]), h.x21],
        by rw [h₆.saved _ (by simp [preserved]), h.x22], by rw [h₆.saved _ (by simp [preserved]), h.x23],
        by rw [h₆.sp, h.sp], by rw [h₆.rd, h.rd], by rw [h₆.wr, h.wr]⟩)

/-- What the second part (`chain2` and the second run of `update`) leaves,
for `absorbPost`. -/
structure AAfter₂ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = St
  x20 : s.gpr .x20 = BitVec.ofNat 64 (8 * nbOf (s₀.gpr .x1).toNat L)
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (fOf (s₀.gpr .x1).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (leftOf (s₀.gpr .x1).toNat L)
  x23 : s.gpr .x23 = S
  sp : s.sp = s₀.sp

theorem absorb₂_after {s₀ s : State} {St D S : Addr} {L : Nat} (hp : APre s₀ St D S L)
    (h : AAfter₁ s₀ St D S L s) : WP isa absorb₂ s (AAfter₂ s₀ St D S L) := by
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .x1).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  obtain hsum := nb_le c L
  obtain ⟨x19₆, x21₆, x22₆, x23₆, sp₆, rd₆, wr₆⟩ := h
  rw [hc] at x21₆ x22₆
  refine WP.seq (WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_using [hL]) x22₆) fun s₇ h₇ => ?_)
  obtain ⟨x20₇, x3₇, x0₇, x1₇, x2₇, x4₇, sv₇, sp₇, m₇, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 8) = nbOf c L := rfl
  rw [hnb] at x20₇ x3₇
  obtain dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L), 8 * nbOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega_using [hsum])
  obtain c400 : Region.Sub ⟨St + BitVec.ofNat 64 400, 8⟩ ⟨St, 416⟩ := Offset.sub_base St (by decide)
  obtain args₇ := hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf c L)) (n := nbOf c L)
    (by rw [x0₇, x19₆]) (by rw [x1₇, x19₆]) (by rw [x2₇, x21₆]) x3₇ (by rw [x4₇, x23₆])
    (by rw [rd₇, rd₆]) (by rw [wr₇, wr₆]) (by omega_using [hL, hsum]) ((hp.st_d.sub_left c400).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : nbOf c L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf c L)).isLt; omega_using []
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_arith)]; omega_using [hsum, this])
    ⟨⟨D, L⟩, by simp, fOf c L, rfl, by simp; omega_using [hsum]⟩
  refine WP.mono (upd_wp args₇) fun s₈ h₈ => ?_
  subst hc
  exact ⟨by rw [h₈.saved _ (by simp [preserved]), sv₇ _ (by simp [preserved]) (by decide), x19₆],
    by rw [h₈.saved _ (by simp [preserved]), x20₇],
    by rw [h₈.saved _ (by simp [preserved]), sv₇ _ (by simp [preserved]) (by decide), x21₆],
    by rw [h₈.saved _ (by simp [preserved]), sv₇ _ (by simp [preserved]) (by decide), x22₆],
    by rw [h₈.saved _ (by simp [preserved]), sv₇ _ (by simp [preserved]) (by decide), x23₆],
    by rw [h₈.sp, sp₇, sp₆]⟩

theorem absorb_wp {s₀ : State} (h0 : absorbAArch64.pre s₀) :
    WP isa absorb s₀ fun s' => ((∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp) ∧
      absorbAArch64.post s₀ s' := by
  obtain hp := APre.of h0
  generalize s₀.gpr .x0 = St at hp
  generalize s₀.gpr .x2 = D at hp
  generalize s₀.gpr .x4 = S at hp
  generalize (s₀.gpr .x3).toNat = L at hp
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .x1).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have hw := hp.wSt
  have hsw := hp.wS
  have ⟨hfL, hfh⟩ := f_le c L
  obtain hsum := nb_le c L
  obtain hh := held_le c
  refine WP.seq (WP.seq (WP.mono (absorbPre_wp hp) fun s₅ h₅ => ?_))
  obtain ⟨args₅, x19₅, x21₅, x22₅, x23₅, o₅, sp₅, m₅, rd₅, wr₅⟩ := h₅
  rw [hc] at args₅ x21₅ x22₅ m₅
  refine WP.mono (upd_wp args₅) fun s₆ h₆ => ?_
  have k₆ (r : Reg) (hr : r ∈ preserved) : s₆.gpr r = s₅.gpr r := h₆.saved r hr
  refine WP.seq (WP.seq (WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_using [hL])
    (by rw [k₆ .x22 (by simp [preserved]), x22₅])) fun s₇ h₇ => ?_))
  obtain ⟨x20₇, x3₇, x0₇, x1₇, x2₇, x4₇, sv₇, sp₇, m₇, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 8) = nbOf c L := rfl
  rw [hnb] at x20₇ x3₇
  have k₇ (r : Reg) (hr : r ∈ preserved) (a : r ≠ .x20) : s₇.gpr r = s₅.gpr r := by
    rw [sv₇ r hr a, k₆ r hr]
  obtain dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L), 8 * nbOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega_using [hsum])
  obtain c400 : Region.Sub ⟨St + BitVec.ofNat 64 400, 8⟩ ⟨St, 416⟩ := Offset.sub_base St (by decide)
  obtain args₇ := hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf c L)) (n := nbOf c L)
    (by rw [x0₇, k₆ .x19 (by simp [preserved]), x19₅])
    (by rw [x1₇, k₆ .x19 (by simp [preserved]), x19₅])
    (by rw [x2₇, k₆ .x21 (by simp [preserved]), x21₅]) x3₇
    (by rw [x4₇, k₆ .x23 (by simp [preserved]), x23₅]) (by rw [rd₇, h₆.rd, rd₅])
    (by rw [wr₇, h₆.wr, wr₅]) (by omega_using [hL, hsum]) ((hp.st_d.sub_left c400).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : nbOf c L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf c L)).isLt; omega_using []
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_arith)]; omega_using [hsum, this])
    ⟨⟨D, L⟩, by simp, fOf c L, rfl, by simp; omega_using [hsum]⟩
  refine WP.mono (upd_wp args₇) fun s₈ h₈ => ?_
  have k₈ (r : Reg) (hr : r ∈ preserved) : s₈.gpr r = s₇.gpr r := h₈.saved r hr
  obtain ⟨s₉, run₉, x21₉, x22₉, x6₉, x7₉, x8₉, sv₉, sp₉, m₉, rd₉, wr₉⟩ := rest_ok (s := s₈) (D := D)
    (a := fOf c L) (x := leftOf c L) (n := nbOf c L) (by unfold leftOf; omega_using [hsum])
    (by rw [k₈ .x21 (by simp [preserved]), k₇ .x21 (by simp [preserved]) (by decide), x21₅])
    (by rw [k₈ .x20 (by simp [preserved]), x20₇])
    (by rw [k₈ .x22 (by simp [preserved]), k₇ .x22 (by simp [preserved]) (by decide), x22₅])
  refine WP.seq (WP.of_runBlock ⟨s₉, run₉, ?_⟩)
  obtain rd₉' : s₉.rd = s₀.rd := by rw [rd₉, h₈.rd, rd₇, h₆.rd, rd₅]
  obtain wr₉' : s₉.wr = s₀.wr := by rw [wr₉, h₈.wr, wr₇, h₆.wr, wr₅]
  obtain dR : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L + 8 * nbOf c L), restOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega_using [hsum])
  obtain hrr : restOf c L ≤ 8 := by unfold restOf nbOf leftOf; split <;> omega_arith
  obtain sR : Region.Sub ⟨St + BitVec.ofNat 64 408, restOf c L⟩ ⟨St, 416⟩ :=
    Offset.sub_base St (by omega_using [hrr])
  refine WP.seq (WP.mono (copy_ok s₉ (P := D + BitVec.ofNat 64 (fOf c L + 8 * nbOf c L))
    (C := St + BitVec.ofNat 64 408) (L := restOf c L) (by omega_using [hrr]) x7₉
    (by rw [x6₉, k₈ .x19 (by simp [preserved]), k₇ .x19 (by simp [preserved]) (by decide), x19₅]) x8₉
    (fun i hi => by rw [rd₉', wr₉', Offset.add_add]; exact hp.inD (by omega_using [hsum, hi]))
    (fun i hi => by rw [wr₉', Offset.add_add]; exact hp.inSt (by omega_using [hrr, hi]))
    ((hp.st_d.sub_left sR).symm.sub_left dR)) fun s₁₀ h₁₀ => ?_)
  obtain x23₁₀ : s₁₀.gpr .x23 = S := by
    rw [h₁₀.other _ (by decide) (by decide) (by decide) (by decide),
      sv₉ _ (by simp [preserved]) (by decide) (by decide),
      k₈ .x23 (by simp [preserved]), k₇ .x23 (by simp [preserved]) (by decide), x23₅]
  obtain ⟨s₁₁, run₁₁, slot₁₁, keep₁₁, sp₁₁, m₁₁⟩ := restore_ok s₁₀ x23₁₀
    (fun d _ h => by
      rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉']
      obtain ⟨r, hr, hc⟩ := hp.inS (d := d) (n := 8) (by omega_using [h])
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
  refine WP.of_runBlock ⟨s₁₁, run₁₁, ?_⟩
  -- The frames.
  obtain hlf : (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf c L)).length = fOf c L :=
    Proof.Cmac.bytesAt_length _ _ _
  obtain hlr : (Spec.Aes.bytesAt s₉.mem (D + BitVec.ofNat 64 (fOf c L + 8 * nbOf c L)) (restOf c L)).length =
    restOf c L := Proof.Cmac.bytesAt_length _ _ _
  obtain fS : Frame [⟨S + BitVec.ofNat 64 640, 40⟩] s₀.mem (absSavedMem s₀ S) := absSavedMem_frame _ _
  obtain fC1 : Frame [⟨St + BitVec.ofNat 64 (408 + held c), fOf c L⟩] (absSavedMem s₀ S) s₅.mem := by
    rw [m₅, m4]; exact writeBytes_frame _ _ _ (by rw [hlf]; exact Region.contains_self _ _)
  have f6 : Frame [⟨St + BitVec.ofNat 64 400, 8⟩, ⟨S, 640⟩] s₅.mem s₆.mem := h₆.frame
  obtain f8 : Frame [⟨St + BitVec.ofNat 64 400, 8⟩, ⟨S, 640⟩] s₆.mem s₈.mem := by
    rw [← m₇]; exact h₈.frame
  obtain fC2 : Frame [⟨St + BitVec.ofNat 64 408, restOf c L⟩] s₈.mem s₁₁.mem := by
    rw [m₁₁, h₁₀.mem, m₉]
    exact writeBytes_frame _ _ _ (by rw [← m₉, hlr]; exact Region.contains_self _ _)
  let K : List Region := [⟨S + BitVec.ofNat 64 640, 40⟩, ⟨St + BitVec.ofNat 64 (408 + held c), fOf c L⟩,
    ⟨St + BitVec.ofNat 64 400, 8⟩, ⟨S, 640⟩, ⟨St + BitVec.ofNat 64 408, restOf c L⟩]
  obtain F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  obtain F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  obtain F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  obtain F11 : Frame K s₀.mem s₁₁.mem := F8.trans (fC2.mono (by simp [K]))
  -- The key and the data are in none of these.
  obtain dK : ∀ r ∈ K, (⟨St, 400⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base S (by decide))
    · exact Offset.base_disjoint St (by omega_using []) (by omega_using [hfh])
    · exact Offset.base_disjoint St (by omega_using []) (by omega_using [])
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    · exact Offset.base_disjoint St (by omega_using []) (by omega_using [hrr])
  obtain dDat : ∀ r ∈ K, (⟨D, L⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.d_s.sub_right (Offset.sub_base S (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_using [hfh]))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by decide))
    · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_using [hrr]))
  obtain k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
  refine ⟨⟨fun r hr => ?_, by rw [sp₁₁, h₁₀.sp, sp₉, h₈.sp, sp₇, h₆.sp, sp₅]⟩, ?_⟩
  · -- The registers, restored from their slots.
    obtain Fp : Frame K.tail (absSavedMem s₀ S) s₁₁.mem :=
      ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
        ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
    have slot (d : Nat) (h₁ : 640 ≤ d) (h₂ : d + 8 ≤ 680) :
        s₁₀.mem.readW (S + BitVec.ofNat 64 d) 64 = (absSavedMem s₀ S).readW (S + BitVec.ofNat 64 d) 64 := by
      rw [← m₁₁]
      obtain sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 688⟩ := Offset.sub_base S (by omega_using [h₂])
      refine Fp.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hfh]))).symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
      · exact Offset.disjoint_base S (by omega_using [h₁]) (by omega_using [h₂])
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hrr]))).symm.sub_left sub
    have sl {r : Reg} {d : Nat} (h : (r, d) ∈ saved) : s₁₁.gpr r = s₀.gpr r := by
      obtain hd : 640 ≤ d ∧ d + 8 ≤ 680 := by
        simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
        omega
      rw [slot₁₁ r d h, slot d hd.1 hd.2, absSaved_slot s₀ S h]
    obtain hc' : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 →
        r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 := by decide
    have oth (r : Reg) (hr : r ∈ preserved) (a : r ≠ .x19) (b : r ≠ .x20) (c : r ≠ .x21) (d : r ≠ .x22)
        (e : r ≠ .x23) : s₁₁.gpr r = s₀.gpr r := by
      obtain ⟨n6, n7, n8, n9⟩ := hc' r hr a b c d e
      rw [keep₁₁ r a b c d e, h₁₀.other r n6 n7 n8 n9, sv₉ r hr c d, k₈ r hr, k₇ r hr b,
        o₅ r hr a c d e]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sl (d := 640) (by simp [saved])
    · exact sl (d := 648) (by simp [saved])
    · exact sl (d := 656) (by simp [saved])
    · exact sl (d := 664) (by simp [saved])
    · exact sl (d := 672) (by simp [saved])
    all_goals exact oth _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro key msg hr hcnt hlen
    rw [hp.x0] at hr ⊢
    rw [hp.x2, hp.x3]
    rw [hp.x3] at hlen
    obtain hcm : c = msg.length := by rw [← hc, hcnt, toNat_ofNat (by omega_using [hlen])]
    subst hcm
    obtain hsch := ((Proof.CmacTripleDes.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    obtain ciph : ∀ m : Mem, Frame K s₀.mem m →
        Proof.CmacTripleDes.AArch64.ciphAt m St = Spec.Cmac.tdes key := fun m hf => by
      simp only [Proof.CmacTripleDes.AArch64.ciphAt, Spec.Cmac.tdes]
      rw [Proof.CmacTripleDes.scheduleAt_congr fun i hi => frame_at hf dK (by omega_using [hw]) (by omega_using [hi]),
        hsch]
    -- The data, wherever it is read.
    obtain dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem D L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m D hab, bytesAt_frame hf dDat (by omega_using [hlen])]
    obtain fS' : Frame K s₀.mem (absSavedMem s₀ S) := fS.mono (by simp [K])
    -- The chaining value.
    obtain cv5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 400) 8 =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 400) 8 := by
      rw [bytesAt_frame fC1 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint St (by omega_using []) (by omega_using []) (by omega_using [hfh]))
          (by decide),
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).sub_right (Offset.sub_base S (by decide)))
          (by decide)]
    obtain cv11 : Spec.Aes.bytesAt s₁₁.mem (St + BitVec.ofNat 64 400) 8 =
        Spec.Aes.bytesAt s₈.mem (St + BitVec.ofNat 64 400) 8 :=
      bytesAt_frame fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint St (by omega_using []) (by omega_using []) (by omega_using [hrr]))
        (by decide)
    have out6 := h₆.out
    rw [ciph _ F5] at out6
    have out8 := h₈.out
    rw [m₇, ciph _ F6] at out8
    obtain hk : ∀ i < 400, s₁₁.mem (St + BitVec.ofNat 64 i) = s₀.mem (St + BitVec.ofNat 64 i) :=
      fun i hi => frame_at F11 dK (by omega_using [hw]) hi
    obtain hdl : (Spec.Aes.bytesAt s₀.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    obtain hb5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 408) (held msg.length + fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 408) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem D L).take (fOf msg.length L) := by
      obtain e := bytesAt_writeBytes (absSavedMem s₀ S) (St + BitVec.ofNat 64 408) (held msg.length)
        (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf msg.length L)) (by rw [hlf]; omega_using [hfh])
      rw [hlf] at e
      rw [m₅, m4, ← Offset.add_add, e,
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hh]))).sub_right
            (Offset.sub_base S (by decide)))
          (by omega_using [hh])]
      refine congrArg (_ ++ ·) ?_
      have := dat _ fS' 0 (fOf msg.length L) (by omega_using [hsum])
      rwa [k0, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem D L = d at hdl hb5 dat ⊢
    by_cases hx : leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      obtain hfL' : fOf msg.length L = L := by unfold leftOf at hx; omega_using [hsum, hx]
      obtain hb : b1Of msg.length L = 0 := by simp [b1Of, hx]
      obtain hn : nbOf msg.length L = 0 := by simp [nbOf, hx]
      obtain hr0 : restOf msg.length L = 0 := by simp [restOf, hn, hx]
      obtain m118 : s₁₁.mem = s₈.mem := by
        rw [m₁₁, h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem
          (D + BitVec.ofNat 64 (fOf msg.length L + 8 * nbOf msg.length L)) 0 = [] from rfl, writeBytes_nil]
      refine Proof.CmacTripleDes.Stream.repr_fill hr hk
        (by rw [hdl]; have := (f_le msg.length L).2; omega_using [hfL', this]) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 400) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 400) _
        rw [cv11, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
        exact cv5
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 408) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 408) _ ++ _
        obtain sub : Region.Sub ⟨St + BitVec.ofNat 64 408, held msg.length + L⟩ ⟨St, 416⟩ :=
          Offset.sub_base St (by omega_using [hfh, hfL'])
        obtain dj : ∀ r ∈ [⟨St + BitVec.ofNat 64 400, 8⟩, ⟨S, 640⟩],
            (⟨St + BitVec.ofNat 64 408, held msg.length + L⟩ : Region).Disjoint r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega_using []) (by omega_using [hfh, hfL']) (by omega_using [])
          · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
        have hb5' := hb5
        rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
        rw [m118, hdl, bytesAt_frame f8 dj (by omega_using [hfh, hfL']),
          bytesAt_frame f6 dj (by omega_using [hfh, hfL']), hb5']
    · -- The block held back is complete, and more blocks may follow.
      obtain hlt : 8 - held msg.length < L := by unfold leftOf fOf at hx; omega_using [hx]
      obtain hf' : fOf msg.length L = 8 - held msg.length := by unfold fOf; omega_using [hlt]
      obtain hb : b1Of msg.length L = 1 := by simp [b1Of, hx]
      obtain hn : nbOf msg.length L = Proof.CmacTripleDes.Stream.nblocks msg.length L := by
        simp only [nbOf, hx, ↓reduceIte]
        unfold leftOf Proof.CmacTripleDes.Stream.nblocks
        rw [hf']
      have hb5' := hb5
      rw [hf', Nat.add_sub_cancel' hh] at hb5'
      refine Proof.CmacTripleDes.Stream.repr_chain hr hk (by rw [hdl]; exact hlt) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 400) _ =
          Spec.Cmac.chain _ (Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 400) _)
            ([Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 408) _ ++ _] ++ _)
        rw [cv11, out8, out6, hb, blocksAt_one, cv5, Proof.Cmac.chain_append,
          Proof.CmacTripleDes.Stream.blocksAt_eq, dat _ F6 _ _ (by omega_using [hsum]), hb5', hdl, hf', hn]
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 408) _ = _
        obtain e := bytesAt_writeBytes_self s₈.mem (St + BitVec.ofNat 64 408)
          (xs := Spec.Aes.bytesAt s₈.mem (D + BitVec.ofNat 64 (fOf msg.length L + 8 * nbOf msg.length L))
            (restOf msg.length L)) (by rw [Proof.Cmac.bytesAt_length]; omega_using [hrr])
        rw [Proof.Cmac.bytesAt_length] at e
        obtain hr' : d.length - (8 - held msg.length) - 8 * Proof.CmacTripleDes.Stream.nblocks msg.length d.length =
            restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        rw [hr', m₁₁, h₁₀.mem, m₉, e, dat _ F8 _ _ (by omega_using [hsum]),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega_using []),
          List.drop_drop, hdl, ← hn, hf']

end VG.Proof.CmacTripleDes.Stream.AArch64

end

end


/-!
# Streaming TDEA-CMAC on AArch64: `Verified`

Correctness, constant time and satisfiability under this target's contracts
(`Contract.lean`), and the shared contracts with the working space as an
argument (`Proof/CmacTripleDes/StreamScratch.lean`), which imply them, with
no stack: the functions call nothing.

`absorb` is constant time in three parts: the taint analysis covers each
(`CT.lean`), the second and the third from the registers the part before
leaves, which its correctness proof pins to the public arguments (`AAfter₁`,
`AAfter₂`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.AArch64

open VG VG.AArch64 VG.Impl.CmacTripleDes.Stream.AArch64

/-- States agree on the registers `rs` and the stack pointer. -/
theorem agree_of {rs : List Reg} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.AArch64.Taint.Agree (Taint.ofRegs rs) s₁ s₂ :=
  ⟨hsp, fun r hr => h r (VG.AArch64.Taint.mem_ofRegs.mp hr)⟩

theorem absorb_rel {s₀ s₀' : State} (h0 : absorbAArch64.pre s₀) (h0' : absorbAArch64.pre s₀')
    (hq : absorbAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') absorb fun _ _ => True := by
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := hq
  obtain hp := APre.of h0
  obtain hp' : APre s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x4) (s₀.gpr .x3).toNat := by
    rw [q0, q2, q3, q4]; exact APre.of h0'
  generalize s₀.gpr .x0 = St at hp hp'
  generalize s₀.gpr .x2 = D at hp hp'
  generalize s₀.gpr .x4 = S at hp hp'
  generalize (s₀.gpr .x3).toNat = L at hp hp'
  obtain ⟨_, hA⟩ := absorb₁_taint
  obtain ⟨_, hB⟩ := absorb₂_taint
  obtain ⟨_, hC⟩ := absorb₃_taint
  obtain a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of q5 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [q0, q1, q2, q3, q4]) hA).wp
    (F₁ := AAfter₁ s₀ St D S L) (F₂ := AAfter₁ s₀' St D S L) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨absorb₁_after hp, absorb₁_after hp'⟩
  obtain m := (RelCT.taint (A := taint) (P := fun a b => AAfter₁ s₀ St D S L a ∧ AAfter₁ s₀' St D S L b) _
    (fun a b h => by
      refine agree_of (by rw [h.1.sp, h.2.sp, q5]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.x19, h.2.x19]
      · rw [h.1.x21, h.2.x21, q1]
      · rw [h.1.x22, h.2.x22, q1]
      · rw [h.1.x23, h.2.x23]) hB).wp
    (F₁ := AAfter₂ s₀ St D S L) (F₂ := AAfter₂ s₀' St D S L) fun a b h =>
      ⟨absorb₂_after hp h.1, absorb₂_after hp' h.2⟩
  obtain p := RelCT.taint (A := taint) (P := fun a b => AAfter₂ s₀ St D S L a ∧ AAfter₂ s₀' St D S L b) _
    (fun a b h => by
      refine agree_of (by rw [h.1.sp, h.2.sp, q5]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.x19, h.2.x19]
      · rw [h.1.x20, h.2.x20, q1]
      · rw [h.1.x21, h.2.x21, q1]
      · rw [h.1.x22, h.2.x22, q1]
      · rw [h.1.x23, h.2.x23]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)

theorem absorb_ct : ConstantTime isa absorbAArch64.pre absorbAArch64.pub absorb :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

theorem init_correct (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa streamInit s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  WP.withPreservedV (WP.mono (init_wp hs) fun _ ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩) (by lit_decide)

theorem absorb_correct (s : State) (hs : absorbAArch64.pre s) :
    ∃ t s', Exec isa absorb s t s' ∧ abiPreserved s s' ∧ absorbAArch64.post s s' :=
  WP.withPreservedV (absorb_wp hs) (by lit_decide)

theorem finish_correct (s : State) (hs : finishAArch64.pre s) :
    ∃ t s', Exec isa finish s t s' ∧ abiPreserved s s' ∧ finishAArch64.post s s' :=
  WP.withPreservedV (WP.mono (finish_wp hs) fun _ ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩) (by lit_decide)

theorem init_verified : Verified AArch64.target streamInit (streamInitScratchContract AArch64.abi 0) :=
  Verified.of_correct init_correct init_ct init_implies

theorem absorb_verified : Verified AArch64.target absorb (absorbScratchContract AArch64.abi 0) :=
  Verified.of_correct absorb_correct absorb_ct absorb_implies

theorem finish_verified : Verified AArch64.target finish (finishScratchContract AArch64.abi 0) :=
  Verified.of_correct finish_correct finish_ct finish_implies

end VG.Proof.CmacTripleDes.Stream.AArch64

end

end


/-!
# Streaming TDEA-CMAC on AArch64, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackScratch`): 640 bytes, and 688 for `absorb`. Their code uses
no other stack: it calls nothing, and the return address stays in `x30`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.AArch64

open VG VG.AArch64 VG.Impl.CmacTripleDes.Stream.AArch64

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition,
without the working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 416⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesStreamInitContract AArch64.abi 640).pre s := by
  implies_sat [Spec.Cmac.tdesStreamInitContract, Spec.Cmac.tdesStreamInitSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, AArch64.abi, AArch64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition, without
the working space (and with no data). -/
def absorbFrameSat : State := { absorbSat with wr := [⟨0x1000, 416⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.tdesAbsorbContract AArch64.abi 688).pre s := by
  implies_sat [Spec.Cmac.tdesAbsorbContract, Spec.Cmac.tdesAbsorbSig, Spec.Cmac.tdesAbsorbPost,
    AArch64.abi, AArch64.argRegs] [absorbFrameSat, absorbSat] using absorbFrameSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition, without
the working space. -/
def finishFrameSat : State := { finishSat with wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.tdesFinishContract AArch64.abi 640).pre s := by
  implies_sat [Spec.Cmac.tdesFinishContract, Spec.Cmac.tdesFinishSig, Spec.Cmac.tdesFinishPost,
    AArch64.abi, AArch64.argRegs] [finishFrameSat, finishSat] using finishFrameSat

theorem init_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 640 .x3 streamInit)
      (Spec.Cmac.tdesStreamInitContract AArch64.abi 640) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.tdesStreamInitSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesStreamInitPre AArch64.abi.ptrBits)
    (post := Spec.Cmac.tdesStreamInitPost AArch64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 640) init_verified (by decide) (by decide) initFrameSat_pre

theorem absorb_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 688 .x4 absorb)
      (Spec.Cmac.tdesAbsorbContract AArch64.abi 688) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.tdesAbsorbSig) (nm := "scratch") (e := .u64) (n := 86)
    (post := Spec.Cmac.tdesAbsorbPost AArch64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 688) absorb_verified (by decide) (by decide) absorbFrameSat_pre

theorem finish_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 640 .x3 finish)
      (Spec.Cmac.tdesFinishContract AArch64.abi 640) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.tdesFinishSig) (nm := "scratch") (e := .u64) (n := 80)
    (post := Spec.Cmac.tdesFinishPost AArch64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 640) finish_verified (by decide) (by decide) finishFrameSat_pre

end VG.Proof.CmacTripleDes.Stream.AArch64
