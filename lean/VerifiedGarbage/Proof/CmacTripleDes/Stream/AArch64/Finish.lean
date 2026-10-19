module

import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Common
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Contract
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.AArch64
public import VerifiedGarbage.Proof.CmacTripleDes.Stream
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cmac.Stream

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
  have r₁ : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 400) 8 := by
    rw [hp.rd, hp.wr, hp.x0]; exact ⟨⟨St, 416⟩, by simp, Offset.contains_base _ (by decide) (by omega)⟩
  have w₁ : InRegions s₀.wr (s₀.gpr .x2 + BitVec.ofNat 64 0) 8 := by
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
  have pSt : Region.Sub ⟨St + BitVec.ofNat 64 408, L⟩ ⟨St, 416⟩ := Offset.sub_base St (by omega)
  exact
  { x0 := x0, x1 := x1, x2 := x2, x3 := x3, x4 := x4, len := hL
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := hp.st_s.sub_left (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    ps := hp.st_s.sub_left pSt
    sts := hp.o_s
    wrapK := by omega
    wrapSt := hp.wO
    wrapP := by rw [toNat_add_lt St hw (by decide)]; omega
    wrapS := hp.wS
    reads := by
      rw [rd, wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 416⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 416⟩, by simp, 408, rfl, by simp; omega⟩
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
  have hc := (s₀.gpr .x1).isLt
  have h1 : s₀.gpr .x1 = BitVec.ofNat 64 (s₀.gpr .x1).toNat := ofNat_toNat_eq rfl
  by_cases h0 : (s₀.gpr .x1).toNat = 0
  · refine WP.ite true (by rw [eval_zero hc (by rw [x3₁]; exact h1), h0]; rfl)
      (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨hp.fargs (held_le _) x0₁ x1₁ x2₁ ?_ x4₁ rd₁ wr₁, m₁, sv₁, sp₁⟩
    rw [x3₁, h1, h0]; rfl
  · refine WP.ite false (by rw [eval_zero hc (by rw [x3₁]; exact h1)]; simp [h0])
      (fun h => by cases h) fun _ => ?_
    have hne : s₀.gpr .x1 ≠ 0 := fun e => h0 (by rw [e]; rfl)
    obtain ⟨s₂, run₂, x3₂, g₂, sp₂, m₂, rd₂, wr₂⟩ := lastLen_ok s₁ x3₁ hne
    refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
    have hc : ∀ r ∈ preserved, r ≠ .x3 ∧ r ≠ .x9 := by decide
    refine ⟨hp.fargs (held_le _) (by rw [g₂ _ (by decide) (by decide), x0₁])
      (by rw [g₂ _ (by decide) (by decide), x1₁]) (by rw [g₂ _ (by decide) (by decide), x2₁])
      x3₂ (by rw [g₂ _ (by decide) (by decide), x4₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]), by rw [m₂, m₁],
      fun r hr => by rw [g₂ r (hc r hr).1 (hc r hr).2, sv₁ r hr], by rw [sp₂, sp₁]⟩

theorem finish_wp {s₀ : State} (h0 : finishAArch64.pre s₀) :
    WP isa finish s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧
      finishAArch64.post s₀ s' := by
  have hp := HPre.of h0
  generalize s₀.gpr .x0 = St at hp
  generalize s₀.gpr .x2 = O at hp
  generalize s₀.gpr .x3 = S at hp
  have hw := hp.wSt
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.mono (fin_wp h₁.args) fun s₂ h₂ => ?_
  have f₁ : Frame [⟨O, 8⟩] s₀.mem s₁.mem := by rw [h₁.mem]; exact copyCv_frame _ _ _
  refine ⟨fun r hr => by rw [h₂.saved r hr, h₁.saved r hr], by rw [h₂.sp, h₁.sp], ?_⟩
  intro key msg hr hc hlen
  rw [hp.x0] at hr
  rw [hp.x2]
  have hr₁ : Spec.Cmac.tdesRepr s₁.mem St key msg :=
    Proof.CmacTripleDes.Stream.repr_congr_416 (fun i hi => f₁.bytes (R := ⟨St, 416⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.st_o) (by show 416 ≤ 2 ^ 64; decide) hi) hr
  obtain ⟨hm, hne, hst, happ⟩ := Proof.CmacTripleDes.Stream.repr_finish hr₁
  rw [Proof.CmacTripleDes.Stream.repr_iff] at hr₁
  obtain ⟨⟨_, hks, hsk⟩, -, -⟩ := hr₁
  have hn : (s₀.gpr .x1).toNat = msg.length := by rw [hc, toNat_ofNat hlen]
  have hciph : Proof.CmacTripleDes.AArch64.ciphAt s₁.mem St = Spec.Cmac.tdes key := by
    simp only [Proof.CmacTripleDes.AArch64.ciphAt, hks, Spec.Cmac.tdes]
  have e₂ : Spec.Aes.bytesAt s₁.mem O 8 = Spec.Aes.bytesAt s₁.mem (St + 400) 8 := by
    rw [h₁.mem, copyCv_bytes, show St + 400 = St + BitVec.ofNat 64 400 from rfl]
    exact (Proof.Cmac.bytesAt_frame (copyCv_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_o.sub_left (Offset.sub_base St (d := 400) (n := 8) (by decide))) (by decide)).symm
  have out := h₂.out (by rw [hciph]; exact hsk) _ hm (by rw [hn]; exact hne)
    (by rw [hciph, e₂]; exact hst)
  rw [out, hciph, hn, show St + BitVec.ofNat 64 408 = St + 408 from rfl, happ,
    Proof.CmacTripleDes.Stream.tdesCmac_eq]

end VG.Proof.CmacTripleDes.Stream.AArch64
