module

public import VerifiedGarbage.Proof.Ed25519.AArch64.FixedBase
public import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed25519.AArch64.Codec
import VerifiedGarbage.Proof.Ed25519.AArch64.FixedBaseLit
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddCodec
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddMemory
public import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ed25519.ScalarMul
public import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory

/-!
# Ed25519's base-point multiplication on AArch64: memory and the ABI

The comb's result, encoded (`scalarBaseEngine_ok`), written to `out` with the callee-saved registers
restored from the working space (`scalarBase_correct`), under the precondition by register
(`scalarBaseLocal`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Proof.Ed25519 VG.Proof.Ed25519.Word64
open VG.Spec.Ed25519 (bytesAt)

/-! ## What the steps keep -/

theorem ck_outside {base : Addr} {s t : State} (h : CK base s t) : Outside base 64 768 s.mem t.mem := fun x hx =>
  h.mem x (by omega_using [hx]) (by have hN : NIB = 768 := rfl; omega_using [hx, hN])

theorem CounterKeep.ck {base : Addr} {s t : State} (h : CounterKeep base s t) : CK base s t :=
  ⟨fun r h19 _ hc => h.gpr r hc h19, h.rd, h.wr, h.sp, TableFrame.workspace h.mem⟩

/-- A byte of a buffer apart from the working space is beyond it. -/
theorem farScr {p base : Addr} {n i : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hi : i < n)
    (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (off p i) := by
  refine Nat.le_of_not_lt fun hlt => hd _ (Offset.contains_base p (d := i) (n := 1) (by omega_using [hi]) (by omega_using [hi, hn])) ?_
  simp only [Region.Contains]; simp only [ofs, off] at hlt; omega_using [hlt]

theorem bytesAt32_frame {m m' : Mem} {p base : Addr} (hf : Frame [⟨base, 8192⟩] m m')
    (hd : (⟨p, 32⟩ : Region).Disjoint ⟨base, 8192⟩) : bytesAt m' p 32 = bytesAt m p 32 := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, 32⟩) (by simpa only [List.mem_singleton, forall_eq])
    (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

/-! ## The engine -/

/-- The scalar's nibbles and the comb: `[s]B` in slots 0–3. -/
theorem scalarBaseEngine_ok [Divstep.Sound] {s : State} {base k T : Addr} (hs : Scr s base) (hp : s.gpr .x1 = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1) (hd : ∀ q < 32, 8192 ≤ ofs base (off k q))
    (htb : TblAt s base T) (hT : s.syms combSym = T) :
    WP isa scalarBaseEngine s fun t => CK base s t ∧
      Spec.Ed25519.encodeLE 32 (val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7)) =
        Spec.Ed25519.scalarBase (bytesAt s.mem k 32) := by
  rw [scalarBaseEngine]
  refine WP.seq (WP.mono_syms (scalarNibbles_ok hs hp hr hd) fun a ⟨ka, na⟩ sya => ?_)
  obtain hsa := ka.scratch hs
  obtain hta : TblAt a base T := htb.of_far (by rw [ka.rd, ka.wr])
    fun x hx => ck_outside ka x (Or.inr (by omega_using [hx]))
  obtain hS : Spec.Ed25519.decodeLE (bytesAt s.mem k 32) < 2 ^ 256 := by
    obtain h := decodeLE_lt (bytesAt s.mem k 32)
    rw [bytesAt_length] at h
    exact h
  refine WP.seq (WP.mono (combMultiply_ok hsa hta (by rw [sya, hT]) hS na) fun b ⟨pb, kb⟩ => ?_)
  refine WP.mono (pointEncode_ok (kb.scratch hsa)) fun t ⟨kt, vt⟩ => ⟨(ka.trans kb).trans kt.ck, ?_⟩
  rw [vt, Spec.Ed25519.scalarBase, encodePoint_rep (pointMul_rep _ basePoint_rep), ← encodePoint_rep pb]
  rfl

/-! ## The function -/

theorem scalarBaseSetup_ok (s : State) (hw : (⟨s.gpr .x2, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarBaseSetup) s fun t =>
      t.gpr .x0 = s.gpr .x2 ∧ (∀ r, r ≠ .x0 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.mem.readW (off (s.gpr .x2) 48) 64 = s.gpr .x0 ∧ Outside (s.gpr .x2) 48 8 s.mem t.mem := by
  have hin : InRegions s.wr (off (s.gpr .x2) 48) 8 := ⟨_, hw, contains_sc (by decide)⟩
  apply WP.of_runBlock
  simp only [scalarBaseSetup, mov, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, State.store, read_x,
    BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, hin, show (0 : Nat) < 4096 from by decide,
    BitVec.add_zero, RegUpd.gpr_write, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [hr, ite_false]
  · rw [RegUpd.mem_write, write64_eq_writeW]; exact Mem.readW_writeW_self64 _ _ _
  · rw [RegUpd.mem_write, write64_eq_writeW]; exact writeW_outside _ _ _ (by decide)

theorem scalarBaseFinishArgs_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block scalarBaseFinishArgs) s fun t =>
      t.gpr .x2 = base ∧ t.gpr .x0 = s.mem.readW (off base 48) 64 ∧ Keeps [.x2, .x0] s t := by
  have hin : InRegions (s.rd ++ s.wr) (off base 48) 8 := ⟨_, List.mem_append_right _ hs.wr, contains_sc (by decide)⟩
  apply WP.of_runBlock
  simp only [scalarBaseFinishArgs, mov, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, State.load, read_x,
    BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, hs.x0, hin, show (0 : Nat) < 4096 from by decide,
    BitVec.add_zero, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, reduceCtorEq, ite_true, ite_false,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- `vg_ed25519_scalar_base(out = x0, scalar = x1, scratch = x2)`, with the comb's tables at the
static's address. -/
def scalarBaseLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .x1, 32⟩, tblRegion s] ∧ s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩] ∧
    (⟨s.gpr .x1, 32⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
    (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64 ∧ CombHeld s [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩]
  post s t := bytesAt t.mem (s.gpr .x0) 32 = Spec.Ed25519.scalarBase (bytesAt s.mem (s.gpr .x1) 32)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧
    s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧ s.syms combSym = t.syms combSym

/-- The bytes of `scratch` (at `base`) from 1024 on keep their values: the function writes only
its first 1024 bytes. -/
def ScratchTail (base : Addr) (m m' : Mem) : Prop :=
  ∀ i, 1024 ≤ i → i < 8192 → m' (base + BitVec.ofNat 64 i) = m (base + BitVec.ofNat 64 i)

/-- A byte of `scratch` beyond 1024 is outside the bytes a step changes. -/
theorem outside_tail {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    (hon : o + n ≤ 1024) {i : Nat} (hi : 1024 ≤ i) (hi' : i < 8192) :
    m' (base + BitVec.ofNat 64 i) = m (base + BitVec.ofNat 64 i) :=
  h _ (Or.inr (by rw [show base + BitVec.ofNat 64 i = off base i from rfl, ofs_off' base (by omega_using [hi'])]; omega_using [hon, hi]))

/-- What an engine between `scalarBaseSetup` and `scalarBaseFinish` does: from the working space
and the scalar at `k` in `x1`, the result `R` of the scalar's bytes in `x4`–`x7`. -/
def EngineOk (e : Prog isa) (R : List Byte → List Byte) : Prop :=
  ∀ {s : State} {base k T : Addr}, Scr s base → s.gpr .x1 = k →
    (∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1) → (∀ q < 32, 8192 ≤ ofs base (off k q)) →
    TblAt s base T → s.syms combSym = T →
    WP isa e s fun t => CK base s t ∧
      Proof.X25519.leBytes 32 (val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7)) = R (bytesAt s.mem k 32)

/-- The setup, an engine and the finish: the engine's result at `out`, and the callee-saved
registers restored; and the first 1024 bytes of `scratch` alone are written. -/
theorem baseWrap_ok {e : Prog isa} {R : List Byte → List Byte} (he : EngineOk e R)
    (hv : (Code.seq (.block (scalarSave ++ scalarBaseSetup)) (.seq e scalarBaseFinish) : Prog isa).allInstrs keepsV = true)
    {s : State} (hs : scalarBaseLocal.pre s) :
    WP isa (.seq (.block (scalarSave ++ scalarBaseSetup)) (.seq e scalarBaseFinish)) s fun t => abiPreserved s t ∧
      bytesAt t.mem (s.gpr .x0) 32 = R (bytesAt s.mem (s.gpr .x1) 32) ∧
      (Region.Disjoint ⟨s.gpr .x0, 32⟩ ⟨s.gpr .x2, 8192⟩ → ScratchTail (s.gpr .x2) s.mem t.mem) := by
  apply WP.withPreservedV (hc := hv)
  obtain ⟨hr, hw, hd, hn, hct⟩ := hs
  have hws : (⟨s.gpr .x2, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  apply WP.seq
  rw [WP.block_append_iff]
  have htb : TblAt s (s.gpr .x2) (s.syms combSym) := hct.tblAt (by rw [hr]; simp) (by simp)
  refine WP.mono_syms (scalarSave_ok rfl hws) fun a ⟨ga, ra, wa, spa, ma, sva⟩ sya => ?_
  have hwa : (⟨a.gpr .x2, 8192⟩ : Region) ∈ a.wr := by rw [ga, wa]; exact hws
  refine WP.mono_syms (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, spb, ob, mb⟩ syb => ?_
  rw [ga] at pb ob mb
  have hb : Scr b (s.gpr .x2) := ⟨pb, by rw [wb, wa]; exact hws, hn⟩
  have fm : Frame [⟨s.gpr .x2, 8192⟩] s.mem b.mem :=
    (scratchFrame ma (by decide)).trans (scratchFrame mb (by decide))
  have svb : Saved (s.gpr .x2) s.gpr b.mem := sva.outside mb (by decide)
  have input : bytesAt b.mem (s.gpr .x1) 32 = bytesAt s.mem (s.gpr .x1) 32 := bytesAt32_frame fm hd
  apply WP.seq
  refine WP.mono (he hb ((gb _ (by decide)).trans (congrFun ga _))
    (fun q hq => ⟨⟨s.gpr .x1, 32⟩, by rw [rb, ra, hr]; simp,
      Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])⟩)
    (fun q hq => farScr hd hq (by decide))
    (htb.of_far (by rw [rb, ra, wb, wa]) fun x hx => by
      rw [mb x (Or.inr (by omega_using [hx])), ma x (Or.inr (by omega_using [hx]))])
    (by rw [syb, sya])) fun c ⟨kc, vc⟩ => ?_
  have mc := ck_outside kc
  have svc : Saved (s.gpr .x2) s.gpr c.mem := svb.outside mc (by decide)
  have oc : c.mem.readW (off (s.gpr .x2) 48) 64 = s.gpr .x0 :=
    (mc.word (d := 48) (Or.inl (by decide)) (by decide)).trans ob
  have wc : c.wr = s.wr := kc.wr.trans (wb.trans wa)
  rw [scalarBaseFinish]
  apply WP.seq
  refine WP.mono (scalarBaseFinishArgs_ok (kc.scratch hb)) fun d ⟨pd, od, kd⟩ => ?_
  have x2d : d.gpr .x2 = s.gpr .x2 := pd
  have x0d : d.gpr .x0 = s.gpr .x0 := od.trans oc
  have wd : d.wr = s.wr := kd.wr.trans wc
  rw [scalarFinish, WP.block_append_iff]
  refine WP.mono (scalarRestore_ok (g := s.gpr) x2d (wd ▸ hws) (by rw [kd.mem]; exact svc))
    fun f ⟨re, ke⟩ => ?_
  have x0e : f.gpr .x0 = s.gpr .x0 := (ke.gpr _ (by decide)).trans x0d
  have hwo : (⟨s.gpr .x0, 32⟩ : Region) ∈ f.wr := by rw [ke.wr, wd, hw]; simp
  refine WP.mono (scalarOut_ok x0e hwo) fun t ht => ?_
  subst t
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, fun hD i hi hi' => ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact re (.x19, 0) (by decide)
    · exact re (.x20, 8) (by decide)
    · exact re (.x21, 16) (by decide)
    · exact re (.x22, 24) (by decide)
    · exact re (.x23, 32) (by decide)
    · exact re (.x24, 40) (by decide)
    all_goals
      rw [ke.gpr _ (by decide), kd.gpr _ (by decide), kc.gpr _ (by decide) (by decide) (by decide),
        gb _ (by decide), ga]
  · exact ke.sp.trans (kd.sp.trans (kc.sp.trans (spb.trans spa)))
  · change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    rw [bytesAt_st4, ← input, ← vc]
    apply congrArg (Proof.X25519.leBytes 32)
    rw [ke.gpr .x4 (by decide), ke.gpr .x5 (by decide), ke.gpr .x6 (by decide), ke.gpr .x7 (by decide),
      kd.gpr .x4 (by decide), kd.gpr .x5 (by decide), kd.gpr .x6 (by decide), kd.gpr .x7 (by decide)]
  · -- `out` is outside `scratch`, and every step before it wrote below byte 1024
    have hx : ¬ (⟨s.gpr .x0, 32⟩ : Region).Contains (s.gpr .x2 + BitVec.ofNat 64 i) 1 :=
      fun hc => hD _ hc (by
        have e := ofs_off' (s.gpr .x2) (d := i) (by omega_using [hi'])
        simp only [ofs, off] at e
        simp only [Region.Contains, e]; omega_using [hi'])
    simp only [Region.Contains] at hx
    have ho := st4_outside f.mem (s.gpr .x0) (o := 0) (by decide) (f.gpr .x4) (f.gpr .x5) (f.gpr .x6)
      (f.gpr .x7) (s.gpr .x2 + BitVec.ofNat 64 i) (Or.inr (by simp only [ofs]; omega_using [hx]))
    change st4 f.mem (s.gpr .x0) 0 _ _ _ _ _ = _
    rw [ho, ke.mem, kd.mem, outside_tail mc (by decide) hi hi', outside_tail mb (by decide) hi hi',
      outside_tail ma (by decide) hi hi']

theorem scalarBase_correct [Divstep.Sound] {s : State} (hs : scalarBaseLocal.pre s) :
    WP isa scalarBase s fun t => abiPreserved s t ∧ scalarBaseLocal.post s t :=
  WP.mono (baseWrap_ok (R := Spec.Ed25519.scalarBase) (fun h1 h2 h3 h4 h5 h6 => by
    refine WP.mono (scalarBaseEngine_ok h1 h2 h3 h4 h5 h6) fun t ⟨k, e⟩ => ⟨k, ?_⟩
    rw [← encodeLE_eq]
    exact e) (by lit_decide) hs) fun _ ⟨h1, h2, _⟩ => ⟨h1, h2⟩

end VG.Proof.Ed25519.AArch64
