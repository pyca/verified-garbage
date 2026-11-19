module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Matrix
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.MatrixTiming
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.PairTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.BeginTiming
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Last
public import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Env
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Last
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixTiming
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.PairTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.BeginTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Env
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.AArch64.Shared
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.RegSet
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Sums
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Sums
meta import VerifiedGarbage.Proof.Framework.RegSet

/-! ### `MlKem.AArch64.Kem16P.LastTiming`, which only this module used -/

section

/-!
# The singleton computing PRF outputs leaks only public pointers and the public seed

As `Paired.lastCode_relCT`: its start and three main squeezes (`lastPrep`) by
one taint analysis from `x28` of a copy without immediates and offsets, which
are all that tell its squeezes apart, then the rejection, the full sampler and
the restore as there.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P
variable {sha3 : Bool}

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Paired (LastInput seedBytes fullWrites exec_post seq_parts
  fullSampleCode_relCT restore_ct reject_relCT ct_eraseOff_eq)

/-- The singleton's start, three main squeezes and constants. -/
def lastPrep (sha3 : Bool) (sb ss a k bo N₀ : Nat) : Prog isa :=
  .seq (.seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a a k ++ Impl.MlKem.AArch64.ptrTo .x21 .x28 bo))
    (.seq (Impl.MlKem.AArch64.Kem16P.stepB sha3 Impl.MlKem.AArch64.KEM.RB N₀) (.seq (Impl.MlKem.AArch64.Kem16P.stepB sha3 Impl.MlKem.AArch64.KEM.RB (N₀ + 1))
      (Impl.MlKem.AArch64.Kem16P.stepB sha3 Impl.MlKem.AArch64.KEM.RB (N₀ + 2)))))
    (.block Impl.MlKem.AArch64.Rej8.rejConsts)

theorem lastPrep_erase {sb ss a k bo N₀ : Nat} (hss : ss < 4096) (hbo : 4096 ≤ bo) :
    Code.eraseOff (lastPrep sha3 sb ss a k bo N₀) = Code.eraseOff (lastPrep sha3 0 0 0 1 4096 0) := by
  simp only [lastPrep, Code.eraseOff, List.map_append, Impl.MlKem.AArch64.Kem16P.stepB,
    Impl.MlKem.AArch64.Kem16P.reinitB, prfWords_eraseOff, Impl.MlKem.AArch64.Paired.init,
    Impl.MlKem.AArch64.ptrTo, ite_eq_left hss, ite_eq_right (show ¬ bo < 4096 by omega_using [hbo]),
    ite_eq_left (show (0 : Nat) < 4096 by decide), ite_eq_right (show ¬ (4096 : Nat) < 4096 by decide)]
  rfl

theorem lastPrep_ct {sb ss a k bo N₀ : Nat} (hss : ss < 4096) (hbo : 4096 ≤ bo) :
    ConstantTime isa (fun _ => True) (VG.AArch64.Taint.Agree (Taint.ofRegs [.x28]))
      (lastPrep sha3 sb ss a k bo N₀) := by
  cases sha3
  · -- The call of the paired Keccak by its summary (`X2Sums.erased`).
    obtain ⟨hc, h⟩ : ∃ hc, (VectorTaint.taint.check (VectorTaint.ofRegs [.x28])
        (Code.eraseOff (lastPrep false 0 0 0 1 4096 0)) hc).isSome = true := by
      taint_decide_sum [VG.Proof.Sha3.AArch64.Neon.X2Sums.erased]
    exact Paired.vct_eraseOff_eq [.x28] (lastPrep_erase (sha3 := false) hss hbo) h
  · apply ct_eraseOff_eq [.x28] (d := Code.eraseOff (lastPrep true 0 0 0 1 4096 0)) (lastPrep_erase (sha3 := true) hss hbo)
    taint_decide

/-- After `lastPrep`: what the rejection needs. -/
structure LastPreparedP (w16 : Bool) (B : Nat → Byte) (p out table : Addr) (s t : State) : Prop where
  keep : Keep (startBRegs ++ [.x9, .x16]) s t
  env : Rej8.EnvW w16 168 B (p + 400) out t
  constants : Rej8.Constants t
  pointer : t.gpr .x19 = p
  tablePtr : t.gpr .x16 = table

theorem lastPrepP_ok (L : Impl.MlKem.AArch64.KemLay) {w16 : Bool} {s : State}
    {p seed out table R B₀ : Addr} {sb ss a off N₀ : Nat}
    (hN : N₀ + 2 < 256) (hbo : Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀ < 65536)
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8 : sb % 8 = 0)
    (hk : 0 < L.k) (hk256 : L.k ≤ 256)
    (ps : LastInput sb ss off p seed out table s)
    (hl : LayB p R B₀ s) (ap : BufApart p seed out table R B₀)
    (hR : s.gpr .x28 + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : s.gpr .x28 + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀) = B₀) :
    WP isa (lastPrep sha3 sb ss a L.k (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀) N₀) s
      (LastPreparedP w16 (xofByte (seedBytes s.mem seed a L.k)) p out table s) := by
  refine WP.seq (WP.mono_syms (startB_ok (sha3 := sha3) L (a := a) hN hbo hss hsb h8 ps.ptr ps.seedPtr ps.readable
    ps.separate hl hR hB) fun u ⟨ku, fu, _, u19, bu, _⟩ sy => ?_)
  have fuP : Frame (fullWritesP p out B₀) s.mem u.mem :=
    fu.mono (by simp [fullWritesP, fullWrites])
  have cu := ctx_frameP ps.context ap.table ku.rd ku.wr fuP
  refine WP.mono_syms (Rej8.constants_ok u (by
    rw [u19]; exact Noise.inScratch cu.scratch (by decide) (by decide)))
    fun v ⟨kv, cv, mv, tv⟩ syv => ?_
  have fv : Frame [⟨p + 1408, 8⟩] u.mem v.mem := by
    rw [mv, u19]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 8)
  have fvBig : Frame (fullWritesP p out B₀) u.mem v.mem := fv.sub (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨p, 2048⟩, by simp [fullWritesP, fullWrites], Offset.sub_base p (by decide)⟩)
  have ctv := ctx_frameP cu ap.table kv.rd kv.wr fvBig
  have v19 : v.gpr .x19 = p := (kv.get .x19).trans u19
  have v16 : v.gpr .x16 = table := by rw [tv, syv, sy, ps.symbol]
  have stream : ∀ i < 504, v.mem ((p + 400) + BitVec.ofNat 64 i) =
      xofByte (seedBytes s.mem seed a L.k) i := by
    intro i hi
    have hd : ∀ r ∈ [Region.mk (p + 1408) 8], (Region.mk (p + 400) 504).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact Offset.disjoint p (d := 400) (e := 1408) (n := 504) (k := 8) (by decide) (by decide) (by decide)
    exact (fv.bytes hd (by change 504 ≤ 2 ^ 64; decide) hi).trans (bu.xof hk hk256 hi)
  have ready : Rej8.TableReady v out :=
    ⟨by rw [v16]; exact ctv.artifact, by rw [v16]; exact ctv.readable, by rw [v16]; exact ctv.tableOut⟩
  have env := Paired.rejection_envW (w16 := w16) (off := 400) (N := 168) (by decide) (by decide)
    ctv.scratch ctv.output ctv.apart stream (fun _ hm => ready.read hm)
    (fun _ hm => ready.artifact.vector hm) (fun _ hm => ready.disjoint hm)
  exact ⟨ku.trans kv, env, cv, v19, v16⟩

/-- The singleton's start and rejection (`lastStartP`). -/
theorem lastStartP_relCT (L : Impl.MlKem.AArch64.KemLay) {w16 : Bool} {s u : State}
    {p seed out table R B₀ : Addr} {sb ss a off N₀ : Nat}
    (hN : N₀ + 2 < 256) (hbo : Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀ < 65536)
    (h4 : 4096 ≤ Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀)
    (hss : ss < 4096) (hsb : sb + 32 ≤ 32768) (h8 : sb % 8 = 0) (hoff : off < 65536)
    (hk : 0 < L.k) (hk256 : L.k ≤ 256)
    (ps : LastInput sb ss off p seed out table s) (pu : LastInput sb ss off p seed out table u)
    (hls : LayB p R B₀ s) (hlu : LayB p R B₀ u) (ap : BufApart p seed out table R B₀)
    (hR : s.gpr .x28 + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : s.gpr .x28 + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀) = B₀)
    (sp : s.sp = u.sp) (base : s.gpr .x28 = u.gpr .x28)
    (seedEq : seedBytes s.mem seed a L.k = seedBytes u.mem seed a L.k) :
    RelCT isa (fun t v => t = s ∧ v = u)
      (lastStartP sha3 sb ss a L.k off (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀) N₀ w16)
      (fun t v => LastStartPostP w16 (xofByte (seedBytes s.mem seed a L.k)) p out table R B₀ N₀ s t ∧
        LastStartPostP w16 (xofByte (seedBytes u.mem seed a L.k)) p out table R B₀ N₀ u v) := by
  have hRu : u.gpr .x28 + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R := by rw [← base]; exact hR
  have hBu : u.gpr .x28 + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀) = B₀ := by
    rw [← base]; exact hB
  let Rr := fun t v : State => LastPreparedP w16 (xofByte (seedBytes s.mem seed a L.k)) p out table s t ∧
    LastPreparedP w16 (xofByte (seedBytes u.mem seed a L.k)) p out table u v
  have start : RelCT isa (fun t v => t = s ∧ v = u)
      (lastPrep sha3 sb ss a L.k (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀) N₀) Rr := by
    intro t v tr ur t' v' h et ev
    rcases h with ⟨ht, hv⟩; subst t; subst v
    exact ⟨lastPrep_ct (sha3 := sha3) hss h4 s u tr ur t' v' trivial trivial
      (agree_of sp (by intro r hr; rw [List.mem_singleton.mp hr]; exact base)) et ev,
      exec_post (lastPrepP_ok (sha3 := sha3) L hN hbo (by omega_using [hss]) hsb h8 hk hk256 ps hls ap hR hB) et,
      exec_post (lastPrepP_ok (sha3 := sha3) L hN hbo (by omega_using [hss]) hsb h8 hk hk256 pu hlu ap hRu hBu) ev⟩
  have grouped : RelCT isa (fun t v => t = s ∧ v = u)
      (.seq (lastPrep sha3 sb ss a L.k (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀) N₀)
        (Impl.MlKem.AArch64.Paired.reject 400 off .x22 w16)) (fun _ _ => True) := by
    refine RelCT.seq start ?_
    intro t v tr ur t' v' h et ev
    have ht28 := h.1.keep.get .x28
    have hv28 := h.2.keep.get .x28
    have rr := reject_relCT (by decide) hoff (by decide : Reg.x22 ≠ .x3 ∧ Reg.x22 ≠ .x4)
      (by rw [h.1.pointer, ht28, ps.outPtr]; exact h.1.env)
      (by rw [h.2.pointer, hv28, pu.outPtr]; rw [seedEq]; exact h.2.env)
      h.1.constants h.2.constants
      (h.1.keep.sp.trans (sp.trans h.2.keep.sp.symm)) (h.1.pointer.trans h.2.pointer.symm)
      (by rw [ht28, hv28, base]) (h.1.tablePtr.trans h.2.tablePtr.symm)
      t v tr ur t' v' ⟨rfl, rfl⟩ et ev
    exact ⟨rr.1, trivial⟩
  have trace : RelCT isa (fun t v => t = s ∧ v = u)
      (lastStartP sha3 sb ss a L.k off (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀) N₀ w16) (fun _ _ => True) :=
    RelCT.assoc (RelCT.assoc grouped)
  intro t v tr ur t' v' h et ev
  rcases h with ⟨ht, hv⟩; subst t; subst v
  exact ⟨(trace s u tr ur t' v' ⟨rfl, rfl⟩ et ev).1,
    exec_post (lastStartP_ok (sha3 := sha3) L hN hbo (by omega_using [hss]) hsb h8 hoff hk hk256 ps.ptr ps.seedPtr ps.outPtr
      ps.readable ps.separate ps.context ps.symbol hls ap hR hB) et,
    exec_post (lastStartP_ok (sha3 := sha3) L hN hbo (by omega_using [hss]) hsb h8 hoff hk hk256 pu.ptr pu.seedPtr pu.outPtr
      pu.readable pu.separate pu.context pu.symbol hlu ap hRu hBu) ev⟩

theorem afterStartP {w16 : Bool} {s t : State} {p seed out table R B₀ : Addr}
    {sb ss off N₀ : Nat} {B : Nat → Byte}
    (h : LastInput sb ss off p seed out table s)
    (ht : LastStartPostP w16 B p out table R B₀ N₀ s t)
    (sy : t.syms = s.syms) : LastInput sb ss off p seed out table t :=
  ⟨by rw [ht.keep.get .x28]; exact h.ptr, by rw [ht.keep.get .x28]; exact h.seedPtr,
   by rw [ht.keep.get .x28]; exact h.outPtr, by rw [ht.keep.rd, ht.keep.wr]; exact h.readable,
   h.separate, ht.context, by rw [sy]; exact h.symbol⟩

theorem LastStartPostP.seed {w16 : Bool} {s t : State} {p seed out table R B₀ : Addr} {a k N₀ : Nat}
    {B : Nat → Byte} (h : LastStartPostP w16 B p out table R B₀ N₀ s t)
    (hs : (Region.mk seed 32).Disjoint ⟨p, 2048⟩)
    (ho : (Region.mk seed 32).Disjoint (polyRegion out)) (hb : (Region.mk seed 32).Disjoint (bufR B₀)) :
    seedBytes t.mem seed a k = seedBytes s.mem seed a k := by
  unfold seedBytes
  rw [bytesAt_frame h.frame (by
    intro r hr
    simp only [fullWritesP, fullWrites, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact hs
    · exact ho
    · exact hb) (by decide : 32 ≤ 2 ^ 64)]

theorem lastP_exec {w16 : Bool} {sb ss a k off bo N₀ : Nat} {s t : State} {tr : List Leak}
    (h : Exec isa (lastCodeP sha3 sb ss a k off bo N₀ w16) s tr t) :
    Exec isa (.seq (lastStartP sha3 sb ss a k off bo N₀ w16) (Paired.lastTail sha3 sb ss a k off w16)) s tr t := by
  obtain ⟨_, _, _, rfl, ei, h⟩ := seq_parts h
  obtain ⟨_, _, _, rfl, es, h⟩ := seq_parts h
  obtain ⟨_, _, _, rfl, ec, h⟩ := seq_parts h
  obtain ⟨_, _, _, rfl, er, h⟩ := seq_parts h
  have ee := Exec.seq (Exec.seq ei (Exec.seq es (Exec.seq ec er))) h
  simpa only [lastStartP, Paired.lastTail, List.append_assoc] using ee

/-- **The singleton computing PRF outputs** leaks only public pointers and the public seed. -/
theorem lastCodeP_relCT (L : Impl.MlKem.AArch64.KemLay) {w16 : Bool} {s u : State}
    {p seed out table R B₀ : Addr} {sb ss a off N₀ : Nat}
    (hN : N₀ + 2 < 256) (hbo : Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀ < 65536)
    (h4 : 4096 ≤ Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀)
    (hss : ss < 4096) (hsb : sb + 32 ≤ 32768) (h8 : sb % 8 = 0) (hoff : off < 65536)
    (hk : 0 < L.k) (hk256 : L.k ≤ 256)
    (ps : LastInput sb ss off p seed out table s) (pu : LastInput sb ss off p seed out table u)
    (ho : (Region.mk seed 32).Disjoint (polyRegion out))
    (hls : LayB p R B₀ s) (hlu : LayB p R B₀ u) (ap : BufApart p seed out table R B₀)
    (hR : s.gpr .x28 + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : s.gpr .x28 + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀) = B₀)
    (sp : s.sp = u.sp) (base : s.gpr .x28 = u.gpr .x28)
    (seedEq : seedBytes s.mem seed a L.k = seedBytes u.mem seed a L.k) :
    RelCT isa (fun t v => t = s ∧ v = u)
      (lastCodeP sha3 sb ss a L.k off (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀) N₀ w16) (fun _ _ => True) := by
  let Rr := fun t v : State => LastStartPostP w16 (xofByte (seedBytes s.mem seed a L.k)) p out table R B₀ N₀ s t ∧
    LastStartPostP w16 (xofByte (seedBytes u.mem seed a L.k)) p out table R B₀ N₀ u v ∧
    t.syms = s.syms ∧ v.syms = u.syms
  have start : RelCT isa (fun t v => t = s ∧ v = u)
      (lastStartP sha3 sb ss a L.k off (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀) N₀ w16) Rr := by
    intro t v tr ur t' v' h et ev
    have hh := lastStartP_relCT (sha3 := sha3) L hN hbo h4 hss hsb h8 hoff hk hk256 ps pu hls hlu ap hR hB sp base seedEq
      t v tr ur t' v' h et ev
    rcases h with ⟨ht, hv⟩; subst t; subst v
    exact ⟨hh.1, hh.2.1, hh.2.2, Exec.syms et, Exec.syms ev⟩
  have branch : RelCT isa Rr (.ite (.zero .x .x22) (Paired.fullSampleCode sha3 sb ss off a L.k w16) (.block []))
      (fun t v => t.sp = v.sp ∧ t.gpr .x19 = v.gpr .x19) := by
    refine RelCT.ite ?_ ?_ (RelCT.block_nil ?_)
    · intro t v h
      have ht := h.1.flag
      have hv := h.2.1.flag
      rw [seedEq] at ht
      have hx := BitVec.eq_of_toNat_eq (ht.trans hv.symm)
      change some (t.gpr .x22 == 0) = some (v.gpr .x22 == 0)
      rw [hx]
    · intro t v tr ur t' v' h et ev
      have ht := h.1.1
      have hv := h.1.2.1
      have hh := fullSampleCode_relCT (sha3 := sha3) hss hsb h8 hoff hk hk256
        (afterStartP ps ht h.1.2.2.1) (afterStartP pu hv h.1.2.2.2) ht.ptr hv.ptr ht.saved hv.saved
        (ht.keep.sp.trans (sp.trans hv.keep.sp.symm))
        (by rw [ht.keep.get .x28, hv.keep.get .x28, base])
        (by rw [ht.seed ps.separate ho ap.seed, hv.seed pu.separate ho ap.seed, seedEq])
        t v tr ur t' v' ⟨rfl, rfl⟩ et ev
      exact ⟨hh.1, hh.2.1.keep.sp.trans ((ht.keep.sp.trans (sp.trans hv.keep.sp.symm)).trans hh.2.2.keep.sp.symm),
        hh.2.1.ptr.trans hh.2.2.ptr.symm⟩
    · intro t v h
      exact ⟨h.1.1.keep.sp.trans (sp.trans h.1.2.1.keep.sp.symm), h.1.1.ptr.trans h.1.2.1.ptr.symm⟩
  have grouped : RelCT isa (fun t v => t = s ∧ v = u)
      (.seq (lastStartP sha3 sb ss a L.k off (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀) N₀ w16)
        (Paired.lastTail sha3 sb ss a L.k off w16)) (fun _ _ => True) := by
    refine RelCT.seq start (RelCT.seq branch ?_)
    intro t v tr ur t' v' h et ev
    exact ⟨restore_ct t v tr ur t' v' trivial trivial
      (agree_of h.1 (by intro r hr; rw [List.mem_singleton.mp hr]; exact h.2)) et ev, trivial⟩
  intro t v tr ur t' v' h et ev
  exact grouped t v tr ur t' v' h (lastP_exec (sha3 := sha3) et) (lastP_exec (sha3 := sha3) ev)

end VG.Proof.MlKem.AArch64.Kem16P

end

end

/-!
# The matrix computing PRF outputs leaks only public pointers and `ρ`

The pairs hashing the message by `Hybrid.hashPair_relCT`, `G` by a relation the caller proves, then, with each
run's invariant after `G` (`PRel`), the pairs computing PRF outputs
(`pairPCode_relCT`), the others (`Paired.pair_relCT`) and the singleton
(`lastCodeP_relCT` or `Paired.lastCode_relCT`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P
variable {sha3 : Bool}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Hybrid (Stk128 MT3 HRel Same hashPair_relCT)
open VG.Proof.MlKem.AArch64.Paired (exec_post)
open VG.Spec.MlKem
open VG.Proof.MlKem

variable {P : KemLay} {L : Layout}

/-- Both runs after `G`, `e` entries and the first `c` PRF outputs. -/
def PRel (P : KemLay) (L : Layout) (σ τ : State) (ρ : List Byte) (e c : Nat) (s u : State) : Prop :=
  (∃ m, PInvW true P L σ m ρ e c s) ∧ (∃ n, PInvW true P L τ n ρ e c u) ∧
  MT3 P L σ s ∧ MT3 P L τ u ∧ s.syms "VG_MLKEM_REJ_SHUFFLE" = u.syms "VG_MLKEM_REJ_SHUFFLE"

/-- The singleton's memory. -/
theorem layB_of {s₀ s : State} (hp : Pre P L s₀) {N₀ : Nat} (hN : N₀ + 3 ≤ 12) (h : KB P L s₀ s) :
    LayB (sA L s₀ SS) (sA L s₀ RB) (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N₀)) s := by
  have hw := hp.wf
  have bR := bufR_eq (L := L) (P := P) s₀ N₀
  exact ⟨cov_s hp h (o := SS) (l := 2048) (by lom), cov_sr hp h (o := RB) (l := 32) (by lom),
    sdisj hp (by lom) (by lom) (by lom), by rw [bR]; exact cov_s hp h (by lom),
    by rw [bR]; exact sdisj hp (by lom) (by lom) (by lom),
    by rw [bR]; exact sdisj hp (by lom) (by lom) (by lom)⟩

/-- The singleton's buffers, apart from the rest of its memory. -/
theorem apart_of {s₀ s : State} (hp : Pre P L s₀) {N₀ : Nat} (hN : N₀ + 3 ≤ 12) (tb : MT3 P L s₀ s) :
    BufApart (sA L s₀ SS) (sA L s₀ SB) (aP L s₀ (P.k * P.k - 1)) (s.syms "VG_MLKEM_REJ_SHUFFLE")
      (sA L s₀ RB) (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N₀)) := by
  have hw := hp.wf
  have hf := hw.facts
  have hkk : P.k * P.k ≤ 16 := hf.2.2.1
  have hk1 : 0 < P.k := hf.1
  have hn : 0 < P.k * P.k := Nat.mul_pos hk1 hk1
  have bR := bufR_eq (L := L) (P := P) s₀ N₀
  exact ⟨by rw [bR]; exact sdisj hp (by lom) (by lom) (by lom), by rw [bR]; exact sdisj hp (by lom) (by lom) (by lom),
    by rw [bR]; exact sdisj hp (o₂ := AH + 1024 * (P.k * P.k - 1)) (l₂ := 1024) (by lom) (by lom) (by lom),
    by rw [bR]; exact tb.t.apart.sub_right (scratch_sub hp (by lom))⟩

/-- A pair computing PRF outputs `N₀`, …, `N₀ + m - 1`. -/
theorem prfPair_relCT_inline {M : Hybrid.Msg} {σ τ : State} (hp : Pre P L σ) (hq : Pre P L τ)
    (hk : Stk128 P L σ) (hk' : Stk128 P L τ) (sm : Same L M σ τ) {ρ : List Byte} {i N₀ m : Nat}
    (he : 2 * i + 1 < P.k * P.k) (hN : N₀ + 3 ≤ 12) (hm : m ≤ 3) :
    RelCT isa (PRel P L σ τ ρ (2 * i) N₀) (Impl.MlKem.AArch64.Kem16P.pairP sha3 SB SS AH RB (TP P) P (2 * i) N₀ m)
      (PRel P L σ τ ρ (2 * i + 2) (N₀ + m)) := by
  intro s u tr ur t v h et eu
  obtain ⟨⟨mσ, h₁⟩, ⟨mτ, h₂⟩, t₁, t₂, sh⟩ := h
  have hw := hp.wf
  have hbo : Impl.MlKem.AArch64.Kem16P.bufOff (TP P) (N₀ + 2) < 65536 := by
    simp only [Impl.MlKem.AArch64.Kem16P.bufOff]; lom
  have h4 : 4096 ≤ Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N₀ := by
    simp only [Impl.MlKem.AArch64.Kem16P.bufOff]; lom
  have hf := hw.facts
  have hkk : P.k * P.k ≤ 16 := hf.2.2.1
  have hoa : AH + 1024 * (2 * i) < 65536 := by simp only [KEM.AH]; omega_using [he, hkk]
  have hob : AH + 1024 * (2 * i + 1) < 65536 := by simp only [KEM.AH]; omega_using [he, hkk]
  have ps := pair_input hp he h₁.b.kb t₁.t
  have hs := prf_input hp hk he hN h₁.b.kb t₁
  have pu := pair_input hq he h₂.b.kb t₂.t
  have hu := prf_input hq hk' he hN h₂.b.kb t₂
  have ba : ∀ o, sA L σ o = sA L τ o := fun o => congrArg (fun b => b + BitVec.ofNat 64 o) sm.base
  have aa : ∀ i, aP L σ i = aP L τ i := fun i => ba _
  rw [← ba SS, ← ba SB, ← aa (2 * i), ← aa (2 * i + 1), ← sh] at pu
  rw [← aa (2 * i), ← aa (2 * i + 1), ← ba SS, ← ba RB, ← ba (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N₀), ← sh,
    ← sm.base] at hu
  have seeds : ∀ j, Paired.seedState s.mem (sA L σ SB) j P.k = Paired.seedState u.mem (sA L σ SB) j P.k := by
    intro j
    rw [Paired.seedState_eq _ _ (by lom) (by lom), Paired.seedState_eq _ _ (by lom) (by lom)]
    unfold Paired.seedBytes
    rw [h₁.b.rho, ba SB, h₂.b.rho]
  have ct := pairPCode_relCT (sha3 := sha3) (w16 := true) P RB (TP P) (a := 2 * i) (m := m) (by omega_arith) hbo h4 (by decide) (by decide)
    (by decide) hoa hob ps hs pu hu rfl (by decide) (by decide) rfl (by rw [h₁.b.kb.sp, h₂.b.kb.sp, sm.sp]) (seeds _) (seeds _)
  have ht := exec_post (paired_stepP (sha3 := sha3) hp hk he hN hm h₁ t₁) et
  have hv := exec_post (paired_stepP (sha3 := sha3) hq hk' he hN hm h₂ t₂) eu
  exact ⟨(ct _ _ _ _ _ _ ⟨rfl, rfl⟩ (pairP_exec (sha3 := sha3) et) (pairP_exec (sha3 := sha3) eu)).1, ⟨_, ht.1⟩, ⟨_, hv.1⟩, ht.2, hv.2,
    by rw [Exec.syms et, Exec.syms eu]; exact sh⟩

/-- A direct call adds no address leakage on AArch64 and returns its body's final state. -/
theorem call_exec {name : String} {body : Prog isa} {s t : State} {tr : List Leak}
    (he : Exec isa (.call name body) s tr t) : Exec isa body s.callEntry tr t := by
  cases he with
  | call hc hb hr =>
    rw [call_callEntry] at hc
    cases Option.some.inj hc
    cases ret_eq hr
    simpa only [isa, List.map_nil, List.nil_append, List.append_nil] using hb

/-- A pair computing PRF outputs `N₀`, …, `N₀ + m - 1`. -/
theorem prfPair_relCT {M : Hybrid.Msg} {σ τ : State} (hp : Pre P L σ) (hq : Pre P L τ)
    (hk : Stk128 P L σ) (hk' : Stk128 P L τ) (sm : Same L M σ τ) {ρ : List Byte} {i N₀ m : Nat}
    (he : 2 * i + 1 < P.k * P.k) (hN : N₀ + 3 ≤ 12) (hm : m ≤ 3) :
    RelCT isa (PRel P L σ τ ρ (2 * i) N₀) (Impl.MlKem.AArch64.Kem16P.pairPCall sha3 SB SS AH RB (TP P) P (2 * i) N₀ m)
      (PRel P L σ τ ρ (2 * i + 2) (N₀ + m)) := by
  intro s u tr ur t v h et eu
  obtain ⟨⟨mσ, hs⟩, ⟨mτ, hu⟩, ts, tu, sym⟩ := h
  exact prfPair_relCT_inline (sha3 := sha3) hp hq hk hk' sm he hN hm _ _ _ _ _ _
    ⟨⟨mσ, hs.callEntry⟩, ⟨mτ, hu.callEntry⟩, ts.callEntry, tu.callEntry, sym⟩
    (call_exec et) (call_exec eu)

/-- A pair computing no PRF output after `G`. -/
theorem plainPairP_relCT {M : Hybrid.Msg} {σ τ : State} (hp : Pre P L σ) (hq : Pre P L τ)
    (sm : Same L M σ τ) {ρ : List Byte} {e c : Nat} (he : e + 1 < P.k * P.k) (hc : c ≤ 12) :
    RelCT isa (PRel P L σ τ ρ e c) (Impl.MlKem.AArch64.Paired.pair sha3 P false e true) (PRel P L σ τ ρ (e + 2) c) := by
  intro s u tr ur t v h et eu
  obtain ⟨⟨mσ, h₁⟩, ⟨mτ, h₂⟩, t₁, t₂, sh⟩ := h
  have hw := hp.wf
  have ps := pair_input hp he h₁.b.kb t₁.t
  have pu := pair_input hq he h₂.b.kb t₂.t
  have ba : ∀ o, sA L σ o = sA L τ o := fun o => congrArg (fun b => b + BitVec.ofNat 64 o) sm.base
  have aa : ∀ i, aP L σ i = aP L τ i := fun i => ba _
  rw [← ba SS, ← ba SB, ← aa e, ← aa (e + 1), ← sh] at pu
  have seeds : ∀ i, Paired.seedState s.mem (sA L σ SB) i P.k = Paired.seedState u.mem (sA L σ SB) i P.k := by
    intro i
    rw [Paired.seedState_eq _ _ (by lom) (by lom), Paired.seedState_eq _ _ (by lom) (by lom)]
    unfold Paired.seedBytes
    rw [h₁.b.rho, ba SB, h₂.b.rho]
  have ct := Paired.pair_relCT (sha3 := sha3) (w16 := true) (L := P) (kg := false) (a := e) (by decide) (by decide) (by decide)
    (by change AH + 1024 * e < 65536; lom) (by change AH + 1024 * (e + 1) < 65536; lom) ps pu
    (by rw [h₁.b.kb.sp, h₂.b.kb.sp, sm.sp]) (by rw [h₁.b.kb.x28, h₂.b.kb.x28, sm.base]) (seeds e) (seeds (e + 1))
  have ht := exec_post (paired_stepQ (sha3 := sha3) hp he hc h₁ t₁) et
  have hv := exec_post (paired_stepQ (sha3 := sha3) hq he hc h₂ t₂) eu
  exact ⟨(ct _ _ _ _ _ _ ⟨rfl, rfl⟩ et eu).1, ⟨_, ht.1⟩, ⟨_, hv.1⟩, ht.2, hv.2,
    by rw [Exec.syms et, Exec.syms eu]; exact sh⟩

/-- The singleton computing no PRF output after `G`. -/
theorem lastQ_relCT {M : Hybrid.Msg} {σ τ : State} (hp : Pre P L σ) (hq : Pre P L τ)
    (sm : Same L M σ τ) {ρ : List Byte} {e c : Nat} (he : e < P.k * P.k) (hc : c ≤ 12) :
    RelCT isa (PRel P L σ τ ρ e c) (Paired.lastCode sha3 SB SS e P.k (AH + 1024 * e) true)
      (PRel P L σ τ ρ (e + 1) c) := by
  intro s u tr ur t v h et eu
  obtain ⟨⟨mσ, h₁⟩, ⟨mτ, h₂⟩, t₁, t₂, sh⟩ := h
  have hw := hp.wf
  have ps := last_input hp he h₁.b.kb t₁.t
  have pu := last_input hq he h₂.b.kb t₂.t
  have ba : ∀ o, sA L σ o = sA L τ o := fun o => congrArg (fun b => b + BitVec.ofNat 64 o) sm.base
  have aa : ∀ i, aP L σ i = aP L τ i := fun i => ba _
  rw [← ba SS, ← ba SB, ← aa e, ← sh] at pu
  have seed : Paired.seedBytes s.mem (sA L σ SB) e P.k = Paired.seedBytes u.mem (sA L σ SB) e P.k := by
    unfold Paired.seedBytes
    rw [h₁.b.rho, ba SB, h₂.b.rho]
  have ct := Paired.lastCode_relCT (sha3 := sha3) (w16 := true) (by decide) (by decide) (by decide) (by lom) (by lom) (by lom)
    ps pu (sdisj hp (by lom) (by lom) (by lom))
    (by rw [h₁.b.kb.sp, h₂.b.kb.sp, sm.sp]) (by rw [h₁.b.kb.x28, h₂.b.kb.x28, sm.base]) seed
  have ht := exec_post (singleton_stepQ (sha3 := sha3) hp he hc h₁ t₁) et
  have hv := exec_post (singleton_stepQ (sha3 := sha3) hq he hc h₂ t₂) eu
  exact ⟨(ct _ _ _ _ _ _ ⟨rfl, rfl⟩ et eu).1, ⟨_, ht.1⟩, ⟨_, hv.1⟩, ht.2, hv.2,
    by rw [Exec.syms et, Exec.syms eu]; exact sh⟩

/-- The singleton computing PRF outputs `N₀`, `N₀ + 1`, `N₀ + 2` after `G`. -/
theorem lastPP_relCT {M : Hybrid.Msg} {σ τ : State} (hp : Pre P L σ) (hq : Pre P L τ)
    (hk : Stk128 P L σ) (hk' : Stk128 P L τ) (sm : Same L M σ τ) {ρ : List Byte} {N₀ : Nat}
    (hN : N₀ + 3 ≤ 12) :
    RelCT isa (PRel P L σ τ ρ (P.k * P.k - 1) N₀) (Impl.MlKem.AArch64.Kem16P.lastP sha3 P N₀)
      (PRel P L σ τ ρ (P.k * P.k - 1 + 1) (N₀ + 3)) := by
  intro s u tr ur t v h et eu
  obtain ⟨⟨mσ, h₁⟩, ⟨mτ, h₂⟩, t₁, t₂, sh⟩ := h
  have ht := exec_post (singleton_stepP (sha3 := sha3) hp hk hN h₁ t₁) et
  have hv := exec_post (singleton_stepP (sha3 := sha3) hq hk' hN h₂ t₂) eu
  have hw := hp.wf
  have hf := hw.facts
  have hkk : P.k * P.k ≤ 16 := hf.2.2.1
  have hk1 : 0 < P.k := hf.1
  have hn : 0 < P.k * P.k := Nat.mul_pos hk1 hk1
  have he : P.k * P.k - 1 < P.k * P.k := by omega_arith
  have hoff : AH + 1024 * (P.k * P.k - 1) < 65536 := by simp only [KEM.AH]; omega_using [hkk]
  have hbo : Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N₀ < 65536 := by
    simp only [Impl.MlKem.AArch64.Kem16P.bufOff]; lom
  have h4 : 4096 ≤ Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N₀ := by
    simp only [Impl.MlKem.AArch64.Kem16P.bufOff]; lom
  have ps := last_input hp he h₁.b.kb t₁.t
  have pu := last_input hq he h₂.b.kb t₂.t
  have ls := layB_of hp hN h₁.b.kb
  have lu := layB_of hq hN h₂.b.kb
  have ba : ∀ o, sA L σ o = sA L τ o := fun o => congrArg (fun b => b + BitVec.ofNat 64 o) sm.base
  have aa : ∀ i, aP L σ i = aP L τ i := fun i => ba _
  rw [← ba SS, ← ba SB, ← aa (P.k * P.k - 1), ← sh] at pu
  rw [← ba SS, ← ba RB, ← ba (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N₀)] at lu
  have seed : Paired.seedBytes s.mem (sA L σ SB) (P.k * P.k - 1) P.k =
      Paired.seedBytes u.mem (sA L σ SB) (P.k * P.k - 1) P.k := by
    unfold Paired.seedBytes
    rw [h₁.b.rho, ba SB, h₂.b.rho]
  have ct := lastCodeP_relCT (sha3 := sha3) P (w16 := true) (a := P.k * P.k - 1) (by omega_arith) hbo h4 (by decide) (by decide)
    (by decide) hoff hk1 (by omega_arith) ps pu (sdisj hp (o₂ := AH + 1024 * (P.k * P.k - 1)) (l₂ := 1024)
      (by lom) (by lom) (by lom))
    ls lu (apart_of hp hN t₁) (e28 h₁.b.kb RB) (e28 h₁.b.kb _)
    (by rw [h₁.b.kb.sp, h₂.b.kb.sp, sm.sp]) (by rw [h₁.b.kb.x28, h₂.b.kb.x28, sm.base]) seed
  rw [lastP_eq] at et eu
  exact ⟨(ct _ _ _ _ _ _ ⟨rfl, rfl⟩ et eu).1, ⟨_, ht.1⟩, ⟨_, hv.1⟩, ht.2, hv.2,
    by rw [Exec.syms et, Exec.syms eu]; exact sh⟩

/-- A relation that also keeps each run's symbols. -/
theorem relCT_syms {c : Prog isa} {Pr Q : State → State → Prop} {s₀ u₀ : State} (h : RelCT isa Pr c Q) :
    RelCT isa (fun s u => Pr s u ∧ s.syms = s₀.syms ∧ u.syms = u₀.syms) c
      (fun s u => Q s u ∧ s.syms = s₀.syms ∧ u.syms = u₀.syms) := by
  intro s u tr ur t v hh et eu
  have r := h s u tr ur t v hh.1 et eu
  exact ⟨r.1, r.2, by rw [Exec.syms et]; exact hh.2.1, by rw [Exec.syms eu]; exact hh.2.2⟩

/-- **The matrix computing PRF outputs** leaks only public pointers and `ρ`, given that `G`
(`between`) takes the hashing pairs' relation to `PRel`. -/
theorem matrixP_relCT {M : Hybrid.Msg} {σ τ : State} (hp : Pre P L σ) (hq : Pre P L τ)
    (hk : Stk128 P L σ) (hk' : Stk128 P L τ) (hM : Hybrid.MsgOk P L M σ) (hM' : Hybrid.MsgOk P L M τ)
    (sm : Same L M σ τ) (ho : Hybrid.HashOk P M.S) {m n : Mem} {ρ Eσ Eτ : List Byte} {s₀ u₀ : State}
    (habs : ∀ blk, 136 * blk < M.S.len → ∃ h, (taint.check (Taint.ofRegs [M.S.r, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock M.S blk)) h).isSome = true)
    {between : Prog isa}
    (hb : RelCT isa (fun s u => HRel true P L M σ τ m n ρ Eσ Eτ (2 * Impl.MlKem.AArch64.Hybrid.hashPairs M.S)
        (Impl.MlKem.AArch64.Hybrid.hashPairs M.S) s u ∧ s.syms = s₀.syms ∧ u.syms = u₀.syms) between
      (PRel P L σ τ ρ (2 * Impl.MlKem.AArch64.Hybrid.hashPairs M.S) 0)) :
    RelCT isa (fun s u => HRel true P L M σ τ m n ρ Eσ Eτ 0 0 s u ∧ s.syms = s₀.syms ∧ u.syms = u₀.syms)
      (Impl.MlKem.AArch64.Kem16P.matrixP sha3 P M.S between)
      (PRel P L σ τ ρ (P.k * P.k) (finalCount P (Impl.MlKem.AArch64.Hybrid.hashPairs M.S))) := by
  have hw := hp.wf
  have hk1 : 0 < P.k := hw.facts.1
  have hn : 0 < P.k * P.k := Nat.mul_pos hk1 hk1
  have hP := ho.pairs
  have h9 := placed_le (P := P) (hp := Impl.MlKem.AArch64.Hybrid.hashPairs M.S) hw
  have hlen : ∀ i < Impl.MlKem.AArch64.Hybrid.hashPairs M.S, 136 * (3 * i + 2) < M.S.len := by
    intro i hi
    have := ho.part; have := ho.three
    simp only [Impl.MlKem.AArch64.Hybrid.hashPairs, Impl.MlKem.AArch64.Hybrid.blocks] at hi
    omega_arith
  generalize hH : Impl.MlKem.AArch64.Hybrid.hashPairs M.S = H at hP h9 hb hlen ⊢
  have hpairs : Impl.MlKem.AArch64.Kem16P.pairs P = P.k * P.k / 2 := rfl
  unfold Impl.MlKem.AArch64.Kem16P.matrixP
  simp only [hH, filter_lt_range, filter_ge_range, List.map_map]
  rw [show min H (Impl.MlKem.AArch64.Kem16P.pairs P) = H by omega_arith]
  apply RelCTs.seqs (by simp)
  refine RelCTs.append (R := PRel P L σ τ ρ (2 * (Impl.MlKem.AArch64.Kem16P.pairs P - H + H))
      (min (Impl.MlKem.AArch64.Kem16P.placed P H) (3 * (Impl.MlKem.AArch64.Kem16P.pairs P - H))))
    (RelCTs.append (R := PRel P L σ τ ρ (2 * H) 0) (RelCTs.append ?_ ⟨_, hb, fun _ _ h => h⟩) ?_) ?_
  -- The pairs hashing the message.
  · have r := RelCTs.range (n := H) (f := fun i => Impl.MlKem.AArch64.Hybrid.pair3 sha3 P M.S (2 * i) i true)
      (I := fun i s u => HRel true P L M σ τ m n ρ Eσ Eτ (2 * i) i s u ∧ s.syms = s₀.syms ∧ u.syms = u₀.syms)
      fun i hi => by
        rw [show 2 * (i + 1) = 2 * i + 2 by omega_arith]
        exact relCT_syms (hashPair_relCT (sha3 := sha3) hp hq hk hk' hM hM' sm (by omega_arith) (hlen i hi) habs)
    simpa only [Nat.mul_zero] using r
  -- The pairs computing PRF outputs.
  · have r := RelCTs.range (n := Impl.MlKem.AArch64.Kem16P.pairs P - H)
      (I := fun j => PRel P L σ τ ρ (2 * (j + H)) (min (Impl.MlKem.AArch64.Kem16P.placed P H) (3 * j)))
      (f := (fun i => if Impl.MlKem.AArch64.Kem16P.pairCount P H i = 0 then Paired.pair sha3 P false (2 * i) true
        else Impl.MlKem.AArch64.Kem16P.pairPCall sha3 SB SS AH RB (TP P) P (2 * i) (3 * (i - H)) (Impl.MlKem.AArch64.Kem16P.pairCount P H i)) ∘
          (· + H))
      fun j hj => by
        have he : 2 * (j + H) + 1 < P.k * P.k := by omega_arith
        simp only [Function.comp]
        rw [show 2 * (j + 1 + H) = 2 * (j + H) + 2 by omega_arith]
        by_cases hc : Impl.MlKem.AArch64.Kem16P.pairCount P H (j + H) = 0
        · rw [ite_eq_left hc]
          have hc' : Impl.MlKem.AArch64.Kem16P.placed P H ≤ 3 * j := by
            simp only [Impl.MlKem.AArch64.Kem16P.pairCount] at hc; omega_arith
          rw [show min (Impl.MlKem.AArch64.Kem16P.placed P H) (3 * (j + 1)) =
            min (Impl.MlKem.AArch64.Kem16P.placed P H) (3 * j) by omega_arith]
          exact plainPairP_relCT (sha3 := sha3) hp hq sm he (by omega_arith)
        · rw [ite_eq_right hc]
          have hc' : 3 * j < Impl.MlKem.AArch64.Kem16P.placed P H := by
            simp only [Impl.MlKem.AArch64.Kem16P.pairCount] at hc; omega_arith
          rw [show min (Impl.MlKem.AArch64.Kem16P.placed P H) (3 * j) = 3 * (j + H - H) by omega_arith,
            show min (Impl.MlKem.AArch64.Kem16P.placed P H) (3 * (j + 1)) =
              3 * (j + H - H) + Impl.MlKem.AArch64.Kem16P.pairCount P H (j + H) by
              simp only [Impl.MlKem.AArch64.Kem16P.pairCount]; omega_arith]
          exact prfPair_relCT (sha3 := sha3) hp hq hk hk' sm he (by omega_arith)
            (by simp only [Impl.MlKem.AArch64.Kem16P.pairCount]; omega_arith)
    simpa only [Nat.zero_add, Nat.mul_zero, Nat.min_zero] using r
  -- The singleton.
  · rw [show Impl.MlKem.AArch64.Kem16P.pairs P - H + H = P.k * P.k / 2 by omega_arith]
    by_cases hodd : Impl.MlKem.AArch64.Kem16P.single P = true
    · rw [ite_eq_left hodd]
      have hodd' : P.k * P.k % 2 = 1 := by
        simpa [Impl.MlKem.AArch64.Kem16P.single] using hodd
      rw [show 2 * (P.k * P.k / 2) = P.k * P.k - 1 by omega_arith]
      by_cases hl : Impl.MlKem.AArch64.Kem16P.placed P H ≥ 3 * (Impl.MlKem.AArch64.Kem16P.pairs P - H) + 3
      · rw [ite_eq_left hl, show min (Impl.MlKem.AArch64.Kem16P.placed P H)
          (3 * (Impl.MlKem.AArch64.Kem16P.pairs P - H)) = 3 * (Impl.MlKem.AArch64.Kem16P.pairs P - H) by omega_arith]
        refine ⟨_, lastPP_relCT (sha3 := sha3) hp hq hk hk' sm (by omega_arith), fun s u h => ?_⟩
        rw [Nat.sub_add_cancel hn] at h
        simpa only [finalCount, hodd, hl, and_self, ite_true] using h
      · rw [ite_eq_right hl, Paired.lastSample_eq]
        refine ⟨_, lastQ_relCT (sha3 := sha3) hp hq sm (by omega_arith : P.k * P.k - 1 < P.k * P.k) (by omega_arith), fun s u h => ?_⟩
        rw [Nat.sub_add_cancel hn] at h
        simpa only [finalCount, hodd, hl, and_false, ite_false, Bool.false_eq_true] using h
    · rw [ite_eq_right hodd]
      have hev : P.k * P.k % 2 = 0 := by
        simp only [Impl.MlKem.AArch64.Kem16P.single, decide_eq_true_eq] at hodd; omega_arith
      rw [show 2 * (P.k * P.k / 2) = P.k * P.k by omega_arith]
      intro s u h
      simpa only [finalCount, hodd, Bool.false_eq_true, false_and, ite_false] using h

end VG.Proof.MlKem.AArch64.Kem16P
