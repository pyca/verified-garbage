module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Last
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastTiming
public import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.SlotTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FinishTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Env
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Last
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastTiming
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.SlotTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FinishTiming
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

/-!
# The singleton computing PRF outputs leaks only public pointers and the public seed

As `Paired.lastCode_relCT`: its start and three main squeezes (`lastPrep`) by
one taint analysis from `x28` of a copy without immediates and offsets, which
are all that tell its squeezes apart, then the rejection, the full sampler and
the restore as there.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Paired (LastInput seedBytes fullWrites exec_post seq_parts
  fullSampleCode_relCT restore_ct reject_relCT ct_eraseOff_eq)

/-- The singleton's start, three main squeezes and constants. -/
def lastPrep (sb ss a k bo N₀ : Nat) : Prog isa :=
  .seq (.seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a a k ++ Impl.MlKem.AArch64.ptrTo .x21 .x28 bo))
    (.seq (Impl.MlKem.AArch64.Kem16P.stepB N₀) (.seq (Impl.MlKem.AArch64.Kem16P.stepB (N₀ + 1))
      (Impl.MlKem.AArch64.Kem16P.stepB (N₀ + 2)))))
    (.block Impl.MlKem.AArch64.Rej8.rejConsts)

theorem lastPrep_erase {sb ss a k bo N₀ : Nat} (hss : ss < 4096) (hbo : 4096 ≤ bo) :
    Code.eraseOff (lastPrep sb ss a k bo N₀) = Code.eraseOff (lastPrep 0 0 0 1 4096 0) := by
  simp only [lastPrep, Code.eraseOff, List.map_append, Impl.MlKem.AArch64.Kem16P.stepB,
    Impl.MlKem.AArch64.Kem16P.reinitB, prfWords_eraseOff, Impl.MlKem.AArch64.Paired.init,
    Impl.MlKem.AArch64.ptrTo, ite_eq_left hss, ite_eq_right (show ¬ bo < 4096 by omega),
    ite_eq_left (show (0 : Nat) < 4096 by decide), ite_eq_right (show ¬ (4096 : Nat) < 4096 by decide)]
  rfl

theorem lastPrep_ct {sb ss a k bo N₀ : Nat} (hss : ss < 4096) (hbo : 4096 ≤ bo) :
    ConstantTime isa (fun _ => True) (VG.AArch64.Taint.Agree (Taint.ofRegs [.x28]))
      (lastPrep sb ss a k bo N₀) := by
  apply ct_eraseOff_eq [.x28] (d := Code.eraseOff (lastPrep 0 0 0 1 4096 0)) (lastPrep_erase hss hbo)
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
    (hN : N₀ + 2 < 256) (hbo : Impl.MlKem.AArch64.Kem16P.bufOff L N₀ < 65536)
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8 : sb % 8 = 0)
    (hk : 0 < L.k) (hk256 : L.k ≤ 256)
    (ps : LastInput sb ss off p seed out table s)
    (hl : LayB p R B₀ s) (ap : BufApart p seed out table R B₀)
    (hR : s.gpr .x28 + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : s.gpr .x28 + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) = B₀) :
    WP isa (lastPrep sb ss a L.k (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) N₀) s
      (LastPreparedP w16 (xofByte (seedBytes s.mem seed a L.k)) p out table s) := by
  refine WP.seq (WP.mono_syms (startB_ok L (a := a) hN hbo hss hsb h8 ps.ptr ps.seedPtr ps.readable
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
    (hN : N₀ + 2 < 256) (hbo : Impl.MlKem.AArch64.Kem16P.bufOff L N₀ < 65536)
    (h4 : 4096 ≤ Impl.MlKem.AArch64.Kem16P.bufOff L N₀)
    (hss : ss < 4096) (hsb : sb + 32 ≤ 32768) (h8 : sb % 8 = 0) (hoff : off < 65536)
    (hk : 0 < L.k) (hk256 : L.k ≤ 256)
    (ps : LastInput sb ss off p seed out table s) (pu : LastInput sb ss off p seed out table u)
    (hls : LayB p R B₀ s) (hlu : LayB p R B₀ u) (ap : BufApart p seed out table R B₀)
    (hR : s.gpr .x28 + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : s.gpr .x28 + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) = B₀)
    (sp : s.sp = u.sp) (base : s.gpr .x28 = u.gpr .x28)
    (seedEq : seedBytes s.mem seed a L.k = seedBytes u.mem seed a L.k) :
    RelCT isa (fun t v => t = s ∧ v = u)
      (lastStartP sb ss a L.k off (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) N₀ w16)
      (fun t v => LastStartPostP w16 (xofByte (seedBytes s.mem seed a L.k)) p out table R B₀ N₀ s t ∧
        LastStartPostP w16 (xofByte (seedBytes u.mem seed a L.k)) p out table R B₀ N₀ u v) := by
  have hRu : u.gpr .x28 + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R := by rw [← base]; exact hR
  have hBu : u.gpr .x28 + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) = B₀ := by
    rw [← base]; exact hB
  let Rr := fun t v : State => LastPreparedP w16 (xofByte (seedBytes s.mem seed a L.k)) p out table s t ∧
    LastPreparedP w16 (xofByte (seedBytes u.mem seed a L.k)) p out table u v
  have start : RelCT isa (fun t v => t = s ∧ v = u)
      (lastPrep sb ss a L.k (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) N₀) Rr := by
    intro t v tr ur t' v' h et ev
    rcases h with ⟨ht, hv⟩; subst t; subst v
    exact ⟨lastPrep_ct hss h4 s u tr ur t' v' trivial trivial
      (agree_of sp (by intro r hr; rw [List.mem_singleton.mp hr]; exact base)) et ev,
      exec_post (lastPrepP_ok L hN hbo (by omega) hsb h8 hk hk256 ps hls ap hR hB) et,
      exec_post (lastPrepP_ok L hN hbo (by omega) hsb h8 hk hk256 pu hlu ap hRu hBu) ev⟩
  have grouped : RelCT isa (fun t v => t = s ∧ v = u)
      (.seq (lastPrep sb ss a L.k (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) N₀)
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
      (lastStartP sb ss a L.k off (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) N₀ w16) (fun _ _ => True) :=
    RelCT.assoc (RelCT.assoc grouped)
  intro t v tr ur t' v' h et ev
  rcases h with ⟨ht, hv⟩; subst t; subst v
  exact ⟨(trace s u tr ur t' v' ⟨rfl, rfl⟩ et ev).1,
    exec_post (lastStartP_ok L hN hbo (by omega) hsb h8 hoff hk hk256 ps.ptr ps.seedPtr ps.outPtr
      ps.readable ps.separate ps.context ps.symbol hls ap hR hB) et,
    exec_post (lastStartP_ok L hN hbo (by omega) hsb h8 hoff hk hk256 pu.ptr pu.seedPtr pu.outPtr
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
    (h : Exec isa (lastCodeP sb ss a k off bo N₀ w16) s tr t) :
    Exec isa (.seq (lastStartP sb ss a k off bo N₀ w16) (Paired.lastTail sb ss a k off w16)) s tr t := by
  obtain ⟨_, _, _, rfl, ei, h⟩ := seq_parts h
  obtain ⟨_, _, _, rfl, es, h⟩ := seq_parts h
  obtain ⟨_, _, _, rfl, ec, h⟩ := seq_parts h
  obtain ⟨_, _, _, rfl, er, h⟩ := seq_parts h
  have ee := Exec.seq (Exec.seq ei (Exec.seq es (Exec.seq ec er))) h
  simpa only [lastStartP, Paired.lastTail, List.append_assoc] using ee

/-- **The singleton computing PRF outputs** leaks only public pointers and the public seed. -/
theorem lastCodeP_relCT (L : Impl.MlKem.AArch64.KemLay) {w16 : Bool} {s u : State}
    {p seed out table R B₀ : Addr} {sb ss a off N₀ : Nat}
    (hN : N₀ + 2 < 256) (hbo : Impl.MlKem.AArch64.Kem16P.bufOff L N₀ < 65536)
    (h4 : 4096 ≤ Impl.MlKem.AArch64.Kem16P.bufOff L N₀)
    (hss : ss < 4096) (hsb : sb + 32 ≤ 32768) (h8 : sb % 8 = 0) (hoff : off < 65536)
    (hk : 0 < L.k) (hk256 : L.k ≤ 256)
    (ps : LastInput sb ss off p seed out table s) (pu : LastInput sb ss off p seed out table u)
    (ho : (Region.mk seed 32).Disjoint (polyRegion out))
    (hls : LayB p R B₀ s) (hlu : LayB p R B₀ u) (ap : BufApart p seed out table R B₀)
    (hR : s.gpr .x28 + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : s.gpr .x28 + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) = B₀)
    (sp : s.sp = u.sp) (base : s.gpr .x28 = u.gpr .x28)
    (seedEq : seedBytes s.mem seed a L.k = seedBytes u.mem seed a L.k) :
    RelCT isa (fun t v => t = s ∧ v = u)
      (lastCodeP sb ss a L.k off (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) N₀ w16) (fun _ _ => True) := by
  let Rr := fun t v : State => LastStartPostP w16 (xofByte (seedBytes s.mem seed a L.k)) p out table R B₀ N₀ s t ∧
    LastStartPostP w16 (xofByte (seedBytes u.mem seed a L.k)) p out table R B₀ N₀ u v ∧
    t.syms = s.syms ∧ v.syms = u.syms
  have start : RelCT isa (fun t v => t = s ∧ v = u)
      (lastStartP sb ss a L.k off (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) N₀ w16) Rr := by
    intro t v tr ur t' v' h et ev
    have hh := lastStartP_relCT L hN hbo h4 hss hsb h8 hoff hk hk256 ps pu hls hlu ap hR hB sp base seedEq
      t v tr ur t' v' h et ev
    rcases h with ⟨ht, hv⟩; subst t; subst v
    exact ⟨hh.1, hh.2.1, hh.2.2, Exec.syms et, Exec.syms ev⟩
  have branch : RelCT isa Rr (.ite (.zero .x .x22) (Paired.fullSampleCode sb ss off a L.k w16) (.block []))
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
      have hh := fullSampleCode_relCT hss hsb h8 hoff hk hk256
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
      (.seq (lastStartP sb ss a L.k off (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) N₀ w16)
        (Paired.lastTail sb ss a L.k off w16)) (fun _ _ => True) := by
    refine RelCT.seq start (RelCT.seq branch ?_)
    intro t v tr ur t' v' h et ev
    exact ⟨restore_ct t v tr ur t' v' trivial trivial
      (agree_of h.1 (by intro r hr; rw [List.mem_singleton.mp hr]; exact h.2)) et ev, trivial⟩
  intro t v tr ur t' v' h et ev
  exact grouped t v tr ur t' v' h (lastP_exec et) (lastP_exec ev)

end VG.Proof.MlKem.AArch64.Kem16P
