module

public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Rounds
import VerifiedGarbage.Proof.Framework.Interleave

/-! # Composition of the serial core's read-only arithmetic kernel -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.Impl.Camellia.AArch64.Serial

structure Stable (s t : State) : Prop where
  regs : ∀ r, r ∉ written → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem Stable.refl (s : State) : Stable s s :=
  ⟨fun _ _ => rfl,rfl,rfl,rfl,rfl⟩

theorem Stable.trans {s t u : State} (h : Stable s t) (g : Stable t u) : Stable s u :=
  ⟨fun r hr => (g.regs r hr).trans (h.regs r hr),g.mem.trans h.mem,
    g.rd.trans h.rd,g.wr.trans h.wr,g.sp.trans h.sp⟩

theorem Stable.keys {s t : State} (h : Stable s t) : keyWord t = keyWord s := by
  funext j
  simp only [keyWord,h.mem,h.regs .x5 (by decide)]

structure Context (s : State) : Prop where
  constants : Constants s
  masks : Masks s
  table : Table s
  read : ∀ j < 34, InRegions (s.rd ++ s.wr) (s.gpr .x5+BitVec.ofNat 64 (256+8*j)) 8

theorem Context.read_stable {s t : State} (h : Context s) (hs : Stable s t) :
    ∀ j < 34, InRegions (t.rd ++ t.wr) (t.gpr .x5+BitVec.ofNat 64 (256+8*j)) 8 := by
  intro j hj
  rw [hs.rd,hs.wr,hs.regs .x5 (by decide)]
  exact h.read j hj

theorem six_step {s : State} (h : Context s) (k : Nat) (hk : k+6 ≤ 34) :
    ∃ t, runBlock isa (six k) s = some t ∧ Context t ∧ Stable s t ∧
      halves t = pairs (keyWord s) k 3 (halves s) := by
  obtain ⟨t,he,hv,hc,hm,ht,hg,hmem,hrd,hwr,hsp⟩ :=
    six_run s k hk h.constants h.masks h.table h.read
  have hs : Stable s t := ⟨hg,hmem,hrd,hwr,hsp⟩
  exact ⟨t,he,⟨hc,hm,ht,h.read_stable hs⟩,hs,hv⟩

theorem fl_step {s : State} (h : Context s) (k : Nat) (hk : k+1 < 34) :
    ∃ t, runBlock isa (flPair k) s = some t ∧ Context t ∧ Stable s t ∧
      halves t = (Spec.Camellia.fl (halves s).1 (keyWord s k),
        Spec.Camellia.flinv (halves s).2 (keyWord s (k+1))) := by
  obtain ⟨t,he,hv,hc,hm,ht,hg,hmem,hrd,hwr,hsp⟩ :=
    flPair_run s k hk h.constants h.masks h.table h.read
  have hs : Stable s t := ⟨hg,hmem,hrd,hwr,hsp⟩
  exact ⟨t,he,⟨hc,hm,ht,h.read_stable hs⟩,hs,hv⟩

theorem partial_run {s : State} (h : Context s) :
    ∃ t, runBlock isa (six 2 ++ flPair 8 ++ six 10 ++ flPair 16 ++ six 18) s = some t ∧
      Context t ∧ Stable s t ∧ halves t = partialRounds (keyWord s) (halves s) := by
  obtain ⟨a,ae,ac,as,av⟩ := six_step h 2 (by decide)
  obtain ⟨b,be,bc,bs,bv⟩ := fl_step ac 8 (by decide)
  obtain ⟨c,ce,cc,cs,cv⟩ := six_step bc 10 (by decide)
  obtain ⟨d,de,dc,ds,dv⟩ := fl_step cc 16 (by decide)
  obtain ⟨e,ee,ec,es,ev⟩ := six_step dc 18 (by decide)
  have ab := as.trans bs
  have abc := ab.trans cs
  have abcd := abc.trans ds
  refine ⟨e,?_,ec,abcd.trans es,?_⟩
  · rw [VG.Interleave.runBlock_append,VG.Interleave.runBlock_append,
      VG.Interleave.runBlock_append,VG.Interleave.runBlock_append,
      ae,Option.bind_some,be,Option.bind_some,ce,Option.bind_some,de,Option.bind_some,ee]
  · rw [ev,dv,cv,bv,av,abcd.keys,abc.keys,ab.keys,as.keys]
    rfl

theorem last_run {s : State} (h : Context s) :
    ∃ t, runBlock isa (flPair 24 ++ six 26) s = some t ∧ Context t ∧ Stable s t ∧
      halves t = lastRounds (keyWord s) (halves s) := by
  obtain ⟨a,ae,ac,as,av⟩ := fl_step h 24 (by decide)
  obtain ⟨b,be,bc,bs,bv⟩ := six_step ac 26 (by decide)
  refine ⟨b,?_,bc,as.trans bs,?_⟩
  · rw [VG.Interleave.runBlock_append,ae,Option.bind_some,be]
  · rw [bv,av,as.keys]
    rfl

end VG.Proof.Camellia.AArch64.Serial
