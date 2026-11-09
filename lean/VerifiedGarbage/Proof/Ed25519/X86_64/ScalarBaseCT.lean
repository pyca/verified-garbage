module

import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
public import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseMain
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
meta import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseMain
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
meta import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldWide
public import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowers

/-! Merged from `Proof.Ed25519.X86_64.PointMulCT`. -/

@[expose] public section

/-! Merged from `Proof.Ed25519.X86_64.ScalarBaseCTEngine`. -/
section
/-! Expand secret scalar bits, multiply, and encode with a public trace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs)

variable {fld : Arith} [EdArith fld]

def BaseEnginePre (base k T : Addr) (s : State) : Prop :=
  Scratch s base ∧ s.gpr .rsi = k ∧
    (∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1) ∧
    (∀ q < 32, 8192 ≤ ofs base (off k q)) ∧ CombTbl s T ∧ TblFar base T

end VG.Proof.Ed25519.X86_64
end

/-! Public argument pointers survive the secret point arithmetic. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]

private def BaseStart (base k T out : Addr) (s : State) : Prop :=
  scalarBaseLocal.pre s ∧ s.gpr .rdi = out ∧ s.gpr .rsi = k ∧ s.gpr .rdx = base ∧ s.syms combSym = T

private def BasePrepared (base k T out : Addr) (s : State) : Prop :=
  BaseEnginePre base k T s ∧ s.mem.readW (off base 48) 64 = out

private def BaseReady (base out : Addr) (s : State) : Prop :=
  Scratch s base ∧ s.mem.readW (off base 48) 64 = out

private theorem start_ok {base k T out : Addr} {s : State} (hs : BaseStart base k T out s) :
    WP isa (.block (scalarSave ++ scalarBaseSetup)) s (BasePrepared base k T out) := by
  have ⟨tbl, far⟩ := scalarBaseLocal_tbl hs.1
  obtain ⟨⟨hr, hw, hd, _, _, hn, hh⟩, ho, hk, hb, hT⟩ := hs
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hb]; simp
  rw [WP.block_append_iff]
  refine WP.mono_syms (scalarSave_ok hb hws) fun a ⟨ga, ra, wa, ma, _⟩ asy => ?_
  have hwa : (⟨a.gpr .rdx, 8192⟩ : Region) ∈ a.wr := by rw [ga, hb, wa]; exact hws
  refine WP.mono_syms (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, ob, mb⟩ bsy => ?_
  rw [ga, hb] at pb ob mb
  rw [hb] at far
  have hh2 := hh.2.2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  rw [hT] at tbl far hh2
  have fm : Frame [⟨base, 8192⟩] s.mem b.mem :=
    (scratchFrame ma (by decide)).trans (scratchFrame mb (by decide))
  refine ⟨⟨⟨pb, by rw [wb, wa]; exact hws, by rw [← hb]; exact hn⟩,
    (gb _ (by decide)).trans ((congrFun ga _).trans hk), ?_, ?_,
    tbl.frame fm (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [← hb]; exact hh2)
      (by rw [rb, wb, ra, wa]) (by rw [bsy, asy]), far⟩, ob.trans ho⟩
  · intro q hq
    exact ⟨⟨k, 32⟩, by rw [rb, ra, hr, hk]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  · intro q hq
    rw [hk, hb] at hd
    exact farScratch hd hq (by decide)

private theorem start_ct (base k T out : Addr) :
    RelCT isa (fun x y => BaseStart base k T out x ∧ BaseStart base k T out y)
      (.block (scalarSave ++ scalarBaseSetup))
      (fun x y => BasePrepared base k T out x ∧ BasePrepared base k T out y) := by
  have hc : RelCT isa (fun x y => BaseStart base k T out x ∧ BaseStart base k T out y)
      (.block (scalarSave ++ scalarBaseSetup)) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi, .rsi, .rdx]) _ (by fld_taint_decide)
    intro x y h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.1.trans h.2.2.2.2.1.symm
  exact (hc.wp (fun _ _ h => ⟨start_ok h.1, start_ok h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem engine_ready {engine : Prog isa} (engine_ok : BaseEngineCorrect engine) {base k T out : Addr}
    {s : State} (hs : BasePrepared base k T out s) :
    WP isa engine s (BaseReady base out) := by
  refine WP.mono (engine_ok hs.1.1 hs.1.2.1 hs.1.2.2.1 hs.1.2.2.2.1 hs.1.2.2.2.2.1 hs.1.2.2.2.2.2)
    fun t ⟨kt, _⟩ => ?_
  exact ⟨kt.scratch hs.1.1, ((powersKeep_outside kt).word
    (d := 48) (Or.inl (by decide)) (by decide)).trans hs.2⟩

private theorem engine_ct {engine : Prog isa} (engine_ok : BaseEngineCorrect engine)
    (engine_ct : ∀ base k T, RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      engine (fun _ _ => True)) (base k T out : Addr) :
    RelCT isa (fun x y => BasePrepared base k T out x ∧ BasePrepared base k T out y)
      engine (fun x y => BaseReady base out x ∧ BaseReady base out y) := by
  have hc := (engine_ct base k T).mono
    (fun _ _ (h : BasePrepared base k T out _ ∧ BasePrepared base k T out _) => ⟨h.1.1, h.2.1⟩)
    (fun _ _ h => h)
  exact (hc.wp (fun _ _ h => ⟨engine_ready engine_ok h.1, engine_ready engine_ok h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem finish_ct (base out : Addr) :
    RelCT isa (fun x y => BaseReady base out x ∧ BaseReady base out y)
      scalarBaseFinish (fun _ _ => True) := by
  have hc : RelCT isa (fun x y => BaseReady base out x ∧ BaseReady base out y)
      (.block scalarBaseFinishArgs) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro x y h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.rdi.trans h.2.1.rdi.symm)
  have hw : ∀ s, BaseReady base out s → WP isa (.block scalarBaseFinishArgs) s
      (fun t => t.gpr .rdx = base ∧ t.gpr .rdi = out) := by
    intro s h
    exact WP.mono (scalarBaseFinishArgs_ok h.1) fun _ ht => ⟨ht.1, ht.2.1.trans h.2⟩
  have hc' := (hc.wp (fun _ _ h => ⟨hw _ h.1, hw _ h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)
  rw [scalarBaseFinish]
  refine VG.RelCT.seq hc' ?_
  apply taintFld (Taint.ofRegs [.rdx, .rdi]) _ (by fld_taint_decide)
  intro x y h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem scalarBase_ct_of_engine (engine : Prog isa) (engine_ok : BaseEngineCorrect engine)
    (engineCT : ∀ base k T, RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      engine (fun _ _ => True)) :
    ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub (scalarBaseWith engine) := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  intro x y tx ty x' y' ⟨hx, hy, _, ho, hk, hb, hT⟩ ex ey
  have hc := VG.RelCT.seq (start_ct (x.gpr .rdx) (x.gpr .rsi) (x.syms combSym) (x.gpr .rdi))
    (VG.RelCT.seq (engine_ct engine_ok engineCT (x.gpr .rdx) (x.gpr .rsi) (x.syms combSym) (x.gpr .rdi))
      (finish_ct (x.gpr .rdx) (x.gpr .rdi)))
  exact hc _ _ _ _ _ _ ⟨⟨hx, rfl, rfl, rfl, rfl⟩, ⟨hy, ho.symm, hk.symm, hb.symm, hT.symm⟩⟩ ex ey

end VG.Proof.Ed25519.X86_64
