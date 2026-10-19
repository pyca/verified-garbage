module

public import VerifiedGarbage.Proof.X25519.X86_64.Base.Main
meta import VerifiedGarbage.Proof.X25519.X86_64.Base.Main
public import VerifiedGarbage.Proof.X25519.X86_64.Base.Lit
meta import VerifiedGarbage.Proof.X25519.X86_64.Base.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
meta import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.Ed25519.X86_64.BaseOdd
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Group.Decode
import VerifiedGarbage.Proof.Ed25519.Recode
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.Ed25519.X86_64.CachedPoint
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.CombNeg
import VerifiedGarbage.Proof.Ed25519.X86_64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldLazy
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Keeps
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Ops
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAffine
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEncode
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowersLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowEntry
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.X25519.X86_64.AddSub
import VerifiedGarbage.Proof.X25519.X86_64.Adx.A24
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Mul
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Sqr
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.X25519.X86_64.Bits
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.ARow
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Main
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Step
import VerifiedGarbage.Proof.X25519.X86_64.Finish
import VerifiedGarbage.Proof.X25519.X86_64.Freeze
import VerifiedGarbage.Proof.X25519.X86_64.Inv
import VerifiedGarbage.Proof.X25519.X86_64.Invert
import VerifiedGarbage.Proof.X25519.X86_64.Iter
import VerifiedGarbage.Proof.X25519.X86_64.Sqr
meta import VerifiedGarbage.Impl.Ed25519.X86_64.BaseOdd
meta import VerifiedGarbage.Proof.Ed25519.Bytes
meta import VerifiedGarbage.Proof.Ed25519.Group.Decode
meta import VerifiedGarbage.Proof.Ed25519.Recode
meta import VerifiedGarbage.Proof.Ed25519.Scalar
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CachedPoint
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CombLoop
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CombNeg
meta import VerifiedGarbage.Proof.Ed25519.X86_64.DecodeBits
meta import VerifiedGarbage.Proof.Ed25519.X86_64.FieldLazy
meta import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
meta import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddMemory
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Keeps
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Ops
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointAffine
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointEncode
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTBatch
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowersLoop
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Points
meta import VerifiedGarbage.Proof.Ed25519.X86_64.WindowEntry
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.Pratt
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.X25519.X86_64.AddSub
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.A24
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.Mul
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.Sqr
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
meta import VerifiedGarbage.Proof.X25519.X86_64.Bits
meta import VerifiedGarbage.Proof.X25519.X86_64.Divstep.ARow
meta import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Main
meta import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Step
meta import VerifiedGarbage.Proof.X25519.X86_64.Finish
meta import VerifiedGarbage.Proof.X25519.X86_64.Freeze
meta import VerifiedGarbage.Proof.X25519.X86_64.Inv
meta import VerifiedGarbage.Proof.X25519.X86_64.Invert
meta import VerifiedGarbage.Proof.X25519.X86_64.Iter
meta import VerifiedGarbage.Proof.X25519.X86_64.Sqr

/-! Public pointers survive the secret fixed-base arithmetic. -/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Base
open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64.Base
open VG.Proof.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)
variable {fld : Arith} [EdArith fld]

private def BaseStart (base k T out : Addr) (s : State) : Prop :=
  baseLocal.pre s ∧ s.gpr .rdi = out ∧ s.gpr .rsi = k ∧ s.gpr .rdx = base ∧ s.syms combSym = T

private def BasePrepared (base k T out : Addr) (s : State) : Prop :=
  BaseEnginePre base k T s ∧ s.mem.readW (off base 48) 64 = out

private def BaseReady (base out : Addr) (s : State) : Prop :=
  Scratch s base ∧ s.mem.readW (off base 48) 64 = out

private theorem start_ok {base k T out : Addr} {s : State} (hs : BaseStart base k T out s) :
    WP isa (.block (scalarSave ++ scalarBaseSetup)) s (BasePrepared base k T out) := by
  have ⟨tbl, far⟩ := scalarBaseLocal_tbl (baseLocal_pre hs.1)
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

private theorem engine_ready {eng : Prog isa} (heng : UEngineOk eng) {base k T out : Addr} {s : State}
    (hs : BasePrepared base k T out s) : WP isa eng s (BaseReady base out) := by
  refine WP.mono (heng hs.1.1 hs.1.2.1 hs.1.2.2.1 hs.1.2.2.2.1 hs.1.2.2.2.2.1 hs.1.2.2.2.2.2)
    fun t ⟨kt, _⟩ => ?_
  exact ⟨kt.scratch hs.1.1, ((powersKeep_outside kt).word
    (d := 48) (Or.inl (by decide)) (by decide)).trans hs.2⟩

private theorem engine_ct {eng : Prog isa} (heng : UEngineOk eng)
    (engine_ct : ∀ base k T, RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      eng (fun _ _ => True)) (base k T out : Addr) :
    RelCT isa (fun x y => BasePrepared base k T out x ∧ BasePrepared base k T out y)
      eng (fun x y => BaseReady base out x ∧ BaseReady base out y) := by
  have hc := (engine_ct base k T).mono
    (fun _ _ (h : BasePrepared base k T out _ ∧ BasePrepared base k T out _) => ⟨h.1.1, h.2.1⟩)
    (fun _ _ h => h)
  exact (hc.wp (fun _ _ h => ⟨engine_ready heng h.1, engine_ready heng h.2⟩)).mono
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

theorem x25519BaseWith_ct (eng : Prog isa) (heng : UEngineOk eng)
    (engineCT : ∀ base k T, RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      eng (fun _ _ => True)) :
    ConstantTime isa baseLocal.pre baseLocal.pub (scalarBaseWith eng) := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  intro x y tx ty x' y' ⟨hx, hy, _, ho, hk, hb, hT⟩ ex ey
  have hc := VG.RelCT.seq (start_ct (x.gpr .rdx) (x.gpr .rsi) (x.syms combSym) (x.gpr .rdi))
    (VG.RelCT.seq (engine_ct heng engineCT (x.gpr .rdx) (x.gpr .rsi) (x.syms combSym) (x.gpr .rdi))
      (finish_ct (x.gpr .rdx) (x.gpr .rdi)))
  exact hc _ _ _ _ _ _ ⟨⟨hx, rfl, rfl, rfl, rfl⟩, ⟨hy, ho.symm, hk.symm, hb.symm, hT.symm⟩⟩ ex ey

theorem x25519Base_ct [DivstepInv]
    (engineCT : ∀ base k T, RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      (engine fld).inline (fun _ _ => True)) :
    ConstantTime isa baseLocal.pre baseLocal.pub (x25519Base fld).inline := by
  rw [x25519Base, scalarBaseWith_inline]
  exact x25519BaseWith_ct _ engine_ok engineCT

end VG.Proof.X25519.X86_64.Base
