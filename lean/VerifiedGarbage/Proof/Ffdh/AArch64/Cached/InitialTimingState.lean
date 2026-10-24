module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.InitialTimingParts
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.FieldFrame
import VerifiedGarbage.Proof.Framework.Omega

/-! Field and immutable-domain state across the table initializer. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure InitialPublic where
 p : Parameters
 dom : Addr
 bs : List Byte
 words : p.w=(p.k+7)/8
 positive : 0<p.k
 size : p.k<2^31
 reduced : p.G<p.P

structure TableInitialReady (q : InitialPublic) (s : State) : Prop where
 field : FieldInitial q.p s
 space : ContextSpace q.p s
 generator : GeneratorSource q.p (q.dom+BitVec.ofNat 64 q.p.k) q.bs s
 context : word s.mem q.p.B (8*sCtx)=q.p.ctx
 domain : word s.mem q.p.B (8*sDom)=q.dom
 length : word s.mem q.p.B (8*sLen)=BitVec.ofNat 64 q.p.k

structure InitialWorking (q : InitialPublic) (s : State) : Prop where
 state : ModState q.p s
 space : ContextSpace q.p s
 generator : GeneratorSource q.p (q.dom+BitVec.ofNat 64 q.p.k) q.bs s
 context : word s.mem q.p.B (8*sCtx)=q.p.ctx
 domain : word s.mem q.p.B (8*sDom)=q.dom
 length : word s.mem q.p.B (8*sLen)=BitVec.ofNat 64 q.p.k

theorem initialOne_working (M : Mont) {q : InitialPublic} {s : State} (h : TableInitialReady q s) :
 WP isa (.seq (const 7 1) (M.mm 6 4 7)) s (InitialWorking q) := by
 refine WP.mono (field_initial_power M h.field) ?_
 rintro t ⟨power,frame,rest⟩
 exact ⟨power.toModState,h.space.after rest,h.generator.after_inscr (InScr.of_arrays frame q.p.room (by simp)) rest,
  (arrays_header frame (by decide)).trans h.context,(arrays_header frame (by decide)).trans h.domain,
  (arrays_header frame (by decide)).trans h.length⟩

theorem initialZero_stored {q : InitialPublic} {s : State} (h : InitialWorking q s) :
 WP isa (.seq (.block [movi .x3 0]) (storeEntry 6)) s (InitialWorking q) := by
 refine WP.mono (storeLiteral_ok h.state.good h.space h.context (by decide : 6<8) (by decide : 0<32)) ?_
 rintro t ⟨good,_,frame,same,rest⟩
 have field : FieldInitial q.p s := ⟨h.state.good,h.state.modulus,h.state.inverse,h.state.r2⟩
 have next :=field.after_workspace good same
 have one :=(workspace_array h.state.good same (by decide : 7<8)).trans h.state.one
 have state : ModState q.p t :=⟨next.good,next.modulus,next.inverse,one,next.r2⟩
 exact ⟨state,h.space.after rest,h.generator.after_entry frame (by decide) rest,
  (workspace_header h.state.good same (by decide)).trans h.context,
  (workspace_header h.state.good same (by decide)).trans h.domain,
  (workspace_header h.state.good same (by decide)).trans h.length⟩

/-- Input to the generator-to-Montgomery conversion. -/
def GeneratorLoaded (q : InitialPublic) (s : State) : Prop :=
 InitialWorking q s ∧ wv s.mem q.p.B (slot q.p.w 1) q.p.w=q.p.G

theorem initialGenerator_loaded {q : InitialPublic} {s : State} (h : InitialWorking q s) :
 WP isa (.seq (.block [ldh .x1 sDom,ldh .x2 sLen,.add .x .x1 .x1 .x2]) (load 1)) s (GeneratorLoaded q) := by
 refine WP.mono (generatorLoad_ok h.state.good h.generator q.words q.positive q.size h.domain h.length) ?_
 rintro t ⟨good,value,frame,rest⟩
 exact ⟨⟨h.state.after_arrays good frame (by decide) (by decide) (by decide),h.space.after rest,
  h.generator.after_inscr (InScr.of_arrays frame q.p.room (by simp)) rest,
  (arrays_header frame (by decide)).trans h.context,(arrays_header frame (by decide)).trans h.domain,
  (arrays_header frame (by decide)).trans h.length⟩,value⟩

end VG.Proof.Ffdh.AArch64.Cached
