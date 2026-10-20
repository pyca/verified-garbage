module

public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPower
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack

/-! The saved public layout and context pointer supply cached exponentiation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedPower
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem load_ok (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat}
    (h : SampleContext p l slots s) (h52 : 52∈slots) :
    WP isa (.block VG.Impl.Ffdh.Arm.CachedPower.load) s fun t =>
      (t.gpr .r1=l.start ∧ t.gpr .r2=BitVec.ofNat 32 l.width ∧
        t.gpr .r4=p.cachedContext ∧ t.mem=s.mem) ∧ Rest [.r1,.r2,.r4] s t := by
  have addr (d : Nat) (hd : d≤68) : State.addr (s.sp+BitVec.ofNat 32 d)=off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  have read16 := h.locals.read (by decide : 16+4≤72)
  have read20 := h.locals.read (by decide : 20+4≤72)
  have read52 := h.locals.read (by decide : 52+4≤72)
  have context := h.saved 52 h52
  change s.mem.readW (off (State.addr s.sp) 52) 32=p.cachedContext at context
  refine withRest [.r1,.r2,.r4] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.CachedPower.load : Prog isa)).all
        (fun i=>!(clobbers i r))=true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have flag := List.all_eq_true.mp checked i hi
    cases hi' : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.CachedPower.load
  ffrun [addr 16 (by decide),addr 20 (by decide),addr 52 (by decide),read16,read20,read52,
    h.scalarStart,h.scalarWidth,context,off]

end VG.Proof.Ffdh.Arm.CachedPower
