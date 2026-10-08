import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Buffer
import VerifiedGarbage.Proof.Framework.X86_64.YFrame

/-! # Register frames for the integer and vector work between AES rounds -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64

structure FlowFrame (rs : List XReg) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  lane : ∀ r, r ∉ rs → ∀ l < 2, t.lane r l = s.lane r l
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem FlowFrame.refl (rs : List XReg) (s : State) : FlowFrame rs s s :=
  ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl⟩

theorem FlowFrame.trans {rs : List XReg} {s t u : State}
    (h : FlowFrame rs s t) (h' : FlowFrame rs t u) : FlowFrame rs s u :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr),
    fun r hr l hl => (h'.lane r hr l hl).trans (h.lane r hr l hl),
    h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem FlowFrame.of_yframe {rs : List XReg} {s t : State} (h : YFrame rs s t) :
    FlowFrame rs s t := ⟨fun r _ => congrFun h.gpr r, h.lane, h.rd, h.wr⟩

theorem FlowFrame.of_buffer (rs : List XReg) {s t : State} (h : BufferFrame s t) :
    FlowFrame rs s t := ⟨h.gpr, fun r _ l _ => h.lane r l, h.rd, h.wr⟩

theorem FlowFrame.mono {rs rs' : List XReg} {s t : State} (h : FlowFrame rs s t)
    (hs : ∀ r ∈ rs, r ∈ rs') : FlowFrame rs' s t :=
  ⟨h.gpr, fun r hr => h.lane r (fun he => hr (hs r he)), h.rd, h.wr⟩

end VG.Proof.Gcm.X86_64.StitchAvx8
