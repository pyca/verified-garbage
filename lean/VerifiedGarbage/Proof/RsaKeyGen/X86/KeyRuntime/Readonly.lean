module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
public import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Framework.Omega

/-! # Arithmetic writes only the workspace, keeping the original arguments read-only -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.KeyRt (RtWs)
open VG.Proof.Bignum.X86 (CallArgument)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context)

def readonly (s : State) (B : Addr) (Z : Nat) : State :=
  s.withRegions (s.rd ++ s.wr) [⟨B, Z⟩]

theorem readonly_read {s : State} {B : Addr} {Z : Nat} :
    Covers (s.rd ++ s.wr) ((readonly s B Z).rd ++ (readonly s B Z).wr) :=
  Covers.of_mem fun _ hr => List.mem_append_left _ hr

theorem argument_readonly {s : State} {B : Addr} {Z i : Nat} {v : BitVec 32}
    (h : CallArgument s B Z i v) : CallArgument (readonly s B Z) B Z i v :=
  ⟨⟨readonly_read _ _ h.stack.read, h.stack.apart⟩, h.value⟩

theorem rtws_readonly {L : VG.Impl.Rsa.X86.KeyRt.Lay} {s : State} {B : Addr} {Z len N : Nat}
    (h : RtWs L s B Z len N) : RtWs L (readonly s B Z) B Z len N := by
  refine ⟨?_, h.lenArg.imp fun _ ⟨a, l, c⟩ => ⟨a, l, argument_readonly c⟩,
    argument_readonly h.wsArg, h.lenLe, h.layLen⟩
  exact { h.ws with workspace := { h.ws.workspace with wr := List.mem_singleton_self _ } }

theorem Ws.readonly {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N) :
    Ws (readonly s B Z) B Z n N :=
  ⟨rtws_readonly h.full, rtws_readonly h.prime, rtws_readonly h.exponent, h.width, h.size⟩

theorem context_readonly {s : State} {B : Addr} {Z : Nat} {p : BitVec 32} {args : Nat → BitVec 32}
    (C : Context B Z p args s) : Context B Z p args (readonly s B Z) := by
  refine ⟨{ C.scratch with wr := List.mem_singleton_self _ }, C.header, C.sp, C.fit, C.separate, ?_⟩
  intro i hi
  exact VG.X86.readSrc_widen readonly_read (C.read i hi)

theorem readonly_covers {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N) :
    Covers ((readonly s B Z).rd ++ (readonly s B Z).wr) (s.rd ++ s.wr) ∧
      Covers (readonly s B Z).wr s.wr := by
  have write : Covers (readonly s B Z).wr s.wr := Covers.of_mem (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact h.old.workspace.wr)
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right write), write⟩

theorem trace_readonly_of_wp {c : Prog isa} {s t : State} {B : Addr} {Z n N : Nat} {Q : State → Prop}
    (h : Ws s B Z n N) (run : WP isa c (readonly s B Z) Q)
    {trace : List Leak} (E : Exec isa c s trace t) :
    ∃ u, Exec isa c (readonly s B Z) trace u := by
  obtain ⟨trace', u, EU, _⟩ := run
  obtain ⟨read, write⟩ := readonly_covers h
  have EW := VG.X86.Exec.widen EU read write
  simp only [readonly, State.withRegions_withRegions, State.withRegions_self] at EW
  obtain ⟨rfl, _⟩ := Exec.det E EW
  exact ⟨u, EU⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
