module

public import VerifiedGarbage.Proof.Dsa.X86_64.CallHeadCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain

/-! # Constant time of the complete parent-to-child scalar addition -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def CallAddPre (a b output : Operand) (p : Call3ProductPublic) (s : State) : Prop :=
  Call3Pre a b output p.toCall3Public s ∧ p.x.o = qWorkspace ∧
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem p.base p.baseLen) < p.modulus ∧
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem p.bytes.ptr p.bytes.len) < p.modulus

theorem callAddHead_ok {p : Call3ProductPublic} {s : State} {a b output : Operand}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    (h : CallAddPre a b output p s) :
    WP isa (.block (callHead a b output qWorkspace)) s (AddFinishPre p.finish) := by
  obtain ⟨h, heq, hbr, her⟩ := h
  rw [← heq]
  refine WP.mono (callHead_run ha hb ho h) fun t ⟨ht, hf, hk⟩ => ?_
  obtain ⟨_, _, ⟨ba, bb, has, hbs, hbl, hel⟩, hp, hep, _⟩ := h
  have hsa : Src s p.x.B p.x.Z p.base ba := hp ▸ has.source
  have hsb : Src s p.x.B p.x.Z p.bytes.ptr bb := hep ▸ hbs.source
  have hta := arguments_source hf hk (Nat.le_trans (by decide) p.extent) hsa
  have htb := arguments_source hf hk (Nat.le_trans (by decide) p.extent) hsb
  refine ⟨ht, ?_, ?_⟩
  · change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem p.base p.baseLen) < p.modulus
    rw [← hbl, sourceBytes_eq hta]
    rw [← hbl, sourceBytes_eq hsa] at hbr
    exact hbr
  · change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem p.bytes.ptr p.bytes.len) < p.modulus
    rw [← hel, sourceBytes_eq htb]
    rw [← hel, sourceBytes_eq hsb] at her
    exact her

theorem coreAdd_ct {a b output : Operand}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (callHead a b output qWorkspace)) hc).isSome = true) :
    RelCT isa (Two (CallAddPre a b output)) (Core.add a b output) (fun _ _ => True) := by
  change RelCT isa _ (.seq (.block (callHead a b output qWorkspace))
    (seqs ([Arithmetic.load aX arg argLen, Arithmetic.load aXm arg2 arg2Len,
      Crt.addMod aY aX aXm] ++ Core.finish))) _
  refine RelCT.seq (two_post (Ψ := fun p s => AddFinishPre p.finish s)
    (two_map Call3ProductPublic.toCall3Public (fun _ _ h => h.1) (callHead_ct hT))
    (fun _ _ h => callAddHead_ok ha hb ho h)) ?_
  exact RelCT.seqs_append (by simp) (by simp [Core.finish])
    (two_map Call3ProductPublic.finish (fun _ _ h => h) addFinish_ct)

end VG.Proof.Dsa.X86_64
