module
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputPlan
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryState

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryReady
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Dispatch
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Generate

/-! # The initialized and size-dispatched ABI body implements parameter generation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.X86_64

theorem entryBody_ok (H : GenerationHashes) (M : Mont) (Sq : MontS) (K : Kernel)
    {p : GenerationContext} {s : State} (h : EntryState p s) (o : OutputPlan p)
    (hw : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ s.wr)
    (seedLength : p.seeds.bytes.length % p.geo.qLen = 0)
    (hLength : p.hs.bytes.length % p.geo.pLen = 0) :
    WP isa (Impl.Dsa.X86_64.Generation.entryBody H.sha1 H.sha256 Sq.mm M.mm K.run) s fun t =>
      let result := Spec.Dsa.generateParametersBytes p.geo.pLen p.geo.qLen p.seeds.bytes p.hs.bytes p.rand.bytes
      t.gpr .rax = BitVec.ofNat 64 (Spec.Dsa.signStatus result) ∧
      Spec.Rsa.bytesAt t.mem (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) =
        result.getD (List.replicate (2 * p.geo.pLen + p.geo.qLen) 0) ∧
      Frame (p.changed ++ [⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩]) s.mem t.mem ∧
      t.gpr .rsp = s.gpr .rsp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Impl.Dsa.X86_64.Generation.entryBody
  refine WP.seq (WP.mono (entryReady_ok h) fun u ⟨W, mu, h16, fu, ku⟩ => ?_)
  apply dispatch_ok H.sha1 H.sha256 Sq.mm M.mm K.run mu
  intro v mv hm kv
  refine WP.mono (generate_ok H M Sq K mv h16 o (by rw [kv.2.2, ku.2.2]; exact hw) seedLength hLength)
    fun t ⟨status, bytes, ft, rsp, rd, wr⟩ => ?_
  refine ⟨status, bytes, ?_, ?_, rd.trans (kv.2.1.trans ku.2.1), wr.trans (kv.2.2.trans ku.2.2)⟩
  · have fv : Frame p.changed s.mem v.mem := by rw [hm]; exact fu
    exact (fv.mono (by intro r hr; exact List.mem_append_left _ hr)).trans ft
  · exact rsp.trans ((kv.gpr (by decide)).trans (ku.gpr (by decide)))

end VG.Proof.Dsa.X86_64.Generation
