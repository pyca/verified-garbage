module
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Call
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Fwd

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Inv
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Input
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Out
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Prepare
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Stores
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd2
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Bytes
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecInput
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLoop
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecSpec
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Decode
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncLoop
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncMath
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Encode
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce1Step
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4Step
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
import VerifiedGarbage.Proof.MlKem.AArch64.Decode12
import VerifiedGarbage.Proof.MlKem.AArch64.Encode12
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Fwd
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Gs
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Inv
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.At
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Fwd
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Inv
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Words
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.InvPass1
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.InvPass2
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Pass2
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.PrimCall
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.Rc4.AArch64.Group
import VerifiedGarbage.Proof.Rc4.AArch64.Rotate
import VerifiedGarbage.Proof.Rc4.AArch64.Rows
import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Rc4.Table
import VerifiedGarbage.Proof.Sha3.AArch64.Call
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.TCB.AArch64.Target

/-!
# ML-KEM on AArch64: the 16-bit NTT and its inverse of polynomials stored with 16 bits, inlined

`fwdW` and `invW` (`Impl.MlKem.AArch64.Ntt16.Readonly`) as `Readonly.fwd` and
`Readonly.inv` are used: a contract (`contractW`), the code inlined where its
caller's pointers are (`transformW_call`), and from offsets of `x28`
(`nttAtWithW_ok`, `nttInvAtWithW_ok`). The polynomial and the working space
are 512 bytes each.
-/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.W
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Ntt16
open VG.Proof.MlKem.AArch64.Ntt16.Readonly (TableReady)
open VG.Impl.MlKem.AArch64.Ntt16

def contractW (op : Poly → Poly) (symbol : String) (H : List Nat) : Contract isa where
  pre s := Input s symbol H
  post s t := PolyIsW 16 t.mem (s.gpr .x0) (op (polyAtW 16 s.mem (s.gpr .x0)))
  pub s t := s.sp=t.sp ∧ s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧ s.syms symbol=t.syms symbol

def fwdContractW : Contract isa := contractW ntt "VG_MLKEM_NTT16_ZETAS" tableHalves
def invContractW : Contract isa := contractW nttInv "VG_MLKEM_INTT16_ZETAS" invTableHalves

theorem fwdW_correct (s : State) (h : fwdContractW.pre s) :
    ∃ tr t, Exec isa Impl.MlKem.AArch64.Ntt16.Readonly.fwdW s tr t ∧
      abiPreserved s t ∧ fwdContractW.post s t := by
  obtain ⟨tr,t,he,_,hf⟩ := fwdW_ok s h
  exact ⟨tr,t,he,abi_of rfl (by lit_decide) he (by lit_decide),hf⟩

theorem invW_correct (s : State) (h : invContractW.pre s) :
    ∃ tr t, Exec isa Impl.MlKem.AArch64.Ntt16.Readonly.invW s tr t ∧
      abiPreserved s t ∧ invContractW.post s t := by
  obtain ⟨tr,t,he,_,hf⟩ := invW_ok s h
  exact ⟨tr,t,he,abi_of rfl (by lit_decide) he (by lit_decide),hf⟩

/-- The transform inlined, on the polynomial at `f` with working space at `w`, both of 512
bytes. -/
theorem transformW_call {op : Poly → Poly} {symbol : String} {H : List Nat} {c : Prog isa}
    (hv : ∀ s, (contractW op symbol H).pre s → ∃ tr t, Exec isa c s tr t ∧
      abiPreserved s t ∧ (contractW op symbol H).post s t)
    (hn : c.noCalls=true) {s : State} {f w : Addr} (h0 : s.gpr .x0=f) (h1 : s.gpr .x1=w)
    (hd : (Region.mk f 512).Disjoint ⟨w,512⟩) (hr : ReducedW 16 s.mem f)
    (hw : Covers [⟨f,512⟩,⟨w,512⟩] s.wr) (ht : TableReady s symbol H f w) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f,512⟩,⟨w,512⟩] s s' → PolyIsW 16 s'.mem f (op (polyAtW 16 s.mem f)) → Q s') :
    WP isa c s Q := by
  refine WP.inline (k:=contractW op symbol H) hv (rd:=[⟨s.syms symbol,512⟩])
    (wr:=[⟨f,512⟩,⟨w,512⟩]) ?_ (ht.readable.append_left hw.right) hw ?_ hn
  · refine ⟨⟨?_,?_,?_⟩,?_,?_,?_,?_⟩
    · simp only [fP,sP,fR,sR,State.withRegions_wr,State.withRegions_gpr,h0,h1]
    · simpa only [fP,sP,fR,sR,State.withRegions_gpr,h0,h1] using hd
    · simpa only [fP,State.withRegions_mem,State.callEntry_mem,State.withRegions_gpr,h0] using hr
    · exact ht.table
    · exact Covers.of_mem (fun r h => List.mem_append_left _ h)
    · simp only [fP,fR,State.withRegions_gpr,h0]
      exact ht.output.sub_left (Region.sub_prefix (by decide : 512 ≤ 1024))
    · simp only [sP,sR,State.withRegions_gpr,h1]
      exact ht.scratch.sub_left (Region.sub_prefix (by decide : 512 ≤ 1024))
  · intro s' hrd hwr habi hf _ hpost
    change PolyIsW 16 s'.mem (s.gpr .x0) (op (polyAtW 16 s.mem (s.gpr .x0))) at hpost
    rw [h0] at hpost
    exact hQ s' ⟨fun r hr _ => habi.1 r hr,habi.2.1,hrd,hwr,hf,habi.2.2⟩ hpost

theorem nttAtWithW_ok {s : State} {off ns : Nat} {f w : Addr} {F : Poly}
    (hoff : off<65536) (hns : ns<65536)
    (hf : s.gpr .x28+BitVec.ofNat 64 off=f) (hw : s.gpr .x28+BitVec.ofNat 64 ns=w)
    (hd : (Region.mk f 512).Disjoint ⟨w,512⟩) (hp : PolyIsW 16 s.mem f F)
    (hc : Covers [⟨f,512⟩,⟨w,512⟩] s.wr)
    (ht : TableReady s "VG_MLKEM_NTT16_ZETAS" tableHalves f w) :
    WP isa (Impl.MlKem.AArch64.Ntt16.Readonly.nttAtWithW off ns) s fun t=>
      Kept [⟨f,512⟩,⟨w,512⟩] s t ∧ PolyIsW 16 t.mem f (ntt F) := by
  have prep : WP isa (.block (Impl.MlKem.AArch64.ptrTo .x0 .x28 off ++ Impl.MlKem.AArch64.ptrTo .x1 .x28 ns)) s
      fun z=>Only [.x0,.x1] s z ∧ z.gpr .x0=f ∧ z.gpr .x1=w := by
    refine wp_ptrTo (by decide) hoff fun a ha ea=>wp_ptrTo' (by decide) hns fun z hz ez=>?_
    exact ⟨(ha.trans hz).mono (by simp),by rw [hz.get .x0 (by decide),ea]; exact hf,
      by rw [ez,ha.get .x28 (by decide)]; exact hw⟩
  refine WP.seq (WP.mono_syms prep fun z ⟨oz,z0,z1⟩ zs=>?_)
  have table : TableReady z "VG_MLKEM_NTT16_ZETAS" tableHalves f w :=
    ⟨by simpa only [zs,oz.mem] using ht.table,
      by simpa only [zs,oz.rd,oz.wr] using ht.readable,
      by simpa only [zs] using ht.output,by simpa only [zs] using ht.scratch⟩
  exact transformW_call fwdW_correct (by decide +kernel) z0 z1 hd (by rw [oz.mem]; exact hp.1)
    (by rw [oz.wr]; exact hc) table fun t kt pt=>
    ⟨(Kept.of_keep oz.keep oz.mem (by decide)).trans kt,by simpa only [oz.mem,hp.2] using pt⟩

theorem nttInvAtWithW_ok {s : State} {off ns : Nat} {f w : Addr} {F : Poly}
    (hoff : off<65536) (hns : ns<65536)
    (hf : s.gpr .x28+BitVec.ofNat 64 off=f) (hw : s.gpr .x28+BitVec.ofNat 64 ns=w)
    (hd : (Region.mk f 512).Disjoint ⟨w,512⟩) (hp : PolyIsW 16 s.mem f F)
    (hc : Covers [⟨f,512⟩,⟨w,512⟩] s.wr)
    (ht : TableReady s "VG_MLKEM_INTT16_ZETAS" invTableHalves f w) :
    WP isa (Impl.MlKem.AArch64.Ntt16.Readonly.nttInvAtWithW off ns) s fun t=>
      Kept [⟨f,512⟩,⟨w,512⟩] s t ∧ PolyIsW 16 t.mem f (nttInv F) := by
  have prep : WP isa (.block (Impl.MlKem.AArch64.ptrTo .x0 .x28 off ++ Impl.MlKem.AArch64.ptrTo .x1 .x28 ns)) s
      fun z=>Only [.x0,.x1] s z ∧ z.gpr .x0=f ∧ z.gpr .x1=w := by
    refine wp_ptrTo (by decide) hoff fun a ha ea=>wp_ptrTo' (by decide) hns fun z hz ez=>?_
    exact ⟨(ha.trans hz).mono (by simp),by rw [hz.get .x0 (by decide),ea]; exact hf,
      by rw [ez,ha.get .x28 (by decide)]; exact hw⟩
  refine WP.seq (WP.mono_syms prep fun z ⟨oz,z0,z1⟩ zs=>?_)
  have table : TableReady z "VG_MLKEM_INTT16_ZETAS" invTableHalves f w :=
    ⟨by simpa only [zs,oz.mem] using ht.table,
      by simpa only [zs,oz.rd,oz.wr] using ht.readable,
      by simpa only [zs] using ht.output,by simpa only [zs] using ht.scratch⟩
  exact transformW_call invW_correct (by decide +kernel) z0 z1 hd (by rw [oz.mem]; exact hp.1)
    (by rw [oz.wr]; exact hc) table fun t kt pt=>
    ⟨(Kept.of_keep oz.keep oz.mem (by decide)).trans kt,by simpa only [oz.mem,hp.2] using pt⟩

end VG.Proof.MlKem.AArch64.Ntt16.W
