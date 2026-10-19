module
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateStores
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateStores
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant time of full-width candidate and exponent stores -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

structure StorePublic where
  B : Addr
  Z : Nat
  w : Nat
  out : Addr

structure StoreState (ptr : Nat) (p : StorePublic) (s : State) : Prop where
  ws : Ws s p.B p.Z p.w
  pointer : word s.mem p.B (8 * ptr) = p.out
  length : word s.mem p.B 136 = BitVec.ofNat 64 (8 * p.w)
  mask : word s.mem p.B (8 * Public.sMask) = mask true
  write : ∀ i < 8 * p.w, InRegions s.wr (off p.out i) 1
  outside : ∀ i < 8 * p.w, p.Z ≤ ofs p.B (off p.out i)

def storePublicRegs (a : Nat) (p : StorePublic) : Reg → BitVec 64
  | .rdi => p.B
  | .rbx => off p.B (slot p.w a)
  | .rsi => p.out
  | .rcx => BitVec.ofNat 64 (8 * p.w)
  | _ => 0

theorem storeCandidate_ct {a ptr : Nat} (ha : a < 16) (hp : ptr < 32)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base a .rbx ++
      ([.mov .rsi (.mem (hdr ptr)), .mov .rcx (.mem (hdr 17)),
        .mov .r15 (.mem (hdr Public.sMask))] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (StoreState ptr)) (seqs (storeA a ptr 17 Public.sMask)) (fun _ _ => True) := by
  have ct := pin_ct (c₂ := storeBE) (Φ := StoreState ptr) (Ψ := fun _ _ => True)
    [.rdi] [.rdi, .rbx, .rsi, .rcx] (storePublicRegs a) (by
      intro p s t hs ht r hr
      simp only [List.mem_singleton] at hr
      subst r; exact hs.ws.rdi.trans ht.ws.rdi.symm) ht
    (fun p s h => WP.mono (storeBlk_ok h.ws hp (by decide : 17 < 32) h.pointer h.length)
      fun t ⟨hbx, hsi, hcx, hdi⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact hbx
        · exact hsi
        · exact hcx)
    (by taint_decide)
    (fun _ _ h => WP.mono (storeCandidateArray_ok h.ws ha hp h.pointer h.length h.mask h.write h.outside)
      (fun _ _ => True.intro))
  exact ct.mono (fun _ _ h => h) (fun _ _ _ => True.intro)

end VG.Proof.Dsa.X86_64.Generation
