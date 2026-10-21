module
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Index
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Mask
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Parse

import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Accept
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # Composition of vector parsing, acceptance, horizontal sum and lookup index -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64

def probeCode : List Instr := Impl.MlKem.AArch64.Rej8.parse ++
  Impl.MlKem.AArch64.Rej8.accept ++ sumCode ++ indexCode

structure Constants (s : State) : Prop where
  index : s.v .v16=gatherIndex
  mask : s.v .v17=lowMask
  q : ∀ i<8,vhalf (s.v .v19) i=3329
  weights : ∀ i<8,vhalf (s.v .v20) i=BitVec.ofNat 16 (256+2^i)
  zero : ∀ i<8,vhalf (s.v .v21) i=0

def candidatesAt (s : State) : BitVec 128 := parsed (s.mem.read (s.gpr .x2) 16)
def maskAt (s : State) : Nat := acceptanceMask (candidatesAt s)

structure ProbePost (s t : State) : Prop where
  keep : Keep [.x6,.x7] s t
  mem : t.mem=s.mem
  other : ∀ r, r ∉ [.v0,.v1,.v2] → t.v r=s.v r
  values : t.v .v0=candidatesAt s
  index : t.gpr .x7=s.gpr .x16+BitVec.ofNat 64 (16*maskAt s)
  count : ((t.gpr .x6 >>> 8) &&& 15).toNat=(Impl.MlKem.AArch64.Rej8.acceptedLanes (maskAt s)).length

theorem probe_ok (s : State) (hc : Constants s)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x2) 16) :
    WP isa (.block probeCode) s (fun t => ProbePost s t) := by
  rw [probeCode,WP.block_append_iff,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (parse_ok s hr hc.index hc.mask) fun a ⟨ha,hav⟩ => ?_
  refine WP.mono (accept_ok a (fun i hi => by rw [ha.get .v19]; exact hc.q i hi)
    (fun i hi => by rw [ha.get .v20]; exact hc.weights i hi)
    (fun i hi => by rw [hav,parsed_candidate _ _ hi]; exact candidate_lt _ _ _)) fun b ⟨hb,hbv⟩ => ?_
  refine WP.mono (sumCode_ok b) fun c ⟨hc0,hcv⟩ => ?_
  have hmask : vhalf (c.v .v1) 0 = BitVec.ofNat 16 (packedCount (maskAt s)) := by
    rw [hcv,accepted_sum hbv,hav]
    rfl
  refine WP.mono (index_ok c (acceptanceMask_bound _) hmask) fun t ⟨ht,htv,h6,h7⟩ => ?_
  have hall := ((ha.trans hb).trans hc0).mono (rs' := [.v0,.v1,.v2]) (by decide)
  refine ⟨(hall.keep.trans ht.keep).mono (by decide),ht.mem.trans hall.mem,?_,?_,?_,?_⟩
  · intro r hr0
    rw [htv,hall.get r hr0]
  · rw [htv,hc0.get .v0,hb.get .v0,hav]
    rfl
  · rw [h7,hall.gpr]
    rfl
  · rw [h6]
    exact word_count (acceptanceMask_bound _) hmask

end VG.Proof.MlKem.AArch64.Rej8
