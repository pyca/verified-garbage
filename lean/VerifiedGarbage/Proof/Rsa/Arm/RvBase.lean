module

public import VerifiedGarbage.Impl.Rsa.Arm.Recover
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # `vg_rsa_recover_primes` on ARMv7: the public parameters and the base of every stage

`RP`: what two runs share (the stack pointer in the frame, the pointers,
the lengths, `n`, `e` and the number of candidates tried, which
`vg_rsa_recover_primes`' stages take as public, `Tries`). `In P σ`: the
state `σ` the body starts from, after the push of the frame and the entry,
with the regions widened by Montgomery multiplication's working space
(`rM`). `Bs P σ s`: what every later state keeps of `σ`: the stack pointer,
the regions, and memory outside the working space and frame word 0.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

structure RP where
  sp : BitVec 32
  pP : BitVec 32
  qP : BitVec 32
  nP : BitVec 32
  eP : BitVec 32
  dP : BitVec 32
  B : BitVec 32
  K : Nat
  el : Nat
  dl : Nat
  SL : Nat
  nB : List Byte
  eB : List Byte
  nt : Nat

namespace RP

/-- The 64-bit words of Montgomery multiplication, and the 32-bit words of
the key working space with `w` and with `W`. -/
abbrev w6 (P : RP) : Nat := (P.K + 7) / 8
abbrev w (P : RP) : Nat := 2 * P.w6 + 2
abbrev W (P : RP) : Nat := 2 * P.w + 2
abbrev Z (P : RP) : Nat := P.SL * 8
/-- Montgomery multiplication's working space: its `u64`s, its offset and base. -/
abbrev lenM (P : RP) : Nat := 8 * P.w6 + 48
abbrev oM (P : RP) : Nat := arr P.w mBase - 256
abbrev M0 (P : RP) : BitVec 32 := P.B + BitVec.ofNat 32 P.oM
/-- The bits of `d e`. -/
abbrev c (P : RP) : Nat := 8 * (P.dl + P.el)

abbrev rS (P : RP) : Region := ⟨State.addr P.B, P.Z⟩
abbrev rM (P : RP) : Region := ⟨State.addr P.M0, 8 * P.lenM⟩
abbrev rP (P : RP) : Region := ⟨State.addr P.pP, P.K⟩
abbrev rQ (P : RP) : Region := ⟨State.addr P.qP, P.K⟩
abbrev rN (P : RP) : Region := ⟨State.addr P.nP, P.K⟩
abbrev rE (P : RP) : Region := ⟨State.addr P.eP, P.el⟩
abbrev rD (P : RP) : Region := ⟨State.addr P.dP, P.dl⟩
/-- The frame and the stack arguments. -/
abbrev rF (P : RP) : Region := ⟨State.addr P.sp, 88⟩
/-- The frame alone. -/
abbrev rFr (P : RP) : Region := ⟨State.addr P.sp, 56⟩
/-- Frame word 0. -/
abbrev r0F (P : RP) : Region := ⟨State.addr P.sp, 4⟩

abbrev n (P : RP) : Nat := Spec.Rsa.os2ip P.nB
abbrev e (P : RP) : Nat := Spec.Rsa.os2ip P.eB

end RP

/-- The stack word at byte `o` of the frame. -/
abbrev fw (m : Mem) (P : RP) (o : Nat) : BitVec 32 := m.readW (off (State.addr P.sp) o) 32

/-- `d`. -/
abbrev dB (P : RP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dP) P.dl
abbrev dv (P : RP) (σ : State) : Nat := Spec.Rsa.os2ip (dB P σ)

structure In (P : RP) (σ : State) : Prop where
  sp : σ.sp = P.sp
  spFit : P.sp.toNat + 88 ≤ 2 ^ 32
  wr : σ.wr = [⟨State.addr P.sp, 56⟩, P.rP, P.rQ, P.rS, P.rM]
  rdN : InRegions (σ.rd ++ σ.wr) (State.addr P.nP) P.K
  rdE : InRegions (σ.rd ++ σ.wr) (State.addr P.eP) P.el
  rdD : InRegions (σ.rd ++ σ.wr) (State.addr P.dP) P.dl
  rdA : InRegions (σ.rd ++ σ.wr) (off (State.addr P.sp) 56) 32
  k1 : 64 ≤ P.K
  k2 : P.K ≤ 1024
  el1 : 1 ≤ P.el
  el2 : P.el ≤ P.K
  dl1 : 1 ≤ P.dl
  dl2 : P.dl ≤ P.K
  scr : Spec.Rsa.scratchWords P.K ≤ P.SL
  fP : P.pP.toNat + P.K ≤ 2 ^ 32
  fQ : P.qP.toNat + P.K ≤ 2 ^ 32
  fN : P.nP.toNat + P.K ≤ 2 ^ 32
  fE : P.eP.toNat + P.el ≤ 2 ^ 32
  fD : P.dP.toNat + P.dl ≤ 2 ^ 32
  fS : P.B.toNat + P.Z ≤ 2 ^ 32
  sP : P.rS.Disjoint P.rP
  sQ : P.rS.Disjoint P.rQ
  sN : P.rS.Disjoint P.rN
  sE : P.rS.Disjoint P.rE
  sD : P.rS.Disjoint P.rD
  sF : P.rS.Disjoint P.rF
  pQ : P.rP.Disjoint P.rQ
  pN : P.rP.Disjoint P.rN
  pE : P.rP.Disjoint P.rE
  pD : P.rP.Disjoint P.rD
  pF : P.rP.Disjoint P.rF
  qN : P.rQ.Disjoint P.rN
  qE : P.rQ.Disjoint P.rE
  qD : P.rQ.Disjoint P.rD
  qF : P.rQ.Disjoint P.rF
  nF : P.rN.Disjoint P.rFr
  eF : P.rE.Disjoint P.rFr
  dF : P.rD.Disjoint P.rFr
  wP : fw σ.mem P oP = P.pP
  wQ : fw σ.mem P oQ = P.qP
  aN : fw σ.mem P aoN = P.nP
  aK : fw σ.mem P aoK = BitVec.ofNat 32 P.K
  aE : fw σ.mem P aoE = P.eP
  aEl : fw σ.mem P aoEl = BitVec.ofNat 32 P.el
  aD : fw σ.mem P aoD = P.dP
  aDl : fw σ.mem P aoDl = BitVec.ofNat 32 P.dl
  aS : fw σ.mem P aoS = P.B
  nB : Spec.Rsa.bytesAt σ.mem (State.addr P.nP) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (State.addr P.eP) P.el = P.eB

/-- The number of candidates `vg_rsa_recover_primes` tries for `σ`'s `d`,
which its stages take as public. -/
abbrev Tries (P : RP) (σ : State) : Prop := (Spec.Rsa.primesKey P.nB P.eB (dB P σ)).2 = P.nt

/-- What every state of the body keeps of `σ`. -/
structure Bs (P : RP) (σ s : State) : Prop where
  pre : In P σ
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  frame : Frame [P.rS, P.r0F] σ.mem s.mem

/-! ## Sizes -/

structure Sizes (P : RP) : Prop where
  w6a : 8 ≤ P.w6
  w6b : P.w6 ≤ 128
  wle : P.w ≤ 258
  Wle : P.W ≤ 518
  kw : P.K ≤ 4 * P.w - 8
  fits : arr P.w nArr ≤ P.Z
  hdrM : arr P.w 16 ≤ P.oM
  endM : P.oM + 8 * P.lenM = arr P.w (mBase + 8)
  sw : S P.w = 8 * (P.w6 + 2)
  zle : P.Z ≤ 2 ^ 32

theorem In.sizes {P : RP} {σ : State} (h : In P σ) : Sizes P := by
  have k1 := h.k1; have k2 := h.k2; have scr := h.scr; have fS := h.fS
  simp only [Spec.Rsa.scratchWords] at scr
  simp only [RP.Z] at fS
  refine ⟨show 8 ≤ (P.K + 7) / 8 by omega, show (P.K + 7) / 8 ≤ 128 by omega,
    show 2 * ((P.K + 7) / 8) + 2 ≤ 258 by omega, show 2 * (2 * ((P.K + 7) / 8) + 2) + 2 ≤ 518 by omega,
    show P.K ≤ 4 * (2 * ((P.K + 7) / 8) + 2) - 8 by omega, ?_, ?_, ?_, ?_, show P.SL * 8 ≤ 2 ^ 32 by omega⟩
  · simp only [arr, S, hdr, nArr, RP.w, RP.w6, RP.Z]; omega
  · simp only [RP.oM, arr, S, hdr, mBase, RP.w, RP.w6]; omega
  · simp only [RP.oM, RP.lenM, arr, S, hdr, mBase, RP.w, RP.w6]; omega
  · simp only [S, RP.w]; omega

/-! ## Steps -/

theorem Bs.of_rest {P : RP} {σ s t : State} (h : Bs P σ s) {rs : List Reg} (r : Rest rs s t)
    (m : t.mem = s.mem) : Bs P σ t :=
  ⟨h.pre, r.sp.trans h.sp, r.rd.trans h.rd, r.wr.trans h.wr, m ▸ h.frame⟩

/-- Memory that changed only within the working space. -/
theorem Bs.of_frame {P : RP} {σ s t : State} (h : Bs P σ s) (f : Frame [P.rS] s.mem t.mem)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Bs P σ t :=
  ⟨h.pre, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr,
    h.frame.trans (f.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])⟩

end VG.Proof.Rsa.Arm.Recover

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Recover VG.Impl.Rsa.Arm.Keys

/-- A step that writes arrays and header words of the key working space. -/
theorem Keep.frameS {P : RP} {v : Nat} {js ds : List Nat} {m m' : Mem}
    (k : Keep P.B v js ds m m') (hj : ∀ j ∈ js, arr v j + S v ≤ P.Z) (hd : ∀ d ∈ ds, d + 4 ≤ hdr)
    (hz : hdr ≤ P.Z) : Frame [P.rS] m m' := by
  intro x hx
  have hz' : ¬ P.rS.Contains x 1 := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hz'
  exact k.out (Z := P.Z) hj (fun d hd' => Nat.le_trans (hd d hd') hz) (by simp only [ofs]; omega)

end VG.Proof.Rsa.Arm.Keys
