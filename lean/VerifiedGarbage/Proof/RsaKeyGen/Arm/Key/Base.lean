module

public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Key
public import VerifiedGarbage.Proof.Rsa.Arm.KeyArrs
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP
public import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # An RSA key on ARMv7: the public parameters and the stages

`KP`: what two runs share (the frame, the pointers, the lengths, `e` and the
status returned). `In P σ`: the state `σ` the body starts from, after the
push, with the regions narrowed to the frame, the outputs and the working
space. `KS P σ A live V ls s`: a stage of the body before the outputs are
written: what it keeps of `σ` (the stack pointer, the regions, and all of
memory but the working space), `W` in the division's header, the arrays
`live` holding `A` and the header words `ls` holding `V`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

structure KP where
  sp : BitVec 32
  nP : BitVec 32
  dP : BitVec 32
  pP : BitVec 32
  qP : BitVec 32
  dpP : BitVec 32
  dqP : BitVec 32
  qiP : BitVec 32
  eP : BitVec 32
  B : BitVec 32
  K : Nat
  el : Nat
  SL : Nat
  eB : List Byte
  st : Nat

namespace KP

/-- The 32-bit words of the working space's numbers, and its size. -/
abbrev W (P : KP) : Nat := P.K / 2 + 4
abbrev Z (P : KP) : Nat := P.SL * 8

abbrev rS (P : KP) : Region := ⟨State.addr P.B, P.Z⟩
abbrev rN (P : KP) : Region := ⟨State.addr P.nP, 2 * P.K⟩
abbrev rD (P : KP) : Region := ⟨State.addr P.dP, 2 * P.K⟩
abbrev rP (P : KP) : Region := ⟨State.addr P.pP, P.K⟩
abbrev rQ (P : KP) : Region := ⟨State.addr P.qP, P.K⟩
abbrev rDp (P : KP) : Region := ⟨State.addr P.dpP, P.K⟩
abbrev rDq (P : KP) : Region := ⟨State.addr P.dqP, P.K⟩
abbrev rQi (P : KP) : Region := ⟨State.addr P.qiP, P.K⟩
abbrev rE (P : KP) : Region := ⟨State.addr P.eP, P.el⟩
/-- The frame alone, and with the stack arguments. -/
abbrev rFr (P : KP) : Region := ⟨State.addr P.sp, 56⟩
abbrev rF (P : KP) : Region := ⟨State.addr P.sp, 112⟩

/-- The outputs. -/
abbrev outs (P : KP) : List Region := [P.rN, P.rD, P.rP, P.rQ, P.rDp, P.rDq, P.rQi]

abbrev e (P : KP) : Nat := Spec.Rsa.os2ip P.eB

end KP

/-- The frame word at byte `o`. -/
abbrev fw (m : Mem) (P : KP) (o : Nat) : BitVec 32 := m.readW (off (State.addr P.sp) o) 32

/-- The primes given. -/
abbrev pB (P : KP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.pP) P.K
abbrev qB (P : KP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.qP) P.K

/-- The result. -/
abbrev res (P : KP) (σ : State) : Except Spec.RsaKeyGen.Failure (List (List Byte)) ⊕ Unit :=
  Spec.RsaKeyGen.keyOp P.K P.eB (pB P σ) (qB P σ)

structure In (P : KP) (σ : State) : Prop where
  sp : σ.sp = P.sp
  spFit : P.sp.toNat + 112 ≤ 2 ^ 32
  wr : σ.wr = [P.rFr, P.rN, P.rD, P.rP, P.rQ, P.rDp, P.rDq, P.rQi, P.rS]
  rdE : InRegions (σ.rd ++ σ.wr) (State.addr P.eP) P.el
  rdA : InRegions (σ.rd ++ σ.wr) (off (State.addr P.sp) 56) 56
  k1 : 32 ≤ P.K
  k2 : P.K ≤ 512
  k8 : P.K % 8 = 0
  el1 : 1 ≤ P.el
  el2 : P.el ≤ 8
  scr : Spec.Rsa.scratchWords (2 * P.K) ≤ P.SL
  fN : P.nP.toNat + 2 * P.K ≤ 2 ^ 32
  fD : P.dP.toNat + 2 * P.K ≤ 2 ^ 32
  fP : P.pP.toNat + P.K ≤ 2 ^ 32
  fQ : P.qP.toNat + P.K ≤ 2 ^ 32
  fDp : P.dpP.toNat + P.K ≤ 2 ^ 32
  fDq : P.dqP.toNat + P.K ≤ 2 ^ 32
  fQi : P.qiP.toNat + P.K ≤ 2 ^ 32
  fE : P.eP.toNat + P.el ≤ 2 ^ 32
  fS : P.B.toNat + P.Z ≤ 2 ^ 32
  sN : P.rS.Disjoint P.rN
  sD : P.rS.Disjoint P.rD
  sP : P.rS.Disjoint P.rP
  sQ : P.rS.Disjoint P.rQ
  sDp : P.rS.Disjoint P.rDp
  sDq : P.rS.Disjoint P.rDq
  sQi : P.rS.Disjoint P.rQi
  sE : P.rS.Disjoint P.rE
  sF : P.rS.Disjoint P.rF
  nD : P.rN.Disjoint P.rD
  nP : P.rN.Disjoint P.rP
  nQ : P.rN.Disjoint P.rQ
  nDp : P.rN.Disjoint P.rDp
  nDq : P.rN.Disjoint P.rDq
  nQi : P.rN.Disjoint P.rQi
  dP : P.rD.Disjoint P.rP
  dQ : P.rD.Disjoint P.rQ
  dDp : P.rD.Disjoint P.rDp
  dDq : P.rD.Disjoint P.rDq
  dQi : P.rD.Disjoint P.rQi
  pQ : P.rP.Disjoint P.rQ
  pDp : P.rP.Disjoint P.rDp
  pDq : P.rP.Disjoint P.rDq
  pQi : P.rP.Disjoint P.rQi
  qDp : P.rQ.Disjoint P.rDp
  qDq : P.rQ.Disjoint P.rDq
  qQi : P.rQ.Disjoint P.rQi
  dpDq : P.rDp.Disjoint P.rDq
  dpQi : P.rDp.Disjoint P.rQi
  dqQi : P.rDq.Disjoint P.rQi
  nF : P.rN.Disjoint P.rF
  dF : P.rD.Disjoint P.rF
  pF : P.rP.Disjoint P.rF
  qF : P.rQ.Disjoint P.rF
  dpF : P.rDp.Disjoint P.rF
  dqF : P.rDq.Disjoint P.rF
  qiF : P.rQi.Disjoint P.rF
  eF : P.rE.Disjoint P.rFr
  wN : fw σ.mem P aoN = P.nP
  wNl : fw σ.mem P aoNl = BitVec.ofNat 32 (2 * P.K)
  wD : fw σ.mem P aoD = P.dP
  aP : fw σ.mem P aoP = P.pP
  aPl : fw σ.mem P aoPl = BitVec.ofNat 32 P.K
  aQ : fw σ.mem P aoQ = P.qP
  aQl : fw σ.mem P (aoQ + 4) = BitVec.ofNat 32 P.K
  aDp : fw σ.mem P aoDp = P.dpP
  aDq : fw σ.mem P aoDq = P.dqP
  aQi : fw σ.mem P aoQi = P.qiP
  aE : fw σ.mem P aoE = P.eP
  aEl : fw σ.mem P aoEl = BitVec.ofNat 32 P.el
  aS : fw σ.mem P aoS = P.B
  eB : Spec.Rsa.bytesAt σ.mem (State.addr P.eP) P.el = P.eB
  st : Spec.RsaKeyGen.keyStatus (res P σ) = P.st

/-! ## Sizes -/

section
variable {P : KP} {σ : State}

theorem In.W_eq (h : In P σ) : 2 * (P.W - 4) = P.K := by have := h.k8; simp only [KP.W]; omega

theorem In.wle (h : In P σ) : P.W ≤ 260 := by have := h.k2; simp only [KP.W]; omega

theorem In.wge (h : In P σ) : 20 ≤ P.W := by have := h.k1; simp only [KP.W]; omega

theorem In.fits (h : In P σ) : arr P.W nArr ≤ P.Z := by
  have := h.scr; have := h.k1; have := h.k2
  simp only [Spec.Rsa.scratchWords] at *
  simp only [arr, S, hdr, nArr, KP.W, KP.Z]; omega

theorem In.Z_le (h : In P σ) : P.Z ≤ 2 ^ 32 := by have := h.fS; omega

theorem In.hdr_Z (h : In P σ) : hdr ≤ P.Z := Nat.le_trans (Nat.le_add_right _ _) h.fits

theorem In.fitZ (h : In P σ) {j : Nat} (hj : j < nArr) : arr P.W j + S P.W ≤ P.Z :=
  Nat.le_trans (arr_end hj) h.fits

theorem In.fit (h : In P σ) {j : Nat} (hj : j < nArr) : arr P.W j + S P.W ≤ 2 ^ 64 := by
  have := h.fitZ hj; have := h.Z_le; omega

theorem In.rS_mem (h : In P σ) : P.rS ∈ σ.wr := by rw [h.wr]; simp

end

/-! ## Stages -/

/-- The header words of the stages: apart from `W` (byte 16). -/
abbrev SlotOk (d : Nat) : Prop := d + 4 ≤ hdr ∧ (d + 4 ≤ 16 ∨ 20 ≤ d) ∧ d % 4 = 0

/-- The header words a stage holds: past the division's. -/
abbrev LsOk (d : Nat) : Prop := d + 4 ≤ hdr ∧ 20 ≤ d ∧ d % 4 = 0

theorem LsOk.sep {d e : Nat} (hd : LsOk d) (he : SlotOk e) (h : d ≠ e) : d + 4 ≤ e ∨ e + 4 ≤ d := by
  omega

structure KS (P : KP) (σ : State) (A : Nat → Nat) (live : List Nat) (V : Nat → Nat) (ls : List Nat)
    (s : State) : Prop where
  pre : In P σ
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  frame : Frame [P.rS] σ.mem s.mem
  cnt : slot s.mem P.B 16 = P.W
  arrs : Arrs s.mem P.B P.W A live
  sl : ∀ d ∈ ls, slot s.mem P.B d = V d
  live_lt : ∀ j ∈ live, j < nArr
  ls_ok : ∀ d ∈ ls, LsOk d

section
variable {P : KP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- The working space's context. -/
theorem KS.ws (h : KS P σ A live V ls s) (r7 : s.gpr .r7 = BitVec.ofNat 32 (S P.W)) (r8 : s.gpr .r8 = P.B)
    (r9 : s.gpr .r9 = BitVec.ofNat 32 P.W) : Ws s P.B P.Z P.W nArr :=
  ⟨h.pre.fS, by rw [h.wr]; exact h.pre.rS_mem, h.pre.fits, by have := h.pre.wge; omega,
    by have := h.pre.wle; omega, r7, r8, r9⟩

/-- The same memory, other registers. -/
theorem KS.of_rest (h : KS P σ A live V ls s) {rs : List Reg} (r : Rest rs s t) (m : t.mem = s.mem) :
    KS P σ A live V ls t :=
  ⟨h.pre, r.sp.trans h.sp, r.rd.trans h.rd, r.wr.trans h.wr, m ▸ h.frame, m ▸ h.cnt, m ▸ h.arrs, m ▸ h.sl,
    h.live_lt, h.ls_ok⟩

theorem KS.mono (h : KS P σ A live V ls s) {A' : Nat → Nat} {live' : List Nat} {V' : Nat → Nat}
    {ls' : List Nat} (hl : ∀ j ∈ live', j ∈ live ∧ A j = A' j) (hls : ∀ d ∈ ls', d ∈ ls ∧ V d = V' d) :
    KS P σ A' live' V' ls' s :=
  ⟨h.pre, h.sp, h.rd, h.wr, h.frame, h.cnt, fun j hj => (h.arrs j (hl j hj).1).trans (hl j hj).2,
    fun d hd => (h.sl d (hls d hd).1).trans (hls d hd).2, fun j hj => h.live_lt j (hl j hj).1,
    fun d hd => h.ls_ok d (hls d hd).1⟩

/-- Memory that changed only within the working space. -/
theorem keep_frameK {v : Nat} {js ds : List Nat} {m m' : Mem}
    (k : Keep P.B v js ds m m') (hj : ∀ j ∈ js, arr v j + S v ≤ P.Z) (hd : ∀ d ∈ ds, d + 4 ≤ hdr)
    (hz : hdr ≤ P.Z) : Frame [P.rS] m m' := by
  intro x hx
  have hz' : ¬ P.rS.Contains x 1 := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hz'
  exact k.out (Z := P.Z) hj (fun d hd' => Nat.le_trans (hd d hd') hz) (by simp only [ofs]; omega)

/-- A step that writes the arrays `js` and the header words `ds`. -/
theorem KS.core {js ds : List Nat} (h : KS P σ A live V ls s) (k : Keep P.B P.W js ds s.mem t.mem)
    (hjs : ∀ j ∈ js, j < nArr) (hds : ∀ d ∈ ds, SlotOk d) (sp : t.sp = s.sp) (rd : t.rd = s.rd)
    (wr : t.wr = s.wr) {A' : Nat → Nat} {live' : List Nat} {V' : Nat → Nat} {ls' : List Nat}
    (ha : Arrs t.mem P.B P.W A' live') (hsl : ∀ d ∈ ls', slot t.mem P.B d = V' d)
    (hl : ∀ j ∈ live', j < nArr) (hls : ∀ d ∈ ls', LsOk d) :
    KS P σ A' live' V' ls' t := by
  have pre := h.pre
  refine ⟨pre, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr,
    h.frame.trans (keep_frameK k (fun j hj => pre.fitZ (hjs j hj)) (fun d hd => (hds d hd).1) pre.hdr_Z), ?_,
    ha, hsl, hl, hls⟩
  rw [k.slot (e := 16) (by decide) fun d hd => by have := (hds d hd).2.1; omega]
  exact h.cnt

/-- The arrays a step does not write. -/
theorem KS.arrs_keep {js ds : List Nat} (h : KS P σ A live V ls s) (k : Keep P.B P.W js ds s.mem t.mem)
    (hl : ∀ j ∈ live, j ∉ js) (hds : ∀ d ∈ ds, SlotOk d) : Arrs t.mem P.B P.W A live := by
  intro j hj
  rw [k.num (fun i hi e => hl j hj (by subst e; exact hi)) (fun d hd => (hds d hd).1) (h.pre.fit (h.live_lt j hj))]
  exact h.arrs j hj

/-- The header words a step does not write. -/
theorem KS.sl_keep {js ds : List Nat} (h : KS P σ A live V ls s) (k : Keep P.B P.W js ds s.mem t.mem)
    (hds : ∀ e ∈ ds, SlotOk e) (hl : ∀ d ∈ ls, d ∉ ds) : ∀ d ∈ ls, slot t.mem P.B d = V d := fun d hd => by
  rw [k.slot (h.ls_ok d hd).1 (fun e he => (h.ls_ok d hd).sep (hds e he) fun x => hl d hd (x ▸ he)), h.sl d hd]

end

end VG.Proof.RsaKeyGen.Arm.Key
