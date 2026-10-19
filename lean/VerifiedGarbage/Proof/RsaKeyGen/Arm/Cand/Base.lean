module

public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate
public import VerifiedGarbage.Proof.Rsa.Arm.KeyArrs
public import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
public import Batteries.Logic
public import VerifiedGarbage.Proof.Framework.Lit

/-! # A candidate on ARMv7: the public parameters and the stages

`CP`: what two runs share (the frame, the pointers, the lengths, `e`, and
the branches the candidate takes, `sch`). `In P σ`: the state `σ` the body
starts from, after the push, with the regions narrowed to the frame, the
outputs, the working space and Montgomery multiplication's part of it.
`KS P σ A live V ls s`: a stage of the body: what it keeps of `σ`, `W` in
the division's header, the arrays `live` holding `A` and the header words
`ls` holding `V` (as for the key, `Proof/RsaKeyGen/Arm/Key/Base.lean`). What
memory a stage may have changed besides the working space (`chg`): the
outputs, frame word 0 (Montgomery multiplication's base), and the frame of
the round below the stack pointer. The body starts after the entry, which
moves `out` to frame word 12.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

structure CP where
  sp : BitVec 32
  oP : BitVec 32
  uP : BitVec 32
  eP : BitVec 32
  pP : BitVec 32
  nP : BitVec 32
  B : BitVec 32
  L : Nat
  el : Nat
  pl : Nat
  rl : Nat
  SL : Nat
  eB : List Byte
  sch : VG.Proof.RsaKeyGen.Sched

namespace CP

/-- The 32-bit words of the working space's numbers, the 64-bit words of the
candidate, and the working space's size. -/
abbrev W (P : CP) : Nat := P.L / 4 + 2
abbrev w (P : CP) : Nat := P.L / 8
abbrev Z (P : CP) : Nat := P.SL * 8

/-- Montgomery multiplication's working space: its offset in the working
space (256 bytes before the key array `mBase`), its base and its 64-bit
words: those of its eight arrays (the round's are the rest of the working
space, `lenR`). -/
abbrev oM (P : CP) : Nat := 8 * (21 * P.w + 30)
abbrev M0 (P : CP) : BitVec 32 := P.B + BitVec.ofNat 32 P.oM
abbrev lenM (P : CP) : Nat := 8 * P.w + 48
abbrev lenR (P : CP) : Nat := P.SL - (21 * P.w + 30)

abbrev rS (P : CP) : Region := ⟨State.addr P.B, P.Z⟩
abbrev rM (P : CP) : Region := ⟨State.addr P.M0, 8 * P.lenM⟩
abbrev rO (P : CP) : Region := ⟨State.addr P.oP, P.L⟩
abbrev rU (P : CP) : Region := ⟨State.addr P.uP, 8⟩
abbrev rE (P : CP) : Region := ⟨State.addr P.eP, P.el⟩
abbrev rPp (P : CP) : Region := ⟨State.addr P.pP, P.pl⟩
abbrev rR (P : CP) : Region := ⟨State.addr P.nP, P.rl⟩
/-- The frame alone, with the stack arguments, and the round's frame below it. -/
abbrev rFr (P : CP) : Region := ⟨State.addr P.sp, 56⟩
abbrev rF (P : CP) : Region := ⟨State.addr P.sp, 84⟩
abbrev rC (P : CP) : Region := ⟨State.addr (P.sp - BitVec.ofNat 32 56), 56⟩
/-- Frame word 0. -/
abbrev rW0 (P : CP) : Region := ⟨State.addr P.sp, 4⟩

/-- What the body may change. -/
abbrev chg (P : CP) : List Region := [P.rS, P.rO, P.rU, P.rC, P.rW0]

abbrev e (P : CP) : Nat := Spec.Rsa.os2ip P.eB

end CP

/-- The frame word at byte `o`. -/
abbrev fw (m : Mem) (P : CP) (o : Nat) : BitVec 32 := m.readW (off (State.addr P.sp) o) 32

/-- The other prime, and the random octets. -/
abbrev pB (P : CP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.pP) P.pl
abbrev rB (P : CP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.nP) P.rl

/-- The result. -/
abbrev res (P : CP) (σ : State) : Option (Spec.RsaKeyGen.Candidate × Spec.RsaKeyGen.Rand) :=
  Spec.RsaKeyGen.candidateOp P.L P.eB (pB P σ) (rB P σ)

structure In (P : CP) (σ : State) : Prop where
  sp : σ.sp = P.sp
  spLo : 56 ≤ P.sp.toNat
  spFit : P.sp.toNat + 84 ≤ 2 ^ 32
  wr : σ.wr = [P.rFr, P.rO, P.rU, P.rS, P.rM]
  rdE : InRegions (σ.rd ++ σ.wr) (State.addr P.eP) P.el
  rdP : InRegions (σ.rd ++ σ.wr) (State.addr P.pP) P.pl
  rdR : InRegions (σ.rd ++ σ.wr) (State.addr P.nP) P.rl
  rdA : InRegions (σ.rd ++ σ.wr) (off (State.addr P.sp) 56) 28
  k1 : 32 ≤ P.L
  k2 : P.L ≤ 512
  k8 : P.L % 8 = 0
  el1 : 1 ≤ P.el
  el2 : P.el ≤ 8
  plv : P.pl = 0 ∨ P.pl = P.L
  scr : Spec.Rsa.scratchWords P.L ≤ P.SL
  fO : P.oP.toNat + P.L ≤ 2 ^ 32
  fU : P.uP.toNat + 8 ≤ 2 ^ 32
  fE : P.eP.toNat + P.el ≤ 2 ^ 32
  fP : P.pP.toNat + P.pl ≤ 2 ^ 32
  fR : P.nP.toNat + P.rl ≤ 2 ^ 32
  rlt : P.rl < 2 ^ 32
  fS : P.B.toNat + P.Z ≤ 2 ^ 32
  sO : P.rS.Disjoint P.rO
  sU : P.rS.Disjoint P.rU
  sE : P.rS.Disjoint P.rE
  sP : P.rS.Disjoint P.rPp
  sR : P.rS.Disjoint P.rR
  sF : P.rS.Disjoint P.rF
  sC : P.rS.Disjoint P.rC
  oU : P.rO.Disjoint P.rU
  oE : P.rO.Disjoint P.rE
  oP : P.rO.Disjoint P.rPp
  oR : P.rO.Disjoint P.rR
  oF : P.rO.Disjoint P.rF
  oC : P.rO.Disjoint P.rC
  uE : P.rU.Disjoint P.rE
  uP : P.rU.Disjoint P.rPp
  uR : P.rU.Disjoint P.rR
  uF : P.rU.Disjoint P.rF
  uC : P.rU.Disjoint P.rC
  eF : P.rE.Disjoint P.rFr
  eC : P.rE.Disjoint P.rC
  pF : P.rPp.Disjoint P.rFr
  pC : P.rPp.Disjoint P.rC
  rF : P.rR.Disjoint P.rFr
  rC : P.rR.Disjoint P.rC
  wO : fw σ.mem P foOut = P.oP
  wL : fw σ.mem P foL = BitVec.ofNat 32 P.L
  wU : fw σ.mem P foUsed = P.uP
  wE : fw σ.mem P foE = P.eP
  aEl : fw σ.mem P aoEl = BitVec.ofNat 32 P.el
  aP : fw σ.mem P aoP = P.pP
  aPl : fw σ.mem P aoPl = BitVec.ofNat 32 P.pl
  aR : fw σ.mem P aoR = P.nP
  aRl : fw σ.mem P aoRl = BitVec.ofNat 32 P.rl
  aS : fw σ.mem P aoS = P.B
  aSl : fw σ.mem P aoSl = BitVec.ofNat 32 P.SL
  eB : Spec.Rsa.bytesAt σ.mem (State.addr P.eP) P.el = P.eB
  sch : P.L ≤ P.rl → VG.Proof.RsaKeyGen.schedOf P.L P.e (Spec.RsaKeyGen.otherPrime (pB P σ)) (rB P σ) = P.sch

/-! ## Sizes -/

section
variable {P : CP} {σ : State}

theorem In.W_eq (h : In P σ) : P.W = 2 * P.w + 2 := by have := h.k8; simp only [CP.W, CP.w]; omega

theorem In.L_eq (h : In P σ) : P.L = 8 * P.w := by have := h.k8; simp only [CP.w]; omega

theorem In.wle (h : In P σ) : P.W ≤ 130 := by have := h.k2; simp only [CP.W]; omega

theorem In.wge (h : In P σ) : 10 ≤ P.W := by have := h.k1; simp only [CP.W]; omega

theorem In.w4 (h : In P σ) : 4 ≤ P.w ∧ P.w ≤ 64 := by have := h.k1; have := h.k2; simp only [CP.w]; omega

theorem In.fits (h : In P σ) : arr P.W nArr ≤ P.Z := by
  have := h.scr; have := h.k1; have := h.k2
  simp only [Spec.Rsa.scratchWords] at *
  simp only [arr, S, hdr, nArr, CP.W, CP.Z]; omega

theorem In.Z_le (h : In P σ) : P.Z ≤ 2 ^ 32 := by have := h.fS; omega

theorem In.hdr_Z (h : In P σ) : hdr ≤ P.Z := Nat.le_trans (Nat.le_add_right _ _) h.fits

theorem In.fitZ (h : In P σ) {j : Nat} (hj : j < nArr) : arr P.W j + S P.W ≤ P.Z :=
  Nat.le_trans (arr_end hj) h.fits

theorem In.fit (h : In P σ) {j : Nat} (hj : j < nArr) : arr P.W j + S P.W ≤ 2 ^ 64 := by
  have := h.fitZ hj; have := h.Z_le; omega

theorem In.rS_mem (h : In P σ) : P.rS ∈ σ.wr := by rw [h.wr]; simp

theorem In.rM_mem (h : In P σ) : P.rM ∈ σ.wr := by rw [h.wr]; simp

/-- Montgomery multiplication's working space: 256 bytes before the key array
`mBase`, its arrays within the working space. -/
theorem In.oM_eq (h : In P σ) : P.oM + 256 = arr P.W mBase := by
  have := h.W_eq; simp only [arr, S, hdr, mBase, CP.oM]; omega

theorem In.endM (h : In P σ) : P.oM + 8 * P.lenM = arr P.W (mBase + 8) := by
  have := h.W_eq; simp only [arr, S, hdr, mBase, CP.oM, CP.lenM]; omega

theorem In.lenR_fit (h : In P σ) : P.oM + 8 * P.lenR = P.Z := by
  have := h.scr; have := h.w4; have := h.L_eq
  simp only [Spec.Rsa.scratchWords] at *
  simp only [CP.oM, CP.lenR, CP.Z]; omega

theorem In.lenR_ge (h : In P σ) : 49 * P.w + 118 ≤ P.lenR := by
  have := h.scr; have := h.w4; have := h.L_eq
  simp only [Spec.Rsa.scratchWords] at *
  simp only [CP.lenR]; omega

end

/-! ## Stages -/

/-- The header words of the stages: apart from `W` (byte 16). -/
abbrev SlotOk (d : Nat) : Prop := d + 4 ≤ hdr ∧ (d + 4 ≤ 16 ∨ 20 ≤ d) ∧ d % 4 = 0

/-- The header words a stage holds: past the division's. -/
abbrev LsOk (d : Nat) : Prop := d + 4 ≤ hdr ∧ 20 ≤ d ∧ d % 4 = 0

theorem LsOk.sep {d e : Nat} (hd : LsOk d) (he : SlotOk e) (h : d ≠ e) : d + 4 ≤ e ∨ e + 4 ≤ d := by
  omega

structure KS (P : CP) (σ : State) (A : Nat → Nat) (live : List Nat) (V : Nat → Nat) (ls : List Nat)
    (s : State) : Prop where
  pre : In P σ
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  frame : Frame P.chg σ.mem s.mem
  cnt : slot s.mem P.B 16 = P.W
  arrs : Arrs s.mem P.B P.W A live
  sl : ∀ d ∈ ls, slot s.mem P.B d = V d
  live_lt : ∀ j ∈ live, j < nArr
  ls_ok : ∀ d ∈ ls, LsOk d

section
variable {P : CP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat}

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
theorem keep_frameC {v : Nat} {js ds : List Nat} {m m' : Mem}
    (k : Keep P.B v js ds m m') (hj : ∀ j ∈ js, arr v j + S v ≤ P.Z) (hd : ∀ d ∈ ds, d + 4 ≤ hdr)
    (hz : hdr ≤ P.Z) : Frame P.chg m m' := by
  intro x hx
  have hz' : ¬ P.rS.Contains x 1 := hx _ (List.mem_cons_self)
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
    h.frame.trans (keep_frameC k (fun j hj => pre.fitZ (hjs j hj)) (fun d hd => (hds d hd).1) pre.hdr_Z), ?_,
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

end VG.Proof.RsaKeyGen.Arm.Cand
