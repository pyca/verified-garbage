module

import VerifiedGarbage.Proof.Mont.X86.Sse2.Shape

public import VerifiedGarbage.Proof.Rsa.X86.RvMontFrame
import VerifiedGarbage.Proof.Rsa.X86.RvMontArgs
import VerifiedGarbage.Proof.Rsa.X86.RvMontClear
import VerifiedGarbage.Proof.Rsa.X86.RvFrameStep
import VerifiedGarbage.Proof.Rsa.X86.RvWrite
import VerifiedGarbage.Proof.Rsa.X86.RvViews
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.MontMulContract
public import VerifiedGarbage.TCB.X86.Isa

/-! # A Montgomery multiplication advances the tracked recovery stage

`KS.mmul`: `mmul o a b`, a call of `vg_rsa_mont_mul_at` and the result's two
words above the callee's cleared, sets `[o]` to the Montgomery product of
`[a]` and `[b]` modulo `m`, keeping the stage's other arrays and header
words, and the modulus and its inverse (`MR`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.RtCall
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Impl.Rsa.X86.RecoverRt (mmul mulArgs narF)
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Bignum.X86.PublicRt (argAt_alloc)
open VG.Proof.Rsa.MontMul (Apart scratchBytes)

theorem mulBody_noSp (o a b : Nat) :
    NoSp (.seq (.block (mulArgs o a b)) (.call "vg_rsa_mont_mul_at" Sse2.atBody) : Prog isa) := by
  apply NoSp.of_all
  have e : (!Taint.clobbers (Instr.alu AluOp.add Reg.eax (Src.reg Reg.edx)) Reg.esp) = true := rfl
  rw [Code.allInstrs_eq]
  simp only [instrs, mulArgs, VG.Impl.Rsa.X86.KeyRt.bytesB, VG.Impl.Rsa.X86.KeyRt.Shape.extra,
    VG.Impl.Bignum.X86.PublicRt.widthB, VG.Impl.Rsa.X86.RecoverRt.offIn, List.all_append, List.all_cons,
    List.all_nil, List.all_replicate, e, ite_self]
  rw [← Code.allInstrs_eq]
  rw [show Sse2.atBody.allInstrs (fun i => !Taint.clobbers i .esp)=true from VG.Proof.Mont.X86.Sse2.atBody_allNoSp]
  rfl

/-- The callee's offsets: the operands apart from its range, the result apart from the modulus. -/
theorem mont_offs {g : Geo} {Z : Nat} (fits : arr g.w nArr ≤ Z) {o a b : Nat} (ho : MontIndex o)
    (ha : MontIndex a) (hb : MontIndex b) (ho0 : o ≠ mBase) (pos : 0 < g.n) :
    Offs Z g.n (arr g.w mBase) sInv (arr g.w mAcc) (arr g.w o) (arr g.w a) (arr g.w b) := by
  have S8 : S g.w = 8 * g.n + 16 := by simp only [S, Geo.w, width]; omega_arith
  have fN : ∀ j, j < nArr → arr g.w j + S g.w ≤ Z := fun j hj => Nat.le_trans (arr_end hj) fits
  have side : ∀ j, MontIndex j → arr g.w j + S g.w ≤ arr g.w mAcc ∨ arr g.w (mAcc + 4) ≤ arr g.w j :=
    fun j hj => hj.2.elim (fun lt => .inl (arr_end lt)) (fun ge => .inr (arr_mono ge))
  have acc : arr g.w (mAcc + 4) = arr g.w mAcc + 4 * S g.w := by simp only [arr, mAcc]; omega_arith
  have lowA : hdr ≤ arr g.w 0 := by simp [arr]
  have low : ∀ j, arr g.w 0 ≤ arr g.w j := fun j => arr_mono (Nat.zero_le j)
  have sb : scratchBytes g.n ≤ 4 * S g.w := by simp only [scratchBytes]; omega_arith
  have fo := fN o ho.1
  have fa := fN a ha.1
  have fb := fN b hb.1
  have fm := fN mBase (by decide)
  have fs := fN (mAcc + 3) (by decide)
  have es : arr g.w (mAcc + 3) = arr g.w mAcc + 3 * S g.w := by simp only [arr, mAcc]; omega_arith
  have so := side o ho
  have sa := side a ha
  have sbb := side b hb
  have sm := side mBase (by decide)
  have om := arr_disj (w := g.w) ho0
  have lo := low o
  have lm := low mBase
  have ls := low mAcc
  have hi : sInv + 4 ≤ hdr := by decide
  refine ⟨pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [Apart]) <;> omega_arith

theorem num_prefix {g : Geo} {m : Mem} {j x : Nat} (h : num m g.B g.w j = x) (hx : x < 2 ^ (64 * g.n)) :
    val32 m g.B (arr g.w j) (2 * g.n) = x := by
  have e := words_eq_num (m := m) (g := g) (j := j) (by rw [h]; exact hx)
  rw [wordsVal_eq_val32] at e
  rw [e, h]

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {m : Nat}

/-- A call of `vg_rsa_mont_mul_at` for `mmul o a b`, its arguments pushed: the callee's precondition,
its arguments, and the regions it is given. -/
def CallOk (g : Geo) (o a b : Nat) (x : State) : Prop :=
  (Proof.Rsa.MontMul.mulContract abi 56).pre (VG.Proof.Bignum.X86.PublicRt.calleeOf x g.B g.Z) ∧
    x.gpr .esp = g.sp - BitVec.ofNat 32 36 ∧
    (∀ i < 9, arg (VG.Proof.Bignum.X86.PublicRt.calleeOf x g.B g.Z) i =
      callArg (BitVec.ofNat 32 g.B.toNat) (BitVec.ofNat 32 (g.Z / 8)) g.n (arr g.w mBase) sInv
        (arr g.w mAcc) (arr g.w o) (arr g.w a) (arr g.w b) i) ∧
    (⟨(x.gpr .esp).setWidth 64, 36⟩ : Region) ∈ x.wr ∧ (⟨g.B, g.Z⟩ : Region) ∈ x.wr

theorem KS.callOk {o a b : Nat} (h : KS g s0 A live AW liveW V ls s) (mr : MR g m s)
    (ho : MontIndex o) (ha : MontIndex a) (hb : MontIndex b) (ho0 : o ≠ mBase)
    (hbl : b ∈ live) (hB : A b < m) :
    WP isa (.block (mulArgs o a b)) (allocFrame 36 s) (CallOk g o a b) := by
  have pos := mr.positive
  have nw := h.ws.workspace.nowrap
  have fits := h.ws.fits
  have z8 := h.z8
  have low := h.room.low
  have top := h.top
  have up := h.upper
  have esp := h.sp
  have bnd := mr.bound
  have vm : val32 s.mem g.B (arr g.w mBase) (2 * g.n) = m := num_prefix mr.modulus mr.bound
  have vb : val32 s.mem g.B (arr g.w b) (2 * g.n) = A b := num_prefix (h.arrs b hbl) (by omega_arith)
  have wsl : g.Z = (BitVec.ofNat 32 (g.Z / 8)).toNat * 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  have R : CallRoom (s.gpr .esp) g.B g.Z := by rw [esp]; exact h.room
  have fEsp : (allocFrame 36 s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := allocFrame_esp _ _
  have hl5 : VG.Proof.Rsa.X86.KeyRt.LenSrc narF (allocFrame 36 s) (8 * g.n + 8) := by
    obtain ⟨a', la, ea, ca⟩ := h.rt.lenArg
    have r5 : readSrc s (.mem (VG.Impl.Bignum.X86.PublicFn.argument 5)) = some (BitVec.ofNat 32 a') := ca.readSrc
    have e : VG.Proof.Rsa.X86.KeyRt.lenOp narF = VG.Impl.Bignum.X86.PublicRt.argAt 9 5 := rfl
    refine ⟨a', la, ea, ?_⟩
    rw [e]
    exact argAt_alloc r5
  have hr11 := argAt_alloc h.wsLen.readSrc
  have lowS : 96 ≤ (s.gpr .esp).toNat := by rw [esp]; exact low
  have edi : s.gpr .edi = BitVec.ofNat 32 g.B.toNat := by
    apply BitVec.eq_of_toNat_eq
    have header := h.ws.hdr_le
    unfold hdr at header
    rw [h.ws.workspace.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have M := mulArgs_ok (f := allocFrame 36 s) (n := g.n) (o := o) (a := a) (b := b) hl5 up hr11 ho.1 ha.1 hb.1
    (by rw [fEsp, VG.X86.sub_toNat (by omega_arith)]; omega_arith) (by rw [allocFrame_wr, fEsp]; exact List.mem_cons_self ..)
  rw [show (allocFrame 36 s).gpr .edi = s.gpr .edi from allocFrame_gpr _ _ (by decide)] at M
  refine WP.mono M fun x ⟨Kx, Fx, Rx⟩ => ?_
  have xEsp : x.gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := by rw [Kx.1 _ (by decide), fEsp]
  have hFx : Frame [below (s.gpr .esp) 36] s.mem x.mem := by
    have := Fx; rwa [fEsp, allocFrame_mem] at this
  have hread : ∀ i < 9, x.mem.readW ((x.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
      callArg (s.gpr .edi) (BitVec.ofNat 32 (g.Z / 8)) g.n (arr g.w mBase) sInv (arr g.w mAcc) (arr g.w o)
        (arr g.w a) (arr g.w b) i := by
    intro i hi; rw [Kx.1 _ (by decide), Rx i hi]
  refine ⟨VG.Proof.Bignum.X86.PublicRt.callee_pre (callee_abi h.ws.workspace wsl R (mont_offs fits ho ha hb ho0 pos) xEsp hFx hread
    (by rw [vm]; exact mr.inverse) (by rw [vb, vm]; exact hB)) R xEsp, by rw [xEsp, esp], fun i hi => ?_, ?_, ?_⟩
  · rw [callee_arg (base := g.B) (bytes := g.Z) lowS xEsp hread hi, edi]
  · rw [Kx.2.2, allocFrame_wr, xEsp]; exact List.mem_cons_self ..
  · rw [Kx.2.2, allocFrame_wr]; exact List.mem_cons_of_mem _ h.ws.workspace.wr

theorem KS.mmulCall {o a b : Nat} (h : KS g s0 A live AW liveW V ls s) (mr : MR g m s)
    (ho : MontIndex o) (ha : MontIndex a) (hb : MontIndex b) (ho0 : o ≠ mBase)
    (hal : a ∈ live) (hbl : b ∈ live) (hA : A a < m) (hB : A b < m)
    (hl : ∀ j ∈ live, j = o ∨ j ∉ montWrites o)
    (hlW : ∀ j ∈ liveW, ∀ i ∈ montWrites o, i / 2 ≠ j) :
    WP isa (callCode (mulArgs o a b)) s fun u =>
      KS g s0 A (live.filter (· ≠ o)) AW liveW V ls u ∧ MR g m u ∧ Keeps opRegs s u ∧
      u.gpr .esi = s.gpr .esi ∧ val32 u.mem g.B (arr g.w o) (2 * g.n) < m ∧
      val32 u.mem g.B (arr g.w o) (2 * g.n) * 2 ^ (64 * g.n) % m = A a * A b % m := by
  have pos := mr.positive
  have nw := h.ws.workspace.nowrap
  have fits := h.ws.fits
  have header := h.ws.hdr_le
  have z8 := h.z8
  have low := h.room.low
  have top := h.top
  have up := h.upper
  have esp := h.sp
  have bnd := mr.bound
  have S8 : S g.w = 8 * g.n + 16 := by simp only [S, Geo.w, width]; omega_arith
  have vm : val32 s.mem g.B (arr g.w mBase) (2 * g.n) = m := num_prefix mr.modulus mr.bound
  have va : val32 s.mem g.B (arr g.w a) (2 * g.n) = A a := num_prefix (h.arrs a hal) (by omega_arith)
  have vb : val32 s.mem g.B (arr g.w b) (2 * g.n) = A b := num_prefix (h.arrs b hbl) (by omega_arith)
  have wsl : g.Z = (BitVec.ofNat 32 (g.Z / 8)).toNat * 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  have R : CallRoom (s.gpr .esp) g.B g.Z := by rw [esp]; exact h.room
  have fEsp : (allocFrame 36 s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := allocFrame_esp _ _
  have hl5 : VG.Proof.Rsa.X86.KeyRt.LenSrc narF (allocFrame 36 s) (8 * g.n + 8) := by
    obtain ⟨a', la, ea, ca⟩ := h.rt.lenArg
    have r5 : readSrc s (.mem (VG.Impl.Bignum.X86.PublicFn.argument 5)) = some (BitVec.ofNat 32 a') := ca.readSrc
    have e : VG.Proof.Rsa.X86.KeyRt.lenOp narF = VG.Impl.Bignum.X86.PublicRt.argAt 9 5 := rfl
    refine ⟨a', la, ea, ?_⟩
    rw [e]
    exact argAt_alloc r5
  have hr11 := argAt_alloc h.wsLen.readSrc
  have lowS : 96 ≤ (s.gpr .esp).toNat := by rw [esp]; exact low
  have C := call_ok (is := mulArgs o a b) h.ws.workspace wsl R (mont_offs fits ho ha hb ho0 pos)
    (by rw [vm]; exact mr.inverse) (by rw [vb, vm]; exact hB) (mulBody_noSp o a b) (by
      have := mulArgs_ok (f := allocFrame 36 s) (n := g.n) (o := o) (a := a) (b := b) hl5 up hr11 ho.1 ha.1 hb.1
        (by rw [fEsp, VG.X86.sub_toNat (by omega_arith)]; omega_arith) (by rw [allocFrame_wr, fEsp]; exact List.mem_cons_self ..)
      rwa [show (allocFrame 36 s).gpr .edi = s.gpr .edi from allocFrame_gpr _ _ (by decide)] at this)
  refine WP.mono C fun u ⟨cs, rd, wr, F, L, Vv⟩ => ?_
  have Ku : Keeps opRegs s u :=
    ⟨fun r hr => cs r (by revert hr; cases r <;> decide), rd, wr⟩
  have Fu : Frame (VG.Proof.Bignum.X86.CrtRt.frameR g.B g.sp [(arr g.w o, 8 * g.n), (arr g.w mAcc, scratchBytes g.n)])
      s.mem u.mem := by
    rw [← esp]; exact VG.Proof.Bignum.X86.CrtRt.frameR_of_mul F (by simp) (by simp)
  have sb : scratchBytes g.n ≤ 4 * S g.w := by simp only [scratchBytes]; omega_arith
  have acc4 : arr g.w (mAcc + 4) = arr g.w mAcc + 4 * S g.w := by simp only [arr, mAcc]; omega_arith
  have fN : ∀ j, j < nArr → arr g.w j + S g.w ≤ g.Z := fun j hj => Nat.le_trans (arr_end hj) fits
  have lowA : ∀ j, hdr ≤ arr g.w j := fun j => Nat.le_add_right _ _
  have w4 : 4 * g.w = 8 * g.n + 8 := by simp only [Geo.w, width]; omega_arith
  have apartN : ∀ j, j < nArr → j ≠ o → (j < mAcc ∨ mAcc + 4 ≤ j) →
      ∀ p ∈ [(arr g.w o, 8 * g.n), (arr g.w mAcc, scratchBytes g.n)], arr g.w j + 4 * g.w ≤ p.1 ∨ p.1 + p.2 ≤ arr g.w j := by
    intro j hj ne side p hp
    have d := arr_disj (w := g.w) ne
    have sj := side.elim (fun lt => Or.inl (arr_end (w := g.w) lt)) (fun ge => Or.inr (arr_mono (w := g.w) ge))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega_arith
  -- The stage at `u`, without `o`.
  have hu : KS g s0 A (live.filter (· ≠ o)) AW liveW V ls u := by
    have hf := h.mono (live' := live.filter (· ≠ o)) (fun j hj => ⟨(List.mem_filter.mp hj).1, rfl⟩)
      (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
    refine hf.frameStep Ku Fu (fun p hp => ?_) (fun j hj => ?_) (fun j hj => ?_) (fun d hd p hp => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      have fo := fN o ho.1
      have fs := fN (mAcc + 3) (by decide)
      have es : arr g.w (mAcc + 3) = arr g.w mAcc + 3 * S g.w := by simp only [arr, mAcc]; omega_arith
      rcases hp with rfl | rfl <;> dsimp only <;> have := lowA o <;> have := lowA mAcc <;> unfold hdr at * <;> omega_arith
    · obtain ⟨jl, jo⟩ := List.mem_filter.mp hj
      have jo' : j ≠ o := by simpa using jo
      have side := (hl j jl).resolve_left jo'
      simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at side
      exact apartN j (h.live_lt j jl) jo' (by unfold mAcc at *; omega_arith)
    · intro p hp
      have hw := hlW j hj
      simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hw
      have jlt := h.liveW_lt j hj
      rw [show arr g.W j = arr g.w (2 * j) by rw [Geo.W, wide, arr_W]]
      have W4 : 4 * g.W = 2 * S g.w - 8 := by simp only [S, Geo.W, Geo.w, wide, width]; omega_arith
      rw [W4]
      have d0 := arr_disj (w := g.w) (j := 2 * j) (k := o) (by omega_arith)
      have d1 := arr_disj (w := g.w) (j := 2 * j + 1) (k := o) (by omega_arith)
      have s1 : arr g.w (2 * j + 1) = arr g.w (2 * j) + S g.w := arr_succ _ _
      have sj : arr g.w (2 * j + 1) + S g.w ≤ arr g.w mAcc ∨ arr g.w (mAcc + 4) ≤ arr g.w (2 * j) := by
        unfold mAcc at *
        by_cases lt : 2 * j + 1 < 16
        · exact .inl (arr_end lt)
        · exact .inr (arr_mono (by omega_arith))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega_arith
    · have ok := h.ls_ok d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      unfold SlotOk at ok
      rcases hp with rfl | rfl <;> dsimp only <;> have := lowA o <;> have := lowA mAcc <;> omega_arith
  -- The modulus and its inverse through the call.
  have mU : num u.mem g.B g.w mBase = num s.mem g.B g.w mBase := by
    have fm := fN mBase (by decide)
    exact VG.Proof.Bignum.X86.CrtRt.frameR_val32 Fu h.room nw (by simp only [S] at fm; omega_arith)
      (apartN mBase (by decide) (Ne.symm ho0) (by decide)) (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        have fo := fN o ho.1
        have fs := fN (mAcc + 3) (by decide)
        have es : arr g.w (mAcc + 3) = arr g.w mAcc + 3 * S g.w := by simp only [arr, mAcc]; omega_arith
        rcases hp with rfl | rfl <;> dsimp only <;> omega_arith)
  have iU : w32 u.mem g.B sInv = w32 s.mem g.B sInv := by
    have e := VG.Proof.Bignum.X86.CrtRt.frameR_val32 (d := sInv) (k := 1) Fu h.room nw
      (by unfold sInv hdr at *; omega_arith) (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> dsimp only <;> have := lowA o <;> have := lowA mAcc <;>
          unfold sInv hdr at * <;> omega_arith) (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        have fo := fN o ho.1
        have fs := fN (mAcc + 3) (by decide)
        have es : arr g.w (mAcc + 3) = arr g.w mAcc + 3 * S g.w := by simp only [arr, mAcc]; omega_arith
        rcases hp with rfl | rfl <;> dsimp only <;> omega_arith)
    simpa only [val32, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add] using e
  have mrU : MR g m u := mr.of_eq mU iU
  exact ⟨hu, mrU, Ku, cs _ (by decide), by rw [← vm]; exact L, by rw [← vm, ← va, ← vb]; exact Vv⟩

theorem KS.mmul {o a b : Nat} (h : KS g s0 A live AW liveW V ls s) (mr : MR g m s)
    (ho : MontIndex o) (ha : MontIndex a) (hb : MontIndex b) (ho0 : o ≠ mBase)
    (hal : a ∈ live) (hbl : b ∈ live) (hA : A a < m) (hB : A b < m)
    (hl : ∀ j ∈ live, j = o ∨ j ∉ montWrites o)
    (hlW : ∀ j ∈ liveW, ∀ i ∈ montWrites o, i / 2 ≠ j) :
    WP isa (mmul o a b) s fun t => ∃ X,
      KS g s0 (upd A o X) (o :: live) AW liveW V ls t ∧ MR g m t ∧
      (Keeps opRegs s t ∧ t.gpr .esi = s.gpr .esi) ∧
      X < m ∧ X * 2 ^ (64 * g.n) % m = A a * A b % m := by
  unfold VG.Impl.Rsa.X86.RecoverRt.mmul
  refine WP.seq (WP.mono (h.mmulCall mr ho ha hb ho0 hal hbl hA hB hl hlW)
    fun u ⟨hu, mrU, Ku, esi, L, Vv⟩ => ?_)
  have kn := kw_nar g.n
  refine WP.mono (clrTop_ok hu.rt (j := o) ho.1 (by rw [kn]; simp only [width]; omega_arith))
    fun t ⟨_, k, e, r⟩ => ?_
  rw [kn] at k e
  have Kt : Keeps opRegs u t := r.mono (by decide)
  have e' : num t.mem g.B g.w o = val32 u.mem g.B (arr g.w o) (2 * g.n) := by
    rw [e, show width g.n - 2 = 2 * g.n by simp only [width]; omega_arith]
  have ht := hu.write_w k ho.1 (by simp) Kt e' (fun j hj => by
      have := hlW j hj o (by simp); exact this) (by simp)
  refine ⟨val32 u.mem g.B (arr g.w o) (2 * g.n), ht.mono (fun j hj => ?_) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩),
    mrU.keep hu.ws k (by simpa using ho0), ⟨Ku.trans Kt, ?_⟩, ?_, ?_⟩
  · rcases List.mem_cons.mp hj with rfl | hj'
    · exact ⟨List.mem_cons_self .., rfl⟩
    · by_cases jo : j = o
      · subst jo; exact ⟨List.mem_cons_self .., rfl⟩
      · exact ⟨List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hj', by simpa using jo⟩), rfl⟩
  · rw [r.1 _ (by decide), esi]
  · exact L
  · exact Vv

end
end VG.Proof.Rsa.X86.Recover
