module

public import VerifiedGarbage.Impl.Mont.X86.Sse2
import VerifiedGarbage.Proof.Mont.X86.Sse2.AtVerified
import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified
public import VerifiedGarbage.Proof.Mont.X86.Sse2.Shape
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Callee
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Offset

/-! # A multiplication by a call, in public RSA at a run-time width

`mul o a b` (`Impl/Bignum/X86/PublicRt.lean`): from the arguments' frame
below `esp`, a call of `vg_rsa_mont_mul_at` writes the Montgomery product of
numbers `a` and `b` into number `o`, changing only it, the callee's range
and the 96 bytes of stack below `esp` (`mul_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.MontMul (scratchBytes)

section
variable {s g : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- The callee's arguments: the stored words of the frame. -/
theorem callee_arg (low : 96 ≤ (s.gpr .esp).toNat) (hesp : g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 36)
    {o a b : Nat} (hread : ∀ i < 9, g.mem.readW ((g.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
        mulArg len o a b (s.gpr .edi) (args 9) i) {i : Nat} (hi : i < 9) :
    arg (calleeOf g base bytes) i = mulArg len o a b (s.gpr .edi) (args 9) i := by
  have hsp := (s.gpr .esp).isLt
  have gEsp : (g.gpr .esp).toNat = (s.gpr .esp).toNat - 36 := by rw [hesp, sub_toNat (by omega_arith)]
  show arg g.callEntry i = _
  rw [arg_callEntry (by omega_arith) (by omega_arith)]
  have e := addr_eq (x := g.gpr .esp) (k := 4 * i) (by omega_arith)
  simp only [addr] at e
  rw [e, hread i hi]

/-- The callee's memory is the caller's, but for the 40 bytes below `esp`. -/
theorem callee_frame (low : 96 ≤ (s.gpr .esp).toNat) (hesp : g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 36)
    (hFg : Frame [below (s.gpr .esp) 36] s.mem g.mem) :
    Frame [below (s.gpr .esp) 40] s.mem (calleeOf g base bytes).mem := by
  have hsp := (s.gpr .esp).isLt
  have gEsp : (g.gpr .esp).toNat = (s.gpr .esp).toNat - 36 := by rw [hesp, sub_toNat (by omega_arith)]
  have F₁ : Frame [below (g.gpr .esp) 4] g.mem g.callEntry.mem :=
    Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_top (Nat.le_refl 4) (by omega_arith) (by decide))
  refine (hFg.sub fun r hr => ?_).trans (F₁.sub fun r hr => ?_)
  · rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, below_sub (by decide) (by omega_arith)⟩
  · rw [List.mem_singleton.mp hr, hesp]
    exact ⟨_, List.mem_singleton_self _, below_inner (by decide) (by omega_arith)⟩

end

/-- An argument of the caller, in the frame of 36 bytes below its `esp`. -/
theorem argAt_alloc {s : State} {i : Nat} {v : BitVec 32} (h : readSrc s (.mem (PublicFn.argument i)) = some v) :
    readSrc (allocFrame 36 s) (.mem (argAt 9 i)) = some v := by
  have e : (allocFrame 36 s).ea (argAt 9 i) = s.ea (PublicFn.argument i) := by
    simp only [State.ea, argAt, PublicFn.argument, at_, allocFrame_esp]
    congr 1
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_neg, BitVec.toNat_ofNat]
    omega_arith
  revert h
  simp only [readSrc, State.load32, e, allocFrame_mem, allocFrame_rd, allocFrame_wr]
  intro h
  split at h
  · rename_i hr
    rw [ite_eq_left_iff.mpr fun hn => absurd ?_ hn]
    · exact h
    obtain ⟨r, hr, hc⟩ := hr
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, hc⟩
    · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), hc⟩
  · cases h

/-- Outside a range at an offset of `base`: its offset is before or past it. -/
theorem ofs_out {base x : Addr} {d k : Nat}
    (h : ¬ (⟨off base d, k⟩ : Region).Contains x 1) : ofs base x < d ∨ d + k ≤ ofs base x := by
  simp only [Region.Contains, off, ofs] at h ⊢
  bv_omega

theorem ofs_in {base x : Addr} {k : Nat} (h : (⟨base, k⟩ : Region).Contains x 1) : ofs base x < k := by
  simp only [Region.Contains, ofs] at h ⊢; omega_arith

theorem ofs_eq (base x : Addr) : x = base + BitVec.ofNat 64 (ofs base x) := by
  simp only [ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rw [BitVec.add_comm, BitVec.sub_add_cancel]

theorem rtBody_noSp : NoSp Sse2.atBody := VG.Proof.Mont.X86.Sse2.atBody_NoSp

theorem rtBody_stackUse : stackUse Sse2.atBody = 56 := VG.Proof.Mont.X86.Sse2.atBody_stack

theorem mulBody_noSp (o a b : Nat) (wl : Nat := 9) :
    NoSp (.seq (.block (mulArgs o a b wl)) (.call "vg_rsa_mont_mul_at" Sse2.atBody)) := by
  apply NoSp.of_all
  have e : (!Taint.clobbers (Instr.alu AluOp.add Reg.eax (Src.reg Reg.edx)) Reg.esp) = true := rfl
  rw [Code.allInstrs_eq]
  simp only [instrs, mulArgs, widthB, offEax, List.all_append, List.all_cons, List.all_nil, List.all_replicate, e,
    ite_self]
  rw [← Code.allInstrs_eq]
  rw [show Sse2.atBody.allInstrs (fun i => !Taint.clobbers i .esp)=true from VG.Proof.Mont.X86.Sse2.atBody_allNoSp]
  rfl

theorem mul_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) (hbytes : bytes = (args 9).toNat * 8)
    (R : CallRoom (s.gpr .esp) base bytes) {o a b : Nat} (ho : o ≤ 4) (ha : a ≤ 4) (hb : b ≤ 4) (ho0 : o ≠ 0)
    (hinv : (val32 s.mem base numOff (nw len) * w32 s.mem base invOff + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base (numAt len b) (nw len) < val32 s.mem base numOff (nw len)) :
    WP isa (PublicRt.mul o a b) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨off base (numAt len o), wb len⟩, ⟨off base (numAt len 5), 3 * wb len + 56⟩, below (s.gpr .esp) 96]
        s.mem t.mem ∧
      val32 t.mem base (numAt len o) (nw len) < val32 s.mem base numOff (nw len) ∧
      val32 t.mem base (numAt len o) (nw len) * 2 ^ (32 * nw len) % val32 s.mem base numOff (nw len) =
        val32 s.mem base (numAt len a) (nw len) * val32 s.mem base (numAt len b) (nw len) %
          val32 s.mem base numOff (nw len) := by
  have low := R.low
  have low40 : 40 ≤ (s.gpr .esp).toNat := by omega_arith
  have hsp := (s.gpr .esp).isLt
  have nwr := h.scratch.nowrap
  unfold PublicRt.mul
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by omega_arith) (mulBody_noSp o a b) ?_
  have fEsp : (allocFrame 36 s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := allocFrame_esp _ _
  have fEspN : ((allocFrame 36 s).gpr .esp).toNat = (s.gpr .esp).toNat - 36 := by rw [fEsp, sub_toNat (by omega_arith)]
  refine WP.seq (WP.mono (mulArgs_ok (f := allocFrame 36 s) (len := len) (o := o) (a := a) (b := b)
    (argAt_alloc (by rw [← h.outLen]; exact (h.stack 1 (by decide)).readSrc))
    (argAt_alloc (h.stack 9 (by decide)).readSrc) h.upper (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by rw [allocFrame_wr, fEsp]; exact List.mem_cons_self ..)) fun g ⟨Kg, Fg, Rg⟩ => ?_)
  have gEsp : g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := by rw [Kg.1 _ (by decide), fEsp]
  have gEdi : g.gpr .edi = s.gpr .edi := by rw [Kg.1 _ (by decide), allocFrame_gpr _ _ (by decide)]
  have hFg : Frame [below (s.gpr .esp) 36] s.mem g.mem := by
    have := Fg; rwa [fEsp, allocFrame_mem] at this
  have hread : ∀ i < 9, g.mem.readW ((g.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
      mulArg len o a b (s.gpr .edi) (args 9) i := by
    intro i hi; rw [Kg.1 _ (by decide), Rg i hi, allocFrame_gpr _ _ (by decide)]
  have A := callee_abi h hbytes R ho ha hb ho0 gEsp hFg hread hinv hB
  have Fc := callee_frame (base := base) (bytes := bytes) low gEsp hFg
  have gEspN : (g.gpr .esp).toNat = (s.gpr .esp).toNat - 36 := by rw [gEsp, sub_toNat (by omega_arith)]
  have hframe : (⟨(g.gpr .esp).setWidth 64, 36⟩ : Region) ∈ g.wr := by
    rw [Kg.2.2, allocFrame_wr, gEsp]; exact List.mem_cons_self ..
  have hscr : (⟨base, bytes⟩ : Region) ∈ g.wr := by
    rw [Kg.2.2, allocFrame_wr]; exact List.mem_cons_of_mem _ h.scratch.wr
  have argA : argAddr g.callEntry 0 = (g.gpr .esp).setWidth 64 := by rw [argAddr_callEntry]; simp
  have low96 := R.low
  refine WP.call (k := Proof.Rsa.MontMul.mulContract abi 56) (rd := [⟨argAddr g.callEntry 0, 36⟩])
    (wr := [⟨base, bytes⟩]) VG.Proof.Mont.X86.Sse2.at_correct rtBody_noSp (by rw [rtBody_stackUse]; omega_arith)
    (callee_pre A R gEsp)
    (Covers.of_mem fun r hr => ?_) (Covers.of_mem fun r hr => ?_) fun s' rd' wr' cs' F _ ⟨s₂, m₂, _, post⟩ => ?_
  · rcases List.mem_append.mp hr with hr | hr <;> rw [List.mem_singleton.mp hr]
    · rw [argA]; exact List.mem_append_right _ hframe
    · exact List.mem_append_right _ hscr
  · rw [List.mem_singleton.mp hr]; exact hscr
  change (Proof.Rsa.MontMul.mulContract abi 56).post (calleeOf g base bytes) s₂ at post
  sig_post [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes] at post
  obtain ⟨L₂, C₂, K₂⟩ := post
  have hw := wb_le h.upper
  have dims := h.dimensions
  have ca := fun i (hi : i < 9) => callee_arg (base := base) (bytes := bytes) low gEsp hread hi
  have vn : ∀ {v : Nat}, v < 2 ^ 32 → (BitVec.ofNat 32 v).toNat = v := fun hv => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  have v8 : ∀ j ≤ 8, numAt len j < 2 ^ 32 := fun j hj => by
    have := Nat.mul_le_mul hj hw; simp only [numAt, numOff]; omega_arith
  have w0 : BitVec.setWidth 64 (arg (calleeOf g base bytes) 0) = base := by
    rw [ca 0 (by decide)]; exact h.scratch.edi
  have w1 : (arg (calleeOf g base bytes) 1).toNat = (args 9).toNat := by rw [ca 1 (by decide)]; rfl
  have w2 : (arg (calleeOf g base bytes) 2).toNat = Spec.Rsa.modulusWords len := by
    rw [ca 2 (by decide)]; exact vn (by simp only [Spec.Rsa.modulusWords]; omega_arith)
  have w3 : (arg (calleeOf g base bytes) 3).toNat = numOff := by rw [ca 3 (by decide)]; exact vn (by decide)
  have w5 : (arg (calleeOf g base bytes) 5).toNat = numAt len 5 := by
    rw [ca 5 (by decide)]; exact vn (v8 5 (by decide))
  have w6 : (arg (calleeOf g base bytes) 6).toNat = numAt len o := by
    rw [ca 6 (by decide)]; exact vn (v8 o (by omega_arith))
  have w7 : (arg (calleeOf g base bytes) 7).toNat = numAt len a := by
    rw [ca 7 (by decide)]; exact vn (v8 a (by omega_arith))
  have w8 : (arg (calleeOf g base bytes) 8).toNat = numAt len b := by
    rw [ca 8 (by decide)]; exact vn (v8 b (by omega_arith))
  simp only [w0, w1, w2, w3, w5, w6, w7, w8, numAt_val32] at L₂ C₂ K₂
  have Fc' : Frame [below (s.gpr .esp) 40] s.mem (g.mem.writeW ((g.gpr .esp - 4).setWidth 64) (g.unknowns 0)) := Fc
  have vc : ∀ d, d + wb len ≤ bytes →
      val32 (g.mem.writeW ((g.gpr .esp - 4).setWidth 64) (g.unknowns 0)) base d (nw len) =
        val32 s.mem base d (nw len) := fun d hd => by
    rw [← read_eq_val32, ← read_eq_val32, Fc'.read (r := ⟨base, bytes⟩)
      (Offset.contains_base _ (by rw [← wb_eq]; exact hd) (by omega_arith))
      (fun r' hr' => by rw [List.mem_singleton.mp hr']; exact R.apart40.symm) (by simp only [nw]; omega_arith)]
  have f0 := (h.fits (j := 0) (by decide)).1
  have fa := (h.fits (j := a) (by omega_arith)).1
  have fb := (h.fits (j := b) (by omega_arith)).1
  have n0 : numAt len 0 = numOff := by simp [numAt]
  rw [n0] at f0
  rw [vc _ f0] at L₂ C₂
  rw [vc _ fa, vc _ fb] at C₂
  have e64 : 64 * Spec.Rsa.modulusWords len = 32 * nw len := by simp only [nw]; omega_arith
  rw [e64] at C₂
  refine ⟨fun r hr => ?_, by rw [freed_rd, rd', Kg.2.1, allocFrame_rd],
    by rw [freed_wr, wr', Kg.2.2, allocFrame_wr]; rfl, fun x hx => ?_,
    by rw [freed_mem, ← m₂]; exact L₂, by rw [freed_mem, ← m₂]; exact C₂⟩
  · by_cases he : r = .esp
    · subst he
      rw [freed_esp, cs' _ hr, gEsp, BitVec.sub_add_cancel]
    · rw [freed_gpr _ _ he, cs' _ hr, Kg.1 _ (by revert hr; cases r <;> simp [calleeSaved]),
        allocFrame_gpr _ _ he]
  · -- Memory: the callee's range and the result in the working space, the stack below `esp` outside it.
    have f5 := (h.fits (j := 5) (by decide)).2
    have fo := (h.fits (j := o) (by omega_arith)).1
    have nst96 : ¬ (below (s.gpr .esp) 96).Contains x 1 := hx _ (by simp)
    have nst : ¬ (below (s.gpr .esp) 40).Contains x 1 := fun hc => nst96 (below_sub (by decide) low96 x hc)
    have no5 : ¬ (⟨off base (numAt len 5), 3 * wb len + 56⟩ : Region).Contains x 1 := hx _ (by simp)
    have noo : ¬ (⟨off base (numAt len o), wb len⟩ : Region).Contains x 1 := hx _ (by simp)
    rw [freed_mem]
    by_cases hin : (⟨base, bytes⟩ : Region).Contains x 1
    · have hi := ofs_in hin
      have o5 := ofs_out no5
      have oo := ofs_out noo
      rw [← m₂, ofs_eq base x, K₂ _ (by rw [hbytes] at hi; omega_arith) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simp only [scratchBytes, wb] at o5 ⊢; omega_arith
        · simp only [wb] at oo ⊢; omega_arith), ← ofs_eq base x]
      exact Fc' x fun r hr => by rw [List.mem_singleton.mp hr]; exact nst
    · rw [F x fun r hr => ?_]
      · exact hFg x fun r hr => by
          rw [List.mem_singleton.mp hr]; exact fun hc => nst (below_sub (by decide) low40 x hc)
      · rcases List.mem_append.mp hr with hr | hr <;> rw [List.mem_singleton.mp hr]
        · exact hin
        · rw [rtBody_stackUse, gEsp]
          exact fun hc => nst96 (below_inner (a := 56 + 4) (k := 36) (b := 96) (by decide) low96 x hc)

end VG.Proof.Bignum.X86.PublicRt
